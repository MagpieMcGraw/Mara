package mara

import "core:fmt"
import "core:os"
import "core:slice"

// ---------------------------------------------------------------------------
// Materialized call graph (design/mara_ask.md §12)
//
// A post-check artifact on Checked_Program. Nodes are the program's callable
// scopes (funs + ctors); edges are resolved calls collected during checking
// (Checker.call_edges, recorded by check_call); the strongly-connected
// components are computed once here (Tarjan).
//
// The SCCs are the prize, not the skeleton: they are the shared cycle/recursion
// structure every interprocedural summary pass would otherwise hand-roll.
// fun_return_arg_set's pending-set + `-1` return IS exactly one such ad-hoc SCC
// check; with this materialized, that becomes "the SCC this node is in".
//
// First cut: skeleton + SCCs, over the resolved/monomorphized edge flavor (the
// `callee` pointer a resolved call carries). The dispatch-set / opaque-indirect
// edges (§12 "one honest seam") and isolated (call-free) functions as nodes are
// later additions on the same structure.
// ---------------------------------------------------------------------------

Call_Graph :: struct {
    nodes:     [dynamic]^Type_Scope,   // node id -> the callable scope
    index_of:  map[^Type_Scope]int,    // scope -> node id
    out_edges: [dynamic][dynamic]int,  // node id -> callee node ids

    // Strongly-connected components. scc_of[node] = its component id; sccs[id] =
    // that component's member node ids. Tarjan emits components in REVERSE
    // topological order, so iterating sccs[] front-to-back visits callees before
    // callers — the order a bottom-up summary pass wants.
    scc_of:    [dynamic]int,
    sccs:      [dynamic][dynamic]int,

    // Reachable from the program entry (`main`) via resolved/dispatch edges.
    // reachable[n] == false on a source function = dead-code candidate. (Library
    // functions live in the graph too, so "dead in this program" is a per-build
    // property, not "delete it" — a warning would gate on the main package.)
    reachable: [dynamic]bool,

    // Purity summary (cg_compute_purity): pure[n] == false means the function
    // directly or transitively hits the outside world (IO / foreign). The first
    // interprocedural summary computed via the bottom-up framework below.
    pure:      [dynamic]bool,

    // Return-arg-set summary (cg_compute_return_args): return_args[n] = the sorted
    // set of parameter indices node n's return value can trace back to (Self-field
    // indices for a ctor). Backs the escape pass's laundering check. stmt_to_node
    // bridges the AST key fun_return_arg_set is queried with (^Stmt_Scope) to the
    // graph's node id (a node's Type_Scope.ast IS that Stmt_Scope).
    return_args:  [dynamic][]int,
    stmt_to_node: map[^Stmt_Scope]int,
}

// Intern a scope as a node, returning its id (stable for the graph's lifetime).
cg_node :: proc(g: ^Call_Graph, s: ^Type_Scope) -> int {
    if i, ok := g.index_of[s]; ok { return i }
    i := len(g.nodes)
    append(&g.nodes, s)
    g.index_of[s] = i
    append(&g.out_edges, make([dynamic]int))
    return i
}

// Materialize the graph from the edges collected during checking, then compute
// its SCCs. Idempotent w.r.t. duplicate edges (Checker.call_edges is a set).
build_call_graph :: proc(c: ^Checker) -> Call_Graph {
    g: Call_Graph
    for edge in c.call_edges {
        from := cg_node(&g, edge.from)
        to   := cg_node(&g, edge.to)
        append(&g.out_edges[from], to)
    }
    // Completeness: intern every source function as a node, so a call-free
    // function (neither calls nor is called) is still a node — reachability/DCE
    // needs it (uncalled IS the thing DCE flags). Foreign/intrinsic have no body
    // to analyze and are reachable by definition (external entry), so skip them.
    if c.checked != nil {
        for _, cs in c.checked.functions {
            if _, is_source := cs.origin.(Origin_Source); is_source && cs != nil {
                cg_node(&g, cs)
            }
        }
    }
    cg_compute_sccs(&g)
    cg_compute_reachability(&g)
    cg_compute_purity(&g, c)
    cg_dump_purity(&g)
    return g
}

// Mark every node reachable from the program entry (`main`) by a forward walk
// over the resolved/dispatch call edges. Leaves all-false when there's no `main`
// (a library / -shared build).
//
// CALL-reachability is NOT liveness — remaining seams make a LIVE function read
// as call-unreachable, so this is a building block, not a drop-in DCE:
//   1. opaque calls (fn-typed-param / indirect) aren't edges (§12 "honest seam").
//   2. byte-read placement (`x : Head = #big_endian bytes[off]`) reinterprets a
//      struct from bytes WITHOUT running its constructor — correctly no edge, but
//      the struct is still TYPE-used (that's the type-dependency graph, not this).
// (Bracket default-init `Foo{}` DOES run the ctor and IS now an edge —
// record_construction_edge. That was the Megastruct/Camera gap on Pounce.mara:83.)
cg_compute_reachability :: proc(g: ^Call_Graph) {
    resize(&g.reachable, len(g.nodes))
    root := -1
    for s, i in g.nodes {
        if s.source_name == "main" { root = i; break }
    }
    if root < 0 { return }
    stack: [dynamic]int
    defer delete(stack)
    append(&stack, root)
    g.reachable[root] = true
    for len(stack) > 0 {
        v := pop(&stack)
        for w in g.out_edges[v] {
            if !g.reachable[w] {
                g.reachable[w] = true
                append(&stack, w)
            }
        }
    }
}

// True when node `n` is recursive: it's in a multi-node SCC (mutual recursion)
// or has a self-edge (direct recursion). A leaf of the bottom-up framework.
cg_is_recursive :: proc(g: ^Call_Graph, n: int) -> bool {
    if len(g.sccs[g.scc_of[n]]) > 1 { return true }
    for w in g.out_edges[n] { if w == n { return true } }
    return false
}

// --- Interprocedural summary framework -------------------------------------
// The bottom-up engine every summary pass shares. `transfer(g, node)` recomputes
// a node's summary from its callees' summaries and returns whether it changed.
// SCCs are visited callees-first (reverse-topo order Tarjan already produced),
// so a node's callees are final before it's reached; a non-trivial SCC iterates
// to a fixpoint. Each analysis supplies a state array on the Call_Graph and a
// monotone transfer — the recursion/cycle handling that fun_return_arg_set
// hand-rolled with its `-1` guard lives here, once.

cg_bottom_up :: proc(g: ^Call_Graph, transfer: proc(g: ^Call_Graph, node: int) -> bool) {
    for scc in g.sccs {
        if len(scc) == 1 && !cg_is_recursive(g, scc[0]) {
            transfer(g, scc[0])
            continue
        }
        for {
            changed := false
            for node in scc { if transfer(g, node) { changed = true } }
            if !changed { break }
        }
    }
}

// Purity: a function is impure if it directly hits the outside world — an IO
// built-in or a foreign call, seeded into Checker.effectful_callers during
// checking — or transitively calls something that does. Pure functions are
// const-eval candidates. Optimistic seed (pure until proven otherwise) + the
// bottom-up monotone propagation = the transitive verdict.
cg_compute_purity :: proc(g: ^Call_Graph, c: ^Checker) {
    resize(&g.pure, len(g.nodes))
    for s, i in g.nodes {
        // A foreign node has an opaque body — impure by definition.
        g.pure[i] = !(s == nil || s.calling_conv == .C || c.effectful_callers[s])
    }
    cg_bottom_up(g, cg_purity_transfer)
}

@(private="file")
cg_purity_transfer :: proc(g: ^Call_Graph, n: int) -> bool {
    if !g.pure[n] { return false }   // monotone: impurity only grows
    for callee in g.out_edges[n] {
        if !g.pure[callee] { g.pure[n] = false; return true }
    }
    return false
}

// Return-arg-set: which parameter indices each function's return can trace back
// to. The second interprocedural summary on the bottom-up framework. A function's
// set is recomputed from its body (compute_return_arg_set, which reads callees'
// sets via fun_return_arg_set → this graph); cg_bottom_up visits callees-first
// and iterates each SCC to a fixpoint — so a recursive/mutually-recursive
// function gets the precise transitive answer the lazy `pending → nil` guard
// only approximated (conservatively empty). c.cg must already point at `g`.
@(private="file") g_cg_c: ^Checker

cg_compute_return_args :: proc(g: ^Call_Graph, c: ^Checker) {
    g_cg_c = c
    for ts, i in g.nodes {
        if ts != nil && ts.ast != nil { g.stmt_to_node[ts.ast] = i } // node.ast IS the Stmt_Scope key
    }
    resize(&g.return_args, len(g.nodes))
    cg_bottom_up(g, cg_return_args_transfer)
}

@(private="file")
cg_return_args_transfer :: proc(g: ^Call_Graph, n: int) -> bool {
    ts := g.nodes[n]
    if ts == nil || ts.ast == nil { return false } // foreign/no body — empty set
    new_set := compute_return_arg_set(g_cg_c, ts.ast)
    if slice.equal(g.return_args[n], new_set) { return false }
    g.return_args[n] = new_set // monotone: the set only grows toward its fixpoint
    return true
}

// Query a scope's purity verdict (false if it isn't a graph node).
cg_is_pure :: proc(g: ^Call_Graph, s: ^Type_Scope) -> bool {
    if i, ok := g.index_of[s]; ok { return g.pure[i] }
    return false
}

// Pure vs total over SOURCE functions (the ones with bodies — foreign/external
// nodes are impure by definition and aren't "the program's code"). The numbers
// behind the purity quotient printed on a successful build.
cg_purity_stats :: proc(g: ^Call_Graph) -> (pure_n: int, total: int) {
    for s, i in g.nodes {
        if s == nil { continue }
        if _, src := s.origin.(Origin_Source); !src { continue }
        total += 1
        if g.pure[i] { pure_n += 1 }
    }
    return
}

// Diagnostic: `MARA_DUMP_PURITY=1` prints each function's purity verdict. The
// framework has no real consumer yet, so this is how the result is inspected.
cg_dump_purity :: proc(g: ^Call_Graph) {
    env_buf: [8]u8
    if os.get_env_buf(env_buf[:], "MARA_DUMP_PURITY") == "" { return }
    fmt.eprintln("--- call-graph purity ---")
    for s, i in g.nodes {
        name := s.source_name if s.source_name != "" else s.name
        fmt.eprintf("  %-30s %s\n", name, g.pure[i] ? "pure" : "impure")
    }
}

// --- Tarjan's strongly-connected-components (recursive: recursion goes to call
// --- graph DEPTH, which is shallow, not node count). ------------------------

@(private="file")
Tarjan :: struct {
    g:        ^Call_Graph,
    index:    []int,
    lowlink:  []int,
    on_stack: []bool,
    stack:    [dynamic]int,
    counter:  int,
}

cg_compute_sccs :: proc(g: ^Call_Graph) {
    n := len(g.nodes)
    resize(&g.scc_of, n)
    t := Tarjan{ g = g, index = make([]int, n), lowlink = make([]int, n), on_stack = make([]bool, n) }
    defer { delete(t.index); delete(t.lowlink); delete(t.on_stack); delete(t.stack) }
    for i in 0 ..< n { t.index[i] = -1 }
    for v in 0 ..< n {
        if t.index[v] == -1 { cg_strongconnect(&t, v) }
    }
}

@(private="file")
cg_strongconnect :: proc(t: ^Tarjan, v: int) {
    t.index[v]   = t.counter
    t.lowlink[v] = t.counter
    t.counter   += 1
    append(&t.stack, v)
    t.on_stack[v] = true

    for w in t.g.out_edges[v] {
        if t.index[w] == -1 {
            cg_strongconnect(t, w)
            t.lowlink[v] = min(t.lowlink[v], t.lowlink[w])
        } else if t.on_stack[w] {
            t.lowlink[v] = min(t.lowlink[v], t.index[w])
        }
    }

    // v is an SCC root: pop the stack down to v, that's one component.
    if t.lowlink[v] == t.index[v] {
        scc_id := len(t.g.sccs)
        comp: [dynamic]int
        for {
            w := pop(&t.stack)
            t.on_stack[w] = false
            t.g.scc_of[w] = scc_id
            append(&comp, w)
            if w == v { break }
        }
        append(&t.g.sccs, comp)
    }
}
