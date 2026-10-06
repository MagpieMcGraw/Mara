package mara

import "core:fmt"
import "core:os"
import "core:slice"

// ---------------------------------------------------------------------------
// Materialized call graph (design/mara_ask.md §12)
//
// A post-check artifact on Checked_Program, an index over the calls the
// checker annotated (annot.odin: each call's callee, where its node is, what
// its params receive). Nodes are the program's callable scopes (funs +
// ctors); edges are calls and constructions; the strongly-connected components
// are computed once here (Tarjan).
//
// The SCCs are the prize, not the skeleton: they are the shared cycle/recursion
// structure every interprocedural summary pass (escape, purity, return deps)
// would otherwise hand-roll. Every source function is a node, a call-free one
// too. A call through a function value is no edge (§12 "one honest seam").
// ---------------------------------------------------------------------------

// One directed edge of the call graph: `from` calls `to`.
Call_Edge :: struct {
    from: ^Type_Scope,
    to:   ^Type_Scope,
}

Call_Graph :: struct {
    nodes:     [dynamic]^Type_Scope,   // node id -> the callable scope
    index_of:  map[^Type_Scope]int,    // scope -> node id
    out_edges: [dynamic][dynamic]int,  // node id -> callee node ids
    edge_line: map[Call_Edge]int,      // (caller,callee) scope edge -> first call-site line (call order)

    // Strongly-connected components. scc_of[node] = its component id; sccs[id] =
    // that component's member node ids. Tarjan emits components in REVERSE
    // topological order, so iterating sccs[] front-to-back visits callees before
    // callers — the order a bottom-up summary pass wants.
    scc_of:    [dynamic]int,
    sccs:      [dynamic][dynamic]int,


    // Purity summary (cg_compute_purity): pure[n] == false means the function
    // directly or transitively hits the outside world (IO / foreign). The first
    // interprocedural summary computed via the bottom-up framework below.
    pure:      [dynamic]bool,

    // Return-DEP summary (cg_compute_return_deps): return_deps[n] = the sorted set
    // of parameter indices node n's return value is computed from: its data and
    // the branches that decide it (vs the escape summary's narrower ALIASING
    // relation). A value computed from a param —
    // `obj_get_directions(dir)` returning `mat4_from_quat(dir)[2].xyz` — depends on
    // `dir` without pointing into it. The `ask` slicer crosses calls with THIS set
    // so a call contributes the args its result is computed from. Built the first
    // time a slice crosses a call (deps_ready).
    return_deps:  [dynamic][]int,
    deps_ready:   bool,

    // Escape summary (escape.odin): which parameters node n's result may point
    // into, and which parameter's memory each parameter may be stored into.
    esc:          [dynamic]Esc_Summary,
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

// The call graph from the annotations: an edge for each annotated callee —
// a written call, a construction, an operator through `overload` — from the
// function the call runs in (cg_runs_in). A call's line is its node's; a
// default argument's call gives none in the caller. A fun hits the outside
// world directly when it calls a foreign fun or prints: the seed of the
// purity summary.
build_call_graph :: proc(checked: ^Checked_Program) -> Call_Graph {
    g: Call_Graph
    rc := cg_runs_make(checked.annot, &build_tree)
    defer cg_runs_free(&rc)
    effectful: map[^Type_Scope]bool
    defer delete(effectful)
    a := checked.annot
    t := &build_tree
    keys := make([dynamic]Syntax_Id, 0, len(a.callees), context.temp_allocator)
    for key in a.callees { append(&keys, key) }
    slice.sort(keys[:])   // (a node order that doesn't hang on the map's)
    for key in keys {
        // (A call through a fun's value runs whatever it holds: no edge, the one
        // honest seam.)
        if a.forms[key] == .Value { continue }
        callee := a.callees[key]
        callers, implied := cg_runs_in(&rc, key)
        for caller in callers {
            from, to := cg_node(&g, caller), cg_node(&g, callee)
            if !slice.contains(g.out_edges[from][:], to) { append(&g.out_edges[from], to) }
            if callee.calling_conv == .C { effectful[caller] = true }
            // Call order: the first line calling it. A default argument is
            // written in the callee, so it gives no line in the caller.
            if implied { continue }
            edge := Call_Edge{from = caller, to = callee}
            line := span_line(tree_span(t, Tree_Id(u64(key) & 0xffff_ffff)))
            if cur, ok := g.edge_line[edge]; !ok || line < cur { g.edge_line[edge] = line }
        }
    }
    for key, form in a.forms {
        if form != .Builtin || !cg_prints(t, Tree_Id(u64(key) & 0xffff_ffff)) { continue }
        callers, _ := cg_runs_in(&rc, key)
        for caller in callers { effectful[caller] = true }
    }
    // Every source function a node, a call-free one (neither calls nor is
    // called) too: the purity count is of all of them. Foreign and intrinsic
    // ones have no body to analyze.
    for _, cs in checked.functions {
        if _, is_source := cs.origin.(Origin_Source); is_source && cs != nil {
            cg_node(&g, cs)
        }
    }
    cg_compute_sccs(&g)

    cg_compute_purity(&g, effectful)
    cg_dump_purity(&g)
    return g
}

// Whether a builtin call prints: `print`, `print_cstr`, `print_int`,
// `print_float`.
@(private="file")
cg_prints :: proc(t: ^Tree, n: Tree_Id) -> bool {
    name: string
    #partial switch t.tag[n] {
    case .Call:        name = token_text(build_tokens[t.main[n]])
    case .Method_Call: name = token_text(build_tokens[method_view(t, n).name])
    case:              return false
    }
    switch name {
    case "print", "print_cstr", "print_int", "print_float": return true
    }
    return false
}

// Where code runs: each node's innermost body or constant value the checker
// checked (Annotations.bodies), by instance; and each default argument a
// call takes, with those calls (Annotations.args).
@(private="file")
Cg_Runs :: struct {
    a:          ^Annotations,
    owner:      map[Instance_Id][]i32,            // an instance's nodes → each one's innermost body (in a.bodies); -1: none
    in_default: map[Tree_Id]Tree_Id,              // a default argument's nodes → the innermost default each is in
    defaults:   map[Tree_Id][dynamic]Syntax_Id,   // a default's node → the calls that take it
    callers:    map[Tree_Id][]^Type_Scope,        // ... the functions it runs in, once found
}

@(private="file")
cg_runs_make :: proc(a: ^Annotations, t: ^Tree) -> Cg_Runs {
    rc := Cg_Runs{a = a}
    // (The widest first: a nested body's nodes are its own.)
    Sized :: struct { size: Tree_Id, i: int }
    sized := make([]Sized, len(a.bodies), context.temp_allocator)
    for b, i in a.bodies { sized[i] = {b.hi - b.lo, i} }
    slice.sort_by(sized, proc(x, y: Sized) -> bool { return x.size > y.size })
    for s in sized {
        b := a.bodies[s.i]
        inst := a.instances[b.inst]
        owner, made := rc.owner[b.inst]
        if !made {
            owner = make([]i32, int(inst.hi - inst.lo) + 1)
            slice.fill(owner, -1)
            rc.owner[b.inst] = owner
        }
        for n in b.lo ..= b.hi { owner[n - inst.lo] = i32(s.i) }
    }
    for key, args in a.args {
        for arg in args {
            if arg.kind != .Default || arg.node == 0 { continue }
            list := rc.defaults[arg.node]
            if !slice.contains(list[:], key) { append(&list, key) }
            rc.defaults[arg.node] = list
        }
    }
    Range :: struct { lo, d: Tree_Id }
    ranges := make([dynamic]Range, 0, len(rc.defaults), context.temp_allocator)
    for d in rc.defaults { append(&ranges, Range{tree_lo(t, d), d}) }
    slice.sort_by(ranges[:], proc(x, y: Range) -> bool { return x.d - x.lo > y.d - y.lo })
    for r in ranges { for n in r.lo ..= r.d { rc.in_default[n] = r.d } }
    return rc
}

@(private="file")
cg_runs_free :: proc(rc: ^Cg_Runs) {
    for _, owner in rc.owner { delete(owner) }
    for _, list in rc.defaults { delete(list) }
    for _, c in rc.callers { delete(c) }
    delete(rc.owner); delete(rc.in_default); delete(rc.defaults); delete(rc.callers)
}

// The functions a node runs in: in a default argument, each function whose
// call takes it (`implied`); else the fun or struct whose body is innermost
// around it, in its instance — none, in a constant's value or outside any
// body.
@(private="file")
cg_runs_in :: proc(rc: ^Cg_Runs, key: Syntax_Id) -> (callers: []^Type_Scope, implied: bool) {
    inst, n := Instance_Id(u64(key) >> 32), Tree_Id(u64(key) & 0xffff_ffff)
    if def, in_default := rc.in_default[n]; in_default {
        if found, ok := rc.callers[def]; ok { return found, true }
        rc.callers[def] = nil   // (a default that takes itself: none more)
        out: [dynamic]^Type_Scope
        calls, _ := rc.defaults[def]
        for call in calls {
            cs, _ := cg_runs_in(rc, call)
            for c in cs { if !slice.contains(out[:], c) { append(&out, c) } }
        }
        rc.callers[def] = out[:]
        return out[:], true
    }
    owner, _ := rc.owner[inst]
    lo := rc.a.instances[inst].lo
    if n < lo || int(n - lo) >= len(owner) || owner[n - lo] < 0 { return nil, false }
    b := rc.a.bodies[owner[n - lo]]
    if b.scope == nil { return nil, false }
    out := make([]^Type_Scope, 1, context.temp_allocator)
    out[0] = b.scope
    return out, false
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
// monotone transfer; the recursion and cycle handling lives here, once.

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
// built-in or a foreign call, the seeds build_call_graph collects — or
// transitively calls something that does. Pure functions are
// const-eval candidates. Optimistic seed (pure until proven otherwise) + the
// bottom-up monotone propagation = the transitive verdict.
cg_compute_purity :: proc(g: ^Call_Graph, effectful: map[^Type_Scope]bool) {
    resize(&g.pure, len(g.nodes))
    for s, i in g.nodes {
        // A foreign node has an opaque body — impure by definition.
        g.pure[i] = !(s == nil || s.calling_conv == .C || effectful[s])
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

@(private="file") g_cg_checked: ^Checked_Program

// Return-dep set: which parameter indices each function's result is computed
// from (slice_return_deps, a slice over the program graph from its returns).
// A construction's Self is computed from every argument, an intrinsic's result
// too; a fun with no body in the program (foreign) has none, and its callers
// take every argument. A summary on the bottom-up framework: callees first,
// each SCC to a fixpoint. Only `mara ask` reads it, so it is built the first
// time a slice crosses a call.
cg_compute_return_deps :: proc(g: ^Call_Graph, checked: ^Checked_Program) {
    g.deps_ready = true   // the fixpoint below reads the sets it is building
    g_cg_checked = checked
    resize(&g.return_deps, len(g.nodes))
    cg_bottom_up(g, cg_return_deps_transfer)
    cg_dump_return_deps(g)
}

@(private="file")
cg_return_deps_transfer :: proc(g: ^Call_Graph, n: int) -> bool {
    ts := g.nodes[n]
    if ts == nil || !scope_is_written(ts) { return false }
    new_set: []int
    if ts.kind == .Struct || scope_is_intrinsic(ts) {
        count := len(ts.params)
        if ts.kind == .Struct && count == 0 { count = len(ts.fields) }   // positional args are its fields
        if count > 0 {
            new_set = make([]int, count)
            for &x, i in new_set { x = i }
        }
    } else {
        new_set = slice_return_deps(g_cg_checked, ts)
    }
    if slice.equal(g.return_deps[n], new_set) { return false }
    g.return_deps[n] = new_set   // monotone: the set only grows toward its fixpoint
    return true
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

// Diagnostic: `MARA_DUMP_RETURN_DEPS=1` prints each function's return-dependency
// summary, once a slice has built it.
cg_dump_return_deps :: proc(g: ^Call_Graph) {
    env_buf: [8]u8
    if os.get_env_buf(env_buf[:], "MARA_DUMP_RETURN_DEPS") == "" { return }
    for s, i in g.nodes {
        if s == nil { continue }
        fmt.eprintf("  %-40s %v\n", s.name, g.return_deps[i])
    }
}
