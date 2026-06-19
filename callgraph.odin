package mara

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
    cg_compute_sccs(&g)
    return g
}

// True when node `n` is recursive: it's in a multi-node SCC (mutual recursion)
// or has a self-edge (direct recursion). A leaf of the bottom-up framework.
cg_is_recursive :: proc(g: ^Call_Graph, n: int) -> bool {
    if len(g.sccs[g.scc_of[n]]) > 1 { return true }
    for w in g.out_edges[n] { if w == n { return true } }
    return false
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
