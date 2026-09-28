package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Escape analysis — Mara's lifetime rule, checked over the program graph
// (design/graph_retrofit.md, phase 2).
//
// DEPTHS. All memory has a lifetime depth: global memory is 0, the caller's
// memory 1, and each block of the function being checked one more (its body
// is 2, a loop's variables 3, the loop's body 4). A deeper block dies first —
// and in Mara it really does die: the scope allocator resets when the block
// ends. A variable lives at its declaration's depth; a struct's fields are
// its caller's.
//
// ROOTS. A reference value carries the set of memory it may point into
// (Esc_Roots): global memory, a parameter's caller memory (by index), a
// variable's own storage (a synthetic local — an expression's temporary —
// included), and a value's own storage when an array decays to a slice of it
// in place.
//
// THE RULE. A store is legal only when everything the value may point into
// outlives everything the destination may be:
//
//     deepest(value roots) <= shallowest(destination roots)
//
// A return is a store into the caller. Every operation computes its roots
// from its operands': a place's are the storage it names, a read's what that
// storage holds, an address's the place itself. Storing into a variable's
// storage adds to what it holds, so reading it back — directly, through a
// field or an element, or through a pointer to it — carries those roots
// onward. That one check is the whole analysis: returns, writes through
// parameters at any field/element depth, writes through aliases of
// parameters, reassigned locals, and values outliving an inner block all
// fall out of it.
//
// FLOW. What each variable holds is dataflow over the runs: a write of the
// whole variable replaces it, a write of part of it (or through a pointer)
// adds to it, a join unions, and a loop iterates to its fixpoint. A defer's
// block starts from the state at every exit that runs it, and what it leaves
// joins back in there. A `let` view and a match arm's binding have no storage
// of their own: they name the storage they view.
//
// SUMMARIES. Inside a callee all caller memory is depth 1, so a callee can't
// tell a long-lived argument from a short-lived one. Instead each function's
// summary records which parameters its result may point into, and which
// parameter's memory each parameter may be stored into. Summaries are
// computed callees-first over the call graph's SCCs (cg_bottom_up iterates
// recursion to a fixpoint) and applied at every call and construction with
// the caller's real depths. A summary keeps two levels per parameter — the
// memory the argument points at, and anything deeper — so storing into `h.p`
// isn't confused with storing into `h.p^`. Foreign and indirect calls are the
// honest seam: assumed not to retain their arguments.
// ---------------------------------------------------------------------------

ESC_GLOBAL       :: 0
ESC_CALLER       :: 1
ESC_BODY         :: 2
ESC_STORE_GLOBAL :: -1
ESC_MAX_PARAMS   :: 128

Esc_Param_Set :: bit_set[0 ..< ESC_MAX_PARAMS; u128]

// The memory a reference value may point into.
Esc_Roots :: struct {
    params: Esc_Param_Set,   // the caller memory these parameters point at
    deep:   Esc_Param_Set,   // caller memory reachable further through them
    global: bool,
    temp:   int,             // deepest block holding a value it views in place; 0 = none
    vars:   [dynamic]i32,    // variables' own storage, by index in the fun's
}

// A parameter's memory stored into another's (a function-summary edge): memory
// reachable from `src` may end up referenced from memory reachable from `dst`.
Esc_Store :: struct {
    dst:      int,  // ESC_STORE_GLOBAL: into global memory
    dst_deep: bool,
    src:      int,
    src_deep: bool,
}

Esc_Summary :: struct {
    ret:      Esc_Param_Set, // the result may point at what these arguments point at
    ret_deep: Esc_Param_Set, // ... or at anything reachable through them
    stores:   [dynamic]Esc_Store,
}

// A variable of the fun or struct being checked: a param, a named result, a
// local (synthetic ones too), or — in a struct's code — a field.
@(private="file")
Esc_Var :: struct {
    node:  Node_Id,
    name:  string,
    type_: Type,
    depth: int,
    param: int,       // its position when a param; -1 otherwise
    slot:  int,       // its entry in a state; -1 when it can hold no reference
    view:  bool,      // a `let` view or a match arm's binding: its slot holds
                      // the storage it names, not what it holds
    init:  Node_Id,   // a `let` view: the write declaring it
}

// Where a store lands, for its diagnostic.
@(private="file")
Esc_Site :: struct {
    op:     Node_Id,      // the write, or the call whose summary stores
    place:  Operand,      // a write's destination
    callee: ^Type_Scope,  // a call's
    st:     Esc_Store,
}

@(private="file")
Esc_Diag :: struct {
    span: Span,
    msg:  string,
}

// One walk of one fun's or struct's code.
@(private="file")
Esc :: struct {
    c:      ^Checker,
    cg:     ^Call_Graph,
    g:      ^Program_Graph,
    ft:     ^Type_Scope,
    node:   Node_Id,
    ctor:   bool,                // a struct's code: `Self` is its fields
    vars:   [dynamic]Esc_Var,
    var_of: []i32,               // a declaration → its variable, by id - node; -1 for none
    run_of: []i32,               // an operation → its run's position in `runs`, by id - node
    slots:  int,
    runs:   [dynamic]i32,        // its code's runs, then its defer blocks'
    main:   int,                 // how many of `runs` are its code's own
    run_at: map[i32]int,
    memo:   []Esc_Roots,         // each operation's roots, by id - node

    // The fixpoint.
    in_state:    [][]Esc_Roots,
    entered:     []bool,
    queued:      []bool,
    todo:        [dynamic]int,
    uses:        map[Node_Id][dynamic]int,    // an operation → the other runs using its value
    used_across: []bool,                      // ... whether it has any, by id - node
    defer_exit:  map[Node_Id][]Esc_Roots,     // a defer block → the state it leaves
    defer_users: map[Node_Id][dynamic]int,    // ... and the runs that run it

    // The last pass, over the fixpoint: summary and diagnostics.
    final:  bool,
    report: bool,
    sum:    Esc_Summary,
    diags:  [dynamic]Esc_Diag,
}

@(private="file")
Esc_Pass :: struct {
    c:        ^Checker,
    graph:    ^Program_Graph,
    starts:   map[Node_Id]i32,
    reported: []bool,
    diags:    [dynamic]Esc_Diag,
}

@(private="file") g_esc: Esc_Pass

// Entry point, after build_call_graph: summaries bottom-up, each fun's
// diagnostics against its callees' final summaries. A fun outside recursion
// reports in its summary walk; a recursive one walks again once its SCC is
// done, with the summaries final.
escape_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program) {
    cg := c.cg
    if cg == nil { return }
    resize(&cg.esc, len(cg.nodes))
    g_esc = Esc_Pass{
        c        = c,
        graph    = &checked.graph,
        starts   = graph_run_starts(&checked.graph),
        reported = make([]bool, len(cg.nodes)),
    }
    cg_bottom_up(cg, esc_summary_transfer)
    esc_dump(cg)
    for _, n in cg.nodes {
        if !g_esc.reported[n] { esc_walk(cg, n, true) }
    }
    // In source order, once each (a generic's instances share their spans).
    slice.sort_by(g_esc.diags[:], proc(a, b: Esc_Diag) -> bool {
        if a.span.file != b.span.file { return a.span.file < b.span.file }
        if a.span.line != b.span.line { return a.span.line < b.span.line }
        if a.span.col != b.span.col { return a.span.col < b.span.col }
        return a.msg < b.msg
    })
    for d, i in g_esc.diags {
        if i > 0 && g_esc.diags[i - 1] == d { continue }
        check_error(c, d.span, "%s", d.msg)
    }
}

@(private="file")
esc_summary_transfer :: proc(cg: ^Call_Graph, n: int) -> bool {
    report := !cg_is_recursive(cg, n)
    s, ok := esc_walk(cg, n, report)
    if report || !ok { g_esc.reported[n] = true }
    if !ok { return false }
    cur := &cg.esc[n]
    changed := false
    if !(s.ret <= cur.ret)           { cur.ret += s.ret; changed = true }
    if !(s.ret_deep <= cur.ret_deep) { cur.ret_deep += s.ret_deep; changed = true }
    for st in s.stores {
        if !slice.contains(cur.stores[:], st) { append(&cur.stores, st); changed = true }
    }
    return changed // monotone: summaries only grow toward the fixpoint
}

// Walk call-graph node n's code: the fixpoint, then the last pass. False when
// it has no code (foreign, intrinsic).
@(private="file")
esc_walk :: proc(cg: ^Call_Graph, n: int, report: bool) -> (Esc_Summary, bool) {
    ft := cg.nodes[n]
    g := g_esc.graph
    node, has := g.scope_node[ft]
    if !has { return {}, false }
    e := Esc{c = g_esc.c, cg = cg, g = g, ft = ft, node = node, ctor = g.kind[node] == .Struct, report = report}
    e.main = graph_code_runs(g, g_esc.starts, node, &e.runs)
    if len(e.runs) == 0 { return {}, false }
    if len(ft.params) > ESC_MAX_PARAMS {
        fmt.panicf("escape analysis: %s has %d parameters (max %d)", ft.name, len(ft.params), ESC_MAX_PARAMS)
    }
    size := int(g.last[node] - node) + 1
    e.memo = make([]Esc_Roots, size)
    e.var_of = make([]i32, size)
    e.run_of = make([]i32, size)
    e.used_across = make([]bool, size)
    slice.fill(e.var_of, -1)
    slice.fill(e.run_of, -1)
    esc_vars(&e)
    esc_scan(&e)
    esc_fixpoint(&e)

    e.final = true
    state := make([]Esc_Roots, e.slots)
    for ri in 0 ..< len(e.runs) {
        if !e.entered[ri] { continue }
        esc_state_copy(state, e.in_state[ri])
        esc_run(&e, ri, state)
    }
    if report { append(&g_esc.diags, ..e.diags[:]) }
    return e.sum, true
}

// The variables: its own subtree's params, results, locals and (a struct's)
// fields, less the subtrees of what it defines.
@(private="file")
esc_vars :: proc(e: ^Esc) {
    g := e.g
    params := 0
    for id := e.node + 1; id <= g.last[e.node]; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct, .Union, .Enum:
            id = g.last[id]
        case .Param, .Result, .Local, .Field:
            v := Esc_Var{node = id, name = g.name[id], type_ = g.type_[id], depth = esc_depth(e, id),
                         param = -1, slot = -1, init = NO_NODE}
            #partial switch g.kind[id] {
            case .Param:
                v.param = params
                params += 1
            case .Field:
                v.depth = ESC_CALLER   // a field of the value under construction: the caller's
            }
            e.var_of[id - e.node] = i32(len(e.vars))
            append(&e.vars, v)
        }
    }
}

// Before the walk: which variables are views, which values cross runs, and
// each variable's slot.
@(private="file")
esc_scan :: proc(e: ^Esc) {
    g := e.g
    for r, ri in e.runs {
        e.run_at[r] = ri
        for op in graph_run(g, int(r)) { e.run_of[op - e.node] = i32(ri) }
    }
    for r, ri in e.runs {
        for op in graph_run(g, int(r)) {
            ops := graph_operands(g, op)
            for o in ops {
                if o.op == NO_NODE { continue }
                if from := e.run_of[o.op - e.node]; from != i32(ri) {
                    e.used_across[o.op - e.node] = true
                    if o.op not_in e.uses { e.uses[o.op] = {} }
                    list := &e.uses[o.op]
                    if !slice.contains(list[:], ri) { append(list, ri) }
                }
            }
            #partial switch g.op[op] {
            case .Write:
                k := esc_var_named(e, ops[0])
                val := ops[1].op
                if k < 0 || val == NO_NODE { break }
                v := &e.vars[k]
                s := g.stmt[op]
                if g.op[val] == .Carve && g.name[val] == "let" && s >= 0 && g.stmts[s].kind == .Decl {
                    v.view = true   // `x := let(T, s)`: x IS the storage it views
                    v.init = op
                }
            case .Variant:
                // A match arm's binding is the payload's place, not a copy.
                if k := esc_var(e, g.refers[op]); k >= 0 { e.vars[k].view = true }
            }
        }
    }
    for &v in e.vars {
        if v.view || esc_has_refs(e.c, v.type_) {
            v.slot = e.slots
            e.slots += 1
        }
    }
}

// --- the fixpoint --------------------------------------------------------------

@(private="file")
esc_fixpoint :: proc(e: ^Esc) {
    n := len(e.runs)
    e.in_state = make([][]Esc_Roots, n)
    e.entered = make([]bool, n)
    e.queued = make([]bool, n)
    // The entry: each param holds the caller memory it points at.
    entry := make([]Esc_Roots, e.slots)
    for v in e.vars {
        if v.param >= 0 && v.slot >= 0 && !v.view { entry[v.slot].params = {v.param} }
    }
    e.in_state[0] = entry
    e.entered[0] = true
    esc_queue(e, 0)
    state := make([]Esc_Roots, e.slots)
    visits := 0
    for len(e.todo) > 0 {
        ri := pop(&e.todo)
        e.queued[ri] = false
        esc_state_copy(state, e.in_state[ri])
        esc_run(e, ri, state)
        visits += 1
        if visits > 10_000_000 { fmt.panicf("escape analysis: %s did not converge", e.ft.name) }
    }
}

@(private="file")
esc_queue :: proc(e: ^Esc, ri: int) {
    if e.queued[ri] { return }
    e.queued[ri] = true
    append(&e.todo, ri)
}

// Join a state into run si's.
@(private="file")
esc_flow :: proc(e: ^Esc, si: int, state: []Esc_Roots) {
    if !e.entered[si] {
        e.entered[si] = true
        e.in_state[si] = make([]Esc_Roots, e.slots)
        esc_state_copy(e.in_state[si], state)
        esc_queue(e, si)
        return
    }
    if esc_merge(e.in_state[si], state) { esc_queue(e, si) }
}

@(private="file")
esc_run :: proc(e: ^Esc, ri: int, state: []Esc_Roots) {
    g := e.g
    ops := graph_run(g, int(e.runs[ri]))
    for op in ops { esc_op(e, ri, op, state) }
    if e.final { return }
    last := ops[len(ops) - 1]
    for edge in graph_out(g, last) {
        if edge.kind != .Then { continue }
        if si, ok := e.run_at[g_esc.starts[edge.to]]; ok { esc_flow(e, si, state) }
    }
    // The end of a defer's block: what it leaves joins back in where it ran.
    if g.op[last] == .Return && ri >= e.main {
        d := esc_defer_block(g, last)
        if d not_in e.defer_exit { e.defer_exit[d] = make([]Esc_Roots, e.slots) }
        if esc_merge(e.defer_exit[d], state) {
            for u in e.defer_users[d] { esc_queue(e, u) }
        }
    }
}

// The defer block whose code an operation ends: the scope its code is entered from.
@(private="file")
esc_defer_block :: proc(g: ^Program_Graph, op: Node_Id) -> Node_Id {
    for p := g.parent[op]; p != NO_NODE; p = g.parent[p] {
        for edge in graph_out(g, p) { if edge.kind == .Then { return p } }
    }
    return NO_NODE
}

@(private="file")
esc_run_defer :: proc(e: ^Esc, ri: int, op: Node_Id, state: []Esc_Roots) {
    g := e.g
    for edge in graph_out(g, op) {
        if edge.kind != .Runs { continue }
        d := edge.to
        if !e.final {
            if d not_in e.defer_users { e.defer_users[d] = {} }
            users := &e.defer_users[d]
            if !slice.contains(users[:], ri) { append(users, ri) }
            for entry in graph_out(g, d) {
                if entry.kind != .Then { continue }
                if si, ok := e.run_at[g_esc.starts[entry.to]]; ok { esc_flow(e, si, state) }
            }
        }
        if exit, ok := e.defer_exit[d]; ok { esc_merge(state, exit) }
    }
}

// --- operations ----------------------------------------------------------------

// Run one operation: its roots into the memo, its effects on the state.
@(private="file")
esc_op :: proc(e: ^Esc, ri: int, op: Node_Id, state: []Esc_Roots) {
    g := e.g
    ops := graph_operands(g, op)
    // A value another run uses: when it grows, that run goes again.
    watched := !e.final && e.used_across[op - e.node]
    old: Esc_Roots
    if watched { esc_join(&old, e.memo[op - e.node]) }
    r := &e.memo[op - e.node]
    esc_clear(r)
    #partial switch g.op[op] {
    case .Var:
        esc_var_roots(e, r, op, state)
    case .Global:
        r.global = true
    case .Field, .Swizzle:
        esc_join(r, esc_at(e, ops[0]))
    case .Variant:
        esc_join(r, esc_at(e, ops[0]))
        if k := esc_var(e, g.refers[op]); k >= 0 { esc_copy(&state[e.vars[k].slot], r^) }
    case .Index, .View:
        esc_mem(e, r, ops[0], state)
    case .Slice:
        if g.name[op] == "slice_from_ptr" {   // may view any argument
            for o in ops { esc_join(r, esc_at(e, o)) }
        } else {
            esc_mem(e, r, ops[0], state)
        }
    case .Deref:
        esc_deref(e, r, esc_at(e, ops[0]), state)
    case .Read:
        if esc_has_refs(e.c, g.type_[op]) { esc_deref(e, r, esc_at(e, ops[0]), state) }
    case .Address:
        esc_join(r, esc_at(e, ops[0]))
    case .Arith, .Compare, .Unary, .Cast:
        if esc_has_refs(e.c, g.type_[op]) {
            for o in ops { esc_join(r, esc_at(e, o)) }
        }
    case .Carve:
        // let(T, s) reads a T out of s's memory; slice(..., s) views it.
        mem: Esc_Roots
        esc_mem(e, &mem, ops[0], state)
        if g.name[op] != "let" {
            esc_join(r, mem)
        } else if esc_has_refs(e.c, g.type_[op]) {
            esc_deref(e, r, mem, state)
        }
    case .Call:
        if callee := esc_callee(e, op); callee != nil {
            esc_call(e, r, op, callee, ops, state)
        } else {
            // Through a function value (the first operand): may view any argument.
            for o in ops[1:] { esc_join(r, esc_at(e, o)) }
        }
    case .Construct:
        // Into its destination (the first operand); a union variant has no
        // constructor and holds nothing yet.
        val: Esc_Roots
        if callee := esc_callee(e, op); callee != nil { esc_call(e, &val, op, callee, ops[1:], state) }
        esc_write(e, op, ops[0], val, state)
    case .Zero:
        // `s : [:n]T` (a capacity): s views storage that lives as long as s
        // does, so for its lifetime, s's own.
        val: Esc_Roots
        if len(ops) > 1 {
            if k := esc_var_named(e, ops[0]); k >= 0 { append(&val.vars, i32(k)) }
        }
        esc_write(e, op, ops[0], val, state)
    case .Fill:
        val: Esc_Roots
        if esc_has_refs(e.c, g.type_[ops[0].op]) { esc_join(&val, esc_at(e, ops[1])) }
        esc_write(e, op, ops[0], val, state)
    case .Write:
        esc_write_op(e, op, ops, state)
    case .Byte_Read:
        // A value read out of a byte buffer holds what the buffer's memory does.
        val: Esc_Roots
        if esc_has_refs(e.c, g.type_[ops[0].op]) {
            mem: Esc_Roots
            esc_mem(e, &mem, ops[1], state)
            esc_deref(e, &val, mem, state)
        }
        esc_write(e, op, ops[0], val, state)
    case .Return:
        if e.final && ri < e.main { esc_return_op(e, ri, op, ops, state) }
    case .Run_Defer:
        esc_run_defer(e, ri, op, state)
    }
    if watched && !esc_equal(old, r^) {
        for u in e.uses[op] { esc_queue(e, u) }
    }
}

// A variable's storage. A view names the storage it views; `Self` in a
// struct's code is its fields; anything else is global.
@(private="file")
esc_var_roots :: proc(e: ^Esc, r: ^Esc_Roots, op: Node_Id, state: []Esc_Roots) {
    d := e.g.refers[op]
    if k := esc_var(e, d); k >= 0 {
        v := e.vars[k]
        if v.view {
            esc_join(r, state[v.slot])
        } else {
            append(&r.vars, i32(k))
        }
        return
    }
    if e.ctor && d == e.node {
        for v, k in e.vars { if e.g.kind[v.node] == .Field { append(&r.vars, i32(k)) } }
        return
    }
    r.global = true   // a constant, a function, the program's globals
}

// The variable a declaration is, or -1: its own subtree's only.
@(private="file")
esc_var :: proc(e: ^Esc, d: Node_Id) -> int {
    if d <= e.node || d > e.g.last[e.node] { return -1 }
    return int(e.var_of[d - e.node])
}

// The variable a place operand names directly, or -1.
@(private="file")
esc_var_named :: proc(e: ^Esc, o: Operand) -> int {
    if o.op == NO_NODE || e.g.op[o.op] != .Var { return -1 }
    return esc_var(e, e.g.refers[o.op])
}

@(private="file")
esc_at :: proc(e: ^Esc, o: Operand) -> Esc_Roots {
    if o.op == NO_NODE { return {} }
    return e.memo[o.op - e.node]
}

// The memory holding a place's elements: through a pointer, what it points
// at; through a slice, the data it views; otherwise the place's own storage.
@(private="file")
esc_mem :: proc(e: ^Esc, dst: ^Esc_Roots, place: Operand, state: []Esc_Roots) {
    m := esc_at(e, place)
    #partial switch bt in distinct_base(e.g.type_[place.op]) {
    case ^Type_Ptr:
        pointee: Esc_Roots
        esc_deref(e, &pointee, m, state)
        if _, to_slice := distinct_base(bt.elem).(^Type_Slice); to_slice {
            esc_slice_data(e, dst, pointee, state)
        } else {
            esc_join(dst, pointee)
        }
    case ^Type_Slice:
        esc_slice_data(e, dst, m, state)
    case:
        esc_join(dst, m)
    }
}

// --- stores --------------------------------------------------------------------

@(private="file")
esc_write_op :: proc(e: ^Esc, op: Node_Id, ops: []Operand, state: []Esc_Roots) {
    dest, val := ops[0], ops[1]
    if k := esc_var_named(e, dest); k >= 0 && e.vars[k].view && e.vars[k].init == op {
        // `x := let(T, s)`: x names s's memory.
        at: Esc_Roots
        esc_mem(e, &at, graph_operands(e.g, val.op)[0], state)
        esc_copy(&state[e.vars[k].slot], at)
        return
    }
    if e.g.op[dest.op] == .Slice {
        // `dst[lo:hi] = src`: src's elements copied into the ones the slice views.
        elems := esc_elems(e, val, index_elem_type(e.g.type_[dest.op]), state)
        esc_store(e, Esc_Site{op = op, place = dest}, esc_at(e, dest), elems, state)
        return
    }
    esc_write(e, op, dest, esc_into(e, val, e.g.type_[dest.op], state), state)
}

// Store `val` into the place `dest`. A write of a whole variable replaces
// what it holds; anything else adds to what the storage holds.
@(private="file")
esc_write :: proc(e: ^Esc, op: Node_Id, dest: Operand, val: Esc_Roots, state: []Esc_Roots) {
    dst := esc_at(e, dest)
    if k := esc_var_named(e, dest); k >= 0 && !e.vars[k].view {
        esc_check(e, Esc_Site{op = op, place = dest}, dst, val)
        if s := e.vars[k].slot; s >= 0 { esc_copy(&state[s], val) }
        return
    }
    esc_store(e, Esc_Site{op = op, place = dest}, dst, val, state)
}

// Check the rule, then record that the variables in `dst` may now hold what
// `val` points into.
@(private="file")
esc_store :: proc(e: ^Esc, site: Esc_Site, dst, val: Esc_Roots, state: []Esc_Roots) {
    esc_check(e, site, dst, val)
    for k in dst.vars {
        if s := e.vars[k].slot; s >= 0 && !e.vars[k].view { esc_join(&state[s], val) }
    }
}

// THE RULE: everything `val` may point into must outlive everything `dst` may be.
@(private="file")
esc_check :: proc(e: ^Esc, site: Esc_Site, dst, val: Esc_Roots) {
    if !e.final { return }
    if esc_deepest_local(e, val) > esc_shallowest(e, dst) && e.report {
        esc_report_store(e, site, val)
    }
    if val.params == {} && val.deep == {} { return }
    // Caller memory into caller memory can't be judged in here — every parameter
    // is depth 1 to the callee. Summarize it; call sites check it.
    for i in dst.params { esc_record_stores(e, i, false, val) }
    for i in dst.deep   { esc_record_stores(e, i, true, val) }
    if dst.global       { esc_record_stores(e, ESC_STORE_GLOBAL, false, val) }
    // A constructor's field is part of the constructed result.
    for k in dst.vars {
        if e.vars[k].depth == ESC_CALLER {
            e.sum.ret += val.params
            e.sum.ret_deep += val.deep
        }
    }
}

@(private="file")
esc_record_stores :: proc(e: ^Esc, dst: int, dst_deep: bool, val: Esc_Roots) {
    for j in val.params { esc_record(e, Esc_Store{dst, dst_deep, j, false}) }
    for j in val.deep   { esc_record(e, Esc_Store{dst, dst_deep, j, true}) }
}

@(private="file")
esc_record :: proc(e: ^Esc, st: Esc_Store) {
    if !slice.contains(e.sum.stores[:], st) { append(&e.sum.stores, st) }
}

// A return: each value a store into the caller (`?`'s hands back only the err).
@(private="file")
esc_return_op :: proc(e: ^Esc, ri: int, op: Node_Id, ops: []Operand, state: []Esc_Roots) {
    rts := e.ft.return_types
    for o, i in ops {
        k := len(rts) - 1 if len(ops) == 1 && len(rts) > 1 else i
        rt: Type = rts[k] if k < len(rts) else nil
        esc_return(e, ri, op, esc_into(e, o, rt, state), o, state)
    }
}

@(private="file")
esc_return :: proc(e: ^Esc, ri: int, op: Node_Id, val: Esc_Roots, o: Operand, state: []Esc_Roots) {
    e.sum.ret += val.params
    e.sum.ret_deep += val.deep
    if esc_deepest_local(e, val) <= ESC_CALLER || !e.report { return }
    if o.op != NO_NODE && esc_report_call_return(e, ri, op, o, state) { return }
    esc_diag(e, e.g.origin[op], TYPE_CANNOT_RETURN_LOCAL_REFERENCE_MEMORY)
}

// --- values --------------------------------------------------------------------

// A value headed into a destination of type `dest` — the destination decides
// what is actually stored. A fixed or partial array decaying to a slice
// becomes a view of the array's own storage; a slice copied into an array
// copies its elements, not the view; and a destination that can't hold a
// reference stores none, whatever the source.
@(private="file")
esc_into :: proc(e: ^Esc, o: Operand, dest: Type, state: []Esc_Roots) -> Esc_Roots {
    r: Esc_Roots
    if o.op == NO_NODE { return r }
    if dest != nil && !esc_has_refs(e.c, dest) { return r }
    #partial switch db in distinct_base(dest) {
    case ^Type_Slice:
        #partial switch _ in distinct_base(esc_value_type(e, o)) {
        case ^Type_Fixed_Array, ^Type_Partial_Array:
            esc_value_storage(e, &r, o)
            return r
        }
    case ^Type_Fixed_Array:
        return esc_elems(e, o, db.elem, state)
    case ^Type_Partial_Array:
        return esc_elems(e, o, db.elem, state)
    }
    esc_join(&r, esc_at(e, o))
    return r
}

// What copying a value's elements (into elements of type `elem`) stores.
@(private="file")
esc_elems :: proc(e: ^Esc, o: Operand, elem: Type, state: []Esc_Roots) -> Esc_Roots {
    r: Esc_Roots
    if !esc_has_refs(e.c, elem) { return r }
    #partial switch _ in distinct_base(esc_value_type(e, o)) {
    case ^Type_Slice, ^Type_Ptr:
        esc_deref(e, &r, esc_at(e, o), state)   // the elements live where the view points
        return r
    }
    esc_join(&r, esc_at(e, o))   // an array value: its contents are its elements'
    return r
}

// A value's type; a call's later outputs have none recorded.
@(private="file")
esc_value_type :: proc(e: ^Esc, o: Operand) -> Type {
    return e.g.type_[o.op] if o.out == 0 else nil
}

// Where a value sits: a read's place, or else a temporary of the block
// computing it.
@(private="file")
esc_value_storage :: proc(e: ^Esc, r: ^Esc_Roots, o: Operand) {
    if e.g.op[o.op] == .Read {
        esc_join(r, esc_at(e, graph_operands(e.g, o.op)[0]))
    } else {
        r.temp = max(r.temp, esc_depth(e, o.op))
    }
}

// --- calls ---------------------------------------------------------------------

@(private="file")
esc_callee :: proc(e: ^Esc, op: Node_Id) -> ^Type_Scope {
    for edge in graph_out(e.g, op) {
        if edge.kind == .Calls { return e.g.type_[edge.to].(^Type_Scope) }
    }
    return nil
}

@(private="file")
esc_summary_of :: proc(e: ^Esc, callee: ^Type_Scope) -> ^Esc_Summary {
    if callee == nil || callee.calling_conv == .C { return nil }
    if n, ok := e.cg.index_of[callee]; ok && n < len(e.cg.esc) { return &e.cg.esc[n] }
    return nil
}

// A call's result, and its summarized stores applied with this caller's depths.
@(private="file")
esc_call :: proc(e: ^Esc, r: ^Esc_Roots, op: Node_Id, callee: ^Type_Scope, args: []Operand, state: []Esc_Roots) {
    if callee.calling_conv == .C {
        r.global = true // foreign memory
        return
    }
    sum := esc_summary_of(e, callee)
    if sum == nil {
        for a in args { esc_join(r, esc_at(e, a)) }   // unknown: the result may view any argument
        return
    }
    for i in sum.ret      { if i < len(args) { esc_join(r, esc_arg(e, callee, args, i, false, state)) } }
    for i in sum.ret_deep { if i < len(args) { esc_join(r, esc_arg(e, callee, args, i, true, state)) } }
    for st in sum.stores {
        if st.src >= len(args) || st.dst >= len(args) { continue }
        val := esc_arg(e, callee, args, st.src, st.src_deep, state)
        dst: Esc_Roots
        if st.dst == ESC_STORE_GLOBAL {
            dst.global = true
        } else {
            dst = esc_arg(e, callee, args, st.dst, st.dst_deep, state)
        }
        esc_store(e, Esc_Site{op = op, callee = callee, st = st}, dst, val, state)
    }
}

// Argument `i` as the callee's parameter `i` sees it (decay included).
@(private="file")
esc_arg :: proc(e: ^Esc, callee: ^Type_Scope, args: []Operand, i: int, deep: bool, state: []Esc_Roots) -> Esc_Roots {
    pt: Type = callee.params[i].type_ if i < len(callee.params) else nil
    r := esc_into(e, args[i], pt, state)
    return esc_reach(e, r, state) if deep else r
}

// --- roots ---------------------------------------------------------------------

@(private="file")
esc_clear :: proc(r: ^Esc_Roots) {
    r.params, r.deep, r.global, r.temp = {}, {}, false, 0
    clear(&r.vars)
}

@(private="file")
esc_join :: proc(dst: ^Esc_Roots, src: Esc_Roots) -> (changed: bool) {
    if !(src.params <= dst.params) { dst.params += src.params; changed = true }
    if !(src.deep <= dst.deep)     { dst.deep += src.deep; changed = true }
    if src.global && !dst.global   { dst.global = true; changed = true }
    if src.temp > dst.temp         { dst.temp = src.temp; changed = true }
    for k in src.vars {
        if !slice.contains(dst.vars[:], k) { append(&dst.vars, k); changed = true }
    }
    return
}

@(private="file")
esc_copy :: proc(dst: ^Esc_Roots, src: Esc_Roots) {
    esc_clear(dst)
    esc_join(dst, src)
}

@(private="file")
esc_equal :: proc(a, b: Esc_Roots) -> bool {
    if a.params != b.params || a.deep != b.deep || a.global != b.global || a.temp != b.temp { return false }
    if len(a.vars) != len(b.vars) { return false }
    for k in a.vars { if !slice.contains(b.vars[:], k) { return false } }
    return true
}

@(private="file")
esc_state_copy :: proc(dst, src: []Esc_Roots) {
    for &r, i in dst { esc_copy(&r, src[i]) }
}

@(private="file")
esc_merge :: proc(dst, src: []Esc_Roots) -> (changed: bool) {
    for &r, i in dst { if esc_join(&r, src[i]) { changed = true } }
    return
}

// What the memory at `r` may hold: one level of indirection further. Memory
// never holds references to anything shorter-lived than itself (that's the
// rule), so a temporary or global holds nothing deeper than itself, and a
// parameter's memory holds more of the caller's memory.
@(private="file")
esc_deref :: proc(e: ^Esc, dst: ^Esc_Roots, r: Esc_Roots, state: []Esc_Roots) {
    dst.deep += r.params + r.deep
    if r.global { dst.global = true }
    dst.temp = max(dst.temp, r.temp)
    for k in r.vars {
        if s := e.vars[k].slot; s >= 0 && !e.vars[k].view { esc_join(dst, state[s]) }
    }
}

// The data a slice header at `r` points into. A partial array's header points
// into its own inline elements, so it is (also) its own data.
@(private="file")
esc_slice_data :: proc(e: ^Esc, dst: ^Esc_Roots, r: Esc_Roots, state: []Esc_Roots) {
    esc_deref(e, dst, r, state)
    for k in r.vars {
        if esc_self_pointing(e.vars[k].type_) && !slice.contains(dst.vars[:], k) { append(&dst.vars, k) }
    }
}

// Everything reachable from `r`, at any depth of indirection (r included).
@(private="file")
esc_reach :: proc(e: ^Esc, r: Esc_Roots, state: []Esc_Roots) -> Esc_Roots {
    out: Esc_Roots
    esc_join(&out, r)
    for {
        more: Esc_Roots
        esc_slice_data(e, &more, out, state)
        if !esc_join(&out, more) { return out }
    }
}

// Deepest root other than caller memory reached through a parameter; -1 if none.
@(private="file")
esc_deepest_local :: proc(e: ^Esc, r: Esc_Roots) -> int {
    d := -1
    if r.global { d = ESC_GLOBAL }
    if r.temp > 0 { d = max(d, r.temp) }
    for k in r.vars { d = max(d, e.vars[k].depth) }
    return d
}

// Shallowest root, parameters' memory counting as the caller's; max(int) if none.
@(private="file")
esc_shallowest :: proc(e: ^Esc, r: Esc_Roots) -> int {
    d := max(int)
    if r.global { d = ESC_GLOBAL }
    if r.params != {} || r.deep != {} { d = min(d, ESC_CALLER) }
    if r.temp > 0 { d = min(d, r.temp) }
    for k in r.vars { d = min(d, e.vars[k].depth) }
    return d
}

// The lifetime depth of what sits where `id` does: one more than the body for
// each block around it.
@(private="file")
esc_depth :: proc(e: ^Esc, id: Node_Id) -> int {
    d := ESC_BODY
    for p := e.g.parent[id]; p != e.node && p != NO_NODE; p = e.g.parent[p] {
        if e.g.kind[p] == .Block { d += 1 }
    }
    return d
}

// --- types ---------------------------------------------------------------------

@(private="file") g_esc_refs_cache: map[^Type_Scope]bool
@(private="file") g_esc_self_cache: map[^Type_Scope]bool

// Can a value of this type hold a reference? (Unknown: assume it can.)
esc_has_refs :: proc(c: ^Checker, t: Type) -> bool {
    if t == nil { return true }
    #partial switch bt in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice, Type_CString, Type_Any:
        return true
    case ^Type_Fixed_Array:
        return esc_has_refs(c, bt.elem)
    case ^Type_Partial_Array:
        return esc_has_refs(c, bt.elem)
    case ^Type_Union:
        for _, sname in bt.variant_structs {
            if st, ok := c.table.structs[sname]; ok && esc_has_refs(c, st) { return true }
        }
    case ^Type_Scope:
        sd := as_struct_body(bt)
        if sd == nil { return false } // a function value points at code
        if cached, ok := g_esc_refs_cache[bt]; ok { return cached }
        g_esc_refs_cache[bt] = false // terminates recursion; a by-value cycle can't exist
        has := false
        for &f in sd.fields {
            if esc_has_refs(c, f.type_) { has = true; break }
        }
        g_esc_refs_cache[bt] = has
        return has
    }
    return false
}

// Does a value of this type hold a partial array inline (whose header points
// back into the value itself)?
@(private="file")
esc_self_pointing :: proc(t: Type) -> bool {
    if t == nil { return false }
    #partial switch bt in distinct_base(t) {
    case ^Type_Partial_Array:
        return true
    case ^Type_Fixed_Array:
        return esc_self_pointing(bt.elem)
    case ^Type_Scope:
        sd := as_struct_body(bt)
        if sd == nil { return false }
        if cached, ok := g_esc_self_cache[bt]; ok { return cached }
        g_esc_self_cache[bt] = false
        has := false
        for &f in sd.fields {
            if esc_self_pointing(f.type_) { has = true; break }
        }
        g_esc_self_cache[bt] = has
        return has
    }
    return false
}

// --- diagnostics ---------------------------------------------------------------

@(private="file")
esc_diag :: proc(e: ^Esc, span: Span, msg: string, args: ..any) {
    append(&e.diags, Esc_Diag{span = span, msg = fmt.aprintf(msg, ..args)})
}

@(private="file")
esc_report_store :: proc(e: ^Esc, site: Esc_Site, val: Esc_Roots) {
    g := e.g
    what := esc_describe(e, val)
    if site.callee != nil {
        name := g.name[site.op]
        src := esc_param_name(site.callee, site.st.src)
        if site.st.dst == ESC_STORE_GLOBAL {
            esc_diag(e, g.origin[site.op], TYPE_ESCAPE_CALL_STORE_GLOBAL, name, src, what)
        } else {
            esc_diag(e, g.origin[site.op], TYPE_ESCAPE_CALL_STORE, name, src, esc_param_name(site.callee, site.st.dst), what)
        }
        return
    }
    span := g.stmts[g.stmt[site.op]].span if g.stmt[site.op] >= 0 else g.origin[site.op]
    if into := graph_place_name(g, site.place); into != "" {
        esc_diag(e, span, TYPE_ESCAPE_STORE, what, into)
    } else {
        esc_diag(e, span, TYPE_ESCAPE_STORE_ANON, what)
    }
}

// Name the argument(s) that bring local memory into a returned call result.
// A construction's result is read out of the temporary it builds.
@(private="file")
esc_report_call_return :: proc(e: ^Esc, ri: int, ret: Node_Id, o: Operand, state: []Esc_Roots) -> bool {
    g := e.g
    call := o.op
    if g.op[call] == .Read { call = esc_built_by(e, ri, ret, call) }
    if call == NO_NODE || (g.op[call] != .Call && g.op[call] != .Construct) { return false }
    callee := esc_callee(e, call)
    sum := esc_summary_of(e, callee)
    if sum == nil { return false }
    args := graph_operands(g, call)
    if g.op[call] == .Construct { args = args[1:] }
    sb := strings.builder_make(context.temp_allocator)
    n := 0
    for i in 0 ..< min(len(args), ESC_MAX_PARAMS) {
        local := false
        if i in sum.ret      && esc_deepest_local(e, esc_arg(e, callee, args, i, false, state)) > ESC_CALLER { local = true }
        if i in sum.ret_deep && esc_deepest_local(e, esc_arg(e, callee, args, i, true, state))  > ESC_CALLER { local = true }
        if !local { continue }
        if n > 0 { strings.write_string(&sb, ", ") }
        fmt.sbprintf(&sb, "parameter `%s`", esc_param_name(callee, i))
        n += 1
    }
    if n == 0 { return false }
    esc_diag(e, g.origin[ret], TYPE_CANNOT_RETURN_RESULT_RETURN_REFERENCE,
        g.name[call], strings.to_string(sb), "argument" if n == 1 else "arguments")
    return true
}

// The construction whose temporary a read reads, earlier in the return's run.
@(private="file")
esc_built_by :: proc(e: ^Esc, ri: int, ret: Node_Id, read: Node_Id) -> Node_Id {
    g := e.g
    place := graph_operands(g, read)[0].op
    if g.op[place] != .Var || g.refers[place] == NO_NODE || g.written[g.refers[place]] != .Synthetic { return NO_NODE }
    temp := g.refers[place]
    ops := graph_run(g, int(e.runs[ri]))
    for i := len(ops) - 1; i >= 0; i -= 1 {
        op := ops[i]
        if g.op[op] != .Construct { continue }
        dest := graph_operands(g, op)[0].op
        if g.op[dest] == .Var && g.refers[dest] == temp { return op }
    }
    return NO_NODE
}

@(private="file")
esc_param_name :: proc(callee: ^Type_Scope, i: int) -> string {
    if callee != nil && i >= 0 && i < len(callee.params) { return callee.params[i].name }
    return "?"
}

// The shortest-lived thing a value may point into, for a diagnostic.
@(private="file")
esc_describe :: proc(e: ^Esc, r: Esc_Roots) -> string {
    g := e.g
    worst := -1
    for k in r.vars {
        v := e.vars[k]
        if worst < 0 { worst = int(k); continue }
        w := e.vars[worst]
        // The deepest; between equals, one the source names.
        if v.depth > w.depth || (v.depth == w.depth && g.written[w.node] == .Synthetic && g.written[v.node] != .Synthetic) {
            worst = int(k)
        }
    }
    if worst >= 0 && e.vars[worst].depth >= r.temp {
        v := e.vars[worst]
        switch {
        case g.written[v.node] == .Synthetic: return "a temporary"
        case v.param >= 0:                    return fmt.tprintf("the local copy of parameter `%s`", v.name)
        case v.depth > ESC_BODY:              return fmt.tprintf("block-local `%s`", v.name)
        case:                                 return fmt.tprintf("local `%s`", v.name)
        }
    }
    if r.temp > 0 { return "a temporary" }
    return "local memory"
}

// MARA_DUMP_ESC=1: each function's summary, after the bottom-up pass.
@(private="file")
esc_dump :: proc(cg: ^Call_Graph) {
    env_buf: [8]u8
    if os.get_env_buf(env_buf[:], "MARA_DUMP_ESC") == "" { return }
    for s, i in cg.nodes {
        sum := cg.esc[i]
        if sum.ret == {} && sum.ret_deep == {} && len(sum.stores) == 0 { continue }
        fmt.eprintf("  %-40s ret %v deep %v stores %v\n", s.name, sum.ret, sum.ret_deep, sum.stores[:])
    }
}
