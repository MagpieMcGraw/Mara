package mara

import "core:fmt"
import "core:mem"
import "core:mem/virtual"
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
    two:    Esc_Param_Set,   // ... what that memory points at, one step on: a
                             // `^[]T`'s elements (where an append lands)
    deep:   Esc_Param_Set,   // caller memory reachable further through them
    global: bool,
    temp:   int,             // deepest block holding a value it views in place; 0 = none
    vars:   Esc_Vars,        // variables' own storage, by index in the fun's
}

// Variables, by index in the fun's: a value's are mostly none or one — two
// kept in place, and past two, all in a list.
Esc_Vars :: struct {
    n:    i32,
    one:  [2]i32,
    more: [dynamic]i32,
}

esc_var_count :: proc(v: Esc_Vars) -> int {
    return len(v.more) if len(v.more) > 0 else int(v.n)
}

esc_var_at :: proc(v: Esc_Vars, i: int) -> i32 {
    return v.more[i] if len(v.more) > 0 else v.one[i]
}

esc_vars_has :: proc(v: Esc_Vars, k: i32) -> bool {
    for i in 0 ..< esc_var_count(v) { if esc_var_at(v, i) == k { return true } }
    return false
}

esc_vars_push :: proc(v: ^Esc_Vars, k: i32) {
    switch {
    case len(v.more) > 0: append(&v.more, k)
    case v.n < 2:         v.one[v.n] = k; v.n += 1
    case:                 append(&v.more, v.one[0], v.one[1], k)
    }
}

// A parameter's memory stored into another's (a function-summary edge): memory
// `src_level` steps from `src` may end up referenced from memory `dst_level`
// steps from `dst` — ESC_LEVEL_ONE: what the parameter points at;
// ESC_LEVEL_TWO: what that points at (a `^[]T`'s elements); ESC_LEVEL_DEEP:
// anything reachable. (Two kept apart from deep: an append through `^[]T`
// lands in the elements, not in what they point at — text items appended
// to a list don't make it a store into the text.)
Esc_Store :: struct {
    dst:       int,  // ESC_STORE_GLOBAL: into global memory
    dst_level: u8,
    src:       int,
    src_level: u8,
}

ESC_LEVEL_ONE  :: 1
ESC_LEVEL_TWO  :: 2
ESC_LEVEL_DEEP :: 3

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

// A diagnostic a walk found, kept until every component is walked
// (escape_report).
Esc_Diag :: struct {
    span: Span,
    msg:  string,
}

// One walk of one fun's or struct's code.
@(private="file")
Esc :: struct {
    cg:     ^Call_Graph,
    g:      ^Program_Graph,
    ft:     ^Type_Scope,
    ctor:   bool,                // a struct's code: `Self` is its fields
    vars:   [dynamic]Esc_Var,
    var_of: []i32,               // a declaration → its variable + 1, by id; 0 for none
    run_of: []i32,               // an operation → its run's position in `runs` + 1, by id; 0 for none
    slots:  int,
    runs:   [dynamic]i32,        // its code's runs, then its defer blocks'
    main:   int,                 // how many of `runs` are its code's own
    memo:   []Esc_Roots,         // each operation's roots, by id (a leaf's: esc_at)
    state:  []Esc_Roots,         // the state the operation being run sees

    // The fixpoint.
    flow:        Run_Flow(Esc_Roots),
    used_across: []bool,                      // an operation another run uses the value of, by id
    defer_exit:  map[Node_Id][]Esc_Roots,     // a defer block → the state it leaves

    // The last pass, over the fixpoint: summary and diagnostics.
    final:  bool,
    report: bool,
    sum:    Esc_Summary,
    diags:  [dynamic]Esc_Diag,
}

@(private="file")
Esc_Pass :: struct {
    code:     ^Program_Code,

    diags:    [dynamic]Esc_Diag,
    kept:     mem.Allocator,    // what outlives a walk: its diagnostics
    walk:     virtual.Arena,    // what a walk makes, until the next (esc_walk)
}

// A thread's: each thread of the middle end walks with its own
// (escape_thread_begin).
@(private="file", thread_local) g_esc: Esc_Pass

// Which call graph nodes have reported (by node: each written by the thread
// that walks its component).
@(private="file") g_esc_reported: []bool

// Escape analysis, a strongly connected component of the call graph at a
// time (escape_scc), bottom-up — once its funs' codes are built, its
// callees' summaries final — then its diagnostics reported (escape_report).
escape_begin :: proc(c: ^Checker, code: ^Program_Code) {
    cg := c.cg
    resize(&cg.esc, len(cg.nodes))
    g_esc_reported = make([]bool, len(cg.nodes))
}

// A thread's escape analysis begins: a walk arena, diagnostics, the type
// caches its walks fill, its own.
escape_thread_begin :: proc(code: ^Program_Code) {
    g_esc = Esc_Pass{
        code     = code,
        diags    = make([dynamic]Esc_Diag),
        kept     = context.allocator,
    }
    if err := virtual.arena_init_growing(&g_esc.walk); err != nil {
        fmt.panicf("escape analysis: no arena for its walks (%v)", err)
    }
    // (The type caches fill during walks: kept, with their own allocator —
    // new each run, as its types are: `mara serve` checks again.)
    g_esc_refs_cache = make(map[^Type_Scope]bool, 64)
    g_esc_self_cache = make(map[^Type_Scope]bool, 64)
}

// ... and ends: what it found, handed back.
escape_thread_end :: proc() -> [dynamic]Esc_Diag {
    virtual.arena_destroy(&g_esc.walk)
    delete(g_esc_refs_cache)
    delete(g_esc_self_cache)
    diags := g_esc.diags
    g_esc = {}
    return diags
}

// One component's summaries, to their fixpoint (cg_bottom_up's step), then
// each fun's diagnostics against them: a fun outside recursion reports in
// its summary walk; a recursive one walks again, the summaries final.
escape_scc :: proc(cg: ^Call_Graph, scc: []int) {
    if len(scc) == 1 && !cg_is_recursive(cg, scc[0]) {
        esc_summary_transfer(cg, scc[0])
    } else {
        for {
            changed := false
            for n in scc { if esc_summary_transfer(cg, n) { changed = true } }
            if !changed { break }
        }
    }
    for n in scc {
        if !g_esc_reported[n] { esc_walk(cg, n, true) }
    }
}

// Every component's diagnostics, in source order (check_error reports one
// once: a generic's instances share their spans).
escape_report :: proc(c: ^Checker, threads: [][dynamic]Esc_Diag) {
    diags := make([dynamic]Esc_Diag, context.temp_allocator)
    for list in threads { append(&diags, ..list[:]) }
    slice.sort_by(diags[:], proc(a, b: Esc_Diag) -> bool {
        if span_before(a.span, b.span) { return true }
        if span_before(b.span, a.span) { return false }
        return a.msg < b.msg
    })
    for d in diags { check_error(c, d.span, "%s", d.msg) }
    delete(g_esc_reported)
}
@(private="file")
esc_summary_transfer :: proc(cg: ^Call_Graph, n: int) -> bool {
    report := !cg_is_recursive(cg, n)
    s, ok := esc_walk(cg, n, report)
    if report || !ok { g_esc_reported[n] = true }
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
    g := graph_fun_code(g_esc.code, ft)
    if g == nil { return {}, false }
    // (All a walk makes is the walk arena's, the last walk's freed: its
    // summary is read before the next.)
    virtual.arena_free_all(&g_esc.walk)
    context.allocator = virtual.arena_allocator(&g_esc.walk)
    e := Esc{cg = cg, g = g, ft = ft, ctor = graph_kind_of(g, 0) == .Struct, report = report}
    e.main = graph_code_runs(g, 0, &e.runs)
    if len(e.runs) == 0 { return {}, false }
    if len(ft.params) > ESC_MAX_PARAMS {
        fmt.panicf("escape analysis: %s has %d parameters (max %d)", ft.name, len(ft.params), ESC_MAX_PARAMS)
    }
    // (Nothing in it can hold a reference: nothing can escape — its summary
    // is empty, and there is nothing to report.)
    if !esc_any_refs(g, ft) { return {}, true }
    size := graph_ix_count(g)
    e.memo = make([]Esc_Roots, size)
    e.var_of = make([]i32, size)
    e.run_of = make([]i32, size)
    e.used_across = make([]bool, size)
    esc_vars(&e)
    esc_scan(&e)
    esc_fixpoint(&e)

    e.final = true
    run_flow_replay(&e.flow, &e, esc_op)
    if report { append(&g_esc.diags, ..e.diags[:]) }
    return e.sum, true
}

// Whether anything in a code can hold a reference: a param, a result, a
// node's value — its own subtree's, less what it defines.
@(private="file")
esc_any_refs :: proc(g: ^Program_Graph, ft: ^Type_Scope) -> bool {
    for p in ft.params { if esc_has_refs(p.type_) { return true } }
    for t in ft.return_types { if esc_has_refs(t) { return true } }
    without: Type_Id = 0   // (the last type found to hold none: a run of nodes is mostly one type)
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        }
        t := g.type_[id]
        if t == 0 || t == without { continue }   // (0: no value)
        if esc_has_refs(g.types[t]) { return true }
        without = t
    }
    return false
}

// The variables: its own subtree's params, results, locals and (a struct's)
// fields, less the subtrees of what it defines.
@(private="file")
esc_vars :: proc(e: ^Esc) {
    g := e.g
    params := 0
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
        case .Param, .Result, .Local, .Field:
            v := Esc_Var{node = id, name = graph_name(g, id), type_ = graph_type(g, id), depth = esc_depth(e, id),
                         param = -1, slot = -1, init = NO_NODE}
            #partial switch g.kind[id] {
            case .Param:
                v.param = params
                params += 1
            case .Field:
                v.depth = ESC_CALLER   // a field of the value under construction: the caller's
            }
            e.var_of[id] = i32(len(e.vars)) + 1
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
        for op in graph_run(g, int(r)) { e.run_of[graph_ix(e.g, op)] = i32(ri) + 1 }
    }
    for r, ri in e.runs {
        for op in graph_run(g, int(r)) {
            ops := graph_operands(g, op)
            for o in ops {
                if o.op == NO_NODE || o.op >= CONST && o.op < READ { continue }
                if from := e.run_of[graph_ix(e.g, o.op)]; from != i32(ri) + 1 { e.used_across[graph_ix(e.g, o.op)] = true }
            }
            #partial switch graph_op_of(g, op) {
            case .Write:
                k := esc_var_named(e, ops[0])
                val := ops[1].op
                if k < 0 || val == NO_NODE { break }
                v := &e.vars[k]
                if graph_op_of(g, val) == .Carve && graph_name(g, val) == "let" && graph_stmt(g, op).kind == .Decl {
                    v.view = true   // `x := let(T, s)`: x IS the storage it views
                    v.init = op
                }
            case .Variant:
                // A match arm's binding is the payload's place, not a copy.
                if k := esc_var(e, graph_refers(g, op)); k >= 0 { e.vars[k].view = true }
            }
        }
    }
    for &v in e.vars {
        if v.view || esc_has_refs(v.type_) {
            v.slot = e.slots
            e.slots += 1
        }
    }
}

// --- the fixpoint --------------------------------------------------------------

@(private="file")
esc_fixpoint :: proc(e: ^Esc) {
    e.flow = run_flow_make(e.g, e.runs[:], e.slots, esc_state_copy, esc_merge)
    // The entry: each param holds the caller memory it points at.
    entry := make([]Esc_Roots, e.slots)
    for v in e.vars {
        if v.param >= 0 && v.slot >= 0 && !v.view { entry[v.slot].params = {v.param} }
    }
    run_flow_solve(&e.flow, entry, e, esc_op)
}

// The end of a defer's block: what it leaves joins back in where it ran
// (esc_run_defer) — a change when that grows.
@(private="file")
esc_defer_end :: proc(e: ^Esc, ret: Node_Id, state: []Esc_Roots) {
    d := esc_defer_block(e.g, ret)
    if d not_in e.defer_exit { e.defer_exit[d] = make([]Esc_Roots, e.slots) }
    if esc_merge(e.defer_exit[d], state) { e.flow.changed = true }
}

// The defer block whose code an operation ends: the scope its code is entered from.
@(private="file")
esc_defer_block :: proc(g: ^Program_Graph, op: Node_Id) -> Node_Id {
    for p := g.parent[op]; p != NO_NODE; p = g.parent[p] {
        if len(graph_out(g, p)) > 0 { return p }
    }
    return NO_NODE
}

// A run-defer (its block entered with this state: run_flow_solve): what the
// block leaves joins in, once known.
@(private="file")
esc_run_defer :: proc(e: ^Esc, op: Node_Id, state: []Esc_Roots) {
    if exit, ok := e.defer_exit[e.g.defer_of[op]]; ok { esc_merge(state, exit) }
}

// --- operations ----------------------------------------------------------------

// Run one operation: its roots into the memo, its effects on the state.
@(private="file")
esc_op :: proc(e: ^Esc, ri: int, op: Node_Id, state: []Esc_Roots) {
    g := e.g
    ops := graph_operands(g, op)
    // A value another run uses: when it grows, a change.
    watched := !e.final && e.used_across[graph_ix(e.g, op)]
    old: Esc_Roots
    if watched { esc_join(&old, e.memo[graph_ix(e.g, op)]) }
    r := &e.memo[graph_ix(e.g, op)]
    esc_clear(r)
    e.state = state
    #partial switch graph_op_of(g, op) {
    case .Global:
        r.global = true
    case .Field, .Swizzle:
        esc_join(r, esc_at(e, ops[0]))
    case .Variant:
        esc_join(r, esc_at(e, ops[0]))
        if k := esc_var(e, graph_refers(g, op)); k >= 0 { esc_copy(&state[e.vars[k].slot], r^) }
    case .Index, .View:
        esc_mem(e, r, ops[0], state)
    case .Slice:
        if graph_name(g, op) == "slice_from_ptr" {   // may view any argument
            for o in ops { esc_join(r, esc_at(e, o)) }
        } else {
            esc_mem(e, r, ops[0], state)
        }
    case .Deref:
        esc_deref(e, r, esc_at(e, ops[0]), state)
    case .Read:
        if esc_has_refs(graph_type(g, op)) { esc_deref(e, r, esc_at(e, ops[0]), state) }
    case .Address:
        esc_join(r, esc_at(e, ops[0]))
    case .Arith, .Compare, .Unary, .Cast:
        if esc_has_refs(graph_type(g, op)) {
            // (An array cast to a slice — `return list`, a [..N]T given back
            // as a []T — is a view of the array's own storage, as esc_into's
            // decay: not of what the array holds.)
            if esc_array_to_slice(e, op, ops) {
                esc_value_storage(e, r, ops[0])
            } else {
                for o in ops { esc_join(r, esc_at(e, o)) }
            }
        }
    case .Carve:
        // let(T, s) reads a T out of s's memory; slice(..., s) views it.
        mem: Esc_Roots
        esc_mem(e, &mem, ops[0], state)
        if graph_name(g, op) != "let" {
            esc_join(r, mem)
        } else if esc_has_refs(graph_type(g, op)) {
            esc_deref(e, r, mem, state)
        }
    case .Call:
        if callee := graph_called(e.g, op); callee != nil {
            esc_call(e, r, op, callee, ops, state)
        } else {
            // Through a function value (the first operand): may view any argument.
            for o in ops[1:] { esc_join(r, esc_at(e, o)) }
        }
    case .Construct:
        // Into its destination (the first operand); a union variant has no
        // constructor and holds nothing yet.
        val: Esc_Roots
        if callee := graph_called(e.g, op); callee != nil { esc_call(e, &val, op, callee, ops[1:], state) }
        esc_write(e, op, ops[0], val, state)
    case .Zero:
        // (Zero holds no reference.)
        esc_write(e, op, ops[0], {}, state)
    case .Fill:
        val: Esc_Roots
        if esc_has_refs(graph_type(g, ops[0].op)) { esc_join(&val, esc_at(e, ops[1])) }
        esc_write(e, op, ops[0], val, state)
    case .Write:
        esc_write_op(e, op, ops, state)
    case .Byte_Read:
        // A value read out of a byte buffer holds what the buffer's memory does.
        val: Esc_Roots
        if esc_has_refs(graph_type(g, ops[0].op)) {
            mem: Esc_Roots
            esc_mem(e, &mem, ops[1], state)
            esc_deref(e, &val, mem, state)
        }
        esc_write(e, op, ops[0], val, state)
    case .Return:
        if e.final && ri < e.main { esc_return_op(e, ri, op, ops, state) }
        if !e.final && ri >= e.main { esc_defer_end(e, op, state) }
    case .Run_Defer:
        esc_run_defer(e, op, state)
    }
    if watched && !esc_equal(old, r^) { e.flow.changed = true }
}

// A variable's storage, a leaf's. A view names the storage it views; `Self`
// in a struct's code is its fields; anything else is global.
@(private="file")
esc_var_roots :: proc(e: ^Esc, r: ^Esc_Roots, op: Node_Id, state: []Esc_Roots) {
    d := graph_refers(e.g, op)
    if k := esc_var(e, d); k >= 0 {
        v := e.vars[k]
        if v.view {
            esc_join(r, state[v.slot])
        } else {
            esc_vars_push(&r.vars, i32(k))
        }
        return
    }
    if e.ctor && d == 0 {
        for v, k in e.vars { if graph_kind_of(e.g, v.node) == .Field { esc_vars_push(&r.vars, i32(k)) } }
        return
    }
    r.global = true   // a constant, a function, the program's globals
}

// The variable a declaration is, or -1: its own subtree's only.
@(private="file")
esc_var :: proc(e: ^Esc, d: Node_Id) -> int {
    if d <= 0 || d > e.g.end { return -1 }
    return int(e.var_of[d]) - 1
}

// The variable a place operand names directly, or -1.
@(private="file")
esc_var_named :: proc(e: ^Esc, o: Operand) -> int {
    if !graph_is_leaf(o.op) { return -1 }
    return esc_var(e, graph_refers(e.g, o.op))
}

// An operand's roots: an operation's, as it ran; a leaf's, its variable's
// as the operation that uses it runs.
@(private="file")
esc_at :: proc(e: ^Esc, o: Operand) -> Esc_Roots {
    if o.op == NO_NODE || graph_is_const(o.op) { return {} }
    if graph_is_leaf(o.op) {
        r: Esc_Roots
        esc_var_roots(e, &r, o.op, e.state)
        return r
    }
    return e.memo[graph_ix(e.g, o.op)]
}

// The memory holding a place's elements: through a pointer, what it points
// at; through a slice, the data it views; otherwise the place's own storage.
@(private="file")
esc_mem :: proc(e: ^Esc, dst: ^Esc_Roots, place: Operand, state: []Esc_Roots) {
    m := esc_at(e, place)
    #partial switch bt in distinct_base(graph_type(e.g, place.op)) {
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
    if graph_op_of(e.g, dest.op) == .Slice {
        // `dst[lo:hi] = src`: src's elements copied into the ones the slice views.
        elems := esc_elems(e, val, index_elem_type(graph_type(e.g, dest.op)), state)
        esc_store(e, Esc_Site{op = op, place = dest}, esc_at(e, dest), elems, state)
        return
    }
    esc_write(e, op, dest, esc_into(e, val, graph_type(e.g, dest.op), state), state)
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
    for vi in 0 ..< esc_var_count(dst.vars) {
        k := esc_var_at(dst.vars, vi)
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
    if val.params == {} && val.two == {} && val.deep == {} { return }
    // Caller memory into caller memory can't be judged in here — every parameter
    // is depth 1 to the callee. Summarize it; call sites check it.
    for i in dst.params { esc_record_stores(e, i, ESC_LEVEL_ONE, val) }
    for i in dst.two    { esc_record_stores(e, i, ESC_LEVEL_TWO, val) }
    for i in dst.deep   { esc_record_stores(e, i, ESC_LEVEL_DEEP, val) }
    if dst.global       { esc_record_stores(e, ESC_STORE_GLOBAL, ESC_LEVEL_ONE, val) }
    // A constructor's field is part of the constructed result.
    for vi in 0 ..< esc_var_count(dst.vars) {
        k := esc_var_at(dst.vars, vi)
        if e.vars[k].depth == ESC_CALLER {
            e.sum.ret += val.params
            e.sum.ret_deep += val.two + val.deep
        }
    }
}

@(private="file")
esc_record_stores :: proc(e: ^Esc, dst: int, dst_level: u8, val: Esc_Roots) {
    for j in val.params { esc_record(e, Esc_Store{dst, dst_level, j, ESC_LEVEL_ONE}) }
    for j in val.two    { esc_record(e, Esc_Store{dst, dst_level, j, ESC_LEVEL_TWO}) }
    for j in val.deep   { esc_record(e, Esc_Store{dst, dst_level, j, ESC_LEVEL_DEEP}) }
}

@(private="file")
esc_record :: proc(e: ^Esc, st: Esc_Store) {
    if !slice.contains(e.sum.stores[:], st) { append(&e.sum.stores, st) }
}

// A return: each value a store into the caller (`?`'s hands back only the err).
@(private="file")
esc_return_op :: proc(e: ^Esc, ri: int, op: Node_Id, ops: []Operand, state: []Esc_Roots) {
    rts := e.ft.return_types
    for o, i in ops {   // (an operand for each result)
        rt: Type = rts[i] if i < len(rts) else nil
        esc_return(e, ri, op, esc_into(e, o, rt, state), o, state)
    }
}

@(private="file")
esc_return :: proc(e: ^Esc, ri: int, op: Node_Id, val: Esc_Roots, o: Operand, state: []Esc_Roots) {
    e.sum.ret += val.params
    e.sum.ret_deep += val.two + val.deep
    if esc_deepest_local(e, val) <= ESC_CALLER || !e.report { return }
    if o.op != NO_NODE && esc_report_call_return(e, ri, op, o, state) { return }
    esc_diag(e, graph_origin(e.g, op), TYPE_CANNOT_RETURN_LOCAL_REFERENCE_MEMORY)
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
    if dest != nil && !esc_has_refs(dest) { return r }
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
    if !esc_has_refs(elem) { return r }
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
    return graph_type(e.g, o.op) if o.out == 0 else nil
}

// Whether a cast is a fixed or partial array's decay to a slice — of one
// with storage of its own, a variable's or a temporary's (a constant's, a
// text literal's, a global's: static, viewed for good).
@(private="file")
esc_array_to_slice :: proc(e: ^Esc, op: Node_Id, ops: []Operand) -> bool {
    if graph_op_of(e.g, op) != .Cast || len(ops) != 1 { return false }
    if graph_is_const(ops[0].op) || graph_op_of(e.g, ops[0].op) == .Global { return false }
    if _, to_slice := distinct_base(graph_type(e.g, op)).(^Type_Slice); !to_slice { return false }
    #partial switch _ in distinct_base(esc_value_type(e, ops[0])) {
    case ^Type_Fixed_Array, ^Type_Partial_Array: return true
    }
    return false
}

// Where a value sits: a read's place, or else a temporary of the block
// computing it.
@(private="file")
esc_value_storage :: proc(e: ^Esc, r: ^Esc_Roots, o: Operand) {
    if graph_op_of(e.g, o.op) == .Read {
        esc_join(r, esc_at(e, graph_operands(e.g, o.op)[0]))
    } else {
        r.temp = max(r.temp, esc_depth(e, o.op))
    }
}

// --- calls ---------------------------------------------------------------------


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
    for i in sum.ret      { if i < len(args) { esc_join(r, esc_arg(e, callee, args, i, ESC_LEVEL_ONE, state)) } }
    for i in sum.ret_deep { if i < len(args) { esc_join(r, esc_arg(e, callee, args, i, ESC_LEVEL_DEEP, state)) } }
    for st in sum.stores {
        if st.src >= len(args) || st.dst >= len(args) { continue }
        val := esc_arg(e, callee, args, st.src, st.src_level, state)
        dst: Esc_Roots
        if st.dst == ESC_STORE_GLOBAL {
            dst.global = true
        } else {
            dst = esc_arg(e, callee, args, st.dst, st.dst_level, state)
        }
        esc_store(e, Esc_Site{op = op, callee = callee, st = st}, dst, val, state)
    }
}

// Argument `i` as the callee's parameter `i` sees it (decay included), at a
// level: what it points at; one step on from there; anything reachable.
@(private="file")
esc_arg :: proc(e: ^Esc, callee: ^Type_Scope, args: []Operand, i: int, level: u8, state: []Esc_Roots) -> Esc_Roots {
    pt: Type = callee.params[i].type_ if i < len(callee.params) else nil
    r := esc_into(e, args[i], pt, state)
    switch level {
    case ESC_LEVEL_ONE: return r
    case ESC_LEVEL_TWO:
        on: Esc_Roots
        esc_slice_data(e, &on, r, state)
        return on
    }
    return esc_reach(e, r, state)
}

// --- roots ---------------------------------------------------------------------

@(private="file")
esc_clear :: proc(r: ^Esc_Roots) {
    r.params, r.two, r.deep, r.global, r.temp = {}, {}, {}, false, 0
    r.vars.n = 0
    clear(&r.vars.more)
}

@(private="file")
esc_join :: proc(dst: ^Esc_Roots, src: Esc_Roots) -> (changed: bool) {
    if !(src.params <= dst.params) { dst.params += src.params; changed = true }
    if !(src.two <= dst.two)       { dst.two += src.two; changed = true }
    if !(src.deep <= dst.deep)     { dst.deep += src.deep; changed = true }
    if src.global && !dst.global   { dst.global = true; changed = true }
    if src.temp > dst.temp         { dst.temp = src.temp; changed = true }
    for i in 0 ..< esc_var_count(src.vars) {
        if k := esc_var_at(src.vars, i); !esc_vars_has(dst.vars, k) { esc_vars_push(&dst.vars, k); changed = true }
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
    if a.params != b.params || a.two != b.two || a.deep != b.deep || a.global != b.global || a.temp != b.temp { return false }
    if esc_var_count(a.vars) != esc_var_count(b.vars) { return false }
    for i in 0 ..< esc_var_count(a.vars) { if !esc_vars_has(b.vars, esc_var_at(a.vars, i)) { return false } }
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
    dst.two += r.params
    dst.deep += r.two + r.deep
    if r.global { dst.global = true }
    dst.temp = max(dst.temp, r.temp)
    for vi in 0 ..< esc_var_count(r.vars) {
        k := esc_var_at(r.vars, vi)
        if s := e.vars[k].slot; s >= 0 && !e.vars[k].view { esc_join(dst, state[s]) }
    }
}

// The data a slice header at `r` points into. A partial array's header points
// into its own inline elements, so it is (also) its own data.
@(private="file")
esc_slice_data :: proc(e: ^Esc, dst: ^Esc_Roots, r: Esc_Roots, state: []Esc_Roots) {
    esc_deref(e, dst, r, state)
    for i in 0 ..< esc_var_count(r.vars) {
        k := esc_var_at(r.vars, i)
        if esc_self_pointing(e.vars[k].type_) && !esc_vars_has(dst.vars, k) { esc_vars_push(&dst.vars, k) }
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
    for vi in 0 ..< esc_var_count(r.vars) { d = max(d, e.vars[esc_var_at(r.vars, vi)].depth) }
    return d
}

// Shallowest root, parameters' memory counting as the caller's; max(int) if none.
@(private="file")
esc_shallowest :: proc(e: ^Esc, r: Esc_Roots) -> int {
    d := max(int)
    if r.global { d = ESC_GLOBAL }
    if r.params != {} || r.two != {} || r.deep != {} { d = min(d, ESC_CALLER) }
    if r.temp > 0 { d = min(d, r.temp) }
    for vi in 0 ..< esc_var_count(r.vars) { d = min(d, e.vars[esc_var_at(r.vars, vi)].depth) }
    return d
}

// The lifetime depth of what sits where `id` does: one more than the body for
// each block around it.
@(private="file")
esc_depth :: proc(e: ^Esc, id: Node_Id) -> int {
    d := ESC_BODY
    for p := e.g.parent[id]; p != 0 && p != NO_NODE; p = e.g.parent[p] {
        if graph_kind_of(e.g, p) == .Block { d += 1 }
    }
    return d
}

// --- types ---------------------------------------------------------------------

@(private="file", thread_local) g_esc_refs_cache: map[^Type_Scope]bool
@(private="file", thread_local) g_esc_self_cache: map[^Type_Scope]bool

// Can a value of this type hold a reference? (Unknown: assume it can.)
esc_has_refs :: proc(t: Type) -> bool {
    if t == nil { return true }
    #partial switch bt in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice, Type_CString, Type_Any:
        return true
    case ^Type_Fixed_Array:
        return esc_has_refs(bt.elem)
    case ^Type_Partial_Array:
        return esc_has_refs(bt.elem)
    case ^Type_Union:
        for _, st in bt.variant_structs {
            if esc_has_refs(st) { return true }
        }
    case ^Type_Scope:
        sd := as_struct_body(bt)
        if sd == nil { return false } // a function value points at code
        if cached, ok := g_esc_refs_cache[bt]; ok { return cached }
        g_esc_refs_cache[bt] = false // terminates recursion; a by-value cycle can't exist
        has := false
        for &f in sd.fields {
            if esc_has_refs(f.type_) { has = true; break }
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
    append(&e.diags, Esc_Diag{span = span, msg = fmt.aprintf(msg, ..args, allocator = g_esc.kept)})
}

@(private="file")
esc_report_store :: proc(e: ^Esc, site: Esc_Site, val: Esc_Roots) {
    g := e.g
    what := esc_describe(e, val)
    if site.callee != nil {
        name := graph_name(g, site.op)
        src := esc_param_name(site.callee, site.st.src)
        if site.st.dst == ESC_STORE_GLOBAL {
            esc_diag(e, graph_origin(g, site.op), TYPE_ESCAPE_CALL_STORE_GLOBAL, name, src, what)
        } else {
            esc_diag(e, graph_origin(g, site.op), TYPE_ESCAPE_CALL_STORE, name, src, esc_param_name(site.callee, site.st.dst), what)
        }
        return
    }
    st := graph_stmt(g, site.op)
    span := st.span if st.node != 0 else graph_origin(g, site.op)
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
    if graph_op_of(g, call) == .Read { call = esc_built_by(e, ri, ret, call) }
    if call == NO_NODE || (graph_op_of(g, call) != .Call && graph_op_of(g, call) != .Construct) { return false }
    callee := graph_called(e.g, call)
    sum := esc_summary_of(e, callee)
    if sum == nil { return false }
    args := graph_operands(g, call)
    if graph_op_of(g, call) == .Construct { args = args[1:] }
    sb := strings.builder_make(context.temp_allocator)
    n := 0
    for i in 0 ..< min(len(args), ESC_MAX_PARAMS) {
        local := false
        if i in sum.ret      && esc_deepest_local(e, esc_arg(e, callee, args, i, ESC_LEVEL_ONE, state)) > ESC_CALLER { local = true }
        if i in sum.ret_deep && esc_deepest_local(e, esc_arg(e, callee, args, i, ESC_LEVEL_DEEP, state)) > ESC_CALLER { local = true }
        if !local { continue }
        if n > 0 { strings.write_string(&sb, ", ") }
        fmt.sbprintf(&sb, "parameter `%s`", esc_param_name(callee, i))
        n += 1
    }
    if n == 0 { return false }
    esc_diag(e, graph_origin(g, ret), TYPE_CANNOT_RETURN_RESULT_RETURN_REFERENCE,
        graph_name(g, call), strings.to_string(sb), "argument" if n == 1 else "arguments")
    return true
}

// The construction whose temporary a read reads, earlier in the return's run.
@(private="file")
esc_built_by :: proc(e: ^Esc, ri: int, ret: Node_Id, read: Node_Id) -> Node_Id {
    g := e.g
    temp := graph_leaf_decl(g, graph_operands(g, read)[0].op)
    if temp < 0 || graph_written(g, temp) != .Synthetic { return NO_NODE }
    ops := graph_run(g, int(e.runs[ri]))
    for i := len(ops) - 1; i >= 0; i -= 1 {
        op := ops[i]
        if graph_op_of(g, op) != .Construct { continue }
        if graph_leaf_decl(g, graph_operands(g, op)[0].op) == temp { return op }
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
    for vi in 0 ..< esc_var_count(r.vars) {
        k := esc_var_at(r.vars, vi)
        v := e.vars[k]
        if worst < 0 { worst = int(k); continue }
        w := e.vars[worst]
        // The deepest; between equals, one the source names.
        if v.depth > w.depth || (v.depth == w.depth && graph_written(g, w.node) == .Synthetic && graph_written(g, v.node) != .Synthetic) {
            worst = int(k)
        }
    }
    if worst >= 0 && e.vars[worst].depth >= r.temp {
        v := e.vars[worst]
        switch {
        case graph_written(g, v.node) == .Synthetic: return "a temporary"
        case v.param >= 0:                    return fmt.tprintf("the local copy of parameter `%s`", v.name)
        case v.depth > ESC_BODY:              return fmt.tprintf("block-local `%s`", v.name)
        case:                                 return fmt.tprintf("local `%s`", v.name)
        }
    }
    if r.temp > 0 { return "a temporary" }
    return "local memory"
}
