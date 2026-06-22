package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Backward data slice — `mara ask <fn> contributors` (slice analysis, step 3).
//
// "What does this function's return value depend on?" Starting from the return
// expression's uses, walk the def-use graph (Checked_Program.reaching) backward:
// a use pulls in the definitions that may reach it; each definition pulls in the
// uses in its RHS; repeat to a fixpoint. The result is the set of the function's
// own definitions (parameters + statements) that feed the return.
//
// Calls are crossed by SUMMARY, not by inlining: a call contributes only the
// arguments its return value traces back to — the call graph's `return_args`
// set, the same interprocedural summary escape analysis uses — so `pick_first(x,
// y)` that returns its first parameter pulls in `x` and NOT `y`. Unknown callees
// (foreign / indirect / no summary) fall back to all arguments (sound).
//
// This is a DATA slice: it omits control dependence (the branch conditions that
// guard the contributing statements) — that is step 4.
// ---------------------------------------------------------------------------

@(private="file")
Slice :: struct {
    checked:   ^Checked_Program,
    seen_use:  map[^Expr_Ident]bool,
    seen_def:  map[^Def]bool,
    result:    [dynamic]^Def,
    work:      [dynamic]^Expr_Ident,
    ctrl:      [dynamic]Guard,       // the branches/loops guarding contributing statements (control dependence)
    ctrl_seen: map[Span]bool,        // dedup of `ctrl` by controlling-statement span
}

@(private="file")
slice_use :: proc(s: ^Slice, u: ^Expr_Ident) {
    if u == nil || s.seen_use[u] { return }
    s.seen_use[u] = true
    append(&s.work, u)
}

// Add a contributing definition: its RHS uses (data dependence) and the branches
// /loops that guard it (control dependence) become contributors too.
@(private="file")
slice_add_def :: proc(s: ^Slice, d: ^Def) {
    if s.seen_def[d] { return }
    s.seen_def[d] = true
    append(&s.result, d)
    slice_value(s, d.value)
    slice_guards(s, d.guards)
}

// Fold control dependence: each guarding predicate is recorded (for the render)
// and its own driving expressions are sliced (a predicate has data dependence).
@(private="file")
slice_guards :: proc(s: ^Slice, guards: []Guard) {
    for g in guards {
        if g.span in s.ctrl_seen { continue }
        s.ctrl_seen[g.span] = true
        append(&s.ctrl, g)
        for c in g.conds { slice_value(s, c) }
    }
}


// Enqueue every variable use that contributes to an expression's value. A call
// contributes only the arguments its RETURN traces back to (return_args) — the
// interprocedural step — falling back to all arguments when the callee or its
// summary is unknown.
@(private="file")
slice_value :: proc(s: ^Slice, e: Expr) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident: slice_use(s, v)
    case ^Expr_Call:
        if ra, ok := slice_return_args(s.checked, v); ok {
            for i in ra { if i >= 0 && i < len(v.args) { slice_value(s, v.args[i]) } }
        } else {
            for a in v.args { slice_value(s, a) }
        }
        if v.overrides != nil { slice_value(s, v.overrides) }
    case ^Expr_Unary:        slice_value(s, v.operand)
    case ^Expr_Binary:       slice_value(s, v.left); slice_value(s, v.right)
    case ^Expr_Index:        slice_value(s, v.expr); slice_value(s, v.index)
    case ^Expr_Slice:        slice_value(s, v.expr); slice_value(s, v.low); slice_value(s, v.high)
    case ^Expr_Field_Access: slice_value(s, v.expr)
    case ^Expr_Struct_Literal:
        for f in v.fields { slice_value(s, f.value) }
        for a in v.array_values { slice_value(s, a) }
        slice_value(s, v.broadcast_value)
    case ^Expr_Take:         slice_value(s, v.storage); slice_value(s, v.count_expr)
    case ^Expr_Try:          slice_value(s, v.inner)
    case ^Expr_If:           slice_value(s, v.condition); slice_value(s, v.then_expr); slice_value(s, v.else_expr)
    case ^Expr_Array:        for el in v.elements { slice_value(s, el) }
    }
}

// The callee's return-arg set (which parameter indices its return traces to),
// read off the materialized call graph. ok=false for foreign / indirect / no-
// summary calls — the caller then conservatively follows all arguments.
@(private="file")
slice_return_args :: proc(checked: ^Checked_Program, call: ^Expr_Call) -> ([]int, bool) {
    rf, ok := call.resolved_func.?
    if !ok || rf.callee == nil || rf.callee.ast == nil { return nil, false }
    cg := &checked.call_graph
    node, found := cg.stmt_to_node[rf.callee.ast]
    if !found || node >= len(cg.return_args) { return nil, false }
    return cg.return_args[node], true
}

// The uses an expression depends on (return_args-filtered) — the collection-form
// mirror of `slice_value`, used to build the forward dependency edges so the two
// directions agree about which arguments a call propagates.
@(private="file")
slice_collect :: proc(checked: ^Checked_Program, e: Expr, out: ^map[^Expr_Ident]bool) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident: out[v] = true
    case ^Expr_Call:
        if ra, ok := slice_return_args(checked, v); ok {
            for i in ra { if i >= 0 && i < len(v.args) { slice_collect(checked, v.args[i], out) } }
        } else {
            for a in v.args { slice_collect(checked, a, out) }
        }
        if v.overrides != nil { slice_collect(checked, v.overrides, out) }
    case ^Expr_Unary:        slice_collect(checked, v.operand, out)
    case ^Expr_Binary:       slice_collect(checked, v.left, out); slice_collect(checked, v.right, out)
    case ^Expr_Index:        slice_collect(checked, v.expr, out); slice_collect(checked, v.index, out)
    case ^Expr_Slice:        slice_collect(checked, v.expr, out); slice_collect(checked, v.low, out); slice_collect(checked, v.high, out)
    case ^Expr_Field_Access: slice_collect(checked, v.expr, out)
    case ^Expr_Struct_Literal:
        for f in v.fields { slice_collect(checked, f.value, out) }
        for a in v.array_values { slice_collect(checked, a, out) }
        slice_collect(checked, v.broadcast_value, out)
    case ^Expr_Take:         slice_collect(checked, v.storage, out); slice_collect(checked, v.count_expr, out)
    case ^Expr_Try:          slice_collect(checked, v.inner, out)
    case ^Expr_If:           slice_collect(checked, v.condition, out); slice_collect(checked, v.then_expr, out); slice_collect(checked, v.else_expr, out)
    case ^Expr_Array:        for el in v.elements { slice_collect(checked, el, out) }
    }
}

// Seed the worklist from every `return` in the body (recursing into nested
// blocks, but not nested functions — those are separate slices).
@(private="file")
slice_seed :: proc(s: ^Slice, stmts: []Stmt) {
    for st in stmts {
        #partial switch v in st {
        case Stmt_Return:
            for e in v.values { slice_value(s, e) }
            g := s.checked.control_deps[v.span]   // the return's control dependence, from the CFG
            slice_guards(s, g)
        case ^Stmt_If:    slice_seed(s, v.body[:]); slice_seed(s, v.else_body[:])
        case ^Stmt_For:   slice_seed(s, v.body[:])
        case ^Stmt_Match: for arm in v.arms { slice_seed(s, arm.body[:]) }
        case ^Stmt_Defer: slice_seed(s, v.body[:])
        }
    }
}

// Functions with named returns (`-> (x, y: f32)`) assign the result into those
// bindings and return them implicitly, so seed from every definition of a named
// return — its computation is the slice. (Sound: early `return <const>` paths add
// no contributors.)
@(private="file")
slice_seed_named_returns :: proc(s: ^Slice, ft: ^Type_Scope) {
    if ft.ast == nil || len(ft.ast.return_bindings) == 0 { return }
    for d in s.checked.defs {
        if d.binding == nil || d.binding.fn != ft || s.seen_def[d] { continue }
        for rb in ft.ast.return_bindings {
            if d.binding.name == rb.name { slice_add_def(s, d); break }
        }
    }
}

@(private="file")
slice_run :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> (defs: [dynamic]^Def, ctrl: [dynamic]Guard) {
    s := Slice{ checked = checked }
    defer { delete(s.seen_use); delete(s.seen_def); delete(s.work); delete(s.ctrl_seen) }
    slice_seed(&s, ft.body[:])
    slice_seed_named_returns(&s, ft)
    for len(s.work) > 0 {
        u := pop(&s.work)
        rdefs := checked.reaching[u]   // bind before ranging (transient map-index lvalue)
        for d in rdefs { slice_add_def(&s, d) }
    }
    return s.result, s.ctrl
}

// --- render ----------------------------------------------------------------

render_contributors :: proc(checked: ^Checked_Program, ft: ^Type_Scope, label: string) -> string {
    ensure_fn_analysis(checked, ft)   // build this function's def-use graph + control deps on demand
    if len(ft.return_types) == 0 {
        return fmt.tprintf("%s returns no value — nothing to slice.\n", label)
    }
    defs, ctrl := slice_run(checked, ft)
    defer { delete(defs); delete(ctrl) }

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in defs {
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], slice_def_less)
    slice.sort_by(stmts[:],  slice_def_less)
    slice.sort_by(ctrl[:],   guard_span_less)

    b := strings.builder_make()
    fmt.sbprint(&b, "\nabove (flow) — contributors to the return value  (backward slice)\n")
    if len(params) > 0 {
        fmt.sbprintf(&b, "\n  parameters (%d)\n", len(params))
        for d in params { fmt.sbprintf(&b, "    %-14s %s\n", d.binding.name, ask_loc(d.span)) }
    }
    if len(stmts) > 0 {
        fmt.sbprintf(&b, "\n  statements (%d)\n", len(stmts))
        for d in stmts {
            fmt.sbprintf(&b, "    %-7s %-14s %s\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span))
        }
    }
    if len(ctrl) > 0 {
        fmt.sbprintf(&b, "\n  control — branches/loops guarding the above (%d)\n", len(ctrl))
        for g in ctrl { fmt.sbprintf(&b, "    %-6s %s\n", guard_word(g.kind), ask_loc(g.span)) }
    }
    if len(params) == 0 && len(stmts) == 0 {
        fmt.sbprint(&b, "\n  (no variable contributors — the return value is a constant)\n")
    }
    fmt.sbprint(&b, "\n  note: data + control dependence — control comes from the control-flow\n")
    fmt.sbprint(&b, "        graph, so early-return / break guard clauses are included.\n")
    return strings.to_string(b)
}

@(private="file")
guard_span_less :: proc(a, b: Guard) -> bool {
    if a.span.file != b.span.file { return a.span.file < b.span.file }
    if a.span.line != b.span.line { return a.span.line < b.span.line }
    return a.span.col < b.span.col
}

@(private="file")
guard_word :: proc(k: Guard_Kind) -> string {
    switch k {
    case .If:    return "if"
    case .For:   return "loop"
    case .Match: return "match"
    }
    return "?"
}

// ---------------------------------------------------------------------------
// Forward slice — `mara ask <fn> affects` (slice analysis, step 5).
//
// The mirror of `contributors`: "what does each parameter affect?" Built on the
// SAME def-use graph, walked the other way. We materialize the def -> def
// dependency edges (D1 -> D2 when D2's value or a guard controlling it reads a
// binding D1 defines, return_args-filtered exactly like the backward slice),
// then BFS forward from a parameter's definition. A parameter affects the return
// when its forward set reaches a definition that feeds a `return`.
//
// Intraprocedural (within the queried function); effects through calls use the
// same return_args summary the backward direction does, so `affects` and
// `contributors` agree (a callee-ignored argument affects nothing through it).
// ---------------------------------------------------------------------------

// Forward dependency edges D1 -> {D2}: D2 reads a binding D1 defines (in D2's RHS
// or in a guard controlling D2). The inverse of the backward dependency.
@(private="file")
slice_build_succ :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> map[^Def][dynamic]^Def {
    succ: map[^Def][dynamic]^Def
    for d2 in checked.defs {
        if d2.binding == nil || d2.binding.fn != ft { continue }
        deps: map[^Expr_Ident]bool
        slice_collect(checked, d2.value, &deps)
        for g in d2.guards { for c in g.conds { slice_collect(checked, c, &deps) } }
        for u in deps {
            rdefs := checked.reaching[u]   // bind before ranging (transient map-index lvalue)
            for d1 in rdefs {
                s := succ[d1]; append(&s, d2); succ[d1] = s
            }
        }
        delete(deps)
    }
    return succ
}

@(private="file")
slice_free_succ :: proc(succ: ^map[^Def][dynamic]^Def) {
    for _, s in succ^ { delete(s) }
    delete(succ^)
}

// Definitions whose value flows into a `return` — explicit return-value uses'
// reaching defs, plus named-return definitions. A parameter affects the return
// iff its forward set contains one of these.
@(private="file")
slice_build_feeders :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> map[^Def]bool {
    feeders: map[^Def]bool
    slice_return_feeders(checked, ft.body[:], &feeders)
    if ft.ast != nil {
        for d in checked.defs {
            if d.binding == nil || d.binding.fn != ft { continue }
            for rb in ft.ast.return_bindings { if d.binding.name == rb.name { feeders[d] = true; break } }
        }
    }
    return feeders
}

@(private="file")
slice_return_feeders :: proc(checked: ^Checked_Program, stmts: []Stmt, feeders: ^map[^Def]bool) {
    for st in stmts {
        #partial switch v in st {
        case Stmt_Return:
            for e in v.values {
                uses: map[^Expr_Ident]bool
                slice_collect(checked, e, &uses)
                for u in uses {
                    rdefs := checked.reaching[u]   // bind before ranging (transient map-index lvalue)
                    for d in rdefs { feeders[d] = true }
                }
                delete(uses)
            }
        case ^Stmt_If:    slice_return_feeders(checked, v.body[:], feeders); slice_return_feeders(checked, v.else_body[:], feeders)
        case ^Stmt_For:   slice_return_feeders(checked, v.body[:], feeders)
        case ^Stmt_Match: for arm in v.arms { slice_return_feeders(checked, arm.body[:], feeders) }
        case ^Stmt_Defer: slice_return_feeders(checked, v.body[:], feeders)
        }
    }
}

@(private="file")
slice_forward_reach :: proc(succ: map[^Def][dynamic]^Def, seed: ^Def) -> map[^Def]bool {
    seen: map[^Def]bool
    stack: [dynamic]^Def
    defer delete(stack)
    seen[seed] = true
    append(&stack, seed)
    for len(stack) > 0 {
        d := pop(&stack)
        edges := succ[d]   // bind before ranging — a transient map-index lvalue faults on an absent key
        for s in edges {
            if !seen[s] { seen[s] = true; append(&stack, s) }
        }
    }
    return seen
}


// ---------------------------------------------------------------------------
// Consumed-by-call detection — the forward slice's blind spot.
//
// The def->def forward graph links a value only to OTHER definitions (a decl it
// initializes, a reassignment, a partial write) and to `return`. A value passed
// as an argument to a call whose result is discarded — a bare call statement, or
// a call standing as a loop/if predicate or a match subject — mints no definition
// and reaches no return, so the forward walk drops it and the slice reads
// "nothing". But the value IS consumed: the call receives it (and may mutate it
// through a pointer, or act on it via I/O). We don't trace across the call — that
// is the interprocedural summary's job, and an argument's downstream effect is
// not a `return_args` edge — so we surface it honestly as "feeds N call(s)
// (effect not traced)", the same hedge `render_fn_flow_below` uses for inline
// results, instead of claiming the value flows nowhere.
// ---------------------------------------------------------------------------

// Does any argument (or receiver / override) of `call` read one of `targets`?
// return_args-filtered through nested calls, exactly like the backward slice, so
// the two directions agree about which calls a value reaches.
@(private="file")
call_reads_target :: proc(checked: ^Checked_Program, call: ^Expr_Call, targets: map[^Var_Binding]bool) -> bool {
    uses: map[^Expr_Ident]bool
    defer delete(uses)
    for arg in call.args { slice_collect(checked, arg, &uses) }
    slice_collect(checked, call.qualifier, &uses)                       // nil-safe
    if call.overrides != nil { slice_collect(checked, call.overrides, &uses) }
    for u in uses {
        if b := checked.use_def[u]; b != nil && targets[b] { return true }
    }
    return false
}

// Count the result-discarded calls in `ft` that consume one of `targets`: bare
// call statements, plus calls standing as a loop/if predicate or a match subject
// (the result drives control, but the argument carrying the value still flows in
// untraced). A call whose result binds a variable is NOT counted — that is a
// definition the def->def graph already traces as a reached statement.
@(private="file")
count_consumed_by_calls :: proc(checked: ^Checked_Program, ft: ^Type_Scope, targets: map[^Var_Binding]bool) -> int {
    n := 0
    cc_stmts(checked, ft.body[:], targets, &n)
    return n
}

@(private="file")
cc_call :: proc(checked: ^Checked_Program, e: Expr, targets: map[^Var_Binding]bool, n: ^int) {
    if call, ok := e.(^Expr_Call); ok && call_reads_target(checked, call, targets) { n^ += 1 }
}

@(private="file")
cc_stmts :: proc(checked: ^Checked_Program, stmts: []Stmt, targets: map[^Var_Binding]bool, n: ^int) {
    for s in stmts {
        #partial switch v in s {
        case Stmt_Call:   cc_call(checked, v.expr, targets, n)
        case ^Stmt_If:    cc_call(checked, v.condition, targets, n); cc_stmts(checked, v.body[:], targets, n); cc_stmts(checked, v.else_body[:], targets, n)
        case ^Stmt_For:   cc_call(checked, v.condition, targets, n); cc_stmts(checked, v.body[:], targets, n)
        case ^Stmt_Match: cc_call(checked, v.subject, targets, n); for arm in v.arms { cc_stmts(checked, arm.body[:], targets, n) }
        case ^Stmt_Defer: cc_stmts(checked, v.body[:], targets, n)
        // nested ^Stmt_Scope is its own slice (matches usedef.odin); Stmt_Decl /
        // Stmt_Assign RHS calls bind a result, so the def->def graph traces them.
        }
    }
}

// Render the "X -> ..." summary of a forward slice: a value can reach the return,
// other statements (definitions), and/or calls it feeds untraced — joined, or
// "nothing" when it reaches none of the three.
@(private="file")
flow_affects_tail :: proc(ret: bool, n_stmts, n_calls: int) -> string {
    parts: [3]string
    k := 0
    if ret         { parts[k] = "the return";                                              k += 1 }
    if n_stmts > 0 { parts[k] = ask_plural(n_stmts, "statement");                           k += 1 }
    if n_calls > 0 { parts[k] = fmt.tprintf("%s (effect not traced)", ask_plural(n_calls, "call")); k += 1 }
    switch k {
    case 0:  return "nothing"
    case 1:  return parts[0]
    case 2:  return fmt.tprintf("%s + %s", parts[0], parts[1])
    case:    return fmt.tprintf("%s + %s + %s", parts[0], parts[1], parts[2])
    }
}

@(private="file")
slice_def_less :: proc(a, b: ^Def) -> bool {
    if a.span.file != b.span.file { return a.span.file < b.span.file }
    if a.span.line != b.span.line { return a.span.line < b.span.line }
    return a.span.col < b.span.col
}

@(private="file")
slice_def_word :: proc(k: Def_Kind) -> string {
    switch k {
    case .Param:       return "param"
    case .Decl:        return "decl"
    case .Assign:      return "assign"
    case .Loop_Var:    return "loop"
    case .Destructure: return "destr"
    case .Complex:     return "write"
    }
    return "?"
}

// ---------------------------------------------------------------------------
// Variable slice — `mara ask <var> in <fn>`.
//
// The same def-use machinery the function-endpoint slices use, seeded from an
// arbitrary variable instead of the return / parameters. `above` is the backward
// slice (what feeds the variable); `below` is the forward slice (what it feeds).
// A variable has no type graph — its query is data-only.
// ---------------------------------------------------------------------------

render_var_slice :: proc(checked: ^Checked_Program, b: ^Var_Binding, fn_label, kind, dir, pkg: string) -> string {
    ensure_fn_analysis(checked, b.fn)
    knd := "param" if b.kind == .Param else "local"
    bb := strings.builder_make()
    fmt.sbprintf(&bb, "%s — %s in %s  %s   (module %s)\n", b.name, knd, fn_label, ask_loc(b.span), pkg)

    // The `types` filter selects a graph a variable doesn't have. Say so plainly.
    if kind == "types" {
        fmt.sbprint(&bb, "\n(a variable has no type graph — its slice is flow only; drop the `types` filter)\n")
        return strings.to_string(bb)
    }
    show_above := dir == "" || dir == "above"
    show_below := dir == "" || dir == "below"
    if show_above { render_var_contributors(&bb, checked, b) }
    if show_below { render_var_affects(&bb, checked, b) }
    return strings.to_string(bb)
}

// Backward: seed a slice from every definition of the variable, drain to a
// fixpoint, then report the contributing params/statements (the variable's own
// definitions excluded — they are not contributors to themselves) plus the
// branches/loops guarding them.
@(private="file")
render_var_contributors :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding) {
    s := Slice{ checked = checked }
    defer { delete(s.seen_use); delete(s.seen_def); delete(s.work); delete(s.ctrl_seen) }
    for d in checked.defs { if d.binding == b { slice_add_def(&s, d) } }
    for len(s.work) > 0 {
        u := pop(&s.work)
        rdefs := checked.reaching[u]   // bind before ranging (transient map-index lvalue)
        for d in rdefs { slice_add_def(&s, d) }
    }

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in s.result {
        if d.binding == b { continue }   // the variable's own defs aren't contributors to it
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], slice_def_less)
    slice.sort_by(stmts[:],  slice_def_less)
    slice.sort_by(s.ctrl[:], guard_span_less)

    fmt.sbprint(bb, "\nabove (flow) — what feeds this variable  (backward slice)\n")
    if len(params) > 0 {
        fmt.sbprintf(bb, "\n  parameters (%d)\n", len(params))
        for d in params { fmt.sbprintf(bb, "    %-14s %s\n", d.binding.name, ask_loc(d.span)) }
    }
    if len(stmts) > 0 {
        fmt.sbprintf(bb, "\n  statements (%d)\n", len(stmts))
        for d in stmts {
            fmt.sbprintf(bb, "    %-7s %-14s %s\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span))
        }
    }
    if len(s.ctrl) > 0 {
        fmt.sbprintf(bb, "\n  control — branches/loops guarding the above (%d)\n", len(s.ctrl))
        for g in s.ctrl { fmt.sbprintf(bb, "    %-6s %s\n", guard_word(g.kind), ask_loc(g.span)) }
    }
    if len(params) == 0 && len(stmts) == 0 {
        fmt.sbprint(bb, "\n  (nothing — the variable's value is a constant or an external input)\n")
    }
}

// Forward: BFS the def -> def edges from every definition of the variable, then
// report the definitions it reaches (its own + parameters excluded) and whether
// it reaches the return.
@(private="file")
render_var_affects :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding) {
    succ := slice_build_succ(checked, b.fn)
    defer slice_free_succ(&succ)
    feeders := slice_build_feeders(checked, b.fn)
    defer delete(feeders)

    reached: map[^Def]bool
    defer delete(reached)
    for d in checked.defs {
        if d.binding == b {
            r := slice_forward_reach(succ, d)
            for k in r { reached[k] = true }
            delete(r)
        }
    }

    stmts: [dynamic]^Def
    defer delete(stmts)
    ret := false
    for d in reached {
        if feeders[d] { ret = true }
        if d.binding != b && d.kind != .Param { append(&stmts, d) }
    }
    slice.sort_by(stmts[:], slice_def_less)

    targets: map[^Var_Binding]bool
    defer delete(targets)
    targets[b] = true
    calls := count_consumed_by_calls(checked, b.fn, targets)

    fmt.sbprint(bb, "\nbelow (flow) — what this variable affects  (forward slice)\n")
    fmt.sbprintf(bb, "\n  %s  ->  %s\n", b.name, flow_affects_tail(ret, len(stmts), calls))
    for d in stmts {
        fmt.sbprintf(bb, "    %-7s %-14s %s\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span))
    }
}

// ---------------------------------------------------------------------------
// Type flow — `mara ask <Type> flow`.
//
// The "outside" view of a type: aggregate the variable slice over every value of
// that type in the program. above = what feeds those values (backward), below =
// what they feed (forward). Spans functions, so each row carries its owning
// function. Seeds are every local/parameter whose type — pointer/slice/array
// layers stripped — is the queried type.
// ---------------------------------------------------------------------------

// Strip pointer / slice / array layers to the underlying nominal type, so a
// variable of `^Camera`, `[..]Camera`, `[3]Camera` all match a `Camera` query.
// Distinct types are left intact — they ARE a nominal type (e.g. Vec3).
flow_type_base :: proc(t: Type) -> Type {
    cur := t
    for {
        #partial switch v in cur {
        case ^Type_Ptr:           cur = v.elem
        case ^Type_Slice:         cur = v.elem
        case ^Type_Fixed_Array:   cur = v.elem
        case ^Type_Partial_Array: cur = v.elem
        case: return cur
        }
    }
}

@(private="file")
type_flow_seeds :: proc(checked: ^Checked_Program, T: Type) -> map[^Var_Binding]bool {
    seeds: map[^Var_Binding]bool
    for b in checked.var_bindings {
        if b.type_ == nil { continue }
        if flow_type_base(b.type_) == T { seeds[b] = true }
    }
    return seeds
}

// flow_analyze_all is data-only (no post-dominators) for speed, so an aggregate
// would miss control dependence. But a slice stays inside the function holding its
// seed (calls are crossed by summary), so only the functions that actually hold a
// relevant occurrence need control-deps. Build them just for `fns`, then re-stamp
// their defs' guards (the defs were created data-only, with empty guards). Keeps
// the cost ~O(uses) instead of O(all functions) while restoring full fidelity.
@(private="file")
flow_build_guards :: proc(checked: ^Checked_Program, fns: map[^Type_Scope]bool) {
    for ft in fns {
        cfg, ok := checked.cfgs[ft]
        if !ok { continue }
        cfg_build_control_deps(checked, cfg)
        for d in checked.defs {
            if d.binding != nil && d.binding.fn == ft { d.guards = checked.control_deps[d.span] }
        }
    }
}

// Control-deps for the functions holding a value of type T (where type-flow slices).
flow_build_type_guards :: proc(checked: ^Checked_Program, T: Type) {
    fns: map[^Type_Scope]bool
    defer delete(fns)
    for b in checked.var_bindings {
        if b.type_ != nil && b.fn != nil && flow_type_base(b.type_) == T { fns[b.fn] = true }
    }
    flow_build_guards(checked, fns)
}

// Control-deps for the functions that call F (where function-flow slices the args).
flow_build_fn_guards :: proc(checked: ^Checked_Program, F: ^Type_Scope) {
    fns: map[^Type_Scope]bool
    defer delete(fns)
    sites := checked.call_sites[F]
    for site in sites { if site.caller != nil { fns[site.caller] = true } }
    flow_build_guards(checked, fns)
}

render_type_flow_above :: proc(bb: ^strings.Builder, checked: ^Checked_Program, T: Type, label: string) {
    seeds := type_flow_seeds(checked, T)
    defer delete(seeds)

    s := Slice{ checked = checked }
    defer { delete(s.seen_use); delete(s.seen_def); delete(s.work); delete(s.ctrl_seen); delete(s.result); delete(s.ctrl) }
    for d in checked.defs { if d.binding != nil && seeds[d.binding] { slice_add_def(&s, d) } }
    for len(s.work) > 0 {
        u := pop(&s.work)
        rdefs := checked.reaching[u]
        for d in rdefs { slice_add_def(&s, d) }
    }

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in s.result {
        if d.binding != nil && seeds[d.binding] { continue }   // the T-typed values themselves aren't feeders
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], slice_def_less)
    slice.sort_by(stmts[:],  slice_def_less)
    slice.sort_by(s.ctrl[:], guard_span_less)

    fmt.sbprintf(bb, "\nabove (flow) — what feeds values of type %s  (%s, backward slice)\n", label, ask_plural(len(seeds), "value"))
    if len(seeds) == 0 {
        fmt.sbprintf(bb, "  (no variables or parameters of type %s)\n", label)
        return
    }
    if len(params) > 0 {
        fmt.sbprintf(bb, "\n  parameters (%d)\n", len(params))
        for d in params { fmt.sbprintf(bb, "    %-14s %s  (in %s)\n", d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(stmts) > 0 {
        fmt.sbprintf(bb, "\n  statements (%d)\n", len(stmts))
        for d in stmts { fmt.sbprintf(bb, "    %-7s %-14s %s  (in %s)\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(s.ctrl) > 0 {
        fmt.sbprintf(bb, "\n  control (%d)\n", len(s.ctrl))
        for g in s.ctrl { fmt.sbprintf(bb, "    %-6s %s\n", guard_word(g.kind), ask_loc(g.span)) }
    }
    if len(params) == 0 && len(stmts) == 0 {
        fmt.sbprint(bb, "\n  (these values are constants or external inputs — nothing feeds them)\n")
    }
}

render_type_flow_below :: proc(bb: ^strings.Builder, checked: ^Checked_Program, T: Type, label: string) {
    seeds := type_flow_seeds(checked, T)
    defer delete(seeds)

    reached:  map[^Def]bool
    ret_fns:  map[^Type_Scope]bool   // functions where a value of type T reaches the return
    done_fns: map[^Type_Scope]bool   // build each owning function's forward graph once
    defer { delete(reached); delete(ret_fns); delete(done_fns) }
    for b in seeds {
        G := b.fn
        if done_fns[G] { continue }
        done_fns[G] = true
        succ := slice_build_succ(checked, G)
        feeders := slice_build_feeders(checked, G)
        for d in checked.defs {
            if d.binding != nil && seeds[d.binding] && d.binding.fn == G {
                r := slice_forward_reach(succ, d)
                for k in r { reached[k] = true; if feeders[k] { ret_fns[G] = true } }
                delete(r)
            }
        }
        slice_free_succ(&succ)
        delete(feeders)
    }

    stmts: [dynamic]^Def
    defer delete(stmts)
    for d in reached {
        if d.binding != nil && seeds[d.binding] { continue }
        if d.kind != .Param { append(&stmts, d) }
    }
    slice.sort_by(stmts[:], slice_def_less)

    // Calls these values feed untraced — counted once per seed-holding function
    // (seeds spans many). `seeds` as targets is safe: a use in function G's body
    // resolves to a G binding, which is a seed only if it is one.
    calls := 0
    counted_fns: map[^Type_Scope]bool
    defer delete(counted_fns)
    for b in seeds {
        if b.fn == nil || counted_fns[b.fn] { continue }
        counted_fns[b.fn] = true
        calls += count_consumed_by_calls(checked, b.fn, seeds)
    }

    fmt.sbprintf(bb, "\nbelow (flow) — what values of type %s feed  (%s, forward slice)\n", label, ask_plural(len(seeds), "value"))
    if len(seeds) == 0 {
        fmt.sbprintf(bb, "  (no variables or parameters of type %s)\n", label)
        return
    }
    if len(stmts) > 0 {
        fmt.sbprintf(bb, "\n  statements (%d)\n", len(stmts))
        for d in stmts { fmt.sbprintf(bb, "    %-7s %-14s %s  (in %s)\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(ret_fns) > 0 {
        fmt.sbprintf(bb, "\n  reaches the return of %s\n", ask_plural(len(ret_fns), "function"))
    }
    if calls > 0 {
        fmt.sbprintf(bb, "\n  feeds %s  (effect not traced — passed as a call argument)\n", ask_plural(calls, "call"))
    }
    if len(stmts) == 0 && len(ret_fns) == 0 && calls == 0 {
        fmt.sbprint(bb, "\n  (these values don't flow onward — terminal or unused)\n")
    }
}

// ---------------------------------------------------------------------------
// Function flow — `mara ask <fn> flow`.
//
// The "outside" view of a function: look around it, at its call sites, not inside
// its body (the inside — what feeds the return / what the parameters reach — is a
// slice of the return / parameters as variables: `mara ask <var> in <fn>`).
// above = what computes the arguments at every call; below = where each call's
// result flows. Aggregated across all call sites, each row tagged with its caller.
// ---------------------------------------------------------------------------

render_fn_flow_above :: proc(bb: ^strings.Builder, checked: ^Checked_Program, F: ^Type_Scope, label: string) {
    sites := checked.call_sites[F]
    if len(sites) == 0    { fmt.sbprintf(bb, "\nabove (flow) — %s is never called\n", label); return }
    if len(F.params) == 0 { fmt.sbprintf(bb, "\nabove (flow) — %s takes no arguments  (%s)\n", label, ask_plural(len(sites), "call site")); return }

    s := Slice{ checked = checked }
    defer { delete(s.seen_use); delete(s.seen_def); delete(s.work); delete(s.ctrl_seen); delete(s.result); delete(s.ctrl) }
    for site in sites { for arg in site.call.args { slice_value(&s, arg) } }
    for len(s.work) > 0 {
        u := pop(&s.work)
        rdefs := checked.reaching[u]
        for d in rdefs { slice_add_def(&s, d) }
    }

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in s.result {
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], slice_def_less)
    slice.sort_by(stmts[:],  slice_def_less)
    slice.sort_by(s.ctrl[:], guard_span_less)

    fmt.sbprintf(bb, "\nabove (flow) — what feeds the arguments at its %s  (backward slice)\n", ask_plural(len(sites), "call site"))
    if len(params) > 0 {
        fmt.sbprintf(bb, "\n  parameters (%d)\n", len(params))
        for d in params { fmt.sbprintf(bb, "    %-14s %s  (in %s)\n", d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(stmts) > 0 {
        fmt.sbprintf(bb, "\n  statements (%d)\n", len(stmts))
        for d in stmts { fmt.sbprintf(bb, "    %-7s %-14s %s  (in %s)\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(s.ctrl) > 0 {
        fmt.sbprintf(bb, "\n  control (%d)\n", len(s.ctrl))
        for g in s.ctrl { fmt.sbprintf(bb, "    %-6s %s\n", guard_word(g.kind), ask_loc(g.span)) }
    }
    if len(params) == 0 && len(stmts) == 0 {
        fmt.sbprint(bb, "\n  (arguments are constants or literals — nothing feeds them)\n")
    }
}

render_fn_flow_below :: proc(bb: ^strings.Builder, checked: ^Checked_Program, F: ^Type_Scope, label: string) {
    sites := checked.call_sites[F]
    if len(sites) == 0            { fmt.sbprintf(bb, "\nbelow (flow) — %s is never called\n", label); return }
    if len(F.return_types) == 0   { fmt.sbprintf(bb, "\nbelow (flow) — %s returns no value  (%s)\n", label, ask_plural(len(sites), "call site")); return }

    // Result definitions: a call to F bound to a variable (`r := F(...)`). Calls
    // whose result is used inline aren't a def, so they're counted, not traced.
    result_defs: map[^Def]bool
    defer delete(result_defs)
    for d in checked.defs {
        if call, ok := d.value.(^Expr_Call); ok && d.binding != nil {
            if rf, rok := call.resolved_func.?; rok && rf.callee == F { result_defs[d] = true }
        }
    }
    inline := len(sites) - len(result_defs)
    if inline < 0 { inline = 0 }

    reached:  map[^Def]bool
    done_fns: map[^Type_Scope]bool
    defer { delete(reached); delete(done_fns) }
    for rd in result_defs {
        G := rd.binding.fn
        if done_fns[G] { continue }
        done_fns[G] = true
        succ := slice_build_succ(checked, G)
        for rd2 in result_defs {
            if rd2.binding.fn == G {
                r := slice_forward_reach(succ, rd2)
                for k in r { reached[k] = true }
                delete(r)
            }
        }
        slice_free_succ(&succ)
    }

    stmts: [dynamic]^Def
    defer delete(stmts)
    for d in reached {
        if result_defs[d] { continue }   // the result variables themselves
        if d.kind != .Param { append(&stmts, d) }
    }
    slice.sort_by(stmts[:], slice_def_less)

    fmt.sbprintf(bb, "\nbelow (flow) — where its results flow, across %s  (forward slice)\n", ask_plural(len(sites), "call site"))
    if len(stmts) > 0 {
        fmt.sbprintf(bb, "\n  statements (%d)\n", len(stmts))
        for d in stmts { fmt.sbprintf(bb, "    %-7s %-14s %s  (in %s)\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if inline > 0 {
        fmt.sbprintf(bb, "\n  %s use the result inline (flows into the enclosing expression — not traced)\n", ask_plural(inline, "call"))
    }
    if len(stmts) == 0 && inline == 0 {
        fmt.sbprint(bb, "\n  (results are discarded — nothing consumes them)\n")
    }
}

// `mara ask return in <fn>` — the inside view of a function's output: slice the
// return value backward to what feeds it (the contributors). The return's forward
// flow leaves the function, so for that direction the caller is pointed at the
// outside view (`mara ask <fn> flow below`).
render_return_slice :: proc(checked: ^Checked_Program, ft: ^Type_Scope, fn_label, kind, dir, pkg: string) -> string {
    ensure_fn_analysis(checked, ft)
    bb := strings.builder_make()
    fmt.sbprintf(&bb, "return — the value returned by %s  %s   (module %s)\n", fn_label, ask_loc(ft.body_span), pkg)

    if len(ft.return_types) == 0 {
        fmt.sbprintf(&bb, "\n(%s returns no value — nothing to slice)\n", fn_label)
        return strings.to_string(bb)
    }
    if kind == "types" {
        fmt.sbprint(&bb, "\n(the return value has no type graph — flow only; drop the `types` filter)\n")
        return strings.to_string(bb)
    }
    show_above := dir == "" || dir == "above"
    show_below := dir == "" || dir == "below"
    if show_above {
        fmt.sbprint(&bb, render_contributors(checked, ft, fn_label))
    }
    if show_below {
        fmt.sbprintf(&bb, "\nbelow (flow) — the return exits to callers; for where results flow use `mara ask %s flow below`\n", fn_label)
    }
    return strings.to_string(bb)
}
