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
    fmt.sbprintf(&b, "%s — contributors to the return value  (backward slice)\n", label)
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
slice_param_def :: proc(checked: ^Checked_Program, ft: ^Type_Scope, name: string) -> ^Def {
    for d in checked.defs {
        if d.kind == .Param && d.binding != nil && d.binding.fn == ft && d.binding.name == name { return d }
    }
    return nil
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

render_affects :: proc(checked: ^Checked_Program, ft: ^Type_Scope, label: string) -> string {
    ensure_fn_analysis(checked, ft)   // build this function's def-use graph + control deps on demand
    if len(ft.params) == 0 {
        return fmt.tprintf("%s has no parameters to trace forward.\n", label)
    }
    succ := slice_build_succ(checked, ft)
    defer slice_free_succ(&succ)
    feeders := slice_build_feeders(checked, ft)
    defer delete(feeders)

    b := strings.builder_make()
    fmt.sbprintf(&b, "%s — what each parameter affects  (forward slice)\n", label)
    for p in ft.params {
        if p.name == "" || p.name == "_" { continue }
        pdef := slice_param_def(checked, ft, p.name)
        if pdef == nil { continue }
        reached := slice_forward_reach(succ, pdef)
        defer delete(reached)

        stmts: [dynamic]^Def
        defer delete(stmts)
        ret := false
        for d in reached {
            if feeders[d] { ret = true }
            if d != pdef && d.kind != .Param { append(&stmts, d) }
        }
        slice.sort_by(stmts[:], slice_def_less)

        tail: string
        switch {
        case ret && len(stmts) > 0: tail = fmt.tprintf("the return + %s", ask_plural(len(stmts), "statement"))
        case ret:                   tail = "the return"
        case len(stmts) > 0:        tail = fmt.tprintf("%s (not the return)", ask_plural(len(stmts), "statement"))
        case:                       tail = "nothing"
        }
        fmt.sbprintf(&b, "\n  %-14s ->  %s\n", p.name, tail)
        for d in stmts {
            fmt.sbprintf(&b, "    %-7s %-14s %s\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span))
        }
    }
    fmt.sbprint(&b, "\n  note: data + control dependence (from the control-flow graph) within this\n")
    fmt.sbprint(&b, "        function; effects through calls use return_args, like `contributors`.\n")
    return strings.to_string(b)
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
