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

@(private="file")
slice_guards_plus :: proc(guards: []Guard, g: Guard) -> []Guard {
    out := make([]Guard, len(guards) + 1)
    copy(out, guards)
    out[len(guards)] = g
    return out
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
        if ra, ok := slice_return_args(s, v); ok {
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
slice_return_args :: proc(s: ^Slice, call: ^Expr_Call) -> ([]int, bool) {
    rf, ok := call.resolved_func.?
    if !ok || rf.callee == nil || rf.callee.ast == nil { return nil, false }
    cg := &s.checked.call_graph
    node, found := cg.stmt_to_node[rf.callee.ast]
    if !found || node >= len(cg.return_args) { return nil, false }
    return cg.return_args[node], true
}

// Seed the worklist from every `return` in the body (recursing into nested
// blocks, but not nested functions — those are separate slices).
@(private="file")
slice_seed :: proc(s: ^Slice, stmts: []Stmt, guards: []Guard) {
    for st in stmts {
        #partial switch v in st {
        case Stmt_Return:
            for e in v.values { slice_value(s, e) }
            slice_guards(s, guards)             // a return is control-dependent on its enclosing branches
        case ^Stmt_If:
            g := slice_guards_plus(guards, guard_if(v))
            slice_seed(s, v.body[:], g)
            slice_seed(s, v.else_body[:], g)
        case ^Stmt_For:
            slice_seed(s, v.body[:], slice_guards_plus(guards, guard_for(v)))
        case ^Stmt_Match:
            mg := slice_guards_plus(guards, guard_match(v))
            for arm in v.arms { slice_seed(s, arm.body[:], mg) }
        case ^Stmt_Defer:
            slice_seed(s, v.body[:], guards)
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
    slice_seed(&s, ft.body[:], nil)
    slice_seed_named_returns(&s, ft)
    for len(s.work) > 0 {
        u := pop(&s.work)
        for d in checked.reaching[u] { slice_add_def(&s, d) }
    }
    return s.result, s.ctrl
}

// --- render ----------------------------------------------------------------

render_contributors :: proc(checked: ^Checked_Program, ft: ^Type_Scope, label: string) -> string {
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
    fmt.sbprint(&b, "\n  note: control dependence is lexical (statements inside the branches/loops\n")
    fmt.sbprint(&b, "        shown); paths via early return / break are not yet folded in.\n")
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
