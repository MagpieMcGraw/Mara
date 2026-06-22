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
// Within the queried function this is the def->def reach; value flow OUT of a
// call's return uses the same return_args summary the backward direction does, so
// `affects` and `contributors` agree. Value flow INTO a call (a bare/predicate
// call's argument, where the value is consumed by the callee, not returned) is
// followed ONE hop to the callee parameter it lands in — see the interprocedural
// forward hop above.
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
// Interprocedural forward hop — following a value into the callees it feeds.
//
// The def->def forward graph links a value only to OTHER definitions in the SAME
// function and to `return`. A value passed as a call argument — a bare call, a
// loop/if predicate, a match subject, a pointer the callee mutates — flows into
// the CALLEE, where this function's def-use graph can't see it. That flow does
// not exist in the caller at all (it is a side effect, not a `return_args` edge),
// so the slice used to report it honestly but blindly as "feeds N calls (effect
// not traced)".
//
// The call graph closes the gap by following ONE hop into the callee: a resolved
// call carries its callee (resolved_func.callee), and post-UFCS-desugar the
// receiver is folded into args[0], so call.args[i] maps positionally to
// callee.params[i]. We report where the value lands — `callee (param p)`. Deeper
// hops are a drill-down: slice that parameter (`mara ask p in callee`). Only
// resolved calls with a body are followed; foreign / indirect / bodiless callees
// stay an honest "not followed" count.
// ---------------------------------------------------------------------------

// The call-hop budget for a forward flow query. The shared `depth` token is the
// type-graph hop budget for type queries; for flow it bounds call-following. An
// omitted depth (-1) follows to UNBOUNDED depth, matching the type-graph default
// (omit = full closure) so the token reads identically on both axes. It still
// terminates: flow_reach expands each parameter once (its `expanded` cycle guard)
// over a finite call graph, so a budget past any real call chain is "no cap" — a
// value through a god-object now reaches most of the program (the wall the old
// 1-hop default avoided, accepted here for a consistent default). An explicit 0
// disables following (the pre-hop "feeds N calls" count only); N caps at N hops.
@(private="file")
flow_max_hops :: proc(depth: int) -> int {
    return (1 << 30) if depth < 0 else depth   // 1<<30 ≈ 1e9 hops — effectively ∞
}

// One landing: a callee parameter a traced value flows into. `site` is a
// representative (earliest) call site; `sites` counts how many calls land the
// value in this same parameter (the value reaching `draw_marker.state` from four
// call sites is one landing, ×4, not four rows); `depth` is the shortest call-hop
// distance from the queried value (1 = a direct call).
@(private="file")
Hop_Landing :: struct {
    callee: ^Type_Scope,
    param:  ^Var_Binding,
    site:   Span,
    sites:  int,
    depth:  int,
}

// The callee a resolved call reaches, or nil (distinct-cast / foreign / indirect).
@(private="file")
hop_callee :: proc(call: ^Expr_Call) -> ^Type_Scope {
    if rf, ok := call.resolved_func.?; ok { return rf.callee }
    return nil
}

// The ^Var_Binding for parameter `idx` of `callee`. nil when the callee has no
// analyzed parameters (e.g. a constructor, which flow_analyze_all skips) or idx
// is out of range — the caller then treats that argument as not-followed.
@(private="file")
hop_param_binding :: proc(checked: ^Checked_Program, callee: ^Type_Scope, idx: int) -> ^Var_Binding {
    for b in checked.var_bindings {
        if b.fn == callee && b.kind == .Param && b.param_index == idx { return b }
    }
    return nil
}

// Does an argument expression read one of `targets`? return_args-filtered through
// nested calls (slice_collect), exactly like the slices, so the directions agree.
@(private="file")
arg_reads_targets :: proc(checked: ^Checked_Program, arg: Expr, targets: map[^Var_Binding]bool) -> bool {
    uses: map[^Expr_Ident]bool
    defer delete(uses)
    slice_collect(checked, arg, &uses)
    for u in uses {
        if b := checked.use_def[u]; b != nil && targets[b] { return true }
    }
    return false
}

// Every binding the seeds reach within `fn` — the seeds plus their forward
// def->def closure. This is the set of names that carry the traced value, so a
// call reading ANY of them (a local the value was copied into, a field pointer
// carved from it) consumes the value, not only a call reading the seed directly.
@(private="file")
flow_targets :: proc(checked: ^Checked_Program, fn: ^Type_Scope, seeds: map[^Var_Binding]bool) -> map[^Var_Binding]bool {
    targets: map[^Var_Binding]bool
    succ := slice_build_succ(checked, fn)
    defer slice_free_succ(&succ)
    for b in seeds {
        if b.fn != fn { continue }
        targets[b] = true
        for d in checked.defs {
            if d.binding == b {
                r := slice_forward_reach(succ, d)
                for k in r { if k.binding != nil { targets[k.binding] = true } }
                delete(r)
            }
        }
    }
    return targets
}

// Collect the callee-param landings out of `fn`: for every call whose argument
// reads a target, the parameter that argument lands in. Walks the same statement
// shapes the rest of the slicer does (bare calls + calls driving a loop/if/match;
// a result-binding call's RETURN flow is already traced by the def->def graph).
// `unfollowed` counts consuming calls whose callee has no body to follow into.
@(private="file")
collect_landings :: proc(checked: ^Checked_Program, fn: ^Type_Scope, targets: map[^Var_Binding]bool, out: ^[dynamic]Hop_Landing) -> (unfollowed: int) {
    ld_stmts(checked, fn.body[:], targets, out, &unfollowed)
    return
}

@(private="file")
ld_stmts :: proc(checked: ^Checked_Program, stmts: []Stmt, targets: map[^Var_Binding]bool, out: ^[dynamic]Hop_Landing, unfollowed: ^int) {
    for s in stmts {
        #partial switch v in s {
        case Stmt_Call:   ld_call(checked, v.expr, targets, out, unfollowed)
        case ^Stmt_If:    ld_call(checked, v.condition, targets, out, unfollowed); ld_stmts(checked, v.body[:], targets, out, unfollowed); ld_stmts(checked, v.else_body[:], targets, out, unfollowed)
        case ^Stmt_For:   ld_call(checked, v.condition, targets, out, unfollowed); ld_stmts(checked, v.body[:], targets, out, unfollowed)
        case ^Stmt_Match: ld_call(checked, v.subject, targets, out, unfollowed); for arm in v.arms { ld_stmts(checked, arm.body[:], targets, out, unfollowed) }
        case ^Stmt_Defer: ld_stmts(checked, v.body[:], targets, out, unfollowed)
        }
    }
}

@(private="file")
ld_call :: proc(checked: ^Checked_Program, e: Expr, targets: map[^Var_Binding]bool, out: ^[dynamic]Hop_Landing, unfollowed: ^int) {
    call, ok := e.(^Expr_Call)
    if !ok { return }
    callee := hop_callee(call)
    followable := callee != nil && callee.ast != nil
    consuming, landed := false, false
    for arg, i in call.args {
        if !arg_reads_targets(checked, arg, targets) { continue }
        consuming = true
        if !followable { continue }
        if p := hop_param_binding(checked, callee, i); p != nil {
            append(out, Hop_Landing{ callee = callee, param = p, site = call.span })
            landed = true
        }
    }
    if consuming && !landed { unfollowed^ += 1 }
}

// Interprocedural forward reach over a seed set, up to `max_hops` call hops (a
// breadth-first walk: hop 1 = the calls the seeds feed directly, hop 2 = the
// calls THOSE callee parameters feed, and so on). Returns the callee-param
// landings (collapsed per parameter, each tagged with its shortest hop depth and
// a site count), the number of distinct calls at hop 1 (the "feeds N calls"
// tail), and the count of consuming calls with no followable body across all hops.
// A parameter is expanded once (the `expanded` set is the cycle / recursion guard,
// seeded with the query's own values so a hop landing back on them stops).
@(private="file")
flow_reach :: proc(checked: ^Checked_Program, seeds: map[^Var_Binding]bool, max_hops: int) -> (landings: [dynamic]Hop_Landing, hop1_calls: int, unfollowed: int) {
    by_param: map[^Var_Binding]Hop_Landing
    defer delete(by_param)
    expanded: map[^Var_Binding]bool
    defer delete(expanded)
    for b in seeds { expanded[b] = true }

    // Hop 1: the initial seeds, grouped by their owning functions (sorted for a
    // deterministic representative site when the same param is reached twice).
    fns: [dynamic]^Type_Scope
    defer delete(fns)
    {
        seen_fn: map[^Type_Scope]bool
        defer delete(seen_fn)
        for b in seeds { if b.fn != nil && !seen_fn[b.fn] { seen_fn[b.fn] = true; append(&fns, b.fn) } }
    }
    slice.sort_by(fns[:], proc(a, b: ^Type_Scope) -> bool { return ask_label(a) < ask_label(b) })

    // Hop 1 is always counted (the "feeds N calls" tail), but only RECORDED as
    // landings when we're following (max_hops >= 1). depth 0 = count only, no block.
    follow := max_hops >= 1
    frontier: [dynamic]^Var_Binding
    defer delete(frontier)
    {
        hop1_sites: map[Span]bool
        defer delete(hop1_sites)
        hop1_uf := 0
        for fn in fns {
            targets := flow_targets(checked, fn, seeds)
            raw: [dynamic]Hop_Landing
            hop1_uf += collect_landings(checked, fn, targets, &raw)
            for L in raw {
                hop1_sites[L.site] = true
                if follow {
                    flow_record(&by_param, L, 1)
                    if !expanded[L.param] { expanded[L.param] = true; append(&frontier, L.param) }
                }
            }
            delete(targets); delete(raw)
        }
        hop1_calls = len(hop1_sites) + hop1_uf
        if follow { unfollowed += hop1_uf }
    }
    if !follow { return }   // depth 0: the count is in hop1_calls; emit no landings

    // Hops 2..max_hops: each frontier parameter is a seed inside its own callee.
    depth := 1
    for depth < max_hops && len(frontier) > 0 {
        depth += 1
        next: [dynamic]^Var_Binding
        for p in frontier {
            ps: map[^Var_Binding]bool
            ps[p] = true
            targets := flow_targets(checked, p.fn, ps)
            raw: [dynamic]Hop_Landing
            unfollowed += collect_landings(checked, p.fn, targets, &raw)
            for L in raw {
                flow_record(&by_param, L, depth)
                if !expanded[L.param] { expanded[L.param] = true; append(&next, L.param) }
            }
            delete(ps); delete(targets); delete(raw)
        }
        delete(frontier)
        frontier = next
    }

    for _, L in by_param { append(&landings, L) }
    slice.sort_by(landings[:], landing_less)
    return
}

// Fold a raw landing into the per-parameter map: bump the site count, keep the
// shallowest hop depth and the earliest call site.
@(private="file")
flow_record :: proc(by_param: ^map[^Var_Binding]Hop_Landing, L: Hop_Landing, depth: int) {
    if cur, ok := by_param[L.param]; ok {
        cur.sites += 1
        if depth < cur.depth { cur.depth = depth }
        if landing_site_less(L.site, cur.site) { cur.site = L.site }
        by_param[L.param] = cur
    } else {
        e := L; e.sites = 1; e.depth = depth; by_param[L.param] = e
    }
}

@(private="file")
landing_site_less :: proc(a, b: Span) -> bool {
    if a.file != b.file { return a.file < b.file }
    return a.line < b.line
}

// Sort landings by hop depth first (so the render can bucket "N hops:"), then by
// callee / parameter / site for stable output within a hop.
@(private="file")
landing_less :: proc(a, b: Hop_Landing) -> bool {
    if a.depth != b.depth { return a.depth < b.depth }
    la, lb := ask_label(a.callee), ask_label(b.callee)
    if la != lb { return la < lb }
    if a.param.param_index != b.param.param_index { return a.param.param_index < b.param.param_index }
    if a.site.file != b.site.file { return a.site.file < b.site.file }
    return a.site.line < b.site.line
}

// A parameter's type as the compiler prints it (`^Megastruct`, `f64`) — the ^ vs
// value distinction tells the reader whether the callee can mutate the caller's
// value. `type_name` is the same renderer the type-checker diagnostics use.
@(private="file")
flow_param_type :: proc(t: Type) -> string {
    if t == nil { return "" }
    return type_name(t)
}

// The param-landing block shared by the variable and type-flow forward views:
// where the value flows in one interprocedural hop, plus any calls we can't follow.
@(private="file")
render_landings :: proc(bb: ^strings.Builder, landings: []Hop_Landing, unfollowed: int) {
    if len(landings) > 0 {
        max_d := 1
        for L in landings { if L.depth > max_d { max_d = L.depth } }
        multi := max_d > 1   // a single ring stays flat, like before; deeper views bucket by hop
        fmt.sbprintf(bb, "\n  into calls — the value lands in  (%s)\n", ask_plural(len(landings), "parameter"))
        cur_d := 0
        for L in landings {
            if multi && L.depth != cur_d {
                cur_d = L.depth
                tag := " (direct)" if L.depth == 1 else ""
                fmt.sbprintf(bb, "    %s%s:\n", ask_plural(L.depth, "hop"), tag)
            }
            indent := "      " if multi else "    "
            ty := flow_param_type(L.param.type_)
            tystr := fmt.tprintf(" : %s", ty) if ty != "" else ""
            more := fmt.tprintf("  (+%d more)", L.sites - 1) if L.sites > 1 else ""
            fmt.sbprintf(bb, "%s%-22s (param %s%s)  %s%s\n", indent, ask_label(L.callee), L.param.name, tystr, ask_loc(L.site), more)
        }
    }
    if unfollowed > 0 {
        fmt.sbprintf(bb, "\n  %s not followed  (foreign / indirect / no body)\n", ask_plural(unfollowed, "call"))
    }
}

// Render the "X -> ..." summary of a forward slice: a value can reach the return,
// other statements (definitions), and/or calls it feeds (detailed below as param
// landings) — joined, or "nothing" when it reaches none of the three.
@(private="file")
flow_affects_tail :: proc(ret: bool, n_stmts, n_calls: int) -> string {
    parts: [3]string
    k := 0
    if ret         { parts[k] = "the return";                  k += 1 }
    if n_stmts > 0 { parts[k] = ask_plural(n_stmts, "statement"); k += 1 }
    if n_calls > 0 { parts[k] = ask_plural(n_calls, "call");      k += 1 }
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

render_var_slice :: proc(checked: ^Checked_Program, b: ^Var_Binding, fn_label, kind, dir, pkg: string, depth: int) -> string {
    ensure_fn_analysis(checked, b.fn)
    knd := "param" if b.kind == .Param else "local"
    bb := strings.builder_make()
    home_pkg := ask_home_package(b.fn)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&bb, "%s — %s in %s  %s   (module %s)\n", b.name, knd, fn_label, ask_loc(b.span), home_pkg)

    // The `types` filter selects a graph a variable doesn't have. Say so plainly.
    if kind == "types" {
        fmt.sbprint(&bb, "\n(a variable has no type graph — its slice is flow only; drop the `types` filter)\n")
        return strings.to_string(bb)
    }
    show_above := dir == "" || dir == "above"
    show_below := dir == "" || dir == "below"
    if show_above { render_var_contributors(&bb, checked, b) }
    if show_below { render_var_affects(&bb, checked, b, depth) }
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
render_var_affects :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding, depth: int) {
    flow_analyze_all(checked)   // the interprocedural hop reads callees' param bindings

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

    seeds: map[^Var_Binding]bool
    defer delete(seeds)
    seeds[b] = true
    landings, hop1_calls, unfollowed := flow_reach(checked, seeds, flow_max_hops(depth))
    defer delete(landings)

    fmt.sbprint(bb, "\nbelow (flow) — what this variable affects  (forward slice)\n")
    fmt.sbprintf(bb, "\n  %s  ->  %s\n", b.name, flow_affects_tail(ret, len(stmts), hop1_calls))
    for d in stmts {
        fmt.sbprintf(bb, "    %-7s %-14s %s\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span))
    }
    render_landings(bb, landings[:], unfollowed)
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

render_type_flow_below :: proc(bb: ^strings.Builder, checked: ^Checked_Program, T: Type, label: string, depth: int) {
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

    // The calls these values feed, followed into the callee parameters they land
    // in (flow_reach spans every seed-holding function, up to the hop budget).
    landings, _, unfollowed := flow_reach(checked, seeds, flow_max_hops(depth))
    defer delete(landings)

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
    render_landings(bb, landings[:], unfollowed)
    if len(stmts) == 0 && len(ret_fns) == 0 && len(landings) == 0 && unfollowed == 0 {
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
    home_pkg := ask_home_package(ft)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&bb, "return — the value returned by %s  %s   (module %s)\n", fn_label, ask_loc(ft.body_span), home_pkg)

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
