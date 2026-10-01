package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Backward data slice — `mara ask return in <fn>` (contributors).
//
// "What does this function's return value depend on?" Starting from the
// returns' uses, walk the def-use (defuse.odin) backward: a use pulls in the
// definitions that may reach it; each definition pulls in the uses its value
// reads; repeat to a fixpoint. The result is the set of the function's own
// definitions (parameters + statements) that feed the return.
//
// Calls are crossed by SUMMARY, not by inlining: a call contributes only the
// arguments its return value is computed from — the call graph's `return_deps`
// set (its data and the branches that decide it; wider than escape's aliasing
// summary) — so `pick_first(x, y)` returning its first parameter pulls in `x`
// and NOT `y`, `len_of(x)` returning a count computed from `x` still pulls in
// `x`, and `starts_with(s, p)` pulls in both. Unknown callees (foreign /
// indirect / no summary) fall back to all arguments (sound).
//
// With `control`, the branches guarding each contributing statement are
// contributors too (control dependence), and so are the values they branch on.
// The params a fun's slice reaches, with control, are its return-dependency
// summary (slice_return_deps).
// ---------------------------------------------------------------------------

@(private="file")
Slice :: struct {
    checked:   ^Checked_Program,
    f:         ^Du_Fn,
    control:   bool,                 // follow the guarding branches too
    seen_use:  map[Node_Id]bool,
    seen_def:  map[^Def]bool,
    result:    [dynamic]^Def,
    work:      [dynamic]Node_Id,
    ctrl:      [dynamic]Guard,       // the branches/loops guarding contributing statements (control dependence)
    ctrl_seen: map[Span]bool,        // dedup of `ctrl` by controlling-statement span
}

@(private="file")
slice_free :: proc(s: ^Slice) {
    delete(s.seen_use); delete(s.seen_def); delete(s.work); delete(s.ctrl_seen)
}

@(private="file")
slice_use :: proc(s: ^Slice, u: Node_Id) {
    if s.seen_use[u] { return }
    s.seen_use[u] = true
    append(&s.work, u)
}

// Add a contributing definition: the uses its value reads (data dependence)
// and the branches/loops that guard it (control dependence) become
// contributors too.
@(private="file")
slice_add_def :: proc(s: ^Slice, d: ^Def) {
    if s.seen_def[d] { return }
    s.seen_def[d] = true
    append(&s.result, d)
    uses: [dynamic]Node_Id
    defer delete(uses)
    du_def_uses(s.checked, d, true, &uses)
    for u in uses { slice_use(s, u) }
    if s.control { slice_guards(s, du_def_guards(s.checked, d)) }
}

// Fold control dependence: each guarding predicate is recorded (for the render)
// and what it branches on is sliced (a predicate has data dependence).
@(private="file")
slice_guards :: proc(s: ^Slice, guards: []Guard) {
    for g in guards {
        if g.span in s.ctrl_seen { continue }
        s.ctrl_seen[g.span] = true
        append(&s.ctrl, g)
        for c in g.conds { slice_value(s, c) }
    }
}

// Enqueue every variable use that contributes to a value.
@(private="file")
slice_value :: proc(s: ^Slice, o: Operand) {
    uses: [dynamic]Node_Id
    defer delete(uses)
    du_value_uses(s.checked, o, true, &uses)
    for u in uses { slice_use(s, u) }
}

// Drain the worklist: each use pulls in the definitions that may reach it.
@(private="file")
slice_close :: proc(s: ^Slice) {
    for len(s.work) > 0 {
        u := pop(&s.work)
        for d in s.checked.du.reaching[u] { slice_add_def(s, d) }
    }
}

// Seed the worklist from every explicit `return`, and from every definition
// of a named result (`-> (x, y: f32)`): the body assigns those and returns
// them implicitly, so their computation is the slice.
@(private="file")
slice_seed :: proc(s: ^Slice) {
    g := &s.checked.graph
    for ret in s.f.returns {
        for o in graph_operands(g, ret) { slice_value(s, o) }
        if s.control { slice_guards(s, du_return_guards(s.f, ret)) }
    }
    for d in s.f.defs {
        if d.binding != nil && g.kind[d.binding.node] == .Result { slice_add_def(s, d) }
    }
}

@(private="file")
slice_run :: proc(checked: ^Checked_Program, ft: ^Type_Scope, control: bool) -> (defs: [dynamic]^Def, ctrl: [dynamic]Guard) {
    f := du_fn(checked, ft)
    if f == nil { return }
    if control && !f.guarded { du_guards(checked, f) }
    s := Slice{checked = checked, f = f, control = control}
    defer slice_free(&s)
    slice_seed(&s)
    slice_close(&s)
    return s.result, s.ctrl
}

// Which params a fun's result is computed from: its slice, following the
// branches that decide the result too — what `find` returns is the position
// where haystack matched needle, though only `start` flows into it as data.
// Calls are crossed by their callees' summaries, so the call graph computes
// these bottom-up (cg_compute_return_deps).
slice_return_deps :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> []int {
    if len(ft.return_types) == 0 { return nil }   // no result to be computed
    defs, ctrl := slice_run(checked, ft, control = true)
    defer { delete(defs); delete(ctrl) }
    params: [dynamic]int
    defer delete(params)
    for d in defs { if d.kind == .Param { append(&params, d.binding.param_index) } }
    if len(params) == 0 { return nil }
    slice.sort(params[:])
    out := make([]int, len(params))
    n := 0
    for p in params { if n == 0 || out[n - 1] != p { out[n] = p; n += 1 } }
    return out[:n]
}

// --- render ----------------------------------------------------------------

render_contributors :: proc(checked: ^Checked_Program, ft: ^Type_Scope, label: string) -> string {
    if len(ft.return_types) == 0 {
        return fmt.tprintf("%s returns no value — nothing to slice.\n", label)
    }
    defs, ctrl := slice_run(checked, ft, checked.du.want_control)
    defer { delete(defs); delete(ctrl) }

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in defs {
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], def_less)
    slice.sort_by(stmts[:],  def_less)
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
    if checked.du.want_control {
        fmt.sbprint(&b, "\n  note: data + control dependence — control comes from the control-flow\n")
        fmt.sbprint(&b, "        graph, so early-return / break guard clauses are included.\n")
    } else {
        fmt.sbprint(&b, "\n  note: data dependence only — add `control` for the guarding branches/loops\n")
    }
    return strings.to_string(b)
}

@(private="file")
guard_span_less :: proc(a, b: Guard) -> bool {
    return span_before(a.span, b.span)
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
// Forward slice — what a variable affects.
//
// The mirror of the backward slice, built on the SAME def-use walked the other
// way. We materialize the def -> def dependency edges (D1 -> D2 when D2's value
// or a guard controlling it reads a variable D1 defines, return_deps-filtered
// exactly like the backward slice), then BFS forward from a definition. A value
// affects the return when its forward set reaches a definition that feeds a
// `return`.
//
// Value flow INTO a call (an argument the callee consumes rather than returns)
// is followed into the callee parameter it lands in — see the interprocedural
// forward hop below.
// ---------------------------------------------------------------------------

// Forward dependency edges D1 -> {D2}: D2 reads a variable D1 defines.
// `data_only` counts just D2's value (pure data flow); the full graph also
// counts a variable read in a guard CONTROLLING D2 (control dependence). The
// two-graph split is how the forward slice separates data from control: reach
// via data_only, then via full; the difference is control-only.
@(private="file")
slice_build_succ :: proc(checked: ^Checked_Program, ft: ^Type_Scope, data_only: bool) -> map[^Def][dynamic]^Def {
    succ: map[^Def][dynamic]^Def
    f := du_fn(checked, ft)
    if f == nil { return succ }
    for d2 in f.defs {
        if d2.binding == nil { continue }
        deps: [dynamic]Node_Id
        du_def_uses(checked, d2, true, &deps)
        if !data_only { for g in du_def_guards(checked, d2) { for c in g.conds { du_value_uses(checked, c, true, &deps) } } }
        for u in deps {
            for d1 in checked.du.reaching[u] {
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

// Definitions whose value flows into a `return` — the explicit returns' uses'
// reaching defs, plus named-result definitions. A value affects the return iff
// its forward set contains one of these.
@(private="file")
slice_build_feeders :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> map[^Def]bool {
    feeders: map[^Def]bool
    f := du_fn(checked, ft)
    if f == nil { return feeders }
    g := &checked.graph
    for ret in f.returns {
        uses: [dynamic]Node_Id
        for o in graph_operands(g, ret) { du_value_uses(checked, o, true, &uses) }
        for u in uses {
            for d in checked.du.reaching[u] { feeders[d] = true }
        }
        delete(uses)
    }
    for d in f.defs {
        if d.binding != nil && g.kind[d.binding.node] == .Result { feeders[d] = true }
    }
    return feeders
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
// the CALLEE, where this function's def-use can't see it. That flow does not
// exist in the caller at all (it is a side effect, not a `return_deps` edge).
//
// The graph closes the gap: a call operation carries its callee (a Calls edge)
// and its arguments in the callee's parameter order, so argument i lands in
// callee parameter i. We report where the value lands — `callee (param p)` —
// and keep following from there, up to the hop budget. Only funs with a body
// are followed; a construction, a print, a foreign or indirect callee stays an
// honest "not followed" count.
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

// The binding of parameter `idx` of fun `callee`, or nil.
@(private="file")
hop_param_binding :: proc(checked: ^Checked_Program, callee: ^Type_Scope, idx: int) -> ^Var_Binding {
    f := du_fn(checked, callee)
    if f == nil { return nil }
    for b in f.vars {
        if b.kind == .Param && b.param_index == idx { return b }
    }
    return nil
}

// Does an argument carry one of `targets`? Matched by the uses' reaching defs
// (the same def-level edges the backward graph uses), NOT by binding — so a read
// of a target variable from a def outside the slice (an earlier one, or one
// writing a different field) does not count. return_deps-filtered through nested
// calls, exactly like the slices, so the directions agree.
@(private="file")
arg_reads_targets :: proc(checked: ^Checked_Program, arg: Operand, targets: map[^Def]bool) -> bool {
    uses: [dynamic]Node_Id
    defer delete(uses)
    du_value_uses(checked, arg, true, &uses)
    for u in uses {
        for d in checked.du.reaching[u] { if targets[d] { return true } }
    }
    return false
}

// Every DEFINITION the seeds reach within `fn` — the seed defs plus their forward
// def->def closure. Kept at definition granularity (NOT collapsed to bindings): a
// call consumes the value only when an argument's reaching def is in this set, so a
// read of the same variable from a different def — an earlier one, or one writing a
// different field — does not spuriously count.
@(private="file")
flow_targets :: proc(checked: ^Checked_Program, fn: ^Type_Scope, seeds: map[^Var_Binding]bool) -> map[^Def]bool {
    targets: map[^Def]bool
    succ := slice_build_succ(checked, fn, true)   // a value "lands in" a call by data flow, not control
    defer slice_free_succ(&succ)
    f := du_fn(checked, fn)
    if f == nil { return targets }
    for d in f.defs {
        if d.binding == nil || !seeds[d.binding] { continue }
        r := slice_forward_reach(succ, d)   // includes the seed def d itself
        for k in r { targets[k] = true }    // keep defs, do not collapse to bindings
        delete(r)
    }
    return targets
}

// Collect the callee-param landings out of `fn`: for every call whose argument
// reads a target, the parameter that argument lands in — whether or not the
// callee's RETURN carries it back (a glyph's w/h landing in pack_rect, which
// returns a skyline position, not the glyph). `unfollowed` counts consuming
// calls whose callee has no body to follow into.
@(private="file")
collect_landings :: proc(checked: ^Checked_Program, fn: ^Type_Scope, targets: map[^Def]bool, out: ^[dynamic]Hop_Landing) -> (unfollowed: int) {
    f := du_fn(checked, fn)
    if f == nil { return }
    g := &checked.graph
    for op in f.calls {
        callee := graph_called(g, op)
        followable := callee != nil && callee.kind == .Fun && scope_is_written(callee)
        args := du_call_args(g, op)
        if g.op[op] == .Print || g.op[op] == .Crash { args = graph_operands(g, op) }
        consuming, landed := false, false
        for arg, i in args {
            if !arg_reads_targets(checked, arg, targets) { continue }
            consuming = true
            if !followable { continue }
            if p := hop_param_binding(checked, callee, i); p != nil {
                append(out, Hop_Landing{ callee = callee, param = p, site = g.origin[op] })
                landed = true
            }
        }
        if consuming && !landed { unfollowed += 1 }
    }
    return
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
        if span_before(L.site, cur.site) { cur.site = L.site }
        by_param[L.param] = cur
    } else {
        e := L; e.sites = 1; e.depth = depth; by_param[L.param] = e
    }
}


// Sort landings by hop depth first (so the render can bucket "N hops:"), then by
// callee / parameter / site for stable output within a hop.
@(private="file")
landing_less :: proc(a, b: Hop_Landing) -> bool {
    if a.depth != b.depth { return a.depth < b.depth }
    la, lb := ask_label(a.callee), ask_label(b.callee)
    if la != lb { return la < lb }
    if a.param.param_index != b.param.param_index { return a.param.param_index < b.param.param_index }
    return span_before(a.site, b.site)
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
// where the value flows across call hops, plus any calls we can't follow.
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

// A variable's definitions, in its fun's analysis.
var_defs :: proc(checked: ^Checked_Program, b: ^Var_Binding) -> [dynamic]^Def {
    out: [dynamic]^Def
    if f := du_fn(checked, b.fn); f != nil {
        for d in f.defs { if d.binding == b { append(&out, d) } }
    }
    return out
}

// The variable's root def for a flow query — its earliest definition in source
// order (the declaration, or a parameter's entry). Flow roots here by default;
// `at <file>:<line>` overrides it with the specific write on that line.
var_root_def :: proc(checked: ^Checked_Program, b: ^Var_Binding) -> ^Def {
    defs := var_defs(checked, b)
    defer delete(defs)
    best: ^Def
    for d in defs {
        if best == nil || span_line(d.span) < span_line(best.span) || (span_line(d.span) == span_line(best.span) && span_col(d.span) < span_col(best.span)) {
            best = d
        }
    }
    return best
}

// ---------------------------------------------------------------------------
// Variable slice — `mara ask <var> in <fn>`.
//
// The same def-use machinery the function-endpoint slices use, seeded from an
// arbitrary variable instead of the return / parameters. `above` is the backward
// slice (what feeds the variable); `below` is the forward slice (what it feeds).
// A variable has no type graph — its query is data-only. Flow roots at one point
// in the variable's timeline (the declaration by default, or `root_def` from
// `at <file>:<line>`): above = what supplies that point, below = the variable's
// modifications from there on plus what they feed.
// ---------------------------------------------------------------------------

render_var_slice :: proc(checked: ^Checked_Program, b: ^Var_Binding, fn_label, kind, dir, pkg: string, depth: int, root_def: ^Def = nil) -> string {
    du_fn(checked, b.fn)
    knd := "param" if b.kind == .Param else "local"
    bb := strings.builder_make()
    home_pkg := ask_home_package(b.fn)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&bb, "%s — %s in %s  %s   (module %s)\n", b.name, knd, fn_label, ask_loc(b.span), home_pkg)
    if root_def != nil && (span_line(root_def.span) != span_line(b.span) || span_file(root_def.span) != span_file(b.span)) {
        fmt.sbprintf(&bb, "  (flow rooted at the write on %s)\n", ask_loc(root_def.span))
    }

    show_above := dir == "" || dir == "above"
    show_below := dir == "" || dir == "below"
    // A variable's natural view is its FLOW slice, so a bare query (no kind) is flow.
    // `types` (the types its flow carries) and `call` (the calls around it) are
    // explicit opt-ins — the broad-but-overlapping variable cells of mara_ask.txt.
    show_types := kind == "types"
    show_call  := kind == "call"
    show_flow  := kind == "" || kind == "flow"

    if show_types { render_var_type_graph(&bb, checked, b, show_above, show_below, depth) }
    if show_call {
        if show_above { render_var_calls_above(&bb, checked, b) }
        if show_below { render_var_calls_below(&bb, checked, b, depth) }
    }
    if show_flow {
        if show_above { render_lineage_body(checked, &bb, b, depth, root_def) }   // flow above = the lineage / producer tree
        if show_below { render_var_affects(&bb, checked, b, depth, root_def) }
    }
    return strings.to_string(bb)
}

// var `types` — FLOWY (per the mara ask matrix). A variable relates to exactly ONE
// type for free — its own; every OTHER type it touches, it touches because a value
// of that type flowed in or out. So `var type` is the variable's flow slice projected
// onto the type lattice: above = the distinct types whose values SUPPLY it (its
// backward slice), below = the types whose values it SUPPLIES (its forward slice) —
// the very slices `var call` projects onto calls, read for the types they carry. The
// structural "what is this type built from" is a question about the TYPE, not the
// variable; ask it on the type itself (`mara ask <Type>`).
@(private="file")
render_var_type_graph :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding, show_above, show_below: bool, depth: int) {
    if show_above { render_var_types_above(bb, checked, b) }
    if show_below { render_var_types_below(bb, checked, b, depth) }
}

// The backward slice from every definition of `b`.
@(private="file")
slice_of_var :: proc(checked: ^Checked_Program, b: ^Var_Binding) -> Slice {
    s := Slice{checked = checked, control = checked.du.want_control}
    defs := var_defs(checked, b)
    defer delete(defs)
    for d in defs { slice_add_def(&s, d) }
    slice_close(&s)
    return s
}

// var `type above` — the types carried by the variable's BACKWARD slice: every value
// that flows into it (its producers, transitively up the chain), grouped by nominal
// type. The SAME backward slice `var call above` reads for the calls it contains. The
// seed itself is excluded — its own type is the one it gets for free.
@(private="file")
render_var_types_above :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding) {
    s := slice_of_var(checked, b)
    defer { slice_free(&s); delete(s.result); delete(s.ctrl) }
    suppliers: map[^Var_Binding]bool
    defer delete(suppliers)
    for d in s.result {
        if d.binding == nil || d.binding == b { continue }
        suppliers[d.binding] = true
    }
    rows := var_type_rows(suppliers)
    defer { for r in rows { delete(r.vars) }; delete(rows) }
    render_var_type_rows(bb, "above", b.name, rows[:])
}

// var `type below` — the types carried by the variable's FORWARD slice: the values it
// feeds, intraprocedurally (locals computed from it) and across calls (the callee
// parameters it lands in, to `depth` hops), grouped by nominal type. The SAME forward
// reach `var call below` uses.
@(private="file")
render_var_types_below :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding, depth: int) {
    consumers: map[^Var_Binding]bool
    defer delete(consumers)

    // Intraprocedural: locals in b.fn that b's value reaches (params are inputs, not
    // things it supplies — skip them, as the forward flow view does).
    data_succ := slice_build_succ(checked, b.fn, true)
    defer slice_free_succ(&data_succ)
    defs := var_defs(checked, b)
    defer delete(defs)
    for d in defs {
        r := slice_forward_reach(data_succ, d)
        for k in r {
            if k.binding != nil && k.binding != b && k.kind != .Param { consumers[k.binding] = true }
        }
        delete(r)
    }

    // Interprocedural: the callee parameters the value lands in, across call hops.
    seeds: map[^Var_Binding]bool
    defer delete(seeds)
    seeds[b] = true
    landings, _, _ := flow_reach(checked, seeds, flow_max_hops(depth))
    defer delete(landings)
    for L in landings { if L.param != nil { consumers[L.param] = true } }

    rows := var_type_rows(consumers)
    defer { for r in rows { delete(r.vars) }; delete(rows) }
    render_var_type_rows(bb, "below", b.name, rows[:])
}

// One type in a variable's flow projection: a nominal (or basic) type, plus the
// distinct variables in the slice that carry it (for a representative sample).
@(private="file")
Var_Type_Row :: struct {
    label: string,
    sub:   string,            // "struct" / "union" / "error" / "distinct" / "basic"
    span:  Span,
    named: bool,              // a queryable named type (vs a basic like i64 / f32 / bool)
    vars:  [dynamic]string,   // distinct variable names carrying this type, discovery order
}

// A basic type's printed name, resolving an open inference cell to the width codegen
// defaults it to (Infer_Int -> i64, Infer_Float -> f64). A local like `n := 10` used
// only at i64 stays an unpinned Infer_Int cell post-check; codegen emits it as i64, so
// `ask` shows i64 too — never the internal "infer_int" placeholder — and such locals
// fold onto the real i64 row instead of splitting into a phantom type.
@(private="file")
flow_basic_name :: proc(t: Type) -> string {
    r := resolve_infer(t)
    #partial switch _ in r {
    case Type_Infer_Int:   return "i64"
    case Type_Infer_Float: return "f64"
    }
    return type_name(r)
}

// Group supplier / consumer bindings by their nominal type — pointer / slice / array
// layers stripped, distinct kept (so `^Camera`, `[..]Camera`, `Camera` all fold to
// Camera) — into rows sorted named-first (the meaningful types), then most-carried,
// then by name. Caller owns the rows' `vars` (frees them).
@(private="file")
var_type_rows :: proc(bindings: map[^Var_Binding]bool) -> [dynamic]Var_Type_Row {
    by_type: map[string]int   // dedup key -> row index
    defer delete(by_type)
    rows: [dynamic]Var_Type_Row
    for vb in bindings {
        if vb == nil || vb.type_ == nil { continue }
        base := flow_type_base(vb.type_)
        key := ask_type_name(base)       // flat (globally-unique) name for named types
        named := key != ""
        bname: string
        if !named {
            bname = flow_basic_name(base)   // resolve infer cells to i64/f64 (codegen's default)
            key = bname                     // dedup basics on the normalized printed form
        }
        idx, seen := by_type[key]
        if !seen {
            row := Var_Type_Row{ named = named }
            if named { row.label = ask_label(base); row.sub, _ = ask_sub(base); row.span = ask_span(base) }
            else     { row.label = bname; row.sub = "basic" }
            idx = len(rows)
            append(&rows, row)
            by_type[key] = idx
        }
        dup := false
        for n in rows[idx].vars { if n == vb.name { dup = true; break } }
        if !dup { append(&rows[idx].vars, vb.name) }
    }
    for &r in rows { slice.sort(r.vars[:]) }   // stable sample order — the bindings map iterates nondeterministically
    slice.sort_by(rows[:], proc(x, y: Var_Type_Row) -> bool {
        if x.named != y.named         { return x.named }                  // named types first
        if len(x.vars) != len(y.vars) { return len(x.vars) > len(y.vars) }  // most-carried first
        return x.label < y.label
    })
    return rows
}

@(private="file")
render_var_type_rows :: proc(bb: ^strings.Builder, dir, name: string, rows: []Var_Type_Row) {
    if dir == "above" {
        fmt.sbprintf(bb, "\nabove (types) — types whose values supply %s  (%s, via flow)\n", name, ask_plural(len(rows), "type"))
    } else {
        fmt.sbprintf(bb, "\nbelow (types) — types whose values %s supplies  (%s, via flow)\n", name, ask_plural(len(rows), "type"))
    }
    if len(rows) == 0 {
        if dir == "above" {
            fmt.sbprintf(bb, "  (nothing of a named or basic type feeds %s — built from literals or operators)\n", name)
        } else {
            fmt.sbprintf(bb, "  (%s feeds no further typed value — terminal, or used only in local expressions)\n", name)
        }
        return
    }
    for r in rows {
        loc := ask_loc(r.span) if r.named else ""
        fmt.sbprintf(bb, "  %-8s %-14s %-16s · %s%s\n", r.sub, r.label, loc, ask_plural(len(r.vars), "value"), var_type_sample(r.vars[:]))
    }
}

// Up to three carrying-variable names as a parenthetical sample (`  (fwd, right, +2
// more)`), or "" for none — keeps the row a summary, with `flow` the full listing.
@(private="file")
var_type_sample :: proc(vars: []string) -> string {
    if len(vars) == 0 { return "" }
    CAP :: 3
    n := min(CAP, len(vars))
    sb := strings.builder_make()
    strings.write_string(&sb, "  (")
    for i in 0 ..< n {
        if i > 0 { strings.write_string(&sb, ", ") }
        strings.write_string(&sb, vars[i])
    }
    if len(vars) > CAP { fmt.sbprintf(&sb, ", +%d more", len(vars) - CAP) }
    strings.write_string(&sb, ")")
    return strings.to_string(sb)
}

// var `call above` — the function calls that SUPPLY this value: the call-valued
// definitions in its backward slice (its own producer plus transitive producers up
// the chain). A cast (`i32(x)`) is not a call and is skipped, matching lineage.
@(private="file")
render_var_calls_above :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding) {
    s := slice_of_var(checked, b)
    defer { slice_free(&s); delete(s.result); delete(s.ctrl) }
    Row :: struct { callee, recv: string, span: Span }
    rows: [dynamic]Row
    defer delete(rows)
    seen: map[Span]bool
    defer delete(seen)
    for d in s.result {
        callee, ok := du_call_label(checked, d)
        if !ok || seen[d.span] { continue }
        seen[d.span] = true
        recv := d.binding.name if d.binding != nil else ""
        append(&rows, Row{ callee = callee, recv = recv, span = d.span })
    }
    slice.sort_by(rows[:], proc(x, y: Row) -> bool {
        if span_file(x.span) != span_file(y.span) { return span_file(x.span) < span_file(y.span) }
        return span_line(x.span) < span_line(y.span)
    })
    fmt.sbprintf(bb, "\nabove (calls) — calls that supply %s  (%s)\n", b.name, ask_plural(len(rows), "call"))
    if len(rows) == 0 {
        fmt.sbprint(bb, "  (no calls supply it — built from literals, parameters, or operators)\n")
        return
    }
    for r in rows {
        fmt.sbprintf(bb, "  %-22s ->  %-14s %s\n", fmt.tprintf("%s()", r.callee), r.recv, ask_loc(r.span))
    }
}

// var `call below` — the function calls this value SUPPLIES (the forward slice's
// "lands in" set), reusing flow_reach + render_landings.
@(private="file")
render_var_calls_below :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding, depth: int) {
    seeds: map[^Var_Binding]bool
    defer delete(seeds)
    seeds[b] = true
    landings, _, unfollowed := flow_reach(checked, seeds, flow_max_hops(depth))
    defer delete(landings)
    fmt.sbprintf(bb, "\nbelow (calls) — calls %s supplies\n", b.name)
    render_landings(bb, landings[:], unfollowed)
    if len(landings) == 0 && unfollowed == 0 {
        fmt.sbprintf(bb, "  (feeds no calls — %s is terminal or used only in local expressions)\n", b.name)
    }
}

// Forward: BFS the def -> def edges from every definition of the variable, then
// report the definitions it reaches (its own + parameters excluded) and whether
// it reaches the return.
@(private="file")
render_var_affects :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding, depth: int, root_def: ^Def) {
    // Flow roots at one point: the addressed write (root_def), else the declaration.
    // From the root forward, the variable's OWN later modifications are part of what
    // it affects (its value evolving), so — unlike the backward view — same-binding
    // defs are KEPT; only the root itself (the subject) and parameters are dropped.
    root := root_def
    if root == nil { root = var_root_def(checked, b) }
    defs := var_defs(checked, b)
    defer delete(defs)

    // Data reach: pure value flow (no guards). The hot path. With an explicit root
    // we reach forward from it alone; by default we union every def of the variable
    // so an independent reassignment (one not reading the prior value) is still covered.
    data_succ := slice_build_succ(checked, b.fn, true)
    defer slice_free_succ(&data_succ)
    feeders := slice_build_feeders(checked, b.fn)
    defer delete(feeders)

    reached: map[^Def]bool
    defer delete(reached)
    if root_def != nil {
        r := slice_forward_reach(data_succ, root_def)
        for k in r { reached[k] = true }
        delete(r)
    } else {
        for d in defs {
            r := slice_forward_reach(data_succ, d)
            for k in r { reached[k] = true }
            delete(r)
        }
    }

    stmts: [dynamic]^Def
    defer delete(stmts)
    ret := false
    for d in reached {
        if feeders[d] { ret = true }
        if d == root || d.kind == .Param { continue }   // drop the subject + inputs; keep same-binding mods
        append(&stmts, d)
    }
    slice.sort_by(stmts[:], def_less)

    // Control reach (opt-in `control`): statements that run inside a branch/loop
    // this value drives but aren't computed from its data — full reach minus data.
    ctrl_stmts: [dynamic]^Def
    defer delete(ctrl_stmts)
    if checked.du.want_control {
        full_succ := slice_build_succ(checked, b.fn, false)
        defer slice_free_succ(&full_succ)
        full: map[^Def]bool
        defer delete(full)
        if root_def != nil {
            r := slice_forward_reach(full_succ, root_def)
            for k in r { full[k] = true }
            delete(r)
        } else {
            for d in defs {
                r := slice_forward_reach(full_succ, d)
                for k in r { full[k] = true }
                delete(r)
            }
        }
        for d in full {
            if reached[d] { continue }
            if d == root || d.kind == .Param { continue }
            append(&ctrl_stmts, d)
        }
        slice.sort_by(ctrl_stmts[:], def_less)
    }

    seeds: map[^Var_Binding]bool
    defer delete(seeds)
    seeds[b] = true
    landings, hop1_calls, unfollowed := flow_reach(checked, seeds, flow_max_hops(depth))
    defer delete(landings)

    fmt.sbprint(bb, "\nbelow (flow) — what this variable affects  (forward slice)\n")
    fmt.sbprintf(bb, "\n  %s  ->  %s\n", b.name, flow_affects_tail(ret, len(stmts), hop1_calls))
    for d in stmts {
        word := slice_def_word(d.kind)
        if d.binding == b { word = "modify" }   // the variable's own evolution, not a downstream effect
        fmt.sbprintf(bb, "    %-7s %-14s %s\n", word, d.binding.name, ask_loc(d.span))
    }
    if len(ctrl_stmts) > 0 {
        fmt.sbprintf(bb, "\n  control — runs inside branches/loops it drives (%d)\n", len(ctrl_stmts))
        for d in ctrl_stmts {
            word := slice_def_word(d.kind)
            if d.binding == b { word = "modify" }
            fmt.sbprintf(bb, "    %-7s %-14s %s\n", word, d.binding.name, ask_loc(d.span))
        }
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
    for b in checked.du.vars {
        if b.type_ == nil { continue }
        if flow_type_base(b.type_) == T { seeds[b] = true }
    }
    return seeds
}

// du_all is data-only (no post-dominators) for speed, so an aggregate would miss
// control dependence. But a slice stays inside the function holding its seed
// (calls are crossed by summary), so only the functions that actually hold a
// relevant occurrence need guards: build them just for `fns` (du_fn stamps
// their defs). Keeps the cost ~O(uses) instead of O(all functions).
@(private="file")
flow_build_guards :: proc(checked: ^Checked_Program, fns: map[^Type_Scope]bool) {
    for ft in fns { du_fn(checked, ft) }
}

// Guards for the functions holding a value of type T (where type-flow slices).
flow_build_type_guards :: proc(checked: ^Checked_Program, T: Type) {
    fns: map[^Type_Scope]bool
    defer delete(fns)
    for b in checked.du.vars {
        if b.type_ != nil && b.fn != nil && flow_type_base(b.type_) == T { fns[b.fn] = true }
    }
    flow_build_guards(checked, fns)
}

// Guards for the functions that call F (where function-flow slices the args).
flow_build_fn_guards :: proc(checked: ^Checked_Program, F: ^Type_Scope) {
    fns: map[^Type_Scope]bool
    defer delete(fns)
    sites := du_call_sites(checked, F)
    defer delete(sites)
    for site in sites { if site.caller != nil { fns[site.caller] = true } }
    flow_build_guards(checked, fns)
}

render_type_flow_above :: proc(bb: ^strings.Builder, checked: ^Checked_Program, T: Type, label: string) {
    seeds := type_flow_seeds(checked, T)
    defer delete(seeds)

    s := Slice{checked = checked, control = checked.du.want_control}
    defer { slice_free(&s); delete(s.result); delete(s.ctrl) }
    for d in checked.du.defs { if d.binding != nil && seeds[d.binding] { slice_add_def(&s, d) } }
    slice_close(&s)

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in s.result {
        if d.binding != nil && seeds[d.binding] { continue }   // the T-typed values themselves aren't feeders
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], def_less)
    slice.sort_by(stmts[:],  def_less)
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

    reached:  map[^Def]bool          // data reach (the hot path)
    ctrl:     map[^Def]bool          // control-only reach (opt-in `control`)
    ret_fns:  map[^Type_Scope]bool   // functions where a value of type T reaches the return
    done_fns: map[^Type_Scope]bool   // build each owning function's forward graph once
    defer { delete(reached); delete(ctrl); delete(ret_fns); delete(done_fns) }
    for b in seeds {
        G := b.fn
        if done_fns[G] { continue }
        done_fns[G] = true
        f := du_fn(checked, G)
        data_succ := slice_build_succ(checked, G, true)
        feeders := slice_build_feeders(checked, G)
        for d in f.defs {
            if d.binding != nil && seeds[d.binding] {
                r := slice_forward_reach(data_succ, d)
                for k in r { reached[k] = true; if feeders[k] { ret_fns[G] = true } }
                delete(r)
            }
        }
        slice_free_succ(&data_succ)
        if checked.du.want_control {
            full_succ := slice_build_succ(checked, G, false)
            for d in f.defs {
                if d.binding != nil && seeds[d.binding] {
                    r := slice_forward_reach(full_succ, d)
                    for k in r { ctrl[k] = true }
                    delete(r)
                }
            }
            slice_free_succ(&full_succ)
        }
        delete(feeders)
    }

    stmts: [dynamic]^Def
    defer delete(stmts)
    for d in reached {
        if d.binding != nil && seeds[d.binding] { continue }
        if d.kind != .Param { append(&stmts, d) }
    }
    slice.sort_by(stmts[:], def_less)

    // Control-only = reachable through guards but not through data (and not a seed).
    ctrl_stmts: [dynamic]^Def
    defer delete(ctrl_stmts)
    for d in ctrl {
        if reached[d] { continue }
        if d.binding != nil && seeds[d.binding] { continue }
        if d.kind != .Param { append(&ctrl_stmts, d) }
    }
    slice.sort_by(ctrl_stmts[:], def_less)

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
    if len(ctrl_stmts) > 0 {
        fmt.sbprintf(bb, "\n  control — run inside branches/loops these values drive (%d)\n", len(ctrl_stmts))
        for d in ctrl_stmts { fmt.sbprintf(bb, "    %-7s %-14s %s  (in %s)\n", slice_def_word(d.kind), d.binding.name, ask_loc(d.span), ask_label(d.binding.fn)) }
    }
    if len(ret_fns) > 0 {
        fmt.sbprintf(bb, "\n  reaches the return of %s\n", ask_plural(len(ret_fns), "function"))
    }
    render_landings(bb, landings[:], unfollowed)
    if len(stmts) == 0 && len(ctrl_stmts) == 0 && len(ret_fns) == 0 && len(landings) == 0 && unfollowed == 0 {
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
    sites := du_call_sites(checked, F)
    defer delete(sites)
    if len(sites) == 0    { fmt.sbprintf(bb, "\nabove (flow) — %s is never called\n", label); return }
    if len(F.params) == 0 { fmt.sbprintf(bb, "\nabove (flow) — %s takes no arguments  (%s)\n", label, ask_plural(len(sites), "call site")); return }

    s := Slice{checked = checked, control = checked.du.want_control}
    defer { slice_free(&s); delete(s.result); delete(s.ctrl) }
    for site in sites { for arg in du_call_args(&checked.graph, site.op) { slice_value(&s, arg) } }
    slice_close(&s)

    params: [dynamic]^Def
    stmts:  [dynamic]^Def
    defer { delete(params); delete(stmts) }
    for d in s.result {
        if d.kind == .Param { append(&params, d) } else { append(&stmts, d) }
    }
    slice.sort_by(params[:], def_less)
    slice.sort_by(stmts[:],  def_less)
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
    sites := du_call_sites(checked, F)
    defer delete(sites)
    if len(sites) == 0            { fmt.sbprintf(bb, "\nbelow (flow) — %s is never called\n", label); return }
    if len(F.return_types) == 0   { fmt.sbprintf(bb, "\nbelow (flow) — %s returns no value  (%s)\n", label, ask_plural(len(sites), "call site")); return }

    // Result definitions: a call to F bound to a variable (`r := F(...)`). Calls
    // whose result is used inline aren't a def, so they're counted, not traced.
    g := &checked.graph
    result_defs: map[^Def]bool
    defer delete(result_defs)
    for d in checked.du.defs {
        if len(d.writes) == 0 || g.op[d.writes[0]] != .Write { continue }
        val := graph_operands(g, d.writes[0])[1].op
        if val != NO_NODE && g.op[val] == .Call && graph_called(g, val) == F { result_defs[d] = true }
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
        succ := slice_build_succ(checked, G, true)   // where results flow = data flow
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
    slice.sort_by(stmts[:], def_less)

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
    du_fn(checked, ft)
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
