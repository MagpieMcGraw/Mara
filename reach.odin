package mara

import "core:fmt"
import "core:mem/virtual"
import "core:slice"
import "core:sync"

// What a call can reach, and where places are, from the program graph alone —
// shared by the analysis that holds a program to the rule a result isn't
// built over what its call reads (reach_code) and by codegen,
// which builds results in place where nothing they read can be that place
// (llvm_result_place, storage_in_place).

// Each fun's summary, worked out once: reach_summary's cache.
Reach_Summaries :: map[^Type_Scope]^Fun_Summary

// What a fun's code reaches (reach_summary).
Fun_Summary :: struct {
    reaches:  []bool,   // by param: whether it reads or writes through it
    returned: []bool,   // by param: whether a pointer param may be in its result
    done:     bool,
}

// A fun's summary — a struct's code's too, which a construction runs —
// worked out from its code once per cache (the analysis its own, each codegen worker its own). A fun
// with no code reaches through every param: a foreign one, or an intrinsic
// (expanded in place). So does a fun being worked out — a call back into it.
reach_summary :: proc(code: ^Program_Code, cache: ^Reach_Summaries, f: ^Type_Scope) -> ^Fun_Summary {
    if s := graph_fun_summary(code, f); s != nil { return s }   // (worked out for everyone: reach_scc)
    if s, known := cache^[f]; known && s.done { return s }
    n := len(f.cg_params)
    all := new(Fun_Summary)
    all.reaches, all.returned, all.done = make([]bool, n), make([]bool, n), true
    for &r in all.reaches { r = true }
    if f in cache^ { return all }
    pg := graph_fun_code(code, f)
    if _, src := f.origin.(Origin_Source); pg == nil || !src {
        cache^[f] = all
        return all
    }
    s := new(Fun_Summary)
    s.reaches, s.returned = make([]bool, n), make([]bool, n)
    cache^[f] = s
    if !reach_summarize(code, cache, f, pg, s) { s^ = all^ }
    s.done = true
    return s
}

// A component of the call graph's funs' summaries, worked out together once
// their codes are built — every call they make out of the component reaches
// what its callee's summary says; one within it, through every param it's
// handed, whichever is worked out first — and kept for everyone
// (Program_Code.summaries): the middle end's reach check, codegen.
reach_scc :: proc(code: ^Program_Code, rp: ^Reach_Pass, members: []^Type_Scope) {
    cache := &rp.cache
    for f in members { cache^[f] = new(Fun_Summary) }   // (being worked out: a call to one reaches all)
    out := make([]^Fun_Summary, len(members), context.temp_allocator)
    if rp.walk.curr_block == nil { _ = virtual.arena_init_growing(&rp.walk) }
    for f, i in members {
        // (What a summary's walk makes — each node's uses — is let go of
        // once it's worked out: every fun's is.)
        context.temp_allocator = virtual.arena_allocator(&rp.walk)
        defer virtual.arena_free_all(&rp.walk)
        n := len(f.cg_params)
        s := new(Fun_Summary)
        s.reaches, s.returned = make([]bool, n), make([]bool, n)
        pg := graph_fun_code(code, f)
        if _, src := f.origin.(Origin_Source); pg == nil || !src || !reach_summarize(code, cache, f, pg, s) {
            for &r in s.reaches { r = true }
            for &r in s.returned { r = false }
        }
        s.done = true
        out[i] = s
    }
    if code.lock != nil { sync.mutex_lock(code.lock) }
    for f, i in members { code.summaries[f] = out[i] }
    if code.lock != nil { sync.mutex_unlock(code.lock) }
    for f, i in members { cache^[f] = out[i] }
}

// A summary from a fun's code (false: its params aren't the code's). A param
// passed as storage is reached through when its code uses it: an aggregate,
// by any use (it's read where it is); a pointer, unless its value is only
// compared, returned, kept in the result being built, or passed where it
// isn't reached through or returned.
reach_summarize :: proc(code: ^Program_Code, cache: ^Reach_Summaries, f: ^Type_Scope, pg: ^Program_Graph, s: ^Fun_Summary) -> bool {
    // Each node's uses (what it's an operand of, and where), each
    // declaration's variable operations, the params in order.
    Use :: struct { by: Node_Id, at: int }
    uses := make([][dynamic]Use, int(pg.end) + 1, context.temp_allocator)
    for &u in uses { u.allocator = context.temp_allocator }   // (each list grows where the walk's things are)
    vars := make(map[Node_Id][dynamic]Node_Id, allocator = context.temp_allocator)
    params := make([dynamic]Node_Id, context.temp_allocator)
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct: id = graph_last(pg, id); continue   // (another scope's)
        case .Param: append(&params, id)
        case .Op:
            for o, i in graph_operands(pg, id) {
                if o.op > 0 && o.op <= pg.end { append(&uses[o.op], Use{id, i}) }
            }
            if pg.op[id] == .Var {
                d := pg.refers[id]
                if d > 0 && d <= pg.end {   // (not `this_program`, outside the code)
                    if d not_in vars { vars[d] = make([dynamic]Node_Id, context.temp_allocator) }
                    append(&vars[d], id)
                }
            }
        }
    }
    if len(params) != len(f.cg_params) { return false }

    // A place in a local that only becomes the result: written, built, and
    // read only to be returned — a value kept there is returned, not read.
    in_result :: proc(pg: ^Program_Graph, uses: [][dynamic]Use, vars: map[Node_Id][dynamic]Node_Id, place: Node_Id) -> bool {
        at := place
        for pg.op[at] == .Field || pg.op[at] == .Index { at = graph_operands(pg, at)[0].op }
        if pg.op[at] != .Var { return false }
        d := pg.refers[at]
        if d <= 0 || d > pg.end || (pg.kind[d] != .Local && pg.kind[d] != .Result) { return false }
        written_only :: proc(pg: ^Program_Graph, uses: [][dynamic]Use, x: Node_Id) -> bool {
            for u in uses[x] {
                if u.at != 0 { return false }
                #partial switch pg.op[u.by] {
                case .Write, .Construct, .Zero, .Fill, .Arena_Alloc:
                case .Field, .Index: if !written_only(pg, uses, u.by) { return false }
                case .Read:
                    for r in uses[u.by] { if pg.op[r.by] != .Return { return false } }
                case: return false
                }
            }
            return true
        }
        written, _ := vars[d]   // (bound first: `for x in m[k]` faults on a missing key)
        for v in written { if !written_only(pg, uses, v) { return false } }
        return true
    }

    for pn, k in params {
        t := distinct_base(f.cg_params[k].type_)
        if ir, _ := llvm_param_type(t); ir != "ptr" { continue }   // a value: nothing behind it
        if ft, is_fun := t.(^Type_Scope); is_fun && ft.kind == .Fun { continue }
        if _, is_ptr := t.(^Type_Ptr); !is_ptr {
            s.reaches[k] = len(vars[pn]) > 0
            continue
        }
        named, _ := vars[pn]   // (bound first: `for x in m[k]` faults on a missing key — a param never named)
        for v in named {
            for u in uses[v] {
                if pg.op[u.by] != .Read { s.reaches[k] = true; continue }
                for r in uses[u.by] {
                    ok := false
                    #partial switch pg.op[r.by] {
                    case .Compare:
                        ok = true
                    case .Return:
                        ok, s.returned[k] = true, true
                    case .Write:
                        if r.at == 1 && in_result(pg, uses[:], vars, graph_operands(pg, r.by)[0].op) { ok, s.returned[k] = true, true }
                    case .Call, .Construct:
                        c := graph_called(pg, r.by)
                        j := r.at - (1 if pg.op[r.by] == .Construct else 0)
                        if c != nil && j >= 0 {
                            cs := reach_summary(code, cache, c)
                            ok = j < len(cs.reaches) && !cs.reaches[j] && !cs.returned[j]
                        }
                    }
                    if !ok { s.reaches[k] = true }
                }
            }
        }
    }
    return true
}

// A step of a place's path from its variable: a field's, a variant's, an
// element's (its index when it's a number), a pointer's (`cross`: a deref, or
// a slice's element — its data is through a pointer), or another kind.
Place_Step :: struct {
    op:    Op_Kind,
    name:  string,
    index: i128,
    known: bool,
    cross: bool,
}

// A place's path, root first: its variable and each step from it (ok false:
// no variable at its root, or a step no path names).
place_path :: proc(pg: ^Program_Graph, bound: map[Node_Id]Node_Id, p: Node_Id) -> (root: Node_Id, steps: [dynamic]Place_Step, ok: bool) {
    steps = make([dynamic]Place_Step, context.temp_allocator)
    for id := p; id != NO_NODE; {
        ops := graph_operands(pg, id)
        s := Place_Step{op = pg.op[id]}
        #partial switch pg.op[id] {
        case .Var:
            if v, bound := bound[pg.refers[id]]; bound {   // (a match arm's binding: its scrutinee's payload)
                id = v
                continue
            }
            for i in 0 ..< len(steps) / 2 { steps[i], steps[len(steps) - 1 - i] = steps[len(steps) - 1 - i], steps[i] }
            return pg.refers[id], steps, true
        case .Field, .Variant:
            s.name = graph_name(pg, id)
        case .Index:
            at := ops[1].op
            for at != NO_NODE && pg.op[at] == .Cast { at = graph_operands(pg, at)[0].op }
            if c, has := graph_value(pg, at); has && !c.is_float && !c.is_text { s.index, s.known = c.int, true }
            _, s.cross = distinct_base(graph_type(pg, ops[0].op)).(^Type_Slice)
        case .Deref:
            s.cross = true
        case .Slice, .Swizzle:
        case:
            return NO_NODE, steps, false
        }
        append(&steps, s)
        id = ops[0].op
    }
    return NO_NODE, steps, false
}

// Whether two places surely don't overlap: from one variable by the same steps,
// then apart — different fields of a struct, different elements by number —
// with no pointer crossed past where they part (one there could lead anywhere,
// the other place included). Different variants of a union share storage.
places_disjoint :: proc(pg: ^Program_Graph, bound: map[Node_Id]Node_Id, a, b: Node_Id) -> bool {
    ra, sa, oka := place_path(pg, bound, a)
    rb, sb, okb := place_path(pg, bound, b)
    if !oka || !okb || ra != rb { return false }
    n := min(len(sa), len(sb))
    for i in 0 ..< n {
        x, y := sa[i], sb[i]
        if x.op == y.op && x.name == y.name && x.known == y.known && x.index == y.index && (x.op != .Index || x.known) {
            continue   // (the same step: on along it)
        }
        apart := false
        #partial switch x.op {
        case .Field: apart = y.op == .Field && x.name != y.name
        case .Index: apart = y.op == .Index && x.known && y.known && x.index != y.index
        }
        if !apart { return false }
        for s in sa[i + 1:] { if s.cross { return false } }
        for s in sb[i + 1:] { if s.cross { return false } }
        return true
    }
    return false   // (one is the other, or inside it)
}

// Whether two places are one: from one variable by the same steps (elements
// by number).
places_same :: proc(pg: ^Program_Graph, bound: map[Node_Id]Node_Id, a, b: Node_Id) -> bool {
    ra, sa, oka := place_path(pg, bound, a)
    rb, sb, okb := place_path(pg, bound, b)
    if !oka || !okb || ra != rb || len(sa) != len(sb) { return false }
    for x, i in sa {
        y := sb[i]
        if x.op != y.op || x.name != y.name || x.known != y.known || x.index != y.index { return false }
        if x.op == .Index && !x.known { return false }
    }
    return true
}

// Whether two places surely overlap: from one variable by the same steps
// (elements by number) until one ends — it holds the other, or is it.
places_contain :: proc(pg: ^Program_Graph, bound: map[Node_Id]Node_Id, a, b: Node_Id) -> bool {
    ra, sa, oka := place_path(pg, bound, a)
    rb, sb, okb := place_path(pg, bound, b)
    if !oka || !okb || ra != rb { return false }
    for i in 0 ..< min(len(sa), len(sb)) {
        x, y := sa[i], sb[i]
        if x.op != y.op || x.name != y.name || x.known != y.known || x.index != y.index { return false }
        if x.op == .Index && !x.known { return false }
    }
    return true
}

// A match arm's bindings: each the payload's place, the variant it names.
graph_bound :: proc(pg: ^Program_Graph) -> map[Node_Id]Node_Id {
    bound := make(map[Node_Id]Node_Id, allocator = context.temp_allocator)
    for id := Node_Id(1); id <= pg.end; id += 1 {
        if pg.kind[id] == .Op && pg.op[id] == .Variant && pg.refers[id] != NO_NODE { bound[pg.refers[id]] = id }
    }
    return bound
}

// A call or a construction handed `&place` where its result is written —
// place that result's place, or holding it, or inside it (places_contain):
// `v = swap(&v)`, `g.big = make(&g)` would read what it overwrites. The
// program is held to it here, a code at a time once its callees' codes are
// built (reach_code), as escape analysis holds it to its references; codegen,
// which would otherwise have to hide a copy, stops at it too
// (storage_reads_its_dest), should a program get past.
Reach_Pass :: struct {
    cache: Reach_Summaries,
    diags: [dynamic]Reach_Diag,
    walk:  virtual.Arena,   // what working out a summary makes, until the next (reach_scc)
}

Reach_Diag :: struct { span: Span, msg: string }

reach_code :: proc(rp: ^Reach_Pass, code: ^Program_Code, pg: ^Program_Graph) {
    bound := graph_bound(pg)
    // (A temporary's one put: the place its value is written to.)
    puts := make(map[Node_Id]Node_Id, allocator = context.temp_allocator)
    for id := Node_Id(1); id <= pg.end; id += 1 {
        if pg.kind[id] != .Op || pg.op[id] != .Write { continue }
        ops := graph_operands(pg, id)
        v := ops[1].op
        if v == NO_NODE || pg.op[v] != .Read { continue }
        t := graph_operands(pg, v)[0].op
        if pg.op[t] != .Var { continue }
        d := pg.refers[t]
        if d <= 0 || d > pg.end || pg.kind[d] != .Local || pg.written[d] != .Synthetic { continue }
        puts[d] = NO_NODE if d in puts else ops[0].op   // (two: no one place)
    }
    // (Where a value written to place `dest` by operation `w` ends up: a
    // temporary's put; nowhere to check when it's fresh storage — a
    // declaration's local, a temporary with no one put.)
    lands :: proc(pg: ^Program_Graph, puts: map[Node_Id]Node_Id, w, dest: Node_Id) -> (Node_Id, bool) {
        if pg.op[dest] != .Var { return dest, true }
        d := pg.refers[dest]
        if d <= 0 || d > pg.end { return dest, true }
        if pg.kind[d] == .Local && pg.written[d] == .Synthetic {
            x, has := puts[d]
            return x, has && x != NO_NODE
        }
        if s := pg.stmt[w]; s >= 0 && pg.stmts[s].kind == .Decl { return NO_NODE, false }
        return dest, true
    }
    check :: proc(code: ^Program_Code, cache: ^Reach_Summaries, pg: ^Program_Graph, bound: map[Node_Id]Node_Id,
                  op, x: Node_Id, first: int, diags: ^[dynamic]Reach_Diag) {
        callee := graph_called(pg, op)
        if callee == nil { return }
        s := reach_summary(code, cache, callee)
        args := graph_operands(pg, op)[first:]
        if len(args) != len(s.reaches) { return }
        for a, k in args {
            if !s.reaches[k] { continue }
            at := a.op
            for at != NO_NODE && pg.op[at] == .Cast { at = graph_operands(pg, at)[0].op }
            if at == NO_NODE || pg.op[at] != .Address { continue }
            place := graph_operands(pg, at)[0].op
            if !places_contain(pg, bound, place, x) { continue }
            name := scope_display_name(callee)
            into := graph_place_name(pg, Operand{op = x})
            msg := fmt.aprintf(TYPE_RESULT_READS_DEST, name, graph_place_name(pg, Operand{op = place}), into, name, into)
            append(diags, Reach_Diag{pg.origin[op], msg})
            return
        }
    }
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct: if id != 0 { id = graph_last(pg, id); continue }   // (another scope's)
        }
        if pg.kind[id] != .Op { continue }
        ops := graph_operands(pg, id)
        #partial switch pg.op[id] {
        case .Write:
            // (A result built where it's written: an aggregate's. A
            // number comes back as a value — nothing built over anything.)
            if v := ops[1]; v.op != NO_NODE && pg.op[v.op] == .Call {
                callee := graph_called(pg, v.op)
                if callee == nil || int(v.out) >= len(callee.cg_returns) || !graph_aggregate(callee.cg_returns[v.out]) { continue }
                if x, ok := lands(pg, puts, id, ops[0].op); ok { check(code, &rp.cache, pg, bound, v.op, x, 0, &rp.diags) }
            }
        case .Construct:
            if len(ops) > 1 {
                if x, ok := lands(pg, puts, id, ops[0].op); ok { check(code, &rp.cache, pg, bound, id, x, 1, &rp.diags) }
            }
        }
    }
}

// Every code's — every pass's — reported in source order.
reach_report :: proc(c: ^Checker, passes: []^Reach_Pass) {
    diags := make([dynamic]Reach_Diag, context.temp_allocator)
    for rp in passes {
        append(&diags, ..rp.diags[:])
        delete(rp.diags)
        delete(rp.cache)
    }
    slice.sort_by(diags[:], proc(a, b: Reach_Diag) -> bool {
        if span_before(a.span, b.span) { return true }
        if span_before(b.span, a.span) { return false }
        return a.msg < b.msg
    })
    for d in diags { check_error(c, d.span, "%s", d.msg) }
    for rp in passes { virtual.arena_destroy(&rp.walk) }
}
