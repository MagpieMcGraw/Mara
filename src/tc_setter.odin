package mara

import "core:slice"
import "core:strings"

// `set_x :: #setter (…) {…}`: the fields it writes — it or a helper only it
// calls — are written by it alone. Anywhere else, a write of one is warned:
// it skips what the setter keeps in step (`set_scale` writes scale and
// radius). The struct's own constructor may write them; a field has one
// setter. (The user's design, 2026-11-21.)

Setter_Mark :: struct { fun: ^Type_Scope, span: Span }
Field_Write :: struct { decl: Token_Id, at: Syntax_Id }   // (its place: at's node)

// A fun marked `#setter` (span: the mark), its body about to be checked.
tc_setter_mark :: proc(k: ^TC, fun: ^Type_Scope, span: Span) {
    for m in k.setters { if m.fun == fun { return } }
    append(&k.setters, Setter_Mark{fun, span})
}

// A write's target: each field it writes, its own or one it is part of
// (`o.scale.x = 3` writes scale) — not past a pointer or a slice's items,
// which are written where they are, not in what holds the reference.
tc_note_field_writes :: proc(k: ^TC, target: Tree_Id) {
    tr := k.t
    for cur := target; true; {
        #partial switch tr.tag[cur] {
        case .Paren:
            cur = Tree_Id(tr.a[cur])
            continue
        case .Field, .Index, .Slice:
            if tr.tag[cur] == .Field {
                if ref := tc_ref(k, cur); ref.kind == .Field { tc_note_field_write(k, ref.decl, cur) }
            }
            inner := Tree_Id(tr.a[cur])
            #partial switch _ in distinct_base(tc_node_type(k, inner)) {
            case ^Type_Ptr, ^Type_Slice: return
            }
            cur = inner
            continue
        case .Ident:
            // (A struct's own field by its bare name, in its body.)
            if ref := k.names.refs[cur]; ref.kind == .Field { tc_note_field_write(k, ref.decl, cur) }
        }
        return
    }
}

tc_note_field_write :: proc(k: ^TC, decl: Token_Id, n: Tree_Id) {
    if decl != 0 { append(&k.field_writes, Field_Write{decl, tc_sid(k, n)}) }
}

// The check's end: each setter's fields, each write of one elsewhere warned.
tc_setters_report :: proc(k: ^TC) {
    if len(k.setters) == 0 { return }
    // (In written order, not checked order: a staged check's differs.)
    slice.sort_by(k.setters[:], proc(x, y: Setter_Mark) -> bool { return x.span.at < y.span.at })
    a := k.annot
    rc := cg_runs_make(a, k.t)
    defer cg_runs_free(&rc)
    // (Who calls whom: the call graph's edges, from the annotations as it
    // makes them — build_call_graph — a call through a fun's value none.)
    callees := make(map[^Type_Scope][dynamic]^Type_Scope, allocator = context.temp_allocator)
    callers := make(map[^Type_Scope][dynamic]^Type_Scope, allocator = context.temp_allocator)
    for key, callee in a.callees {
        if a.forms[key] == .Value { continue }
        to := callee
        if needed, is_needed := to.origin.(Origin_Required); is_needed && needed.of != nil { to = needed.of }
        from, _ := cg_runs_in(&rc, key)
        for f in from {
            if f not_in callees { callees[f] = make([dynamic]^Type_Scope, context.temp_allocator) }
            if to not_in callers { callers[to] = make([dynamic]^Type_Scope, context.temp_allocator) }
            append(&callees[f], to)
            append(&callers[to], f)
        }
    }
    // (Each write, by the funs it runs in.)
    writes_in := make(map[^Type_Scope][dynamic]int, allocator = context.temp_allocator)
    runs := make([][]^Type_Scope, len(k.field_writes), context.temp_allocator)
    for w, i in k.field_writes {
        in_, _ := cg_runs_in(&rc, w.at)
        runs[i] = slice.clone(in_, context.temp_allocator)
        for f in runs[i] {
            if f not_in writes_in { writes_in[f] = make([dynamic]int, context.temp_allocator) }
            append(&writes_in[f], i)
        }
    }
    // Each setter's own: it, and what it calls that nothing else calls —
    // what it reaches, less any one called from outside them, until none is.
    own := make([]map[^Type_Scope]bool, len(k.setters), context.temp_allocator)
    reach := make([]map[^Type_Scope]bool, len(k.setters), context.temp_allocator)
    for m, si in k.setters {
        set := make(map[^Type_Scope]bool, allocator = context.temp_allocator)
        todo := make([dynamic]^Type_Scope, context.temp_allocator)
        set[m.fun] = true
        append(&todo, m.fun)
        for len(todo) > 0 {
            f := pop(&todo)
            for c in callees[f] or_else nil { if c not_in set { set[c] = true; append(&todo, c) } }
        }
        reach[si] = make(map[^Type_Scope]bool, len(set), context.temp_allocator)
        for f in set { reach[si][f] = true }
        for {
            out := make([dynamic]^Type_Scope, context.temp_allocator)
            for f in set {
                if f == m.fun { continue }
                for c in callers[f] or_else nil { if c not_in set { append(&out, f); break } }
            }
            if len(out) == 0 { break }
            for f in out { delete_key(&set, f) }
        }
        own[si] = set
    }
    // The fields each one writes: of the structs it's given or writes
    // itself, those anything it calls writes too (so a helper something
    // else calls is said, not missed) — not every struct a call deep in it
    // touches (an arena's). One setter a field.
    owner := make(map[Token_Id]Tree_Id, allocator = context.temp_allocator)   // (each field's struct, its definition: a generic's instances one)
    for sc in k.scopes {
        if sc.ts == nil || sc.ts.kind != .Struct { continue }
        for f in sc.ts.fields { if f.decl != 0 && f.decl not_in owner { owner[f.decl] = sc.ts.node } }
    }
    setter_of := make(map[Token_Id]int, allocator = context.temp_allocator)
    clash := make(map[Token_Id]bool, allocator = context.temp_allocator)
    for m, si in k.setters {
        structs := make(map[Tree_Id]bool, allocator = context.temp_allocator)
        for i in writes_in[m.fun] or_else nil { if o, known := owner[k.field_writes[i].decl]; known { structs[o] = true } }
        for p in m.fun.params {
            t := distinct_base(p.type_)
            if pt, is_ptr := t.(^Type_Ptr); is_ptr { t = distinct_base(pt.elem) }
            if ts, is_scope := t.(^Type_Scope); is_scope && ts.kind == .Struct { structs[ts.node] = true }
        }
        for f in reach[si] {
            for i in writes_in[f] or_else nil {
                d := k.field_writes[i].decl
                if owner[d] not_in structs { continue }
                if was, taken := setter_of[d]; taken {
                    if was != si && d not_in clash {
                        clash[d] = true
                        tc_error(k, m.span, TYPE_SETTER_FIELD_TWICE, tc_text(d), scope_path_name(m.fun), scope_path_name(k.setters[was].fun))
                    }
                    continue
                }
                setter_of[d] = si
            }
        }
    }
    // Every write of one: in its setter's own funs, or its struct's
    // constructor; else warned, once a place — a helper it calls that
    // something else calls too, said so.
    said := make(map[u64]bool, allocator = context.temp_allocator)
    for w, i in k.field_writes {
        si, guarded := setter_of[w.decl]
        if !guarded || w.decl in clash { continue }
        m := k.setters[si]
        _, n := annot_split(w.at)
        span := tree_span(k.t, n)
        for f in runs[i] {
            if f in own[si] || tc_declares_field(f, w.decl) { continue }
            key := u64(span.at) << 32 | u64(w.decl)
            if key in said { continue }
            said[key] = true
            name, setter := tc_text(w.decl), scope_path_name(m.fun)
            if f in reach[si] {
                outside: ^Type_Scope
                for c in callers[f] or_else nil { if c not_in own[si] { outside = c; break } }
                check_warning(k.c, span, WARN_SETTER_HELPER_SHARED, name, setter, scope_path_name(f), setter, scope_path_name(outside) if outside != nil else "another fun")
                continue
            }
            others := make([dynamic]string, context.temp_allocator)
            for d, s in setter_of {
                if s == si && d != w.decl { append(&others, tc_text(d)) }
            }
            slice.sort(others[:])
            if len(others) > 0 {
                check_warning(k.c, span, WARN_SETTER_SKIPPED_ALSO, name, setter, strings.join(others[:], ", ", context.temp_allocator), setter)
            } else {
                check_warning(k.c, span, WARN_SETTER_SKIPPED, name, setter, setter)
            }
        }
    }
}

// Whether a struct declares the field (decl): its constructor may write it.
tc_declares_field :: proc(ts: ^Type_Scope, decl: Token_Id) -> bool {
    if ts.kind != .Struct { return false }
    for f in ts.fields { if f.decl == decl { return true } }
    return false
}
