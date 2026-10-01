package mara

// A take: `let(T, s)` a value of T carved from storage, `slice([:n]T, s)` n
// of them as a slice, `slice(s)` a slice of the type its use expects. The
// storage: `&bytes` (a cursor, advanced: ^[]byte) or `&bytes[i]` (at a
// place: ^byte).

// Built: the count at the header's width, then the storage it carves from (a
// plain place, built where the carve is), then the carve.
tc_take :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Build_Want, w: Written) -> (Type, Built) {
    t := k.t
    span := tree_span(t, n)
    ty, storage := Tree_Id(t.a[n]), Tree_Id(t.b[n])
    hint := k.hint
    // (`[:n]T`: n counted at run time, the slice []T.)
    count := Tree_Id(0)
    taken: Type
    switch {
    case ty == 0:
        if is_slice_type(hint) {
            taken = hint
        } else {
            tc_error(k, span, TYPE_TAKE_UNKNOWN_TYPE)
            taken = Type_Error{}
        }
    case t.tag[ty] == .Type_Slice && t.a[ty] != 0:
        count = Tree_Id(t.a[ty])
        taken = new_clone(Type_Slice{elem = tc_type(k, Tree_Id(t.b[ty]), env, span)})
    case t.tag[ty] == .Type_Slice && tc_count_arg(k, Tree_Id(t.b[ty]), take = true) != 0:
        // (`[]T(n)`: the same.)
        count = tc_count_arg(k, Tree_Id(t.b[ty]), take = true)
        taken = new_clone(Type_Slice{elem = tc_generic_base(k, Tree_Id(t.b[ty]), env, span)})
    case:
        taken = tc_type(k, ty, env, span)
        if _, is_err := taken.(Type_Error); is_err { tc_error(k, span, TYPE_TAKE_UNKNOWN_TYPE) }
    }
    b := tc_building(k) if want != .None else nil
    if b != nil && (want == .Place || !tc_carves_place(k, storage)) {
        tc_fail(k, "a take's place, or a take from no plain place")
        b = nil
    }
    count_op := NO_VALUE
    if count != 0 {
        ct: Type
        ct, count_op = tc_bound(k, count, env, w, span, b != nil)
        if !is_any(ct) && !is_numeric(ct) {
            tc_error(k, span, TYPE_TAKE_COUNT_INTEGER, type_name(ct))
        } else if !coerces_to_slice_width(ct) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ct))
        }
    }
    // (`&x`: its address — a view of bytes the carve's, not the use's.)
    st: Type
    from := NO_VALUE
    su := tc_unparen(k, storage)
    addressed := t.tag[su] == .Unary
    if b != nil {
        r: Built
        st, r = tc_expr(k, storage, env, .Value if addressed else .Place)
        from = r.v
        if addressed { delete_key(&k.byte_addrs, tc_sid(k, su)) }
    } else {
        st = tc_check(k, storage, env)
    }
    // (A cursor is ^[]byte: a []byte would be a header of the call's own,
    // its takes each from 0.)
    cursor, at_byte := false, false
    if pt, is_ptr := distinct_base(st).(^Type_Ptr); is_ptr {
        #partial switch elem in distinct_base(pt.elem) {
        case ^Type_Slice:
            _, cursor = elem.elem.(Type_Byte)
        case Type_Byte:
            at_byte = true
        }
    }
    if !cursor && !at_byte && !is_any(st) { tc_error(k, span, TYPE_TAKE_REQUIRES_BYTE_CURSOR_FORM, type_name(st)) }
    if b = tc_building(k); b == nil || want == .None { return taken, {} }
    keyword := tc_text(t.main[n])
    v := graph_build_carve(b, span, keyword, taken, from, st, addressed, t.tag[su] == .Self, count_op, w)
    return taken, {v = v, ok = true}
}

// Whether a take's storage is a plain place (`&s`, `&bytes[i]`, `s`): what
// is walked where the carve is.
tc_carves_place :: proc(k: ^TC, storage: Tree_Id) -> bool {
    su := tc_unparen(k, storage)
    if k.t.tag[su] == .Unary && build_tokens[k.t.main[su]].kind == .Ampersand { return tc_pure_place(k, Tree_Id(k.t.a[su])) }
    return tc_pure_place(k, storage)
}

// `x := let(T, s)`, `x : T = slice([:n]T, s)`: the local bound to the
// memory taken (a `let`'s, no space of its own on the arena), the take into
// it; an annotation, the take's type.
tc_decl_take :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, env, fields_of: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    b := tc_building(k)
    decl := NO_NODE
    field := false
    if b != nil {
        decl = tc_field_decl(k, fields_of, name, target, value, span)
        field = decl != NO_NODE
        if !field { decl = graph_build_decl(b, name, span, bound = tc_text(t.main[tc_unparen(k, value)]) == "let") }
    }
    vt: Type
    r: Built
    if b != nil {
        vt, r = tc_expr(k, value, env, .Into, dest = graph_dest_var(name, decl, nil if is_untyped(ann) else ann))
    } else {
        vt = tc_check(k, value, env)
    }
    if !is_any(ann) && types_incompatible(ann, vt) && !value_preserving_widen(vt, ann) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(ann))
    }
    final := vt if is_any(ann) else ann
    scope_bind(env, name, final)
    tc_note_decl(k, name, final, span, true)
    if fields_of != nil && is_any(ann) { tc_add_field(fields_of, name, final, value) }
    if b = tc_building(k); b == nil { return }
    if field { final = b.g.type_[decl] }   // (a field: its struct's type)
    graph_build_typed(b, decl, final)
    tc_store(k, value, vt, r, graph_dest_var(name, decl, final), span, settle = true)
}
