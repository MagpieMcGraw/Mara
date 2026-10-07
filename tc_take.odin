package mara

// A take: `let(T, s)` a value of T carved from storage, `slice([:n]T, s)` n
// of them as a slice, `slice(s)` a slice of the type its use expects. The
// storage: `&bytes` (a cursor, advanced: ^[]byte) or `&bytes[i]` (at a
// place: ^byte).

// Its type; its count, an integer at the header's width; its storage, a
// cursor or a byte's place.
tc_take :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
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
    if count != 0 {
        ct := tc_check_at(k, count, env, slice_header_width_type)
        if !is_any(ct) && !is_numeric(ct) {
            tc_error(k, span, TYPE_TAKE_COUNT_INTEGER, type_name(ct))
        } else if !coerces_to_slice_width(ct) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ct))
        }
    }
    // (A cursor is ^[]byte: a []byte would be a header of the call's own,
    // its takes each from 0.)
    st := tc_check(k, storage, env)
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
    return taken
}

// `x := let(T, s)`, `x : T = slice([:n]T, s)`: the local bound to the
// memory taken (a `let`'s, no space of its own on the arena); an
// annotation, the take's type.
tc_decl_take :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, env, fields_of: ^Type_Scope) {
    span := tree_span(k.t, s)
    ref := tc_decl_ref(k, target, fields_of)
    vt := tc_check(k, value, env)
    if !is_any(ann) && types_incompatible(ann, vt) && !value_preserving_widen(vt, ann) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(ann))
    }
    final := vt if is_any(ann) else ann
    tc_bind(k, env, name, final, ref)
    tc_set_type(k, target, final)
    tc_note_decl(k, name, final, span, true)
    if fields_of != nil && is_any(ann) { tc_add_field(fields_of, name, ref.decl, final, value) }
}
