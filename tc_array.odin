package mara

// Arrays in the checker: an element read or written, an array literal.

// `a[i]`: its collection (through a pointer, what it points at), the index at
// the header's width — the element.
tc_index :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    base_n, idx_n := Tree_Id(tr.a[n]), Tree_Id(tr.b[n])
    tc_lower_dots(k, base_n, idx_n)
    bt := tc_check(k, base_n, env)
    target := distinct_base(bt)
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array, ^Type_Partial_Array: target = distinct_base(pt.elem)
        }
    }
    if fa, ok := target.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it := tc_check_at(k, idx_n, env, slice_header_width_type)
    if !is_numeric(it) {
        tc_error(k, span, TYPE_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    t: Type = Type_Error{}
    #partial switch v in target {
    case ^Type_Fixed_Array:
        // (A known index past its end: said so now.)
        if at, known := tc_comptime_int(k, idx_n, nil); known && (at < 0 || at >= i64(v.size)) {
            tc_error(k, span, TYPE_INDEX_OUT_OF_BOUNDS_CONST, at, v.size, v.size - 1)
        }
        t = v.elem
    case ^Type_Slice:         t = v.elem
    case ^Type_Partial_Array: t = v.elem
    case:
        if !is_any(target) { tc_error(k, span, TYPE_CANNOT_INDEX_INTO, type_name(target)) }
    }
    return t
}

// `a[i] = v`: the element, then the value into it.
tc_index_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    diag := value if op_tok == 0 else 0   // (the value, as diagnostics name it)
    tr := k.t
    span := tree_span(tr, s)
    base_n, idx_n := Tree_Id(tr.a[target]), Tree_Id(tr.b[target])
    tc_lower_dots(k, base_n, idx_n)
    if tr.tag[base_n] == .Ident && tc_name(k, base_n) in k.consts {
        name := tc_name(k, base_n)
        tc_error(k, span, TYPE_CANNOT_WRITE_INDEXED_CONSTANT, name, name)
        return
    }
    ct := tc_check(k, base_n, env)
    tt := distinct_base(ct)
    elem := index_elem_type(tt)
    tc_set_type(k, target, elem)
    if fa, ok := tt.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it := tc_check_at(k, idx_n, env, slice_header_width_type)
    #partial switch v in tt {
    case ^Type_Fixed_Array:   k.hint = v.elem
    case ^Type_Partial_Array: if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    case ^Type_Slice:         if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    }
    if is_byte_buffer(ct) {
        // (Into bytes: the value's raw bytes, the element's place a view.)
        tc_byte_write(k, s, target, value, it, env, op_tok)
        return
    }
    vt := tc_store_at(k, value, env, op_tok, target, s)
    tc_settle(k, diag, elem)
    if !is_numeric(it) && !is_any(it) {
        tc_error(k, span, TYPE_ARRAY_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER, pname)
    }
    size := -1   // (a fixed array's, for its diagnostic)
    #partial switch v in tt {
    case ^Type_Fixed_Array: size = v.size
    case ^Type_Partial_Array, ^Type_Slice:
    case:
        return
    }
    if !is_infer(vt) && !buffer_elem_compatible(elem, vt) && !value_preserving_widen(vt, elem) {
        if size >= 0 {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_ELEMENT, type_name(vt), size, type_name(elem))
        } else {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_ELEMENT_TYPE, type_name(vt), type_name(tt))
        }
    }
    if is_infer(vt) { tc_literal_overflow(k, diag, elem, span) }
}

// `.len`, `.cap` in a subscript of a plain name (`a.b[.len - 1]`): its
// base's — checked as `base.len` where it is written (tc_field).
tc_lower_dots :: proc(k: ^TC, base, sub: Tree_Id) {
    if sub == 0 || !tc_plain_name(k, base) { return }
    t := k.t
    #partial switch t.tag[sub] {
    case .Dot_Ident:
        name := tc_text(Token_Id(t.a[sub]))
        if (name == "len" || name == "cap") && tc_sid(k, sub) not_in k.annot.dot_bases { k.annot.dot_bases[tc_sid(k, sub)] = base }
    case .Binary:
        tc_lower_dots(k, base, Tree_Id(t.a[sub]))
        tc_lower_dots(k, base, Tree_Id(t.b[sub]))
    case .Unary, .Deref, .Paren:
        tc_lower_dots(k, base, Tree_Id(t.a[sub]))
    }
}

// A name, or a field of one (`a.b.c`): walked again, the same place.
tc_plain_name :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[n] {
    case .Ident: return true
    case .Field: return tc_plain_name(k, Tree_Id(k.t.a[n]))
    }
    return false
}

// `[a, b, c]`: each element, the first's type the literal's element type.
// (Empty: typed by where it goes.)
tc_array_literal :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    elems := tree_list(tr, tr.a[n])
    if len(elems) == 0 { return Type_Error{} }
    et := tc_check(k, elems[0], env)
    for e, i in elems[1:] {
        if t := tc_check(k, e, env); types_incompatible(et, t) {
            tc_error(k, span, TYPE_ARRAY_ELEMENT_TYPE_EXPECTED, i + 1, type_name(t), type_name(et))
        }
    }
    for e in elems { tc_settle(k, e, et) }   // (each written to its slot, at its type)
    return new_clone(Type_Fixed_Array{size = len(elems), elem = et})
}

// `a[lo:hi]`: its collection, its bounds at the header's width — a slice of
// its elements.
tc_slice :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    base_n := Tree_Id(tr.a[n])
    lo_n, hi_n := tree_pair(tr, n)
    tc_lower_dots(k, base_n, lo_n)
    tc_lower_dots(k, base_n, hi_n)
    tt := tc_check(k, base_n, env)
    // (A named type — `str64`, a distinct array — sliced as its base is.)
    target := distinct_base(tt)
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array, ^Type_Partial_Array: target = distinct_base(pt.elem)
        }
    }
    // (A slice of an array in this_program — not of a slice, whose view it
    // shares — would be a view that writes it.)
    if _, of_slice := target.(^Type_Slice); !of_slice && tc_in_program(k, base_n) {
        tc_error(k, span, TYPE_PROGRAM_READ_ONLY, "slice", " (a slice can write what it views)")
    }
    elem: Type
    #partial switch v in target {
    case ^Type_Fixed_Array:   elem = v.elem
    case ^Type_Slice:         elem = v.elem
    case ^Type_Partial_Array: elem = v.elem
    case:
        if !is_any(target) {
            tc_error(k, span, TYPE_CANNOT_SLICE, type_name(target))
            return Type_Error{}
        }
    }
    if lo_n != 0 {
        lt := tc_check_at(k, lo_n, env, slice_header_width_type)
        if !is_numeric(lt) && !is_any(lt) {
            tc_error(k, span, TYPE_SLICE_LOW_BOUND_NUMERIC, type_name(lt))
        } else if !coerces_to_slice_width(lt) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(lt))
        }
    }
    if hi_n != 0 {
        ht := tc_check_at(k, hi_n, env, slice_header_width_type)
        if !is_numeric(ht) && !is_any(ht) {
            tc_error(k, span, TYPE_SLICE_HIGH_BOUND_NUMERIC, type_name(ht))
        } else if !coerces_to_slice_width(ht) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ht))
        }
    }
    if elem == nil { return Type_Error{} }
    return new_clone(Type_Slice{elem = elem})
}

// `a[lo:hi] = v`: the target's slice — its collection, its bounds — then
// the value into its elements. Into bytes, a value no array is written as
// its own type at lo (a view: tc_byte_span_checks).
tc_slice_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, s)
    base_n := Tree_Id(tr.a[target])
    lo_n, hi_n := tree_pair(tr, target)
    tc_lower_dots(k, base_n, lo_n)
    tc_lower_dots(k, base_n, hi_n)
    tt := tc_check(k, base_n, env)
    if elem := index_elem_type(tt); elem != nil {   // (the target names a run of elements)
        tc_set_type(k, target, new_clone(Type_Slice{elem = elem}))
    }
    lt, ht: Type = Type_Any{}, Type_Any{}
    if lo_n != 0 { lt = tc_check_at(k, lo_n, env, slice_header_width_type) }
    if hi_n != 0 { ht = tc_check_at(k, hi_n, env, slice_header_width_type) }
    vt := tc_check(k, value, env)
    if !is_numeric(lt) && !is_any(lt) {
        tc_error(k, span, TYPE_SLICE_LOWER_BOUND_NUMBER, type_name(lt))
    } else if !coerces_to_slice_width(lt) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(lt))
    }
    if hi_n != 0 && !is_numeric(ht) && !is_any(ht) {
        tc_error(k, span, TYPE_SLICE_UPPER_BOUND_NUMBER, type_name(ht))
    } else if hi_n != 0 && !coerces_to_slice_width(ht) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ht))
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_SLICE_ASSIGN_INTO_IMMUTABLE, pname)
    }
    if is_byte_buffer(tt) {
        if view := tc_byte_span_checks(k, lo_n, hi_n, tt, vt, span); view != nil { return }
    }
    fa, is_array := distinct_base(tt).(^Type_Fixed_Array)
    if !is_array { return }
    #partial switch v in distinct_base(vt) {
    case ^Type_Fixed_Array:
        if types_incompatible(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_SLICE_ASSIGN_INTO, v.size, type_name(v.elem), fa.size, type_name(fa.elem))
        }
    case ^Type_Slice:
        if types_incompatible(fa.elem, v.elem) { tc_error(k, span, TYPE_CANNOT_SLICE_ASSIGN_INTO_2, type_name(v.elem), fa.size, type_name(fa.elem)) }
    case ^Type_Partial_Array:
        if types_incompatible(fa.elem, v.elem) { tc_error(k, span, TYPE_CANNOT_SLICE_ASSIGN_INTO_2, type_name(v.elem), fa.size, type_name(fa.elem)) }
    case:
        if !is_any(vt) { tc_error(k, span, TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE, type_name(vt)) }
    }
}
