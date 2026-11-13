package mara

import "core:fmt"

// Arrays in the checker: an element read or written, an array literal.

// `a[i]`: its collection (through a pointer, what it points at), the index at
// the header's width — the element.
tc_index :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    base_n, idx_n := Tree_Id(tr.a[n]), Tree_Id(tr.b[n])
    tc_lower_dots(k, base_n, idx_n)
    k.list_at = tc_unparen(k, base_n)
    bt := tc_check(k, base_n)
    // (A field reference's array, `r[i]`: a reference to its item. A struct
    // indexed, `events[f]`: the field f is a reference to — field_ref.odin.)
    if fr, is_ref := distinct_base(bt).(^Type_Field); is_ref { return tc_field_ref_index(k, n, idx_n, fr, span) }
    if st := index_struct(bt); st != nil { return tc_index_by_field(k, idx_n, st, span) }
    target := distinct_base(bt)
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array, ^Type_Partial_Array: target = distinct_base(pt.elem)
        }
    }
    if fa, ok := target.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it := tc_check_at(k, idx_n, slice_header_width_type)
    if !is_numeric(it) {
        tc_error(k, span, TYPE_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    t: Type = Type_Error{}
    #partial switch v in target {
    case ^Type_Fixed_Array:
        // (A known index past its end: said so now.)
        if at, known := tc_comptime_int(k, idx_n); known && (at < 0 || at >= i64(v.size)) {
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

// A list declared with nothing in it that no code gives a len stays empty:
// an index into it is past its len, and a loop over it runs no times —
// warned once the program is checked, where it is first indexed or looped
// over (Indexed: either). A list's declaration (a local's, a
// global's, a field's) is Fresh when it is given no value, and Changed by
// any use that could give it one: all but an index's base, a `.len` or
// `.cap` read, a loop over it and an argument that is the list itself, by
// value (k.list_at, k.list_ok: the node about to be checked as one of those).
List_Flag    :: enum u8 { Fresh, Changed, Indexed }
List_Flags   :: bit_set[List_Flag; u8]
List_Indexed :: struct { decl: Token_Id, span: Span, loop: bool }

// A use of a list's name: `ok`, one that can't change it; `index`, an index's base.
tc_list_use :: proc(k: ^TC, decl: Token_Id, t: Type, ok, index: bool, span: Span) {
    if decl == 0 || !is_partial_array(t) { return }
    if !ok && !index {
        k.lists[decl] += {.Changed}
    } else if index && .Indexed not_in k.lists[decl] {
        k.lists[decl] += {.Indexed}
        append(&k.list_indexed, List_Indexed{decl, span, false})
    }
}

// A loop over a list's name (n, checked): as an index is, what only a list
// with a len answers.
tc_list_looped :: proc(k: ^TC, n: Tree_Id, t: Type) {
    if !is_partial_array(t) { return }
    r := tc_ref(k, n)
    if r.decl == 0 || (r.kind != .Local && r.kind != .Field) || .Indexed in k.lists[r.decl] { return }
    k.lists[r.decl] += {.Indexed}
    append(&k.list_indexed, List_Indexed{r.decl, tree_span(k.t, n), true})
}

// A value of type `t` read out of raw memory (bytes, a take): the lists in
// it come with the lens written there.
tc_lists_raw :: proc(k: ^TC, t: Type) {
    #partial switch v in distinct_base(t) {
    case ^Type_Fixed_Array:   tc_lists_raw(k, v.elem)
    case ^Type_Partial_Array: tc_lists_raw(k, v.elem)
    case ^Type_Slice:         tc_lists_raw(k, v.elem)
    case ^Type_Union:
        for _, vs in v.variant_structs { tc_lists_raw(k, vs) }
    case ^Type_Scope:
        if v.kind != .Struct || k.lists_raw[v] { return }
        k.lists_raw[v] = true
        for f in v.fields {
            tc_list_use(k, f.decl, f.type_, false, false, {})
            tc_lists_raw(k, f.type_)
        }
    }
}

tc_lists_report :: proc(k: ^TC) {
    for u in k.list_indexed {
        if f := k.lists[u.decl]; .Fresh in f && .Changed not_in f {
            check_warning(k.c, u.span, WARN_LIST_STAYS_EMPTY, tc_text(u.decl), "looped over" if u.loop else "indexed", "the loop" if u.loop else "a loop over it")
        }
    }
}

// `a[i] = v`: the element, then the value into it.
tc_index_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    diag := value if op_tok == 0 else 0   // (the value, as diagnostics name it)
    tr := k.t
    span := tree_span(tr, s)
    base_n, idx_n := Tree_Id(tr.a[target]), Tree_Id(tr.b[target])
    tc_lower_dots(k, base_n, idx_n)
    if tr.tag[base_n] == .Ident && k.names.refs[base_n].kind == .Const {
        name := tc_name(k, base_n)
        tc_error(k, span, TYPE_CANNOT_WRITE_INDEXED_CONSTANT, name, name)
        return
    }
    k.list_at = tc_unparen(k, base_n)
    ct := tc_check(k, base_n)
    if st := index_struct(ct); st != nil {
        // (`events[f] = v`: the field f is a reference to, written.)
        field_t := tc_index_by_field(k, idx_n, st, tree_span(tr, target))
        tc_set_type(k, target, field_t)
        k.hint = field_t
        tc_store_at(k, value, op_tok, target, s)
        tc_settle(k, diag, field_t)
        if pname, immutable := tc_write_root_param(k, target); immutable {
            tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, fmt.tprintf("[%s]", tc_written(k, idx_n)), pname)
        }
        return
    }
    tt := distinct_base(ct)
    elem := index_elem_type(tt)
    tc_set_type(k, target, elem)
    if fa, ok := tt.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it := tc_check_at(k, idx_n, slice_header_width_type)
    #partial switch v in tt {
    case ^Type_Fixed_Array:   k.hint = v.elem
    case ^Type_Partial_Array: if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    case ^Type_Slice:         if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    }
    if is_byte_buffer(ct) {
        // (Into bytes: the value's raw bytes, the element's place a view.)
        tc_byte_write(k, s, target, value, it, op_tok)
        return
    }
    vt := tc_store_at(k, value, op_tok, target, s)
    tc_settle(k, diag, elem)
    if !is_numeric(it) && !is_any(it) {
        tc_error(k, span, TYPE_ARRAY_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    if pname, immutable := tc_write_root_param(k, target); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER, pname)
    }
    size := -1   // (a fixed array's, for its diagnostic)
    #partial switch v in tt {
    case ^Type_Fixed_Array: size = v.size
    case ^Type_Partial_Array, ^Type_Slice:
    case:
        return
    }
    if !is_infer(vt) && !buffer_elem_compatible(elem, vt) {
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
tc_array_literal :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    elems := tree_list(tr, tr.a[n])
    // (The element type of where it goes, when that's an array.)
    place: Type
    #partial switch v in distinct_base(k.hint) {
    case ^Type_Slice:         place = v.elem
    case ^Type_Partial_Array: place = v.elem
    case ^Type_Fixed_Array:   place = v.elem
    }
    if len(elems) == 0 {
        // (`[]`: none, of the element type its place takes — a view of
        // nothing, an empty list. Where a slice goes, the empty slice
        // itself: it views nothing, so it can be given back (`return []`)
        // or kept anywhere. With no place saying, said so.)
        if _, to_slice := distinct_base(k.hint).(^Type_Slice); to_slice { return k.hint }
        if place != nil { return type_fixed_array(0, place) }
        if _, failed := k.hint.(Type_Error); !failed { tc_error(k, span, TYPE_EMPTY_ARRAY_NO_TYPE) }
        return Type_Error{}
    }
    _, into_bytes := distinct_base(place).(Type_Byte)
    // An element's type. Into bytes (`data : [4!]byte = [1, 0, 0, 0]`), an
    // int literal is one byte, from 0 to 255, as a comparison with a byte
    // takes it (tc_byte_compare). Any other number is refused: a byte isn't
    // a number.
    elem_type :: proc(k: ^TC, e: Tree_Id, i: int, into_bytes: bool, place: Type) -> Type {
        k.hint = place   // (each element's hint its place's element type)
        t := tc_check(k, e)
        if !into_bytes { return t }
        at := tree_span(k.t, e)
        if lit, is_int := t.(Type_Infer_Int); is_int && lit.cell == nil {
            if v, known := tc_comptime_int(k, e); known && (v < 0 || v > 255) {
                tc_error(k, at, TYPE_CONSTANT_OVERFLOWS_RANGE_2, v, type_name(place), 255)
            }
            return place
        }
        if is_numeric(t) {
            tc_error(k, at, TYPE_BYTE_ELEMENT_NUMBER, i + 1, tc_written(k, e), type_name(solidify_type(t)))
            return place
        }
        return t
    }
    et := elem_type(k, elems[0], 0, into_bytes, place)
    for e, i in elems[1:] {
        // (A pointee's width not yet decided, either side: decided by the other.)
        if t := elem_type(k, e, i + 1, into_bytes, place); !coerce_deferred_pointee(k.c, t, et, span) && !coerce_deferred_pointee(k.c, et, t, span) && types_incompatible(et, t) {
            tc_error(k, span, TYPE_ARRAY_ELEMENT_TYPE_EXPECTED, i + 1, type_name(t), type_name(et))
        }
    }
    // (Items laid out otherwise than their place's are made as its items:
    // where slices go, slices of them — `first(["walk", "run"])` hands over
    // slices of the text; rows where longer fixed arrays go, the rest zero,
    // or where lists with room for them go. With no place, text is kept as
    // lists, and such an array is no slice of slices: item_layout_mismatch.)
    if place != nil && item_layout_mismatch(place, et) && buffer_elem_compatible(place, et) {
        _, as_place := distinct_base(place).(^Type_Slice)
        if from, is_fixed := distinct_base(resolve_infer(et)).(^Type_Fixed_Array); is_fixed {
            #partial switch to in distinct_base(place) {
            case ^Type_Fixed_Array:   as_place = from.size <= to.size
            case ^Type_Partial_Array: as_place = from.size <= to.size
            }
        }
        if as_place { et = place }
    }
    for e in elems { tc_settle(k, e, et) }   // (each written to its slot, at its type)
    return type_fixed_array(len(elems), et)
}

// `a[lo:hi]`: its collection, its bounds at the header's width — a slice of
// its elements.
tc_slice :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    base_n := Tree_Id(tr.a[n])
    lo_n, hi_n := tree_pair(tr, n)
    tc_lower_dots(k, base_n, lo_n)
    tc_lower_dots(k, base_n, hi_n)
    tt := tc_check(k, base_n)
    // (A named type — `str64`, a distinct array — sliced as its base is.)
    target := distinct_base(tt)
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array, ^Type_Partial_Array: target = distinct_base(pt.elem)
        }
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
        lt := tc_check_at(k, lo_n, slice_header_width_type)
        if !is_numeric(lt) && !is_any(lt) {
            tc_error(k, span, TYPE_SLICE_LOW_BOUND_NUMERIC, type_name(lt))
        } else if !coerces_to_slice_width(lt) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(lt))
        }
    }
    if hi_n != 0 {
        ht := tc_check_at(k, hi_n, slice_header_width_type)
        if !is_numeric(ht) && !is_any(ht) {
            tc_error(k, span, TYPE_SLICE_HIGH_BOUND_NUMERIC, type_name(ht))
        } else if !coerces_to_slice_width(ht) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ht))
        }
    }
    if elem == nil { return Type_Error{} }
    // (A fixed array's known bounds past its end, or crossed: said so now.)
    if fa, is_fixed := target.(^Type_Fixed_Array); is_fixed {
        size := i64(fa.size)
        lo, lo_known := i64(0), true
        hi, hi_known := size, true
        if lo_n != 0 { lo, lo_known = tc_comptime_int(k, lo_n) }
        if hi_n != 0 { hi, hi_known = tc_comptime_int(k, hi_n) }
        bad := lo_known && (lo < 0 || lo > size) || hi_known && (hi < 0 || hi > size) || lo_known && hi_known && lo > hi
        if bad { tc_error(k, span, TYPE_SLICE_OUT_OF_BOUNDS_CONST, lo if lo_known else 0, hi if hi_known else size, size, size) }
    }
    return type_slice(elem)
}

// `a[lo:hi] = v`: the target's slice — its collection, its bounds — then
// the value into its elements. Into bytes, a value no array is written as
// its own type at lo (a view: tc_byte_span_checks).
tc_slice_assign :: proc(k: ^TC, s, target, value: Tree_Id) {
    tr := k.t
    span := tree_span(tr, s)
    base_n := Tree_Id(tr.a[target])
    lo_n, hi_n := tree_pair(tr, target)
    tc_lower_dots(k, base_n, lo_n)
    tc_lower_dots(k, base_n, hi_n)
    tt := tc_check(k, base_n)
    if elem := index_elem_type(tt); elem != nil {   // (the target names a run of elements)
        tc_set_type(k, target, type_slice(elem))
    }
    lt, ht: Type = Type_Any{}, Type_Any{}
    if lo_n != 0 { lt = tc_check_at(k, lo_n, slice_header_width_type) }
    if hi_n != 0 { ht = tc_check_at(k, hi_n, slice_header_width_type) }
    vt := tc_check(k, value)
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
    if pname, immutable := tc_write_root_param(k, target); immutable {
        tc_error(k, span, TYPE_CANNOT_SLICE_ASSIGN_INTO_IMMUTABLE, pname)
    }
    if is_byte_buffer(tt) {
        // (Into bytes, a value's bytes — an array's too, not its elements:
        // all checked there.)
        if view := tc_byte_span_checks(k, lo_n, hi_n, tt, vt, span); view != nil || is_array_shaped(vt) { return }
    } else if te := index_elem_type(tt); te != nil && is_byte_buffer(vt) {
        // (From bytes into a run of another type's elements — `verts[0:n] =
        // buf[0:nbytes]` — their raw bytes read in.)
        tc_byte_read_run(k, lo_n, hi_n, value, vt, te, span)
        return
    } else if v := tc_unparen(k, value); tr.tag[v] == .Array {
        // (An array literal at the elements' type — `f[2:4] = [0.5, 0.25]`
        // into f32s: an array of f32s, tc_settle.)
        if elem := index_elem_type(tt); elem != nil { tc_settle(k, v, type_slice(elem)) }
    }
    // (A run lo:hi, both known, from an array shorter than it: said now —
    // else the copy would stop the program, its value run past.)
    if hi_n != 0 {
        lo, lo_known := i64(0), true
        if lo_n != 0 { lo, lo_known = tc_comptime_int(k, lo_n) }
        hi, hi_known := tc_comptime_int(k, hi_n)
        if va, from_array := distinct_base(vt).(^Type_Fixed_Array); from_array && lo_known && hi_known && hi - lo > i64(va.size) {
            tc_error(k, span, TYPE_SLICE_ASSIGN_VALUE_SHORT, lo, hi, hi - lo, va.size)
        }
    }
    fa, is_array := distinct_base(tt).(^Type_Fixed_Array)
    if !is_array {
        // (A slice's or partial array's run: the value's elements its own type.)
        te := index_elem_type(tt)
        if te == nil || is_any(vt) { return }
        ve: Type
        #partial switch v in distinct_base(vt) {
        case ^Type_Fixed_Array:   ve = v.elem
        case ^Type_Slice:         ve = v.elem
        case ^Type_Partial_Array: ve = v.elem
        case:
            tc_error(k, span, TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE, type_name(vt))
            return
        }
        if !is_infer(ve) && types_incompatible(te, ve) { tc_error(k, span, TYPE_SLICE_ASSIGN_ELEMENTS, type_name(ve), type_name(te)) }
        return
    }
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
