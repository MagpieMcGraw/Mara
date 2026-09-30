package mara

// Arrays in the new checker: an element read or written, an array literal.

// `a[i]`: the element's place — its collection's (through a pointer, what it
// points at), the index at the header's width — read, or itself.
tc_index :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    base_n, idx_n := Tree_Id(tr.a[n]), Tree_Id(tr.b[n])
    if tc_has_dot_ref(k, idx_n) {
        tc_unsupported(k, n, "`.len` in a subscript")
        return Type_Error{}, {}
    }
    build := want != .None && tc_building(k) != nil
    bt, br := tc_expr(k, base_n, env, .Place if build else .None, temp_span = span)
    base := br.v
    if b := tc_building(k); build && b != nil {
        if pt, is_ptr := distinct_base(bt).(^Type_Ptr); is_ptr {
            base = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", br.v)
        }
    }
    target := distinct_base(bt)
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array: target = distinct_base(pt.elem)
        }
    }
    if fa, ok := target.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it, ir := tc_expr(k, idx_n, env, .Value if build else .None, .Explicit)
    index := NO_VALUE
    if b := tc_building(k); build && b != nil { index = fuse_index_value(b, ir.v, it, span) }
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
    b := tc_building(k)
    if !build || b == nil { return t, {} }
    if _, of_byte := distinct_base(t).(Type_Byte); !of_byte && t != nil && !is_infer(t) && is_byte_buffer(bt) {
        tc_fail(k, "bytes indexed as another type")
        return t, {}
    }
    p := graph_op_value(b, .Index, .Explicit, span, t, "", base, index)
    if want == .Value { return t, {v = graph_read(b, p, t, span), ok = true} }
    return t, {v = p, place = true, ok = true}
}

// `a[i] = v`: the element's place, then the value into it.
tc_index_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    diag := value if op_tok == 0 else 0   // (the value, as diagnostics name it)
    tr := k.t
    span := tree_span(tr, s)
    ix_span := tree_span(tr, target)
    base_n, idx_n := Tree_Id(tr.a[target]), Tree_Id(tr.b[target])
    if tc_has_dot_ref(k, idx_n) {
        tc_unsupported(k, target, "`.len` in a subscript")
        return
    }
    if tr.tag[base_n] == .Ident && tc_name(k, base_n) in k.table.constants {
        name := tc_name(k, base_n)
        tc_error(k, span, TYPE_CANNOT_WRITE_INDEXED_CONSTANT, name, name)
        return
    }
    b := tc_building(k)
    ct, cr := tc_expr(k, base_n, env, .Place if b != nil else .None, temp_span = ix_span)
    tt := distinct_base(ct)
    elem := index_elem_type(tt)
    tc_set_type(k, target, elem)
    base := cr.v
    if b = tc_building(k); b != nil {
        if pt, is_ptr := tt.(^Type_Ptr); is_ptr { base = graph_op_value(b, .Deref, .Implied, ix_span, pt.elem, "", cr.v) }
    }
    if fa, ok := tt.(^Type_Fixed_Array); ok && fa.index_type != nil { k.hint = fa.index_type }
    it, ir := tc_expr(k, idx_n, env, .Value if tc_building(k) != nil else .None)
    place := NO_VALUE
    if b = tc_building(k); b != nil {
        place = graph_op_value(b, .Index, .Explicit, ix_span, elem, "", base, fuse_index_value(b, ir.v, it, ix_span))
    }
    #partial switch v in tt {
    case ^Type_Fixed_Array:   k.hint = v.elem
    case ^Type_Partial_Array: if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    case ^Type_Slice:         if _, is_byte := v.elem.(Type_Byte); !is_byte { k.hint = v.elem }
    }
    if is_byte_buffer(ct) {
        // (Into bytes: the value's raw bytes, the element's place a view.)
        tc_byte_write(k, s, target, value, place, ct, tt, it, env, op_tok)
        return
    }
    vt := tc_store_at(k, value, place, env, span, op_tok, target)
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

// Whether a subscript holds a `.len` / `.cap` (its base's).
tc_has_dot_ref :: proc(k: ^TC, n: Tree_Id) -> bool {
    if n == 0 { return false }
    if k.t.tag[n] == .Dot_Ident { return true }
    #partial switch k.t.tag[n] {
    case .Binary: return tc_has_dot_ref(k, Tree_Id(k.t.a[n])) || tc_has_dot_ref(k, Tree_Id(k.t.b[n]))
    case .Unary, .Paren: return tc_has_dot_ref(k, Tree_Id(k.t.a[n]))
    }
    return false
}

// `[a, b, c]`: zero where it goes (else in a temporary), then each element
// into its slot — the first's type the literal's element type, when where it
// goes gives none.
tc_array_literal :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                         dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    elems := tree_list(tr, tr.a[n])
    if len(elems) == 0 { return Type_Error{}, {} }   // (typed by where it goes)
    b := tc_building(k)
    if want == .None || b == nil {
        et := tc_check(k, elems[0], env)
        for e, i in elems[1:] {
            if t := tc_check(k, e, env); types_incompatible(et, t) {
                tc_error(k, span, TYPE_ARRAY_ELEMENT_TYPE_EXPECTED, i + 1, type_name(t), type_name(et))
            }
        }
        return new_clone(Type_Fixed_Array{size = len(elems), elem = et}), {}
    }
    in_temp := want != .Into || temp
    placed := want != .Into && temp_span != {}
    at := temp_span if temp || placed else span
    d := dest
    if in_temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
    ga := graph_fuse_array(b, span, d)
    et: Type
    if ga.elem_t == nil {
        r: Fused
        et, r = tc_expr(k, elems[0], env, .Either)
        lit_t := new_clone(Type_Fixed_Array{size = len(elems), elem = et})
        if b = tc_building(k); b != nil { tc_store(k, elems[0], et, r, graph_fuse_array_elem(b, ga, 0, et, lit_t), span) }
    } else {
        et = tc_store_into(k, elems[0], env, graph_fuse_array_elem(b, ga, 0, nil, nil), span)
    }
    for e, i in elems[1:] {
        t: Type
        if b = tc_building(k); b != nil {
            t = tc_store_into(k, e, env, graph_fuse_array_elem(b, ga, i + 1, nil, nil), span)
        } else {
            t = tc_check(k, e, env)
        }
        if types_incompatible(et, t) {
            tc_error(k, span, TYPE_ARRAY_ELEMENT_TYPE_EXPECTED, i + 1, type_name(t), type_name(et))
        }
    }
    t := new_clone(Type_Fixed_Array{size = len(elems), elem = et})
    if b = tc_building(k); b == nil { return t, {} }
    if b.g.type_[ga.zero] == nil { b.g.type_[ga.zero] = t }
    return t, tc_built(k, want, in_temp, temp, d, t, at, placed)
}

// A value stored into a destination: built there, what builds in place;
// else written at the destination's type.
tc_store_into :: proc(k: ^TC, e: Tree_Id, env: ^Type_Scope, d: Dest, span: Span, settle := false) -> Type {
    t, r := tc_expr(k, e, env, .Into, dest = d, temp_span = span)
    tc_store(k, e, t, r, d, span, settle)
    return t
}

// What building a value in place gives its use: nothing more (built into
// where it goes); else its temporary, typed — read, or its place.
tc_built :: proc(k: ^TC, want: Fuse_Want, in_temp, into_temp: bool, d: Dest, t: Type, span: Span, placed: bool) -> Fused {
    b := tc_building(k)
    if b == nil { return {} }
    if !in_temp { return {v = NO_VALUE, ok = true, into = true} }
    tt := d.type_ if d.type_ != nil else t
    p := graph_fuse_temp_end(b, d, tt, span)
    switch {
    case into_temp:                return {v = graph_read(b, p, tt, span), ok = true, temp = true}
    case want == .Place || placed: return {v = p, place = true, ok = true}
    }
    return {v = graph_read(b, p, tt, span), ok = true}
}

// `a[lo:hi]`: its bounds at the header's width, then its collection's place
// — a plain place checked first and built after them, as the builder walks
// it; any other base built as it is checked (held, when it has no place)
// and put after the bounds — then the slice.
tc_slice :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written, dest: Dest) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    base_n := Tree_Id(tr.a[n])
    lo_n, hi_n := tree_pair(tr, n)
    if tc_has_dot_ref(k, lo_n) || tc_has_dot_ref(k, hi_n) {
        tc_unsupported(k, n, "`.len` in a subscript")
        return Type_Error{}, {}
    }
    b := tc_building(k)
    build := want != .None && b != nil
    read_as: Type
    if build && (want == .Into || dest.type_ != nil) { read_as = graph_dest_type(b, dest) }
    held := false
    early: Graph_Early
    base, plain := NO_VALUE, NO_VALUE
    plain_t, tt: Type
    if build && !tc_pure_place(k, base_n) {
        held, early = true, graph_fuse_early_begin(b)
        if tc_is_place_form(k, base_n) {
            r: Fused
            tt, r = tc_expr(k, base_n, env, .Place, temp_span = span)
            base = r.v
        } else {
            tt, base = tc_hold(k, base_n, env, span)
        }
        if b = tc_building(k); b != nil {
            if pt, is_ptr := distinct_base(tt).(^Type_Ptr); is_ptr && base != NO_VALUE {
                base = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", base)
            }
            graph_fuse_early_end(b, &early)
        }
    } else if build {
        r: Fused
        tt, r = tc_expr(k, base_n, env, .Place)
        plain, plain_t = r.v, tt
    } else {
        tt = tc_check(k, base_n, env)
    }
    target := tt
    if pt, is_ptr := target.(^Type_Ptr); is_ptr {
        #partial switch inner in distinct_base(pt.elem) {
        case ^Type_Slice, ^Type_Fixed_Array: target = distinct_base(pt.elem)
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
            return Type_Error{}, {}
        }
    }
    if build && read_as != nil && elem != nil && is_byte_buffer(target) {
        tc_unsupported(k, n, "a span of bytes read as a type")
        return Type_Error{}, {}
    }
    lo, hi := NO_VALUE, NO_VALUE
    if lo_n != 0 {
        lt: Type
        lt, lo = tc_bound(k, lo_n, env, w, span, build)
        if !is_numeric(lt) && !is_any(lt) {
            tc_error(k, span, TYPE_SLICE_LOW_BOUND_NUMERIC, type_name(lt))
        } else if !coerces_to_slice_width(lt) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(lt))
        }
    }
    if hi_n != 0 {
        ht: Type
        ht, hi = tc_bound(k, hi_n, env, w, span, build)
        if !is_numeric(ht) && !is_any(ht) {
            tc_error(k, span, TYPE_SLICE_HIGH_BOUND_NUMERIC, type_name(ht))
        } else if !coerces_to_slice_width(ht) {
            tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(ht))
        }
    }
    if elem == nil { return Type_Error{}, {} }
    t := new_clone(Type_Slice{elem = elem})
    if b = tc_building(k); !build || b == nil { return t, {} }
    if held {
        if !graph_fuse_early_place(b, &early) {
            tc_fail(k, "a slice's bounds that branch, of a value")
            return t, {}
        }
    } else {
        base = graph_fuse_base_place(b, plain, plain_t, false, span)
    }
    return t, {v = graph_op_value(b, .Slice, w, span, t, "", base, lo, hi), ok = true}
}

// A slice's bound, at the header's width.
tc_bound :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, w: Written, span: Span, build: bool) -> (Type, Operand) {
    t, r := tc_expr(k, n, env, .Value if build else .None, w)
    b := tc_building(k)
    if !build || b == nil { return t, NO_VALUE }
    return t, graph_fuse_widen(b, r.v, span, {to = slice_header_width_type})
}

// A place however its base is reached: a field, an element, what a pointer
// points at.
tc_is_place_form :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[tc_unparen(k, n)] {
    case .Field, .Index, .Deref: return true
    }
    return false
}

// `a[lo:hi] = v`: the target's slice — its collection's place (a plain
// place, checked first), its bounds — then the value into its elements.
tc_slice_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, s)
    sl_span := tree_span(tr, target)
    base_n := Tree_Id(tr.a[target])
    lo_n, hi_n := tree_pair(tr, target)
    if tc_has_dot_ref(k, lo_n) || tc_has_dot_ref(k, hi_n) {
        tc_unsupported(k, target, "`.len` in a subscript")
        return
    }
    b := tc_building(k)
    if b != nil && !tc_pure_place(k, base_n) {
        tc_fail(k, "a slice of no plain place")
        b = nil
    }
    tt: Type
    coll := NO_VALUE
    if b != nil {
        r: Fused
        tt, r = tc_expr(k, base_n, env, .Place)
        coll = r.v
    } else {
        tt = tc_check(k, base_n, env)
    }
    if is_byte_buffer(tt) {
        tc_unsupported(k, target, "a write into a span of bytes")
        return
    }
    st: Type
    if elem := index_elem_type(tt); elem != nil {   // (the target names a run of elements)
        st = new_clone(Type_Slice{elem = elem})
        tc_set_type(k, target, st)
    }
    build := b != nil
    lt, ht: Type = Type_Any{}, Type_Any{}
    lo, hi := NO_VALUE, NO_VALUE
    if lo_n != 0 { lt, lo = tc_bound(k, lo_n, env, .Explicit, sl_span, build) }
    if hi_n != 0 { ht, hi = tc_bound(k, hi_n, env, .Explicit, sl_span, build) }
    place := NO_VALUE
    if b = tc_building(k); build && b != nil {
        place = graph_op_value(b, .Slice, .Explicit, sl_span, st, "", graph_fuse_base_place(b, coll, tt, false, sl_span), lo, hi)
    }
    vt := tc_store_at(k, value, place, env, span)
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
    fa, is_array := tt.(^Type_Fixed_Array)
    if !is_array { return }
    #partial switch v in vt {
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
