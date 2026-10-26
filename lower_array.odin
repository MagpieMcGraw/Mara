package mara

// Lowering arrays (what tc_array.odin and tc_bytes.odin check): an element
// read or written, an array literal, a slice — and bytes read or written as
// another type.

// `a[i]` (tc_index): the element's place — read, or itself.
lw_index :: proc(k: ^TC, n: Tree_Id, want: Build_Want) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    base_n, idx_n := Tree_Id(tr.a[n]), Tree_Id(tr.b[n])
    br := lw_expr(k, base_n, .Place, temp_span = span)
    bt := tc_node_type(k, base_n)
    base := br.v
    if pt, is_ptr := distinct_base(bt).(^Type_Ptr); is_ptr {
        base = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", br.v)
    }
    ir := lw_expr(k, idx_n, .Value, .Explicit)
    index := build_index_value(b, ir.v, tc_node_type(k, idx_n), span)
    t := tc_node_type(k, n)
    if _, of_byte := distinct_base(t).(Type_Byte); !of_byte && t != nil && !is_infer(t) && is_byte_buffer(bt) {
        lw_fail(k, n, "bytes indexed as another type")
    }
    p := graph_op_value(b, .Index, .Explicit, span, t, "", base, index)
    if want == .Value { return {v = graph_read(b, p, t, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// `a[i] = v` (tc_index_assign): the element's place, then the value into it.
lw_index_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    tr := k.t
    b := k.gb
    span := tree_span(tr, s)
    ix_span := tree_span(tr, target)
    base_n, idx_n := Tree_Id(tr.a[target]), Tree_Id(tr.b[target])
    cr := lw_expr(k, base_n, .Place, temp_span = ix_span)
    ct := tc_node_type(k, base_n)
    tt := distinct_base(ct)
    elem := tc_node_type(k, target)
    base := cr.v
    at := lw_at(k, target)   // (the element's place: the target's)
    if pt, is_ptr := tt.(^Type_Ptr); is_ptr { base = graph_op_value(b, .Deref, .Implied, ix_span, pt.elem, "", cr.v) }
    ir := lw_expr(k, idx_n, .Value)
    place := graph_op_value(b, .Index, .Explicit, ix_span, elem, "", base, build_index_value(b, ir.v, tc_node_type(k, idx_n), ix_span))
    b.at = at
    if is_byte_buffer(ct) {
        lw_byte_write(k, s, target, value, place, tt, op_tok)
        return
    }
    lw_store_at(k, value, place, span, op_tok, target, s)
}

// `bytes[i] = v` (tc_byte_write): v's raw bytes, the element's place a view
// of them as v's type.
lw_byte_write :: proc(k: ^TC, s, target, value: Tree_Id, place: Operand, tt: Type, op_tok: Token_Id) {
    b := k.gb
    span := tree_span(k.t, s)
    if op_tok != 0 { lw_fail(k, s, "a compound assignment into bytes") }
    // (The value built at its own type — `buf[4] = P{}` a P, not the byte
    // the element is: the place becomes a view of it, graph_build_view.)
    vt := tc_node_type(k, value)
    r := lw_expr(k, value, .Into, dest = Dest{kind = .At, at = place, type_ = solidify_type(vt)}, temp = true, temp_span = span)
    _, big := tc_byte_node(k, target)
    graph_build_view(b, place, solidify_type(vt), big, span)
    lw_store(k, value, vt, r, lw_parallel_hold(k, Dest{kind = .At, at = place, type_ = tt}, span), span, settle = true)
}

// `[a, b, c]` (tc_array_literal): zero where it goes (else in a temporary),
// then each element into its slot. `[]`, no elements: the zero alone — an
// empty view, an empty list.
lw_array_literal :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    elems := tree_list(tr, tr.a[n])
    // (A temporary is for a literal reading where it goes, `a = [a[1], a[0]]`:
    // `[]` reads nothing, its zero written where it goes.)
    in_temp := (want != .Into || temp) && !(len(elems) == 0 && want == .Into)
    placed := want != .Into && temp_span != {}
    at := temp_span if temp || placed else span
    d := dest
    if in_temp {
        tt := build_temp_type(d)
        // (Into a slice — `a[1:3] = [9, 9]` — the elements are built in an
        // array of their own, then copied in: a slice's header holds none.)
        if sl, to_slice := distinct_base(tt).(^Type_Slice); to_slice {
            tt = new_clone(Type_Fixed_Array{size = len(elems), elem = sl.elem})
        }
        d = graph_build_temp(b, at, tt)
    }
    ga := graph_build_array(b, span, d)
    if len(elems) == 0 {
        // (Nothing to store: what it is, its zero.)
    } else if ga.elem_t == nil {
        r := lw_expr(k, elems[0], .Either)
        et := tc_node_type(k, elems[0])
        lit_t := new_clone(Type_Fixed_Array{size = len(elems), elem = et})
        lw_store(k, elems[0], et, r, graph_build_array_elem(b, ga, 0, et, lit_t), span)
    } else {
        lw_store_into(k, elems[0], graph_build_array_elem(b, ga, 0, nil, nil), span)
    }
    if len(elems) > 1 {
        for e, i in elems[1:] { lw_store_into(k, e, graph_build_array_elem(b, ga, i + 1, nil, nil), span) }
    }
    graph_build_array_len(b, ga, len(elems), span)   // (into a list: as many as it holds)
    t := tc_node_type(k, n)
    if b.g.type_[ga.zero] == 0 { graph_retype(b, ga.zero, t) }
    return lw_built(k, want, in_temp, temp, d, t, at, placed)
}

// `a[lo:hi]` (tc_slice): its bounds, then its collection's place — a plain
// place walked after them, as the builder walks it; anything else built
// after them — then the slice. Bytes read as where it goes: their place and
// bounds as they are, for the store to take apart (lw_store_span).
lw_slice :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    base_n := Tree_Id(tr.a[n])
    lo_n, hi_n := tree_pair(tr, n)
    read_as: Type
    if want == .Into || dest.type_ != nil { read_as = graph_dest_type(b, dest) }
    view := want != .Into && dest.type_ != nil
    held := !lw_pure_place(k, base_n)
    tt := tc_node_type(k, base_n)
    is_self := tc_is_self(k, base_n)
    target := distinct_base(tt)   // (as tc_slice reads it: a named one as its base)
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
    }
    reads, scalar := false, false
    if read_as != nil && elem != nil {
        probe := Type_Slice{elem = elem}
        if tc_byte_flow(k, read_as, n, &probe) == .Read {
            if held { lw_fail(k, n, "bytes read from a value's span") }
            reads, scalar = true, view || !graph_aggregate(read_as)
        }
    }
    base := NO_VALUE
    if reads { base = graph_base_of(b, lw_expr(k, base_n, .Place).v, tt, span, is_self) }
    lo, hi := NO_VALUE, NO_VALUE
    if lo_n != 0 { lo = lw_bound(k, lo_n, w, span, raw = reads) }
    if hi_n != 0 && !scalar { hi = lw_bound(k, hi_n, w, span, raw = reads) }
    t := tc_node_type(k, n)
    if reads {
        v := graph_op_value(b, .Slice, w, span, t, "", base, lo, hi)
        k.lower.span_read = {v.op, scalar}
        return {v = v, ok = true}
    }
    if held {
        if lw_is_place_form(k, base_n) {
            base = lw_expr(k, base_n, .Place, temp_span = span).v
        } else {
            base = lw_hold(k, base_n, span)
        }
        if pt, is_ptr := distinct_base(tt).(^Type_Ptr); is_ptr && base != NO_VALUE {
            base = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", base)
        }
    } else {
        base = graph_base_of(b, lw_expr(k, base_n, .Place).v, tt, span, is_self)
    }
    return {v = graph_op_value(b, .Slice, w, span, t, "", base, lo, hi), ok = true}
}

// A slice's bound, at the header's width (`raw`: as it is).
lw_bound :: proc(k: ^TC, n: Tree_Id, w: Written, span: Span, raw := false) -> Operand {
    r := lw_expr(k, n, .Value, w)
    if raw { return r.v }
    return graph_build_widen(k.gb, r.v, span, {to = slice_header_width_type})
}

// `a[lo:hi] = v` (tc_slice_assign): the target's slice, then the value into
// its elements — into bytes, a value no array its raw bytes at lo: their
// place, lo (0 when it has none), a view of them as the value's type.
lw_slice_assign :: proc(k: ^TC, s, target, value: Tree_Id) {
    tr := k.t
    b := k.gb
    span := tree_span(tr, s)
    sl_span := tree_span(tr, target)
    base_n := Tree_Id(tr.a[target])
    lo_n, hi_n := tree_pair(tr, target)
    if !lw_pure_place(k, base_n) { lw_fail(k, target, "a slice of no plain place") }
    tt := tc_node_type(k, base_n)
    st := tc_node_type(k, target)
    is_self := tc_is_self(k, base_n)
    bytes := is_byte_buffer(tt)
    if bytes && tc_is_void(k, value) { lw_fail(k, s, "void written into bytes") }
    vt := tc_node_type(k, value)
    // (The view's type: a value no array's, or a fixed array's, own — its
    // raw bytes: tc_byte_span_checks. A slice's or partial array's, the copy's.)
    view: Type
    if _, fixed := distinct_base(vt).(^Type_Fixed_Array); bytes && (!is_array_shaped(vt) || fixed) { view = solidify_type(vt) }
    place: Operand
    if view != nil {
        vplace := graph_base_of(b, lw_expr(k, base_n, .Place).v, tt, span, is_self)
        at := NO_VALUE
        if lo_n != 0 { at = graph_build_widen(b, lw_bound(k, lo_n, .Explicit, sl_span, raw = true), span, {to = slice_header_width_type}) }
        if at == NO_VALUE { at = graph_const(b, .Synthetic, span, slice_header_width_type, "0", Const_Value{}) }
        // (Its hi, written: the span is the value's size — checked where the
        // bounds aren't numbers, llvm_view.)
        if hi_n != 0 {
            hi := graph_build_widen(b, lw_bound(k, hi_n, .Explicit, sl_span, raw = true), span, {to = slice_header_width_type})
            place = graph_op_value(b, .View, .Explicit, span, view, "", vplace, at, hi)
        } else {
            place = graph_op_value(b, .View, .Explicit, span, view, "", vplace, at)
        }
    } else {
        lo, hi := NO_VALUE, NO_VALUE
        if lo_n != 0 { lo = lw_bound(k, lo_n, .Explicit, sl_span) }
        if hi_n != 0 { hi = lw_bound(k, hi_n, .Explicit, sl_span) }
        base := graph_base_of(b, lw_expr(k, base_n, .Place).v, tt, sl_span, is_self)
        place = graph_op_value(b, .Slice, .Explicit, sl_span, st, "", base, lo, hi)
        // (Bytes into bytes — `out[0:4] = bits.input[2:6]` — a copy, as any
        // slice's is: no bytes read as another type.)
        if !bytes || is_byte_buffer(vt) {
            lw_store_at(k, value, place, span)
            return
        }
    }
    r := lw_expr(k, value, .Into, dest = Dest{kind = .At, at = NO_VALUE}, temp = true, temp_span = span)
    lw_store(k, value, vt, r, lw_parallel_hold(k, Dest{kind = .At, at = place, type_ = tt}, span), span, settle = true)
}
