package mara

// Bytes in the new checker: a value read out of a byte buffer as another
// type (`h : Head = bytes[off]`), or written into one (`bytes[off] = v`), is
// its raw bytes — the element's place a view of them as that type.

// The read an expression is, under `#big_endian` and parens: its node, and
// whether its bytes are big-endian.
tc_byte_node :: proc(k: ^TC, n: Tree_Id) -> (Tree_Id, bool) {
    m := tc_unparen(k, n)
    if k.t.tag[m] == .Big_Endian { return tc_unparen(k, Tree_Id(k.t.a[m])), true }
    return m, false
}

// Whether an expression reads an element of bytes: `bytes[i]`.
tc_byte_index :: proc(k: ^TC, n: Tree_Id) -> bool {
    m, _ := tc_byte_node(k, n)
    return k.t.tag[m] == .Index && is_byte_buffer(tc_node_type(k, Tree_Id(k.t.a[m])))
}

// How a value moves into a destination of type `dest`: bytes read as it, a
// range of bytes viewed as a byte slice, or neither (byte_flow's rule).
tc_byte_flow :: proc(k: ^TC, dest: Type, value: Tree_Id, vt: Type) -> Byte_Flow {
    index_read := tc_byte_index(k, value)
    if !index_read && !is_byte_buffer(vt) { return .None }
    if is_slice_type(dest) && !index_read { return .View }
    return .Read
}

// The flow, checked: a view's elements byte-sized; a read into no slice,
// and of nothing holding a header.
tc_check_byte_flow :: proc(k: ^TC, dest: Type, value: Tree_Id, vt: Type, span: Span) -> Byte_Flow {
    flow := tc_byte_flow(k, dest, value, vt)
    #partial switch flow {
    case .View:
        sl := distinct_base(dest).(^Type_Slice)
        if !is_byte_sized_memory_type(sl.elem) {
            en := type_name(sl.elem)
            tc_error(k, span, TYPE_BYTE_VIEW_WIDE_ELEM, type_name(dest), en, en)
        }
    case .Read:
        if is_slice_type(dest) {
            tc_error(k, span, TYPE_BYTE_READ_SLICE_BY_INDEX, type_name(dest))
        } else if why := byte_slice_reason(k.c, dest); why != "" {
            tc_error(k, span, TYPE_BYTE_READ_REFERENCE, type_name(dest), why)
        }
    }
    return flow
}

// A `#big_endian` read of no bytes: an error.
tc_check_big_endian :: proc(k: ^TC, value: Tree_Id, span: Span) {
    m := tc_unparen(k, value)
    if k.t.tag[m] != .Big_Endian { return }
    inner := tc_unparen(k, Tree_Id(k.t.a[m]))
    #partial switch k.t.tag[inner] {
    case .Index, .Slice:
        if st := tc_node_type(k, Tree_Id(k.t.a[inner])); !is_byte_buffer(st) {
            tc_error(k, span, TYPE_BIG_ENDIAN_NEEDS_BYTE_BUFFER, type_name(st))
        }
    }
}

// An element of bytes read into its destination (tc_store): a slice or a
// partial array filled by a byte read; else the bytes there seen as the
// destination's type, read, written. (`zeroed`: a new partial array it fills
// was zero first.)
tc_store_bytes :: proc(k: ^TC, e: Tree_Id, r: Fused, d: Dest, dt: Type, span: Span) -> (wrote, zeroed: bool) {
    b := tc_building(k)
    _, big := tc_byte_node(k, e)
    if !r.place {
        tc_fail(k, "bytes read as another type")
        return
    }
    if is_slice_type(dt) || is_partial_array(dt) {
        buf, off := graph_fuse_byte_operands(b, r.v, span)
        graph_op(b, .Byte_Read, .Explicit, span, d.type_, "#big_endian" if big else "", graph_dest_place(b, d, span), buf, off)
        return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
    }
    graph_fuse_view(b, r.v, dt, big, span)
    val := graph_read(b, r.v, dt, span)
    graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
    return true, false
}

// A span of bytes read as the destination's type: its bytes' place and
// bounds, as its slice built them; a register value the bytes at its start
// seen as it, read, else a byte read — at the span, where its failures say
// it is. (A new partial array is zero first.)
tc_store_span :: proc(k: ^TC, e: Tree_Id, r: Fused, d: Dest, dt: Type, span: Span) -> (wrote, zeroed: bool) {
    b := tc_building(k)
    m, big := tc_byte_node(k, e)
    if r.v.op == NO_NODE || r.v.op != k.span_read.op || k.span_read.scalar == graph_aggregate(dt) {
        tc_fail(k, "a span of bytes read as another type")
        return
    }
    if k.span_read.scalar {
        val := graph_read(b, graph_fuse_span_view(b, r.v, dt, big, span), dt, span)
        graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
        return true, false
    }
    buf, lo, hi := graph_fuse_span_operands(b, r.v, span)
    graph_op(b, .Byte_Read, .Explicit, tree_span(k.t, m), d.type_, "#big_endian" if big else "", graph_dest_place(b, d, span), buf, lo, hi)
    return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
}

// `bytes[i] = v`: the element's place, v into it — v's raw bytes: the
// place a view of them as v's type.
tc_byte_write :: proc(k: ^TC, s, target, value: Tree_Id, place: Operand, ct, tt: Type, it: Type, env: ^Type_Scope, op_tok: Token_Id) {
    span := tree_span(k.t, s)
    if op_tok != 0 {
        tc_unsupported(k, s, "a compound assignment into bytes")
        return
    }
    b := tc_building(k)
    vt: Type
    r: Fused
    d: Dest
    if b != nil && place != NO_VALUE {
        pt := b.g.type_[place.op] if place.op != NO_NODE else nil
        d = Dest{kind = .At, at = place, type_ = pt}
        vt, r = tc_expr(k, value, env, .Into, dest = d, temp = true, temp_span = span)
    } else {
        vt = tc_check(k, value, env)
    }
    if !is_numeric(it) && !is_any(it) {
        tc_error(k, span, TYPE_ARRAY_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER, pname)
    }
    // (An untyped number has no width to write: cast it.)
    if is_infer(vt) {
        tc_error(k, span, TYPE_BYTE_BUFFER_WRITE_UNTYPED)
        return
    }
    check_byte_write(k.c, vt, span)
    if b = tc_building(k); b == nil || place == NO_VALUE { return }
    _, big := tc_byte_node(k, target)
    graph_fuse_view(b, place, solidify_type(vt), big, span)
    tc_store(k, value, vt, r, tc_parallel_hold(k, Dest{kind = .At, at = place, type_ = tt}, span), span, settle = true)
}

// `&bytes[i]` where a pointer to another type takes it: a view of the bytes
// as that type, its address a pointer to it (its bounds checked where made).
tc_byte_view_address :: proc(k: ^TC, expected: Type, value: Tree_Id) {
    pt, is_ptr := expected.(^Type_Ptr)
    if !is_ptr { return }
    if _, to_byte := pt.elem.(Type_Byte); to_byte { return }
    u := tc_unparen(k, value)
    b := tc_building(k)
    if b == nil || k.t.tag[u] != .Unary { return }
    ops, built := k.byte_addrs[tc_sid(k, u)]
    if !built { return }
    _, big := tc_byte_node(k, Tree_Id(k.t.a[u]))
    graph_fuse_view(b, {ops[1], 0}, pt.elem, big, tree_span(k.t, u))
    b.g.type_[ops[0]] = new_clone(Type_Ptr{elem = pt.elem})
}

// Into a span of bytes: a value no array is its raw bytes — plain data, as
// many as the span has when its bounds are numbers — and the view's type is
// its own; an array's elements are copied (of a width: no untyped ones).
tc_byte_span_checks :: proc(k: ^TC, lo_n, hi_n: Tree_Id, tt, vt: Type, span: Span) -> Type {
    shaped := is_array_shaped(vt)
    if !shaped {
        if why := byte_slice_reason(k.c, vt); why != "" { tc_error(k, span, TYPE_BYTE_WRITE_REFERENCE, type_name(vt), why) }
    }
    if fa, is_array := distinct_base(vt).(^Type_Fixed_Array); is_array && is_infer(fa.elem) {
        tc_error(k, span, TYPE_BYTE_BUFFER_COPY_UNTYPED, fa.size)
    }
    if shaped { return nil }
    view := solidify_type(vt)
    lo, lo_ok := tc_number_int(k, lo_n)
    hi, hi_ok := tc_number_int(k, hi_n)
    if size := checker_type_byte_size(view); lo_ok && hi_ok && hi - lo != size {
        msg := TYPE_BYTE_ARRAY_WRITE_BYTES_SLICE if is_byte_fixed_array(tt) else TYPE_BYTE_SLICE_WRITE_BYTES_SLICE
        tc_error(k, span, msg, type_name(view), size, hi - lo)
    }
    return view
}

// The write into bytes: the target the value's type says — the view at lo,
// as that type (`view`), else the span — then the value into it, at the
// bytes' type.
tc_byte_span_write :: proc(k: ^TC, value: Tree_Id, vt: Type, r: Fused, gs: ^Graph_Span_Target, tt, view: Type,
                           void: bool, span: Span) {
    b := tc_building(k)
    if b == nil { return }
    if void {
        tc_fail(k, "void written into bytes")
        return
    }
    place, ok := graph_fuse_span_target_end(b, gs, view, span)
    if !ok {
        tc_fail(k, "a span's end that branches, viewed")
        return
    }
    tc_store(k, value, vt, r, tc_parallel_hold(k, Dest{kind = .At, at = place, type_ = tt}, span), span, settle = true)
}

// A span of bytes read as a type, its bounds numbers: as many bytes as the
// type has — a struct or an array may take fewer (the tail zero), a partial
// array whole elements up to its size; a distinct type or a field (`exact`),
// exactly.
tc_span_read_size :: proc(k: ^TC, value: Tree_Id, ann: Type, exact: bool, span: Span) {
    m, _ := tc_byte_node(k, value)
    if k.t.tag[m] != .Slice { return }
    lo_n, hi_n := tree_pair(k.t, m)
    lo, lo_ok := tc_number_int(k, lo_n)
    hi, hi_ok := tc_number_int(k, hi_n)
    if !lo_ok || !hi_ok { return }
    n := hi - lo
    if exact {
        if size := checker_type_byte_size(ann); n != size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(ann), size, n) }
        return
    }
    t := distinct_base(ann)
    size := checker_type_byte_size(t)
    sd := as_scope_body(t)
    switch {
    case sd != nil && len(sd.fields) > 0, tc_is_fixed_array(t):
        if n > size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), size, n) }
    case is_partial_array(t):
        pa := t.(^Type_Partial_Array)
        elem := checker_type_byte_size(pa.elem)
        backing := pa.size * elem
        if elem > 0 && n % elem != 0 || n > backing { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), backing, n) }
    case:
        if n != size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), size, n) }
    }
}
