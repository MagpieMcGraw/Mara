package mara

// Bytes in the checker: a value read out of a byte buffer as another
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
// range of bytes viewed as a byte slice, or neither.
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

// `bytes[i] = v`: v's raw bytes written at the element — as v's type, of a
// width.
tc_byte_write :: proc(k: ^TC, s, target, value: Tree_Id, it: Type, op_tok: Token_Id) {
    span := tree_span(k.t, s)
    if op_tok != 0 {
        tc_unsupported(k, s, "a compound assignment into bytes")
        return
    }
    vt := tc_check(k, value)
    if !is_numeric(it) && !is_any(it) {
        tc_error(k, span, TYPE_ARRAY_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    if pname, immutable := tc_write_root_param(k, target); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER, pname)
    }
    // (An untyped number has no width to write: cast it — a binding no use
    // has given one yet, too.)
    if is_infer(vt) {
        tc_error(k, span, TYPE_BYTE_BUFFER_WRITE_UNTYPED)
        return
    }
    check_byte_write(k.c, vt, span)
}

// Into a span of bytes, a value's raw bytes: a value no array, or a fixed
// array — `[2]u32`, `[2]u8{1, 2}` — a view of its own type, as many bytes as
// the span has when its bounds are numbers; a slice's or a partial array's
// elements, theirs, as many as it holds (tc_slice_assign leaves them to the
// copy; byte elements are copied as they are). Plain data, of a width: no
// references, no untyped numbers.
tc_byte_span_checks :: proc(k: ^TC, lo_n, hi_n: Tree_Id, tt, vt: Type, span: Span) -> Type {
    fa, fixed := distinct_base(vt).(^Type_Fixed_Array)
    if fixed && is_infer(fa.elem) {
        tc_error(k, span, TYPE_BYTE_BUFFER_COPY_UNTYPED, fa.size)
        return nil
    }
    if is_array_shaped(vt) && !fixed {
        if elem := index_elem_type(vt); elem != nil {
            if why := byte_slice_reason(k.c, elem); why != "" { tc_error(k, span, TYPE_BYTE_WRITE_REFERENCE, type_name(vt), why) }
        }
        return nil
    }
    if why := byte_slice_reason(k.c, vt); why != "" {
        tc_error(k, span, TYPE_BYTE_WRITE_REFERENCE, type_name(vt), why)
        return nil
    }
    view := tc_pin_default(k, vt, span)   // (a binding of no width yet: its default, from here)
    lo, lo_ok := tc_comptime_int(k, lo_n, names = false)
    hi, hi_ok := tc_comptime_int(k, hi_n, names = false)
    if size := type_size(view); lo_ok && hi_ok && int(hi - lo) != size {
        msg := TYPE_BYTE_ARRAY_WRITE_BYTES_SLICE if is_byte_fixed_array(tt) else TYPE_BYTE_SLICE_WRITE_BYTES_SLICE
        tc_error(k, span, msg, type_name(view), size, hi - lo)
    }
    return view
}

// From bytes into a run of another type's elements — `verts[0:n] =
// buf[0:nbytes]`: the bytes are the elements', raw. Plain data only. Its
// bounds and the bytes' count known: the run's elements take exactly the
// bytes (an open run, `verts[lo:]`, a whole number of elements of them);
// else checked as the program runs (llvm_copy_into).
tc_byte_read_run :: proc(k: ^TC, lo_n, hi_n, value: Tree_Id, vt, elem: Type, span: Span) {
    if why := byte_slice_reason(k.c, elem); why != "" {
        tc_error(k, span, TYPE_BYTE_READ_REFERENCE, type_name(elem), why)
        return
    }
    size := type_size(elem)
    if size <= 0 { return }
    // (The bytes' count, when it's known: an array's size, a span's bounds.)
    nbytes, known := 0, false
    if fa, is_array := distinct_base(vt).(^Type_Fixed_Array); is_array { nbytes, known = fa.size, true }
    if v := tc_unparen(k, value); k.t.tag[v] == .Slice {
        known = false
        blo_n, bhi_n := tree_pair(k.t, v)
        if bhi_n != 0 {
            blo, blo_ok := i64(0), true
            if blo_n != 0 { blo, blo_ok = tc_comptime_int(k, blo_n, names = false) }
            bhi, bhi_ok := tc_comptime_int(k, bhi_n, names = false)
            if blo_ok && bhi_ok { nbytes, known = int(bhi - blo), true }
        }
    }
    if !known { return }
    if hi_n == 0 {
        if nbytes % size != 0 { tc_error(k, span, TYPE_BYTE_READ_RUN_WHOLE, nbytes, type_name(elem), size) }
        return
    }
    lo, lo_ok := i64(0), true
    if lo_n != 0 { lo, lo_ok = tc_comptime_int(k, lo_n, names = false) }
    hi, hi_ok := tc_comptime_int(k, hi_n, names = false)
    if lo_ok && hi_ok && int(hi - lo) * size != nbytes {
        tc_error(k, span, TYPE_BYTE_READ_RUN_SIZE, hi - lo, type_name(elem), int(hi - lo) * size, nbytes)
    }
}

// A span of bytes read as a type, its bounds numbers: as many bytes as the
// type has — a struct or an array may take fewer (the tail zero), a partial
// array whole elements up to its size; a distinct type or a field (`exact`),
// exactly.
tc_span_read_size :: proc(k: ^TC, value: Tree_Id, ann: Type, exact: bool, span: Span) {
    m, _ := tc_byte_node(k, value)
    if k.t.tag[m] != .Slice { return }
    lo_n, hi_n := tree_pair(k.t, m)
    lo, lo_ok := tc_comptime_int(k, lo_n, names = false)
    hi, hi_ok := tc_comptime_int(k, hi_n, names = false)
    if !lo_ok || !hi_ok { return }
    n := int(hi - lo)
    if exact {
        if size := type_size(ann); n != size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(ann), size, n) }
        return
    }
    t := distinct_base(ann)
    size := type_size(t)
    sd := as_scope_body(t)
    switch {
    case sd != nil && len(sd.fields) > 0, tc_is_fixed_array(t):
        if n > size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), size, n) }
    case is_partial_array(t):
        pa := t.(^Type_Partial_Array)
        elem := type_size(pa.elem)
        backing := pa.size * elem
        if elem > 0 && n % elem != 0 || n > backing { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), backing, n) }
    case:
        if n != size { tc_error(k, span, TYPE_BYTE_BUFFER_READ_BYTES_SLICE, type_name(t), size, n) }
    }
}
