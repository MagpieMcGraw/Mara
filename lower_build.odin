package mara

// What lowering builds with: what an expression built, and the helpers
// that take a value to the type its use takes.

// What an expression's use asks of it: its value; its place — a variable, a
// field, an element; or its place when it has one, else its value (its
// consumer decides: a view, a read); or it built into a destination.
Build_Want :: enum u8 { None, Value, Place, Either, Into }

// What was built for an expression: a value, or a place — or nothing, built
// into the destination it was given (.Into: else, as .Either).
Built :: struct {
    v:     Operand,
    place: bool,
    ok:    bool,
    into:  bool,
    temp:  bool,   // built in a temporary, as storage that holds a value is written (read)
}

// Whether what was built is a text constant: its global (a table's is no
// partial array; a string literal is built as one of its own).
built_is_text_constant :: proc(b: ^Graph_Builder, r: Built) -> bool {
    if b == nil || r.v.op == NO_NODE { return false }
    op := r.v.op
    if !r.place && b.g.op[op] == .Read { op = graph_built_operands(b, op)[0].op }
    return op != NO_NODE && b.g.op[op] == .Global && is_partial_array(b.g.type_[op])
}

// A dispatch's array literal argument: its position, its nodes, its type.
Build_Literal_Arg :: struct {
    arg, from, to: int,
    t:             Type,
}

// Whether a function's param would view an argument that is an array's
// value (its place, or a temporary) — a slice over it.
build_views_value :: proc(ft: ^Type_Scope, array_values: []bool) -> bool {
    for is_value, i in array_values {
        if !is_value || i >= len(ft.params) { continue }
        if _, to_slice := distinct_base(ft.params[i].type_).(^Type_Slice); to_slice { return true }
    }
    return false
}

// Whether a use of a `from` as a `to` views it: a fixed array as a slice; a
// partial array, or a pointer to one, as a slice's header.
build_views :: proc(to, from: Type) -> bool {
    if to == nil || from == nil { return false }
    _, to_ptr := distinct_base(to).(^Type_Ptr)
    _, from_ptr := distinct_base(from).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(from) { return true }
    _, to_slice := distinct_base(to).(^Type_Slice)
    _, from_array := distinct_base(from).(^Type_Fixed_Array)
    return to_slice && from_array
}

// The type of the temporary a value is built in before it goes to `d`: the
// destination's, once settled; nil leaves it the value's own.
build_temp_type :: proc(d: Dest) -> Type {
    if d.type_ != nil && !is_infer(d.type_) { return d.type_ }
    return nil
}

// The type of a written field that is no struct's: a header's len, cap or
// ptr; an array's swizzle.
build_target_field_type :: proc(obj_type: Type, field: string) -> Type {
    t := obj_type
    if pt, ok := t.(^Type_Ptr); ok { t = pt.elem }
    t = distinct_base(t)
    elem: Type
    #partial switch v in t {
    case ^Type_Slice:         elem = v.elem
    case ^Type_Partial_Array: elem = v.elem
    case ^Type_Fixed_Array:
        if !is_swizzle_field(field, v.size) { return nil }
        if len(field) == 1 { return v.elem }
        return new_clone(Type_Fixed_Array{size = len(field), elem = v.elem})
    case:
        return nil
    }
    switch field {
    case "len", "cap": return slice_header_width_type
    case "ptr":        return new_clone(Type_Ptr{elem = elem})
    }
    return nil
}

// An index at the header's width: an enum's value is its tag, taken as a
// number; a narrower number widens.
build_index_value :: proc(b: ^Graph_Builder, at: Operand, t: Type, span: Span) -> Operand {
    if _, is_enum := distinct_base(t).(^Type_Enum); is_enum {
        return graph_op_value(b, .Cast, .Implied, span, slice_header_width_type, type_name(slice_header_width_type), at)
    }
    return graph_build_widen(b, at, span, {to = slice_header_width_type})
}

// A span of bytes read as its destination's type: the bytes' place, built
// first, and whether it is read as a register value (its start only).
Built_Span_Read :: struct {
    op:     Node_Id,
    scalar: bool,
}

// A built expression's value: a place is read, right after it.
lw_value :: proc(k: ^TC, r: Built, n: Tree_Id, t: Type) -> Operand {
    b := k.gb
    if b == nil || !r.place { return r.v }
    return graph_read(b, r.v, t, tree_span(k.t, n))
}

// Whether an expression built for its value or its place (lw_expr, .Either;
// `temp_span`, where a literal's temporary is) gives its place — known
// before it is built, for a temporary made before it to hold a value (and
// checked once it is built: lw_value_as, lw_loop_items).
lw_either_place :: proc(k: ^TC, e: Tree_Id, temp_span: Span = {}) -> bool {
    t := k.t
    if e == k.lower.compound.target { return true }
    #partial switch t.tag[e] {
    case .Paren, .Big_Endian:
        return lw_either_place(k, Tree_Id(t.a[e]), temp_span)
    case .Deref, .If_Expr, .Index:
        return true
    case .Array, .Literal, .Broadcast:
        return temp_span != {}   // (built in a temporary, placed at its use: lw_built)
    case .Ident, .Type_Name:
        ref := tc_ref(k, e)
        ty := tc_node_type(k, e)
        switch {
        case ref.kind == .Variant:                return false
        case ref.kind == .Const:                  return graph_aggregate(ty)   // (a table's global)
        case ref.kind == .Module || ref.kind == .Type: return false
        case tc_name(k, e) == "void":             return false
        }
        if ts, is_scope := ty.(^Type_Scope); is_scope && !ts.is_module {   // (a fun's name: its global)
            if tc_name(k, e) in k.c.declared_funs && (ts.kind == .Fun || len(ts.params) > 0) || ref.kind == .Fun && ts.kind == .Fun { return false }
        }
        return true
    case .Field, .Dot_Ident:
        if t.tag[e] == .Dot_Ident && tc_sid(k, e) not_in k.annot.dot_bases { return false }   // (a variant)
        if lw_const_named(k, e) { return graph_aggregate(tc_node_type(k, e)) }
        base, field := lw_field_parts(k, e)
        bt := tc_node_type(k, base)
        if sd := as_scope_body(bt); sd != nil && sd_is_module(sd) {
            _, found := scope_lookup(sd_module_scope(sd), field)
            return found   // (else an enum's variant it holds)
        }
        if ut, is_union := bt.(^Type_Union); is_union && field != "tag" && field != "pad" {
            if _, has := ut.tag_map[field]; has { return false }
        }
        ft, is_member, _, known_ok := tc_field_type(k, e, base, bt, field, tree_span(t, e))
        if known_ok { return false }
        if fun, is_fun := ft.(^Type_Scope); is_fun && !is_member && fun.kind == .Fun { return false }
        return is_member
    }
    return false
}

// Whether a name or a field names a constant (lw_ident, lw_field: its use
// is lw_const_use's).
lw_const_named :: proc(k: ^TC, e: Tree_Id) -> bool {
    t := k.t
    #partial switch t.tag[e] {
    case .Paren:
        return lw_const_named(k, Tree_Id(t.a[e]))
    case .Ident:
        return tc_ref(k, e).kind == .Const
    case .Field, .Dot_Ident:
        if t.tag[e] == .Dot_Ident && tc_sid(k, e) not_in k.annot.dot_bases { return false }
        base, field := lw_field_parts(k, e)
        if t.tag[base] == .Ident && k.pkg != "" && tc_name(k, base) == k.pkg && make_flat_name(k.pkg, field) in k.consts { return true }
        if sd := as_scope_body(tc_node_type(k, base)); sd != nil && sd_is_module(sd) {
            if _, found := scope_lookup(sd_module_scope(sd), field); found { return make_flat_name(sd.name, field) in k.consts }
        }
    }
    return false
}

// A field access's base and its field's name.
lw_field_parts :: proc(k: ^TC, n: Tree_Id) -> (base: Tree_Id, field: string) {
    tr := k.t
    if tr.tag[n] == .Dot_Ident { return k.annot.dot_bases[tc_sid(k, n)], tc_text(Token_Id(tr.a[n])) }
    return Tree_Id(tr.a[n]), tc_text(Token_Id(tr.b[n]))
}

// An expression with no place of its own: an operation's value, a `?`'s, a
// slice, an assert, a take. (A deref names one.)
lw_holds :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[n] {
    case .Binary, .Unary, .Try, .Slice, .Assert, .Take: return true
    }
    return false
}

// What a use that takes a value at a type asks of it: an array literal is
// built at that type (a short one's other slots zero); a literal a slice
// views, in a temporary placed at the use's span — an array's at the slice's
// element type.
lw_use_type :: proc(k: ^TC, n: Tree_Id, t: Type, span: Span) -> (Dest, Span) {
    if t == nil { return {}, {} }
    e := tc_unparen(k, n)
    tag := k.t.tag[e]
    if sl, to_slice := distinct_base(t).(^Type_Slice); to_slice {
        #partial switch tag {
        case .Array:
            count := len(tree_list(k.t, k.t.a[e]))
            return {type_ = new_clone(Type_Fixed_Array{size = count, elem = sl.elem})}, span
        case .Literal:
            return {}, span
        }
        return {}, {}
    }
    if tag == .Array && graph_aggregate(t) { return {type_ = t}, {} }
    // (A span taken as an array: of bytes, read as it — tc_slice.)
    m, _ := tc_byte_node(k, n)
    if _, to_array := distinct_base(t).(^Type_Fixed_Array); to_array && k.t.tag[m] == .Slice { return {type_ = t}, {} }
    return {}, {}
}

// An argument or a returned value at the type its use takes: a view where
// one is taken (a partial array's header, an array's slice — its value held
// in the temporary made before it for a value, `held`: lw_either_place),
// else its value, widened.
lw_value_as :: proc(k: ^TC, e: Tree_Id, t: Type, r: Built, to: Type, span: Span, w: Graph_Widen,
                    held := NO_NODE) -> Operand {
    b := k.gb
    used := false
    defer if held != NO_NODE && !used { lw_fail(k, e, "a temporary made before a value it never holds") }
    if to != nil {
        _, to_slice := distinct_base(to).(^Type_Slice)
        _, from_array := distinct_base(t).(^Type_Fixed_Array)
        is_literal := k.t.tag[tc_unparen(k, e)] == .Array
        if _, at := lw_use_type(k, e, to, span); at != {} && !from_array {
            lw_fail(k, e, "a literal placed at its use, of no array")
        }
        _, to_ptr := distinct_base(to).(^Type_Ptr)
        _, from_ptr := distinct_base(t).(^Type_Ptr)
        if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(t) {
            return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), lw_value(k, r, e, t))
        }
        if to_slice && from_array {
            if r.place { return graph_op_value(b, .Slice, .Implied, span, to, "", r.v) }
            if held == NO_NODE { lw_fail(k, e, "a slice of an array value") }
            used = true
            graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", held, t, span), r.v)
            return graph_op_value(b, .Slice, .Implied, span, to, "", graph_var(b, "temp", held, t, span))
        }
        // (Bytes taken as an array: a view, copied into a temporary.)
        _, to_array := distinct_base(to).(^Type_Fixed_Array)
        m, big := tc_byte_node(k, e)
        is_span := k.t.tag[m] == .Slice
        if to_array && tc_byte_index(k, e) && r.place {
            // (That many bytes at the index, seen as the array.)
            graph_build_view(b, r.v, to, big, span)
            return graph_build_view_temp(b, r.v, to, span)
        }
        if to_array && is_span && r.v.op != NO_NODE && r.v.op == k.lower.span_read.op && k.lower.span_read.scalar {
            // (That many bytes at the span's start, seen as the array.)
            return graph_build_view_temp(b, graph_build_span_view(b, r.v, to, big, span), to, span)
        }
        if is_literal && graph_aggregate(to) && r.v.op != NO_NODE && b.g.type_[r.v.op] == to { return r.v }
        if to_array && (tc_byte_index(k, e) || is_span && is_byte_buffer(tc_node_type(k, Tree_Id(k.t.a[m])))) || is_literal && graph_aggregate(to) {
            lw_fail(k, e, "bytes or a literal at its use's type")
        }
    }
    return graph_build_widen(b, lw_value(k, r, e, t), span, w)
}

// Whether a branch may fill only a prefix of a partial array: what is no
// number, literal or operation.
lw_may_fill_prefix :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[tc_unparen(k, n)] {
    case .Number, .Char, .True, .False, .Array, .Literal, .Binary, .Unary, .Deref: return false
    }
    return true
}

// A built value stored where it goes: at the destination's type (a number
// widened to it).
lw_store :: proc(k: ^TC, e: Tree_Id, t: Type, r: Built, d: Dest, span: Span, settle := false) -> (wrote, zeroed: bool) {
    b := k.gb
    if r.into { return }
    if r.temp {
        graph_build_write_at(b, graph_dest_place(b, d, span), r.v, span)
        return true, false
    }
    if lw_builds_into(k, e) { lw_fail(k, e, "a value built in place, taken as one") }
    dt := graph_dest_type(b, d)
    _, to_ptr := distinct_base(dt).(^Type_Ptr)
    _, from_ptr := distinct_base(t).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(dt) && graph_partial_of(t) {
        // A partial array seen as a slice's header.
        v := graph_op_value(b, .Cast, .Implied, span, dt, type_name(dt), lw_value(k, r, e, t))
        graph_build_write_at(b, graph_dest_place(b, d, span), v, span)
        return
    }
    _, to_slice := distinct_base(dt).(^Type_Slice)
    _, from_array := distinct_base(t).(^Type_Fixed_Array)
    if to_slice && from_array {
        if !r.place { lw_fail(k, e, "a slice of an array value") }
        v := graph_op_value(b, .Slice, .Implied, span, dt, "", r.v)
        graph_build_write_at(b, graph_dest_place(b, d, span), v, span)
        return
    }
    // (Bytes read as the destination's type: lw_store_bytes, lw_store_span.)
    if m, _ := tc_byte_node(k, e); d.type_ != nil && tc_byte_flow(k, d.type_, e, t) == .Read {
        #partial switch k.t.tag[m] {
        case .Index: return lw_store_bytes(k, e, r, d, dt, span)
        case .Slice: return lw_store_span(k, e, r, d, dt, span)
        }
    }
    val := graph_build_widen(b, lw_value(k, r, e, t), span, {to = dt, settle_to = settle})
    graph_build_write_at(b, graph_dest_place(b, d, span), val, span)
    return true, false
}

// What builds where it goes (a literal, an array, a construction): never
// taken as a value.
lw_builds_into :: proc(k: ^TC, e: Tree_Id) -> bool {
    n := tc_unparen(k, e)
    #partial switch k.t.tag[n] {
    case .Literal, .Array: return true
    case .Call, .Method_Call:
        callee := tc_callee(k, n)
        return callee != nil && callee.kind == .Struct
    }
    return false
}

// A struct's field's node, made with its declaration (else none: a local's
// is made by its caller).
lw_field_decl :: proc(k: ^TC, fields_of: ^Type_Scope, name: string, target, value: Tree_Id, span: Span) -> Node_Id {
    b := k.gb
    if fields_of == nil { return NO_NODE }
    key := tc_sid(k, target)
    if d, made := b.body.fields[key]; made { return d }   // (made with the others declared with it)
    inits := []Span{tree_span(k.t, value)} if value != 0 else nil
    graph_build_fields(b, {name}, {k.t.main[target]}, span, {key}, inits, false)
    return b.body.fields[key]
}

// An expression that names a place without running anything: walking it
// again gives the same place.
lw_pure_place :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := k.t
    #partial switch t.tag[n] {
    case .Paren: return lw_pure_place(k, Tree_Id(t.a[n]))
    case .Ident, .Self: return true
    case .Field, .Deref: return lw_pure_place(k, Tree_Id(t.a[n]))
    case .Index:
        #partial switch t.tag[tc_unparen(k, Tree_Id(t.b[n]))] {
        case .Number, .Ident: return lw_pure_place(k, Tree_Id(t.a[n]))
        }
    }
    return false
}

// A member's place: its base's (through a pointer, what it points at), then
// the field — or an array's swizzle.
lw_member_place :: proc(k: ^TC, n: Tree_Id, field: string, base: Built, bt: Type, t: Type, self := false) -> Operand {
    b := k.gb
    if !base.ok || !base.place { lw_fail(k, n, "a field of a value") }
    span := tree_span(k.t, n)
    p := base.v
    if pt, is_ptr := distinct_base(bt).(^Type_Ptr); is_ptr && !self {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)
    }
    _, is_array := distinct_base(graph_pointee(bt)).(^Type_Fixed_Array)
    return graph_op_value(b, .Swizzle if is_array else .Field, .Explicit, span, t, field, p)
}

// What building a value in place gives its use: nothing more (built into
// where it goes); else its temporary, typed — read, or its place.
lw_built :: proc(k: ^TC, want: Build_Want, in_temp, into_temp: bool, d: Dest, t: Type, span: Span, placed: bool) -> Built {
    b := k.gb
    if !in_temp { return {v = NO_VALUE, ok = true, into = true} }
    tt := d.type_ if d.type_ != nil else t
    p := graph_build_temp_end(b, d, tt, span)
    switch {
    case into_temp:                return {v = graph_read(b, p, tt, span), ok = true, temp = true}
    case want == .Place || placed: return {v = p, place = true, ok = true}
    }
    return {v = graph_read(b, p, tt, span), ok = true}
}

// A place however its base is reached: a field, an element, what a pointer
// points at.
lw_is_place_form :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[tc_unparen(k, n)] {
    case .Field, .Index, .Deref: return true
    }
    return false
}

// --- bytes --------------------------------------------------------------------

// An element of bytes read into its destination (lw_store): a slice or a
// partial array filled by a byte read; else the bytes there seen as the
// destination's type, read, written. (`zeroed`: a new partial array it fills
// was zero first.)
lw_store_bytes :: proc(k: ^TC, e: Tree_Id, r: Built, d: Dest, dt: Type, span: Span) -> (wrote, zeroed: bool) {
    b := k.gb
    _, big := tc_byte_node(k, e)
    if !r.place { lw_fail(k, e, "bytes read as another type") }
    if is_slice_type(dt) || is_partial_array(dt) {
        buf, off := graph_build_byte_operands(b, r.v, span)
        graph_op(b, .Byte_Read, .Explicit, span, d.type_, "#big_endian" if big else "", graph_dest_place(b, d, span), buf, off)
        return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
    }
    graph_build_view(b, r.v, dt, big, span)
    val := graph_read(b, r.v, dt, span)
    graph_build_write_at(b, graph_dest_place(b, d, span), val, span)
    return true, false
}

// A span of bytes read as the destination's type: its bytes' place and
// bounds, as its slice built them; a register value the bytes at its start
// seen as it, read, else a byte read — at the span, where its failures say
// it is. (A new partial array is zero first.)
lw_store_span :: proc(k: ^TC, e: Tree_Id, r: Built, d: Dest, dt: Type, span: Span) -> (wrote, zeroed: bool) {
    b := k.gb
    m, big := tc_byte_node(k, e)
    if r.v.op == NO_NODE || r.v.op != k.lower.span_read.op || k.lower.span_read.scalar == graph_aggregate(dt) {
        lw_fail(k, e, "a span of bytes read as another type")
    }
    if k.lower.span_read.scalar {
        val := graph_read(b, graph_build_span_view(b, r.v, dt, big, span), dt, span)
        graph_build_write_at(b, graph_dest_place(b, d, span), val, span)
        return true, false
    }
    buf, lo, hi := graph_build_span_operands(b, r.v, span)
    graph_op(b, .Byte_Read, .Explicit, tree_span(k.t, m), d.type_, "#big_endian" if big else "", graph_dest_place(b, d, span), buf, lo, hi)
    return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
}

// `&bytes[i]` where a pointer to another type takes it: a view of the bytes
// as that type, its address a pointer to it (its bounds checked where made).
lw_byte_view_address :: proc(k: ^TC, expected: Type, value: Tree_Id) {
    pt, is_ptr := expected.(^Type_Ptr)
    if !is_ptr { return }
    if _, to_byte := pt.elem.(Type_Byte); to_byte { return }
    u := tc_unparen(k, value)
    b := k.gb
    if k.t.tag[u] != .Unary { return }
    ops, built := k.lower.byte_addrs[tc_sid(k, u)]
    if !built { return }
    _, big := tc_byte_node(k, Tree_Id(k.t.a[u]))
    graph_build_view(b, {ops[1], 0}, pt.elem, big, tree_span(k.t, u))
    graph_type(b, ops[0], new_clone(Type_Ptr{elem = pt.elem}))
}
