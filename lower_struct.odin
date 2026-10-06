package mara

import "core:slice"

// Lowering structs (tc_struct.odin's building): fields, literals,
// constructions, unions' variants, writes to a field or through a pointer.

// `x.f` (tc_field): a struct's field — through a pointer, what it points at;
// an array's length or swizzle; a header's field; a module's member; a
// union's variant.
lw_field :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    base := Tree_Id(tr.a[n])
    field: string
    if tr.tag[n] == .Dot_Ident {
        base, field = k.annot.dot_bases[tc_sid(k, n)], tc_text(Token_Id(tr.a[n]))
    } else {
        field = tc_text(Token_Id(tr.b[n]))
    }
    // (`pkg.X` inside pkg: its own constant.)
    if tr.tag[base] == .Ident && k.pkg != "" && tc_name(k, base) == k.pkg {
        if kc, ok := k.consts[make_flat_name(k.pkg, field)]; ok { return tc_const_use(k, kc, n, tc_node_type(k, n), want, w) }
    }
    ask: Build_Want = .Place if tc_holds(k, tc_unparen(k, base)) || tc_is_call(k, tc_unparen(k, base)) || tc_is_self(k, base) else .Either
    mark := graph_build_mark(b)
    br := lw_expr(k, base, ask, w, temp_span = span)
    bt := tc_node_type(k, base)
    if sd := as_scope_body(bt); sd != nil && sd_is_module(sd) {
        _, r := tc_module_member(k, n, sd, field, bt, br, mark, true, want, w)
        return r
    }
    if ut, is_union := bt.(^Type_Union); is_union && field != "tag" && field != "pad" {
        if _, has := ut.tag_map[field]; has {
            graph_build_drop_since(b, mark)
            return lw_union_variant(k, ut, field, span, want, w, dest, temp, temp_span)
        }
    }
    t, is_member, known, known_ok := tc_field_type(k, n, base, bt, field, span)
    if known_ok {
        graph_build_drop_since(b, mark)
        if want == .Place { return {} }
        return {v = graph_const(b, w, span, t, field, Const_Value{int = known}), ok = true}
    }
    if fun, is_fun := t.(^Type_Scope); is_fun && !is_member && fun.kind == .Fun {
        graph_build_drop_since(b, mark)
        if want == .Place { return {} }
        return {v = graph_op_value(b, .Global, w, span, t, field), ok = true}
    }
    if !is_member { return {} }
    p := tc_member_place(k, n, field, br, bt, t, tc_is_self(k, base))
    if p == NO_VALUE { return {} }
    if want == .Value { return {v = graph_read(b, p, t, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// A variant by itself (tc_variant_of): a union's, constructed; an enum's,
// its value.
lw_variant_of :: proc(k: ^TC, t: Type, name: string, span: Span, want: Build_Want, w: Written,
                      dest: Dest, temp: bool, temp_span: Span) -> Built {
    if ut, is_union := t.(^Type_Union); is_union { return lw_union_variant(k, ut, name, span, want, w, dest, temp, temp_span) }
    return tc_variant_value(k, t.(^Type_Enum), lw_variant_value(t, name), name, span, want, w)
}

// A union's variant as a value (tc_union_variant): constructed where it goes
// — else in a temporary — then its fields' defaults.
lw_union_variant :: proc(k: ^TC, ut: ^Type_Union, name: string, span: Span, want: Build_Want, w: Written,
                         dest: Dest, temp: bool, temp_span: Span) -> Built {
    b := k.gb
    if want == .Place { return {} }
    if want == .Into {
        d := dest
        if temp { d = graph_build_temp(b, temp_span, build_temp_type(d)) }
        lw_variant_build(k, ut, name, d, span)
        return tc_built(k, want, temp, temp, d, ut, temp_span, false)
    }
    d := graph_build_temp(b, span, ut)
    lw_variant_build(k, ut, name, d, span)
    return {v = graph_read(b, graph_dest_place(b, d, span), ut, span), ok = true}
}

// A variant built at d (tc_variant_build): its construction, then its defaults.
lw_variant_build :: proc(k: ^TC, t: Type, name: string, d: Dest, span: Span) {
    st := graph_build_variant(k.gb, t, name, d, span)
    dd := d
    lw_variant_defaults(k, st, nil, Dest{kind = .Variant, name = name, type_ = st, parent = &dd}, span)
}

// A variant's field defaults a literal doesn't give (tc_variant_defaults).
lw_variant_defaults :: proc(k: ^TC, st: ^Type_Scope, given: map[string]bool, d: Dest, span: Span) {
    if st == nil { return }
    for f in st.fields {
        if f.default_node == 0 || f.name in given { continue }
        v := lw_default(k, f.default_node, f.type_, span, {to = f.type_})
        graph_build_field_default(k.gb, d, f.name, f.type_, v, span)
    }
}

// `#self` (tc_self): the place a constructor builds, or its address.
lw_self :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    t := tc_node_type(k, n)
    f := t.(^Type_Ptr).elem
    self := graph_var(b, "Self", b.self, f, span)
    if want == .Place { return {v = self, place = true, ok = true} }
    return {v = graph_op_value(b, .Address, w, span, t, "", self), ok = true}
}

// --- literals -------------------------------------------------------------------

// `Foo{…}`, `Foo{0}`, `{…}`, `[3]f32{…}`, `{all v}` (tc_literal): its
// construction where it goes (else in a temporary), then each entry stored.
lw_literal :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    ty := Tree_Id(tr.a[n])
    entries := tree_list(tr, tr.b[n])
    if tr.tag[n] == .Broadcast { ty, entries = 0, slice.clone([]Tree_Id{n}, context.temp_allocator) }
    name := tc_name(k, ty) if ty != 0 && tr.tag[ty] == .Ident else ""
    t := tc_node_type(k, n)
    fd: ^TC_Field_Default
    if ty == 0 && n == k.field_default.value && tc_is_broadcast(k, n) { fd = &k.field_default }
    variant := name if ty != 0 && tr.tag[ty] == .Ident && tc_ref(k, ty).kind == .Variant else ""
    empty := fd == nil && ty != 0 && tr.tag[ty] != .Ident && tr.tag[ty] != .Field && is_partial_array(t)
    fa: ^Type_Fixed_Array
    if tc_is_fixed_array(t) { fa = distinct_base(t).(^Type_Fixed_Array) }
    ts, _ := t.(^Type_Scope)
    vst: ^Type_Scope
    if variant != "" { vst = t.(^Type_Union).variant_structs[variant] }
    zero := len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0"
    sd: ^Scope_Body
    if vst != nil {
        sd = &vst.sd
    } else if fa == nil && fd == nil && !empty {
        sd = &ts.sd
    }
    d := dest
    into_temp := temp
    in_temp := want != .Into || into_temp
    placed := want != .Into && temp_span != {}
    at := temp_span if into_temp || placed else span
    gl: ^Graph_Literal
    broadcast := (fa != nil || fd != nil) && tc_is_broadcast(k, n)
    if in_temp { d = graph_build_temp(b, at, build_temp_type(d)) }
    if fa != nil || fd != nil {
        if !broadcast { gl = graph_build_literal(b, span, name, zero, t, d) }
    } else if empty {
        gl = graph_build_literal(b, span, name, zero, t, d)
    } else if vst != nil {
        gl = graph_build_literal(b, span, name, zero, t, d)
        if gl != nil { lw_variant_defaults(k, gl.variant, tc_literal_given(k, entries, sd), gl.parent, span) }
    } else {
        args: []Operand
        if !zero { args = lw_ctor_args(k, ts, span) }
        gl = graph_build_literal(b, span, name, zero, t, d, args)
        if gl != nil && gl.variant != nil { lw_variant_defaults(k, gl.variant, tc_literal_given(k, entries, sd), gl.parent, span) }
    }
    if gl == nil && !broadcast { lw_fail(k, n, "a literal the graph builds no way") }
    if fd != nil {
        lw_broadcast_fill(k, n, Tree_Id(tr.a[entries[0]]), t, d)
    } else if fa != nil {
        lw_array_entries(k, n, entries, fa, t, gl, d, broadcast)
    } else if !zero && !empty {
        lw_literal_fields(k, n, entries, sd, gl)
    }
    return tc_built(k, want, in_temp, into_temp, d, t, at, placed)
}

// `all v` into an array (tc_broadcast_fill): v, then the fill.
lw_broadcast_fill :: proc(k: ^TC, n, value: Tree_Id, lit_t: Type, d: Dest) {
    r := lw_expr(k, value)
    graph_build_fill(k.gb, tree_span(k.t, n), lit_t, d, r.v)
}

// An array literal's entries (tc_array_entries): each element into its slot,
// by position or by its swizzle letter; `{all v}`, v then the fill.
lw_array_entries :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, fa: ^Type_Fixed_Array, lit_t: Type, gl: ^Graph_Literal, d: Dest, fill: bool) {
    tr := k.t
    span := tree_span(tr, n)
    elem_t := graph_elem_type(lit_t) if gl != nil else nil
    if len(entries) == 1 && tr.tag[entries[0]] == .Broadcast {
        if fill { lw_broadcast_fill(k, n, Tree_Id(tr.a[entries[0]]), lit_t, d) }
        return
    }
    if len(entries) == 0 || len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0" { return }
    if gl == nil { lw_fail(k, n, "an array's entries with no literal built") }
    if tr.tag[entries[0]] != .Named_Entry {
        for e, i in entries { lw_store_into(k, e, graph_build_literal_elem(gl, i, elem_t), span) }
        return
    }
    for e in entries {
        idx := swizzle_char_to_index(tc_name(k, e)[0])
        lw_store_into(k, Tree_Id(tr.a[e]), graph_build_literal_elem(gl, idx, elem_t), span)
    }
}

// A literal's entries against its struct's fields (tc_literal_fields):
// named, or by position — one call's results, its fields.
lw_literal_fields :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, sd: ^Scope_Body, gl: ^Graph_Literal) {
    tr := k.t
    span := tree_span(tr, n)
    if len(entries) == 0 { return }
    if tr.tag[entries[0]] != .Named_Entry {
        if call := tc_unparen(k, entries[0]); len(entries) == 1 && tc_is_call(k, call) && len(sd.fields) > 1 {
            returns := tc_call_returns(k, call, nil)
            fits := len(returns) == len(sd.fields)
            for f, i in sd.fields {
                if fits && types_incompatible(f.type_, returns[i]) { fits = false }
            }
            if !fits { lw_fail(k, n, "a spread literal that doesn't match") }
            spread := lw_expr(k, entries[0], .Value)
            if !graph_build_spread(k.gb, gl, span, spread.v) { lw_fail(k, n, "a spread literal of no call") }
            return
        }
        user := sd.fields[first_user_field(sd):]
        for e, i in entries {
            if i >= len(user) { break }
            lw_literal_field(k, e, user[i], i, "", span, gl)
        }
        return
    }
    for e in entries {
        idx := sd.field_map[tc_name(k, e)]
        lw_literal_field(k, Tree_Id(tr.a[e]), sd.fields[idx], 0, tc_name(k, e), span, gl)
    }
}

lw_literal_field :: proc(k: ^TC, value: Tree_Id, f: Struct_Type_Field, i: int, name: string, span: Span, gl: ^Graph_Literal) {
    d := graph_build_literal_field(gl, name, i)
    r := lw_expr(k, value, .Into, dest = d, temp_span = span)
    tc_store(k, value, tc_node_type(k, value), r, d, span)
    tc_byte_view_address(k, f.type_, value)
}

// `Foo(args)` (tc_construct): its constructor run where it goes (else in a
// temporary), then its override block's fields.
lw_construct :: proc(k: ^TC, n: Tree_Id, ts: ^Type_Scope, ops: []Operand, want: Build_Want, w: Written,
                     dest: Dest, temp: bool, temp_span: Span, made := false, overrides := Tree_Id(0)) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    if want == .Place { lw_fail(k, n, "a call's place") }
    at: Dest
    if want == .Into && temp && !made {
        at = graph_build_temp(b, temp_span, build_temp_type(dest))
    } else if want == .Into {
        at = dest
    } else {
        at = graph_dest_var("temp", graph_slot(b, "temp", ts, span), ts)
    }
    gl := graph_build_construct(b, ts, ts, at, ops, w, span)
    if overrides != 0 { lw_literal_fields(k, overrides, tree_list(k.t, k.t.b[overrides]), &ts.sd, gl) }
    switch {
    case want == .Into && temp:
        tt: Type = at.type_ if at.type_ != nil else Type(ts)
        p := graph_build_temp_end(b, at, tt, temp_span)
        return {v = graph_read(b, p, tt, temp_span), ok = true, temp = true}
    case want == .Into:
        return {v = NO_VALUE, ok = true, into = true}
    }
    return {v = graph_read(b, graph_dest_place(b, at, span), ts, span), ok = true}
}

// `v{ x = 1 }` as a statement (tc_override): each field given written into v's.
lw_override :: proc(k: ^TC, e: Tree_Id) -> bool {
    if !(k.annot.overrides[tc_sid(k, e)] or_else false) { return false }
    tr := k.t
    ty := Tree_Id(tr.a[e])
    vt := tc_node_type(k, ty)
    sd := resolve_to_struct_type(k.c, vt)
    gl := graph_build_override(k.gb, graph_dest_var(tc_name(k, ty), NO_NODE, vt), sd)
    lw_literal_fields(k, e, tree_list(tr, tr.b[e]), sd, gl)
    return true
}

// --- writes -----------------------------------------------------------------------

// `x.f = v` (tc_field_assign): the field's place, then the value into it.
lw_field_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    base := Tree_Id(tr.a[target])
    field := tc_text(Token_Id(tr.b[target]))
    br := lw_expr(k, base, .Either)
    bt := tc_node_type(k, base)
    sd := as_scope_body(bt)
    if sd == nil || len(sd.fields) == 0 {
        sd = nil
        if pt, is_ptr := bt.(^Type_Ptr); is_ptr {
            if psd := as_scope_body(pt.elem); psd != nil && len(psd.fields) > 0 { sd = psd }
        }
    }
    if sd == nil {
        // (A header's field, an array's swizzle.)
        ft := build_target_field_type(bt, field)
        if ft == nil { lw_fail(k, target, "a write to an unknown field") }
        lw_store_at(k, value, tc_member_place(k, target, field, br, bt, ft), span, op_tok, target, s)
        return
    }
    ft := resolve_struct_field(sd, field)
    if ft == nil { lw_fail(k, target, "a write to an unknown field") }
    lw_store_at(k, value, tc_member_place(k, target, field, br, bt, ft), span, op_tok, target, s)
}

// `p^ = v` (tc_deref_assign): the place p points at, then v into it.
lw_deref_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    at := tree_span(tr, target)
    pr := lw_expr(k, Tree_Id(tr.a[target]), .Place, temp_span = at)
    place := NO_VALUE
    if p, is_ptr := tc_node_type(k, Tree_Id(tr.a[target])).(^Type_Ptr); is_ptr {
        place = graph_op_value(k.gb, .Deref, .Explicit, at, p.elem, "", pr.v)
    }
    lw_store_at(k, value, place, span, op_tok, target, s)
}

// A value written into a place built for it (tc_store_at): built into a
// temporary where it builds in place, then written at the place's type.
lw_store_at :: proc(k: ^TC, value: Tree_Id, place: Operand, span: Span, op_tok: Token_Id = 0, target: Tree_Id = 0, s: Tree_Id = 0) {
    b := k.gb
    if place == NO_VALUE { lw_fail(k, value, "a write to no place") }
    pt := b.g.type_[place.op] if place.op != NO_NODE else nil
    d := Dest{kind = .At, at = place, type_ = pt}
    if op_tok != 0 {
        saved := k.compound
        k.compound = {target, place}
        r := lw_compound_value(k, s, op_tok, target, value, .Into)
        k.compound = saved
        tc_store(k, 0, tc_node_type(k, s), r, tc_parallel_hold(k, d, span), span, settle = true)
        return
    }
    if tc_is_void(k, value) {
        graph_build_write_at(b, place, graph_build_void(b, pt, tree_span(k.t, value)), span)
        return
    }
    r := lw_expr(k, value, .Into, dest = d, temp = true, temp_span = span)
    tc_store(k, value, tc_node_type(k, value), r, tc_parallel_hold(k, d, span), span, settle = true)
}
