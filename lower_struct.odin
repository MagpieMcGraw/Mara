package mara

import "core:slice"

// Lowering structs (what tc_struct.odin checks): fields, literals,
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
    if lw_own_const(k, n, base) { return lw_const_use(k, lw_const_of(k, n, tc_ref(k, n).decl), n, tc_node_type(k, n), want, w) }
    bt := tc_node_type(k, base)
    if sd := as_scope_body(bt); sd != nil && sd_is_module(sd) {
        return lw_module_member(k, n, base, field, bt, want, w)
    }
    // (What reads no value of its base — a union's variant, an enum's, a
    // fun — builds none of it.)
    if ut, is_union := distinct_base(bt).(^Type_Union); is_union && field != "tag" && field != "pad" {
        if _, has := ut.tag_map[field]; has { return lw_union_variant(k, ut, field, span, want, w, dest, temp, temp_span) }
    }
    t, is_member, known, known_ok := lw_field_is(k, n)
    if known_ok {
        if want == .Place { return {} }
        return {v = graph_const(b, w, span, t, field, Const_Value{int = known | lw_err_site(k, n)}), ok = true}
    }
    if fun, is_fun := t.(^Type_Scope); is_fun && !is_member && fun.kind == .Fun {
        if want == .Place { return {} }
        return {v = graph_op_value(b, .Global, w, span, t, field), ok = true}
    }
    br := lw_field_base(k, base, span, w)
    if !is_member { return {} }
    p := lw_member_place(k, n, field, br, bt, t, tc_is_self(k, base))
    if p == NO_VALUE { return {} }
    if want == .Value { return {v = graph_read(b, p, t, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// What `x.f` is, as the checker found it (tc_field): its type; the value it
// knows (an enum's variant, an array's length, a text constant's); else
// whether it's a member — a field, a header's, a swizzle — read through
// its base, or no member (a fun of its struct's, a type it has).
lw_field_is :: proc(k: ^TC, n: Tree_Id) -> (t: Type, member: bool, known: i128, known_ok: bool) {
    if kv, has := k.annot.known[tc_sid(k, n)]; has { return kv.t, false, kv.value, true }
    r := tc_ref(k, n).kind
    return tc_node_type(k, n), r == .Field || r == .Builtin, 0, false
}

// A field's base, as a field reads it: its place (its value held, a
// call's), else either. (A module's or a type's name is no value: nothing
// of it built.)
lw_field_base :: proc(k: ^TC, base: Tree_Id, span: Span, w: Written) -> Built {
    if r := tc_ref(k, tc_unparen(k, base)).kind; r == .Module || r == .Type { return {} }
    ask: Build_Want = .Place if lw_holds(k, tc_unparen(k, base)) || tc_is_call(k, tc_unparen(k, base)) || tc_is_self(k, base) else .Either
    return lw_expr(k, base, ask, w, temp_span = span)
}

// `m.X`, m a module (tc_module_member): an enum's variant it holds, its
// value; its constant, a value of its own; else its member (the base
// built).
lw_module_member :: proc(k: ^TC, n, base: Tree_Id, field: string, bt: Type, want: Build_Want, w: Written) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    t := tc_node_type(k, n)
    ref := tc_ref(k, n)
    if ref.kind == .Variant {
        et, is_enum := distinct_base(t).(^Type_Enum)
        if !is_enum { lw_fail(k, n, "a module's member of no enum") }
        return lw_enum_value(k, et, et.variants[field], field, span, want, w, lw_err_site(k, n))
    }
    if ref.kind == .Const { return lw_const_use(k, lw_const_of(k, n, ref.decl), n, t, want, w) }
    // (A fun of the module as a value, `gl_load(sdl.GL_GetProcAddress)`: its
    // global, as its bare name gives — lw_ident. A module holds no place.)
    if lw_names_fun(k, n, t) {
        if want == .Place { return {} }
        return {v = graph_op_value(b, .Global, w, span, t, field), ok = true}
    }
    p := lw_member_place(k, n, field, lw_field_base(k, base, span, w), bt, t)
    if p == NO_VALUE { return {} }
    if want == .Value { return {v = graph_read(b, p, t, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// A variant by itself (`.Circle`, `Shape.Circle`): a union's, constructed;
// an enum's, its value.
lw_variant_of :: proc(k: ^TC, t: Type, name: string, span: Span, want: Build_Want, w: Written,
                      dest: Dest, temp: bool, temp_span: Span, site := i128(0)) -> Built {
    // (A named one's — `type U`, `distinct E` — as its base's.)
    tb := distinct_base(t)
    if ut, is_union := tb.(^Type_Union); is_union { return lw_union_variant(k, ut, name, span, want, w, dest, temp, temp_span) }
    return lw_enum_value(k, tb.(^Type_Enum), lw_variant_value(t, name), name, span, want, w, site)
}

// An error's variant's site, where it makes an err (tc_note_err_site): its
// atom + 1, above the kind's 32 bits. 0: none.
lw_err_site :: proc(k: ^TC, n: Tree_Id) -> i128 {
    if site, ok := k.annot.err_sites[tc_sid(k, n)]; ok { return i128(site) << 32 }
    return 0
}

// An enum's variant, as a value: its tag, known (an error's, with where it
// makes an err above it: `site`, lw_err_site).
lw_enum_value :: proc(k: ^TC, et: ^Type_Enum, value: int, name: string, span: Span, want: Build_Want, w: Written, site := i128(0)) -> Built {
    if want == .None || want == .Place { return {} }
    return {v = graph_const(k.gb, w, span, et, name, Const_Value{int = i128(value) | site}), ok = true}
}

// A union's variant as a value, `.Rect`: constructed where it goes — else in
// a temporary — its constructor running its fields' defaults (on its
// params'); a literal, `Rect{…}`, runs none.
lw_union_variant :: proc(k: ^TC, ut: ^Type_Union, name: string, span: Span, want: Build_Want, w: Written,
                         dest: Dest, temp: bool, temp_span: Span) -> Built {
    b := k.gb
    if want == .Place { return {} }
    args := lw_variant_args(k, ut, name, span)
    if want == .Into {
        d := dest
        if temp { d = graph_build_temp(b, temp_span, build_temp_type(d)) }
        graph_build_variant(b, ut, name, d, span, args, construct = true)
        return lw_built(k, want, temp, temp, d, ut, temp_span, false)
    }
    d := graph_build_temp(b, span, ut)
    graph_build_variant(b, ut, name, d, span, args, construct = true)
    return {v = graph_read(b, graph_dest_place(b, d, span), ut, span), ok = true}
}

// A variant's constructor's arguments where none are written: its params'
// defaults (tc_variant_built).
lw_variant_args :: proc(k: ^TC, t: Type, name: string, span: Span) -> []Operand {
    ut, is_union := distinct_base(t).(^Type_Union)
    if !is_union { return nil }
    st := ut.variant_structs[name]
    return lw_ctor_args(k, st, span) if st != nil && st.node != 0 else nil
}

// `Rect(5)`, `Shape.Rect(5)` (tc_variant_call): the variant built where it
// goes — else in a temporary — its constructor run on the arguments, then
// the fields its overrides give written.
lw_variant_call :: proc(k: ^TC, n: Tree_Id, ut: ^Type_Union, vst: ^Type_Scope, args: []Operand, want: Build_Want, w: Written,
                        dest: Dest, temp: bool, temp_span: Span, overrides: Tree_Id, made := false) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    if want == .Place { lw_fail(k, n, "a variant's call's place") }
    name := ""
    for vname in ut.variants { if ut.variant_structs[vname] == vst { name = vname } }
    d := dest
    switch {
    case want != .Into:  d = graph_build_temp(b, span, ut)
    case temp && !made: d = graph_build_temp(b, temp_span, build_temp_type(d))
    }
    gl := graph_build_literal(b, span, name, false, ut, d, args, construct = true)
    if overrides != 0 { lw_literal_fields(k, overrides, tree_list(k.t, k.t.b[overrides]), &vst.sd, gl) }
    if want == .Into { return lw_built(k, want, temp, temp, d, ut, temp_span, false) }
    return {v = graph_read(b, graph_dest_place(b, d, span), ut, span), ok = true}
}

// `#self` (tc_self): the place a constructor builds, or its address.
lw_self :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    t := tc_node_type(k, n)
    f := t.(^Type_Ptr).elem
    self := graph_var(b, b.self, f, span)
    if want == .Place { return {v = self, place = true, ok = true} }
    return {v = graph_op_value(b, .Address, w, span, t, "", self), ok = true}
}

// --- literals -------------------------------------------------------------------

// `Foo{…}`, `Foo{0}`, `{…}`, `[3!]f32{…}`, `{all v}` (tc_literal): its
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
    _, to_list := distinct_base(t).(^Type_Partial_Array)
    list_fill := fd == nil && to_list && tr.tag[n] == .Broadcast   // (`all v` into a list where it goes: tc_literal)
    // (A named struct or union — `type P`, `distinct U` — built as its base.)
    ts, _ := distinct_base(t).(^Type_Scope)
    vst: ^Type_Scope
    if variant != "" { vst = distinct_base(t).(^Type_Union).variant_structs[variant] }
    zero := len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0"
    sd: ^Scope_Body
    if vst != nil {
        sd = &vst.sd
    } else if fa == nil && fd == nil && !list_fill && !empty {
        sd = &ts.sd
    }
    d := dest
    into_temp := temp
    in_temp := want != .Into || into_temp
    placed := want != .Into && temp_span != {}
    at := temp_span if into_temp || placed else span
    gl: ^Graph_Literal
    broadcast := (fa != nil || fd != nil || list_fill) && tc_is_broadcast(k, n)
    if in_temp { d = graph_build_temp(b, at, build_temp_type(d)) }
    if fa != nil || fd != nil || list_fill {
        if !broadcast { gl = graph_build_literal(b, span, name, zero, t, d) }
    } else if empty {
        gl = graph_build_literal(b, span, name, zero, t, d)
    } else {
        // (A literal runs no constructor: its zero, then its entries.)
        gl = graph_build_literal(b, span, name, zero, t, d)
    }
    if gl == nil && !broadcast { lw_fail(k, n, "a literal the graph builds no way") }
    if fd != nil || list_fill {
        lw_broadcast_fill(k, n, Tree_Id(tr.a[entries[0]]), t, d)
    } else if fa != nil {
        lw_array_entries(k, n, entries, t, gl, d, broadcast)
    } else if !zero && !empty {
        lw_literal_fields(k, n, entries, sd, gl)
        lw_literal_gaps(k, n, entries, sd, d, vst, name)
    }
    return lw_built(k, want, in_temp, into_temp, d, t, at, placed)
}

// A literal's fields it gives no value — unset, as it runs no constructor.
// Into a fun's own variable of a struct, they may be written after (flow.odin
// finds a read before); anywhere else — an argument, an element, a field, a
// constant, a union's variant — nothing can: each is said (Literal_Gap). A
// partial array's zero, an empty one, is a value.
lw_literal_gaps :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, sd: ^Scope_Body, d: Dest, vst: ^Type_Scope, variant: string) {
    b := k.gb
    tr := k.t
    if sd == nil { return }
    // (A fun's own variable: declared with it, or assigned it — its place computed.)
    decl := d.decl if d.kind == .Var else NO_NODE
    if d.kind == .At && graph_is_leaf(d.at.op) { decl = graph_refers(b.g, d.at.op) }
    if vst == nil && decl > 0 && int(decl) < len(b.g.kind) && graph_kind_of(b.g, 0) == .Fun && graph_kind_of(b.g, decl) == .Local && b.g.written[decl] == .Explicit { return }
    user := sd.fields[first_user_field(sd):]
    given := make(map[string]bool, allocator = context.temp_allocator)
    if len(entries) > 0 {
        if tr.tag[entries[0]] == .Named_Entry {
            for e in entries { given[tc_name(k, e)] = true }
        } else if call := tc_unparen(k, entries[0]); len(entries) == 1 && tc_is_call(k, call) && len(sd.fields) > 1 {
            return   // (a spread: every field the call's)
        } else {
            for _, i in entries { if i < len(user) { given[user[i].name] = true } }
        }
    }
    owner := sd.source_name if sd.source_name != "" else sd.name
    if vst != nil && variant != "" { owner = variant }
    gaps := make([dynamic]Literal_Gap, context.temp_allocator)
    for f in user {
        if given[f.name] { continue }
        if _, pa := distinct_base(f.type_).(^Type_Partial_Array); pa { continue }
        append(&gaps, Literal_Gap{tree_span(tr, n), f.name, owner, len(user)})
    }
    if len(gaps) > 0 { graph_note_literal_gaps(b, gaps[:]) }
}

// `all v` into an array (tc_broadcast_fill): v, then the fill.
lw_broadcast_fill :: proc(k: ^TC, n, value: Tree_Id, lit_t: Type, d: Dest) {
    r := lw_expr(k, value)
    graph_build_fill(k.gb, tree_span(k.t, n), lit_t, d, r.v)
}

// An array literal's entries (tc_array_entries): each element into its slot,
// by position or by its swizzle letter; `{all v}`, v then the fill.
lw_array_entries :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, lit_t: Type, gl: ^Graph_Literal, d: Dest, fill: bool) {
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
            returns := tc_call_returns(k, call)
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
    lw_store(k, value, tc_node_type(k, value), r, d, span)
    lw_byte_view_address(k, f.type_, value)
}

// `Foo(args)`: its constructor run where it goes (else in a
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
        at = graph_dest_var(graph_slot(b, "temp", ts, span), ts)
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

// `v{ x = 1 }` as a statement (tc_override): each field given written into v's
// — through a pointer, into what it points at's (as `v.x = 1` is).
lw_override :: proc(k: ^TC, e: Tree_Id) -> bool {
    if !(k.annot.overrides[tc_sid(k, e)] or_else false) { return false }
    tr := k.t
    ty := Tree_Id(tr.a[e])
    vt := tc_node_type(k, ty)
    sd := resolve_to_struct_type(k.c, vt)
    d := graph_dest_var(lw_local(k, ty), vt, tc_sid(k, ty))
    if pt, is_ptr := distinct_base(vt).(^Type_Ptr); is_ptr {
        span := tree_span(tr, ty)
        d = Dest{kind = .At, at = graph_op_value(k.gb, .Deref, .Implied, span, pt.elem, "", graph_dest_place(k.gb, d, span)), type_ = pt.elem}
    }
    gl := graph_build_override(k.gb, d, sd)
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
        // (A header's field, an array's swizzle: as the checker typed it.)
        ft := tc_node_type(k, target)
        if ft == nil { lw_fail(k, target, "a write to an unknown field") }
        at := lw_at(k, target)   // (the field's place: the target's)
        place := lw_member_place(k, target, field, br, bt, ft)
        k.gb.at = at
        lw_store_at(k, value, place, span, op_tok, target, s)
        return
    }
    ft := resolve_struct_field(sd, field)
    if ft == nil { lw_fail(k, target, "a write to an unknown field") }
    at := lw_at(k, target)   // (the field's place: the target's)
    place := lw_member_place(k, target, field, br, bt, ft)
    k.gb.at = at
    lw_store_at(k, value, place, span, op_tok, target, s)
}

// `p^ = v` (tc_deref_assign): the place p points at, then v into it.
lw_deref_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    at := tree_span(tr, target)
    pr := lw_expr(k, Tree_Id(tr.a[target]), .Place, temp_span = at)
    place := NO_VALUE
    if p, is_ptr := tc_node_type(k, Tree_Id(tr.a[target])).(^Type_Ptr); is_ptr {
        lowering := lw_at(k, target)   // (what it points at: the target's)
        place = graph_op_value(k.gb, .Deref, .Explicit, at, p.elem, "", pr.v)
        k.gb.at = lowering
    }
    lw_store_at(k, value, place, span, op_tok, target, s)
}

// A value written into a place built for it (tc_store_at): built into a
// temporary where it builds in place, then written at the place's type.
lw_store_at :: proc(k: ^TC, value: Tree_Id, place: Operand, span: Span, op_tok: Token_Id = 0, target: Tree_Id = 0, s: Tree_Id = 0) {
    b := k.gb
    if place == NO_VALUE { lw_fail(k, value, "a write to no place") }
    pt := graph_type(b.g, place.op) if place.op != NO_NODE else nil
    d := Dest{kind = .At, at = place, type_ = pt}
    if op_tok != 0 {
        saved := k.lower.compound
        k.lower.compound = {target, place}
        r := lw_compound_value(k, s, op_tok, target, value, .Into)
        k.lower.compound = saved
        lw_store(k, 0, tc_node_type(k, s), r, lw_parallel_hold(k, d, span), span, settle = true)
        return
    }
    if tc_is_void(k, value) {
        graph_build_write_at(b, place, graph_build_void(b, pt, tree_span(k.t, value)), span)
        return
    }
    r := lw_expr(k, value, .Into, dest = d, temp = true, temp_span = span)
    lw_store(k, value, tc_node_type(k, value), r, lw_parallel_hold(k, d, span), span, settle = true)
}
