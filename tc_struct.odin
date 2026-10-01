package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// Structs in the new checker: a field read or written, a struct built (a
// literal, a call of its constructor).

// The struct a type is, or points at (its fields found first).
tc_struct_of :: proc(k: ^TC, t: Type) -> ^Scope_Body {
    sd := as_scope_body(t)
    if sd == nil {
        if pt, is_ptr := t.(^Type_Ptr); is_ptr { sd = as_scope_body(pt.elem) }
    }
    if sd != nil { tc_struct_ensure(k, sd_type_scope(sd)) }
    return sd
}

// `x.f`: a struct's field (through a pointer, what it points at); an
// array's length or swizzle; a slice's or partial array's header field.
tc_field :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                 dest: Dest = {}, temp := false, temp_span := Span{}) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    base := Tree_Id(tr.a[n])
    field: string
    if tr.tag[n] == .Dot_Ident {
        // (`.len` in a subscript: its base's — tc_lower_dots.)
        base, field = k.dot_bases[n], tc_text(Token_Id(tr.a[n]))
    } else {
        field = tc_text(Token_Id(tr.b[n]))
    }
    // (`pkg.X` inside pkg: its own constant — its value's type.)
    if tr.tag[base] == .Ident && k.pkg != "" && tc_name(k, base) == k.pkg {
        if kc, ok := k.consts[make_flat_name(k.pkg, field)]; ok {
            t := tc_check(k, kc.value, env)
            k.const_nodes[n] = true
            return t, tc_const_use(k, kc, n, t, want, w)
        }
    }
    build := want != .None && tc_building(k) != nil
    ask := Fuse_Want.None
    mark: Graph_Mark
    if build {
        ask = .Place if tc_holds(k, base) || tc_is_call(k, tc_unparen(k, base)) || tc_is_self(k, base) else .Either
        mark = graph_fuse_mark(tc_building(k))
    }
    bt, br := tc_expr(k, base, env, ask, w, temp_span = span)
    if sd := as_scope_body(bt); sd != nil && sd_is_module(sd) {
        return tc_module_member(k, n, sd, field, bt, br, mark, build, want, w)
    }
    // (A union's variant: a value of its own — its base, built, left out.)
    if ut, is_union := bt.(^Type_Union); is_union && field != "tag" && field != "pad" {
        if _, has := ut.tag_map[field]; has {
            k.variant_nodes[n] = true
            if b := tc_building(k); build && b != nil { graph_fuse_drop_since(b, mark) }
            return ut, tc_union_variant(k, ut, field, span, want if build else .None, w, dest, temp, temp_span)
        }
    }
    t, is_member, known, known_ok := tc_field_type(k, n, base, bt, field, span)
    if _, is_enum := t.(^Type_Enum); is_enum && known_ok { k.variant_nodes[n] = true }
    if !build || tc_building(k) == nil { return t, {} }
    if known_ok {
        // (A length known — a fixed array's, a text constant's: its value;
        // its base, built, left out.)
        b := tc_building(k)
        graph_fuse_drop_since(b, mark)
        if want == .Place { return t, {} }
        return t, {v = graph_const(b, w, span, t, field, Const_Value{int = known}), ok = true}
    }
    if !is_member { return t, {} }
    p := tc_member_place(k, n, field, br, bt, t, tc_is_self(k, base))
    if p == NO_VALUE { return t, {} }
    if want == .Value { return t, {v = graph_read(tc_building(k), p, t, span), ok = true} }
    return t, {v = p, place = true, ok = true}
}

// A field's type: whether it names part of the value (a member), or a
// fixed array's length (its value, else -1).
tc_field_type :: proc(k: ^TC, n, base: Tree_Id, bt: Type, field: string, span: Span) -> (t: Type, member: bool, known: i128, known_ok: bool) {
    // (An enum's variant: its value, known. A union's tag or pad: part of the
    // value; its variant: a value of its own.)
    #partial switch v in bt {
    case ^Type_Enum:
        if val, has := v.variants[field]; has { return v, false, i128(val), true }
        tc_error(k, span, TYPE_ENUM_VARIANT, v.name, field)
        return Type_Error{}, false, 0, false
    case ^Type_Union:
        switch field {
        case "tag":
            if tag_et, found := k.table.enums[strings.concatenate({v.name, "_Tag"})]; found { return tag_et, true, 0, false }
            tc_error(k, span, TYPE_UNION_TAG_ENUM_INTERNAL_ERROR, v.name)
            return Type_Error{}, false, 0, false
        case "pad":
            if v.tag_pad == nil {
                tc_error(k, span, TYPE_UNION_PADDING_DECLARE_UNION_PAD, v.name)
                return Type_Error{}, false, 0, false
            }
            return v.tag_pad, true, 0, false
        }
        if _, has := v.tag_map[field]; has {
            tc_unsupported(k, n, "a union's variant as a value")
            return Type_Error{}, false, 0, false
        }
        tc_error(k, span, TYPE_UNION_VARIANT, v.name, field)
        return Type_Error{}, false, 0, false
    }

    if sd := tc_struct_of(k, bt); sd != nil && len(sd.fields) > 0 {
        if sd_is_module(sd) {
            tc_unsupported(k, n, "a module's member")
            return Type_Error{}, false, 0, false
        }
        for f in sd.fields {
            if f.is_using {
                tc_unsupported(k, n, "a field of a `using` field's struct")
                return Type_Error{}, false, 0, false
            }
        }
        if ft := resolve_struct_field(sd, field, k.table); ft != nil { return ft, true, 0, false }
        if sd.functions != nil && field in sd.functions {
            tc_unsupported(k, n, "a struct's function as a value")
            return Type_Error{}, false, 0, false
        }
        tc_error(k, span, TYPE_CLASS_FIELD, sd.name, field)
        return Type_Error{}, false, 0, false
    }
    obj := bt
    if pt, is_ptr := obj.(^Type_Ptr); is_ptr { obj = pt.elem }
    obj = distinct_base(obj)
    #partial switch v in obj {
    case ^Type_Fixed_Array:
        if field == "len" || field == "cap" { return Type_Numeric{kind = .Signed, bits = 64}, false, i128(v.size), true }
        if is_swizzle_field(field, v.size) {
            if len(field) == 1 { return v.elem, true, 0, false }
            return new_clone(Type_Fixed_Array{size = len(field), elem = v.elem}), true, 0, false
        }
        if is_all_swizzle_chars(field) {
            tc_error(k, span, TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY, field, v.size)
        } else {
            tc_error(k, span, TYPE_CANNOT_ACCESS_FIELD_ARRAY_TYPE, field, type_name(obj))
        }
        return Type_Error{}, false, 0, false
    case ^Type_Slice:
        switch field {
        case "ptr":        return new_clone(Type_Ptr{elem = v.elem}), true, 0, false
        case "len", "cap": return slice_header_width_type, true, 0, false
        }
        tc_error(k, span, TYPE_SLICE_TYPE_FIELD, type_name(obj), field)
        return Type_Error{}, false, 0, false
    case ^Type_Partial_Array:
        switch field {
        case "ptr":        return new_clone(Type_Ptr{elem = v.elem}), true, 0, false
        case "len", "cap":
            // (A text constant's: its length, known.)
            if b := tc_unparen(k, base); k.t.tag[b] == .Ident {
                if kc, ok := k.consts[tc_name(k, b)]; ok && k.t.tag[kc.value] == .String {
                    return slice_header_width_type, false, i128(len(tc_text(k.t.main[kc.value]))), true
                }
            }
            return slice_header_width_type, true, 0, false
        }
        tc_error(k, span, TYPE_PARTIAL_ARRAY_TYPE_FIELD, type_name(obj), field)
        return Type_Error{}, false, 0, false
    }
    if !is_any(bt) { tc_error(k, span, TYPE_CANNOT_ACCESS_FIELD_TYPE, field, type_name(bt)) }
    return Type_Error{}, false, 0, false
}

// A member's place: its base's (through a pointer, what it points at), then
// the field — or an array's swizzle.
tc_member_place :: proc(k: ^TC, n: Tree_Id, field: string, base: Fused, bt: Type, t: Type, self := false) -> Operand {
    b := tc_building(k)
    if b == nil { return NO_VALUE }
    if !base.ok || !base.place {
        tc_fail(k, "a field of a value")
        return NO_VALUE
    }
    span := tree_span(k.t, n)
    p := base.v
    if pt, is_ptr := distinct_base(bt).(^Type_Ptr); is_ptr && !self {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)
    }
    _, is_array := distinct_base(graph_pointee(bt)).(^Type_Fixed_Array)
    return graph_op_value(b, .Swizzle if is_array else .Field, .Explicit, span, t, field, p)
}

// `x.f = v`: the field's place, then the value into it.
// (`op_tok`: a compound assignment's operator — the value is `target op value`.)
tc_field_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    diag := value if op_tok == 0 else 0   // (the value, as diagnostics name it)
    tr := k.t
    span := tree_span(tr, s)
    base := Tree_Id(tr.a[target])
    field := tc_text(Token_Id(tr.b[target]))
    b := tc_building(k)
    bt, br := tc_expr(k, base, env, .Either if b != nil else .None)
    tc_struct_of(k, bt)   // (its fields known: a nested struct's, checked first)
    sd := as_scope_body(bt)
    if sd == nil || len(sd.fields) == 0 {
        sd = nil
        if pt, is_ptr := bt.(^Type_Ptr); is_ptr {
            if psd := as_scope_body(pt.elem); psd != nil && len(psd.fields) > 0 { sd = psd }
        }
    }
    if sd == nil {
        tc_header_assign(k, s, target, value, bt, br, field, env, op_tok)
        return
    }
    ft := resolve_struct_field(sd, field, k.table)
    place := NO_VALUE
    if ft != nil {
        k.hint = ft
        tc_set_type(k, target, ft)
        if tc_building(k) != nil { place = tc_member_place(k, target, field, br, bt, ft) }
    } else if tc_building(k) != nil {
        tc_fail(k, "a write to an unknown field")
    }
    vt := tc_store_at(k, value, place, env, span, op_tok, target)
    k.hint = nil
    if ft == nil {
        tc_error(k, span, TYPE_CLASS_FIELD, sd.name, field)
        return
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, field, pname)
    }
    tc_no_literal_slice(k, ft, value, span)
    // (Bytes read as the field's type: no conversion to check.)
    if tc_check_byte_flow(k, ft, value, vt, span) == .None && !coerce_deferred(k.c, vt, ft, span) && types_incompatible(ft, vt) && !value_preserving_widen(vt, ft) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_FIELD_TYPE, tc_source_desc(k, diag, vt), tc_diag_name(k, target), type_name(ft))
    }
    if is_infer(vt) { tc_literal_overflow(k, diag, ft, span) }
}

// A value written into a place its target's check built (graph_assign): built
// into a temporary where it builds in place, then written at the place's
// type.
tc_store_at :: proc(k: ^TC, value: Tree_Id, place: Operand, env: ^Type_Scope, span: Span,
                    op_tok: Token_Id = 0, target: Tree_Id = 0) -> Type {
    b := tc_building(k)
    if b == nil || place == NO_VALUE {
        if op_tok != 0 {
            t, _ := tc_compound_value(k, op_tok, target, value, env, .None)
            return t
        }
        return tc_check(k, value, env)
    }
    pt := b.g.type_[place.op] if place.op != NO_NODE else nil
    d := Dest{kind = .At, at = place, type_ = pt}
    if op_tok != 0 {
        // (The operation reads the target through the place built.)
        saved := k.compound
        k.compound = {target, place}
        vt, r := tc_compound_value(k, op_tok, target, value, env, .Into)
        k.compound = saved
        tc_store(k, 0, vt, r, d, span, settle = true)
        return vt
    }
    if tc_is_void(k, value) {
        // (`= void`: the uninitialized value written, of the place's type.)
        vt := tc_check(k, value, env)
        if b = tc_building(k); b != nil { graph_fuse_write_at(b, place, graph_fuse_void(b, pt, tree_span(k.t, value)), span) }
        return vt
    }
    vt, r := tc_expr(k, value, env, .Into, dest = d, temp = true, temp_span = span)
    tc_store(k, value, vt, r, d, span, settle = true)
    return vt
}

// "name (type)" when the expression has a name, else its type.
tc_source_desc :: proc(k: ^TC, n: Tree_Id, t: Type) -> string {
    name := tc_diag_name(k, n)
    if name == "" { return type_name(t) }
    return fmt.tprintf("%s (%s)", name, type_name(t))
}

// The param a write lands in, when its target is rooted at one passed by
// address (through no pointer).
tc_write_root_param :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> (string, bool) {
    tr := k.t
    cur := n
    for {
        #partial switch tr.tag[cur] {
        case .Paren:
            cur = Tree_Id(tr.a[cur])
        case .Field, .Index, .Slice:
            base := Tree_Id(tr.a[cur])
            if _, is_ptr := distinct_base(tc_node_type(k, base)).(^Type_Ptr); is_ptr { return "", false }
            cur = base
        case .Ident:
            name := tc_name(k, cur)
            if is_immutable_param(env, name) { return name, true }
            return "", false
        case:
            return "", false
        }
    }
}

// --- building a struct ----------------------------------------------------

// `Foo{…}`, `Foo{0}`, `{…}` (typed by its use): its construction where it goes
// (else in a temporary), then each field given stored as it is checked.
tc_literal :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                   dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    ty := Tree_Id(tr.a[n])
    entries := tree_list(tr, tr.b[n])
    name := tc_name(k, ty) if ty != 0 && tr.tag[ty] == .Ident else ""
    // Its type: written (`Foo{…}`, `[3]f32{…}`, `Vec3{…}`), or its use's.
    t: Type
    variant: string   // (a union's variant's literal: its name)
    switch {
    case ty == 0:
        hint := k.hint
        if hint == nil || (as_scope_body(distinct_base(hint)) == nil && !tc_is_fixed_array(hint)) {
            tc_unsupported(k, n, "a literal typed by its use")
            return Type_Error{}, {}
        }
        t = hint
    case tr.tag[ty] == .Ident:
        found, ok := type_env_get(env, name)
        if !ok {
            // (A union's variant: the union expected's, or the one union with it.)
            vut, ambiguous := tc_variant_union(k, name)
            if ambiguous { return Type_Error{}, {} }
            if vut == nil {
                return tc_unknown_literal(k, n, name, entries, env)
            }
            t, variant = vut, name
        } else {
            t = found
        }
    case tr.tag[ty] == .Field:
        tc_unsupported(k, n, "this literal's type")
        return Type_Error{}, {}
    case:
        // (A typed array's: `[3]f32{…}`, an empty `[..N]T{}`.)
        t = tc_type(k, ty, env, span)
        if is_partial_array(t) {
            if len(entries) > 0 {
                tc_error(k, span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(t))
                return Type_Error{}, {}
            }
            tc_unsupported(k, n, "an empty partial array's literal")
            return Type_Error{}, {}
        }
        if !tc_is_fixed_array(t) || tc_is_distinct(t) {
            tc_error(k, span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(t))
            return Type_Error{}, {}
        }
    }
    fa: ^Type_Fixed_Array
    if tc_is_fixed_array(t) { fa = distinct_base(t).(^Type_Fixed_Array) }
    ts, is_scope := t.(^Type_Scope)
    vst: ^Type_Scope
    if variant != "" { vst = k.table.structs[t.(^Type_Union).variant_structs[variant]] }
    if fa == nil && vst == nil && (!is_scope || ts.kind != .Struct || ts.is_module || ts.node == 0) {
        tc_unsupported(k, n, "a literal of no struct")
        return Type_Error{}, {}
    }
    zero := len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0"
    sd: ^Scope_Body
    if vst != nil {
        sd = &vst.sd
    } else if fa == nil {
        tc_struct_ensure(k, ts)
        sd = &ts.sd
        if !zero {
            if count_required_params(ts) > 0 {
                qualified := fmt.tprintf("%s.%s", ts.home_package, ts.source_name) if ts.home_package != "" else ts.source_name
                tc_error(k, span, TYPE_EXPECTS_ARGS, qualified, len(ts.params), fn_params_desc(ts), 0)
            } else if len(ts.return_types) > 0 {
                tc_error(k, span, TYPE_LITERAL_CAN_FAIL, ts.source_name, ts.source_name)
            }
        }
    }
    b := tc_building(k)
    build := want != .None && b != nil
    d := dest
    into_temp := temp
    in_temp := want != .Into || into_temp
    placed := want != .Into && temp_span != {}
    at := temp_span if into_temp || placed else span
    gl: ^Graph_Literal
    broadcast := fa != nil && tc_is_broadcast(k, n)
    if build {
        if in_temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
        if fa != nil {
            // (An array: zero, then each element into its slot; a broadcast,
            // its value then the fill.)
            if !broadcast { gl = graph_fuse_literal(b, span, name, zero, t, d) }
        } else if vst != nil {
            // (A variant: its construction, then its defaults the literal doesn't give.)
            gl = graph_fuse_literal(b, span, name, zero, t, d)
            if gl != nil { tc_variant_defaults(k, gl.variant, tc_literal_given(k, entries, sd), gl.parent, span) }
        } else {
            // (Its constructor's arguments — its params' defaults — then it.)
            args: []Operand
            if !zero { args = tc_ctor_args(k, ts, span) }
            if b = tc_building(k); b == nil { return t, {} }
            gl = graph_fuse_literal(b, span, name, zero, t, d, args)
        }
        if gl == nil && !broadcast { tc_fail(k, "a literal the graph builds no way") }
    }
    if fa != nil {
        tc_array_entries(k, n, entries, fa, t, name, env, gl, d, build && broadcast)
    } else if !zero {
        tc_literal_fields(k, n, entries, sd, env, gl)
    }
    b = tc_building(k)
    if !build || b == nil || (gl == nil && !broadcast) { return t, {} }
    return t, tc_built(k, want, in_temp, into_temp, d, t, at, placed)
}

tc_is_fixed_array :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Fixed_Array)
    return ok
}

tc_is_distinct :: proc(t: Type) -> bool {
    _, ok := t.(^Type_Distinct)
    return ok
}

// An array literal's entries: each element into its slot, by position or
// named by its swizzle letter (`{x = 1}`); `{all v}`, v once, then the fill.
tc_array_entries :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, fa: ^Type_Fixed_Array, lit_t: Type, name: string,
                         env: ^Type_Scope, gl: ^Graph_Literal, d: Dest, fill: bool) {
    tr := k.t
    span := tree_span(tr, n)
    elem_t := graph_elem_type(lit_t) if gl != nil else nil
    if len(entries) == 1 && tr.tag[entries[0]] == .Broadcast {
        value := Tree_Id(tr.a[entries[0]])
        if v := tc_unparen(k, value); tr.tag[v] == .Literal && tr.a[v] == 0 { k.hint = fa.elem }
        vt: Type
        if fill && tc_building(k) != nil {
            r: Fused
            vt, r = tc_expr(k, value, env)
            if b := tc_building(k); b != nil { graph_fuse_fill(b, span, lit_t, d, r.v) }
        } else {
            vt = tc_check(k, value, env)
        }
        if types_incompatible(fa.elem, vt) {
            tc_error(k, span, TYPE_BROADCAST_VALUE_TYPE_EXPECTED, name, type_name(vt), type_name(fa.elem))
            return
        }
        if is_infer(vt) { tc_literal_overflow(k, value, fa.elem, span) }
        return
    }
    if len(entries) == 0 || len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0" { return }
    hint_for :: proc(k: ^TC, value: Tree_Id, elem: Type) {
        if v := tc_unparen(k, value); k.t.tag[v] == .Literal && k.t.a[v] == 0 && !tc_is_broadcast(k, v) { k.hint = elem }
    }
    if tr.tag[entries[0]] != .Named_Entry {
        if len(entries) != fa.size {
            tc_error(k, span, TYPE_EXPECTS_POSITIONAL_VALUES, name, fa.size, len(entries))
            return
        }
        for e, i in entries {
            hint_for(k, e, fa.elem)
            vt: Type
            if gl != nil && tc_building(k) != nil {
                vt = tc_store_into(k, e, env, graph_fuse_literal_elem(gl, i, elem_t), span)
            } else {
                vt = tc_check(k, e, env)
            }
            if types_incompatible(fa.elem, vt) { tc_error(k, span, TYPE_ELEMENT_TYPE_EXPECTED, name, i, type_name(vt), type_name(fa.elem)) }
            if is_infer(vt) { tc_literal_overflow(k, e, fa.elem, span) }
        }
        return
    }
    set := make([]bool, fa.size, context.temp_allocator)
    for e in entries {
        field := tc_name(k, e)
        if len(field) != 1 || !is_swizzle_field(field, fa.size) {
            tc_error(k, span, TYPE_FIELD_USE_SWIZZLE_COMPONENTS_WITHIN, name, field, fa.size)
            continue
        }
        idx := swizzle_char_to_index(field[0])
        if set[idx] {
            tc_error(k, span, TYPE_FIELD_SET_MORE_THAN_ONCE, name, field)
            continue
        }
        value := Tree_Id(tr.a[e])
        hint_for(k, value, fa.elem)
        vt: Type
        if gl != nil && tc_building(k) != nil {
            vt = tc_store_into(k, value, env, graph_fuse_literal_elem(gl, idx, elem_t), span)
        } else {
            vt = tc_check(k, value, env)
        }
        if types_incompatible(fa.elem, vt) { tc_error(k, span, TYPE_FIELD_TYPE_EXPECTED, name, field, type_name(vt), type_name(fa.elem)) }
        if is_infer(vt) { tc_literal_overflow(k, value, fa.elem, span) }
        set[idx] = true
    }
}

// A literal's entries against its struct's fields: named, or by position.
tc_literal_fields :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, sd: ^Scope_Body, env: ^Type_Scope, gl: ^Graph_Literal) {
    tr := k.t
    span := tree_span(tr, n)
    if len(entries) == 0 { return }
    if tr.tag[entries[0]] != .Named_Entry {
        // `Foo{f()}`, f's results Foo's fields: each field its result (the
        // call built once).
        gl := gl
        probed: Type
        if call := tc_unparen(k, entries[0]); len(entries) == 1 && tc_is_call(k, call) && len(sd.fields) > 1 {
            spread: Fused
            if gl != nil {
                probed, spread = tc_expr(k, entries[0], env, .Value)
            } else {
                probed = tc_check(k, entries[0], env)
            }
            returns := tc_call_returns(k, call, env)
            fits := len(returns) == len(sd.fields)
            for f, i in sd.fields {
                if fits && types_incompatible(f.type_, returns[i]) { fits = false }
            }
            if fits {
                if b := tc_building(k); b != nil && gl != nil && !graph_fuse_spread(b, gl, span, spread.v) {
                    tc_fail(k, "a spread literal of no call")
                }
                return
            }
            if gl != nil {
                tc_fail(k, "a spread literal that doesn't match")
                gl = nil
            }
        }
        user := sd.fields[first_user_field(sd):]
        if len(entries) > len(user) {
            tc_error(k, span, TYPE_CLASS_FIELDS_POSITIONAL_VALUES, sd.name, len(user), len(entries))
        }
        for e, i in entries {
            if i >= len(user) { break }
            tc_literal_field(k, e, user[i], i, "", span, env, gl, positional = true, probed = probed if i == 0 else nil)
        }
        return
    }
    for e in entries {
        name := tc_name(k, e)
        idx, ok := sd.field_map[name]
        if !ok {
            tc_error(k, span, TYPE_CLASS_FIELD, sd.name, name)
            continue
        }
        tc_literal_field(k, Tree_Id(tr.a[e]), sd.fields[idx], 0, name, span, env, gl)
    }
}

tc_literal_field :: proc(k: ^TC, value: Tree_Id, f: Struct_Type_Field, i: int, name: string, span: Span,
                         env: ^Type_Scope, gl: ^Graph_Literal, positional := false, probed: Type = nil) {
    // (An anonymous literal takes its shape from the field.)
    if v := tc_unparen(k, value); k.t.tag[v] == .Literal && k.t.a[v] == 0 && !tc_is_broadcast(k, v) { k.hint = f.type_ }
    vt: Type
    if probed != nil {
        vt = probed   // (checked as a spread that wasn't)
    } else if gl != nil && tc_building(k) != nil {
        d := graph_fuse_literal_field(gl, name, i)
        t, r := tc_expr(k, value, env, .Into, dest = d, temp_span = span)
        tc_store(k, value, t, r, d, span)
        vt = t
    } else {
        vt = tc_check(k, value, env)
    }
    if !coerce_deferred(k.c, vt, f.type_, span) && types_incompatible(f.type_, vt) && !value_preserving_widen(vt, f.type_) {
        if positional {
            tc_error(k, span, TYPE_FIELD_POSITION_EXPECTED, f.name, i, type_name(f.type_), type_name(vt))
        } else {
            tc_error(k, span, TYPE_FIELD_EXPECTED, f.name, type_name(f.type_), type_name(vt))
        }
    }
    tc_byte_view_address(k, f.type_, value)
    if is_infer(vt) { tc_literal_overflow(k, value, f.type_, span) }
}

// `Foo(args)`: its constructor run where it goes (else in a temporary).
tc_construct :: proc(k: ^TC, n: Tree_Id, ts: ^Type_Scope, ops: []Operand, want: Fuse_Want, w: Written,
                     dest: Dest, temp: bool, temp_span: Span, made := false) -> Fused {
    b := tc_building(k)
    if b == nil { return {} }
    span := tree_span(k.t, n)
    if want == .Place {
        tc_fail(k, "a call's place")
        return {}
    }
    // (`made`: the temporary it is built in, made before its arguments.)
    at: Dest
    if want == .Into && temp && !made {
        at = graph_fuse_temp(b, temp_span, fuse_temp_type(dest))
    } else if want == .Into {
        at = dest
    } else {
        at = graph_dest_var("temp", graph_slot(b, "temp", ts, span), ts)
    }
    graph_fuse_construct(b, ts, ts, at, ops, w, span)
    switch {
    case want == .Into && temp:
        tt: Type = at.type_ if at.type_ != nil else Type(ts)
        p := graph_fuse_temp_end(b, at, tt, temp_span)
        return {v = graph_read(b, p, tt, temp_span), ok = true, temp = true}
    case want == .Into:
        return {v = NO_VALUE, ok = true, into = true}
    }
    return {v = graph_read(b, graph_dest_place(b, at, span), ts, span), ok = true}
}

// `{all v}`: a literal of one value, every slot's.
tc_is_broadcast :: proc(k: ^TC, lit: Tree_Id) -> bool {
    entries := tree_list(k.t, k.t.b[lit])
    return len(entries) == 1 && k.t.tag[entries[0]] == .Broadcast
}

// `s.len = n`, `a.xy = v`: a slice's or partial array's header field, an
// array's swizzle (through a pointer, what it points at), then the value.
tc_header_assign :: proc(k: ^TC, s, target, value: Tree_Id, bt: Type, br: Fused, field: string,
                         env: ^Type_Scope, op_tok: Token_Id) {
    span := tree_span(k.t, s)
    diag := value if op_tok == 0 else 0
    place := NO_VALUE
    if tc_building(k) != nil {
        if ft := fuse_target_field_type(bt, field); ft != nil {
            place = tc_member_place(k, target, field, br, bt, ft)
        } else {
            tc_fail(k, "a write to an unknown field")
        }
    }
    vt := tc_store_at(k, value, place, env, span, op_tok, target)
    k.hint = nil
    obj := bt
    if pt, is_ptr := obj.(^Type_Ptr); is_ptr {
        obj = pt.elem
        if dt, is_distinct := obj.(^Type_Distinct); is_distinct { obj = dt.base_type }
    }
    obj = distinct_base(obj)
    elem: Type
    #partial switch v in obj {
    case ^Type_Slice:         elem = v.elem
    case ^Type_Partial_Array: elem = v.elem
    case ^Type_Fixed_Array:
        if !is_swizzle_field(field, v.size) {
            if is_all_swizzle_chars(field) { tc_error(k, span, TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY, field, v.size) }
            return
        }
        if pname, immutable := tc_write_root_param(k, target, env); immutable {
            tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, field, pname)
        }
        if len(field) == 1 {
            tc_set_type(k, target, v.elem)
            if types_incompatible(v.elem, vt) && !is_infer(vt) {
                tc_error(k, span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPE, type_name(vt), field, type_name(v.elem))
            }
            if is_infer(vt) { tc_literal_overflow(k, diag, v.elem, span) }
            return
        }
        tc_set_type(k, target, new_clone(Type_Fixed_Array{size = len(field), elem = v.elem}))
        if va, is_array := vt.(^Type_Fixed_Array); is_array {
            if types_incompatible(v.elem, va.elem) { tc_error(k, span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPES, type_name(vt), field) }
        } else if !is_any(vt) && !is_infer(vt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_MULTI_COMPONENT_SWIZZLE, type_name(vt), field)
        }
        return
    case:
        return
    }
    // (A param's header is its caller's: `^[]T` moves a cursor.)
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, field, pname)
    }
    ft: Type
    switch field {
    case "len", "cap": ft = slice_header_width_type
    case "ptr":        ft = new_clone(Type_Ptr{elem = elem})
    case:
        tc_error(k, span, TYPE_SLICE_TYPE_FIELD, type_name(obj), field)
        return
    }
    if !coerce_deferred(k.c, vt, ft, span) && types_incompatible(ft, vt) && !is_infer(vt) && !value_preserving_widen(vt, ft) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_FIELD_TYPE, tc_source_desc(k, diag, vt), tc_diag_name(k, target), type_name(ft))
    }
    if is_infer(vt) { tc_literal_overflow(k, diag, ft, span) }
}

// `m.X`, m a module: its constant (a value of its own: the base, built, left
// out), an enum's variant it holds, or its member (a type, a fun — the base
// of a further access).
tc_module_member :: proc(k: ^TC, n: Tree_Id, sd: ^Scope_Body, field: string, bt: Type, br: Fused, mark: Graph_Mark,
                         build: bool, want: Fuse_Want, w: Written) -> (Type, Fused) {
    span := tree_span(k.t, n)
    msc := sd_module_scope(sd)
    t, found := type_env_get(msc, field)
    if !found {
        for _, mt in sd.types {
            if et, is_enum := mt.(^Type_Enum); is_enum {
                if val, has := et.variants[field]; has {
                    k.variant_nodes[n] = true
                    if b := tc_building(k); build && b != nil { graph_fuse_drop_since(b, mark) }
                    return et, tc_variant_value(k, et, val, field, span, want if build else .None, w)
                }
            } else if ut, is_union := mt.(^Type_Union); is_union {
                if _, has := ut.tag_map[field]; has {
                    tc_unsupported(k, n, "a union's variant as a value")
                    return Type_Error{}, {}
                }
            }
        }
        tc_error(k, span, TYPE_MODULE_SYMBOL, sd.name, field)
        return Type_Error{}, {}
    }
    if kc, is_const := k.consts[make_flat_name(sd.name, field)]; is_const {
        k.const_nodes[n] = true
        b := tc_building(k)
        if !build || b == nil { return t, {} }
        graph_fuse_drop_since(b, mark)
        return t, tc_const_use(k, kc, n, t, want, w)
    }
    b := tc_building(k)
    if !build || b == nil { return t, {} }
    p := tc_member_place(k, n, field, br, bt, t)
    if p == NO_VALUE { return t, {} }
    if want == .Value { return t, {v = graph_read(b, p, t, span), ok = true} }
    return t, {v = p, place = true, ok = true}
}

// The constant a write, or an address, lands in, when its target is rooted
// at one through no pointer.
tc_write_root_const :: proc(k: ^TC, n: Tree_Id) -> (string, bool) {
    tr := k.t
    cur := n
    for {
        inner: Tree_Id
        #partial switch tr.tag[cur] {
        case .Paren:
            cur = Tree_Id(tr.a[cur])
            continue
        case .Field:
            if cur in k.const_nodes { return tc_text(Token_Id(tr.b[cur])), true }
            inner = Tree_Id(tr.a[cur])
        case .Index, .Slice:
            inner = Tree_Id(tr.a[cur])
        case .Ident:
            name := tc_name(k, cur)
            return name, cur in k.const_nodes || name in k.consts
        case:
            return "", false
        }
        if _, is_ptr := distinct_base(tc_node_type(k, inner)).(^Type_Ptr); is_ptr { return "", false }
        cur = inner
    }
}

// `v{ x = 1 }` as a statement, v a variable of a struct: each field given
// written into v's, in place.
tc_override :: proc(k: ^TC, e: Tree_Id, env: ^Type_Scope) -> bool {
    tr := k.t
    if tr.tag[e] != .Literal { return false }
    ty := Tree_Id(tr.a[e])
    if ty == 0 || tr.tag[ty] != .Ident { return false }
    name := tc_name(k, ty)
    vt, _, found := type_env_locate(env, name)
    if !found { return false }
    sd := resolve_to_struct_type(k.c, vt)
    if sd == nil { return false }
    tc_set_type(k, e, vt)
    gl: ^Graph_Literal
    if b := tc_building(k); b != nil { gl = graph_fuse_override(b, graph_dest_var(name, NO_NODE, vt), sd) }
    tc_literal_fields(k, e, tree_list(tr, tr.b[e]), sd, env, gl)
    return true
}

// A literal of a name no type or union owns: a variant's two unions have
// (ambiguous: said so), else an unknown type — unless a variant's or a
// local's (what takes it checks it) — its fields' values checked.
tc_unknown_literal :: proc(k: ^TC, n: Tree_Id, name: string, entries: []Tree_Id, env: ^Type_Scope) -> (Type, Fused) {
    span := tree_span(k.t, n)
    owner, is_variant := k.table.variant_to_enum[name]
    if is_variant && owner == "" {
        // (The unions that own it: a literal builds a payload.)
        owners := make([dynamic]string, context.temp_allocator)
        for _, ut in k.table.unions {
            if name in ut.tag_map { append(&owners, ut.source_name if ut.source_name != "" else ut.name) }
        }
        slice.sort(owners[:])
        first := owners[0] if len(owners) > 0 else name
        tc_error(k, span, TYPE_AMBIGUOUS_VARIANT_LITERAL, name, strings.join(owners[:], ", ", context.temp_allocator), first, name)
        return Type_Error{}, {}
    }
    if !is_variant {
        if _, _, bound := type_env_locate(env, name); !bound { tc_error(k, span, TYPE_UNKNOWN_TYPE, name) }
    }
    for e in entries { tc_check(k, Tree_Id(k.t.a[e]) if k.t.tag[e] == .Named_Entry else e, env) }
    return Type_Error{}, {}
}
