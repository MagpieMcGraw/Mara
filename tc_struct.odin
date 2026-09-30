package mara

import "core:fmt"

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
tc_field :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    base := Tree_Id(tr.a[n])
    field := tc_text(Token_Id(tr.b[n]))
    build := want != .None && tc_building(k) != nil
    ask := Fuse_Want.None
    if build { ask = .Place if tc_holds(k, base) || tr.tag[tc_unparen(k, base)] == .Call else .Either }
    bt, br := tc_expr(k, base, env, ask, w, temp_span = span)
    t, is_member, const_len := tc_field_type(k, n, bt, field, span)
    if !build || tc_building(k) == nil { return t, {} }
    if const_len >= 0 {
        // (A fixed array's length: its size; its base, built, stays.)
        if want == .Place { return t, {} }
        return t, {v = graph_const(tc_building(k), w, span, t, field, Const_Value{int = i128(const_len)}), ok = true}
    }
    if !is_member { return t, {} }
    p := tc_member_place(k, n, br, bt, t)
    if p == NO_VALUE { return t, {} }
    if want == .Value { return t, {v = graph_read(tc_building(k), p, t, span), ok = true} }
    return t, {v = p, place = true, ok = true}
}

// A field's type: whether it names part of the value (a member), or a
// fixed array's length (its value, else -1).
tc_field_type :: proc(k: ^TC, n: Tree_Id, bt: Type, field: string, span: Span) -> (t: Type, member: bool, const_len: int) {
    const_len = -1
    if sd := tc_struct_of(k, bt); sd != nil && len(sd.fields) > 0 {
        if sd_is_module(sd) {
            tc_unsupported(k, n, "a module's member")
            return Type_Error{}, false, -1
        }
        for f in sd.fields {
            if f.is_using {
                tc_unsupported(k, n, "a field of a `using` field's struct")
                return Type_Error{}, false, -1
            }
        }
        if ft := resolve_struct_field(sd, field, k.table); ft != nil { return ft, true, -1 }
        if sd.functions != nil && field in sd.functions {
            tc_unsupported(k, n, "a struct's function as a value")
            return Type_Error{}, false, -1
        }
        tc_error(k, span, TYPE_CLASS_FIELD, sd.name, field)
        return Type_Error{}, false, -1
    }
    obj := bt
    if pt, is_ptr := obj.(^Type_Ptr); is_ptr { obj = pt.elem }
    obj = distinct_base(obj)
    #partial switch v in obj {
    case ^Type_Enum, ^Type_Union:
        tc_unsupported(k, n, "a variant or tag")
        return Type_Error{}, false, -1
    case ^Type_Fixed_Array:
        if field == "len" || field == "cap" { return Type_Numeric{kind = .Signed, bits = 64}, false, v.size }
        if is_swizzle_field(field, v.size) {
            if len(field) == 1 { return v.elem, true, -1 }
            return new_clone(Type_Fixed_Array{size = len(field), elem = v.elem}), true, -1
        }
        if is_all_swizzle_chars(field) {
            tc_error(k, span, TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY, field, v.size)
        } else {
            tc_error(k, span, TYPE_CANNOT_ACCESS_FIELD_ARRAY_TYPE, field, type_name(obj))
        }
        return Type_Error{}, false, -1
    case ^Type_Slice:
        switch field {
        case "ptr":        return new_clone(Type_Ptr{elem = v.elem}), true, -1
        case "len", "cap": return slice_header_width_type, true, -1
        }
        tc_error(k, span, TYPE_SLICE_TYPE_FIELD, type_name(obj), field)
        return Type_Error{}, false, -1
    case ^Type_Partial_Array:
        switch field {
        case "ptr":        return new_clone(Type_Ptr{elem = v.elem}), true, -1
        case "len", "cap": return slice_header_width_type, true, -1
        }
        tc_error(k, span, TYPE_PARTIAL_ARRAY_TYPE_FIELD, type_name(obj), field)
        return Type_Error{}, false, -1
    }
    if !is_any(bt) { tc_error(k, span, TYPE_CANNOT_ACCESS_FIELD_TYPE, field, type_name(bt)) }
    return Type_Error{}, false, -1
}

// A member's place: its base's (through a pointer, what it points at), then
// the field — or an array's swizzle.
tc_member_place :: proc(k: ^TC, n: Tree_Id, base: Fused, bt: Type, t: Type) -> Operand {
    b := tc_building(k)
    if b == nil { return NO_VALUE }
    if !base.ok || !base.place {
        tc_fail(k, "a field of a value")
        return NO_VALUE
    }
    span := tree_span(k.t, n)
    p := base.v
    if pt, is_ptr := distinct_base(bt).(^Type_Ptr); is_ptr {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)
    }
    _, is_array := distinct_base(graph_pointee(bt)).(^Type_Fixed_Array)
    return graph_op_value(b, .Swizzle if is_array else .Field, .Explicit, span, t, tc_text(Token_Id(k.t.b[n])), p)
}

// `x.f = v`: the field's place, then the value into it.
tc_field_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, s)
    base := Tree_Id(tr.a[target])
    field := tc_text(Token_Id(tr.b[target]))
    b := tc_building(k)
    bt, br := tc_expr(k, base, env, .Either if b != nil else .None)
    sd := as_scope_body(bt)
    if sd == nil || len(sd.fields) == 0 {
        sd = nil
        if pt, is_ptr := bt.(^Type_Ptr); is_ptr {
            if psd := as_scope_body(pt.elem); psd != nil && len(psd.fields) > 0 { sd = psd }
        }
    }
    if sd == nil {
        tc_unsupported(k, target, "a write to a header or swizzle")
        return
    }
    ft := resolve_struct_field(sd, field, k.table)
    place := NO_VALUE
    if ft != nil {
        k.hint = ft
        tc_set_type(k, target, ft)
        if tc_building(k) != nil { place = tc_member_place(k, target, br, bt, ft) }
    } else if tc_building(k) != nil {
        tc_fail(k, "a write to an unknown field")
    }
    vt := tc_store_at(k, value, place, env, span)
    k.hint = nil
    if ft == nil {
        tc_error(k, span, TYPE_CLASS_FIELD, sd.name, field)
        return
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, field, pname)
    }
    if !coerce_deferred(k.c, vt, ft, span) && types_incompatible(ft, vt) && !value_preserving_widen(vt, ft) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_FIELD_TYPE, tc_source_desc(k, value, vt), tc_diag_name(k, target), type_name(ft))
    }
    if is_infer(vt) { tc_literal_overflow(k, value, ft, span) }
}

// A value written into a place its target's check built (graph_assign): built
// into a temporary where it builds in place, then written at the place's
// type.
tc_store_at :: proc(k: ^TC, value: Tree_Id, place: Operand, env: ^Type_Scope, span: Span) -> Type {
    b := tc_building(k)
    if b == nil || place == NO_VALUE { return tc_check(k, value, env) }
    if t := k.t.tag[tc_unparen(k, value)]; t == .Ident && tc_name(k, tc_unparen(k, value)) == "void" {
        tc_unsupported(k, value, "a `void` write")
        return Type_Error{}
    }
    pt := b.g.type_[place.op] if place.op != NO_NODE else nil
    d := Dest{kind = .At, at = place, type_ = pt}
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
    t: Type
    switch {
    case ty == 0:
        if k.hint == nil || as_scope_body(distinct_base(k.hint)) == nil {
            tc_unsupported(k, n, "a literal typed by its use")
            return Type_Error{}, {}
        }
        t = k.hint
    case tr.tag[ty] == .Ident:
        name := tc_name(k, ty)
        found, ok := type_env_get(env, name)
        if !ok {
            tc_unsupported(k, n, "a literal of an unknown name")
            return Type_Error{}, {}
        }
        t = found
    case:
        tc_unsupported(k, n, "this literal's type")
        return Type_Error{}, {}
    }
    ts, is_scope := t.(^Type_Scope)
    if !is_scope || ts.kind != .Struct || ts.is_module || ts.node == 0 {
        tc_unsupported(k, n, "a literal of no struct")
        return Type_Error{}, {}
    }
    tc_struct_ensure(k, ts)
    sd := &ts.sd
    zero := len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0"
    if !zero {
        if count_required_params(ts) > 0 {
            qualified := fmt.tprintf("%s.%s", ts.home_package, ts.source_name) if ts.home_package != "" else ts.source_name
            tc_error(k, span, TYPE_EXPECTS_ARGS, qualified, len(ts.params), fn_params_desc(ts), 0)
        } else if len(ts.return_types) > 0 {
            tc_error(k, span, TYPE_LITERAL_CAN_FAIL, ts.source_name, ts.source_name)
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
    if build {
        if in_temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
        if len(ts.params) > 0 && !zero {
            tc_unsupported(k, n, "a literal of a struct with params")
            return t, {}
        }
        gl = graph_fuse_literal(b, span, tc_name(k, ty) if ty != 0 else "", zero, t, d, nil)
        if gl == nil { tc_fail(k, "a literal the graph builds no way") }
    }
    if !zero { tc_literal_fields(k, n, entries, sd, env, gl) }
    b = tc_building(k)
    if !build || b == nil || gl == nil { return t, {} }
    return t, tc_built(k, want, in_temp, into_temp, d, t, at, placed)
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
        if call := tc_unparen(k, entries[0]); len(entries) == 1 && tr.tag[call] == .Call && len(sd.fields) > 1 {
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
