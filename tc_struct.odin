package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// Structs in the checker: a field read or written, a struct built (a
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
tc_field :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    base := Tree_Id(tr.a[n])
    field: string
    if tr.tag[n] == .Dot_Ident {
        // (`.len` in a subscript: its base's — tc_lower_dots.)
        base, field = k.annot.dot_bases[tc_sid(k, n)], tc_text(Token_Id(tr.a[n]))
    } else {
        field = tc_text(Token_Id(tr.b[n]))
    }
    // (`pkg.X` inside pkg: its own constant — its value's type.)
    if tr.tag[base] == .Ident && k.pkg != "" && tc_name(k, base) == k.pkg {
        if kc, ok := k.consts[make_flat_name(k.pkg, field)]; ok {
            t := tc_check(k, kc.value, env)
            tc_set_ref(k, n, {k.t.main[kc.def], .Const})
            return t
        }
    }
    bt := tc_check(k, base, env)
    if sd := as_scope_body(bt); sd != nil && sd_is_module(sd) {
        return tc_module_member(k, n, sd, field)
    }
    // (A union's variant: a value of its own.)
    if ut, is_union := bt.(^Type_Union); is_union && field != "tag" && field != "pad" {
        if _, has := ut.tag_map[field]; has {
            tc_set_ref(k, n, {variant_decl(ut, field), .Variant})
            tc_variant_built(k, n, ut, field)
            return ut
        }
    }
    t, is_member, _, _ := tc_field_type(k, n, base, bt, field, span)
    tc_set_ref(k, n, tc_member_ref(k, bt, t, field, is_member))
    return t
}

// What `x.field` names, given its base's type and what tc_field_type found:
// an enum's variant, a fun its struct has, a struct's field — or what no
// source declares (a header's len, a swizzle, a union's tag).
tc_member_ref :: proc(k: ^TC, bt, t: Type, field: string, member: bool) -> Ref {
    if _, is_error := t.(Type_Error); is_error || t == nil { return {} }
    if et, is_enum := t.(^Type_Enum); is_enum && !member { return {variant_decl(et, field), .Variant} }
    if fun, is_fun := t.(^Type_Scope); is_fun && !member && fun.kind == .Fun { return {fun.decl, .Fun} }
    if member {
        if sd := tc_struct_of(k, bt); sd != nil {
            if i, ok := sd.field_map[field]; ok { return {sd.fields[i].decl, .Field} }
        }
    }
    return {kind = .Builtin}
}

// A field's type: whether it names part of the value (a member), or a
// fixed array's length (its value, else -1).
tc_field_type :: proc(k: ^TC, n, base: Tree_Id, bt: Type, field: string, span: Span) -> (t: Type, member: bool, known: i128, known_ok: bool) {
    // (An enum's variant: its value, known. A union's tag or pad: part of the
    // value; its variant: a value of its own.)
    #partial switch v in bt {
    case ^Type_Enum:
        if val, has := v.variants[field]; has { return v, false, i128(val), true }
        tc_error(k, span, TYPE_ENUM_VARIANT, type_name(v), field)
        return Type_Error{}, false, 0, false
    case ^Type_Union:
        switch field {
        case "tag":
            if tag_et, found := k.table.enums[strings.concatenate({v.name, "_Tag"})]; found { return tag_et, true, 0, false }
            tc_error(k, span, TYPE_UNION_TAG_ENUM_INTERNAL_ERROR, type_name(v))
            return Type_Error{}, false, 0, false
        case "pad":
            if v.tag_pad == nil {
                tc_error(k, span, TYPE_UNION_PADDING_DECLARE_UNION_PAD, type_name(v))
                return Type_Error{}, false, 0, false
            }
            return v.tag_pad, true, 0, false
        }
        if _, has := v.tag_map[field]; has {
            tc_unsupported(k, n, "a union's variant as a value")
            return Type_Error{}, false, 0, false
        }
        tc_error(k, span, TYPE_UNION_VARIANT, type_name(v), field)
        return Type_Error{}, false, 0, false
    }

    if sd := tc_struct_of(k, bt); sd != nil && len(sd.fields) > 0 {
        if sd_is_module(sd) {
            tc_unsupported(k, n, "a module's member")
            return Type_Error{}, false, 0, false
        }
        // (Its own field, else one a `using` field's struct has.)
        if field not_in sd.field_map {
            for f in sd.fields {
                if f.is_using {
                    tc_unsupported(k, n, "a field of a `using` field's struct")
                    return Type_Error{}, false, 0, false
                }
            }
        }
        if ft := resolve_struct_field(sd, field); ft != nil { return ft, true, 0, false }
        // (Its function: a value of its own, tc_field's to build.)
        if fun, has := sd.functions[field]; has { return fun, false, 0, false }
        tc_error(k, span, TYPE_CLASS_FIELD, scope_display_name(sd), field)
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

// `x.f = v`: the field the struct has, the value at its type.
// (`op_tok`: a compound assignment's operator — the value is `target op value`.)
tc_field_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    diag := value if op_tok == 0 else 0   // (the value, as diagnostics name it)
    tr := k.t
    span := tree_span(tr, s)
    base := Tree_Id(tr.a[target])
    field := tc_text(Token_Id(tr.b[target]))
    bt := tc_check(k, base, env)
    tc_struct_of(k, bt)   // (its fields known: a nested struct's, checked first)
    sd := as_scope_body(bt)
    if sd == nil || len(sd.fields) == 0 {
        sd = nil
        if pt, is_ptr := bt.(^Type_Ptr); is_ptr {
            if psd := as_scope_body(pt.elem); psd != nil && len(psd.fields) > 0 { sd = psd }
        }
    }
    if sd == nil {
        tc_header_assign(k, s, target, value, bt, field, env, op_tok)
        return
    }
    ft := resolve_struct_field(sd, field)
    if ft != nil {
        k.hint = ft
        tc_set_type(k, target, ft)
        if i, ok := sd.field_map[field]; ok { tc_set_ref(k, target, {sd.fields[i].decl, .Field}) }
    }
    vt := tc_store_at(k, value, env, op_tok, target, s)
    k.hint = nil
    if ft == nil {
        tc_error(k, span, TYPE_CLASS_FIELD, scope_display_name(sd), field)
        return
    }
    if pname, immutable := tc_write_root_param(k, target, env); immutable {
        tc_error(k, span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, field, pname)
    }
    tc_no_literal_slice(k, ft, value, span)
    // (Bytes read as the field's type: no conversion to check.)
    flow := tc_check_byte_flow(k, ft, value, vt, span)
    if flow == .Read && is_byte_buffer(vt) { tc_span_read_size(k, value, ft, true, span) }
    if flow == .None && !coerce_deferred(k.c, vt, ft, span) && types_incompatible(ft, vt) && !value_preserving_widen(vt, ft) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_FIELD_TYPE, tc_source_desc(k, diag, vt), tc_diag_name(k, target), type_name(ft))
    }
    tc_value_at(k, diag, vt, ft, span)
}

// A value written into a place a target names: its type — a compound
// assignment's, its operation's.
tc_store_at :: proc(k: ^TC, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0, target: Tree_Id = 0, s: Tree_Id = 0) -> Type {
    if op_tok != 0 { return tc_compound_value(k, s, op_tok, target, value, env) }
    return tc_check(k, value, env)
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

// --- a struct's literal ---------------------------------------------------

// `Foo{…}`, `Foo{0}`, `{…}` (typed by its use): its type, what it constructs
// (its constructor's defaults, a variant's), each field given checked at its
// field's type.
tc_literal :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    ty := Tree_Id(tr.a[n])
    entries := tree_list(tr, tr.b[n])
    // (`all v`, bare: an anonymous `{all v}`.)
    if tr.tag[n] == .Broadcast { ty, entries = 0, slice.clone([]Tree_Id{n}, context.temp_allocator) }
    name := tc_name(k, ty) if ty != 0 && tr.tag[ty] == .Ident else ""
    // Its type: written (`Foo{…}`, `[3]f32{…}`, `Vec3{…}`), or its use's.
    t: Type
    variant: string   // (a union's variant's literal: its name)
    // (A struct field's `all v`: its field's type, an array — fixed or
    // partial; said at the struct when it is none.)
    fd: ^TC_Field_Default
    if ty == 0 && n == k.field_default.value && tc_is_broadcast(k, n) { fd = &k.field_default }
    empty := false   // (`[..N]T{}`: its zero — len 0, where it goes)
    switch {
    case fd != nil:
        #partial switch _ in distinct_base(fd.t) {
        case ^Type_Fixed_Array, ^Type_Partial_Array:
            t = fd.t
        case:
            tc_error(k, fd.span, TYPE_BROADCAST_LITERAL_ALL_FIELD_REQUIRES, fd.name, type_name(fd.t))
            return Type_Error{}
        }
    case ty == 0:
        hint := k.hint
        if ut, is_union := distinct_base(hint).(^Type_Union); is_union {
            tc_error(k, span, TYPE_UNION_REQUIRES_NAMED_VARIANT_VARIANT, type_name(ut))
            return Type_Error{}
        }
        if hint == nil || (as_scope_body(distinct_base(hint)) == nil && !tc_is_fixed_array(hint)) {
            tc_unsupported(k, n, "a literal typed by its use")
            return Type_Error{}
        }
        t = hint
    case tr.tag[ty] == .Ident:
        found, ok := scope_lookup(env, name)
        if !ok {
            // (A union's variant: the union expected's, or the one union with it.)
            vut, ambiguous := tc_variant_union(k, name)
            if ambiguous { return Type_Error{} }
            if vut == nil {
                return tc_unknown_literal(k, n, name, entries, env)
            }
            t, variant = vut, name
        } else if ts, is_scope := found.(^Type_Scope); is_scope && ts.kind == .Struct && ts.name != name && !strings.has_suffix(ts.name, strings.concatenate({"_", name}, context.temp_allocator)) {
            // (A struct's variable, not its type: `new := var{…}`.)
            tc_error(k, span, TYPE_STRUCT_COPY_FORM, name, name, name)
            return Type_Error{}
        } else {
            t = found
        }
    case tr.tag[ty] == .Field:
        // (`Outer.Inner{…}`, `mod.T{…}`, `Union.Variant{…}` — the variant's
        // struct: as a type is named.)
        parts := make([dynamic]Token_Id, context.temp_allocator)
        if !tc_name_parts(k, ty, &parts) {
            tc_unsupported(k, n, "this literal's type")
            return Type_Error{}
        }
        dotted := tc_dotted(parts[:])
        qt := tc_qualified_type(k, parts[:], env)
        if qt == nil { tc_error(k, span, TYPE_UNKNOWN_TYPE, dotted) }
        if as_scope_body(qt) == nil {
            tc_error(k, span, TYPE_STRUCT_LITERAL_NAME_NOT_STRUCT, dotted, dotted)
            return Type_Error{}
        }
        t = qt
    case:
        // (A typed array's: `[3]f32{…}`, an empty `[..N]T{}`.)
        t = tc_type(k, ty, env, span)
        if is_partial_array(t) {
            if len(entries) > 0 {
                tc_error(k, span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(t))
                return Type_Error{}
            }
            empty = true
        } else if !tc_is_fixed_array(t) || tc_is_distinct(t) {
            tc_error(k, span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(t))
            return Type_Error{}
        }
    }
    // (The type it is written with, a name — `Foo`, `mod.T`, a variant's:
    // what it names.)
    if ty != 0 && (tr.tag[ty] == .Ident || tr.tag[ty] == .Field) {
        tc_set_type(k, ty, t)
        switch {
        case variant != "":
            tc_set_ref(k, ty, {variant_decl(t, variant), .Variant})
        case tr.tag[ty] == .Ident:
            tc_set_ref(k, ty, scope_find_ref(env, name))
        case:
            vs, is_variant := t.(^Type_Scope)
            tc_set_ref(k, ty, {type_decl(t), .Variant if is_variant && vs.is_union_variant else .Type})
        }
    }
    fa: ^Type_Fixed_Array
    if tc_is_fixed_array(t) { fa = distinct_base(t).(^Type_Fixed_Array) }
    ts, is_scope := t.(^Type_Scope)
    vst: ^Type_Scope
    if variant != "" { vst = t.(^Type_Union).variant_structs[variant] }
    if fa == nil && vst == nil && fd == nil && !empty && (!is_scope || ts.kind != .Struct || ts.is_module || ts.node == 0 && !ts.is_union_variant) {
        tc_unsupported(k, n, "a literal of no struct")
        return Type_Error{}
    }
    zero := len(entries) == 1 && tr.tag[entries[0]] == .Number && tc_text(tr.main[entries[0]]) == "0"
    sd: ^Scope_Body
    if vst != nil {
        sd = &vst.sd
    } else if fa == nil && fd == nil && !empty {
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
    // (Its construction: a struct's — `{0}` is its zero.)
    if lt, is_scope := t.(^Type_Scope); is_scope && lt.kind == .Struct && !lt.is_module && !zero {
        tc_set_callee(k, n, lt)
        tc_set_args(k, n, tc_default_args(lt))
    }
    if fa == nil && fd == nil && !empty {
        // (What its construction runs: its constructor's defaults. A
        // variant's are its body's, checked with it.)
        if vst == nil && !zero { tc_ctor_args(k, ts, span) }
        if vst != nil { tc_variant_built(k, n, t, variant) }
    }
    if fd != nil {
        tc_broadcast_fill(k, n, Tree_Id(tr.a[entries[0]]), t, name, env, fd)
    } else if fa != nil {
        tc_array_entries(k, n, entries, fa, t, name, env)
    } else if !zero && !empty {
        tc_literal_fields(k, n, entries, sd, env)
    }
    return t
}

// A dotted name's parts (`a.b.c`): false when it is no plain name's.
tc_name_parts :: proc(k: ^TC, n: Tree_Id, parts: ^[dynamic]Token_Id) -> bool {
    t := k.t
    #partial switch t.tag[n] {
    case .Ident:
        append(parts, t.main[n])
        return true
    case .Field:
        if !tc_name_parts(k, Tree_Id(t.a[n]), parts) { return false }
        append(parts, Token_Id(t.b[n]))
        return true
    }
    return false
}

// A struct field whose value is being checked (its `all v` is its own).
TC_Field_Default :: struct {
    value: Tree_Id,
    name:  string,
    t:     Type,
    span:  Span,   // (its struct's: where its broadcast's failures are said)
}

// `all v` into an array (`lit_t`): v checked against its element. (A struct
// field's, `fd`: said as the field's.)
tc_broadcast_fill :: proc(k: ^TC, n, value: Tree_Id, lit_t: Type, name: string, env: ^Type_Scope, fd: ^TC_Field_Default = nil) {
    span := tree_span(k.t, n)
    elem: Type
    #partial switch v in distinct_base(lit_t) {
    case ^Type_Fixed_Array:   elem = v.elem
    case ^Type_Partial_Array: elem = v.elem
    }
    if v := tc_unparen(k, value); k.t.tag[v] == .Literal && k.t.a[v] == 0 { k.hint = elem }
    vt := tc_check(k, value, env)
    if fd != nil {
        if !is_any(vt) && types_incompatible(elem, vt) {
            tc_error(k, fd.span, TYPE_BROADCAST_VALUE_FIELD_TYPE_EXPECTED, fd.name, type_name(vt), type_name(elem), type_name(lit_t))
            return
        }
        tc_value_at(k, value, vt, elem, fd.span)
        return
    }
    if types_incompatible(elem, vt) {
        tc_error(k, span, TYPE_BROADCAST_VALUE_TYPE_EXPECTED, name, type_name(vt), type_name(elem))
        return
    }
    tc_value_at(k, value, vt, elem, span)
}

tc_is_fixed_array :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Fixed_Array)
    return ok
}

tc_is_distinct :: proc(t: Type) -> bool {
    _, ok := t.(^Type_Distinct)
    return ok
}

// An array literal's entries: each element against its slot, by position or
// named by its swizzle letter (`{x = 1}`); `{all v}`, v once.
tc_array_entries :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, fa: ^Type_Fixed_Array, lit_t: Type, name: string, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, n)
    if len(entries) == 1 && tr.tag[entries[0]] == .Broadcast {
        tc_broadcast_fill(k, n, Tree_Id(tr.a[entries[0]]), lit_t, name, env)
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
            vt := tc_check(k, e, env)
            if types_incompatible(fa.elem, vt) { tc_error(k, span, TYPE_ELEMENT_TYPE_EXPECTED, name, i, type_name(vt), type_name(fa.elem)) }
            tc_value_at(k, e, vt, fa.elem, span)
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
        vt := tc_check(k, value, env)
        if types_incompatible(fa.elem, vt) { tc_error(k, span, TYPE_FIELD_TYPE_EXPECTED, name, field, type_name(vt), type_name(fa.elem)) }
        tc_value_at(k, value, vt, fa.elem, span)
        set[idx] = true
    }
}

// A literal's entries against its struct's fields: named, or by position.
tc_literal_fields :: proc(k: ^TC, n: Tree_Id, entries: []Tree_Id, sd: ^Scope_Body, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, n)
    if len(entries) == 0 { return }
    if tr.tag[entries[0]] != .Named_Entry {
        // `Foo{f()}`, f's results Foo's fields: each field its result.
        probed: Type
        if call := tc_unparen(k, entries[0]); len(entries) == 1 && tc_is_call(k, call) && len(sd.fields) > 1 {
            probed = tc_check(k, entries[0], env)
            returns := tc_call_returns(k, call, env)
            fits := len(returns) == len(sd.fields)
            for f, i in sd.fields {
                if fits && types_incompatible(f.type_, returns[i]) { fits = false }
            }
            if fits { return }
        }
        user := sd.fields[first_user_field(sd):]
        if len(entries) > len(user) {
            tc_error(k, span, TYPE_CLASS_FIELDS_POSITIONAL_VALUES, scope_display_name(sd), len(user), len(entries))
        }
        for e, i in entries {
            if i >= len(user) { break }
            tc_literal_field(k, e, user[i], i, "", span, env, positional = true, probed = probed if i == 0 else nil)
        }
        return
    }
    for e in entries {
        name := tc_name(k, e)
        idx, ok := sd.field_map[name]
        if !ok {
            tc_error(k, span, TYPE_CLASS_FIELD, scope_display_name(sd), name)
            continue
        }
        tc_literal_field(k, Tree_Id(tr.a[e]), sd.fields[idx], 0, name, span, env)
    }
}

tc_literal_field :: proc(k: ^TC, value: Tree_Id, f: Struct_Type_Field, i: int, name: string, span: Span,
                         env: ^Type_Scope, positional := false, probed: Type = nil) {
    // (An anonymous literal takes its shape from the field.)
    if v := tc_unparen(k, value); k.t.tag[v] == .Literal && k.t.a[v] == 0 && !tc_is_broadcast(k, v) { k.hint = f.type_ }
    vt := probed if probed != nil else tc_check(k, value, env)   // (a spread that wasn't: checked as one)
    if !coerce_deferred(k.c, vt, f.type_, span) && types_incompatible(f.type_, vt) && !value_preserving_widen(vt, f.type_) {
        if positional {
            tc_error(k, span, TYPE_FIELD_POSITION_EXPECTED, f.name, i, type_name(f.type_), type_name(vt))
        } else {
            tc_error(k, span, TYPE_FIELD_EXPECTED, f.name, type_name(f.type_), type_name(vt))
        }
    }
    tc_value_at(k, value, vt, f.type_, span)
}

// `{all v}`: a literal of one value, every slot's.
tc_is_broadcast :: proc(k: ^TC, lit: Tree_Id) -> bool {
    if k.t.tag[lit] == .Broadcast { return true }
    entries := tree_list(k.t, k.t.b[lit])
    return len(entries) == 1 && k.t.tag[entries[0]] == .Broadcast
}

// `s.len = n`, `a.xy = v`: a slice's or partial array's header field, an
// array's swizzle (through a pointer, what it points at), then the value.
tc_header_assign :: proc(k: ^TC, s, target, value: Tree_Id, bt: Type, field: string, env: ^Type_Scope, op_tok: Token_Id) {
    span := tree_span(k.t, s)
    diag := value if op_tok == 0 else 0
    vt := tc_store_at(k, value, env, op_tok, target, s)
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
            tc_set_ref(k, target, {kind = .Builtin})
            if types_incompatible(v.elem, vt) && !is_infer(vt) {
                tc_error(k, span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPE, type_name(vt), field, type_name(v.elem))
            }
            tc_value_at(k, diag, vt, v.elem, span)
            return
        }
        tc_set_type(k, target, new_clone(Type_Fixed_Array{size = len(field), elem = v.elem}))
        tc_set_ref(k, target, {kind = .Builtin})
        tc_settle(k, diag, tc_node_type(k, target))
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
    tc_value_at(k, diag, vt, ft, span)
}

// `m.X`, m a module: its constant, an enum's variant it holds, or its member
// (a type, a fun — the base of a further access).
tc_module_member :: proc(k: ^TC, n: Tree_Id, sd: ^Scope_Body, field: string) -> Type {
    span := tree_span(k.t, n)
    msc := sd_module_scope(sd)
    t, found := scope_lookup(msc, field)
    if !found {
        for _, mt in sd.types {
            if et, is_enum := mt.(^Type_Enum); is_enum {
                if _, has := et.variants[field]; has {
                    tc_set_ref(k, n, {variant_decl(et, field), .Variant})
                    return et
                }
            } else if ut, is_union := mt.(^Type_Union); is_union {
                if _, has := ut.tag_map[field]; has {
                    tc_unsupported(k, n, "a union's variant as a value")
                    return Type_Error{}
                }
            }
        }
        tc_error(k, span, TYPE_MODULE_SYMBOL, scope_display_name(sd), field)
        return Type_Error{}
    }
    tc_set_ref(k, n, scope_find_ref(msc, field))
    if kc, is_const := k.consts[make_flat_name(sd.name, field)]; is_const { tc_set_ref(k, n, {k.t.main[kc.def], .Const}) }
    return t
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
            if tc_ref(k, cur).kind == .Const { return tc_text(Token_Id(tr.b[cur])), true }
            inner = Tree_Id(tr.a[cur])
        case .Index, .Slice:
            inner = Tree_Id(tr.a[cur])
        case .Ident:
            name := tc_name(k, cur)
            return name, tc_ref(k, cur).kind == .Const || name in k.consts
        case:
            return "", false
        }
        if _, is_ptr := distinct_base(tc_node_type(k, inner)).(^Type_Ptr); is_ptr { return "", false }
        cur = inner
    }
}

// `v{ x = 1 }` as a statement, v a variable of a struct or a pointer to one:
// each field given written into v's — or what it points at's — in place
// (marked: Annotations.overrides).
tc_override :: proc(k: ^TC, e: Tree_Id, env: ^Type_Scope) -> bool {
    tr := k.t
    if tr.tag[e] != .Literal { return false }
    ty := Tree_Id(tr.a[e])
    if ty == 0 || tr.tag[ty] != .Ident { return false }
    name := tc_name(k, ty)
    vt, _, found := scope_find(env, name)
    if !found { return false }
    sd := resolve_to_struct_type(k.c, vt)
    if sd == nil { return false }
    tc_set_type(k, e, vt)
    k.annot.overrides[tc_sid(k, e)] = true
    tc_set_type(k, ty, vt)   // (the variable it writes into, named)
    tc_set_ref(k, ty, scope_find_ref(env, name))
    // (Into storage that can't be written, as a field's write: tc_field_assign.)
    span := tree_span(tr, e)
    if pname, immutable := tc_write_root_param(k, ty, env); immutable { tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, pname) }
    if cname, is_const := tc_write_root_const(k, ty); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
    if tc_in_program(k, ty) { tc_error(k, span, TYPE_PROGRAM_READ_ONLY, "write into", "") }
    tc_literal_fields(k, e, tree_list(tr, tr.b[e]), sd, env)
    return true
}

// A literal of a name no type or union owns: a variant's two unions have
// (ambiguous: said so), else an unknown type — unless a variant's or a
// local's (what takes it checks it) — its fields' values checked.
tc_unknown_literal :: proc(k: ^TC, n: Tree_Id, name: string, entries: []Tree_Id, env: ^Type_Scope) -> Type {
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
        return Type_Error{}
    }
    if !is_variant {
        if _, _, bound := scope_find(env, name); !bound { tc_error(k, span, TYPE_UNKNOWN_TYPE, name) }
    }
    for e in entries { tc_check(k, Tree_Id(k.t.a[e]) if k.t.tag[e] == .Named_Entry else e, env) }
    return Type_Error{}
}
