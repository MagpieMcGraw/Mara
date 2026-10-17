package mara

import "core:strings"

// Types as written (the flat tree's type nodes), resolved: a keyword to its
// primitive, a name through the scope and the table, a pointer, an array.
// Each type node keeps the type it resolved to, and a name what it names.

tc_type :: proc(k: ^TC, n: Tree_Id, span: Span) -> Type {
    ty := tc_type_impl(k, n, span)
    if n == 0 { return ty }
    tc_set_type(k, n, ty)
    #partial switch k.t.tag[n] {
    case .Type_Keyword:
        tc_set_ref(k, n, {kind = .Builtin})
    case .Type_Name, .Type_Generic, .Type_Of:
        tc_set_ref(k, n, tc_type_ref(k, n, ty))
    }
    return ty
}

// What a type's name names: the type param it is, in an instance; else the
// type's declaration (a fun's, for `fn name`); else — a builtin type, the
// compiler's own — no source's.
tc_type_ref :: proc(k: ^TC, n: Tree_Id, ty: Type) -> Ref {
    t := k.t
    if _, is_error := ty.(Type_Error); is_error || ty == nil { return {} }
    if t.tag[n] == .Type_Name {
        parts := tree_token_list(t, t.a[n])
        if len(parts) == 1 {
            name := tc_text(parts[0])
            if _, is_primitive := tc_primitive_named(name); is_primitive { return {kind = .Builtin} }
            if ref := k.rs.refs[n]; ref.kind == .Type && k.rs.type_params[ref.decl] && k.salt != 0 { return ref }
        }
    }
    if decl := type_decl(ty); decl != 0 {
        if fun, is_scope := ty.(^Type_Scope); is_scope && fun.kind == .Fun { return {decl, .Fun} }
        return {decl, .Type}
    }
    return {kind = .Builtin}
}

tc_type_impl :: proc(k: ^TC, n: Tree_Id, span: Span) -> Type {
    if n == 0 { return Type_Any{} }
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Keyword:
        return tc_primitive(k, tc_name(k, n), span)
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        // (None: a type missing where one was due — the parser said so; only
        // mara lsp checks on past it.)
        if len(parts) == 0 { return Type_Error{} }
        if len(parts) > 1 {
            if qt := tc_qualified_type(k, n, parts); qt != nil { return qt }
            tc_error(k, span, TYPE_UNKNOWN_TYPE, tc_dotted(parts))
            return Type_Error{}
        }
        return tc_type_named(k, tc_text(parts[0]), span, n)
    case .Type_Dollar:
        if bound, is_param := tc_ref_type(k, k.rs.refs[n], ""); is_param && bound != nil { return bound }
        tc_unsupported(k, n, "a type param outside its instance")
        return Type_Error{}
    case .Ident, .Field:
        // (A name by itself, `A :: B`'s B: the type it names — annotated so,
        // `m.B`'s m its module.)
        name := tc_name(k, n) if t.tag[n] == .Ident else ""
        tc_set_ref(k, n, k.rs.refs[n])
        if base := Tree_Id(t.a[n]); t.tag[n] == .Field && t.tag[base] == .Ident { tc_set_ref(k, base, k.rs.refs[base]) }
        if ty, ok := tc_ref_type(k, k.rs.refs[n], name); ok && ty != nil { return ty }
        tc_error(k, span, TYPE_UNKNOWN_TYPE, tc_written(k, n))
        return Type_Error{}
    case .Type_Fun:
        // (A fun's type: its params' and results' types.)
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in tree_list(t, t.a[n]) { append(&ft.params, Struct_Type_Field{type_ = tc_type(k, p, span)}) }
        for r in tree_list(t, t.b[n]) { append(&ft.return_types, tc_type(k, r, span)) }
        return ft
    case .Type_Generic:
        return tc_generic_type(k, n, span)
    case .Type_Tilde:
        // (A shape is a struct param's: tc_struct_generics.)
        name := tc_text(Token_Id(t.a[n]))
        tc_error(k, span, TYPE_ONLY_VALID_TYPE_GENERIC_PARAMETER, name, name)
        return Type_Error{}
    case .Type_Of:
        return tc_fun_type_of(k, n, span)
    case .Type_Pointer:
        return type_ptr(tc_type(k, Tree_Id(t.a[n]), span))
    case .Type_Paren:
        return tc_type(k, Tree_Id(t.a[n]), span)
    case .Type_Slice:
        // (`[:n]T`: n of T, a take's count — `slice([:n]T, s)`; the type []T.)
        return type_slice(tc_type(k, Tree_Id(t.b[n]), span))
    case .Type_Partial:
        elem := tc_type(k, Tree_Id(t.b[n]), span)
        size, ok := tc_type_size(k, Tree_Id(t.a[n]), elem, span)
        if !ok { return Type_Error{} }
        return type_partial_array(size, elem)
    case .Type_Array:
        r := tree_rec(t, t.a[n], 3)
        elem := tc_type(k, Tree_Id(t.b[n]), span)
        index_type: Type
        if r[1] != 0 { index_type = tc_type(k, Tree_Id(r[1]), span) }
        // (`[K]T`: K an enum — one T for each of its values, the highest
        // value + 1 of them, indexed by K.)
        if r[1] == 0 {
            if et, slots := tc_enum_slots(k, Tree_Id(r[0])); et != nil { return type_fixed_array(slots, elem, et) }
            // (A size by a constant's name, `[MAX]T`: exactly MAX, written
            // `[MAX!]T` — the parser said so of any other size.)
            if r[2] == 0 && t.tag[r[0]] == .Ident { tc_error(k, tree_span(t, n), TYPE_FIXED_ARRAY_BANG) }
        }
        size, ok := tc_type_size(k, Tree_Id(r[0]), elem, span)
        if !ok { return Type_Error{} }
        return type_fixed_array(size, elem, index_type)
    }
    tc_unsupported(k, n, "this type")
    return Type_Error{}
}

tc_primitive :: proc(k: ^TC, name: string, span: Span) -> Type {
    switch name {
    case "int":
        tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64)
        return Type_Error{}
    case "uint":
        tc_error(k, span, TYPE_TYPE_UINT_RESERVED_USE_U64)
        return Type_Error{}
    case "cstring":
        // (C's boundary type: a foreign signature's alone.)
        if !k.c.in_foreign_sig {
            tc_error(k, span, TYPE_CSTRING_FOREIGN_ONLY)
            return Type_Error{}
        }
    }
    if p, ok := tc_primitive_named(name); ok { return p }
    return Type_Error{}
}

// A primitive type's name: its type.
tc_primitive_named :: proc(name: string) -> (Type, bool) {
    switch name {
    case "int", "uint": return Type_Error{}, true
    case "f64":     return Type_F64{}, true
    case "bool":    return Type_Bool{}, true
    case "utf8":    return Type_Utf8{}, true
    case "byte":    return Type_Byte{}, true
    case "void":    return Type_Void{}, true
    case "err":     return Type_Err{}, true
    case "cstring": return Type_CString{}, true
    case "i8":      return Type_Numeric{kind = .Signed,   bits = 8}, true
    case "i16":     return Type_Numeric{kind = .Signed,   bits = 16}, true
    case "i32":     return Type_Numeric{kind = .Signed,   bits = 32}, true
    case "i64":     return Type_Numeric{kind = .Signed,   bits = 64}, true
    case "i128":    return Type_Numeric{kind = .Signed,   bits = 128}, true
    case "u8":      return Type_Numeric{kind = .Unsigned, bits = 8}, true
    case "u16":     return Type_Numeric{kind = .Unsigned, bits = 16}, true
    case "u32":     return Type_Numeric{kind = .Unsigned, bits = 32}, true
    case "u64":     return Type_Numeric{kind = .Unsigned, bits = 64}, true
    case "u128":    return Type_Numeric{kind = .Unsigned, bits = 128}, true
    case "f16":     return Type_Numeric{kind = .Float,    bits = 16}, true
    case "f32":     return Type_Numeric{kind = .Float,    bits = 32}, true
    case "usize":   return Type_Numeric{kind = .Unsigned, bits = 0}, true
    case "isize":   return Type_Numeric{kind = .Signed,   bits = 0}, true
    }
    return nil, false
}

// An array's size, known when the program is compiled: a number, a
// constant, or an expression of them.
// An array's size written as an enum's name (a union of plain variants, a
// type param bound to one): the enum, and the slots an array indexed by it
// needs — its highest value + 1 (a value given, `Blue = 5`, counts as
// itself). Nil when the name isn't one.
tc_enum_slots :: proc(k: ^TC, n: Tree_Id) -> (Type, int) {
    t := k.t
    if n == 0 || t.tag[n] != .Ident || k.rs.refs[n].kind != .Type { return nil, 0 }
    ty, ok := tc_ref_type(k, k.rs.refs[n], tc_name(k, n))
    if !ok || ty == nil { return nil, 0 }
    hi := -1
    #partial switch e in distinct_base(ty) {
    case ^Type_Union:
        for _, v in e.tag_map { hi = max(hi, v) }
    case ^Type_Enum:
        if e.is_error_kind { return nil, 0 }
        for _, v in e.variants { hi = max(hi, v) }
    case:
        return nil, 0
    }
    return ty, hi + 1
}

tc_type_size :: proc(k: ^TC, n: Tree_Id, elem: Type, span: Span) -> (int, bool) {
    t := k.t
    // (A generic's size param, `$N` or `N`, in an instance: what it's bound to.)
    if n != 0 && (t.tag[n] == .Type_Dollar || t.tag[n] == .Ident && k.rs.refs[n].kind == .Type) {
        if ty, ok := tc_ref_type(k, k.rs.refs[n], ""); ok {
            if ci, is_int := ty.(Type_Const_Int); is_int { return ci.value, true }
        }
    }
    if t.tag[n] == .Ident {
        // (A constant, known: its value.)
        name := tc_name(k, n)
        kc := tc_const_named(k, n)
        if kc == nil && k.rs.refs[n].kind == .None {
            tc_unresolved(k, k.rs.misses[n] or_else {}, span, name, TYPE_UNDEFINED_IDENTIFIER)   // (nothing in sight by that name)
            return 0, false
        }
        if kc == nil {
            tc_error(k, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2, name, type_name(elem))
            return 0, false
        }
        if v, ok := tc_comptime_int(k, kc.value); ok { return int(v), true }
        tc_error(k, span, TYPE_ARRAY_SIZE_CONSTANT_COMPILE_TIME, name)
        return 0, false
    }
    if v, ok := tc_comptime_int(k, n); ok { return int(v), true }
    if tc_has_float(k, n) {
        tc_error(k, span, TYPE_SIZE_EXPRESSION_INTEGER, "a float")
    } else {
        tc_error(k, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
    }
    return 0, false
}

// Whether a float is written in an expression: `2.5`, `1.5 + 1`.
tc_has_float :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := k.t
    #partial switch t.tag[n] {
    case .Number:
        return strings.index_byte(tc_text(t.main[n]), '.') >= 0
    case .Paren, .Unary:
        return tc_has_float(k, Tree_Id(t.a[n]))
    case .Binary:
        return tc_has_float(k, Tree_Id(t.a[n])) || tc_has_float(k, Tree_Id(t.b[n]))
    }
    return false
}

// An integer expression's value, when it is known before the program runs:
// numbers and the operators over them; with `names`, a constant, a
// size_of, an array's length or capacity too. None is known that is a
// float, divides by zero, shifts past the width, or leaves i64.
tc_comptime_int :: proc(k: ^TC, n: Tree_Id, names := true) -> (i64, bool) {
    t := k.t
    if n == 0 { return 0, false }
    v: i128
    #partial switch t.tag[n] {
    case .Number:
        text := tc_text(t.main[n])
        if strings.index_byte(text, '.') >= 0 { return 0, false }
        _, i, err := parse_number_text(text)
        if err != .None { return 0, false }
        v = i
    case .Paren:
        return tc_comptime_int(k, Tree_Id(t.a[n]), names)
    case .Unary:
        x, ok := tc_comptime_int(k, Tree_Id(t.a[n]), names)
        if !ok { return 0, false }
        #partial switch build_tokens[t.main[n]].kind {
        case .Minus: v = -i128(x)
        case .Tilde: v = i128(~x)
        case:        return 0, false
        }
    case .Binary:
        l, l_ok := tc_comptime_int(k, Tree_Id(t.a[n]), names)
        r, r_ok := tc_comptime_int(k, Tree_Id(t.b[n]), names)
        if !l_ok || !r_ok { return 0, false }
        a, b := i128(l), i128(r)
        op := build_tokens[t.main[n]].kind
        if (op == .Slash || op == .Modulo) && b == 0 { return 0, false }
        if (op == .Shift_Left || op == .Shift_Right) && (b < 0 || b >= 64) { return 0, false }
        #partial switch op {
        case .Plus:        v = a + b
        case .Minus:       v = a - b
        case .Star:        v = a * b
        case .Slash:       v = a / b
        case .Modulo:      v = a % b
        case .Shift_Left:  v = a << uint(b)
        case .Shift_Right: v = a >> uint(b)
        case .Ampersand:   v = a & b
        case .Pipe:        v = a | b
        case .Tilde:       v = a ~ b
        case:              return 0, false
        }
    case .Size_Of:
        st, measured := k.annot.size_of[tc_sid(k, n)]
        if !names || !measured { return 0, false }
        return i64(type_size(st)), true
    case .Field:
        // (An array's capacity is its type's; a fixed one's length too.)
        field := tc_text(Token_Id(t.b[n]))
        base := Tree_Id(t.a[n])
        if !names || (field != "cap" && field != "len") || t.tag[base] != .Ident { return 0, false }
        bt, ok := tc_ref_type(k, k.rs.refs[base], tc_name(k, base))
        if !ok { return 0, false }
        #partial switch a in distinct_base(bt) {
        case ^Type_Partial_Array: if field == "cap" && a.size > 0 { return i64(a.size), true }
        case ^Type_Fixed_Array:   if a.size > 0 { return i64(a.size), true }
        }
        return 0, false
    case .Ident:
        kc := k.const_at[k.rs.refs[n].decl] if k.rs.refs[n].kind == .Const else nil
        if !names || kc == nil || kc.visiting { return 0, false }
        kc.visiting = true
        defer kc.visiting = false
        return tc_comptime_int(k, kc.value, names)
    case:
        return 0, false
    }
    if v < i128(min(i64)) || v > i128(max(i64)) { return 0, false }
    return i64(v), true
}

// `q.T`: a module's type (q its alias), a union's variant's struct, a type a
// struct holds (`Outer.Inner.Innermost`) or a method of it (as a fun's
// type) — what its ref says — else a variable's struct's method (by the
// variable's type); nil when it names none. (n: its node — a type's name, a
// literal's `Outer.Inner{…}`.)
tc_qualified_type :: proc(k: ^TC, n: Tree_Id, parts: []Token_Id) -> Type {
    if t, ok := tc_ref_type(k, k.rs.refs[n], tc_dotted(parts)); ok { return t }
    // (No method either: no type — not a Type holding a nil ^Type_Scope, which
    // isn't nil, and whose declaration the caller then reads.)
    if fn := tc_held_method(k, parts); fn != nil { return fn }
    return nil
}

// `v.method`, named as a type: the method of v's struct (nil: none).
tc_held_method :: proc(k: ^TC, parts: []Token_Id) -> ^Type_Scope {
    if len(parts) != 2 { return nil }
    ref := k.rs.token_refs[parts[0]] or_else {}
    if !tc_is_variable(ref) { return nil }
    vt, ok := tc_ref_type(k, ref, tc_text(parts[0]))
    if !ok { return nil }
    if sd := as_scope_body(vt); sd != nil {
        if fn, has := sd.functions[tc_text(parts[1])]; has && fn != nil { return fn }
    }
    return nil
}

// Name parts, as written: `a.b.c`.
tc_dotted :: proc(parts: []Token_Id) -> string {
    sb := strings.builder_make(context.temp_allocator)
    for p, i in parts {
        if i > 0 { strings.write_byte(&sb, '.') }
        strings.write_string(&sb, tc_text(p))
    }
    return strings.to_string(sb)
}

// `fn name`: the type of the fun a name names (a local holding one, too);
// `fn q.name`, a module's fun or a variable's struct's.
tc_fun_type_of :: proc(k: ^TC, n: Tree_Id, span: Span) -> Type {
    parts := tree_token_list(k.t, k.t.a[n])
    name := tc_dotted(parts)
    vt, ok := tc_ref_type(k, k.rs.refs[n], name)
    if ok {
        if ft, is_scope := vt.(^Type_Scope); is_scope && ft.kind == .Fun { return ft }
        if len(parts) == 1 {
            tc_error(k, span, TYPE_FN_REQUIRES_FUNCTION_VALUED_NAME, name, name, type_name(vt))
            return Type_Error{}
        }
    }
    if fn := tc_held_method(k, parts); fn != nil && fn.kind == .Fun { return fn }
    tc_error(k, span, TYPE_UNKNOWN_FUNCTION_FN, name, name)
    return Type_Error{}
}

// `Name(args)` as a type: a generic struct's or union's instance; else what
// a count or a constructor's call means, written where a type goes: said so.
// (Its arguments resolved first: a name, a type; a number or an operation,
// a size.)
tc_generic_type :: proc(k: ^TC, n: Tree_Id, span: Span) -> Type {
    t := k.t
    if tmpl, is_template := tc_template(k, k.rs.refs[n]); is_template {
        if t.tag[tmpl.node] == .Union_Def { return tc_union_instance(k, n, tmpl, span) }
        return tc_struct_instance(k, n, tmpl, span)
    }
    for a in tree_list(t, t.a[n]) {
        if tc_is_type_tag(t.tag[a]) { tc_type(k, a, span) }
    }
    return tc_generic_base(k, n, span)
}

// `T(n)` where T is no generic: a distinct slice's capacity, a constructor's
// call, or a count (`[]T(n)`: written `[:n]T`) — each an error, said so.
tc_generic_base :: proc(k: ^TC, n: Tree_Id, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    one := len(tree_list(t, t.a[n])) == 1
    found, ok := tc_ref_type(k, k.rs.refs[n], name)
    if one {
        if dt, is_distinct := found.(^Type_Distinct); ok && is_distinct && is_slice_type(dt.base_type) {
            tc_error(k, tree_span(t, n), TYPE_SLICE_ALIAS_CAPACITY)
            return Type_Error{}
        }
    }
    if ok {
        if ts, is_scope := found.(^Type_Scope); is_scope && ts.kind == .Struct && len(ts.params) > 0 {
            tc_error(k, span, TYPE_STRUCT_CLASS_CONSTRUCTOR_PARAMS_GENERIC, name, name, name, name)
            return Type_Error{}
        }
        if _, is_scope := found.(^Type_Scope); is_scope && one {
            tc_error(k, span, TYPE_SLICE_COUNT_SPELLING, name, name, name)
            return Type_Error{}
        }
    }
    tc_error(k, span, TYPE_UNKNOWN_TYPE, name)
    return Type_Error{}
}

tc_is_type_tag :: proc(tag: Tree_Tag) -> bool {
    return tag >= .Type_Name && tag <= .Type_Paren
}

// A type by its name (n: the node that names it): a primitive, else what
// its ref says — a type param, what the instance binds it to; `Self`, the
// struct or fun it's written in.
tc_type_named :: proc(k: ^TC, name: string, span: Span, n: Tree_Id) -> Type {
    if _, is_primitive := tc_primitive_named(name); is_primitive { return tc_primitive(k, name, span) }
    ref := k.rs.refs[n]
    if t, ok := tc_ref_type(k, ref, name); ok { return t }
    // (Two modules' type, said so.)
    if owners := (k.rs.misses[n] or_else {}).owners; ref.kind == .None && len(owners) > 1 {
        tc_error(k, span, TYPE_TYPE_NAME_AMBIGUOUS_DEFINED_USE, name, strings.join(owners[:], ", ", context.temp_allocator), name)
        return Type_Error{}
    }
    tc_error(k, span, TYPE_UNKNOWN_TYPE, name)
    return Type_Error{}
}

// The generic a name refers to, if it's one.
tc_template :: proc(k: ^TC, ref: Ref) -> (TC_Template, bool) {
    if ref.kind != .Type && ref.kind != .Fun { return {}, false }
    return k.templates[ref.decl]
}
