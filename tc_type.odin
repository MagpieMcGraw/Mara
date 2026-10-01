package mara

import "core:strings"

// Types as written (the flat tree's type nodes), resolved: a keyword to its
// primitive, a name through the scope and the table, a pointer, an array.

tc_type :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, span: Span) -> Type {
    if n == 0 { return Type_Any{} }
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Keyword:
        return tc_primitive(k, tc_name(k, n), span)
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        if len(parts) > 1 {
            if qt := tc_qualified_type(k, parts, env); qt != nil { return qt }
            tc_error(k, span, TYPE_UNKNOWN_TYPE, tc_dotted(parts))
            return Type_Error{}
        }
        name := tc_text(parts[0])
        if p, is_primitive := tc_primitive_named(name); is_primitive {
            if name == "int" { tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64); return Type_Error{} }
            if name == "uint" { tc_error(k, span, TYPE_TYPE_UINT_RESERVED_USE_U64); return Type_Error{} }
            return p
        }
        // (A type param, in an instance; `Self`: the struct or fun the type is
        // written in.)
        if bound, is_param := k.subst[name]; is_param && bound != nil { return bound }
        if name == "Self" {
            if s := enclosing_callable_scope(env); s != nil { return s }
        } else if found, ok := type_env_get(env, name); ok {
            return found
        }
        flat := make_flat_name(k.pkg, name)
        if st, ok := k.table.structs[flat]; ok { return st }
        if st, ok := k.table.funs[flat]; ok { return st }
        if ut, ok := k.table.unions[flat]; ok { return ut }
        if et, ok := k.table.enums[flat]; ok { return et }
        if dt, ok := k.table.distinct_types[flat]; ok { return dt }
        tc_error(k, span, TYPE_UNKNOWN_TYPE, name)
        return Type_Error{}
    case .Type_Dollar:
        name := tc_text(Token_Id(t.a[n]))
        if bound, is_param := k.subst[name]; is_param && bound != nil { return bound }
        tc_unsupported(k, n, "a type param outside its instance")
        return Type_Error{}
    case .Type_Fun:
        // (A fun's type: its params' and results' types.)
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in tree_list(t, t.a[n]) { append(&ft.params, Struct_Type_Field{type_ = tc_type(k, p, env, span)}) }
        for r in tree_list(t, t.b[n]) { append(&ft.return_types, tc_type(k, r, env, span)) }
        populate_cg_signature(ft)
        return ft
    case .Type_Generic:
        return tc_generic_type(k, n, env, span)
    case .Type_Of:
        return tc_fun_type_of(k, tree_token_list(t, t.a[n]), env, span)
    case .Type_Pointer:
        pt := new(Type_Ptr)
        pt.elem = tc_type(k, Tree_Id(t.a[n]), env, span)
        return pt
    case .Type_Paren:
        return tc_type(k, Tree_Id(t.a[n]), env, span)
    case .Type_Slice:
        // (`[:n]T`: n a declaration's capacity — tc_decl_sized; the type []T.)
        sl := new(Type_Slice)
        sl.elem = tc_type(k, Tree_Id(t.b[n]), env, span)
        return sl
    case .Type_Partial:
        pa := new(Type_Partial_Array)
        pa.elem = tc_type(k, Tree_Id(t.b[n]), env, span)
        size, ok := tc_type_size(k, Tree_Id(t.a[n]), pa.elem, env, span)
        if !ok { return Type_Error{} }
        pa.size = size
        return pa
    case .Type_Array:
        r := tree_rec(t, t.a[n], 2)
        fa := new(Type_Fixed_Array)
        fa.elem = tc_type(k, Tree_Id(t.b[n]), env, span)
        if r[1] != 0 { fa.index_type = tc_type(k, Tree_Id(r[1]), env, span) }
        size, ok := tc_type_size(k, Tree_Id(r[0]), fa.elem, env, span)
        if !ok { return Type_Error{} }
        fa.size = size
        return fa
    }
    tc_unsupported(k, n, "this type")
    return Type_Error{}
}

tc_primitive :: proc(k: ^TC, name: string, span: Span) -> Type {
    if name == "int" { tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64); return Type_Error{} }
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

// An array's size, known when the program is compiled: a number, or an
// expression of them.
tc_type_size :: proc(k: ^TC, n: Tree_Id, elem: Type, env: ^Type_Scope, span: Span) -> (int, bool) {
    t := k.t
    #partial switch t.tag[n] {
    case .Number:
        _, i, _ := parse_number_text(tc_text(t.main[n]))
        return int(i), true
    case .Ident:
        // (A constant, known: its value.)
        name := tc_name(k, n)
        if _, is_const := k.const_owners[name]; is_const && !tc_const_visible(k, env, name) {
            tc_error(k, span, TYPE_UNDEFINED_IDENTIFIER, name)
            return 0, false
        }
        kc, is_const := k.consts[name]
        if !is_const {
            tc_error(k, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2, name, type_name(elem))
            return 0, false
        }
        if f, i, lit := tc_literal_value(k, kc.value); lit {
            _ = f
            return int(i), true
        }
        if v, ok := tc_comptime_int(k, kc.value, nil); ok { return int(v), true }
        tc_error(k, span, TYPE_ARRAY_SIZE_CONSTANT_COMPILE_TIME, name)
        return 0, false
    }
    if v, ok := tc_comptime_int(k, n, env); ok { return int(v), true }
    tc_error(k, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
    return 0, false
}

// An integer expression's value, when it is known before the program runs.
tc_comptime_int :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> (i64, bool) {
    t := k.t
    #partial switch t.tag[n] {
    case .Number:
        f, _, _ := parse_number_text(tc_text(t.main[n]))
        return i64(f), true
    case .Paren:
        return tc_comptime_int(k, Tree_Id(t.a[n]), env)
    case .Size_Of:
        if st, measured := k.size_of[n]; measured { return i64(elem_byte_size(llvm_type_from_checker(st), k.checked)), true }
    case .Unary:
        if build_tokens[t.main[n]].kind != .Minus { return 0, false }
        v, ok := tc_comptime_int(k, Tree_Id(t.a[n]), env)
        return -v, ok
    case .Binary:
        l, l_ok := tc_comptime_int(k, Tree_Id(t.a[n]), env)
        if !l_ok { return 0, false }
        r, r_ok := tc_comptime_int(k, Tree_Id(t.b[n]), env)
        if !r_ok { return 0, false }
        #partial switch build_tokens[t.main[n]].kind {
        case .Plus:        return l + r, true
        case .Minus:       return l - r, true
        case .Star:        return l * r, true
        case .Slash:       if r != 0 { return l / r, true }
        case .Modulo:      if r != 0 { return l % r, true }
        case .Shift_Left:  return l << uint(r), true
        case .Shift_Right: return l >> uint(r), true
        case .Pipe:        return l | r, true
        case .Ampersand:   return l & r, true
        case .Caret:       return l ~ r, true
        }
    case .Field:
        // An array's capacity is its type's (a fixed one's length too).
        field := tc_text(Token_Id(t.b[n]))
        base := Tree_Id(t.a[n])
        if (field != "cap" && field != "len") || t.tag[base] != .Ident { return 0, false }
        if env == nil { return 0, false }
        bt, ok := type_env_get(env, tc_name(k, base))
        if !ok { return 0, false }
        #partial switch v in distinct_base(bt) {
        case ^Type_Partial_Array: if field == "cap" && v.size > 0 { return i64(v.size), true }
        case ^Type_Fixed_Array:   if v.size > 0 { return i64(v.size), true }
        }
    case .Ident:
        if kc, ok := k.consts[tc_name(k, n)]; ok { return tc_comptime_int(k, kc.value, env) }
    }
    return 0, false
}

// A number as written â or an operation of numbers â its value: no
// constant's name (a span's bounds, its size checked when they are numbers).
tc_number_int :: proc(k: ^TC, n: Tree_Id) -> (int, bool) {
    t := k.t
    if n == 0 { return 0, false }
    #partial switch t.tag[n] {
    case .Number:
        text := tc_text(t.main[n])
        if strings.index_byte(text, '.') >= 0 { return 0, false }
        _, i, err := parse_number_text(text)
        return int(i), err == .None
    case .Paren:
        return tc_number_int(k, Tree_Id(t.a[n]))
    case .Unary:
        v, ok := tc_number_int(k, Tree_Id(t.a[n]))
        if !ok { return 0, false }
        #partial switch build_tokens[t.main[n]].kind {
        case .Minus: return -v, true
        case .Tilde: return ~v, true
        }
    case .Binary:
        l, l_ok := tc_number_int(k, Tree_Id(t.a[n]))
        r, r_ok := tc_number_int(k, Tree_Id(t.b[n]))
        if !l_ok || !r_ok { return 0, false }
        #partial switch build_tokens[t.main[n]].kind {
        case .Plus:        return l + r, true
        case .Minus:       return l - r, true
        case .Star:        return l * r, true
        case .Slash:       if r != 0 { return l / r, true }
        case .Modulo:      if r != 0 { return l % r, true }
        case .Shift_Left:  if r >= 0 { return l << uint(r), true }
        case .Shift_Right: if r >= 0 { return l >> uint(r), true }
        case .Ampersand:   return l & r, true
        case .Pipe:        return l | r, true
        case .Tilde:       return l ~ r, true
        }
    }
    return 0, false
}

// `q.T`: a module's type (q its alias), a union's variant's struct, a type a
// struct holds (`Outer.Inner.Innermost`) or a method of it (as a fun's
// type), a variable's struct's method; nil when it names none.
tc_qualified_type :: proc(k: ^TC, parts: []Token_Id, env: ^Type_Scope) -> Type {
    alias := tc_text(parts[0])
    rest := tc_dotted(parts[1:])
    if flat := resolve_type_name(k.c, rest, alias, env); flat != "" {
        if st, ok := k.table.structs[flat]; ok { return st }
        if st, ok := k.table.funs[flat]; ok { return st }
        if ut, ok := k.table.unions[flat]; ok { return ut }
        if et, ok := k.table.enums[flat]; ok { return et }
        if dt, ok := k.table.distinct_types[flat]; ok { return dt }
    }
    alias_flat := resolve_type_name(k.c, alias, "", env)
    if ut, ok := k.table.unions[alias_flat]; ok {
        if key, has := ut.variant_structs[rest]; has {
            if st, found := k.table.structs[key]; found { return st }
            if st, found := k.table.funs[key]; found { return st }
        }
    }
    parent: ^Scope_Body
    if st, ok := k.table.structs[alias_flat]; ok {
        parent = &st.sd
    } else if st, ok := k.table.funs[alias_flat]; ok {
        parent = &st.sd
    } else if at, ok := type_env_get(env, alias); ok {
        parent = as_scope_body(at)   // (a parent a fun's body defines)
    }
    if parent != nil {
        // (Through each type it holds, as far as they go — registered as
        // they are named, before their holders' bodies are checked.)
        tc_scope_defs(k, parent)
        i := 1
        for ; i < len(parts) - 1; i += 1 {
            seg, has := parent.types[tc_text(parts[i])]
            if !has { break }
            next := as_scope_body(seg)
            if next == nil { break }
            parent = next
            tc_scope_defs(k, parent)
        }
        last := tc_dotted(parts[i:])
        if inner, has := parent.types[last]; has { return inner }
        if fn, has := parent.functions[last]; has && fn != nil { return fn }
    }
    if vt, ok := type_env_get(env, alias); ok {
        if sd := as_scope_body(vt); sd != nil {
            if fn, has := sd.functions[rest]; has && fn != nil { return fn }
        }
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

// A scope's own types and funs, registered (once): a struct's, named in a
// type before its body is checked.
tc_scope_defs :: proc(k: ^TC, sd: ^Scope_Body) {
    if i, ok := k.scope_of[sd_type_scope(sd)]; ok { tc_register_defs(k, k.scopes[i]) }
}

// `fn name`: the type of the fun a name names (a local holding one, too);
// `fn q.name`, a module's fun or a variable's struct's.
tc_fun_type_of :: proc(k: ^TC, parts: []Token_Id, env: ^Type_Scope, span: Span) -> Type {
    name := tc_dotted(parts)
    if len(parts) == 1 {
        if vt, ok := type_env_get(env, name); ok {
            if ft, is_scope := vt.(^Type_Scope); is_scope && ft.kind == .Fun { return ft }
            tc_error(k, span, TYPE_FN_REQUIRES_FUNCTION_VALUED_NAME, name, name, type_name(vt))
            return Type_Error{}
        }
        if ft, ok := k.table.funs[resolve_type_name(k.c, name, "", env)]; ok && ft.kind == .Fun { return ft }
        tc_error(k, span, TYPE_UNKNOWN_FUNCTION_FN, name, name)
        return Type_Error{}
    }
    alias, bare := tc_text(parts[0]), tc_dotted(parts[1:])
    if flat := resolve_type_name(k.c, bare, alias, env); flat != "" {
        if ft, ok := k.table.funs[flat]; ok && ft.kind == .Fun { return ft }
    }
    if vt, ok := type_env_get(env, alias); ok {
        if sd := as_scope_body(vt); sd != nil {
            if fn, has := sd.functions[bare]; has && fn != nil && fn.kind == .Fun { return fn }
        }
    }
    tc_error(k, span, TYPE_UNKNOWN_FUNCTION_FN, name, name)
    return Type_Error{}
}

// `Name(args)` as a type: a generic struct's instance (to come); else `T(n)`
// — `[]T(n)`'s T, n a count its declaration or take reads (tc_count_arg) —
// or what a constructor's call means, written where a type goes: said so.
// (Its arguments resolved first: a name, a type; a number or an operation,
// a size.)
tc_generic_type :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, span: Span) -> Type {
    t := k.t
    if tmpl, is_template := k.templates[tc_name(k, n)]; is_template { return tc_struct_instance(k, n, tmpl, env, span) }
    for a in tree_list(t, t.a[n]) {
        if tc_is_type_tag(t.tag[a]) { tc_type(k, a, env, span) }
    }
    return tc_generic_base(k, n, env, span)
}

// `T(n)`'s T, by its name: a struct — n a count; else an error.
tc_generic_base :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    if len(tree_list(t, t.a[n])) == 1 {
        flat := resolve_type_name(k.c, name, "", env)
        if dt, ok := k.table.distinct_types[flat]; ok && is_slice_type(dt.base_type) {
            tc_unsupported(k, n, "a sized slice alias")
            return Type_Error{}
        }
        if st, ok := k.table.structs[flat]; ok { return st }
        if found, ok := type_env_get(env, name); ok {
            if _, is_scope := found.(^Type_Scope); is_scope { return found }
        }
    }
    if found, ok := type_env_get(env, name); ok {
        if ts, is_scope := found.(^Type_Scope); is_scope && ts.kind == .Struct && len(ts.params) > 0 {
            tc_error(k, span, TYPE_STRUCT_CLASS_CONSTRUCTOR_PARAMS_GENERIC, name, name, name, name)
            return Type_Error{}
        }
    }
    tc_error(k, span, TYPE_UNKNOWN_TYPE, name)
    return Type_Error{}
}

// `T(n)`, T no generic: n, a count — a number or an operation (a take's, a
// name too); 0 when it is none.
tc_count_arg :: proc(k: ^TC, n: Tree_Id, take := false) -> Tree_Id {
    t := k.t
    if n == 0 || t.tag[n] != .Type_Generic || tc_name(k, n) in k.templates { return 0 }
    args := tree_list(t, t.a[n])
    if len(args) != 1 { return 0 }
    if tc_is_type_tag(t.tag[args[0]]) && !(take && t.tag[args[0]] == .Type_Name) { return 0 }
    return args[0]
}

tc_is_type_tag :: proc(tag: Tree_Tag) -> bool {
    return tag >= .Type_Name && tag <= .Type_Paren
}
