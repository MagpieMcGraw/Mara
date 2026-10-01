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
        if len(parts) != 1 {
            tc_unsupported(k, n, "a qualified type name")
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
    case .Type_Pointer:
        pt := new(Type_Ptr)
        pt.elem = tc_type(k, Tree_Id(t.a[n]), env, span)
        return pt
    case .Type_Paren:
        return tc_type(k, Tree_Id(t.a[n]), env, span)
    case .Type_Slice:
        if t.a[n] != 0 {
            tc_unsupported(k, n, "a sized slice")
            return Type_Error{}
        }
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

// A number as written — or an operation of numbers — its value: no
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
