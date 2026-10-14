package mara

import "core:strings"

// ---------------------------------------------------------------------------
// Scopes: what the checker keeps of a fun, a struct, a module — its record
// (its members, by name: what a value of it reaches by type). What a name
// refers to is the resolver's (resolve.odin, design/name_resolution.md).
// ---------------------------------------------------------------------------

raw_type_key :: proc(t: Type) -> rawptr {
    #partial switch v in t {
    case ^Type_Scope:    return rawptr(v)
    case ^Type_Enum:     return rawptr(v)
    case ^Type_Union:    return rawptr(v)
    case ^Type_Distinct: return rawptr(v)
    case ^Type_Ptr:      return rawptr(v)
    case ^Type_Slice:    return rawptr(v)
    case ^Type_Fixed_Array: return rawptr(v)
    }
    return nil
}

// Bind a name in scope s: its type, and what declares it.
scope_bind :: proc(s: ^Type_Scope, name: string, t: Type, ref: Ref) {
    // (A struct's or a fun's member, what a value of it or a qualified name
    // reaches by type; a module's names and a block's are the resolver's.)
    if s == nil || s.is_module || s.kind == .Block { return }
    s.types[name] = t
}

// What declares an enum's or a union's variant, by its name (0: none).
variant_decl :: proc(t: Type, name: string) -> Token_Id {
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:
        return v.variant_decls[name] or_else 0
    case ^Type_Union:
        if vs := v.variant_structs[name] or_else nil; vs != nil { return vs.decl }
    }
    return 0
}

// What declares a type that has a name: its name's token (0: none does).
type_decl :: proc(t: Type) -> Token_Id {
    #partial switch v in t {
    case ^Type_Scope:    return v.decl
    case ^Type_Enum:     return v.span.at
    case ^Type_Union:    return v.span.at
    case ^Type_Distinct: return v.span.at
    }
    return 0
}

// The enclosing function's name (for #caller_name).
enclosing_fn_name :: proc(env: ^Type_Scope) -> string {
    if s := enclosing_callable_scope(env); s != nil {
        return s.source_name if s.source_name != "" else s.name
    }
    return "main" // top-level code runs in main
}

// A callable scope: a fun, or a struct (its constructor's body). A module
// is a .Struct too, but never callable.
scope_is_callable :: proc(s: ^Type_Scope) -> bool {
    return s != nil && (s.kind == .Fun || (s.kind == .Struct && !s.is_module))
}

// The module scope at the top of a scope's chain. nil if `start` is nil.
module_scope :: proc(start: ^Type_Scope) -> ^Type_Scope {
    s := start
    for s != nil && s.parent_scope != nil { s = s.parent_scope }
    return s
}

// The struct whose body this block is directly in, or nil — whether a
// declaration is a field's.
parent_struct_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil { return nil }
    p := env.parent_scope
    if p != nil && p.kind == .Struct && !p.is_module { return p }
    return nil
}

// The results of the fun (or constructor) whose body this is. Empty: none.
enclosing_return_types :: proc(env: ^Type_Scope) -> []Type {
    if s := enclosing_callable_scope(env); s != nil { return s.return_types[:] }
    return nil
}

// The fun or constructor whose body this is; nil at module level (a
// constant's value has no enclosing function).
enclosing_callable_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    for s := env; s != nil; s = s.parent_scope {
        if scope_is_callable(s) { return s }
    }
    return nil
}

// "prefix_name", the module's dots underscores (LLVM symbol names); name
// unchanged when prefix is empty.
make_flat_name :: proc(prefix, name: string) -> string {
    if prefix == "" { return name }
    flat_prefix, _ := strings.replace_all(prefix, ".", "_")
    return strings.concatenate({flat_prefix, "_", name})
}

// A name in a module, flat (make_flat_name), as a key to look up: made once
// a check — made at each lookup, it was millions of strings, all kept.
tc_flat_name :: proc(k: ^TC, prefix, name: string) -> string {
    key := [2]string{prefix, name}
    if s, made := k.flat_names[key]; made { return s }
    s := make_flat_name(prefix, name)
    k.flat_names[key] = s
    return s
}

// Resolve a type to its underlying Scope_Body, handling pointers (auto-deref).
// Returns nil if the type is not a struct.
resolve_to_struct_type :: proc(c: ^Checker, t: Type) -> ^Scope_Body {
    inner := t
    if pt, pt_ok := t.(^Type_Ptr); pt_ok {
        inner = pt.elem
    }
    // (A named struct — `type P`, `distinct P` — has P's functions.)
    if sd := as_scope_body(distinct_base(inner)); sd != nil && len(sd.fields) > 0 { return sd }
    // Check by type name in the struct table
    tn := type_name(t)
    if st, ok := c.table.structs[tn]; ok { return &st.sd }
    if st, ok := c.table.funs[tn]; ok { return &st.sd }
    return nil
}

// Populate a fun's field_map from its fields array for O(1) field lookup.
build_field_map :: proc(st: ^Scope_Body) {
    for f, i in st.fields {
        st.field_map[f.name] = i
    }
}

// Track variant ownership in c.table.variant_to_enum so the dot-shorthand
// fallback (`.Core` with no expected type) can find variants by name across
// visible enums/unions. Variants are never bound as bare names: bare variant
// resolution goes through an expected type.
register_enum_variants :: proc(c: ^Checker, et: ^Type_Enum, enum_key: string = "") {
    key := enum_key if enum_key != "" else et.name
    for vname in et.variants {
        if existing_enum, mapped := c.table.variant_to_enum[vname]; mapped {
            if existing_enum != "" && existing_enum != key {
                c.table.variant_to_enum[vname] = "" // ambiguous — different enum
            }
        } else {
            c.table.variant_to_enum[vname] = key
        }
    }
}

