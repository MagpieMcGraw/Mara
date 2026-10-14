package mara

import "core:strings"

// ---------------------------------------------------------------------------
// Scopes and name resolution
// ---------------------------------------------------------------------------
//
// The checker's current scope is a ^Type_Scope: a block's, a fun's, a
// struct's, a file's or a module's, each chained to the one it is written in
// (parent_scope). A scope holds the names it declares (types, functions) and
// the modules it uses (includes). Resolution walks the chain.

// Whether scope s defines `name` itself (its own types or functions): one
// level, no walk.
scope_defines :: proc(s: ^Type_Scope, name: string) -> (Type, bool) {
    if s == nil { return nil, false }
    if s.types != nil { if t, ok := s.types[name]; ok { return t, true } }
    if s.functions != nil { if f, ok := s.functions[name]; ok && f != nil { return f, true } }
    return nil, false
}

// A name a used module exports.
include_lookup :: proc(inc: ^Scope_Body, name: string) -> (Type, bool) {
    if inc == nil { return nil, false }
    if t, ok := inc.types[name]; ok { return t, true }
    return nil, false
}

// A local, from a block up through the blocks around it, stopping at the
// first scope that is no block (the fun or struct they are in): a block sees
// its own locals, its enclosing blocks' and its function's, never an outer
// function's (no closures).
scope_local_lookup :: proc(start: ^Type_Scope, name: string) -> (Type, bool) {
    for s := start; s != nil && s.kind == .Block; s = s.parent_scope {
        if s.types != nil {
            if t, ok := s.types[name]; ok { return t, true }
        }
    }
    return nil, false
}

// Whether a name binds a module (a file's `gl :: use mara.open_gl`): the one
// kind of block-scoped name seen past a function boundary. A function sees
// the outside world through its arguments, never an enclosing scope's locals
// — a module's variables included, since a module is a scope like any other.
names_module :: proc(t: Type) -> bool {
    m, ok := t.(^Type_Scope)
    return ok && m.is_module
}

// A name a module used along the chain exports (the first found), up to the
// module — or, `below_module`, short of it.
scope_includes_lookup :: proc(env: ^Type_Scope, name: string, below_module: bool) -> (Type, bool) {
    for s := env; s != nil; s = s.parent_scope {
        if below_module && s.is_module { break }
        for inc in s.includes { if t, ok := include_lookup(inc, name); ok { return t, true } }
        if s.is_module { break }
    }
    return nil, false
}

// A name past the locals: each enclosing scope's own definitions (a block's
// only when they name a module), inner to outer, then what the modules used
// along the way export. The scope it was found in (nil: a module's export).
//
// `below_module` stops short of the module's scope — the `:=` shadowing
// policy, so a local `shader := gl.CreateShader(...)` doesn't conflate with
// the module's own binding.
scope_resolve :: proc(env: ^Type_Scope, name: string, below_module := false) -> (Type, ^Type_Scope, bool) {
    for s := env; s != nil; s = s.parent_scope {
        if below_module && s.is_module { break }
        if s.types != nil {
            t, ok := s.types[name]
            if ok && (s.kind != .Block || names_module(t)) { return t, s, true }
        }
        if s.functions != nil { if f, ok := s.functions[name]; ok && f != nil { return f, s, true } }
    }
    if t, ok := scope_includes_lookup(env, name, below_module); ok { return t, nil, true }
    return nil, nil, false
}

// THE name lookup: a local first, else scope_resolve. Returns the scope the
// name was found in — nil for a local or a module's export — so a check can
// ask whether it is a field of an enclosing struct.
scope_find :: proc(env: ^Type_Scope, name: string, below_module := false) -> (Type, ^Type_Scope, bool) {
    if t, ok := scope_local_lookup(env, name); ok {
        return t, nil, true   // a local never lives in a struct's scope
    }
    return scope_resolve(env, name, below_module)
}

scope_lookup :: proc(env: ^Type_Scope, name: string) -> (Type, bool) {
    t, _, ok := scope_find(env, name)
    return t, ok
}

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
    if s == nil { return }
    s.types[name] = t   // (a block's maps grow in its arena: tc_block)
    s.refs[name] = ref
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

// A used module's exports, made reachable from the scope that uses it:
// `use path` and `name :: use path` alike (the alias also names it). Without
// this, `name :: use path` would force `name.X` for every member, and a
// stdlib swap (SDL3 → SDL2) would ripple through every caller. A sealed use
// (`name :: sealed use path`) exports nothing bare — only `name.X` — to
// keep colliding bindings (SDL2 vs SDL3) apart.
flatten_module_exports :: proc(c: ^Checker, env: ^Type_Scope, mod_sd: ^Scope_Body, is_sealed := false) {
    assert(sd_is_module(mod_sd), "module-struct must have scope")
    if is_sealed { return }
    if env != nil { append(&env.includes, mod_sd) }
    for name, t in mod_sd.types {
        if name == "void" { continue }  // don't re-export the void null-pointer literal
        if tf, is_func := t.(^Type_Scope); is_func && (len(tf.params) > 0 || tf.has_parens) {
            c.declared_funs[name] = true
        }
    }
}

// is_enum_visible reports whether the enum identified by `flat_name`
// (e.g. "mara_sdl_Init_Flags") is reachable from `env` via the include chain
// or its parents. Used by the variant-ambiguity check so that a globally
// ambiguous variant (same name in two enums) only errors when both owners
// are actually in scope here.
is_enum_visible :: proc(env: ^Type_Scope, flat_name: string) -> bool {
    scope_has_enum :: proc(s: ^Scope_Body, flat: string) -> bool {
        if s == nil { return false }
        for _, t in s.types {
            if et, ok := t.(^Type_Enum); ok && et.name == flat { return true }
        }
        return false
    }
    for s := env; s != nil; s = s.parent_scope {
        if scope_has_enum(s, flat_name) { return true }
        for inc in s.includes {
            if scope_has_enum(inc, flat_name) { return true }
        }
        if s.is_module { break }
    }
    return false
}

