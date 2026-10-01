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

// When `name` is a local of a scope past the function boundary — the one
// thing scope_resolve won't show — the scope that owns it (the module or
// function the block belongs to); nil otherwise.
outer_local_owner :: proc(env: ^Type_Scope, name: string) -> ^Type_Scope {
    s := env
    for s != nil && s.kind == .Block { s = s.parent_scope }
    for ; s != nil; s = s.parent_scope {
        if s.kind != .Block || s.types == nil { continue }
        if t, ok := s.types[name]; !ok || names_module(t) { continue }
        owner := s
        for owner != nil && owner.kind == .Block { owner = owner.parent_scope }
        return owner
    }
    return nil
}

// A name that didn't resolve. When it is an enclosing scope's local, that is
// the rule it broke, so say so instead of `msg`.
report_unresolved :: proc(c: ^Checker, span: Span, env: ^Type_Scope, name: string, msg: string) {
    if owner := outer_local_owner(env, name); owner != nil {
        where_ := owner.source_name if owner.source_name != "" else owner.name
        check_error(c, span, TYPE_LOCAL_OF_ENCLOSING_SCOPE, name, where_)
        return
    }
    check_error(c, span, msg, name)
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

// A type's name, resolved with ambiguity detection:
//   - typ, ok=true:                it resolves unambiguously
//   - ok=false, ambiguous_owners:  two or more used modules export it at the
//                                  same level (the caller reports it)
//   - ok=false, nil ambiguous:     not found anywhere
// An own definition in any enclosing scope wins over what modules export —
// never ambiguous, since it was written here. Ambiguity only arises among
// modules used: `use mara.sdl3` and `use mara.sdl2`, both with `PollEvent`.
resolve_with_ambiguity :: proc(env: ^Type_Scope, name: string) -> (typ: Type, ok: bool, ambiguous_owners: [dynamic]string) {
    // (`Self`: the struct or fun it is written in.)
    if name == "Self" {
        if s := enclosing_callable_scope(env); s != nil { return s, true, nil }
        return nil, false, nil
    }
    for s := env; s != nil; s = s.parent_scope {
        if t, found := scope_defines(s, name); found {
            typ, ok = t, true
            break
        }
    }
    if !ok {
        // No own definition: the distinct modules exporting it at the nearest
        // level that has it.
        owner_list: [dynamic]string
        distinct_typs: map[rawptr]bool
        distinct_owners: map[string]bool
        first_typ: Type
        for s := env; s != nil; s = s.parent_scope {
            found_any := false
            for inc in s.includes {
                if t, found := include_lookup(inc, name); found {
                    found_any = true
                    if first_typ == nil { first_typ = t }
                    key := raw_type_key(t)
                    if key not_in distinct_typs {
                        distinct_typs[key] = true
                        owner := inc.name if inc != nil else "<anonymous-include>"
                        if owner not_in distinct_owners {
                            distinct_owners[owner] = true
                            append(&owner_list, owner)
                        }
                    }
                }
            }
            if found_any { break }  // stop at nearest level with includes
            if s.is_module { break }
        }
        if len(distinct_typs) == 1 { typ, ok = first_typ, true }
        else if len(distinct_typs) > 1 { ambiguous_owners = owner_list }
    }
    return
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

// Bind a name in scope s.
scope_bind :: proc(s: ^Type_Scope, name: string, t: Type) {
    if s == nil { return }
    if s.types == nil { s.types = make(map[string]Type) }
    s.types[name] = t
}

// A new block's scope (an if's, a loop's, a defer's), inside parent.
new_block_scope :: proc(parent: ^Type_Scope) -> ^Type_Scope {
    s := new(Type_Scope)
    s.parent_scope = parent
    s.kind = .Block
    return s
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

// Resolve a user-written type name to its canonical flat map key.
// If qualifier is non-empty, looks up the import alias to find the package.
// Returns "" when qualifier is not an import alias (caller handles union inner types etc.).
resolve_type_name :: proc(c: ^Checker, bare_name: string, qualifier: string = "", env: ^Type_Scope = nil) -> string {
    if qualifier != "" {
        // Try module-qualified resolution: look up qualifier in env
        if env != nil {
            qual_type, found := scope_lookup(env, qualifier)
            if found {
                if mod_sd := as_scope_body(qual_type); sd_is_module(mod_sd) {
                    return make_flat_name(mod_sd.name, bare_name)
                }
            }
        }
        return ""
    }
    // Walk the chain (own types + includes) to find which module owns this
    // bare name. This matches the actual visibility for the call site, which
    // is important when two modules export the same name (e.g. `Event` in
    // both mara_sdl and mara_sdl2).
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            if s.is_module {
                if _, found := scope_defines(s, bare_name); found {
                    return make_flat_name(c.current_package, bare_name)
                }
            }
            for inc in s.includes {
                if inc == nil { continue }
                if _, found := include_lookup(inc, bare_name); found {
                    return make_flat_name(inc.name, bare_name)
                }
            }
            if s.is_module { break }
        }
    }
    // Local fallback for purely-local names (callers without env, or names
    // declared in the current package itself).
    return make_flat_name(c.current_package, bare_name)
}

// Resolve a type to its underlying Scope_Body, handling pointers (auto-deref).
// Returns nil if the type is not a struct.
resolve_to_struct_type :: proc(c: ^Checker, t: Type) -> ^Scope_Body {
    inner := t
    if pt, pt_ok := t.(^Type_Ptr); pt_ok {
        inner = pt.elem
    }
    if sd := as_scope_body(inner); sd != nil && len(sd.fields) > 0 { return sd }
    // Check by type name in the struct table
    tn := type_name(t)
    if st, ok := c.table.structs[tn]; ok { return &st.sd }
    if st, ok := c.table.funs[tn]; ok { return &st.sd }
    return nil
}

// A function's home module, reporting ambiguity when two or more used
// modules export it — resolve_with_ambiguity's rules, for functions.
resolve_fn_home_with_ambiguity :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> (home: string, ok: bool, ambiguous_owners: [dynamic]string) {
    // Phase 1: own definitions in any enclosing module (always unambiguous).
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            if s.is_module {
                if t, found := scope_defines(s, name); found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        return c.current_package, true, nil
                    }
                }
                break
            }
        }
    }
    // Phase 2: gather distinct include owners exposing this fn.
    distinct_owners: map[string]bool
    owner_list: [dynamic]string
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            for inc in s.includes {
                if inc == nil { continue }
                if t, found := include_lookup(inc, name); found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        owner := inc.name
                        if owner not_in distinct_owners {
                            distinct_owners[owner] = true
                            append(&owner_list, owner)
                        }
                    }
                }
            }
            if s.is_module { break }
        }
    }
    if len(owner_list) == 0 {
        // Fall back to fun_homes (registration-time table) for sites that
        // couldn't reach the right env, then to current_package.
        if h, found := c.table.fun_homes[name]; found && h != "" { return h, true, nil }
        return c.current_package, true, nil
    }
    if len(owner_list) == 1 { return owner_list[0], true, nil }
    return "", false, owner_list
}

// Populate a fun's field_map from its fields array for O(1) field lookup.
build_field_map :: proc(st: ^Scope_Body) {
    for f, i in st.fields {
        st.field_map[f.name] = i
    }
}

// Populate a callable fun's field_map from its params for O(1) param lookup.
build_param_map :: proc(ft: ^Type_Scope) {
    for p, i in ft.params {
        if p.name != "" {
            ft.field_map[p.name] = i
        }
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
    // Dispatches and operator overloads stay on the used module (see
    // Scope_Body.dispatch_groups): a lookup walks the includes at its call.
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

// find_dispatch collects all functions associated with a dispatch group `name`,
// visible at `env`: the current module's own dispatches (c.dispatch_groups),
// then those of the modules used along the chain. Multiple modules may
// contribute candidates to the same dispatch name; all matches are merged so a
// stdlib dispatch (e.g. `sqrt :: dispatch { sqrt_f32, sqrt_f64 }`) can be
// extended by user code that uses the stdlib module. Non-transitive: a used
// module's own uses are not followed.
find_dispatch :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if fns, ok := c.dispatch_groups[name]; ok {
        for f in fns { append(&result, f) }
    }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc != nil {
                if fns, ok := inc.dispatch_groups[name]; ok {
                    for f in fns { append(&result, f) }
                }
            }
        }
    }
    return result, len(result) > 0
}

// find_operator_overload mirrors find_dispatch for `overload OP name` decls.
find_operator_overload :: proc(c: ^Checker, env: ^Type_Scope, op: Token_Kind) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if names, ok := c.operator_overloads[op]; ok {
        for n in names { append(&result, n) }
    }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc != nil {
                if names, ok := inc.operator_overloads[op]; ok {
                    for n in names { append(&result, n) }
                }
            }
        }
    }
    return result, len(result) > 0
}
