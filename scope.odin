package mara

import "core:strings"

// ---------------------------------------------------------------------------
// Type environment (scope chain)
// ---------------------------------------------------------------------------

// Type_Env is GONE. It was a transient per-scope handle carrying resolution state
// during checking; over the teardown every field it held moved onto the durable
// graph or out to a post-check pass (types -> the scope graph; parent -> the
// parent_scope chain; class/fun_scope, is_module_scope, block_scope -> derived
// from scope kind/is_module; return_types -> enclosing_return_types; includes ->
// Scope_Body.includes; bindings -> the escape/flow pass frame stacks). Once it was
// a one-field wrapper `{ scope }`, the wrapper itself was redundant: `env` IS the
// durable ^Type_Scope it pointed at. The checker now threads ^Type_Scope directly
// as the "current scope" handle, walking parent_scope for resolution and
// registering top-level names straight onto the scope.

// Durable scope-member lookup: a scope's nested types + funs live on its
// Does scope `s` define `name` directly (its own types or functions)? One level,
// no parent_scope walk — the durable equivalent of a single env's own .types.
scope_defines :: proc(s: ^Type_Scope, name: string) -> (Type, bool) {
    if s == nil { return nil, false }
    if s.types != nil { if t, ok := s.types[name]; ok { return t, true } }
    if s.functions != nil { if f, ok := s.functions[name]; ok && f != nil { return f, true } }
    return nil, false
}

// True if this env is a module/package namespace — name lookup terminates here.
// Derived purely from the durable scope: each file now gets its OWN .Block scope
// chained to the module (partition_package_files), so a file scope is never the
// module scope — `is_module` alone distinguishes them, no env-identity back-ref.
env_is_module :: proc(env: ^Type_Scope) -> bool {
    return env != nil && env != nil && env.is_module
}

// Look up a bare name exported by an included module — off the module's own
// DURABLE scope (inc.types), which check_module finalizes to the full name
// surface (types + funs + distincts + const/late-bound types) at the end of the
// module's check. A scope holds its names; resolution reads them there.
include_lookup :: proc(inc: ^Scope_Body, name: string) -> (Type, bool) {
    if inc == nil { return nil, false }
    if t, ok := inc.types[name]; ok { return t, true }
    return nil, false
}

// Block-scoped LOCAL lookup over the DURABLE scope graph — the migration target
// for the env.parent walk. From the starting block scope, walk parent_scope
// checking each .Block's locals (.types) and STOP at the first non-.Block (the
// enclosing fun/ctor/struct). The stop encodes "no closures": a block sees its
// own + enclosing blocks' + the function's top-level locals (all .Block scopes),
// but never an outer function's. Members (nested ::types/funs) are NOT here —
// that is scope_member's job, walking past the function boundary.
scope_local_lookup :: proc(start: ^Type_Scope, name: string) -> (Type, bool) {
    for s := start; s != nil && s.kind == .Block; s = s.parent_scope {
        if s.types != nil {
            if t, ok := s.types[name]; ok { return t, true }
        }
    }
    return nil, false
}

// THE durable name-lookup walk: from the current scope up the parent_scope graph
// (own .types/.functions at each level — definitions beat includes), then bare
// includes up the env chain. Returns the SCOPE the name was found in (nil for an
// include hit or a not-found), so callers can ask "was this a field of an
// enclosing class?" without an env back-reference.
//
// `below_module` stops BEFORE the enclosing module scope — the `:=` shadowing
// policy, so a local `shader := gl.CreateShader(...)` doesn't conflate with the
// module's own auto-injected binding.
// Bare-included names via the DURABLE scope graph: walk parent_scope, check each
// scope's own includes, stop at the module. The migration target for the legacy
// env.parent + cur.includes walk (now that decls chain through their file scope,
// the scope chain reaches every include-holding scope the env chain did).
// A block's names are its locals, seen only from inside its own function
// (scope_local_lookup). Past a function boundary a block shows just the
// modules it names (a file's `gl :: use mara.open_gl`): a function sees the
// outside world through its arguments, never an enclosing scope's locals —
// a module's variables included, since a module is a scope like any other.
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

scope_includes_lookup :: proc(env: ^Type_Scope, name: string, below_module: bool) -> (Type, bool) {
    for s := env; s != nil; s = s.parent_scope {
        if below_module && s.is_module { break }
        for inc in s.includes { if t, ok := include_lookup(inc, name); ok { return t, true } }
        if s.is_module { break }
    }
    return nil, false
}

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

// THE name-lookup walk (type_env_get / type_env_locate_below_module are thin
// wrappers). LOCALS first over the block-scope graph (stops at the function
// boundary — no closures), then the durable scope_resolve walk (enclosing class
// members + module names + bare includes). Returns the SCOPE the name was found
// in — nil for a local or an include hit — so the field-leak guards can ask
// "is this a field of an enclosing class?" (a non-module .Struct scope).
//
// This is the env→scope-graph switch: name resolution no longer reads env.types;
// it walks the durable parent_scope graph that runs parallel to the env chain.
type_env_locate :: proc(env: ^Type_Scope, name: string, below_module := false) -> (Type, ^Type_Scope, bool) {
    // LOCALS first: scope_local_lookup self-guards on .Block (the env's scope is a
    // .Block iff this is a block body), so an enclosing fun/class/module scope
    // stops the walk immediately and falls through to scope_resolve.
    if t, ok := scope_local_lookup(env, name); ok {
        return t, nil, true  // a local never lives in a class namespace
    }
    return scope_resolve(env, name, below_module)
}

type_env_get :: proc(env: ^Type_Scope, name: string) -> (Type, bool) {
    t, _, ok := type_env_locate(env, name)
    return t, ok
}

type_env_locate_below_module :: proc(env: ^Type_Scope, name: string) -> (Type, ^Type_Scope, bool) {
    return type_env_locate(env, name, below_module = true)
}

// Resolve a bare name across env-chain own definitions and includes, with
// ambiguity detection. Returns:
//   - typ, ok=true:                name resolves unambiguously
//   - ok=false, ambiguous_owners:  name has multiple include matches at the
//                                  same lookup level (caller should error)
//   - ok=false, nil ambiguous:     name not found anywhere
//
// Own definitions in any enclosing scope still win over imports — those are
// never ambiguous because the user explicitly wrote the local definition.
// Ambiguity only fires when the name comes from imports and 2+ imports
// expose it (e.g. `include mara.sdl3 + include mara.sdl2`, both with
// `PollEvent`).
//
// Variant aliases (enum entries written into env.types so `Init_Flags.Timer`
// can be referenced bare as `Timer` in expression position) are filtered out
// when a real type with the same name is also visible — the user almost
// always means the type. If only variant aliases remain, fall back to one
// of them so the original variant-shorthand semantics still work.
resolve_with_ambiguity :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> (typ: Type, ok: bool, ambiguous_owners: [dynamic]string) {
    // `Self` is the enclosing struct/fun's own scope — derive it from the durable
    // graph (the nearest class_scope/fun_scope marker) rather than an env binding.
    if name == "Self" {
        if s := enclosing_callable_scope(env); s != nil { return s, true, nil }
        return nil, false, nil
    }
    // An OWN definition (a local type, an enclosing class member, or a module
    // definition) wins unambiguously over any import — walk the durable scope
    // graph own-only, inner-to-outer (lexical shadowing built in).
    for s := env; s != nil; s = s.parent_scope {
        if t, found := scope_defines(s, name); found {
            typ, ok = t, true
            break
        }
    }
    if !ok {
        // No own definition: gather distinct include owners at the nearest env
        // level that provides the name (the per-level stop). Two+ distinct
        // imports of the same name = ambiguous; the caller errors.
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

type_env_set :: proc(s: ^Type_Scope, name: string, t: Type) {
    // Names live on the durable scope graph — what resolution walks.
    if s != nil {
        if s.types == nil { s.types = make(map[string]Type) }
        s.types[name] = t
    }
}

type_env_child :: proc(parent: ^Type_Scope) -> ^Type_Scope {
    // Every child scope is chained to the parent's, so the durable graph carries
    // the nesting. Specific creators (block/ns/module) use a concrete scope
    // directly; this is the default shadow.
    s := new(Type_Scope)
    s.parent_scope = parent
    return s
}

// Like type_env_child but also mints the durable .Block Type_Scope this block
// env shadows, linked into the parent_scope graph at the nearest enclosing scope
// (a containing block if there is one, else the enclosing fun/ctor). Used at the
// if/for/defer block sites; locals declared in the block land on bs.types via
// type_env_set. Additive for now — name lookup still runs off the env chain; the
// block scope is built so the kind-gated parent_scope walk can be validated
// against it before the env walk is retired.
type_env_block_child :: proc(parent: ^Type_Scope) -> ^Type_Scope {
    child := type_env_child(parent) // minted, parent_scope = parent
    // The minted durable scope IS the block scope. parent already equals the
    // nearest enclosing scope (a containing block, else the enclosing fun/ctor),
    // so the chain matches the old enclosing-scope link.
    child.kind = .Block
    return child
}

// The enclosing function's user name (for #caller_name), read from the DURABLE
// scope graph — the nearest fun/ctor's Type_Scope — instead of a per-env mirror.
// (Frame-lift: Type_Env no longer carries an fn_name copy.)
enclosing_fn_name :: proc(env: ^Type_Scope) -> string {
    if s := enclosing_callable_scope(env); s != nil {
        return s.source_name if s.source_name != "" else s.name
    }
    return "main" // top-level code runs in main
}

// The expected return types of the nearest enclosing function / constructor body,
// A callable scope: a fun, or a non-module struct/class (a ctor body). Modules
// are .Struct too but never a callable. This is what the old class_scope/fun_scope
// env markers identified — they were always set to the env's own .scope, which is
// a non-module struct (class defs layer) or a fun. Derive instead of storing.
scope_is_callable :: proc(s: ^Type_Scope) -> bool {
    return s != nil && (s.kind == .Fun || (s.kind == .Struct && !s.is_module))
}

// The module scope at the top of a scope's parent_scope chain (the durable
// equivalent of "walk env.parent to the root env"). nil if `s` is nil.
module_scope :: proc(start: ^Type_Scope) -> ^Type_Scope {
    s := start
    for s != nil && s.parent_scope != nil { s = s.parent_scope }
    return s
}

// Register a (mangled) name persistently on the module scope.
register_on_module :: proc(root: ^Type_Scope, name: string, t: Type) {
    if root == nil { return }
    if root.types == nil { root.types = make(map[string]Type) }
    root.types[name] = t
}

// The struct scope this env's block sits DIRECTLY inside (its scope's immediate
// parent), or nil — for "is this decl in a struct body" (a field decl).
parent_struct_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil || env == nil { return nil }
    p := env.parent_scope
    if p != nil && p.kind == .Struct && !p.is_module { return p }
    return nil
}

// DERIVED from the durable scope graph: walk from this env's scope up parent_scope
// to the nearest callable (fun/ctor) and read its return_types. Empty = void.
enclosing_return_types :: proc(env: ^Type_Scope) -> []Type {
    if env == nil { return nil }
    for s := env; s != nil; s = s.parent_scope {
        if scope_is_callable(s) { return s.return_types[:] }
    }
    return nil
}

// The nearest enclosing callable scope — the fun / ctor whose body we're checking.
// The "caller" for call-graph edges. nil at module level (a call in a top-level
// const value etc. has no enclosing function node). Walks the durable scope graph.
enclosing_callable_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil { return nil }
    for s := env; s != nil; s = s.parent_scope {
        if scope_is_callable(s) { return s }
    }
    return nil
}





// Build "prefix_name" without fmt.tprintf (avoids temp allocator overhead).
// Returns name unchanged if prefix is empty.
make_flat_name :: proc(prefix, name: string) -> string {
    if prefix == "" { return name }
    // Module names may be dotted (e.g. "mara.math"); LLVM symbol names use
    // underscore as the separator, so convert dots in the prefix.
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
            qual_type, found := type_env_get(env, qualifier)
            if found {
                if mod_sd := as_scope_body(qual_type); sd_is_module(mod_sd) {
                    return make_flat_name(mod_sd.name, bare_name)
                }
            }
        }
        return ""
    }
    // Walk the env chain (own types + includes) to find which module owns
    // this bare name. This matches the actual visibility for the call site,
    // which is important when two modules export the same name (e.g. `Event`
    // in both mara_sdl and mara_sdl2).
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

// Like resolve_fn_home but reports ambiguity when 2+ visible includes provide
// the same function name. Mirrors resolve_with_ambiguity for type names —
// own definitions in any enclosing scope still win unambiguously; ambiguity
// only fires when the name comes from imports and 2+ imports expose it
// (e.g. `include mara.sdl + include mara.sdl2`, both with PollEvent).
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
// visible enums/unions. We deliberately do NOT bind variants as bare names in
// any env: bare variant resolution must go through an expected type.
register_enum_variants :: proc(c: ^Checker, et: ^Type_Enum, env: ^Type_Scope, enum_key: string = "", skip_func_names := false, public_env: ^Type_Scope = nil) {
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


// flatten_module_exports — make an included module's exports reachable in the
// includer's scope. Both bare `include path` and named `name :: include path`
// call this; the only difference between them is whether the module is also
// addressable by an alias (named) or by its own bare name (bare). Without this
// step, `name :: include path` would force qualified `name.X` access for every
// member, which makes stdlib swaps (SDL3 → SDL2 et al.) ripple through every
// caller — see TODO note on module aliasing.
flatten_module_exports :: proc(c: ^Checker, env: ^Type_Scope, mod_sd: ^Scope_Body, mod_name: string, is_aliased := false, is_sealed := false) {
    assert(sd_is_module(mod_sd), "module-struct must have scope")
    // Sealed includes (`name :: sealed include path`) skip the env.includes
    // append AND the c.declared_funs writes — bare names from the included
    // module are not made available at the call site, only `name.X` access.
    // Used to keep colliding bindings (SDL2 vs SDL3, etc.) properly isolated.
    if is_sealed { return }
    if env != nil { append(&env.includes, mod_sd) }
    for name, t in mod_sd.types {
        if name == "void" { continue }  // don't re-export the void null-pointer literal
        if tf, is_func := t.(^Type_Scope); is_func && (len(tf.params) > 0 || tf.has_parens) {
            c.declared_funs[name] = true
        }
    }
    // Dispatches and operator overloads stay on the included module's struct
    // (see Scope_Body.dispatch_groups). Lookups in the includer walk
    // env.includes (the durable module scopes) at call time, so we don't merge
    // here — matches the non-transitive include semantics used elsewhere.
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
    // Own definitions + each scope's includes up the durable scope graph.
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
// visible at `env`. Sources walked: the current module's own dispatches
// (c.dispatch_groups), then bare-`include`d modules' dispatches via env.includes.
// Multiple modules may contribute candidates to the same dispatch name; all
// matches are merged so a stdlib dispatch (e.g. `sqrt :: dispatch { sqrt_f32,
// sqrt_f64 }`) can be extended by user code that includes the stdlib module.
// Non-transitive: we don't follow inc.includes — re-export of re-exports is
// opt-in (the user would `include` again themselves), matching type_env_get.
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

