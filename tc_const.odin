package mara

import "core:strings"

// Constants in the checker: `X :: v`, `X : T : v`. Each is its value,
// checked once — in its module's order, or sooner by a use — and built as
// its own code by lowering (lw_const); a use is the constant's value (a table's
// global, when it is an aggregate), named by its value's node.

TC_Const :: struct {
    def, value, ann: Tree_Id,
    name:  string,          // as written
    mangled: string,        // a body's: named for its owner
    sid:   Syntax_Id,       // its value's, as the builder keys it (an instance's its own)
    local: bool,            // a body's (its type its value's)
    env:   ^Type_Scope,     // where its value is checked
    pub:   ^Type_Scope,     // where its name is bound
    pkg:   string,
    t:     Type,
    state: Resolution_State,
    visiting: bool,         // its value being checked or folded: a use in it is a cycle
}

// A module's constant: under its flat name, and its bare one unless another
// module has a constant of that name (then a bare use must qualify it).
tc_register_const :: proc(k: ^TC, def, value: Tree_Id, env, mod: ^Type_Scope) {
    name := tc_name(k, def)
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, env = env, pub = mod, pkg = k.pkg})
    kc.sid = tc_sid(k, value)
    k.consts[make_flat_name(k.pkg, name)] = kc
    if owner, mapped := k.const_owners[name]; mapped {
        if owner != k.pkg { k.const_owners[name] = "" }
    } else {
        k.const_owners[name] = k.pkg
        k.consts[name] = kc
    }
}

// A constant checked (once).
tc_check_const :: proc(k: ^TC, kc: ^TC_Const) {
    if kc.state != .Unresolved { return }
    kc.state = .In_Progress
    tc_event(k, {kind = .Const, kc = kc})
    defer kc.state = .Resolved
    t := k.t
    span := tree_span(t, kc.def)
    hint := k.hint
    defer k.hint = hint
    ann: Type = Type_Any{}
    if kc.ann != 0 { ann = tc_type(k, kc.ann, kc.env, span) }
    k.hint = ann if !is_any(ann) else nil
    vt := tc_check(k, kc.value, kc.env)
    final := vt
    if !is_any(ann) && !kc.local {
        if types_incompatible(ann, vt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE, type_name(vt), kc.name, type_name(ann))
        }
        if is_infer(vt) { tc_literal_overflow(k, kc.value, ann, span) }
        final = ann
    }
    kc.t = final
    scope_bind(kc.pub, kc.name, final, {k.t.main[kc.def], .Const})
}

// The constant a bare name names from `env`: its own module's, or one it
// uses'. Two such is ambiguous (reported: its uses must qualify it).
tc_const_ref :: proc(k: ^TC, env: ^Type_Scope, name: string, span: Span) -> (^TC_Const, bool) {
    own := ""
    for s := env; s != nil; s = s.parent_scope {
        if s.home_package != "" { own = s.home_package; break }
        if s.is_module { break }
    }
    if own == "" { own = k.pkg }
    seen := make(map[string]bool, context.temp_allocator)
    seen[own] = true
    found: ^TC_Const
    count := 0
    if kc, ok := k.consts[make_flat_name(own, name)]; ok { found, count = kc, 1 }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc == nil || seen[inc.name] { continue }
            seen[inc.name] = true
            if kc, ok := k.consts[make_flat_name(inc.name, name)]; ok { found, count = kc, count + 1 }
        }
        if s.is_module { break }
    }
    if count < 2 { return found, true }
    owners := make([dynamic]string, context.temp_allocator)
    suffix := strings.concatenate({"_", name})
    for key in k.consts {
        if key == name || !strings.has_suffix(key, suffix) { continue }
        pkg := key[:len(key) - len(suffix)]
        if strings.has_prefix(pkg, "mara_") { pkg = strings.concatenate({"mara.", pkg[len("mara_"):]}) }
        append(&owners, pkg)
    }
    first := owners[0] if len(owners) > 0 else name
    tc_error(k, span, TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED, name, strings.join(owners[:], ", "), first, name)
    return nil, false
}

// Whether a module's constant is visible from env by its bare name: its own
// module's, or one a module it uses defines.
tc_const_visible :: proc(k: ^TC, env: ^Type_Scope, name: string) -> bool {
    if env == nil { return true }
    if owner, mapped := k.const_owners[name]; mapped && owner != "" && owner == k.pkg { return true }
    for s := env; s != nil; s = s.parent_scope {
        if s.is_module && make_flat_name(k.pkg, name) in k.consts { return true }
        for inc in s.includes {
            if inc != nil && make_flat_name(inc.name, name) in k.consts { return true }
        }
        if s.is_module { break }
    }
    return false
}

// A body's constant: named for its owner (`main_K`) and by itself, the
// names the builder's tables take; bound in its owner's body once checked.
tc_register_local_const :: proc(k: ^TC, def, value: Tree_Id, sc: ^TC_Scope) {
    name := tc_name(k, def)
    mangled := strings.concatenate({sc.ts.name, "_", name})
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, mangled = mangled, pkg = k.pkg, local = true})
    kc.sid = tc_sid(k, value)
    k.consts[mangled] = kc
    k.consts[name] = kc
    append(&sc.consts, kc)
    // (A use in its owner's methods finds it through its owner: its scope's.)
    owner := sc.ts
    if owner not_in k.scope_consts { k.scope_consts[owner] = make(map[string]^TC_Const) }
    (&k.scope_consts[owner])[name] = kc
}

// A body's constants, checked in its scope (where its own names are, before
// its code), each bound there — and in its owner, for its methods.
tc_check_local_consts :: proc(k: ^TC, sc: ^TC_Scope, body: ^Type_Scope) {
    if len(sc.consts) == 0 { return }
    if body not_in k.scope_consts { k.scope_consts[body] = make(map[string]^TC_Const) }
    for kc in sc.consts {
        kc.env, kc.pub = body, body
        tc_check_const(k, kc)
        scope_bind(body, kc.mangled, kc.t, {k.t.main[kc.def], .Const})
        scope_bind(sc.ts, kc.mangled, kc.t, {k.t.main[kc.def], .Const})
        scope_bind(sc.ts, kc.name, kc.t, {k.t.main[kc.def], .Const})
        (&k.scope_consts[body])[kc.name] = kc
    }
}

// The body's constant a name found as a local, or in a scope, names: the
// blocks out to its fun's body, or the scope it was found in.
tc_local_const :: proc(k: ^TC, env: ^Type_Scope, loc: ^Type_Scope, name: string) -> ^TC_Const {
    if loc == nil {
        for s := env; s != nil; s = s.parent_scope {
            if cs, ok := k.scope_consts[s]; ok {
                if kc, has := cs[name]; has { return kc }
            }
            if s.kind != .Block { break }
        }
        return nil
    }
    if loc.is_module { return nil }
    if cs, ok := k.scope_consts[loc]; ok { return cs[name] or_else nil }
    return nil
}
