package mara

import "core:strings"

// Constants in the new checker: `X :: v`, `X : T : v`. Each is its value,
// checked once — in its module's order, or sooner by a use — and built as
// its own code (graph_const_begin); a use is the constant's value (a table's
// global, when it is an aggregate), named by its value's node.

TC_Const :: struct {
    def, value, ann: Tree_Id,
    name:  string,          // as written
    env:   ^Type_Scope,     // where its value is checked
    pub:   ^Type_Scope,     // where its name is bound
    pkg:   string,
    t:     Type,
    state: Resolution_State,
}

// A module's constant: under its flat name, and its bare one unless another
// module has a constant of that name (then a bare use must qualify it).
tc_register_const :: proc(k: ^TC, def, value: Tree_Id, env, mod: ^Type_Scope) {
    name := tc_name(k, def)
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, env = env, pub = mod, pkg = k.pkg})
    k.consts[make_flat_name(k.pkg, name)] = kc
    if owner, mapped := k.const_owners[name]; mapped {
        if owner != k.pkg { k.const_owners[name] = "" }
    } else {
        k.const_owners[name] = k.pkg
        k.consts[name] = kc
    }
}

// A constant checked, its value built (once).
tc_check_const :: proc(k: ^TC, kc: ^TC_Const) {
    if kc.state != .Unresolved { return }
    kc.state = .In_Progress
    defer kc.state = .Resolved
    t := k.t
    span := tree_span(t, kc.def)
    b := k.gb
    f: ^Graph_Fuse
    if b != nil && k.c.errors == 0 && syntax_id(kc.def) not_in b.const_segs {
        f = graph_const_begin(b, tc_graph_decl(k, kc.def))
    }
    hint := k.hint
    defer k.hint = hint
    ann: Type = Type_Any{}
    if kc.ann != 0 { ann = tc_type(k, kc.ann, kc.env, span) }
    k.hint = ann if !is_any(ann) else nil
    vt: Type
    r: Fused
    if f != nil && tc_building(k) != nil {
        at := graph_dest_var(kc.name, f.root, nil if is_untyped(ann) else ann)
        vt, r = tc_expr(k, kc.value, kc.env, .Into, dest = at, temp_span = span)
    } else {
        vt = tc_check(k, kc.value, kc.env)
    }
    final := vt
    if !is_any(ann) {
        if types_incompatible(ann, vt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE, type_name(vt), kc.name, type_name(ann))
        }
        if is_infer(vt) { tc_literal_overflow(k, kc.value, ann, span) }
        final = ann
    }
    kc.t = final
    type_env_set(kc.pub, kc.name, final)
    if f != nil {
        if k.c.errors > 0 {
            graph_fuse_fail(b, f, "errors")
        } else if tc_building(k) != nil {
            tc_store(k, kc.value, vt, r, graph_dest_var(kc.name, f.root, final), span, settle = true)
        }
        graph_const_end(b, f, final)
    }
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

// A use of a constant: its value (a table's global, read; asked its place, the
// global itself).
tc_const_use :: proc(k: ^TC, kc: ^TC_Const, n: Tree_Id, t: Type, want: Fuse_Want, w: Written) -> Fused {
    b := tc_building(k)
    if b == nil || want == .None { return {} }
    span := tree_span(k.t, n)
    named := Graph_Named{value = syntax_id(kc.value)}
    if graph_aggregate(t) {
        g := graph_const_global(b, w, span, t, kc.name, named)
        if want == .Value { return {v = graph_read(b, g, t, span), ok = true} }
        return {v = g, place = true, ok = true}
    }
    if want == .Place { return {} }
    return {v = graph_named_const(b, w, span, t, kc.name, named), ok = true}
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
