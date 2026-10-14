package mara

import "core:fmt"

// Definitions in a body: a struct's methods and types, a fun's own funs and
// structs. Each is named for its owner (`Arena_mark`), declared in its
// owner's scope (a method sees its struct's names; no body sees another's
// locals), and checked as its own body.

// A body's definitions, registered (once): each fun's and struct's type made
// and its signature resolved.
tc_register_defs :: proc(k: ^TC, sc: ^TC_Scope) {
    if sc.registered { return }
    sc.registered = true
    t := k.t
    owner := sc.ts
    owner_i := k.scope_of[owner]
    for s in tc_live(k, scope_view(t, sc.node).body) {
        if t.tag[s] != .Define { continue }
        value := Tree_Id(t.b[s])
        if t.a[s] == 0 && value != 0 && (t.tag[value] == .Fun_Def || t.tag[value] == .Struct_Def) {
            tc_register_nested(k, s, value, owner, owner_i)
            continue
        }
        if value != 0 && !tc_is_definition(t.tag[value]) {
            tc_register_local_const(k, s, value, sc)
            continue
        }
        tc_unsupported(k, s, "a definition in a body")
    }
    for i in k.scopes[owner_i].nested { tc_signature(k, k.scopes[i]) }
}

tc_register_nested :: proc(k: ^TC, def, node: Tree_Id, owner: ^Type_Scope, owner_i: int) {
    t := k.t
    name := tc_name(k, def)
    span := tree_span(t, def)
    v := scope_view(t, node)
    is_struct := t.tag[node] == .Struct_Def
    if tc_is_generic(k, node) {
        tc_unsupported(k, def, "a generic definition in a body")
        return
    }
    if is_struct && len(v.returns) > 0 && len(v.params) == 0 {
        tc_error(k, span, TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN, name)
        return
    }
    mangled := fmt.aprintf("%s_%s", owner.name, name)
    ts := new(Type_Scope)
    ts.name, ts.source_name, ts.home_package = mangled, name, k.pkg
    ts.kind = .Struct if is_struct else .Fun
    ts.node, ts.parent_scope = node, owner
    ts.decl = t.main[def]
    ts.has_parens = build_tokens[t.main[node] + 1].kind == .Left_Paren
    ts.is_packed = v.packed != 0
    callable := !is_struct || len(v.params) > 0
    if is_struct {
        if callable { k.table.funs[mangled] = ts } else { k.table.structs[mangled] = ts }
        tc_scope_bind(k, owner, name, ts, {ts.decl, .Type})
    }
    // (Its mangled name the module's, where codegen and a qualified use find it.)
    tc_scope_bind(k, module_scope(owner), mangled, ts, {ts.decl, .Type if is_struct else .Fun})
    if callable {
        k.c.declared_funs[mangled] = true
        if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
        owner.functions[name] = ts
    }
    k.scope_of[ts] = len(k.scopes)
    append(&k.scopes[owner_i].nested, len(k.scopes))
    append(&k.scopes, new_clone(TC_Scope{ts = ts, def = def, node = node, env = owner}))
}

// A body's definitions checked: its structs' bodies (their fields), then its
// funs'.
tc_check_defs :: proc(k: ^TC, sc: ^TC_Scope) {
    hint := k.hint
    defer k.hint = hint
    nested := sc.nested[:]
    for i in nested { tc_struct_ensure(k, k.scopes[i].ts) }
    for i in nested {
        if k.scopes[i].ts.kind == .Fun { tc_scope_body(k, k.scopes[i]) }
    }
}
