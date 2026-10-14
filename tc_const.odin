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
    pkg:   string,
    t:     Type,
    state: Resolution_State,
    visiting: bool,         // its value being checked or folded: a use in it is a cycle
}

// A module's constant: under its flat name, and its bare one unless another
// module has a constant of that name (then a bare use must qualify it).
tc_register_const :: proc(k: ^TC, def, value: Tree_Id) {
    name := tc_name(k, def)
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, pkg = k.pkg})
    kc.sid = tc_sid(k, value)
    k.const_at[k.t.main[def]] = kc
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
    // (A module's: checked outside any body, wherever its first use is.)
    outer_body, outer_top := k.body, k.top
    if !kc.local { k.body, k.top = nil, false }
    defer k.body, k.top = outer_body, outer_top
    append(&k.annot.bodies, Annot_Body{nil, tc_instance(k, kc.value), tree_lo(k.t, kc.value), kc.value})
    t := k.t
    span := tree_span(t, kc.def)
    hint := k.hint
    defer k.hint = hint
    ann: Type = Type_Any{}
    if kc.ann != 0 { ann = tc_type(k, kc.ann, span) }
    k.hint = ann if !is_any(ann) else nil
    vt := tc_check(k, kc.value)
    final := vt
    if !is_any(ann) && !kc.local {
        if types_incompatible(ann, vt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE, type_name(vt), kc.name, type_name(ann))
        }
        tc_value_at(k, kc.value, vt, ann, span)
        final = ann
    }
    kc.t = final
    tc_bound_set(k, k.t.main[kc.def], final)
}

// Whether a bare name (n) names no constant two modules in sight have — its
// own and one it uses, or two it uses: those are ambiguous (reported: its
// uses must qualify it).
tc_const_unambiguous :: proc(k: ^TC, n: Tree_Id, name: string, span: Span) -> bool {
    owners := resolve_const_owners(k.rs, k.t.main[n], name)
    if len(owners) < 2 { return true }
    tc_error(k, span, TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED, name, strings.join(owners[:], ", ", context.temp_allocator), owners[0], name)
    return false
}

// A body's constant: named for its owner (`main_K`) and by itself, the
// names the builder's tables take; bound in its owner's body once checked.
tc_register_local_const :: proc(k: ^TC, def, value: Tree_Id, sc: ^TC_Scope) {
    name := tc_name(k, def)
    mangled := strings.concatenate({sc.ts.name, "_", name})
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, mangled = mangled, pkg = k.pkg, local = true})
    kc.sid = tc_sid(k, value)
    k.const_at[k.t.main[def]] = kc
    k.consts[mangled] = kc
    k.consts[name] = kc
    append(&sc.consts, kc)
    // (A use in its owner's methods finds it through its owner: its scope's.)
    owner := sc.ts
    if owner not_in k.scope_consts { k.scope_consts[owner] = make(map[string]^TC_Const) }
    (&k.scope_consts[owner])[name] = kc
}

// A body's constants, checked before its code — each a member of its owner
// too, for its methods.
tc_check_local_consts :: proc(k: ^TC, sc: ^TC_Scope) {
    for kc in sc.consts {
        tc_check_const(k, kc)
        tc_scope_bind(k, sc.ts, kc.mangled, kc.t, {k.t.main[kc.def], .Const})
        tc_scope_bind(k, sc.ts, kc.name, kc.t, {k.t.main[kc.def], .Const})
    }
}

