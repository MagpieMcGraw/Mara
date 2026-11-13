package mara

import "core:strings"

// Constants in the checker: `X :: v`, `X : T : v`. Each is its value,
// checked once — in its module's order, or sooner by a use — and built as
// its own code by lowering (lw_const); a use is the constant's value (a table's
// global, when it is an aggregate), named by its value's node.

TC_Const :: struct {
    def, value, ann: Tree_Id,
    name:  string,          // as written
    mangled: string,        // its symbol: named for the scope that defines it (`main_K`, `mara_core_KB`)
    sid:   Syntax_Id,       // its value's, as the builder keys it (an instance's its own)
    owner: ^Type_Scope,     // the scope that defines it: a module, a fun, a struct
    pkg:   string,
    t:     Type,
    state: Resolution_State,
    visiting: bool,         // its value being checked or folded: a use in it is a cycle
}

// A constant checked (once).
tc_check_const :: proc(k: ^TC, kc: ^TC_Const) {
    if kc.state != .Unresolved { return }
    kc.state = .In_Progress
    tc_event(k, {kind = .Const, kc = kc})
    defer kc.state = .Resolved
    // (Checked as its scope's code, wherever its first use is.)
    outer_body := k.body
    k.body = kc.owner
    defer k.body = outer_body
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
    if !is_any(ann) {
        if types_incompatible(ann, vt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE, type_name(vt), kc.name, type_name(ann))
        }
        tc_value_at(k, kc.value, vt, ann, span)
        final = ann
    }
    kc.t = final
    tc_bound_set(k, k.t.main[kc.def], final)
}

// A module's name as code qualifies with it: `mara.os`'s is `os`, as in
// `os.clock_ns()`. (`mara.os.clock_ns()` doesn't parse as a module's: `mara`
// is no name.)
module_short_name :: proc(module: string) -> string {
    if at := strings.last_index_byte(module, '.'); at >= 0 { return module[at + 1:] }
    return module
}

// A scope's constant: by the token that declares it, and by its symbol —
// named for the scope that defines it (`main_K`, `mara_core_KB`), the name
// the builder's table takes; bound in its scope's body once checked.
tc_register_const :: proc(k: ^TC, def, value: Tree_Id, sc: ^TC_Scope) {
    name := tc_name(k, def)
    filed := tc_def_name(k, def)
    mangled := make_flat_name(sc.ts.name, filed)
    kc := new_clone(TC_Const{def = def, value = value, ann = Tree_Id(k.t.a[def]), name = name, mangled = mangled, pkg = k.pkg, owner = sc.ts})
    kc.sid = tc_sid(k, value)
    k.const_at[k.t.main[def]] = kc
    k.consts[mangled] = kc
    append(&sc.consts, kc)
}

// A body's constants, checked before its code — each a member of its owner
// too, for its methods.
tc_check_local_consts :: proc(k: ^TC, sc: ^TC_Scope) {
    for kc in sc.consts {
        tc_check_const(k, kc)
        tc_scope_bind(k, sc.ts, kc.mangled, kc.t, {k.t.main[kc.def], .Const})
        if _, in_block := names_block(k.names, kc.def); !in_block { tc_scope_bind(k, sc.ts, kc.name, kc.t, {k.t.main[kc.def], .Const}) }   // (a block's: no member)
    }
}

