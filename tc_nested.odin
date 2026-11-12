package mara

import "core:fmt"

// Definitions in a body: a struct's methods and types, a fun's own funs,
// structs, enums, error sets, distinct types and aliases. Each is named for
// its owner (`Arena_mark`), declared in its owner's scope (a method sees its
// struct's names; no body sees another's locals), and a fun or struct
// checked as its own body.

// A definition in a block of a body — an if's, a loop's, a match arm's, a
// defer's: which of its body's it is (1, 2, …), and its block's tokens.
// It is its body's definition like any other, checked with it; in sight in
// its block alone (the resolver's), and no member of its body's owner.
TC_Block_Def :: struct {
    n:      int,
    lo, hi: Token_Id,
}

// A body's definitions: its own statements', then its blocks' (each noted:
// k.block_defs). Not those of the funs and structs it defines: theirs.
tc_body_defs :: proc(k: ^TC, stmts: []Tree_Id, out: ^[dynamic]Tree_Id, count: ^int, block := false) {
    t := k.t
    live := tc_live(k, stmts)
    for s in live {
        #partial switch t.tag[s] {
        case .Define:
            append(out, s)
            if block && s not_in k.block_defs {
                count^ += 1
                k.block_defs[s] = {count^, t.first[live[0]], t.end[live[len(live) - 1]]}
            }
        case .If, .Elif:
            v := if_view(t, s)
            tc_body_defs(k, v.then, out, count, true)
            tc_body_defs(k, v.else_, out, count, true)
        case .For_Range, .For_Each, .For_C:
            tc_body_defs(k, for_view(t, s).body, out, count, true)
        case .For_Cond:
            tc_body_defs(k, tree_list(t, t.b[s]), out, count, true)
        case .Defer:
            tc_body_defs(k, tree_list(t, t.a[s]), out, count, true)
        case .Match:
            for arm in tree_list(t, t.b[s]) {
                tc_body_defs(k, tree_list(t, t.b[arm] if t.tag[arm] == .Arm_Value else t.a[arm]), out, count, true)
            }
        }
    }
}

// A definition's name as its owner files it: as written; a block's, with
// its number (`Input__2`) — two blocks' of one name are two.
tc_def_name :: proc(k: ^TC, def: Tree_Id) -> string {
    name := tc_name(k, def)
    if bd, in_block := k.block_defs[def]; in_block { return fmt.aprintf("%s__%d", name, bd.n) }
    return name
}

// A body's definitions, registered (once): each fun's and struct's type made
// and its signature resolved.
tc_register_defs :: proc(k: ^TC, sc: ^TC_Scope) {
    if sc.registered { return }
    sc.registered = true
    t := k.t
    owner := sc.ts
    owner_i := k.scope_of[owner]
    distincts := make([dynamic]Tree_Id, context.temp_allocator)
    unions := make([dynamic]Tree_Id, context.temp_allocator)
    dispatches := make([dynamic]Tree_Id, context.temp_allocator)
    defs := make([dynamic]Tree_Id, context.temp_allocator)
    count := 0
    tc_body_defs(k, scope_view(t, sc.node).body, &defs, &count)
    for s in defs {
        value := Tree_Id(t.b[s])
        if t.a[s] == 0 && value != 0 && (t.tag[value] == .Fun_Def || t.tag[value] == .Struct_Def) {
            tc_register_scope(k, s, value, owner, owner_i)
            continue
        }
        if t.a[s] == 0 && value != 0 {
            #partial switch t.tag[value] {
            case .Union_Def, .Error_Def:
                tc_register_union(k, s, value, owner)
                append(&unions, s)
                continue
            case .Alias_Def, .Distinct_Def:
                tc_register_distinct(k, s, value, owner)
                append(&distincts, s)
                continue
            case .Dispatch_Def:
                append(&dispatches, s)   // (the resolver's, as a module's: its members checked once declared)
                continue
            }
        }
        if tc_name_alias(k, s) {
            tc_register_distinct(k, s, value, owner)
            append(&distincts, s)
            continue
        }
        if value != 0 && !tc_is_definition(t.tag[value]) {
            tc_register_local_const(k, s, value, sc)
            continue
        }
        tc_unsupported(k, s, "a definition in a body")
    }
    // (A distinct type's base, once every name here is declared.)
    for s in distincts { tc_resolve_distinct(k, s, Tree_Id(t.b[s])) }
    for s in distincts { tc_alias_sight(k, s, owner) }
    // (A union's variants' fields, as a module's: tc_resolve_union.)
    for s in unions { tc_resolve_union(k, s, Tree_Id(t.b[s])) }
    for i in k.scopes[owner_i].nested { tc_signature(k, k.scopes[i]) }
    for s in dispatches { tc_validate(k, s) }
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
