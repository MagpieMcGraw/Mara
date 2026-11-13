package mara

import "core:fmt"

// Definitions in a scope — a module's, a struct's methods and types, a
// fun's own: funs, structs, enums, error sets, distinct types, aliases,
// constants, dispatch groups, foreign funs. Each is named for the scope that
// defines it (`Arena_mark`, `mara_core_Arena`), declared in it (a method sees
// its struct's names; no body sees another's locals), and a fun or struct
// checked as its own body.

// What a scope defines is the name table's list (names_defs): its own
// statements' definitions and its blocks' — an if's, a loop's, a match arm's, a
// defer's; a module's, its files'. A block's is its body's definition like
// any other, checked with it; in sight in its block alone, and no member of
// its body's owner.

// A definition's name as its owner files it: as written; a block's, with
// its number (`Input__2`) — two blocks' of one name are two.
tc_def_name :: proc(k: ^TC, def: Tree_Id) -> string {
    name := tc_name(k, def)
    if bd, in_block := names_block(k.names, def); in_block { return fmt.aprintf("%s__%d", name, bd.block) }
    return name
}

// A scope's definitions, registered (once): each one's name declared and its
// type made, then — every name of the scope's known — each distinct type's
// base, each fun's and struct's signature, each union's variants.
tc_register_defs :: proc(k: ^TC, sc: ^TC_Scope) {
    if sc.registered { return }
    sc.registered = true
    t := k.t
    owner := sc.ts
    owner_i := k.scope_of[owner]
    distincts := make([dynamic]Tree_Id, context.temp_allocator)
    unions := make([dynamic]Tree_Id, context.temp_allocator)
    dispatches := make([dynamic]Tree_Id, context.temp_allocator)
    for def in names_defs(k.names, owner.decl, owner.name) {
        s := def.node
        if t.tag[s] == .Foreign {
            append(&sc.foreigns, s)
            continue
        }
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
                append(&dispatches, s)   // (the name table's, as a module's: its members checked once declared)
                continue
            case .Import:
                continue   // (`name :: use m`: checked before its module — tc_check_uses)
            }
        }
        if tc_name_alias(k, s) {
            tc_register_distinct(k, s, value, owner)
            append(&distincts, s)
            continue
        }
        if value != 0 && !tc_is_definition(t.tag[value]) {
            tc_register_const(k, s, value, sc)
            continue
        }
        tc_unsupported(k, s, "this definition")
    }
    // (A foreign fun's types, a distinct type's base: once every name here
    // is declared.)
    for s in sc.foreigns { tc_register_foreign(k, s, sc.ts.name) }
    for s in distincts { tc_resolve_distinct(k, s, Tree_Id(t.b[s])) }
    for s in distincts { tc_alias_sight(k, s, owner) }
    for i in k.scopes[owner_i].nested { tc_signature(k, k.scopes[i]) }
    // (A union's variants' fields: their bodies, checked — once the scope's
    // funs have their signatures, for one to call.)
    for s in unions { tc_resolve_union(k, s, Tree_Id(t.b[s])) }
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
