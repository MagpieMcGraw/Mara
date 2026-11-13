package mara

import "core:slice"
import "core:strings"

// Modules in the checker: a module is checked once every module it uses is
// — `use m` in any scope of it, the name table's list (names_module_uses) —
// and each use binds the name that declares it (its alias, else its path's
// last part). What it makes visible where is the name table's.

// A module's uses, each checked and its name bound: before the module is.
tc_check_uses :: proc(k: ^TC, name: string) {
    for u in names_module_uses(k.names, name) { tc_use(k, u.imp, u.alias) }
}

// A module's names, recorded in full once the modules it uses are checked
// (names_module_ready); each `all` it declares, said: a keyword.
tc_module_names_ready :: proc(k: ^TC, name: string) {
    names_module_ready(k.names, name)
    slice.sort(k.names.all_new[:])
    for tok in k.names.all_new { tc_error(k, Span{at = tok, tok = tok, end = tok + 1}, TYPE_ALL_KEYWORD) }
    clear(&k.names.all_new)
}

tc_use :: proc(k: ^TC, imp: Tree_Id, alias := Token_Id(0)) -> ^Type_Scope {
    t := k.t
    span := tree_span(t, imp)
    path := tc_path(k, imp)
    if path not_in k.modules {
        tc_error(k, span, TYPE_MODULE_FOUND, path)
        return nil
    }
    m := tc_check_module(k, path, span)
    if m == nil { return nil }
    // (Its name the alias, else its path's last part: the token that declares it.)
    parts := tree_token_list(t, t.a[imp])
    decl := alias if alias != 0 else parts[len(parts) - 1]
    tc_bound_set(k, decl, m)
    return m
}

// An import's path, its parts joined: `mara.core`.
tc_path :: proc(k: ^TC, imp: Tree_Id) -> string {
    sb := strings.builder_make()
    for part, i in tree_token_list(k.t, k.t.a[imp]) {
        if i > 0 { strings.write_byte(&sb, '.') }
        strings.write_string(&sb, tc_text(part))
    }
    return strings.to_string(sb)
}

// A module checked: its scope (its names), its body — its files' — checked,
// its functions extracted. Once; a module that needs itself is a cycle.
tc_check_module :: proc(k: ^TC, name: string, span: Span) -> ^Type_Scope {
    if m, done := k.checked_modules[name]; done { return m }
    if name in k.in_progress {
        tc_error(k, span, TYPE_CIRCULAR_INCLUDE_MODULE_ALREADY_CHECKED, name)
        return nil
    }
    files := k.modules[name]
    k.in_progress[name] = true
    m := new(Type_Scope)
    m.name, m.home_package = name, name
    m.kind = .Struct
    m.is_module = true
    k.module_scopes[name] = m
    names_module_begin(k.names, name)
    tc_check_uses(k, name)
    tc_module_names_ready(k, name)
    saved_pkg, saved_hint := k.pkg, k.hint
    k.pkg = name
    list := tc_check_module_body(k)
    k.pkg, k.hint = saved_pkg, saved_hint
    delete_key(&k.in_progress, name)
    tc_extract(k, list, name, is_main = false)
    k.checked_modules[name] = m
    k.table.funs[name] = m
    // (A stdlib module is `std`'s member by its last name: `math.sin`.)
    if strings.has_prefix(name, "mara.") {
        tc_scope_bind(k, k.std, name[len("mara."):], m, {kind = .Module})
    }
    return m
}
