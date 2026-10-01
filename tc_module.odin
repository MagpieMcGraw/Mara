package mara

import "core:strings"

// Modules in the new checker: `use m` checks m (once, where it is first
// used — its own uses first), then makes its names visible in the file
// that uses it (`include m`: in its module too); `name :: use m` names it.

tc_use :: proc(k: ^TC, imp: Tree_Id, env, mod: ^Type_Scope, alias := "") -> ^Type_Scope {
    t := k.t
    span := tree_span(t, imp)
    path := tc_path(k, imp)
    reexport := build_tokens[t.main[imp]].kind == .Include
    sealed := t.b[imp] != 0
    if path not_in k.modules {
        tc_error(k, span, TYPE_MODULE_FOUND, path)
        return nil
    }
    m := tc_check_module(k, path, span)
    if m == nil { return nil }
    flatten_module_exports(k.c, env, &m.sd, path, is_aliased = alias != "", is_sealed = sealed)
    if reexport && mod != env {
        flatten_module_exports(k.c, mod, &m.sd, path, is_aliased = alias != "", is_sealed = sealed)
    }
    type_env_set(env, alias if alias != "" else tc_use_name(k, imp), m)
    type_env_set(k.root, path, m)
    return m
}

// The name a bare `use a.b` gives its module: its last part.
tc_use_name :: proc(k: ^TC, imp: Tree_Id) -> string {
    parts := tree_token_list(k.t, k.t.a[imp])
    return tc_text(parts[len(parts) - 1])
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

// A module checked: its scope (its names), its files registered and
// checked, its functions extracted. Once; a module that needs itself is a
// cycle.
tc_check_module :: proc(k: ^TC, name: string, span: Span) -> ^Type_Scope {
    // (Checked from outside any body being built: what it builds is its own.)
    outer: ^Graph_Fuse
    if k.gb != nil { outer, k.gb.fuse = k.gb.fuse, nil }
    defer if k.gb != nil { k.gb.fuse = outer }
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
    // (The build's own names — the program, std, void — every module sees.)
    for builtin in ([]string{"this_program", "Program", "std", "void"}) {
        if bt, ok := scope_defines(k.root, builtin); ok { type_env_set(m, builtin, bt) }
    }
    if _, has_void := scope_defines(m, "void"); !has_void {
        type_env_set(m, "void", new_clone(Type_Ptr{elem = Type_Any{}}))
    }
    saved_pkg, saved_hint := k.pkg, k.hint
    saved_dispatch, saved_overloads := k.c.dispatch_groups, k.c.operator_overloads
    k.pkg, k.c.current_package = name, name
    k.c.dispatch_groups, k.c.operator_overloads = {}, {}
    list := tc_check_module_files(k, files, m)
    // (Its dispatches and overloads stay its own: a `use` of it reaches them.)
    m.dispatch_groups, m.operator_overloads = k.c.dispatch_groups, k.c.operator_overloads
    k.c.dispatch_groups, k.c.operator_overloads = saved_dispatch, saved_overloads
    k.pkg, k.c.current_package, k.hint = saved_pkg, saved_pkg, saved_hint
    delete_key(&k.in_progress, name)
    tc_extract(k, list, name, is_main = false)
    k.checked_modules[name] = m
    k.table.funs[name] = m
    // (A stdlib module is `std`'s member by its last name: `math.sin`.)
    if strings.has_prefix(name, "mara.") {
        type_env_set(k.std, name[len("mara."):], m)
    } else {
        type_env_set(k.root, name, m)
    }
    return m
}
