package mara

import "core:strings"

// Modules in the checker: `use m` checks m (once, where it is first
// used — its own uses first), then makes its names visible in the file
// that uses it (`include m`: in its module too); `name :: use m` names it.

tc_use :: proc(k: ^TC, imp: Tree_Id, env, mod: ^Type_Scope, alias := Token_Id(0)) -> ^Type_Scope {
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
    flatten_module_exports(k.c, env, &m.sd, is_sealed = sealed)
    if reexport && mod != env {
        flatten_module_exports(k.c, mod, &m.sd, is_sealed = sealed)
    }
    // (Its name the alias, else its path's last part: the token that declares it.)
    parts := tree_token_list(t, t.a[imp])
    decl := alias if alias != 0 else parts[len(parts) - 1]
    scope_bind(env, tc_text(decl), m, {decl, .Module})
    scope_bind(k.root, path, m, {decl, .Module})
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
    outer: ^Graph_Body
    if k.gb != nil { outer, k.gb.body = k.gb.body, nil }
    defer if k.gb != nil { k.gb.body = outer }
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
        if bt, ok := scope_defines(k.root, builtin); ok { scope_bind(m, builtin, bt, {kind = .Builtin}) }
    }
    if _, has_void := scope_defines(m, "void"); !has_void {
        scope_bind(m, "void", new_clone(Type_Ptr{elem = Type_Any{}}), {kind = .Builtin})
    }
    saved_pkg, saved_hint := k.pkg, k.hint
    saved_dispatch, saved_overloads := k.c.dispatch_groups, k.c.operator_overloads
    k.pkg = name
    k.c.dispatch_groups, k.c.operator_overloads = {}, {}
    list := tc_check_module_files(k, files, m)
    // (Its dispatches and overloads stay its own: a `use` of it reaches them.)
    m.dispatch_groups, m.operator_overloads = k.c.dispatch_groups, k.c.operator_overloads
    k.c.dispatch_groups, k.c.operator_overloads = saved_dispatch, saved_overloads
    k.pkg, k.hint = saved_pkg, saved_hint
    delete_key(&k.in_progress, name)
    tc_extract(k, list, name, is_main = false)
    k.checked_modules[name] = m
    k.table.funs[name] = m
    // (A stdlib module is `std`'s member by its last name: `math.sin`.)
    if strings.has_prefix(name, "mara.") {
        scope_bind(k.std, name[len("mara."):], m, {kind = .Module})
    } else {
        scope_bind(k.root, name, m, {kind = .Module})
    }
    return m
}

// A module's variables: its file's block's locals — typed (by what is
// written, else by its value), no function sees them (one that reaches for
// one is told so: report_unresolved).
tc_module_decl :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    v := decl_view(t, s)
    span := tree_span(t, s)
    ann: Type
    if v.type_ != 0 { ann = tc_type(k, v.type_, env, span) }
    for tg, i in v.targets {
        vt: Type = Type_Error{}
        if i < len(v.values) { vt = solidify_type(tc_check(k, v.values[i], env)) }
        scope_bind(env, tc_name(k, tg), ann if ann != nil else vt, {t.main[tg], .Global})
        tc_set_ref(k, tg, {t.main[tg], .Global})
    }
}
