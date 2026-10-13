package mara

import "core:strings"

// `foreign "lib" [prefix p] { fun Name(params) -> T }`: each a fun of C's
// calling convention, linked as prefix + name.

tc_register_foreign :: proc(k: ^TC, s: Tree_Id, env, mod: ^Type_Scope) {
    t := k.t
    fv := foreign_view(t, s)
    k.c.in_foreign_sig = true
    defer k.c.in_foreign_sig = false
    for ff in fv.funs {
        v := foreign_fun_view(t, ff)
        name := tc_text(v.name)
        span := tree_span(t, ff)
        ft := new(Type_Scope)
        ft.kind, ft.calling_conv = .Fun, .C
        ft.home_package, ft.name = k.pkg, make_flat_name(k.pkg, name)
        for g in v.params {
            pv := params_view(t, g)
            for pn in pv.names {
                append(&ft.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = tc_type(k, pv.type_, env, span)})
            }
        }
        for r in v.returns { append(&ft.return_types, tc_type(k, r, env, span)) }
        ft.decl = v.name
        scope_bind(mod, name, ft, {ft.decl, .Fun})
        k.c.declared_funs[name] = true
        k.table.fun_homes[name] = k.pkg
        if mod.functions == nil { mod.functions = make(map[string]^Type_Scope) }
        mod.functions[name] = ft
    }
}

// A module's foreign funs, for the emitter: each by its flat name, linked as
// prefix + name (one declaration per symbol in the program).
tc_extract_foreign :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, module: string) {
    t := k.t
    fv := foreign_view(t, s)
    library := tc_text(fv.library)
    prefix := tc_text(fv.prefix) if fv.prefix != 0 else ""
    k.checked.foreign_libs[library] = true
    for ff in fv.funs {
        name := tc_text(foreign_fun_view(t, ff).name)
        found, _ := scope_lookup(env, name)
        ft, is_scope := found.(^Type_Scope)
        if !is_scope { continue }
        span := tree_span(t, ff)
        link := strings.concatenate({prefix, name}) if prefix != "" else name
        for _, existing in k.checked.functions {
            fo, is_foreign := existing.origin.(Origin_Foreign)
            if !is_foreign || fo.link_name != link { continue }
            tc_error(k, span, TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY, link, fo.library, span_loc(existing.body_span))
            break
        }
        ft.origin = Origin_Foreign{library = library, link_name = link}
        ft.body_span = span
        // (Its params: its variables, though it has no body to bind them.)
        for p in ft.params { annot_add_var(k.annot, ft, {p.decl, .Param, p.type_}) }
        k.checked.functions[make_flat_name(module, name)] = ft
    }
}
