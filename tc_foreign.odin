package mara

import "core:fmt"
import "core:strings"

// `foreign "lib" [prefix p] [fails F] { fun Name(params) -> T }`: each a fun of
// C's calling convention, linked as prefix + name.
//
// `fails F` says how this library reports failure, for its funs that give err:
// `-> err` for a C bool, false when it failed, and `-> T, err` for a C pointer,
// NULL when it failed. Those become F. A fun that gives no err is called as it is.

tc_register_foreign :: proc(k: ^TC, s: Tree_Id) {
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
                append(&ft.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = tc_type(k, pv.type_, span)})
            }
        }
        for r in v.returns { append(&ft.return_types, tc_type(k, r, span)) }
        ft.decl = v.name
        tc_bound_set(k, ft.decl, ft)
    }
}

// The value of the error named after `fails`; false when it's no error that can
// be failed with, which is said.
tc_foreign_fails :: proc(k: ^TC, tok: Token_Id) -> (int, bool) {
    span := token_span(build_tokens[tok])
    name := tc_text(tok)
    t, value, found := tc_variant_ident(k, name, Type_Err{}, false, span)
    if !found {
        tc_error(k, span, TYPE_FOREIGN_FAILS_NOT_ERROR, name)
        return 0, false
    }
    if t == nil { return 0, false }   // (more than one has it: said)
    if value == 0 {
        tc_error(k, span, TYPE_FOREIGN_FAILS_OK, name)
        return 0, false
    }
    return value, true
}

// A foreign fun's results, if it gives err: what C returns for them, into its
// origin. An err anywhere else than this is an error.
tc_foreign_err :: proc(k: ^TC, ft: ^Type_Scope, origin: ^Origin_Foreign, fails: Token_Id, kind: int, known: bool, name: string, span: Span) {
    gives_err := false
    for r in ft.return_types {
        if _, is_err := distinct_base(r).(Type_Err); is_err { gives_err = true }
    }
    if !gives_err { return }
    if fails == 0 {
        tc_error(k, span, TYPE_FOREIGN_ERR_NEEDS_FAILS, name)
        return
    }
    if !known { return }   // (what's wrong with `fails`: said)
    n := len(ft.return_types)
    _, last_err := distinct_base(ft.return_types[n - 1]).(Type_Err)
    if !last_err || n > 2 {
        tc_error(k, span, TYPE_FOREIGN_ERR_RESULTS, name)
        return
    }
    origin.c_result = Type_Bool{}
    if n == 2 {
        if _, is_ptr := distinct_base(ft.return_types[0]).(^Type_Ptr); !is_ptr {
            tc_error(k, span, TYPE_FOREIGN_ERR_RESULTS, name)
            return
        }
        origin.c_result = ft.return_types[0]
    }
    origin.fails, origin.fail_kind = true, kind
    origin.fail_site = checked_atom(k.checked, fmt.tprintf("%s in %s", span_location(span), origin.link_name))
}

// A module's foreign funs, for the emitter: each by its flat name, linked as
// prefix + name (one declaration per symbol in the program).
tc_extract_foreign :: proc(k: ^TC, s: Tree_Id, module: string) {
    t := k.t
    fv := foreign_view(t, s)
    library := tc_text(fv.library)
    prefix := tc_text(fv.prefix) if fv.prefix != 0 else ""
    fail_kind, fails_known := 0, false
    if fv.fails != 0 { fail_kind, fails_known = tc_foreign_fails(k, fv.fails) }
    // ("mara_runtime": the compiler's own runtime, runtime/*.c — its objects
    // linked by the build itself, no library to look for.)
    if library != "mara_runtime" { k.checked.foreign_libs[library] = true }
    for ff in fv.funs {
        name := tc_text(foreign_fun_view(t, ff).name)
        found, _ := tc_bound(k, foreign_fun_view(t, ff).name)
        ft, is_scope := found.(^Type_Scope)
        if !is_scope { continue }
        span := tree_span(t, ff)
        link := strings.concatenate({prefix, name}) if prefix != "" else name
        origin := Origin_Foreign{library = library, link_name = link}
        tc_foreign_err(k, ft, &origin, fv.fails, fail_kind, fails_known, name, span)
        ft.origin = origin
        // (A foreign block is its file's own, so another file may bind a C
        // function another has: as that one does — a symbol has one C
        // signature, its one `declare`. Its Mara types may differ, a
        // distinct File_Id for an i64, the C ones not.)
        for _, existing in k.checked.functions {
            fo, is_foreign := existing.origin.(Origin_Foreign)
            if !is_foreign || fo.link_name != link { continue }
            os := k.checked.target_os
            if build_c_declare(existing, link, os) != build_c_declare(ft, link, os) {
                tc_error(k, span, TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY, link, fo.library, span_loc(existing.body_span))
            }
            break
        }
        ft.body_span = span
        // (Its params: its variables, though it has no body to bind them.)
        for p in ft.params { annot_add_var(k.annot, ft, {p.decl, .Param, p.type_}) }
        k.checked.functions[make_flat_name(module, name)] = ft
    }
}
