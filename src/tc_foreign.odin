package mara

import "core:fmt"
import "core:strings"

// `foreign "lib" [prefix p] [fails F] { fun Name(params) -> T }`: each a fun of
// C's calling convention, linked as prefix + name.
//
// `fails F` says how this library reports failure, for its funs that give err:
// `-> err` for a C bool, false when it failed, and `-> T, err` for a C pointer,
// NULL when it failed. Those become F. A fun that gives no err is called as it is.

// (`owner`: the scope whose body has it, by name — its funs are named for it.)
tc_register_foreign :: proc(k: ^TC, s: Tree_Id, owner: string) {
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
        ft.home_package, ft.name = k.pkg, make_flat_name(owner, name)
        for g in v.params {
            pv := params_view(t, g)
            for pn in pv.names {
                pt := tc_type(k, pv.type_, span)
                if foreign_header_type(pt) { tc_error(k, token_span(build_tokens[pn]), TYPE_FOREIGN_HEADER_TYPE, name, fmt.tprintf("param '%s'", tc_text(pn)), type_name(pt)) }
                if what := foreign_fun_by_value(pt); what != "" { tc_error(k, token_span(build_tokens[pn]), TYPE_FOREIGN_FUN_BY_VALUE, name, fmt.tprintf("param '%s'", tc_text(pn)), what) }
                append(&ft.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = pt})
            }
        }
        for r in v.returns {
            rt := tc_type(k, r, span)
            if foreign_header_type(rt) { tc_error(k, span, TYPE_FOREIGN_HEADER_TYPE, name, "result", type_name(rt)) }
            if what := foreign_fun_by_value(rt); what != "" { tc_error(k, span, TYPE_FOREIGN_FUN_BY_VALUE, name, "result", what) }
            append(&ft.return_types, rt)
        }
        ft.decl = v.name
        tc_bound_set(k, ft.decl, ft)
    }
}

// A fun C calls — a fun type among a foreign fun's params, or its result —
// that Mara's own convention doesn't make C's: what it has that the two pass
// differently, "" when nothing. Mara takes a struct, an array or a union by
// its address and gives one back, or several results, through hidden
// pointers; C takes and gives small ones in registers.
foreign_fun_by_value :: proc(t: Type) -> string {
    f, is_scope := distinct_base(t).(^Type_Scope)
    if !is_scope || f.kind != .Fun { return "" }
    by_value :: proc(t: Type) -> bool {
        #partial switch v in distinct_base(t) {
        case ^Type_Scope:       return v.kind != .Fun
        case ^Type_Fixed_Array, ^Type_Union, ^Type_Slice, ^Type_Partial_Array: return true
        }
        return false
    }
    for _, i in f.params {
        if p := fn_param(f, i).type_; by_value(p) { return fmt.tprintf("a param of type %s, by value", type_name(p)) }
    }
    if fn_result_count(f) > 1 { return "more than one result" }
    if fn_result_count(f) == 1 {
        if r := fn_result(f, 0); by_value(r) { return fmt.tprintf("a result of type %s, by value", type_name(r)) }
    }
    return ""
}

// A type C can't be handed as it is: Mara's own record of items — a list (its
// len before them), a slice ({len, cap, ptr}), a ^[]T — or a pointer to one.
// C given it reads the record, not the items.
foreign_header_type :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Slice, ^Type_Partial_Array: return true
    case ^Type_Ptr:
        if slice_ref_of(v) != nil { return true }
        #partial switch e in distinct_base(v.elem) {
        case ^Type_Slice, ^Type_Partial_Array: return true
        }
    }
    return false
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

// A scope's foreign funs, for the emitter: each by its flat name (`owner`:
// the scope's), linked as prefix + name (one declaration per symbol in the
// program).
tc_extract_foreign :: proc(k: ^TC, s: Tree_Id, owner: string) {
    t := k.t
    fv := foreign_view(t, s)
    library := tc_text(fv.library)
    prefix := tc_text(fv.prefix) if fv.prefix != 0 else ""
    fail_kind, fails_known := 0, false
    if fv.fails != 0 { fail_kind, fails_known = tc_foreign_fails(k, fv.fails) }
    // ("mara_runtime": the compiler's own runtime, runtime/*.c — its objects
    // linked by the build itself, no library to look for.)
    if library != "mara_runtime" {
        k.checked.foreign_libs[library] = true
        if library not_in k.checked.foreign_homes { k.checked.foreign_homes[library] = {} }
        homes := &k.checked.foreign_homes[library]
        known := false
        for home in homes { known ||= home == k.pkg }
        if !known { append(homes, k.pkg) }
    }
    for ff in fv.funs {
        name := tc_text(foreign_fun_view(t, ff).name)
        found, _ := tc_bound(k, foreign_fun_view(t, ff).name)
        ft, is_scope := found.(^Type_Scope)
        if !is_scope { continue }
        span := tree_span(t, ff)
        link := strings.concatenate({prefix, name}) if prefix != "" else name
        // (A name a module defines once, as any definition's.)
        flat := make_flat_name(owner, name)
        if _, bound := k.checked.functions[flat]; bound || flat in k.table.funs {
            tc_error(k, span, TYPE_FUNCTION_ALREADY_DEFINED, name)
            continue
        }
        origin := Origin_Foreign{library = library, link_name = link}
        tc_foreign_err(k, ft, &origin, fv.fails, fail_kind, fails_known, name, span)
        ft.origin = origin
        // (Another module may bind a C function one has: as that one does — a
        // symbol has one C signature, its one `declare`. Its Mara types may
        // differ, a distinct File_Id for an i64, the C ones not.)
        // (Of several that bind it, the first as written: the same one
        // whatever order the functions come in.)
        bound: ^Type_Scope
        for _, existing in k.checked.functions {
            fo, is_foreign := existing.origin.(Origin_Foreign)
            if !is_foreign || fo.link_name != link { continue }
            if bound == nil || existing.body_span.at < bound.body_span.at { bound = existing }
        }
        if bound != nil {
            os := k.checked.target_os
            if build_c_declare(bound, link, os) != build_c_declare(ft, link, os) {
                tc_error(k, span, TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY, link, bound.origin.(Origin_Foreign).library, span_loc(bound.body_span))
            }
        }
        ft.body_span = span
        // (Its params: its variables, though it has no body to bind them.)
        for p in ft.params { annot_add_var(k.annot, ft, {p.decl, .Param, p.type_}) }
        k.checked.functions[flat] = ft
    }
}
