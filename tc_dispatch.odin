package mara

import "core:strings"

// Dispatch groups and operator overloads in the checker: `add(a, b)`
// calls the one function of the group its argument types fit; `a + b` with
// an operand no number calls the best fit of the groups `overload +` names.

// Whether a binding of no written width (an int's or a float's) can take a
// param's type: a number of its kind.
tc_binding_kind_fits :: proc(t, param: Type) -> bool {
    _, pk, ok := numeric_info(resolve_infer(param))
    if !ok { return false }
    _, is_float := t.(Type_Infer_Float)
    return is_float == (pk == .Float)
}

// `f(args)` where f is a dispatch group: each argument checked, the one
// member they fit chosen — each argument its param's type (a binding no use
// has given a width yet: a param of its kind) — then the call.
tc_dispatch_call :: proc(k: ^TC, n: Tree_Id, name: string, members: []TC_Member, args: []Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    // (A `_`: the default the chosen function has there — checked once it
    // is chosen.)
    underscore := make([]bool, len(args), context.temp_allocator)
    for a, i in args { underscore[i] = tr.tag[a] == .Ident && tc_name(k, a) == "_" }
    arg_types := make([dynamic]Type, context.temp_allocator)
    for a, i in args { append(&arg_types, nil if underscore[i] else tc_arg(k, a)) }
    matched := make([dynamic]string, context.temp_allocator)
    matched_fts := make([dynamic]^Type_Scope, context.temp_allocator)
    candidates: for m in members {
        f := m.name
        found, ok := tc_ref_type(k, m.ref, f)
        if !ok { continue }
        ft, is_scope := found.(^Type_Scope)
        if !is_scope || len(ft.params) < len(arg_types) { continue }
        for i := len(arg_types); i < len(ft.params); i += 1 {
            if !field_has_default(ft.params[i]) { continue candidates }
        }
        for at, i in arg_types {
            if underscore[i] {
                if !field_has_default(ft.params[i]) { continue candidates }
                continue
            }
            if types_incompatible(ft.params[i].type_, at) { continue candidates }
            // (A binding of no width yet fits a param of its kind only: a whole
            // number's no float.)
            if tc_open_binding(at) && !tc_binding_kind_fits(at, ft.params[i].type_) { continue candidates }
        }
        append(&matched, f)
        append(&matched_fts, ft)
    }
    // (More than one fitting a binding no use has given a width yet: the one
    // its default width fits — that width the binding's from here,
    // tc_pin_default's way.)
    open_args := false
    for at, i in arg_types { if !underscore[i] && tc_open_binding(at) { open_args = true } }
    if open_args && len(matched) > 1 {
        by_default := make([dynamic]string, context.temp_allocator)
        by_default_fts := make([dynamic]^Type_Scope, context.temp_allocator)
        defaults: for f, m in matched {
            for at, i in arg_types {
                if underscore[i] || !tc_open_binding(at) { continue }
                if !infer_same(matched_fts[m].params[i].type_, solidify_type(at)) { continue defaults }
            }
            append(&by_default, f)
            append(&by_default_fts, matched_fts[m])
        }
        if len(by_default) > 0 {
            clear(&matched)
            clear(&matched_fts)
            append(&matched, ..by_default[:])
            append(&matched_fts, ..by_default_fts[:])
        }
    }
    if len(matched) == 0 {
        names := make([dynamic]string, context.temp_allocator)
        for at, i in arg_types { append(&names, "_" if underscore[i] else type_name(at)) }
        tc_error(k, span, TYPE_MATCHING_FUNCTION_DISPATCH_GROUP_ARGUMENT, name, strings.join(names[:], ", "))
        return Type_Error{}
    }
    if len(matched) > 1 {
        tc_error(k, span, TYPE_AMBIGUOUS_DISPATCH_MATCHES_MULTIPLE_OVERLOADS, name, strings.join(matched[:], ", "))
        return Type_Error{}
    }
    ft := matched_fts[0]
    // (A binding's argument: a use of its width, the member's param's.)
    for at, i in arg_types {
        if underscore[i] || i >= len(ft.params) { continue }
        if cell := infer_cell_of(at); cell != nil && tc_binding_kind_fits(at, ft.params[i].type_) {
            unify_infer_concrete(k.c, cell, ft.params[i].type_, span)
        }
    }
    tc_set_callee(k, n, ft)
    tc_set_ref(k, n, {ft.decl, .Fun})
    k.annot.forms[tc_sid(k, n)] = .Dispatch
    // (What each param receives, kept: a `_`'s default, its own (dispatched
    // whole, no slot), the rest's after the arguments.)
    received := make([dynamic]Arg, 0, len(ft.params), context.temp_allocator)
    for i in 0 ..< len(ft.params) {
        def := ft.params[i].default_node
        switch {
        case i < len(args) && !underscore[i] && args[i] == k.recv.node: append(&received, Arg{args[i], .Receiver, -1})
        case i < len(args) && !underscore[i]:                           append(&received, Arg{args[i], .Written, -1})
        case tr.tag[def] == .Hash_Name:                                 append(&received, Arg{def, .Call_Site, -1})
        case:                                                           append(&received, Arg{def, .Default, -1})
        }
    }
    tc_set_args(k, n, received[:])
    for a, i in args { if i < len(ft.params) && !underscore[i] { tc_settle(k, a, ft.params[i].type_) } }   // (each at its param's type, now known)
    // (Its defaults — a `_`'s, then the params it leaves off; a call site's
    // (`#caller_name`) where the call is.)
    for i in 0 ..< len(ft.params) {
        if i < len(args) && !underscore[i] { continue }
        def := ft.params[i].default_node
        if tr.tag[def] == .Hash_Name { tc_hash_name(k, def) } else { tc_check_at(k, def, ft.params[i].type_) }
    }
    return fn_primary_return(ft)
}

// The function `l op r` calls, when an operand is no number: of the groups
// `overload op` names, the member that fits best — its params the operands'
// types exactly, then structurally, then a generic one's instance.
tc_operator_overload :: proc(k: ^TC, op: Token_Kind, lt, rt: Type, span: Span) -> (^Type_Scope, bool) {
    groups := resolve_overloads(k.rs, span.at, op)
    if len(groups) == 0 { return nil, false }
    best: ^Type_Scope
    best_score := 0   // (1 a generic's instance, 2 structural, 3 exact)
    for group in groups {
        for m in tc_dispatch_members(k, resolve_dispatches(k.rs, span.at, tc_text(group))) {
            f := m.name
            if found, ok := tc_ref_type(k, m.ref, f); ok {
                ft, is_scope := found.(^Type_Scope)
                if !is_scope || len(ft.params) != 2 { continue }
                if types_incompatible(ft.params[0].type_, lt) || types_incompatible(ft.params[1].type_, rt) { continue }
                score := 3 if types_name_equal(ft.params[0].type_, lt) && types_name_equal(ft.params[1].type_, rt) else 2
                if score > best_score {
                    actual := [2]Type{lt, rt}
                    if tc_respecializes(ft, actual[:]) {
                        tc_error(k, span, "an overload specialized to a generic struct's instance is not supported yet")
                        return nil, false
                    }
                    best, best_score = ft, score
                }
                continue
            }
            // (A generic member is instantiated whether or not a better fit is
            // found: its instance exists.)
            tmpl, is_template := tc_template(k, m.ref)
            if !is_template { continue }
            if inst := tc_overload_instance(k, f, tmpl, lt, rt); inst != nil && best_score < 1 { best, best_score = inst, 1 }
        }
    }
    return best, best_score > 0
}

// A generic member's instance for two operands, when its params, bound from
// them, take them.
tc_overload_instance :: proc(k: ^TC, name: string, tmpl: TC_Template, lt, rt: Type) -> ^Type_Scope {
    tr := k.t
    v := scope_view(tr, tmpl.node)
    ptypes := make([dynamic]Tree_Id, context.temp_allocator)
    for g in v.params {
        pv := params_view(tr, g)
        for _ in pv.names { append(&ptypes, pv.type_) }
    }
    if len(ptypes) != 2 { return nil }
    params := tc_generic_params(k, tmpl.node)
    subst: map[string]Type
    for p in params { subst[p] = nil }
    tc_infer(k, &subst, ptypes[0], lt)
    tc_infer(k, &subst, ptypes[1], rt)
    for p in params { if subst[p] == nil { return nil } }
    // (Its params at the bindings take the operands, before it is made.)
    saved := k.subst
    k.subst = subst
    was := tc_type_params_bind(k, tmpl.node, subst)
    span := tree_span(tr, tmpl.def)
    p0 := tc_type(k, ptypes[0], span)
    p1 := tc_type(k, ptypes[1], span)
    tc_type_params_restore(k, was)
    k.subst = saved
    if types_incompatible(p0, lt) || types_incompatible(p1, rt) { return nil }
    type_args := make([dynamic]Type, context.temp_allocator)
    for p in params { append(&type_args, subst[p]) }
    mangled := mangle_generic_name(name, type_args[:])
    ft := k.instances[mangled] or_else nil
    if ft == nil { ft = tc_instantiate_fun(k, tmpl, subst, mangled) }
    if len(ft.params) != 2 || types_incompatible(ft.params[0].type_, lt) || types_incompatible(ft.params[1].type_, rt) { return nil }
    return ft
}


// The function `-x` calls, when x is no number: of the groups `overload -`
// names, the one-param member that fits best.
tc_unary_overload :: proc(k: ^TC, t: Type, at: Token_Id) -> ^Type_Scope {
    best: ^Type_Scope
    best_score := 0
    for group in resolve_overloads(k.rs, at, .Minus) {
        for m in tc_dispatch_members(k, resolve_dispatches(k.rs, at, tc_text(group))) {
            found, ok := tc_ref_type(k, m.ref, m.name)
            if !ok { continue }
            ft, is_scope := found.(^Type_Scope)
            if !is_scope || len(ft.params) != 1 || types_incompatible(ft.params[0].type_, t) { continue }
            score := 3 if types_name_equal(ft.params[0].type_, t) else 2
            if score > best_score { best, best_score = ft, score }
        }
    }
    return best
}

// Whether a fun is called with another instance of a generic struct its
// param points at (`add(^String(256))` given a ^String(64)), which would need
// the fun specialized for it.
tc_respecializes :: proc(ft: ^Type_Scope, actual: []Type) -> bool {
    for p, i in ft.params {
        if i >= len(actual) { break }
        pt, is_ptr := p.type_.(^Type_Ptr)
        if !is_ptr { continue }
        want := as_scope_body(pt.elem)
        if want == nil || want.generic_base == "" { continue }
        at, at_ptr := actual[i].(^Type_Ptr)
        if !at_ptr { continue }
        if got := as_scope_body(at.elem); got != nil && got.name != want.name && got.generic_base == want.generic_base { return true }
    }
    return false
}
