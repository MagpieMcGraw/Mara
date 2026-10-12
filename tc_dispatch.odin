package mara

import "core:strings"

// Dispatch groups and operator overloads in the checker: `add(a, b)`
// calls the function of the group its arguments fit closest — each as it
// is, or a number widened as it would be into any param; `a + b` with an
// operand no number calls the best fit of the groups `overload +` names.

// Whether a binding of no written width (an int's or a float's) can take a
// param's type: a number of its kind.
tc_binding_kind_fits :: proc(t, param: Type) -> bool {
    _, pk, ok := numeric_info(resolve_infer(param))
    if !ok { return false }
    _, is_float := t.(Type_Infer_Float)
    return is_float == (pk == .Float)
}

// How far an argument's type is from a param's, for a dispatch's choice:
// 0 when it fits as it is; a number that widens into it, the bits it gains
// (one more when it turns signed, so u16 → u32 comes before u16 → i32); -1
// when it doesn't fit. An untyped number, or a binding whose width isn't
// decided yet, takes the param's width: 0 for any number of its kind.
tc_dispatch_distance :: proc(at, pt: Type) -> int {
    if tc_open_binding(at) {
        if !tc_binding_kind_fits(at, pt) || types_incompatible(pt, at) { return -1 }
        return 0
    }
    if !types_incompatible(pt, at) { return 0 }
    if value_preserving_widen(resolve_infer(at), resolve_infer(pt)) {
        fb, fk, _ := numeric_info(at)
        tb, tk, _ := numeric_info(pt)
        return tb - fb + (1 if fk != tk else 0)
    }
    return -1
}

// The members no other is closer than: closer on some argument, and no
// farther on any (each one's distances, per argument).
tc_dispatch_closest :: proc(dist: [][]int) -> [dynamic]int {
    best := make([dynamic]int, context.temp_allocator)
    members: for d, m in dist {
        for o, j in dist {
            if j == m { continue }
            closer, farther := false, false
            for i in 0 ..< len(d) {
                if o[i] < d[i] { closer = true }
                if o[i] > d[i] { farther = true }
            }
            if closer && !farther { continue members }
        }
        append(&best, m)
    }
    return best
}

// `f(args)` where f is a dispatch group: each argument checked, the member
// they fit closest chosen (tc_dispatch_distance), then the call.
tc_dispatch_call :: proc(k: ^TC, n: Tree_Id, name: string, members: [dynamic]string, args: []Tree_Id,
                         env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    // (A `_`: the default the chosen function has there — checked once it
    // is chosen.)
    underscore := make([]bool, len(args), context.temp_allocator)
    for a, i in args { underscore[i] = tr.tag[a] == .Ident && tc_name(k, a) == "_" }
    arg_types := make([dynamic]Type, context.temp_allocator)
    for a, i in args { append(&arg_types, nil if underscore[i] else tc_arg(k, a, env)) }
    // Each member the arguments fit, and how far each argument is from its param.
    fit_names := make([dynamic]string, context.temp_allocator)
    fit_fts := make([dynamic]^Type_Scope, context.temp_allocator)
    fit_dist := make([dynamic][]int, context.temp_allocator)
    candidates: for f in members {
        found, ok := scope_lookup(env, f)
        if !ok { continue }
        ft, is_scope := found.(^Type_Scope)
        if !is_scope || len(ft.params) < len(arg_types) { continue }
        for i := len(arg_types); i < len(ft.params); i += 1 {
            if !field_has_default(ft.params[i]) { continue candidates }
        }
        dist := make([]int, len(arg_types), context.temp_allocator)
        for at, i in arg_types {
            if underscore[i] {
                if !field_has_default(ft.params[i]) { continue candidates }
                continue
            }
            dist[i] = tc_dispatch_distance(at, ft.params[i].type_)
            if dist[i] < 0 { continue candidates }
        }
        append(&fit_names, f)
        append(&fit_fts, ft)
        append(&fit_dist, dist)
    }
    // The closest of them. A binding among the arguments whose uses haven't
    // decided its width yet (`n := 0; f(n)`) takes any member's width, and
    // when that leaves more than one: in a first pass, the one its default
    // width would choose, for now, and the program checked again once every
    // width is known (TC.deferred); after that — no use decided it — the
    // one its default width chooses.
    closest := tc_dispatch_closest(fit_dist[:])
    open_args := false
    for at, i in arg_types { if !underscore[i] && tc_open_binding(at) { open_args = true } }
    provisional := false
    if open_args && len(closest) > 1 {
        at_default := make([dynamic][]int, context.temp_allocator)
        for m in closest {
            dist := make([]int, len(arg_types), context.temp_allocator)
            copy(dist, fit_dist[m])
            for at, i in arg_types {
                if underscore[i] || !tc_open_binding(at) { continue }
                dist[i] = tc_dispatch_distance(solidify_type(at), fit_fts[m].params[i].type_)
            }
            append(&at_default, dist)
        }
        // (Fitting at the default width: closest among those.)
        fits := make([dynamic][]int, context.temp_allocator)
        which := make([dynamic]int, context.temp_allocator)
        for d, j in at_default {
            ok := true
            for x in d { if x < 0 { ok = false } }
            if ok {
                append(&fits, d)
                append(&which, closest[j])
            }
        }
        by_default := make([dynamic]int, context.temp_allocator)
        for j in tc_dispatch_closest(fits[:]) { append(&by_default, which[j]) }
        if k.pass == 1 {
            k.deferred = true
            provisional = true
            pick := closest[0]
            if len(by_default) > 0 { pick = by_default[0] }
            clear(&closest)
            append(&closest, pick)
        } else if len(by_default) > 0 {
            clear(&closest)
            append(&closest, ..by_default[:])
        }
    }
    matched := make([dynamic]string, context.temp_allocator)
    matched_fts := make([dynamic]^Type_Scope, context.temp_allocator)
    for m in closest {
        append(&matched, fit_names[m])
        append(&matched_fts, fit_fts[m])
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
    // (A binding's argument: a use of its width, the member's param as any
    // param is — widened into. Not for a choice made for now.)
    if !provisional {
        for at, i in arg_types {
            if underscore[i] || i >= len(ft.params) { continue }
            if cell := infer_cell_of(at); cell != nil && tc_binding_kind_fits(at, ft.params[i].type_) {
                infer_constrain(k.c, cell, .Into, ft.params[i].type_, span)
            }
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
    // (Its defaults — a `_`'s, then the params it leaves off: each in its
    // function's defining scope; a call site's (`#caller_name`) where the
    // call is.)
    callee := callee_def_scope(ft)
    if callee == nil { callee = env }
    for i in 0 ..< len(ft.params) {
        if i < len(args) && !underscore[i] { continue }
        def := ft.params[i].default_node
        if tr.tag[def] == .Hash_Name { tc_hash_name(k, def, env) } else { tc_check_at(k, def, callee, ft.params[i].type_) }
    }
    return fn_primary_return(ft)
}

// The function `l op r` calls, when an operand is no number: of the groups
// `overload op` names, the member that fits best — its params the operands'
// types exactly, then structurally, then a generic one's instance.
tc_operator_overload :: proc(k: ^TC, op: Token_Kind, lt, rt: Type, env: ^Type_Scope, span: Span) -> (^Type_Scope, bool) {
    groups, has := find_operator_overload(k.c, env, op)
    if !has { return nil, false }
    best: ^Type_Scope
    best_score := 0   // (1 a generic's instance, 2 structural, 3 exact)
    for group in groups {
        members, is_dispatch := find_dispatch(k.c, env, group)
        if !is_dispatch { continue }
        for f in members {
            if found, ok := scope_lookup(env, f); ok {
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
            tmpl, is_template := k.templates[f]
            if !is_template { continue }
            if inst := tc_overload_instance(k, f, tmpl, lt, rt, env); inst != nil && best_score < 1 { best, best_score = inst, 1 }
        }
    }
    return best, best_score > 0
}

// A generic member's instance for two operands, when its params, bound from
// them, take them.
tc_overload_instance :: proc(k: ^TC, name: string, tmpl: TC_Template, lt, rt: Type, env: ^Type_Scope) -> ^Type_Scope {
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
    span := tree_span(tr, tmpl.def)
    p0 := tc_type(k, ptypes[0], tmpl.env, span)
    p1 := tc_type(k, ptypes[1], tmpl.env, span)
    k.subst = saved
    if types_incompatible(p0, lt) || types_incompatible(p1, rt) { return nil }
    type_args := make([dynamic]Type, context.temp_allocator)
    for p in params { append(&type_args, subst[p]) }
    mangled := mangle_generic_name(name, type_args[:])
    ft := k.instances[mangled] or_else nil
    if ft == nil { ft = tc_instantiate_fun(k, tmpl, subst, mangled, env) }
    if len(ft.params) != 2 || types_incompatible(ft.params[0].type_, lt) || types_incompatible(ft.params[1].type_, rt) { return nil }
    return ft
}


// The function `-x` calls, when x is no number: of the groups `overload -`
// names, the one-param member that fits best.
tc_unary_overload :: proc(k: ^TC, t: Type, env: ^Type_Scope) -> ^Type_Scope {
    groups, has := find_operator_overload(k.c, env, .Minus)
    if !has { return nil }
    best: ^Type_Scope
    best_score := 0
    for group in groups {
        members, is_dispatch := find_dispatch(k.c, env, group)
        if !is_dispatch { continue }
        for f in members {
            found, ok := scope_lookup(env, f)
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
