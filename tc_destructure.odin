package mara

// `a, b := f()`, `x, err = f()`, `v, w := f()?`: a call's outputs, each to a
// name (declared, or written) or a target, in turn — each at its result's
// type.

tc_destructure :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool, ann: Tree_Id,
                       fields_of: ^Type_Scope = nil) {
    t := k.t
    span := tree_span(t, s)
    names := make([]string, len(targets))
    for tg, i in targets {
        if t.tag[tg] == .Ident { names[i] = tc_name(k, tg) }
    }
    // (`a, b : T = f()`: each result a T.)
    ann_t: Type = Type_Any{}
    if ann != 0 { ann_t = tc_type(k, ann, span) }
    v := tc_unparen(k, value)
    is_try := t.tag[v] == .Try && tc_is_call(k, tc_unparen(k, Tree_Id(t.a[v])))
    returns: []Type
    if is_try {
        // (The call checked as a call: `?` its branch, the rest its values.)
        call := tc_unparen(k, Tree_Id(t.a[v]))
        k.several_ok = call
        tc_check(k, call)
        k.several_ok = 0
        rets := tc_call_returns(k, call)
        rts := tc_results(k)
        if len(rets) == 0 || !is_err_type(rets[len(rets) - 1]) {
            tc_error(k, span, TYPE_TRY_REQUIRES_ERR_RETURN)
            return
        }
        if k.in_defer {
            tc_error(k, span, TYPE_TRY_IN_DEFER)   // (its names still bound: no errors after it)
        } else if len(rts) == 0 || !is_err_type(rts[len(rts) - 1]) {
            tc_error(k, span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
            return
        }
        returns = rets[:len(rets) - 1]
        tc_set_type(k, v, returns[0] if len(returns) > 0 else Type(Type_Void{}))
    } else {
        // (One value no call of several results: a broadcast, its value
        // checked in each target's copy.)
        k.several_ok = v
        vt := tc_check(k, value)
        k.several_ok = 0
        returns = tc_call_returns(k, value)
        if returns == nil {
            if is_any(vt) {
                // (Of no type, reported: its names none either.)
                for name, i in names { if name != "" { tc_bind(k, name, Type_Error{}, tc_decl_ref(k, targets[i], fields_of)) } }
                return
            }
            tc_broadcast(k, s, targets, value, is_decl)
            return
        }
    }
    if len(targets) != len(returns) {
        tc_error(k, span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE, len(targets), len(returns))
        return
    }
    for tg, i in targets {
        rt := solidify_type(returns[i])
        if !is_any(ann_t) && !is_any(rt) && !types_equal(ann_t, rt) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_MULTI_RETURN, type_name(rt), type_name(ann_t))
        }
        if names[i] == "_" {
            // (Names nothing, declared or written: its output dropped.)
        } else if names[i] != "" {
            name := names[i]
            if !is_decl {
                // (Written: at the variable's own type — the result's, or a
                // width still open, settled to it.)
                existing, _, ok := tc_name_write(k, tg, name, span)
                if !ok { return }
                if !coerce_deferred(k.c, existing, rt, span) && !is_any(existing) && !is_any(rt) && !types_equal(existing, rt) {
                    tc_error(k, span, TYPE_CANNOT_ASSIGN_MULTI_RETURN, type_name(rt), type_name(existing))
                }
            } else {
                tc_bind(k, name, rt, tc_decl_ref(k, tg, fields_of))
                tc_set_type(k, tg, rt)
                tc_set_ref(k, tg, tc_decl_ref(k, tg, fields_of))
            }
            // (A struct's field: its value its slot of the call's.)
            if fields_of != nil { tc_add_field(fields_of, name, k.t.main[tg], rt, value, i) }
        } else {
            if pname, immutable := tc_write_root_param(k, tg); immutable {
                tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, pname)
            }
            tt := tc_check(k, tg)
            if cname, is_const := tc_write_root_const(k, tg); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
            if !is_any(tt) && !is_any(rt) && !types_equal(tt, rt) {
                tc_error(k, span, TYPE_CANNOT_ASSIGN_MULTI_RETURN, type_name(rt), type_name(tt))
            }
        }
    }
}

// `a, b = v`, `x, y := v`: v to each target — the statement's copies, one a
// target, each a statement of its own, v checked in each. (A declaration's
// copies take no annotation.)
tc_broadcast :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool) {
    for tg in targets {
        // (A declaration's bare names declared; a place, written.)
        if is_decl && k.t.tag[tg] == .Ident { tc_decl_one(k, s, tg, value, 0, nil) } else { tc_assign_one(k, s, tg, value) }
    }
}
