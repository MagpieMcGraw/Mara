package mara

// `a, b := f()`, `x, err = f()`, `v, w := f()?`: a call's outputs, each to a
// name (declared, or written) or a target's place, in turn — the names it
// declares made first, then the call, then each output written.

tc_destructure :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool, ann: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    names := make([]string, len(targets))
    stores := make([]bool, len(targets))
    for tg, i in targets {
        if t.tag[tg] == .Ident { names[i] = tc_name(k, tg) } else { stores[i] = true }
    }
    ann_t: Type = Type_Any{}
    if ann != 0 { ann_t = tc_type(k, ann, env, span) }
    _ = ann_t
    v := tc_unparen(k, value)
    is_try := t.tag[v] == .Try && tc_is_call(k, tc_unparen(k, Tree_Id(t.a[v])))
    if !is_try && !tc_is_call(k, v) {
        tc_unsupported(k, s, "one value given to several targets")
        return
    }
    b := tc_building(k)
    mr: Graph_Destructure
    if b != nil { mr = graph_fuse_destructure(b, tc_sid(k, s), span, names, stores, is_decl) }
    returns: []Type
    call := value
    if is_try {
        // (The call checked as a call: `?` its branch, the rest its values.)
        call = tc_unparen(k, Tree_Id(t.a[v]))
        _, r := tc_expr(k, call, env, .Value if b != nil else .None)
        if b = tc_building(k); b != nil && mr.on {
            if !r.ok {
                tc_fail(k, "a `?` on no call built")
            } else {
                b.g.type_[r.v.op] = nil
                mr.call = graph_try_after(b, tree_span(t, v), r.v)
            }
        }
        rets := tc_call_returns(k, call, env)
        rts := enclosing_return_types(env)
        if len(rets) == 0 || !is_err_type(rets[len(rets) - 1]) {
            tc_error(k, span, TYPE_TRY_REQUIRES_ERR_RETURN)
            return
        }
        if len(rts) == 0 || !is_err_type(rts[len(rts) - 1]) {
            tc_error(k, span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
            return
        }
        returns = rets[:len(rets) - 1]
        tc_set_type(k, v, returns[0] if len(returns) > 0 else Type(Type_Void{}))
    } else {
        _, r := tc_expr(k, value, env, .Value if b != nil else .None)
        mr.call = r.v
        returns = tc_call_returns(k, value, env)
        if returns == nil {
            tc_unsupported(k, s, "one value given to several targets")
            return
        }
    }
    if len(targets) != len(returns) {
        tc_error(k, span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE, len(targets), len(returns))
        return
    }
    for tg, i in targets {
        rt := solidify_type(returns[i])
        if names[i] != "" {
            name := names[i]
            if !is_try {
                if !is_decl && name != "_" && name not_in k.consts {
                    if _, found := type_env_get(env, name); !found {
                        report_unresolved(k.c, span, env, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
                    } else if is_immutable_param(env, name) {
                        tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name)
                    }
                }
            }
            type_env_set(env, name, rt)
        } else {
            if !is_try {
                if pname, immutable := tc_write_root_param(k, tg, env); immutable {
                    tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, pname)
                }
            }
            tt, at := tc_expr(k, tg, env, .Place if tc_building(k) != nil else .None)
            mr.place = at.v
            if cname, is_const := tc_write_root_const(k, tg); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
            if !is_any(tt) && !is_any(rt) && !types_equal(tt, rt) {
                tc_error(k, span, TYPE_CANNOT_ASSIGN_MULTI_RETURN, type_name(rt), type_name(tt))
            }
        }
        if b = tc_building(k); b != nil && mr.on { graph_fuse_destructure_write(b, &mr, i, distinct_base(rt)) }
    }
}
