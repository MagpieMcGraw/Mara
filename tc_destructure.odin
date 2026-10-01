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
    of_call := tc_is_call(k, v)
    b := tc_building(k)
    mark: Graph_Mark
    mr: Graph_Destructure
    if b != nil {
        mark = graph_fuse_mark(b)
        if is_try || of_call { mr = graph_fuse_destructure(b, tc_sid(k, s), span, names, stores, is_decl) }
    }
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
        // (One value no call of several results: a broadcast, its value
        // built in each target's copy — a call's, built before that was
        // known, left out.)
        vt: Type
        r: Fused
        if of_call { vt, r = tc_expr(k, value, env, .Value if b != nil else .None) } else { vt = tc_check(k, value, env) }
        mr.call = r.v
        returns = tc_call_returns(k, value, env)
        if returns == nil {
            if b = tc_building(k); b != nil && mr.on {
                graph_fuse_drop_since(b, mark)
                mr.on = false
            }
            if is_any(vt) {
                // (Of no type, reported: its names none either.)
                for name in names { if name != "" { type_env_set(env, name, Type_Error{}) } }
                return
            }
            tc_broadcast(k, s, targets, value, is_decl, env)
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

// `a, b = v`, `x, y := v`: v to each target — the statement's copies, one a
// target, each a statement of its own, v checked in each. (A declaration's
// copies take no annotation: the old checker's desugaring left it off.)
tc_broadcast :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    if b := tc_building(k); b != nil { graph_fuse_stmt_kind(b, .Other) }
    for tg in targets {
        kind := Stmt_Kind.Decl if is_decl else tc_assign_kind(k, tg)
        b := tc_building(k)
        saved: i32
        if b != nil { saved = graph_fuse_stmt(b, tc_sid(k, s), span, kind, fresh = true) }
        if is_decl { tc_decl_one(k, s, tg, value, 0, env, nil) } else { tc_assign_one(k, s, tg, value, env) }
        if b != nil { graph_fuse_stmt_end(b, saved) }
    }
}

// An assignment's statement kind, by its target: a place's a write; `_`'s
// and this_program's no assignment.
tc_assign_kind :: proc(k: ^TC, target: Tree_Id) -> Stmt_Kind {
    if k.t.tag[target] != .Ident { return .Write }
    if name := tc_name(k, target); name == "_" || name == "this_program" { return .Other }
    return .Assign
}

// `a, b = c, d`: each assignment checked in turn, a statement of its own.
// Reassigned together, every value goes in first — each store held in a
// temporary at its target's type (tc_parallel_hold) — then each target is
// written from its own.
tc_parallel_assign :: proc(k: ^TC, s: Tree_Id, targets, values: []Tree_Id, env: ^Type_Scope) {
    span := tree_span(k.t, s)
    held := make([dynamic]TC_Held, context.temp_allocator)
    parallel := tc_building(k) != nil
    saved := k.parallel
    if parallel { k.parallel = &held }
    for tg, i in targets {
        b := tc_building(k)
        saved_stmt: i32
        if b != nil { saved_stmt = graph_fuse_stmt(b, tc_sid(k, s), span, tc_assign_kind(k, tg), fresh = true) }
        tc_assign_one(k, s, tg, values[i], env)
        if b != nil { graph_fuse_stmt_end(b, saved_stmt) }
    }
    k.parallel = saved
    b := tc_building(k)
    if !parallel || b == nil { return }
    for h in held {
        v := graph_read(b, graph_var(b, "parallel", h.slot, h.t, h.span), h.t, h.span)
        graph_fuse_write_at(b, graph_dest_place(b, h.d, h.span), v, h.span)
    }
}

TC_Held :: struct {
    d:    Dest,
    slot: Node_Id,
    t:    Type,
    span: Span,
}

// A store assigned together with others: into a temporary of its own, at
// its target's type (tc_parallel_assign writes the target from it).
tc_parallel_hold :: proc(k: ^TC, d: Dest, span: Span) -> Dest {
    b := tc_building(k)
    if b == nil || k.parallel == nil { return d }
    t := graph_dest_type(b, d)
    slot := graph_slot(b, "parallel", t, span)
    append(k.parallel, TC_Held{d, slot, t, span})
    return graph_dest_var("parallel", slot, t)
}
