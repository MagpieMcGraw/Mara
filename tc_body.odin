package mara

// Bodies: a fun's, checked and built statement by statement in the order
// they run (its graph is built as it is checked, through the builder).

tc_fun_body :: proc(k: ^TC, fn: ^TC_Fun) {
    t := k.t
    ft := fn.ft
    v := scope_view(t, fn.fun)
    span := tree_span(t, fn.def)
    f: ^Graph_Fuse
    if k.gb != nil { f = graph_fuse_begin(k.gb, ft, syntax_id(fn.def), span, v.intrinsic != 0, .Explicit) }
    defer if f != nil {
        if k.c.errors > 0 { graph_fuse_fail(k.gb, f, "errors") }
        graph_fuse_end(k.gb, f)
    }
    if v.intrinsic != 0 { return }
    body := type_env_block_child(ft)
    for p in ft.params { type_env_set(body, p.name, p.type_) }
    tc_scope(k, v.body, body)
}

// A block's statements: each checked whole, and built, before the next.
tc_scope :: proc(k: ^TC, stmts: []Tree_Id, env: ^Type_Scope) {
    t := k.t
    for s in stmts {
        if t.tag[s] == .Define {
            tc_unsupported(k, s, "a definition in a body")
            continue
        }
        b := tc_building(k)
        saved: i32
        if b != nil {
            span := tree_span(t, s)
            graph_fuse_body_stmt(b, span, true)
            saved = graph_fuse_stmt(b, syntax_id(s), span, tc_stmt_kind(k, s), fresh = true)
        }
        tc_stmt(k, s, env)
        if b != nil { graph_fuse_stmt_end(b, saved) }
    }
}

tc_stmt :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        rt, _ := tc_expr(k, e, env, .Value)
        // A call's value, dropped: `_ = f()` says so.
        if t.tag[e] == .Call && rt != nil {
            _, is_void := rt.(Type_Void)
            _, is_error := rt.(Type_Error)
            if !is_void && !is_error { tc_error(k, span, TYPE_DISCARDED_RETURN, tc_name(k, e)) }
        }
    case .Decl:
        tc_decl(k, s, env)
    case .Assign:
        tc_assign(k, s, env)
    case .Return:
        tc_return(k, s, env)
    case .If, .Elif:
        tc_if(k, s, env)
    case:
        tc_unsupported(k, s, "this statement")
    }
}

// `x := v`, `x : T = v`: its local, then its value built into it, then
// stored — once the statement is checked (its type known).
tc_decl :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := decl_view(t, s)
    if len(v.targets) != 1 || len(v.values) != 1 || t.tag[v.targets[0]] != .Ident {
        tc_unsupported(k, s, "this declaration")
        return
    }
    name := tc_name(k, v.targets[0])
    value := v.values[0]
    if t.tag[value] == .Ident && tc_name(k, value) == "void" {
        tc_unsupported(k, s, "a `void` declaration")
        return
    }
    ann: Type = Type_Any{}
    if v.type_ != 0 { ann = tc_type(k, v.type_, env, span) }
    if name in k.table.constants {
        tc_error(k, span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, name)
        return
    }
    b := tc_building(k)
    decl := NO_NODE
    prefix: [2]Node_Id
    prefixed := false
    if b != nil {
        decl = graph_fuse_decl(b, name, span)
        // Text fills only a prefix of a new partial array: it is zero first
        // — kept once the value's type says so.
        #partial switch t.tag[value] {
        case .String, .Ident, .Field:
            if is_untyped(ann) { prefix, prefixed = graph_fuse_prefix(b, name, decl, span), true }
        }
        if !prefixed && is_partial_array(ann) { prefix, prefixed = graph_fuse_prefix(b, name, decl, span), true }
    }
    k.hint = ann
    errors_before := k.c.errors
    want := Fuse_Want.Into if b != nil else .None
    vt, r := tc_expr(k, value, env, want, dest = graph_dest_var(name, decl, nil if is_untyped(ann) else ann), temp_span = span)
    final: Type
    if !is_any(ann) {
        if !coerce_deferred(k.c, vt, ann, span) && types_incompatible(ann, vt) && !value_preserving_widen(vt, ann) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(ann))
        }
        if is_infer(vt) { tc_literal_overflow(k, value, ann, span) }
        final = ann
    } else {
        _, prior, declared := type_env_locate_below_module(env, name)
        _ = prior
        if declared {
            tc_error(k, span, TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING, name)
            return
        }
        if is_infer(vt) {
            // Its width is the one its first concrete use decides.
            cell := new(Infer_Cell)
            cell.name, cell.span = name, span
            if src := infer_cell_of(vt); src != nil { unify_infer_cells(k.c, cell, src, span) }
            if _, is_float := vt.(Type_Infer_Float); is_float {
                final = Type_Infer_Float{cell = cell}
            } else {
                final = Type_Infer_Int{cell = cell}
            }
        } else {
            final = solidify_type(vt)
            if is_untyped(final) && k.c.errors == errors_before {
                check_warning(k.c, span, TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING, name)
            }
            if is_cstring(final) { tc_error(k, span, TYPE_CSTRING_FOREIGN_ONLY) }
        }
    }
    type_env_set(env, name, final)
    if b = tc_building(k); b == nil { return }
    graph_fuse_typed(b, decl, final)
    wrote := tc_store(k, value, vt, r, graph_dest_var(name, decl, final), span, settle = true)
    if prefixed {
        fills := is_partial_array(final) && (t.tag[value] == .String || is_slice_type(vt))
        graph_fuse_prefix_end(b, prefix, wrote && fills, final)
    }
}

is_slice_type :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Slice)
    return ok
}

// A built value stored where it goes: at the destination's type (a number
// widened to it).
tc_store :: proc(k: ^TC, e: Tree_Id, t: Type, r: Fused, d: Dest, span: Span, settle := false) -> bool {
    b := tc_building(k)
    if b == nil || r.into { return false }
    if r.temp {
        graph_fuse_write_at(b, graph_dest_place(b, d, span), r.v, span)
        return true
    }
    dt := graph_dest_type(b, d)
    if !fuse_scalar(dt) && !is_partial_array(dt) {
        tc_fail(k, "a store of this type")
        return false
    }
    if is_partial_array(dt) && !(k.t.tag[e] == .String && is_partial_array(t)) {
        tc_fail(k, "a partial array's store")
        return false
    }
    val := graph_fuse_widen(b, tc_value(k, r, e, t), span, {to = dt, settle_to = settle})
    graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
    return true
}

// `x = v`: the value, then the write, at the variable's type.
tc_assign :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) != 1 || len(values) != 1 || t.tag[targets[0]] != .Ident {
        tc_unsupported(k, s, "this assignment")
        return
    }
    name := tc_name(k, targets[0])
    value := values[0]
    existing, loc, found := type_env_locate(env, name)
    if !found {
        tc_error(k, span, TYPE_UNDEFINED_IDENTIFIER, name)
        tc_check(k, value, env)
        return
    }
    if loc != nil && loc.kind == .Struct {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    b := tc_building(k)
    want := Fuse_Want.Into if b != nil else .None
    vt: Type = distinct_base(existing) if !is_untyped(existing) else nil
    val_type, r := tc_expr(k, value, env, want, dest = graph_dest_var(name, NO_NODE, vt), temp = true, temp_span = span)
    if !coerce_deferred(k.c, val_type, existing, span) && !coerce_deferred(k.c, existing, val_type, span) &&
       types_incompatible(existing, val_type) && !value_preserving_widen(val_type, existing) {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(val_type), name, type_name(existing))
    }
    if is_infer(val_type) { tc_literal_overflow(k, value, existing, span) }
    tc_store(k, value, val_type, r, graph_dest_var(name, NO_NODE, existing), span)
}

// `return a, b`: each value at its result's type (trailing errs implied `.Ok`).
tc_return :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    values := tree_list(t, t.a[s])
    rts := enclosing_return_types(env)
    expected, supplied := len(rts), len(values)
    trailing_errs := 0
    for i := expected - 1; i >= 0 && is_err_type(rts[i]); i -= 1 { trailing_errs += 1 }
    least := expected - trailing_errs
    count_ok := true
    switch {
    case expected == 0 && supplied > 0, expected == 1 && supplied > 1:
        tc_error(k, span, TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN)
        count_ok = false
    case expected == 1 && supplied == 0 && least > 0, expected > 1 && (supplied > expected || supplied < least):
        tc_error(k, span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED, supplied, expected)
        count_ok = false
    }
    vals := make([dynamic]Operand, 0, supplied, context.temp_allocator)
    if count_ok {
        for val, i in values {
            want := rts[i]
            if is_partial_array(want) || is_slice_type(want) || !fuse_scalar(want) {
                tc_unsupported(k, s, "a return of this type")
                return
            }
            k.hint = want
            vt, r := tc_expr(k, val, env, .Either if tc_building(k) != nil else .None, temp_span = span)
            if b := tc_building(k); b != nil {
                append(&vals, graph_fuse_widen(b, tc_value(k, r, val, vt), span, {to = want}))
            }
            if !is_any(vt) && !is_any(want) && !coerce_deferred(k.c, vt, want, span) &&
               !types_equal(want, vt) && !value_preserving_widen(vt, want) {
                if expected > 1 {
                    tc_error(k, span, TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED, i + 1, type_name(vt), type_name(want))
                } else {
                    tc_error(k, span, TYPE_RETURN_TYPE_MATCH_EXPECTED, type_name(vt), type_name(want))
                }
            }
            if is_infer(vt) { tc_literal_overflow(k, val, want, span) }
        }
    }
    if b := tc_building(k); b != nil { graph_fuse_return(b, vals[:], span) }
}

// `if c {…} elif d {…} else {…}`: the branch, then each block as it is
// checked (an elif, the else block's one statement).
tc_if :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := if_view(t, s)
    if v.hash != 0 {
        tc_unsupported(k, s, "`#if`")
        return
    }
    ct, cond := tc_expr(k, v.cond, env, .Value if tc_building(k) != nil else .None)
    if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL_2, type_name(ct)) }
    b := tc_building(k)
    fi: Graph_If
    if b != nil { fi = graph_fuse_if(b, cond.v, span, len(v.else_) > 0) }
    tc_scope(k, v.then, type_env_block_child(env))
    if b != nil { graph_fuse_else(b, &fi, span) }
    if len(v.else_) > 0 { tc_scope(k, v.else_, type_env_block_child(env)) }
    if b != nil { graph_fuse_if_end(b, &fi) }
}
