package mara

// Lowering the rest of the calls and of the writes: a method's call, a
// dispatch's, a call's several results destructured, a broadcast, a
// parallel assignment, a take.

// `x.f(args)` (tc_method_call): its receiver built first when it is a value
// the method was found through (Annotations.receivers) and the call's first
// argument — else none of it built — then the call.
lw_method_call :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span, addressed := Tree_Id(0)) -> Built {
    tr := k.t
    mv := method_view(tr, n)
    saved := k.lower.recv
    k.lower.recv = {}
    defer k.lower.recv = saved
    recv := mv.receiver
    arg := addressed if addressed != 0 else recv
    given := k.annot.args[tc_sid(k, n)] or_else nil
    found_through := k.annot.receivers[tc_sid(k, n)] or_else false
    // (Its arguments as the call takes them: the receiver first when the
    // method takes Self, or when it is no method — a fun, a builtin, called
    // on its first argument.)
    args := mv.args
    form := k.annot.forms[tc_sid(k, n)] or_else .Fun
    switch {
    case found_through && form == .Builtin:
        args = tc_with_receiver(arg, mv.args)
    case len(given) > 0 && (given[0].node == arg || given[0].node == recv) && given[0].kind != .Default:
        args = tc_with_receiver(given[0].node, mv.args)
    }
    if found_through {
        qt := tc_node_type(k, addressed if addressed != 0 else recv)
        k.lower.recv = {node = arg, t = qt}
        if len(args) > 0 && args[0] == arg {
            if addressed != 0 {
                k.lower.recv.r = lw_unary(k, addressed, .Either, w, of = recv)
            } else {
                k.lower.recv.r = lw_expr(k, recv, .Either, w)
            }
        }
    }
    return lw_call_core(k, n, tc_call_name(k, n), args, want, w, dest, temp, temp_span)
}

// A dispatch's call (tc_dispatch_call): each argument as it is — a `_`, the
// default the chosen function has there — then the call.
lw_dispatch_call :: proc(k: ^TC, n: Tree_Id, args: []Tree_Id, want: Build_Want, w: Written) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    if want == .Place { lw_fail(k, n, "a call's place") }
    ft := tc_callee(k, n)
    ret := fn_primary_return(ft)
    default_at :: proc(k: ^TC, def: Tree_Id, w: Written, at: Span) -> (Type, Built) {
        if k.t.tag[def] == .Hash_Name { return lw_hash_name_type(k, def), lw_hash_name(k, def, .Either, w, at) }
        return tc_node_type(k, def), lw_expr(k, def, .Either, .Implied)
    }
    vals := make([dynamic]Operand, context.temp_allocator)
    array_values := make([dynamic]bool, context.temp_allocator)
    for a, i in args {
        if tr.tag[a] == .Ident && tc_name(k, a) == "_" {
            def := ft.params[i].default_node
            t, r := default_at(k, def, w, tree_span(tr, a))
            append(&vals, lw_value_as(k, def, t, r, ft.params[i].type_, span, {sig = ft, param = i}))
            append(&array_values, false)
            continue
        }
        r := lw_arg(k, a, .Either, w)
        t := lw_arg_type(k, a)
        _, is_array := distinct_base(t).(^Type_Fixed_Array)
        u := tc_unparen(k, a)
        if tr.tag[u] == .Index && is_byte_buffer(tc_node_type(k, Tree_Id(tr.a[u]))) ||
           tr.tag[u] == .Slice && is_byte_buffer(tc_node_type(k, Tree_Id(tr.a[u]))) {
            lw_fail(k, a, "bytes as a dispatch's argument")
        }
        at := lw_at(k, a)   // (its read and its widening: the argument's)
        append(&vals, graph_build_as(b, r.v, r.place, t, tree_span(tr, a), span, {sig = ft, param = i}))
        b.at = at
        append(&array_values, is_array && !r.place)
    }
    for i := len(args); i < len(ft.params); i += 1 {
        def := ft.params[i].default_node
        t, r := default_at(k, def, w, span)
        append(&vals, lw_value_as(k, def, t, r, ft.params[i].type_, span, {sig = ft, param = i}))
    }
    if build_views_value(ft, array_values[:]) { lw_fail(k, n, "an array's value viewed by a dispatch's param") }
    return {v = {graph_call_op(b, .Call, w, span, ft, ret, ..vals[:]), 0}, ok = true}
}

// A compiler name's type (tc_hash_name's): text's, else a bool.
lw_hash_name_type :: proc(k: ^TC, n: Tree_Id) -> Type {
    switch tc_text(Token_Id(k.t.a[n])) {
    case "caller_name", "caller_span": return new_clone(Type_Ptr{elem = Type_Byte{}})
    }
    return Type_Bool{}
}

// `a, b := f()`, `x, err = f()`, `v, w := f()?` (tc_destructure): the names
// it declares made first, then the call, then each output written. One value
// of no several results: a broadcast.
lw_destructure :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool, fields_of: ^Type_Scope = nil) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    names := make([]string, len(targets), context.temp_allocator)
    stores := make([]bool, len(targets), context.temp_allocator)
    toks := make([]Token_Id, len(targets), context.temp_allocator)
    for tg, i in targets {
        if t.tag[tg] == .Ident { names[i], toks[i] = tc_name(k, tg), tc_ref(k, tg).decl } else { stores[i] = true }
    }
    v := tc_unparen(k, value)
    is_try := t.tag[v] == .Try && tc_is_call(k, tc_unparen(k, Tree_Id(t.a[v])))
    of_call := tc_is_call(k, v)
    // (A value of no several results: a broadcast, nothing of it built here.)
    returns: []Type
    if !is_try {
        returns = tc_call_returns(k, value, nil)
        if returns == nil {
            lw_broadcast(k, s, targets, value, is_decl)
            return
        }
    }
    mr: Graph_Destructure
    if is_try || of_call { mr = graph_build_destructure(b, tc_sid(k, s), span, names, toks, stores, is_decl) }
    if is_try {
        call := tc_unparen(k, Tree_Id(t.a[v]))
        r := lw_expr(k, call, .Value)
        if mr.on {
            if !r.ok { lw_fail(k, v, "a `?` on no call built") }
            graph_retype(b, r.v.op, nil)
            at := lw_at(k, v)   // (the `?`'s branch and return: its)
            mr.call = graph_try_after(b, tree_span(t, v), r.v)
            b.at = at
        }
        rets := tc_call_returns(k, call, nil)
        returns = rets[:len(rets) - 1]
    } else {
        r: Built
        if of_call { r = lw_expr(k, value, .Value) }
        mr.call = r.v
    }
    for tg, i in targets {
        rt := solidify_type(returns[i])
        if names[i] == "" { mr.place = lw_expr(k, tg, .Place).v }
        if mr.on { graph_build_destructure_write(b, &mr, i, distinct_base(rt)) }
    }
}

// `a, b = v`, `x, y := v` (tc_broadcast): v to each target, each a statement
// of its own.
lw_broadcast :: proc(k: ^TC, s: Tree_Id, targets: []Tree_Id, value: Tree_Id, is_decl: bool) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    graph_build_stmt_none(b)
    for tg in targets {
        declares := is_decl && t.tag[tg] == .Ident
        kind := Stmt_Kind.Decl if declares else lw_assign_kind(k, tg)
        saved := graph_build_stmt(b, span, kind)
        if declares { lw_decl_one(k, s, tg, value, 0, nil) } else { lw_assign_one(k, s, tg, value) }
        graph_build_stmt_end(b, saved)
    }
}

// `a, b = c, d` (tc_assign): every value in first, each held at its
// target's type, then each target written from its own.
lw_parallel_assign :: proc(k: ^TC, s: Tree_Id, targets, values: []Tree_Id) {
    b := k.gb
    span := tree_span(k.t, s)
    held := make([dynamic]LW_Held, context.temp_allocator)
    saved := k.lower.parallel
    k.lower.parallel = &held
    for tg, i in targets {
        saved_stmt := graph_build_stmt(b, span, lw_assign_kind(k, tg))
        lw_assign_one(k, s, tg, values[i])
        graph_build_stmt_end(b, saved_stmt)
    }
    k.lower.parallel = saved
    for h in held {
        v := graph_read(b, graph_var(b, "parallel", h.slot, h.t, h.span), h.t, h.span)
        graph_build_write_at(b, graph_dest_place(b, h.d, h.span), v, h.span)
    }
}

// An assignment's statement kind, by its target: a place's a write; `_`'s
// and this_program's no assignment.
lw_assign_kind :: proc(k: ^TC, target: Tree_Id) -> Stmt_Kind {
    if k.t.tag[target] != .Ident { return .Write }
    if name := tc_name(k, target); name == "_" || name == "this_program" { return .Other }
    return .Assign
}

LW_Held :: struct {
    d:    Dest,
    slot: Node_Id,
    t:    Type,
    span: Span,
}

// A store assigned together with others: into a temporary of its own, at
// its target's type (lw_parallel_assign writes the target from it).
lw_parallel_hold :: proc(k: ^TC, d: Dest, span: Span) -> Dest {
    if k.lower.parallel == nil { return d }
    b := k.gb
    t := graph_dest_type(b, d)
    slot := graph_slot(b, "parallel", t, span)
    append(k.lower.parallel, LW_Held{d, slot, t, span})
    return graph_dest_var("parallel", slot, t)
}

// A take (tc_take): the count at the header's width, then the storage it
// carves from, then the carve.
lw_take :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    t := k.t
    b := k.gb
    span := tree_span(t, n)
    ty, storage := Tree_Id(t.a[n]), Tree_Id(t.b[n])
    count := Tree_Id(0)
    switch {
    case ty == 0:
    case t.tag[ty] == .Type_Slice && t.a[ty] != 0:
        count = Tree_Id(t.a[ty])
    }
    if want == .Place || !lw_carves_place(k, storage) { lw_fail(k, n, "a take's place, or a take from no plain place") }
    count_op := NO_VALUE
    if count != 0 { count_op = lw_bound(k, count, w, span) }
    su := tc_unparen(k, storage)
    addressed := t.tag[su] == .Unary
    from: Operand
    if addressed {   // (`&x`: x's place, what it carves from)
        if build_tokens[t.main[su]].kind != .Ampersand || tc_callee(k, su) != nil { lw_fail(k, storage, "a take's `&` that takes no address") }
        from = lw_expr(k, Tree_Id(t.a[su]), .Place, temp_span = tree_span(t, su)).v
    } else {
        from = lw_expr(k, storage, .Place).v
    }
    st := tc_node_type(k, storage)
    taken := tc_node_type(k, n)
    v := graph_build_carve(b, span, tc_text(t.main[n]), taken, from, st, addressed, t.tag[su] == .Self, count_op, w)
    return {v = v, ok = true}
}

// Whether a take's storage is a plain place (`&s`, `&bytes[i]`, `s`): what
// is walked where the carve is.
lw_carves_place :: proc(k: ^TC, storage: Tree_Id) -> bool {
    su := tc_unparen(k, storage)
    if k.t.tag[su] == .Unary && build_tokens[k.t.main[su]].kind == .Ampersand { return lw_pure_place(k, Tree_Id(k.t.a[su])) }
    return lw_pure_place(k, storage)
}

// `x := let(T, s)`, `x : T = slice([:n]T, s)` (tc_decl_take): the local bound
// to the memory taken, the take into it.
lw_decl_take :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, fields_of: ^Type_Scope) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    decl := lw_field_decl(k, fields_of, name, target, value, span)
    field := decl != NO_NODE
    if !field { decl = graph_build_decl(b, name, t.main[target], span, tc_node_type(k, target), bound = tc_text(t.main[tc_unparen(k, value)]) == "let") }
    r := lw_expr(k, value, .Into, dest = graph_dest_var(name, decl, nil if is_untyped(ann) else ann))
    final := tc_node_type(k, target)
    if field { final = graph_type(b.g, decl) }
    graph_build_typed(b, decl, final)
    lw_store(k, value, tc_node_type(k, value), r, graph_dest_var(name, decl, final), span, settle = true)
}
