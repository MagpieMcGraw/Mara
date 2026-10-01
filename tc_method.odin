package mara

// `x.f(args)`, resolved by its qualifier: a function of the type, module or
// type path x names (`Type.f`, `mod.f`, `Outer.Inner.f`: a static call — by
// a struct's value, an instance's, x its first argument when it takes Self);
// a type it holds (`Outer.Inner()`: construction); a module's dispatch; else
// x a value, built here — a method of its struct's, or `f(x, args)`. The
// receiver's build dropped where it is no argument. (`addressed`: the `&`
// written around the call — `&x.f()`, x's address the receiver, a value.)

tc_method_call :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Build_Want, w: Written,
                       dest: Dest, temp: bool, temp_span: Span, addressed := Tree_Id(0)) -> (Type, Built) {
    tr := k.t
    span := tree_span(tr, n)
    mv := method_view(tr, n)
    name := tc_text(mv.name)
    saved := k.recv
    k.recv = {}
    defer k.recv = saved
    // (A call of several results, as one argument: its extras would be lost.)
    for a in mv.args {
        if returns := tc_call_returns(k, a, env); len(returns) > 1 {
            tc_error(k, tree_span(tr, tc_unparen(k, a)), TYPE_MULTI_RETURN_AS_ARG, len(returns))
        }
    }
    b := tc_building(k)
    build := want != .None && b != nil
    mark: Graph_Mark
    if build { mark = graph_build_mark(b) }
    recv := mv.receiver
    arg := addressed if addressed != 0 else recv   // (the receiver, as an argument)
    args := mv.args
    qual: ^Type_Scope
    qual_dispatch: []string
    resolved, failed := false, false
    if q := tc_unparen(k, recv); addressed == 0 && tr.tag[q] == .Ident {
        qname := tc_name(k, q)
        if qt, found := scope_lookup(env, qname); found {
            if qsd := as_scope_body(qt); qsd != nil {
                if fn, has := qsd.functions[name]; has && fn != nil {
                    // (Named by its type, a static call; by a value of it,
                    // an instance's when it takes Self.)
                    qual, resolved = fn, true
                    k.call_names[n] = fn.name
                    flat := resolve_type_name(k.pkg, qname, "", env)
                    is_type := flat != "" && (flat in k.table.structs || flat in k.table.funs)
                    if !is_type && !sd_is_module(qsd) {
                        args, failed = tc_self_args(k, n, fn, qsd, qt, recv, args)
                    }
                } else if t, holds := qsd.types[name]; holds {
                    qual, resolved = tc_held_type(k, n, t), true
                    failed = qual == nil
                } else if fns, dispatches := qsd.dispatch_groups[name]; dispatches {
                    qual_dispatch, resolved = fns[:], true
                } else if sd_is_module(qsd) {
                    tc_error(k, span, TYPE_MODULE_FUNCTION, qsd.name, name)
                    return Type_Error{}, {}
                }
            }
        }
        // (A type the module has, bound nowhere the env sees.)
        if !resolved {
            flat := resolve_type_name(k.pkg, qname, "", env)
            sd: ^Scope_Body
            if ss, is_struct := k.table.structs[flat]; is_struct { sd = &ss.sd } else if sf, is_fun := k.table.funs[flat]; is_fun { sd = &sf.sd }
            if sd != nil {
                if fn, has := sd.functions[name]; has && fn != nil {
                    qual, resolved = fn, true
                    k.call_names[n] = fn.name
                }
            }
        }
    }
    if !resolved && addressed == 0 && tr.tag[tc_unparen(k, recv)] == .Field {
        if qsd := tc_type_path_scope(k, recv, env); qsd != nil {
            if t, holds := qsd.types[name]; holds {
                qual, resolved = tc_held_type(k, n, t), true
                failed = qual == nil
            } else if fn, has := qsd.functions[name]; has && fn != nil {
                qual, resolved = fn, true
                k.call_names[n] = fn.name
            }
        }
    }
    if !resolved {
        // (A value: a method of its struct's, else `f(x, args)`.)
        ask: Build_Want = .Either if build else .None
        qt: Type
        qr: Built
        if addressed != 0 { qt, qr = tc_unary(k, addressed, env, ask, w, of = recv) } else { qt, qr = tc_expr(k, recv, env, ask, w) }
        k.recv = {node = arg, t = qt, r = qr}
        tc_struct_of(k, qt)
        if st := resolve_to_struct_type(k.c, qt); st != nil {
            if fn, has := st.functions[name]; has && fn != nil {
                qual, resolved = fn, true
                k.call_names[n] = fn.name
                args, failed = tc_self_args(k, n, fn, st, qt, arg, args)
            }
        }
        if !resolved { args = tc_with_receiver(arg, args) }
    }
    if build && k.recv.r.ok && (len(args) == 0 || args[0] != arg) {
        if bb := tc_building(k); bb != nil { graph_build_drop_since(bb, mark) }
    }
    if failed { return Type_Error{}, {} }
    callee_name := tc_call_name(k, n)
    return tc_call_core(k, n, callee_name, args, env, want, w, dest, temp, temp_span, qual, qual_dispatch)
}

// An instance's method: x its first argument, when the method takes Self (a
// pointer to it, x must be one).
tc_self_args :: proc(k: ^TC, n: Tree_Id, fn: ^Type_Scope, sd: ^Scope_Body, qt: Type, recv: Tree_Id,
                     args: []Tree_Id) -> ([]Tree_Id, bool) {
    if len(fn.params) == 0 { return args, false }
    inner := fn.params[0].type_
    pt, wants_ptr := inner.(^Type_Ptr)
    if wants_ptr { inner = pt.elem }
    if as_scope_body(inner) != sd { return args, false }
    if _, is_ptr := qt.(^Type_Ptr); wants_ptr && !is_ptr {
        tc_error(k, tree_span(k.t, n), TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE, fn.name, sd.name)
        return args, true
    }
    return tc_with_receiver(recv, args), false
}

tc_with_receiver :: proc(recv: Tree_Id, args: []Tree_Id) -> []Tree_Id {
    out := make([]Tree_Id, len(args) + 1, context.temp_allocator)
    out[0] = recv
    copy(out[1:], args)
    return out
}

// A type a scope holds, called: its constructor.
tc_held_type :: proc(k: ^TC, n: Tree_Id, t: Type) -> ^Type_Scope {
    k.call_names[n] = type_flat_name(t)
    if ts, is_scope := t.(^Type_Scope); is_scope { return ts }
    tc_unsupported(k, n, "a call of a scope's type")
    return nil
}

// The scope a type path names (`Outer.Inner`): its root a scope the env
// binds, else a type the module has; each further name a type it holds.
tc_type_path_scope :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> ^Scope_Body {
    tr := k.t
    q := tc_unparen(k, n)
    #partial switch tr.tag[q] {
    case .Ident:
        name := tc_name(k, q)
        if t, found := scope_lookup(env, name); found {
            if sd := as_scope_body(t); sd != nil { return sd }
        }
        flat := resolve_type_name(k.pkg, name, "", env)
        if ss, is_struct := k.table.structs[flat]; is_struct { return &ss.sd }
        if sf, is_fun := k.table.funs[flat]; is_fun { return &sf.sd }
    case .Field:
        sd := tc_type_path_scope(k, Tree_Id(tr.a[q]), env)
        if sd == nil { return nil }
        if t, found := sd.types[tc_text(Token_Id(tr.b[q]))]; found { return as_scope_body(t) }
    }
    return nil
}
