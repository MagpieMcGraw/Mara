package mara

import "core:strings"

// `x.f(args)`, resolved by its qualifier: a function of the type, module or
// type path x names (`Type.f`, `mod.f`, `Outer.Inner.f`: a static call — by
// a struct's value, an instance's, x its first argument when it takes Self);
// a type it holds (`Outer.Inner()`: construction); a module's dispatch; else
// x a value, checked here — a method of its struct's, or `f(x, args)`.
// (`addressed`: the `&` written around the call — `&x.f()`, x's address the
// receiver, a value.)

tc_method_call :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, addressed := Tree_Id(0)) -> Type {
    tr := k.t
    if addressed != 0 {
        if n in k.addressed_calls { return Type_Error{} }   // (inside itself: said where it began)
        k.addressed_calls[n] = true
    }
    defer if addressed != 0 { delete_key(&k.addressed_calls, n) }
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
    recv := mv.receiver
    arg := addressed if addressed != 0 else recv   // (the receiver, as an argument)
    args := mv.args
    qual: ^Type_Scope
    qual_dispatch: []string
    resolved, failed := false, false
    if q := tc_unparen(k, recv); addressed == 0 && tr.tag[q] == .Ident {
        qname := tc_name(k, q)
        if qt, found := scope_lookup(env, qname); found {
            tc_set_ref(k, q, scope_find_ref(env, qname))
            // (`Shape.Rect(5)`: the union's variant built by its params.)
            if ut, is_union := qt.(^Type_Union); is_union && name in ut.tag_map { return tc_variant_call(k, n, ut, name, args, env) }
            if qsd := as_scope_body(qt); qsd != nil {
                if fn, has := qsd.functions[name]; has && fn != nil {
                    // (Named by its type, a static call; by a value of it,
                    // an instance's when it takes Self.)
                    qual, resolved = fn, true
                    k.annot.call_names[tc_sid(k, n)] = fn.name
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
                    tc_error(k, span, TYPE_MODULE_FUNCTION, scope_display_name(qsd), name)
                    return Type_Error{}
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
                    k.annot.call_names[tc_sid(k, n)] = fn.name
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
                k.annot.call_names[tc_sid(k, n)] = fn.name
            }
        }
    }
    if !resolved {
        // (A value: a method of its struct's, else `f(x, args)`.)
        qt := tc_unary(k, addressed, env, of = recv) if addressed != 0 else tc_check(k, recv, env)
        k.recv = {node = arg, t = qt}
        k.annot.receivers[tc_sid(k, n)] = true   // (checked as a value, before its method is found)
        tc_struct_of(k, qt)
        if st := resolve_to_struct_type(k.c, qt); st != nil {
            if fn, has := st.functions[name]; has && fn != nil {
                qual, resolved = fn, true
                k.annot.call_names[tc_sid(k, n)] = fn.name
                args, failed = tc_self_args(k, n, fn, st, qt, arg, args)
            }
        }
        if !resolved { args = tc_with_receiver(arg, args) }
    }
    if failed { return Type_Error{} }
    callee_name := tc_call_name(k, n)
    return tc_call_core(k, n, callee_name, args, env, qual, qual_dispatch)
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
        owner := scope_display_name(sd)
        method := strings.concatenate({owner, ".", fn.source_name if fn.source_name != "" else fn.name}, context.temp_allocator)
        tc_error(k, tree_span(k.t, n), TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE, method, owner)
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
    k.annot.call_names[tc_sid(k, n)] = type_flat_name(t)
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
