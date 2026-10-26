package mara

import "core:slice"
import "core:strings"

// `x.f(args)`, resolved by its qualifier: a function of the type, module or
// type path x names (`Type.f`, `mod.f`, `Outer.Inner.f`: a static call — by
// a struct's value, an instance's, x its first argument when it takes Self);
// a type it holds (`Outer.Inner()`: construction); a module's dispatch; else
// x a value, checked here — a method of its struct's, or `f(x, args)`.
// (`addressed`: the `&` written around the call — `&x.f()`, x's address the
// receiver, a value.)

tc_method_call :: proc(k: ^TC, n: Tree_Id, addressed := Tree_Id(0)) -> Type {
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
    recv := mv.receiver
    arg := addressed if addressed != 0 else recv   // (the receiver, as an argument)
    args := mv.args
    qual: ^Type_Scope
    qual_dispatch: []TC_Member
    resolved, failed := false, false
    if q := tc_unparen(k, recv); addressed == 0 && tr.tag[q] == .Ident {
        qname := tc_name(k, q)
        qref := k.rs.refs[q]
        qt, found := tc_ref_type(k, qref, qname)
        if found {
            tc_set_ref(k, q, qref)
            // (`Shape.Rect(5)`: the union's variant built by its params.)
            if ut, is_union := qt.(^Type_Union); is_union && name in ut.tag_map { return tc_variant_call(k, n, ut, name, args) }
            // (`Mode.from_text(s)`: the enum's variant a text names.)
            if name == "from_text" && qref.kind == .Type {
                if ft := tc_from_text_fun(qt); ft != nil {
                    qual, resolved = ft, true
                    k.annot.call_names[tc_sid(k, n)] = ft.name
                }
            }
            if qsd := as_scope_body(qt); !resolved && qsd != nil && tc_names_def(qref) {
                // (Through a module or a type: its member, the resolver's.)
                mref := k.rs.refs[n]
                mt, has := tc_ref_type(k, mref, name)
                if mref.kind == .Fun && k.rs.dispatches[mref.decl] {
                    qual_dispatch, resolved = tc_dispatch_members(k, {mref.decl}), true
                } else if fn, is_fun := mt.(^Type_Scope); has && mref.kind == .Fun && is_fun {
                    qual, resolved = fn, true
                    k.annot.call_names[tc_sid(k, n)] = fn.name
                } else if tmpl, is_template := tc_template(k, mref); mref.kind == .Fun && is_template && k.t.tag[tmpl.node] == .Fun_Def {
                    return tc_generic_call(k, n, name, tmpl, args)   // (`gl.BufferData(…, data)`: a generic fun a module has)
                } else if et := tc_held_enum(mt); has && mref.kind == .Type && et != nil {
                    return tc_enum_number(k, n, name, et, args)   // (`gl.GL_Tex_Param(n)`)
                } else if has && mref.kind == .Type {
                    qual, resolved = tc_held_type(k, n, mt), true
                    failed = qual == nil
                } else if sd_is_module(qsd) {
                    if resolve_module_foreign(k.rs, qsd.name, name) {
                        tc_error(k, span, TYPE_FOREIGN_FUN_PRIVATE, name, scope_display_name(qsd))
                    } else {
                        tc_error(k, span, TYPE_MODULE_FUNCTION, scope_display_name(qsd), name)
                    }
                    return Type_Error{}
                }
            } else if qsd := as_scope_body(qt); qsd != nil {
                if fn, has := qsd.functions[name]; has && fn != nil {
                    // (Named by its type, a static call; by a value of it,
                    // an instance's when it takes Self.)
                    qual, resolved = fn, true
                    k.annot.call_names[tc_sid(k, n)] = fn.name
                    is_type := qref.kind == .Type || qref.kind == .Fun
                    if !is_type && !sd_is_module(qsd) {
                        args, failed = tc_self_args(k, n, fn, qsd, qt, recv, args)
                    }
                } else if t, holds := qsd.types[name]; holds {
                    if et := tc_held_enum(t); et != nil { return tc_enum_number(k, n, name, et, args) }
                    qual, resolved = tc_held_type(k, n, t), true
                    failed = qual == nil
                }
            }
        }
    }
    if !resolved && addressed == 0 && tr.tag[tc_unparen(k, recv)] == .Field && tc_names_def(k.rs.refs[tc_unparen(k, recv)]) {
        // (`Outer.Inner.f()`, `m.T.f()`: its member, the resolver's. `m.E.from_text(s)`:
        // the enum's variant a text names.)
        mref := k.rs.refs[n]
        q := tc_unparen(k, recv)
        if name == "from_text" && k.rs.refs[q].kind == .Type {
            if qt, is_type := tc_ref_type(k, k.rs.refs[q], tc_text(Token_Id(tr.b[q]))); is_type {
                if ft := tc_from_text_fun(qt); ft != nil {
                    qual, resolved = ft, true
                    k.annot.call_names[tc_sid(k, n)] = ft.name
                }
            }
        }
        if resolved {
            // (from_text's, above)
        } else if mt, has := tc_ref_type(k, mref, name); has && mref.kind == .Type {
            if et := tc_held_enum(mt); et != nil { return tc_enum_number(k, n, name, et, args) }
            qual, resolved = tc_held_type(k, n, mt), true
            failed = qual == nil
        } else if fn, is_fun := mt.(^Type_Scope); has && mref.kind == .Fun && is_fun {
            qual, resolved = fn, true
            k.annot.call_names[tc_sid(k, n)] = fn.name
        }
    }
    if !resolved {
        // (A value: a method of its struct's, else `f(x, args)`.)
        qt := tc_unary(k, addressed, of = recv) if addressed != 0 else tc_check(k, recv)
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
        // (`m.text()`, `e.text()`: an enum's or an err's name.)
        if !resolved && name == "text" && len(args) == 0 {
            if ft := tc_text_fun(k, qt); ft != nil {
                qual, resolved = ft, true
                k.annot.call_names[tc_sid(k, n)] = ft.name
                args = tc_with_receiver(arg, args)
            }
        }
        if !resolved { args = tc_with_receiver(arg, args) }
    }
    if failed { return Type_Error{} }
    callee_name := tc_call_name(k, n)
    return tc_call_core(k, n, callee_name, args, qual, qual_dispatch)
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

// Whether a receiver of type `at` is the struct its method's Self param `pt`
// takes — a distinct struct's is its base's — by value or through a pointer.
tc_own_receiver :: proc(at, pt: Type) -> bool {
    a, p := distinct_base(at), distinct_base(pt)
    if ap, is_ptr := a.(^Type_Ptr); is_ptr {
        pp, also := p.(^Type_Ptr)
        if !also { return false }
        a, p = distinct_base(ap.elem), distinct_base(pp.elem)
    }
    as, a_ok := a.(^Type_Scope)
    ps, p_ok := p.(^Type_Scope)
    return a_ok && p_ok && as == ps && as.kind == .Struct
}

tc_with_receiver :: proc(recv: Tree_Id, args: []Tree_Id) -> []Tree_Id {
    out := make([]Tree_Id, len(args) + 1, context.temp_allocator)
    out[0] = recv
    copy(out[1:], args)
    return out
}

// A type a scope holds, when it's an enum (no error set): called, the
// variant a number is (`gl.GL_Tex_Param(n)`, tc_enum_number).
tc_held_enum :: proc(t: Type) -> ^Type_Enum {
    et, is_enum := t.(^Type_Enum)
    return et if is_enum && !et.is_error_kind && !et.is_synthetic else nil
}

// A type a scope holds, called: its constructor.
tc_held_type :: proc(k: ^TC, n: Tree_Id, t: Type) -> ^Type_Scope {
    k.annot.call_names[tc_sid(k, n)] = type_flat_name(t)
    if ts, is_scope := t.(^Type_Scope); is_scope { return ts }
    tc_unsupported(k, n, "a call of a scope's type")
    return nil
}

// `E.from_text(s)`, E an enum (no error set): its fun — made at each call, its
// body generated where it's called (Origin_From_Text) — taking a text, giving
// the variant whose name it spells exactly, else E's variant written `= 0`
// (tc_call: E must have one). nil: E is no such enum. (Named as written,
// `Mode.from_text`: no symbol has the name.)
tc_from_text_fun :: proc(qt: Type) -> ^Type_Scope {
    et, is_enum := distinct_base(qt).(^Type_Enum)
    if !is_enum || et.is_error_kind { return nil }
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.home_package = et.home_package
    ft.name = strings.concatenate({type_name(qt), ".from_text"})
    ft.source_name = "from_text"
    append(&ft.params, Struct_Type_Field{name = "text", type_ = type_slice(Type_Utf8{})})
    append(&ft.return_types, qt)
    ft.origin = Origin_From_Text{enum_ = et}
    ft.body_span = et.span
    return ft
}

// `E(n)`, E an enum (no error set): its fun — made at each call, its body
// generated where it's called (Origin_From_Number) — taking the number, of
// its own type `pt`, giving the variant whose value it is; none, the program
// stops (llvm_from_number). A constant's is checked first (tc_enum_number).
tc_from_number_fun :: proc(qt: Type, et: ^Type_Enum, pt: Type) -> ^Type_Scope {
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.home_package = et.home_package
    ft.name = strings.concatenate({type_name(qt), "(n)"})
    ft.source_name = type_name(qt)
    append(&ft.params, Struct_Type_Field{name = "n", type_ = pt})
    append(&ft.return_types, qt)
    ft.origin = Origin_From_Number{enum_ = et}
    ft.body_span = et.span
    return ft
}

// `x.text()`, x an enum or an err: its fun — made at each call, its body
// generated where it's called (Origin_Variant_Text) — giving x's name as
// an atom (variant_text; "?" for a value no variant has). The names' atoms
// are made now, in a fixed order, so their ids are the same each build: an
// enum's here, an open err's — any error set's — once all are checked
// (atoms_for_err_text). nil: x is neither.
tc_text_fun :: proc(k: ^TC, qt: Type) -> ^Type_Scope {
    et, is_enum := distinct_base(qt).(^Type_Enum)
    _, is_err := distinct_base(qt).(Type_Err)
    if !is_enum && !is_err { return nil }
    checked_atom(k.checked, "?")
    if is_err {
        k.checked.err_text = true
    } else {
        names := make([dynamic]string, 0, len(et.variants), context.temp_allocator)
        for name in et.variants { append(&names, variant_text(et, name)) }
        slice.sort(names[:])
        for name in names { checked_atom(k.checked, name) }
    }
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.home_package = et.home_package if is_enum else k.pkg
    ft.name = strings.concatenate({type_name(qt), ".text"})
    ft.source_name = "text"
    append(&ft.params, Struct_Type_Field{name = "value", type_ = qt})
    append(&ft.return_types, Type_Atom{})
    ft.origin = Origin_Variant_Text{enum_ = et if is_enum else nil}
    return ft
}

// `E.from_text(…)`'s fun, when n is one — E an enum its receiver names,
// `Mode` or `m.Mode` — else nil. (Asked before the call is checked.)
tc_from_text_call :: proc(k: ^TC, n: Tree_Id) -> ^Type_Scope {
    tr := k.t
    if tr.tag[n] != .Method_Call { return nil }
    mv := method_view(tr, n)
    if tc_text(mv.name) != "from_text" { return nil }
    q := tc_unparen(k, mv.receiver)
    ref := k.rs.refs[q]
    if ref.kind != .Type { return nil }
    name: string
    #partial switch tr.tag[q] {
    case .Ident: name = tc_name(k, q)
    case .Field: name = tc_text(Token_Id(tr.b[q]))
    case:        return nil
    }
    qt, ok := tc_ref_type(k, ref, name)
    if !ok { return nil }
    return tc_from_text_fun(qt)
}
