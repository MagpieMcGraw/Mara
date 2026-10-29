package mara

import "core:fmt"

// Generics in the checker. A definition is a template when its signature
// names a type it is given (`$T`), a struct's param is a shape (`~T`), or a
// struct's param is used in its fields' types (`[n]T`). A template is
// checked only as its instances; its names are resolved once (the
// resolver's), its type params known by the tokens that declare them
// (TC_Bindings: what an instance binds each to).

TC_Template :: struct {
    def, node: Tree_Id,
    lo:        Tree_Id,   // its body's lowest node (its nodes: [lo, node])
    pkg:       string,
}

tc_is_generic :: proc(k: ^TC, node: Tree_Id) -> bool {
    t := k.t
    v := scope_view(t, node)
    if len(v.generics) > 0 { return true }
    is_struct := t.tag[node] == .Struct_Def
    for g in v.params {
        pt := params_view(t, g).type_
        if tc_type_has_dollar(k, pt) { return true }
        if is_struct && pt != 0 && t.tag[pt] == .Type_Tilde { return true }
    }
    for r in v.returns {
        rt := params_view(t, r).type_ if t.tag[r] == .Param_Group else r
        if tc_type_has_dollar(k, rt) { return true }
    }
    if !is_struct { return false }
    // A struct's params its fields' types use; `$T` in them.
    for s in v.body {
        if t.tag[s] != .Decl { continue }
        ft := decl_view(t, s).type_
        if tc_type_has_dollar(k, ft) { return true }
        for g in v.params {
            pv := params_view(t, g)
            if pv.type_ == 0 || (t.tag[pv.type_] != .Type_Name && t.tag[pv.type_] != .Type_Keyword) { continue }
            for name in pv.names {
                if tc_type_uses(k, ft, name) { return true }
            }
        }
    }
    return false
}

// Whether a type as written names a type it is given: `$T`.
tc_type_has_dollar :: proc(k: ^TC, n: Tree_Id) -> bool {
    if n == 0 { return false }
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Dollar: return true
    case .Type_Pointer, .Type_Paren: return tc_type_has_dollar(k, Tree_Id(t.a[n]))
    case .Type_Slice: return tc_type_has_dollar(k, Tree_Id(t.b[n]))
    case .Type_Partial: return tc_type_has_dollar(k, Tree_Id(t.a[n])) || tc_type_has_dollar(k, Tree_Id(t.b[n]))
    case .Type_Array: return tc_type_has_dollar(k, Tree_Id(tree_rec(t, t.a[n], 2)[0])) || tc_type_has_dollar(k, Tree_Id(t.b[n]))
    case .Type_Generic:
        for a in tree_list(t, t.a[n]) { if tc_type_has_dollar(k, a) { return true } }
    case .Type_Fun:
        for a in tree_list(t, t.a[n]) { if tc_type_has_dollar(k, a) { return true } }
        for a in tree_list(t, t.b[n]) { if tc_type_has_dollar(k, a) { return true } }
    }
    return false
}

// Whether a type as written uses a declaration (decl: the token that
// declares it) — names it as a type, or as an array's size: what the
// resolver says those names refer to.
tc_type_uses :: proc(k: ^TC, n: Tree_Id, decl: Token_Id) -> bool {
    if n == 0 { return false }
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Name:
        return len(tree_token_list(t, t.a[n])) == 1 && k.rs.refs[n].decl == decl
    case .Ident:
        return k.rs.refs[n].decl == decl
    case .Type_Pointer, .Type_Paren, .Type_Slice:
        inner := Tree_Id(t.a[n]) if t.tag[n] != .Type_Slice else Tree_Id(t.b[n])
        return tc_type_uses(k, inner, decl)
    case .Type_Partial:
        return tc_size_names(k, Tree_Id(t.a[n]), decl) || tc_type_uses(k, Tree_Id(t.b[n]), decl)
    case .Type_Array:
        return tc_size_names(k, Tree_Id(tree_rec(t, t.a[n], 2)[0]), decl) || tc_type_uses(k, Tree_Id(t.b[n]), decl)
    case .Type_Generic:
        for a in tree_list(t, t.a[n]) { if tc_type_uses(k, a, decl) { return true } }
    case .Type_Fun:
        for a in tree_list(t, t.a[n]) { if tc_type_uses(k, a, decl) { return true } }
        for a in tree_list(t, t.b[n]) { if tc_type_uses(k, a, decl) { return true } }
    }
    return false
}

// Whether an array's size is written as a bare name of the declaration.
tc_size_names :: proc(k: ^TC, n: Tree_Id, decl: Token_Id) -> bool {
    return n != 0 && k.t.tag[n] == .Ident && k.rs.refs[n].decl == decl
}

// A fun template's type params, in order — those it declares, then each
// `$T` its params and results introduce, first use first: the resolver's,
// by the tokens that declare them.
tc_generic_params :: proc(k: ^TC, node: Tree_Id) -> []Token_Id {
    return k.rs.type_params_of[node][:] if node in k.rs.type_params_of else nil
}

// The type param a type as written names (`$T`, `T`): the token that
// declares it (0: none).
tc_type_param_named :: proc(k: ^TC, n: Tree_Id) -> Token_Id {
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Dollar:
        if ref := k.rs.refs[n]; ref.kind != .None { return ref.decl }
        return Token_Id(t.a[n])
    case .Type_Name:
        if len(tree_token_list(t, t.a[n])) == 1 { return k.rs.refs[n].decl }
    }
    return 0
}

// What a param's type as written binds, given the type of the argument
// passed to it: `^[]$T` given ^[]i64 binds T to i64.
tc_infer :: proc(k: ^TC, subst: ^TC_Bindings, n: Tree_Id, actual_raw: Type) {
    if n == 0 { return }
    t := k.t
    actual := unwrap_alias(actual_raw)
    decl := tc_type_param_named(k, n)
    #partial switch t.tag[n] {
    case .Type_Paren:
        tc_infer(k, subst, Tree_Id(t.a[n]), actual)
    case .Type_Pointer:
        if pt, ok := actual.(^Type_Ptr); ok { tc_infer(k, subst, Tree_Id(t.a[n]), pt.elem) }
    case .Type_Array:
        if fa, ok := actual.(^Type_Fixed_Array); ok {
            tc_infer_size(k, subst, Tree_Id(tree_rec(t, t.a[n], 2)[0]), fa.size)
            tc_infer(k, subst, Tree_Id(t.b[n]), fa.elem)
        }
    case .Type_Slice:
        // (An array or a partial array a slice param views drives it too:
        // `&s + "lit"` binds slice_add's T.)
        #partial switch a in actual {
        case ^Type_Slice:         tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        case ^Type_Fixed_Array:   tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        case ^Type_Partial_Array: tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        }
    case .Type_Partial:
        #partial switch a in actual {
        case ^Type_Partial_Array:
            tc_infer_size(k, subst, Tree_Id(t.a[n]), a.size)
            tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        case ^Type_Fixed_Array:   // (`[Kind]$T`: an enum's array)
            if a.index_type != nil { tc_infer(k, subst, Tree_Id(t.b[n]), a.elem) }
        }
    case .Type_Fun:
        if ft, ok := actual.(^Type_Scope); ok {
            for p, i in tree_list(t, t.a[n]) { if i < len(ft.params) { tc_infer(k, subst, p, ft.params[i].type_) } }
            for r, i in tree_list(t, t.b[n]) { if i < len(ft.return_types) { tc_infer(k, subst, r, ft.return_types[i]) } }
        }
    case .Type_Generic:
        tc_unsupported(k, n, "a generic instance's type param inferred")
    }
    // (An untyped argument binds its settled type, as a declaration would; a
    // binding no use has given a width yet, its default — from here on.)
    if decl != 0 && decl in subst^ && subst[decl] == nil {
        subst[decl] = tc_pin_default(k, actual, k.infer_at if k.infer_at != {} else tree_span(t, n))
    }
}

// An array's size written `$N`, given the size of the array passed: N bound
// to it (a compile-time integer, as a struct's `$N: int` is).
tc_infer_size :: proc(k: ^TC, subst: ^TC_Bindings, n: Tree_Id, size: int) {
    if n == 0 || k.t.tag[n] != .Type_Dollar { return }
    decl := tc_type_param_named(k, n)
    if decl != 0 && decl in subst^ && subst[decl] == nil { subst[decl] = Type_Const_Int{value = size} }
}

// A call of a generic fun: each argument checked, the type params bound from
// them, the instance made once per bindings, then the call.
tc_generic_call :: proc(k: ^TC, n: Tree_Id, name: string, tmpl: TC_Template, args: []Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    if tr.tag[tmpl.node] != .Fun_Def {
        tc_unsupported(k, n, "a generic struct's construction")
        return Type_Error{}
    }
    // (`[]` given a generic slice param, `[]$T`, is checked after the rest:
    // a slice of what they bind T to, else of bytes — it holds none, as a
    // binding's `data: []$T` given no data.)
    empty :: proc(k: ^TC, a: Tree_Id) -> bool {
        m := tc_unparen(k, a)
        return k.t.tag[m] == .Array && k.t.a[m] == 0
    }
    // (`_`: its param's default, as for a plain fun — nothing inferred from it.)
    left_off :: proc(k: ^TC, a: Tree_Id) -> bool {
        m := tc_unparen(k, a)
        return k.t.tag[m] == .Ident && tc_name(k, m) == "_"
    }
    arg_types := make([dynamic]Type, len(args), context.temp_allocator)
    for a, i in args { if !empty(k, a) && !left_off(k, a) { arg_types[i] = tc_arg(k, a) } }
    params := tc_generic_params(k, tmpl.node)
    subst: TC_Bindings
    for p in params { subst[p] = nil }
    v := scope_view(tr, tmpl.node)
    param_types := make([dynamic]Tree_Id, context.temp_allocator)
    for g in v.params {
        pv := params_view(tr, g)
        for _ in pv.names { append(&param_types, pv.type_) }
    }
    for pt, i in param_types {
        if i < len(arg_types) && arg_types[i] != nil && pt != 0 {
            k.infer_at = tree_span(tr, args[i])
            tc_infer(k, &subst, pt, arg_types[i])
            k.infer_at = {}
        }
    }
    for a, i in args {
        if arg_types[i] != nil || left_off(k, a) { continue }
        saved := k.hint
        if i < len(param_types) && tr.tag[param_types[i]] == .Type_Slice {
            if decl := tc_type_param_named(k, Tree_Id(tr.b[param_types[i]])); decl != 0 && decl in subst {
                k.hint = type_slice(subst[decl] if subst[decl] != nil else Type_Byte{})
            }
        }
        arg_types[i] = tc_arg(k, a)
        k.hint = saved
        if i < len(param_types) && param_types[i] != 0 {
            k.infer_at = tree_span(tr, a)
            tc_infer(k, &subst, param_types[i], arg_types[i])
            k.infer_at = {}
        }
    }
    i := 0
    for p in params {
        if subst[p] == nil {
            // (A param taking a pointer, given a value: nothing bound from it
            // — the `&` left off, `next(list)`. Said so.)
            i = 0
            for g in v.params {
                pv := params_view(tr, g)
                for pname in pv.names {
                    defer i += 1
                    // (A list, `[$N]T`, given a slice: a view has no room
                    // of its own — text for C, no 0 after it.)
                    if i < len(arg_types) && tr.tag[pv.type_] == .Type_Partial && tc_type_has_dollar(k, pv.type_) && is_slice_type(arg_types[i]) {
                        tc_error(k, span, TYPE_GENERIC_PARAM_LIST_VALUE, tc_text(p), name, tc_text(pname), tc_source_desc(k, args[i], arg_types[i]))
                        return Type_Error{}
                    }
                    if i >= len(arg_types) || tr.tag[pv.type_] != .Type_Pointer || !tc_type_has_dollar(k, pv.type_) { continue }
                    // (A list to grow, `^[$N]T`, given a fixed array or a
                    // slice: neither has a len to move.)
                    if ap, is_ptr := distinct_base(arg_types[i]).(^Type_Ptr); is_ptr && ap.elem != nil {
                        if hint := tc_partial_hint(k, args[i], arg_types[i]); hint != "" {
                            tc_error(k, span, TYPE_GENERIC_PARAM_LIST, tc_text(p), name, tc_text(pname), tc_source_desc(k, args[i], arg_types[i]), hint)
                            return Type_Error{}
                        }
                        if is_slice_type(ap.elem) {
                            m := tc_unparen(k, args[i])
                            if tr.tag[m] == .Unary && build_tokens[tr.main[m]].kind == .Ampersand { m = Tree_Id(tr.a[m]) }
                            arg := tc_diag_name(k, m)
                            tc_error(k, span, TYPE_SLICE_CANT_GROW, fmt.tprintf("`%s`", arg) if arg != "" else "it")
                            return Type_Error{}
                        }
                    }
                    if _, is_ptr := distinct_base(arg_types[i]).(^Type_Ptr); is_ptr || is_any(arg_types[i]) { continue }
                    arg := tc_diag_name(k, args[i])
                    hint := fmt.tprintf("`&%s`", arg) if arg != "" else "`&` before it"
                    tc_error(k, span, TYPE_GENERIC_PARAM_POINTER, tc_text(p), name, tc_text(pname), tc_source_desc(k, args[i], arg_types[i]), hint)
                    return Type_Error{}
                }
            }
            tc_error(k, span, TYPE_COULD_INFER_TYPE_PARAMETER_CALL, tc_text(p), name)
            return Type_Error{}
        }
    }
    type_args := make([dynamic]Type, context.temp_allocator)
    for p in params { append(&type_args, subst[p]) }
    mangled := mangle_generic_name(name, type_args[:])
    ft := k.instances[mangled] or_else nil
    if ft == nil { ft = tc_instantiate_fun(k, tmpl, subst, mangled) }
    if len(args) < count_required_params(ft) || len(args) > len(ft.params) {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT, name, len(ft.params), len(args))
    }
    tc_set_callee(k, n, ft)
    tc_set_ref(k, n, {ft.decl, .Fun})
    k.annot.forms[tc_sid(k, n)] = .Generic
    // (What each param receives: what's written, else its default, run at
    // the call — `#caller_span`, `#caller_name`, the call site's.)
    received := make([dynamic]Arg, 0, len(ft.params), context.temp_allocator)
    for i in 0 ..< len(ft.params) {
        p := ft.params[i]
        if i < len(args) && !left_off(k, args[i]) {
            append(&received, Arg{args[i], .Receiver if args[i] == k.recv.node else .Written, -1})
            continue
        }
        if p.default_node == 0 {
            if i < len(args) { tc_error(k, span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER, i + 1, name, p.name) }
            break
        }
        k.hint = p.type_
        at: Type
        if tr.tag[p.default_node] == .Hash_Name {
            append(&received, Arg{p.default_node, .Call_Site, -1})
            at = tc_hash_name(k, p.default_node)
        } else if slot, is_slot := p.default_slot.?; is_slot {
            append(&received, Arg{p.default_node, .Default, i32(slot)})
            at = tc_tuple_default(k, p.default_node, slot, span)
        } else {
            append(&received, Arg{p.default_node, .Default, -1})
            at = tc_check(k, p.default_node)
        }
        if !coerce_deferred(k.c, at, p.type_, span) && arg_incompatible(p.type_, at) {
            tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, fmt.tprintf(" (`%s`'s default)", p.name), name, p.name, type_name(p.type_), type_name(at), "")
        }
        if p.default_slot == nil { tc_settle(k, p.default_node, p.type_) }
    }
    tc_set_args(k, n, received[:])
    // (Each argument fits its param, the bindings in: `x: T` given another
    // type, a fun given for `fun(T) -> $K` taking something else — as a
    // call of a plain fun is checked.)
    for a, i in args {
        if i >= len(ft.params) { break }
        if left_off(k, a) { continue }
        pt, at := ft.params[i].type_, arg_types[i]
        own := a == k.recv.node && a != 0 && tc_own_receiver(at, pt)
        if own || coerce_deferred(k.c, at, pt, span) || !arg_incompatible(pt, at) { continue }
        clause := ""
        if an := tc_diag_name(k, a); an != "" { clause = fmt.tprintf(" ('%s')", an) }
        got := type_name(at)
        if fs, is_fun := at.(^Type_Scope); is_fun && fs.kind == .Fun && fs.name != "" {
            shape := fs^
            shape.name = ""
            got = fmt.tprintf("%s, a %s", got, type_name(&shape))
        }
        tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, clause, name, ft.params[i].name, type_name(pt), got, "")
    }
    for a, i in args { if i < len(ft.params) && !left_off(k, a) { tc_settle(k, a, ft.params[i].type_) } }   // (each at its param's type, now known)
    return fn_primary_return(ft)
}

// An instance of a generic fun: its signature at the bindings, its body the
// template's own checked again with them bound — its scope the call's.
tc_instantiate_fun :: proc(k: ^TC, tmpl: TC_Template, subst: TC_Bindings, mangled: string) -> ^Type_Scope {
    tr := k.t
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.home_package = tmpl.pkg
    ft.node = tmpl.node
    ft.name = make_flat_name(tmpl.pkg, mangled)   // (no source name: named by its flat one)
    saved_pkg := k.pkg
    k.pkg = tmpl.pkg
    defer k.pkg = saved_pkg
    // (Its body's nodes its own: tc_sid.)
    saved_inst := tc_instance_begin(k, tmpl, ft, subst)
    defer tc_instance_end(k, saved_inst)
    span := tree_span(tr, tmpl.def)
    v := scope_view(tr, tmpl.node)
    for g in v.params {
        pv := params_view(tr, g)
        // (A default as a plain fun's: run at the call, `#caller_span` the
        // call site's — tc_signature.)
        for pn, i in pv.names {
            def := pv.values[i] if i < len(pv.values) else 0
            slot: Maybe(int)
            if len(pv.values) == 1 && len(pv.names) > 1 { def, slot = pv.values[0], i }
            pt := tc_param_type(k, tc_text(pn), pv.type_, def, span, slot)
            append(&ft.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = pt, default_node = def, default_slot = slot})
        }
    }
    for r in v.returns {
        if tr.tag[r] == .Param_Group {
            tc_unsupported(k, r, "a generic's named result")
            continue
        }
        append(&ft.return_types, tc_type(k, r, span))
    }
    ft.decl = tr.main[tmpl.def]
    tc_bound_set(k, ft.decl, ft)   // (its template's name, in it: it)
    k.instances[mangled] = ft
    append(&k.instance_order, mangled)
    ft.parent_scope = k.module_scopes[tmpl.pkg] or_else nil
    k.scope_of[ft] = len(k.scopes)
    sc := new_clone(TC_Scope{ts = ft, def = tmpl.def, node = tmpl.node, subst = subst, synthetic = true})
    append(&k.scopes, sc)
    tc_scope_body(k, sc)
    // (Its own funs, for codegen: extracted as a fun's are.)
    tc_extract(k, sc.nested[:], tmpl.pkg, false, nested = true)
    return ft
}

// A generic struct's params: its `$T: type`
// and `$N: int` first; then each param that is a type (`item: $T`), a shape
// (`a: ~Arena`), or a value its fields' types use (`n: i64` in `[n]T`), by
// the param's name; then any other `$T` its params or fields name. The rest
// are its constructor's.
TC_Generic_Param :: struct {
    decl:  Token_Id,  // the token that declares it (its name)
    value: bool,      // a value (`n: i64`, `$N: int`), not a type
    shape: Token_Id,  // `~T`: T, what its type must have (its name, written)
    def:   Tree_Id,   // its default
}

tc_struct_generics :: proc(k: ^TC, node: Tree_Id) -> (gps: [dynamic]TC_Generic_Param, promoted: map[Token_Id]bool) {
    t := k.t
    v := scope_view(t, node)
    has :: proc(gps: []TC_Generic_Param, decl: Token_Id) -> bool {
        for g in gps { if g.decl == decl { return true } }
        return false
    }
    for g in v.generics {
        append(&gps, TC_Generic_Param{decl = t.main[g], value = tc_text(Token_Id(t.a[g])) != "type"})
    }
    dropped := make(map[Token_Id]bool, context.temp_allocator)   // (a `$T` a param named)
    for g in v.params {
        pv := params_view(t, g)
        if pv.type_ == 0 { continue }
        for name, i in pv.names {
            def := pv.values[i] if i < len(pv.values) else 0
            #partial switch t.tag[pv.type_] {
            case .Type_Tilde:
                append(&gps, TC_Generic_Param{decl = name, shape = Token_Id(t.a[pv.type_]), def = def})
                promoted[name] = true
            case .Type_Dollar:
                append(&gps, TC_Generic_Param{decl = name})
                dropped[tc_type_param_named(k, pv.type_)] = true
                promoted[name] = true
            case .Type_Name, .Type_Keyword:
                for s in v.body {
                    if t.tag[s] == .Decl && tc_type_uses(k, decl_view(t, s).type_, name) {
                        append(&gps, TC_Generic_Param{decl = name, value = true, def = def})
                        promoted[name] = true
                        break
                    }
                }
            }
        }
    }
    // (A `$T` written anywhere else in its params or fields.)
    dollars :: proc(k: ^TC, n: Tree_Id, gps: ^[dynamic]TC_Generic_Param, dropped: map[Token_Id]bool) {
        if n == 0 { return }
        t := k.t
        #partial switch t.tag[n] {
        case .Type_Dollar:
            decl := tc_type_param_named(k, n)
            if !dropped[decl] && !has(gps[:], decl) { append(gps, TC_Generic_Param{decl = decl}) }
        case .Type_Pointer, .Type_Paren:
            dollars(k, Tree_Id(t.a[n]), gps, dropped)
        case .Type_Slice, .Type_Partial, .Type_Array:
            dollars(k, Tree_Id(t.b[n]), gps, dropped)
        case .Type_Generic:
            for a in tree_list(t, t.a[n]) { dollars(k, a, gps, dropped) }
        }
    }
    for g in v.params { dollars(k, params_view(t, g).type_, &gps, dropped) }
    for s in v.body { if t.tag[s] == .Decl { dollars(k, decl_view(t, s).type_, &gps, dropped) } }
    return
}

// `Name(args)`, Name a generic struct: its instance — its params bound to
// the arguments (a value's, a constant), made once.
tc_struct_instance :: proc(k: ^TC, n: Tree_Id, tmpl: TC_Template, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    if t.tag[tmpl.node] != .Struct_Def {
        tc_unsupported(k, n, "a generic fun named as a type")
        return Type_Error{}
    }
    gps, promoted := tc_struct_generics(k, tmpl.node)
    args := tree_list(t, t.a[n])
    targs := make([dynamic]Type, context.temp_allocator)
    for a, i in args {
        if i >= len(gps) { break }
        gp := gps[i]
        if gp.shape != 0 {
            // (A type; a constructor's call, its struct's — its value the
            // declaration's to build: tc_shape_bindings.)
            if u := tc_unparen(k, a); tc_is_call(k, u) {
                append(&targs, tc_type_named(k, tc_call_name(k, u), span, u))
            } else {
                append(&targs, tc_type(k, a, span))
            }
            continue
        }
        if !gp.value {
            append(&targs, tc_type(k, a, span))
            continue
        }
        // (A value: a number, a constant, an operation of them.)
        at := a
        if t.tag[a] == .Type_Name {
            kc := k.const_at[k.rs.refs[a].decl] if k.rs.refs[a].kind == .Const else nil
            if kc == nil {
                tc_unsupported(k, a, "a generic's size known at run time")
                return Type_Error{}
            }
            at = kc.value
        }
        v, known := tc_comptime_int(k, at)
        if !known {
            tc_unsupported(k, a, "a generic's size known at run time")
            return Type_Error{}
        }
        append(&targs, Type_Const_Int{value = int(v)})
    }
    // (The params it leaves off: their defaults.)
    for i := len(targs); i < len(gps); i += 1 {
        gp := gps[i]
        if gp.def == 0 { break }
        if gp.shape != 0 && t.tag[gp.def] == .Ident {
            append(&targs, tc_type_named(k, tc_name(k, gp.def), span, gp.def))   // (`~T = void`)
            continue
        }
        if !gp.value {
            tc_unsupported(k, gp.def, "a generic type param's default")
            return Type_Error{}
        }
        v, known := tc_comptime_int(k, gp.def)
        if !known { break }
        append(&targs, Type_Const_Int{value = int(v)})
    }
    if len(targs) != len(gps) || len(args) > len(gps) {
        tc_error(k, span, TYPE_EXPECTS_TYPE_ARGUMENT, name, len(gps), len(args))
        return Type_Error{}
    }
    mangled := mangle_generic_name(name, targs[:])
    if st, made := k.table.mono_cache[mangled]; made { return st }
    // (A shape's argument has what its constraint has: checked once.)
    for gp, i in gps {
        if gp.shape == 0 { continue }
        shape, _ := tc_ref_type(k, k.rs.token_refs[gp.shape] or_else {}, tc_text(gp.shape))
        check_shape_constraint(k.c, tc_text(gp.decl), tc_text(gp.shape), shape.(^Type_Scope) or_else nil, targs[i], span)
    }
    subst := make(TC_Bindings)
    for gp, i in gps { subst[gp.decl] = targs[i] }
    return tc_instantiate_struct(k, tmpl, subst, targs[:], promoted, mangled)
}

// A generic struct's instance: its type (named for its arguments), its
// params bound in it; then its body — its fields, its methods — checked as
// its own (its nodes salted: tc_sid). Its init and methods are extracted with
// the main module's.
tc_instantiate_struct :: proc(k: ^TC, tmpl: TC_Template, subst: TC_Bindings, targs: []Type,
                              promoted: map[Token_Id]bool, mangled: string) -> ^Type_Scope {
    tr := k.t
    v := scope_view(tr, tmpl.node)
    span := tree_span(tr, tmpl.def)
    st := new(Type_Scope)
    st.name, st.source_name, st.home_package = make_flat_name(tmpl.pkg, mangled), mangled, tmpl.pkg
    st.kind, st.node = .Struct, tmpl.node
    st.generic_base = tc_name(k, tmpl.def)
    append(&st.generic_args, ..targs)
    st.parent_scope = k.module_scopes[tmpl.pkg] or_else nil
    st.has_parens = build_tokens[tr.main[tmpl.node] + 1].kind == .Left_Paren
    st.is_packed = v.packed != 0
    k.table.mono_cache[mangled] = st
    k.table.funs[st.name] = st
    st.decl = tr.main[tmpl.def]
    for tok, bound in subst { scope_bind(st, tc_text(tok), bound) }   // (its type params, its members)
    saved_pkg := k.pkg
    k.pkg = tmpl.pkg
    defer k.pkg = saved_pkg
    saved_inst := tc_instance_begin(k, tmpl, st, subst)
    defer tc_instance_end(k, saved_inst)
    tc_bound_set(k, st.decl, st)   // (its template's name, in it: it)
    // (Its constructor's params: those no generic's.)
    for g in v.params {
        pv := params_view(tr, g)
        for pn, i in pv.names {
            if promoted[pn] { continue }
            def := pv.values[i] if i < len(pv.values) else 0
            pt := tc_param_type(k, tc_text(pn), pv.type_, def, span)
            append(&st.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = pt, default_node = def})
        }
    }
    k.scope_of[st] = len(k.scopes)
    append(&k.struct_instances, len(k.scopes))
    append(&k.scopes, new_clone(TC_Scope{ts = st, def = tmpl.def, node = tmpl.node, subst = subst, synthetic = true}))
    tc_struct_ensure(k, st)
    return st
}
