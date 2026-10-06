package mara

// Generics in the checker. A definition is a template when its signature
// names a type it is given (`$T`), a struct's param is a shape (`~T`), or a
// struct's param is used in its fields' types (`[n]T`): the tree keeps
// them as written, and the checker reads them off it. A template is
// checked only as its instances.

TC_Template :: struct {
    def, node: Tree_Id,
    lo:        Tree_Id,   // its body's lowest node (its nodes: [lo, node])
    env:       ^Type_Scope,
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
                if tc_type_refs(k, ft, tc_text(name)) { return true }
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
    case .Type_Slice, .Type_Partial, .Type_Array: return tc_type_has_dollar(k, Tree_Id(t.b[n]))
    case .Type_Generic:
        for a in tree_list(t, t.a[n]) { if tc_type_has_dollar(k, a) { return true } }
    case .Type_Fun:
        for a in tree_list(t, t.a[n]) { if tc_type_has_dollar(k, a) { return true } }
        for a in tree_list(t, t.b[n]) { if tc_type_has_dollar(k, a) { return true } }
    }
    return false
}

// Whether a type as written uses a name: as a type, or as an array's size.
tc_type_refs :: proc(k: ^TC, n: Tree_Id, name: string) -> bool {
    if n == 0 { return false }
    t := k.t
    #partial switch t.tag[n] {
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        return len(parts) == 1 && tc_text(parts[0]) == name
    case .Ident:
        return tc_name(k, n) == name
    case .Type_Pointer, .Type_Paren, .Type_Slice:
        inner := Tree_Id(t.a[n]) if t.tag[n] != .Type_Slice else Tree_Id(t.b[n])
        return tc_type_refs(k, inner, name)
    case .Type_Partial:
        return tc_size_is(k, Tree_Id(t.a[n]), name) || tc_type_refs(k, Tree_Id(t.b[n]), name)
    case .Type_Array:
        return tc_size_is(k, Tree_Id(tree_rec(t, t.a[n], 2)[0]), name) || tc_type_refs(k, Tree_Id(t.b[n]), name)
    case .Type_Generic:
        for a in tree_list(t, t.a[n]) { if tc_type_refs(k, a, name) { return true } }
    case .Type_Fun:
        for a in tree_list(t, t.a[n]) { if tc_type_refs(k, a, name) { return true } }
        for a in tree_list(t, t.b[n]) { if tc_type_refs(k, a, name) { return true } }
    }
    return false
}

// Whether an array's size is written as the bare name.
tc_size_is :: proc(k: ^TC, n: Tree_Id, name: string) -> bool {
    return n != 0 && k.t.tag[n] == .Ident && tc_name(k, n) == name
}

// The program's struct (the compiler's): built from mara.core's declaration
// of it — its fields, each a declaration, and no code (nothing constructs
// it: main's entry sets up its storage).
tc_program_struct :: proc(k: ^TC) {
    pt := k.table.funs["Program"] or_else nil
    if k.gb == nil || pt == nil || pt.body_span == {} { return }
    t := k.t
    for _, tmpl in k.templates {
        span := tree_span(t, tmpl.def)
        if span != pt.body_span { continue }
        v := scope_view(t, tmpl.node)
        f := graph_body_begin(k.gb, pt, tc_sid(k, tmpl.def), span, v.intrinsic != 0, .Synthetic)
        b := k.gb
        for s in v.body {
            if t.tag[s] != .Decl {
                graph_body_fail(b, f, "the program's struct declares no field")
                break
            }
            ss := tree_span(t, s)
            graph_build_body_stmt(b, ss, true)
            saved := graph_build_stmt(b, tc_sid(k, s), ss, tc_stmt_kind(k, s), fresh = true)
            for target in decl_view(t, s).targets { graph_build_program_field(b, tc_name(k, target), ss) }
            graph_build_stmt_end(b, saved)
        }
        if k.c.errors > 0 { graph_body_fail(b, f, "errors") }
        graph_body_end(b, f)
        return
    }
}

// A template's type params, in order: those it declares, then each
// `$T` its params and results introduce, first use first.
tc_generic_params :: proc(k: ^TC, node: Tree_Id) -> [dynamic]string {
    t := k.t
    v := scope_view(t, node)
    names: [dynamic]string
    add :: proc(names: ^[dynamic]string, name: string) {
        for n in names^ { if n == name { return } }
        append(names, name)
    }
    for g in v.generics { add(&names, tc_name(k, g)) }
    walk :: proc(k: ^TC, n: Tree_Id, names: ^[dynamic]string) {
        if n == 0 { return }
        t := k.t
        #partial switch t.tag[n] {
        case .Type_Dollar:
            add(names, tc_text(Token_Id(t.a[n])))
        case .Type_Pointer, .Type_Paren:
            walk(k, Tree_Id(t.a[n]), names)
        case .Type_Slice, .Type_Partial, .Type_Array:
            walk(k, Tree_Id(t.b[n]), names)
        case .Type_Generic:
            for a in tree_list(t, t.a[n]) { walk(k, a, names) }
        case .Type_Fun:
            for a in tree_list(t, t.a[n]) { walk(k, a, names) }
            for a in tree_list(t, t.b[n]) { walk(k, a, names) }
        }
    }
    for g in v.params { walk(k, params_view(t, g).type_, &names) }
    for r in v.returns { walk(k, params_view(t, r).type_ if t.tag[r] == .Param_Group else r, &names) }
    return names
}

// The token that declares a template's type param: its `$T: type`, else the
// first `$T` its params, results or fields write, else the param it
// promotes (`item: $T`, `n: i64` in `[n]T`). 0 when none is found.
tc_type_param_decl :: proc(k: ^TC, node: Tree_Id, name: string) -> Token_Id {
    t := k.t
    v := scope_view(t, node)
    for g in v.generics { if tc_name(k, g) == name { return t.main[g] } }
    walk :: proc(k: ^TC, n: Tree_Id, name: string) -> Token_Id {
        if n == 0 { return 0 }
        t := k.t
        #partial switch t.tag[n] {
        case .Type_Dollar, .Type_Tilde:
            if tok := Token_Id(t.a[n]); tc_text(tok) == name { return tok }
        case .Type_Pointer, .Type_Paren:
            return walk(k, Tree_Id(t.a[n]), name)
        case .Type_Slice, .Type_Partial, .Type_Array:
            return walk(k, Tree_Id(t.b[n]), name)
        case .Type_Generic, .Type_Fun:
            for a in tree_list(t, t.a[n]) { if tok := walk(k, a, name); tok != 0 { return tok } }
            if t.tag[n] == .Type_Fun { for a in tree_list(t, t.b[n]) { if tok := walk(k, a, name); tok != 0 { return tok } } }
        }
        return 0
    }
    for g in v.params { if tok := walk(k, params_view(t, g).type_, name); tok != 0 { return tok } }
    for r in v.returns { if tok := walk(k, params_view(t, r).type_ if t.tag[r] == .Param_Group else r, name); tok != 0 { return tok } }
    for s in v.body { if t.tag[s] == .Decl { if tok := walk(k, decl_view(t, s).type_, name); tok != 0 { return tok } } }
    for g in v.params { for pn in params_view(t, g).names { if tc_text(pn) == name { return pn } } }
    return 0
}

// What a param's type as written binds, given the type of the argument
// passed to it: `^[]$T` given ^[]i64 binds T to i64.
tc_infer :: proc(k: ^TC, subst: ^map[string]Type, n: Tree_Id, actual_raw: Type) {
    if n == 0 { return }
    t := k.t
    actual := unwrap_alias(actual_raw)
    name: string
    #partial switch t.tag[n] {
    case .Type_Dollar:
        name = tc_text(Token_Id(t.a[n]))
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        if len(parts) == 1 { name = tc_text(parts[0]) }
    case .Type_Paren:
        tc_infer(k, subst, Tree_Id(t.a[n]), actual)
    case .Type_Pointer:
        if pt, ok := actual.(^Type_Ptr); ok { tc_infer(k, subst, Tree_Id(t.a[n]), pt.elem) }
    case .Type_Array:
        if fa, ok := actual.(^Type_Fixed_Array); ok { tc_infer(k, subst, Tree_Id(t.b[n]), fa.elem) }
    case .Type_Slice:
        // (An array or a partial array a slice param views drives it too:
        // `&s + "lit"` binds slice_add's T.)
        #partial switch a in actual {
        case ^Type_Slice:         tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        case ^Type_Fixed_Array:   tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        case ^Type_Partial_Array: tc_infer(k, subst, Tree_Id(t.b[n]), a.elem)
        }
    case .Type_Partial:
        if pa, ok := actual.(^Type_Partial_Array); ok { tc_infer(k, subst, Tree_Id(t.b[n]), pa.elem) }
    case .Type_Fun:
        if ft, ok := actual.(^Type_Scope); ok {
            for p, i in tree_list(t, t.a[n]) { if i < len(ft.params) { tc_infer(k, subst, p, ft.params[i].type_) } }
            for r, i in tree_list(t, t.b[n]) { if i < len(ft.return_types) { tc_infer(k, subst, r, ft.return_types[i]) } }
        }
    case .Type_Generic:
        tc_unsupported(k, n, "a generic instance's type param inferred")
    }
    // (An untyped argument binds its settled type, as a declaration would.)
    if name != "" && name in subst^ && subst[name] == nil { subst[name] = solidify_type(actual) }
}

// A call of a generic fun: each argument checked and built (at its param's
// type once the instance is known), the type params bound from them, the
// instance made once per bindings, then the call.
tc_generic_call :: proc(k: ^TC, n: Tree_Id, name: string, tmpl: TC_Template, args: []Tree_Id, env: ^Type_Scope,
                        want: Build_Want, w: Written) -> (Type, Built) {
    tr := k.t
    span := tree_span(tr, n)
    b := tc_building(k) if want != .None else nil
    if b != nil && want == .Place {
        tc_fail(k, "a call's place")
        b = nil
    }
    if tr.tag[tmpl.node] != .Fun_Def {
        tc_unsupported(k, n, "a generic struct's construction")
        return Type_Error{}, {}
    }
    vals := make([dynamic]Operand, context.temp_allocator)
    widens := make([dynamic]int, context.temp_allocator)
    array_values := make([dynamic]bool, context.temp_allocator)
    literals := make([dynamic]Build_Literal_Arg, context.temp_allocator)
    arg_types := make([dynamic]Type, context.temp_allocator)
    for a, i in args {
        if b != nil && tc_building(k) != nil {
            from := b.nodes
            t, r := tc_arg(k, a, env, .Either, w)
            append(&arg_types, t)
            if tc_building(k) == nil { continue }
            _, is_array := distinct_base(t).(^Type_Fixed_Array)
            if u := tc_unparen(k, a); tr.tag[u] == .Index && is_byte_buffer(tc_node_type(k, Tree_Id(tr.a[u]))) {
                tc_fail(k, "bytes as a generic's argument")
                continue
            }
            v, wi := graph_build_as(b, r.v, r.place, t, tree_span(tr, a), span, {})
            append(&vals, v)
            append(&widens, wi)
            append(&array_values, is_array && !r.place)
            if tr.tag[tc_unparen(k, a)] == .Array { append(&literals, Build_Literal_Arg{i, from, b.nodes, t}) }
        } else {
            append(&arg_types, k.recv.t if a == k.recv.node else tc_check(k, a, env))
        }
    }
    params := tc_generic_params(k, tmpl.node)
    subst: map[string]Type
    for p in params { subst[p] = nil }
    v := scope_view(tr, tmpl.node)
    i := 0
    for g in v.params {
        pv := params_view(tr, g)
        for _ in pv.names {
            if i < len(arg_types) { tc_infer(k, &subst, pv.type_, arg_types[i]) }
            i += 1
        }
    }
    for p in params {
        if subst[p] == nil {
            tc_error(k, span, TYPE_COULD_INFER_TYPE_PARAMETER_CALL, p, name)
            return Type_Error{}, {}
        }
    }
    type_args := make([dynamic]Type, context.temp_allocator)
    for p in params { append(&type_args, subst[p]) }
    mangled := mangle_generic_name(name, type_args[:])
    ft := k.instances[mangled] or_else nil
    if ft == nil { ft = tc_instantiate_fun(k, tmpl, subst, mangled, env) }
    if len(args) != len(ft.params) {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT, name, len(ft.params), len(args))
    }
    tc_set_callee(k, n, ft)
    tc_set_ref(k, n, {ft.decl, .Fun})
    ret := fn_primary_return(ft)
    b = tc_building(k) if b != nil else nil
    if b == nil { return ret, {} }
    for wi, j in widens {
        if wi >= 0 { b.body.widens[wi].sig, b.body.widens[wi].param = ft, j }
    }
    for la in literals {
        if la.arg >= len(ft.params) { continue }
        pt := ft.params[la.arg].type_
        if graph_aggregate(pt) && pt != la.t { graph_build_retype_literal(b, la.from, la.to, pt) }
    }
    if build_views_value(ft, array_values[:]) {
        tc_fail(k, "an array's value viewed by a generic's param")
        return ret, {}
    }
    return ret, {v = {graph_call_op(b, .Call, w, span, ft, ret, ..vals[:]), 0}, ok = true}
}

// An instance of a generic fun: its signature at the bindings, its body the
// template's own checked again with them bound — its scope the call's, its
// graph its own.
tc_instantiate_fun :: proc(k: ^TC, tmpl: TC_Template, subst: map[string]Type, mangled: string, env: ^Type_Scope) -> ^Type_Scope {
    outer: ^Graph_Body
    if k.gb != nil { outer, k.gb.body = k.gb.body, nil }
    defer if k.gb != nil { k.gb.body = outer }
    tr := k.t
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.home_package = tmpl.pkg
    ft.node = tmpl.node
    ft.name = make_flat_name(tmpl.pkg, mangled)   // (no source name: named by its flat one)
    saved_subst, saved_pkg := k.subst, k.pkg
    k.subst, k.pkg = subst, tmpl.pkg
    defer k.subst, k.pkg = saved_subst, saved_pkg
    // (Its body's nodes its own: tc_sid.)
    saved_inst := tc_instance_begin(k, tmpl, ft)
    defer tc_instance_end(k, saved_inst)
    span := tree_span(tr, tmpl.def)
    v := scope_view(tr, tmpl.node)
    for g in v.params {
        pv := params_view(tr, g)
        if pv.type_ == 0 || len(pv.values) > 0 {
            tc_unsupported(k, g, "a generic's param with a default")
            continue
        }
        pt := tc_type(k, pv.type_, tmpl.env, span)
        for pn in pv.names { append(&ft.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = pt}) }
    }
    for r in v.returns {
        if tr.tag[r] == .Param_Group {
            tc_unsupported(k, r, "a generic's named result")
            continue
        }
        append(&ft.return_types, tc_type(k, r, tmpl.env, span))
    }
    build_param_map(ft)
    ft.decl = tr.main[tmpl.def]
    scope_bind(k.root, mangled, ft, {ft.decl, .Fun})
    if env != k.root { scope_bind(env, mangled, ft, {ft.decl, .Fun}) }
    k.instances[mangled] = ft
    append(&k.instance_order, mangled)
    ft.parent_scope = env
    k.scope_of[ft] = len(k.scopes)
    sc := new_clone(TC_Scope{ts = ft, def = tmpl.def, node = tmpl.node, env = env, subst = subst, synthetic = true})
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
    name:  string,
    value: bool,      // a value (`n: i64`, `$N: int`), not a type
    shape: string,    // `~T`: T, what its type must have
    def:   Tree_Id,   // its default
}

tc_struct_generics :: proc(k: ^TC, node: Tree_Id) -> (gps: [dynamic]TC_Generic_Param, promoted: map[string]bool) {
    t := k.t
    v := scope_view(t, node)
    has :: proc(gps: []TC_Generic_Param, name: string) -> bool {
        for g in gps { if g.name == name { return true } }
        return false
    }
    for g in v.generics {
        append(&gps, TC_Generic_Param{name = tc_name(k, g), value = tc_text(Token_Id(t.a[g])) != "type"})
    }
    dropped := make(map[string]bool, context.temp_allocator)   // (a `$T` a param named)
    for g in v.params {
        pv := params_view(t, g)
        if pv.type_ == 0 { continue }
        for name, i in pv.names {
            pn := tc_text(name)
            def := pv.values[i] if i < len(pv.values) else 0
            #partial switch t.tag[pv.type_] {
            case .Type_Tilde:
                append(&gps, TC_Generic_Param{name = pn, shape = tc_text(Token_Id(t.a[pv.type_])), def = def})
                promoted[pn] = true
            case .Type_Dollar:
                append(&gps, TC_Generic_Param{name = pn})
                dropped[tc_text(Token_Id(t.a[pv.type_]))] = true
                promoted[pn] = true
            case .Type_Name, .Type_Keyword:
                for s in v.body {
                    if t.tag[s] == .Decl && tc_type_refs(k, decl_view(t, s).type_, pn) {
                        append(&gps, TC_Generic_Param{name = pn, value = true, def = def})
                        promoted[pn] = true
                        break
                    }
                }
            }
        }
    }
    // (A `$T` written anywhere else in its params or fields.)
    dollars :: proc(k: ^TC, n: Tree_Id, gps: ^[dynamic]TC_Generic_Param, dropped: map[string]bool) {
        if n == 0 { return }
        t := k.t
        #partial switch t.tag[n] {
        case .Type_Dollar:
            name := tc_text(Token_Id(t.a[n]))
            if !dropped[name] && !has(gps[:], name) { append(gps, TC_Generic_Param{name = name}) }
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
tc_struct_instance :: proc(k: ^TC, n: Tree_Id, tmpl: TC_Template, env: ^Type_Scope, span: Span) -> Type {
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
        if gp.shape != "" {
            // (A type; a constructor's call, its struct's — its value the
            // declaration's to build: tc_shape_bindings.)
            if u := tc_unparen(k, a); tc_is_call(k, u) {
                append(&targs, tc_type_named(k, tc_call_name(k, u), env, span))
            } else {
                append(&targs, tc_type(k, a, env, span))
            }
            continue
        }
        if !gp.value {
            append(&targs, tc_type(k, a, env, span))
            continue
        }
        // (A value: a number, a constant, an operation of them.)
        at := a
        if t.tag[a] == .Type_Name {
            kc := k.consts[tc_name(k, a)] or_else nil
            if kc == nil {
                tc_unsupported(k, a, "a generic's size known at run time")
                return Type_Error{}
            }
            at = kc.value
        }
        v, known := tc_comptime_int(k, at, env)
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
        if gp.shape != "" && t.tag[gp.def] == .Ident {
            append(&targs, tc_type_named(k, tc_name(k, gp.def), env, span))   // (`~T = void`)
            continue
        }
        if !gp.value {
            tc_unsupported(k, gp.def, "a generic type param's default")
            return Type_Error{}
        }
        v, known := tc_comptime_int(k, gp.def, env)
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
        if gp.shape != "" { check_shape_constraint(k.c, gp.name, gp.shape, targs[i], tmpl.pkg, span) }
    }
    subst := make(map[string]Type)
    for gp, i in gps { subst[gp.name] = targs[i] }
    return tc_instantiate_struct(k, tmpl, subst, targs[:], promoted, mangled)
}

// A generic struct's instance: its type (named for its arguments), its
// params bound in it; then its body — its fields, its methods — checked as
// its own (its nodes salted: tc_sid), its graph built apart from where it is
// named. Its init and methods are extracted with the main module's.
tc_instantiate_struct :: proc(k: ^TC, tmpl: TC_Template, subst: map[string]Type, targs: []Type,
                              promoted: map[string]bool, mangled: string) -> ^Type_Scope {
    outer: ^Graph_Body
    if k.gb != nil { outer, k.gb.body = k.gb.body, nil }
    defer if k.gb != nil { k.gb.body = outer }
    tr := k.t
    v := scope_view(tr, tmpl.node)
    span := tree_span(tr, tmpl.def)
    st := new(Type_Scope)
    st.name, st.source_name, st.home_package = make_flat_name(tmpl.pkg, mangled), mangled, tmpl.pkg
    st.kind, st.node = .Struct, tmpl.node
    st.generic_base = tc_name(k, tmpl.def)
    append(&st.generic_args, ..targs)
    st.parent_scope = tmpl.env
    st.has_parens = build_tokens[tr.main[tmpl.node] + 1].kind == .Left_Paren
    st.is_packed = v.packed != 0
    k.table.mono_cache[mangled] = st
    k.table.funs[st.name] = st
    st.decl = tr.main[tmpl.def]
    scope_bind(k.root, mangled, st, {st.decl, .Type})
    for name, bound in subst { scope_bind(st, name, bound, {tc_type_param_decl(k, tmpl.node, name), .Type}) }
    saved_subst, saved_pkg := k.subst, k.pkg
    k.subst, k.pkg = subst, tmpl.pkg
    defer k.subst, k.pkg = saved_subst, saved_pkg
    saved_inst := tc_instance_begin(k, tmpl, st)
    defer tc_instance_end(k, saved_inst)
    // (Its constructor's params: those no generic's.)
    for g in v.params {
        pv := params_view(tr, g)
        for pn, i in pv.names {
            if promoted[tc_text(pn)] { continue }
            def := pv.values[i] if i < len(pv.values) else 0
            pt := tc_param_type(k, tc_text(pn), pv.type_, def, tmpl.env, span)
            append(&st.params, Struct_Type_Field{name = tc_text(pn), decl = pn, type_ = pt, default_node = def})
        }
    }
    build_param_map(st)
    k.scope_of[st] = len(k.scopes)
    append(&k.struct_instances, len(k.scopes))
    append(&k.scopes, new_clone(TC_Scope{ts = st, def = tmpl.def, node = tmpl.node, env = tmpl.env, subst = subst, synthetic = true}))
    tc_struct_ensure(k, st)
    return st
}
