package mara

import "core:strings"

// Unions and enums in the checker. `Name :: union { A, B = 5 }` with no
// variant holding fields is an enum; one with fields a union — its tag an
// enum of its own (`Name_Tag`), each variant a struct (`Name_A`) whose first
// field is the tag. `Name :: error { A, B }` is an enum of the global error
// set (each variant's value its set's id and its place in it).

// Its name declared, its type made (a union's fields wait: tc_resolve_union).
tc_register_union :: proc(k: ^TC, def, node: Tree_Id, env, mod: ^Type_Scope) {
    t := k.t
    name := tc_name(k, def)
    // (A generic union: a template, made as each instance — tc_union_instance.)
    if tc_union_is_generic(k, node) {
        if name not_in k.union_templates { k.union_templates[name] = TC_Template{def = def, node = node, lo = tc_subtree_lo(k, node), env = env, pkg = k.pkg} }
        return
    }
    span := tree_span(t, def)
    is_error := t.tag[node] == .Error_Def
    tag_type, min_size := "", 0
    variants := make([dynamic]TC_Variant, context.temp_allocator)
    if is_error {
        tag_type = "u32"
        for tok in tree_token_list(t, t.a[node]) {
            append(&variants, TC_Variant{name = tc_text(tok), span = Span{at = tok, tok = tok, end = tok + 1}})
        }
    } else {
        for opt in tree_list(t, t.a[node]) {
            #partial switch t.tag[opt] {
            case .Union_Tag:  tag_type = tc_text(Token_Id(t.a[opt]))
            case .Union_Size:
                _, n, _ := parse_number_text(tc_text(Token_Id(t.a[opt])))
                min_size = int(n)
            case .Union_Pad:
            case:
                tc_unsupported(k, opt, "a generic union")
                return
            }
        }
        next := 0
        for vn in tree_list(t, t.b[node]) {
            // (Its tag: as written, else one past the one before.)
            tag := next
            if v := Tree_Id(t.a[vn]); v != 0 {
                if _, i, lit := tc_literal_value(k, v); lit { tag = int(i) }
            }
            next = tag + 1
            main := t.main[vn]
            append(&variants, TC_Variant{name = tc_name(k, vn), tag = tag, node = vn, fields = len(tree_list(t, t.b[vn])) > 0,
                                         span = Span{at = main, tok = main, end = main + 1}})
        }
    }
    has_data := false
    for v in variants { if v.fields { has_data = true } }
    flat := make_flat_name(k.pkg, name)
    if !has_data {
        if flat in k.table.enums {
            tc_error(k, span, TYPE_ENUM_ALREADY_DEFINED, name)
            return
        }
        et := new(Type_Enum)
        et.name, et.source_name, et.home_package, et.span = flat, name, k.pkg, span
        et.tag_type, et.is_error_kind = tag_type, is_error
        if is_error {
            // (Its set's id, its variants' values its id and their place.)
            k.table.error_set_counter += 1
            et.error_set_id = k.table.error_set_counter
            et.variants["Ok"] = 0
            for v, i in variants {
                et.variants[v.name] = (et.error_set_id << 16) | (i + 1)
                et.variant_decls[v.name] = v.span.at
            }
        } else {
            for v in variants { et.variants[v.name], et.variant_decls[v.name] = v.tag, v.span.at }
        }
        k.table.enums[flat] = et
        scope_bind(mod, name, et, {k.t.main[def], .Type})
        register_enum_variants(k.c, et, flat)
        return
    }
    if flat in k.table.unions {
        tc_error(k, span, TYPE_UNION_ALREADY_DEFINED, name)
        return
    }
    ut := new(Type_Union)
    ut.name, ut.source_name, ut.home_package, ut.span = flat, name, k.pkg, span
    ut.tag_type, ut.min_size = tag_type, min_size
    tag_et := new(Type_Enum)
    tag_et.name = make_flat_name(k.pkg, strings.concatenate({name, "_Tag"}))
    tag_et.home_package, tag_et.tag_type, tag_et.span, tag_et.is_synthetic = k.pkg, tag_type, span, true
    for v in variants { tag_et.variants[v.name], tag_et.variant_decls[v.name] = v.tag, v.span.at }
    k.table.enums[tag_et.name] = tag_et
    register_enum_variants(k.c, tag_et, tag_et.name)
    ut.tag_enum = tag_et
    for v in variants {
        vst := new(Type_Scope)
        vst.name = make_flat_name(k.pkg, strings.concatenate({name, "_", v.name}))
        vst.home_package, vst.kind, vst.body_span = k.pkg, .Struct, v.span
        vst.decl = v.span.at
        k.table.structs[vst.name] = vst
        append(&ut.variants, v.name)
        ut.tag_map[v.name] = v.tag
        ut.variant_structs[v.name] = vst
    }
    k.table.unions[flat] = ut
    scope_bind(mod, name, ut, {k.t.main[def], .Type})
}

TC_Variant :: struct {
    name:   string,
    tag:    int,
    node:   Tree_Id,
    fields: bool,
    span:   Span,
}

// A union's pad and its variants' fields, once every name is known; each
// variant's tag its first field.
tc_resolve_union :: proc(k: ^TC, def, node: Tree_Id, env: ^Type_Scope) {
    t := k.t
    ut, ok := k.table.unions[make_flat_name(k.pkg, tc_name(k, def))]
    if !ok || t.tag[node] != .Union_Def { return }
    span := tree_span(t, def)
    for opt in tree_list(t, t.a[node]) {
        if t.tag[opt] == .Union_Pad { ut.tag_pad = tc_type(k, Tree_Id(t.a[opt]), env, span) }
    }
    for vn in tree_list(t, t.b[node]) {
        vst := ut.variant_structs[tc_name(k, vn)]
        if vst == nil { continue }
        for f in tree_list(t, t.b[vn]) {
            ft := tc_type(k, Tree_Id(t.a[f]), env, span)
            append(&vst.fields, Struct_Type_Field{name = tc_name(k, f), decl = t.main[f], type_ = ft, default_node = Tree_Id(t.b[f])})
        }
        build_field_map(&vst.sd)
    }
    finalize_union_variant_headers(k.c, ut)
}

// A variant named by itself (`.Red`, or `Red` where an enum is expected):
// the variant of the enum expected, or — `.Red` — the one enum visible that
// has it.
tc_variant_ident :: proc(k: ^TC, name: string, hint: Type, env: ^Type_Scope, dot: bool, span: Span) -> (Type, int, bool) {
    if hint != nil {
        if et, is_enum := hint.(^Type_Enum); is_enum {
            if v, has := et.variants[name]; has { return et, v, true }
        }
        if ut, is_union := hint.(^Type_Union); is_union {
            if v, has := ut.tag_map[name]; has { return ut, v, true }
        }
        if _, is_err := hint.(Type_Err); is_err {
            owners := make([dynamic]string, context.temp_allocator)
            for ename, edef in k.table.enums {
                if edef.is_error_kind && name in edef.variants && is_enum_visible(env, ename) { append(&owners, ename) }
            }
            if len(owners) > 1 {
                tc_error(k, span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS, name, strings.join(owners[:], ", "), owners[0], name)
                return nil, 0, true
            }
            if len(owners) == 1 {
                et := k.table.enums[owners[0]]
                return et, et.variants[name], true
            }
        }
    }
    if !dot { return nil, 0, false }
    owners := make([dynamic]string, context.temp_allocator)
    for ename, edef in k.table.enums {
        if name in edef.variants && is_enum_visible(env, ename) { append(&owners, ename) }
    }
    if len(owners) > 1 {
        tc_error(k, span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS, name, strings.join(owners[:], ", "), owners[0], name)
        return nil, 0, true
    }
    if len(owners) == 1 {
        et := k.table.enums[owners[0]]
        return et, et.variants[name], true
    }
    return nil, 0, false
}

// An enum's variant, as a value: its tag, known.
tc_variant_value :: proc(k: ^TC, et: ^Type_Enum, value: int, name: string, span: Span, want: Build_Want, w: Written) -> Built {
    b := tc_building(k)
    if b == nil || want == .None || want == .Place { return {} }
    return {v = graph_const(b, w, span, et, name, Const_Value{int = i128(value)}), ok = true}
}

// A union's variant as a value (`.Circle`, `Shape.Circle`, `Circle` where a
// Shape is expected): the variant constructed where it goes — else in a
// temporary made first, read — then its fields' defaults.
tc_union_variant :: proc(k: ^TC, ut: ^Type_Union, name: string, span: Span, want: Build_Want, w: Written,
                         dest: Dest, temp: bool, temp_span: Span) -> Built {
    b := tc_building(k)
    if b == nil || want == .None || want == .Place {
        // (Not built: its defaults checked all the same.)
        tc_variant_defaults(k, ut.variant_structs[name], nil, {}, span)
        return {}
    }
    if want == .Into {
        d := dest
        if temp { d = graph_build_temp(b, temp_span, build_temp_type(d)) }
        tc_variant_build(k, ut, name, d, span)
        return tc_built(k, want, temp, temp, d, ut, temp_span, false)
    }
    d := graph_build_temp(b, span, ut)
    tc_variant_build(k, ut, name, d, span)
    if b = tc_building(k); b == nil { return {} }
    return {v = graph_read(b, graph_dest_place(b, d, span), ut, span), ok = true}
}

// A variant built at d: its construction, then its defaults.
tc_variant_build :: proc(k: ^TC, t: Type, name: string, d: Dest, span: Span) {
    b := tc_building(k)
    if b == nil { return }
    st := graph_build_variant(b, t, name, d, span)
    dd := d
    tc_variant_defaults(k, st, nil, Dest{kind = .Variant, name = name, type_ = st, parent = &dd}, span)
}

// A variant's field defaults, each one a literal doesn't give (`given`),
// written into its place once it's constructed.
tc_variant_defaults :: proc(k: ^TC, st: ^Type_Scope, given: map[string]bool, d: Dest, span: Span) {
    if st == nil { return }
    for f in st.fields {
        if f.default_node == 0 || f.name in given { continue }
        v := tc_default(k, f.default_node, f.type_, st, span, {to = f.type_})
        if b := tc_building(k); b != nil { graph_build_field_default(b, d, f.name, f.type_, v, span) }
    }
}

// A variant as a value: an enum's its tag; a union's constructed.
tc_variant_of :: proc(k: ^TC, t: Type, value: int, name: string, span: Span, want: Build_Want, w: Written,
                      dest: Dest, temp: bool, temp_span: Span) -> Built {
    if ut, is_union := t.(^Type_Union); is_union { return tc_union_variant(k, ut, name, span, want, w, dest, temp, temp_span) }
    return tc_variant_value(k, t.(^Type_Enum), value, name, span, want, w)
}

// The union a literal named by a bare variant builds: the one expected,
// else the one union with that variant (two such: ambiguous, reported).
tc_variant_union :: proc(k: ^TC, name: string) -> (^Type_Union, bool) {
    if ut, is_union := distinct_base(k.hint).(^Type_Union); is_union && name in ut.tag_map { return ut, false }
    if ut := variant_owner_union(k.c, name); ut != nil { return ut, false }
    return nil, false
}

// The fields a literal gives: named, or by position (past a variant's tag).
tc_literal_given :: proc(k: ^TC, entries: []Tree_Id, sd: ^Scope_Body) -> map[string]bool {
    given := make(map[string]bool, context.temp_allocator)
    skip := first_user_field(sd)
    for e, j in entries {
        if k.t.tag[e] == .Named_Entry {
            given[tc_name(k, e)] = true
        } else if skip + j < len(sd.fields) {
            given[sd.fields[skip + j].name] = true
        }
    }
    return given
}

// Whether a union is generic: its header names a param (`union($T: type)`).
tc_union_is_generic :: proc(k: ^TC, node: Tree_Id) -> bool {
    if k.t.tag[node] != .Union_Def { return false }
    for opt in tree_list(k.t, k.t.a[node]) {
        if k.t.tag[opt] == .Generic_Param { return true }
    }
    return false
}

// `Name(args)`, Name a generic union: its instance — its params bound to the
// arguments, its tag enum and its variants' structs made for them (once). A
// niche — `Maybe(^T)`: the pointer, None its null — is decided as a union's
// is (finalize_union_variant_headers).
tc_union_instance :: proc(k: ^TC, n: Tree_Id, tmpl: TC_Template, env: ^Type_Scope, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    params := make([dynamic]string, context.temp_allocator)
    tag_type, min_size := "", 0
    pad := Tree_Id(0)
    for opt in tree_list(t, t.a[tmpl.node]) {
        #partial switch t.tag[opt] {
        case .Generic_Param: append(&params, tc_name(k, opt))
        case .Union_Tag:     tag_type = tc_text(Token_Id(t.a[opt]))
        case .Union_Pad:     pad = Tree_Id(t.a[opt])
        case .Union_Size:
            _, size, _ := parse_number_text(tc_text(Token_Id(t.a[opt])))
            min_size = int(size)
        }
    }
    args := tree_list(t, t.a[n])
    targs := make([dynamic]Type, context.temp_allocator)
    for a in args { append(&targs, tc_type(k, a, env, span)) }
    if len(targs) != len(params) {
        tc_error(k, span, TYPE_EXPECTS_TYPE_ARGUMENT, name, len(params), len(targs))
        return Type_Error{}
    }
    mangled := mangle_generic_name(name, targs[:])
    if ut, made := k.table.mono_union_cache[mangled]; made { return ut }
    subst := make(map[string]Type)
    for p, i in params { subst[p] = targs[i] }
    saved_subst, saved_pkg := k.subst, k.pkg
    k.subst, k.pkg = subst, tmpl.pkg
    defer k.subst, k.pkg = saved_subst, saved_pkg
    def_span := tree_span(t, tmpl.def)
    ut := new(Type_Union)
    ut.name, ut.source_name, ut.home_package, ut.span = make_flat_name(tmpl.pkg, mangled), mangled, tmpl.pkg, def_span
    ut.tag_type, ut.min_size = tag_type, min_size
    if pad != 0 { ut.tag_pad = tc_type(k, pad, tmpl.env, span) }
    tag_et := new(Type_Enum)
    tag_et.name = make_flat_name(tmpl.pkg, strings.concatenate({mangled, "_Tag"}))
    tag_et.home_package, tag_et.tag_type, tag_et.span, tag_et.is_synthetic = tmpl.pkg, tag_type, def_span, true
    // (Each variant's tag: as written, else one past the one before.)
    variants := tree_list(t, t.b[tmpl.node])
    tags := make([]int, len(variants), context.temp_allocator)
    next := 0
    for vn, i in variants {
        tags[i] = next
        if v := Tree_Id(t.a[vn]); v != 0 {
            if _, at, lit := tc_literal_value(k, v); lit { tags[i] = int(at) }
        }
        next = tags[i] + 1
        tag_et.variants[tc_name(k, vn)], tag_et.variant_decls[tc_name(k, vn)] = tags[i], t.main[vn]
    }
    k.table.enums[tag_et.name] = tag_et
    ut.tag_enum = tag_et
    for vn, i in variants {
        vname := tc_name(k, vn)
        main := t.main[vn]
        vst := new(Type_Scope)
        vst.name = make_flat_name(tmpl.pkg, strings.concatenate({mangled, "_", vname}))
        vst.home_package, vst.kind, vst.body_span = tmpl.pkg, .Struct, Span{at = main, tok = main, end = main + 1}
        vst.decl = main
        for f in tree_list(t, t.b[vn]) {
            ft := tc_type(k, Tree_Id(t.a[f]), tmpl.env, span)
            append(&vst.fields, Struct_Type_Field{name = tc_name(k, f), decl = t.main[f], type_ = ft, default_node = Tree_Id(t.b[f])})
        }
        build_field_map(&vst.sd)
        k.table.structs[vst.name] = vst
        append(&ut.variants, vname)
        ut.tag_map[vname] = tags[i]
        ut.variant_structs[vname] = vst
    }
    finalize_union_variant_headers(k.c, ut)
    k.table.unions[ut.name] = ut
    k.table.mono_union_cache[mangled] = ut
    scope_bind(k.root, mangled, ut, {ut.span.at, .Type})
    return ut
}
