package mara

import "core:slice"
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
        if name not_in k.union_templates { k.union_templates[name] = TC_Template{def = def, node = node, lo = tree_lo(k.t, node), env = env, pkg = k.pkg} }
        return
    }
    span := tree_span(t, def)
    is_error := t.tag[node] == .Error_Def
    h: TC_Union_Header
    variants: [dynamic]TC_Variant
    if is_error {
        h.tag_type = "u32"
        for tok in tree_token_list(t, t.a[node]) {
            append(&variants, TC_Variant{name = tc_text(tok), span = Span{at = tok, tok = tok, end = tok + 1}})
        }
    } else {
        h = tc_union_header(k, node)
        variants = tc_union_variants(k, node)
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
        et.tag_type, et.is_error_kind = h.tag_type, is_error
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
    ut := tc_make_union(k, k.pkg, name, span, h, variants[:], env)
    register_enum_variants(k.c, ut.tag_enum, ut.tag_enum.name)
    scope_bind(mod, name, ut, {k.t.main[def], .Type})
    // (Its tag's enum, `Name_Tag`, a name too — `U_Tag.A` a value, as an
    // enum's variant is — declared where the union is; unless the name's taken.)
    if _, taken := scope_lookup(mod, ut.tag_enum.source_name); !taken {
        scope_bind(mod, ut.tag_enum.source_name, ut.tag_enum, {k.t.main[def], .Type})
    }
}

// A union's header, as written: its tag's type, its least size, its pad
// (its type resolved with its variants: tc_union_resolve), a generic's params.
TC_Union_Header :: struct {
    tag_type: string,
    min_size: int,
    pad:      Tree_Id,
    params:   [dynamic]string,
}

tc_union_header :: proc(k: ^TC, node: Tree_Id) -> (h: TC_Union_Header) {
    t := k.t
    h.params = make([dynamic]string, context.temp_allocator)
    for opt in tree_list(t, t.a[node]) {
        #partial switch t.tag[opt] {
        case .Generic_Param: append(&h.params, tc_name(k, opt))
        case .Union_Tag:     h.tag_type = tc_text(Token_Id(t.a[opt]))
        case .Union_Pad:     h.pad = Tree_Id(t.a[opt])
        case .Union_Size:
            _, n, _ := parse_number_text(tc_text(Token_Id(t.a[opt])))
            h.min_size = int(n)
        }
    }
    return
}

// A union's variants as written, each its tag: as written, else one past
// the one before.
tc_union_variants :: proc(k: ^TC, node: Tree_Id) -> [dynamic]TC_Variant {
    t := k.t
    variants := make([dynamic]TC_Variant, context.temp_allocator)
    next := 0
    for vn in tree_list(t, t.b[node]) {
        tag := next
        if v := Tree_Id(t.a[vn]); v != 0 {
            if _, i, lit := tc_literal_value(k, v); lit { tag = int(i) }
        }
        next = tag + 1
        append(&variants, tc_variant(k, vn, tag))
    }
    return variants
}

// A union's type, made: `name` in module `pkg` (an instance's, its mangled
// name), its tag an enum of its own (`Name_Tag`), each variant a struct
// (tc_variant_struct). (`subst`: an instance's params, bound.)
tc_make_union :: proc(k: ^TC, pkg, name: string, span: Span, h: TC_Union_Header, variants: []TC_Variant, env: ^Type_Scope,
                      subst: map[string]Type = nil) -> ^Type_Union {
    ut := new(Type_Union)
    ut.name, ut.source_name, ut.home_package, ut.span = make_flat_name(pkg, name), name, pkg, span
    ut.tag_type, ut.min_size = h.tag_type, h.min_size
    tag_et := new(Type_Enum)
    tag_et.source_name = strings.concatenate({name, "_Tag"})
    tag_et.name = make_flat_name(pkg, tag_et.source_name)
    tag_et.home_package, tag_et.tag_type, tag_et.span, tag_et.is_synthetic = pkg, h.tag_type, span, true
    for v in variants { tag_et.variants[v.name], tag_et.variant_decls[v.name] = v.tag, v.span.at }
    k.table.enums[tag_et.name] = tag_et
    ut.tag_enum = tag_et
    for v in variants {
        append(&ut.variants, v.name)
        ut.tag_map[v.name] = v.tag
        ut.variant_structs[v.name] = tc_variant_struct(k, pkg, name, v, env, subst)
        ut.variant_structs[v.name].variant_of = ut
    }
    k.table.unions[ut.name] = ut
    return ut
}

TC_Variant :: struct {
    name:   string,
    tag:    int,
    node:   Tree_Id,
    body:   Tree_Id,   // its Struct_Def (0: none)
    fields: bool,      // (its body declares something, or it has params: it is built)
    span:   Span,
}

// A union's variant as written, its tag given.
tc_variant :: proc(k: ^TC, vn: Tree_Id, tag: int) -> TC_Variant {
    t := k.t
    main := t.main[vn]
    body := Tree_Id(t.b[vn])
    v := scope_view(t, body) if body != 0 else {}
    return {name = tc_name(k, vn), tag = tag, node = vn, body = body, fields = len(v.body) > 0 || len(v.params) > 0,
            span = Span{at = main, tok = main, end = main + 1}}
}

// A variant's struct, named for its union (`Shape_Rect`). Its body is a
// struct's: registered as one — its params, its declarations its fields
// (both once every name is known: tc_union_resolve) — run as its constructor
// when it is built. (`subst`: a generic union's instance's bindings.)
tc_variant_struct :: proc(k: ^TC, pkg, union_name: string, v: TC_Variant, env: ^Type_Scope, subst: map[string]Type = nil) -> ^Type_Scope {
    vst := new(Type_Scope)
    vst.source_name = strings.concatenate({union_name, "_", v.name})
    vst.name = make_flat_name(pkg, vst.source_name)
    vst.home_package, vst.kind, vst.body_span = pkg, .Struct, v.span
    vst.decl = v.span.at
    k.table.structs[vst.name] = vst
    if v.fields {
        vst.node, vst.parent_scope = v.body, env
        k.scope_of[vst] = len(k.scopes)
        append(&k.variant_scopes, len(k.scopes))
        append(&k.scopes, new_clone(TC_Scope{ts = vst, def = v.node, node = v.body, env = env, subst = subst, synthetic = subst != nil}))
    }
    return vst
}

// A union's pad's type and its variants' params and bodies, once every name
// is known (an instance's, its params bound): each variant's fields found,
// then its tag put first — its layout known.
tc_union_resolve :: proc(k: ^TC, ut: ^Type_Union, pad: Tree_Id, env: ^Type_Scope, span: Span) {
    if pad != 0 { ut.tag_pad = tc_type(k, pad, env, span) }
    for vname in ut.variants {
        if i, has := k.scope_of[ut.variant_structs[vname]]; has { tc_signature(k, k.scopes[i]) }
    }
    for vname in ut.variants { tc_struct_ensure(k, ut.variant_structs[vname]) }
    finalize_union_variant_headers(k.c, ut)
}

// A module's union, resolved (tc_union_resolve).
tc_resolve_union :: proc(k: ^TC, def, node: Tree_Id, env: ^Type_Scope) {
    t := k.t
    ut, ok := k.table.unions[make_flat_name(k.pkg, tc_name(k, def))]
    if !ok || t.tag[node] != .Union_Def { return }
    tc_union_resolve(k, ut, tc_union_header(k, node).pad, env, tree_span(t, def))
}

// A variant named by itself (`.Red`, or `Red` where an enum is expected):
// the variant of the enum expected, or — `.Red` — the one enum visible that
// has it.
tc_variant_ident :: proc(k: ^TC, name: string, hint: Type, env: ^Type_Scope, dot: bool, span: Span) -> (Type, int, bool) {
    if hint != nil {
        // (A named enum or union — `type E`, `distinct U` — looked in as its
        // base is; the variant is of the named one, so a distinct one takes it.)
        hb := distinct_base(hint)
        if et, is_enum := hb.(^Type_Enum); is_enum {
            if v, has := et.variants[name]; has { return hint, v, true }
        }
        if ut, is_union := hb.(^Type_Union); is_union {
            if v, has := ut.tag_map[name]; has { return hint, v, true }
        }
        if _, is_err := hb.(Type_Err); is_err {
            owners := make([dynamic]string, context.temp_allocator)
            for ename, edef in k.table.enums {
                if edef.is_error_kind && name in edef.variants && is_enum_visible(env, ename) { append(&owners, ename) }
            }
            tc_error_ok(k, name, &owners)
            if len(owners) > 1 {
                tc_variant_ambiguous(k, name, owners[:], span)
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
    tc_error_ok(k, name, &owners)
    if len(owners) > 1 {
        tc_variant_ambiguous(k, name, owners[:], span)
        return nil, 0, true
    }
    if len(owners) == 1 {
        et := k.table.enums[owners[0]]
        return et, et.variants[name], true
    }
    return nil, 0, false
}

// Ok is 0 in every error set, the one no-error value: `.Ok` that only error
// sets name is theirs, not an ambiguity — the first set's, the same one
// every build.
tc_error_ok :: proc(k: ^TC, name: string, owners: ^[dynamic]string) {
    if name != "Ok" || len(owners) < 2 { return }
    first := owners[0]
    for o in owners {
        et := k.table.enums[o]
        if !et.is_error_kind { return }
        if et.error_set_id < k.table.enums[first].error_set_id { first = o }
    }
    clear(owners)
    append(owners, first)
}

// `.name` that more than one enum visible has: an error naming them as the
// source does.
tc_variant_ambiguous :: proc(k: ^TC, name: string, owners: []string, span: Span) {
    names := make([dynamic]string, context.temp_allocator)
    for o in owners { append(&names, type_name(k.table.enums[o])) }
    slice.sort(names[:])
    tc_error(k, span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS, name, strings.join(names[:], ", ", context.temp_allocator), names[0], name)
}

// A variant built at n — its literal, its name as a value: its constructor
// called there, when it has one (the graph's Calls edge). One with params is
// built by them (tc_variant_call): it can't be built bare.
tc_variant_built :: proc(k: ^TC, n: Tree_Id, t: Type, name: string) {
    ut, is_union := distinct_base(t).(^Type_Union)
    if !is_union { return }
    st := ut.variant_structs[name]
    if st == nil || st.node == 0 { return }
    if count_required_params(st) > 0 {
        tc_error(k, tree_span(k.t, n), TYPE_VARIANT_NEEDS_ARGS, name, name)
        return
    }
    tc_set_callee(k, n, st)
    tc_set_args(k, n, tc_default_args(st))
    tc_ctor_args(k, st, tree_span(k.t, n))
}

// `Rect(5)` where a Shape goes, `Shape.Rect(5)`: a union's variant built by
// its params — its arguments checked as a struct's constructor's are, its
// value the union's.
tc_variant_call :: proc(k: ^TC, n: Tree_Id, ut: ^Type_Union, name: string, args: []Tree_Id, env: ^Type_Scope) -> Type {
    vst := ut.variant_structs[name]
    if vst == nil || len(vst.params) == 0 {
        tc_error(k, tree_span(k.t, n), TYPE_VARIANT_TAKES_NO_ARGS, name, name, "{…}", name)
        return Type_Error{}
    }
    qualified := strings.concatenate({ut.source_name, ".", name}, context.temp_allocator)   // (as its diagnostics name it)
    if _, failed := tc_call_core(k, n, qualified, args, env, qual = vst).(Type_Error); failed { return Type_Error{} }
    tc_set_ref(k, n, {variant_decl(ut, name), .Variant})
    return ut
}

// The union a literal named by a bare variant builds: the one expected,
// else the one union with that variant (two such: ambiguous, reported).
tc_variant_union :: proc(k: ^TC, name: string) -> (^Type_Union, bool) {
    if ut, is_union := distinct_base(k.hint).(^Type_Union); is_union && name in ut.tag_map { return ut, false }
    if ut := variant_owner_union(k.c, name); ut != nil { return ut, false }
    return nil, false
}

// Whether a union is generic: its header names a param (`union($T: type)`).
tc_union_is_generic :: proc(k: ^TC, node: Tree_Id) -> bool {
    if k.t.tag[node] != .Union_Def { return false }
    for opt in tree_list(k.t, k.t.a[node]) {
        if k.t.tag[opt] == .Generic_Param { return true }
    }
    return false
}

// `Name(args)`, Name a generic union: its instance (once) — its params bound
// to the arguments, then made and resolved as a union is, its variants'
// bodies checked again as its own. A niche — `Maybe(^T)`: the pointer, None
// its null — is decided as a union's is (finalize_union_variant_headers).
tc_union_instance :: proc(k: ^TC, n: Tree_Id, tmpl: TC_Template, env: ^Type_Scope, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    h := tc_union_header(k, tmpl.node)
    targs := make([dynamic]Type, context.temp_allocator)
    for a in tree_list(t, t.a[n]) { append(&targs, tc_type(k, a, env, span)) }
    if len(targs) != len(h.params) {
        tc_error(k, span, TYPE_EXPECTS_TYPE_ARGUMENT, name, len(h.params), len(targs))
        return Type_Error{}
    }
    mangled := mangle_generic_name(name, targs[:])
    if ut, made := k.table.mono_union_cache[mangled]; made { return ut }
    subst := make(map[string]Type)
    for p, i in h.params { subst[p] = targs[i] }
    saved_subst, saved_pkg := k.subst, k.pkg
    k.subst, k.pkg = subst, tmpl.pkg
    defer k.subst, k.pkg = saved_subst, saved_pkg
    ut := tc_make_union(k, tmpl.pkg, mangled, tree_span(t, tmpl.def), h, tc_union_variants(k, tmpl.node)[:], tmpl.env, subst)
    k.table.mono_union_cache[mangled] = ut
    scope_bind(k.root, mangled, ut, {ut.span.at, .Type})
    // (Its variants' bodies are its template's, checked again with its params
    // bound: their nodes its own — tc_sid.)
    saved_inst := tc_instance_begin(k, tmpl, nil)
    defer tc_instance_end(k, saved_inst)
    tc_union_resolve(k, ut, h.pad, tmpl.env, span)
    return ut
}
