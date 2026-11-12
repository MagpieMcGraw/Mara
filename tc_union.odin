package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// Unions and enums in the checker. `Name :: union { A, B = 5 }` with no
// variant holding fields is an enum; one with fields a union — its tag an
// enum of its own (`Name_Tag`), each variant a struct (`Name_A`) whose first
// field is the tag. `Name :: error { A, B }` is an enum of the global error
// set (each variant's value its set's id and its place in it).

// Its name declared, its type made (a union's fields wait: tc_resolve_union).
// (`owner`: the scope defining it — named for it, as a struct is. A body's
// variants are seen only there; a module's, wherever the module is.)
tc_register_union :: proc(k: ^TC, def, node: Tree_Id, owner: ^Type_Scope) {
    t := k.t
    name := tc_name(k, def)
    filed := tc_def_name(k, def)
    // (A generic union: a template, made as each instance — tc_union_instance.)
    if tc_union_is_generic(k, node) {
        k.templates[t.main[def]] = TC_Template{def = def, node = node, lo = tree_lo(k.t, node), pkg = k.pkg, owner = owner}
        return
    }
    span := tree_span(t, def)
    is_error := t.tag[node] == .Error_Def
    h: TC_Union_Header
    variants: [dynamic]TC_Variant
    if is_error {
        // (An err's width: its kind low, where it was made high — tc_note_err_site.)
        h.tag_type = "u64"
        for tok in tree_token_list(t, t.a[node]) {
            append(&variants, TC_Variant{name = tc_text(tok), span = Span{at = tok, tok = tok, end = tok + 1}})
        }
    } else {
        h = tc_union_header(k, node)
        variants = tc_union_variants(k, node)
        tc_union_same_tags(k, variants[:])
    }
    has_data := false
    for v in variants { if v.fields { has_data = true } }
    flat := make_flat_name(owner.name, filed)
    if !has_data {
        if flat in k.table.enums {
            tc_error(k, span, TYPE_ENUM_ALREADY_DEFINED, name)
            return
        }
        // (One definition is one enum: a generic's body's, its first
        // instance's, is every instance's — nothing in it is the generic's
        // params'.)
        if made := k.text_enums[def] or_else nil; made != nil {
            tc_bound_set(k, k.t.main[def], made)
            for _, tok in made.variant_decls { tc_bound_set(k, tok, made) }
            return
        }
        et := new(Type_Enum)
        k.text_enums[def] = et
        et.name, et.source_name, et.home_package, et.span = flat, name, k.pkg, span
        et.tag_type, et.is_error_kind, et.owner = h.tag_type, is_error, owner
        et.sight_lo, et.sight_hi, et.sight_block = tc_sight(k, def, owner)
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
            et.zero_name = tc_zero_name(variants[:])
        }
        k.table.enums[flat] = et
        tc_bound_set(k, k.t.main[def], et)
        for _, tok in et.variant_decls { tc_bound_set(k, tok, et) }   // (a variant named, `m.Red`: its enum's value)
        return
    }
    if flat in k.table.unions {
        tc_error(k, span, TYPE_UNION_ALREADY_DEFINED, name)
        return
    }
    ut := tc_make_union(k, k.pkg, filed, span, h, variants[:], nil, owner, shown = name)
    ut.tag_enum.sight_lo, ut.tag_enum.sight_hi, ut.tag_enum.sight_block = tc_sight(k, def, owner)
    ut.tag_enum.span.at = t.main[node]   // (its tag's enum: declared by its `union`)
    tc_bound_set(k, k.t.main[def], ut)
    // (Its tag's enum, `Name_Tag`, a name too — `U_Tag.A` a value, as an
    // enum's variant is — declared where the union is, by its `union`; unless
    // the name's taken.)
    tc_bound_set(k, k.t.main[node], ut.tag_enum)
}

// A union's header, as written: its tag's type, its least size, its pad
// (its type resolved with its variants: tc_union_resolve), a generic's params.
TC_Union_Header :: struct {
    tag_type: string,
    min_size: int,
    pad:      Tree_Id,
    params:   [dynamic]Token_Id,   // a generic's: the tokens that declare them
}

tc_union_header :: proc(k: ^TC, node: Tree_Id) -> (h: TC_Union_Header) {
    t := k.t
    h.params = make([dynamic]Token_Id, context.temp_allocator)
    for opt in tree_list(t, t.a[node]) {
        #partial switch t.tag[opt] {
        case .Generic_Param: append(&h.params, t.main[opt])
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
// the one before. A variant written `= 0` counts as the first, wherever it
// is: `{ a, none = 0, b }` is 1, 0, 2.
tc_union_variants :: proc(k: ^TC, node: Tree_Id) -> [dynamic]TC_Variant {
    t := k.t
    variants := make([dynamic]TC_Variant, context.temp_allocator)
    // (The values written, `none = 0`: a variant not written takes none of
    // them — the one after the last, else the next free.)
    written := make(map[int]bool, context.temp_allocator)
    for vn in tree_list(t, t.b[node]) {
        if v := Tree_Id(t.a[vn]); v != 0 {
            if _, i, lit := tc_literal_value(k, v); lit { written[int(i)] = true }
        }
    }
    next := 0
    for vn in tree_list(t, t.b[node]) {
        tag, explicit := next, false
        if v := Tree_Id(t.a[vn]); v != 0 {
            if _, i, lit := tc_literal_value(k, v); lit { tag, explicit = int(i), true }
        }
        if !explicit {
            for written[tag] { tag += 1 }
        }
        // (A `= 0` leaves the count where it was: as if written first.)
        if !explicit || tag != 0 { next = tag + 1 }
        variant := tc_variant(k, vn, tag)
        variant.explicit = explicit
        append(&variants, variant)
    }
    return variants
}

// A variant not given a value that lands on another's, said so at the
// second: `{ x = 2, y, z = 1, w }` gives w y's 3. (Two written alike are
// allowed: another name for one value.)
tc_union_same_tags :: proc(k: ^TC, variants: []TC_Variant) {
    first := make(map[int]TC_Variant, context.temp_allocator)
    for v in variants {
        if other, taken := first[v.tag]; taken {
            if !v.explicit || !other.explicit { tc_error(k, v.span, TYPE_UNION_SAME_TAG, other.name, v.name, v.tag) }
            continue
        }
        first[v.tag] = v
    }
}

// A union's type, made: `name` in module `pkg` (an instance's, its mangled
// name), its tag an enum of its own (`Name_Tag`), each variant a struct
// (tc_variant_struct). (`subst`: an instance's params, bound. `owner`: the
// scope defining it — named for it, as a struct is.)
tc_make_union :: proc(k: ^TC, pkg, name: string, span: Span, h: TC_Union_Header, variants: []TC_Variant,
                      subst: TC_Bindings, owner: ^Type_Scope, shown := "") -> ^Type_Union {
    ut := new(Type_Union)
    shown := shown if shown != "" else name   // (as written: a block's is filed with its number)
    ut.name, ut.source_name, ut.home_package, ut.span = make_flat_name(owner.name, name), shown, pkg, span
    ut.tag_type, ut.min_size = h.tag_type, h.min_size
    tag_et := new(Type_Enum)
    tag_et.source_name = strings.concatenate({shown, "_Tag"})
    tag_et.name = make_flat_name(owner.name, strings.concatenate({name, "_Tag"}))
    tag_et.owner = owner
    tag_et.sight_lo, tag_et.sight_hi = k.t.first[owner.node], k.t.end[owner.node]
    tag_et.home_package, tag_et.tag_type, tag_et.span, tag_et.is_synthetic = pkg, h.tag_type, span, true
    for v in variants { tag_et.variants[v.name], tag_et.variant_decls[v.name] = v.tag, v.span.at }
    tag_et.zero_name = tc_zero_name(variants)
    k.table.enums[tag_et.name] = tag_et
    ut.tag_enum = tag_et
    for v in variants {
        append(&ut.variants, v.name)
        ut.tag_map[v.name] = v.tag
        vst := tc_variant_struct(k, pkg, name, v, subst, owner)
        vst.variant_of = ut
        ut.variant_structs[v.name] = vst
        tc_bound_set(k, vst.decl, vst)   // (a variant named, `Shape.Rect`: its struct)
    }
    k.table.unions[ut.name] = ut
    return ut
}

TC_Variant :: struct {
    name:   string,
    tag:    int,
    explicit: bool,    // its tag written, `= 0`
    node:   Tree_Id,
    body:   Tree_Id,   // its Struct_Def (0: none)
    fields: bool,      // (its body declares something, or it has params: it is built)
    span:   Span,
}

// The variant written `= 0`, the first; "" for none.
tc_zero_name :: proc(variants: []TC_Variant) -> string {
    for v in variants { if v.explicit && v.tag == 0 { return v.name } }
    return ""
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
tc_variant_struct :: proc(k: ^TC, pkg, union_name: string, v: TC_Variant, subst: TC_Bindings, owner: ^Type_Scope) -> ^Type_Scope {
    vst := new(Type_Scope)
    vst.source_name = strings.concatenate({union_name, "_", v.name})
    vst.name = make_flat_name(owner.name, vst.source_name)
    vst.home_package, vst.kind, vst.body_span = pkg, .Struct, v.span
    vst.decl = v.span.at
    k.table.funs[vst.name] = vst
    if v.fields {
        vst.node, vst.parent_scope = v.body, owner
        k.scope_of[vst] = len(k.scopes)
        append(&k.variant_scopes, len(k.scopes))
        append(&k.scopes, new_clone(TC_Scope{ts = vst, def = v.node, node = v.body, subst = subst, synthetic = subst != nil}))
    }
    return vst
}

// A union's pad's type and its variants' params and bodies, once every name
// is known (an instance's, its params bound): each variant's fields found,
// then its tag put first — its layout known.
tc_union_resolve :: proc(k: ^TC, ut: ^Type_Union, pad: Tree_Id, span: Span) {
    if pad != 0 { ut.tag_pad = tc_type(k, pad, span) }
    for vname in ut.variants {
        if i, has := k.scope_of[ut.variant_structs[vname]]; has { tc_signature(k, k.scopes[i]) }
    }
    for vname in ut.variants { tc_struct_ensure(k, ut.variant_structs[vname]) }
    finalize_union_variant_headers(k.c, ut)
}

// A module's union, resolved (tc_union_resolve).
tc_resolve_union :: proc(k: ^TC, def, node: Tree_Id) {
    t := k.t
    bound, _ := tc_bound(k, t.main[def])
    ut, ok := bound.(^Type_Union)
    if !ok || t.tag[node] != .Union_Def { return }
    tc_union_resolve(k, ut, tc_union_header(k, node).pad, tree_span(t, def))
}

// A variant named by itself (`.Red`, or `Red` where an enum is expected):
// the variant of the enum expected, or — `.Red` — the one enum visible that
// has it.
tc_variant_ident :: proc(k: ^TC, name: string, hint: Type, dot: bool, span: Span, bare := false) -> (Type, int, bool) {
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
            owners := tc_variant_enums(k, name, span, errors = true)
            tc_error_ok(k, name, &owners)
            if len(owners) > 1 {
                tc_variant_ambiguous(k, name, owners[:], span, bare)
                return nil, 0, true
            }
            if len(owners) == 1 {
                et := k.table.enums[owners[0]]
                return et, et.variants[name], true
            }
        }
    }
    if !dot { return nil, 0, false }
    owners := tc_variant_enums(k, name, span)
    tc_error_ok(k, name, &owners)
    if len(owners) > 1 {
        tc_variant_ambiguous(k, name, owners[:], span, bare)
        return nil, 0, true
    }
    if len(owners) == 1 {
        et := k.table.enums[owners[0]]
        return et, et.variants[name], true
    }
    return nil, 0, false
}

// The enums in sight where `span` is that have a variant `name` (`errors`:
// the error sets alone), by name. (A union with fields in a generic's body is
// made for each instance: of those, the one made for the body being checked.)
tc_variant_enums :: proc(k: ^TC, name: string, span: Span, errors := false) -> [dynamic]string {
    owners := make([dynamic]string, context.temp_allocator)
    for ename, edef in k.table.enums {
        if errors && !edef.is_error_kind || name not_in edef.variants { continue }
        // (A union's tag's enum: one that isn't its definition's only.)
        if tc_sees_enum(k, edef, span) && !(edef.is_synthetic && tc_another_instances(k, edef.owner)) { append(&owners, ename) }
    }
    return owners
}

// Whether a scope is a generic's instance other than the one being checked
// (or one around it).
tc_another_instances :: proc(k: ^TC, owner: ^Type_Scope) -> bool {
    i, known := k.scope_of[owner]
    if !known || !k.scopes[i].synthetic { return false }
    for b := k.body; b != nil; b = b.parent_scope { if b == owner { return false } }
    return true
}

// The text a definition's variants are in sight in by themselves: its block's
// (an if's, a loop's), else its owner's body's — a module's has none: its
// files are its text.
tc_sight :: proc(k: ^TC, def: Tree_Id, owner: ^Type_Scope) -> (lo, hi: Token_Id, block: bool) {
    if bd, in_block := k.block_defs[def]; in_block { return bd.lo, bd.hi, true }
    return k.t.first[owner.node], k.t.end[owner.node], false
}

// Whether an enum is in sight where its variant is named by itself: in the
// text of the scope that defines it — a module's files, a body, a block —
// and where that scope is used (a block is no one's to use). By the text,
// whichever instance of a generic is being checked.
tc_sees_enum :: proc(k: ^TC, et: ^Type_Enum, span: Span) -> bool {
    sees :: proc(k: ^TC, home: string, owner: ^Type_Scope, lo, hi: Token_Id, block: bool, at: Token_Id) -> bool {
        if hi == 0 { return resolve_sees_module(k.rs, at, home) }   // (a module's: its files, and where it is used)
        return at >= lo && at < hi || !block && resolve_uses_scope(k.rs, at, owner.decl)
    }
    if sees(k, et.home_package, et.owner, et.sight_lo, et.sight_hi, et.sight_block, span.at) { return true }
    for a in et.aliased { if sees(k, a.home, a.owner, a.lo, a.hi, a.block, span.at) { return true } }
    return false
}

// `A :: alias E`, E an enum, an error set or a union: E's variants in sight
// where A is (tc_sees_enum), as they are where E is. Once A's base is known.
tc_alias_sight :: proc(k: ^TC, s: Tree_Id, owner: ^Type_Scope) {
    t := k.t
    if t.tag[s] != .Define || t.a[s] != 0 { return }
    value := Tree_Id(t.b[s])
    if value == 0 || t.tag[value] != .Alias_Def { return }
    bound, _ := tc_bound(k, t.main[s])
    dt, is_dt := bound.(^Type_Distinct)
    if !is_dt || dt.base_type == nil { return }
    et: ^Type_Enum
    #partial switch b in unwrap_alias(dt) {
    case ^Type_Enum:  et = b
    case ^Type_Union: et = b.tag_enum
    }
    if et == nil { return }
    lo, hi, block := tc_sight(k, s, owner)
    a := Enum_Alias{k.pkg, owner, lo, hi, block}
    if (et.home_package == a.home && et.sight_lo == lo && et.sight_hi == hi) || slice.contains(et.aliased[:], a) { return }
    append(&et.aliased, a)
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
tc_variant_ambiguous :: proc(k: ^TC, name: string, owners: []string, span: Span, bare := false) {
    names := make([dynamic]string, context.temp_allocator)
    for o in owners { append(&names, type_name(k.table.enums[o])) }
    slice.sort(names[:])
    tc_error(k, span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS, "" if bare else ".", name, strings.join(names[:], ", ", context.temp_allocator), names[0], name)
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
tc_variant_call :: proc(k: ^TC, n: Tree_Id, ut: ^Type_Union, name: string, args: []Tree_Id) -> Type {
    vst := ut.variant_structs[name]
    if vst == nil || len(vst.params) == 0 {
        tc_error(k, tree_span(k.t, n), TYPE_VARIANT_TAKES_NO_ARGS, name, name, "{…}", name)
        return Type_Error{}
    }
    qualified := strings.concatenate({ut.source_name, ".", name}, context.temp_allocator)   // (as its diagnostics name it)
    if _, failed := tc_call_core(k, n, qualified, args, qual = vst).(Type_Error); failed { return Type_Error{} }
    tc_set_ref(k, n, {variant_decl(ut, name), .Variant})
    return ut
}

// The union a literal named by a bare variant builds: the one expected,
// else the one union in sight with that variant (two such: ambiguous,
// reported).
tc_variant_union :: proc(k: ^TC, name: string, span: Span) -> (^Type_Union, bool) {
    if ut, is_union := distinct_base(k.hint).(^Type_Union); is_union && name in ut.tag_map { return ut, false }
    found: ^Type_Union
    owners := make([dynamic]string, context.temp_allocator)
    for _, ut in k.table.unions {
        if name not_in ut.tag_map || !tc_sees_enum(k, ut.tag_enum, span) || tc_another_instances(k, ut.tag_enum.owner) { continue }
        found = ut
        append(&owners, ut.source_name if ut.source_name != "" else ut.name)
    }
    if len(owners) > 1 {
        slice.sort(owners[:])
        tc_error(k, span, TYPE_AMBIGUOUS_VARIANT_LITERAL, name, strings.join(owners[:], ", ", context.temp_allocator), owners[0], name)
        return nil, true
    }
    return found, false
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
// bodies checked again as its own.
tc_union_instance :: proc(k: ^TC, n: Tree_Id, tmpl: TC_Template, span: Span) -> Type {
    t := k.t
    name := tc_name(k, n)
    tmpl := tmpl
    tmpl.owner = tc_template_owner(k, tmpl)
    h := tc_union_header(k, tmpl.node)
    targs := make([dynamic]Type, context.temp_allocator)
    for a in tree_list(t, t.a[n]) { append(&targs, tc_type(k, a, span)) }
    if len(targs) != len(h.params) {
        tc_error(k, span, TYPE_EXPECTS_TYPE_ARGUMENT, name, len(h.params), len(targs))
        return Type_Error{}
    }
    // (Cached by its owner's name too; made named for its owner, as a union
    // written out is — tc_make_union.)
    mangled := mangle_generic_name(name, targs[:])
    key := tc_instance_name(k, tmpl, name, targs[:])
    if ut, made := k.table.mono_union_cache[key]; made { return ut }
    subst := make(TC_Bindings)
    for p, i in h.params { subst[p] = targs[i] }
    saved_pkg := k.pkg
    k.pkg = tmpl.pkg
    defer k.pkg = saved_pkg
    outer := tc_type_params_bind(k, tc_owner_bindings(k, tmpl.owner))   // (as a fun's, tc_instantiate_fun)
    defer tc_type_params_restore(k, outer)
    // (Its variants' bodies are its template's, checked again with its params
    // bound: their nodes its own — tc_sid.)
    saved_inst := tc_instance_begin(k, tmpl, nil, subst)
    defer tc_instance_end(k, saved_inst)
    ut := tc_make_union(k, tmpl.pkg, mangled, tree_span(t, tmpl.def), h, tc_union_variants(k, tmpl.node)[:], subst, tmpl.owner)
    k.table.mono_union_cache[key] = ut
    tc_bound_set(k, ut.span.at, ut)   // (its template's name, in it: it)
    tc_union_resolve(k, ut, h.pad, span)
    return ut
}
