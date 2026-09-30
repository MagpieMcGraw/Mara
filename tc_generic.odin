package mara

// Generics in the new checker. A definition is a template when its signature
// names a type it is given (`$T`), a struct's param is a shape (`~T`), or a
// struct's param is used in its fields' types (`[n]T`): the old parser
// lowered these into generic params; the tree keeps them as written, and the
// checker reads them off it. A template is checked only as its instances.

TC_Template :: struct {
    def, node: Tree_Id,
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
        f := graph_fuse_begin(k.gb, pt, syntax_id(tmpl.def), span, v.intrinsic != 0, .Synthetic)
        b := k.gb
        for s in v.body {
            if t.tag[s] != .Decl {
                graph_fuse_fail(b, f, "the program's struct declares no field")
                break
            }
            ss := tree_span(t, s)
            graph_fuse_body_stmt(b, ss, true)
            saved := graph_fuse_stmt(b, syntax_id(s), ss, tc_stmt_kind(k, s), fresh = true)
            for target in decl_view(t, s).targets { graph_fuse_program_field(b, tc_name(k, target), ss) }
            graph_fuse_stmt_end(b, saved)
        }
        if k.c.errors > 0 { graph_fuse_fail(b, f, "errors") }
        graph_fuse_end(b, f)
        return
    }
}
