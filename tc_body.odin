package mara

// Bodies, checked and built statement by statement in the order they run
// (the graph is built as they are checked, through the builder): a fun's
// code; a struct's constructor, whose field declarations are its fields —
// each typed as its declaration finds, so its fields are known once its
// body is checked.

tc_scope_body :: proc(k: ^TC, sc: ^TC_Scope) {
    t := k.t
    ts := sc.ts
    v := scope_view(t, sc.node)
    span := tree_span(t, sc.def)
    is_struct := ts.kind == .Struct
    if is_struct { ts.sig_state = .In_Progress }
    hint := k.hint
    defer k.hint = hint
    f: ^Graph_Fuse
    if k.gb != nil { f = graph_fuse_begin(k.gb, ts, syntax_id(sc.def), span, v.intrinsic != 0, .Explicit) }
    if v.intrinsic == 0 {
        body := type_env_block_child(ts)
        for p in ts.params { type_env_set(body, p.name, p.type_) }
        tc_scope(k, v.body, body, ts if is_struct else nil)
    }
    if is_struct {
        // (A field's width its uses left open: settled, as a local's is.)
        for &fl in ts.fields { fl.type_ = solidify_type(fl.type_) }
        ts.sig_state = .Resolved
    }
    if f != nil {
        if k.c.errors > 0 { graph_fuse_fail(k.gb, f, "errors") }
        graph_fuse_end(k.gb, f)
    }
}

// A block's statements: each checked whole, and built, before the next.
// `fields_of`: the struct whose top block it is (its declarations are its
// fields).
tc_scope :: proc(k: ^TC, stmts: []Tree_Id, env: ^Type_Scope, fields_of: ^Type_Scope = nil) {
    t := k.t
    for s in stmts {
        if t.tag[s] == .Define {
            tc_unsupported(k, s, "a definition in a body")
            continue
        }
        b := tc_building(k)
        saved: i32
        if b != nil {
            span := tree_span(t, s)
            graph_fuse_body_stmt(b, span, true)
            saved = graph_fuse_stmt(b, syntax_id(s), span, tc_stmt_kind(k, s), fresh = true)
        }
        if t.tag[s] == .Decl && fields_of != nil {
            tc_decl(k, s, env, fields_of)
        } else {
            tc_stmt(k, s, env)
        }
        if b != nil { graph_fuse_stmt_end(b, saved) }
    }
}

tc_stmt :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        rt, _ := tc_expr(k, e, env, .Value)
        // A call's value, dropped: `_ = f()` says so.
        if t.tag[e] == .Call && rt != nil {
            _, is_void := rt.(Type_Void)
            _, is_error := rt.(Type_Error)
            if !is_void && !is_error { tc_error(k, span, TYPE_DISCARDED_RETURN, tc_name(k, e)) }
        }
    case .Decl:
        tc_decl(k, s, env)
    case .Assign:
        tc_assign(k, s, env)
    case .Return:
        tc_return(k, s, env)
    case .If, .Elif:
        tc_if(k, s, env)
    case:
        tc_unsupported(k, s, "this statement")
    }
}


// `x := v`, `x : T = v`, `x : T`: its local, then its value built into it
// (or its zero), then stored — once the statement is checked (its type known).
// In a struct's top block (`fields_of`), a field: typed as its annotation,
// else as its value.
tc_decl :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, fields_of: ^Type_Scope = nil) {
    t := k.t
    span := tree_span(t, s)
    v := decl_view(t, s)
    switch {
    case len(v.targets) != 1:
        tc_unsupported(k, s, "a destructure")
        return
    case len(v.values) > 1 || t.tag[v.targets[0]] != .Ident:
        tc_unsupported(k, s, "this declaration")
        return
    }
    target := v.targets[0]
    name := tc_name(k, target)
    ann: Type = Type_Any{}
    if v.type_ != 0 { ann = tc_type(k, v.type_, env, span) }
    if !tc_declarable(k, env, name, span) { return }
    value := v.values[0] if len(v.values) > 0 else 0
    if value != 0 && t.tag[value] == .Ident && tc_name(k, value) == "void" {
        tc_unsupported(k, s, "a `void` declaration")
        return
    }
    if fields_of != nil && !is_any(ann) { tc_add_field(fields_of, name, ann, value) }
    if len(v.values) == 0 {
        tc_decl_bare(k, name, ann, env, span, tc_field_decl(k, fields_of, name, target, 0, span))
        return
    }
    b := tc_building(k)
    decl := NO_NODE
    prefix: [2]Node_Id
    prefixed := false
    if b != nil {
        decl = tc_field_decl(k, fields_of, name, target, value, span)
        if decl == NO_NODE { decl = graph_fuse_decl(b, name, span) }
        // Text fills only a prefix of a new partial array: it is zero first
        // — kept once the value's type says so.
        #partial switch t.tag[value] {
        case .String, .Ident, .Field:
            if is_untyped(ann) { prefix, prefixed = graph_fuse_prefix(b, name, decl, span), true }
        }
        if !prefixed && is_partial_array(ann) { prefix, prefixed = graph_fuse_prefix(b, name, decl, span), true }
    }
    k.hint = ann
    errors_before := k.c.errors
    want := Fuse_Want.Into if b != nil else .None
    vt, r := tc_expr(k, value, env, want, dest = graph_dest_var(name, decl, nil if is_untyped(ann) else ann), temp_span = span)
    final: Type
    if !is_any(ann) {
        if !coerce_deferred(k.c, vt, ann, span) && types_incompatible(ann, vt) && !value_preserving_widen(vt, ann) {
            tc_assign_error(k, span, vt, name, ann, value)
        }
        if is_infer(vt) { tc_literal_overflow(k, value, ann, span) }
        final = ann
    } else if existing, shadowed := tc_declared_before(env, name, fields_of != nil); shadowed {
        // (Reported as a shadow: checked as the write it reads as.)
        tc_check_write(k, value, vt, existing, name, span)
        return
    } else if is_infer(vt) {
        // Its width is the one its first concrete use decides.
        cell := new(Infer_Cell)
        cell.name, cell.span = name, span
        if src := infer_cell_of(vt); src != nil { unify_infer_cells(k.c, cell, src, span) }
        if _, is_float := vt.(Type_Infer_Float); is_float {
            final = Type_Infer_Float{cell = cell}
        } else {
            final = Type_Infer_Int{cell = cell}
        }
    } else {
        final = solidify_type(vt)
        if is_untyped(final) && k.c.errors == errors_before {
            check_warning(k.c, span, TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING, name)
        }
        if is_cstring(final) { tc_error(k, span, TYPE_CSTRING_FOREIGN_ONLY) }
    }
    type_env_set(env, name, final)
    if fields_of != nil && is_any(ann) { tc_add_field(fields_of, name, final, value) }
    if b = tc_building(k); b == nil { return }
    graph_fuse_typed(b, decl, final)
    wrote := tc_store(k, value, vt, r, graph_dest_var(name, decl, final), span, settle = true)
    if prefixed {
        fills := is_partial_array(final) && (t.tag[value] == .String || is_slice_type(vt))
        graph_fuse_prefix_end(b, prefix, wrote && fills, final)
    }
}

// Whether a name can be declared here: not in this scope already, and no
// constant's. (Shadowing an enclosing local is reported, and declares.)
tc_declarable :: proc(k: ^TC, env: ^Type_Scope, name: string, span: Span) -> bool {
    _, here := scope_defines(env, name)
    if here {
        tc_error(k, span, TYPE_VARIABLE_ALREADY_DECLARED_SCOPE, name)
        return false
    }
    if !env_is_module(env) && parent_struct_scope(env) == nil {
        // Past a function's boundary a block's locals are out of sight.
        crossed := false
        for sc := env.parent_scope; sc != nil && !sc.is_module; sc = sc.parent_scope {
            if sc.kind != .Block { crossed = true }
            st, found := scope_defines(sc, name)
            if found && !(crossed && sc.kind == .Block && !names_module(st)) {
                tc_error(k, span, TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING, name)
                break
            }
        }
    }
    if name in k.table.constants {
        tc_error(k, span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, name)
        return false
    }
    return true
}

// `x : T`: its zero, or its construction (a struct's, an array of them's
// each). `field`: its node, when it is a struct's field.
tc_decl_bare :: proc(k: ^TC, name: string, ann: Type, env: ^Type_Scope, span: Span, field := NO_NODE) {
    defer type_env_set(env, name, ann)
    if _, is_error := ann.(Type_Error); is_error { return }
    if is_any(ann) { tc_error(k, span, TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE) }
    b := tc_building(k)
    if b == nil { return }
    args: []Operand
    if st := tc_bare_struct(ann); st != nil {
        tc_struct_ensure(k, st)
        if len(st.params) > 0 {
            tc_fail(k, "a declaration constructed with args")
            return
        }
        if constructs_bare(st) { args = make([]Operand, 0, context.temp_allocator) }
    }
    if b = tc_building(k); b == nil { return }
    decl := field
    if decl == NO_NODE {
        decl = graph_fuse_decl(b, name, span)
        graph_fuse_typed(b, decl, ann)
    }
    graph_fuse_bare(b, decl, ann, nil, args, span)
}

// The struct a bare declaration of the type constructs: its own, or its
// elements'.
tc_bare_struct :: proc(t: Type) -> ^Type_Scope {
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        if v.kind == .Struct && !v.is_module { return v }
    case ^Type_Fixed_Array, ^Type_Partial_Array:
        return graph_elem_struct(t)
    }
    return nil
}

// A struct's field, as its declaration finds it.
tc_add_field :: proc(ts: ^Type_Scope, name: string, t: Type, value: Tree_Id) {
    append(&ts.fields, Struct_Type_Field{name = name, type_ = t, default_node = value})
    build_field_map(&ts.sd)
}

// A field's node, made with its declaration (else none: a local's is made
// by its caller).
tc_field_decl :: proc(k: ^TC, fields_of: ^Type_Scope, name: string, target, value: Tree_Id, span: Span) -> Node_Id {
    b := tc_building(k)
    if fields_of == nil || b == nil { return NO_NODE }
    key := syntax_id(target)
    inits := []Span{tree_span(k.t, value)} if value != 0 else nil
    graph_fuse_fields(b, {name}, span, {key}, inits, false)
    return b.fuse.fields[key]
}

// A name already declared where a declaration would declare it: below the
// module (in a struct's top block, in it).
tc_declared_before :: proc(env: ^Type_Scope, name: string, in_struct: bool) -> (Type, bool) {
    if in_struct {
        t, ok := env.types[name]
        return t, ok
    }
    t, _, ok := type_env_locate_below_module(env, name)
    return t, ok
}

// A value written to a variable of type `existing`: checked against it.
tc_check_write :: proc(k: ^TC, value: Tree_Id, vt, existing: Type, name: string, span: Span) {
    if !coerce_deferred(k.c, vt, existing, span) && !coerce_deferred(k.c, existing, vt, span) &&
       types_incompatible(existing, vt) && !value_preserving_widen(vt, existing) {
        tc_assign_error(k, span, vt, name, existing, value)
    }
    if is_infer(vt) { tc_literal_overflow(k, value, existing, span) }
}

is_slice_type :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Slice)
    return ok
}

// A built value stored where it goes: at the destination's type (a number
// widened to it).
tc_store :: proc(k: ^TC, e: Tree_Id, t: Type, r: Fused, d: Dest, span: Span, settle := false) -> bool {
    b := tc_building(k)
    if b == nil || r.into { return false }
    if r.temp {
        graph_fuse_write_at(b, graph_dest_place(b, d, span), r.v, span)
        return true
    }
    if tc_builds_into(k, e) {
        tc_fail(k, "a value built in place, taken as one")
        return false
    }
    dt := graph_dest_type(b, d)
    _, to_ptr := distinct_base(dt).(^Type_Ptr)
    _, from_ptr := distinct_base(t).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(dt) && graph_partial_of(t) {
        // A partial array seen as a slice's header.
        v := graph_op_value(b, .Cast, .Implied, span, dt, type_name(dt), tc_value(k, r, e, t))
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)
        return false
    }
    _, to_slice := distinct_base(dt).(^Type_Slice)
    _, from_array := distinct_base(t).(^Type_Fixed_Array)
    if to_slice && from_array {
        if !r.place {
            tc_fail(k, "a slice of an array value")
            return false
        }
        v := graph_op_value(b, .Slice, .Implied, span, dt, "", r.v)
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)
        return false
    }
    if tag := k.t.tag[tc_unparen(k, e)]; tag == .Slice || tag == .Index {
        tc_unsupported(k, e, "a store of an element or a span")
        return false
    }
    val := graph_fuse_widen(b, tc_value(k, r, e, t), span, {to = dt, settle_to = settle})
    graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
    return true
}

// `x = v`: the value, then the write, at the variable's type.
tc_assign :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) == 1 && len(values) == 1 && t.tag[targets[0]] == .Field {
        tc_field_assign(k, s, targets[0], values[0], env)
        return
    }
    if len(targets) != 1 || len(values) != 1 || t.tag[targets[0]] != .Ident {
        if len(targets) == 1 { tc_unsupported(k, targets[0], "this assignment target"); return }
        tc_unsupported(k, s, "this assignment")
        return
    }
    name := tc_name(k, targets[0])
    value := values[0]
    if name == "_" {
        // A discard: the value checked (and built) for its own sake.
        k.hint = nil
        tc_expr(k, value, env, .Value if tc_building(k) != nil else .None)
        return
    }
    if name == "this_program" {
        tc_unsupported(k, s, "an assignment to this_program")
        return
    }
    existing, loc, found := type_env_locate(env, name)
    if !found && name not_in k.table.constants {
        report_unresolved(k.c, span, env, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
        type_env_set(env, name, Type_Error{})
        return
    }
    if is_immutable_param(env, name) { tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name) }
    if loc != nil && loc.kind == .Struct {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    b := tc_building(k)
    want := Fuse_Want.Into if b != nil else .None
    vt: Type = distinct_base(existing) if !is_untyped(existing) else nil
    val_type, r := tc_expr(k, value, env, want, dest = graph_dest_var(name, NO_NODE, vt), temp = true, temp_span = span)
    tc_check_write(k, value, val_type, existing, name, span)
    tc_store(k, value, val_type, r, graph_dest_var(name, NO_NODE, existing), span)
}

// `return a, b`: each value at its result's type (trailing errs implied `.Ok`).
tc_return :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    values := tree_list(t, t.a[s])
    rts := enclosing_return_types(env)
    expected, supplied := len(rts), len(values)
    trailing_errs := 0
    for i := expected - 1; i >= 0 && is_err_type(rts[i]); i -= 1 { trailing_errs += 1 }
    least := expected - trailing_errs
    count_ok := true
    switch {
    case expected == 0 && supplied > 0, expected == 1 && supplied > 1:
        tc_error(k, span, TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN)
        count_ok = false
    case expected == 1 && supplied == 0 && least > 0, expected > 1 && (supplied > expected || supplied < least):
        tc_error(k, span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED, supplied, expected)
        count_ok = false
    }
    vals := make([dynamic]Operand, 0, supplied, context.temp_allocator)
    if count_ok {
        for val, i in values {
            want := rts[i]
            if is_partial_array(want) || is_slice_type(want) {
                tc_unsupported(k, s, "a return of this type")
                return
            }
            k.hint = want
            vt, r := tc_expr(k, val, env, .Either if tc_building(k) != nil else .None, temp_span = span)
            if b := tc_building(k); b != nil {
                append(&vals, graph_fuse_widen(b, tc_value(k, r, val, vt), span, {to = want}))
            }
            if !is_any(vt) && !is_any(want) && !coerce_deferred(k.c, vt, want, span) &&
               !types_equal(want, vt) && !value_preserving_widen(vt, want) {
                if expected > 1 {
                    tc_error(k, span, TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED, i + 1, type_name(vt), type_name(want))
                } else {
                    tc_error(k, span, TYPE_RETURN_TYPE_MATCH_EXPECTED, type_name(vt), type_name(want))
                }
            }
            if is_infer(vt) { tc_literal_overflow(k, val, want, span) }
        }
    }
    if b := tc_building(k); b != nil { graph_fuse_return(b, vals[:], span) }
}

// `if c {…} elif d {…} else {…}`: the branch, then each block as it is
// checked (an elif, the else block's one statement).
tc_if :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := if_view(t, s)
    if v.hash != 0 {
        tc_unsupported(k, s, "`#if`")
        return
    }
    ct, cond := tc_expr(k, v.cond, env, .Value if tc_building(k) != nil else .None)
    if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL_2, type_name(ct)) }
    b := tc_building(k)
    fi: Graph_If
    if b != nil { fi = graph_fuse_if(b, cond.v, span, len(v.else_) > 0) }
    tc_scope(k, v.then, type_env_block_child(env))
    if b != nil { graph_fuse_else(b, &fi, span) }
    if len(v.else_) > 0 { tc_scope(k, v.else_, type_env_block_child(env)) }
    if b != nil { graph_fuse_if_end(b, &fi) }
}

// What builds where it goes (a literal, an array, a construction): never
// taken as a value.
tc_builds_into :: proc(k: ^TC, e: Tree_Id) -> bool {
    n := tc_unparen(k, e)
    #partial switch k.t.tag[n] {
    case .Literal, .Array: return true
    case .Call:
        return n in k.constructs
    }
    return false
}
