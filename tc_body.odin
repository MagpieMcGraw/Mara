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
    tc_register_defs(k, sc)
    body := type_env_block_child(ts)
    // (A struct's params its constants may use; its and a fun's constants
    // checked, and built, before its code.)
    if is_struct { for p in ts.params { type_env_set(body, p.name, p.type_) } }
    tc_check_local_consts(k, sc, body)
    f: ^Graph_Fuse
    if k.gb != nil { f = graph_fuse_begin(k.gb, ts, tc_sid(k, sc.def), span, v.intrinsic != 0, .Synthetic if sc.synthetic else .Explicit) }
    // (A fun's definitions are checked before its code; a struct's once its
    // fields are known: its methods read them.)
    if !is_struct { tc_check_defs(k, sc) }
    if v.intrinsic == 0 {
        if !is_struct { for p in ts.params { type_env_set(body, p.name, p.type_) } }
        for name, bt in sc.subst { type_env_set(body, name, bt) }
        tc_scope(k, v.body, body, ts if is_struct else nil, top = true)
    }
    if is_struct {
        // (A field's width its uses left open: settled, as a local's is.)
        for &fl in ts.fields { fl.type_ = solidify_type(fl.type_) }
        ts.sig_state = .Resolved
    }
    // (A default param's width the body left open: settled.)
    solidify_param_defaults(k.c, ts)
    if f != nil {
        if k.c.errors > 0 { graph_fuse_fail(k.gb, f, "errors") }
        graph_fuse_end(k.gb, f)
    }
    if is_struct { tc_check_defs(k, sc) }
}

// A block's statements: each checked whole, and built, before the next.
// `fields_of`: the struct whose top block it is (its declarations are its
// fields).
tc_scope :: proc(k: ^TC, stmts: []Tree_Id, env: ^Type_Scope, fields_of: ^Type_Scope = nil, top := false) {
    t := k.t
    stmts := tc_live(k, stmts)   // (`#if`: its live arm's, in its place)
    // (Its declarations, for the stack's size guard at its end.)
    saved := k.decls
    decls := make([dynamic]TC_Decl_Note, context.temp_allocator)
    k.decls = &decls
    defer {
        tc_storage_sizes(k, decls[:])
        k.decls = saved
    }
    // (A body's constants, checked with it: their declarations, settled.)
    if b := tc_building(k); b != nil && top {
        for s in stmts {
            if t.tag[s] == .Define && t.b[s] != 0 && !tc_is_definition(t.tag[t.b[s]]) { graph_fuse_def_settled(b, tc_graph_decl(k, s)) }
        }
    }
    for s in stmts {
        if t.tag[s] == .Define {
            // (A body's definitions are registered and checked with it: built
            // by the builder from where each is written.)
            if !top { tc_unsupported(k, s, "a definition in a block") }
            if b := tc_building(k); b != nil && top { graph_fuse_def(b, tc_graph_decl(k, s)) }
            continue
        }
        b := tc_building(k)
        saved: i32
        if b != nil {
            span := tree_span(t, s)
            graph_fuse_body_stmt(b, span, true)
            saved = graph_fuse_stmt(b, tc_sid(k, s), span, tc_stmt_kind(k, s), fresh = true)
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
        if tc_override(k, e, env) { return }
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
    case .For_Range, .For_Each, .For_C, .For_Cond:
        tc_for(k, s, env)
    case .Compound:
        tc_compound(k, s, env)
    case .Defer:
        tc_defer(k, s, env)
    case .Break, .Continue:
        if b := tc_building(k); b != nil { graph_fuse_loop_exit(b, span, is_break = t.tag[s] == .Break) }
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
    for tg in v.targets {
        if t.tag[tg] != .Ident {
            tc_unsupported(k, s, "a declaration of no name")
            return
        }
    }
    if len(v.targets) > 1 && len(v.values) == 1 {
        if fields_of != nil {
            tc_unsupported(k, s, "a struct's fields from one call")
            return
        }
        tc_destructure(k, s, v.targets, v.values[0], true, v.type_, env)
        return
    }
    if len(v.values) > 0 && len(v.values) != len(v.targets) {
        tc_unsupported(k, s, "this declaration")
        return
    }
    // (Several names, each its own declaration — a struct's fields made
    // first, together.)
    if len(v.targets) > 1 && fields_of != nil {
        if v.type_ != 0 {
            // (Annotated: its fields typed as they are made.)
            ft := tc_type(k, v.type_, env, span)
            for tg, i in v.targets { tc_add_field(fields_of, tc_name(k, tg), ft, v.values[i] if i < len(v.values) else 0) }
        }
        if b := tc_building(k); b != nil {
            names := make([]string, len(v.targets), context.temp_allocator)
            ids := make([]Syntax_Id, len(v.targets), context.temp_allocator)
            inits := make([]Span, len(v.values), context.temp_allocator)
            for tg, i in v.targets { names[i], ids[i] = tc_name(k, tg), tc_sid(k, tg) }
            for val, i in v.values { inits[i] = tree_span(t, val) }
            graph_fuse_fields(b, names, span, ids, inits, false)
        }
    }
    for tg, i in v.targets {
        tc_decl_one(k, s, tg, v.values[i] if i < len(v.values) else 0, v.type_, env, fields_of)
    }
}

// One name's declaration.
tc_decl_one :: proc(k: ^TC, s, target, value, ann_node: Tree_Id, env: ^Type_Scope, fields_of: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    name := tc_name(k, target)
    ann: Type = Type_Any{}
    if ann_node != 0 { ann = tc_type(k, ann_node, env, span) }
    if !tc_declarable(k, env, name, span) { return }
    // (`x : T = void`, T no pointer: uninitialized — a pointer's void is its
    // null, a value.)
    skip := value != 0 && tc_is_void(k, value) && !tc_is_pointer(ann)
    if skip {
        tc_decl_void(k, s, target, value, name, ann, env, fields_of)
        return
    }
    if fields_of != nil && !is_any(ann) { tc_add_field(fields_of, name, ann, value) }
    if value == 0 {
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
    tc_no_literal_slice(k, vt if is_untyped(ann) else ann, value, span)
    tc_check_big_endian(k, value, span)
    if returns := tc_call_returns(k, value, env); len(returns) > 1 {
        // (One name for several results: `a, b := f()` takes them.)
        tc_error(k, span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE, 1, len(returns))
        type_env_set(env, name, Type_Error{})
        return
    }
    final: Type
    if !is_any(ann) {
        // (Bytes read as the annotation's type: no conversion to check.)
        flow := tc_check_byte_flow(k, ann, value, vt, span)
        fa, to_array := distinct_base(ann).(^Type_Fixed_Array)
        if to_array && !tc_is_distinct(ann) && flow == .None {
            // (A fixed array: its elements', and room for them.)
            tc_array_assign(k, span, name, fa, vt, value)
        } else if flow == .None && !coerce_deferred(k.c, vt, ann, span) && types_incompatible(ann, vt) && !value_preserving_widen(vt, ann) {
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
    tc_note_decl(k, name, final, span, k.t.tag[tc_unparen(k, value)] == .Take)
    if fields_of != nil && is_any(ann) { tc_add_field(fields_of, name, final, value) }
    if b = tc_building(k); b == nil { return }
    graph_fuse_typed(b, decl, final)
    wrote, zeroed := tc_store(k, value, vt, r, graph_dest_var(name, decl, final), span, settle = true)
    if prefixed {
        fills := is_partial_array(final) && (t.tag[value] == .String || is_slice_type(vt))
        graph_fuse_prefix_end(b, prefix, zeroed || wrote && fills, final)
    }
    if zeroed && !prefixed { tc_fail(k, "a new partial array read from bytes") }
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
    tc_note_decl(k, name, ann, span, false)
    if _, is_error := ann.(Type_Error); is_error { return }
    if is_any(ann) { tc_error(k, span, TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE) }
    b := tc_building(k)
    if b == nil { return }
    args: []Operand
    if st := tc_bare_struct(ann); st != nil {
        tc_struct_ensure(k, st)
        if constructs_bare(st) { args = tc_ctor_args(k, st, span) }
    }
    if b = tc_building(k); b == nil { return }
    decl := field
    if decl == NO_NODE {
        decl = graph_fuse_decl(b, name, span)
        graph_fuse_typed(b, decl, ann)
    } else if b.g.type_[decl] == nil {
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
    if name in ts.field_map { return }   // (added with the others declared with it)
    append(&ts.fields, Struct_Type_Field{name = name, type_ = t, default_node = value})
    build_field_map(&ts.sd)
}

// A field's node, made with its declaration (else none: a local's is made
// by its caller).
tc_field_decl :: proc(k: ^TC, fields_of: ^Type_Scope, name: string, target, value: Tree_Id, span: Span) -> Node_Id {
    b := tc_building(k)
    if fields_of == nil || b == nil { return NO_NODE }
    key := tc_sid(k, target)
    if d, made := b.fuse.fields[key]; made { return d }   // (made with the others declared with it)
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
    tc_no_literal_slice(k, existing, value, span)
    if tc_check_byte_flow(k, existing, value, vt, span) != .None { return }
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
tc_store :: proc(k: ^TC, e: Tree_Id, t: Type, r: Fused, d: Dest, span: Span, settle := false) -> (wrote, zeroed: bool) {
    b := tc_building(k)
    if b == nil || r.into { return }
    if r.temp {
        graph_fuse_write_at(b, graph_dest_place(b, d, span), r.v, span)
        return true, false
    }
    if tc_builds_into(k, e) {
        tc_fail(k, "a value built in place, taken as one")
        return
    }
    dt := graph_dest_type(b, d)
    _, to_ptr := distinct_base(dt).(^Type_Ptr)
    _, from_ptr := distinct_base(t).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(dt) && graph_partial_of(t) {
        // A partial array seen as a slice's header.
        v := graph_op_value(b, .Cast, .Implied, span, dt, type_name(dt), tc_value(k, r, e, t))
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)
        return
    }
    _, to_slice := distinct_base(dt).(^Type_Slice)
    _, from_array := distinct_base(t).(^Type_Fixed_Array)
    if to_slice && from_array {
        if !r.place {
            tc_fail(k, "a slice of an array value")
            return
        }
        v := graph_op_value(b, .Slice, .Implied, span, dt, "", r.v)
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)
        return
    }
    // (Bytes read as the destination's type: tc_store_bytes.)
    if m, _ := tc_byte_node(k, e); d.type_ != nil && tc_byte_flow(k, d.type_, e, t) == .Read {
        if k.t.tag[m] == .Index { return tc_store_bytes(k, e, r, d, dt, span) }
        tc_unsupported(k, e, "a span of bytes read as a type")
        return
    }
    val := graph_fuse_widen(b, tc_value(k, r, e, t), span, {to = dt, settle_to = settle})
    graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
    return true, false
}

// `x = v`: the value, then the write, at the variable's type.
tc_assign :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) > 1 && len(values) == 1 {
        tc_destructure(k, s, targets, values[0], false, 0, env)
        return
    }
    if len(targets) == 1 && len(values) == 1 {
        target := targets[0]
        #partial switch t.tag[target] {
        case .Field: tc_field_assign(k, s, target, values[0], env)
        case .Index: tc_index_assign(k, s, target, values[0], env)
        case .Slice: tc_slice_assign(k, s, target, values[0], env)
        case .Deref: tc_deref_assign(k, s, target, values[0], env)
        }
        #partial switch t.tag[target] {
        case .Field, .Index, .Slice, .Deref:
            // (Into a constant: its storage is read-only.)
            if cname, is_const := tc_write_root_const(k, target); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
            return
        }
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
    if tc_is_void(k, value) {
        // (`x = void` de-initializes: the void value written, unchecked.)
        tc_check(k, value, env)
        if b := tc_building(k); b != nil { graph_fuse_void_assign(b, name, distinct_base(existing), span, tree_span(t, value)) }
        return
    }
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
            k.hint = want
            // (Text returned as a partial array: built into a temporary, zero
            // first, then read.)
            text, slot := false, NO_NODE
            if b := tc_building(k); b != nil && is_partial_array(want) {
                if t.tag[tc_unparen(k, val)] == .String {
                    text, slot = true, graph_slot(b, "temp", want, span)
                    graph_fuse_zero_var(b, slot, want, span)
                } else {
                    _ = graph_fuse_later(b)   // (where a text constant's would go)
                }
            }
            use, at := tc_use_type(k, val, want, span)
            held: Graph_Later
            if b := tc_building(k); b != nil && is_slice_type(want) { held = graph_fuse_later(b) }
            vt, r := tc_expr(k, val, env, .Either if tc_building(k) != nil else .None, dest = use, temp_span = at)
            if b := tc_building(k); b != nil && !text {
                append(&vals, tc_value_as(k, val, vt, r, want, span, {to = want}, &held))
            } else if b != nil {
                tc_store(k, val, vt, r, graph_dest_var("temp", slot, want), span)
                append(&vals, graph_read(b, graph_var(b, "temp", slot, want, span), want, span))
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
        callee := k.callees[n] or_else nil
        return callee != nil && callee.kind == .Struct
    }
    return false
}

// --- loops ------------------------------------------------------------------

// `for i in lo..hi`, `for e, i in c`, `for init; cond; step`, `for cond`: built
// around its checks (graph_for) — its block, its variables, then its runs.
tc_for :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := for_view(t, s)
    tag := t.tag[s]
    child := type_env_block_child(env)
    b := tc_building(k)
    fl: Graph_For
    if b != nil {
        fl = graph_fuse_for(b, {span = span, var_name = tc_text(v.var) if v.var != 0 else "",
                                elem_name = tc_text(v.elem) if v.elem != 0 else "",
                                index_name = tc_text(v.index) if v.index != 0 else "",
                                is_range = tag == .For_Range, has_cond = v.cond != 0, has_step = v.post != 0,
                                end_literal = v.hi != 0 && t.tag[tc_unparen(k, v.hi)] == .Number})
    }
    defer if b != nil { graph_fuse_for_end(b, &fl) }
    #partial switch tag {
    case .For_Each:
        // (A plain place: walked where the loop needs it. Anything else is
        // held first, in a local the loop walks.)
        ct: Type
        coll := NO_VALUE
        if b != nil && !tc_pure_place(k, v.collection) {
            ct = tc_loop_items(k, &fl, v.collection, child)
        } else if b != nil {
            r: Fused
            ct, r = tc_expr(k, v.collection, child, .Place)
            coll = r.v
        } else {
            ct = tc_check(k, v.collection, child)
        }
        elem: Type = Type_Error{}
        #partial switch c in ct {
        case ^Type_Fixed_Array:   elem = c.elem
        case ^Type_Slice:         elem = c.elem
        case ^Type_Partial_Array: elem = c.elem
        case ^Type_Scope:         tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE, c.name)
        case:                     tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_TYPE, type_name(ct))
        }
        if v.type_ != 0 { elem = tc_type(k, v.type_, env, span) }
        if v.elem != 0 { type_env_set(child, tc_text(v.elem), elem) }
        if v.index != 0 { type_env_set(child, tc_text(v.index), slice_header_width_type) }
        if b := tc_building(k); b != nil {
            graph_fuse_for_collection(b, &fl, coll, ct, false, distinct_base(elem))
        }
        tc_scope(k, v.body, child)
    case .For_Range:
        // The counter first, then each bound at its type (known once both
        // are checked).
        bounds := [2]int{-1, -1}
        if b != nil { graph_fuse_range_counter(b, &fl) }
        lt, lo := tc_expr(k, v.lo, child, .Value if b != nil else .None)
        if b := tc_building(k); b != nil {
            bounds[0] = len(b.fuse.checks)
            fl.lo = graph_fuse_range_bound(b, lo.v, lt, span)
        }
        ht, hi := tc_expr(k, v.hi, child, .Value if b != nil else .None)
        if b := tc_building(k); b != nil {
            fl.high = hi.v
            bounds[1] = len(b.fuse.checks)
            fl.hi = graph_fuse_range_bound(b, hi.v, ht, span)
        }
        it: Type
        if v.type_ != 0 {
            it = tc_type(k, v.type_, env, span)
        } else {
            // (Bounds that disagree count at the header's width.)
            it = try_promote_numeric(lt, ht)
            if _, is_error := it.(Type_Error); is_error || is_infer(it) { it = slice_header_width_type }
        }
        if !is_numeric(lt) && !is_infer(lt) && !is_any(lt) { tc_error(k, span, TYPE_RANGE_LOWER_BOUND_NUMERIC, type_name(lt)) }
        if !is_numeric(ht) && !is_infer(ht) && !is_any(ht) { tc_error(k, span, TYPE_RANGE_UPPER_BOUND_NUMERIC, type_name(ht)) }
        // (`..` counts up: known bounds that count down are an error.)
        lc, lc_ok := tc_comptime_int(k, v.lo, child)
        hc, hc_ok := tc_comptime_int(k, v.hi, child)
        if lc_ok && hc_ok && lc > hc { tc_error(k, span, TYPE_DESCENDING_RANGE, lc, hc, lc, hc) }
        type_env_set(child, tc_text(v.var), it)
        if b := tc_building(k); b != nil { graph_fuse_range(b, &fl, bounds, distinct_base(it)) }
        tc_scope(k, v.body, child)
    case:
        if v.init != 0 { tc_stmt_entry(k, v.init, child) }
        if b := tc_building(k); b != nil { graph_fuse_for_runs(b, &fl) }
        ct, cond := tc_expr(k, v.cond, child, .Value if tc_building(k) != nil else .None)
        if b := tc_building(k); b != nil { graph_fuse_for_cond(b, &fl, cond.v) }
        if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL, type_name(ct)) }
        if v.post != 0 {
            // (Built into the step's run, put after the body, where it runs.)
            step: Graph_Step
            if b := tc_building(k); b != nil { step = graph_fuse_step(b, &fl) }
            tc_stmt_entry(k, v.post, child)
            if b := tc_building(k); b != nil { graph_fuse_step_end(b, &fl, step) }
        }
        tc_scope(k, v.body, child)
    }
}

// A statement checked where it is its own entry in the graph's statements (a
// loop's init, its step).
tc_stmt_entry :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    b := tc_building(k)
    saved: i32
    if b != nil { saved = graph_fuse_stmt(b, tc_sid(k, s), tree_span(k.t, s), tc_stmt_kind(k, s)) }
    tc_stmt(k, s, env)
    if b != nil { graph_fuse_stmt_end(b, saved) }
}

// A loop's collection that is no plain place: held in the loop's own local
// (a literal built there, its elements settled), or viewed.
tc_loop_items :: proc(k: ^TC, fl: ^Graph_For, e: Tree_Id, env: ^Type_Scope) -> Type {
    b := tc_building(k)
    gi := graph_fuse_items(b, fl)
    #partial switch k.t.tag[tc_unparen(k, e)] {
    case .Array, .Literal:
        from := b.nodes
        t := solidify_type(tc_store_into(k, e, env, graph_dest_var("items", fl.coll_slot, nil), fl.span))
        if b := tc_building(k); b != nil {
            if graph_loop_view_of(t) != nil { tc_fail(k, "a literal loop over its view") }
            graph_fuse_retype_literal(b, from, b.nodes, t)
            graph_fuse_typed(b, fl.coll_slot, t)
        }
        return t
    }
    t, r := tc_expr(k, e, env, .Either)
    if b := tc_building(k); b != nil {
        if view := graph_loop_view_of(t); view != nil {
            fills := is_partial_array(t) && (k.t.tag[tc_unparen(k, e)] == .String || is_slice_type(t))
            graph_fuse_items_view(b, fl, &gi, r.v, r.place, t, view, false, fills)
        } else {
            graph_fuse_typed(b, fl.coll_slot, t)
            tc_store(k, e, t, r, graph_dest_var("items", fl.coll_slot, t), fl.span)
        }
    }
    return t
}

// An expression that names a place without running anything: walking it
// again gives the same place.
tc_pure_place :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := k.t
    #partial switch t.tag[n] {
    case .Paren: return tc_pure_place(k, Tree_Id(t.a[n]))
    case .Ident: return true
    case .Field, .Deref: return tc_pure_place(k, Tree_Id(t.a[n]))
    case .Index:
        #partial switch t.tag[tc_unparen(k, Tree_Id(t.b[n]))] {
        case .Number, .Ident: return tc_pure_place(k, Tree_Id(t.a[n]))
        }
    }
    return false
}

// `defer {…}`: its body, built as its own code (run at the scope's exits).
tc_defer :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    span := tree_span(k.t, s)
    b := tc_building(k)
    gd: Graph_Defer
    if b != nil { gd = graph_fuse_defer(b, span) }
    tc_scope(k, tree_list(k.t, k.t.a[s]), type_env_block_child(env))
    if b != nil { graph_fuse_defer_end(b, gd) }
}

// `x op= v`: `x = x op v`, the operation at the `op=`; a field's or an
// element's place built once, the operation reading through it.
tc_compound :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    target := Tree_Id(t.a[s])
    r := tree_rec(t, t.b[s], 2)
    op_tok, value := Token_Id(r[0]), Tree_Id(r[1])
    #partial switch t.tag[target] {
    case .Field, .Index, .Deref:
        #partial switch t.tag[target] {
        case .Field: tc_field_assign(k, s, target, value, env, op_tok)
        case .Index: tc_index_assign(k, s, target, value, env, op_tok)
        case .Deref: tc_deref_assign(k, s, target, value, env, op_tok)
        }
        if cname, is_const := tc_write_root_const(k, target); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
        return
    case .Ident:
    case:
        tc_unsupported(k, target, "this compound assignment's target")
        return
    }
    name := tc_name(k, target)
    existing, loc, found := type_env_locate(env, name)
    if !found && name not_in k.table.constants {
        report_unresolved(k.c, span, env, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
        type_env_set(env, name, Type_Error{})
        return
    }
    if loc != nil && loc.kind == .Struct {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    if is_immutable_param(env, name) { tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name) }
    k.hint = existing if !is_untyped(existing) else nil
    vt, fr := tc_compound_value(k, op_tok, target, value, env, .Into if tc_building(k) != nil else .None)
    if !coerce_deferred(k.c, vt, existing, span) && !coerce_deferred(k.c, existing, vt, span) &&
       types_incompatible(existing, vt) && !value_preserving_widen(vt, existing) {
        tc_assign_error(k, span, vt, name, existing, target, value)
    }
    tc_store(k, 0, vt, fr, graph_dest_var(name, NO_NODE, existing), span)
}

// A compound assignment's operation: its target (read, or through the place
// already built: `k.compound`) op its value.
tc_compound_value :: proc(k: ^TC, op_tok: Token_Id, target, value: Tree_Id, env: ^Type_Scope, want: Fuse_Want) -> (Type, Fused) {
    op, _ := compound_assign_op(build_tokens[op_tok].kind)
    t, r := tc_binary_op(k, op, token_span(build_tokens[op_tok]), target, value, env, want, .Explicit)
    if want != .None && !r.ok { tc_fail(k, "a compound assignment's operation") }
    return t, r
}

// A slice bound to a string literal or to a constant: a writable view of
// read-only storage (a write through it would fault).
tc_no_literal_slice :: proc(k: ^TC, target: Type, value: Tree_Id, span: Span) {
    if value == 0 || !is_slice_type(target) { return }
    if k.t.tag[tc_unparen(k, value)] == .String {
        tc_error(k, span, TYPE_SLICE_CANNOT_BIND_STRING_LITERAL)
    } else if name, is_const := tc_write_root_const(k, value); is_const {
        tc_error(k, span, TYPE_SLICE_CANNOT_BIND_CONSTANT, name, name)
    }
}

// A value declared as a fixed array: its elements' type, and no more of
// them than it holds (a shorter one leaves the rest zero; text counts its
// bytes, not its tier).
tc_array_assign :: proc(k: ^TC, span: Span, name: string, fa: ^Type_Fixed_Array, vt: Type, value: Tree_Id) {
    #partial switch v in vt {
    case ^Type_Fixed_Array:
        if types_incompatible(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
        } else if v.size > 0 && v.size > fa.size {
            tc_error(k, span, TYPE_ARRAY_ELEMENTS_CAPACITY, v.size, name, fa.size)
        }
    case ^Type_Partial_Array:
        size := v.size
        if m := tc_unparen(k, value); k.t.tag[m] == .String { size = len(tc_text(k.t.main[m])) }
        if types_incompatible(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
        } else if size > 0 && size > fa.size {
            tc_error(k, span, TYPE_ARRAY_ELEMENTS_CAPACITY, size, name, fa.size)
        }
    case:
        if !is_any(vt) { tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa)) }
    }
}

// `p^ = v`: the place p points at, then v into it.
tc_deref_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    at := tree_span(tr, target)
    diag := value if op_tok == 0 else 0
    b := tc_building(k)
    pt, pr := tc_expr(k, Tree_Id(tr.a[target]), env, .Place if b != nil else .None, temp_span = at)
    place := NO_VALUE
    if b = tc_building(k); b != nil {
        if p, is_ptr := pt.(^Type_Ptr); is_ptr { place = graph_op_value(b, .Deref, .Explicit, at, p.elem, "", pr.v) }
    }
    vt := tc_store_at(k, value, place, env, span, op_tok, target)
    if p, is_ptr := pt.(^Type_Ptr); is_ptr {
        tc_set_type(k, target, p.elem)
        if types_incompatible(p.elem, vt) { tc_error(k, span, TYPE_CANNOT_ASSIGN_THROUGH_POINTER, type_name(vt), type_name(p.elem)) }
        if is_infer(vt) { tc_literal_overflow(k, diag, p.elem, span) }
    } else if !is_any(pt) {
        tc_error(k, span, TYPE_CANNOT_DEREFERENCE_ASSIGN_NON_POINTER, type_name(pt))
    }
}

// A block's statements with each `#if` whose condition is known replaced by
// its live arm's (folded before the old checker ran; an elif in its chain
// is an ordinary if, as the old parser had it).
tc_live :: proc(k: ^TC, stmts: []Tree_Id) -> []Tree_Id {
    t := k.t
    folds := false
    for s in stmts {
        if t.tag[s] == .If && if_view(t, s).hash != 0 { folds = true; break }
    }
    if !folds { return stmts }
    out := make([dynamic]Tree_Id, 0, len(stmts), context.temp_allocator)
    for s in stmts {
        if t.tag[s] != .If || if_view(t, s).hash == 0 {
            append(&out, s)
            continue
        }
        v := if_view(t, s)
        live, known := tc_comptime_bool(k, v.cond)
        if !known {
            append(&out, s)   // (left for the check to report)
            continue
        }
        append(&out, ..tc_live(k, v.then if live else v.else_))
    }
    return out[:]
}

// A condition known when the program is compiled: a bool, the target (#web,
// #native, #windows, #linux, #mac), `not` of one.
tc_comptime_bool :: proc(k: ^TC, n: Tree_Id) -> (bool, bool) {
    t := k.t
    m := tc_unparen(k, n)
    #partial switch t.tag[m] {
    case .True:  return true, true
    case .False: return false, true
    case .Hash_Name:
        switch tc_text(Token_Id(t.a[m])) {
        case "web":     return k.c.target_web, true
        case "native":  return !k.c.target_web, true
        case "windows": return k.c.target_os == .Windows, true
        case "linux":   return k.c.target_os == .Linux, true
        case "mac":     return k.c.target_os == .Mac, true
        }
    case .Unary:
        if build_tokens[t.main[m]].kind == .Not {
            v, ok := tc_comptime_bool(k, Tree_Id(t.a[m]))
            if ok { return !v, true }
        }
    }
    return false, false
}

// `void`, written as a value.
tc_is_void :: proc(k: ^TC, n: Tree_Id) -> bool {
    return k.t.tag[n] == .Ident && tc_name(k, n) == "void"
}

tc_is_pointer :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Ptr)
    return ok
}

// `x : T = void`: declared uninitialized (no construction, no stores) —
// the value where it is written void. Unannotated, there is no type.
tc_decl_void :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, env: ^Type_Scope, fields_of: ^Type_Scope) {
    span := tree_span(k.t, s)
    if is_any(ann) {
        if _, shadowed := tc_declared_before(env, name, fields_of != nil); !shadowed {
            tc_error(k, span, TYPE_VOID_INIT_REQUIRES_EXPLICIT, name, name)
            type_env_set(env, name, Type_Error{})
        }
        return
    }
    if fields_of != nil { tc_add_field(fields_of, name, ann, 0) }
    b := tc_building(k)
    decl := NO_NODE
    if b != nil {
        decl = tc_field_decl(k, fields_of, name, target, value, span)
        if decl == NO_NODE { decl = graph_fuse_decl(b, name, span) }
    }
    type_env_set(env, name, ann)
    tc_note_decl(k, name, ann, span, false)
    if b = tc_building(k); b == nil { return }
    graph_fuse_typed(b, decl, ann)
    if fields_of != nil {
        // (A field's `= void`: its declaration's, as written — the value
        // stored, unchecked.)
        val := graph_fuse_void(b, ann, b.fuse.field_inits[tc_sid(k, target)])
        graph_fuse_write_at(b, graph_var(b, name, decl, ann, span), val, span)
        return
    }
    graph_fuse_void_decl(b, decl, ann, span, span)
}

// A declaration of a block, for its size guard.
TC_Decl_Note :: struct {
    name: string,
    t:    Type,
    span: Span,
    take: bool,   // (a take binds memory it takes: no storage of its own)
}

tc_note_decl :: proc(k: ^TC, name: string, t: Type, span: Span, take: bool) {
    if k.decls != nil { append(k.decls, TC_Decl_Note{name, distinct_base(t), span, take}) }
}

// A value too big for the stack, with no scope arena to hold it: an error
// (check_storage_sizes). Analysis alone runs no code.
tc_storage_sizes :: proc(k: ^TC, decls: []TC_Decl_Note) {
    if k.c.analysis_only || k.table.has_scope_allocator || k.table.context_expected_at_runtime { return }
    for d in decls {
        if !d.take && routes_to_arena(d.t) {
            tc_error(k, d.span, TYPE_VALUE_TOO_LARGE_STACK_BYTES, d.name, checker_type_byte_size(d.t))
        }
    }
}
