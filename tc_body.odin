package mara

import "core:strings"

// Bodies, checked statement by statement in the order they run: a fun's
// code; a struct's constructor, whose field declarations are its fields —
// each typed as its declaration finds, so its fields are known once its
// body is checked. (The graph is lowered from them once checking is done:
// lower.odin, which replays each body where TC.events says it was checked.)

tc_scope_body :: proc(k: ^TC, sc: ^TC_Scope) {
    t := k.t
    ts := sc.ts
    v := scope_view(t, sc.node)
    span := tree_span(t, sc.def)
    is_struct := ts.kind == .Struct
    if is_struct { ts.sig_state = .In_Progress }
    hint := k.hint
    defer k.hint = hint
    outer := k.body
    k.body = ts
    defer k.body = outer
    tc_register_defs(k, sc)
    if is_struct { tc_early_self(k, v.body) }
    body := new_block_scope(ts)
    // (A struct's params its constants may use; its and a fun's constants
    // checked before its code.)
    if is_struct { for p in ts.params { tc_bind(k, body, p.name, p.type_, {p.decl, .Param}) } }
    tc_check_local_consts(k, sc, body)
    // (An intrinsic's body is the compiler's: its signature, the LLVM
    // intrinsic's shape.)
    if v.intrinsic != 0 && !is_struct { check_llvm_intrinsic_signature(k.c, ts, tc_intrinsic_name(k, v.intrinsic), span) }
    tc_event(k, {kind = .Body, sc = sc})   // (lowered from here: after its constants)
    // (A fun's definitions are checked before its code; a struct's once its
    // fields are known: its methods read them.)
    if !is_struct { tc_check_defs(k, sc) }
    // (Its params and named results — locals: its variables, an intrinsic's
    // too, though no code of its reads them.)
    if !is_struct { for p in ts.params { tc_bind(k, body, p.name, p.type_, {p.decl, .Param}) } }
    for name, i in ts.return_binding_names { tc_bind(k, body, name, ts.return_types[i], {ts.return_binding_decls[i], .Result}) }
    if v.intrinsic == 0 {
        for name, bt in sc.subst { tc_bind(k, body, name, bt, {tc_type_param_decl(k, sc.node, name), .Type}) }
        tc_scope(k, v.body, body, ts if is_struct else nil, top = true)
    }
    if is_struct {
        // (A field's width its uses left open: settled, as a local's is.)
        for &fl in ts.fields { fl.type_ = solidify_type(fl.type_) }
        ts.sig_state = .Resolved
    }
    // (A default param's width the body left open: settled.)
    solidify_param_defaults(k.c, ts)
    if is_struct { tc_check_defs(k, sc) }
}

// A block's statements: each checked whole before the next. `fields_of`: the
// struct whose top block it is (its declarations are its fields).
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
    for s in stmts {
        if t.tag[s] == .Define {
            // (A body's definitions are registered and checked with it.)
            if !top { tc_unsupported(k, s, "a definition in a block") }
            continue
        }
        if t.tag[s] == .Using && fields_of != nil {
            tc_using(k, s, env, fields_of)
        } else if t.tag[s] == .Decl && fields_of != nil {
            tc_decl(k, s, env, fields_of)
        } else {
            tc_stmt(k, s, env)
        }
    }
}

tc_stmt :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        if tc_override(k, e, env) { return }
        rt := tc_check(k, e, env)
        // A call's value, dropped: `_ = f()` says so.
        if tc_is_call(k, e) && rt != nil {
            _, is_void := rt.(Type_Void)
            _, is_error := rt.(Type_Error)
            if !is_void && !is_error { tc_error(k, span, TYPE_DISCARDED_RETURN, tc_call_name(k, e)) }
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
        tc_scope(k, tree_list(t, t.a[s]), new_block_scope(env))
    case .Match:
        tc_match(k, s, env)
    case .Break, .Continue:
    case:
        tc_unsupported(k, s, "this statement")
    }
}


// `x := v`, `x : T = v`, `x : T`: its type the annotation's, else the
// value's. In a struct's top block (`fields_of`), a field: typed as its
// annotation, else as its value.
tc_decl :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, fields_of: ^Type_Scope = nil) {
    t := k.t
    span := tree_span(t, s)
    v := decl_view(t, s)
    if len(v.targets) > 1 && len(v.values) == 1 {
        // (Several from one value: its results — bare names declared, places
        // stored.)
        tc_destructure(k, s, v.targets, v.values[0], true, v.type_, env, fields_of)
        return
    }
    for tg in v.targets {
        if t.tag[tg] != .Ident {
            tc_unsupported(k, s, "a declaration of no name")
            return
        }
    }
    if len(v.values) > 0 && len(v.values) != len(v.targets) {
        tc_unsupported(k, s, "this declaration")
        return
    }
    // (Several names, each its own declaration — a struct's fields made
    // first, together: annotated, typed as they are made.)
    if len(v.targets) > 1 && fields_of != nil && v.type_ != 0 {
        ft := tc_type(k, v.type_, env, span)
        for tg, i in v.targets { tc_add_field(fields_of, tc_name(k, tg), k.t.main[tg], ft, v.values[i] if i < len(v.values) else 0) }
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
    ref := tc_decl_ref(k, target, fields_of)
    tc_set_ref(k, target, ref)
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
    if fields_of != nil && !is_any(ann) { tc_add_field(fields_of, name, ref.decl, ann, value) }
    if value != 0 && t.tag[tc_unparen(k, value)] == .Take {
        tc_decl_take(k, s, target, value, name, ann, env, fields_of)
        return
    }
    // (`[:n]T`: n its capacity.)
    cap_n := Tree_Id(0)
    if ann_node != 0 && t.tag[ann_node] == .Type_Slice {
        cap_n = Tree_Id(t.a[ann_node])
        if cap_n == 0 { cap_n = tc_count_arg(k, Tree_Id(t.b[ann_node])) }   // (`[]T(n)`)
    }
    if value == 0 {
        if bindings := tc_shape_bindings(k, ann_node); len(bindings) > 0 {
            tc_decl_shape(k, s, target, name, ann, bindings, env, fields_of)
            return
        }
        tc_decl_bare(k, target, name, ref, ann, env, span, cap_n)
        return
    }
    if cap_n != 0 {
        if ct := tc_check(k, cap_n, env); !is_any(ct) && !is_numeric(ct) { tc_error(k, span, TYPE_SLICE_CAPACITY_INTEGER, type_name(ct)) }
    }
    k.hint = ann
    errors_before := k.c.errors
    // (A struct's field: its `all v` is its field's.)
    saved_field := k.field_default
    k.field_default = {}
    if fields_of != nil {
        sc := k.scopes[k.scope_of[fields_of]]
        k.field_default = {value = tc_unparen(k, value), name = name, t = ann, span = tree_span(t, sc.def)}
    }
    vt := tc_check(k, value, env)
    k.field_default = saved_field
    if is_any(ann) && !tc_is_value(k, value, vt, span) {
        tc_bind(k, env, name, Type_Error{}, ref)
        return
    }
    // (A sized slice's text is copied into what it allocates.)
    if cap_n == 0 { tc_no_literal_slice(k, vt if is_untyped(ann) else ann, value, span) }
    tc_check_big_endian(k, value, span)
    if returns := tc_call_returns(k, value, env); len(returns) > 1 {
        // (One name for several results: `a, b := f()` takes them.)
        tc_error(k, span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE, 1, len(returns))
        tc_bind(k, env, name, Type_Error{}, ref)
        return
    }
    final: Type
    if !is_any(ann) {
        // (Bytes read as the annotation's type: no conversion to check.)
        flow := tc_check_byte_flow(k, ann, value, vt, span)
        if flow == .Read { tc_span_read_size(k, value, ann, tc_is_distinct(ann), span) }
        fa, to_array := distinct_base(ann).(^Type_Fixed_Array)
        // (A distinct type: matched by name — unless the value is a literal
        // not of it, matched by its shape.)
        #partial switch t.tag[tc_unparen(k, value)] {
        case .Array, .Literal, .Broadcast:
            if tc_is_distinct(ann) && types_equal(ann, vt) { to_array = false }
        case:
            if tc_is_distinct(ann) { to_array = false }
        }
        if to_array && flow == .None {
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
    tc_bind(k, env, name, final, ref)
    tc_set_type(k, target, final)   // (the name declared: its type)
    tc_note_decl(k, name, final, span, k.t.tag[tc_unparen(k, value)] == .Take)
    if fields_of != nil && is_any(ann) { tc_add_field(fields_of, name, ref.decl, final, value) }
}

// What a declaration's name declares: its own token — a struct's field in
// its top block, else a local.
tc_decl_ref :: proc(k: ^TC, target: Tree_Id, fields_of: ^Type_Scope) -> Ref {
    return {k.t.main[target], .Field if fields_of != nil else .Local}
}

// Whether a name can be declared here: not in this scope already, and no
// constant's. (Shadowing an enclosing local is reported, and declares.)
tc_declarable :: proc(k: ^TC, env: ^Type_Scope, name: string, span: Span) -> bool {
    _, here := scope_defines(env, name)
    if here {
        tc_error(k, span, TYPE_VARIABLE_ALREADY_DECLARED_SCOPE, name)
        return false
    }
    if (env == nil || !env.is_module) && parent_struct_scope(env) == nil {
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
    if name in k.consts {
        tc_error(k, span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, name)
        return false
    }
    return true
}

// `x : T`: its zero, or its construction (a struct's, an array of them's
// each) — what it constructs annotated, its constructor's defaults checked.
tc_decl_bare :: proc(k: ^TC, target: Tree_Id, name: string, ref: Ref, ann: Type, env: ^Type_Scope, span: Span, cap_n := Tree_Id(0)) {
    tc_set_type(k, target, ann)
    defer tc_bind(k, env, name, ann, ref)
    tc_note_decl(k, name, ann, span, false)
    if _, is_error := ann.(Type_Error); is_error { return }
    tc_bare_construction(k, name, ann, env, span)
    if is_any(ann) { tc_error(k, span, TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE) }
    if cap_n != 0 {
        // (`s : [:n]T`: n of T allocated for it.)
        ct := tc_check(k, cap_n, env)
        if !is_any(ct) && !is_numeric(ct) { tc_error(k, span, TYPE_SLICE_CAPACITY_INTEGER, type_name(ct)) }
        return
    }
    st := tc_bare_struct(ann)
    // (Its construction, implied: its struct's — each element's, an array's —
    // when one can be built without arguments; else it is zero.)
    if st != nil && constructs_bare(st) {
        tc_set_callee(k, target, st)
        tc_set_args(k, target, tc_default_args(st))
        tc_ctor_args(k, st, span)
    }
}


// A bare declaration of a struct its constructor's arguments make — or an
// array of them: each must have a default, and the constructor can't fail
// (nothing would take its err). An array's elements that can't be built so
// are left zero: said so. (A body's own declarations: no nested block's.)
tc_bare_construction :: proc(k: ^TC, name: string, t: Type, env: ^Type_Scope, span: Span) {
    if env.kind == .Block && env.parent_scope != nil && env.parent_scope.kind == .Block { return }
    // (A generic struct's instance: its fields made with it, not checked so.)
    if env.kind == .Block && env.parent_scope != nil && env.parent_scope.generic_base != "" { return }
    elem, is_array := t, false
    for {
        #partial switch v in distinct_base(elem) {
        case ^Type_Fixed_Array:
            elem, is_array = v.elem, true
            continue
        case ^Type_Partial_Array:
            elem, is_array = v.elem, true
            continue
        }
        break
    }
    st, is_scope := elem.(^Type_Scope)
    if !is_scope || st.kind != .Struct || len(st.params) == 0 { return }
    shown := st.source_name if st.source_name != "" else st.name
    if is_array && !constructs_bare(st) {
        check_warning(k.c, span, TYPE_WON_GET_AUTO_CONSTRUCTED_DECLARED, shown, name)
        return
    }
    for p in st.params {
        if field_has_default(p) { continue }
        // (Its signature, to show what to pass.)
        sig := strings.builder_make(context.temp_allocator)
        strings.write_string(&sig, shown)
        strings.write_string(&sig, "(")
        for pp, i in st.params {
            if i > 0 { strings.write_string(&sig, ", ") }
            strings.write_string(&sig, pp.name)
            if pp.type_ != nil {
                strings.write_string(&sig, ": ")
                strings.write_string(&sig, type_name(pp.type_))
            }
        }
        strings.write_string(&sig, ")")
        tc_error(k, span, TYPE_TYPE_SELF_CONSTRUCTING_CALL_LIKE, name, shown, strings.to_string(sig), name, shown, shown)
        return
    }
    if len(st.return_types) > 0 { tc_error(k, span, TYPE_BARE_CAN_FAIL, name, shown, name, shown) }
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
tc_add_field :: proc(ts: ^Type_Scope, name: string, decl: Token_Id, t: Type, value: Tree_Id, slot: Maybe(int) = nil) {
    if name in ts.field_map { return }   // (added with the others declared with it)
    append(&ts.fields, Struct_Type_Field{name = name, decl = decl, type_ = t, default_node = value, default_slot = slot})
    build_field_map(&ts.sd)
}

// A name already declared where a declaration would declare it: below the
// module (in a struct's top block, in it).
tc_declared_before :: proc(env: ^Type_Scope, name: string, in_struct: bool) -> (Type, bool) {
    if in_struct {
        t, ok := env.types[name]
        return t, ok
    }
    t, _, ok := scope_find(env, name, below_module = true)
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

// `x = v`: the value at the variable's type.
tc_assign :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) > 1 && len(values) == 1 {
        tc_destructure(k, s, targets, values[0], false, 0, env)
        return
    }
    if len(targets) > 1 && len(targets) == len(values) {
        for tg, i in targets { tc_assign_one(k, s, tg, values[i], env) }
        return
    }
    if len(targets) != 1 || len(values) != 1 {
        tc_unsupported(k, s, "this assignment")
        return
    }
    tc_assign_one(k, s, targets[0], values[0], env)
}

// One target's assignment (a broadcast's copies are each one).
tc_assign_one :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[target] {
    case .Field: tc_field_assign(k, s, target, value, env)
    case .Index: tc_index_assign(k, s, target, value, env)
    case .Slice: tc_slice_assign(k, s, target, value, env)
    case .Deref: tc_deref_assign(k, s, target, value, env)
    }
    #partial switch t.tag[target] {
    case .Field, .Index, .Slice, .Deref:
        // (Into a constant: its storage is read-only.)
        if cname, is_const := tc_write_root_const(k, target); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
        return
    case .Ident:
    case:
        tc_unsupported(k, target, "this assignment target")
        return
    }
    name := tc_name(k, target)
    if name == "_" {
        // A discard: the value checked for its own sake.
        k.hint = nil
        tc_check(k, value, env)
        return
    }
    if name == "this_program" {
        tc_program_assign(k, value, env)
        return
    }
    existing, loc, ok := tc_name_write(k, target, name, env, span)
    if !ok { return }
    if tc_is_void(k, value) {
        // (`x = void` de-initializes: the void value written, unchecked.)
        tc_check(k, value, env)
        return
    }
    if loc != nil && loc.kind == .Struct {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    tc_check_write(k, value, tc_check(k, value, env), existing, name, span)
}

// A write to a bare name, checked: the name is declared, no constant, and no
// param the fun can't write. Its type and where it is declared; ok false when
// it can't be written (reported).
tc_name_write :: proc(k: ^TC, target: Tree_Id, name: string, env: ^Type_Scope, span: Span) -> (existing: Type, loc: ^Type_Scope, ok: bool) {
    found: bool
    existing, loc, found = scope_find(env, name)
    if found {
        tc_set_ref(k, target, scope_find_ref(env, name))
        tc_set_type(k, target, existing)   // (the name written: its type)
    }
    if !found && name not_in k.consts {
        report_unresolved(k.c, span, env, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
        tc_bind(k, env, name, Type_Error{}, {})
        return nil, nil, false
    }
    if (loc == nil || loc.kind == .Struct) && name in k.consts {
        tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, name)
        return nil, nil, false
    }
    if is_immutable_param(env, name) { tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name) }
    return existing, loc, true
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
    switch {
    case expected == 0 && supplied > 0, expected == 1 && supplied > 1:
        tc_error(k, span, TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN)
        return
    case expected == 1 && supplied == 0 && least > 0, expected > 1 && (supplied > expected || supplied < least):
        tc_error(k, span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED, supplied, expected)
        return
    }
    for val, i in values {
        want := rts[i]
        k.hint = want
        vt := tc_check(k, val, env)
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

// `if c {…} elif d {…} else {…}`: the condition a bool, then each block (an
// elif, the else block's one statement).
tc_if :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := if_view(t, s)
    if v.hash != 0 {
        // (One whose condition is known is folded away: tc_live.)
        tc_error(k, tree_span(t, v.cond), TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN)
        return
    }
    ct := tc_check(k, v.cond, env)
    if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL_2, type_name(ct)) }
    tc_scope(k, v.then, new_block_scope(env))
    if len(v.else_) > 0 { tc_scope(k, v.else_, new_block_scope(env)) }
}

// --- loops ------------------------------------------------------------------

// `for i in lo..hi`, `for e, i in c`, `for init; cond; step`, `for cond`: its
// variables bound in its block, then its body.
tc_for :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    v := for_view(t, s)
    child := new_block_scope(env)
    #partial switch t.tag[s] {
    case .For_Each:
        ct := tc_check(k, v.collection, child)
        // (A literal looped over is held at its own type, settled.)
        #partial switch k.t.tag[tc_unparen(k, v.collection)] {
        case .Array, .Literal: ct = solidify_type(ct)
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
        if v.elem != 0 { tc_bind(k, child, tc_text(v.elem), elem, {v.elem, .Local}) }
        if v.index != 0 { tc_bind(k, child, tc_text(v.index), slice_header_width_type, {v.index, .Local}) }
        tc_scope(k, v.body, child)
    case .For_Range:
        lt := tc_check(k, v.lo, child)
        ht := tc_check(k, v.hi, child)
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
        tc_bind(k, child, tc_text(v.var), it, {v.var, .Local})
        tc_scope(k, v.body, child)
    case:
        if v.init != 0 { tc_stmt(k, v.init, child) }
        ct := tc_check(k, v.cond, child)
        if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL, type_name(ct)) }
        if v.post != 0 { tc_stmt(k, v.post, child) }
        tc_scope(k, v.body, child)
    }
}

// `x op= v`: `x = x op v`, the operation at the `op=`.
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
    existing, loc, ok := tc_name_write(k, target, name, env, span)
    if !ok { return }
    if loc != nil && loc.kind == .Struct {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    vt := tc_compound_value(k, s, op_tok, target, value, env)
    if !coerce_deferred(k.c, vt, existing, span) && !coerce_deferred(k.c, existing, vt, span) &&
       types_incompatible(existing, vt) && !value_preserving_widen(vt, existing) {
        tc_assign_error(k, span, vt, name, existing, target, value)
    }
}

// A compound assignment's operation: its target op its value — its type,
// kept on its statement.
tc_compound_value :: proc(k: ^TC, s: Tree_Id, op_tok: Token_Id, target, value: Tree_Id, env: ^Type_Scope) -> Type {
    op, _ := compound_assign_op(build_tokens[op_tok].kind)
    t := tc_binary_op(k, s, op, token_span(build_tokens[op_tok]), target, value, env)
    tc_set_type(k, s, t)
    return t
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

// `p^ = v`: what p points at, at its type.
tc_deref_assign :: proc(k: ^TC, s, target, value: Tree_Id, env: ^Type_Scope, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    diag := value if op_tok == 0 else 0
    pt := tc_check(k, Tree_Id(tr.a[target]), env)
    vt := tc_store_at(k, value, env, op_tok, target, s)
    if p, is_ptr := pt.(^Type_Ptr); is_ptr {
        tc_set_type(k, target, p.elem)
        if types_incompatible(p.elem, vt) { tc_error(k, span, TYPE_CANNOT_ASSIGN_THROUGH_POINTER, type_name(vt), type_name(p.elem)) }
        if is_infer(vt) { tc_literal_overflow(k, diag, p.elem, span) }
    } else if !is_any(pt) {
        tc_error(k, span, TYPE_CANNOT_DEREFERENCE_ASSIGN_NON_POINTER, type_name(pt))
    }
}

// A block's statements with each `#if` whose condition is known replaced by
// its live arm's (an elif in its chain is an ordinary if).
tc_live :: proc(k: ^TC, stmts: []Tree_Id) -> []Tree_Id {
    t := k.t
    folds := false
    for s in stmts {
        if t.tag[s] == .If && if_view(t, s).hash != 0 || t.tag[s] == .Expose { folds = true; break }
    }
    if !folds { return stmts }
    out := make([dynamic]Tree_Id, 0, len(stmts), context.temp_allocator)
    for s in stmts {
        // (`#expose`: the definition it marks — a DLL's entry.)
        if t.tag[s] == .Expose {
            inner := Tree_Id(t.a[s])
            k.exposed[inner] = true
            append(&out, inner)
            continue
        }
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
    ref := tc_decl_ref(k, target, fields_of)
    if is_any(ann) {
        if _, shadowed := tc_declared_before(env, name, fields_of != nil); !shadowed {
            tc_error(k, span, TYPE_VOID_INIT_REQUIRES_EXPLICIT, name, name)
            tc_bind(k, env, name, Type_Error{}, ref)
        }
        return
    }
    if fields_of != nil { tc_add_field(fields_of, name, ref.decl, ann, 0) }
    tc_bind(k, env, name, ann, ref)
    tc_set_type(k, target, ann)
    tc_note_decl(k, name, ann, span, false)
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
// Analysis alone runs no code.
tc_storage_sizes :: proc(k: ^TC, decls: []TC_Decl_Note) {
    if k.c.analysis_only || k.table.has_scope_allocator || k.table.context_expected_at_runtime { return }
    for d in decls {
        if !d.take && routes_to_arena(d.t) {
            tc_error(k, d.span, TYPE_VALUE_TOO_LARGE_STACK_BYTES, d.name, type_size(d.t))
        }
    }
}

// `match x { .A {…}  B b {…}  v {…}  else {…} }`: the subject a union, an
// enum or an err; each arm's variant one it has (a union's payload bound
// where an arm names it); every variant covered, unless an else says
// otherwise.
tc_match :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    tr := k.t
    span := tree_span(tr, s)
    subj := Tree_Id(tr.a[s])
    arms := tree_list(tr, tr.b[s])
    if subj == 0 { return }
    st := tc_check(k, subj, env)
    ut, is_union := st.(^Type_Union)
    et, is_enum := st.(^Type_Enum)
    _, is_err := st.(Type_Err)
    if !is_union && !is_enum && !is_err {
        tc_error(k, span, TYPE_MATCH_REQUIRES_UNION, type_name(st))
        return
    }
    has_else := false
    for arm in arms { if tr.tag[arm] == .Arm_Else { has_else = true } }
    if is_err && !has_else { tc_error(k, span, TYPE_MATCH_ERR_REQUIRES_ELSE) }
    for arm, i in arms {
        if tr.tag[arm] == .Arm_Else && i != len(arms) - 1 { tc_error(k, span, TYPE_LAST_ARM_MATCH) }
    }
    covered := make(map[string]bool, context.temp_allocator)
    for arm in arms {
        variant := ""
        body: []Tree_Id
        child := new_block_scope(env)
        #partial switch tr.tag[arm] {
        case .Arm_Dot:
            name := tc_text(tr.main[arm])
            variant = name
            body = tree_list(tr, tr.a[arm])
            switch {
            case is_enum:
                if name not_in et.variants { tc_error(k, span, TYPE_ENUM_VARIANT, et.name, name) }
            case is_union:
                if name not_in ut.tag_map { tc_error(k, span, TYPE_UNION_VARIANT, ut.name, name) }
            case:
                tc_error(k, span, TYPE_DOT_SHORTHAND_ONLY_USED_MATCHING, name)
            }
        case .Arm_Variant:
            name := tc_text(tr.main[arm])
            variant = name
            body = tree_list(tr, tr.a[arm])
            if is_union && name not_in ut.tag_map { tc_error(k, span, TYPE_VARIANT_UNION, name, ut.name) }
            // (No binding: a bare subject's own name sees the payload — the
            // binding declared where the subject's name is written.)
            bound: string
            bound_decl: Token_Id
            if bt := Token_Id(tr.b[arm]); bt != 0 {
                bound, bound_decl = tc_text(bt), bt
            } else if su := tc_unparen(k, subj); tr.tag[su] == .Ident {
                bound, bound_decl = tc_name(k, su), tr.main[su]
            }
            if is_union {
                if vs := ut.variant_structs[name]; vs != nil && bound != "" { tc_bind(k, child, bound, vs, {bound_decl, .Local}) }
            }
        case .Arm_Else:
            body = tree_list(tr, tr.a[arm])
        case .Arm_Value:
            value := Tree_Id(tr.a[arm])
            body = tree_list(tr, tr.b[arm])
            if tr.tag[value] == .Ident {
                name := tc_name(k, value)
                if is_enum && name in et.variants || is_union && name in ut.tag_map { variant = name }
            }
            if variant == "" {
                tc_check(k, value, env)
                if tr.tag[value] == .Field { covered[tc_text(Token_Id(tr.b[value]))] = true }
            }
        }
        if variant != "" { covered[variant] = true }
        tc_scope(k, body, child)
    }
    // (Every variant covered, unless an else says otherwise.)
    if has_else || !(is_enum || is_union) { return }
    if is_enum {
        for name in et.variants {
            if name not_in covered { tc_error(k, span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, et.name, name) }
        }
    } else {
        for name in ut.variants {
            if name not_in covered { tc_error(k, span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, ut.name, name) }
        }
    }
}

// A struct's field initializer handing `#self` to anything — a call, an
// expression — while field declarations follow it: what it reads may not be
// written yet: a warning.
tc_early_self :: proc(k: ^TC, body: []Tree_Id) {
    t := k.t
    stmts := tc_live(k, body)
    decl_after := make([]bool, len(stmts), context.temp_allocator)
    seen := false
    for i := len(stmts) - 1; i >= 0; i -= 1 {
        decl_after[i] = seen
        if t.tag[stmts[i]] == .Decl || t.tag[stmts[i]] == .Using { seen = true }
    }
    for s, i in stmts {
        if t.tag[s] != .Decl || !decl_after[i] { continue }
        v := decl_view(t, s)
        for value in v.values {
            if name, found := tc_self_call(k, value); found {
                check_warning(k.c, tree_span(t, s), TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS, name)
                break
            }
            if tc_has_self(k, value) {
                names := make([dynamic]string, context.temp_allocator)
                for tg in v.targets { append(&names, tc_name(k, tg)) }
                check_warning(k.c, tree_span(t, s), TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS, strings.join(names[:], ", ", context.temp_allocator))
                break
            }
        }
    }
}

// The call an expression hands `#self` to, by name — the innermost.
tc_self_call :: proc(k: ^TC, n: Tree_Id) -> (string, bool) {
    if n == 0 { return "", false }
    t := k.t
    #partial switch t.tag[n] {
    case .Call, .Method_Call:
        args := tree_list(t, t.a[n]) if t.tag[n] == .Call else method_view(t, n).args
        for a in args {
            if name, found := tc_self_call(k, a); found { return name, true }
        }
        for a in args {
            if tc_is_self(k, a) { return tc_call_name(k, n), true }
        }
    case .Binary:
        if name, found := tc_self_call(k, Tree_Id(t.a[n])); found { return name, true }
        return tc_self_call(k, Tree_Id(t.b[n]))
    case .Unary, .Deref, .Paren, .Field, .Broadcast, .Take:
        sub := Tree_Id(t.b[n]) if t.tag[n] == .Take else Tree_Id(t.a[n])
        return tc_self_call(k, sub)
    case .Index:
        if name, found := tc_self_call(k, Tree_Id(t.a[n])); found { return name, true }
        return tc_self_call(k, Tree_Id(t.b[n]))
    case .Slice:
        lo, hi := tree_pair(t, n)
        for p in ([3]Tree_Id{Tree_Id(t.a[n]), lo, hi}) {
            if name, found := tc_self_call(k, p); found { return name, true }
        }
    case .Literal:
        for e in tree_list(t, t.b[n]) {
            if name, found := tc_self_call(k, Tree_Id(t.a[e]) if t.tag[e] == .Named_Entry else e); found { return name, true }
        }
    case .Array:
        for e in tree_list(t, t.a[n]) {
            if name, found := tc_self_call(k, e); found { return name, true }
        }
    case .If_Expr:
        then_, else_ := tree_pair(t, n)
        if name, found := tc_self_call(k, then_); found { return name, true }
        return tc_self_call(k, else_)
    }
    return "", false
}

// Whether `#self` is anywhere in an expression.
tc_has_self :: proc(k: ^TC, n: Tree_Id) -> bool {
    if n == 0 { return false }
    t := k.t
    #partial switch t.tag[n] {
    case .Self: return true
    case .Call, .Method_Call:
        args := tree_list(t, t.a[n]) if t.tag[n] == .Call else method_view(t, n).args
        for a in args { if tc_has_self(k, a) { return true } }
    case .Binary, .Index:
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, Tree_Id(t.b[n]))
    case .Unary, .Deref, .Paren, .Field, .Broadcast:
        return tc_has_self(k, Tree_Id(t.a[n]))
    case .Take:
        return tc_has_self(k, Tree_Id(t.b[n]))
    case .Slice:
        lo, hi := tree_pair(t, n)
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, lo) || tc_has_self(k, hi)
    case .Literal:
        for e in tree_list(t, t.b[n]) {
            if tc_has_self(k, Tree_Id(t.a[e]) if t.tag[e] == .Named_Entry else e) { return true }
        }
    case .Array:
        for e in tree_list(t, t.a[n]) { if tc_has_self(k, e) { return true } }
    case .If_Expr:
        then_, else_ := tree_pair(t, n)
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, then_) || tc_has_self(k, else_)
    }
    return false
}

// `using f: T`: a struct's field whose own fields are reached as its
// struct's — T a struct with fields, or a fixed array (its swizzles); said
// at the struct when it is neither.
tc_using :: proc(k: ^TC, s: Tree_Id, env, fields_of: ^Type_Scope) {
    t := k.t
    d := Tree_Id(t.a[s])
    if t.tag[d] != .Decl {
        tc_unsupported(k, s, "this `using`")
        return
    }
    tc_decl(k, d, env, fields_of)
    at := tree_span(t, k.scopes[k.scope_of[fields_of]].def)
    for tg in decl_view(t, d).targets {
        i, has := fields_of.field_map[tc_name(k, tg)]
        if !has { continue }
        f := &fields_of.fields[i]
        f.is_using = true
        if _, is_array := f.type_.(^Type_Fixed_Array); is_array { continue }
        sd := as_scope_body(f.type_)
        if sd != nil { tc_struct_ensure(k, sd_type_scope(sd)) }   // (its fields known)
        if sd == nil || len(sd.fields) == 0 {
            tc_error(k, at, TYPE_USING_FIELD_STRUCT_FIXED_ARRAY, f.name)
        }
    }
}

// The shape shortcut: `h : Holder(Box(5))`, a shape's argument a
// constructor's call, means `h : Holder(Box) = {inner = Box(5)}` — each field
// of the shape's type given that call. Its bindings (none: no shortcut).
TC_Binding :: struct {
    field: string,
    call:  Tree_Id,
}

tc_shape_bindings :: proc(k: ^TC, ann: Tree_Id) -> []TC_Binding {
    t := k.t
    if ann == 0 || t.tag[ann] != .Type_Generic { return nil }
    tmpl, is_template := k.templates[tc_name(k, ann)]
    if !is_template || t.tag[tmpl.node] != .Struct_Def { return nil }
    gps, _ := tc_struct_generics(k, tmpl.node)
    out := make([dynamic]TC_Binding, context.temp_allocator)
    for a, i in tree_list(t, t.a[ann]) {
        if i >= len(gps) || gps[i].shape == "" { continue }
        call := tc_unparen(k, a)
        if !tc_is_call(k, call) { continue }
        for s in scope_view(t, tmpl.node).body {
            if t.tag[s] != .Decl { continue }
            v := decl_view(t, s)
            if v.type_ == 0 || t.tag[v.type_] != .Type_Name || tc_name(k, v.type_) != gps[i].name { continue }
            for tg in v.targets { append(&out, TC_Binding{tc_name(k, tg), call}) }
        }
    }
    return out[:]
}

// A declaration by the shape shortcut: its struct's literal, each field the
// shape's call.
tc_decl_shape :: proc(k: ^TC, s, target: Tree_Id, name: string, ann: Type, bindings: []TC_Binding, env, fields_of: ^Type_Scope) {
    span := tree_span(k.t, s)
    ref := tc_decl_ref(k, target, fields_of)
    // (Its construction: its struct's, its literal built from the shape.)
    if st, is_scope := ann.(^Type_Scope); is_scope && st.kind == .Struct && !st.is_module {
        tc_set_callee(k, target, st)
        tc_set_args(k, target, tc_default_args(st))
    }
    k.hint = ann
    tc_shape_literal(k, s, ann, bindings, env)
    tc_bind(k, env, name, ann, ref)
    tc_set_type(k, target, ann)
    tc_note_decl(k, name, ann, span, false)
}

// `{inner = Box(5)}` of the shape shortcut, at its type.
tc_shape_literal :: proc(k: ^TC, s: Tree_Id, t: Type, bindings: []TC_Binding, env: ^Type_Scope) {
    span := tree_span(k.t, s)
    ts, is_scope := t.(^Type_Scope)
    if !is_scope || ts.kind != .Struct {
        tc_unsupported(k, s, "a shape's shortcut of no struct")
        return
    }
    tc_struct_ensure(k, ts)
    sd := &ts.sd
    tc_ctor_args(k, ts, span)
    for bd in bindings {
        idx, has := sd.field_map[bd.field]
        if !has { continue }
        tc_literal_field(k, bd.call, sd.fields[idx], 0, bd.field, span, env)
    }
}
