package mara

// ---------------------------------------------------------------------------
// Post-check INTRAPROCEDURAL escape pass.
//
// Pointer/slice validity used to be checked DURING type-checking, with the
// per-name provenance state living on Type_Env.bindings. This pass lifts that
// out: it walks each source function's durable body with its OWN block-scoped
// frame stack (g_esc — mirrors flow.odin's flow_unused_block), re-deriving the
// same provenance and running the same escape checks. The existing helpers
// (expr_provenance / is_local_ref / report_return_escape / ...) are reused
// unchanged — their provenance accessors read the frame stack (g_esc), so there
// is exactly one copy of the logic and no env-bound escape state.
//
// Frame depth + params are derived from the durable scope (enclosing_fun_depth /
// is_param), so the pass only needs a synthetic env whose `scope` is the function.
//
// Validated against the during-check checker before the switch (MARA migration):
// the would-emit set was EMPTY on the green corpus (no false positives) and
// MATCHED the during-check errors on every expect-fail escape fixture, for all
// five flavors (return-local-ref / return-struct-slice / return-struct-lit /
// write-through-param / write-field-param) plus call/ctor laundering.
// ---------------------------------------------------------------------------

escape_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program) {
    defer clear(&g_esc)
    for _, ft in checked.functions {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue } // foreign/intrinsic: no body
        if len(ft.ast.generic_params if ft.ast != nil else nil) > 0 { continue } // uninstantiated template
        escape_check_fn(c, ft)
    }
}

escape_check_fn :: proc(c: ^Checker, ft: ^Type_Scope) {
    if ft.ast == nil { return }
    // The fun's own scope is the resolution context (read by enclosing_fun_depth /
    // is_param / enclosing_callable_scope) — provenance comes from the frame stack.
    exempt := ft.home_package == "memory" // arena_alloc must return slices
    escape_block(c, ft, ft.ast.body[:], ft, exempt)
}

// One lexical block: push a frame, walk its statements, pop. Block-scoping of
// provenance falls out exactly as it did from env.bindings + env.parent.
escape_block :: proc(c: ^Checker, env: ^Type_Scope, stmts: []Stmt, ft: ^Type_Scope, exempt: bool) {
    frame: Escape_Frame
    frame.prov = make(map[string]Provenance)
    frame.is_let = make(map[string]bool)
    frame.slice_backed = make(map[string]bool)
    append(&g_esc, &frame)
    for s in stmts { escape_stmt(c, env, s, ft, exempt) }
    pop(&g_esc)
    delete(frame.prov); delete(frame.is_let); delete(frame.slice_backed)
}

escape_stmt :: proc(c: ^Checker, env: ^Type_Scope, s: Stmt, ft: ^Type_Scope, exempt: bool) {
    #partial switch v in s {
    case ^Stmt_Decl:
        // The desugared per-name assigns carry the resolved value; set provenance
        // off each, matching the during-check decl handler.
        if len(v.checked) > 0 {
            for inner in v.checked {
                if a, ok := inner.(^Stmt_Assign); ok && a.is_decl { escape_decl(c, env, a.name, a.value) }
            }
        } else {
            for name, i in v.names {
                val: Expr
                if i < len(v.init_values)      { val = v.init_values[i] }
                else if len(v.init_values) == 1 { val = v.init_values[0] }
                escape_decl(c, env, name, val)
            }
        }
    case ^Stmt_Assign:
        if v.is_decl {
            escape_decl(c, env, v.name, v.value)
        } else {
            escape_param_write(c, env, v, exempt)
        }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { escape_stmt(c, env, a, ft, exempt) }
    case Stmt_Return:
        if exempt { return }
        for val in v.values { escape_return_value(c, env, val, v.span) }
    case ^Stmt_If:
        escape_block(c, env, v.body[:], ft, exempt)
        escape_block(c, env, v.else_body[:], ft, exempt)
    case ^Stmt_For:
        if v.init != nil { escape_stmt(c, env, v.init, ft, exempt) }
        escape_block(c, env, v.body[:], ft, exempt)
        if v.post != nil { escape_stmt(c, env, v.post, ft, exempt) }
    case ^Stmt_Match:
        for arm in v.arms { escape_block(c, env, arm.body[:], ft, exempt) }
    case ^Stmt_Defer:
        escape_block(c, env, v.body[:], ft, exempt)
    }
}

// Provenance of a freshly-declared name, mirroring the during-check decl handler:
//   take      -> the storage's provenance (+ mark is_let)
//   uninit    -> prov_local
//   struct/union literal -> prov_local (the value's bytes live in our frame)
//   else      -> expr_provenance(value)
escape_decl :: proc(c: ^Checker, env: ^Type_Scope, name: string, value: Expr) {
    if name == "" || name == "_" { return }
    if value == nil {
        set_provenance(env, name, prov_local(env))
        return
    }
    #partial switch val in value {
    case ^Expr_Take:
        if f := esc_top(); f != nil { f.is_let[name] = true }
        set_provenance(env, name, expr_provenance(c, val.storage, env))
    case ^Expr_Struct_Literal:
        set_provenance(env, name, prov_local(env))
    case:
        set_provenance(env, name, expr_provenance(c, value, env))
    }
    mark_local_slice_backed_if_needed(c, env, name, value)
}

// The three return-escape checks (check_scope_body's Stmt_Return tail).
escape_return_value :: proc(c: ^Checker, env: ^Type_Scope, val: Expr, span: Span) {
    if is_local_ref(c, val, env) {
        report_return_escape(c, val, span, env)
    }
    if returns_locally_backed_struct(c, val, env) {
        check_error(c, span, TYPE_CANNOT_RETURN_STRUCT_WHOSE_SLICE)
    }
    if lit, ok := val.(^Expr_Struct_Literal); ok && returned_struct_literal_dangles(c, lit, env) {
        check_error(c, span, TYPE_CANNOT_RETURN_STRUCT_WHOSE_SLICE)
    }
}

// Writing a local reference through a param pointer (`p^ = &local`) or into a
// param struct's ref field (`p.field = &local`).
escape_param_write :: proc(c: ^Checker, env: ^Type_Scope, s: ^Stmt_Assign, exempt: bool) {
    if exempt || s.target == nil || s.value == nil { return }
    // `p^ = value`
    if un, ok := s.target.(^Expr_Unary); ok && un.op == .Caret {
        if is_local_ref(c, s.value, env) {
            if ident, id_ok := un.operand.(^Expr_Ident); id_ok && is_param(env, ident.name) {
                check_error(c, s.span, TYPE_CANNOT_WRITE_LOCAL_REFERENCE_THROUGH, ident.name)
            }
        }
        return
    }
    // `p.field = value`
    if fa, ok := s.target.(^Expr_Field_Access); ok {
        ftype := s.target_type // stamped with the field type by the field-write checker
        is_ref_field := false
        if _, p := ftype.(^Type_Ptr); p { is_ref_field = true }
        if _, sl := ftype.(^Type_Slice); sl { is_ref_field = true }
        if is_ref_field && is_local_ref(c, s.value, env) {
            if ident, id_ok := fa.expr.(^Expr_Ident); id_ok && is_param(env, ident.name) {
                check_error(c, s.span, TYPE_CANNOT_WRITE_LOCAL_REFERENCE_FIELD, fa.field, ident.name)
            }
        }
    }
}
