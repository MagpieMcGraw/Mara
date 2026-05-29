package mara

import "core:fmt"

// ---------------------------------------------------------------------------
// Block codegen helpers
// ---------------------------------------------------------------------------

// Top-level terminator: the statement emits its own branch (and any scope
// cleanup) before yielding control. Subsequent statements at the same nesting
// level would land in a dead block, so iteration must stop after one of these.
stmt_is_terminator :: proc(s: Stmt) -> bool {
    #partial switch _ in s {
    case Stmt_Return, Stmt_Break, Stmt_Continue:
        return true
    }
    return false
}

// Generate a basic block of statements. Returns true if the block was terminated
// (by a return / break / continue at this level). Handles push/pop scope and
// emits a branch to fallthrough_label when not terminated.
gen_body_block :: proc(g: ^Codegen, stmts: []Stmt, scope_kind: Control_Scope_Kind, fallthrough_label: string) -> bool {
    push_scope(g, scope_kind, stmts)
    terminated := false
    for stmt in stmts {
        gen_stmt(g, stmt)
        if stmt_is_terminator(stmt) {
            terminated = true
            break
        }
    }
    if !terminated {
        pop_scope(g)
        emit_br(g, fallthrough_label)
    } else {
        // Terminator already emitted scope cleanup; just drop the stack entry
        if len(g.scope_stack) > 0 { pop(&g.scope_stack) }
    }
    return terminated
}

// Emit defers + arena reset for every scope from the top of the stack down
// to and including the innermost For_Body. Used by `break` / `continue` to
// unwind any intervening if-then / if-else / match-arm scopes before jumping
// out of the loop. The stack itself is not popped — the surrounding gen_*
// helpers manage Scope_Entry lifecycle.
emit_loop_exit :: proc(g: ^Codegen) {
    for i := len(g.scope_stack) - 1; i >= 0; i -= 1 {
        emit_scope_defers(g, &g.scope_stack[i])
        if g.context_enabled && g.scope_stack[i].has_mark {
            emit_arena_reset(g)
        }
        if g.scope_stack[i].scope_kind == .For_Body {
            return
        }
    }
}

// Generate a loop body block with break/continue support. Pushes the loop's
// branch targets onto the codegen-wide stack so nested break / continue (e.g.
// inside an if-then or a match arm in the body) can reach them via gen_stmt.
// Returns true if the block was terminated.
gen_loop_body :: proc(g: ^Codegen, stmts: []Stmt, break_label: string, continue_label: string) -> bool {
    append(&g.loop_label_stack, Loop_Labels{break_label = break_label, continue_label = continue_label})
    defer pop(&g.loop_label_stack)
    return gen_body_block(g, stmts, .For_Body, continue_label)
}

// ---------------------------------------------------------------------------
// If/else codegen
// ---------------------------------------------------------------------------

gen_if :: proc(g: ^Codegen, s: ^Stmt_If) {
    // `#if` was already collapsed to a single branch by the type checker —
    // the dead arm is in the AST but unchecked, so we must skip it entirely.
    // Emit the live arm inline as a normal block (no branch instructions
    // needed since there's no runtime decision to make).
    if s.is_comptime {
        live_body := s.body[:]
        if eb, eb_ok := s.condition.(^Expr_Bool); eb_ok && !eb.value {
            live_body = s.else_body[:]
        } else if intr, intr_ok := s.condition.(^Expr_Compiler_Intrinsic); intr_ok && !intr.bool_value {
            live_body = s.else_body[:]
        }
        for stmt in live_body {
            gen_stmt(g, stmt)
        }
        return
    }
    cond := gen_expr(g, s.condition)

    then_label := fresh_label(g, "if.then")
    else_label := fresh_label(g, "if.else")
    end_label  := fresh_label(g, "if.end")

    if len(s.else_body) > 0 {
        emit_cond_br(g, cond, then_label, else_label)
    } else {
        emit_cond_br(g, cond, then_label, end_label)
    }

    // Save variable state — variables declared in branches must not leak
    snap := save_var_scope(g)

    // Then block
    emit_label(g, then_label)
    gen_body_block(g, s.body[:], .If_Then, end_label)

    // Restore before else — then-block variables must not be visible in else
    restore_var_scope(g, &snap)

    // Else block
    if len(s.else_body) > 0 {
        emit_label(g, else_label)
        gen_body_block(g, s.else_body[:], .If_Else, end_label)
    }

    // Restore after branches — branch-local variables must not leak to merge point
    restore_var_scope(g, &snap)

    // End block
    emit_label(g, end_label)
}

// ---------------------------------------------------------------------------
// For loop codegen
// ---------------------------------------------------------------------------

gen_for :: proc(g: ^Codegen, s: ^Stmt_For) {
    if s.is_collection_for {
        gen_for_collection(g, s)
        return
    }
    if s.is_range {
        gen_for_range(g, s)
        return
    }

    cond_label := fresh_label(g, "for.cond")
    body_label := fresh_label(g, "for.body")
    end_label  := fresh_label(g, "for.end")

    // C-style for: determine the continue target (post label or cond label)
    has_post := s.post != nil
    post_label := has_post ? fresh_label(g, "for.post") : cond_label
    continue_target := post_label

    // Init clause (once, before loop)
    if s.init != nil {
        gen_stmt(g, s.init)
    }

    emit_br(g, cond_label)

    // Condition
    emit_label(g, cond_label)
    cond := gen_expr(g, s.condition)
    emit_cond_br(g, cond, body_label, end_label)

    // Body
    emit_label(g, body_label)
    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post clause
    if has_post {
        emit_label(g, post_label)
        gen_stmt(g, s.post)
        emit_br(g, cond_label)
    }

    // End
    emit_label(g, end_label)
}

// ---------------------------------------------------------------------------
// Range-for loop codegen: `for i in low..<high { body }`
// ---------------------------------------------------------------------------

gen_for_range :: proc(g: ^Codegen, s: ^Stmt_For) {
    // Determine the LLVM IR type for the iterator
    ir_type := llvm_type_from_checker(s.var_type)

    // Evaluate bounds. Bounds whose source IR width differs from the loop's
    // iter type (e.g. `for i in start..end` with start: i64, end: i32 and
    // iter resolved to i32 via slice-header default) get narrowed/widened
    // to ir_type so the store / icmp at iter width is well-typed.
    low_val  := coerce_int_to_ir(g, gen_expr(g, s.range_low, ir_type),
        expr_ir_type(g, s.range_low), ir_type)
    high_val := coerce_int_to_ir(g, gen_expr(g, s.range_high, ir_type),
        expr_ir_type(g, s.range_high), ir_type)

    // Alloca + init loop variable. Skip the pre-store-0 step that previously
    // shadowed the low_val store — LLVM still emits both as separate
    // instructions, and the first one is always dead.
    alloca_name := fmt.tprintf("%%%s", s.loop_var)
    emit_alloca(g, alloca_name, ir_type)
    emit_store(g, ir_type, low_val, alloca_name)
    g.all_vars[s.loop_var] = Scalar_Var{alloca_name}

    // Labels
    cond_label := fresh_label(g, "for.cond")
    body_label := fresh_label(g, "for.body")
    post_label := fresh_label(g, "for.post")
    end_label  := fresh_label(g, "for.end")
    continue_target := post_label

    emit_br(g, cond_label)

    // Condition: i < high (half-open). Range-for is always exclusive.
    emit_label(g, cond_label)
    cur := fresh_tmp(g)
    emit_load_into(g, cur, ir_type, alloca_name)
    cmp := fresh_tmp(g)
    cmp_op := "slt"
    if s.var_type != nil {
        if num, num_ok := s.var_type.(Type_Numeric); num_ok {
            #partial switch num.kind {
            case .Unsigned: cmp_op = "ult"
            }
        }
    }
    emit(g, "  %s = icmp %s %s %s, %s", cmp, cmp_op, ir_type, cur, high_val)
    emit_cond_br(g, cmp, body_label, end_label)

    // Body
    emit_label(g, body_label)
    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post: i += 1
    emit_label(g, post_label)
    inc_load := fresh_tmp(g)
    emit_load_into(g, inc_load, ir_type, alloca_name)
    inc_val := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", inc_val, ir_type, inc_load)
    emit_store(g, ir_type, inc_val, alloca_name)
    emit_br(g, cond_label)

    // End
    emit_label(g, end_label)
}

// ---------------------------------------------------------------------------
// Collection-for loop codegen: `for elem, idx in collection { body }`
// ---------------------------------------------------------------------------

gen_for_collection :: proc(g: ^Codegen, s: ^Stmt_For) {
    // Get collection variable name from the expression
    coll_name := ""
    coll_fa: ^Expr_Field_Access  // set when collection is a field access
    if ident, ok := s.collection.(^Expr_Ident); ok {
        coll_name = ident.name
    } else if fa, fa_ok := s.collection.(^Expr_Field_Access); fa_ok {
        coll_fa = fa
    }
    if coll_name == "" && coll_fa == nil {
        codegen_fatal(g, s.span, CODE_COLLECTION_REQUIRES_IDENTIFIER_FIELD_ACCESS)
    }

    // Resolve data pointer, length, and element IR type from the collection variable
    data_ptr := ""
    length_val := ""
    elem_ir := ""
    use_array_gep := false  // true for fixed arrays (need [N x T] GEP), false for pointer GEP
    arr_type_str := ""      // e.g. "[8 x i64]" for fixed array GEP

    // Field access whose result is a partial array, e.g. `context.args`.
    // Read len from field 0 and data ptr from field 2 of the partial-array
    // header (shared layout with slice for the first slice_header_bytes).
    resolved := false
    if coll_fa != nil {
        // Partial-array and slice fields share the same first slice_header_bytes
        // ({len, cap, ptr}), so reading .len and .ptr is identical for both —
        // the only thing that differs is the element type lookup.
        elem_t: Type
        is_pa_or_sl := false
        ir_type: string
        if pa, pa_ok := expr_type(coll_fa).(^Type_Partial_Array); pa_ok {
            elem_t = pa.elem
            ir_type = llvm_type_from_checker(pa)
            is_pa_or_sl = true
        } else if sl, sl_ok := expr_type(coll_fa).(^Type_Slice); sl_ok {
            elem_t = sl.elem
            ir_type = llvm_type_from_checker(sl)
            is_pa_or_sl = true
        }
        if is_pa_or_sl {
            hdr_ptr := gen_field_address(g, coll_fa)
            len_gep := fresh_tmp(g)
            emit_field_gep_into(g, len_gep, ir_type, hdr_ptr, SLICE.len)
            len_val := fresh_tmp(g)
            emit_typed_load_len(g, len_val, len_gep)
            length_val = len_val
            ptr_gep := fresh_tmp(g)
            emit_field_gep_into(g, ptr_gep, ir_type, hdr_ptr, SLICE.ptr)
            data_val := fresh_tmp(g)
            emit_load_into(g, data_val, "ptr", ptr_gep)
            data_ptr = data_val
            elem_ir = llvm_type_from_checker(elem_t)
            resolved = true
        }
    }
    if resolved {
        // skip the dispatch below
    } else if coll_name == "" && coll_fa != nil {
        // Resolve the array data pointer via address chain
        data_ptr = gen_field_address(g, coll_fa)
        elem_ir = llvm_type_from_checker(s.elem_type_)
        // The array type for GEP — look at the field access type
        if fa_type, fa_ok := expr_type(coll_fa).(^Type_Fixed_Array); fa_ok {
            use_array_gep = true
            arr_type_str = llvm_type_from_checker(fa_type)
        }
        // Length from collection_len (set by checker desugaring)
        if s.collection_len != nil {
            length_val = gen_expr(g, s.collection_len)
        }
    } else if av, av_ok := get_array(g, coll_name); av_ok {
        // Fixed array: iterate 0 to capacity
        data_ptr = av.alloca
        length_val = fmt.tprintf("%d", av.capacity)
        elem_ir = av.elem_type
        use_array_gep = true
        arr_type_str = array_var_type(&av)
    } else if sv, sv_ok := get_slice(g, coll_name); sv_ok {
        // Slice: iterate over valid data only — bound by len (cursor), not cap.
        data_ptr = slice_var_data_ptr(g, &sv)
        len_gep := fresh_tmp(g)
        emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
        len_val := fresh_tmp(g)
        emit_typed_load_len(g, len_val, len_gep)
        length_val = len_val
        elem_ir = sv.elem_type
    } else {
        codegen_fatal(g, s.span, CODE_UNKNOWN_COLLECTION_VARIABLE, coll_name)
    }

    // Loop counter runs at slice header width — length_val is loaded
    // from emit_typed_load_len for slice iteration (slice_layout.len_ir
    // wide) or is a compile-time int literal for fixed-array iteration.
    // Either way the counter at the same width keeps the comparison and
    // GEP homogeneous.
    w := slice_layout.len_ir
    idx_alloca := fresh_tmp(g)
    emit_alloca(g, idx_alloca, w)
    emit_store(g, w, "0", idx_alloca)
    if s.index_var != "" {
        g.all_vars[s.index_var] = Scalar_Var{idx_alloca}
    }

    // Labels
    cond_label := fresh_label(g, "for.cond")
    body_label := fresh_label(g, "for.body")
    post_label := fresh_label(g, "for.post")
    end_label  := fresh_label(g, "for.end")
    continue_target := post_label

    emit_br(g, cond_label)

    // Condition: idx < length
    emit_label(g, cond_label)
    cur_idx := fresh_tmp(g)
    emit_load_into(g, cur_idx, w, idx_alloca)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", cmp, w, cur_idx, length_val)
    emit_cond_br(g, cmp, body_label, end_label)

    // Body
    emit_label(g, body_label)

    // Load element if elem_var is provided
    if s.elem_var != "" {
        // Reload index for element access
        body_idx := fresh_tmp(g)
        emit_load_into(g, body_idx, w, idx_alloca)

        // GEP to element — index is at slice width.
        elem_ptr := fresh_tmp(g)
        if use_array_gep {
            emit_array_gep_var(g, elem_ptr, arr_type_str, data_ptr, body_idx, w)
        } else {
            emit_elem_gep(g, elem_ptr, elem_ir, data_ptr, body_idx, w)
        }

        // Check element kind: struct, slice, or scalar
        is_struct_elem := false
        struct_name := ""
        if sd := as_struct_body(s.elem_type_); sd != nil {
            is_struct_elem = true
            struct_name = sd.name
        }
        is_slice_elem := false
        is_utf8_slice := false
        if sl, sl_ok := s.elem_type_.(^Type_Slice); sl_ok {
            is_slice_elem = true
            _, is_byte := sl.elem.(Type_Byte)
            _, is_utf8 := sl.elem.(Type_Utf8)
            is_utf8_slice = is_byte || is_utf8
        }

        if is_struct_elem {
            // Struct element: alloca + memcpy
            elem_alloca := fmt.tprintf("%%%s", s.elem_var)
            st_llvm_name := struct_llvm_name(struct_name)
            emit_alloca(g, elem_alloca, st_llvm_name)
            if st_def, st_ok := lookup_struct(g, struct_name); st_ok {
                sz := struct_byte_size(st_def, g.checked)
                emit_memcpy(g, elem_alloca, elem_ptr, sz)
            }
            g.all_vars[s.elem_var] = Struct_Var{elem_alloca, struct_name}
        } else if is_slice_elem {
            // Slice element: alloca slice header + memcpy
            elem_alloca := fmt.tprintf("%%%s", s.elem_var)
            emit_slice_alloca(g, elem_alloca)
            emit_memcpy(g, elem_alloca, elem_ptr, slice_header_bytes)
            g.all_vars[s.elem_var] = Slice_Var{alloca = elem_alloca, elem_type = "i8", is_utf8 = is_utf8_slice}
        } else {
            // Scalar element: alloca + load + store
            elem_alloca := fmt.tprintf("%%%s", s.elem_var)
            emit_alloca(g, elem_alloca, elem_ir)
            elem_val := fresh_tmp(g)
            emit_load_into(g, elem_val, elem_ir, elem_ptr)
            emit_store(g, elem_ir, elem_val, elem_alloca)
            g.all_vars[s.elem_var] = Scalar_Var{elem_alloca}
        }
    }

    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post: idx += 1
    emit_label(g, post_label)
    inc_load := fresh_tmp(g)
    emit_load_into(g, inc_load, w, idx_alloca)
    inc_val := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", inc_val, w, inc_load)
    emit_store(g, w, inc_val, idx_alloca)
    emit_br(g, cond_label)

    // End
    emit_label(g, end_label)
}
