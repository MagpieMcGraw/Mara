package mara

import "core:fmt"

// ---------------------------------------------------------------------------
// Block codegen helpers
// ---------------------------------------------------------------------------

// Generate a basic block of statements. Returns true if the block was terminated
// (by a return statement). Handles push/pop scope and emits a branch to
// fallthrough_label when not terminated.
gen_body_block :: proc(g: ^Codegen, stmts: []Stmt, scope_kind: Control_Scope_Kind, fallthrough_label: string) -> bool {
    push_scope(g, scope_kind, stmts)
    terminated := false
    for stmt in stmts {
        gen_stmt(g, stmt)
        if _, ok := stmt.(Stmt_Return); ok {
            terminated = true
            break
        }
    }
    if !terminated {
        pop_scope(g)
        emit(g, "  br label %%%s", fallthrough_label)
    } else {
        // Return already emitted resets; just pop the stack entry
        if len(g.scope_stack) > 0 { pop(&g.scope_stack) }
    }
    return terminated
}

// Emit break/continue scope cleanup (defers + arena reset).
emit_loop_exit :: proc(g: ^Codegen) {
    if len(g.scope_stack) > 0 {
        emit_scope_defers(g, &g.scope_stack[len(g.scope_stack) - 1])
        if g.scope_stack[len(g.scope_stack) - 1].has_mark {
            emit_arena_reset(g)
        }
    }
}

// Generate a loop body block with break/continue support.
// Returns true if the block was terminated.
gen_loop_body :: proc(g: ^Codegen, stmts: []Stmt, break_label: string, continue_label: string) -> bool {
    push_scope(g, .For_Body, stmts)
    terminated := false
    for stmt in stmts {
        if _, ok := stmt.(Stmt_Break); ok {
            emit_loop_exit(g)
            emit(g, "  br label %%%s", break_label)
            terminated = true
            break
        }
        if _, ok := stmt.(Stmt_Continue); ok {
            emit_loop_exit(g)
            emit(g, "  br label %%%s", continue_label)
            terminated = true
            break
        }
        gen_stmt(g, stmt)
    }
    if !terminated {
        pop_scope(g)
        emit(g, "  br label %%%s", continue_label)
    } else {
        if len(g.scope_stack) > 0 { pop(&g.scope_stack) }
    }
    return terminated
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
        emit(g, "  br i1 %s, label %%%s, label %%%s", cond, then_label, else_label)
    } else {
        emit(g, "  br i1 %s, label %%%s, label %%%s", cond, then_label, end_label)
    }

    // Save variable state — variables declared in branches must not leak
    snap := save_var_scope(g)

    // Then block
    emit(g, "%s:", then_label)
    gen_body_block(g, s.body[:], .If_Then, end_label)

    // Restore before else — then-block variables must not be visible in else
    restore_var_scope(g, &snap)

    // Else block
    if len(s.else_body) > 0 {
        emit(g, "%s:", else_label)
        gen_body_block(g, s.else_body[:], .If_Else, end_label)
    }

    // Restore after branches — branch-local variables must not leak to merge point
    restore_var_scope(g, &snap)

    // End block
    emit(g, "%s:", end_label)
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

    emit(g, "  br label %%%s", cond_label)

    // Condition
    emit(g, "%s:", cond_label)
    cond := gen_expr(g, s.condition)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cond, body_label, end_label)

    // Body
    emit(g, "%s:", body_label)
    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post clause
    if has_post {
        emit(g, "%s:", post_label)
        gen_stmt(g, s.post)
        emit(g, "  br label %%%s", cond_label)
    }

    // End
    emit(g, "%s:", end_label)
}

// ---------------------------------------------------------------------------
// Range-for loop codegen: `for i in low..<high { body }`
// ---------------------------------------------------------------------------

gen_for_range :: proc(g: ^Codegen, s: ^Stmt_For) {
    // Determine the LLVM IR type for the iterator
    ir_type := llvm_type_from_checker(s.var_type)

    // Evaluate bounds
    low_val  := gen_expr(g, s.range_low, ir_type)
    high_val := gen_expr(g, s.range_high, ir_type)

    // Alloca + init loop variable
    alloca_name := fmt.tprintf("%%%s", s.loop_var)
    emit(g, "  %s = alloca %s", alloca_name, ir_type)
    emit(g, "  store %s 0, ptr %s", ir_type, alloca_name)
    emit(g, "  store %s %s, ptr %s", ir_type, low_val, alloca_name)
    g.all_vars[s.loop_var] = Scalar_Var{alloca_name}

    // Labels
    cond_label := fresh_label(g, "for.cond")
    body_label := fresh_label(g, "for.body")
    post_label := fresh_label(g, "for.post")
    end_label  := fresh_label(g, "for.end")
    continue_target := post_label

    emit(g, "  br label %%%s", cond_label)

    // Condition: i < high (half-open). Range-for is always exclusive.
    emit(g, "%s:", cond_label)
    cur := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", cur, ir_type, alloca_name)
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
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_label, end_label)

    // Body
    emit(g, "%s:", body_label)
    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post: i += 1
    emit(g, "%s:", post_label)
    inc_load := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", inc_load, ir_type, alloca_name)
    inc_val := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", inc_val, ir_type, inc_load)
    emit(g, "  store %s %s, ptr %s", ir_type, inc_val, alloca_name)
    emit(g, "  br label %%%s", cond_label)

    // End
    emit(g, "%s:", end_label)
}

// ---------------------------------------------------------------------------
// Collection-for loop codegen: `for elem, idx in collection { body }`
// ---------------------------------------------------------------------------

gen_for_collection :: proc(g: ^Codegen, s: ^Stmt_For) {
    // Get collection variable name from the expression
    coll_name := ""
    coll_fa: ^Expr_Field_Access  // set when collection is a field access (desugared array class)
    if ident, ok := s.collection.(^Expr_Ident); ok {
        coll_name = ident.name
    } else if fa, fa_ok := s.collection.(^Expr_Field_Access); fa_ok {
        // Desugared array class: `args.buf` or `context.args.buf`
        coll_fa = fa
        // Extract base name for simple cases
        if ident, id_ok := fa.expr.(^Expr_Ident); id_ok {
            coll_name = ident.name
        }
    }
    if coll_name == "" && coll_fa == nil {
        codegen_fatal(g, s.span, "collection-for requires an identifier or field access")
    }

    // Resolve data pointer, length, and element IR type from the collection variable
    data_ptr := ""
    length_val := ""
    elem_ir := ""
    use_array_gep := false  // true for fixed arrays (need [N x T] GEP), false for pointer GEP
    arr_type_str := ""      // e.g. "[8 x i64]" for fixed array GEP

    // Field access collection (desugared array class on a non-local, e.g. context.args)
    if coll_name == "" && coll_fa != nil {
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
        emit(g, "  %s = load i64, ptr %s", len_val, len_gep)
        length_val = len_val
        elem_ir = sv.elem_type
    } else if chain, chain_ok := build_address_chain(g, s.collection); chain_ok && chain.final_kind == .Struct {
        // Array class via the address chain — works for any expression that
        // resolves to an array-class struct. Most chained accesses are
        // already desugared to `expr.buf` + collection_len by the type
        // checker, so this primarily covers bare-ident array classes; using
        // the chain keeps the resolution shape consistent with the other
        // address-resolution sites.
        ac_st, ac_ok := lookup_struct(g, chain.struct_name)
        if !ac_ok || !ac_st.is_array_class {
            codegen_fatal(g, s.span, "cannot iterate over struct '%s'", chain.struct_name)
        }
        ac_ptr := emit_address_chain(g, &chain)
        st_llvm := struct_llvm_name(chain.struct_name)
        elem_ir = ac_elem_ir_type(ac_st)
        arr_gep := fresh_tmp(g)
        arr_fi := ac_array_field_index(ac_st)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", arr_gep, st_llvm, ac_ptr, arr_fi)
        data_ptr = arr_gep
        use_array_gep = true
        arr_type_str = fmt.tprintf("[%d x %s]", ac_st.array_cap, elem_ir)
        len_gep := fresh_tmp(g)
        len_fi := ac_len_field_index(ac_st)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", len_gep, st_llvm, ac_ptr, len_fi)
        len_val := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", len_val, len_gep)
        length_val = len_val
    } else {
        codegen_fatal(g, s.span, "unknown collection variable '%s'", coll_name)
    }

    // Alloca index variable, init to 0
    idx_alloca := fresh_tmp(g)
    emit(g, "  %s = alloca i64", idx_alloca)
    emit(g, "  store i64 0, ptr %s", idx_alloca)
    if s.index_var != "" {
        g.all_vars[s.index_var] = Scalar_Var{idx_alloca}
    }

    // Labels
    cond_label := fresh_label(g, "for.cond")
    body_label := fresh_label(g, "for.body")
    post_label := fresh_label(g, "for.post")
    end_label  := fresh_label(g, "for.end")
    continue_target := post_label

    emit(g, "  br label %%%s", cond_label)

    // Condition: idx < length
    emit(g, "%s:", cond_label)
    cur_idx := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", cur_idx, idx_alloca)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt i64 %s, %s", cmp, cur_idx, length_val)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_label, end_label)

    // Body
    emit(g, "%s:", body_label)

    // Load element if elem_var is provided
    if s.elem_var != "" {
        // Reload index for element access
        body_idx := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", body_idx, idx_alloca)

        // GEP to element
        elem_ptr := fresh_tmp(g)
        if use_array_gep {
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", elem_ptr, arr_type_str, data_ptr, body_idx)
        } else {
            emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, elem_ir, data_ptr, body_idx)
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
            emit(g, "  %s = alloca %s", elem_alloca, st_llvm_name)
            if st_def, st_ok := lookup_struct(g, struct_name); st_ok {
                sz := struct_byte_size(st_def, g.checked)
                emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", elem_alloca, elem_ptr, sz)
            }
            g.all_vars[s.elem_var] = Struct_Var{elem_alloca, struct_name, ""}
        } else if is_slice_elem {
            // Slice element: alloca { ptr, i64, i64 } + memcpy
            elem_alloca := fmt.tprintf("%%%s", s.elem_var)
            emit_slice_alloca(g, elem_alloca)
            emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", elem_alloca, elem_ptr)
            g.all_vars[s.elem_var] = Slice_Var{alloca = elem_alloca, elem_type = "i8", is_utf8 = is_utf8_slice}
        } else {
            // Scalar element: alloca + load + store
            elem_alloca := fmt.tprintf("%%%s", s.elem_var)
            emit(g, "  %s = alloca %s", elem_alloca, elem_ir)
            elem_val := fresh_tmp(g)
            emit(g, "  %s = load %s, ptr %s", elem_val, elem_ir, elem_ptr)
            emit(g, "  store %s %s, ptr %s", elem_ir, elem_val, elem_alloca)
            g.all_vars[s.elem_var] = Scalar_Var{elem_alloca}
        }
    }

    gen_loop_body(g, s.body[:], end_label, continue_target)

    // Post: idx += 1
    emit(g, "%s:", post_label)
    inc_load := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", inc_load, idx_alloca)
    inc_val := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, 1", inc_val, inc_load)
    emit(g, "  store i64 %s, ptr %s", inc_val, idx_alloca)
    emit(g, "  br label %%%s", cond_label)

    // End
    emit(g, "%s:", end_label)
}
