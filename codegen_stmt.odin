package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Statement dispatch
// ---------------------------------------------------------------------------

gen_stmt :: proc(g: ^Codegen, stmt: Stmt) {
    switch s in stmt {
    case ^Stmt_Assign:
        // Complex LHS: dispatch by target kind.
        if s.target != nil {
            #partial switch t in s.target {
            case ^Expr_Field_Access: gen_field_assign(g, s)
            case ^Expr_Index:        gen_index_assign(g, s)
            case ^Expr_Slice:
                // Byte-buffer reinterpret write: buf[lo:hi] = value
                // `assign_value_type` is set by the checker only on the reinterpret
                // path, so its presence distinguishes a scalar/struct reinterpret
                // from an array-to-array copy between byte buffers.
                if (is_byte_slice(s.target_type) || is_byte_fixed_array(s.target_type)) &&
                   s.assign_value_type != nil {
                    gen_byte_target_write(g, s, t.expr, t.low)
                } else {
                    gen_slice_range_assign(g, s)
                }
            case ^Expr_Unary:
                if t.op == .Caret { gen_deref_assign(g, s) }
            }
            return
        }
        // Skip include statements — desugared into imports before codegen
        if _, is_include := s.value.(^Expr_Include); is_include { return }

        // take(T, storage) decl — let-style binding into storage's bytes. The
        // variable's alloca IS the typed pointer returned by take; no fresh
        // alloca, no copy. Routes by resolved_type to the right Var_Entry shape.
        if take_expr, is_take := s.value.(^Expr_Take); is_take {
            gen_take_decl(g, s.name, take_expr)
            return
        }

        var_type := s.var_type

        // Fixed array type (covers explicit [N]T annotations, Type_Name aliases like Mat4, etc.)
        // The checker resolves all array types to Type_Fixed_Array with concrete size.
        if fa, fa_ok := var_type.(^Type_Fixed_Array); fa_ok {
            loc := format_location(s.span.file, s.span.line, s.span.col)
            elem_t := llvm_type_from_checker(fa.elem)
            utf8 := false
            if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
            // Array-returning call: use sret convention
            if call, call_ok := s.value.(^Expr_Call); call_ok {
                info, info_ok := lookup_fun_info(g, call_resolved_name(call))
                if info_ok && info.ret_array_cap > 0 {
                    if existing, ex_ok := get_array(g, s.name); ex_ok {
                        // NRVO alias: call directly into pre-registered buffer
                        gen_call_into_array(g, call, &existing, &info)
                    } else {
                        gen_array_assign(g, s.name, fa.size, elem_t, nil, utf8, loc, fa.has_sentinel, fa.sentinel)
                        existing, _ := get_array(g, s.name)
                        gen_call_into_array(g, call, &existing, &info)
                    }
                    return
                }
            }
            gen_array_assign(g, s.name, fa.size, elem_t, s.value, utf8, loc, fa.has_sentinel, fa.sentinel)
            return
        }

        // Check if reassigning to an existing array variable
        if is_array(g, s.name) {
            av, _ := get_array(g, s.name)
            loc := format_location(s.span.file, s.span.line, s.span.col)
            gen_array_assign(g, s.name, av.capacity, av.elem_type, s.value, av.is_utf8, loc)
            return
        }

        // Byte-buffer reinterpret read into a typed declaration:
        //     x : T = buf[lo:hi]   (slice form)
        //     x : T = buf[off]     (index form)
        // Source may be []byte, [N]byte, or Array(byte, N) (post-desugar `.items`).
        if var_type != nil && !is_byte_buffer(var_type) {
            if sl_expr, ok := s.value.(^Expr_Slice); ok {
                if codegen_is_byte_buffer_source(g, sl_expr.expr) {
                    gen_byte_target_read(g, s.name, sl_expr.expr, sl_expr.low, sl_expr.span, var_type)
                    return
                }
            }
            if idx_expr, ok := s.value.(^Expr_Index); ok {
                if codegen_is_byte_buffer_source(g, idx_expr.expr) {
                    gen_byte_target_read(g, s.name, idx_expr.expr, idx_expr.index, idx_expr.span, var_type)
                    return
                }
            }
        }

        // Check if value is a slice expression (inferred type)
        if _, ok := s.value.(^Expr_Slice); ok {
            gen_slice_assign_inferred(g, s.name, s.value)
            return
        }

        // Check if reassigning to an existing slice variable
        if _, sl_ok := get_slice(g, s.name); sl_ok {
            gen_slice_assign_inferred(g, s.name, s.value)
            return
        }

        // Slice type from alloc() or explicit []byte annotation
        if sl, sl_ok := var_type.(^Type_Slice); sl_ok {
            elem_t := llvm_type_from_checker(sl.elem)
            _, sl_utf8 := sl.elem.(Type_Utf8)
            sl_sentinel := sl.has_sentinel
            // Sized slice declaration `name : []T(N)` — allocate backing
            // storage + slice header, init to (ptr, 0, N). Same stack-vs-arena
            // policy as fixed-array decls. Sentinel slices (`[,0]T`) reserve
            // one extra element for the terminator and store the physical cap;
            // the `cap()` builtin subtracts 1 for utf8 slices so the user
            // sees N usable elements.
            if s.slice_cap_expr != nil {
                cap_val, cap_ok := codegen_const_eval_int(g, s.slice_cap_expr)
                if !cap_ok {
                    codegen_fatal(g, s.span, "slice capacity must be a compile-time constant")
                }
                cap_n := int(cap_val)
                alloc_cap := cap_n
                if sl.has_sentinel { alloc_cap += 1 }
                elem_bytes := elem_byte_size(elem_t, g.checked)
                total_bytes := alloc_cap * elem_bytes
                loc := format_location(s.span.file, s.span.line, s.span.col)
                data_name: string
                if g.context_enabled && total_bytes >= 1024 {
                    data_name = emit_arena_bump(g, total_bytes, s.name, loc)
                } else {
                    data_name = fmt.tprintf("%%%s.data", s.name)
                    emit(g, "  %s = alloca [%d x %s]", data_name, alloc_cap, elem_t)
                }
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_slice_alloca(g, alloca_name)
                ptr_gep := fresh_tmp(g)
                emit_slice_gep(g, ptr_gep, alloca_name, 0)
                emit(g, "  store ptr %s, ptr %s", data_name, ptr_gep)
                len_gep := fresh_tmp(g)
                emit_slice_gep(g, len_gep, alloca_name, 1)
                emit(g, "  store i64 0, ptr %s", len_gep)
                cap_gep := fresh_tmp(g)
                emit_slice_gep(g, cap_gep, alloca_name, 2)
                emit(g, "  store i64 %d, ptr %s", alloc_cap, cap_gep)
                // Sized slice of a slice-bearing struct: allocate a sibling
                // pool whose bytes are carved by each `&slice + call()` for
                // the call's escape locals. Pool size = sum of escape bytes
                // across all appends visible in this scope; stack-alloca for
                // small pools, arena-bump for big ones (1024-byte threshold).
                pool_alloca := ""
                if struct_has_slice_fields(sl.elem) {
                    pool_bytes := sum_pool_appends(g, g.current_fun_body, s.name)
                    if pool_bytes > 0 {
                        pool_data: string
                        if g.context_enabled && pool_bytes >= 1024 {
                            pool_name := fmt.tprintf("<%s.pool>", s.name)
                            pool_data = emit_arena_bump(g, pool_bytes, pool_name, loc)
                        } else {
                            pool_data = fmt.tprintf("%%%s.pool.data", s.name)
                            emit(g, "  %s = alloca [%d x i8]", pool_data, pool_bytes)
                        }
                        pool_alloca = fmt.tprintf("%%%s.pool", s.name)
                        emit_slice_alloca(g, pool_alloca)
                        p_ptr_gep := fresh_tmp(g)
                        emit_slice_gep(g, p_ptr_gep, pool_alloca, 0)
                        emit(g, "  store ptr %s, ptr %s", pool_data, p_ptr_gep)
                        p_len_gep := fresh_tmp(g)
                        emit_slice_gep(g, p_len_gep, pool_alloca, 1)
                        emit(g, "  store i64 0, ptr %s", p_len_gep)
                        p_cap_gep := fresh_tmp(g)
                        emit_slice_gep(g, p_cap_gep, pool_alloca, 2)
                        emit(g, "  store i64 %d, ptr %s", pool_bytes, p_cap_gep)
                    }
                }
                g.all_vars[s.name] = Slice_Var{
                    alloca       = alloca_name,
                    elem_type    = elem_t,
                    is_utf8      = sl_utf8,
                    has_sentinel = sl_sentinel,
                    pool_alloca  = pool_alloca,
                }
                // Initialize from a string literal: `s : String = "hello"` (or
                // `s : []byte(64) = "hello"`). The cap path above already
                // allocated the backing buffer; here we memcpy the literal
                // bytes in and bump len to the literal's length so the slice
                // is a usable view of the initialized prefix.
                if str_lit, str_ok := s.value.(^Expr_String); str_ok && elem_bytes == 1 {
                    str_bytes := str_lit.value
                    if len(str_bytes) > 0 {
                        global, _ := get_string_literal(g, str_bytes)
                        src_ptr := fresh_tmp(g)
                        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", src_ptr, len(str_bytes)+1, global)
                        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", data_name, src_ptr, len(str_bytes))
                    }
                    emit(g, "  store i64 %d, ptr %s", len(str_bytes), len_gep)
                    // Sentinel slices use a trailing \0; for printf-style consumers
                    // that walk the data pointer until a null, write it after the
                    // copied bytes so reading stops at the literal's end.
                    if sl.has_sentinel {
                        term_ptr := fresh_tmp(g)
                        emit(g, "  %s = getelementptr i8, ptr %s, i64 %d", term_ptr, data_name, len(str_bytes))
                        emit(g, "  store i8 0, ptr %s", term_ptr)
                    }
                }
                return
            }
            if s.value == nil {
                // Uninitialized slice: alloca + zero all three fields.
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_slice_alloca(g, alloca_name)
                ptr_gep := fresh_tmp(g)
                emit_slice_gep(g, ptr_gep, alloca_name, 0)
                emit(g, "  store ptr null, ptr %s", ptr_gep)
                len_gep := fresh_tmp(g)
                emit_slice_gep(g, len_gep, alloca_name, 1)
                emit(g, "  store i64 0, ptr %s", len_gep)
                cap_gep := fresh_tmp(g)
                emit_slice_gep(g, cap_gep, alloca_name, 2)
                emit(g, "  store i64 0, ptr %s", cap_gep)
                g.all_vars[s.name] = Slice_Var{alloca = alloca_name, elem_type = elem_t, is_utf8 = sl_utf8, has_sentinel = sl_sentinel}
                return
            }
            gen_slice_from_expr(g, s.name, s.value, elem_t, sl_utf8, sl_sentinel)
            return
        }

        // Function value or pointer type declaration
        if tf, ok := var_type.(^Type_Scope); ok && tf.kind == .Fun {
            if s.value == nil {
                // Uninitialized function pointer: alloca + null
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit(g, "  %s = alloca ptr", alloca_name)
                emit(g, "  store ptr null, ptr %s", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit(g, "  %s = alloca ptr", alloca_name)
                emit(g, "  store ptr null, ptr %s", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
            }
            alloca, _ := get_scalar(g, s.name)
            emit(g, "  store ptr %s, ptr %s", val, alloca)
            return
        }

        // Pointer type declaration: x : ^Point = ...
        if _, ok := var_type.(^Type_Ptr); ok {
            if s.value == nil {
                // Uninitialized pointer: alloca + null
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit(g, "  %s = alloca ptr", alloca_name)
                emit(g, "  store ptr null, ptr %s", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit(g, "  %s = alloca ptr", alloca_name)
                emit(g, "  store ptr null, ptr %s", alloca_name)  // zero-init
                g.all_vars[s.name] = Scalar_Var{alloca_name}
            }
            alloca, _ := get_scalar(g, s.name)
            emit(g, "  store ptr %s, ptr %s", val, alloca)
            return
        }

        // Union-typed variable (must be checked before struct literal check,
        // because union variants ARE struct literals)
        if ut, ut_ok := var_type.(^Type_Union); ut_ok {
            ukey := union_key(ut)
            if s.value == nil {
                // Uninitialized union: alloca only (e.g. for foreign code to fill)
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit(g, "  %s = alloca %s", alloca_name, union_llvm_name(ukey))
                g.all_vars[s.name] = Union_Var{
                    alloca = alloca_name,
                    union_name  = ukey,
                }
            } else {
                gen_union_assign(g, s.name, ut, s.value)
            }
            return
        }

        // Struct-typed variable (covers Type_Name, generic instances, imported types)
        if sd := as_struct_body(var_type); sd != nil {
            if checked_st, cs_ok := lookup_struct(g, sd.name); cs_ok {
                // VLA struct, `var` declaration, or any struct large enough that
                // a stack alloca would be unsafe — entire struct goes on the
                // scope arena. The 1024-byte threshold matches the type
                // checker's big-array gate.
                if checked_st.has_vla_field || s.is_var || struct_byte_size(checked_st, g.checked) > 1024 {
                    gen_vla_struct_assign(g, s.name, checked_st, s.value, s.vla_size_expr, s.span)
                    return
                }
                // Array class special handling
                if checked_st.is_array_class {
                    // Array literal init: buf : Buffer = [1, 2, 3]
                    if _, al_ok := s.value.(^Expr_Array); al_ok {
                        gen_array_class_literal_init(g, s.name, checked_st, s.value)
                        return
                    }
                    // String literal init for utf8 array class: buf : String = "hello"
                    if str_lit, str_ok := s.value.(^Expr_String); str_ok && ac_is_utf8(checked_st) {
                        gen_array_class_string_init(g, s.name, checked_st, str_lit)
                        return
                    }
                }
                // Overloaded binary returning this struct type — use the dispatch path
                if bin, bin_ok := s.value.(^Expr_Binary); bin_ok {
                    if rf, rf_ok := bin.overload_fn.?; rf_ok {
                        result_ptr := gen_binary(g, bin)
                        g.all_vars[s.name] = Struct_Var{
                            alloca = result_ptr,
                            struct_name = sd.name,
                        }
                        return
                    }
                }
                gen_struct_assign(g, s.name, checked_st, s.value)
                return
            }
        }

        // Check if value is a struct literal (inferred type)
        if _, lit_ok := s.value.(^Expr_Struct_Literal); lit_ok {
            if sd := as_struct_body(expr_type(s.value)); sd != nil {
                if checked_st, cs_ok := lookup_struct(g, sd.name); cs_ok {
                    gen_struct_assign(g, s.name, checked_st, s.value)
                    return
                }
            }
        }

        // Check if value is an overloaded binary that returns a struct or array
        // (must come before struct reassignment, so overloaded ops aren't swallowed)
        if bin, bin_ok := s.value.(^Expr_Binary); bin_ok {
            if rf, rf_ok := bin.overload_fn.?; rf_ok {
                info, info_ok := lookup_fun_info(g, rf.name)
                if info_ok && info.ret_struct != "" {
                    result_ptr := gen_binary(g, bin)
                    g.all_vars[s.name] = Struct_Var{
                        alloca = result_ptr,
                        struct_name = info.ret_struct,
                    }
                    return
                }
                if info_ok && info.ret_array_cap > 0 {
                    gen_binary(g, bin)
                    if cr, cr_ok := claim_call_result(g); cr_ok {
                        g.all_vars[s.name] = cr
                    }
                    return
                }
            }
        }

        // Check if reassigning to an existing struct variable
        if sv, ok := get_struct(g, s.name); ok {
            if checked_st, cs_ok := lookup_struct(g, sv.struct_name); cs_ok {
                gen_struct_assign(g, s.name, checked_st, s.value)
                return
            }
        }

        // Check if value is a call to a struct-returning or array-returning function
        if call, call_ok := s.value.(^Expr_Call); call_ok {
            resolved := call_resolved_name(call)
            if info, info_ok := lookup_fun_info(g, resolved); info_ok && info.ret_struct != "" {
                result_ptr := gen_call(g, call)
                g.all_vars[s.name] = Struct_Var{
                    alloca = result_ptr,
                    struct_name = info.ret_struct,
                }
                return
            }
            if info, info_ok := lookup_fun_info(g, resolved); info_ok && info.ret_array_cap > 0 {
                if existing, ex_ok := get_array(g, s.name); ex_ok {
                    gen_call_into_array(g, call, &existing, &info)
                } else {
                    gen_call(g, call)
                    if cr, cr_ok := claim_call_result(g); cr_ok {
                        g.all_vars[s.name] = cr
                    }
                }
                return
            }
        }

        // Check if reassigning to an existing union variable
        if uv, ok := get_union(g, s.name); ok {
            if ut, ut_ok := g.checked.table.unions[uv.union_name]; ut_ok {
                gen_union_assign(g, s.name, ut, s.value)
                return
            }
        }

        // Check if this is a string literal assignment (inferred utf8 array)
        // e.g. name := "hello" — produces a full [6]utf8 array
        if _, str_ok := s.value.(^Expr_String); str_ok {
            if fa, fa_ok := var_type.(^Type_Fixed_Array); fa_ok {
                if _, utf8_ok := fa.elem.(Type_Utf8); utf8_ok {
                    loc := format_location(s.span.file, s.span.line, s.span.col)
                    gen_array_assign(g, s.name, fa.size, "i8", s.value, true, loc, fa.has_sentinel, fa.sentinel)
                    return
                }
            }
        }

        // Determine the IR type for this variable.
        // Priority: checker type > existing alloca > expression type
        ir_type := "i64"
        if var_type != nil && !is_untyped(var_type) {
            ir_type = llvm_type_from_checker(var_type)
        } else if at, at_ok := g.emitted_allocas[fmt.tprintf("%%%s", s.name)]; at_ok {
            ir_type = at
        } else {
            ir_type = expr_ir_type(g, s.value)
        }

        val := gen_expr(g, s.value, ir_type)

        // Check if gen_expr produced a swizzle result (e.g. sub := arr.xy)
        if sr, sr_ok := claim_swizzle_result(g); sr_ok {
            g.all_vars[s.name] = sr
            return
        }

        // Check if gen_expr produced a call result array (e.g. result := some_array_fn())
        if cr, cr_ok := claim_call_result(g); cr_ok {
            g.all_vars[s.name] = cr
            return
        }

        // If variable doesn't exist yet, alloca it with zero initialization
        if !is_scalar(g, s.name) {
            alloca_name := fmt.tprintf("%%%s", s.name)
            emit(g, "  %s = alloca %s", alloca_name, ir_type)
            // Zero-initialize to prevent undefined values
            if ir_type == "ptr" {
                emit(g, "  store ptr null, ptr %s", alloca_name)
            } else if ir_type == "double" {
                emit(g, "  store double 0.0, ptr %s", alloca_name)
            } else if ir_type == "float" {
                emit(g, "  store float 0.0, ptr %s", alloca_name)
            } else if ir_type == "i1" {
                emit(g, "  store i1 false, ptr %s", alloca_name)
            } else if strings.has_prefix(ir_type, "[") || strings.has_prefix(ir_type, "%") {
                emit(g, "  store %s zeroinitializer, ptr %s", ir_type, alloca_name)
            } else {
                emit(g, "  store %s 0, ptr %s", ir_type, alloca_name)
            }
            g.all_vars[s.name] = Scalar_Var{alloca_name}
        }

        // Convert value to target type if needed (only for concrete-typed exprs)
        if !is_infer_expr(g, s.value) {
            val_type := expr_ir_type(g, s.value)
            if val_type != ir_type {
                val = emit_type_convert(g, val, val_type, ir_type)
            }
        }

        alloca, _ := get_scalar(g, s.name)
        emit(g, "  store %s %s, ptr %s", ir_type, val, alloca)

    case Stmt_Call:
        // Bare function call — evaluate for side effects (e.g. print calls)
        gen_expr(g, s.expr)

    case ^Stmt_Multi_Assign:
        for a in s.assigns { gen_stmt(g, a) }
    case ^Stmt_Multi_Return_Assign:
        gen_multi_return_assign(g, s)

    case Stmt_Return:
        gen_return(g, s)

    case ^Stmt_If:
        gen_if(g, s)

    case ^Stmt_For:
        gen_for(g, s)

    case ^Stmt_Scope:
        // Function definitions are handled at top level, skip here

    case Stmt_Break:
        // Handled by gen_for
    case Stmt_Continue:
        // Handled by gen_for
    case ^Stmt_Match:
        gen_match(g, s)
    case ^Stmt_Foreign:
        // Handled at top level in generate_program
    case ^Stmt_Union_Def:
        // Union type definitions are handled at top level in generate_program
    case ^Stmt_Distinct_Def:
        // Distinct type definitions are transparent — no LLVM declaration needed
    case Stmt_Module:
        // Module declarations are resolved before codegen — nothing to emit
    case ^Stmt_Dispatch_Def:
        // Dispatch groups are resolved at type-check time — no codegen needed
    case Stmt_Overload:
        // Operator overloads are resolved at type-check time — no codegen needed
    case ^Stmt_Decl:
        // Desugared by the type checker into Stmt_Assign / Stmt_Multi_Return_Assign
        // entries in s.checked. Iterate and delegate.
        for inner in s.checked { gen_stmt(g, inner) }
    case ^Stmt_Define:
        // Comptime constants: no runtime alloca. Infer-type values inline via
        // checked.constants at use sites; concrete-type constants are emitted
        // at use sites too. Nothing to emit at declaration.
    }
}

// ---------------------------------------------------------------------------
// Constant integer evaluation (codegen-side)
// ---------------------------------------------------------------------------

// Compile-time-evaluate an integer expression. Mirrors type_checker's
// const_eval_int but draws on g.checked.constant_values (the resolved
// int map) for ident lookups, since codegen doesn't hold a ^Checker.
codegen_const_eval_int :: proc(g: ^Codegen, e: Expr) -> (int, bool) {
    if e == nil { return 0, false }
    if num, ok := e.(^Expr_Number); ok {
        if !num.is_float { return int(num.int_value), true }
    }
    if un, ok := e.(^Expr_Unary); ok {
        if v, v_ok := codegen_const_eval_int(g, un.operand); v_ok {
            #partial switch un.op {
            case .Minus: return -v, true
            case .Tilde: return ~v, true
            }
        }
    }
    if bin, ok := e.(^Expr_Binary); ok {
        l, l_ok := codegen_const_eval_int(g, bin.left)
        r, r_ok := codegen_const_eval_int(g, bin.right)
        if l_ok && r_ok {
            #partial switch bin.op {
            case .Plus:        return l + r, true
            case .Minus:       return l - r, true
            case .Star:        return l * r, true
            case .Slash:       if r != 0 { return l / r, true }
            case .Modulo:      if r != 0 { return l % r, true }
            case .Shift_Left:  if r >= 0 { return l << uint(r), true }
            case .Shift_Right: if r >= 0 { return l >> uint(r), true }
            case .Ampersand:   return l & r, true
            case .Pipe:        return l | r, true
            case .Tilde:       return l ~ r, true  // xor
            }
        }
    }
    // Named constant lookup. constant_values only has trivially-resolvable
    // entries (number literals, unary minus). For richer expressions like
    // `MB :: 1 << 20`, fall back to the original constant expression and
    // recurse.
    if ident, ok := e.(^Expr_Ident); ok {
        if val, found := g.checked.constant_values[ident.name]; found {
            return val, true
        }
        if const_expr, found := g.checked.table.constants[ident.name]; found {
            return codegen_const_eval_int(g, const_expr)
        }
    }
    return 0, false
}

// ---------------------------------------------------------------------------
// take(T, storage) declaration binding
// ---------------------------------------------------------------------------

// Emit the let-style binding for `name := take(T, storage)`. The take call
// advances storage's cursor and returns a typed pointer; we bind `name` so
// that subsequent reads/writes go directly through that pointer (no copy).
gen_take_decl :: proc(g: ^Codegen, name: string, e: ^Expr_Take) {
    ptr := gen_expr_take(g, e)
    rt := distinct_base(e.resolved_type)

    // Fixed array: bind Array_Var whose data ptr is the take result.
    if fa, ok := rt.(^Type_Fixed_Array); ok {
        elem_ir := llvm_type_from_checker(fa.elem)
        is_utf8 := false
        if _, u_ok := fa.elem.(Type_Utf8); u_ok { is_utf8 = true }
        g.all_vars[name] = Array_Var{
            alloca       = ptr,
            capacity     = fa.size,
            elem_type    = elem_ir,
            is_utf8      = is_utf8,
            has_sentinel = fa.has_sentinel,
            sentinel     = fa.sentinel,
        }
        return
    }

    // Runtime-counted slice: gen_expr_take already built the slice header.
    // Bind Slice_Var pointing at it.
    if sl, ok := rt.(^Type_Slice); ok {
        elem_ir := llvm_type_from_checker(sl.elem)
        is_utf8 := false
        if _, u_ok := sl.elem.(Type_Utf8); u_ok { is_utf8 = true }
        g.all_vars[name] = Slice_Var{
            alloca       = ptr,
            elem_type    = elem_ir,
            is_utf8      = is_utf8,
            has_sentinel = sl.has_sentinel,
        }
        return
    }

    // Struct / class: bind Struct_Var whose alloca is the take result.
    if sd := as_scope_body(rt); sd != nil {
        g.all_vars[name] = Struct_Var{
            alloca      = ptr,
            struct_name = sd.name,
        }
        return
    }

    // Scalar: alias the storage memory through Scalar_Var{alloca: ptr}. Reads
    // load from ptr, writes store to ptr — no fresh stack slot.
    g.all_vars[name] = Scalar_Var{alloca = ptr}
}

// ---------------------------------------------------------------------------
// Multi-assignment: x, y := get_pair()
// ---------------------------------------------------------------------------

gen_multi_return_assign :: proc(g: ^Codegen, s: ^Stmt_Multi_Return_Assign) {
    // Multi-return function call: x, y := call()
    if len(s.values) == 0 {
        codegen_fatal(g, s.span, "multi-assign has no RHS values")
    }
    call, call_ok := s.values[0].(^Expr_Call)
    if !call_ok {
        codegen_fatal(g, s.span, "multi-assign RHS must be a function call")
    }

    // Look up the function's tuple return type BEFORE calling gen_call
    tuple_type: ^Type_Tuple = nil
    if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok {
        tuple_type = info.ret_tuple
    }

    gen_call(g, call)

    if len(g.tuple_result_ptrs) == 0 {
        codegen_fatal(g, s.span, "multi-assign call did not produce tuple results")
    }

    for name, i in s.names {
        if i >= len(g.tuple_result_ptrs) { break }

        elem_type := g.tuple_result_types[i]
        src_ptr := g.tuple_result_ptrs[i]

        // Struct element: alloca the struct, memcpy from sret slot, register
        // as Struct_Var so subsequent field access (info.size) works.
        if tuple_type != nil && i < len(tuple_type.elems) {
            if sd := as_struct_body(distinct_base(tuple_type.elems[i])); sd != nil {
                if name == "" {
                    codegen_fatal(g, s.span, "struct in multi-return can't target an expression yet")
                }
                alloca_name: string
                if existing, ok := get_struct(g, name); ok {
                    alloca_name = existing.alloca
                } else {
                    alloca_name = fmt.tprintf("%%%s", name)
                    emit(g, "  %s = alloca %s", alloca_name, elem_type)
                    g.all_vars[name] = Struct_Var{
                        alloca      = alloca_name,
                        struct_name = sd.name,
                    }
                }
                struct_llvm := struct_llvm_name(sd.name)
                emit_struct_copy(g, sd, struct_llvm, src_ptr, alloca_name)
                continue
            }
        }

        val := fresh_tmp(g)
        emit(g, "  %s = load %s, ptr %s", val, elem_type, src_ptr)

        // Expression target (field access, index, deref)
        if name == "" && i < len(s.targets) && s.targets[i] != nil {
            gen_multi_return_store_target(g, s.targets[i], elem_type, val)
            continue
        }

        // Bare identifier target
        if existing, ok := get_scalar(g, name); ok {
            emit(g, "  store %s %s, ptr %s", elem_type, val, existing)
        } else {
            alloca_name := fmt.tprintf("%%%s", name)
            emit(g, "  %s = alloca %s", alloca_name, elem_type)
            emit(g, "  store %s %s, ptr %s", elem_type, val, alloca_name)
            g.all_vars[name] = Scalar_Var{alloca_name}
        }
    }

    clear(&g.tuple_result_ptrs)
    clear(&g.tuple_result_types)
}

// Store a multi-return element into an expression target (field access, index, deref).
gen_multi_return_store_target :: proc(g: ^Codegen, target: Expr, elem_type: string, val: string) {
    #partial switch t in target {
    case ^Expr_Field_Access:
        st, base_ptr, found := resolve_lhs_struct(g, t.expr)
        if !found {
            codegen_fatal(g, t.span, "multi-return target field access — cannot resolve struct")
        }
        st_llvm := struct_llvm_name(struct_key(st))
        idx := struct_field_index(st, t.field)
        if idx < 0 {
            codegen_fatal(g, t.span, "struct '%s' has no field '%s'", struct_key(st), t.field)
        }
        gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", gep, st_llvm, base_ptr, idx)
        emit(g, "  store %s %s, ptr %s", elem_type, val, gep)
    case ^Expr_Index:
        codegen_fatal(g, t.span, "index target in multi-return assign not yet supported")
    case ^Expr_Unary:
        if t.op == .Caret {
            // Deref target: store through pointer
            ptr_val := gen_expr(g, t.operand)
            emit(g, "  store %s %s, ptr %s", elem_type, val, ptr_val)
        } else {
            codegen_fatal(g, t.span, "unary op '%v' is not a valid multi-return target", t.op)
        }
    case:
        codegen_fatal(g, {}, "unsupported multi-return target expression")
    }
}

// ---------------------------------------------------------------------------
// Return statement codegen
// ---------------------------------------------------------------------------

emit_ret_void :: proc(g: ^Codegen) {
    emit_return_resets(g)
    emit(g, "  ret void")
}

// Tuple return: store each value into its sret param.
gen_return_tuple :: proc(g: ^Codegen, s: Stmt_Return) {
    for val, i in s.values {
        resolved_type := distinct_base(g.ret_tuple.elems[i])
        elem_type := llvm_type_from_checker(g.ret_tuple.elems[i])
        // Array/fixed-array returns: memcpy from alloca to sret
        if fa, fa_ok := resolved_type.(^Type_Fixed_Array); fa_ok {
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if av, av_ok := get_array(g, ident.name); av_ok {
                    arr_size := fa.size * checker_type_byte_size(fa.elem)
                    sret_ptr := fmt.tprintf("%%sret.%d", i)
                    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", sret_ptr, av.alloca, arr_size)
                    continue
                }
            }
        }
        // Struct returns: field-wise copy from src alloca to sret (can't use
        // `store %struct %ptr` — the value operand must be a struct, not a ptr).
        if sd := as_struct_body(resolved_type); sd != nil {
            sret_ptr := fmt.tprintf("%%sret.%d", i)
            struct_llvm := struct_llvm_name(sd.name)
            if lit, lit_ok := val.(^Expr_Struct_Literal); lit_ok {
                emit_struct_literal_into(g, sd, struct_llvm, sret_ptr, lit)
                continue
            }
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if src_sv, sv_ok := get_struct(g, ident.name); sv_ok {
                    emit_struct_copy(g, sd, struct_llvm, src_sv.alloca, sret_ptr)
                    continue
                }
            }
            // Fallback: gen_expr yields a pointer to the struct
            src_ptr := gen_expr(g, val, elem_type)
            emit_struct_copy(g, sd, struct_llvm, src_ptr, sret_ptr)
            continue
        }
        // Slice returns: memcpy the slice descriptor (ptr + len + cap = 24 bytes).
        // The single-slice-return path (gen_return_slice) does the same; this
        // mirrors it for slices as one element of a multi-return tuple. The
        // bare scalar fallback below would otherwise emit
        // `store { ptr, i64 } <alloca-ptr>, ptr %sret.N` which is invalid IR
        // (alloca-ptr is `ptr`, not the slice descriptor value).
        if _, sl_ok := resolved_type.(^Type_Slice); sl_ok {
            sret_ptr := fmt.tprintf("%%sret.%d", i)
            src: string
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                    src = sv.alloca
                }
            }
            if src == "" {
                src = gen_expr(g, val, elem_type)
            }
            emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", sret_ptr, src)
            continue
        }
        v := gen_expr(g, val, elem_type)
        emit(g, "  store %s %s, ptr %%sret.%d", elem_type, v, i)
    }
    emit_ret_void(g)
}

// Write a struct literal (explicit fields + defaults) into a destination pointer.
// Shared by single-struct and tuple-with-struct returns.
emit_struct_literal_into :: proc(g: ^Codegen, sd: ^Scope_Body, struct_llvm: string, dst_ptr: string, lit: ^Expr_Struct_Literal) {
    for field in lit.fields {
        idx := struct_field_index(sd, field.name)
        if idx < 0 { continue }
        ft := field_ir_type(&sd.fields[idx])
        val := gen_expr(g, field.value, ft)
        gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", gep, struct_llvm, dst_ptr, idx)
        emit(g, "  store %s %s, ptr %s", ft, val, gep)
    }
    // Fill in defaults (skip for {0} zero-init)
    if !lit.zero_init {
        for &sdf, sdf_i in sd.fields {
            if sdf.default_value == nil { continue }
            provided := false
            for field in lit.fields {
                if field.name == sdf.name { provided = true; break }
            }
            if !provided {
                sdf_ft := field_ir_type(&sdf)
                val := gen_expr(g, sdf.default_value, sdf_ft)
                gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", gep, struct_llvm, dst_ptr, sdf_i)
                emit(g, "  store %s %s, ptr %s", sdf_ft, val, gep)
            }
        }
    }
}

// Struct return: copy value into %sret.
gen_return_struct :: proc(g: ^Codegen, s: Stmt_Return, sret_sv: Struct_Var) {
    sret_st, _ := lookup_struct(g, sret_sv.struct_name)
    sret_llvm := struct_llvm_name(sret_sv.struct_name)
    sret_ptr := sret_sv.alloca
    ret_val := len(s.values) > 0 ? s.values[0] : nil

    if lit, lit_ok := ret_val.(^Expr_Struct_Literal); lit_ok {
        // Case A: returning a struct literal. Route through the unified store
        // primitive so positional literals, slice fields (auto-coerced from
        // local fixed arrays), and embedded structs all behave correctly.
        gen_store_struct_into(g, sret_ptr, sret_st, lit)
    } else if ident, id_ok := ret_val.(^Expr_Ident); id_ok {
        // Case B: returning a struct variable
        if src_sv, sv_ok := get_struct(g, ident.name); sv_ok {
            emit_struct_copy(g, sret_st, sret_llvm, src_sv.alloca, sret_ptr)
        }
    } else if call, call_ok := ret_val.(^Expr_Call); call_ok {
        // Case C: returning result of another struct-returning call
        result_ptr := gen_call(g, call)
        emit_struct_copy(g, sret_st, sret_llvm, result_ptr, sret_ptr)
    }
    emit_ret_void(g)
}

// Array return: copy array data into sret.
gen_return_array :: proc(g: ^Codegen, s: Stmt_Return, sret_av_in: Array_Var) {
    sret_av := sret_av_in
    sret_type := fmt.tprintf("[%d x %s]", sret_av.capacity, sret_av.elem_type)
    arr_ret_val := len(s.values) > 0 ? s.values[0] : nil

    if ident, id_ok := arr_ret_val.(^Expr_Ident); id_ok {
        // Case A: returning an array variable (NRVO if aliased to sret, else loop-copy)
        if src_av, av_ok := get_array(g, ident.name); av_ok && src_av.alloca != sret_av.alloca {
            src_type := array_var_type(&src_av)
            copy_bound := fmt.tprintf("%d", src_av.capacity)

            cond_label := fresh_label(g, "ret.copy.cond")
            body_label := fresh_label(g, "ret.copy.body")
            end_label  := fresh_label(g, "ret.copy.end")

            idx_ptr := fresh_tmp(g)
            emit(g, "  %s = alloca i64", idx_ptr)
            emit(g, "  store i64 0, ptr %s", idx_ptr)
            emit(g, "  br label %%%s", cond_label)

            emit(g, "%s:", cond_label)
            idx := fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", idx, idx_ptr)
            cmp := fresh_tmp(g)
            emit(g, "  %s = icmp slt i64 %s, %s", cmp, idx, copy_bound)
            emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_label, end_label)

            emit(g, "%s:", body_label)
            idx2 := fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", idx2, idx_ptr)
            src_gep := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", src_gep, src_type, src_av.alloca, idx2)
            val := fresh_tmp(g)
            emit(g, "  %s = load %s, ptr %s", val, sret_av.elem_type, src_gep)
            dst_gep := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", dst_gep, sret_type, sret_av.alloca, idx2)
            emit(g, "  store %s %s, ptr %s", sret_av.elem_type, val, dst_gep)
            next := fresh_tmp(g)
            emit(g, "  %s = add i64 %s, 1", next, idx2)
            emit(g, "  store i64 %s, ptr %s", next, idx_ptr)
            emit(g, "  br label %%%s", cond_label)

            emit(g, "%s:", end_label)
        }
    } else if arr_lit, lit_ok := arr_ret_val.(^Expr_Array); lit_ok {
        // Case B: returning an array literal
        for elem, i in arr_lit.elements {
            val := gen_expr(g, elem, sret_av.elem_type)
            gep := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", gep, sret_type, sret_av.alloca, i)
            emit(g, "  store %s %s, ptr %s", sret_av.elem_type, val, gep)
        }
    } else if call, call_ok := arr_ret_val.(^Expr_Call); call_ok {
        // Case C: returning result of another array-returning call
        // Pass sret pointers directly to the inner call — no intermediate copy
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok && info.ret_array_cap > 0 {
            gen_call_into_array(g, call, &sret_av, &info)
        } else {
            gen_call(g, call)
        }
    }
    emit_ret_void(g)
}

// Slice return: copy { ptr, i64 } into sret.
gen_return_slice :: proc(g: ^Codegen, s: Stmt_Return, sret_slv: Slice_Var) {
    ret_val := len(s.values) > 0 ? s.values[0] : nil
    src: string
    if ident, id_ok := ret_val.(^Expr_Ident); id_ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            src = sv.alloca
        } else {
            src = gen_expr(g, ret_val)
        }
    } else if ret_val != nil {
        src = gen_expr(g, ret_val)
    }
    if src != "" {
        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", sret_slv.alloca, src)
    }
    emit_ret_void(g)
}

// Scalar return: convert value to declared return type if needed, then ret.
gen_return_scalar :: proc(g: ^Codegen, s: Stmt_Return) {
    val := gen_expr(g, s.values[0], g.current_ret_type)
    ret_type := expr_ir_type(g, s.values[0])
    if g.current_ret_type != "" && g.current_ret_type != ret_type {
        if g.current_ret_type == "ptr" && val == "0" {
            val = "null"
            ret_type = "ptr"
        } else if g.current_ret_type == "i64" && (ret_type == "i32" || ret_type == "i16" || ret_type == "i8") {
            conv := fresh_tmp(g)
            emit(g, "  %s = sext %s %s to i64", conv, ret_type, val)
            val = conv
        } else if g.current_ret_type == "double" && ret_type == "float" {
            conv := fresh_tmp(g)
            emit(g, "  %s = fpext float %s to double", conv, val)
            val = conv
        }
        ret_type = g.current_ret_type
    }
    emit_return_resets(g)
    emit(g, "  ret %s %s", ret_type, val)
}

gen_return :: proc(g: ^Codegen, s: Stmt_Return) {
    if g.ret_tuple != nil && len(s.values) > 1 {
        gen_return_tuple(g, s)
        return
    }
    if sret_sv, ok := get_struct(g, "__sret"); ok {
        gen_return_struct(g, s, sret_sv)
        return
    }
    if sret_av, ok := get_array(g, "__sret"); ok {
        gen_return_array(g, s, sret_av)
        return
    }
    if sret_slv, ok := get_slice(g, "__sret"); ok {
        gen_return_slice(g, s, sret_slv)
        return
    }
    if len(s.values) > 0 {
        gen_return_scalar(g, s)
        return
    }
    // Bare `return` in a void function — emit the terminator so the basic
    // block is well-formed. Without this, LLVM rejects the IR with
    // "expected instruction opcode" at whichever label follows.
    emit(g, "  ret void")
}
