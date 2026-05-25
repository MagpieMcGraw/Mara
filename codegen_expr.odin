package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Expression codegen
// ---------------------------------------------------------------------------

gen_expr :: proc(g: ^Codegen, expr: Expr, target_type: string = "") -> string {
    switch e in expr {
    case ^Expr_Number:
        // Resolve the effective IR type: target_type from context, or default
        tt := target_type
        if tt == "" {
            tt = e.is_float ? "double" : "i64"
        }
        // Read int_value (exact i64) for integer targets — e.value is f64
        // and loses precision above 2^53. e.value is authoritative for
        // float targets.
        switch tt {
        case "half":
            // LLVM half literals use the `0xH<4 hex>` form. Cast through f16
            // first to round to half precision.
            return fmt.tprintf("0xH%04X", transmute(u16)f16(e.value))
        case "float":
            return fmt.tprintf("0x%016X", transmute(u64)f64(f32(e.value)))
        case "double":
            return fmt.tprintf("%f", e.value)
        case "i8", "i16", "i32", "i64", "i128":
            return fmt.tprintf("%d", e.int_value)
        case:
            // Unknown target, fall back to literal kind
            if e.is_float {
                return fmt.tprintf("%f", e.value)
            }
            return fmt.tprintf("%d", e.int_value)
        }

    case ^Expr_Skip_Constructor:
        // `---` should never reach gen_expr as a value-producing expression.
        // Callers (gen_struct_assign, apply_struct_defaults, etc.) recognize
        // it as an opt-out marker before falling through to gen_expr. If we
        // get here, something forgot the check — emit zeroinitializer so the
        // IR is at least well-typed.
        return "zeroinitializer"

    case ^Expr_Bool:
        // When target is an integer type, emit 0/1 instead of false/true (i1 literals)
        if target_type == "i64" || target_type == "i32" || target_type == "i16" || target_type == "i8" {
            return e.value ? "1" : "0"
        }
        return e.value ? "true" : "false"

    case ^Expr_String:
        global_name, byte_len := get_string_literal(g, e.value)
        tmp := fresh_tmp(g)
        emit_string_gep(g, tmp, byte_len, global_name)
        return tmp

    case ^Expr_Char:
        return fmt.tprintf("%d", int(e.value))

    case ^Expr_Ident:
        // Null pointer literal — the only legal way to spell a null pointer
        // in Mara source. Lowers to LLVM's `null` keyword unchanged.
        if e.name == "void" {
            return "null"
        }
        // Type checker may have rewritten this ident into a richer expression
        // (namespace-match subject-field access, etc.). Route through if so.
        if e.desugared != nil {
            return gen_expr(g, e.desugared, target_type)
        }
        // Check resolved annotation on the node (populated by type checker)
        if ev, ev_ok := e.resolved.(Resolved_Enum_Variant); ev_ok {
            return fmt.tprintf("%d", ev.value)
        }
        // Infer-type constant: emit inline with target type
        if const_expr, ok := g.checked.table.constants[e.name]; ok {
            return gen_expr(g, const_expr, target_type)
        }
        // SSA-bound synthetic binding (compound assignment's pre-loaded LHS):
        // the value already lives in a named SSA reg, no load needed.
        if entry, ok := g.all_vars[e.name]; ok {
            if sv, sv_ok := entry.(SSA_Var); sv_ok {
                return sv.ssa
            }
        }
        // Struct variable: return the pointer directly (no load — structs are always ptrs)
        if sv, sv_ok := get_struct(g, e.name); sv_ok {
            return sv.alloca
        }
        // Union variable: return the pointer directly (like structs — unions are aggregates)
        if uv, uv_ok := get_union(g, e.name); uv_ok {
            return uv.alloca
        }
        // Array variable: return the data pointer directly
        if av, av_ok := get_array(g, e.name); av_ok {
            return av.alloca
        }
        // Slice variable: return the alloca pointer (like structs — { ptr, i64 })
        if slv, slv_ok := get_slice(g, e.name); slv_ok {
            return slv.alloca
        }
        alloca_name, ok := get_scalar(g, e.name)
        if !ok {
            // Function reference: emit the function's IR address as a ptr value
            if tf, is_func := e.type_.(^Type_Scope); is_func && tf.kind == .Fun {
                // Use resolved flat name if available (e.g. "test_fn_values_add")
                fn_name := e.name
                if rf, rf_ok := e.resolved.(Resolved_Func); rf_ok {
                    fn_name = rf.name
                }
                ir_name := mara_fn_name(g, fn_name)
                if fir, fir_ok := foreign_ir_name(g, fn_name); fir_ok {
                    ir_name = fir
                }
                return ir_name
            }
            codegen_fatal(g, e.span, CODE_UNDEFINED_VARIABLE, e.name)
        }
        tmp := fresh_tmp(g)
        ir_type := "i64"
        if e.type_ != nil && !is_untyped(e.type_) {
            ir_type = llvm_type_from_checker(e.type_)
        }
        emit_load_into(g, tmp, ir_type, alloca_name)
        return tmp

    case ^Expr_Unary:
        #partial switch e.op {
        case .Ampersand:
            // Address-of: return the alloca pointer without loading
            if ident, ok := e.operand.(^Expr_Ident); ok {
                // For struct vars, return the alloca directly
                if sv, sv_ok := get_struct(g, ident.name); sv_ok {
                    return sv.alloca
                }
                // For union vars, return the alloca directly
                if uv, uv_ok := get_union(g, ident.name); uv_ok {
                    return uv.alloca
                }
                // For slice vars, return the slice header alloca (the slice
                // is already a fat-pointer ref; `&` is just for readability).
                if slv, slv_ok := get_slice(g, ident.name); slv_ok {
                    return slv.alloca
                }
                if alloca_name, v_ok := get_scalar(g, ident.name); v_ok {
                    return alloca_name
                }
                // `&program` — the compiler-managed program global is stored
                // at @__mara_program_storage; the address is the storage label.
                // Used in cross-DLL handover (`game_run(&program, ...)`).
                if ident.name == "program" {
                    return "@__mara_program_storage"
                }
            }
            // Address-of a field: emit GEP but don't load
            if fa, ok := e.operand.(^Expr_Field_Access); ok {
                return gen_field_address(g, fa)
            }
            // Address-of an array element: emit GEP but don't load
            if idx, ok := e.operand.(^Expr_Index); ok {
                if e.byte_view_size > 0 {
                    return gen_byte_view_address(g, idx, e.byte_view_size)
                }
                return gen_index_address(g, idx)
            }
            codegen_fatal(g, e.span, CODE_CANNOT_TAKE_ADDRESS_EXPRESSION)
        case .Caret:
            // Dereference: load through pointer
            ptr_val := gen_expr(g, e.operand)

            // Null pointer check
            deref_name := "ptr"
            if ident, ok := e.operand.(^Expr_Ident); ok {
                deref_name = ident.name
            }
            emit_null_check(g, ptr_val, deref_name, e.span)

            // Determine what type to load from the operand's type annotation
            deref_type := "i64"
            operand_type := expr_type(e.operand)
            if pt, pt_ok := operand_type.(^Type_Ptr); pt_ok {
                if as_struct_body(pt.elem) != nil {
                    // Dereferencing a ^Struct — return the pointer itself,
                    // since struct values are represented as pointers
                    return ptr_val
                }
                if !is_untyped(pt.elem) {
                    deref_type = llvm_type_from_checker(pt.elem)
                }
            }
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, deref_type, ptr_val)
            return tmp
        case .Minus:
            // Overloaded unary `-` (e.g. `-vec3`): synthesize a 1-arg call to
            // the resolved function. Same shape as gen_binary's overload path.
            if rf, rf_ok := e.overload_fn.?; rf_ok {
                call := new(Expr_Call)
                call.name = rf.name
                append(&call.args, e.operand)
                call.span = e.span
                call.type_ = e.type_
                call.resolved_func = rf
                return gen_call(g, call)
            }
            operand := gen_expr(g, e.operand, target_type)
            tmp := fresh_tmp(g)
            op_type := target_type != "" ? target_type : expr_ir_type(g, e.operand)
            if op_type == "double" || op_type == "float" {
                emit(g, "  %s = fneg %s %s", tmp, op_type, operand)
            } else {
                emit(g, "  %s = sub %s 0, %s", tmp, op_type, operand)
            }
            return tmp
        case .Not:
            operand := gen_expr(g, e.operand)
            tmp := fresh_tmp(g)
            emit(g, "  %s = xor i1 %s, true", tmp, operand)
            return tmp
        case .Tilde:
            operand := gen_expr(g, e.operand, target_type)
            tmp := fresh_tmp(g)
            op_type := target_type != "" ? target_type : expr_ir_type(g, e.operand)
            emit(g, "  %s = xor %s %s, -1", tmp, op_type, operand)
            return tmp
        }

    case ^Expr_Binary:
        return gen_binary(g, e, target_type)

    case ^Expr_Call:
        return gen_call(g, e)

    case ^Expr_Array:
        // Try to emit as an LLVM inline constant (works for literals)
        fa_type := e.type_
        // Unwrap distinct type to get the underlying fixed array
        if dt, dt_ok := fa_type.(^Type_Distinct); dt_ok {
            fa_type = dt.base_type
        }
        if fa, fa_ok := fa_type.(^Type_Fixed_Array); fa_ok {
            elem_t := llvm_type_from_checker(fa.elem)
            // If element type is inferred and we have a target type, extract element type from it
            // e.g. target_type="[4 x float]" → elem_t="float"
            if is_infer(fa.elem) && target_type != "" {
                if x_idx := strings.index(target_type, " x "); x_idx >= 0 {
                    rest := target_type[x_idx+3:]
                    if close := strings.index_byte(rest, ']'); close >= 0 {
                        elem_t = rest[:close]
                    }
                }
            }
            parts: [dynamic]string
            for elem in e.elements {
                val := gen_expr(g, elem, elem_t)
                append(&parts, fmt.tprintf("%s %s", elem_t, val))
            }
            // Pad remaining elements with zeroinitializer
            for _ in len(e.elements)..<fa.size {
                append(&parts, fmt.tprintf("%s 0", elem_t))
            }
            return fmt.tprintf("[%s]", strings.join(parts[:], ", "))
        }
        return "zeroinitializer"
    case ^Expr_Index:
        return gen_index_expr(g, e)
    case ^Expr_Slice:
        return gen_slice_expr(g, e)
    case ^Expr_Struct_Literal:
        // Distinct-fixed-array literal (Quat{...} / Vec3{...}): emit as an inline
        // LLVM array constant, with nil slots rendered as `elem 0`.
        if e.array_values != nil {
            fa_type := e.type_
            if dt, dt_ok := fa_type.(^Type_Distinct); dt_ok {
                fa_type = dt.base_type
            }
            if fa, fa_ok := fa_type.(^Type_Fixed_Array); fa_ok {
                elem_t := llvm_type_from_checker(fa.elem)
                zero_lit := elem_t == "float" || elem_t == "double" ? "0.0" : "0"
                parts: [dynamic]string
                for elem in e.array_values {
                    if elem == nil {
                        append(&parts, fmt.tprintf("%s %s", elem_t, zero_lit))
                    } else {
                        val := gen_expr(g, elem, elem_t)
                        append(&parts, fmt.tprintf("%s %s", elem_t, val))
                    }
                }
                return fmt.tprintf("[%s]", strings.join(parts[:], ", "))
            }
        }
        // Empty struct/array literal or {0} used as zero-initializer (e.g. obj.field = {})
        if (len(e.fields) == 0 || e.zero_init) && (strings.has_prefix(target_type, "%class.") || strings.has_prefix(target_type, "[")) {
            return "zeroinitializer"
        }
        // Standalone struct literal (not in typed assignment) — can't determine type
        return "0"
    case ^Expr_Field_Access:
        return gen_field_access(g, e)
    case ^Expr_Size_Of:
        ir_type := llvm_type_from_checker(e.resolved_type)
        size := elem_byte_size(ir_type, g.checked)
        return fmt.tprintf("%d", size)
    case ^Expr_Take:
        return gen_expr_take(g, e)
    case ^Expr_If:
        return gen_if_expr(g, e, target_type)
    case ^Expr_Compiler_Intrinsic:
        if e.kind == .Web || e.kind == .Native ||
           e.kind == .Windows || e.kind == .Linux || e.kind == .Mac {
            return "1" if e.bool_value else "0"
        }
        global_name, byte_len := get_string_literal(g, e.resolved_value)
        tmp := fresh_tmp(g)
        emit_string_gep(g, tmp, byte_len, global_name)
        return tmp
    case ^Expr_Include:
        // Include expressions are desugared before codegen — should never reach here
        return "0"
    case ^Expr_Type_Name:
        // Bare type-keyword as a value flows through generic-arg binding at
        // type-check time and never produces a runtime value. If one reaches
        // codegen it's a misuse (e.g. assigning a type-name to a variable);
        // emit a placeholder so the generated IR still parses.
        return "0"
    case ^Expr_Tuple_Default:
        return gen_tuple_default(g, e)
    case ^Expr_Self:
        // The constructor's destination pointer — pre-bind_field_var at
        // codegen_fn.odin GEPs every field off %sret, so %sret IS the
        // under-construction instance pointer.
        return "%sret"
    }
    return "0"
}

// Evaluate one binding's slot of a default that was parsed as `a, b := X`.
// When X is a tuple-returning call this is true destructure: evaluate the
// source once at this call site (cached per-source-ptr) and load slot i.
// When X is anything else (literal, scalar call, etc.) the binding-group
// is effectively broadcast — just re-evaluate the source per binding, same
// as if the parser had cloned X into each binding's default_value.
gen_tuple_default :: proc(g: ^Codegen, e: ^Expr_Tuple_Default) -> string {
    call, is_call := e.source.(^Expr_Call)
    is_tuple := false
    if is_call {
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok {
            is_tuple = info.ret_tuple != nil
        }
    }
    if !is_tuple {
        // Broadcast fallback: evaluate the source for this binding. The
        // same source Expr is shared by all bindings in the group but
        // gen_expr emits fresh IR each time, matching the historical
        // clone-per-name behaviour.
        return gen_expr(g, e.source)
    }

    // Destructure path: dedup by source ptr within this call site.
    src_key := rawptr(call)
    if g.tuple_default_cache == nil {
        g.tuple_default_cache = make(map[rawptr]Tuple_Default_Entry)
    }
    entry, hit := g.tuple_default_cache[src_key]
    if !hit {
        gen_call(g, call)
        // gen_call clears+repopulates g.tuple_result_ptrs/types per call;
        // snapshot them now so subsequent gen_call invocations in this
        // arg list don't overwrite our entry.
        ptrs:  [dynamic]string
        types: [dynamic]string
        for p in g.tuple_result_ptrs  { append(&ptrs, p) }
        for t in g.tuple_result_types { append(&types, t) }
        entry = Tuple_Default_Entry{ptrs = ptrs, types = types}
        g.tuple_default_cache[src_key] = entry
    }
    if e.index < 0 || e.index >= len(entry.ptrs) {
        codegen_fatal(g, e.span, CODE_TUPLE_DEFAULT_INDEX_OUT_RANGE, e.index)
    }
    val := fresh_tmp(g)
    emit_load_into(g, val, entry.types[e.index], entry.ptrs[e.index])
    return val
}

// ---------------------------------------------------------------------------
// If-expression codegen: if cond do then_expr else else_expr
// ---------------------------------------------------------------------------

gen_if_expr :: proc(g: ^Codegen, e: ^Expr_If, target_type: string = "") -> string {
    cond_val := gen_expr(g, e.condition)
    then_label := fresh_label(g, "ifx.then")
    else_label := fresh_label(g, "ifx.else")
    end_label  := fresh_label(g, "ifx.end")

    emit_cond_br(g, cond_val, then_label, else_label)

    emit_raw(g, fmt.tprintf("%s:", then_label))
    then_val := gen_expr(g, e.then_expr, target_type)
    emit_br(g, end_label)

    emit_raw(g, fmt.tprintf("%s:", else_label))
    else_val := gen_expr(g, e.else_expr, target_type)
    emit_br(g, end_label)

    emit_raw(g, fmt.tprintf("%s:", end_label))
    result := fresh_tmp(g)
    result_type := target_type != "" ? target_type : expr_ir_type(g, e.then_expr)
    emit(g, "  %s = phi %s [ %s, %%%s ], [ %s, %%%s ]",
        result, result_type, then_val, then_label, else_val, else_label)
    return result
}

// ---------------------------------------------------------------------------
// Binary expression codegen
// ---------------------------------------------------------------------------

// Resolve the IR type for a binary operation.
// Priority: target_type from context > concrete operand > defaults.
// Comparisons (==, !=, <, <=, >, >=) always yield i1 regardless of operand
// width, so the target hint (the result type) must NOT override operand type.
resolve_binary_type :: proc(g: ^Codegen, e: ^Expr_Binary, target_type: string) -> string {
    is_comparison := false
    #partial switch e.op {
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
        is_comparison = true
    }
    if target_type != "" && !is_comparison { return target_type }
    left_type := expr_ir_type(g, e.left)
    right_type := expr_ir_type(g, e.right)
    left_infer := is_infer_expr(g, e.left)
    right_infer := is_infer_expr(g, e.right)
    if !left_infer { return left_type }
    if !right_infer { return right_type }
    // Both infer — use left's default
    return left_type
}

gen_binary :: proc(g: ^Codegen, e: ^Expr_Binary, target_type: string = "") -> string {
    // Overloaded operator: delegate to function call
    if rf, rf_ok := e.overload_fn.?; rf_ok {
        // Pool routing for `&pool_slice + call_with_escape()`: detect the
        // pattern, set the pool ctx so the call's escape args carve from it
        // instead of fresh allocas. Without this, alloca-hoist would make
        // every loop iteration share one sibling buffer.
        prev_pool := g.escape_pool_alloca
        defer g.escape_pool_alloca = prev_pool
        if un, un_ok := e.left.(^Expr_Unary); un_ok && un.op == .Ampersand {
            if ident, id_ok := un.operand.(^Expr_Ident); id_ok {
                if sv, sv_ok := get_slice(g, ident.name); sv_ok && sv.pool_alloca != "" {
                    if call_rhs, call_ok := e.right.(^Expr_Call); call_ok {
                        if info, info_ok := lookup_fun_info(g, call_resolved_name(call_rhs)); info_ok && len(info.escape_locals) > 0 {
                            g.escape_pool_alloca = sv.pool_alloca
                        }
                    }
                }
            }
        }
        call := new(Expr_Call)
        call.name = rf.name
        append(&call.args, e.left)
        append(&call.args, e.right)
        call.span = e.span
        call.type_ = e.type_
        call.resolved_func = rf
        return gen_call(g, call)
    }

    // Short-circuit for and/or
    if e.op == .And {
        return gen_short_circuit_and(g, e)
    }
    if e.op == .Or {
        return gen_short_circuit_or(g, e)
    }

    // Resolve the working IR type: target_type > concrete side > defaults
    ir_type := resolve_binary_type(g, e, target_type)

    left := gen_expr(g, e.left, ir_type)
    right := gen_expr(g, e.right, ir_type)
    tmp := fresh_tmp(g)

    is_float := ir_type == "double" || ir_type == "float" || ir_type == "half"

    if is_float {
        #partial switch e.op {
        case .Plus:
            emit(g, "  %s = fadd %s %s, %s", tmp, ir_type, left, right)
        case .Minus:
            emit(g, "  %s = fsub %s %s, %s", tmp, ir_type, left, right)
        case .Star:
            emit(g, "  %s = fmul %s %s, %s", tmp, ir_type, left, right)
        case .Slash:
            emit(g, "  %s = fdiv %s %s, %s", tmp, ir_type, left, right)
        case .Modulo:
            emit(g, "  %s = frem %s %s, %s", tmp, ir_type, left, right)
        case .Equal_Equal:
            emit(g, "  %s = fcmp oeq %s %s, %s", tmp, ir_type, left, right)
        case .Not_Equal:
            emit(g, "  %s = fcmp une %s %s, %s", tmp, ir_type, left, right)
        case .Less:
            emit(g, "  %s = fcmp olt %s %s, %s", tmp, ir_type, left, right)
        case .Less_Equal:
            emit(g, "  %s = fcmp ole %s %s, %s", tmp, ir_type, left, right)
        case .Greater:
            emit(g, "  %s = fcmp ogt %s %s, %s", tmp, ir_type, left, right)
        case .Greater_Equal:
            emit(g, "  %s = fcmp oge %s %s, %s", tmp, ir_type, left, right)
        case:
            emit(g, "  %s = fadd %s %s, %s", tmp, ir_type, left, right)
        }
    } else {
        // Signedness flows from the resolved type. For arithmetic, e.type_ is
        // the operand type (catches the literal-on-literal case where both
        // operands are infer-typed). For comparisons, e.type_ is bool, so we
        // fall back to operand types.
        is_unsigned := false
        if n, ok := distinct_base(e.type_).(Type_Numeric); ok && n.kind == .Unsigned {
            is_unsigned = true
        } else if n, ok := distinct_base(expr_type(e.left)).(Type_Numeric); ok && n.kind == .Unsigned {
            is_unsigned = true
        } else if n, ok := distinct_base(expr_type(e.right)).(Type_Numeric); ok && n.kind == .Unsigned {
            is_unsigned = true
        }
        #partial switch e.op {
        case .Plus:
            tmp = emit_checked_arith(g, is_unsigned ? "uadd" : "sadd", ir_type, left, right)
        case .Minus:
            tmp = emit_checked_arith(g, is_unsigned ? "usub" : "ssub", ir_type, left, right)
        case .Star:
            tmp = emit_checked_arith(g, is_unsigned ? "umul" : "smul", ir_type, left, right)
        case .Slash:
            emit_div_zero_check(g, right, ir_type)
            emit(g, "  %s = %s %s %s, %s", tmp, is_unsigned ? "udiv" : "sdiv", ir_type, left, right)
        case .Modulo:
            emit_div_zero_check(g, right, ir_type)
            emit(g, "  %s = %s %s %s, %s", tmp, is_unsigned ? "urem" : "srem", ir_type, left, right)
        case .Equal_Equal:
            emit(g, "  %s = icmp eq %s %s, %s", tmp, ir_type, left, right)
        case .Not_Equal:
            emit(g, "  %s = icmp ne %s %s, %s", tmp, ir_type, left, right)
        case .Less:
            emit(g, "  %s = icmp %s %s %s, %s", tmp, is_unsigned ? "ult" : "slt", ir_type, left, right)
        case .Less_Equal:
            emit(g, "  %s = icmp %s %s %s, %s", tmp, is_unsigned ? "ule" : "sle", ir_type, left, right)
        case .Greater:
            emit(g, "  %s = icmp %s %s %s, %s", tmp, is_unsigned ? "ugt" : "sgt", ir_type, left, right)
        case .Greater_Equal:
            emit(g, "  %s = icmp %s %s %s, %s", tmp, is_unsigned ? "uge" : "sge", ir_type, left, right)
        case .Ampersand:
            emit(g, "  %s = and %s %s, %s", tmp, ir_type, left, right)
        case .Pipe:
            emit(g, "  %s = or %s %s, %s", tmp, ir_type, left, right)
        case .Tilde:
            emit(g, "  %s = xor %s %s, %s", tmp, ir_type, left, right)
        case .Shift_Left:
            emit(g, "  %s = shl %s %s, %s", tmp, ir_type, left, right)
        case .Shift_Right:
            emit(g, "  %s = %s %s %s, %s", tmp, is_unsigned ? "lshr" : "ashr", ir_type, left, right)
        case:
            emit(g, "  %s = add %s %s, %s", tmp, ir_type, left, right)
        }
    }

    return tmp
}

gen_short_circuit_and :: proc(g: ^Codegen, e: ^Expr_Binary) -> string {
    // Use alloca+store pattern to avoid PHI predecessor tracking issues
    result_ptr := fresh_tmp(g)
    emit_alloca(g, result_ptr, "i1")
    emit(g, "  store i1 false, ptr %s", result_ptr)

    left := gen_expr(g, e.left)

    rhs_label := fresh_label(g, "and.rhs")
    end_label := fresh_label(g, "and.end")

    emit_cond_br(g, left, rhs_label, end_label)

    emit_label(g, rhs_label)
    right := gen_expr(g, e.right)
    emit_store(g, "i1", right, result_ptr)
    emit_br(g, end_label)

    emit_label(g, end_label)
    result := fresh_tmp(g)
    emit_load_into(g, result, "i1", result_ptr)
    return result
}

gen_short_circuit_or :: proc(g: ^Codegen, e: ^Expr_Binary) -> string {
    // Use alloca+store pattern to avoid PHI predecessor tracking issues
    result_ptr := fresh_tmp(g)
    emit_alloca(g, result_ptr, "i1")
    emit(g, "  store i1 true, ptr %s", result_ptr)

    left := gen_expr(g, e.left)

    rhs_label := fresh_label(g, "or.rhs")
    end_label := fresh_label(g, "or.end")

    emit_cond_br(g, left, end_label, rhs_label)

    emit_label(g, rhs_label)
    right := gen_expr(g, e.right)
    emit_store(g, "i1", right, result_ptr)
    emit_br(g, end_label)

    emit_label(g, end_label)
    result := fresh_tmp(g)
    emit_load_into(g, result, "i1", result_ptr)
    return result
}

// ---------------------------------------------------------------------------
// Type cast codegen: i32(x), f64(x), etc.
// ---------------------------------------------------------------------------

cast_target_ir_type :: proc(name: string) -> (ir_type: string, is_float: bool, is_ptr: bool, ok: bool) {
    switch name {
    case "int", "i64":  return "i64", false, false, true
    case "uint", "u64": return "i64", false, false, true
    case "i128":        return "i128", false, false, true
    case "u128":        return "i128", false, false, true
    case "i32":         return "i32", false, false, true
    case "i16":         return "i16", false, false, true
    case "i8", "c8", "utf8": return "i8", false, false, true
    case "u32":         return "i32", false, false, true
    case "u16":         return "i16", false, false, true
    case "u8":          return "i8", false, false, true
    case "usize", "isize":
        // Word-sized: same flag the codegen uses for llvm_type_from_checker.
        return "i32" if word_size_is_32 else "i64", false, false, true
    case "f64":         return "double", true, false, true
    case "f32":         return "float", true, false, true
    case "f16":         return "half", true, false, true
    case "bool":        return "i1", false, false, true
    }
    return "", false, false, false
}

ir_type_bits :: proc(t: string) -> int {
    switch t {
    case "i1":     return 1
    case "i8":     return 8
    case "i16":    return 16
    case "i32":    return 32
    case "i64":    return 64
    case "i128":   return 128
    case "half":   return 16
    case "float":  return 32
    case "double": return 64
    }
    return 0
}

is_ir_float :: proc(t: string) -> bool {
    return t == "half" || t == "float" || t == "double"
}

is_unsigned_cast :: proc(name: string) -> bool {
    switch name {
    case "u8", "u16", "u32", "u64", "u128", "uint", "usize", "bool":
        return true
    }
    return false
}

gen_type_cast :: proc(g: ^Codegen, e: ^Expr_Call) -> (string, bool) {
    target, target_is_float, target_is_ptr, ok := cast_target_ir_type(e.name)
    if !ok { return "", false }
    if len(e.args) != 1 { return "0", true }

    src_type := expr_ir_type(g, e.args[0])
    src_is_float := is_ir_float(src_type)
    src_is_ptr := src_type == "ptr"

    // Evaluate the source expression in its native type
    val := gen_expr(g, e.args[0], src_type)

    // Same type → no-op
    if src_type == target {
        return val, true
    }

    tmp := fresh_tmp(g)

    // ptr → int
    if src_is_ptr && !target_is_ptr && !target_is_float {
        emit(g, "  %s = ptrtoint ptr %s to %s", tmp, val, target)
        return tmp, true
    }

    // int → ptr: disallowed for memory safety (rejected by type checker)

    // float → float
    if src_is_float && target_is_float {
        src_bits := ir_type_bits(src_type)
        tgt_bits := ir_type_bits(target)
        if src_bits < tgt_bits {
            emit(g, "  %s = fpext %s %s to %s", tmp, src_type, val, target)
        } else {
            emit(g, "  %s = fptrunc %s %s to %s", tmp, src_type, val, target)
        }
        return tmp, true
    }

    // float → int
    if src_is_float && !target_is_float {
        if is_unsigned_cast(e.name) {
            emit(g, "  %s = fptoui %s %s to %s", tmp, src_type, val, target)
        } else {
            emit(g, "  %s = fptosi %s %s to %s", tmp, src_type, val, target)
        }
        return tmp, true
    }

    // int → float
    if !src_is_float && target_is_float {
        // Source arg name determines signedness for sitofp vs uitofp
        // But we don't know the source signedness easily, default to signed
        emit(g, "  %s = sitofp %s %s to %s", tmp, src_type, val, target)
        return tmp, true
    }

    // int → int (or bool)
    src_bits := ir_type_bits(src_type)
    tgt_bits := ir_type_bits(target)
    if src_bits == tgt_bits {
        // Same width, just return the value (e.g. i32 signed vs unsigned)
        return val, true
    } else if src_bits < tgt_bits {
        if is_unsigned_cast(e.name) || src_type == "i1" {
            emit(g, "  %s = zext %s %s to %s", tmp, src_type, val, target)
        } else {
            emit(g, "  %s = sext %s %s to %s", tmp, src_type, val, target)
        }
    } else {
        emit(g, "  %s = trunc %s %s to %s", tmp, src_type, val, target)
    }
    return tmp, true
}

// ---------------------------------------------------------------------------
// Function call codegen
// ---------------------------------------------------------------------------

// Resolve any slice-coercible expression to a pointer to a slice descriptor.
// Handles fixed-array literal, fixed-array var/expr, array-class struct,
// existing slice var, and general slice expression. Returns the IR pointer
// to a `{ ptr, i64, i64 }` slice header — callers wrap as needed (arg
// strings, memcpy sources for struct field stores, etc.).
gen_slice_value_ptr :: proc(g: ^Codegen, arg: Expr) -> string {
    arg_checker_type := expr_type(arg)
    if fa, fa_ok := distinct_base(arg_checker_type).(^Type_Fixed_Array); fa_ok {
        // Array literal: materialize on stack, then build slice
        if al, al_ok := arg.(^Expr_Array); al_ok {
            elem_ir := llvm_type_from_checker(fa.elem)
            arr_type := fmt.tprintf("[%d x %s]", fa.size, elem_ir)
            arr_alloca := fresh_tmp(g)
            emit_alloca(g, arr_alloca, arr_type)
            total_bytes := fa.size * elem_byte_size(elem_ir, g.checked)
            emit_memset_zero(g, arr_alloca, total_bytes)
            for elem, ei in al.elements {
                val := gen_expr(g, elem, elem_ir)
                gep := fresh_tmp(g)
                emit_array_gep_const(g, gep, arr_type, arr_alloca, ei)
                emit_store(g, elem_ir, val, gep)
            }
            size_str := fmt.tprintf("%d", fa.size)
            return emit_build_temp_slice(g, arr_alloca, size_str, size_str)
        }
        val := gen_expr(g, arg)  // returns data_ptr for arrays
        len_val: string
        if fa.is_vla {
            len_val = "0"
            if ident, id_ok := arg.(^Expr_Ident); id_ok {
                if entry, av_ok := g.all_vars[ident.name]; av_ok {
                    if av, is_arr := entry.(Array_Var); is_arr && av.capacity_val != "" {
                        len_val = av.capacity_val
                    }
                }
            }
        } else {
            len_val = fmt.tprintf("%d", fa.size)
        }
        // Fixed-array → slice: populated view (len=N, cap=N). Fixed arrays
        // are populated buffers — coercing them gives a view the receiver
        // can iterate / index naturally. For a fresh-cursor scratch buffer,
        // declare `name : []T(N)` (a sized slice) instead of `name : [N]T`.
        return emit_build_temp_slice(g, val, len_val, len_val)
    }
    // Existing slice var: the alloca pointer is already a ptr-to-header.
    if ident, id_ok := arg.(^Expr_Ident); id_ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            return sv.alloca
        }
    }
    // General slice expression (e.g. arr[:], call returning slice):
    // gen_expr returns an alloca ptr to the slice header.
    return gen_expr(g, arg, SLICE_IR_TYPE)
}

// Build a slice-typed function argument string `ptr %hdr`. Slice params lower
// to pointer-to-header at the IR ABI; mutations propagate to the caller.
gen_slice_param_arg :: proc(g: ^Codegen, arg: Expr) -> string {
    return slice_arg_str(gen_slice_value_ptr(g, arg))
}

// Load an array value for passing by value to a [N x T] parameter.
// `val` is the result of `gen_expr(g, arg, pt)` and usually already points at the array data;
// this helper returns the loaded SSA value if a load is needed, or the original `val` otherwise.
gen_array_param_arg :: proc(g: ^Codegen, arg: Expr, pt: string, val: string) -> string {
    // String literal / intrinsic passed to array param: alloca + memset + memcpy + load.
    string_like_src := ""
    if str_lit, str_ok := arg.(^Expr_String); str_ok {
        string_like_src = str_lit.value
    } else if intrinsic, intr_ok := arg.(^Expr_Compiler_Intrinsic); intr_ok {
        string_like_src = intrinsic.resolved_value
    }
    if string_like_src != "" {
        global_name, byte_len := get_string_literal(g, string_like_src)
        src_ptr := fresh_tmp(g)
        emit_string_gep(g, src_ptr, byte_len, global_name)
        arr_alloca := fresh_tmp(g)
        emit_alloca(g, arr_alloca, pt)
        arr_cap, arr_elem, _ := parse_array_ir_type(pt)
        param_bytes := arr_cap * elem_byte_size(arr_elem, g.checked)
        emit_memset_zero(g, arr_alloca, param_bytes)
        emit_memcpy(g, arr_alloca, src_ptr, byte_len)
        loaded := fresh_tmp(g)
        emit_load_into(g, loaded, pt, arr_alloca)
        return loaded
    }
    // Ident / field access / call returning an array: `val` is a ptr to the data; load it.
    needs_load := false
    #partial switch a in arg {
    case ^Expr_Ident:
        _, needs_load = get_array(g, a.name)
    case ^Expr_Field_Access:
        _, needs_load = claim_field_array(g)
    case ^Expr_Call:
        _, needs_load = claim_call_result(g)
    case ^Expr_Binary:
        // Operator overload: gen_binary wraps the expression into an Expr_Call
        // and routes through gen_call, which set_call_results an Array_Var
        // for array-returning callees. We need to claim that result so the
        // ptr-to-array gets loaded into the array value the param expects.
        // Without this, `a * (b * c)` for a Mat4-returning `*` passes the
        // inner sret pointer where an `[N x T]` value is expected.
        if _, has_overload := a.overload_fn.?; has_overload {
            _, needs_load = claim_call_result(g)
        }
    case ^Expr_Unary:
        // Same situation for unary `-`: `-v3` resolved to vec3_negate gets
        // wrapped into a 1-arg Expr_Call. The ptr-to-array result needs the
        // same load so it can flow into a `[N x T]` param.
        if _, has_overload := a.overload_fn.?; has_overload {
            _, needs_load = claim_call_result(g)
        }
    }
    if needs_load {
        loaded := fresh_tmp(g)
        emit_load_into(g, loaded, pt, val)
        return loaded
    }
    return val
}

// Attempt to emit a call to an intrinsic function. Returns (value, true) on success.
// Returns ("", false) if the function isn't a recognised intrinsic (caller falls back to normal call path).
//
// The LLVM intrinsic mnemonic comes from the function's `intrinsic_name` (set
// by the parser from a `{ @llvm.<op>.<suffix> }` body). The type checker has
// already validated that the name is well-formed and matches the declared
// signature, so codegen just emits the call verbatim.
emit_intrinsic_call :: proc(g: ^Codegen, lookup_name: string, e: ^Expr_Call) -> (string, bool) {
    cf, cf_ok := g.checked.functions[lookup_name]
    if !cf_ok { return "", false }
    oi, is_intrinsic := cf.origin.(Origin_Intrinsic)
    if !is_intrinsic || oi.llvm_name == "" { return "", false }

    info, info_ok := lookup_fun_info(g, lookup_name)
    if !info_ok { return "", false }

    arg_strs: [dynamic]string
    for arg, i in e.args {
        pt := "i64"
        if i < len(info.param_types) { pt = info.param_types[i] }
        val := gen_expr(g, arg, pt)
        append(&arg_strs, fmt.tprintf("%s %s", pt, val))
    }
    args_joined := strings.join(arg_strs[:], ", ")
    tmp := fresh_tmp(g)
    emit(g, "  %s = call %s @%s(%s)", tmp, info.ret_type, oi.llvm_name, args_joined)
    return tmp, true
}

gen_call :: proc(g: ^Codegen, e: ^Expr_Call) -> string {
    // Each call site evaluates its tuple-default sources fresh. Save the
    // outer cache, install an empty one, run, then restore — so nested
    // gen_call invocations (e.g. when evaluating the source itself) get a
    // clean cache and our cache doesn't survive past this call. Done as a
    // wrapper because gen_call_inner ends in a `noreturn` codegen_fatal,
    // which Odin's defer analysis rejects.
    saved_cache := g.tuple_default_cache
    g.tuple_default_cache = nil
    result := gen_call_inner(g, e)
    if g.tuple_default_cache != nil {
        for _, entry in g.tuple_default_cache {
            delete(entry.ptrs)
            delete(entry.types)
        }
        delete(g.tuple_default_cache)
    }
    g.tuple_default_cache = saved_cache
    return result
}

gen_call_inner :: proc(g: ^Codegen, e: ^Expr_Call) -> string {
    // Desugared builtin: type checker rewrote this call to a simpler expression
    if e.desugared != nil {
        return gen_expr(g, e.desugared)
    }

    // Built-in: print
    if e.name == "print" {
        gen_print(g, e)
        return "0"
    }

    // Built-in: crash(msg?) — print message (if given) and exit(1)
    if e.name == "crash" && len(e.args) <= 1 {
        gen_crash(g, e)
        return "0"
    }

    // Built-in: print_cstr(ptr) — print a null-terminated C string (no newline)
    if e.name == "print_cstr" && len(e.args) == 1 {
        val := gen_expr(g, e.args[0])
        fmt_name, fmt_len := get_string_literal(g, "%s")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_ptr(g, fmt_ptr, val)
        return "0"
    }

    // Built-in: print_int(val) — print an integer (no newline)
    if e.name == "print_int" && len(e.args) == 1 {
        val := gen_expr(g, e.args[0])
        fmt_name, fmt_len := get_string_literal(g, "%lld")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_i64(g, fmt_ptr, val)
        return "0"
    }

    // Built-in: print_float(val) — print a float (no newline)
    if e.name == "print_float" && len(e.args) == 1 {
        val := gen_expr(g, e.args[0])
        fmt_name, fmt_len := get_string_literal(g, "%g")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_double(g, fmt_ptr, val)
        return "0"
    }

    // Built-in: len(arr) — returns capacity for plain arrays, runtime len for array class/slices
    if e.name == "len" && len(e.args) == 1 {
        if ident, ok := e.args[0].(^Expr_Ident); ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                if av.capacity_val != "" { return av.capacity_val } // VLA: runtime size
                return fmt.tprintf("%d", av.capacity)
            }
            if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                _ = sv
                return gen_slice_len(g, ident.name)
            }
            // Array class len() is desugared to buf.len field access by the type checker
        }
        // Field access argument: len(obj.field) — array class case desugared by type checker
        if fa, fa_ok := e.args[0].(^Expr_Field_Access); fa_ok {
            gen_field_access(g, fa)
            if av, av_ok := claim_field_array(g); av_ok {
                return fmt.tprintf("%d", av.capacity)
            }
            // Slice field: load field 1 (len cursor) from the slice header.
            if sv, sv_ok := claim_field_slice(g); sv_ok {
                len_gep := fresh_tmp(g)
                emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
                len_val := fresh_tmp(g)
                emit_typed_load_len(g, len_val, len_gep)
                return len_val
            }
        }
    }

    // Built-in: cap(arr) — returns usable capacity (utf8 arrays reserve last byte for null)
    if e.name == "cap" && len(e.args) == 1 {
        if ident, ok := e.args[0].(^Expr_Ident); ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                if av.capacity_val != "" { return av.capacity_val } // VLA: runtime size
                return fmt.tprintf("%d", usable_cap(&av))
            }
            if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                raw_cap := gen_slice_cap(g, ident.name)
                if sv.has_sentinel {
                    // Hide the sentinel slot from the user-facing capacity.
                    result := fresh_tmp(g)
                    emit(g, "  %s = sub i64 %s, 1", result, raw_cap)
                    return result
                }
                return raw_cap
            }
            // Array class cap() is desugared to buf.cap field access or compile-time constant by the type checker
        }
        // Field access argument: cap(obj.slice_field) — load field 2 from the slice header.
        if fa, fa_ok := e.args[0].(^Expr_Field_Access); fa_ok {
            gen_field_access(g, fa)
            if sv, sv_ok := claim_field_slice(g); sv_ok {
                cap_gep := fresh_tmp(g)
                emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
                cap_val := fresh_tmp(g)
                emit_typed_load_cap(g, cap_val, cap_gep)
                if sv.has_sentinel {
                    result := fresh_tmp(g)
                    emit(g, "  %s = sub i64 %s, 1", result, cap_val)
                    return result
                }
                return cap_val
            }
        }
    }

    // Built-in: slice_from_ptr(ptr, cap) -> []byte — wraps a raw pointer + capacity into a byte slice
    if e.name == "slice_from_ptr" && len(e.args) == 2 {
        ptr_val := gen_expr(g, e.args[0])
        cap_val := gen_expr(g, e.args[1])
        return emit_build_temp_slice(g, ptr_val, cap_val, cap_val)
    }

    // Type casts: i32(x), f64(x), etc.
    if cast_result, cast_ok := gen_type_cast(g, e); cast_ok {
        return cast_result
    }

    // Distinct type construction: Foo(x) where Foo :: distinct T.
    // The type checker rewrote e.resolved_func.name to the distinct's flat
    // name, so we look it up here. At IR level the wrapper is identical to
    // its underlying type (Type_Distinct lowers to base_type in
    // llvm_type_from_checker), so construction is a no-op pass-through —
    // just evaluate the arg in the underlying's IR type and return it.
    if dt, found := g.checked.table.distinct_types[call_resolved_name(e)]; found {
        if len(e.args) == 1 {
            base_ir := llvm_type_from_checker(dt.base_type)
            return gen_expr(g, e.args[0], base_ir)
        }
    }

    // Foreign function call — apply .C ABI lowering per platform.
    foreign_lookup := call_resolved_name(e)
    if cs, ok := g.checked.functions[foreign_lookup]; ok {
        if fo, is_foreign := cs.origin.(Origin_Foreign); is_foreign {
            return gen_c_call(g, e, &cs, fo.link_name, foreign_lookup)
        }
    }

    // User-defined function call (or qualified call: pkg.func)
    // Use the resolved (flat) name throughout — e.name is the source-level name which
    // may not match the flat key in checked.functions (e.g. "arena_new" vs "arena_arena_new").
    lookup_name := call_resolved_name(e)

    // Intrinsic function: emit an @llvm.* call directly at this site, no user-function body exists.
    if intr_result, intr_ok := emit_intrinsic_call(g, lookup_name, e); intr_ok {
        return intr_result
    }

    ir_name: string
    if fir, fir_ok := foreign_ir_name(g, lookup_name); fir_ok {
        ir_name = fir
    } else {
        ir_name = mara_fn_name(g, lookup_name)
    }
    if info, info_ok := lookup_fun_info(g, lookup_name); info_ok {
        arg_strs: [dynamic]string
        for arg, i in e.args {
            if i < len(info.param_structs) && info.param_structs[i] != "" {
                // Struct arg: pass as ptr (no target_type needed)
                val := gen_expr(g, arg)
                append(&arg_strs, fmt.tprintf("ptr %s", val))
            } else {
                pt := "i64"
                if i < len(info.param_types) {
                    pt = info.param_types[i]
                }
                if pt == SLICE_IR_TYPE {
                    append(&arg_strs, gen_slice_param_arg(g, arg))
                    continue
                }
                val := gen_expr(g, arg, pt)
                if strings.has_prefix(pt, "[") {
                    val = gen_array_param_arg(g, arg, pt, val)
                }
                append(&arg_strs, fmt.tprintf("%s %s", pt, val))
            }
        }

        if info.ret_struct != "" {
            // Struct return: alloca a temp, pass as sret, call void.
            // Sibling storage args (if any) follow sret.
            tmp_struct := fresh_tmp(g)
            emit_alloca(g, tmp_struct, struct_llvm_name(info.ret_struct))
            append(&arg_strs, fmt.tprintf("ptr %s", tmp_struct))
            emit_escape_storage_args(g, &arg_strs, &info, lookup_name, e.span)
            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)
            return tmp_struct
        } else if info.ret_array_cap > 0 {
            // Array return: allocate temp data buffer (+len), pass as sret, call void
            total_bytes := info.ret_array_cap * elem_byte_size(info.ret_array_elem)
            tmp_data: string
            if g.context_enabled && total_bytes >= 1024 {
                ret_name := fmt.tprintf("<ret %s>", call_resolved_name(e))
                ret_loc := format_location(e.span.file, e.span.line, e.span.col)
                tmp_data = emit_arena_bump(g, total_bytes, ret_name, ret_loc)
            } else {
                arr_type := fmt.tprintf("[%d x %s]", info.ret_array_cap, info.ret_array_elem)
                tmp_data = fresh_tmp(g)
                emit_alloca(g, tmp_data, arr_type)
            }
            append(&arg_strs, fmt.tprintf("ptr %s", tmp_data))

            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)

            // Register as temp call result so the caller (Stmt_Assign or Stmt_Return) can pick it up
            set_call_result(g, Array_Var{
                alloca    = tmp_data,
                capacity  = info.ret_array_cap,
                elem_type = info.ret_array_elem,
            })
            return tmp_data
        } else if info.ret_slice_elem != "" {
            // Slice return: alloca temp { ptr, i64 }, pass as sret, call void
            tmp_slice := fresh_tmp(g)
            emit_slice_alloca(g, tmp_slice)
            append(&arg_strs, fmt.tprintf("ptr %s", tmp_slice))
            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)
            return tmp_slice
        } else if info.ret_tuple != nil {
            // Tuple return: alloca temp pointers for each element, pass as sret, call void
            clear(&g.tuple_result_ptrs)
            clear(&g.tuple_result_types)
            for elem, i in info.ret_tuple.elems {
                et := llvm_type_from_checker(elem)
                tmp_ptr := fresh_tmp(g)
                emit_alloca(g, tmp_ptr, et)
                append(&arg_strs, fmt.tprintf("ptr %s", tmp_ptr))
                append(&g.tuple_result_ptrs, tmp_ptr)
                append(&g.tuple_result_types, et)
            }
            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)
            return "0" // no single return value; results are in tuple_result_ptrs
        } else if info.ret_type == "void" {
            // IO function: void return, no result value
            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)
            return "0"
        } else {
            args_joined := strings.join(arg_strs[:], ", ")
            tmp := fresh_tmp(g)
            emit(g, "  %s = call %s %s(%s)", tmp, info.ret_type, ir_name, args_joined)
            // Reconcile: call IR type may differ from type checker annotation.
            // Convert so the returned value matches what expr_ir_type reports.
            if e.type_ != nil && !is_untyped(e.type_) {
                expected := llvm_type_from_checker(e.type_)
                if expected != info.ret_type {
                    tmp = emit_type_convert(g, tmp, info.ret_type, expected)
                }
            }
            return tmp
        }
    }

    // Indirect call: callee is a function pointer variable
    if alloca, alloca_ok := get_scalar(g, lookup_name); alloca_ok {
        fn_ptr := fresh_tmp(g)
        emit_load_into(g, fn_ptr, "ptr", alloca)
        // Build typed arg list from each arg's checker type
        arg_strs: [dynamic]string
        for arg in e.args {
            at := expr_type(arg)
            pt := "i64"
            if at != nil && !is_untyped(at) {
                pt = llvm_type_from_checker(at)
            }
            val := gen_expr(g, arg, pt)
            append(&arg_strs, fmt.tprintf("%s %s", pt, val))
        }
        args_joined := strings.join(arg_strs[:], ", ")
        ret := "i64"
        if e.type_ != nil && !is_untyped(e.type_) {
            ret = llvm_type_from_checker(e.type_)
        }
        if ret == "void" {
            emit(g, "  call void %s(%s)", fn_ptr, args_joined)
            return "0"
        }
        tmp := fresh_tmp(g)
        emit(g, "  %s = call %s %s(%s)", tmp, ret, fn_ptr, args_joined)
        return tmp
    }

    codegen_fatal(g, e.span, CODE_CALL_UNKNOWN_FUNCTION_FUN_INFO, lookup_name)
}

// Emit a foreign (.C convention) function call. Applies platform ABI lowering
// (SysV / Win64) to each parameter and the return.
//
//   Direct arg, scalar     → existing primitive emission path
//   Direct arg, aggregate  → load classified parts from the arg's struct memory
//   Indirect arg           → ptr byval(<T>) %addr (caller provides the address)
//   Direct return, scalar  → capture the SSA result
//   Direct return, aggr.   → alloca slot + extract+store each part, return slot
//   Indirect return        → alloca slot, pass as hidden sret first arg
gen_c_call :: proc(g: ^Codegen, e: ^Expr_Call, cs: ^Checked_Scope, link_name, foreign_lookup: string) -> string {
    conv := Calling_Conv.C
    if cs.type_ != nil { conv = cs.type_.calling_conv }
    os := g.checked.target_os

    arg_strs: [dynamic]string

    // Return lowering: prepend hidden sret slot for Indirect, set ret_ir for Direct.
    has_void_return := cs.return_type == nil || is_untyped(cs.return_type)
    ret_low: Lowering
    ret_ir := "void"
    sret_slot := ""
    if !has_void_return {
        ret_low = classify_ret(cs.return_type, conv, os)
        switch r in ret_low {
        case Lowering_Direct:
            ret_ir = direct_ir_for_return(r.parts[:])
        case Lowering_Indirect:
            ret_struct_ir := llvm_type_from_checker(cs.return_type)
            sret_slot = fresh_tmp(g)
            emit_alloca(g, sret_slot, ret_struct_ir)
            append(&arg_strs, fmt.tprintf("ptr sret(%s) %s", ret_struct_ir, sret_slot))
        }
    }

    // Each user arg.
    for arg_expr, i in e.args {
        if i >= len(cs.params) {
            // Variadic excess (not yet supported beyond best-effort scalar pass-through).
            val := gen_expr(g, arg_expr)
            append(&arg_strs, fmt.tprintf("i64 %s", val))
            continue
        }
        pt := cs.params[i].type_
        p_low := classify_arg(pt, conv, os)

        switch pp in p_low {
        case Lowering_Direct:
            if is_aggregate(pt) {
                emit_c_aggregate_direct_arg(g, arg_expr, pp.parts[:], &arg_strs)
            } else {
                emit_c_scalar_arg(g, arg_expr, pp.parts[0], &arg_strs)
            }
        case Lowering_Indirect:
            arg_addr := gen_expr(g, arg_expr)
            arg_struct_ir := llvm_type_from_checker(pt)
            append(&arg_strs, fmt.tprintf("ptr byval(%s) %s", arg_struct_ir, arg_addr))
        }
    }

    args_joined := strings.join(arg_strs[:], ", ")
    call_name := link_name
    if call_name == "" { call_name = foreign_lookup }

    // Emit the call.
    if has_void_return {
        emit(g, "  call void @%s(%s)", call_name, args_joined)
        return "0"
    }
    if sret_slot != "" {
        emit(g, "  call void @%s(%s)", call_name, args_joined)
        return sret_slot
    }
    tmp := fresh_tmp(g)
    emit(g, "  %s = call %s @%s(%s)", tmp, ret_ir, call_name, args_joined)

    // For Direct aggregate returns, materialize the SSA result into a memory
    // slot so callers — which expect aggregate values via pointer — can use it.
    if direct, ok := ret_low.(Lowering_Direct); ok {
        if is_aggregate(cs.return_type) {
            ret_struct_ir := llvm_type_from_checker(cs.return_type)
            slot := fresh_tmp(g)
            emit_alloca(g, slot, ret_struct_ir)
            if len(direct.parts) == 1 {
                emit_store(g, direct.parts[0], tmp, slot)
            } else {
                for part, pi in direct.parts {
                    offset := pi * 8
                    ev := fresh_tmp(g)
                    emit(g, "  %s = extractvalue %s %s, %d", ev, ret_ir, tmp, pi)
                    if offset == 0 {
                        emit_store(g, part, ev, slot)
                    } else {
                        gep := fresh_tmp(g)
                        emit(g, "  %s = getelementptr i8, ptr %s, i64 %d", gep, slot, offset)
                        emit_store(g, part, ev, gep)
                    }
                }
            }
            return slot
        }
    }
    return tmp
}

// Emit a scalar-typed C call argument. Preserves the legacy primitive paths:
// utf8 array → cstring ptr, type conversion, ptr null sentinel.
emit_c_scalar_arg :: proc(g: ^Codegen, arg_expr: Expr, pt: string, arg_strs: ^[dynamic]string) {
    if pt == "ptr" {
        if ident, id_ok := arg_expr.(^Expr_Ident); id_ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                append(arg_strs, fmt.tprintf("ptr %s", av.alloca))
                return
            }
        }
    }
    val := gen_expr(g, arg_expr, pt)
    if !is_infer_expr(g, arg_expr) {
        val_type := expr_ir_type(g, arg_expr)
        if val_type != pt {
            val = emit_type_convert(g, val, val_type, pt)
        }
    }
    if pt == "ptr" && val == "0" {
        val = "null"
    }
    append(arg_strs, fmt.tprintf("%s %s", pt, val))
}

// Emit an aggregate-typed Direct C call argument: load each classified part
// from the struct's memory at the corresponding eightbyte offset.
emit_c_aggregate_direct_arg :: proc(g: ^Codegen, arg_expr: Expr, parts: []string, arg_strs: ^[dynamic]string) {
    addr := gen_expr(g, arg_expr)
    for part, i in parts {
        offset := i * 8
        gep: string
        if offset == 0 {
            gep = addr
        } else {
            gep = fresh_tmp(g)
            emit(g, "  %s = getelementptr i8, ptr %s, i64 %d", gep, addr, offset)
        }
        loaded := fresh_tmp(g)
        emit_load_into(g, loaded, part, gep)
        append(arg_strs, fmt.tprintf("%s %s", part, loaded))
    }
}

// Allocate sibling storage for each of a callee's escape locals and append
// `ptr %x` entries to arg_strs. Stack-alloca for small buffers; bump from
// the scope arena once we cross the 1024-byte threshold, mirroring the
// rule that governs manual `name : []T(N)` declarations.
//
// When g.escape_pool_alloca is set, the storage is carved from that pool
// instead — the pool's len field becomes the cursor, each carve advances
// it, and the pool's element backing lives next to the receiving slice.
// This breaks the alloca-hoist-aliasing trap that would otherwise make
// loop-bodies share a single sibling buffer across iterations.
emit_escape_storage_args :: proc(g: ^Codegen, arg_strs: ^[dynamic]string, info: ^Fun_Info, call_name: string, span: Span) {
    if len(info.escape_locals) == 0 { return }
    loc := format_location(span.file, span.line, span.col)
    pool := g.escape_pool_alloca
    for &el in info.escape_locals {
        alloc_cap := el.cap
        if el.has_sentinel { alloc_cap += 1 }
        total_bytes := alloc_cap * el.elem_size
        ptr: string
        if pool != "" {
            // Carve `total_bytes` from pool: data + len → ptr; len += total.
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, pool, SLICE.ptr)
            base := fresh_tmp(g)
            emit_load_into(g, base, "ptr", data_gep)
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, pool, SLICE.len)
            cur := fresh_tmp(g)
            emit_typed_load_len(g, cur, len_gep)
            ptr = fresh_tmp(g)
            emit(g, "  %s = getelementptr i8, ptr %s, i64 %s", ptr, base, cur)
            next := fresh_tmp(g)
            emit(g, "  %s = add i64 %s, %d", next, cur, total_bytes)
            emit_typed_store_len(g, next, len_gep)
        } else if g.context_enabled && total_bytes >= 1024 {
            name := fmt.tprintf("<%s.%s>", call_name, el.name)
            ptr = emit_arena_bump(g, total_bytes, name, loc)
        } else {
            ptr = fresh_tmp(g)
            emit(g, "  %s = alloca [%d x %s]", ptr, alloc_cap, el.elem_type)
        }
        append(arg_strs, fmt.tprintf("ptr %s", ptr))
    }
}

// Emit a struct-returning call, writing directly into a caller-supplied
// destination pointer (NRVO) instead of allocating a temp sret slot. Same
// shape as gen_call_into_array but the destination is just a raw pointer.
gen_call_into_struct :: proc(g: ^Codegen, e: ^Expr_Call, dest_ptr: string, info: ^Fun_Info) {
    cn := call_resolved_name(e)

    ir_name: string
    if fir, fir_ok := foreign_ir_name(g, cn); fir_ok {
        ir_name = fir
    } else {
        ir_name = mara_fn_name(g, cn)
    }

    arg_strs: [dynamic]string
    for arg, i in e.args {
        if i < len(info.param_structs) && info.param_structs[i] != "" {
            val := gen_expr(g, arg)
            append(&arg_strs, fmt.tprintf("ptr %s", val))
        } else {
            pt := "i64"
            if i < len(info.param_types) {
                pt = info.param_types[i]
            }
            if pt == SLICE_IR_TYPE {
                append(&arg_strs, gen_slice_param_arg(g, arg))
                continue
            }
            val := gen_expr(g, arg, pt)
            if strings.has_prefix(pt, "[") {
                val = gen_array_param_arg(g, arg, pt, val)
            }
            append(&arg_strs, fmt.tprintf("%s %s", pt, val))
        }
    }

    append(&arg_strs, fmt.tprintf("ptr %s", dest_ptr))
    emit_escape_storage_args(g, &arg_strs, info, cn, e.span)
    args_joined := strings.join(arg_strs[:], ", ")
    emit(g, "  call void %s(%s)", ir_name, args_joined)
}

// Emit an array-returning call, writing directly into a pre-existing Array_Var
// (e.g. an NRVO-aliased variable) instead of allocating temp buffers.
gen_call_into_array :: proc(g: ^Codegen, e: ^Expr_Call, dest: ^Array_Var, info: ^Fun_Info) {
    cn := call_resolved_name(e)

    ir_name: string
    if fir, fir_ok := foreign_ir_name(g, cn); fir_ok {
        ir_name = fir
    } else {
        ir_name = mara_fn_name(g, cn)
    }

    // Build normal arguments
    arg_strs: [dynamic]string
    for arg, i in e.args {
        if i < len(info.param_structs) && info.param_structs[i] != "" {
            val := gen_expr(g, arg)
            append(&arg_strs, fmt.tprintf("ptr %s", val))
        } else {
            pt := "i64"
            if i < len(info.param_types) {
                pt = info.param_types[i]
            }
            val := gen_expr(g, arg, pt)
            // Array param passed by value: route through the shared helper so
            // every arg shape (Ident, Field_Access, Call, overload-Binary,
            // string-literal, …) gets the same load-from-ptr treatment as
            // the regular gen_call path.
            if strings.has_prefix(pt, "[") {
                val = gen_array_param_arg(g, arg, pt, val)
            }
            append(&arg_strs, fmt.tprintf("%s %s", pt, val))
        }
    }

    // Append the destination's data pointer as sret arg
    append(&arg_strs, fmt.tprintf("ptr %s", dest.alloca))

    args_joined := strings.join(arg_strs[:], ", ")
    emit(g, "  call void %s(%s)", ir_name, args_joined)
}

// ---------------------------------------------------------------------------
// Crash builtin — print message and exit(1)
// ---------------------------------------------------------------------------

gen_crash :: proc(g: ^Codegen, e: ^Expr_Call) {
    if len(e.args) == 1 {
        arg := e.args[0]
        val := gen_expr(g, arg)
        arg_type := expr_type(arg)

        // Print the message (string literal or runtime string)
        if _, ok := arg_type.(^Type_Fixed_Array); ok {
            fa := arg_type.(^Type_Fixed_Array)
            if _, is_utf8 := fa.elem.(Type_Utf8); is_utf8 {
                fmt_name, fmt_len := get_string_literal(g, "%s")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_ptr(g, fmt_ptr, val)
            }
        } else {
            // Assume string-like (ptr)
            fmt_name, fmt_len := get_string_literal(g, "%s")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_ptr(g, fmt_ptr, val)
        }

        // Print newline
        nl_name, nl_len := get_string_literal(g, "\n")
        nl_ptr := fresh_tmp(g)
        emit_string_gep(g, nl_ptr, nl_len, nl_name)
        emit_printf_void(g, nl_ptr)
    }

    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    // Start a dead block so any code after crash() in the same scope
    // doesn't produce IR after unreachable (which is invalid LLVM IR).
    dead_label := fresh_label(g, "crash.dead")
    emit_label(g, dead_label)
}

// ---------------------------------------------------------------------------
// Print builtin — uses C printf
// ---------------------------------------------------------------------------

gen_print :: proc(g: ^Codegen, e: ^Expr_Call) {
    // Format-string mode: when the first arg resolves to a string literal
    // containing unescaped `%`, treat it as a format string. Resolves direct
    // string literals as well as `name :: "..."` constants — those parse as
    // an Expr_Ident at the call site, but the constants table holds the
    // underlying Expr_String.
    if len(e.args) > 0 {
        if fmt_str, ok := resolve_format_string_value(g, e.args[0]); ok {
            if string_has_format_pct(fmt_str) {
                gen_print_format(g, fmt_str, e.args[1:], e.span)
                emit_print_newline(g)
                return
            }
        }
    }

    // Variadic mode: print each arg, space-separated, type-dispatched.
    for arg_expr, i in e.args {
        if i > 0 {
            // Print a space between arguments
            emit_print_literal(g, " ")
        }
        emit_print_arg(g, arg_expr)
    }

    emit_print_newline(g)
}

// If `expr` is (transitively) a string literal — either an inline literal,
// an identifier bound to a `name :: "..."` constant, or `Module.name` access
// to the same — return its value.
resolve_format_string_value :: proc(g: ^Codegen, expr: Expr) -> (string, bool) {
    if lit, ok := expr.(^Expr_String); ok { return lit.value, true }
    if ident, ok := expr.(^Expr_Ident); ok {
        if const_expr, found := g.checked.table.constants[ident.name]; found {
            if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                return lit.value, true
            }
        }
    }
    if fa, ok := expr.(^Expr_Field_Access); ok {
        if qual, q_ok := fa.expr.(^Expr_Ident); q_ok {
            // Try the flat-key form `Module_field` — covers self-module
            // qualification and imported-module qualification uniformly.
            flat := strings.concatenate({qual.name, "_", fa.field})
            if const_expr, found := g.checked.table.constants[flat]; found {
                if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                    return lit.value, true
                }
            }
        }
    }
    return "", false
}

// True if `s` contains a `%` placeholder (i.e. an unescaped `%`). `%%` is the
// escape for a literal `%` and does not count.
string_has_format_pct :: proc(s: string) -> bool {
    i := 0
    for i < len(s) {
        if s[i] == '%' {
            if i+1 < len(s) && s[i+1] == '%' {
                i += 2
                continue
            }
            return true
        }
        i += 1
    }
    return false
}

// Emit the printf calls for a format string with `%` placeholders. Static
// runs are emitted as a single `printf("%s", ...)` per run (with `%%` decoded
// to a literal `%`); each placeholder pulls the next arg through emit_print_arg.
gen_print_format :: proc(g: ^Codegen, fmt_str: string, args: []Expr, call_span: Span) {
    seg_buf: [dynamic]u8
    defer delete(seg_buf)
    arg_idx := 0
    flush :: proc(g: ^Codegen, seg: ^[dynamic]u8) {
        if len(seg^) == 0 { return }
        emit_print_literal(g, string(seg^[:]))
        clear(seg)
    }
    i := 0
    for i < len(fmt_str) {
        ch := fmt_str[i]
        if ch == '%' {
            if i+1 < len(fmt_str) && fmt_str[i+1] == '%' {
                append(&seg_buf, '%')
                i += 2
                continue
            }
            flush(g, &seg_buf)
            if arg_idx >= len(args) {
                codegen_fatal(g, call_span, CODE_FORMAT_STRING_MORE_PLACEHOLDERS_THAN)
            }
            emit_print_arg(g, args[arg_idx])
            arg_idx += 1
            // Skip both the `%` and the marker character (d, g, s, v, etc.).
            // The marker is human-readable shorthand only — Mara picks the
            // actual printf spec from the arg's type. Used to advance by 1,
            // which left the marker char to be appended as a literal in the
            // next iteration (`%d` printed as `<value>d`).
            i += i+1 < len(fmt_str) ? 2 : 1
            continue
        }
        append(&seg_buf, ch)
        i += 1
    }
    flush(g, &seg_buf)
}

// Emit a printf("%s", literal) for an inline static string.
emit_print_literal :: proc(g: ^Codegen, s: string) {
    str_name, str_len := get_string_literal(g, s)
    str_ptr := fresh_tmp(g)
    emit_string_gep(g, str_ptr, str_len, str_name)
    fmt_name, fmt_len := get_string_literal(g, "%s")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    emit_printf_ptr(g, fmt_ptr, str_ptr)
}

emit_print_newline :: proc(g: ^Codegen) {
    nl_name, nl_len := get_string_literal(g, "\n")
    nl_ptr := fresh_tmp(g)
    emit_string_gep(g, nl_ptr, nl_len, nl_name)
    emit_printf_void(g, nl_ptr)
}

// Emit a single arg as printf output, dispatched on the arg's checker type.
// Used by both variadic mode and format-string placeholders.
emit_print_arg :: proc(g: ^Codegen, arg_expr: Expr) {
        // Check if the expression is a utf8 array/array class/slice (string) — print with %s
        if is_utf8_array_expr(g, arg_expr) {
            // For utf8 arrays, pass the data pointer to printf with %s
            printed := false
            if ident, id_ok := arg_expr.(^Expr_Ident); id_ok {
                if av, av_ok := get_array(g, ident.name); av_ok {
                    // Use %.*s (length-bounded) instead of %s. A plain
                    // [N]utf8 buffer might not be null-terminated, in
                    // which case printf("%s", ...) walks past the buffer
                    // into adjacent memory until it finds a 0 — leaking
                    // garbage to the user's terminal at best, ringing
                    // the BEL byte at worst. %.*s reads exactly cap
                    // bytes (stops early on a null), so sentinel and
                    // non-sentinel utf8 arrays both print cleanly.
                    fmt_name, fmt_len := get_string_literal(g, "%.*s")
                    fmt_ptr := fresh_tmp(g)
                    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %d, ptr %s)", fmt_ptr, av.capacity, av.alloca)
                    printed = true
                } else if sv, sv_ok := get_slice(g, ident.name); sv_ok && sv.is_utf8 {
                    // utf8 slice — bound by len via %.*s. Mirrors the
                    // fixed-array branch above: a plain %s walks until it
                    // hits a 0, which leaks stack garbage when the sentinel
                    // was never written (non-sentinel slices) or got out of
                    // sync with len (partial overwrites). %.*s reads exactly
                    // len bytes regardless.
                    data_ptr := slice_var_data_ptr(g, &sv)
                    len_gep := fresh_tmp(g)
                    emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
                    len_i64 := fresh_tmp(g)
                    emit_typed_load_len(g, len_i64, len_gep)
                    len_i32 := fresh_tmp(g)
                    emit(g, "  %s = trunc i64 %s to i32", len_i32, len_i64)
                    fmt_name, fmt_len := get_string_literal(g, "%.*s")
                    fmt_ptr := fresh_tmp(g)
                    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s, ptr %s)", fmt_ptr, len_i32, data_ptr)
                    printed = true
                }
            } else if fa, fa_ok := arg_expr.(^Expr_Field_Access); fa_ok {
                // Field access yielding a utf8 slice or partial array
                // (e.g. `print(h.name)` where name: String). The address
                // chain bottoms out at .Slice for both shapes, so the same
                // header-relative %.*s load works. Without this branch the
                // outer `if printed` falls through to nothing and the call
                // emits just a newline.
                gen_field_access(g, fa)
                if sv, sv_ok := claim_field_slice(g); sv_ok && sv.is_utf8 {
                    data_gep := fresh_tmp(g)
                    emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
                    data_ptr := fresh_tmp(g)
                    emit_load_into(g, data_ptr, "ptr", data_gep)
                    len_gep := fresh_tmp(g)
                    emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
                    len_i64 := fresh_tmp(g)
                    emit_typed_load_len(g, len_i64, len_gep)
                    len_i32 := fresh_tmp(g)
                    emit(g, "  %s = trunc i64 %s to i32", len_i32, len_i64)
                    fmt_name, fmt_len := get_string_literal(g, "%.*s")
                    fmt_ptr := fresh_tmp(g)
                    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s, ptr %s)", fmt_ptr, len_i32, data_ptr)
                    printed = true
                }
            } else if _, str_ok := arg_expr.(^Expr_String); str_ok {
                // Bare string literal in print — use old ptr path
                val := gen_expr(g, arg_expr)
                fmt_name, fmt_len := get_string_literal(g, "%s")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_ptr(g, fmt_ptr, val)
                printed = true
            }
            _ = printed
        } else if is_array_expr(g, arg_expr) {
            // Check if the expression is a non-utf8 array variable
            gen_print_array(g, arg_expr)
        } else if is_plain_struct_expr(g, arg_expr) {
            // Non-array-class struct — print fields
            if ident, id_ok := arg_expr.(^Expr_Ident); id_ok {
                if stv, stv_ok := get_struct(g, ident.name); stv_ok {
                    if print_st, ps_ok := lookup_struct(g, stv.struct_name); ps_ok {
                        gen_print_struct(g, &stv, print_st)
                    }
                }
            }
        } else if is_c8_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            // c8 prints as a character using %c
            ext := fresh_tmp(g)
            emit(g, "  %s = zext i8 %s to i32", ext, val)
            fmt_name, fmt_len := get_string_literal(g, "%c")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, ext)
        } else if is_string_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            fmt_name, fmt_len := get_string_literal(g, "%s")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_ptr(g, fmt_ptr, val)
        } else if is_float_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            fmt_name, fmt_len := get_string_literal(g, "%g")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_double(g, fmt_ptr, val)
        } else if is_ptr_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            // ^byte by convention carries null-terminated cstrings (e.g.
            // #caller_name); print them as text rather than addresses.
            spec := "%p"
            t := expr_type(arg_expr)
            if pt, ok := t.(^Type_Ptr); ok {
                if _, is_byte := pt.elem.(Type_Byte); is_byte { spec = "%s" }
            }
            if _, is_cs := t.(Type_CString); is_cs { spec = "%s" }
            fmt_name, fmt_len := get_string_literal(g, spec)
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_ptr(g, fmt_ptr, val)
        } else if is_numeric_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            nt := get_numeric_type(g, arg_expr)
            if nt == "float" {
                // f32 must be extended to double for printf varargs
                ext := fresh_tmp(g)
                emit(g, "  %s = fpext float %s to double", ext, val)
                fmt_name, fmt_len := get_string_literal(g, "%g")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_double(g, fmt_ptr, ext)
            } else if nt == "i64" {
                // Already i64 — pass directly to printf
                fmt_name, fmt_len := get_string_literal(g, "%lld")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_i64(g, fmt_ptr, val)
            } else {
                // Small integer: extend to i64 for printf
                ext := fresh_tmp(g)
                is_unsigned := false
                ft := expr_type(arg_expr)
                if n, n_ok := ft.(Type_Numeric); n_ok {
                    is_unsigned = n.kind == .Unsigned
                }
                if is_unsigned {
                    emit(g, "  %s = zext %s %s to i64", ext, nt, val)
                } else {
                    emit(g, "  %s = sext %s %s to i64", ext, nt, val)
                }
                fmt_name, fmt_len := get_string_literal(g, "%lld")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_i64(g, fmt_ptr, ext)
            }
        } else {
            val := gen_expr(g, arg_expr)
            fmt_name, fmt_len := get_string_literal(g, "%lld")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_i64(g, fmt_ptr, val)
        }
}

// Check if an expression refers to an array variable
is_array_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if ident, ok := expr.(^Expr_Ident); ok {
        return is_array(g, ident.name)
    }
    // Field access / index expression yielding a fixed-size array. Read the
    // expr's checker type — set during type checking. Allows
    // `print(obj.field)` and `print(slice[i].field)` when the resolved type
    // is `[N]T`.
    t := distinct_base(expr_type(expr))
    if _, ok := t.(^Type_Fixed_Array); ok { return true }
    return false
}

is_plain_struct_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if ident, ok := expr.(^Expr_Ident); ok {
        if stv, stv_ok := get_struct(g, ident.name); stv_ok {
            if _, st_ok := lookup_struct(g, stv.struct_name); st_ok {
                return true
            }
        }
    }
    return false
}

// Print a struct as: StructName { field1: val1, field2: val2 }
gen_print_struct :: proc(g: ^Codegen, stv: ^Struct_Var, st: ^Scope_Body) {
    st_llvm := struct_llvm_name(struct_key(st))
    // Print "StructName { "
    header_name, header_len := get_string_literal(g, fmt.tprintf("%s {{ ", struct_key(st)))
    header_ptr := fresh_tmp(g)
    emit_string_gep(g, header_ptr, header_len, header_name)
    emit_printf_void(g, header_ptr)

    for &f, fi in st.fields {
        if fi > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        // Print "fieldname: "
        label_name, label_len := get_string_literal(g, fmt.tprintf("%s: ", f.name))
        label_ptr := fresh_tmp(g)
        emit_string_gep(g, label_ptr, label_len, label_name)
        emit_printf_void(g, label_ptr)

        ft := field_ir_type(&f)
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, stv.alloca, fi)

        acap := field_array_cap(&f)
        aelem := field_array_elem(&f)
        if acap > 0 {
            // Array field — print as [v1, v2, ...]
            inner_cap, inner_elem, is_nested := parse_array_ir_type(ft)
            _ = inner_cap; _ = inner_elem
            if is_nested {
                // Nested array like [4][4]f32 — print rows
                gen_print_nested_array(g, gep, acap, aelem)
            } else {
                gen_print_array_inline(g, gep, acap, aelem)
            }
        } else {
            // Scalar field — load and print
            val := fresh_tmp(g)
            emit_load_into(g, val, ft, gep)
            switch {
            case ft == "double":
                fmt_name, fmt_len := get_string_literal(g, "%g")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_double(g, fmt_ptr, val)
            case ft == "float":
                ext := fresh_tmp(g)
                emit(g, "  %s = fpext float %s to double", ext, val)
                fmt_name, fmt_len := get_string_literal(g, "%g")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_double(g, fmt_ptr, ext)
            case ft == "i1":
                fmt_name, fmt_len := get_string_literal(g, "%d")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                ext := fresh_tmp(g)
                emit(g, "  %s = zext i1 %s to i32", ext, val)
                emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, ext)
            case:
                ext := fresh_tmp(g)
                emit(g, "  %s = sext %s %s to i64", ext, ft, val)
                fmt_name, fmt_len := get_string_literal(g, "%lld")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_i64(g, fmt_ptr, ext)
            }
        }
    }

    // Print " }"
    close_name, close_len := get_string_literal(g, " }")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print a flat array inline: [v1, v2, v3]
gen_print_array_inline :: proc(g: ^Codegen, data_ptr: string, cap: int, elem_type: string) {
    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    arr_type := fmt.tprintf("[%d x %s]", cap, elem_type)
    for i := 0; i < cap; i += 1 {
        if i > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        gep := fresh_tmp(g)
        emit_array_gep_const(g, gep, arr_type, data_ptr, i)
        val := fresh_tmp(g)
        emit_load_into(g, val, elem_type, gep)
        switch {
        case elem_type == "double":
            fmt_name, fmt_len := get_string_literal(g, "%g")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_double(g, fmt_ptr, val)
        case elem_type == "float":
            ext := fresh_tmp(g)
            emit(g, "  %s = fpext float %s to double", ext, val)
            fmt_name, fmt_len := get_string_literal(g, "%g")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_double(g, fmt_ptr, ext)
        case:
            ext := fresh_tmp(g)
            emit(g, "  %s = sext %s %s to i64", ext, elem_type, val)
            fmt_name, fmt_len := get_string_literal(g, "%lld")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_i64(g, fmt_ptr, ext)
        }
    }

    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print a nested array like [4][4]f32 as: [[v, v, v, v], [v, v, v, v], ...]
gen_print_nested_array :: proc(g: ^Codegen, data_ptr: string, outer_cap: int, inner_ir_type: string) {
    inner_cap, inner_elem, _ := parse_array_ir_type(inner_ir_type)
    outer_arr_type := fmt.tprintf("[%d x %s]", outer_cap, inner_ir_type)

    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    for i := 0; i < outer_cap; i += 1 {
        if i > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        row_gep := fresh_tmp(g)
        emit_array_gep_const(g, row_gep, outer_arr_type, data_ptr, i)
        gen_print_array_inline(g, row_gep, inner_cap, inner_elem)
    }

    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print an array as: [1, 2, 3]
gen_print_array :: proc(g: ^Codegen, expr: Expr) {
    av: Array_Var
    if ident, ok := expr.(^Expr_Ident); ok {
        av, _ = get_array(g, ident.name)
    } else {
        // Field access / index yielding a fixed-size array — drive codegen
        // to populate the field-array result, then claim it.
        gen_expr(g, expr)
        cf, cf_ok := claim_field_array(g)
        if !cf_ok {
            codegen_fatal(g, {}, CODE_PRINT_ARRAY_EXPRESSION_DID_RESOLVE)
        }
        av = cf
    }
    arr_type := array_var_type(&av)

    // Nested array: delegate to gen_print_nested_array
    if inner_cap, inner_elem, is_nested := parse_array_ir_type(av.elem_type); is_nested {
        gen_print_nested_array(g, av.alloca, av.capacity, av.elem_type)
        _ = inner_cap; _ = inner_elem
        return
    }

    // Determine printf format and LLVM type for elements based on elem_type
    print_fmt: string
    print_llvm_type: string
    switch av.elem_type {
    case "double":
        print_fmt = "%f"
        print_llvm_type = "double"
    case "float":
        // f32 must be promoted to double for variadic printf
        print_fmt = "%f"
        print_llvm_type = "float"
    case "ptr":
        print_fmt = "%s"
        print_llvm_type = "ptr"
    case "i1":
        // Print booleans as 0/1 (i1 gets zero-extended to i64 for printf)
        print_fmt = "%lld"
        print_llvm_type = "i1"
    case:
        print_fmt = "%lld"
        print_llvm_type = "i64"
    }

    // Print opening bracket
    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    // Element count is always capacity (full arrays)
    arr_len := fmt.tprintf("%d", av.capacity)

    // Loop through elements
    cond_label := fresh_label(g, "print.cond")
    body_label := fresh_label(g, "print.body")
    end_label  := fresh_label(g, "print.end")

    idx_ptr := fresh_tmp(g)
    emit_alloca(g, idx_ptr, "i64")
    emit_store(g, "i64", "0", idx_ptr)
    emit_br(g, cond_label)

    emit_label(g, cond_label)
    idx := fresh_tmp(g)
    emit_load_into(g, idx, "i64", idx_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt i64 %s, %s", cmp, idx, arr_len)
    emit_cond_br(g, cmp, body_label, end_label)

    emit_label(g, body_label)
    idx2 := fresh_tmp(g)
    emit_load_into(g, idx2, "i64", idx_ptr)

    // Print comma+space if not first element
    comma_label := fresh_label(g, "print.comma")
    no_comma_label := fresh_label(g, "print.nocomma")
    after_comma_label := fresh_label(g, "print.aftercomma")
    is_first := fresh_tmp(g)
    emit(g, "  %s = icmp eq i64 %s, 0", is_first, idx2)
    emit_cond_br(g, is_first, no_comma_label, comma_label)

    emit_label(g, comma_label)
    comma_name, comma_len := get_string_literal(g, ", ")
    comma_ptr := fresh_tmp(g)
    emit_string_gep(g, comma_ptr, comma_len, comma_name)
    emit_printf_void(g, comma_ptr)
    emit_br(g, after_comma_label)

    emit_label(g, no_comma_label)
    emit_br(g, after_comma_label)

    emit_label(g, after_comma_label)
    // Load and print the element
    idx3 := fresh_tmp(g)
    emit_load_into(g, idx3, "i64", idx_ptr)
    gep := fresh_tmp(g)
    emit_array_gep_var(g, gep, arr_type, av.alloca, idx3)
    val := fresh_tmp(g)
    emit_load_into(g, val, av.elem_type, gep)

    // For i1 (bool), zero-extend to i64 for printf; for double, use as-is
    fmt_name, fmt_len := get_string_literal(g, print_fmt)
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    if print_llvm_type == "double" {
        emit_printf_double(g, fmt_ptr, val)
    } else if print_llvm_type == "float" {
        // Promote f32 → double for variadic call
        promoted := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", promoted, val)
        emit_printf_double(g, fmt_ptr, promoted)
    } else if print_llvm_type == "i1" {
        ext := fresh_tmp(g)
        emit(g, "  %s = zext i1 %s to i64", ext, val)
        emit_printf_i64(g, fmt_ptr, ext)
    } else if print_llvm_type == "ptr" {
        emit_printf_ptr(g, fmt_ptr, val)
    } else {
        emit_printf_i64(g, fmt_ptr, val)
    }

    // Increment index
    next := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, 1", next, idx3)
    emit_store(g, "i64", next, idx_ptr)
    emit_br(g, cond_label)

    emit_label(g, end_label)

    // Print closing bracket
    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// ---------------------------------------------------------------------------
// Type query helpers
// ---------------------------------------------------------------------------

// Check if this expression is a single character byte — c8 literal,
// c8 variable, or a Type_Utf8 byte (e.g. one element loaded out of a
// utf8 string array). Both print the same way (%c via printf): they're
// 8-bit values whose only meaningful rendering is as a glyph. Calling
// the helper is_c8_expr is a slight name lie now that utf8 is included,
// but every caller uses it for "should this print as a character?"
// which is exactly the right semantic for both kinds.
is_c8_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_Char); ok { return true }
    t := expr_type(expr)
    if _, is_c8 := t.(Type_C8); is_c8 { return true }
    if _, is_utf8 := t.(Type_Utf8); is_utf8 { return true }
    return false
}

is_string_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_String); ok { return true }
    t := expr_type(expr)
    _, is_str := t.(Type_CString)
    return is_str
}

// Check if an expression is a utf8 array variable (string stored as [N]utf8),
// a utf8 array class, or a utf8 slice. Unwraps distinct so distinct slice
// aliases (String, Path, etc.) still register as utf8 for print formatting.
is_utf8_array_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_String); ok { return true }
    t := distinct_base(expr_type(expr))
    if fa, fa_ok := t.(^Type_Fixed_Array); fa_ok {
        if _, utf8_ok := fa.elem.(Type_Utf8); utf8_ok { return true }
    }
    // Check utf8 slice
    if sl, sl_ok := t.(^Type_Slice); sl_ok {
        if _, utf8_ok := sl.elem.(Type_Utf8); utf8_ok { return true }
    }
    // Check utf8 partial array — same shape for print purposes.
    if pa, pa_ok := t.(^Type_Partial_Array); pa_ok {
        if _, utf8_ok := pa.elem.(Type_Utf8); utf8_ok { return true }
    }
    // Check codegen-level vars (for idents that may not have full type info)
    if ident, id_ok := expr.(^Expr_Ident); id_ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok && sv.is_utf8 { return true }
    }
    return false
}

// Simple check: is this expression a float literal or float variable?
is_float_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if num, ok := expr.(^Expr_Number); ok {
        return num.is_float || num.value != f64(int(num.value))
    }
    t := expr_type(expr)
    if t != nil && !is_untyped(t) {
        if _, is_f64 := t.(Type_F64); is_f64 { return true }
        // f32 (Type_Numeric Float) is NOT a "float expr" — it goes through
        // is_numeric_expr instead, which handles fpext float→double for printf
    }
    // Check struct field access: obj.field where field type is double.
    // float (f32) deliberately falls through — is_numeric_expr handles it
    // and emits the fpext float→double needed for printf varargs.
    if fa, ok := expr.(^Expr_Field_Access); ok {
        ft := expr_ir_type(g, fa)
        return ft == "double"
    }
    // Check array index into a float array: arr[i] where arr is [N x double]
    if idx, ok := expr.(^Expr_Index); ok {
        if id, id_ok := idx.expr.(^Expr_Ident); id_ok {
            if av, av_ok := get_array(g, id.name); av_ok {
                return av.elem_type == "double"
            }
        }
    }
    return false
}

// Simple check: is this expression a pointer variable or foreign call returning ptr?
is_ptr_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    t := expr_type(expr)
    if _, is_ptr := t.(^Type_Ptr); is_ptr { return true }
    if call, ok := expr.(^Expr_Call); ok {
        if cs, cs_ok := g.checked.functions[call_resolved_name(call)]; cs_ok {
            if _, is_foreign := cs.origin.(Origin_Foreign); is_foreign {
                if _, is_ptr := cs.return_type.(^Type_Ptr); is_ptr { return true }
                if _, is_cs := cs.return_type.(Type_CString); is_cs { return true }
            }
        }
    }
    if unary, ok := expr.(^Expr_Unary); ok {
        if unary.op == .Ampersand { return true }
    }
    return false
}

is_numeric_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    t := expr_type(expr)
    if t != nil {
        if _, is_num := t.(Type_Numeric); is_num { return true }
        if _, is_enum := t.(^Type_Enum); is_enum { return true }
    }
    if bin, ok := expr.(^Expr_Binary); ok {
        return is_numeric_expr(g, bin.left)
    }
    if unary, ok := expr.(^Expr_Unary); ok {
        return is_numeric_expr(g, unary.operand)
    }
    return false
}

get_numeric_type :: proc(g: ^Codegen, expr: Expr) -> string {
    t := expr_type(expr)
    if t != nil {
        if n, n_ok := t.(Type_Numeric); n_ok {
            return llvm_type_from_checker(n)
        }
        if _, e_ok := t.(^Type_Enum); e_ok {
            return llvm_type_from_checker(t)
        }
        // Pointer dereference: the expression's type is the dereferenced type
        if pt, pt_ok := t.(^Type_Ptr); pt_ok {
            return llvm_type_from_checker(pt.elem)
        }
    }
    if bin, ok := expr.(^Expr_Binary); ok {
        return get_numeric_type(g, bin.left)
    }
    if unary, ok := expr.(^Expr_Unary); ok {
        return get_numeric_type(g, unary.operand)
    }
    return "i64"
}

// Infer the LLVM IR type string for an expression.
// Uses type annotations from the type checker as the primary source.
expr_ir_type :: proc(g: ^Codegen, expr: Expr) -> string {
    // Runtime representation overrides (these differ from semantic type)
    #partial switch v in expr {
    case ^Expr_String:              return "ptr"   // gen_expr GEPs strings to pointers
    case ^Expr_Struct_Literal:      return "ptr"   // gen_expr returns alloca pointer
    case ^Expr_Array:               return "i64"   // array literals have special codegen paths
    case ^Expr_Compiler_Intrinsic:
        if v.kind == .Web || v.kind == .Native ||
           v.kind == .Windows || v.kind == .Linux || v.kind == .Mac { return "i1" }
        return "ptr"   // Caller_* GEP resolved string to pointer
    case: // fall through to type-based path
    }

    // Primary path: use type annotation filled by the type checker
    t := expr_type(expr)
    if t != nil && !is_untyped(t) {
        return llvm_type_from_checker(t)
    }
    return "i64"
}

// Returns true if expr is a numeric literal or an infer-type constant.
// When true, gen_expr with target_type already emitted the correct type,
// so post-hoc conversion is unnecessary.
is_infer_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_Number); ok { return true }
    if e, ok := expr.(^Expr_Ident); ok {
        if _, c_ok := g.checked.table.constants[e.name]; c_ok { return true }
    }
    // Check the type checker annotation: if infer, gen_expr already
    // used target_type to emit the correct IR type.
    t := expr_type(expr)
    if t != nil { return is_infer(t) }
    return false
}
