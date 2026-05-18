package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Array class VLA helpers
// ---------------------------------------------------------------------------

// Get the capacity string for an array class — loads from cap field if present,
// falls back to VLA runtime register or compile-time constant.
ac_cap_str :: proc(g: ^Codegen, ac_st: ^Scope_Body, sv: ^Struct_Var) -> string {
    cap_fi := ac_cap_field_index(ac_st)
    if cap_fi >= 0 {
        cap_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", cap_gep, struct_llvm_name(sv.struct_name), sv.alloca, cap_fi)
        cap_val := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
        return cap_val
    }
    if sv.vla_cap != "" { return sv.vla_cap }
    return fmt.tprintf("%d", ac_st.array_cap)
}

// Load cap from any struct pointer (works across function boundaries via ^ArrayClass).
ac_cap_from_ptr :: proc(g: ^Codegen, ac_st: ^Scope_Body, struct_ptr: string) -> string {
    cap_fi := ac_cap_field_index(ac_st)
    if cap_fi >= 0 {
        cap_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", cap_gep, struct_llvm_name(ac_st.name), struct_ptr, cap_fi)
        cap_val := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
        return cap_val
    }
    return fmt.tprintf("%d", ac_st.array_cap)
}

// Get the LLVM array type for GEP — uses [0 x T] for VLA, [N x T] for fixed.
ac_arr_type :: proc(ac_st: ^Scope_Body) -> string {
    elem := ac_elem_ir_type(ac_st)
    return fmt.tprintf("[%d x %s]", ac_st.array_cap, elem)
}

// ---------------------------------------------------------------------------
// Slice IR helpers (emit_raw with strings.concatenate to avoid fmt brace issues)
// ---------------------------------------------------------------------------

// Slice fields: 0 = data ptr, 1 = len (cursor), 2 = cap (capacity).
emit_slice_gep :: proc(g: ^Codegen, result: string, src: string, field: int) {
    field_suffix := ", i32 0, i32 0"
    switch field {
    case 0: field_suffix = ", i32 0, i32 0"
    case 1: field_suffix = ", i32 0, i32 1"
    case 2: field_suffix = ", i32 0, i32 2"
    }
    emit_raw(g, strings.concatenate({"  ", result, " = getelementptr ", SLICE_IR_TYPE, ", ptr ", src, field_suffix}))
}

emit_slice_alloca :: proc(g: ^Codegen, result: string) {
    emit_raw(g, strings.concatenate({"  ", result, " = alloca ", SLICE_IR_TYPE}))
}

emit_slice_load :: proc(g: ^Codegen, result: string, src: string) {
    emit_raw(g, strings.concatenate({"  ", result, " = load ", SLICE_IR_TYPE, ", ptr ", src}))
}

emit_slice_store :: proc(g: ^Codegen, val: string, dst: string) {
    emit_raw(g, strings.concatenate({"  store ", SLICE_IR_TYPE, " ", val, ", ptr ", dst}))
}

// Slice args are passed by pointer-to-header — fat pointers are reference
// types in Mara, so cursor / ptr mutations through them propagate to the
// caller's slice. `val` must be a pointer to a slice descriptor alloca.
slice_arg_str :: proc(val: string) -> string {
    return strings.concatenate({"ptr ", val})
}

// Alloca a { ptr, i64, i64 } and store data_ptr / len / cap into its fields.
// Returns the alloca ptr. Callers load from it to get the slice value.
emit_build_temp_slice :: proc(g: ^Codegen, data_ptr: string, len_val: string, cap_val: string) -> string {
    slice_alloca := fresh_tmp(g)
    emit_slice_alloca(g, slice_alloca)
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, slice_alloca, 0)
    emit(g, "  store ptr %s, ptr %s", data_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, slice_alloca, 1)
    emit(g, "  store i64 %s, ptr %s", len_val, len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, slice_alloca, 2)
    emit(g, "  store i64 %s, ptr %s", cap_val, cap_gep)
    return slice_alloca
}

// ---------------------------------------------------------------------------
// Array codegen
// ---------------------------------------------------------------------------

gen_array_assign :: proc(g: ^Codegen, name: string, capacity: int, elem_type: string, value: Expr, is_utf8: bool = false, loc: string = "<unknown>", has_sentinel: bool = false, sentinel: int = 0) {
    alloc_cap := capacity
    if has_sentinel { alloc_cap += 1 }
    arr_type := fmt.tprintf("[%d x %s]", alloc_cap, elem_type)

    // If variable doesn't exist yet, allocate data
    if !is_array(g, name) {
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        data_name: string

        if g.context_enabled && total_bytes >= 1024 {
            // Big array: bump-allocate from the arena instead of the stack
            data_name = emit_arena_bump(g, total_bytes, name, loc)
        } else {
            // Small array: stack alloca as usual
            data_name = fmt.tprintf("%%%s.data", name)
            emit(g, "  %s = alloca %s", data_name, arr_type)
        }

        g.all_vars[name] = Array_Var{
            alloca       = data_name,
            capacity     = capacity,
            elem_type    = elem_type,
            is_utf8      = is_utf8,
            has_sentinel = has_sentinel,
            sentinel     = sentinel,
        }
    }

    av, _ := get_array(g, name)

    // No initializer — just zero the array
    if value == nil {
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", av.alloca, total_bytes)
        return
    }

    // Check if the value is a string literal (for utf8 arrays)
    if str_lit, ok := value.(^Expr_String); ok {
        global_name, byte_len := get_string_literal(g, str_lit.value)
        src_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", src_ptr, byte_len, global_name)
        // Zero-initialize first, then copy string bytes over
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", av.alloca, total_bytes)
        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", av.alloca, src_ptr, byte_len)
        return
    }

    // Check if the value is a compiler intrinsic (#caller_name, #caller_span) — same as string literal
    if intrinsic, ok := value.(^Expr_Compiler_Intrinsic); ok {
        global_name, byte_len := get_string_literal(g, intrinsic.resolved_value)
        src_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", src_ptr, byte_len, global_name)
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", av.alloca, total_bytes)
        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", av.alloca, src_ptr, byte_len)
        return
    }

    // Check if the value is an array literal
    if arr_lit, ok := value.(^Expr_Array); ok {
        // Zero-init first (handles undersized literals + sentinel), then store each element
        if len(arr_lit.elements) < alloc_cap {
            total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
            emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", av.alloca, total_bytes)
        }
        for elem, i in arr_lit.elements {
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", gep, arr_type, av.alloca, i)
            emit(g, "  store %s %s, ptr %s", elem_type, val, gep)
        }
    } else if sl, ok := value.(^Expr_Struct_Literal); ok && sl.array_values != nil {
        // Distinct-fixed-array struct literal (Quat{...}). Zero-init the slab
        // then store each non-nil slot; nil entries were checker-marked as
        // zero-fill.
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", av.alloca, total_bytes)
        for elem, i in sl.array_values {
            if elem == nil { continue }
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", gep, arr_type, av.alloca, i)
            emit(g, "  store %s %s, ptr %s", elem_type, val, gep)
        }
    } else {
        // Value is an expression — copy from another array
        gen_array_copy_expr(g, name, value)
    }
}

// Copy an array expression result into a named array variable.
gen_array_copy_expr :: proc(g: ^Codegen, name: string, value: Expr) {
    // For an identifier (copying one array to another)
    if ident, ok := value.(^Expr_Ident); ok {
        // Compile-time constant referring to an array-shaped value (e.g.
        // `QUAT_IDENTITY :: Quat{w = 1.0}`): inline the constant's expression
        // through the normal gen_array_assign dispatch so its
        // struct-literal / array-literal handling kicks in.
        if const_expr, const_ok := g.checked.table.constants[ident.name]; const_ok {
            dst, dst_ok := get_array(g, name)
            if dst_ok {
                loc := format_location(ident.span.file, ident.span.line, ident.span.col)
                gen_array_assign(g, name, dst.capacity, dst.elem_type, const_expr, dst.is_utf8, loc, dst.has_sentinel, dst.sentinel)
            }
            return
        }
        src, src_ok := get_array(g, ident.name)
        if !src_ok {
            codegen_fatal(g, ident.span, "'%s' is not an array", ident.name)
        }
        dst, _ := get_array(g, name)

        // Copy all elements (always use capacity — full arrays)
        loop_bound := fmt.tprintf("%d", src.capacity)

        src_type := array_var_type(&src)
        dst_type := array_var_type(&dst)
        cond_label := fresh_label(g, "copy.cond")
        body_label := fresh_label(g, "copy.body")
        end_label  := fresh_label(g, "copy.end")

        idx_ptr := fresh_tmp(g)
        emit(g, "  %s = alloca i64", idx_ptr)
        emit(g, "  store i64 0, ptr %s", idx_ptr)
        emit(g, "  br label %%%s", cond_label)

        emit(g, "%s:", cond_label)
        idx := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", idx, idx_ptr)
        cmp := fresh_tmp(g)
        emit(g, "  %s = icmp slt i64 %s, %s", cmp, idx, loop_bound)
        emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_label, end_label)

        emit(g, "%s:", body_label)
        idx2 := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", idx2, idx_ptr)
        src_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", src_gep, src_type, src.alloca, idx2)
        val := fresh_tmp(g)
        emit(g, "  %s = load %s, ptr %s", val, dst.elem_type, src_gep)
        dst_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", dst_gep, dst_type, dst.alloca, idx2)
        emit(g, "  store %s %s, ptr %s", dst.elem_type, val, dst_gep)
        next := fresh_tmp(g)
        emit(g, "  %s = add i64 %s, 1", next, idx2)
        emit(g, "  store i64 %s, ptr %s", next, idx_ptr)
        emit(g, "  br label %%%s", cond_label)

        emit(g, "%s:", end_label)
        return
    }

    // Field access (multi-component swizzle): arr.xy → temp array
    if fa, fa_ok := value.(^Expr_Field_Access); fa_ok {
        gen_field_access(g, fa)  // triggers gen_swizzle_read_multi → sets temp_swizzle_result
        if sr, sr_ok := claim_swizzle_result(g); sr_ok {
            dst, _ := get_array(g, name)
            src_arr_type := array_var_type(&sr)
            dst_arr_type := array_var_type(&dst)
            count := sr.capacity
            for i := 0; i < count; i += 1 {
                src_gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", src_gep, src_arr_type, sr.alloca, i)
                val := fresh_tmp(g)
                emit(g, "  %s = load %s, ptr %s", val, dst.elem_type, src_gep)
                dst_gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", dst_gep, dst_arr_type, dst.alloca, i)
                emit(g, "  store %s %s, ptr %s", dst.elem_type, val, dst_gep)
            }
            return
        }
    }

    // Fallback: evaluate expression (e.g. function call returning array)
    gen_expr(g, value)

    // If the expression produced a call result array, copy it into the destination
    if cr, cr_ok := claim_call_result(g); cr_ok {
        dst, dst_ok := get_array(g, name)
        if dst_ok {
            total_bytes := dst.capacity * elem_byte_size(dst.elem_type)
            emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)",
                dst.alloca, cr.alloca, total_bytes)
        }
    }
}

// Handle: arr[idx] = value
gen_index_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    ix := s.target.(^Expr_Index)
    // Byte-buffer reinterpret write: buf[offset] = value. Covers []byte slices
    // and [N]byte fixed arrays (Array(byte, N) reaches here post-desugar as a
    // Type_Fixed_Array). Special enough — and unrelated to the regular
    // address-chain shape — that it stays an explicit early branch.
    if is_byte_slice(s.target_type) || is_byte_fixed_array(s.target_type) {
        gen_byte_target_write(g, s, ix.expr, ix.index)
        return
    }

    // Try the unified address chain — covers `arr[i] = X`, `obj.field[i] = X`,
    // `a[i][j] = X`, and any deeper combination on fixed-size arrays. The
    // chain emits its own bounds checks per index step.
    if chain, chain_ok := build_address_chain(g, ix); chain_ok {
        elem_ptr := emit_address_chain(g, &chain)
        if chain.final_kind == .Struct {
            gen_struct_store_at(g, elem_ptr, chain.struct_name, s.value)
        } else {
            val := gen_expr(g, s.value, chain.final_type)
            emit(g, "  store %s %s, ptr %s", chain.final_type, val, elem_ptr)
        }
        return
    }

    // Chain fallback: VLA arrays (chain rejects them) and any other shape the
    // chain doesn't model. Today this is just the bare-ident-into-VLA case;
    // VLAs GEP by element type directly (no [N x T] wrapper).
    ident, ident_ok := ix.expr.(^Expr_Ident)
    if !ident_ok {
        codegen_fatal(g, s.span, "index assignment target must be a variable")
    }
    // Slice element write: load the data ptr from the slice header, bounds
    // check against the len cursor, GEP, store. Lets `add_element` and other
    // single-slot writes work on a Slice_Var directly without going through
    // the chain (chains model fixed-array indexing, not slice-deref).
    if sv, sv_ok := get_slice(g, ident.name); sv_ok {
        idx_raw := gen_expr(g, ix.index)
        idx := ensure_i64(g, idx_raw, ix.index)
        // Bound the index by .cap (the physical buffer size). Bounding by .len
        // would forbid append-at-len, which is exactly what `dst[dst.len] = src`
        // does. Cap is the storage extent.
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, sv.alloca, 2)
        cap_val := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
        emit_bounds_check(g, idx, cap_val, ident.name, s.span)
        // Load data pointer + GEP
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, sv.alloca, 0)
        data_ptr := fresh_tmp(g)
        emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
        elem_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, sv.elem_type, data_ptr, idx)
        if strings.has_prefix(sv.elem_type, "%class.") {
            elem_struct := sv.elem_type[len("%class."):]
            gen_struct_store_at(g, elem_ptr, elem_struct, s.value)
        } else {
            val := gen_expr(g, s.value, sv.elem_type)
            emit(g, "  store %s %s, ptr %s", sv.elem_type, val, elem_ptr)
        }
        return
    }
    av, av_ok := get_array(g, ident.name)
    if !av_ok {
        codegen_fatal(g, s.span, "'%s' is not an array", ident.name)
    }
    idx_raw := gen_expr(g, ix.index)
    idx := ensure_i64(g, idx_raw, ix.index)
    arr_cap: string
    if av.capacity_val != "" {
        arr_cap = av.capacity_val
    } else {
        arr_cap = fmt.tprintf("%d", usable_cap(&av))
    }
    emit_bounds_check(g, idx, arr_cap, ident.name, s.span)
    gep := fresh_tmp(g)
    if av.capacity_val != "" {
        emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", gep, av.elem_type, av.alloca, idx)
    } else {
        arr_type := array_var_type(&av)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", gep, arr_type, av.alloca, idx)
    }
    if strings.has_prefix(av.elem_type, "%class.") {
        elem_struct := av.elem_type[len("%class."):]
        gen_struct_store_at(g, gep, elem_struct, s.value)
    } else {
        val := gen_expr(g, s.value, av.elem_type)
        emit(g, "  store %s %s, ptr %s", av.elem_type, val, gep)
    }
}

// Handle: arr[low:high] = rhs — copy rhs elements into arr[low..high)
gen_slice_range_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    sl := s.target.(^Expr_Slice)
    // Resolve destination into (data_ptr, capacity, elem_type, name).
    // Supports: plain arrays, array classes, and field access chains.
    dst_data_ptr: string
    dst_cap_str: string   // capacity as LLVM value (literal or register)
    dst_capacity: int     // compile-time capacity (0 if runtime only)
    dst_elem_type: string
    dst_name: string
    dst_is_utf8: bool
    dst_resolved := false

    ident, ident_ok := sl.expr.(^Expr_Ident)

    // Path 1: Field access (e.g. result.indices[0:6])
    if !ident_ok {
        if fa, fa_ok := sl.expr.(^Expr_Field_Access); fa_ok {
            gen_field_access(g, fa)
            // Try as plain array field
            if av, av_ok := claim_field_array(g); av_ok {
                dst_data_ptr    = av.alloca
                dst_capacity  = av.capacity
                dst_cap_str   = av.capacity_val != "" ? av.capacity_val : fmt.tprintf("%d", av.capacity)
                dst_elem_type = av.elem_type
                dst_is_utf8   = av.is_utf8
                dst_name      = fa.field
                dst_resolved  = true
            }
        }
        if !dst_resolved {
            codegen_fatal(g, s.span, "slice assignment target must be a variable")
        }
    }

    // Path 2: Ident + slice variable (load data ptr + cap from header)
    if !dst_resolved && ident_ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            // Pull data ptr from field 0 and cap from field 2 (raw-memory range).
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, sv.alloca, 0)
            data_ptr := fresh_tmp(g)
            emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)

            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, 2)
            cap_val := fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)

            dst_data_ptr  = data_ptr
            dst_capacity  = 0  // runtime
            dst_cap_str   = cap_val
            dst_elem_type = sv.elem_type
            dst_is_utf8   = sv.is_utf8
            dst_name      = ident.name
            dst_resolved  = true
        }
    }

    // Path 3: Ident + plain array / array class
    if !dst_resolved && ident_ok {
        av, av_ok := get_array(g, ident.name)
        if !av_ok {
            codegen_fatal(g, s.span, "'%s' is not an array, array class, or slice", ident.name)
        }
        dst_data_ptr    = av.alloca
        dst_capacity  = av.capacity
        dst_cap_str   = av.capacity_val != "" ? av.capacity_val : fmt.tprintf("%d", av.capacity)
        dst_elem_type = av.elem_type
        dst_is_utf8   = av.is_utf8
        dst_name      = ident.name
        dst_resolved  = true
    }

    // Compute low
    low := gen_expr(g, sl.low)

    // Resolve the RHS into an Array_Var (or slice).
    // Must happen before high computation to support open-ended slices [low:].
    rhs_av: Array_Var
    rhs_resolved := false
    rhs_is_slice := false      // true when RHS is a []T slice (flat pointer, not fixed array)
    rhs_slice_len: string      // runtime length for slice RHS
    #partial switch rv in s.value {
    case ^Expr_Ident:
        if rav, rav_ok := get_array(g, rv.name); rav_ok {
            rhs_av = rav
            rhs_resolved = true
        } else if rsv, rsv_ok := get_struct(g, rv.name); rsv_ok {
            // RHS is an array class — GEP to its data field
            if rac_st, rac_ok := lookup_struct(g, rsv.struct_name); rac_ok && rac_st.is_array_class {
                rac_arr_idx := ac_array_field_index(rac_st)
                rac_elem    := ac_elem_ir_type(rac_st)
                rac_llvm    := struct_llvm_name(rsv.struct_name)
                rac_gep     := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", rac_gep, rac_llvm, rsv.alloca, rac_arr_idx)
                rhs_av = Array_Var{
                    alloca    = rac_gep,
                    capacity  = rac_st.array_cap,
                    elem_type = rac_elem,
                }
                rhs_resolved = true
            }
        } else if slv, slv_ok := get_slice(g, rv.name); slv_ok {
            // RHS is a []T slice — extract data pointer and length
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, slv.alloca, 0)
            data_ptr := fresh_tmp(g)
            emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
            rhs_av = Array_Var{
                alloca    = data_ptr,
                capacity  = 0,
                elem_type = slv.elem_type,
            }
            rhs_is_slice = true
            rhs_resolved = true
            // Load slice's valid-data length for open-ended high computation
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, slv.alloca, 1)
            rhs_slice_len = fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", rhs_slice_len, len_gep)
        }
        if !rhs_resolved {
            codegen_fatal(g, s.span, "'%s' is not an array or slice", rv.name)
        }
    case ^Expr_Array:
        // Give each literal a unique temp name so multiple slice assigns don't collide
        g.tmp_counter += 1
        rhs_tmp_name := fmt.tprintf("__slice_rhs%d", g.tmp_counter)
        rhs_cap := len(rv.elements)
        gen_array_assign(g, rhs_tmp_name, rhs_cap, dst_elem_type, s.value, dst_is_utf8)
        rhs_av, _ = get_array(g, rhs_tmp_name)
        rhs_resolved = true
    }
    if !rhs_resolved {
        codegen_fatal(g, s.span, "slice RHS must be a named array, slice, or array literal")
    }

    // Compute high — explicit or derived from RHS length for open-ended [low:]
    high: string
    if sl.high != nil {
        high = gen_expr(g, sl.high)
    } else if rhs_is_slice {
        // Open-ended slice with slice RHS: high = low + slice.len
        high = fresh_tmp(g)
        emit(g, "  %s = add i64 %s, %s", high, low, rhs_slice_len)
    } else {
        // Open-ended slice with fixed array RHS: high = low + capacity
        high = fresh_tmp(g)
        emit(g, "  %s = add i64 %s, %d", high, low, rhs_av.capacity)
    }

    // Bounds check against capacity (not current len) — we're writing, not reading.
    // This matches swizzle write behaviour: you can write to any slot within cap.
    dst_len := dst_cap_str

    // Bounds check low: must be 0 <= low < dst_len
    emit_bounds_check(g, low, dst_len, dst_name, s.span)

    // Bounds check high: must be high <= dst_len (allow high == dst_len for end-of-array slices)
    high_ok_lbl  := fresh_label(g, "slice.high.ok")
    high_err_lbl := fresh_label(g, "slice.high.err")
    high_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sgt i64 %s, %s", high_cmp, high, dst_len)
    emit(g, "  br i1 %s, label %%%s, label %%%s", high_cmp, high_err_lbl, high_ok_lbl)
    emit(g, "%s:", high_err_lbl)
    err_msg := fmt.tprintf("runtime error: slice assignment out of bounds: high %%lld > capacity %%lld for '%s'\n", dst_name)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s, i64 %s)", err_ptr, high, dst_len)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit(g, "%s:", high_ok_lbl)

    // Emit loop: for i = 0; i < (high - low); i++
    //   dst[low + i] = src[i]
    loop_lbl  := fresh_label(g, "slice.loop")
    body_lbl  := fresh_label(g, "slice.body")
    end_lbl   := fresh_label(g, "slice.end")

    i_ptr := fresh_tmp(g)
    emit(g, "  %s = alloca i64", i_ptr)
    emit(g, "  store i64 0, ptr %s", i_ptr)

    count := fresh_tmp(g)
    emit(g, "  %s = sub i64 %s, %s", count, high, low)

    emit(g, "  br label %%%s", loop_lbl)
    emit(g, "%s:", loop_lbl)
    i_cur := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", i_cur, i_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt i64 %s, %s", cmp, i_cur, count)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_lbl, end_lbl)

    emit(g, "%s:", body_lbl)

    // Load src[i] — use flat GEP for slices, array GEP for fixed arrays
    src_gep := fresh_tmp(g)
    if rhs_is_slice {
        emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", src_gep, rhs_av.elem_type, rhs_av.alloca, i_cur)
    } else {
        rhs_arr_type := array_var_type(&rhs_av)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", src_gep, rhs_arr_type, rhs_av.alloca, i_cur)
    }
    src_val := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", src_val, dst_elem_type, src_gep)

    // Store into dst[low + i]
    dst_idx := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, %s", dst_idx, low, i_cur)
    dst_arr_type := fmt.tprintf("[%d x %s]", dst_capacity, dst_elem_type)
    dst_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", dst_gep, dst_arr_type, dst_data_ptr, dst_idx)
    emit(g, "  store %s %s, ptr %s", dst_elem_type, src_val, dst_gep)

    // i++
    i_next := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, 1", i_next, i_cur)
    emit(g, "  store i64 %s, ptr %s", i_next, i_ptr)
    emit(g, "  br label %%%s", loop_lbl)

    emit(g, "%s:", end_lbl)
}

// Handle: arr[idx] — read element from array or slice
gen_index_expr :: proc(g: ^Codegen, e: ^Expr_Index) -> string {
    // Try unified address chain for chained access (obj.items[i], a[i][j], etc.)
    if chain, chain_ok := build_address_chain(g, e); chain_ok {
        addr := emit_address_chain(g, &chain)
        if chain.final_kind == .Scalar {
            return emit_load(g, chain.final_type, addr)
        }
        if chain.final_kind == .Struct {
            set_field_result(g, Struct_Var{alloca = addr, struct_name = chain.struct_name})
            return addr
        }
        if chain.final_kind == .Array {
            set_field_result(g, Array_Var{alloca = addr, capacity = chain.array_cap, elem_type = chain.array_elem})
            return addr
        }
        return emit_load(g, chain.final_type, addr)
    }

    // The expr should be an identifier naming an array or slice
    ident, ok := e.expr.(^Expr_Ident)
    if !ok {
        // Handle field access targets: input.keyboard.pressed[scancode]
        if fa, fa_ok := e.expr.(^Expr_Field_Access); fa_ok {
            gen_field_access(g, fa)
            if av, av_ok := claim_field_array(g); av_ok {
                idx_raw := gen_expr(g, e.index)
                idx := ensure_i64(g, idx_raw, e.index)
                arr_len := fmt.tprintf("%d", usable_cap(&av))
                emit_bounds_check(g, idx, arr_len, fa.field, e.span)
                arr_type := array_var_type(&av)
                gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", gep, arr_type, av.alloca, idx)
                val := fresh_tmp(g)
                emit(g, "  %s = load %s, ptr %s", val, av.elem_type, gep)
                return val
            }
            // Slice field: `s.field[i]` where `field` is a `[]T`. Route the
            // claimed Slice_Var through gen_slice_index for the same bounds-
            // checked deref-load path that bare slice idents use.
            if sv, sv_ok := claim_field_slice(g); sv_ok {
                return gen_slice_index(g, &sv, e)
            }
        }
        // Handle nested index: a[i][j] for multi-dimensional arrays
        if inner_idx, idx_ok := e.expr.(^Expr_Index); idx_ok {
            inner_ptr := gen_index_address(g, inner_idx)
            inner_type := expr_type(e.expr)
            if inner_fa, fa_ok := inner_type.(^Type_Fixed_Array); fa_ok {
                inner_elem := llvm_type_from_checker(inner_fa.elem)
                inner_arr_type := fmt.tprintf("[%d x %s]", inner_fa.size, inner_elem)
                idx_raw := gen_expr(g, e.index)
                idx := ensure_i64(g, idx_raw, e.index)
                arr_len := fmt.tprintf("%d", inner_fa.size)
                emit_bounds_check(g, idx, arr_len, "array", e.span)
                gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", gep, inner_arr_type, inner_ptr, idx)
                val := fresh_tmp(g)
                emit(g, "  %s = load %s, ptr %s", val, inner_elem, gep)
                return val
            }
        }
        codegen_fatal(g, e.span, "index target must be a variable")
    }

    // Check if it's a slice variable
    if sv, sv_ok := get_slice(g, ident.name); sv_ok {
        return gen_slice_index(g, &sv, e)
    }

    av, av_ok := get_array(g, ident.name)
    if !av_ok {
        codegen_fatal(g, e.span, "'%s' is not an array or slice", ident.name)
    }

    idx_raw := gen_expr(g, e.index)
    idx := ensure_i64(g, idx_raw, e.index)

    // Runtime bounds check — against capacity (compile-time) or capacity_val (VLA)
    arr_cap: string
    if av.capacity_val != "" {
        arr_cap = av.capacity_val
    } else {
        arr_cap = fmt.tprintf("%d", usable_cap(&av))
    }
    emit_bounds_check(g, idx, arr_cap, ident.name, e.span)

    // VLA: GEP by element type directly (no [N x T] wrapper)
    gep := fresh_tmp(g)
    if av.capacity_val != "" {
        emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", gep, av.elem_type, av.alloca, idx)
    } else {
        arr_type := array_var_type(&av)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", gep, arr_type, av.alloca, idx)
    }
    val := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", val, av.elem_type, gep)
    return val
}

// Address-of array element: &arr[i] — emit GEP to element, return pointer (no load).
gen_index_address :: proc(g: ^Codegen, e: ^Expr_Index) -> string {
    // Chain handles ident-rooted fixed-array and `obj.<fixed_arr>[i]` shapes.
    if chain, chain_ok := build_address_chain(g, e); chain_ok {
        return emit_address_chain(g, &chain)
    }

    // Slice: &slice[i] — chain rejects slice indexing today, so handle it here.
    // Bounds-check against the slice's total capacity (raw-memory range), then GEP
    // into its data pointer. `&slice[i]` is an address-of operation, so it's valid
    // anywhere in the underlying storage — not just within the populated region.
    if ident, ok := e.expr.(^Expr_Ident); ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            idx_raw := gen_expr(g, e.index)
            idx := ensure_i64(g, idx_raw, e.index)

            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, 2)
            slice_cap := fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", slice_cap, cap_gep)
            emit_bounds_check(g, idx, slice_cap, ident.name, e.span)

            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, sv.alloca, 0)
            data_ptr := fresh_tmp(g)
            emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)

            elem_ptr := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, sv.elem_type, data_ptr, idx)
            return elem_ptr
        }
    }

    // &field_access[i] where the field is a slice — same shape as the ident case,
    // sourced from a field-access-yielding-slice via claim_field_slice.
    if fa, fa_ok := e.expr.(^Expr_Field_Access); fa_ok {
        gen_field_access(g, fa)
        if sv, sv_ok := claim_field_slice(g); sv_ok {
            idx_raw := gen_expr(g, e.index)
            idx := ensure_i64(g, idx_raw, e.index)

            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, 2)
            slice_cap := fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", slice_cap, cap_gep)
            emit_bounds_check(g, idx, slice_cap, fa.field, e.span)

            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, sv.alloca, 0)
            data_ptr := fresh_tmp(g)
            emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)

            elem_ptr := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, sv.elem_type, data_ptr, idx)
            return elem_ptr
        }
    }

    codegen_fatal(g, e.span, "cannot take address of this index expression")
}

// ---------------------------------------------------------------------------
// Slice codegen
// ---------------------------------------------------------------------------

// Load the data pointer from a slice variable's { ptr, i64 } struct
gen_slice_data_ptr :: proc(g: ^Codegen, name: string) -> string {
    sv, _ := get_slice(g, name)
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, 0)
    data_ptr := fresh_tmp(g)
    emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
    return data_ptr
}

// Load the data pointer (field 0) from a slice variable's { ptr, i64, i64 } struct
gen_slice_ptr :: proc(g: ^Codegen, name: string) -> string {
    sv, _ := get_slice(g, name)
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, sv.alloca, 0)
    ptr_val := fresh_tmp(g)
    emit(g, "  %s = load ptr, ptr %s", ptr_val, ptr_gep)
    return ptr_val
}

// Load the cursor / valid-data length (field 1) from a slice variable.
gen_slice_len :: proc(g: ^Codegen, name: string) -> string {
    sv, _ := get_slice(g, name)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, sv.alloca, 1)
    len_val := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", len_val, len_gep)
    return len_val
}

// take(T, storage) — two forms:
//   take(T, &slice)     — cursor form: carve from slice.len, advance it.
//                         Cursor lives in the caller's slice header; multiple
//                         takes from the same storage share the cursor because
//                         every `&slice` resolves to the same header address.
//                         Inside a callee with `storage: ^[]byte`, the param
//                         already has the right shape — pass it directly
//                         without re-`&`.
//   take(T, &buf[i])    — positional form: typed view at the given address,
//                         no cursor mutation.
//
// The form is detected by the storage argument's type at the checker layer:
//   ^[]byte -> cursor form
//   ^byte   -> positional form
gen_expr_take :: proc(g: ^Codegen, e: ^Expr_Take) -> string {
    src_type := distinct_base(expr_type(e.storage))

    // Positional form: `take(T, &buf[i])` — view at the given address.
    // Required shape: source must be `&<byte_buffer>[<offset>]` so we can
    // bounds-check `offset + size_of(T) <= buf.cap`. Routes through
    // emit_byte_offset_ptr (same path as the byte-view mechanism).
    // Other ^byte sources (function returns, casts, FFI ptrs) carry no
    // size info — those are rejected here. Use the cursor form, or
    // construct a slice over the unchecked memory if you need it.
    if pt, ok := src_type.(^Type_Ptr); ok {
        if _, is_byte := pt.elem.(Type_Byte); is_byte {
            t_size := elem_byte_size(llvm_type_from_checker(e.resolved_type), g.checked)
            if un, un_ok := e.storage.(^Expr_Unary); un_ok && un.op == .Ampersand {
                if idx, idx_ok := un.operand.(^Expr_Index); idx_ok {
                    if elem_ptr, ok := emit_byte_offset_ptr(g, idx.expr, idx.index, t_size, "take", idx.span); ok {
                        return elem_ptr
                    }
                }
            }
            codegen_fatal(g, e.span, "positional take requires a &buf[i] source (byte slice or [N]byte) so the carve can be bounds-checked")
        }
    }

    // Cursor form: storage is ^[]byte. Two source shapes resolve to the same
    // Slice_Var by name:
    //   `&slice_var`         — Expr_Unary{Ampersand, Expr_Ident}: the local's
    //                          alloca address IS already a ptr to the slice
    //                          header.
    //   `slice_ptr_param`    — bare Expr_Ident with `^[]T` type: the slice-
    //                          param ABI binds the ident as a Slice_Var whose
    //                          alloca is the incoming ptr arg.
    // Either way, get_slice on the underlying name returns the right header.
    name := ""
    if un, un_ok := e.storage.(^Expr_Unary); un_ok && un.op == .Ampersand {
        if id, id_ok := un.operand.(^Expr_Ident); id_ok {
            name = id.name
        }
    } else if id, id_ok := e.storage.(^Expr_Ident); id_ok {
        name = id.name
    }
    if name == "" {
        codegen_fatal(g, e.span, "take's storage must be &slice_var or a slice-pointer parameter")
    }
    sv, sv_ok := get_slice(g, name)
    if !sv_ok {
        codegen_fatal(g, e.span, "take: '%s' is not a slice variable", name)
    }

    // Load storage's data pointer (field 0).
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, 0)
    data_ptr := fresh_tmp(g)
    emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)

    // Load storage's current cursor (field 1 = len).
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, sv.alloca, 1)
    cursor := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", cursor, len_gep)

    // Round cursor up to the take type's alignment. The data ptr is
    // over-aligned at the storage's source (sys_alloc gives page alignment;
    // stack `[]byte(N)` allocas get align 16) so a cursor that is a multiple
    // of `type_align` lands typed_ptr on a properly aligned address. Padding
    // bytes between old cursor and aligned cursor are simply wasted — the
    // contract is "take advances len; you don't get to address the gap."
    // Skip the math when type_align <= 1 (byte takes need no padding).
    advance_amount: string
    count_runtime: string
    elem_size: int
    type_align: int
    if e.count_expr != nil {
        // Runtime-counted slice: resolved_type is []T; elem is T.
        sl, _ := distinct_base(e.resolved_type).(^Type_Slice)
        elem_ir := llvm_type_from_checker(sl.elem)
        elem_size = elem_byte_size(elem_ir, g.checked)
        type_align = elem_alignment(elem_ir, g.checked)
        count_runtime = gen_expr(g, e.count_expr)
        advance_amount = fresh_tmp(g)
        emit(g, "  %s = mul i64 %s, %d", advance_amount, count_runtime, elem_size)
    } else {
        elem_ir := llvm_type_from_checker(e.resolved_type)
        elem_size = elem_byte_size(elem_ir, g.checked)
        type_align = elem_alignment(elem_ir, g.checked)
        advance_amount = fmt.tprintf("%d", elem_size)
    }
    aligned_cursor := cursor
    if type_align > 1 {
        bumped := fresh_tmp(g)
        emit(g, "  %s = add i64 %s, %d", bumped, cursor, type_align - 1)
        aligned_cursor = fresh_tmp(g)
        // Mask is -type_align (e.g. -8 = 0xFFFFFFFFFFFFFFF8), the two's-complement
        // pattern that clears the low log2(align) bits. LLVM accepts signed decimals.
        emit(g, "  %s = and i64 %s, %d", aligned_cursor, bumped, -type_align)
    }

    // Compute typed_ptr = &storage.data[aligned_cursor] (GEP by i8 to step bytes).
    typed_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, i64 %s", typed_ptr, data_ptr, aligned_cursor)

    new_len := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, %s", new_len, aligned_cursor, advance_amount)

    // Bounds check: new_len must not exceed cap. Take in a loop or take from
    // a too-small buffer triggers this rather than silently walking past the
    // end. (Cursor form only — positional take takes a raw pointer.)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, sv.alloca, 2)
    cap_val := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
    overflow := fresh_tmp(g)
    emit(g, "  %s = icmp sgt i64 %s, %s", overflow, new_len, cap_val)
    fail_label := fresh_label(g, "take.fail")
    ok_label := fresh_label(g, "take.ok")
    emit(g, "  br i1 %s, label %%%s, label %%%s", overflow, fail_label, ok_label)
    emit(g, "%s:", fail_label)
    loc := format_location(e.span.file, e.span.line, e.span.col)
    msg := fmt.tprintf("%s runtime error: take overflows storage: advance to %%lld exceeds cap %%lld for '%s'\n",
        loc, name)
    msg_global, msg_byte_len := get_string_literal(g, msg)
    msg_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", msg_ptr, msg_byte_len, msg_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s, i64 %s)", msg_ptr, new_len, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit(g, "%s:", ok_label)

    emit(g, "  store i64 %s, ptr %s", new_len, len_gep)

    // Runtime-counted slice form: allocate a fresh slice header that points at
    // typed_ptr with len=cap=count. The header is the caller-visible value;
    // typed_ptr is the data it views into the caller's storage. gen_take_decl
    // sees Type_Slice and binds a Slice_Var to this header.
    if e.count_expr != nil {
        hdr := fmt.tprintf("%%take.hdr.%d", g.tmp_counter)
        g.tmp_counter += 1
        emit_slice_alloca(g, hdr)
        h_ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, h_ptr_gep, hdr, 0)
        emit(g, "  store ptr %s, ptr %s", typed_ptr, h_ptr_gep)
        h_len_gep := fresh_tmp(g)
        emit_slice_gep(g, h_len_gep, hdr, 1)
        emit(g, "  store i64 %s, ptr %s", count_runtime, h_len_gep)
        h_cap_gep := fresh_tmp(g)
        emit_slice_gep(g, h_cap_gep, hdr, 2)
        emit(g, "  store i64 %s, ptr %s", count_runtime, h_cap_gep)
        return hdr
    }

    return typed_ptr
}

// Load the total capacity (field 2) from a slice variable.
gen_slice_cap :: proc(g: ^Codegen, name: string) -> string {
    sv, _ := get_slice(g, name)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, sv.alloca, 2)
    cap_val := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
    return cap_val
}

// Index into a slice: slice[idx] (value read).
// Bounded by len (valid-data cursor) — you can only read what's been written.
gen_slice_index :: proc(g: ^Codegen, sv: ^Slice_Var, e: ^Expr_Index) -> string {
    idx := gen_expr(g, e.index)

    // Load len from slice for bounds check
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, sv.alloca, 1)
    slice_len := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", slice_len, len_gep)

    // Get variable name for error message
    slice_name := "slice"
    if ident, ok := e.expr.(^Expr_Ident); ok {
        slice_name = ident.name
    }
    emit_bounds_check(g, idx, slice_len, slice_name, e.span)

    // Load data pointer from slice
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, 0)
    data_ptr := fresh_tmp(g)
    emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)

    // GEP to element
    elem_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, sv.elem_type, data_ptr, idx)
    // Struct element: don't load. Hand back the address and tag it as a
    // struct-result so the caller (memcpy on assign, field-access, etc.)
    // works against the slot in place — same idiom as the field-access
    // path. Loading would force the struct into a register and break the
    // memcpy on the next assignment site.
    if strings.has_prefix(sv.elem_type, "%class.") {
        struct_name := sv.elem_type[len("%class."):]
        set_field_result(g, Struct_Var{alloca = elem_ptr, struct_name = struct_name})
        return elem_ptr
    }
    val := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", val, sv.elem_type, elem_ptr)
    return val
}

// Create a slice from an array or another slice: arr[low:high]
gen_slice_expr :: proc(g: ^Codegen, e: ^Expr_Slice) -> string {
    // Resolve the slice source into a local union (no magic variables in all_vars)
    Slice_Source :: union { Array_Var, Slice_Var }
    source: Slice_Source

    if ident, ok := e.expr.(^Expr_Ident); ok {
        if av, av_ok := get_array(g, ident.name); av_ok {
            source = av
        } else if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            source = sv
        }
    } else if fa, ok := e.expr.(^Expr_Field_Access); ok {
        gen_field_access(g, fa)
        if sv, sv_ok := claim_field_slice(g); sv_ok {
            source = sv
        } else if av, av_ok := claim_field_array(g); av_ok {
            source = av
        }
    } else {
        codegen_fatal(g, e.span, "slice target must be a variable")
    }

    // Resolve start index
    start: string
    if e.low != nil {
        start = gen_expr(g, e.low)
    } else {
        start = "0"
    }

    switch src in source {
    case Array_Var:
        // Slicing an array
        end: string
        if e.high != nil {
            end = gen_expr(g, e.high)
        } else if src.capacity_val != "" {
            // VLA: use runtime capacity
            end = src.capacity_val
        } else {
            end = fmt.tprintf("%d", src.capacity)
        }

        slice_cap := fresh_tmp(g)
        emit(g, "  %s = sub i64 %s, %s", slice_cap, end, start)

        av := src
        arr_type := array_var_type(&av)
        data_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", data_ptr, arr_type, src.alloca, start)
        // Sub-slice gives len=cap=(end-start): no preserved growth room beyond the carved range.
        return emit_build_temp_slice(g, data_ptr, slice_cap, slice_cap)

    case Slice_Var:
        // Re-slicing a slice
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, src.alloca, 0)
        orig_data := fresh_tmp(g)
        emit(g, "  %s = load ptr, ptr %s", orig_data, data_gep)

        end: string
        if e.high != nil {
            end = gen_expr(g, e.high)
        } else {
            // Open-ended `s[a:]` defaults end to the source's capacity (raw-memory range).
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, src.alloca, 2)
            end = fresh_tmp(g)
            emit(g, "  %s = load i64, ptr %s", end, cap_gep)
        }

        new_cap := fresh_tmp(g)
        emit(g, "  %s = sub i64 %s, %s", new_cap, end, start)

        new_data := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", new_data, src.elem_type, orig_data, start)
        // Sub-slice gives len=cap=(end-start).
        return emit_build_temp_slice(g, new_data, new_cap, new_cap)
    }

    codegen_fatal(g, e.span, "slice target is not an array or slice")
}

// Assign a slice expression to an inferred-type variable: x := arr[1:3]
gen_slice_assign_inferred :: proc(g: ^Codegen, name: string, value: Expr) {
    // Determine elem type from the source expression
    elem_t := "i64"
    utf8 := false
    sentinel := false
    if sl, ok := value.(^Expr_Slice); ok {
        if ident, id_ok := sl.expr.(^Expr_Ident); id_ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                elem_t = av.elem_type
                utf8 = av.is_utf8
                sentinel = av.has_sentinel
            } else if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                elem_t = sv.elem_type
                utf8 = sv.is_utf8
                sentinel = sv.has_sentinel
            } else if stv, stv_ok := get_struct(g, ident.name); stv_ok {
                if st, st_ok := lookup_struct(g, stv.struct_name); st_ok && st.is_array_class {
                    elem_t = ac_elem_ir_type(st)
                    utf8 = ac_is_utf8(st)
                }
            }
        } else if sl.expr != nil {
            // Field access or other expr — check type annotation
            sl_type := expr_type(sl.expr)
            if slice_t, st_ok := sl_type.(^Type_Slice); st_ok {
                elem_t = llvm_type_from_checker(slice_t.elem)
                _, utf8 = slice_t.elem.(Type_Utf8)
                sentinel = slice_t.has_sentinel
            } else if fa_t, fa_ok := sl_type.(^Type_Fixed_Array); fa_ok {
                elem_t = llvm_type_from_checker(fa_t.elem)
                _, utf8 = fa_t.elem.(Type_Utf8)
                sentinel = fa_t.has_sentinel
            }
        }
    }

    src := gen_expr(g, value)

    if _, slice_exists := get_slice(g, name); !slice_exists {
        alloca_name := fmt.tprintf("%%%s.slice", name)
        emit_slice_alloca(g, alloca_name)
        g.all_vars[name] = Slice_Var{
            alloca       = alloca_name,
            elem_type    = elem_t,
            is_utf8      = utf8,
            has_sentinel = sentinel,
        }
    }

    sv, _ := get_slice(g, name)

    // Copy whole slice header { ptr, len, cap } from source into destination.
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", sv.alloca, src)
}

// Single point of truth for "store a slice value into a destination pointer".
// Mirrors gen_store_struct_into / gen_store_array_into for slice IR
// ({ ptr, i64, i64 }, 24 bytes). gen_expr on any slice-valued expression
// returns a pointer to a slice descriptor, so almost every case is a 24-byte
// memcpy.
gen_store_slice_into :: proc(g: ^Codegen, dst_ptr: string, value: Expr) {
    if value == nil {
        ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, ptr_gep, dst_ptr, 0)
        emit(g, "  store ptr null, ptr %s", ptr_gep)
        len_gep := fresh_tmp(g)
        emit_slice_gep(g, len_gep, dst_ptr, 1)
        emit(g, "  store i64 0, ptr %s", len_gep)
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, dst_ptr, 2)
        emit(g, "  store i64 0, ptr %s", cap_gep)
        return
    }
    src := gen_expr(g, value)
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", dst_ptr, src)
}

// Assign a slice-typed expression (e.g. alloc()) to a named variable.
// The expression must return a { ptr, i64, i64 } alloca.
gen_slice_from_expr :: proc(g: ^Codegen, name: string, value: Expr, elem_type: string, is_utf8: bool = false, has_sentinel: bool = false) {
    src := gen_expr(g, value)

    if _, slice_exists := get_slice(g, name); !slice_exists {
        alloca_name := fmt.tprintf("%%%s.slice", name)
        emit_slice_alloca(g, alloca_name)
        g.all_vars[name] = Slice_Var{
            alloca       = alloca_name,
            elem_type    = elem_type,
            is_utf8      = is_utf8,
            has_sentinel = has_sentinel,
        }
    }

    sv, _ := get_slice(g, name)

    // Copy whole slice header { ptr, len, cap } from source into destination.
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 24, i1 false)", sv.alloca, src)
}

// ---------------------------------------------------------------------------
// Byte-buffer reinterpret codegen
//
// Covers []byte, [N]byte, and Array(byte, N). All three share the same shape:
//   1. Resolve the buffer to (data_ptr, cap_val)
//   2. Check offset + size <= cap
//   3. GEP by i8 at the offset, store/load sized by value type
// The only real difference between buffer kinds is step 1.
// ---------------------------------------------------------------------------

// True when `expr` names a byte buffer that resolve_byte_target can handle.
// Used by gen_stmt to decide whether a typed declaration should route through
// the reinterpret-read path. Mirrors the shapes resolve_byte_target accepts.
codegen_is_byte_buffer_source :: proc(g: ^Codegen, expr: Expr) -> bool {
    if ident, ok := expr.(^Expr_Ident); ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok && sv.elem_type == "i8" {
            return true
        }
        if av, av_ok := get_array(g, ident.name); av_ok && av.elem_type == "i8" {
            return true
        }
        return false
    }
    if _, ok := expr.(^Expr_Field_Access); ok {
        // Field access carries a checker type from type-checking; inspect it.
        src_type := expr_type(expr)
        return is_byte_slice(src_type) || is_byte_fixed_array(src_type)
    }
    return false
}

// Resolve any byte-buffer source expression to (data_ptr, cap_val).
//
// Handles:
//   - Expr_Ident naming a []byte slice variable      → load ptr/cap from fat pointer
//   - Expr_Ident naming a [N]byte array (incl. VLA)  → alloca is the data ptr; cap is literal or runtime
//   - Expr_Field_Access yielding a byte slice field  → same as slice ident, via claim_field_slice
//   - Expr_Field_Access yielding a byte array field  → same as array ident, via claim_field_array
//     (Array(byte, N) reaches here post-desugar as `.items` field access.)
resolve_byte_target :: proc(g: ^Codegen, expr: Expr, span: Span) -> (data_ptr: string, cap_val: string, ok: bool) {
    resolve_slice :: proc(g: ^Codegen, sv: Slice_Var) -> (string, string) {
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, sv.alloca, 0)
        data_ptr := fresh_tmp(g)
        emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
        // Byte-view / let-binding addresses raw storage — bound by cap, not len.
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, sv.alloca, 2)
        cap_val := fresh_tmp(g)
        emit(g, "  %s = load i64, ptr %s", cap_val, cap_gep)
        return data_ptr, cap_val
    }
    resolve_array :: proc(g: ^Codegen, av: Array_Var) -> (string, string) {
        if av.capacity_val != "" {
            return av.alloca, av.capacity_val
        }
        av_copy := av
        return av.alloca, fmt.tprintf("%d", usable_cap(&av_copy))
    }

    if ident, id_ok := expr.(^Expr_Ident); id_ok {
        if sv, sv_ok := get_slice(g, ident.name); sv_ok && sv.elem_type == "i8" {
            d, c := resolve_slice(g, sv)
            return d, c, true
        }
        if av, av_ok := get_array(g, ident.name); av_ok && av.elem_type == "i8" {
            d, c := resolve_array(g, av)
            return d, c, true
        }
    }
    if fa, fa_ok := expr.(^Expr_Field_Access); fa_ok {
        gen_field_access(g, fa)
        if sv, sv_ok := claim_field_slice(g); sv_ok {
            d, c := resolve_slice(g, sv)
            return d, c, true
        }
        if av, av_ok := claim_field_array(g); av_ok && av.elem_type == "i8" {
            d, c := resolve_array(g, av)
            return d, c, true
        }
    }
    // No printf here — callers add context-specific fatals when they need one.
    // Some callers (e.g. take's cursor-form probe) treat !ok as a shape miss
    // and fall through to a more informative error.
    return "", "", false
}

// Emit size-aware bounds check: offset + size <= cap.
// Resolve a byte-buffer expression + offset to a checked i8 element pointer.
// Validates `[offset, offset+size)` lies within the buffer's capacity (compile-
// time when both sides are known, runtime otherwise) and returns the GEP
// result. All three byte-buffer entry points (view, read, write) funnel
// through this helper. `offset_expr` may be nil (treated as 0).
emit_byte_offset_ptr :: proc(g: ^Codegen, buf_expr: Expr, offset_expr: Expr, size: int, label: string, span: Span) -> (elem_ptr: string, ok: bool) {
    data_ptr, cap_val, resolved := resolve_byte_target(g, buf_expr, span)
    if !resolved { return "", false }

    offset := "0"
    if offset_expr != nil {
        offset_raw := gen_expr(g, offset_expr)
        offset = ensure_i64(g, offset_raw, offset_expr)
    }
    emit_byte_size_bounds_check(g, cap_val, offset, size, label)

    elem_ptr = fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, i64 %s", elem_ptr, data_ptr, offset)
    return elem_ptr, true
}

// Address of a byte-buffer element, widened to a typed-pointer view of
// `target_size` bytes. Used for `^T = &buf[i]` where buf is a byte slice
// or [N]byte.
gen_byte_view_address :: proc(g: ^Codegen, idx: ^Expr_Index, target_size: int) -> string {
    elem_ptr, ok := emit_byte_offset_ptr(g, idx.expr, idx.index, target_size, "view", idx.span)
    if !ok {
        codegen_fatal(g, idx.span, "byte view source must be a byte slice or [N]byte")
    }
    return elem_ptr
}

emit_byte_size_bounds_check :: proc(g: ^Codegen, cap_val: string, low: string, size: int, label: string) {
    end_offset := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, %d", end_offset, low, size)
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt i64 %s, %s", cmp, end_offset, cap_val)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, err_lbl, ok_lbl)
    emit(g, "%s:", err_lbl)
    err_msg := fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%lld + %d > capacity %%lld\n", label, size)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s, i64 %s)", err_ptr, low, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit(g, "%s:", ok_lbl)
}

// Get the data pointer from a Slice_Var. Used by non-byte-buffer code
// paths that deal with generic slices.
slice_var_data_ptr :: proc(g: ^Codegen, sv: ^Slice_Var) -> string {
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, 0)
    data_ptr := fresh_tmp(g)
    emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
    return data_ptr
}

// Write a sized value into a byte buffer at `offset`:
//     buf[offset]      = value   (index form)
//     buf[low:low+N]   = value   (slice form — caller passes sl.low as offset_expr)
// `offset_expr` may be nil, in which case offset is 0 (matches the []T[:hi] case).
gen_byte_target_write :: proc(g: ^Codegen, s: ^Stmt_Assign, buf_expr: Expr, offset_expr: Expr) {
    val_type := s.assign_value_type
    val_ir_type := llvm_type_from_checker(val_type)
    val_size := checker_type_byte_size(val_type)

    elem_ptr, ok := emit_byte_offset_ptr(g, buf_expr, offset_expr, val_size, "write", s.span)
    if !ok {
        codegen_fatal(g, s.span, "byte buffer write target must be a byte slice or [N]byte")
    }

    if sd := as_struct_body(val_type); sd != nil {
        val := gen_expr(g, s.value)
        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", elem_ptr, val, val_size)
    } else {
        val := gen_expr(g, s.value)
        // `align 1` — the offset is user-chosen so the address could be anything.
        // Lying here (omitting the annotation, which defaults to natural alignment)
        // would let LLVM optimize as if `&buf[off]` were aligned to sizeof(T).
        emit(g, "  store %s %s, ptr %s, align 1", val_ir_type, val, elem_ptr)
    }
}

// Read a sized value from a byte buffer at `offset` into a newly-declared variable:
//     x : T = buf[offset]       (index form)
//     x : T = buf[low:low+N]    (slice form — caller passes sl.low as offset_expr)
// `offset_expr` may be nil, in which case offset is 0.
gen_byte_target_read :: proc(g: ^Codegen, name: string, buf_expr: Expr, offset_expr: Expr, span: Span, target_type: Type) {
    target_ir_type := llvm_type_from_checker(target_type)
    target_size := checker_type_byte_size(target_type)

    elem_ptr, ok := emit_byte_offset_ptr(g, buf_expr, offset_expr, target_size, "read", span)
    if !ok {
        codegen_fatal(g, span, "byte buffer read source must be a byte slice or [N]byte")
    }

    alloca_name := fmt.tprintf("%%%s", name)
    if sd := as_struct_body(target_type); sd != nil {
        emit(g, "  %s = alloca %s", alloca_name, target_ir_type)
        emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", alloca_name, elem_ptr, target_size)
        g.all_vars[name] = Struct_Var{alloca = alloca_name, struct_name = struct_key(sd)}
    } else {
        val := fresh_tmp(g)
        // `align 1` on the byte-buffer load (offset user-chosen); the store
        // into the local alloca stays natural since the alloca is aligned.
        emit(g, "  %s = load %s, ptr %s, align 1", val, target_ir_type, elem_ptr)
        emit(g, "  %s = alloca %s", alloca_name, target_ir_type)
        emit(g, "  store %s %s, ptr %s", target_ir_type, val, alloca_name)
        g.all_vars[name] = Scalar_Var{alloca_name}
    }
}

// ---------------------------------------------------------------------------
// Array class codegen
// ---------------------------------------------------------------------------

// Initialize an array class variable from an array literal: buf : Buffer = [1, 2, 3]
gen_array_class_literal_init :: proc(g: ^Codegen, name: string, st: ^Scope_Body, value: Expr) {
    llvm_name := struct_llvm_name(st.name)
    elem_type := ac_elem_ir_type(st)
    arr_fi := ac_array_field_index(st)
    len_fi := ac_len_field_index(st)

    // Alloca the struct if not already present
    if _, already := get_struct(g, name); !already {
        alloca_name := fmt.tprintf("%%%s", name)
        emit(g, "  %s = alloca %s", alloca_name, llvm_name)
        // Zero-init the entire struct
        total := struct_byte_size(st, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", alloca_name, total)
        g.all_vars[name] = Struct_Var{
            alloca = alloca_name,
            struct_name = st.name,
        }
    }

    sv, _ := get_struct(g, name)

    al, al_ok := value.(^Expr_Array)
    if !al_ok { return }

    // GEP to array data field
    arr_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", arr_gep, llvm_name, sv.alloca, arr_fi)

    // Store each element
    arr_type := fmt.tprintf("[%d x %s]", st.array_cap, elem_type)
    for elem, i in al.elements {
        val := gen_expr(g, elem, elem_type)
        elem_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %d", elem_gep, arr_type, arr_gep, i)
        emit(g, "  store %s %s, ptr %s", elem_type, val, elem_gep)
    }

    // Set len = number of elements in the literal
    len_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", len_gep, llvm_name, sv.alloca, len_fi)
    emit(g, "  store i64 %d, ptr %s", len(al.elements), len_gep)

    // Set cap = compile-time array capacity (usable slots, minus sentinel if utf8)
    cap_fi := ac_cap_field_index(st)
    if cap_fi >= 0 {
        cap_val := st.array_cap
        if ac_is_utf8(st) { cap_val -= 1 }
        cap_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", cap_gep, llvm_name, sv.alloca, cap_fi)
        emit(g, "  store i64 %d, ptr %s", cap_val, cap_gep)
    }
}

// Initialize a utf8 array class from a string literal.
// Copies the string bytes (including null terminator) into the array data field,
// and sets len = string length (excluding null terminator).
gen_array_class_string_init :: proc(g: ^Codegen, name: string, st: ^Scope_Body, str_lit: ^Expr_String) {
    llvm_name := struct_llvm_name(st.name)
    arr_fi := ac_array_field_index(st)
    len_fi := ac_len_field_index(st)

    // Alloca the struct if not already present
    if _, already := get_struct(g, name); !already {
        alloca_name := fmt.tprintf("%%%s", name)
        emit(g, "  %s = alloca %s", alloca_name, llvm_name)
        // Zero-init the entire struct
        total := struct_byte_size(st, g.checked)
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %d, i1 false)", alloca_name, total)
        g.all_vars[name] = Struct_Var{
            alloca = alloca_name,
            struct_name = st.name,
        }
    }

    sv, _ := get_struct(g, name)

    // Get the global string constant
    global_name, byte_len := get_string_literal(g, str_lit.value)
    str_len := byte_len - 1 // exclude null terminator from len

    // GEP to array data field
    arr_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", arr_gep, llvm_name, sv.alloca, arr_fi)

    // Copy string bytes (including null terminator) into array data
    copy_len := byte_len
    if copy_len > st.array_cap { copy_len = st.array_cap }
    src_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", src_ptr, byte_len, global_name)
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %d, i1 false)", arr_gep, src_ptr, copy_len)

    // Set len = string length (excluding null terminator)
    actual_len := str_len
    if actual_len > st.array_cap - 1 { actual_len = st.array_cap - 1 }
    len_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", len_gep, llvm_name, sv.alloca, len_fi)
    emit(g, "  store i64 %d, ptr %s", actual_len, len_gep)

    // Set cap = compile-time array capacity (usable slots, minus sentinel if utf8)
    cap_fi := ac_cap_field_index(st)
    if cap_fi >= 0 {
        cap_val := st.array_cap
        if ac_is_utf8(st) { cap_val -= 1 }
        cap_gep := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", cap_gep, llvm_name, sv.alloca, cap_fi)
        emit(g, "  store i64 %d, ptr %s", cap_val, cap_gep)
    }
}

// Print an array class variable — prints elements up to len
gen_print_array_class :: proc(g: ^Codegen, stv: ^Struct_Var, st: ^Scope_Body) {
    llvm_name := struct_llvm_name(st.name)
    elem_type := ac_elem_ir_type(st)
    arr_fi := ac_array_field_index(st)
    len_fi := ac_len_field_index(st)

    // Load len
    len_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", len_gep, llvm_name, stv.alloca, len_fi)
    cur_len := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", cur_len, len_gep)

    // GEP to array field
    arr_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", arr_gep, llvm_name, stv.alloca, arr_fi)

    arr_type := fmt.tprintf("[%d x %s]", st.array_cap, elem_type)

    // Print "[" prefix
    open_name, open_len := get_string_literal(g, "[")
    open_str := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", open_str, open_len, open_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", open_str)

    // Loop: for i = 0; i < len; i++
    i_alloca := fresh_tmp(g)
    emit(g, "  %s = alloca i64", i_alloca)
    emit(g, "  store i64 0, ptr %s", i_alloca)

    loop_label := fmt.tprintf("ac_print_%d", g.tmp_counter)
    g.tmp_counter += 1
    body_label := fmt.tprintf("ac_body_%d", g.tmp_counter)
    g.tmp_counter += 1
    end_label := fmt.tprintf("ac_end_%d", g.tmp_counter)
    g.tmp_counter += 1

    emit(g, "  br label %%%s", loop_label)
    emit(g, "%s:", loop_label)
    i_val := fresh_tmp(g)
    emit(g, "  %s = load i64, ptr %s", i_val, i_alloca)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt i64 %s, %s", cmp, i_val, cur_len)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, body_label, end_label)

    emit(g, "%s:", body_label)
    // Print ", " separator if i > 0
    cmp_zero := fresh_tmp(g)
    emit(g, "  %s = icmp sgt i64 %s, 0", cmp_zero, i_val)
    sep_label := fmt.tprintf("ac_sep_%d", g.tmp_counter)
    g.tmp_counter += 1
    nosep_label := fmt.tprintf("ac_nosep_%d", g.tmp_counter)
    g.tmp_counter += 1
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp_zero, sep_label, nosep_label)
    emit(g, "%s:", sep_label)
    sep_name, sep_len := get_string_literal(g, ", ")
    sep_str := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", sep_str, sep_len, sep_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", sep_str)
    emit(g, "  br label %%%s", nosep_label)
    emit(g, "%s:", nosep_label)

    // Load and print element
    elem_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i64 0, i64 %s", elem_gep, arr_type, arr_gep, i_val)
    elem_val := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", elem_val, elem_type, elem_gep)

    // Print based on element type
    if elem_type == "double" {
        fn, fl := get_string_literal(g, "%f")
        fp := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fp, fl, fn)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, double %s)", fp, elem_val)
    } else {
        fn, fl := get_string_literal(g, "%lld")
        fp := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fp, fl, fn)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s)", fp, elem_val)
    }

    // i++
    next_i := fresh_tmp(g)
    emit(g, "  %s = add i64 %s, 1", next_i, i_val)
    emit(g, "  store i64 %s, ptr %s", next_i, i_alloca)
    emit(g, "  br label %%%s", loop_label)

    emit(g, "%s:", end_label)
    close_name, close_len := get_string_literal(g, "]")
    close_str := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", close_str, close_len, close_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", close_str)
}

