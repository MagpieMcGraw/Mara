package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Array class VLA helpers
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Slice IR helpers (emit_raw with strings.concatenate to avoid fmt brace issues)
// ---------------------------------------------------------------------------

// GEP into a slice header by field index — see SLICE constants (codegen.odin)
// for the canonical len/cap/ptr ordering.
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

// Store an i64 value (SSA name or literal like "0", "42") into the slot
// addressed by `field_gep`, truncating to the layout's storage type if
// narrower than i64. The caller does the GEP and passes the result here;
// this lets sites that reuse the gep continue to do so.
// Store at the slice header's natural len/cap width. Caller must pass
// the value already at slice_layout.len_ir / cap_ir width. Integer
// literals are width-agnostic in IR so they pass through unchanged.
emit_typed_store_len :: proc(g: ^Codegen, val: string, field_gep: string) {
    emit_store(g, slice_layout.len_ir, val, field_gep)
}

emit_typed_store_cap :: proc(g: ^Codegen, val: string, field_gep: string) {
    emit_store(g, slice_layout.cap_ir, val, field_gep)
}

// Load len/cap from `field_gep` at natural width — no zext to i64.
// Callers operate at slice_layout.len_ir / cap_ir (today: i32). Sites
// that genuinely need a wider arithmetic context insert an explicit
// conversion at use rather than paying for the round-trip here.
emit_typed_load_len :: proc(g: ^Codegen, result: string, field_gep: string) {
    emit_load_into(g, result, slice_layout.len_ir, field_gep)
}

emit_typed_load_cap :: proc(g: ^Codegen, result: string, field_gep: string) {
    emit_load_into(g, result, slice_layout.cap_ir, field_gep)
}

// Slice args are passed by pointer-to-header — fat pointers are reference
// types in Mara, so cursor / ptr mutations through them propagate to the
// caller's slice. `val` must be a pointer to a slice descriptor alloca.
slice_arg_str :: proc(val: string) -> string {
    return strings.concatenate({"ptr ", val})
}

// Copy a `[..N]T` partial array from src into dst (both are pointers to a
// `{len, cap, ptr, [N x T]}` header). The trailing elements live inline, so
// the byte-for-byte memcpy lands the destination's `ptr` field still aliased
// to the source's elements — re-anchor it to `&dst.elements` so reads through
// the copy hit its own storage. Without that re-store, dst silently observes
// and clobbers src.
partial_array_copy :: proc(g: ^Codegen, dst_ptr: string, src_ptr: string, elem_ir: string, alloc_cap: int) {
    elem_bytes := elem_byte_size(elem_ir, g.checked)
    total_bytes := slice_header_bytes + alloc_cap * elem_bytes
    emit_memcpy(g, dst_ptr, src_ptr, total_bytes)
    ir_type := partial_array_ir_type(elem_ir, alloc_cap)
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", dst_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, dst_ptr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
}

// Alloca a slice header (SLICE_IR_TYPE) and store data_ptr / len / cap into
// its fields. Returns the alloca ptr. Callers load from it to get the slice value.
emit_build_temp_slice :: proc(g: ^Codegen, data_ptr: string, len_val: string, cap_val: string) -> string {
    slice_alloca := fresh_tmp(g)
    emit_slice_alloca(g, slice_alloca)
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, slice_alloca, SLICE.ptr)
    emit_store(g, "ptr", data_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, slice_alloca, SLICE.len)
    emit_typed_store_len(g, len_val, len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, slice_alloca, SLICE.cap)
    emit_typed_store_cap(g, cap_val, cap_gep)
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
            emit_alloca(g, data_name, arr_type)
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
        emit_memset_zero(g, av.alloca, total_bytes)
        return
    }

    // Check if the value is a string literal (for utf8 arrays)
    if str_lit, ok := value.(^Expr_String); ok {
        global_name, byte_len := get_string_literal(g, str_lit.value)
        src_ptr := fresh_tmp(g)
        emit_string_gep(g, src_ptr, byte_len, global_name)
        // Zero-initialize first, then copy string bytes over
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit_memset_zero(g, av.alloca, total_bytes)
        emit_memcpy(g, av.alloca, src_ptr, byte_len)
        return
    }

    // Check if the value is a compiler intrinsic (#caller_name, #caller_span) — same as string literal
    if intrinsic, ok := value.(^Expr_Compiler_Intrinsic); ok {
        global_name, byte_len := get_string_literal(g, intrinsic.resolved_value)
        src_ptr := fresh_tmp(g)
        emit_string_gep(g, src_ptr, byte_len, global_name)
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit_memset_zero(g, av.alloca, total_bytes)
        emit_memcpy(g, av.alloca, src_ptr, byte_len)
        return
    }

    // Check if the value is an array literal
    if arr_lit, ok := value.(^Expr_Array); ok {
        // Zero-init first (handles undersized literals + sentinel), then store each element
        if len(arr_lit.elements) < alloc_cap {
            total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
            emit_memset_zero(g, av.alloca, total_bytes)
        }
        for elem, i in arr_lit.elements {
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, arr_type, av.alloca, i)
            emit_store(g, elem_type, val, gep)
        }
    } else if sl, ok := value.(^Expr_Struct_Literal); ok && sl.array_values != nil {
        // Distinct-fixed-array struct literal (Quat{...}). Zero-init the slab
        // then store each non-nil slot; nil entries were checker-marked as
        // zero-fill.
        total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
        emit_memset_zero(g, av.alloca, total_bytes)
        for elem, i in sl.array_values {
            if elem == nil { continue }
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, arr_type, av.alloca, i)
            emit_store(g, elem_type, val, gep)
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
            codegen_fatal(g, ident.span, CODE_ARRAY, ident.name)
        }
        dst, _ := get_array(g, name)

        // Copy all elements (always use capacity — full arrays). Counter
        // is slice_layout.len_ir wide; array capacities fit by construction.
        loop_bound := fmt.tprintf("%d", src.capacity)
        w := slice_layout.len_ir

        src_type := array_var_type(&src)
        dst_type := array_var_type(&dst)
        cond_label := fresh_label(g, "copy.cond")
        body_label := fresh_label(g, "copy.body")
        end_label  := fresh_label(g, "copy.end")

        idx_ptr := fresh_tmp(g)
        emit_alloca(g, idx_ptr, w)
        emit_store(g, w, "0", idx_ptr)
        emit_br(g, cond_label)

        emit_label(g, cond_label)
        idx := fresh_tmp(g)
        emit_load_into(g, idx, w, idx_ptr)
        cmp := fresh_tmp(g)
        emit(g, "  %s = icmp slt %s %s, %s", cmp, w, idx, loop_bound)
        emit_cond_br(g, cmp, body_label, end_label)

        emit_label(g, body_label)
        idx2 := fresh_tmp(g)
        emit_load_into(g, idx2, w, idx_ptr)
        src_gep := fresh_tmp(g)
        emit_array_gep_var(g, src_gep, src_type, src.alloca, idx2, w)
        val := fresh_tmp(g)
        emit_load_into(g, val, dst.elem_type, src_gep)
        dst_gep := fresh_tmp(g)
        emit_array_gep_var(g, dst_gep, dst_type, dst.alloca, idx2, w)
        emit_store(g, dst.elem_type, val, dst_gep)
        next := fresh_tmp(g)
        emit(g, "  %s = add %s %s, 1", next, w, idx2)
        emit_store(g, w, next, idx_ptr)
        emit_br(g, cond_label)

        emit_label(g, end_label)
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
                emit_array_gep_const(g, src_gep, src_arr_type, sr.alloca, i)
                val := fresh_tmp(g)
                emit_load_into(g, val, dst.elem_type, src_gep)
                dst_gep := fresh_tmp(g)
                emit_array_gep_const(g, dst_gep, dst_arr_type, dst.alloca, i)
                emit_store(g, dst.elem_type, val, dst_gep)
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
    if is_byte_slice(s.target_type) || is_byte_fixed_array(s.target_type) ||
       is_byte_partial_array(s.target_type) {
        gen_byte_target_write(g, s, ix.expr, ix.index)
        return
    }

    // Try the unified address chain — covers `arr[i] = X`, `obj.field[i] = X`,
    // `a[i][j] = X`, and any deeper combination on fixed-size arrays. The
    // chain emits its own bounds checks per index step.
    if chain, chain_ok := build_address_chain(g, ix); chain_ok {
        elem_ptr := emit_address_chain(g, &chain)
        apply_compound_load_substitute(g, s, elem_ptr, chain.final_type)
        if chain.final_kind == .Struct {
            gen_struct_store_at(g, elem_ptr, chain.struct_name, s.value)
        } else {
            val := gen_expr(g, s.value, chain.final_type)
            emit_store(g, chain.final_type, val, elem_ptr)
        }
        return
    }

    // Chain fallback: VLA arrays (chain rejects them) and any other shape the
    // chain doesn't model. Today this is just the bare-ident-into-VLA case;
    // VLAs GEP by element type directly (no [N x T] wrapper).
    ident, ident_ok := ix.expr.(^Expr_Ident)
    if !ident_ok {
        codegen_fatal(g, s.span, CODE_INDEX_ASSIGNMENT_TARGET_VARIABLE)
    }
    // Slice element write: load the data ptr from the slice header, bounds
    // check against the len cursor, GEP, store. Lets `add_element` and other
    // single-slot writes work on a Slice_Var directly without going through
    // the chain (chains model fixed-array indexing, not slice-deref).
    if sv, sv_ok := get_slice(g, ident.name); sv_ok {
        idx := gen_expr(g, ix.index, slice_layout.len_ir)
        // Bound the index by .cap (the physical buffer size). Bounding by .len
        // would forbid append-at-len, which is exactly what `dst[dst.len] = src`
        // does. Cap is the storage extent.
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
        cap_val := fresh_tmp(g)
        emit_typed_load_cap(g, cap_val, cap_gep)
        emit_bounds_check(g, idx, cap_val, ident.name, s.span)
        // Load data pointer + GEP
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
        data_ptr := fresh_tmp(g)
        emit_load_into(g, data_ptr, "ptr", data_gep)
        elem_ptr := fresh_tmp(g)
        emit_elem_gep(g, elem_ptr, sv.elem_type, data_ptr, idx, slice_layout.len_ir)
        if strings.has_prefix(sv.elem_type, "%class.") {
            elem_struct := sv.elem_type[len("%class."):]
            gen_struct_store_at(g, elem_ptr, elem_struct, s.value)
        } else {
            val := gen_expr(g, s.value, sv.elem_type)
            emit_store(g, sv.elem_type, val, elem_ptr)
        }
        return
    }
    av, av_ok := get_array(g, ident.name)
    if !av_ok {
        codegen_fatal(g, s.span, CODE_ARRAY, ident.name)
    }
    idx := gen_expr(g, ix.index, slice_layout.len_ir)
    arr_cap: string
    if av.capacity_val != "" {
        arr_cap = av.capacity_val
    } else {
        arr_cap = fmt.tprintf("%d", usable_cap(&av))
    }
    emit_bounds_check(g, idx, arr_cap, ident.name, s.span)
    gep := fresh_tmp(g)
    if av.capacity_val != "" {
        emit_elem_gep(g, gep, av.elem_type, av.alloca, idx, slice_layout.len_ir)
    } else {
        arr_type := array_var_type(&av)
        emit_array_gep_var(g, gep, arr_type, av.alloca, idx, slice_layout.len_ir)
    }
    if strings.has_prefix(av.elem_type, "%class.") {
        elem_struct := av.elem_type[len("%class."):]
        gen_struct_store_at(g, gep, elem_struct, s.value)
    } else {
        val := gen_expr(g, s.value, av.elem_type)
        emit_store(g, av.elem_type, val, gep)
    }
}

// Handle: arr[low:high] = rhs — copy rhs elements into arr[low..high)
gen_slice_range_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    sl := s.target.(^Expr_Slice)
    // Resolve destination through the unified array handle. Replaces three
    // hand-rolled paths (field-access, slice ident, array ident) that all
    // produced the same set of locals from different starting points.
    h, h_ok := resolve_array_handle(g, sl.expr)
    if !h_ok {
        // Match prior error: field access without an array/slice claim is a
        // different code than a bare unresolved ident.
        if _, fa_ok := sl.expr.(^Expr_Field_Access); fa_ok {
            codegen_fatal(g, s.span, CODE_SLICE_ASSIGNMENT_TARGET_VARIABLE)
        }
        if ident, ok := sl.expr.(^Expr_Ident); ok {
            codegen_fatal(g, s.span, CODE_ARRAY_ARRAY_CLASS_SLICE, ident.name)
        }
        codegen_fatal(g, s.span, CODE_SLICE_ASSIGNMENT_TARGET_VARIABLE)
    }

    dst_data_ptr   := emit_array_data(g, &h)
    dst_elem_type  := h.elem_type
    dst_is_utf8    := h.is_utf8
    dst_has_sentinel := h.has_sentinel
    dst_sentinel_val := h.sentinel_value
    // Pre-refactor bounds rule (preserved literally): fixed arrays bound
    // against user-visible capacity (excludes the sentinel slot), slices
    // and partial arrays bound against the raw header cap (which includes
    // the sentinel slot — so a brim-fill of a sentinel slice can still
    // overwrite the terminator). The sentinel write below guards that case
    // at runtime so the terminator survives whenever there's room for it.
    dst_capacity:  int     // compile-time fixed cap, 0 = runtime
    dst_cap_str:   string  // SSA value of the bounds-check upper limit
    if handle_is_fixed(&h) {
        dst_capacity = h.static_cap
        dst_cap_str  = h.static_cap_str != "" ? h.static_cap_str : fmt.tprintf("%d", h.static_cap)
    } else {
        dst_capacity = 0
        dst_cap_str  = emit_array_raw_cap(g, &h)
    }
    dst_name := ""
    if ident, ok := sl.expr.(^Expr_Ident); ok {
        dst_name = ident.name
    } else if fa, ok := sl.expr.(^Expr_Field_Access); ok {
        dst_name = fa.field
    }

    // Compute low at the slice header's natural width so the bounds
    // check and arithmetic below stay homogeneous.
    low := gen_expr(g, sl.low, slice_layout.len_ir)

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
        } else if slv, slv_ok := get_slice(g, rv.name); slv_ok {
            // RHS is a []T slice — extract data pointer and length
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, slv.alloca, SLICE.ptr)
            data_ptr := fresh_tmp(g)
            emit_load_into(g, data_ptr, "ptr", data_gep)
            rhs_av = Array_Var{
                alloca    = data_ptr,
                capacity  = 0,
                elem_type = slv.elem_type,
            }
            rhs_is_slice = true
            rhs_resolved = true
            // Load slice's valid-data length for open-ended high computation
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, slv.alloca, SLICE.len)
            rhs_slice_len = fresh_tmp(g)
            emit_typed_load_len(g, rhs_slice_len, len_gep)
        }
        if !rhs_resolved {
            codegen_fatal(g, s.span, CODE_ARRAY_SLICE, rv.name)
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
        codegen_fatal(g, s.span, CODE_SLICE_RHS_NAMED_ARRAY_SLICE)
    }

    // All slice arithmetic in this function operates at the header's
    // natural width — low, high, rhs_slice_len, the loop counter, and
    // the bounds checks are all w-typed. No widening/truncating dance.
    w := slice_layout.len_ir

    // Compute high — explicit or derived from RHS length for open-ended [low:]
    high: string
    if sl.high != nil {
        high = gen_expr(g, sl.high, w)
    } else if rhs_is_slice {
        // Open-ended slice with slice RHS: high = low + slice.len
        high = fresh_tmp(g)
        emit(g, "  %s = add %s %s, %s", high, w, low, rhs_slice_len)
    } else {
        // Open-ended slice with fixed array RHS: high = low + capacity
        high = fresh_tmp(g)
        emit(g, "  %s = add %s %s, %d", high, w, low, rhs_av.capacity)
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
    emit(g, "  %s = icmp sgt %s %s, %s", high_cmp, w, high, dst_len)
    emit_cond_br(g, high_cmp, high_err_lbl, high_ok_lbl)
    emit_label(g, high_err_lbl)
    err_msg := fmt.tprintf("runtime error: slice assignment out of bounds: high %%d > capacity %%d for '%s'\n", dst_name)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", err_ptr, w, high, w, dst_len)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, high_ok_lbl)

    // Emit loop: for i = 0; i < (high - low); i++
    //   dst[low + i] = src[i]
    loop_lbl  := fresh_label(g, "slice.loop")
    body_lbl  := fresh_label(g, "slice.body")
    end_lbl   := fresh_label(g, "slice.end")

    i_ptr := fresh_tmp(g)
    emit_alloca(g, i_ptr, w)
    emit_store(g, w, "0", i_ptr)

    count := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", count, w, high, low)

    emit_br(g, loop_lbl)
    emit_label(g, loop_lbl)
    i_cur := fresh_tmp(g)
    emit_load_into(g, i_cur, w, i_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", cmp, w, i_cur, count)
    emit_cond_br(g, cmp, body_lbl, end_lbl)

    emit_label(g, body_lbl)

    // Load src[i] — use flat GEP for slices, array GEP for fixed arrays.
    // GEP index is at the slice header's width (i_cur is `w`).
    src_gep := fresh_tmp(g)
    if rhs_is_slice {
        emit_elem_gep(g, src_gep, rhs_av.elem_type, rhs_av.alloca, i_cur, w)
    } else {
        rhs_arr_type := array_var_type(&rhs_av)
        emit_array_gep_var(g, src_gep, rhs_arr_type, rhs_av.alloca, i_cur, w)
    }
    src_val := fresh_tmp(g)
    emit_load_into(g, src_val, dst_elem_type, src_gep)

    // Store into dst[low + i]
    dst_idx := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", dst_idx, w, low, i_cur)
    dst_arr_type := fmt.tprintf("[%d x %s]", dst_capacity, dst_elem_type)
    dst_gep := fresh_tmp(g)
    emit_array_gep_var(g, dst_gep, dst_arr_type, dst_data_ptr, dst_idx, w)
    emit_store(g, dst_elem_type, src_val, dst_gep)

    // i++
    i_next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", i_next, w, i_cur)
    emit_store(g, w, i_next, i_ptr)
    emit_br(g, loop_lbl)

    emit_label(g, end_lbl)

    // Sentinel destinations rely on a terminator immediately after the written
    // region so C-style consumers stop at the right spot. Stamp dst[high] = 0
    // after the copy. Only safe when `high` is inside the physical buffer:
    // sentinel slices/partial-arrays reserve one extra slot (cap is N+1), so
    // writing at high <= N stays in-bounds; sentinel fixed arrays have
    // capacity = N with [N+1 x T] storage, so dst[high] hits the reserved
    // slot when high == capacity. Skip the write only when there is genuinely
    // no spare slot (high == physical buffer size); the bounds check above
    // already accepted high == raw cap, so emit a runtime guard.
    if dst_has_sentinel {
        // Physical buffer size: cap for slices/partial arrays (already includes
        // the +1), cap+1 for fixed arrays (capacity is user-visible N).
        phys_cap: string
        if dst_capacity != 0 {
            // Fixed array path: compile-time capacity, +1 reserved slot.
            phys_cap = fmt.tprintf("%d", dst_capacity + 1)
        } else {
            phys_cap = dst_cap_str
        }
        room_ok_lbl  := fresh_label(g, "sentinel.ok")
        room_skip_lbl := fresh_label(g, "sentinel.skip")
        room_cmp := fresh_tmp(g)
        emit(g, "  %s = icmp slt %s %s, %s", room_cmp, w, high, phys_cap)
        emit_cond_br(g, room_cmp, room_ok_lbl, room_skip_lbl)
        emit_label(g, room_ok_lbl)
        sent_gep := fresh_tmp(g)
        emit_elem_gep(g, sent_gep, dst_elem_type, dst_data_ptr, high, w)
        // GEP strides by elem type (so `[10, -1]i64` lands at the correct
        // byte offset) and the store is element-typed too, with the
        // declared sentinel value rather than a hardcoded 0.
        emit_store(g, dst_elem_type, fmt.tprintf("%d", dst_sentinel_val), sent_gep)
        emit_br(g, room_skip_lbl)
        emit_label(g, room_skip_lbl)
    }
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
                idx := gen_expr(g, e.index, slice_layout.len_ir)
                arr_len := fmt.tprintf("%d", usable_cap(&av))
                emit_bounds_check(g, idx, arr_len, fa.field, e.span)
                arr_type := array_var_type(&av)
                gep := fresh_tmp(g)
                emit_array_gep_var(g, gep, arr_type, av.alloca, idx, slice_layout.len_ir)
                val := fresh_tmp(g)
                emit_load_into(g, val, av.elem_type, gep)
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
                idx := gen_expr(g, e.index, slice_layout.len_ir)
                arr_len := fmt.tprintf("%d", inner_fa.size)
                emit_bounds_check(g, idx, arr_len, "array", e.span)
                gep := fresh_tmp(g)
                emit_array_gep_var(g, gep, inner_arr_type, inner_ptr, idx, slice_layout.len_ir)
                val := fresh_tmp(g)
                emit_load_into(g, val, inner_elem, gep)
                return val
            }
        }
        codegen_fatal(g, e.span, CODE_INDEX_TARGET_VARIABLE)
    }

    // Check if it's a slice variable
    if sv, sv_ok := get_slice(g, ident.name); sv_ok {
        return gen_slice_index(g, &sv, e)
    }

    av, av_ok := get_array(g, ident.name)
    if !av_ok {
        // Indexing a `::` string constant. The literal lives in a
        // module-level [N x i8] global, so we GEP+load the byte the
        // same way any other byte buffer would. Writes are already
        // blocked at type-check (TYPE_CANNOT_ASSIGN_CONSTANT_TYPE),
        // so this path only fires for reads.
        if const_expr, found := g.checked.table.constants[ident.name]; found {
            if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                global_name, byte_len := get_string_literal(g, lit.value)
                idx := gen_expr(g, e.index, slice_layout.len_ir)
                emit_bounds_check(g, idx, fmt.tprintf("%d", byte_len), ident.name, e.span)
                gep := fresh_tmp(g)
                emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, %s %s",
                    gep, byte_len, global_name, slice_layout.len_ir, idx)
                val := fresh_tmp(g)
                emit(g, "  %s = load i8, ptr %s", val, gep)
                return val
            }
        }
        codegen_fatal(g, e.span, CODE_ARRAY_SLICE, ident.name)
    }

    idx := gen_expr(g, e.index, slice_layout.len_ir)

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
        emit_elem_gep(g, gep, av.elem_type, av.alloca, idx, slice_layout.len_ir)
    } else {
        arr_type := array_var_type(&av)
        emit_array_gep_var(g, gep, arr_type, av.alloca, idx, slice_layout.len_ir)
    }
    val := fresh_tmp(g)
    emit_load_into(g, val, av.elem_type, gep)
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
            idx := gen_expr(g, e.index, slice_layout.len_ir)

            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
            slice_cap := fresh_tmp(g)
            emit_typed_load_cap(g, slice_cap, cap_gep)
            emit_bounds_check(g, idx, slice_cap, ident.name, e.span)

            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
            data_ptr := fresh_tmp(g)
            emit_load_into(g, data_ptr, "ptr", data_gep)

            elem_ptr := fresh_tmp(g)
            emit_elem_gep(g, elem_ptr, sv.elem_type, data_ptr, idx, slice_layout.len_ir)
            return elem_ptr
        }
    }

    // &field_access[i] where the field is a slice — same shape as the ident case,
    // sourced from a field-access-yielding-slice via claim_field_slice.
    if fa, fa_ok := e.expr.(^Expr_Field_Access); fa_ok {
        gen_field_access(g, fa)
        if sv, sv_ok := claim_field_slice(g); sv_ok {
            idx := gen_expr(g, e.index, slice_layout.len_ir)

            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
            slice_cap := fresh_tmp(g)
            emit_typed_load_cap(g, slice_cap, cap_gep)
            emit_bounds_check(g, idx, slice_cap, fa.field, e.span)

            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
            data_ptr := fresh_tmp(g)
            emit_load_into(g, data_ptr, "ptr", data_gep)

            elem_ptr := fresh_tmp(g)
            emit_elem_gep(g, elem_ptr, sv.elem_type, data_ptr, idx, slice_layout.len_ir)
            return elem_ptr
        }
    }

    codegen_fatal(g, e.span, CODE_CANNOT_TAKE_ADDRESS_INDEX_EXPRESSION)
}

// ---------------------------------------------------------------------------
// Slice codegen
// ---------------------------------------------------------------------------

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
// `dest_hdr` is an existing slice-header alloca to write into when supplied
// — used by gen_take_decl to skip the fresh `take.hdr.N` alloca + later
// memcpy when the destination is already NRVO-aliased to %sret. Empty
// string means "allocate a fresh header" (the historical behaviour).
// Only applies to the runtime-counted slice form; positional takes still
// return a raw element pointer.
gen_expr_take :: proc(g: ^Codegen, e: ^Expr_Take, dest_hdr: string = "") -> string {
    src_type := distinct_base(expr_type(e.storage))

    // Positional form: `let(T, &buf[i])` or `slice([:n]T, &buf[i])` — view at
    // the given address. Required shape: source is `&<byte_buffer>[<offset>]`
    // so we can bounds-check `offset + bytes <= buf.cap`. Routes through
    // emit_byte_offset_ptr (same path as the byte-view mechanism). Other
    // ^byte sources (function returns, casts, FFI ptrs) carry no size info —
    // those are rejected here.
    if pt, ok := src_type.(^Type_Ptr); ok {
        if _, is_byte := pt.elem.(Type_Byte); is_byte {
            w := slice_layout.len_ir
            // Bytes to view depends on the form. For `let(T, ...)` it's
            // sizeof(T). For `slice([:n]T, ...)` it's n * sizeof(elem).
            t_size := elem_byte_size(llvm_type_from_checker(e.resolved_type), g.checked)
            bytes_str := fmt.tprintf("%d", t_size)
            count_runtime := ""
            elem_size := t_size
            if e.count_expr != nil {
                // Slice form: compute count * sizeof(elem) at runtime.
                sl, _ := distinct_base(e.resolved_type).(^Type_Slice)
                elem_ir := llvm_type_from_checker(sl.elem)
                elem_size = elem_byte_size(elem_ir, g.checked)
                count_runtime = gen_expr(g, e.count_expr, w)
                bytes_tmp := fresh_tmp(g)
                emit(g, "  %s = mul %s %s, %d", bytes_tmp, w, count_runtime, elem_size)
                bytes_str = bytes_tmp
            }
            if un, un_ok := e.storage.(^Expr_Unary); un_ok && un.op == .Ampersand {
                if idx, idx_ok := un.operand.(^Expr_Index); idx_ok {
                    elem_ptr := ""
                    ok2 := false
                    if e.count_expr != nil {
                        elem_ptr, ok2 = emit_byte_offset_ptr_runtime(g, idx.expr, idx.index, bytes_str, "slice", idx.span)
                    } else {
                        elem_ptr, ok2 = emit_byte_offset_ptr(g, idx.expr, idx.index, t_size, "let", idx.span)
                    }
                    if ok2 {
                        if e.count_expr != nil {
                            // Build a fresh slice header pointing at elem_ptr
                            // with len = cap = count. Header lives in writable
                            // local memory (or NRVO'd into dest_hdr). Mirrors
                            // the cursor-form header construction below — the
                            // bytes the header points at are the source's, but
                            // the header itself is never reinterpreted from
                            // file bytes.
                            hdr := dest_hdr
                            if hdr == "" {
                                hdr = fmt.tprintf("%%slice.hdr.%d", g.tmp_counter)
                                g.tmp_counter += 1
                                emit_slice_alloca(g, hdr)
                            }
                            h_ptr_gep := fresh_tmp(g)
                            emit_slice_gep(g, h_ptr_gep, hdr, SLICE.ptr)
                            emit_store(g, "ptr", elem_ptr, h_ptr_gep)
                            h_len_gep := fresh_tmp(g)
                            emit_slice_gep(g, h_len_gep, hdr, SLICE.len)
                            emit_typed_store_len(g, count_runtime, h_len_gep)
                            h_cap_gep := fresh_tmp(g)
                            emit_slice_gep(g, h_cap_gep, hdr, SLICE.cap)
                            emit_typed_store_cap(g, count_runtime, h_cap_gep)
                            return hdr
                        }
                        return elem_ptr
                    }
                }
            }
            codegen_fatal(g, e.span, CODE_POSITIONAL_TAKE_REQUIRES_BUF_SOURCE)
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
        codegen_fatal(g, e.span, CODE_TAKE_STORAGE_SLICE_VAR_SLICE)
    }
    sv, sv_ok := get_slice(g, name)
    if !sv_ok {
        codegen_fatal(g, e.span, CODE_TAKE_SLICE_VARIABLE, name)
    }

    // Load storage's data pointer (field 0).
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
    data_ptr := fresh_tmp(g)
    emit_load_into(g, data_ptr, "ptr", data_gep)

    // Load storage's current cursor (field 1 = len).
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
    cursor := fresh_tmp(g)
    emit_typed_load_len(g, cursor, len_gep)

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
    // Everything below operates at slice_layout.len_ir — cursor / advance /
    // aligned_cursor / new_len / cap_val all live at the storage slice's
    // natural width. No widen/trunc dance.
    w := slice_layout.len_ir
    if e.count_expr != nil {
        // Runtime-counted slice: resolved_type is []T; elem is T.
        sl, _ := distinct_base(e.resolved_type).(^Type_Slice)
        elem_ir := llvm_type_from_checker(sl.elem)
        elem_size = elem_byte_size(elem_ir, g.checked)
        type_align = elem_alignment(elem_ir, g.checked)
        count_runtime = gen_expr(g, e.count_expr, w)
        advance_amount = fresh_tmp(g)
        emit(g, "  %s = mul %s %s, %d", advance_amount, w, count_runtime, elem_size)
    } else {
        elem_ir := llvm_type_from_checker(e.resolved_type)
        elem_size = elem_byte_size(elem_ir, g.checked)
        type_align = elem_alignment(elem_ir, g.checked)
        advance_amount = fmt.tprintf("%d", elem_size)
    }
    aligned_cursor := cursor
    if type_align > 1 {
        bumped := fresh_tmp(g)
        emit(g, "  %s = add %s %s, %d", bumped, w, cursor, type_align - 1)
        aligned_cursor = fresh_tmp(g)
        // Mask is -type_align — the two's-complement pattern that clears the
        // low log2(align) bits. LLVM accepts signed decimals at any width.
        emit(g, "  %s = and %s %s, %d", aligned_cursor, w, bumped, -type_align)
    }

    // Compute typed_ptr = &storage.data[aligned_cursor] (GEP by i8 to step bytes).
    typed_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", typed_ptr, data_ptr, w, aligned_cursor)

    new_len := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", new_len, w, aligned_cursor, advance_amount)

    // Bounds check: new_len must not exceed cap. Take in a loop or take from
    // a too-small buffer triggers this rather than silently walking past the
    // end. (Cursor form only — positional take takes a raw pointer.)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
    cap_val := fresh_tmp(g)
    emit_typed_load_cap(g, cap_val, cap_gep)
    overflow := fresh_tmp(g)
    emit(g, "  %s = icmp sgt %s %s, %s", overflow, w, new_len, cap_val)
    fail_label := fresh_label(g, "take.fail")
    ok_label := fresh_label(g, "take.ok")
    emit_cond_br(g, overflow, fail_label, ok_label)
    emit_label(g, fail_label)
    loc := format_location(e.span.file, e.span.line, e.span.col)
    msg := fmt.tprintf("%s runtime error: take overflows storage: advance to %%d exceeds cap %%d for '%s'\n",
        loc, name)
    msg_global, msg_byte_len := get_string_literal(g, msg)
    msg_ptr := fresh_tmp(g)
    emit_string_gep(g, msg_ptr, msg_byte_len, msg_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", msg_ptr, w, new_len, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok_label)

    emit_typed_store_len(g, new_len, len_gep)

    // Runtime-counted slice form: write a slice header pointing at typed_ptr
    // with len=cap=count. If the caller supplied `dest_hdr` (because `name`
    // is NRVO-aliased to %sret), write into that slot directly. Otherwise
    // allocate a fresh `take.hdr.N`. The header is the caller-visible value;
    // typed_ptr is the data it views into the caller's storage. gen_take_decl
    // sees Type_Slice and binds a Slice_Var to whichever header we returned.
    if e.count_expr != nil {
        hdr := dest_hdr
        if hdr == "" {
            hdr = fmt.tprintf("%%take.hdr.%d", g.tmp_counter)
            g.tmp_counter += 1
            emit_slice_alloca(g, hdr)
        }
        h_ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, h_ptr_gep, hdr, SLICE.ptr)
        emit_store(g, "ptr", typed_ptr, h_ptr_gep)
        h_len_gep := fresh_tmp(g)
        emit_slice_gep(g, h_len_gep, hdr, SLICE.len)
        emit_typed_store_len(g, count_runtime, h_len_gep)
        h_cap_gep := fresh_tmp(g)
        emit_slice_gep(g, h_cap_gep, hdr, SLICE.cap)
        emit_typed_store_cap(g, count_runtime, h_cap_gep)
        return hdr
    }

    return typed_ptr
}

// Load the total capacity from a slice variable.
// Index into a slice: slice[idx] (value read).
// Bounded by len (valid-data cursor) — you can only read what's been written.
gen_slice_index :: proc(g: ^Codegen, sv: ^Slice_Var, e: ^Expr_Index) -> string {
    // Type checker guarantees e.index is at slice header width — no convert.
    idx := gen_expr(g, e.index, slice_layout.len_ir)

    // Load len from slice for bounds check (natural width)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
    slice_len := fresh_tmp(g)
    emit_typed_load_len(g, slice_len, len_gep)

    // Get variable name for error message
    slice_name := "slice"
    if ident, ok := e.expr.(^Expr_Ident); ok {
        slice_name = ident.name
    }
    emit_bounds_check(g, idx, slice_len, slice_name, e.span)

    // Load data pointer from slice
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
    data_ptr := fresh_tmp(g)
    emit_load_into(g, data_ptr, "ptr", data_gep)

    // GEP to element — idx is at slice header width per the conversion above.
    elem_ptr := fresh_tmp(g)
    emit_elem_gep(g, elem_ptr, sv.elem_type, data_ptr, idx, slice_layout.len_ir)
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
    emit_load_into(g, val, sv.elem_type, elem_ptr)
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
        codegen_fatal(g, e.span, CODE_SLICE_TARGET_VARIABLE)
    }

    // Slice arithmetic runs at slice_layout.len_ir throughout — start /
    // end / (end-start) all live at slice width. Type checker guarantees
    // user low/high are already at slice header width.
    w := slice_layout.len_ir

    // Resolve start index
    start: string
    if e.low != nil {
        start = gen_expr(g, e.low, w)
    } else {
        start = "0"
    }

    switch src in source {
    case Array_Var:
        // Slicing an array
        end: string
        if e.high != nil {
            end = gen_expr(g, e.high, w)
        } else if src.capacity_val != "" {
            // VLA: use runtime capacity
            end = src.capacity_val
        } else {
            end = fmt.tprintf("%d", src.capacity)
        }

        slice_cap := fresh_tmp(g)
        emit(g, "  %s = sub %s %s, %s", slice_cap, w, end, start)

        av := src
        arr_type := array_var_type(&av)
        data_ptr := fresh_tmp(g)
        emit_array_gep_var(g, data_ptr, arr_type, src.alloca, start, w)
        // Sub-slice gives len=cap=(end-start): no preserved growth room beyond the carved range.
        return emit_build_temp_slice(g, data_ptr, slice_cap, slice_cap)

    case Slice_Var:
        // Re-slicing a slice
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, src.alloca, SLICE.ptr)
        orig_data := fresh_tmp(g)
        emit_load_into(g, orig_data, "ptr", data_gep)

        end: string
        if e.high != nil {
            end = gen_expr(g, e.high, w)
        } else {
            // Open-ended `s[a:]` defaults end to the source's LEN — the
            // active-data extent. For partial arrays this is the count
            // tracked by .len (bytes filled by file_read, push, etc.); for
            // pure slices it's the slice's len (usually == cap, which is
            // why this rule used to be cap-based and worked anyway). The
            // raw-memory range is reachable via `data[a:data.cap]` when
            // genuinely needed.
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, src.alloca, SLICE.len)
            end = fresh_tmp(g)
            emit_typed_load_len(g, end, len_gep)
        }

        new_cap := fresh_tmp(g)
        emit(g, "  %s = sub %s %s, %s", new_cap, w, end, start)

        new_data := fresh_tmp(g)
        emit_elem_gep(g, new_data, src.elem_type, orig_data, start, w)
        // Sub-slice gives len=cap=(end-start).
        return emit_build_temp_slice(g, new_data, new_cap, new_cap)
    }

    codegen_fatal(g, e.span, CODE_SLICE_TARGET_ARRAY_SLICE)
}

// Runtime-cap variant of the sized-slice declaration path. Mirrors the
// comptime-cap path in gen_stmt — alloca backing storage + slice header,
// init to (ptr, len=0, cap=N) — but the cap evaluates at runtime via
// gen_expr, and the backing storage uses LLVM's runtime-sized alloca
// (`alloca T, i32 %count`) instead of `alloca [N x T]`. Pool allocation
// and string-literal init aren't supported here; both assume a comptime
// known size.
gen_slice_decl_runtime_cap :: proc(g: ^Codegen, s: ^Stmt_Assign, sl: ^Type_Slice,
                                    elem_t: string, sl_utf8, sl_sentinel: bool, sl_sentinel_val: int) {
    w := slice_layout.len_ir
    // Evaluate the user-visible count at runtime. cap_user = N (no sentinel
    // adjustment) — what `.cap()` returns and what we store in the header
    // for non-sentinel slices.
    cap_user := gen_expr(g, s.slice_cap_expr, w)
    // Physical allocation count adds one slot for the sentinel terminator.
    alloc_cap := cap_user
    if sl_sentinel {
        bumped := fresh_tmp(g)
        emit(g, "  %s = add %s %s, 1", bumped, w, cap_user)
        alloc_cap = bumped
    }
    // Backing storage alloca with runtime count. `alloca T, <w> %count`
    // allocates `count * sizeof(T)` bytes. For utf8/byte/i8 element types
    // we over-align to 16 to match the comptime path's `take(T, ...)`-
    // friendly alignment policy. Goes through emit_alloca_runtime so the
    // alloca stays at the point of use — the count SSA isn't visible from
    // the entry block where static allocas live.
    data_name := fmt.tprintf("%%%s.data", s.name)
    if elem_t == "i8" {
        emit_alloca_runtime(g, data_name, "i8", w, alloc_cap, 16)
    } else {
        emit_alloca_runtime(g, data_name, elem_t, w, alloc_cap, 0)
    }
    // Sentinel slices need the trailing slot to start at zero so C-style
    // consumers that walk-until-null see a defined boundary on day zero.
    // Zeroing the full region matches the comptime path.
    if sl_sentinel {
        elem_bytes := elem_byte_size(elem_t, g.checked)
        size_ssa := fresh_tmp(g)
        emit(g, "  %s = mul %s %s, %d", size_ssa, w, alloc_cap, elem_bytes)
        // memset uses i64 size — extend if header width is narrower.
        size64 := size_ssa
        if w != "i64" {
            zext := fresh_tmp(g)
            emit(g, "  %s = zext %s %s to i64", zext, w, size_ssa)
            size64 = zext
        }
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %s, i1 false)",
            data_name, size64)
    }
    // Build the slice header. Stores cap_user (not alloc_cap) so callers
    // see N usable elements regardless of the hidden sentinel slot.
    alloca_name := fmt.tprintf("%%%s", s.name)
    emit_slice_alloca(g, alloca_name)
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
    emit_store(g, "ptr", data_name, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
    emit_typed_store_cap(g, cap_user, cap_gep)
    g.all_vars[s.name] = Slice_Var{
        alloca       = alloca_name,
        elem_type    = elem_t,
        is_utf8      = sl_utf8,
        has_sentinel = sl_sentinel,
        sentinel     = sl_sentinel_val,
    }
}

// Assign a slice expression to an inferred-type variable: x := arr[1:3]
gen_slice_assign_inferred :: proc(g: ^Codegen, name: string, value: Expr) {
    // Pre-bound slice with no body initializer (e.g. `name: String` as a struct
    // field where prebind_field_var already wired the header) — there's
    // nothing to do here. Falling through would `gen_expr(nil) = "0"` and
    // memcpy from `ptr 0`, which clang rejects as an integer constant in a
    // pointer slot.
    if value == nil { return }
    // Explicit `#skip_constructor`: opt out of construction. The pre-bound
    // header (ptr → inline elements, cap = N) is already valid; overwriting
    // from gen_expr's "zeroinitializer" placeholder would clobber it with
    // garbage. The opt-out covers per-element construction only; structural
    // setup stays.
    if _, is_skip := value.(^Expr_Skip_Constructor); is_skip { return }
    // `{all <expr>}` broadcast literal: the type checker expanded into
    // array_values (one per element). The pre-bound partial-array header is
    // already valid; emit element-by-element stores into the inline storage.
    if lit, lit_ok := value.(^Expr_Struct_Literal); lit_ok && lit.is_broadcast && len(lit.array_values) > 0 {
        if pa, pa_ok := distinct_base(lit.type_).(^Type_Partial_Array); pa_ok {
            sv, sv_ok := get_slice(g, name)
            if !sv_ok { return }
            elem_t := llvm_type_from_checker(pa.elem)
            alloc_cap := pa.size
            if pa.has_sentinel { alloc_cap += 1 }
            ir_type := partial_array_ir_type(elem_t, alloc_cap)
            for elem_expr, i in lit.array_values {
                if elem_expr == nil { continue }
                slot := fresh_tmp(g)
                emit(g, "  %s = getelementptr inbounds %s, ptr %s, i32 0, i32 %d, i32 %d",
                    slot, ir_type, sv.alloca, PARTIAL_ELEMENTS_FIELD, i)
                if sd := as_struct_body(pa.elem); sd != nil {
                    // Struct/class element — write through the unified store.
                    gen_store_struct_into(g, slot, sd, elem_expr)
                } else {
                    val := gen_expr(g, elem_expr, elem_t)
                    emit_store(g, elem_t, val, slot)
                }
            }
            // Update the slice's len to match the broadcast count (the user
            // initialized all N elements, so len = N).
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
            emit_typed_store_len(g, fmt.tprintf("%d", pa.size), len_gep)
            return
        }
    }
    // NRVO: if value is a slice-returning Mara call, route its sret
    // straight to our dest's alloca. Same trick as gen_slice_from_expr.
    if call, call_ok := value.(^Expr_Call); call_ok {
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok && info.ret_slice_elem != "" {
            if _, slice_exists := get_slice(g, name); !slice_exists {
                alloca_name := fmt.tprintf("%%%s.slice", name)
                emit_slice_alloca(g, alloca_name)
                g.all_vars[name] = Slice_Var{
                    alloca    = alloca_name,
                    elem_type = info.ret_slice_elem,
                }
            }
            sv, _ := get_slice(g, name)
            gen_call_into_struct(g, call, sv.alloca, &info)
            return
        }
    }

    // Determine elem type from the source expression
    elem_t := "i64"
    utf8 := false
    sentinel := false
    sentinel_val := 0
    if sl, ok := value.(^Expr_Slice); ok {
        if ident, id_ok := sl.expr.(^Expr_Ident); id_ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                elem_t = av.elem_type
                utf8 = av.is_utf8
                sentinel = av.has_sentinel
                sentinel_val = av.sentinel
            } else if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                elem_t = sv.elem_type
                utf8 = sv.is_utf8
                sentinel = sv.has_sentinel
                sentinel_val = sv.sentinel
            }
        } else if sl.expr != nil {
            // Field access or other expr — check type annotation
            sl_type := expr_type(sl.expr)
            if slice_t, st_ok := sl_type.(^Type_Slice); st_ok {
                elem_t = llvm_type_from_checker(slice_t.elem)
                _, utf8 = slice_t.elem.(Type_Utf8)
                sentinel = slice_t.has_sentinel
                sentinel_val = slice_t.sentinel
            } else if fa_t, fa_ok := sl_type.(^Type_Fixed_Array); fa_ok {
                elem_t = llvm_type_from_checker(fa_t.elem)
                _, utf8 = fa_t.elem.(Type_Utf8)
                sentinel = fa_t.has_sentinel
                sentinel_val = fa_t.sentinel
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
            sentinel     = sentinel_val,
        }
    }

    sv, _ := get_slice(g, name)

    // Copy whole slice header { len, cap, ptr } from source into destination.
    emit_memcpy(g, sv.alloca, src, slice_header_bytes)
}

// Single point of truth for "store a slice value into a destination pointer".
// Mirrors gen_store_struct_into / gen_store_array_into for slice IR
// ({ len, cap, ptr }, slice_header_bytes total). gen_expr on any slice-valued
// expression returns a pointer to a slice descriptor, so almost every case is
// a slice-header-sized memcpy.
gen_store_slice_into :: proc(g: ^Codegen, dst_ptr: string, value: Expr) {
    if value == nil {
        ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, ptr_gep, dst_ptr, SLICE.ptr)
        emit_store(g, "ptr", "null", ptr_gep)
        len_gep := fresh_tmp(g)
        emit_slice_gep(g, len_gep, dst_ptr, SLICE.len)
        emit_typed_store_len(g, "0", len_gep)
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, dst_ptr, SLICE.cap)
        emit_typed_store_cap(g, "0", cap_gep)
        return
    }
    // 1-arg `slice(source)` — the parser produces an Expr_Take with no
    // type_expr and no count_expr. The slice's element type / cap come from
    // the LHS (already in dst_ptr's slot, set by a prior assignment to
    // `.cap` and `.len`). We just rewrite `.ptr` to aim at the new source;
    // len/cap stay as the user already set them.
    if take, take_ok := value.(^Expr_Take); take_ok &&
       take.keyword == "slice" && take.type_expr == nil && take.count_expr == nil {
        elem_ptr := gen_slice_one_arg_source_ptr(g, take.storage, take.span)
        ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, ptr_gep, dst_ptr, SLICE.ptr)
        emit_store(g, "ptr", elem_ptr, ptr_gep)
        return
    }
    src := gen_expr(g, value)
    emit_memcpy(g, dst_ptr, src, slice_header_bytes)
}

// Resolve the source pointer for a 1-arg `slice(source)`. Currently accepts
// `&bytes[offset]` (typed pointer at a byte-buffer offset) — the same shape
// the 2-arg form already takes for its byte-buffer source. Other shapes
// (cursor form / arbitrary ^byte) are deferred; the byte-buffer case covers
// the binary-parsing pattern this feature was introduced for.
gen_slice_one_arg_source_ptr :: proc(g: ^Codegen, storage: Expr, span: Span) -> string {
    if un, un_ok := storage.(^Expr_Unary); un_ok && un.op == .Ampersand {
        if idx, idx_ok := un.operand.(^Expr_Index); idx_ok {
            // The byte span is unknown to slice() here — we deferred bounds
            // checking against the LHS cap. Use a 1-byte minimum so the
            // existing emit_byte_offset_ptr machinery still validates the
            // starting offset is in range.
            ptr, ok := emit_byte_offset_ptr(g, idx.expr, idx.index, 1, "slice", idx.span)
            if !ok {
                codegen_fatal(g, span, CODE_POSITIONAL_TAKE_REQUIRES_BUF_SOURCE)
            }
            return ptr
        }
    }
    codegen_fatal(g, span, CODE_POSITIONAL_TAKE_REQUIRES_BUF_SOURCE)
}

// Assign a slice-typed expression (e.g. alloc()) to a named variable.
// The expression must return a { len, cap, ptr } alloca.
gen_slice_from_expr :: proc(g: ^Codegen, name: string, value: Expr, elem_type: string, is_utf8: bool = false, has_sentinel: bool = false, sentinel: int = 0) {
    // NRVO: if value is a slice-returning Mara call, route its sret
    // straight to our dest's alloca. When `name` is the function's NRVO
    // candidate, its alloca is %sret — so the inner call writes directly
    // into the outer caller's slot. Saves one alloca + one 16-byte memcpy
    // per assignment, and propagates through chains where each level
    // modifies the result before returning.
    if call, call_ok := value.(^Expr_Call); call_ok {
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok && info.ret_slice_elem != "" {
            if _, slice_exists := get_slice(g, name); !slice_exists {
                alloca_name := fmt.tprintf("%%%s.slice", name)
                emit_slice_alloca(g, alloca_name)
                g.all_vars[name] = Slice_Var{
                    alloca       = alloca_name,
                    elem_type    = elem_type,
                    is_utf8      = is_utf8,
                    has_sentinel = has_sentinel,
                    sentinel     = sentinel,
                }
            }
            sv, _ := get_slice(g, name)
            gen_call_into_struct(g, call, sv.alloca, &info)
            return
        }
    }

    // Slice-coercible source (string literal, fixed array, existing slice
    // var, etc.) — route through gen_slice_value_ptr which knows how to
    // synthesize a real slice header. Without this, a bare string literal
    // would memcpy 24 bytes of string data through emit_memcpy and leave the
    // slice header pointing at garbage.
    src := gen_slice_value_ptr(g, value)

    if _, slice_exists := get_slice(g, name); !slice_exists {
        alloca_name := fmt.tprintf("%%%s.slice", name)
        emit_slice_alloca(g, alloca_name)
        g.all_vars[name] = Slice_Var{
            alloca       = alloca_name,
            elem_type    = elem_type,
            is_utf8      = is_utf8,
            has_sentinel = has_sentinel,
            sentinel     = sentinel,
        }
    }

    sv, _ := get_slice(g, name)

    // Copy whole slice header { len, cap, ptr } from source into destination.
    emit_memcpy(g, sv.alloca, src, slice_header_bytes)
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
    // Source must be a true byte buffer at the Mara type level. Both `[..N]byte`
    // and `[..N]utf8` lower to IR `i8`, so checking the LLVM elem_type would
    // misclassify utf8 containers — fall back to the type-level check.
    src_type := expr_type(expr)
    if src_type != nil {
        if is_byte_slice(src_type) || is_byte_fixed_array(src_type) || is_byte_partial_array(src_type) {
            return true
        }
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
        emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
        data_ptr := fresh_tmp(g)
        emit_load_into(g, data_ptr, "ptr", data_gep)
        // Byte-view / let-binding addresses raw storage — bound by cap, not len.
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
        cap_val := fresh_tmp(g)
        emit_typed_load_cap(g, cap_val, cap_gep)
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
//
// offset is normalised to slice_layout.len_ir so the bounds check and the
// GEP both operate at the same width as cap_val (loaded at slice header
// width post-migration). Conversion is explicit at the indexing primitive,
// not a hidden widen elsewhere.
emit_byte_offset_ptr :: proc(g: ^Codegen, buf_expr: Expr, offset_expr: Expr, size: int, label: string, span: Span) -> (elem_ptr: string, ok: bool) {
    data_ptr, cap_val, resolved := resolve_byte_target(g, buf_expr, span)
    if !resolved { return "", false }

    offset := "0"
    if offset_expr != nil {
        offset = gen_expr(g, offset_expr, slice_layout.len_ir)
    }
    emit_byte_size_bounds_check(g, cap_val, offset, size, label)

    elem_ptr = fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", elem_ptr, data_ptr, slice_layout.len_ir, offset)
    return elem_ptr, true
}

// Runtime-sized variant of emit_byte_offset_ptr. Used by `slice([:n]T, &buf[off])`
// where the carved region's size is `n * sizeof(elem)` — a runtime SSA value,
// not a compile-time constant.
emit_byte_offset_ptr_runtime :: proc(g: ^Codegen, buf_expr: Expr, offset_expr: Expr, byte_count_ssa: string, label: string, span: Span) -> (elem_ptr: string, ok: bool) {
    data_ptr, cap_val, resolved := resolve_byte_target(g, buf_expr, span)
    if !resolved { return "", false }

    w := slice_layout.len_ir
    offset := "0"
    if offset_expr != nil {
        offset = gen_expr(g, offset_expr, w)
    }
    end_offset := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", end_offset, w, offset, byte_count_ssa)
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", cmp, w, end_offset, cap_val)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    err_msg := fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%d + %%d > capacity %%d\n", label)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s, %s %s)", err_ptr, w, offset, w, byte_count_ssa, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok_lbl)

    elem_ptr = fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", elem_ptr, data_ptr, w, offset)
    return elem_ptr, true
}

// Address of a byte-buffer element, widened to a typed-pointer view of
// `target_size` bytes. Used for `^T = &buf[i]` where buf is a byte slice
// or [N]byte.
gen_byte_view_address :: proc(g: ^Codegen, idx: ^Expr_Index, target_size: int) -> string {
    elem_ptr, ok := emit_byte_offset_ptr(g, idx.expr, idx.index, target_size, "view", idx.span)
    if !ok {
        codegen_fatal(g, idx.span, CODE_BYTE_VIEW_SOURCE_BYTE_SLICE)
    }
    return elem_ptr
}

// Bounds check for byte-buffer access at offset [low, low+size). Operates
// at slice_layout.len_ir — caller has already normalised low and cap_val
// to that width via emit_byte_offset_ptr / resolve_byte_target.
emit_byte_size_bounds_check :: proc(g: ^Codegen, cap_val: string, low: string, size: int, label: string) {
    w := slice_layout.len_ir
    end_offset := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %d", end_offset, w, low, size)
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", cmp, w, end_offset, cap_val)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    err_msg := fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%d + %d > capacity %%d\n", label, size)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", err_ptr, w, low, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok_lbl)
}

// Get the data pointer from a Slice_Var. Used by non-byte-buffer code
// paths that deal with generic slices.
slice_var_data_ptr :: proc(g: ^Codegen, sv: ^Slice_Var) -> string {
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, sv.alloca, SLICE.ptr)
    data_ptr := fresh_tmp(g)
    emit_load_into(g, data_ptr, "ptr", data_gep)
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
        codegen_fatal(g, s.span, CODE_BYTE_BUFFER_WRITE_TARGET_BYTE)
    }

    if sd := as_struct_body(val_type); sd != nil {
        val := gen_expr(g, s.value)
        emit_memcpy(g, elem_ptr, val, val_size)
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
// `is_big_endian` (from a `#big_endian` decorator) byte-swaps every multi-byte
// integer leaf in the destination after the load/memcpy.
gen_byte_target_read :: proc(g: ^Codegen, name: string, buf_expr: Expr, offset_expr: Expr, span: Span, target_type: Type, is_big_endian: bool) {
    target_ir_type := llvm_type_from_checker(target_type)
    target_size := checker_type_byte_size(target_type)

    elem_ptr, ok := emit_byte_offset_ptr(g, buf_expr, offset_expr, target_size, "read", span)
    if !ok {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }

    alloca_name := fmt.tprintf("%%%s", name)
    if sd := as_struct_body(target_type); sd != nil {
        emit_alloca(g, alloca_name, target_ir_type)
        emit_memcpy(g, alloca_name, elem_ptr, target_size)
        if is_big_endian {
            emit_bswap_in_place(g, alloca_name, target_ir_type, target_type)
        }
        g.all_vars[name] = Struct_Var{alloca = alloca_name, struct_name = struct_key(sd)}
    } else if fa, fa_ok := target_type.(^Type_Fixed_Array); fa_ok {
        // Fixed-array reinterpret target: allocate the destination using the
        // `<name>.data` naming convention used elsewhere for array storage,
        // memcpy the source bytes in, register the local as an Array_Var so
        // subsequent indexing / further reinterpret-reads find it.
        data_name := fmt.tprintf("%%%s.data", name)
        emit_alloca(g, data_name, target_ir_type)
        emit_memcpy(g, data_name, elem_ptr, target_size)
        if is_big_endian {
            emit_bswap_in_place(g, data_name, target_ir_type, target_type)
        }
        elem_t := llvm_type_from_checker(fa.elem)
        utf8 := false
        if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Array_Var{
            alloca       = data_name,
            capacity     = fa.size,
            elem_type    = elem_t,
            is_utf8      = utf8,
            has_sentinel = fa.has_sentinel,
            sentinel     = fa.sentinel,
        }
    } else {
        val := fresh_tmp(g)
        // `align 1` on the byte-buffer load (offset user-chosen); the store
        // into the local alloca stays natural since the alloca is aligned.
        emit(g, "  %s = load %s, ptr %s, align 1", val, target_ir_type, elem_ptr)
        if is_big_endian && is_swappable_integer(target_type) {
            bits := checker_type_byte_size(target_type) * 8
            if bits >= 16 {
                intrinsic := fmt.tprintf("llvm.bswap.i%d", bits)
                g.bswap_intrinsics[bits] = true
                swapped := fresh_tmp(g)
                emit(g, "  %s = call i%d @%s(i%d %s)", swapped, bits, intrinsic, bits, val)
                val = swapped
            }
        }
        emit_alloca(g, alloca_name, target_ir_type)
        emit_store(g, target_ir_type, val, alloca_name)
        g.all_vars[name] = Scalar_Var{alloca_name}
    }
}

// Big-endian byte-swap in place: walks `ty` rooted at `base_ptr` and emits
// llvm.bswap on every multi-byte integer leaf. Used by `#big_endian` byte-
// buffer reads after the load/memcpy.
//
// `base_ir_type` is the LLVM aggregate type at `base_ptr` (used for struct/
// array GEPs). For scalar leaves it's unused — the bit width comes from
// checker_type_byte_size.
//
// Skipped leaves: 1-byte primitives (byte/utf8/c8/u8/i8/bool — already in
// order); floats, pointers, slices, partial arrays (bswap is meaningless).
emit_bswap_in_place :: proc(g: ^Codegen, base_ptr: string, base_ir_type: string, ty: Type) {
    base := distinct_base(ty)

    if sd := as_struct_body(base); sd != nil {
        st_llvm := struct_llvm_name(struct_key(sd))
        for &f, idx in sd.fields {
            field_ir := field_ir_type(&f)
            field_gep := fresh_tmp(g)
            emit_field_gep_into(g, field_gep, st_llvm, base_ptr, idx)
            emit_bswap_in_place(g, field_gep, field_ir, f.type_)
        }
        return
    }

    if fa, ok := base.(^Type_Fixed_Array); ok {
        elem_bytes := checker_type_byte_size(fa.elem)
        if elem_bytes <= 1 { return }
        elem_ir := llvm_type_from_checker(fa.elem)
        for i in 0..<fa.size {
            elem_gep := fresh_tmp(g)
            emit_array_gep_const(g, elem_gep, base_ir_type, base_ptr, i)
            emit_bswap_in_place(g, elem_gep, elem_ir, fa.elem)
        }
        return
    }

    if !is_swappable_integer(base) { return }
    bits := checker_type_byte_size(base) * 8
    if bits < 16 { return }
    intrinsic := fmt.tprintf("llvm.bswap.i%d", bits)
    g.bswap_intrinsics[bits] = true
    loaded := fresh_tmp(g)
    emit(g, "  %s = load i%d, ptr %s, align 1", loaded, bits, base_ptr)
    swapped := fresh_tmp(g)
    emit(g, "  %s = call i%d @%s(i%d %s)", swapped, bits, intrinsic, bits, loaded)
    emit(g, "  store i%d %s, ptr %s, align 1", bits, swapped, base_ptr)
}

// True when `t` is a multi-byte integer type — the kind bswap is meaningful for.
// Returns true for Type_Int (i64), signed/unsigned Type_Numeric, Type_Enum
// (integer tag). Returns false for byte/utf8/c8/bool (1 byte), floats, pointers,
// slices, etc. Caller filters out widths < 16 bits.
is_swappable_integer :: proc(t: Type) -> bool {
    bt := distinct_base(t)
    #partial switch v in bt {
    case Type_Int:
        return true
    case Type_Numeric:
        return v.kind == .Signed || v.kind == .Unsigned
    case ^Type_Enum:
        return true
    }
    return false
}

// Reinterpret-read a byte-buffer source into a fresh [N x T] SSA value at a
// call site: `f(buf[off])` or `f(buf[lo:hi])` where the param expects a fixed
// array. Allocates a temporary, memcpys the bytes in, loads as [N x T], and
// returns the loaded SSA name. Bounds-checked via emit_byte_offset_ptr.
// `arr_ty` is the Mara fixed-array type; consulted when `is_big_endian` is
// set so we can byte-swap each element after the memcpy.
emit_array_from_byte_buffer :: proc(g: ^Codegen, buf_expr: Expr, offset_expr: Expr, pt: string, span: Span, arr_ty: Type, is_big_endian: bool) -> string {
    arr_cap, arr_elem, _ := parse_array_ir_type(pt)
    size_bytes := arr_cap * elem_byte_size(arr_elem, g.checked)
    elem_ptr, ok := emit_byte_offset_ptr(g, buf_expr, offset_expr, size_bytes, "read", span)
    if !ok {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }
    arr_alloca := fresh_tmp(g)
    emit_alloca(g, arr_alloca, pt)
    emit_memcpy(g, arr_alloca, elem_ptr, size_bytes)
    if is_big_endian && arr_ty != nil {
        emit_bswap_in_place(g, arr_alloca, pt, arr_ty)
    }
    loaded := fresh_tmp(g)
    emit_load_into(g, loaded, pt, arr_alloca)
    return loaded
}

// Byte-buffer reinterpret read into a struct field: obj.field = buf[lo:hi] or obj.field = buf[off].
// Memcpys `size_of(field)` bytes from the byte-buffer source into the field GEP.
// Scalar fields use load+store (align 1 on the load; natural alignment at the GEP).
// `is_big_endian` byte-swaps every multi-byte integer leaf written into the
// field after the load/memcpy.
gen_byte_target_field_read :: proc(g: ^Codegen, st_llvm: string, base_ptr: string, idx: int, f: ^Struct_Type_Field, buf_expr: Expr, offset_expr: Expr, span: Span, is_big_endian: bool) {
    ft := field_ir_type(f)
    field_size := checker_type_byte_size(f.type_)
    elem_ptr, ok := emit_byte_offset_ptr(g, buf_expr, offset_expr, field_size, "read", span)
    if !ok {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }
    gep := fresh_tmp(g)
    emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
    if as_struct_body(f.type_) != nil {
        emit_memcpy(g, gep, elem_ptr, field_size)
        if is_big_endian {
            emit_bswap_in_place(g, gep, ft, f.type_)
        }
    } else {
        val := fresh_tmp(g)
        emit(g, "  %s = load %s, ptr %s, align 1", val, ft, elem_ptr)
        if is_big_endian && is_swappable_integer(f.type_) {
            bits := checker_type_byte_size(f.type_) * 8
            if bits >= 16 {
                intrinsic := fmt.tprintf("llvm.bswap.i%d", bits)
                g.bswap_intrinsics[bits] = true
                swapped := fresh_tmp(g)
                emit(g, "  %s = call i%d @%s(i%d %s)", swapped, bits, intrinsic, bits, val)
                val = swapped
            }
        }
        emit_store(g, ft, val, gep)
    }
}

// Partial-array byte-buffer reinterpret read:
//   arr : [..N]T = bytes[lo:hi]
// Allocates the partial array's inline backing (struct of ptr/len/cap +
// [N x T] elements), initialises the header (ptr → elements, len → 0,
// cap → N), then memcpys the source byte slice into the elements area
// and adds `source.len / sizeof(T)` to `len`. Runtime checks:
//   1. source.len is a multiple of sizeof(T) — partial reads of a typed
//      element are loud failures, not silent truncation.
//   2. resulting count fits in cap — caller declared N as the static
//      upper bound; a longer source is malformed input or a wrong type.
gen_partial_array_byte_read :: proc(g: ^Codegen, name: string, pa: ^Type_Partial_Array, sl_expr: ^Expr_Slice, span: Span) {
    elem_t := llvm_type_from_checker(pa.elem)
    _, pa_utf8 := pa.elem.(Type_Utf8)
    cap_n := pa.size
    alloc_cap := cap_n
    if pa.has_sentinel { alloc_cap += 1 }
    ir_type := partial_array_ir_type(elem_t, alloc_cap)
    alloca_name := fmt.tprintf("%%%s", name)
    elem_bytes := elem_byte_size(elem_t, g.checked)

    if elem_t == "i8" {
        emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type, ", align 16"}))
    } else {
        emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type}))
    }

    // Initialise header: ptr → elements, len → 0, cap → N.
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", alloca_name, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)

    // Resolve the source byte slice: produce a data ptr at sl_expr.low and a
    // byte count = sl_expr.high - sl_expr.low. Routes through the same
    // byte-buffer machinery that take/let/slice use.
    src_data_ptr, src_cap, resolved := resolve_byte_target(g, sl_expr.expr, span)
    if !resolved {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }

    w := slice_layout.len_ir
    src_low := "0"
    if sl_expr.low != nil { src_low = gen_expr(g, sl_expr.low, w) }
    src_high := src_cap
    if sl_expr.high != nil { src_high = gen_expr(g, sl_expr.high, w) }

    // Runtime check 0: high >= low. Fires before the divisibility check below
    // so an inverted slice (e.g. `bytes[12 : table_section]` when table_section
    // happens to be < 12) reports the actual problem instead of producing a
    // negative span that confuses the modulo check downstream.
    inv_ok := fresh_label(g, "pa.inv.ok")
    inv_err := fresh_label(g, "pa.inv.err")
    inv_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", inv_cmp, w, src_high, src_low)
    emit_cond_br(g, inv_cmp, inv_err, inv_ok)
    emit_label(g, inv_err)
    inv_msg := fmt.tprintf("runtime error: partial-array byte read slice bounds inverted (low=%%d, high=%%d) for '%s'\n", name)
    inv_global, inv_byte_len := get_string_literal(g, inv_msg)
    inv_ptr := fresh_tmp(g)
    emit_string_gep(g, inv_ptr, inv_byte_len, inv_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", inv_ptr, w, src_low, w, src_high)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, inv_ok)

    src_bytes := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", src_bytes, w, src_high, src_low)

    // Runtime check 1: src_bytes % elem_bytes == 0.
    rem := fresh_tmp(g)
    emit(g, "  %s = urem %s %s, %d", rem, w, src_bytes, elem_bytes)
    rem_ok := fresh_label(g, "pa.div.ok")
    rem_err := fresh_label(g, "pa.div.err")
    rem_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ne %s %s, 0", rem_cmp, w, rem)
    emit_cond_br(g, rem_cmp, rem_err, rem_ok)
    emit_label(g, rem_err)
    rem_msg := fmt.tprintf("runtime error: partial-array byte read slice bounds [%%d : %%d] = %%d bytes, not divisible by elem size %d for '%s'\n", elem_bytes, name)
    rem_global, rem_byte_len := get_string_literal(g, rem_msg)
    rem_ptr := fresh_tmp(g)
    emit_string_gep(g, rem_ptr, rem_byte_len, rem_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s, %s %s)", rem_ptr, w, src_low, w, src_high, w, src_bytes)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, rem_ok)

    // count = src_bytes / elem_bytes.
    count := fresh_tmp(g)
    emit(g, "  %s = udiv %s %s, %d", count, w, src_bytes, elem_bytes)

    // Runtime check 2: count <= cap.
    cap_str := fmt.tprintf("%d", cap_n)
    cap_ok := fresh_label(g, "pa.cap.ok")
    cap_err := fresh_label(g, "pa.cap.err")
    cap_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", cap_cmp, w, count, cap_str)
    emit_cond_br(g, cap_cmp, cap_err, cap_ok)
    emit_label(g, cap_err)
    cap_msg := fmt.tprintf("runtime error: partial-array byte read slice bounds [%%d : %%d] produced %%d elements, exceeds cap %d for '%s'\n", cap_n, name)
    cap_global, cap_byte_len := get_string_literal(g, cap_msg)
    cap_msg_ptr := fresh_tmp(g)
    emit_string_gep(g, cap_msg_ptr, cap_byte_len, cap_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s, %s %s)", cap_msg_ptr, w, src_low, w, src_high, w, count)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, cap_ok)

    // memcpy(elements_ptr, src_data_ptr + src_low, src_bytes).
    src_offset_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", src_offset_ptr, src_data_ptr, w, src_low)
    emit_memcpy_runtime(g, elements_ptr, src_offset_ptr, src_bytes)

    // `#big_endian` decorator on the source slice: byte-swap each element in
    // place. Count is runtime, so we emit a counter-driven loop wrapping the
    // per-element bswap.
    if sl_expr.is_big_endian {
        emit_partial_bswap_loop(g, elements_ptr, count, pa.elem)
    }

    // Auto-add to len. For a fresh decl this is + 0, so the final len = count.
    cur_len := fresh_tmp(g)
    emit_typed_load_len(g, cur_len, len_gep)
    new_len := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", new_len, w, cur_len, count)
    emit_typed_store_len(g, new_len, len_gep)

    g.all_vars[name] = Slice_Var{
        alloca       = alloca_name,
        elem_type    = elem_t,
        is_utf8      = pa_utf8,
        has_sentinel = pa.has_sentinel,
        sentinel     = pa.sentinel,
    }
}

// Counter-driven loop that calls emit_bswap_in_place on each of `count`
// elements rooted at `elements_ptr`. Count is an SSA value at slice-header
// width. Used by `#big_endian` on partial-array reads — the count is only
// known at runtime, so the per-element swap can't be unrolled.
//
// If `elem_ty` contains no multi-byte integer leaves (e.g. `[..N]byte`), the
// inner body is a no-op and an optimizer will see through it — but skip the
// loop entirely as a cheap source-level guard.
emit_partial_bswap_loop :: proc(g: ^Codegen, elements_ptr: string, count: string, elem_ty: Type) {
    if !type_has_swappable_leaf(elem_ty) { return }

    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(elem_ty)
    idx_slot := fresh_tmp(g)
    emit(g, "  %s = alloca %s", idx_slot, w)
    emit_typed_store_len(g, "0", idx_slot)
    loop_lbl := fresh_label(g, "bswap.loop")
    body_lbl := fresh_label(g, "bswap.body")
    end_lbl  := fresh_label(g, "bswap.end")
    emit(g, "  br label %%%s", loop_lbl)
    emit_label(g, loop_lbl)
    cur := fresh_tmp(g)
    emit_typed_load_len(g, cur, idx_slot)
    done := fresh_tmp(g)
    emit(g, "  %s = icmp uge %s %s, %s", done, w, cur, count)
    emit_cond_br(g, done, end_lbl, body_lbl)
    emit_label(g, body_lbl)
    elem_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, %s %s", elem_gep, elem_ir, elements_ptr, w, cur)
    emit_bswap_in_place(g, elem_gep, elem_ir, elem_ty)
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, cur)
    emit_typed_store_len(g, next, idx_slot)
    emit(g, "  br label %%%s", loop_lbl)
    emit_label(g, end_lbl)
}

// True if `ty` contains any multi-byte integer leaf — i.e. emit_bswap_in_place
// would emit at least one bswap. Lets callers skip the wrapping loop entirely
// when the element layout has nothing to swap.
type_has_swappable_leaf :: proc(ty: Type) -> bool {
    base := distinct_base(ty)
    if sd := as_struct_body(base); sd != nil {
        for &f in sd.fields {
            if type_has_swappable_leaf(f.type_) { return true }
        }
        return false
    }
    if fa, ok := base.(^Type_Fixed_Array); ok {
        return type_has_swappable_leaf(fa.elem)
    }
    if !is_swappable_integer(base) { return false }
    return checker_type_byte_size(base) >= 2
}

// Runtime-sized memcpy. Used when the byte count is an SSA value, not a
// compile-time literal — e.g. partial-array byte-buffer reads where the
// source span size is computed from runtime slice bounds. `bytes` is at
// slice header width (i32); the memcpy intrinsic takes i64, so we zext.
emit_memcpy_runtime :: proc(g: ^Codegen, dst, src, bytes: string) {
    w := slice_layout.len_ir
    n64 := bytes
    if w != "i64" {
        n64 = fresh_tmp(g)
        emit(g, "  %s = zext %s %s to i64", n64, w, bytes)
    }
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %s, i1 false)", dst, src, n64)
}
