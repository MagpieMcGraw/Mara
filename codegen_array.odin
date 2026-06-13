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

// Write an initial value into an already-allocated, header-stamped partial
// array at `pa_ptr` (pointer to a `{len, cap, ptr, [N x T]}` structure):
//   - string literal into a byte/utf8 array: memcpy the bytes and set len.
//   - another partial array of the same shape: deep copy via partial_array_copy.
//   - anything else: a located codegen error.
// Shared by the local partial-array decl path and the struct-field-default path
// (constructor body) so both initialise len/elements identically — a field
// default used to skip this entirely and leave the field's len uninitialised.
gen_partial_array_init_value :: proc(g: ^Codegen, pa_ptr: string, value: Expr, elem_t: string, elem_bytes, alloc_cap: int, pa: ^Type_Partial_Array, span: Span, name: string) {
    // `= void` (skip marker): the header is already stamped by the decl
    // path — leaving the elements untouched is exactly the request.
    if _, is_skip := value.(^Expr_Skip_Constructor); is_skip { return }
    if str_lit, str_ok := value.(^Expr_String); str_ok && elem_bytes == 1 {
        ir_type := partial_array_ir_type(elem_t, alloc_cap)
        elements_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", pa_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
        str_bytes := str_lit.value
        if len(str_bytes) > 0 {
            global, _ := get_string_literal(g, str_bytes)
            src_ptr := fresh_tmp(g)
            emit_string_gep(g, src_ptr, len(str_bytes)+1, global)
            // Copy the rodata global's trailing \0 along with the content
            // when there's headroom — the copy is then born terminated and
            // passes cstring()'s [len] check. Exact-fit caps copy content
            // only (the [cap-1] rule covers them if the last byte is 0).
            copy_n := len(str_bytes)
            if alloc_cap > copy_n { copy_n += 1 }
            emit_memcpy(g, elements_ptr, src_ptr, copy_n)
        }
        len_gep := fresh_tmp(g)
        emit_slice_gep(g, len_gep, pa_ptr, SLICE.len)
        emit_typed_store_len(g, fmt.tprintf("%d", len(str_bytes)), len_gep)
    } else if _, src_pa_ok := distinct_base(expr_type(value)).(^Type_Partial_Array); src_pa_ok {
        // ident / field access: a pointer to the source PA. A PA-returning call
        // (sret ABI) also yields a pointer — to the temp the callee built into.
        src_ptr := gen_expr(g, value)
        partial_array_copy(g, pa_ptr, src_ptr, elem_t, alloc_cap)
    } else {
        codegen_fatal(g, span,
            CODE_PARTIAL_ARRAY_INITIALIZER_STRING_LITERAL,
            name, type_name(expr_type(value)))
    }
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

gen_array_assign :: proc(g: ^Codegen, name: string, capacity: int, elem_type: string, value: Expr, is_utf8: bool = false, loc: string = "<unknown>") {
    // `= void` (skip marker) on a fixed array — same as no initializer:
    // allocate, register, and stop — under the zero-init policy, `= void`
    // is the opt-out, so the skip marker leaves the bytes untouched.
    value := value
    skip_zero := false
    if _, is_skip := value.(^Expr_Skip_Constructor); is_skip {
        value = nil
        skip_zero = true
    }
    alloc_cap := capacity
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
            alloca    = data_name,
            capacity  = capacity,
            elem_type = elem_type,
            is_utf8   = is_utf8,
        }
    }

    av, _ := get_array(g, name)

    // No initializer — just zero the array (unless `= void` opted out)
    if value == nil {
        if !skip_zero {
            total_bytes := alloc_cap * elem_byte_size(elem_type, g.checked)
            emit_memset_zero(g, av.alloca, total_bytes)
        }
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
        // Zero-init first (handles undersized literals), then store each element
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
                gen_array_assign(g, name, dst.capacity, dst.elem_type, const_expr, dst.is_utf8, loc)
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
            val := gen_expr_coerced(g, s.value, chain.final_type)
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
        // Bound the index by .cap (the physical buffer size). Bounding by .len
        // would forbid append-at-len, which is exactly what `dst[dst.len] = src`
        // does. Cap is the storage extent.
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
        cap_val := fresh_tmp(g)
        emit_typed_load_cap(g, cap_val, cap_gep)
        idx := gen_checked_index(g, ix.index, cap_val, ident.name, s.span)
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
            val := gen_expr_coerced(g, s.value, sv.elem_type)
            emit_store(g, sv.elem_type, val, elem_ptr)
        }
        return
    }
    av, av_ok := get_array(g, ident.name)
    if !av_ok {
        codegen_fatal(g, s.span, CODE_ARRAY, ident.name)
    }
    arr_cap: string
    if av.capacity_val != "" {
        arr_cap = av.capacity_val
    } else {
        arr_cap = fmt.tprintf("%d", usable_cap(&av))
    }
    idx := gen_checked_index(g, ix.index, arr_cap, ident.name, s.span)
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
        val := gen_expr_coerced(g, s.value, av.elem_type)
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

    // Compute low at the slice header's natural width (widening a narrower
    // bound) so the bounds check and arithmetic below stay homogeneous.
    low := gen_int_at_slice_width(g, sl.low)

    // Resolve the RHS into an Array_Handle — the same unified resolver the
    // destination uses. Covers bare idents (array / slice / partial array),
    // field access (obj.field), and array literals, so `buf[lo:hi] = src`
    // copies src's CONTENTS regardless of how src is spelled. (A scalar/struct
    // RHS never reaches here — the checker routes those to the reinterpret
    // byte-write path via assign_value_type.)
    // Must happen before high computation to support open-ended slices [low:].
    rhs_h: Array_Handle
    rhs_h_ok := false
    if arr_lit, is_lit := s.value.(^Expr_Array); is_lit {
        // Materialize the literal into a temp fixed array, then view it.
        g.tmp_counter += 1
        rhs_tmp_name := fmt.tprintf("__slice_rhs%d", g.tmp_counter)
        rhs_cap := len(arr_lit.elements)
        gen_array_assign(g, rhs_tmp_name, rhs_cap, dst_elem_type, s.value, dst_is_utf8)
        if rav, ok := get_array(g, rhs_tmp_name); ok {
            rhs_h = array_handle_from_array_var(&rav)
            rhs_h_ok = true
        }
    } else {
        rhs_h, rhs_h_ok = resolve_array_handle(g, s.value)
    }
    if !rhs_h_ok {
        codegen_fatal(g, s.span, CODE_SLICE_RHS_NAMED_ARRAY_SLICE)
    }

    // Data pointer to the RHS's first element (loaded once). For fixed arrays
    // this is the alloca; for slices / partial arrays it is header.ptr.
    rhs_data := emit_array_data(g, &rhs_h)

    // All slice arithmetic in this function operates at the header's
    // natural width — low, high, rhs_slice_len, the loop counter, and
    // the bounds checks are all w-typed. No widening/truncating dance.
    w := slice_layout.len_ir

    // Compute high — explicit, or derived from the RHS length for open-ended
    // [low:] (works for fixed arrays — len == cap — and slices / partial arrays).
    high: string
    if sl.high != nil {
        high = gen_int_at_slice_width(g, sl.high)
    } else {
        rhs_len := emit_array_len(g, &rhs_h)
        high = fresh_tmp(g)
        emit(g, "  %s = add %s %s, %s", high, w, low, rhs_len)
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

    // Load src[i] via a flat element GEP from the RHS data pointer. Works for
    // fixed arrays (data ptr is the alloca's first element) and slices /
    // partial arrays (data ptr loaded from the header) alike.
    src_gep := fresh_tmp(g)
    emit_elem_gep(g, src_gep, rhs_h.elem_type, rhs_data, i_cur, w)
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
}

// Handle: arr[idx] — read element from array or slice
// Is an integer index type signed (governs how a narrow index extends to i32)?
// byte/c8/utf8 and the unsigned numerics zero-extend; everything else (i8..i64,
// int, infer_int) sign-extends.
index_is_signed :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_Numeric:                       return v.kind == .Signed
    case Type_Byte, Type_Utf8, Type_Bool: return false
    }
    return true
}

// Generate an index expression and bounds-check it, returning an i32 operand
// the GEP can use directly. The type checker now lets an index be any integer
// (the bounds check makes it safe); this is where width is reconciled:
//   - i32 / u32 / infer literals: the original path (generate at header width,
//     keeping literal handling and bounds-check elision). A u32 past i32 max
//     reads as negative and trips the check — correct (it's out of bounds).
//   - i8 / i16: sign/zero-extend to i32 (always lossless).
//   - i64 / int / u64: bounds-check at i64 BEFORE narrowing, so a value that
//     would wrap into a valid-looking i32 traps; the in-range result provably
//     fits i32 (0 <= idx < len < 2^31), so the trunc is lossless.
gen_checked_index :: proc(g: ^Codegen, idx_expr: Expr, len_val: string, name: string, span: Span) -> string {
    t := distinct_base(expr_type(idx_expr))
    ibits, _, iok := numeric_info(t)
    wbits := slice_layout.len_size * 8
    if iok && ibits > wbits {
        // Index WIDER than the slice header (e.g. an i64 index, i32 header):
        // bounds-check at the index's own width BEFORE narrowing, so an
        // out-of-range value traps instead of wrapping, then trunc to header.
        ir := llvm_type_from_checker(t)
        idx := gen_expr(g, idx_expr)
        wide_len := len_val
        if len(len_val) > 0 && len_val[0] == '%' {
            w := fresh_tmp(g)
            emit(g, "  %s = sext %s %s to %s", w, slice_layout.len_ir, len_val, ir)
            wide_len = w
        }
        emit_bounds_check(g, idx, wide_len, name, span, ir)
        narrowed := fresh_tmp(g)
        emit(g, "  %s = trunc %s %s to %s", narrowed, ir, idx, slice_layout.len_ir)
        return narrowed
    }
    // Equal width, a narrower integer (i8/i16/i32/u32/byte/enum tag), or an
    // infer/literal index: coerce to the slice-header width — a lossless widen —
    // so the bounds check runs at that width. gen_int_at_slice_width centralises
    // it (it's the same primitive the byte-buffer offset paths use).
    idx := gen_int_at_slice_width(g, idx_expr)
    emit_bounds_check(g, idx, len_val, name, span)
    return idx
}

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
                arr_len := fmt.tprintf("%d", usable_cap(&av))
                idx := gen_checked_index(g, e.index, arr_len, fa.field, e.span)
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
                arr_len := fmt.tprintf("%d", inner_fa.size)
                idx := gen_checked_index(g, e.index, arr_len, "array", e.span)
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
                idx := gen_checked_index(g, e.index, fmt.tprintf("%d", byte_len), ident.name, e.span)
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

    // Runtime bounds check — against capacity (compile-time) or capacity_val (VLA)
    arr_cap: string
    if av.capacity_val != "" {
        arr_cap = av.capacity_val
    } else {
        arr_cap = fmt.tprintf("%d", usable_cap(&av))
    }
    idx := gen_checked_index(g, e.index, arr_cap, ident.name, e.span)

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
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
            slice_cap := fresh_tmp(g)
            emit_typed_load_cap(g, slice_cap, cap_gep)
            idx := gen_checked_index(g, e.index, slice_cap, ident.name, e.span)

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
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
            slice_cap := fresh_tmp(g)
            emit_typed_load_cap(g, slice_cap, cap_gep)
            idx := gen_checked_index(g, e.index, slice_cap, fa.field, e.span)

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
                count_runtime = gen_int_at_slice_width(g, e.count_expr)
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
        count_runtime = gen_int_at_slice_width(g, e.count_expr)
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
    idx := gen_checked_index(g, e.index, slice_len, slice_name, e.span)

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
    // end / (end-start) all live at slice width. A narrower user low/high
    // (e.g. an i32 offset) widens losslessly into that width via
    // gen_int_at_slice_width; the type checker permits the widen.
    w := slice_layout.len_ir

    // Resolve start index
    start: string
    if e.low != nil {
        start = gen_int_at_slice_width(g, e.low)
    } else {
        start = "0"
    }

    switch src in source {
    case Array_Var:
        // Slicing an array
        end: string
        if e.high != nil {
            end = gen_int_at_slice_width(g, e.high)
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
            end = gen_int_at_slice_width(g, e.high)
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
                                    elem_t: string, sl_utf8: bool) {
    w := slice_layout.len_ir
    // Evaluate the count at runtime — what `.cap()` returns and what we
    // store in the header.
    cap_user := gen_int_at_slice_width(g, s.slice_cap_expr)
    // Backing storage alloca with runtime count. `alloca T, <w> %count`
    // allocates `count * sizeof(T)` bytes. For utf8/byte/i8 element types
    // we over-align to 16 to match the comptime path's `take(T, ...)`-
    // friendly alignment policy. Goes through emit_alloca_runtime so the
    // alloca stays at the point of use — the count SSA isn't visible from
    // the entry block where static allocas live.
    data_name := fmt.tprintf("%%%s.data", s.name)
    if elem_t == "i8" {
        emit_alloca_runtime(g, data_name, "i8", w, cap_user, 16)
    } else {
        emit_alloca_runtime(g, data_name, elem_t, w, cap_user, 0)
    }
    // Zero-init policy: runtime-sized backing zeroes too (`= void` opts
    // out). Size is an SSA value, so emit the memset intrinsic directly.
    if _, zinit_skip := s.value.(^Expr_Skip_Constructor); !zinit_skip {
        elem_bytes := elem_byte_size(elem_t, g.checked)
        size_ssa := cap_user
        if elem_bytes != 1 {
            size_ssa = fresh_tmp(g)
            emit(g, "  %s = mul %s %s, %d", size_ssa, w, cap_user, elem_bytes)
        }
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %s, i1 false)", data_name, size_ssa)
    }
    // Build the slice header.
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
        alloca    = alloca_name,
        elem_type = elem_t,
        is_utf8   = sl_utf8,
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
            ir_type := partial_array_ir_type(elem_t, pa.size)
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
    if sl, ok := value.(^Expr_Slice); ok {
        if ident, id_ok := sl.expr.(^Expr_Ident); id_ok {
            if av, av_ok := get_array(g, ident.name); av_ok {
                elem_t = av.elem_type
                utf8 = av.is_utf8
            } else if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                elem_t = sv.elem_type
                utf8 = sv.is_utf8
            }
        } else if sl.expr != nil {
            // Field access or other expr — check type annotation
            sl_type := expr_type(sl.expr)
            if slice_t, st_ok := sl_type.(^Type_Slice); st_ok {
                elem_t = llvm_type_from_checker(slice_t.elem)
                _, utf8 = slice_t.elem.(Type_Utf8)
            } else if fa_t, fa_ok := sl_type.(^Type_Fixed_Array); fa_ok {
                elem_t = llvm_type_from_checker(fa_t.elem)
                _, utf8 = fa_t.elem.(Type_Utf8)
            }
        }
    }

    src := gen_expr(g, value)

    if _, slice_exists := get_slice(g, name); !slice_exists {
        alloca_name := fmt.tprintf("%%%s.slice", name)
        emit_slice_alloca(g, alloca_name)
        g.all_vars[name] = Slice_Var{
            alloca    = alloca_name,
            elem_type = elem_t,
            is_utf8   = utf8,
        }
    }

    sv, _ := get_slice(g, name)

    // Copy whole slice header { len, cap, ptr } from source into destination.
    // This shares the source's ptr — correct for a slice/view destination, but
    // WRONG for a partial array, which owns its inline elements. A top-level
    // partial-array destination reassignment (`pa = other`) is intercepted in
    // gen_stmt and deep-copied via partial_array_copy (which re-anchors ptr);
    // by the time it reaches here the destination is a genuine view.
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
gen_slice_from_expr :: proc(g: ^Codegen, name: string, value: Expr, elem_type: string, is_utf8: bool = false) {
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
                    alloca    = alloca_name,
                    elem_type = elem_type,
                    is_utf8   = is_utf8,
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
            alloca    = alloca_name,
            elem_type = elem_type,
            is_utf8   = is_utf8,
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
// Emit an integer offset/count expr at slice-header width (slice_layout.len_ir),
// extending a narrower integer (sext/zext by signedness); a value already at the
// header width passes through, and literals/infer emit at the hint width. Callers
// do their own bounds check at that width. Assumes len_ir is the widest integer
// in play (true for the i64 header) — a strictly wider index would need
// gen_checked_index's trap-before-narrow path instead.
gen_int_at_slice_width :: proc(g: ^Codegen, expr: Expr) -> string {
    t := distinct_base(expr_type(expr))
    if is_infer(t) || is_any(t) {
        return gen_expr(g, expr, slice_layout.len_ir)
    }
    ir := llvm_type_from_checker(t)
    if ir == slice_layout.len_ir {
        return gen_expr(g, expr, slice_layout.len_ir)
    }
    raw := gen_expr(g, expr)
    ext := fresh_tmp(g)
    op := index_is_signed(t) ? "sext" : "zext"
    emit(g, "  %s = %s %s %s to %s", ext, op, ir, raw, slice_layout.len_ir)
    return ext
}

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
        // Normalise the offset to slice-header width: a narrower integer (e.g. an
        // i32 cursor) widens losslessly, an `int`/i64 passes through. Mirrors the
        // index reconciliation in gen_checked_index.
        offset = gen_int_at_slice_width(g, offset_expr)
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
        offset = gen_int_at_slice_width(g, offset_expr)  // widen narrower offsets to header width
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
        // Reuse pre-bound storage when the destination is already a struct var —
        // e.g. a struct-fun field NRVO'd to %sret. Without this the read lands in
        // a throwaway local and the field reads back zero after construction.
        // Mirrors the span-form path (gen_byte_target_read_span).
        existing, ex_ok := get_struct(g, name)
        if ex_ok {
            alloca_name = existing.alloca
        } else {
            emit_alloca(g, alloca_name, target_ir_type)
        }
        emit_memcpy(g, alloca_name, elem_ptr, target_size)
        if is_big_endian {
            emit_bswap_in_place(g, alloca_name, target_ir_type, target_type)
        }
        if !ex_ok {
            g.all_vars[name] = Struct_Var{alloca = alloca_name, struct_name = struct_key(sd)}
        }
    } else if fa, fa_ok := target_type.(^Type_Fixed_Array); fa_ok {
        // Fixed-array reinterpret target: allocate the destination using the
        // `<name>.data` naming convention used elsewhere for array storage,
        // memcpy the source bytes in, register the local as an Array_Var so
        // subsequent indexing / further reinterpret-reads find it.
        // Arena fallback past 1024 bytes mirrors the standard fixed-array
        // allocation path (gen_array_assign) — otherwise large reinterpret
        // reads (e.g. `[65537]u16 = bytes[off]` for a TTF loca short-format
        // staging buffer) put hundreds of KB on the function's stack frame
        // and have, in practice, tripped clang's x86 backend on big enough
        // arrays.
        loc := format_location(span.file, span.line, span.col)
        data_name: string
        if g.context_enabled && target_size >= 1024 {
            data_name = emit_arena_bump(g, target_size, name, loc)
        } else {
            data_name = fmt.tprintf("%%%s.data", name)
            emit_alloca(g, data_name, target_ir_type)
        }
        emit_memcpy(g, data_name, elem_ptr, target_size)
        if is_big_endian {
            emit_bswap_in_place(g, data_name, target_ir_type, target_type)
        }
        elem_t := llvm_type_from_checker(fa.elem)
        utf8 := false
        if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Array_Var{
            alloca    = data_name,
            capacity  = fa.size,
            elem_type = elem_t,
            is_utf8   = utf8,
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

// Slice-form reinterpret read into a struct / fixed-array destination:
//   dst : T = src[lo:hi]   (or src[lo:], where the omitted high bound is cap)
// Destination-bounded sized read: `span = hi - lo` bytes are copied into a
// zero-initialised dst, so a span SHORTER than T leaves the tail at zero; a span
// LARGER than T traps (it would overrun the destination). Source is bounds-
// checked (lo + span <= cap). Mirrors gen_partial_array_byte_fill_at_core, but
// for a single aggregate destination rather than an element-divided one. The
// index form (src[i]) stays on gen_byte_target_read — an exact sizeof(T) read.
gen_byte_target_read_span :: proc(g: ^Codegen, name: string, buf_expr: Expr, low_expr: Expr, high_expr: Expr, span_loc: Span, target_type: Type, is_big_endian: bool) {
    target_ir_type := llvm_type_from_checker(target_type)
    target_size := checker_type_byte_size(target_type)
    w := slice_layout.len_ir
    loc := format_location(span_loc.file, span_loc.line, span_loc.col)

    data_ptr, cap_val, resolved := resolve_byte_target(g, buf_expr, span_loc)
    if !resolved {
        codegen_fatal(g, span_loc, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }

    low := "0"
    if low_expr != nil { low = gen_int_at_slice_width(g, low_expr) }
    high := cap_val
    if high_expr != nil { high = gen_int_at_slice_width(g, high_expr) }

    // span = high - low
    span_ssa := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", span_ssa, w, high, low)

    // Source bound: low + span <= cap.
    end_off := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", end_off, w, low, span_ssa)
    src_ok := fresh_label(g, "span.src.ok")
    src_err := fresh_label(g, "span.src.err")
    src_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", src_cmp, w, end_off, cap_val)
    emit_cond_br(g, src_cmp, src_err, src_ok)
    emit_label(g, src_err)
    src_global, src_len := get_string_literal(g, fmt.tprintf("<%s> runtime error: sized read runs past the source buffer\n", loc))
    src_msg_ptr := fresh_tmp(g)
    emit_string_gep(g, src_msg_ptr, src_len, src_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", src_msg_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, src_ok)

    // Destination bound: span <= sizeof(T), else trap. Catches the dynamic case;
    // a statically over-large span is rejected by the type checker.
    size_str := fmt.tprintf("%d", target_size)
    dst_ok := fresh_label(g, "span.dst.ok")
    dst_err := fresh_label(g, "span.dst.err")
    dst_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", dst_cmp, w, span_ssa, size_str)
    emit_cond_br(g, dst_cmp, dst_err, dst_ok)
    emit_label(g, dst_err)
    dst_msg := fmt.tprintf("<%s> runtime error: sized read of %%d bytes exceeds destination (%d bytes)\n", loc, target_size)
    dst_global, dst_len := get_string_literal(g, dst_msg)
    dst_msg_ptr := fresh_tmp(g)
    emit_string_gep(g, dst_msg_ptr, dst_len, dst_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s)", dst_msg_ptr, w, span_ssa)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, dst_ok)

    // src element ptr = data_ptr + low
    src_off_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", src_off_ptr, data_ptr, w, low)

    // Destination: zero-init the whole value, then copy `span` bytes; the tail
    // past `span` keeps its zero init.
    if sd := as_struct_body(target_type); sd != nil {
        // Reuse the destination's existing storage when it's already bound: a
        // bare-declared return var is NRVO-aliased to %sret, so writing there
        // keeps the self-referential partial-array ptr valid through the return
        // copy. A fresh alloca would dangle that ptr once the struct is copied
        // out of this frame.
        alloca_name := fmt.tprintf("%%%s", name)
        if existing, ex_ok := get_struct(g, name); ex_ok {
            alloca_name = existing.alloca
        } else {
            emit_alloca(g, alloca_name, target_ir_type)
        }
        emit_memset_zero(g, alloca_name, target_size)
        emit_memcpy_runtime(g, alloca_name, src_off_ptr, span_ssa)
        // The zero-fill leaves any [..N]T field header cap=0 / ptr=null; stamp
        // them (cap=N, ptr -> inline backing) so the struct is usable, exactly
        // as a normal decl's constructor would. Those fields sit past the header
        // span, so the memcpy above doesn't touch them.
        fixup_partial_array_fields(g, alloca_name, sd)
        if is_big_endian {
            emit_bswap_in_place(g, alloca_name, target_ir_type, target_type)
        }
        g.all_vars[name] = Struct_Var{alloca = alloca_name, struct_name = struct_key(sd)}
    } else if fa, fa_ok := target_type.(^Type_Fixed_Array); fa_ok {
        data_name := fmt.tprintf("%%%s.data", name)
        emit_alloca(g, data_name, target_ir_type)
        emit_memset_zero(g, data_name, target_size)
        emit_memcpy_runtime(g, data_name, src_off_ptr, span_ssa)
        if is_big_endian {
            emit_bswap_in_place(g, data_name, target_ir_type, target_type)
        }
        elem_t := llvm_type_from_checker(fa.elem)
        utf8 := false
        if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Array_Var{
            alloca    = data_name,
            capacity  = fa.size,
            elem_type = elem_t,
            is_utf8   = utf8,
        }
    } else {
        codegen_fatal(g, span_loc, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
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
        // Bounded unroll: large fixed arrays (e.g. `[65536]u32` for a TTF loca
        // table) produce ~4 IR lines per element times fa.size — a few hundred
        // is fine, tens of thousands ruins the IR file and clang. Past the
        // threshold, emit the same counter-driven loop the partial-array path
        // uses. The threshold is empirical: 16 keeps small Mat4/Vec swizzles
        // and per-table-entry record bswaps unrolled (fast paths) while
        // catching the bulk-array case.
        BSWAP_UNROLL_THRESHOLD :: 16
        if fa.size > BSWAP_UNROLL_THRESHOLD {
            // Build a ptr to element 0, then loop count = fa.size.
            elem0 := fresh_tmp(g)
            emit_array_gep_const(g, elem0, base_ir_type, base_ptr, 0)
            count_str := fmt.tprintf("%d", fa.size)
            emit_partial_bswap_loop(g, elem0, count_str, fa.elem)
            return
        }
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
// Returns true for signed/unsigned Type_Numeric (incl. i64), Type_Enum
// (integer tag). Returns false for byte/utf8/c8/bool (1 byte), floats, pointers,
// slices, etc. Caller filters out widths < 16 bits.
is_swappable_integer :: proc(t: Type) -> bool {
    bt := distinct_base(t)
    #partial switch v in bt {
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
    is_struct := as_struct_body(f.type_) != nil
    _, is_fa := f.type_.(^Type_Fixed_Array)
    if is_struct || is_fa {
        // Struct or fixed-array field — memcpy the bytes in. The load-then-
        // store path below would synthesize a single aggregate SSA value of
        // the field's full size, which clang's x86 instruction selector
        // chokes on past a few KB (a TTF loca's [65537]u32 field produced
        // a 512KB-aggregate load/store that segfaulted clang). Memcpy
        // lowers cleanly regardless of size, and the bswap walk handles
        // multi-byte integer leaves the same way it does for structs.
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
// Initialize a partial-array slot in place: set .ptr to aim at the inline
// elements area (right after the header), .len = 0, .cap = N from the type.
// Used by the `[..N]T{}` empty-literal path in gen_field_assign to handle
// the .ptr-fixup invariant that the user can't easily express by hand
// (the elements area's address is a GEP into the slot at the well-known
// PARTIAL_ELEMENTS_FIELD offset).
gen_partial_array_init_in_place :: proc(g: ^Codegen, slot_ptr: string, pa: ^Type_Partial_Array) {
    elem_t := llvm_type_from_checker(pa.elem)
    cap_n := pa.size
    ir_type := partial_array_ir_type(elem_t, cap_n)
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({
        "  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ",
        slot_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0",
    }))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, slot_ptr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, slot_ptr, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, slot_ptr, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", cap_n), cap_gep)
}

// Allocate a fresh partial-array's backing storage and register it as a
// Slice_Var. Returns the alloca's name so the caller can populate the
// elements area (e.g. via gen_partial_array_byte_fill_at_*). Used by the
// two standalone-decl entry points (Expr_Slice and Expr_Index sources).
gen_partial_array_alloc_and_register :: proc(g: ^Codegen, name: string, pa: ^Type_Partial_Array) -> string {
    // Reassignment into an existing partial array — `off16 = mem[off]` after a
    // prior `off16 : [..N]u16` decl — reuses the existing alloca. Emitting a
    // second `alloca %name` would be invalid LLVM SSA ("multiple definition of
    // local value '%name'"); the fill helpers write into the elements area, so
    // the already-constructed header (ptr -> elements, cap = N) stays valid.
    if sv, ok := get_slice(g, name); ok {
        return sv.alloca
    }
    elem_t := llvm_type_from_checker(pa.elem)
    _, pa_utf8 := pa.elem.(Type_Utf8)
    ir_type := partial_array_ir_type(elem_t, pa.size)
    alloca_name := fmt.tprintf("%%%s", name)

    if elem_t == "i8" {
        emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type, ", align 16"}))
    } else {
        emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type}))
    }
    // Zero-init policy: the byte-fill that follows is dest-bounded and may
    // leave a tail — zeroed elements make that tail (and any later
    // cstring terminator check) deterministic.
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", alloca_name, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    emit_memset_zero(g, elements_ptr, pa.size * elem_byte_size(elem_t, g.checked))
    g.all_vars[name] = Slice_Var{
        alloca    = alloca_name,
        elem_type = elem_t,
        is_utf8   = pa_utf8,
    }
    return alloca_name
}

gen_partial_array_byte_read :: proc(g: ^Codegen, name: string, pa: ^Type_Partial_Array, sl_expr: ^Expr_Slice, span: Span) {
    alloca_name := gen_partial_array_alloc_and_register(g, name, pa)
    gen_partial_array_byte_fill_at(g, alloca_name, pa, sl_expr, span)
}

gen_partial_array_byte_read_index :: proc(g: ^Codegen, name: string, pa: ^Type_Partial_Array, idx_expr: ^Expr_Index, span: Span) {
    alloca_name := gen_partial_array_alloc_and_register(g, name, pa)
    gen_partial_array_byte_fill_at_from_index(g, alloca_name, pa, idx_expr, span)
}

// Convenience entry: byte-fill from an Expr_Slice source. Computes the byte
// span from sl_expr.low/sl_expr.high and forwards to the core helper.
gen_partial_array_byte_fill_at :: proc(g: ^Codegen, slot_ptr: string, pa: ^Type_Partial_Array, sl_expr: ^Expr_Slice, span: Span) {
    w := slice_layout.len_ir
    src_data_ptr, src_cap, resolved := resolve_byte_target(g, sl_expr.expr, span)
    if !resolved {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }
    src_low := "0"
    if sl_expr.low != nil { src_low = gen_int_at_slice_width(g, sl_expr.low) }
    src_high := src_cap
    if sl_expr.high != nil { src_high = gen_int_at_slice_width(g, sl_expr.high) }

    // Runtime check 0: high >= low (slice form only — Expr_Index path skips
    // this since byte_count comes from a static cap × elem_size product
    // that can't be negative).
    inv_ok := fresh_label(g, "pa.inv.ok")
    inv_err := fresh_label(g, "pa.inv.err")
    inv_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", inv_cmp, w, src_high, src_low)
    emit_cond_br(g, inv_cmp, inv_err, inv_ok)
    emit_label(g, inv_err)
    inv_msg := fmt.tprintf("runtime error: partial-array byte read slice bounds inverted (low=%%d, high=%%d) for partial-array byte read\n")
    inv_global, inv_byte_len := get_string_literal(g, inv_msg)
    inv_ptr := fresh_tmp(g)
    emit_string_gep(g, inv_ptr, inv_byte_len, inv_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", inv_ptr, w, src_low, w, src_high)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, inv_ok)

    src_bytes := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", src_bytes, w, src_high, src_low)

    gen_partial_array_byte_fill_at_core(g, slot_ptr, pa, src_data_ptr, src_low, src_bytes, sl_expr.is_big_endian, span)
}

// Convenience entry: byte-fill from an Expr_Index source. The static cap is
// the only count signal available, so we read `cap_n * elem_bytes` bytes
// starting at idx_expr.index and set .len = cap. Useful when the source is
// "I have a pointer into a buffer, fill this fixed-cap array from there"
// without needing to compute an explicit end offset.
gen_partial_array_byte_fill_at_from_index :: proc(g: ^Codegen, slot_ptr: string, pa: ^Type_Partial_Array, idx_expr: ^Expr_Index, span: Span) {
    w := slice_layout.len_ir
    src_data_ptr, _, resolved := resolve_byte_target(g, idx_expr.expr, span)
    if !resolved {
        codegen_fatal(g, span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
    }
    src_low := "0"
    if idx_expr.index != nil { src_low = gen_int_at_slice_width(g, idx_expr.index) }
    elem_bytes := elem_byte_size(llvm_type_from_checker(pa.elem), g.checked)
    src_bytes := fmt.tprintf("%d", pa.size * elem_bytes)
    gen_partial_array_byte_fill_at_core(g, slot_ptr, pa, src_data_ptr, src_low, src_bytes, idx_expr.is_big_endian, span)
}

// Initialize a partial-array slot in place AND populate its inline elements
// from a byte-buffer span. Used by both the standalone-decl path (after
// `alloca`) and the field-assign path (slot_ptr is the field's GEP).
// Handles the header init (.ptr → elements, .len = count, .cap = N), the
// byte-span memcpy into the elements area, and optional `#big_endian`
// per-element bswap. Runtime checks: source bytes is divisible by elem
// size, and produces count <= cap. The slice-range inverted-bounds check
// lives in the Expr_Slice entry — the Expr_Index entry uses a static byte
// count that can't be negative.
gen_partial_array_byte_fill_at_core :: proc(g: ^Codegen, slot_ptr: string, pa: ^Type_Partial_Array,
                                             src_data_ptr, src_low, src_bytes: string,
                                             is_big_endian: bool, span: Span) {
    elem_t := llvm_type_from_checker(pa.elem)
    cap_n := pa.size
    alloc_cap := cap_n
    ir_type := partial_array_ir_type(elem_t, alloc_cap)
    elem_bytes := elem_byte_size(elem_t, g.checked)

    // Initialise header: ptr → elements, len → 0 (auto-add at the end),
    // cap → N. Mirrors the literal init helper.
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", slot_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, slot_ptr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, slot_ptr, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, slot_ptr, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)

    w := slice_layout.len_ir

    // Runtime check 1: src_bytes % elem_bytes == 0.
    rem := fresh_tmp(g)
    emit(g, "  %s = urem %s %s, %d", rem, w, src_bytes, elem_bytes)
    rem_ok := fresh_label(g, "pa.div.ok")
    rem_err := fresh_label(g, "pa.div.err")
    rem_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ne %s %s, 0", rem_cmp, w, rem)
    emit_cond_br(g, rem_cmp, rem_err, rem_ok)
    emit_label(g, rem_err)
    rem_msg := fmt.tprintf("runtime error: partial-array byte read at offset %%d: %%d bytes not divisible by elem size %d\n", elem_bytes)
    rem_global, rem_byte_len := get_string_literal(g, rem_msg)
    rem_ptr := fresh_tmp(g)
    emit_string_gep(g, rem_ptr, rem_byte_len, rem_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", rem_ptr, w, src_low, w, src_bytes)
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
    cap_msg := fmt.tprintf("runtime error: partial-array byte read at offset %%d: produced %%d elements, exceeds cap %d\n", cap_n)
    cap_global, cap_byte_len := get_string_literal(g, cap_msg)
    cap_msg_ptr := fresh_tmp(g)
    emit_string_gep(g, cap_msg_ptr, cap_byte_len, cap_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", cap_msg_ptr, w, src_low, w, count)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, cap_ok)

    // memcpy(elements_ptr, src_data_ptr + src_low, src_bytes).
    src_offset_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", src_offset_ptr, src_data_ptr, w, src_low)
    emit_memcpy_runtime(g, elements_ptr, src_offset_ptr, src_bytes)

    // `#big_endian` decorator on the source: byte-swap each element in
    // place. Count is runtime, so we emit a counter-driven loop wrapping the
    // per-element bswap.
    if is_big_endian {
        emit_partial_bswap_loop(g, elements_ptr, count, pa.elem)
    }

    // Auto-add to len. For a fresh decl this is + 0, so the final len = count.
    cur_len := fresh_tmp(g)
    emit_typed_load_len(g, cur_len, len_gep)
    new_len := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", new_len, w, cur_len, count)
    emit_typed_store_len(g, new_len, len_gep)
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
