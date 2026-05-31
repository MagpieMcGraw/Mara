package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Statement dispatch
// ---------------------------------------------------------------------------

gen_stmt :: proc(g: ^Codegen, stmt: Stmt) {
    switch s in stmt {
    case ^Stmt_Assign:
        // Compound assign (`lhs op= rhs`) was desugared by the parser into
        // `lhs = lhs op rhs`, with the LHS AST node shared between `s.target`
        // and the binary's `left`. To evaluate the LHS once — matching the
        // semantics of every other language with compound assignment — pre-
        // evaluate any side-effectful sub-expressions inside the LHS into
        // temps. The in-place mutation propagates to the binary's left
        // operand since both refer to the same node.
        if s.is_compound && s.target != nil {
            hoist_compound_lhs(g, s.target)
        }
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
                if (is_byte_slice(s.target_type) || is_byte_fixed_array(s.target_type) ||
                    is_byte_partial_array(s.target_type)) &&
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

        // `this_program = Program(...)` is a compiler-managed marker —
        // Phase 0 already extracted the arena info; the actual program
        // global is synthesized at main entry. Skip codegen of the
        // assignment itself.
        if s.name == "this_program" && !s.is_decl { return }

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
            // Byte-buffer reinterpret read: `arr : [N]T = buf[off]` /
            // `arr : [N]T = buf[lo:hi]`. Index form reads sizeof([N]T) exactly;
            // slice form is a destination-bounded sized read (partial fill OK).
            if sl_expr, ok := s.value.(^Expr_Slice); ok {
                if codegen_is_byte_buffer_source(g, sl_expr.expr) {
                    gen_byte_target_read_span(g, s.name, sl_expr.expr, sl_expr.low, sl_expr.high, sl_expr.span, var_type, sl_expr.is_big_endian)
                    return
                }
            }
            if idx_expr, ok := s.value.(^Expr_Index); ok {
                if codegen_is_byte_buffer_source(g, idx_expr.expr) {
                    gen_byte_target_read(g, s.name, idx_expr.expr, idx_expr.index, idx_expr.span, var_type, idx_expr.is_big_endian)
                    return
                }
            }
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
        // Slice/partial-array destinations are NOT a reinterpret — they're a
        // slice-header copy (`as_str : []utf8 = data[:]` views the same bytes
        // through a utf8-typed header), so let those fall through to the
        // standard slice-decl path below. Fixed-array destinations ARE valid
        // reinterpret targets even when they themselves are byte arrays —
        // the destination is a concrete value, not a view.
        target_is_slice_shaped := false
        if _, sl_ok := var_type.(^Type_Slice); sl_ok { target_is_slice_shaped = true }
        if _, pa_ok := var_type.(^Type_Partial_Array); pa_ok { target_is_slice_shaped = true }
        target_is_fixed_array := false
        if _, fa_ok := var_type.(^Type_Fixed_Array); fa_ok { target_is_fixed_array = true }
        if var_type != nil && !target_is_slice_shaped && (target_is_fixed_array || !is_byte_buffer(var_type)) {
            if sl_expr, ok := s.value.(^Expr_Slice); ok {
                if codegen_is_byte_buffer_source(g, sl_expr.expr) {
                    // Struct target via the slice form is a destination-bounded
                    // sized read (partial fill OK); scalars stay exact-size.
                    if as_struct_body(var_type) != nil {
                        gen_byte_target_read_span(g, s.name, sl_expr.expr, sl_expr.low, sl_expr.high, sl_expr.span, var_type, sl_expr.is_big_endian)
                    } else {
                        gen_byte_target_read(g, s.name, sl_expr.expr, sl_expr.low, sl_expr.span, var_type, sl_expr.is_big_endian)
                    }
                    return
                }
            }
            if idx_expr, ok := s.value.(^Expr_Index); ok {
                if codegen_is_byte_buffer_source(g, idx_expr.expr) {
                    gen_byte_target_read(g, s.name, idx_expr.expr, idx_expr.index, idx_expr.span, var_type, idx_expr.is_big_endian)
                    return
                }
            }
        }

        // Sized-slice repoint: `name : [:N]T = bytes[off]` — build a fresh
        // slice header whose ptr aims at &bytes[off] and len/cap = N. Has to
        // be checked BEFORE the existing-slice reassign path below, because
        // struct-constructor field decls pre-bind table_dir as a Slice_Var
        // pointing into the sret slot. Without this check, the existing-slice
        // path would dispatch to gen_slice_assign_inferred, which treats
        // `bytes[12]` as a generic source and emits a wrong-shape memcpy.
        if s.slice_cap_expr != nil {
            if sl, sl_ok := s.var_type.(^Type_Slice); sl_ok {
                if idx_expr, idx_ok := s.value.(^Expr_Index); idx_ok && codegen_is_byte_buffer_source(g, idx_expr.expr) {
                    elem_t := llvm_type_from_checker(sl.elem)
                    w := slice_layout.len_ir
                    elem_bytes := elem_byte_size(elem_t, g.checked)
                    count_runtime := gen_expr(g, s.slice_cap_expr, w)
                    bytes_ssa := fresh_tmp(g)
                    emit(g, "  %s = mul %s %s, %d", bytes_ssa, w, count_runtime, elem_bytes)
                    elem_ptr, op_ok := emit_byte_offset_ptr_runtime(g, idx_expr.expr, idx_expr.index, bytes_ssa, "slice", idx_expr.span)
                    if !op_ok {
                        codegen_fatal(g, s.span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
                    }
                    alloca_name := ""
                    if existing, ex_ok := get_slice(g, s.name); ex_ok {
                        alloca_name = existing.alloca
                    } else {
                        alloca_name = fmt.tprintf("%%%s", s.name)
                        emit_slice_alloca(g, alloca_name)
                    }
                    ptr_gep := fresh_tmp(g)
                    emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
                    emit_store(g, "ptr", elem_ptr, ptr_gep)
                    len_gep := fresh_tmp(g)
                    emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
                    emit_typed_store_len(g, count_runtime, len_gep)
                    cap_gep := fresh_tmp(g)
                    emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
                    emit_typed_store_cap(g, count_runtime, cap_gep)
                    _, sl_utf8 := sl.elem.(Type_Utf8)
                    g.all_vars[s.name] = Slice_Var{
                        alloca       = alloca_name,
                        elem_type    = elem_t,
                        is_utf8      = sl_utf8,
                        has_sentinel = sl.has_sentinel,
                        sentinel     = sl.sentinel,
                    }
                    return
                }
            }
        }

        // Partial-array byte-buffer reinterpret read:
        //   arr : [..N]T = bytes[lo:hi]
        // Allocate the partial array's inline backing, memcpy source bytes in,
        // auto-add to len = (source.len / size_of(elem)). Runtime checks:
        // source.len is a multiple of sizeof(elem); resulting count fits in cap.
        if pa, pa_ok := var_type.(^Type_Partial_Array); pa_ok {
            if sl_expr, ok := s.value.(^Expr_Slice); ok && codegen_is_byte_buffer_source(g, sl_expr.expr) {
                gen_partial_array_byte_read(g, s.name, pa, sl_expr, s.span)
                return
            }
            if idx_expr, ok := s.value.(^Expr_Index); ok && codegen_is_byte_buffer_source(g, idx_expr.expr) {
                // Expr_Index source: read cap * sizeof(elem) bytes starting
                // at the index. .len = cap. User trims afterward if needed.
                gen_partial_array_byte_read_index(g, s.name, pa, idx_expr, s.span)
                return
            }
        }

        // Check if value is a slice expression (inferred type)
        if _, ok := s.value.(^Expr_Slice); ok {
            gen_slice_assign_inferred(g, s.name, s.value)
            return
        }

        // Top-level partial-array copy into an EXISTING var (`a = b`, both
        // [..N]T — incl. distinct-over-partial-array like `str`). The
        // existing-slice reassign path below does a header-only memcpy, which
        // leaves dst.ptr aliasing src's inline elements — the two silently
        // share storage. Route through partial_array_copy, which re-anchors
        // dst.ptr to its own backing, matching the decl path's semantics
        // (`c : [..N]T = b`). Only genuine copy sources (ident / field access
        // reading existing storage) need this; the `{all expr}` broadcast and
        // slice-returning calls construct in place and stay in
        // gen_slice_assign_inferred. Decls (var not yet bound) fall through to
        // the partial-array decl path, which already uses the same helper.
        if pa, pa_ok := var_type.(^Type_Partial_Array); pa_ok {
            is_copy_source := false
            #partial switch _ in s.value {
            case ^Expr_Ident:        is_copy_source = true
            case ^Expr_Field_Access: is_copy_source = true
            }
            if is_copy_source {
                if _, src_pa := distinct_base(expr_type(s.value)).(^Type_Partial_Array); src_pa {
                    if existing, ex_ok := get_slice(g, s.name); ex_ok {
                        elem_t := llvm_type_from_checker(pa.elem)
                        alloc_cap := pa.size
                        if pa.has_sentinel { alloc_cap += 1 }
                        src_ptr := gen_expr(g, s.value)
                        partial_array_copy(g, existing.alloca, src_ptr, elem_t, alloc_cap)
                        return
                    }
                }
            }
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
            sl_sentinel_val := sl.sentinel
            // Sized slice declaration `name : [:N]T` without a byte-buffer
            // source — allocate backing storage + slice header, init to
            // (ptr, 0, N). The repoint case (byte-buffer source) is handled
            // earlier in gen_stmt. Stack-vs-arena policy mirrors fixed-array
            // decls. Sentinel slices (`[:N, 0]T`) reserve one extra element
            // for the terminator and store the physical cap; the `cap()`
            // builtin subtracts 1 for utf8 slices so the user sees N usable
            // elements.
            if s.slice_cap_expr != nil {
                cap_val, cap_ok := codegen_const_eval_int(g, s.slice_cap_expr)
                if !cap_ok {
                    // Runtime-cap path: cap_expr evaluates at runtime, backing
                    // storage uses an LLVM runtime-sized alloca (`alloca T, i32
                    // %count`), and the slice header's .cap is stored from the
                    // SSA. Skips the optional pool-allocation and string-literal
                    // init paths below — both assume a comptime-known size.
                    gen_slice_decl_runtime_cap(
                        g, s, sl, elem_t, sl_utf8, sl_sentinel, sl_sentinel_val)
                    return
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
                    // Byte buffers default to align 1, but `take(T, storage)` carves
                    // typed regions out of them and needs the data ptr to satisfy
                    // T's alignment. Over-align to 16 (covers every scalar type and
                    // SSE vectors); take's per-call padding handles the cursor side.
                    if elem_t == "i8" {
                        emit(g, "  %s = alloca [%d x i8], align 16", data_name, alloc_cap)
                    } else {
                        emit(g, "  %s = alloca [%d x %s]", data_name, alloc_cap, elem_t)
                    }
                }
                // Sentinel slices need byte `cap` of the backing storage to hold
                // the terminator on day zero — before any append happens. Zeroing
                // the whole region is the cheapest way to guarantee that and
                // also gives the slice a defined initial state for C consumers
                // that walk the pointer until they hit a 0.
                if sl.has_sentinel {
                    emit_memset_zero(g, data_name, total_bytes)
                }
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
                emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)
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
                        emit_slice_gep(g, p_ptr_gep, pool_alloca, SLICE.ptr)
                        emit_store(g, "ptr", pool_data, p_ptr_gep)
                        p_len_gep := fresh_tmp(g)
                        emit_slice_gep(g, p_len_gep, pool_alloca, SLICE.len)
                        emit_typed_store_len(g, "0", p_len_gep)
                        p_cap_gep := fresh_tmp(g)
                        emit_slice_gep(g, p_cap_gep, pool_alloca, SLICE.cap)
                        emit_typed_store_cap(g, fmt.tprintf("%d", pool_bytes), p_cap_gep)
                    }
                }
                g.all_vars[s.name] = Slice_Var{
                    alloca       = alloca_name,
                    elem_type    = elem_t,
                    is_utf8      = sl_utf8,
                    has_sentinel = sl_sentinel,
                    sentinel     = sl_sentinel_val,
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
                        emit_string_gep(g, src_ptr, len(str_bytes)+1, global)
                        emit_memcpy(g, data_name, src_ptr, len(str_bytes))
                    }
                    emit_typed_store_len(g, fmt.tprintf("%d", len(str_bytes)), len_gep)
                    // Sentinel slices use a trailing \0; for printf-style consumers
                    // that walk the data pointer until a null, write it after the
                    // copied bytes so reading stops at the literal's end.
                    if sl.has_sentinel {
                        term_ptr := fresh_tmp(g)
                        emit(g, "  %s = getelementptr i8, ptr %s, i64 %d", term_ptr, data_name, len(str_bytes))
                        emit_store(g, "i8", "0", term_ptr)
                    }
                }
                return
            }
            if s.value == nil {
                // Uninitialized slice: alloca + zero all three fields.
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_slice_alloca(g, alloca_name)
                ptr_gep := fresh_tmp(g)
                emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
                emit_store(g, "ptr", "null", ptr_gep)
                len_gep := fresh_tmp(g)
                emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
                emit_typed_store_len(g, "0", len_gep)
                cap_gep := fresh_tmp(g)
                emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
                emit_typed_store_cap(g, "0", cap_gep)
                g.all_vars[s.name] = Slice_Var{alloca = alloca_name, elem_type = elem_t, is_utf8 = sl_utf8, has_sentinel = sl_sentinel, sentinel = sl_sentinel_val}
                return
            }
            gen_slice_from_expr(g, s.name, s.value, elem_t, sl_utf8, sl_sentinel, sl_sentinel_val)
            return
        }

        // Partial array declaration: `name : [..N]T`. Allocates a single
        // structure { len, cap, ptr, [N x T] } with ptr pre-set to &elements
        // so the first slice_header_bytes are layout-compatible with a slice
        // header.
        if pa, pa_ok := var_type.(^Type_Partial_Array); pa_ok {
            elem_t := llvm_type_from_checker(pa.elem)
            _, pa_utf8 := pa.elem.(Type_Utf8)
            cap_n := pa.size
            alloc_cap := cap_n
            if pa.has_sentinel { alloc_cap += 1 }
            ir_type := partial_array_ir_type(elem_t, alloc_cap)
            alloca_name := fmt.tprintf("%%%s", s.name)
            elem_bytes := elem_byte_size(elem_t, g.checked)
            total_bytes := alloc_cap * elem_bytes
            loc := format_location(s.span.file, s.span.line, s.span.col)
            if g.context_enabled && total_bytes >= 1024 {
                // Big partial array: arena-bump the whole structure including
                // header. The arena returns a pointer to a fresh region whose
                // layout matches our IR type — initialize ptr/len/cap into it.
                data_name := emit_arena_bump(g, total_bytes + slice_header_bytes, s.name, loc)
                emit(g, "  %s = bitcast ptr %s to ptr", alloca_name, data_name)
            } else {
                if elem_t == "i8" {
                    emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type, ", align 16"}))
                } else {
                    emit_raw(g, strings.concatenate({"  ", alloca_name, " = alloca ", ir_type}))
                }
            }
            // Initialise header: ptr → elements, len → 0, cap → N.
            elements_ptr := fresh_tmp(g)
            emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", alloca_name, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
            // Sentinel partial arrays need byte `cap` of the inline storage to
            // hold the terminator before any append happens. Zero the storage
            // (not the header) so C consumers walking the pointer stop cleanly.
            if pa.has_sentinel {
                emit_memset_zero(g, elements_ptr, total_bytes)
            }
            ptr_gep := fresh_tmp(g)
            emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
            emit_store(g, "ptr", elements_ptr, ptr_gep)
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
            emit_typed_store_len(g, "0", len_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
            emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)
            g.all_vars[s.name] = Slice_Var{
                alloca       = alloca_name,
                elem_type    = elem_t,
                is_utf8      = pa_utf8,
                has_sentinel = pa.has_sentinel,
                sentinel     = pa.sentinel,
            }
            // Optional initial value: string literal into a byte/utf8 partial
            // array, or another partial array of the same shape. Mirrors the
            // sized-slice path.
            if s.value != nil {
                if str_lit, str_ok := s.value.(^Expr_String); str_ok && elem_bytes == 1 {
                    str_bytes := str_lit.value
                    if len(str_bytes) > 0 {
                        global, _ := get_string_literal(g, str_bytes)
                        src_ptr := fresh_tmp(g)
                        emit_string_gep(g, src_ptr, len(str_bytes)+1, global)
                        emit_memcpy(g, elements_ptr, src_ptr, len(str_bytes))
                    }
                    emit_typed_store_len(g, fmt.tprintf("%d", len(str_bytes)), len_gep)
                    if pa.has_sentinel {
                        term_ptr := fresh_tmp(g)
                        emit(g, "  %s = getelementptr i8, ptr %s, i64 %d", term_ptr, elements_ptr, len(str_bytes))
                        emit_store(g, "i8", "0", term_ptr)
                    }
                } else if _, src_pa_ok := distinct_base(expr_type(s.value)).(^Type_Partial_Array); src_pa_ok {
                    // Partial-to-partial copy: memcpy the header + inline elements,
                    // then re-anchor dst.ptr (which still aliases src.elements).
                    src_ptr := gen_expr(g, s.value)
                    partial_array_copy(g, alloca_name, src_ptr, elem_t, alloc_cap)
                } else {
                    codegen_fatal(g, s.span,
                        CODE_PARTIAL_ARRAY_INITIALIZER_STRING_LITERAL,
                        s.name, type_name(expr_type(s.value)))
                }
            }
            return
        }

        // Function value or pointer type declaration
        if tf, ok := var_type.(^Type_Scope); ok && tf.kind == .Fun {
            if s.value == nil {
                // Uninitialized function pointer: alloca + null
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_alloca(g, alloca_name, "ptr")
                emit_store(g, "ptr", "null", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_alloca(g, alloca_name, "ptr")
                emit_store(g, "ptr", "null", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
            }
            alloca, _ := get_scalar(g, s.name)
            emit_store(g, "ptr", val, alloca)
            return
        }

        // Pointer type declaration: x : ^Point = ...
        if _, ok := var_type.(^Type_Ptr); ok {
            if s.value == nil {
                // Uninitialized pointer: alloca + null
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_alloca(g, alloca_name, "ptr")
                emit_store(g, "ptr", "null", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_alloca(g, alloca_name, "ptr")
                emit_store(g, "ptr", "null", alloca_name)  // zero-init
                g.all_vars[s.name] = Scalar_Var{alloca_name}
            }
            alloca, _ := get_scalar(g, s.name)
            emit_store(g, "ptr", val, alloca)
            return
        }

        // Union-typed variable (must be checked before struct literal check,
        // because union variants ARE struct literals)
        if ut, ut_ok := var_type.(^Type_Union); ut_ok {
            ukey := union_key(ut)
            if s.value == nil {
                // Uninitialized union: alloca only (e.g. for foreign code to fill)
                alloca_name := fmt.tprintf("%%%s", s.name)
                emit_alloca(g, alloca_name, union_llvm_name(ukey))
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
                // gen_struct_assign arena-allocates large structs internally.
                gen_struct_assign(g, s.name, checked_st, s.value, s.span)
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
                gen_struct_assign(g, s.name, checked_st, s.value, s.span)
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

        // No initializer: alloca + zero-init below is the final state.
        // Mostly fires for class-body field decls (`x: f32`) which desugar to
        // Stmt_Assigns with nil .value; storing again from gen_expr's "0"
        // fallthrough would clobber float/double slots with `store float 0`,
        // which LLVM rejects.
        if s.value == nil {
            // Already prebound (struct-constructor field path): the name
            // resolves to a sret-field GEP, so a fresh local alloca would
            // be dead. Leave the prebind alone — the field stays at its
            // caller-provided storage (typically zeroed by an outer memset).
            if _, already := g.all_vars[s.name]; already {
                return
            }
            alloca_name := fmt.tprintf("%%%s", s.name)
            emit_alloca(g, alloca_name, ir_type)
            if ir_type == "ptr" {
                emit_store(g, "ptr", "null", alloca_name)
            } else if ir_type == "double" {
                emit(g, "  store double 0.0, ptr %s", alloca_name)
            } else if ir_type == "float" {
                emit(g, "  store float 0.0, ptr %s", alloca_name)
            } else if ir_type == "half" {
                emit(g, "  store half 0xH0000, ptr %s", alloca_name)
            } else if ir_type == "i1" {
                emit(g, "  store i1 false, ptr %s", alloca_name)
            } else if strings.has_prefix(ir_type, "[") || strings.has_prefix(ir_type, "%") {
                emit(g, "  store %s zeroinitializer, ptr %s", ir_type, alloca_name)
            } else {
                emit_store(g, ir_type, "0", alloca_name)
            }
            g.all_vars[s.name] = Scalar_Var{alloca_name}
            return
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
            emit_alloca(g, alloca_name, ir_type)
            // Zero-initialize to prevent undefined values
            if ir_type == "ptr" {
                emit_store(g, "ptr", "null", alloca_name)
            } else if ir_type == "double" {
                emit(g, "  store double 0.0, ptr %s", alloca_name)
            } else if ir_type == "float" {
                emit(g, "  store float 0.0, ptr %s", alloca_name)
            } else if ir_type == "half" {
                emit(g, "  store half 0xH0000, ptr %s", alloca_name)
            } else if ir_type == "i1" {
                emit(g, "  store i1 false, ptr %s", alloca_name)
            } else if strings.has_prefix(ir_type, "[") || strings.has_prefix(ir_type, "%") {
                emit(g, "  store %s zeroinitializer, ptr %s", ir_type, alloca_name)
            } else {
                emit_store(g, ir_type, "0", alloca_name)
            }
            g.all_vars[s.name] = Scalar_Var{alloca_name}
        }

        // Type checker enforces val_type == ir_type for concrete exprs;
        // infer literals already produce the target type via gen_expr's hint.
        alloca, _ := get_scalar(g, s.name)
        emit_store(g, ir_type, val, alloca)

    case Stmt_Call:
        // Bare function call — evaluate for side effects (e.g. print calls).
        // The result is discarded, so drop any pending temp result the call
        // registered (e.g. the sret buffer of an array-returning call like
        // `&font.glyphs.load_glyphs(...)`). Left dangling, it would be
        // mis-claimed by the next scalar decl — even one in a later function.
        gen_expr(g, s.expr)
        clear_temp_results(g)

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
        // Branch to the innermost loop's end label, unwinding any intervening
        // if/match/etc. scopes' defers + arena marks first. Works at any depth.
        if len(g.loop_label_stack) == 0 {
            codegen_fatal(g, s.span, CODE_BREAK_OUTSIDE_LOOP)
        }
        labels := g.loop_label_stack[len(g.loop_label_stack) - 1]
        emit_loop_exit(g)
        emit_br(g, labels.break_label)
    case Stmt_Continue:
        // Branch to the innermost loop's continue target (post clause or
        // condition check), unwinding intervening scopes' cleanup first.
        if len(g.loop_label_stack) == 0 {
            codegen_fatal(g, s.span, CODE_CONTINUE_OUTSIDE_LOOP)
        }
        labels := g.loop_label_stack[len(g.loop_label_stack) - 1]
        emit_loop_exit(g)
        emit_br(g, labels.continue_label)
    case ^Stmt_Defer:
        // Register the defer body on the innermost scope. emit_scope_defers
        // (called from pop_scope / emit_return_resets / emit_loop_exit) emits
        // these in LIFO order on scope exit, before the arena reset.
        if len(g.scope_stack) == 0 {
            codegen_fatal(g, s.span, CODE_DEFER_OUTSIDE_ANY_SCOPE)
        }
        top := &g.scope_stack[len(g.scope_stack) - 1]
        block: [dynamic]Stmt
        for st in s.body { append(&block, st) }
        append(&top.deferred_blocks, block)
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
    // If `name` is already bound to a slice slot (e.g. NRVO pre-aliased
    // it to %sret), let the runtime-counted take write its slice header
    // straight into that slot. Saves one alloca + one 16-byte memcpy at
    // return for leaf functions shaped `out := take(...); ...; return out`.
    dest_hdr: string
    if existing, ex_ok := get_slice(g, name); ex_ok {
        dest_hdr = existing.alloca
    }
    ptr := gen_expr_take(g, e, dest_hdr)
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
            sentinel     = sl.sentinel,
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
    // Multi-return function call: x, y := call()  or  x, y := call()?
    if len(s.values) == 0 {
        codegen_fatal(g, s.span, CODE_MULTI_ASSIGN_RHS_VALUES)
    }
    // Broadcast: `a, b = single_value` — the type checker has already flagged
    // this case. Evaluate the RHS once, store into each target. Bypasses the
    // call-machinery below.
    if s.is_broadcast {
        gen_broadcast_assign(g, s)
        return
    }
    call: ^Expr_Call
    is_try := false
    if direct, direct_ok := s.values[0].(^Expr_Call); direct_ok {
        call = direct
    } else if try_node, try_ok := s.values[0].(^Expr_Try); try_ok {
        if inner, inner_ok := try_node.inner.(^Expr_Call); inner_ok {
            call = inner
            is_try = true
        }
    }
    if call == nil {
        codegen_fatal(g, s.span, CODE_MULTI_ASSIGN_RHS_FUNCTION_CALL)
    }

    // Look up the function's multi-return list BEFORE calling gen_call
    ret_types: []Type
    if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok {
        ret_types = info.ret_types
    }

    gen_call(g, call)

    if len(g.tuple_result_ptrs) == 0 {
        codegen_fatal(g, s.span, CODE_MULTI_ASSIGN_CALL_DID_PRODUCE)
    }

    // `?` propagation: the trailing slot is the err. Test it, propagate on
    // non-zero, and shrink the bind window so the err slot isn't bound to a
    // user variable.
    bind_count := len(g.tuple_result_ptrs)
    if is_try {
        n := len(g.tuple_result_ptrs)
        err_slot := g.tuple_result_ptrs[n-1]
        err_val := fresh_tmp(g)
        emit_load_into(g, err_val, "i32", err_slot)

        prop_lbl := fresh_label(g, "try.propagate")
        cont_lbl := fresh_label(g, "try.continue")
        cmp := fresh_tmp(g)
        emit(g, "  %s = icmp ne i32 %s, 0", cmp, err_val)
        emit_cond_br(g, cmp, prop_lbl, cont_lbl)

        emit_label(g, prop_lbl)
        if g.ret_types != nil {
            n_ret := len(g.ret_types)
            for i in 0..<n_ret - 1 {
                ir_t := llvm_type_from_checker(g.ret_types[i])
                emit(g, "  store %s zeroinitializer, ptr %%sret.%d", ir_t, i)
            }
            emit(g, "  store i32 %s, ptr %%sret.%d", err_val, n_ret - 1)
            emit(g, "  ret void")
        } else {
            emit(g, "  ret i32 %s", err_val)
        }
        emit_label(g, cont_lbl)

        // The err slot has been peeled off; downstream bind loop should see
        // only the value slots. Drop the trailing entry from the tuple
        // tracking arrays so the loop's bound check shortens with us.
        bind_count = n - 1
        resize(&g.tuple_result_ptrs, bind_count)
        resize(&g.tuple_result_types, bind_count)
        if ret_types != nil && len(ret_types) == n {
            ret_types = ret_types[:n-1]
        }
    }
    _ = bind_count

    for name, i in s.names {
        if i >= len(g.tuple_result_ptrs) { break }

        elem_type := g.tuple_result_types[i]
        src_ptr := g.tuple_result_ptrs[i]

        // Struct element: alloca the struct, memcpy from sret slot, register
        // as Struct_Var so subsequent field access (info.size) works.
        if ret_types != nil && i < len(ret_types) {
            if sd := as_struct_body(distinct_base(ret_types[i])); sd != nil {
                if name == "" {
                    codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                }
                alloca_name: string
                if existing, ok := get_struct(g, name); ok {
                    alloca_name = existing.alloca
                } else {
                    alloca_name = fmt.tprintf("%%%s", name)
                    emit_alloca(g, alloca_name, elem_type)
                    g.all_vars[name] = Struct_Var{
                        alloca      = alloca_name,
                        struct_name = sd.name,
                    }
                }
                struct_llvm := struct_llvm_name(sd.name)
                emit_struct_copy(g, sd, struct_llvm, src_ptr, alloca_name)
                continue
            }
            // Fixed-array element: same shape as the struct case — alloca
            // an array, memcpy the bytes from the sret slot, register as
            // Array_Var so downstream `vtext[i]` and slice coercions see
            // the right Var_Entry kind. Without this, the load-as-value /
            // store-as-value default treats the whole `[N x T]` as a
            // scalar and breaks any call site that wants a slice of it.
            if fa, fa_ok := distinct_base(ret_types[i]).(^Type_Fixed_Array); fa_ok {
                if name == "" {
                    codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                }
                arr_elem_t := llvm_type_from_checker(fa.elem)
                arr_utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { arr_utf8 = true }
                alloca_name := fmt.tprintf("%%%s", name)
                emit_alloca(g, alloca_name, elem_type)
                total_bytes := fa.size * elem_byte_size(arr_elem_t, g.checked)
                emit_memcpy(g, alloca_name, src_ptr, total_bytes)
                g.all_vars[name] = Array_Var{
                    alloca       = alloca_name,
                    capacity     = fa.size,
                    elem_type    = arr_elem_t,
                    is_utf8      = arr_utf8,
                    has_sentinel = fa.has_sentinel,
                    sentinel     = fa.sentinel,
                }
                continue
            }
        }

        val := fresh_tmp(g)
        emit_load_into(g, val, elem_type, src_ptr)

        // Expression target (field access, index, deref)
        if name == "" && i < len(s.targets) && s.targets[i] != nil {
            gen_multi_return_store_target(g, s.targets[i], elem_type, val)
            continue
        }

        // Bare identifier target. Honor any pre-bound entry — struct
        // constructors bind every field to its %sret GEP at function entry,
        // and named return bindings bind their alloca too. Without this,
        // an existing Array_Var (Mat4 field, etc.) or Slice_Var falls
        // through to a fresh local alloca and the store-back never reaches
        // the caller's slot. Mirrors the Struct_Var handling above.
        target_ptr := ""
        if existing, ok := g.all_vars[name]; ok {
            #partial switch v in existing {
            case Scalar_Var: target_ptr = v.alloca
            case Array_Var:  target_ptr = v.alloca
            case Slice_Var:  target_ptr = v.alloca
            case Struct_Var: target_ptr = v.alloca
            case Union_Var:  target_ptr = v.alloca
            // SSA_Var: synthetic compound-assign binding, can't be a target.
            }
        }
        if target_ptr != "" {
            emit_store(g, elem_type, val, target_ptr)
        } else {
            alloca_name := fmt.tprintf("%%%s", name)
            emit_alloca(g, alloca_name, elem_type)
            emit_store(g, elem_type, val, alloca_name)
            g.all_vars[name] = Scalar_Var{alloca_name}
        }
    }

    clear(&g.tuple_result_ptrs)
    clear(&g.tuple_result_types)
}

// Store a multi-return element into an expression target (field access, index, deref).
// Broadcast assign: `a, b = single_value` — synthesize one Stmt_Assign per
// target sharing the RHS expression, then dispatch through gen_stmt. This
// reuses the full assignment-dispatch logic (slice `.len`/`.cap` writes,
// chained field access, deref targets, etc.) instead of recreating it.
// The RHS is re-evaluated per target — fine for the common case of bare
// idents and field reads, which the optimizer collapses anyway. If you
// need exactly-one-evaluation semantics for an effectful RHS, bind it to
// a local first: `tmp := f(); a, b = tmp`.
gen_broadcast_assign :: proc(g: ^Codegen, s: ^Stmt_Multi_Return_Assign) {
    target_t: Type
    if len(s.var_types) > 0 { target_t = s.var_types[0] }
    for name, i in s.names {
        synth := new(Stmt_Assign)
        synth.span = s.span
        synth.value = s.values[0]
        synth.target_type = target_t
        synth.var_type = target_t
        synth.env_type = target_t
        if name != "" {
            synth.name = name
        } else if i < len(s.targets) && s.targets[i] != nil {
            synth.target = s.targets[i]
        } else {
            codegen_fatal(g, s.span, CODE_UNSUPPORTED_MULTI_RETURN_TARGET_EXPRESSION)
        }
        gen_stmt(g, synth)
    }
}

gen_multi_return_store_target :: proc(g: ^Codegen, target: Expr, elem_type: string, val: string) {
    #partial switch t in target {
    case ^Expr_Field_Access:
        st, base_ptr, found := resolve_lhs_struct(g, t.expr)
        if !found {
            codegen_fatal(g, t.span, CODE_MULTI_RETURN_TARGET_FIELD_ACCESS)
        }
        st_llvm := struct_llvm_name(struct_key(st))
        idx := struct_field_index(st, t.field)
        if idx < 0 {
            codegen_fatal(g, t.span, CODE_STRUCT_FIELD, struct_key(st), t.field)
        }
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
        emit_store(g, elem_type, val, gep)
    case ^Expr_Index:
        codegen_fatal(g, t.span, CODE_INDEX_TARGET_MULTI_RETURN_ASSIGN)
    case ^Expr_Unary:
        if t.op == .Caret {
            // Deref target: store through pointer
            ptr_val := gen_expr(g, t.operand)
            emit_store(g, elem_type, val, ptr_val)
        } else {
            codegen_fatal(g, t.span, CODE_UNARY_OP_VALID_MULTI_RETURN, t.op)
        }
    case:
        codegen_fatal(g, {}, CODE_UNSUPPORTED_MULTI_RETURN_TARGET_EXPRESSION)
    }
}

// ---------------------------------------------------------------------------
// Return statement codegen
// ---------------------------------------------------------------------------

emit_ret_void :: proc(g: ^Codegen) {
    emit_return_resets(g)
    emit(g, "  ret void")
}

// Multi-return: store each value into its sret param.
gen_return_tuple :: proc(g: ^Codegen, s: Stmt_Return) {
    // Fallible constructor: sret slot 0 is the implicit Self (built in place),
    // so the explicit return values map onto the trailing declared slots —
    // `return <err>` fills slot 1, never Self. offset is 0 for ordinary funs.
    offset := 0
    if g.ctor_has_self_sret { offset = 1 }
    for val, i in s.values {
        slot := i + offset
        resolved_type := distinct_base(g.ret_types[slot])
        elem_type := llvm_type_from_checker(g.ret_types[slot])
        sret_ptr := fmt.tprintf("%%sret.%d", slot)
        // Array/fixed-array returns: memcpy from alloca to sret. When the
        // local's alloca IS the sret slot (named-return NRVO), the memcpy is
        // a self-copy — skip it. LLVM memcpy with overlapping src/dst is UB.
        if fa, fa_ok := resolved_type.(^Type_Fixed_Array); fa_ok {
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if av, av_ok := get_array(g, ident.name); av_ok {
                    if av.alloca == sret_ptr { continue }
                    arr_size := fa.size * checker_type_byte_size(fa.elem)
                    emit_memcpy(g, sret_ptr, av.alloca, arr_size)
                    continue
                }
            }
        }
        // Struct returns: field-wise copy from src alloca to sret (can't use
        // `store %struct %ptr` — the value operand must be a struct, not a ptr).
        if sd := as_struct_body(resolved_type); sd != nil {
            struct_llvm := struct_llvm_name(sd.name)
            if lit, lit_ok := val.(^Expr_Struct_Literal); lit_ok {
                emit_struct_literal_into(g, sd, struct_llvm, sret_ptr, lit)
                continue
            }
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if src_sv, sv_ok := get_struct(g, ident.name); sv_ok {
                    if src_sv.alloca == sret_ptr { continue }
                    emit_struct_copy(g, sd, struct_llvm, src_sv.alloca, sret_ptr)
                    continue
                }
            }
            // Fallback: gen_expr yields a pointer to the struct
            src_ptr := gen_expr(g, val, elem_type)
            emit_struct_copy(g, sd, struct_llvm, src_ptr, sret_ptr)
            continue
        }
        // Slice returns: memcpy the slice descriptor (slice_header_bytes).
        // The single-slice-return path (gen_return_slice) does the same; this
        // mirrors it for slices as one element of a multi-return tuple. The
        // bare scalar fallback below would otherwise emit
        // `store { ptr, i64 } <alloca-ptr>, ptr %sret.N` which is invalid IR
        // (alloca-ptr is `ptr`, not the slice descriptor value).
        if _, sl_ok := resolved_type.(^Type_Slice); sl_ok {
            src: string
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if sv, sv_ok := get_slice(g, ident.name); sv_ok {
                    src = sv.alloca
                }
            }
            if src == "" {
                src = gen_expr(g, val, elem_type)
            }
            if src == sret_ptr { continue }
            emit_memcpy(g, sret_ptr, src, slice_header_bytes)
            continue
        }
        v := gen_expr(g, val, elem_type)
        emit_store(g, elem_type, v, sret_ptr)
    }
    // Implicit `.Ok` fill for trailing err slots the user omitted. The type
    // checker guarantees the missing positions are err-typed (i32 in IR), and
    // .Ok is the zero value (set_id 0, tag 0). With a Self slot 0 (constructor)
    // the offset keeps the fill on the declared err slots and never on Self.
    for i in (len(s.values) + offset)..<len(g.ret_types) {
        sret_ptr := fmt.tprintf("%%sret.%d", i)
        emit_store(g, "i32", "0", sret_ptr)
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
        emit_field_gep_into(g, gep, struct_llvm, dst_ptr, idx)
        emit_store(g, ft, val, gep)
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
                emit_field_gep_into(g, gep, struct_llvm, dst_ptr, sdf_i)
                emit_store(g, sdf_ft, val, gep)
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
        // Case B: returning a struct variable. Skip the self-copy when the
        // local is NRVO-aliased to sret (already constructed in place).
        if src_sv, sv_ok := get_struct(g, ident.name); sv_ok && src_sv.alloca != sret_ptr {
            emit_struct_copy(g, sret_st, sret_llvm, src_sv.alloca, sret_ptr)
        }
    } else if call, call_ok := ret_val.(^Expr_Call); call_ok {
        // Case C: chained struct return. If the callee has a struct sret,
        // forward our own sret directly — no intermediate alloca, no copy.
        // Falls back to alloca+copy for foreign calls or anything else the
        // Fun_Info path can't see.
        cn := call_resolved_name(call)
        if info, info_ok := lookup_fun_info(g, cn); info_ok && info.ret_struct != "" {
            gen_call_into_struct(g, call, sret_ptr, &info)
        } else {
            result_ptr := gen_call(g, call)
            emit_struct_copy(g, sret_st, sret_llvm, result_ptr, sret_ptr)
        }
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

            w := slice_layout.len_ir
            cond_label := fresh_label(g, "ret.copy.cond")
            body_label := fresh_label(g, "ret.copy.body")
            end_label  := fresh_label(g, "ret.copy.end")

            idx_ptr := fresh_tmp(g)
            emit_alloca(g, idx_ptr, w)
            emit_store(g, w, "0", idx_ptr)
            emit_br(g, cond_label)

            emit_label(g, cond_label)
            idx := fresh_tmp(g)
            emit_load_into(g, idx, w, idx_ptr)
            cmp := fresh_tmp(g)
            emit(g, "  %s = icmp slt %s %s, %s", cmp, w, idx, copy_bound)
            emit_cond_br(g, cmp, body_label, end_label)

            emit_label(g, body_label)
            idx2 := fresh_tmp(g)
            emit_load_into(g, idx2, w, idx_ptr)
            src_gep := fresh_tmp(g)
            emit_array_gep_var(g, src_gep, src_type, src_av.alloca, idx2, w)
            val := fresh_tmp(g)
            emit_load_into(g, val, sret_av.elem_type, src_gep)
            dst_gep := fresh_tmp(g)
            emit_array_gep_var(g, dst_gep, sret_type, sret_av.alloca, idx2, w)
            emit_store(g, sret_av.elem_type, val, dst_gep)
            next := fresh_tmp(g)
            emit(g, "  %s = add %s %s, 1", next, w, idx2)
            emit_store(g, w, next, idx_ptr)
            emit_br(g, cond_label)

            emit_label(g, end_label)
        }
    } else if arr_lit, lit_ok := arr_ret_val.(^Expr_Array); lit_ok {
        // Case B: returning an array literal
        for elem, i in arr_lit.elements {
            val := gen_expr(g, elem, sret_av.elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, sret_type, sret_av.alloca, i)
            emit_store(g, sret_av.elem_type, val, gep)
        }
    } else if call, call_ok := arr_ret_val.(^Expr_Call); call_ok {
        // Case C: returning result of another array-returning call
        // Pass sret pointers directly to the inner call — no intermediate copy
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok && info.ret_array_cap > 0 {
            gen_call_into_array(g, call, &sret_av, &info)
        } else {
            gen_call(g, call)
        }
    } else if sl, sl_ok := arr_ret_val.(^Expr_Struct_Literal); sl_ok {
        // Case D: returning a distinct-fixed-array literal like
        // `F64x8{a, b, c, ...}` or `Vec3{x, y, z}`. The type checker has
        // already filled in `array_values` (resolving swizzle-name forms
        // like `Quat{w = 1}` into positional slots), so each element is
        // just a GEP+store into sret. Without this case the return was
        // silently emitting `ret void` with no writes — every distinct-
        // array literal return produced uninitialized output.
        for elem, i in sl.array_values {
            if elem == nil { continue }   // nil slot — leave as zero
            val := gen_expr(g, elem, sret_av.elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, sret_type, sret_av.alloca, i)
            emit_store(g, sret_av.elem_type, val, gep)
        }
    }
    emit_ret_void(g)
}

// Slice return: copy the slice header into sret.
gen_return_slice :: proc(g: ^Codegen, s: Stmt_Return, sret_slv: Slice_Var) {
    ret_val := len(s.values) > 0 ? s.values[0] : nil

    // Chained slice return: forward our sret directly to the callee. Slice
    // returns share the void+sret ABI with structs, so gen_call_into_struct
    // works as-is — the trailing `ptr %sret` arg lands in the callee's
    // sret slot. Skips one alloca + one memcpy per chain layer.
    if call, call_ok := ret_val.(^Expr_Call); call_ok {
        cn := call_resolved_name(call)
        if info, info_ok := lookup_fun_info(g, cn); info_ok && info.ret_slice_elem != "" {
            gen_call_into_struct(g, call, sret_slv.alloca, &info)
            emit_ret_void(g)
            return
        }
    }

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
    // Skip the self-copy when the local is NRVO-aliased to sret (the body
    // already wrote the header in place). Mirrors gen_return_struct's
    // alloca-comparison check.
    if src != "" && src != sret_slv.alloca {
        emit_memcpy(g, sret_slv.alloca, src, slice_header_bytes)
    }
    emit_ret_void(g)
}

// Scalar return: emit `ret <type> <value>` at the declared return type.
// Type checker enforces value type matches; the only special case is the
// `return 0` for ptr returns where infer-int 0 becomes the ptr null literal.
gen_return_scalar :: proc(g: ^Codegen, s: Stmt_Return) {
    val := gen_expr(g, s.values[0], g.current_ret_type)
    ret_type := g.current_ret_type
    if ret_type == "ptr" && val == "0" {
        val = "null"
    }
    emit_return_resets(g)
    emit(g, "  ret %s %s", ret_type, val)
}

gen_return :: proc(g: ^Codegen, s: Stmt_Return) {
    // Multi-return functions always route through the tuple path. The value
    // count may be short of the slot count when trailing err slots are being
    // implicitly filled with `.Ok` (see gen_return_tuple).
    if g.ret_types != nil && len(g.ret_types) > 1 {
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
    // Bare `return` — emit a terminator that matches the enclosing function's
    // IR return type. Mara's `main` lowers to `i64 @main` (C entry-point
    // convention), so an unadorned `return` inside main must emit `ret i64 0`
    // rather than `ret void`. For ordinary void-returning Mara fns the type
    // string is empty and we fall back to `ret void`.
    switch g.current_ret_type {
    case "":
        emit(g, "  ret void")
    case "void":
        emit(g, "  ret void")
    case "ptr":
        emit(g, "  ret ptr null")
    case:
        emit(g, "  ret %s 0", g.current_ret_type)
    }
}

// Walk a compound-assignment LHS and hoist every index sub-expression into a
// precomputed temp. The LHS is shared with the binary RHS's `left` operand,
// so in-place mutation here means the binary reads from the same hoisted
// temp during its own codegen — preserving single-evaluation semantics for
// the LHS as a whole.
//
// Only Expr_Index gets rewritten because field accesses and pointer derefs
// are pure address computations; the only sub-expression a user can drop a
// call (or any other effectful expression) into is an index slot. We hoist
// unconditionally rather than gating on a purity check — mem2reg folds the
// alloca+store+load triple to nothing at -O3, and a "is this expression
// pure?" predicate would grow stale as the language adds new effect-bearing
// kinds, with silent double-evaluation as the failure mode.
hoist_compound_lhs :: proc(g: ^Codegen, lhs: Expr) {
    #partial switch n in lhs {
    case ^Expr_Field_Access:
        hoist_compound_lhs(g, n.expr)
    case ^Expr_Index:
        hoist_compound_lhs(g, n.expr)
        n.index = hoist_lhs_subexpr(g, n.index)
    case ^Expr_Unary:
        if n.op == .Caret {
            hoist_compound_lhs(g, n.operand)
        }
    }
}

// Evaluate `e` once, register the SSA result under a synthetic name, and
// return an Expr_Ident that resolves back to that SSA at codegen time
// (without re-emitting the expression or allocating a stack slot). The
// synthetic name uses a `$` prefix the lexer can't produce so it can't
// collide with anything in scope.
hoist_lhs_subexpr :: proc(g: ^Codegen, e: Expr) -> Expr {
    ir_type := "i64"
    if t := expr_type(e); t != nil && !is_untyped(t) {
        ir_type = llvm_type_from_checker(t)
    }
    val := gen_expr(g, e, ir_type)
    g.tmp_counter += 1
    name := fmt.tprintf("$compound.%d", g.tmp_counter)
    g.all_vars[name] = SSA_Var{ssa = val, ir_type = ir_type}
    id := new(Expr_Ident)
    id.name = name
    id.type_ = expr_type(e)
    return id
}

// For compound assigns (`lhs op= rhs`), the LHS appears on both sides of the
// desugared `lhs = lhs op rhs` and would normally be re-emitted by gen_expr
// on the binary's `left`. The patched gen_*_assign procs already compute the
// LHS address once for the store; calling this helper at that point pre-
// loads through the same address, registers the loaded SSA under a synthetic
// name, and substitutes that name for `bin.left`. The binary's right operand
// and final store then run normally — but the value-side address chain
// (including any null/bounds checks it carried) is gone.
apply_compound_load_substitute :: proc(g: ^Codegen, s: ^Stmt_Assign, addr: string, ir_type: string) {
    if !s.is_compound { return }
    bin, ok := s.value.(^Expr_Binary)
    if !ok { return }
    cur := fresh_tmp(g)
    emit_load_into(g, cur, ir_type, addr)
    g.tmp_counter += 1
    name := fmt.tprintf("$compound_val.%d", g.tmp_counter)
    g.all_vars[name] = SSA_Var{ssa = cur, ir_type = ir_type}
    id := new(Expr_Ident)
    id.name = name
    id.type_ = expr_type(bin.left)
    bin.left = id
}
