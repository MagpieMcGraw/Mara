package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Statement dispatch
// ---------------------------------------------------------------------------

gen_stmt :: proc(g: ^Codegen, stmt: Stmt) {
    switch s in stmt {
    case ^Stmt_Assign:
        if s == g.consume_stmt {
            gen_consume_init(g, s)
            return
        }
        // Complex LHS: dispatch by target kind.
        if s.target != nil {
            gen_target_assign(g, s)
            return
        }
        // Skip include statements — desugared into imports before codegen
        if _, is_include := s.value.(^Expr_Include); is_include { return }

        // `this_program = Program(...)` is a compiler-managed marker —
        // Phase 0 already extracted the arena info; the actual program
        // global is synthesized at main entry. Skip codegen of the
        // assignment itself.
        if s.name == "this_program" && !s.is_decl { return }

        // `_ = e` is a discard (the checker binds nothing): evaluate `e` for
        // its effects and drop the value, exactly like a bare call statement.
        if s.name == "_" && !s.is_decl {
            gen_expr(g, s.value)
            clear_temp_results(g)
            return
        }

        // Reassignment with the uninitialized marker (`x = void` on a
        // non-pointer, or `#skip_constructor`): de-init is flow-side
        // read-tracking only — nothing to emit. Pointer `p = void` stores
        // null through the normal scalar path. Decls fall through: their
        // per-shape paths allocate storage and recognize the skip themselves.
        if !s.is_decl {
            _, is_skip := s.value.(^Expr_Skip_Constructor)
            _, is_ptr := s.var_type.(^Type_Ptr)
            if is_skip || (is_void_literal(s.value) && !is_ptr) { return }
        }

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
            // Array-returning call — or an overloaded operator, the call it
            // is: use sret convention
            call, call_ok := s.value.(^Expr_Call)
            if !call_ok { call, call_ok = overload_as_call(s.value) }
            if call_ok {
                info, info_ok := call_fun_info(g, call)
                if info_ok && info.ret_array_cap > 0 {
                    if existing, ex_ok := get_array(g, s.name); ex_ok {
                        // NRVO alias: call directly into pre-registered buffer
                        gen_call_into_array(g, call, &existing, &info, s.is_decl, var_ref(s.name, s.var_type))
                    } else {
                        // The call writes the whole result: storage, not zeroed.
                        unzeroed := Expr_Skip_Constructor{span = s.span}
                        gen_array_assign(g, s.name, fa.size, elem_t, &unzeroed, utf8, loc)
                        existing, _ := get_array(g, s.name)
                        gen_call_into_array(g, call, &existing, &info, true)
                    }
                    return
                }
            }
            gen_array_assign(g, s.name, fa.size, elem_t, s.value, utf8, loc, fa.elem)
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
                    count_runtime := gen_int_at_slice_width(g, s.slice_cap_expr)
                    elem_ptr, op_ok := emit_byte_offset_ptr_runtime(g, idx_expr.expr, idx_expr.index, count_runtime, elem_bytes, "slice", idx_expr.span)
                    if !op_ok {
                        codegen_fatal(g, s.span, CODE_BYTE_BUFFER_READ_SOURCE_BYTE)
                    }
                    alloca_name := ""
                    if existing, ex_ok := get_slice(g, s.name); ex_ok {
                        alloca_name = existing.alloca
                    } else {
                        alloca_name = emit_local_alloca(g, fmt.tprintf("%%%s", s.name), SLICE_IR_TYPE)
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
                        alloca    = alloca_name,
                        elem_type = elem_t,
                        is_utf8   = sl_utf8,
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

        // A partial array OWNS its elements inline, so a value assigned to an
        // EXISTING one (`a = b`, a prebound struct field or named return — incl.
        // distinct-over-partial-array like `str`) is copied into those
        // elements. The slice paths below repoint the header instead, which
        // left `a` aliasing the source — or dangling into a call's temp, and
        // out of the function when `a` was returned. Only the `{all expr}`
        // broadcast still goes there (it constructs in place). Decls (var not
        // yet bound) go to the partial-array decl path below, which already
        // copies.
        _, pa_dest := var_type.(^Type_Partial_Array)
        if pa, pa_ok := var_type.(^Type_Partial_Array); pa_ok && s.value != nil {
            if existing, ex_ok := get_slice(g, s.name); ex_ok {
                if _, lit := s.value.(^Expr_Struct_Literal); !lit || is_empty_partial_array_literal(s.value) {
                    gen_store_partial_array_into(g, existing.alloca, pa, s.value, s.span, s.name, dest_fresh = s.is_decl, dest_expr = var_ref(s.name, s.var_type))
                    return
                }
            }
        }

        // Check if value is a slice expression (inferred type)
        if _, ok := s.value.(^Expr_Slice); ok && !pa_dest {
            gen_slice_assign_inferred(g, s.name, s.value, var_type, decl = s.is_decl)
            return
        }

        // Check if reassigning to an existing slice variable
        if _, sl_ok := get_slice(g, s.name); sl_ok {
            gen_slice_assign_inferred(g, s.name, s.value, decl = s.is_decl)
            return
        }

        // Slice type from alloc() or explicit []byte annotation
        if sl, sl_ok := var_type.(^Type_Slice); sl_ok {
            elem_t := llvm_type_from_checker(sl.elem)
            _, sl_utf8 := sl.elem.(Type_Utf8)
            // Sized slice declaration `name : [:N]T` without a byte-buffer
            // source — allocate backing storage + slice header, init to
            // (ptr, 0, N). The repoint case (byte-buffer source) is handled
            // earlier in gen_stmt. Stack-vs-arena policy mirrors fixed-array
            // decls.
            if s.slice_cap_expr != nil {
                cap_val, cap_ok := codegen_const_eval_int(g, s.slice_cap_expr)
                if !cap_ok {
                    // Runtime-cap path: cap_expr evaluates at runtime, backing
                    // storage uses an LLVM runtime-sized alloca (`alloca T, i32
                    // %count`), and the slice header's .cap is stored from the
                    // SSA. Skips the optional pool-allocation and string-literal
                    // init paths below — both assume a comptime-known size.
                    gen_slice_decl_runtime_cap(g, s, sl, elem_t, sl_utf8)
                    return
                }
                cap_n := int(cap_val)
                alloc_cap := cap_n
                elem_bytes := elem_byte_size(elem_t, g.checked)
                total_bytes := alloc_cap * elem_bytes
                loc := format_location(s.span.file, s.span.line, s.span.col)
                data_name: string
                if g.context_enabled && total_bytes >= 1024 {
                    data_name = emit_arena_bump(g, total_bytes, s.name, loc)
                } else {
                    data_want := fmt.tprintf("%%%s.data", s.name)
                    // Byte buffers default to align 1, but `take(T, storage)` carves
                    // typed regions out of them and needs the data ptr to satisfy
                    // T's alignment. Over-align to 16 (covers every scalar type and
                    // SSE vectors); take's per-call padding handles the cursor side.
                    if elem_t == "i8" {
                        data_name = emit_local_alloca(g, data_want, fmt.tprintf("[%d x i8], align 16", alloc_cap))
                    } else {
                        data_name = emit_local_alloca(g, data_want, fmt.tprintf("[%d x %s]", alloc_cap, elem_t))
                    }
                }
                // Zero-init policy: backing storage starts zeroed — covers
                // both fresh stack allocas and arena regions (dirty after a
                // reset). `= void` (skip marker) is the per-decl opt-out.
                if _, zinit_skip := s.value.(^Expr_Skip_Constructor); !zinit_skip {
                    emit_memset_zero(g, data_name, total_bytes)
                }
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), SLICE_IR_TYPE)
                ptr_gep := fresh_tmp(g)
                emit_slice_gep(g, ptr_gep, alloca_name, SLICE.ptr)
                emit_store(g, "ptr", data_name, ptr_gep)
                len_gep := fresh_tmp(g)
                emit_slice_gep(g, len_gep, alloca_name, SLICE.len)
                emit_typed_store_len(g, "0", len_gep)
                cap_gep := fresh_tmp(g)
                emit_slice_gep(g, cap_gep, alloca_name, SLICE.cap)
                emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)
                g.all_vars[s.name] = Slice_Var{
                    alloca      = alloca_name,
                    elem_type   = elem_t,
                    is_utf8     = sl_utf8,
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
                        // Bring the rodata \0 along when there's headroom —
                        // mirrors gen_partial_array_init_value.
                        copy_n := len(str_bytes)
                        if cap_n > copy_n { copy_n += 1 }
                        emit_memcpy(g, data_name, src_ptr, copy_n)
                    }
                    emit_typed_store_len(g, fmt.tprintf("%d", len(str_bytes)), len_gep)
                }
                return
            }
            if s.value == nil {
                // Uninitialized slice: its header zero (null, 0, 0).
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), SLICE_IR_TYPE)
                emit_memset_zero(g, alloca_name, slice_header_bytes)
                g.all_vars[s.name] = Slice_Var{alloca = alloca_name, elem_type = elem_t, is_utf8 = sl_utf8}
                return
            }
            gen_slice_from_expr(g, s.name, s.value, elem_t, sl_utf8, decl = s.is_decl)
            return
        }

        // Partial array declaration: `name : [..N]T`. Allocates a single
        // structure { len, cap, ptr, [N x T] } with ptr pre-set to &elements
        // so the first slice_header_bytes are layout-compatible with a slice
        // header.
        if pa, pa_ok := var_type.(^Type_Partial_Array); pa_ok {
            elem_t := llvm_type_from_checker(pa.elem)
            _, pa_utf8 := pa.elem.(Type_Utf8)
            alloc_cap := pa.size
            ir_type := partial_array_ir_type(elem_t, alloc_cap)
            alloca_name := fmt.tprintf("%%%s", s.name)
            elem_bytes := elem_byte_size(elem_t, g.checked)
            total_bytes := alloc_cap * elem_bytes
            // NRVO: when this local is the value a partial-array-returning
            // function hands back, build it directly in the caller's %sret slot
            // — no fresh alloca. The header stamp below points ptr at %sret's
            // own inline storage (which lives in the caller's frame), so the
            // `return` is a no-op (gen_return skips the self-copy when src is
            // already %sret). Otherwise route storage through the shared
            // primitive (stack for small, arena for big — one decision site).
            is_nrvo := g.ret_partial_cap > 0 && s.name == g.nrvo_var
            if is_nrvo {
                alloca_name = "%sret"
            } else {
                alloca_name = emit_partial_array_storage(g, alloca_name, pa, s.name, s.span)
            }
            // Its elements zeroed and its header over them (ptr → elements,
            // len 0, cap N) — unless the value writes the WHOLE partial array
            // (another partial array, copied header and all, then re-anchored,
            // or a partial-array-returning call built in place): then both are
            // dead stores. A string or slice fills only a prefix, so those keep
            // both. `= void` opts out of the zeroing.
            _, zinit_skip := s.value.(^Expr_Skip_Constructor)
            elements_ptr := emit_partial_array_zero(g, alloca_name, pa, stamp = !writes_whole_partial_array(g, s.value), zero = !zinit_skip)
            g.all_vars[s.name] = Slice_Var{
                alloca    = alloca_name,
                elem_type = elem_t,
                is_utf8   = pa_utf8,
            }
            // Bare decl: construct each backing element so `[..N]Struct` /
            // `[..N]str64` comes up with field defaults applied and nested
            // headers stamped, not just zeroed. An initial value (handled
            // below) fills the backing itself; `= void` makes s.value non-nil
            // (Skip_Constructor), so this nil check also honours the opt-out.
            if s.value == nil {
                gen_construct_elements(g, elements_ptr, pa.elem, alloc_cap)
            }
            // Optional initial value: string literal into a byte/utf8 partial
            // array, or another partial array of the same shape. Shared with the
            // struct-field-default path above.
            if s.value != nil {
                // A partial-array-returning call builds directly into our slot
                // (true end-to-end NRVO — no temp, no copy). When this slot IS
                // %sret, the inner call's result lands straight in the outer
                // caller's return slot. Mirrors gen_slice_from_expr.
                if call, call_ok := s.value.(^Expr_Call); call_ok {
                    if info, info_ok := call_fun_info(g, call); info_ok && info.ret_partial_cap > 0 {
                        gen_call_into_struct(g, call, alloca_name, &info, true)
                        return
                    }
                }
                gen_partial_array_init_value(g, alloca_name, s.value, elem_t, elem_bytes, alloc_cap, pa, s.span, s.name)
            }
            return
        }

        // Function value or pointer type declaration
        if tf, ok := var_type.(^Type_Scope); ok && tf.kind == .Fun {
            if s.value == nil {
                // Uninitialized function pointer: alloca + null
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), "ptr")
                emit_store(g, "ptr", "null", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), "ptr")
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
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), "ptr")
                emit_store(g, "ptr", "null", alloca_name)
                g.all_vars[s.name] = Scalar_Var{alloca_name}
                return
            }
            val := gen_expr(g, s.value)
            if !is_scalar(g, s.name) {
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), "ptr")
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
            _, skip := s.value.(^Expr_Skip_Constructor)
            if s.value == nil || skip {
                // A constructor's field, prebound to its place in the
                // caller's slot (zeroed there): left alone.
                if _, bound := get_union(g, s.name); bound && g.result_vars[s.name] { return }
                // A bare declaration: zeroed, like every value; `= void`
                // opts out (e.g. for foreign code to fill).
                alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), union_llvm_name(ukey))
                if !skip { emit_memset_zero(g, alloca_name, union_byte_size(g.checked, ut)) }
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
                gen_struct_assign(g, s.name, checked_st, s.value, s.span, s.is_decl)
                return
            }
        }

        // Check if value is a struct literal (inferred type)
        if _, lit_ok := s.value.(^Expr_Struct_Literal); lit_ok {
            if sd := as_struct_body(expr_type(s.value)); sd != nil {
                if checked_st, cs_ok := lookup_struct(g, sd.name); cs_ok {
                    gen_struct_assign(g, s.name, checked_st, s.value, s.span, s.is_decl)
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
                gen_struct_assign(g, s.name, checked_st, s.value, s.span, s.is_decl)
                return
            }
        }

        // Check if value is a call to a struct-returning or array-returning function
        if call, call_ok := s.value.(^Expr_Call); call_ok {
            if info, info_ok := call_fun_info(g, call); info_ok && info.ret_struct != "" {
                result_ptr := gen_call(g, call)
                g.all_vars[s.name] = Struct_Var{
                    alloca = result_ptr,
                    struct_name = info.ret_struct,
                }
                return
            }
            if info, info_ok := call_fun_info(g, call); info_ok && info.ret_array_cap > 0 {
                if existing, ex_ok := get_array(g, s.name); ex_ok {
                    gen_call_into_array(g, call, &existing, &info, s.is_decl, var_ref(s.name, s.var_type))
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
                    gen_array_assign(g, s.name, fa.size, "i8", s.value, true, loc)
                    return
                }
            }
        }

        // Determine the IR type for this variable.
        // Priority: checker type > existing alloca > expression type
        ir_type := "i64"
        existing_slot, has_slot := get_scalar(g, s.name)
        if var_type != nil && !is_untyped(var_type) {
            ir_type = llvm_type_from_checker(var_type)
        } else if at, at_ok := g.emitted_allocas[existing_slot]; has_slot && at_ok {
            ir_type = at
        } else {
            ir_type = expr_ir_type(g, s.value)
        }

        // No initializer: alloca + zero-init below is the final state.
        // Mostly fires for class-body field decls (`x: f32`) which desugar to
        // Stmt_Assigns with nil .value; storing again from gen_expr's "0"
        // fallthrough would clobber float/double slots with `store float 0`,
        // which LLVM rejects. A scalar `x : T = void` (skip marker) takes
        // the same path — allocate, zero, store nothing else.
        _, scalar_skip := s.value.(^Expr_Skip_Constructor)
        if s.value == nil || scalar_skip {
            // Already prebound (struct-constructor field path): the name
            // resolves to a sret-field GEP, so a fresh local alloca would
            // be dead. Leave the prebind alone — the field stays at its
            // caller-provided storage (typically zeroed by an outer memset).
            if _, already := g.all_vars[s.name]; already {
                return
            }
            alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), ir_type)
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

        val := gen_expr_coerced(g, s.value, ir_type)

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
            alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", s.name), ir_type)
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
        // Broadcast was desugared into s.checked by the type checker — emit
        // those plain assignments. Destructure (s.checked empty) needs the
        // call-once distribution that gen_multi_return_assign provides.
        if len(s.checked) > 0 {
            for inner in s.checked { gen_stmt(g, inner) }
        } else {
            gen_multi_return_assign(g, s)
        }

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
    }
    if const_expr, found := codegen_const_value(g, e); found {
        return codegen_const_eval_int(g, const_expr)
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
    g.alias_vars[name] = true // a typed view of `storage`'s bytes
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
            alloca    = ptr,
            capacity  = fa.size,
            elem_type = elem_ir,
            is_utf8   = is_utf8,
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
            alloca    = ptr,
            elem_type = elem_ir,
            is_utf8   = is_utf8,
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
    // (Broadcast never reaches here — the type checker desugars it into
    // s.checked, which the dispatcher emits as plain assignments.)
    if len(s.values) == 0 {
        codegen_fatal(g, s.span, CODE_MULTI_ASSIGN_RHS_VALUES)
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
    if info, info_ok := call_fun_info(g, call); info_ok {
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
        emit_err_propagate(g, err_val)
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
        if name == "_" { continue }   // discarded: no binding

        elem_type := g.tuple_result_types[i]
        src_ptr := g.tuple_result_ptrs[i]

        // Aggregate elements: a fresh binding claims the call's slot (it was
        // allocated for this statement and nothing else reads it); existing
        // storage, or an expression target, is copied into.
        //
        // Struct element: registered as a Struct_Var so subsequent field
        // access (info.size) works.
        if ret_types != nil && i < len(ret_types) {
            if sd := as_struct_body(distinct_base(ret_types[i])); sd != nil {
                if name == "" {
                    // Expression target (`x, obj.field := f()`): copy the
                    // slot into the target's storage in place.
                    addr, addr_ok := gen_multi_return_target_addr(g, s, i)
                    if !addr_ok {
                        codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                    }
                    emit_value_copy(g, ret_types[i], addr, src_ptr)
                    continue
                }
                if existing, ok := get_struct(g, name); ok {
                    emit_value_copy(g, ret_types[i], existing.alloca, src_ptr)
                    continue
                }
                g.all_vars[name] = Struct_Var{alloca = src_ptr, struct_name = sd.name}
                continue
            }
            // Fixed-array element: same shape as the struct case — alloca
            // an array, memcpy the bytes from the sret slot, register as
            // Array_Var so downstream `vtext[i]` and slice coercions see
            // the right Var_Entry kind. Without this, the load-as-value /
            // store-as-value default treats the whole `[N x T]` as a
            // scalar and breaks any call site that wants a slice of it.
            if fa, fa_ok := distinct_base(ret_types[i]).(^Type_Fixed_Array); fa_ok {
                arr_elem_t := llvm_type_from_checker(fa.elem)
                arr_utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { arr_utf8 = true }
                if name == "" {
                    // Expression target: copy the slot's bytes into the
                    // target's storage in place.
                    addr, addr_ok := gen_multi_return_target_addr(g, s, i)
                    if !addr_ok {
                        codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                    }
                    emit_value_copy(g, ret_types[i], addr, src_ptr)
                    continue
                }
                if existing, exists := get_array(g, name); exists {
                    // Pre-bound storage (ctor field, named return slot):
                    // copy into it so the store reaches the caller's buffer.
                    emit_value_copy(g, ret_types[i], existing.alloca, src_ptr)
                    continue
                }
                // Fresh binding: claim the call's slot buffer directly — it
                // was allocated for this statement (stack or arena per the
                // big-array policy) and nothing else reads it. An alloca +
                // memcpy here doubled a multi-MB return on the stack.
                g.all_vars[name] = Array_Var{
                    alloca    = src_ptr,
                    capacity  = fa.size,
                    elem_type = arr_elem_t,
                    is_utf8   = arr_utf8,
                }
                continue
            }
            // Partial-array element: claim the call's slot directly (it holds
            // the full {ptr,len,cap,[N]} struct the return side re-anchored) and
            // register it as a Slice_Var, so `b[i]` / `b.len` work. Mirrors the
            // fixed-array case — the scalar fallback below would bind it as a
            // Scalar_Var (the whole struct loaded as a value) and indexing fails.
            if pa, pa_ok := distinct_base(ret_types[i]).(^Type_Partial_Array); pa_ok {
                pa_elem_t := llvm_type_from_checker(pa.elem)
                _, pa_utf8 := pa.elem.(Type_Utf8)
                if name == "" {
                    addr, addr_ok := gen_multi_return_target_addr(g, s, i)
                    if !addr_ok {
                        codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                    }
                    partial_array_copy(g, addr, src_ptr, pa_elem_t, pa.size, pa.elem)
                    continue
                }
                if existing, exists := get_slice(g, name); exists {
                    partial_array_copy(g, existing.alloca, src_ptr, pa_elem_t, pa.size, pa.elem)
                    continue
                }
                g.all_vars[name] = Slice_Var{
                    alloca    = src_ptr,
                    elem_type = pa_elem_t,
                    is_utf8   = pa_utf8,
                }
                continue
            }
            // Slice element: the sret slot holds the {ptr,len,cap} header — for the
            // return-a-slice-into-a-caller-buffer idiom (`view, e := fill(&buf)`,
            // where `view` aliases buf) its ptr views that buffer. Claim/copy it as
            // a Slice_Var so `view[i]` / `view.len` work; the scalar fallback below
            // would bind it Scalar_Var (the header loaded as an opaque value) and
            // indexing would fail. Mirrors the partial-array case above.
            if sl, sl_ok := distinct_base(ret_types[i]).(^Type_Slice); sl_ok {
                sl_elem_t := llvm_type_from_checker(sl.elem)
                _, sl_utf8 := sl.elem.(Type_Utf8)
                if name == "" {
                    addr, addr_ok := gen_multi_return_target_addr(g, s, i)
                    if !addr_ok {
                        codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                    }
                    emit_value_copy(g, ret_types[i], addr, src_ptr)
                    continue
                }
                if existing, exists := get_slice(g, name); exists {
                    emit_value_copy(g, ret_types[i], existing.alloca, src_ptr)
                    continue
                }
                g.all_vars[name] = Slice_Var{
                    alloca    = src_ptr,
                    elem_type = sl_elem_t,
                    is_utf8   = sl_utf8,
                }
                continue
            }
            // Union element: claim/copy the slot as a Union_Var. The scalar
            // fallback below would bind it Scalar_Var, so a later `match` or
            // copy would get the union loaded as a VALUE where every union
            // consumer expects its address.
            if ut, ut_ok := distinct_base(ret_types[i]).(^Type_Union); ut_ok {
                if name == "" {
                    addr, addr_ok := gen_multi_return_target_addr(g, s, i)
                    if !addr_ok {
                        codegen_fatal(g, s.span, CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION)
                    }
                    emit_value_copy(g, ret_types[i], addr, src_ptr)
                    continue
                }
                if existing, exists := get_union(g, name); exists {
                    emit_value_copy(g, ret_types[i], existing.alloca, src_ptr)
                    continue
                }
                g.all_vars[name] = Union_Var{alloca = src_ptr, union_name = union_key(ut)}
                continue
            }
        }

        // Expression target (field access, deref): its place, then the value
        // into it.
        if name == "" && i < len(s.targets) && s.targets[i] != nil {
            at := gen_multi_return_target_place(g, s.targets[i])
            val := fresh_tmp(g)
            emit_load_into(g, val, elem_type, src_ptr)
            emit_store(g, elem_type, val, at)
            continue
        }
        val := fresh_tmp(g)
        emit_load_into(g, val, elem_type, src_ptr)

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
            alloca_name := emit_local_alloca(g, fmt.tprintf("%%%s", name), elem_type)
            emit_store(g, elem_type, val, alloca_name)
            g.all_vars[name] = Scalar_Var{alloca_name}
        }
    }

    clear(&g.tuple_result_ptrs)
    clear(&g.tuple_result_types)
}

// Address of an expression target (field access / deref) so an aggregate
// multi-return slot (struct, fixed array) can be copied into it in place.
// Index targets aren't supported — same restriction as the scalar path.
gen_multi_return_target_addr :: proc(g: ^Codegen, s: ^Stmt_Multi_Return_Assign, i: int) -> (string, bool) {
    if i >= len(s.targets) || s.targets[i] == nil { return "", false }
    #partial switch t in s.targets[i] {
    case ^Expr_Field_Access:
        st, base_ptr, found := resolve_lhs_struct(g, t.expr)
        if !found { return "", false }
        st_llvm := struct_llvm_name(struct_key(st))
        idx := struct_field_index(st, t.field)
        if idx < 0 { return "", false }
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
        return gep, true
    case ^Expr_Unary:
        if t.op == .Caret {
            return gen_expr(g, t.operand), true
        }
    }
    return "", false
}

// The place of a multi-return element's expression target (field access,
// deref) — computed before the element is read into it, as the graph does.
gen_multi_return_target_place :: proc(g: ^Codegen, target: Expr) -> string {
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
        return gep
    case ^Expr_Index:
        codegen_fatal(g, t.span, CODE_INDEX_TARGET_MULTI_RETURN_ASSIGN)
    case ^Expr_Unary:
        if t.op == .Caret {
            return gen_expr(g, t.operand)   // a deref target: where the pointer points
        }
        codegen_fatal(g, t.span, CODE_UNARY_OP_VALID_MULTI_RETURN, t.op)
    }
    codegen_fatal(g, {}, CODE_UNSUPPORTED_MULTI_RETURN_TARGET_EXPRESSION)
}

// ---------------------------------------------------------------------------
// Return statement codegen
// ---------------------------------------------------------------------------

emit_ret_void :: proc(g: ^Codegen) {
    emit_return_resets(g)
    emit(g, "  ret void")
}

// Multi-return: each value into its sret param, in the graph's order. The
// values first — a register value computed, an aggregate literal built in its
// slot, any other aggregate found where it is — then the defers the return
// leaves, then the slots written. (A defer can't change a returned local, so
// the order returns the same values either way.)
gen_return_tuple :: proc(g: ^Codegen, s: Stmt_Return) {
    // Fallible constructor: sret slot 0 is the implicit Self (built in place),
    // so the explicit return values map onto the trailing declared slots —
    // `return <err>` fills slot 1, never Self. offset is 0 for ordinary funs.
    offset := 0
    if g.ctor_has_self_sret { offset = 1 }
    // A slot's write, made once the defers ran: a register value stored, a
    // value copied from where it is (a slice's header alone; a partial array
    // re-anchored to the slot's own elements).
    Write_Kind :: enum { Store, Value, Header, Partial }
    Slot_Write :: struct { kind: Write_Kind, slot: string, t: Type, ir, val: string }
    writes := make([dynamic]Slot_Write, 0, len(g.ret_types), context.temp_allocator)
    for val, i in s.values {
        slot := i + offset
        t := g.ret_types[slot]
        resolved_type := distinct_base(t)
        elem_type := llvm_type_from_checker(t)
        sret_ptr := fmt.tprintf("%%sret.%d", slot)
        // Fixed array: a local copied — unless its storage IS the slot
        // (named-return NRVO; a memcpy onto itself is UB).
        if fa, fa_ok := resolved_type.(^Type_Fixed_Array); fa_ok {
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if av, av_ok := get_array(g, ident.name); av_ok {
                    if av.alloca != sret_ptr { append(&writes, Slot_Write{.Value, sret_ptr, t, "", av.alloca}) }
                    continue
                }
            }
            // Anything else (a literal in either spelling, a call, a field) is
            // built or copied straight into the sret slot by the array store —
            // literal slots element by element, so a [3]str64 of string
            // literals or a [2]Pick of variants is constructed in place. The
            // scalar fallback below would store the array's ADDRESS (or an
            // aggregate constant holding SSA values) — invalid IR.
            _, is_utf8 := distinct_base(fa.elem).(Type_Utf8)
            gen_store_array_into(g, sret_ptr, fa.size, llvm_type_from_checker(fa.elem), val, is_utf8, dest_fresh = true)
            continue
        }
        // Union slot: a variant literal is built in place; any other union
        // value is pointer-valued, copied by the union's true size.
        if ut, ut_ok := resolved_type.(^Type_Union); ut_ok {
            lit, is_lit := val.(^Expr_Struct_Literal)
            if _, is_bare := bare_variant_literal(val); is_bare || (is_lit && lit.name != "") {
                gen_store_union_into(g, sret_ptr, ut, val, dest_fresh = true)
                continue
            }
            src := gen_expr(g, val, union_llvm_name(union_key(ut)))
            if src != sret_ptr { append(&writes, Slot_Write{.Value, sret_ptr, t, "", src}) }
            continue
        }
        // Struct slot: a literal built in place — the same construction
        // primitive as everywhere else (zero-init, the init function's
        // defaults, then the literal's fields), so `Foo{...}` returned in a
        // tuple slot behaves as a `Foo{...}` decl does — any other value
        // copied from where it is.
        if sd := as_struct_body(resolved_type); sd != nil {
            if lit, lit_ok := val.(^Expr_Struct_Literal); lit_ok {
                gen_store_struct_into(g, sret_ptr, sd, lit, dest_fresh = true)
                continue
            }
            src := ""
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if src_sv, sv_ok := get_struct(g, ident.name); sv_ok { src = src_sv.alloca }
            }
            if src == "" { src = gen_expr(g, val, elem_type) }   // a pointer to the struct
            if src != sret_ptr { append(&writes, Slot_Write{.Value, sret_ptr, t, "", src}) }
            continue
        }
        // Slice slot: its header copied (slice_header_bytes), as the single
        // slice return does. Not gen_expr for anything but a slice local: a
        // fixed array or string literal decaying to the slice yields its DATA
        // pointer there, which the copy would read as a header.
        if _, sl_ok := resolved_type.(^Type_Slice); sl_ok {
            src: string
            if ident, id_ok := val.(^Expr_Ident); id_ok {
                if sv, sv_ok := get_slice(g, ident.name); sv_ok { src = sv.alloca }
            }
            if src == "" { src = gen_slice_value_ptr(g, val) }
            if src != sret_ptr { append(&writes, Slot_Write{.Header, sret_ptr, t, "", src}) }
            continue
        }
        // Partial-array slot: the whole {ptr,len,cap,[N]} deep-copied into the
        // slot, its ptr re-anchored to the slot's own elements
        // (partial_array_copy), as the single partial-array return does.
        if _, pa_ok := resolved_type.(^Type_Partial_Array); pa_ok {
            src := gen_expr(g, val, elem_type)
            if src != sret_ptr { append(&writes, Slot_Write{.Partial, sret_ptr, t, "", src}) }
            continue
        }
        append(&writes, Slot_Write{.Store, sret_ptr, t, elem_type, gen_expr_coerced(g, val, elem_type)})
    }
    // Implicit `.Ok` fill for trailing err slots the user omitted. The type
    // checker guarantees the missing positions are err-typed (i32 in IR), and
    // .Ok is the zero value (set_id 0, tag 0). With a Self slot 0 (constructor)
    // the offset keeps the fill on the declared err slots and never on Self.
    for i in (len(s.values) + offset)..<len(g.ret_types) {
        append(&writes, Slot_Write{.Store, fmt.tprintf("%%sret.%d", i), g.ret_types[i], "i32", "0"})
    }
    emit_return_resets(g)
    for w in writes {
        switch w.kind {
        case .Store:
            emit_store(g, w.ir, w.val, w.slot)
        case .Value:
            emit_value_copy(g, w.t, w.slot, w.val)
        case .Header:
            emit_memcpy(g, w.slot, w.val, slice_header_bytes)
        case .Partial:
            pa := distinct_base(w.t).(^Type_Partial_Array)
            partial_array_copy(g, w.slot, w.val, llvm_type_from_checker(pa.elem), pa.size, pa.elem)
        }
    }
    emit(g, "  ret void")
}

// Struct return: copy value into %sret.
gen_return_struct :: proc(g: ^Codegen, s: Stmt_Return, sret_sv: Struct_Var) {
    sret_st, _ := lookup_struct(g, sret_sv.struct_name)
    sret_ptr := sret_sv.alloca
    ret_val := len(s.values) > 0 ? s.values[0] : nil

    // A local NRVO-aliased to sret was constructed in place: nothing to copy.
    nrvo := false
    if ident, id_ok := ret_val.(^Expr_Ident); id_ok {
        src_sv, sv_ok := get_struct(g, ident.name)
        nrvo = sv_ok && src_sv.alloca == sret_ptr
    }
    // Anything else goes through the one struct store: a literal is built in
    // place, a call forwards our sret (NRVO), a variable, constant, element,
    // field, ternary or pointee is copied. (Only literals, idents and calls
    // were handled here once — any other shape returned without writing sret.)
    if ret_val != nil && !nrvo {
        gen_store_struct_into(g, sret_ptr, sret_st, ret_val, dest_fresh = true)
    }
    emit_ret_void(g)
}

// Array return: copy array data into sret.
gen_return_array :: proc(g: ^Codegen, s: Stmt_Return, sret_av_in: Array_Var) {
    sret_av := sret_av_in
    sret_type := fmt.tprintf("[%d x %s]", sret_av.capacity, sret_av.elem_type)
    arr_ret_val := len(s.values) > 0 ? s.values[0] : nil

    // Every supported value shape sets handled; an unhandled shape must be a
    // loud codegen error, never a silent fall-through to `ret void` that leaves
    // the sret slot unwritten (= a zeroed array returned to the caller).
    handled := false
    if ident, id_ok := arr_ret_val.(^Expr_Ident); id_ok {
        // Case A: returning an array variable (NRVO if aliased to sret, else copied).
        // A non-array ident (e.g. a slice) leaves handled=false → error below.
        src_av, av_ok := get_array(g, ident.name)
        if av_ok { handled = true }
        if av_ok && src_av.alloca != sret_av.alloca {
            emit_memcpy(g, sret_av.alloca, src_av.alloca, sret_av.capacity * elem_byte_size(sret_av.elem_type, g.checked))
            reanchor_partial_arrays(g, expr_type(arr_ret_val), sret_av.alloca)
        }
    } else if arr_lit, lit_ok := arr_ret_val.(^Expr_Array); lit_ok {
        // Case B: returning an array literal: zeroed, then its elements
        handled = true
        emit_memset_zero(g, sret_av.alloca, sret_av.capacity * elem_byte_size(sret_av.elem_type, g.checked))
        et := literal_elem_type(arr_lit)
        stamped := stamp_literal_array(g, sret_av.alloca, et, sret_av.capacity)
        for elem, i in arr_lit.elements {
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, sret_type, sret_av.alloca, i)
            gen_store_elem_into(g, gep, sret_av.elem_type, et, elem, arr_lit.span, slot_fresh = true, stamped = stamped)
        }
    } else if call, call_ok := arr_ret_val.(^Expr_Call); call_ok {
        // Case C: returning result of another array-returning call
        // Pass sret pointers directly to the inner call — no intermediate copy
        handled = true
        if info, info_ok := call_fun_info(g, call); info_ok && info.ret_array_cap > 0 {
            gen_call_into_array(g, call, &sret_av, &info, true)
        } else {
            // Not an array-returning function (a distinct conversion, ...):
            // the array store copies whatever value it stands for, or errors.
            gen_store_array_into(g, sret_av.alloca, sret_av.capacity, sret_av.elem_type, call, dest_fresh = true)
        }
    } else if sl, sl_ok := arr_ret_val.(^Expr_Struct_Literal); sl_ok {
        // Case D: returning a distinct-fixed-array literal like
        // `F64x8{a, b, c, ...}` or `Vec3{x, y, z}`. The type checker has
        // already filled in `array_values` (resolving swizzle-name forms
        // like `Quat{w = 1}` into positional slots), so each element is
        // just a GEP+store into sret. Without this case the return was
        // silently emitting `ret void` with no writes — every distinct-
        // array literal return produced uninitialized output. A
        // `[N]T = all x` broadcast return lands here too (it writes every
        // slot); anything else is zeroed first, its nil slots left so.
        handled = true
        if !sl.is_broadcast { emit_memset_zero(g, sret_av.alloca, sret_av.capacity * elem_byte_size(sret_av.elem_type, g.checked)) }
        et := literal_elem_type(sl)
        if !gen_broadcast_scalar(g, sret_av.alloca, sret_type, sret_av.elem_type, et, sl) {
            for elem, i in sl.array_values {
                if elem == nil { continue }   // nil slot — leave as zero
                gep := fresh_tmp(g)
                emit_array_gep_const(g, gep, sret_type, sret_av.alloca, i)
                gen_store_elem_into(g, gep, sret_av.elem_type, et, elem, sl.span, slot_fresh = true)
            }
        }
    }
    if !handled {
        codegen_fatal(g, s.span, CODE_GEN_RETURN_ARRAY_UNHANDLED_VALUE)
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
        if info, info_ok := call_fun_info(g, call); info_ok && info.ret_slice_elem != "" {
            gen_call_into_struct(g, call, sret_slv.alloca, &info, true)
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

// Partial-array return: build into %sret. An NRVO'd return (the local's storage
// already IS %sret) is a no-op — `ret void`. Any other source (a param, a
// branchy local, a call result) is copied in via partial_array_copy, which
// re-anchors %sret.ptr to %sret's own inline storage.
gen_return_partial_array :: proc(g: ^Codegen, s: Stmt_Return) {
    if len(s.values) > 0 {
        src := gen_expr(g, s.values[0])
        if src != "%sret" {
            pa, _ := distinct_base(expr_type(s.values[0])).(^Type_Partial_Array)
            partial_array_copy(g, "%sret", src, g.ret_partial_elem, g.ret_partial_cap, pa.elem if pa != nil else nil)
        }
    }
    emit_ret_void(g)
}

// Scalar return: emit `ret <type> <value>` at the declared return type.
// Type checker enforces value type matches; the only special case is the
// `return 0` for ptr returns where infer-int 0 becomes the ptr null literal.
gen_return_scalar :: proc(g: ^Codegen, s: Stmt_Return) {
    ret_type := g.current_ret_type
    val := gen_expr_coerced(g, s.values[0], ret_type)
    if strings.has_prefix(ret_type, "%union.") {
        // Union returned by value: gen_expr yields a pointer to the union
        // storage (a materialized variant literal, a union local, …); load the
        // aggregate so it's returned by value.
        loaded := fresh_tmp(g)
        emit_load_into(g, loaded, ret_type, val)
        val = loaded
    } else if ret_type == "ptr" && val == "0" {
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
    // Single partial-array return (e.g. `-> str64`): the callee builds into the
    // caller-provided %sret slot. NRVO when the returned local was aliased to
    // %sret by the decl path — then this is just `ret void`; otherwise the value
    // is copied into %sret (re-anchoring its ptr to %sret's own inline storage).
    if g.ret_partial_cap > 0 {
        gen_return_partial_array(g, s)
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
    //
    // Like the value-return path (gen_return_scalar) and break/continue
    // (emit_loop_exit), a terminator must emit its own scope cleanup —
    // deferred blocks + arena resets — before the terminator. gen_body_block
    // drops the scope entry WITHOUT re-emitting once it sees the terminator, so
    // skipping this here silently dropped defers on a bare `return`.
    emit_return_resets(g)
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

// An assignment through a field, index, slice or deref target.
//
// Compound assign (`lhs op= rhs`) was desugared by the parser into
// `lhs = lhs op rhs`, with the LHS AST node shared between `s.target` and the
// binary's `left`. To evaluate the LHS once — matching the semantics of every
// other language with compound assignment — pre-evaluate any side-effectful
// sub-expressions inside the LHS into temps, and later load the LHS through its
// store address instead of re-emitting it (apply_compound_load_substitute).
// Both rewrite the statement, so they run on a scratch copy of it: the AST is
// the source of truth for everything after codegen, and a deferred compound
// assign is emitted once per scope exit — each emission starts from the source.
gen_target_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    s := s
    if s.is_compound {
        s = compound_scratch(s)
        hoist_compound_lhs(g, s.target)
    }
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
}

// A copy of a compound assignment that codegen may rewrite: the statement, the
// LHS spine hoisting descends (field access, index, deref), and the binary
// whose left operand the load substitute replaces. The copy's binary keeps
// pointing at the copy's target, as the source's does. Every other node —
// index expressions, the right operand — stays shared and is only read.
@(private="file")
compound_scratch :: proc(s: ^Stmt_Assign) -> ^Stmt_Assign {
    spine :: proc(e: Expr) -> Expr {
        #partial switch n in e {
        case ^Expr_Field_Access:
            c := new_clone(n^); c.expr = spine(n.expr); return c
        case ^Expr_Index:
            c := new_clone(n^); c.expr = spine(n.expr); return c
        case ^Expr_Unary:
            if n.op == .Caret { c := new_clone(n^); c.operand = spine(n.operand); return c }
        }
        return e
    }
    c := new_clone(s^)
    c.target = spine(s.target)
    if bin, ok := s.value.(^Expr_Binary); ok {
        b := new_clone(bin^)
        if bin.left == s.target { b.left = c.target }
        c.value = b
    }
    return c
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
//
// A pointer-valued LHS (fixed array, struct — an operator overload's operand,
// `pos += vel`) isn't loaded: the synthetic name is bound to its storage, the
// way every other value of those types is represented.
apply_compound_load_substitute :: proc(g: ^Codegen, s: ^Stmt_Assign, addr: string, ir_type: string) {
    if !s.is_compound { return }
    bin, ok := s.value.(^Expr_Binary)
    if !ok { return }
    g.tmp_counter += 1
    name := fmt.tprintf("$compound_val.%d", g.tmp_counter)
    lhs_t := distinct_base(expr_type(bin.left))
    if is_pointer_valued_type(lhs_t) { g.alias_vars[name] = true } // IS the LHS's storage
    if fa, is_fa := lhs_t.(^Type_Fixed_Array); is_fa {
        _, utf8 := fa.elem.(Type_Utf8)
        g.all_vars[name] = Array_Var{alloca = addr, capacity = fa.size, elem_type = llvm_type_from_checker(fa.elem), is_utf8 = utf8}
    } else if sd := as_struct_body(lhs_t); sd != nil {
        g.all_vars[name] = Struct_Var{alloca = addr, struct_name = struct_key(sd)}
    } else {
        cur := fresh_tmp(g)
        emit_load_into(g, cur, ir_type, addr)
        g.all_vars[name] = SSA_Var{ssa = cur, ir_type = ir_type}
    }
    id := new(Expr_Ident)
    id.name = name
    id.type_ = expr_type(bin.left)
    bin.left = id
}

// `r := pk` opening a function that consumes pk into its result (see
// consumed_param_of): r IS the result slot. A caller doing `x = f(x, …)`
// passes x as both pk and the slot, and then the copy would be x onto itself —
// so it's skipped when the two pointers are equal, and is the ordinary copy
// into the slot otherwise.
gen_consume_init :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    src := ""
    #partial switch v in g.all_vars[g.consume_src] {
    case Struct_Var: src = v.alloca
    case Array_Var:  src = v.alloca
    case Slice_Var:  src = v.alloca
    }
    if src == "" {
        codegen_fatal(g, s.span, CODE_CALL_UNKNOWN_FUNCTION_FUN_INFO, g.consume_src)
    }
    same := fresh_tmp(g)
    emit(g, "  %s = icmp eq ptr %%sret, %s", same, src)
    copy_label := fresh_label(g, "consume.copy")
    done_label := fresh_label(g, "consume.done")
    emit_cond_br(g, same, done_label, copy_label)
    emit_label(g, copy_label)
    emit_value_copy(g, s.var_type, "%sret", src)
    emit_br(g, done_label)
    emit_label(g, done_label)
    // Struct and fixed-array NRVO locals were bound to %sret at function
    // entry; a partial-array one binds at its declaration — here.
    if pa, is_pa := distinct_base(s.var_type).(^Type_Partial_Array); is_pa {
        _, utf8 := pa.elem.(Type_Utf8)
        g.all_vars[s.name] = Slice_Var{alloca = "%sret", elem_type = llvm_type_from_checker(pa.elem), is_utf8 = utf8}
    }
}
