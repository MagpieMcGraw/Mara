package mara

import "core:fmt"
import "core:slice"
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
                // For fixed-array vars, the alloca (`[N x T]*`) IS the array's
                // address — the same pointer the value path hands out. Lets
                // `&arr` feed a `^T` / foreign pointer param (e.g. gl.* calls).
                if av, av_ok := get_array(g, ident.name); av_ok {
                    return av.alloca
                }
                if alloca_name, v_ok := get_scalar(g, ident.name); v_ok {
                    return alloca_name
                }
                // `&this_program` — the compiler-managed program global is
                // stored at @__mara_program_storage; the address is the
                // storage label. Used in cross-DLL handover
                // (`game_run(&this_program, ...)`).
                if ident.name == "this_program" {
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
            // Address-of a temporary slice (`&buf[a:b]`) — usually an attempt
            // to pass it to a ^[]T parameter. A slice expression builds a fresh
            // header with no address to point at; give the targeted fix.
            if _, is_slice := e.operand.(^Expr_Slice); is_slice {
                codegen_fatal(g, e.span, CODE_CANNOT_TAKE_ADDRESS_SLICE_TEMP)
            }
            codegen_fatal(g, e.span, CODE_CANNOT_TAKE_ADDRESS_EXPRESSION)
        case .Caret:
            // Dereference: load through pointer
            ptr_val := gen_expr(g, e.operand)

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
            op_type := target_type != "" ? target_type : expr_ir_type(g, e.operand)
            if op_type == "double" || op_type == "float" {
                tmp := fresh_tmp(g)
                emit(g, "  %s = fneg %s %s", tmp, op_type, operand)
                return tmp
            }
            // `-%x`: wrapping negate — plain `0 - x`, two's-complement, no trap
            // (so -%MIN == MIN and unsigned negate is well-defined).
            if e.wrapping {
                tmp := fresh_tmp(g)
                emit(g, "  %s = sub %s 0, %s", tmp, op_type, operand)
                return tmp
            }
            // Integer negation is `0 - x` and joins the overflow-checked
            // arithmetic family: -MIN_INT traps like binary `-` instead of
            // silently wrapping. Unsigned only reaches here through an infer
            // cell that settled unsigned after the unary check ran — usub
            // traps for any x != 0, matching the binary underflow rule.
            op := "ssub"
            if _, kind, k_ok := numeric_info(expr_type(e.operand)); k_ok && kind == .Unsigned {
                op = "usub"
            }
            return emit_checked_arith(g, op, op_type, "0", operand, e.span)
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
        // In-place struct override: `var{ a = x; b = y }` applies the field
        // writes directly to the existing variable's storage (statement form;
        // yields no value). Reuses the same applier as construct-time overrides.
        if e.override_target != "" {
            if sv, ok := get_struct(g, e.override_target); ok {
                if sd, sd_ok := lookup_struct(g, sv.struct_name); sd_ok {
                    llvm_name := struct_llvm_name(struct_key(sd))
                    apply_struct_literal_fields(g, e, sd, llvm_name, sv.alloca)
                }
            }
            return "0"
        }
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
        // Named struct literal in expression position (e.g. a struct argument
        // `f(Edge{...})` or an overloaded-operator operand): materialize into
        // a temp alloca and yield the pointer — struct-shaped expressions are
        // ptr-valued (see expr_ir_type). gen_store_struct_into gives the full
        // construct semantics: zero-init, init-fn defaults, then field stores.
        if sd := as_struct_body(e.type_); sd != nil {
            tmp := fresh_tmp(g)
            emit_alloca(g, tmp, struct_llvm_name(struct_key(sd)))
            gen_store_struct_into(g, tmp, sd, e)
            return tmp
        }
        codegen_fatal(g, e.span, CODE_STRUCT_LITERAL_UNTYPED_EXPR)
    case ^Expr_Field_Access:
        return gen_field_access(g, e)
    case ^Expr_Size_Of:
        ir_type := llvm_type_from_checker(e.resolved_type)
        size := elem_byte_size(ir_type, g.checked)
        return fmt.tprintf("%d", size)
    case ^Expr_Assert:
        // assert(cond): on failure print
        //   Assert failed at <file:line:col>
        //   Expected <cond>, but <operand> was <value> [and <operand> was <value>]
        // and exit. Operand values are reported for direct numeric/bool
        // comparisons; a side that is itself a literal is omitted (its text
        // already states its value), and bools print as true/false. The whole
        // message is a per-site printf format assembled here at compile time —
        // only the values are runtime arguments. Asserts stay on in -release
        // (TigerStyle); only an explicit `-no assert` compiles them out.
        if g.no_assert { return "0" }
        ok_label := fresh_label(g, "assert.ok")
        fail_label := fresh_label(g, "assert.fail")
        loc := format_location(e.span.file, e.span.line, e.span.col)

        // Embedded source text must not smuggle conversion specs into the
        // format string (`a % b == 0`), so escape every %.
        esc_cond, _ := strings.replace_all(e.cond_text, "%", "%%")
        msg: strings.Builder
        strings.builder_init(&msg)
        fmt.sbprintf(&msg, "Assert failed at %s\nExpected %s", loc, esc_cond)

        if bin, is_bin := e.cond.(^Expr_Binary); is_bin && is_comparison_op(bin.op) &&
           e.lhs_text != "" && e.rhs_text != "" {
            _, overloaded := bin.overload_fn.?
            ir_type, is_unsigned := binary_op_type(g, bin, "")
            is_float := ir_type == "double" || ir_type == "float" || ir_type == "half"
            is_bool  := ir_type == "i1"
            // Value reporting covers what printf can carry: bools, scalar ints
            // up to 64 bits, floats. Anything else (ptr, i128, aggregates,
            // overloaded compares) falls through to the plain message.
            is_int := ir_type == "i8" || ir_type == "i16" || ir_type == "i32" || ir_type == "i64"
            if !overloaded && (is_float || is_bool || is_int) {
                left := gen_expr_coerced(g, bin.left, ir_type)
                right := gen_expr_coerced(g, bin.right, ir_type)
                cond_val := fresh_tmp(g)
                pred := ""
                if is_float {
                    #partial switch bin.op {
                    case .Equal_Equal:   pred = "oeq"
                    case .Not_Equal:     pred = "une"
                    case .Less:          pred = "olt"
                    case .Less_Equal:    pred = "ole"
                    case .Greater:       pred = "ogt"
                    case .Greater_Equal: pred = "oge"
                    }
                    emit(g, "  %s = fcmp %s %s %s, %s", cond_val, pred, ir_type, left, right)
                } else {
                    #partial switch bin.op {
                    case .Equal_Equal:   pred = "eq"
                    case .Not_Equal:     pred = "ne"
                    case .Less:          pred = is_unsigned ? "ult" : "slt"
                    case .Less_Equal:    pred = is_unsigned ? "ule" : "sle"
                    case .Greater:       pred = is_unsigned ? "ugt" : "sgt"
                    case .Greater_Equal: pred = is_unsigned ? "uge" : "sge"
                    }
                    emit(g, "  %s = icmp %s %s %s, %s", cond_val, pred, ir_type, left, right)
                }
                emit_cond_br(g, cond_val, ok_label, fail_label)
                emit_label(g, fail_label)
                emit_crash_journal_begin(g)

                Assert_Side :: struct { text, val: string, ex: Expr, report: bool }
                sides := [2]Assert_Side{
                    {e.lhs_text, left,  bin.left,  !assert_side_is_literal(bin.left)},
                    {e.rhs_text, right, bin.right, !assert_side_is_literal(bin.right)},
                }
                spec := is_bool ? "%s" : (is_float ? "%g" : (is_unsigned ? "%llu" : "%lld"))
                args: strings.Builder
                strings.builder_init(&args)
                joiner := ", but "
                for side in sides {
                    if !side.report { continue }
                    esc_side, _ := strings.replace_all(side.text, "%", "%%")
                    // An enum side prints its variant name through the same
                    // inline switch print() uses. That machinery does its own
                    // printf calls, so flush the message built so far and let
                    // it take over mid-sentence.
                    if et, is_enum := enum_type_of(side.ex); is_enum {
                        fmt.sbprintf(&msg, "%s%s was ", joiner, esc_side)
                        joiner = " and "
                        assert_flush_printf(g, &msg, &args)
                        tag_ir := "i64"
                        if et.tag_type != "" { tag_ir = tag_type_to_ir(et.tag_type) }
                        v := side.val
                        if ir_type != tag_ir {
                            w := fresh_tmp(g)
                            op := ir_type_bits(ir_type) > ir_type_bits(tag_ir) ? "trunc" : "zext"
                            emit(g, "  %s = %s %s %s to %s", w, op, ir_type, side.val, tag_ir)
                            v = w
                        }
                        gen_print_enum(g, v, tag_ir, et)
                        continue
                    }
                    // A utf8 side renders as the glyph, same as print() — the
                    // value reads like the literal it's compared to: 'e'.
                    is_char := !is_bool && !is_float && is_char_expr(g, side.ex)
                    fmt.sbprintf(&msg, "%s%s was %s", joiner, esc_side, is_char ? "'%c'" : spec)
                    joiner = " and "
                    if is_bool {
                        t_global, _ := get_string_literal(g, "true")
                        f_global, _ := get_string_literal(g, "false")
                        sel := fresh_tmp(g)
                        emit(g, "  %s = select i1 %s, ptr %s, ptr %s", sel, side.val, t_global, f_global)
                        fmt.sbprintf(&args, ", ptr %s", sel)
                    } else if is_float {
                        v := side.val
                        if ir_type != "double" {
                            w := fresh_tmp(g)
                            emit(g, "  %s = fpext %s %s to double", w, ir_type, side.val)
                            v = w
                        }
                        fmt.sbprintf(&args, ", double %s", v)
                    } else if is_char {
                        // %c reads an i32 vararg (default promotion).
                        v := side.val
                        if ir_type != "i32" {
                            w := fresh_tmp(g)
                            emit(g, "  %s = %s %s %s to i32", w, ir_type == "i64" ? "trunc" : "zext", ir_type, side.val)
                            v = w
                        }
                        fmt.sbprintf(&args, ", i32 %s", v)
                    } else {
                        v := side.val
                        if ir_type != "i64" {
                            w := fresh_tmp(g)
                            emit(g, "  %s = %s %s %s to i64", w, is_unsigned ? "zext" : "sext", ir_type, side.val)
                            v = w
                        }
                        fmt.sbprintf(&args, ", i64 %s", v)
                    }
                }
                strings.write_string(&msg, "\n")
                assert_flush_printf(g, &msg, &args)
                emit_crash_journal_end(g)
                emit(g, "  call void @exit(i32 1)")
                emit(g, "  unreachable")
                emit_label(g, ok_label)
                return "0"
            }
        }

        // General condition (and/or chains, calls, unsupported operand
        // types): no operand breakdown — the condition evaluated false.
        cond_val := gen_expr(g, e.cond)
        emit_cond_br(g, cond_val, ok_label, fail_label)
        emit_label(g, fail_label)
        emit_crash_journal_begin(g)
        strings.write_string(&msg, ", but it was false\n")
        args: strings.Builder
        strings.builder_init(&args)
        assert_flush_printf(g, &msg, &args)
        emit_crash_journal_end(g)
        emit(g, "  call void @exit(i32 1)")
        emit(g, "  unreachable")
        emit_label(g, ok_label)
        return "0"
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
    case ^Expr_Try:
        return gen_try(g, e, target_type)
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
    is_multi := false
    if is_call {
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok {
            is_multi = info.ret_types != nil
        }
    }
    if !is_multi {
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
// The IR type the operands are computed in, plus whether the op is unsigned.
// For arithmetic/bitwise this is the checker's promoted result (e.type_ — the
// value-preserving common type). For a comparison (whose result is bool) it's
// the common type of the two operands. Operands are coerced to this width
// before the op; a cross-sign mix lands on a SIGNED common type, so the op runs
// signed even though one operand was unsigned (-1 stays -1, not a huge u-value).
binary_op_type :: proc(g: ^Codegen, e: ^Expr_Binary, target_type: string) -> (ir: string, unsigned: bool) {
    is_comparison := false
    #partial switch e.op {
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
        is_comparison = true
    }
    work: Type
    if !is_comparison && e.type_ != nil && !is_infer(e.type_) && !is_any(e.type_) {
        work = e.type_
    } else {
        l_infer := is_infer_expr(g, e.left)
        r_infer := is_infer_expr(g, e.right)
        lt := distinct_base(expr_type(e.left))
        rt := distinct_base(expr_type(e.right))
        if !l_infer && !r_infer {
            if c, ok := common_numeric_type(lt, rt); ok {
                work = c
            } else {
                work = lt
            }
        } else if !l_infer {
            work = lt
        } else if !r_infer {
            work = rt
        }
    }
    if work == nil || is_infer(work) || is_any(work) {
        // all-infer (no concrete side, no resolved hint): honor target, else default.
        if target_type != "" && !is_comparison { return target_type, false }
        return expr_ir_type(g, e.left), false
    }
    ir = llvm_type_from_checker(work)
    #partial switch n in distinct_base(work) {
    case Type_Numeric:                   unsigned = n.kind == .Unsigned
    case Type_Byte, Type_Utf8:  unsigned = true
    }
    return
}

// A comparison side whose source text already states its value — a number,
// bool, or char literal (incl. a negated number), or an enum/union variant
// reference (.Paused, State.Paused) — is omitted from the assert failure
// report: `game.running == false` reports only game.running. Named constants
// are NOT literals: their text doesn't show their value, so they report.
assert_side_is_literal :: proc(ex: Expr) -> bool {
    #partial switch v in ex {
    case ^Expr_Number: return true
    case ^Expr_Bool:   return true
    case ^Expr_Char:   return true
    case ^Expr_Unary:
        if v.op == .Minus {
            if _, is_num := v.operand.(^Expr_Number); is_num { return true }
        }
    case ^Expr_Ident:
        #partial switch _ in v.resolved {
        case Resolved_Enum_Variant, Resolved_Union_Variant: return true
        }
    case ^Expr_Field_Access:
        #partial switch _ in v.resolved {
        case Resolved_Enum_Variant, Resolved_Union_Variant: return true
        }
    }
    return false
}

// Emit the pending assert-message segment as one printf and reset the
// builders. Segmented because enum sides print through gen_print_enum's
// inline switch, which does its own printf calls mid-message.
assert_flush_printf :: proc(g: ^Codegen, msg: ^strings.Builder, args: ^strings.Builder) {
    if strings.builder_len(msg^) == 0 { return }
    msg_global, _ := get_string_literal(g, strings.to_string(msg^))
    emit(g, "  call i32 (ptr, ...) %s(ptr %s%s)", printf_sym(g), msg_global, strings.to_string(args^))
    strings.builder_reset(msg)
    strings.builder_reset(args)
}

// Open/close a crash.txt journal entry around a fail block's message
// emission (native builds only; web has no filesystem). Between the two,
// g.tee routes every print-shaped emission through __mara_tee_printf so the
// message lands in the journal as well as on stdout.
emit_crash_journal_begin :: proc(g: ^Codegen) {
    if g.web { return }
    emit(g, "  call void @__mara_crash_begin()")
    g.tee = true
}

emit_crash_journal_end :: proc(g: ^Codegen) {
    if g.web { return }
    g.tee = false
    emit(g, "  call void @__mara_crash_end()")
}

gen_binary :: proc(g: ^Codegen, e: ^Expr_Binary, target_type: string = "") -> string {
    // Overloaded operator: delegate to function call
    if rf, rf_ok := e.overload_fn.?; rf_ok {
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
    ir_type, is_unsigned := binary_op_type(g, e, target_type)

    // Coerce each operand to the working type — value-preserving widening makes
    // a narrower operand match (sext/zext by its own signedness, fpext); for
    // same-type operands this is a no-op.
    left := gen_expr_coerced(g, e.left, ir_type)
    right := gen_expr_coerced(g, e.right, ir_type)
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
        // is_unsigned is the working type's signedness (from binary_op_type):
        // a cross-sign mix lands on a signed common type, so the op is signed
        // even though one operand was unsigned.
        #partial switch e.op {
        case .Plus:
            if e.wrapping {
                emit(g, "  %s = add %s %s, %s", tmp, ir_type, left, right)
            } else {
                tmp = emit_checked_arith(g, is_unsigned ? "uadd" : "sadd", ir_type, left, right, e.span)
            }
        case .Minus:
            if e.wrapping {
                emit(g, "  %s = sub %s %s, %s", tmp, ir_type, left, right)
            } else {
                tmp = emit_checked_arith(g, is_unsigned ? "usub" : "ssub", ir_type, left, right, e.span)
            }
        case .Star:
            if e.wrapping {
                emit(g, "  %s = mul %s %s, %s", tmp, ir_type, left, right)
            } else {
                tmp = emit_checked_arith(g, is_unsigned ? "umul" : "smul", ir_type, left, right, e.span)
            }
        case .Slash:
            emit_div_zero_check(g, right, ir_type, e.span)
            emit(g, "  %s = %s %s %s, %s", tmp, is_unsigned ? "udiv" : "sdiv", ir_type, left, right)
        case .Modulo:
            emit_div_zero_check(g, right, ir_type, e.span)
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
    case "i8", "utf8": return "i8", false, false, true
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

// Narrow or widen an integer SSA value from `src_type` to `target` (sext for
// signed widen — the conventional default; trunc for narrow). No-op when
// widths match. Caller is responsible for src_type accurately describing the
// SSA value's actual IR type.
coerce_int_to_ir :: proc(g: ^Codegen, val: string, src_type: string, target: string) -> string {
    if src_type == target { return val }
    src_bits := ir_type_bits(src_type)
    tgt_bits := ir_type_bits(target)
    if src_bits == 0 || tgt_bits == 0 || src_bits == tgt_bits { return val }
    tmp := fresh_tmp(g)
    if src_bits < tgt_bits {
        emit(g, "  %s = sext %s %s to %s", tmp, src_type, val, target)
    } else {
        emit(g, "  %s = trunc %s %s to %s", tmp, src_type, val, target)
    }
    return tmp
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
        // Conversion preserves the SOURCE value, so signedness comes from the
        // source, same rule as int→int widening below: an unsigned source is
        // non-negative and must uitofp — f32(some_byte) holding 200 is 200.0,
        // not -56.0. bool/byte/char are unsigned.
        src_unsigned := src_type == "i1"
        #partial switch t in distinct_base(expr_type(e.args[0])) {
        case Type_Numeric:
            src_unsigned = t.kind == .Unsigned
        case Type_Byte, Type_Utf8, Type_Bool:
            src_unsigned = true
        }
        if src_unsigned {
            emit(g, "  %s = uitofp %s %s to %s", tmp, src_type, val, target)
        } else {
            emit(g, "  %s = sitofp %s %s to %s", tmp, src_type, val, target)
        }
        return tmp, true
    }

    // int → int (or bool)
    src_bits := ir_type_bits(src_type)
    tgt_bits := ir_type_bits(target)
    if src_bits == tgt_bits {
        // Same width, just return the value (e.g. i32 signed vs unsigned)
        return val, true
    } else if src_bits < tgt_bits {
        // Widening preserves the SOURCE value, so the extension is chosen by
        // the source's signedness, not the target's: an unsigned source is
        // non-negative and must zero-extend even into a signed target
        // (`i32(some_u16)` must NOT sign-extend). bool/byte/char are unsigned.
        src_unsigned := src_type == "i1"
        #partial switch t in distinct_base(expr_type(e.args[0])) {
        case Type_Numeric:
            src_unsigned = t.kind == .Unsigned
        case Type_Byte, Type_Utf8, Type_Bool:
            src_unsigned = true
        }
        if src_unsigned {
            emit(g, "  %s = zext %s %s to %s", tmp, src_type, val, target)
        } else {
            emit(g, "  %s = sext %s %s to %s", tmp, src_type, val, target)
        }
    } else {
        emit(g, "  %s = trunc %s %s to %s", tmp, src_type, val, target)
    }
    return tmp, true
}

// Generate `e` for a known target IR type, widening the result when it's a
// narrower numeric. The type checker only allows value-preserving widens at the
// sites that call this (variable init, argument, return, field init), so this
// just performs the already-approved conversion — sign/zero-extend by the
// SOURCE's signedness for ints, fpext for f32 → f64. Literals/infer were already
// emitted at the target width by gen_expr, so they pass through untouched.
gen_expr_coerced :: proc(g: ^Codegen, e: Expr, target_ir: string) -> string {
    val := gen_expr(g, e, target_ir)
    if target_ir == "" { return val }
    // No concrete source type to widen from: nil (the checker didn't stamp a
    // .type_ — e.g. a constant operand in the synthesized Program/Arena
    // construction path), infer (a literal), or any. gen_expr already emitted
    // the value at target_ir, so coercion is a no-op — pass through, exactly as
    // the infer/any cases always did. (nil formerly lowered to i64 here; with
    // the nil panic in llvm_type_from_checker this guard is what keeps it out.)
    src_t := expr_type(e)
    if src_t == nil || is_infer(src_t) || is_any(src_t) { return val }
    src_ir := llvm_type_from_checker(src_t)
    if src_ir == target_ir { return val }
    if src_ir == "float" && target_ir == "double" {
        t := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", t, val)
        return t
    }
    sb := ir_type_bits(src_ir)
    tb := ir_type_bits(target_ir)
    if sb > 0 && tb > sb {
        unsigned := false
        #partial switch v in distinct_base(src_t) {
        case Type_Numeric:                              unsigned = v.kind == .Unsigned
        case Type_Byte, Type_Utf8, Type_Bool:  unsigned = true
        }
        t := fresh_tmp(g)
        op := unsigned ? "zext" : "sext"
        emit(g, "  %s = %s %s %s to %s", t, op, src_ir, val, target_ir)
        return t
    }
    return val
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
    // Constant ident: inline the value expression and let the shape-aware
    // paths below (string-literal, array-literal, ...) fire on the
    // underlying value. Covers `TAG :: "x"` then `f(TAG)` where f takes a
    // slice — without this, the Expr_String case never matches the ident.
    if ident, id_ok := arg.(^Expr_Ident); id_ok {
        if const_expr, ck := g.checked.table.constants[ident.name]; ck {
            return gen_slice_value_ptr(g, const_expr)
        }
    }
    arg_checker_type := expr_type(arg)
    // String literal: typed as a partial array since the
    // literal-type change, but it still lives as raw bytes in rodata.
    // Synthesize a slice header pointing at the global — len = N, cap =
    // N+1 — and pass `&header`. The cap includes the rodata global's
    // trailing \0 slot (those bytes exist), so a literal flowing through
    // `[]utf8` params into cstring() passes the terminator check at [len].
    // Receivers can't write through it: by-value params are immutable and
    // the literal storage bans cover the rest.
    if lit, lit_ok := arg.(^Expr_String); lit_ok {
        global, _ := get_string_literal(g, lit.value)
        data_ptr := fresh_tmp(g)
        emit_string_gep(g, data_ptr, len(lit.value)+1, global)
        size_str := fmt.tprintf("%d", len(lit.value))
        cap_str := fmt.tprintf("%d", len(lit.value)+1)
        return emit_build_temp_slice(g, data_ptr, size_str, cap_str)
    }
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
        len_val := fmt.tprintf("%d", fa.size)
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
        val := gen_expr_coerced(g, arg, pt)
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

// Lower one argument of a Mara-convention call to its single "type val" IR
// operand string. Shared by gen_call_inner, gen_call_into_struct, and
// gen_call_into_array so the per-arg lowering rules can't drift between the
// scalar-return, struct-return (NRVO), and array-return (NRVO) paths — they
// already diverged twice (the SLICE_IR_TYPE and byte-buffer materialization
// branches were each missing from a subset). Every branch produces exactly one
// arg string, so a single return value suffices.
gen_mara_call_arg :: proc(g: ^Codegen, arg: Expr, i: int, info: ^Fun_Info, cs_resolved: ^Checked_Scope, has_cs: bool) -> string {
    if i < len(info.param_structs) && info.param_structs[i] != "" {
        // Struct arg: pass as ptr (no target_type needed)
        val := gen_expr(g, arg)
        return fmt.tprintf("ptr %s", val)
    }

    pt := "i64"
    if i < len(info.param_types) {
        pt = info.param_types[i]
    }
    // Slice / partial-array param: pass a pointer to the header (the
    // fat-pointer-ref ABI). Without this a cstr/partial-array arg (e.g. a
    // string literal to a `cstr` param) is emitted as `{i64,i64,ptr} %val`
    // while the callee declares the param `ptr` — an IR mismatch clang rejects.
    if pt == SLICE_IR_TYPE {
        return gen_slice_param_arg(g, arg)
    }
    // Byte-buffer source → fixed-array param: reinterpret-read sizeof(pt) bytes
    // from `buf[offset:]` / `buf[offset]` into a freshly-allocated `[N x T]` and
    // load it. Mirrors the same pattern that fires at declaration sites
    // (`arr : [N]T = buf[off]`). gen_expr would produce a slice header for
    // `bytes[lo:hi]` — the wrong shape — so we short-circuit before calling it.
    if strings.has_prefix(pt, "[") {
        materialized := ""
        param_ty: Type
        if has_cs && i < len(cs_resolved.params) { param_ty = cs_resolved.params[i].type_ }
        if sl_expr, sl_ok := arg.(^Expr_Slice); sl_ok && codegen_is_byte_buffer_source(g, sl_expr.expr) {
            materialized = emit_array_from_byte_buffer(g, sl_expr.expr, sl_expr.low, pt, sl_expr.span, param_ty, sl_expr.is_big_endian)
        } else if idx_expr, idx_ok := arg.(^Expr_Index); idx_ok && codegen_is_byte_buffer_source(g, idx_expr.expr) {
            materialized = emit_array_from_byte_buffer(g, idx_expr.expr, idx_expr.index, pt, idx_expr.span, param_ty, idx_expr.is_big_endian)
        }
        if materialized != "" {
            return fmt.tprintf("%s %s", pt, materialized)
        }
    }
    val := gen_expr_coerced(g, arg, pt)
    if strings.has_prefix(pt, "[") {
        val = gen_array_param_arg(g, arg, pt, val)
    }
    return fmt.tprintf("%s %s", pt, val)
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

    // Built-in: len(arr) — capacity for fixed arrays (no separate len), runtime
    // len for slices and partial arrays. Array class len() is desugared to a
    // buf.len field access by the type checker, so it doesn't land here.
    if e.name == "len" && len(e.args) == 1 {
        if h, ok := resolve_array_handle(g, e.args[0]); ok {
            return emit_array_len(g, &h)
        }
    }

    // Built-in: cap(arr) — user-facing capacity.
    // Array class cap() likewise gets desugared upstream.
    if e.name == "cap" && len(e.args) == 1 {
        if h, ok := resolve_array_handle(g, e.args[0]); ok {
            return emit_array_cap_user(g, &h)
        }
    }

    // Built-in: cstring(s) — checked, zero-copy conversion. The contract is
    // VALIDITY, not content: a 0 must exist inside the slice's storage so C
    // can never run past it (what C reads up to the 0 is the user's data,
    // the user's business). Positional check: len < cap → the byte at [len]
    // must be 0 (exact-content case — literal views, append-built strings);
    // len == cap → the LAST byte [cap-1] must be 0 (full view of a
    // zero-padded buffer; C stops at the first interior 0). Both reads stay
    // inside the slice's capacity. No terminator → loud crash with the
    // location. No copies, no allocation, no arena.
    // Literal arg: free pointer to the deduped rodata global (trailing \0).
    if e.name == "cstring" && len(e.args) == 1 {
        if lit, lit_ok := e.args[0].(^Expr_String); lit_ok {
            global, _ := get_string_literal(g, lit.value)
            out := fresh_tmp(g)
            emit_string_gep(g, out, len(lit.value)+1, global)
            return out
        }
        w := slice_layout.len_ir
        len_val, cap_val, src_ptr: string
        if h, h_ok := resolve_array_handle(g, e.args[0]); h_ok {
            len_val = emit_array_len(g, &h)
            cap_val = emit_array_raw_cap(g, &h)
            src_ptr = emit_array_data(g, &h)
        } else {
            // General expression (sub-slice, call result): gen_expr yields a
            // pointer to a {len, cap, ptr} header.
            hdr := gen_expr(g, e.args[0])
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, hdr, SLICE.len)
            len_val = fresh_tmp(g)
            emit_typed_load_len(g, len_val, len_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, hdr, SLICE.cap)
            cap_val = fresh_tmp(g)
            emit_typed_load_cap(g, cap_val, cap_gep)
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, hdr, SLICE.ptr)
            src_ptr = fresh_tmp(g)
            emit_load_into(g, src_ptr, "ptr", data_gep)
        }
        at_len_lbl  := fresh_label(g, "cstring.at_len")
        at_end_lbl  := fresh_label(g, "cstring.at_end")
        end_ok_lbl  := fresh_label(g, "cstring.end_ok")
        pass_lbl    := fresh_label(g, "cstring.pass")
        crash_lbl   := fresh_label(g, "cstring.fail")
        has_room := fresh_tmp(g)
        emit(g, "  %s = icmp slt %s %s, %s", has_room, w, len_val, cap_val)
        emit_cond_br(g, has_room, at_len_lbl, at_end_lbl)
        // len < cap: terminator sits right after the content.
        emit_label(g, at_len_lbl)
        p1 := fresh_tmp(g)
        emit(g, "  %s = getelementptr i8, ptr %s, %s %s", p1, src_ptr, w, len_val)
        b1 := fresh_tmp(g)
        emit_load_into(g, b1, "i8", p1)
        ok1 := fresh_tmp(g)
        emit(g, "  %s = icmp eq i8 %s, 0", ok1, b1)
        emit_cond_br(g, ok1, pass_lbl, crash_lbl)
        // len == cap: full view — the last byte must be 0 (and cap > 0 so
        // the [cap-1] read stays inside the storage).
        emit_label(g, at_end_lbl)
        cap_pos := fresh_tmp(g)
        emit(g, "  %s = icmp sgt %s %s, 0", cap_pos, w, cap_val)
        emit_cond_br(g, cap_pos, end_ok_lbl, crash_lbl)
        emit_label(g, end_ok_lbl)
        last := fresh_tmp(g)
        emit(g, "  %s = sub %s %s, 1", last, w, cap_val)
        p2 := fresh_tmp(g)
        emit(g, "  %s = getelementptr i8, ptr %s, %s %s", p2, src_ptr, w, last)
        b2 := fresh_tmp(g)
        emit_load_into(g, b2, "i8", p2)
        ok2 := fresh_tmp(g)
        emit(g, "  %s = icmp eq i8 %s, 0", ok2, b2)
        emit_cond_br(g, ok2, pass_lbl, crash_lbl)
        emit_label(g, crash_lbl)
        loc := format_location(e.span.file, e.span.line, e.span.col)
        err_msg := fmt.tprintf("runtime error: cstring() at %s: no terminating 0 in the slice (checked [len] since len < cap, or [cap-1] for a full slice) — append into headroom or zero-pad the buffer\n", loc)
        err_name, err_len := get_string_literal(g, err_msg)
        err_ptr := fresh_tmp(g)
        emit_string_gep(g, err_ptr, err_len, err_name)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
        emit(g, "  call void @exit(i32 1)")
        emit(g, "  unreachable")
        emit_label(g, pass_lbl)
        return src_ptr
    }

    // Built-in: slice_from_ptr(ptr, cap) -> []byte — wraps a raw pointer + capacity into a byte slice.
    // Type checker enforces cap's width matches slice_layout.cap_ir; codegen
    // does not narrow/widen — pass straight through.
    if e.name == "slice_from_ptr" && len(e.args) == 2 {
        ptr_val := gen_expr(g, e.args[0])
        cap_val := gen_expr(g, e.args[1], slice_layout.cap_ir)
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
        // Pull the resolved Checked_Scope for param checker types — needed for
        // shape-sensitive conversions (cstr → cstring, etc.) that the IR type
        // string alone can't disambiguate.
        cs_resolved: Checked_Scope
        has_cs := false
        if cs_val, cs_ok := g.checked.functions[lookup_name]; cs_ok {
            cs_resolved = cs_val
            has_cs = true
        }
        for arg, i in e.args {
            append(&arg_strs, gen_mara_call_arg(g, arg, i, &info, &cs_resolved, has_cs))
        }

        if info.ret_struct != "" {
            // Struct return: alloca a temp, pass as sret, call void.
            tmp_struct := fresh_tmp(g)
            emit_alloca(g, tmp_struct, struct_llvm_name(info.ret_struct))
            append(&arg_strs, fmt.tprintf("ptr %s", tmp_struct))
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
        } else if info.ret_partial_cap > 0 {
            // Partial-array return: alloca the full {len,cap,ptr,[N]} temp, pass
            // as sret, call void. The callee builds into it (stamps the header,
            // or copies a value in), so the caller just provides raw storage.
            // Big ones arena-bump like the array path.
            ir := partial_array_ir_type(info.ret_partial_elem, info.ret_partial_cap)
            total_bytes := info.ret_partial_cap * elem_byte_size(info.ret_partial_elem) + slice_header_bytes
            tmp: string
            if g.context_enabled && total_bytes >= 1024 {
                ret_name := fmt.tprintf("<ret %s>", call_resolved_name(e))
                ret_loc := format_location(e.span.file, e.span.line, e.span.col)
                tmp = emit_arena_bump(g, total_bytes, ret_name, ret_loc)
            } else {
                tmp = fresh_tmp(g)
                emit_alloca(g, tmp, ir)
            }
            append(&arg_strs, fmt.tprintf("ptr %s", tmp))
            args_joined := strings.join(arg_strs[:], ", ")
            emit(g, "  call void %s(%s)", ir_name, args_joined)
            return tmp
        } else if info.ret_types != nil {
            // Multi-return: temp pointer per element, pass as sret, call void.
            // Big slots (e.g. a multi-MB array riding in a tuple) follow the
            // same arena policy as the single-array-return path above — a
            // plain alloca per slot overflows the stack.
            clear(&g.tuple_result_ptrs)
            clear(&g.tuple_result_types)
            for elem, i in info.ret_types {
                et := llvm_type_from_checker(elem)
                tmp_ptr: string
                total_bytes := checker_type_byte_size(elem)
                if g.context_enabled && total_bytes >= 1024 {
                    ret_name := fmt.tprintf("<ret %s.%d>", call_resolved_name(e), i)
                    ret_loc := format_location(e.span.file, e.span.line, e.span.col)
                    tmp_ptr = emit_arena_bump(g, total_bytes, ret_name, ret_loc)
                } else {
                    tmp_ptr = fresh_tmp(g)
                    emit_alloca(g, tmp_ptr, et)
                }
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
            return tmp
        }
    }

    // Indirect call: callee is a function pointer held in a variable — either
    // an alloca-backed scalar (load the ptr) or an SSA-direct binding (use it
    // as-is). A fn-typed parameter (`cb: fn foo`) takes the SSA path: params
    // bind straight to their `ptr` arg value, so there's no alloca to load.
    fn_ptr := ""
    callee_is_fnptr := false
    if alloca, alloca_ok := get_scalar(g, lookup_name); alloca_ok {
        callee_is_fnptr = true
        fn_ptr = fresh_tmp(g)
        emit_load_into(g, fn_ptr, "ptr", alloca)
    } else if entry, entry_ok := g.all_vars[lookup_name]; entry_ok {
        if sv, sv_ok := entry.(SSA_Var); sv_ok && sv.ir_type == "ptr" {
            callee_is_fnptr = true
            fn_ptr = sv.ssa
        }
    }
    if callee_is_fnptr {
        // Build typed arg list from each arg's checker type
        arg_strs: [dynamic]string
        for arg in e.args {
            at := expr_type(arg)
            pt := "i64"
            if at != nil && !is_untyped(at) {
                pt = llvm_type_from_checker(at)
            }
            val := gen_expr_coerced(g, arg, pt)
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
    // C ABI has no multi-return; cs.return_types has 0 or 1 elements for foreign funs.
    ret_single: Type
    has_void_return := len(cs.return_types) == 0
    if !has_void_return { ret_single = cs.return_types[0] }
    if !has_void_return && is_untyped(ret_single) { has_void_return = true }
    ret_low: Lowering
    ret_ir := "void"
    sret_slot := ""
    if !has_void_return {
        ret_low = classify_ret(ret_single, conv, os)
        switch r in ret_low {
        case Lowering_Direct:
            ret_ir = direct_ir_for_return(r.parts[:])
        case Lowering_Indirect:
            ret_struct_ir := llvm_type_from_checker(ret_single)
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
        if is_aggregate(ret_single) {
            ret_struct_ir := llvm_type_from_checker(ret_single)
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

// `?` postfix propagation. Evaluate the inner call; if its trailing err
// slot is non-zero, fill the enclosing function's trailing err return with
// it (zero-initialize any other return slots) and return early. Otherwise
// yield the call's non-err value (or void for err-only calls). The type
// checker (check_try) already validated both the call shape and the
// enclosing function's return shape, so codegen treats them as given.
gen_try :: proc(g: ^Codegen, e: ^Expr_Try, target_type: string) -> string {
    call := e.inner.(^Expr_Call)
    call_result := gen_call(g, call)

    // Determine the err value and the optional success value.
    err_val: string
    success_val := ""
    multi := len(g.tuple_result_ptrs) > 0
    if multi {
        n := len(g.tuple_result_ptrs)
        err_slot := g.tuple_result_ptrs[n-1]
        err_val = fresh_tmp(g)
        emit_load_into(g, err_val, "i32", err_slot)
        if n == 2 {
            val_ir := g.tuple_result_types[0]
            // Aggregates (struct `%...`, array `[...]`, slice `{...}`) come back
            // by pointer — the binding memcpy's from the sret slot. Returning a
            // loaded aggregate *value* would hand a struct/array value to a copy
            // that expects a pointer (invalid IR). Scalars load into an SSA value.
            if len(val_ir) > 0 && (val_ir[0] == '%' || val_ir[0] == '[' || val_ir[0] == '{') {
                success_val = g.tuple_result_ptrs[0]
            } else {
                tmp := fresh_tmp(g)
                emit_load_into(g, tmp, val_ir, g.tuple_result_ptrs[0])
                success_val = tmp
            }
        }
    } else {
        // Single-return call: result IS the err.
        err_val = call_result
    }

    // Snapshot tuple state — the propagation block emits stores into %sret,
    // and any subsequent gen_expr below should see a clean slate.
    clear(&g.tuple_result_ptrs)
    clear(&g.tuple_result_types)

    prop_lbl := fresh_label(g, "try.propagate")
    cont_lbl := fresh_label(g, "try.continue")
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ne i32 %s, 0", cmp, err_val)
    emit_cond_br(g, cmp, prop_lbl, cont_lbl)

    emit_label(g, prop_lbl)
    if g.ret_types != nil {
        // Multi-return enclosing function: zero the non-err slots, write err
        // into the trailing slot, ret void. zeroinitializer is the universal
        // "default value" — works for primitives, structs, arrays, slices,
        // ptrs alike, so we don't have to fan out by type.
        n_ret := len(g.ret_types)
        for i in 0..<n_ret - 1 {
            ir_t := llvm_type_from_checker(g.ret_types[i])
            emit(g, "  store %s zeroinitializer, ptr %%sret.%d", ir_t, i)
        }
        emit(g, "  store i32 %s, ptr %%sret.%d", err_val, n_ret - 1)
        emit(g, "  ret void")
    } else {
        // Single-return err function — just return the err value.
        emit(g, "  ret i32 %s", err_val)
    }

    emit_label(g, cont_lbl)
    return success_val
}

// (Terminate-in-place cstring conversion used to live here. It's gone: the
// explicit `cstring(s)` builtin copies into a fresh buffer instead, and the
// checker rejects implicit runtime-string → cstring arguments, so codegen
// never converts implicitly. Literals reach cstring params as raw rodata
// pointers via gen_expr's Expr_String handling.)

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
    // Type checker enforces arg matches declared param type — pass the target
    // through gen_expr's hint so infer literals produce the right width.
    val := gen_expr(g, arg_expr, pt)
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

    cs_resolved: Checked_Scope
    has_cs := false
    if cs_val, cs_ok := g.checked.functions[cn]; cs_ok {
        cs_resolved = cs_val
        has_cs = true
    }
    arg_strs: [dynamic]string
    for arg, i in e.args {
        append(&arg_strs, gen_mara_call_arg(g, arg, i, info, &cs_resolved, has_cs))
    }

    append(&arg_strs, fmt.tprintf("ptr %s", dest_ptr))
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

    cs_resolved: Checked_Scope
    has_cs := false
    if cs_val, cs_ok := g.checked.functions[cn]; cs_ok {
        cs_resolved = cs_val
        has_cs = true
    }
    // Build normal arguments
    arg_strs: [dynamic]string
    for arg, i in e.args {
        append(&arg_strs, gen_mara_call_arg(g, arg, i, info, &cs_resolved, has_cs))
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
    // Evaluate the message BEFORE the journal opens — the argument is
    // ordinary user code and must not have its own prints teed.
    val := ""
    arg_type: Type
    if len(e.args) == 1 {
        val = gen_expr(g, e.args[0])
        arg_type = expr_type(e.args[0])
    }

    emit_crash_journal_begin(g)

    // Location line, same family as the assert message.
    loc := format_location(e.span.file, e.span.line, e.span.col)
    esc_loc, _ := strings.replace_all(loc, "%", "%%")
    loc_global, _ := get_string_literal(g, strings.concatenate({"Crashed at ", esc_loc, "\n"}))
    emit(g, "  call i32 (ptr, ...) %s(ptr %s)", printf_sym(g), loc_global)

    if len(e.args) == 1 {
        // Print the message (string literal or runtime string)
        if fa, ok := arg_type.(^Type_Fixed_Array); ok {
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

    emit_crash_journal_end(g)
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
        emit_print_arg(g, arg_expr, e.span)
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
    is_format_marker :: proc(c: u8) -> bool {
        // Letter chars after `%` are human-readable shorthand (`%d`, `%s`,
        // `%g`, `%v`, `%x`, ...). Mara picks the actual printf spec from
        // the arg's type, but the marker letter is consumed so it doesn't
        // appear in output. Non-letter chars (spaces, commas, punctuation,
        // digits) are bare-`%` placeholders followed by literal text.
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
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
            emit_print_arg(g, args[arg_idx], call_span)
            arg_idx += 1
            // Advance past `%`. If a letter follows, treat it as a human-
            // readable type marker and consume it too (`%d` → emit value,
            // skip both). If anything else follows (space, comma, '0',
            // etc.), the user meant a bare placeholder and we leave that
            // char alone — it's part of the surrounding literal text.
            if i+1 < len(fmt_str) && is_format_marker(fmt_str[i+1]) {
                i += 2
            } else {
                i += 1
            }
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
emit_print_arg :: proc(g: ^Codegen, arg_expr: Expr, call_span: Span) {
        // utf8 array shape (fixed array, slice, partial array, or string
        // literal) — print via %.*s bounded by len. Resolves the expression
        // to a unified Array_Handle once, then dispatches through the
        // shared printer instead of branching by source-noun. Replaces four
        // near-identical hand-rolled branches that drifted out of sync.
        if is_utf8_array_expr(g, arg_expr) {
            if h, ok := resolve_array_handle(g, arg_expr); ok && h.is_utf8 {
                emit_array_print(g, &h)
            }
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
        } else if is_indexed_struct_expr(g, arg_expr) {
            // Indexed struct element (`arr[i]` where arr's elements are
            // structs). Without this, the fallback path treats the GEP'd
            // pointer as i64 and emits a printf type mismatch. Compute the
            // element address and route through gen_print_struct with a
            // synthetic Struct_Var anchored at that address.
            idx_expr := arg_expr.(^Expr_Index)
            sd := as_struct_body(expr_type(arg_expr))
            if print_st, ps_ok := lookup_struct(g, sd.name); ps_ok {
                elem_ptr := gen_index_address(g, idx_expr)
                stv := Struct_Var{alloca = elem_ptr, struct_name = sd.name}
                gen_print_struct(g, &stv, print_st)
            }
        } else if is_char_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            // utf8 / char literal prints as a character using %c
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
            // Print-as-string for any pointer-to-utf8 / pointer-to-byte
            // shape, unwrapping distinct types so user wrappers (like the
            // stdlib's `cstring :: distinct ^utf8`) inherit the rule
            // structurally. Codegen sees only the IR shape; the distinct
            // identity is the type checker's concern.
            base := distinct_base(t)
            if pt, ok := base.(^Type_Ptr); ok {
                if _, is_byte := pt.elem.(Type_Byte); is_byte { spec = "%s" }
                if _, is_utf8 := pt.elem.(Type_Utf8); is_utf8 { spec = "%s" }
            }
            if _, is_cs := t.(Type_CString); is_cs { spec = "%s" }
            fmt_name, fmt_len := get_string_literal(g, spec)
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_ptr(g, fmt_ptr, val)
        } else if _, is_err := expr_type(arg_expr).(Type_Err); is_err {
            // Open `err` value: route through the program-wide runtime
            // helper since the specific error_kind isn't known statically.
            val := gen_expr(g, arg_expr, "i32")
            emit(g, "  call void @__mara_print_err(i32 %s)", val)
        } else if et, is_enum := enum_type_of(arg_expr); is_enum {
            // Enum value: print the variant name via an inline switch. Falls
            // back to "EnumName(<tag>)" for unknown tags (out-of-range or
            // bitwise-OR'd flag combos). Caught before is_numeric_expr so
            // raw enums don't render as plain integers.
            tag_ir := "i64"
            if et.tag_type != "" { tag_ir = tag_type_to_ir(et.tag_type) }
            val := gen_expr(g, arg_expr, tag_ir)
            gen_print_enum(g, val, tag_ir, et)
        } else if _, is_bool := expr_type(arg_expr).(Type_Bool); is_bool {
            // bool prints as true/false (see gen_print_bool). Without an
            // explicit case it falls to the final %lld branch, which passes an
            // i1 where printf's i64 vararg is expected — invalid IR.
            gen_print_bool(g, gen_expr(g, arg_expr, "i1"))
        } else if is_numeric_expr(g, arg_expr) {
            val := gen_expr(g, arg_expr)
            nt := get_numeric_type(g, arg_expr)
            // Format spec matches the value's natural IR width — no
            // sext/zext to a "convention" width. Mimics C varargs:
            // printf reads whichever width the spec says.
            is_unsigned := false
            ft := distinct_base(expr_type(arg_expr))
            if n, n_ok := ft.(Type_Numeric); n_ok {
                is_unsigned = n.kind == .Unsigned
            }
            if _, b_ok := ft.(Type_Byte); b_ok {
                // byte is a raw octet — always renders unsigned (0..255).
                is_unsigned = true
            }
            switch nt {
            case "float":
                // f32 → double for printf varargs (C ABI requires default-
                // promotion for variadic float args). Not an implicit type
                // conversion in user code — a calling-convention adapter.
                ext := fresh_tmp(g)
                emit(g, "  %s = fpext float %s to double", ext, val)
                fmt_name, fmt_len := get_string_literal(g, "%g")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_double(g, fmt_ptr, ext)
            case "half":
                // f16 → double for printf varargs, same default-promotion as
                // f32. The half→double widen is fpext; the integer `case:`
                // default below would emit `sext half` — an integer op on a
                // float, which is invalid IR.
                ext := fresh_tmp(g)
                emit(g, "  %s = fpext half %s to double", ext, val)
                fmt_name, fmt_len := get_string_literal(g, "%g")
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_double(g, fmt_ptr, ext)
            case "i64":
                spec := is_unsigned ? "%llu" : "%lld"
                fmt_name, fmt_len := get_string_literal(g, spec)
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit_printf_i64(g, fmt_ptr, val)
            case "i32":
                spec := is_unsigned ? "%u" : "%d"
                fmt_name, fmt_len := get_string_literal(g, spec)
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, val)
            case:
                // i8 / i16: still extend to i32 for printf's default-int
                // varargs promotion (C calling convention; not an implicit
                // user-code conversion).
                ext := fresh_tmp(g)
                if is_unsigned {
                    emit(g, "  %s = zext %s %s to i32", ext, nt, val)
                } else {
                    emit(g, "  %s = sext %s %s to i32", ext, nt, val)
                }
                spec := is_unsigned ? "%u" : "%d"
                fmt_name, fmt_len := get_string_literal(g, spec)
                fmt_ptr := fresh_tmp(g)
                emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
                emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, ext)
            }
        } else {
            // No print rule matched. The fallback passes the raw value in
            // printf's i64 vararg slot, so anything that isn't i64-shaped
            // would emit invalid IR clang rejects with a cryptic type
            // mismatch — hard error here instead, naming the Mara type.
            if it := expr_ir_type(g, arg_expr); it != "i64" {
                codegen_fatal(g, call_span, CODE_PRINT_UNSUPPORTED_VALUE, type_name(expr_type(arg_expr)))
            }
            val := gen_expr(g, arg_expr)
            fmt_name, fmt_len := get_string_literal(g, "%lld")
            fmt_ptr := fresh_tmp(g)
            emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
            emit_printf_i64(g, fmt_ptr, val)
        }
}

// Print an i1 as `true`/`false`. Shared by scalar args, struct fields, and
// array elements so bool renders consistently everywhere — and never reaches
// an integer printf format, which would either mistype the i1 (scalar: i1 in
// an i64 vararg slot → invalid IR) or sext it to a garbage value (array: true
// → -1).
gen_print_bool :: proc(g: ^Codegen, val_i1: string) {
    true_name, true_len := get_string_literal(g, "true")
    false_name, false_len := get_string_literal(g, "false")
    true_ptr := fresh_tmp(g)
    emit_string_gep(g, true_ptr, true_len, true_name)
    false_ptr := fresh_tmp(g)
    emit_string_gep(g, false_ptr, false_len, false_name)
    bool_str := fresh_tmp(g)
    emit(g, "  %s = select i1 %s, ptr %s, ptr %s", bool_str, val_i1, true_ptr, false_ptr)
    fmt_name, fmt_len := get_string_literal(g, "%s")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    emit_printf_ptr(g, fmt_ptr, bool_str)
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

// True when the expression is an Expr_Index whose element type is a struct.
// Used by the print dispatcher to route `arr[i]` (struct elements) through
// the struct printer instead of the numeric fallback.
is_indexed_struct_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    idx, ok := expr.(^Expr_Index)
    if !ok { return false }
    return as_struct_body(expr_type(idx)) != nil
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
// Build a printf format-string pointer for `spec` — folds the get_string_literal
// + GEP pair that every print site otherwise repeats by hand.
emit_fmt_ptr :: proc(g: ^Codegen, spec: string) -> string {
    name, n := get_string_literal(g, spec)
    p := fresh_tmp(g)
    emit_string_gep(g, p, n, name)
    return p
}

// Print an already-loaded scalar VALUE given its Mara type — the value-level twin
// of emit_print_arg's scalar dispatch, and the single source of truth for how a
// scalar renders. Struct fields and array elements route through here so they
// match a bare `print(x)`: chars as glyphs, sign-aware integers, %g floats.
// Non-scalars (a nested struct/array field reaching here) hard-error rather than
// mis-emit — aggregates are handled by their own recursion before this is called.
emit_print_value :: proc(g: ^Codegen, val: string, ty: Type) {
    if ty == nil { codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, "<unknown>") }
    bt := distinct_base(ty)

    if _, ok := bt.(Type_Bool); ok { gen_print_bool(g, val); return }
    if _, ok := bt.(Type_Utf8); ok {
        // utf8 scalar = a character: render the glyph, not the code point.
        ext := fresh_tmp(g)
        emit(g, "  %s = zext i8 %s to i32", ext, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, "%c"), ext)
        return
    }
    if et, ok := bt.(^Type_Enum); ok {
        tag_ir := et.tag_type != "" ? tag_type_to_ir(et.tag_type) : "i64"
        gen_print_enum(g, val, tag_ir, et)
        return
    }
    if _, ok := bt.(Type_Err); ok {
        emit(g, "  call void @__mara_print_err(i32 %s)", val)
        return
    }
    if pt, ok := bt.(^Type_Ptr); ok {
        spec := "%p"
        if _, b := pt.elem.(Type_Byte); b { spec = "%s" }
        if _, u := pt.elem.(Type_Utf8); u { spec = "%s" }
        emit_printf_ptr(g, emit_fmt_ptr(g, spec), val)
        return
    }
    if _, ok := bt.(Type_CString); ok {
        emit_printf_ptr(g, emit_fmt_ptr(g, "%s"), val)
        return
    }

    // Numeric (integers + floats): IR-width driven with sign awareness.
    is_unsigned := false
    if n, ok := bt.(Type_Numeric); ok { is_unsigned = n.kind == .Unsigned }
    if _, ok := bt.(Type_Byte); ok { is_unsigned = true }
    nt := llvm_type_from_checker(ty)
    switch nt {
    case "double":
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), val)
    case "float":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", ext, val)
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), ext)
    case "half":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext half %s to double", ext, val)
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), ext)
    case "i64":
        emit_printf_i64(g, emit_fmt_ptr(g, is_unsigned ? "%llu" : "%lld"), val)
    case "i32":
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, is_unsigned ? "%u" : "%d"), val)
    case "i1":
        gen_print_bool(g, val)
    case "i8", "i16":
        // C varargs promote sub-int integers to int (i32).
        ext := fresh_tmp(g)
        emit(g, "  %s = %s %s %s to i32", ext, is_unsigned ? "zext" : "sext", nt, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, is_unsigned ? "%u" : "%d"), ext)
    case:
        codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, type_name(ty))
    }
}

// Print whatever lives at `addr` given its Mara type — the recursive core of
// aggregate printing. Scalars load + emit_print_value; structs and fixed arrays
// recurse. This is what lets struct fields and array elements render like a bare
// print at any nesting depth (struct-in-struct, array-of-structs, ...).
emit_print_at_addr :: proc(g: ^Codegen, addr: string, ty: Type) {
    if sd := as_struct_body(ty); sd != nil {
        if print_st, ok := lookup_struct(g, sd.name); ok {
            sv := Struct_Var{alloca = addr, struct_name = sd.name}
            gen_print_struct(g, &sv, print_st)
        }
        return
    }
    bt := distinct_base(ty)

    // A utf8 array (fixed / slice / partial) is a string — print it as bounded
    // text (%.*s) like a bare print(string), not element-by-element. Fixed
    // storage anchors the handle at the data; slice/PA anchor at the {len,cap,ptr}
    // header sitting at this address (same shapes resolve_array_handle builds).
    #partial switch t in bt {
    case ^Type_Fixed_Array:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{fixed_alloca = addr, elem_type = "i8", static_cap = t.size, is_utf8 = true}
            emit_array_print(g, &h)
            return
        }
    case ^Type_Slice:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{header_ptr = addr, elem_type = "i8", is_utf8 = true}
            emit_array_print(g, &h)
            return
        }
    case ^Type_Partial_Array:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{header_ptr = addr, elem_type = "i8", is_utf8 = true}
            emit_array_print(g, &h)
            return
        }
    }

    // Non-utf8 fixed array → recurse per element (flat or nested rows).
    if fa, ok := bt.(^Type_Fixed_Array); ok {
        elem_ir := llvm_type_from_checker(fa.elem)
        if _, nested := distinct_base(fa.elem).(^Type_Fixed_Array); nested {
            gen_print_nested_array(g, addr, fa.size, elem_ir, fa.elem)
        } else {
            gen_print_array_inline(g, addr, fa.size, elem_ir, fa.elem)
        }
        return
    }

    // Scalar — load at its IR width and route through the value printer.
    val := fresh_tmp(g)
    emit_load_into(g, val, llvm_type_from_checker(ty), addr)
    emit_print_value(g, val, ty)
}

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

        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, stv.alloca, fi)
        // One field, by its Mara type — scalar, nested struct, or array, each
        // rendered identically to a bare print(field).
        emit_print_at_addr(g, gep, f.type_)
    }

    // Print " }"
    close_name, close_len := get_string_literal(g, " }")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Pull out the enum type behind an expression, unwrapping distinct so
// `Status :: distinct File_Error` still prints by name. Returns (nil, false)
// for non-enum expressions.
enum_type_of :: proc(expr: Expr) -> (^Type_Enum, bool) {
    t := expr_type(expr)
    if t == nil { return nil, false }
    et, ok := distinct_base(t).(^Type_Enum)
    return et, ok
}

// Inline switch that prints the variant name matching `val`, or
// "EnumName(<tag>)" when nothing matches (e.g. flag-combo, out-of-range raw
// tag). Variants are sorted by value for stable IR; same-value aliases keep
// the first in name order — LLVM's switch requires unique case values, so
// duplicates are folded into one case.
gen_print_enum :: proc(g: ^Codegen, val: string, tag_ir: string, et: ^Type_Enum) {
    Variant :: struct { name: string, value: int }
    entries := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
    for name, value in et.variants {
        append(&entries, Variant{name = name, value = value})
    }
    slice.sort_by(entries[:], proc(a, b: Variant) -> bool {
        if a.value != b.value { return a.value < b.value }
        return a.name < b.name
    })
    // Fold same-value aliases: first wins.
    dedup := make([dynamic]Variant, 0, len(entries), context.temp_allocator)
    for entry in entries {
        if len(dedup) > 0 && dedup[len(dedup)-1].value == entry.value { continue }
        append(&dedup, entry)
    }

    unknown_lbl := fresh_label(g, "enum.unknown")
    done_lbl    := fresh_label(g, "enum.done")
    case_labels := make([]string, len(dedup), context.temp_allocator)
    for _, i in dedup {
        case_labels[i] = fresh_label(g, "enum.case")
    }

    sw: strings.Builder
    strings.write_string(&sw, fmt.tprintf("  switch %s %s, label %%%s [\n", tag_ir, val, unknown_lbl))
    for entry, i in dedup {
        strings.write_string(&sw, fmt.tprintf("    %s %d, label %%%s\n", tag_ir, entry.value, case_labels[i]))
    }
    strings.write_string(&sw, "  ]")
    emit_raw(g, strings.to_string(sw))

    // error_kinds print namespaced (`File_Error.Not_Found`) so the variant
    // name alone — which can collide across sets — stays unambiguous in logs.
    // Regular enums print just the variant for compactness (Tag_u8.B -> "B").
    name_prefix := ""
    if et.is_error_kind {
        prefix_name := et.source_name
        if prefix_name == "" { prefix_name = et.name }
        name_prefix = strings.concatenate({prefix_name, "."}, context.temp_allocator)
    }

    for entry, i in dedup {
        emit_label(g, case_labels[i])
        emit_print_literal(g, strings.concatenate({name_prefix, entry.name}, context.temp_allocator))
        emit_br(g, done_lbl)
    }

    emit_label(g, unknown_lbl)
    emit_print_literal(g, fmt.tprintf("%s(", et.source_name if et.source_name != "" else et.name))
    fmt_name, fmt_len := get_string_literal(g, tag_ir == "i64" ? "%lld" : "%d")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    switch tag_ir {
    case "i64":
        emit_printf_i64(g, fmt_ptr, val)
    case "i32":
        // Already at printf's default-int width — pass through.
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), fmt_ptr, val)
    case:
        // i16 / i8: zext to i32 for printf's default-int varargs promotion.
        // zext (not sext) — enum tags are unsigned-shaped values, no two's-
        // complement bits to preserve.
        ext := fresh_tmp(g)
        emit(g, "  %s = zext %s %s to i32", ext, tag_ir, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), fmt_ptr, ext)
    }
    emit_print_literal(g, ")")
    emit_br(g, done_lbl)

    emit_label(g, done_lbl)
}

// Print a flat array inline: [v1, v2, v3]
gen_print_array_inline :: proc(g: ^Codegen, data_ptr: string, cap: int, elem_type: string, elem_ty: Type) {
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
        emit_print_at_addr(g, gep, elem_ty)
    }

    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print a nested array like [4][4]f32 as: [[v, v, v, v], [v, v, v, v], ...]
gen_print_nested_array :: proc(g: ^Codegen, data_ptr: string, outer_cap: int, inner_ir_type: string, row_ty: Type) {
    inner_cap, inner_elem, _ := parse_array_ir_type(inner_ir_type)
    outer_arr_type := fmt.tprintf("[%d x %s]", outer_cap, inner_ir_type)
    // row_ty is the inner row's Mara type (e.g. [M]T); its element type drives
    // each scalar's sign-aware / char-aware rendering.
    inner_elem_ty: Type = nil
    if fa, ok := distinct_base(row_ty).(^Type_Fixed_Array); ok { inner_elem_ty = fa.elem }

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
        gen_print_array_inline(g, row_gep, inner_cap, inner_elem, inner_elem_ty)
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

    // The element's Mara type drives sign-aware / char-aware rendering (matches a
    // bare print of the element). is_array_expr guarantees a fixed-array type.
    elem_ty: Type = nil
    if fa, ok := distinct_base(expr_type(expr)).(^Type_Fixed_Array); ok { elem_ty = fa.elem }

    // Nested array: delegate to gen_print_nested_array
    if inner_cap, inner_elem, is_nested := parse_array_ir_type(av.elem_type); is_nested {
        gen_print_nested_array(g, av.alloca, av.capacity, av.elem_type, elem_ty)
        _ = inner_cap; _ = inner_elem
        return
    }

    // Print opening bracket
    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    // Element count is always capacity (full arrays)
    arr_len := fmt.tprintf("%d", av.capacity)

    // Loop through elements. Counter runs at slice header width; array
    // capacities fit by construction.
    w := slice_layout.len_ir
    cond_label := fresh_label(g, "print.cond")
    body_label := fresh_label(g, "print.body")
    end_label  := fresh_label(g, "print.end")

    idx_ptr := fresh_tmp(g)
    emit_alloca(g, idx_ptr, w)
    emit_store(g, w, "0", idx_ptr)
    emit_br(g, cond_label)

    emit_label(g, cond_label)
    idx := fresh_tmp(g)
    emit_load_into(g, idx, w, idx_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", cmp, w, idx, arr_len)
    emit_cond_br(g, cmp, body_label, end_label)

    emit_label(g, body_label)
    idx2 := fresh_tmp(g)
    emit_load_into(g, idx2, w, idx_ptr)

    // Print comma+space if not first element
    comma_label := fresh_label(g, "print.comma")
    no_comma_label := fresh_label(g, "print.nocomma")
    after_comma_label := fresh_label(g, "print.aftercomma")
    is_first := fresh_tmp(g)
    emit(g, "  %s = icmp eq %s %s, 0", is_first, w, idx2)
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
    emit_load_into(g, idx3, w, idx_ptr)
    gep := fresh_tmp(g)
    emit_array_gep_var(g, gep, arr_type, av.alloca, idx3, w)
    // Print the element by its Mara type — handles structs / nested arrays too.
    emit_print_at_addr(g, gep, elem_ty)

    // Increment index
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, idx3)
    emit_store(g, w, next, idx_ptr)
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

// Should this expression print as a character glyph (%c) rather than a
// number? True for a character literal and for utf8 values (e.g. one
// element loaded out of a string) — 8-bit code units whose meaningful
// rendering is the glyph, not the integer.
is_char_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_Char); ok { return true }
    t := expr_type(expr)
    if _, is_utf8 := t.(Type_Utf8); is_utf8 { return true }
    return false
}

is_string_expr :: proc(g: ^Codegen, expr: Expr) -> bool {
    if _, ok := expr.(^Expr_String); ok { return true }
    t := expr_type(expr)
    base := distinct_base(t)
    if pt, ok := base.(^Type_Ptr); ok {
        if _, utf8_ok := pt.elem.(Type_Utf8); utf8_ok { return true }
    }
    if _, is_cs := t.(Type_CString); is_cs { return true }
    return false
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
            if _, is_foreign := cs.origin.(Origin_Foreign); is_foreign && len(cs.return_types) > 0 {
                // Foreign returns: unwrap distinct so a `distinct ^utf8`
                // return type (the new cstring) is recognized as a pointer
                // via its underlying shape — no cstring-specific check.
                ret_single := cs.return_types[0]
                base := distinct_base(ret_single)
                if _, is_ptr := base.(^Type_Ptr); is_ptr { return true }
                if _, is_cs := ret_single.(Type_CString); is_cs { return true }
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
        // Unwrap distinct so a `distinct u8` (etc.) prints as its base
        // number instead of falling to the i64 fallback with a sub-i64
        // value — printf's vararg slot would mistype and clang rejects
        // the module.
        base := distinct_base(t)
        if _, is_num := base.(Type_Numeric); is_num { return true }
        // byte is numeric for print purposes: a raw memory octet renders
        // as its unsigned value. utf8 is deliberately NOT here — it takes
        // the %c glyph path via is_char_expr before this check.
        if _, is_byte := base.(Type_Byte); is_byte { return true }
        if _, is_enum := base.(^Type_Enum); is_enum { return true }
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
        base := distinct_base(t)
        if n, n_ok := base.(Type_Numeric); n_ok {
            return llvm_type_from_checker(n)
        }
        if _, b_ok := base.(Type_Byte); b_ok {
            return "i8"
        }
        if _, e_ok := base.(^Type_Enum); e_ok {
            return llvm_type_from_checker(base)
        }
        // Pointer dereference: the expression's type is the dereferenced type
        if pt, pt_ok := base.(^Type_Ptr); pt_ok {
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
