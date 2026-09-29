package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Match codegen (union type matching and value matching)
// ---------------------------------------------------------------------------

gen_match :: proc(g: ^Codegen, s: ^Stmt_Match) {
    // match is union-only (the type checker enforces it). Pure-enum unions are
    // registered as Type_Enum and lower through value match; payload-bearing
    // unions go through union match.
    if ut, is_union := expr_type(s.subject).(^Type_Union); is_union {
        if union_ptr, ok := union_subject_ptr(g, s.subject, ut); ok {
            gen_union_match(g, s, ut, union_ptr)
            return
        }
        codegen_fatal(g, s.span, CODE_CANNOT_MATCH_KIND_UNION_EXPRESSION)
    }
    gen_value_match(g, s)
}

// Resolve the subject of a match-on-union to a pointer at the union's
// storage (tag + payload). Handles:
//   - ident         → existing Union_Var alloca
//   - field access  → GEP into the enclosing struct
//   - anything else → spill the value to a stack temp
union_subject_ptr :: proc(g: ^Codegen, expr: Expr, ut: ^Type_Union) -> (string, bool) {
    #partial switch e in expr {
    case ^Expr_Ident:
        if uv, uv_ok := get_union(g, e.name); uv_ok {
            return uv.alloca, true
        }
    case ^Expr_Field_Access:
        addr := gen_field_address(g, e)
        if addr != "" && addr != "null" {
            return addr, true
        }
    case ^Expr_Index:
        return gen_index_address(g, e), true
    }
    // Any other union value — a call result, a variant literal, a deref — is
    // pointer-valued: gen_expr already materializes it and yields its address.
    ptr := gen_expr(g, expr, union_llvm_name(ut.name))
    if ptr == "" { return "", false }
    return ptr, true
}

// A union value's tag, read from its storage. A tagged union keeps it in field
// 0. A niche union stores none — its storage is the Some variant's pointer — so
// its tag is whichever variant the pointer's nullness says it holds.
load_union_tag :: proc(g: ^Codegen, ut: ^Type_Union, union_ptr: string) -> string {
    tag_ir := union_tag_ir_type(ut)
    if is_niche_layout(g, ut) {
        some, none := niche_variants(g, ut)
        ptr := fresh_tmp(g)
        emit_load_into(g, ptr, "ptr", union_ptr)
        live := fresh_tmp(g)
        emit(g, "  %s = icmp ne ptr %s, null", live, ptr)
        tag := fresh_tmp(g)
        emit(g, "  %s = select i1 %s, %s %d, %s %d", tag, live,
             tag_ir, ut.tag_map[some], tag_ir, ut.tag_map[none])
        return tag
    }
    tag_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, union_llvm_name(ut.name), union_ptr)
    tag_val := fresh_tmp(g)
    emit_load_into(g, tag_val, tag_ir, tag_ptr)
    return tag_val
}

gen_union_match :: proc(g: ^Codegen, s: ^Stmt_Match, ut: ^Type_Union, union_ptr: string) {
    tag_val := load_union_tag(g, ut, union_ptr)
    switch_type := union_tag_ir_type(ut)

    // Generate labels
    end_label := fresh_label(g, "match.end")

    // Check for an else arm (must be last if present)
    has_else := len(s.arms) > 0 && s.arms[len(s.arms) - 1].is_else

    // Build arm labels
    arm_labels: [dynamic]string
    for _, i in s.arms {
        append(&arm_labels, fresh_label(g, fmt.tprintf("match.case.%d", i)))
    }

    // The default: the else arm, or — the arms covering every variant — a
    // failure (another tag is corrupt memory).
    default_label := arm_labels[len(arm_labels) - 1] if has_else else fresh_label(g, "match.fail")

    // Build switch instruction using strings.Builder (avoids brace issues with emit)
    sw: strings.Builder
    strings.write_string(&sw, fmt.tprintf("  switch %s %s, label %%%s [\n", switch_type, tag_val, default_label))
    for arm, i in s.arms {
        if arm.variant != "" {
            // Use resolved tag from type checker
            strings.write_string(&sw, fmt.tprintf("    %s %d, label %%%s\n", switch_type, arm.resolved_tag, arm_labels[i]))
        }
    }
    strings.write_string(&sw, "  ]")
    emit_raw(g, strings.to_string(sw))
    if !has_else {
        emit_label(g, default_label)
        emit_match_fail(g, s.span, tag_val, switch_type, union_tag_unsigned(ut))
    }

    // Save variable state — arm-local variables must not leak across arms
    match_snap := save_var_scope(g)

    // Emit each arm block
    for arm, i in s.arms {
        emit_label(g, arm_labels[i])

        if arm.variant != "" {
            // Register the binding variable as a struct var pointing at the payload
            if arm.is_union_arm && arm.bound_name != "" {
                // Use resolved struct name from type checker
                struct_name := arm.resolved_struct
                if struct_name == "" {
                    struct_name = ut.variant_structs[arm.variant_name] or_else arm.variant_name
                }
                // The variant struct carries the tag header and overlays the
                // union at offset 0, so bind it at the union pointer — its
                // user fields sit at the same absolute offsets as before. A
                // niche union's Some variant is its storage outright.
                g.alias_vars[arm.bound_name] = true // the union's own bytes
                g.all_vars[arm.bound_name] = Struct_Var{
                    alloca = union_ptr,
                    struct_name = struct_name,
                }
            }

            // Generate body. gen_body_block handles scope push/pop and the
            // terminator-stop logic (return / break / continue).
            gen_body_block(g, arm.body[:], .Match_Arm, end_label)
        } else if arm.is_else {
            // Else (wildcard) arm — no binding, just emit body
            gen_body_block(g, arm.body[:], .Match_Arm, end_label)
        }

        // Restore variable state after each arm
        restore_var_scope(g, &match_snap)
    }

    // End block
    emit_label(g, end_label)
}

// A match's failure: its subject holds no arm's tag — corrupt memory, since
// every match covers every variant. `tag` (of IR type `tag_ir`) is reported.
emit_match_fail :: proc(g: ^Codegen, span: Span, tag, tag_ir: string, unsigned: bool) {
    wide := tag
    if tag_ir != "i64" {
        wide = fresh_tmp(g)
        emit(g, "  %s = %s %s %s to i64", wide, "zext" if unsigned else "sext", tag_ir, tag)
    }
    loc_global, _ := get_string_literal(g, format_location(span.file, span.line, span.col))
    emit(g, "  call void %s(ptr %s, i64 %s)", __MARA_MATCH_FAIL, loc_global, wide)
    emit(g, "  unreachable")
}

// Whether a union's tag is unsigned (`union(tag u32)`); the default i64 isn't.
union_tag_unsigned :: proc(ut: ^Type_Union) -> bool {
    return strings.has_prefix(ut.tag_type, "u")
}

// Whether a matched value is unsigned: an enum's declared tag type, a number's kind.
match_value_unsigned :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:   return strings.has_prefix(v.tag_type, "u")
    case Type_Numeric: return v.kind == .Unsigned
    case Type_Byte, Type_Utf8, Type_Bool: return true
    }
    return false
}

// ---------------------------------------------------------------------------
// Value match codegen (match on integers, enum values, etc.)
// ---------------------------------------------------------------------------

// The arms' tests come first, a chain of compares, each false edge to the next
// test — the last's to the else arm or, the arms covering every variant, to a
// failure; then the arms' bodies in order.
gen_value_match :: proc(g: ^Codegen, s: ^Stmt_Match) {
    // Evaluate the subject expression
    subj_val := gen_expr(g, s.subject)
    subj_type := expr_ir_type(g, s.subject)

    // Generate labels
    end_label := fresh_label(g, "match.end")

    // Check for an else arm (must be last if present)
    has_else := len(s.arms) > 0 && s.arms[len(s.arms) - 1].is_else
    real_arm_count := len(s.arms)
    if has_else { real_arm_count -= 1 }

    arm_body_labels: [dynamic]string
    for i in 0..<real_arm_count {
        append(&arm_body_labels, fresh_label(g, fmt.tprintf("match.body.%d", i)))
    }
    last_label := fresh_label(g, "match.else" if has_else else "match.fail")

    // The tests.
    if real_arm_count == 0 { emit_br(g, last_label) }
    for i in 0..<real_arm_count {
        arm := s.arms[i]
        next := last_label
        if i < real_arm_count - 1 { next = fresh_label(g, fmt.tprintf("match.next.%d", i)) }
        // Variant arms have their tag value resolved by the type checker
        arm_val := arm.variant != "" ? fmt.tprintf("%d", arm.resolved_tag) : gen_expr(g, arm.value)
        cmp := fresh_tmp(g)
        emit(g, "  %s = icmp eq %s %s, %s", cmp, subj_type, subj_val, arm_val)
        emit_cond_br(g, cmp, arm_body_labels[i], next)
        if i < real_arm_count - 1 { emit_label(g, next) }
    }
    if !has_else {
        emit_label(g, last_label)
        emit_match_fail(g, s.span, subj_val, subj_type, match_value_unsigned(expr_type(s.subject)))
    }

    // The bodies. Arm-local variables must not leak across arms.
    vm_snap := save_var_scope(g)
    for i in 0..<real_arm_count {
        emit_label(g, arm_body_labels[i])
        gen_body_block(g, s.arms[i].body[:], .Match_Arm, end_label)
        restore_var_scope(g, &vm_snap)
    }
    if has_else {
        emit_label(g, last_label)
        gen_body_block(g, s.arms[len(s.arms) - 1].body[:], .Match_Arm, end_label)
        restore_var_scope(g, &vm_snap)
    }

    // End block
    emit_label(g, end_label)
}
