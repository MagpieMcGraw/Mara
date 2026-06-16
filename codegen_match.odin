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
    }
    // Rvalue fallback: spill to a stack alloca.
    llvm_name := union_llvm_name(ut.name)
    tmp := fresh_tmp(g)
    emit_alloca(g, tmp, llvm_name)
    val := gen_expr(g, expr)
    if val != "" && val != "0" {
        emit_store(g, llvm_name, val, tmp)
        return tmp, true
    }
    return "", false
}

// Niche-laid-out union: union storage is `ptr`. Dispatch on null instead of
// reading a tag. The Some-variant payload binding aliases the union storage
// directly — Some's single pointer field sits at offset 0, same as the niche
// pointer slot, so existing field-access codegen reads it correctly with no
// extra GEP.
gen_niche_union_match :: proc(g: ^Codegen, s: ^Stmt_Match, ut: ^Type_Union, union_ptr: string) {
    some_name, none_name := niche_variants(g, ut)

    // Load the pointer value
    ptr_val := fresh_tmp(g)
    emit_load_into(g, ptr_val, "ptr", union_ptr)
    is_null := fresh_tmp(g)
    emit(g, "  %s = icmp eq ptr %s, null", is_null, ptr_val)

    end_label  := fresh_label(g, "match.end")
    none_label := fresh_label(g, "match.none")
    some_label := fresh_label(g, "match.some")
    emit_cond_br(g, is_null, none_label, some_label)

    match_snap := save_var_scope(g)

    // Find which arm covers which case; honour an `else` arm as a catch-all.
    some_arm: ^Match_Arm
    none_arm: ^Match_Arm
    else_arm: ^Match_Arm
    for &arm in s.arms {
        if arm.is_else {
            else_arm = &arm
        } else if arm.variant_name == some_name {
            some_arm = &arm
        } else if arm.variant_name == none_name {
            none_arm = &arm
        }
    }
    if some_arm == nil { some_arm = else_arm }
    if none_arm == nil { none_arm = else_arm }

    // None arm — just the body, no payload binding.
    emit_label(g, none_label)
    if none_arm != nil {
        gen_body_block(g, none_arm.body[:], .Match_Arm, end_label)
    } else {
        emit_br(g, end_label)
    }
    restore_var_scope(g, &match_snap)

    // Some arm — bind the payload to the union storage (Some struct's single
    // pointer field is at offset 0, same as the niche slot).
    emit_label(g, some_label)
    if some_arm != nil {
        if some_arm.binding_name != "" {
            struct_name := some_arm.resolved_struct
            if struct_name == "" {
                struct_name = ut.variant_structs[some_arm.variant_name] or_else some_arm.variant_name
            }
            g.all_vars[some_arm.binding_name] = Struct_Var{
                alloca      = union_ptr,
                struct_name = struct_name,
            }
        }
        gen_body_block(g, some_arm.body[:], .Match_Arm, end_label)
    } else {
        emit_br(g, end_label)
    }
    restore_var_scope(g, &match_snap)

    emit_label(g, end_label)
}

gen_union_match :: proc(g: ^Codegen, s: ^Stmt_Match, ut: ^Type_Union, union_ptr: string) {
    if is_niche_layout(g, ut) {
        gen_niche_union_match(g, s, ut, union_ptr)
        return
    }

    llvm_name := union_llvm_name(ut.name)
    tag_type := union_tag_ir_type(ut)

    // Load tag from field 0 using the union's tag type
    tag_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, llvm_name, union_ptr)
    tag_val := fresh_tmp(g)
    emit_load_into(g, tag_val, tag_type, tag_ptr)
    switch_type := tag_type

    // Get payload pointer (field 1)
    payload_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 1", payload_ptr, llvm_name, union_ptr)

    // Generate labels
    end_label := fresh_label(g, "match.end")

    // Check for an else arm (must be last if present)
    has_else := len(s.arms) > 0 && s.arms[len(s.arms) - 1].is_else
    default_label := end_label

    // Build arm labels
    arm_labels: [dynamic]string
    for _, i in s.arms {
        append(&arm_labels, fresh_label(g, fmt.tprintf("match.case.%d", i)))
    }

    // If last arm is else, its label becomes the switch default
    if has_else {
        default_label = arm_labels[len(arm_labels) - 1]
    }

    // Build switch instruction using strings.Builder (avoids brace issues with emit)
    sw: strings.Builder
    strings.write_string(&sw, fmt.tprintf("  switch %s %s, label %%%s [\n", switch_type, tag_val, default_label))
    for arm, i in s.arms {
        if arm.is_union_arm || arm.dot_shorthand != "" {
            // Use resolved tag from type checker
            strings.write_string(&sw, fmt.tprintf("    %s %d, label %%%s\n", switch_type, arm.resolved_tag, arm_labels[i]))
        }
    }
    strings.write_string(&sw, "  ]")
    emit_raw(g, strings.to_string(sw))

    // Save variable state — arm-local variables must not leak across arms
    match_snap := save_var_scope(g)

    // Emit each arm block
    for arm, i in s.arms {
        emit_label(g, arm_labels[i])

        if arm.is_union_arm || arm.dot_shorthand != "" {
            // Register the binding variable as a struct var pointing at the payload
            if arm.is_union_arm && arm.binding_name != "" {
                // Use resolved struct name from type checker
                struct_name := arm.resolved_struct
                if struct_name == "" {
                    struct_name = ut.variant_structs[arm.variant_name] or_else arm.variant_name
                }
                g.all_vars[arm.binding_name] = Struct_Var{
                    alloca = payload_ptr,
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

// ---------------------------------------------------------------------------
// Value match codegen (match on integers, enum values, etc.)
// ---------------------------------------------------------------------------

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

    else_label := end_label

    // Save variable state — arm-local variables must not leak across arms
    vm_snap := save_var_scope(g)

    // For each real arm, generate: compare, branch to body or next check
    arm_body_labels: [dynamic]string
    arm_next_labels: [dynamic]string
    for i in 0..<real_arm_count {
        append(&arm_body_labels, fresh_label(g, fmt.tprintf("match.body.%d", i)))
        if i < real_arm_count - 1 {
            append(&arm_next_labels, fresh_label(g, fmt.tprintf("match.next.%d", i)))
        } else {
            // Last real arm's false branch: go to else or end
            if has_else {
                else_label = fresh_label(g, "match.else")
                append(&arm_next_labels, else_label)
            } else {
                append(&arm_next_labels, end_label)
            }
        }
    }

    // Edge case: else as only arm — unconditional branch
    if real_arm_count == 0 && has_else {
        else_label = fresh_label(g, "match.else")
        emit_br(g, else_label)
    }

    // Emit comparison chain for real arms
    for i in 0..<real_arm_count {
        arm := s.arms[i]
        // Dot-shorthand arms have their tag value resolved by the type checker
        arm_val := arm.dot_shorthand != "" ? fmt.tprintf("%d", arm.resolved_tag) : gen_expr(g, arm.value)
        cmp := fresh_tmp(g)
        emit(g, "  %s = icmp eq %s %s, %s", cmp, subj_type, subj_val, arm_val)
        emit_cond_br(g, cmp, arm_body_labels[i], arm_next_labels[i])

        // Emit arm body block
        emit_label(g, arm_body_labels[i])
        gen_body_block(g, arm.body[:], .Match_Arm, end_label)

        // Restore variable state after each arm
        restore_var_scope(g, &vm_snap)

        // Start next comparison block (unless this was the last real arm)
        if i < real_arm_count - 1 {
            emit_label(g, arm_next_labels[i])
        }
    }

    // Emit else arm body if present
    if has_else {
        else_arm := s.arms[len(s.arms) - 1]
        emit_label(g, else_label)
        gen_body_block(g, else_arm.body[:], .Match_Arm, end_label)
        // Restore after else arm
        restore_var_scope(g, &vm_snap)
    }

    // End block
    emit_label(g, end_label)
}
