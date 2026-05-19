package mara

import "core:fmt"
import "core:os"
import "core:strings"

dump_checked_program :: proc(path: string, checked: ^Checked_Program) -> bool {
    b: strings.Builder

    // Constants
    if len(checked.constant_values) > 0 {
        fmt.sbprintln(&b, "=== Constants ===")
        for name, val in checked.constant_values {
            fmt.sbprintf(&b, "  %s :: %d\n", name, val)
        }
        fmt.sbprintln(&b)
    }

    // Structs
    if len(checked.table.funs) > 0 {
        fmt.sbprintln(&b, "=== Structs ===")
        for name, st in checked.table.funs {
            dump_struct(&b, name, st)
        }
        fmt.sbprintln(&b)
    }

    // Enums
    if len(checked.table.enums) > 0 {
        fmt.sbprintln(&b, "=== Enums ===")
        for name, et in checked.table.enums {
            dump_enum(&b, name, et)
        }
        fmt.sbprintln(&b)
    }

    // Unions
    if len(checked.table.unions) > 0 {
        fmt.sbprintln(&b, "=== Unions ===")
        for name, ut in checked.table.unions {
            dump_union(&b, name, ut)
        }
        fmt.sbprintln(&b)
    }

    // Distinct types
    if len(checked.table.distinct_types) > 0 {
        fmt.sbprintln(&b, "=== Distinct Types ===")
        for name, dt in checked.table.distinct_types {
            fmt.sbprintf(&b, "  %s :: distinct %s\n", name, type_name(dt.base_type))
        }
        fmt.sbprintln(&b)
    }

    // Foreign functions — pulled out of checked.functions by filtering on origin.
    has_foreign := false
    for _, cs in checked.functions {
        if _, is_foreign := cs.origin.(Origin_Foreign); is_foreign { has_foreign = true; break }
    }
    if has_foreign {
        fmt.sbprintln(&b, "=== Foreign Functions ===")
        for name, cs in checked.functions {
            fo, is_foreign := cs.origin.(Origin_Foreign)
            if !is_foreign { continue }
            fmt.sbprintf(&b, "  %s (link: %s, lib: %s)\n", name, fo.link_name, fo.library)
            fmt.sbprintf(&b, "    params: ")
            for p, i in cs.params {
                if i > 0 { fmt.sbprintf(&b, ", ") }
                fmt.sbprintf(&b, "%s: %s", p.name, type_name(p.type_))
            }
            fmt.sbprintf(&b, "\n    return: %s\n", type_name(cs.return_type))
        }
        fmt.sbprintln(&b)
    }

    // Functions (in order)
    fmt.sbprintln(&b, "=== Functions ===")
    for fn_name in checked.function_order {
        if cf, ok := &checked.functions[fn_name]; ok {
            dump_function(&b, cf)
        }
    }
    // Also dump monomorphized functions not in function_order
    for fn_name, &cf in checked.functions {
        if strings.contains(fn_name, "__") {
            found := false
            for ordered_name in checked.function_order {
                if ordered_name == fn_name { found = true; break }
            }
            if !found {
                dump_function(&b, &cf)
            }
        }
    }
    fmt.sbprintln(&b)

    werr := os.write_entire_file(path, transmute([]u8)strings.to_string(b))
    if werr != nil {
        fmt.printf("Error: could not write dump file '%s'\n", path)
        return false
    }
    fmt.printf("Dumped checked program to '%s'\n", path)
    return true
}

// ---------------------------------------------------------------------------
// Type definitions
// ---------------------------------------------------------------------------

dump_struct :: proc(b: ^strings.Builder, name: string, st: ^Type_Scope, base_indent: int = 1) {
    indent := make_indent(base_indent)
    fmt.sbprintf(b, "%s%s :: struct", indent, name)
    if st.is_array_class {
        fmt.sbprintf(b, " [array_class: cap=%d, elem=%s, array=%s, len=%s]",
            st.array_cap, type_name(st.elem_type), st.array_field, st.len_field)
    }
    if st.generic_base != "" {
        fmt.sbprintf(b, " [generic: %s(", st.generic_base)
        for arg, i in st.generic_args {
            if i > 0 { fmt.sbprintf(b, ", ") }
            fmt.sbprintf(b, "%s", type_name(arg))
        }
        fmt.sbprintf(b, ")]")
    }
    fmt.sbprintln(b, " {")
    field_indent := make_indent(base_indent + 1)
    for f in st.fields {
        fmt.sbprintf(b, "%s%s: %s", field_indent, f.name, type_name(f.type_))
        if f.is_using { fmt.sbprintf(b, " [using]") }
        fmt.sbprintln(b)
    }
    fmt.sbprintf(b, "%s}\n", indent)
}

dump_enum :: proc(b: ^strings.Builder, name: string, et: ^Type_Enum, base_indent: int = 1) {
    indent := make_indent(base_indent)
    fmt.sbprintf(b, "%s%s :: enum", indent, name)
    if et.tag_type != "" {
        fmt.sbprintf(b, "(%s)", et.tag_type)
    }
    fmt.sbprintln(b, " {")
    variant_indent := make_indent(base_indent + 1)
    for vname, val in et.variants {
        fmt.sbprintf(b, "%s%s = %d\n", variant_indent, vname, val)
    }
    fmt.sbprintf(b, "%s}\n", indent)
}

dump_union :: proc(b: ^strings.Builder, name: string, ut: ^Type_Union, base_indent: int = 1) {
    indent := make_indent(base_indent)
    fmt.sbprintf(b, "%s%s :: union", indent, name)
    if ut.tag_type != "" {
        fmt.sbprintf(b, "(%s)", ut.tag_type)
    }
    fmt.sbprintln(b, " {")
    variant_indent := make_indent(base_indent + 1)
    for vname in ut.variants {
        tag := ut.tag_map[vname]
        sname, has_struct := ut.variant_structs[vname]
        if has_struct {
            fmt.sbprintf(b, "%s%s = %d -> %s\n", variant_indent, vname, tag, sname)
        } else {
            fmt.sbprintf(b, "%s%s = %d\n", variant_indent, vname, tag)
        }
    }
    fmt.sbprintf(b, "%s}\n", indent)
}

// ---------------------------------------------------------------------------
// Functions
// ---------------------------------------------------------------------------

dump_function :: proc(b: ^strings.Builder, cf: ^Checked_Scope, base_indent: int = 1) {
    indent := make_indent(base_indent)
    fmt.sbprintf(b, "%s%s :: fun(", indent, cf.name)
    for p, i in cf.params {
        if i > 0 { fmt.sbprintf(b, ", ") }
        fmt.sbprintf(b, "%s: %s", p.name, type_name(p.type_))
    }
    fmt.sbprintf(b, ") -> %s\n", type_name(cf.return_type))

    // Body
    for stmt in cf.body {
        dump_stmt(b, stmt, base_indent + 1)
    }
    fmt.sbprintln(b)
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

dump_if_chain :: proc(b: ^strings.Builder, s: ^Stmt_If, depth: int, is_else_if: bool = false) {
    indent := make_indent(depth)
    if is_else_if {
        strings.write_string(b, "} else if ")
    } else {
        fmt.sbprintf(b, "%sif ", indent)
    }
    dump_expr(b, s.condition)
    strings.write_string(b, " {\n")
    for child in s.body {
        dump_stmt(b, child, depth + 1)
    }
    if len(s.else_body) > 0 {
        if len(s.else_body) == 1 {
            if nested_if, is_if := s.else_body[0].(^Stmt_If); is_if {
                fmt.sbprintf(b, "%s", indent)
                dump_if_chain(b, nested_if, depth, true)
                return
            }
        }
        fmt.sbprintf(b, "%s", indent)
        strings.write_string(b, "} else {\n")
        for child in s.else_body {
            dump_stmt(b, child, depth + 1)
        }
    }
    fmt.sbprintf(b, "%s", indent)
    strings.write_string(b, "}\n")
}

dump_stmt :: proc(b: ^strings.Builder, stmt: Stmt, depth: int) {
    indent := make_indent(depth)

    switch s in stmt {
    case ^Stmt_Assign:
        if s.target != nil {
            fmt.sbprintf(b, "%s", indent)
            #partial switch t in s.target {
            case ^Expr_Field_Access:
                fmt.sbprintf(b, "field_assign [%s] ", type_name(s.target_type))
                dump_expr(b, t.expr)
                fmt.sbprintf(b, ".%s = ", t.field)
                dump_expr(b, s.value)
            case ^Expr_Index:
                fmt.sbprintf(b, "index_assign [%s] ", type_name(s.target_type))
                dump_expr(b, t.expr)
                fmt.sbprintf(b, "[")
                dump_expr(b, t.index)
                fmt.sbprintf(b, "] = ")
                dump_expr(b, s.value)
            case ^Expr_Slice:
                fmt.sbprintf(b, "slice_assign [%s] ", type_name(s.target_type))
                dump_expr(b, t.expr)
                fmt.sbprintf(b, "[")
                dump_expr(b, t.low)
                fmt.sbprintf(b, ":")
                dump_expr(b, t.high)
                fmt.sbprintf(b, "] = ")
                dump_expr(b, s.value)
            case ^Expr_Unary:
                fmt.sbprintf(b, "deref_assign [%s] ", type_name(s.target_type))
                dump_expr(b, t.operand)
                fmt.sbprintf(b, "^ = ")
                dump_expr(b, s.value)
            case:
                dump_expr(b, s.target)
                fmt.sbprintf(b, " = ")
                dump_expr(b, s.value)
            }
            fmt.sbprintln(b)
        } else {
            fmt.sbprintf(b, "%s", indent)
            fmt.sbprintf(b, "%s : %s = ", s.name, type_name(s.var_type))
            dump_expr(b, s.value)
            fmt.sbprintln(b)
        }

    case ^Stmt_Multi_Assign:
        for a in s.assigns {
            dump_stmt(b, a, depth)
        }

    case ^Stmt_Multi_Return_Assign:
        fmt.sbprintf(b, "%s", indent)
        for name, i in s.names {
            if i > 0 { fmt.sbprintf(b, ", ") }
            if name != "" {
                fmt.sbprintf(b, "%s", name)
            } else if i < len(s.targets) && s.targets[i] != nil {
                dump_expr(b, s.targets[i])
            } else {
                fmt.sbprintf(b, "_")
            }
        }
        fmt.sbprintf(b, " : ")
        for t, i in s.var_types {
            if i > 0 { fmt.sbprintf(b, ", ") }
            fmt.sbprintf(b, "%s", type_name(t))
        }
        fmt.sbprintf(b, " = ")
        for val, i in s.values {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_expr(b, val)
        }
        fmt.sbprintln(b)

    case Stmt_Call:
        fmt.sbprintf(b, "%s", indent)
        dump_expr(b, s.expr)
        fmt.sbprintln(b)

    case ^Stmt_If:
        dump_if_chain(b, s, depth)

    case ^Stmt_For:
        if s.is_collection_for {
            fmt.sbprintf(b, "%sfor ", indent)
            if s.elem_var != "" { fmt.sbprintf(b, "%s", s.elem_var) } else { fmt.sbprintf(b, "_") }
            if s.index_var != "" { fmt.sbprintf(b, ", %s", s.index_var) }
            fmt.sbprintf(b, " in ")
            dump_expr(b, s.collection)
        } else if s.is_range {
            fmt.sbprintf(b, "%sfor %s : %s in ", indent, s.loop_var, type_name(s.var_type))
            dump_expr(b, s.range_low)
            fmt.sbprintf(b, "..")
            dump_expr(b, s.range_high)
        } else if s.init != nil {
            fmt.sbprintf(b, "%sfor ", indent)
            dump_stmt_inline(b, s.init)
            fmt.sbprintf(b, "; ")
            dump_expr(b, s.condition)
            fmt.sbprintf(b, "; ")
            dump_stmt_inline(b, s.post)
        } else {
            fmt.sbprintf(b, "%sfor ", indent)
            dump_expr(b, s.condition)
        }
        fmt.sbprintln(b, " {")
        for child in s.body {
            dump_stmt(b, child, depth + 1)
        }
        fmt.sbprintf(b, "%s}\n", indent)

    case ^Stmt_Scope:
        // Should not appear in checked bodies (handled at top level)
        fmt.sbprintf(b, "%sfun_def %s\n", indent, s.name)

    case Stmt_Return:
        fmt.sbprintf(b, "%sreturn ", indent)
        for val, i in s.values {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_expr(b, val)
        }
        fmt.sbprintln(b)

    case Stmt_Break:
        fmt.sbprintf(b, "%sbreak\n", indent)

    case Stmt_Continue:
        fmt.sbprintf(b, "%scontinue\n", indent)

    case ^Stmt_Match:
        fmt.sbprintf(b, "%smatch ", indent)
        dump_expr(b, s.subject)
        fmt.sbprintln(b, " {")
        for arm in s.arms {
            arm_indent := make_indent(depth + 1)
            if arm.is_else {
                fmt.sbprintf(b, "%selse", arm_indent)
            } else if arm.is_union_arm {
                fmt.sbprintf(b, "%s%s", arm_indent, arm.variant_name)
                if arm.binding_name != "" {
                    fmt.sbprintf(b, " %s", arm.binding_name)
                }
                fmt.sbprintf(b, " [tag=%d", arm.resolved_tag)
                if arm.resolved_struct != "" {
                    fmt.sbprintf(b, ", struct=%s", arm.resolved_struct)
                }
                fmt.sbprintf(b, "]")
            } else if arm.dot_shorthand != "" {
                fmt.sbprintf(b, "%s.%s [tag=%d]", arm_indent, arm.dot_shorthand, arm.resolved_tag)
            } else {
                fmt.sbprintf(b, "%s", arm_indent)
                dump_expr(b, arm.value)
            }
            fmt.sbprintln(b, " {")
            for child in arm.body {
                dump_stmt(b, child, depth + 2)
            }
            fmt.sbprintf(b, "%s}\n", arm_indent)
        }
        fmt.sbprintf(b, "%s}\n", indent)

    case ^Stmt_Foreign:
        fmt.sbprintf(b, "%sforeign %s (prefix: %s)\n", indent, s.library, s.prefix)

    case ^Stmt_Union_Def:
        fmt.sbprintf(b, "%sunion_def %s\n", indent, s.name)

    case ^Stmt_Distinct_Def:
        fmt.sbprintf(b, "%sdistinct_def %s\n", indent, s.name)

    case ^Stmt_Dispatch_Def:
        fmt.sbprintf(b, "%sdispatch %s :: [%s]\n", indent, s.name, strings.join(s.functions[:], ", "))

    case Stmt_Overload:
        fmt.sbprintf(b, "%soverload %s %s\n", indent, op_str(s.op), s.dispatch_name)

    case Stmt_Module:
        fmt.sbprintf(b, "%smodule %s\n", indent, s.name)

    case ^Stmt_Decl:
        // Type checker populates s.checked with the underlying Stmt_Assign /
        // Stmt_Multi_Return_Assign nodes. Dump those if present, otherwise
        // fall back to showing the raw parsed shape.
        if len(s.checked) > 0 {
            for inner in s.checked { dump_stmt(b, inner, depth) }
        } else {
            fmt.sbprintf(b, "%s", indent)
            for n, i in s.names {
                if i > 0 { fmt.sbprintf(b, ", ") }
                fmt.sbprintf(b, "%s", n)
            }
            fmt.sbprintln(b, " : ?")
        }
    case ^Stmt_Define:
        fmt.sbprintf(b, "%s%s : %s = ", indent, s.name, type_name(s.var_type))
        dump_expr(b, s.value)
        fmt.sbprintln(b)
    }
}

// Print a statement on a single line (for C-style for init/post)
dump_stmt_inline :: proc(b: ^strings.Builder, stmt: Stmt) {
    #partial switch s in stmt {
    case ^Stmt_Assign:
        if s.target != nil {
            dump_expr(b, s.target)
            fmt.sbprintf(b, " = ")
            dump_expr(b, s.value)
            return
        }
        fmt.sbprintf(b, "%s : %s = ", s.name, type_name(s.var_type))
        dump_expr(b, s.value)
    case:
        fmt.sbprintf(b, "%v", stmt)
    }
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

dump_expr :: proc(b: ^strings.Builder, expr: Expr) {
    switch e in expr {
    case ^Expr_Number:
        if e.is_float {
            fmt.sbprintf(b, "%f:%s", e.value, type_name(e.type_))
        } else {
            fmt.sbprintf(b, "%d:%s", int(e.value), type_name(e.type_))
        }

    case ^Expr_String:
        fmt.sbprintf(b, "\"%s\":%s", e.value, type_name(e.type_))

    case ^Expr_Char:
        fmt.sbprintf(b, "'%c':%s", e.value, type_name(e.type_))

    case ^Expr_Bool:
        fmt.sbprintf(b, "%v:%s", e.value, type_name(e.type_))

    case ^Expr_Uninit:
        fmt.sbprintf(b, "---:%s", type_name(e.type_))

    case ^Expr_Ident:
        fmt.sbprintf(b, "%s:%s", e.name, type_name(e.type_))
        #partial switch r in e.resolved {
        case Resolved_Enum_Variant:
            fmt.sbprintf(b, "[=%s.%s(%d)]", r.enum_name, r.variant, r.value)
        case Resolved_Union_Variant:
            fmt.sbprintf(b, "[=%s.%s(%d)]", r.union_name, r.variant, r.tag_value)
        case Resolved_Constant:
            fmt.sbprintf(b, "[=const %d]", r.int_value)
        case Resolved_Func:
            fmt.sbprintf(b, "[=fn %s]", r.name)
        }

    case ^Expr_Unary:
        fmt.sbprintf(b, "(%v ", e.op)
        dump_expr(b, e.operand)
        fmt.sbprintf(b, "):%s", type_name(e.type_))

    case ^Expr_Binary:
        fmt.sbprintf(b, "(")
        dump_expr(b, e.left)
        fmt.sbprintf(b, " %v ", e.op)
        dump_expr(b, e.right)
        fmt.sbprintf(b, "):%s", type_name(e.type_))
        if rf, ok := e.overload_fn.?; ok {
            fmt.sbprintf(b, "[overload=%s]", rf.name)
        }

    case ^Expr_Call:
        if rf, ok := e.resolved_func.?; ok {
            fmt.sbprintf(b, "%s", rf.name)
        } else {
            fmt.sbprintf(b, "%s", e.name)
        }
        fmt.sbprintf(b, "(")
        for arg, i in e.args {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_expr(b, arg)
        }
        fmt.sbprintf(b, "):%s", type_name(e.type_))

    case ^Expr_Array:
        fmt.sbprintf(b, "[")
        for elem, i in e.elements {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_expr(b, elem)
        }
        fmt.sbprintf(b, "]:%s", type_name(e.type_))

    case ^Expr_Index:
        dump_expr(b, e.expr)
        fmt.sbprintf(b, "[")
        dump_expr(b, e.index)
        fmt.sbprintf(b, "]:%s", type_name(e.type_))

    case ^Expr_Slice:
        dump_expr(b, e.expr)
        fmt.sbprintf(b, "[")
        if e.low != nil { dump_expr(b, e.low) }
        fmt.sbprintf(b, ":")
        if e.high != nil { dump_expr(b, e.high) }
        fmt.sbprintf(b, "]:%s", type_name(e.type_))

    case ^Expr_Struct_Literal:
        if e.name != "" {
            strings.write_string(b, e.name)
        }
        strings.write_string(b, "{{")
        for f, i in e.fields {
            if i > 0 { strings.write_string(b, ", ") }
            strings.write_string(b, f.name)
            strings.write_string(b, ": ")
            dump_expr(b, f.value)
        }
        strings.write_string(b, "}}")
        fmt.sbprintf(b, ":%s", type_name(e.type_))

    case ^Expr_Field_Access:
        dump_expr(b, e.expr)
        fmt.sbprintf(b, ".%s:%s", e.field, type_name(e.type_))
        #partial switch r in e.resolved {
        case Resolved_Enum_Variant:
            fmt.sbprintf(b, "[=%s.%s(%d)]", r.enum_name, r.variant, r.value)
        case Resolved_Constant:
            fmt.sbprintf(b, "[=const %d]", r.int_value)
        }

    case ^Expr_Size_Of:
        fmt.sbprintf(b, "size_of(%v):%s", e.type_expr, type_name(e.type_))

    case ^Expr_Take:
        fmt.sbprintf(b, "take(%v, ", e.type_expr)
        dump_expr(b, e.storage)
        fmt.sbprintf(b, "):%s", type_name(e.type_))

    case ^Expr_If:
        fmt.sbprintf(b, "(if ")
        dump_expr(b, e.condition)
        fmt.sbprintf(b, " do ")
        dump_expr(b, e.then_expr)
        fmt.sbprintf(b, " else ")
        dump_expr(b, e.else_expr)
        fmt.sbprintf(b, ")")

    case ^Expr_Compiler_Intrinsic:
        switch e.kind {
        case .Caller_Name: fmt.sbprintf(b, "#caller_name")
        case .Caller_Span: fmt.sbprintf(b, "#caller_span")
        case .Web:         fmt.sbprintf(b, "#web")
        case .Native:      fmt.sbprintf(b, "#native")
        case .Windows:     fmt.sbprintf(b, "#windows")
        case .Linux:       fmt.sbprintf(b, "#linux")
        case .Mac:         fmt.sbprintf(b, "#mac")
        }
        if e.resolved_value != "" {
            fmt.sbprintf(b, "=\"%s\"", e.resolved_value)
        }

    case ^Expr_Include:
        fmt.sbprintf(b, "include(%s)", e.path)

    case ^Expr_Type_Name:
        fmt.sbprintf(b, "type:%s", type_name(e.type_))

    case nil:
        fmt.sbprintf(b, "<nil>")
    }
}

// ---------------------------------------------------------------------------
// Token_Kind → human-readable operator string
// ---------------------------------------------------------------------------

op_str :: proc(op: Token_Kind) -> string {
    #partial switch op {
    case .Plus:          return "+"
    case .Minus:         return "-"
    case .Star:          return "*"
    case .Slash:         return "/"
    case .Modulo:        return "%"
    case .Equal_Equal:   return "=="
    case .Not_Equal:     return "!="
    case .Less:          return "<"
    case .Less_Equal:    return "<="
    case .Greater:       return ">"
    case .Greater_Equal: return ">="
    case .And:           return "and"
    case .Or:            return "or"
    case .Not:           return "not"
    case .Ampersand:     return "&"
    case .Caret:         return "^"
    case .Pipe:          return "|"
    case .Tilde:         return "~"
    case .Shift_Left:    return "<<"
    case .Shift_Right:   return ">>"
    case .Plus_Equal:    return "+="
    case .Minus_Equal:   return "-="
    case .Mul_Equal:     return "*="
    case .Div_Equal:     return "/="
    case .Mod_Equal:     return "%="
    case .And_Equal:     return "&="
    case .Or_Equal:      return "|="
    case .Xor_Equal:     return "~="
    case .Shift_Left_Equal:  return "<<="
    case .Shift_Right_Equal: return ">>="
    case .Dot_Dot:       return ".."
    }
    return fmt.tprintf("%v", op)
}

// ---------------------------------------------------------------------------
// Type expression (parser-level) formatting
// ---------------------------------------------------------------------------

type_expr_str :: proc(te: Type_Expr) -> string {
    switch v in te {
    case Type_Name:
        return v.name
    case Type_Of_Name:
        return fmt.tprintf("fn %s", v.name)
    case ^Type_Array:
        if v.size_name != "" {
            return fmt.tprintf("[%s]%s", v.size_name, type_expr_str(v.elem))
        }
        return fmt.tprintf("[%d]%s", v.size, type_expr_str(v.elem))
    case ^Type_Pointer:
        return fmt.tprintf("^%s", type_expr_str(v.elem))
    case ^Type_Slice_Expr:
        if v.has_sentinel {
            return fmt.tprintf("[:, %d]%s", v.sentinel, type_expr_str(v.elem))
        }
        return fmt.tprintf("[:]%s", type_expr_str(v.elem))
    case ^Type_Partial_Array_Expr:
        size_str: string
        if v.size_name != "" {
            size_str = v.size_name
        } else {
            size_str = fmt.tprintf("%d", v.size)
        }
        if v.has_sentinel {
            return fmt.tprintf("[..%s, %d]%s", size_str, v.sentinel, type_expr_str(v.elem))
        }
        return fmt.tprintf("[..%s]%s", size_str, type_expr_str(v.elem))
    case ^Type_Tuple_Expr:
        b: strings.Builder
        strings.write_string(&b, "(")
        for elem, i in v.elems {
            if i > 0 { strings.write_string(&b, ", ") }
            strings.write_string(&b, type_expr_str(elem))
        }
        strings.write_string(&b, ")")
        return strings.to_string(b)
    case ^Type_Generic_Instance:
        b: strings.Builder
        strings.write_string(&b, v.name)
        strings.write_string(&b, "(")
        for arg, i in v.type_args {
            if i > 0 { strings.write_string(&b, ", ") }
            strings.write_string(&b, type_expr_str(arg))
        }
        strings.write_string(&b, ")")
        return strings.to_string(b)
    case ^Type_Func_Expr:
        b: strings.Builder
        strings.write_string(&b, "fun(")
        for p, i in v.params {
            if i > 0 { strings.write_string(&b, ", ") }
            strings.write_string(&b, type_expr_str(p))
        }
        strings.write_string(&b, ")")
        if v.return_type != nil {
            strings.write_string(&b, " -> ")
            strings.write_string(&b, type_expr_str(v.return_type))
        }
        return strings.to_string(b)
    case Type_Const_Value:
        return fmt.tprintf("%d", v.value)
    case Type_Const_Expr:
        return "<expr>"
    }
    return "_"
}

// ---------------------------------------------------------------------------
// Parse tree dump — raw AST before type checking
// ---------------------------------------------------------------------------

dump_parse_tree :: proc(program: Program, path: string) -> bool {
    b: strings.Builder

    for stmt in program {
        dump_parse_stmt(&b, stmt, 0)
    }

    output := strings.to_string(b)
    fmt.print(output)

    werr := os.write_entire_file(path, transmute([]u8)output)
    if werr != nil {
        fmt.printf("Error: could not write parse dump to '%s'\n", path)
        return false
    }
    fmt.printf("\nWrote parse dump to '%s'\n", path)
    return true
}

dump_parse_stmt :: proc(b: ^strings.Builder, stmt: Stmt, depth: int) {
    indent := make_indent(depth)

    switch s in stmt {
    case ^Stmt_Assign:
        if s.target != nil {
            fmt.sbprintf(b, "%s", indent)
            dump_parse_expr(b, s.target)
            fmt.sbprintf(b, " = ")
            dump_parse_expr(b, s.value)
            fmt.sbprintln(b)
        } else {
            fmt.sbprintf(b, "%s%s :", indent, s.name)
            te := type_expr_str(s.type_expr)
            if te != "_" { fmt.sbprintf(b, " %s", te) }
            fmt.sbprintf(b, " = ")
            dump_parse_expr(b, s.value)
            fmt.sbprintln(b)
        }

    case ^Stmt_Multi_Assign:
        for a in s.assigns {
            dump_parse_stmt(b, a, depth)
        }

    case ^Stmt_Multi_Return_Assign:
        fmt.sbprintf(b, "%s", indent)
        for name, i in s.names {
            if i > 0 { fmt.sbprintf(b, ", ") }
            if name != "" {
                fmt.sbprintf(b, "%s", name)
            } else if i < len(s.targets) && s.targets[i] != nil {
                dump_expr(b, s.targets[i])
            } else {
                fmt.sbprintf(b, "_")
            }
        }
        te := type_expr_str(s.type_expr)
        if te != "_" {
            fmt.sbprintf(b, " : %s", te)
        }
        fmt.sbprintf(b, " = ")
        for val, i in s.values {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_parse_expr(b, val)
        }
        fmt.sbprintln(b)

    case Stmt_Call:
        fmt.sbprintf(b, "%s", indent)
        dump_parse_expr(b, s.expr)
        fmt.sbprintln(b)

    case ^Stmt_If:
        dump_parse_if_chain(b, s, depth)

    case ^Stmt_For:
        if s.is_collection_for {
            fmt.sbprintf(b, "%sfor ", indent)
            if s.elem_var != "" { fmt.sbprintf(b, "%s", s.elem_var) } else { fmt.sbprintf(b, "_") }
            if s.index_var != "" { fmt.sbprintf(b, ", %s", s.index_var) }
            fmt.sbprintf(b, " in ")
            dump_parse_expr(b, s.collection)
        } else if s.is_range {
            fmt.sbprintf(b, "%sfor %s", indent, s.loop_var)
            te := type_expr_str(s.iter_type)
            if te != "_" { fmt.sbprintf(b, " : %s", te) }
            fmt.sbprintf(b, " in ")
            dump_parse_expr(b, s.range_low)
            fmt.sbprintf(b, "..")
            dump_parse_expr(b, s.range_high)
        } else if s.init != nil {
            fmt.sbprintf(b, "%sfor ", indent)
            dump_parse_stmt_inline(b, s.init)
            fmt.sbprintf(b, "; ")
            dump_parse_expr(b, s.condition)
            fmt.sbprintf(b, "; ")
            dump_parse_stmt_inline(b, s.post)
        } else {
            fmt.sbprintf(b, "%sfor ", indent)
            dump_parse_expr(b, s.condition)
        }
        fmt.sbprintln(b, " {")
        for child in s.body {
            dump_parse_stmt(b, child, depth + 1)
        }
        fmt.sbprintf(b, "%s}\n", indent)

    case ^Stmt_Scope:
        fmt.sbprintf(b, "%s%s :: fun", indent, s.name)
        if len(s.generic_params) > 0 {
            fmt.sbprintf(b, "($")
            for gp, i in s.generic_params {
                if i > 0 { fmt.sbprintf(b, ", $") }
                fmt.sbprintf(b, "%s", gp.name)
                if gp.is_const { fmt.sbprintf(b, ": %s", gp.const_type) }
            }
            fmt.sbprintf(b, ")")
        }
        if len(s.fields) > 0 {
            // Data-type fun (struct-like)
            strings.write_string(b, " {\n")
            for f in s.fields {
                fmt.sbprintf(b, "%s  ", indent)
                if f.is_using { fmt.sbprintf(b, "using ") }
                fmt.sbprintf(b, "%s: %s", f.name, type_expr_str(f.type_expr))
                if f.default_value != nil {
                    fmt.sbprintf(b, " = ")
                    dump_parse_expr(b, f.default_value)
                }
                strings.write_string(b, "\n")
            }
            for child in s.body {
                dump_parse_stmt(b, child, depth + 1)
            }
            fmt.sbprintf(b, "%s}\n", indent)
        } else {
            // Executable fun
            fmt.sbprintf(b, "(")
            for p, i in s.typed_params {
                if i > 0 { fmt.sbprintf(b, ", ") }
                fmt.sbprintf(b, "%s", p.name)
                te := type_expr_str(p.type_expr)
                if te != "_" { fmt.sbprintf(b, ": %s", te) }
            }
            fmt.sbprintf(b, ")")
            ret := type_expr_str(s.return_type)
            if ret != "_" { fmt.sbprintf(b, " -> %s", ret) }
            fmt.sbprintln(b, " {")
            for child in s.body {
                dump_parse_stmt(b, child, depth + 1)
            }
            fmt.sbprintf(b, "%s}\n", indent)
        }

    case Stmt_Return:
        fmt.sbprintf(b, "%sreturn", indent)
        if len(s.values) > 0 {
            fmt.sbprintf(b, " ")
            for val, i in s.values {
                if i > 0 { fmt.sbprintf(b, ", ") }
                dump_parse_expr(b, val)
            }
        }
        fmt.sbprintln(b)

    case Stmt_Break:
        fmt.sbprintf(b, "%sbreak\n", indent)

    case Stmt_Continue:
        fmt.sbprintf(b, "%scontinue\n", indent)

    case ^Stmt_Match:
        fmt.sbprintf(b, "%smatch ", indent)
        dump_parse_expr(b, s.subject)
        fmt.sbprintln(b, " {")
        for arm in s.arms {
            arm_indent := make_indent(depth + 1)
            if arm.is_else {
                fmt.sbprintf(b, "%selse", arm_indent)
            } else if arm.is_union_arm {
                fmt.sbprintf(b, "%s%s", arm_indent, arm.variant_name)
                if arm.binding_name != "" {
                    fmt.sbprintf(b, " %s", arm.binding_name)
                }
            } else if arm.dot_shorthand != "" {
                fmt.sbprintf(b, "%s.%s", arm_indent, arm.dot_shorthand)
            } else {
                fmt.sbprintf(b, "%s", arm_indent)
                dump_parse_expr(b, arm.value)
            }
            fmt.sbprintln(b, " {")
            for child in arm.body {
                dump_parse_stmt(b, child, depth + 2)
            }
            fmt.sbprintf(b, "%s}\n", arm_indent)
        }
        fmt.sbprintf(b, "%s}\n", indent)

    case ^Stmt_Foreign:
        fmt.sbprintf(b, "%sforeign \"%s\"", indent, s.library)
        if s.prefix != "" { fmt.sbprintf(b, " (prefix: %s)", s.prefix) }
        fmt.sbprintln(b, " {")
        for d in s.decls {
            fmt.sbprintf(b, "%s  %s :: fun(", indent, d.name)
            for p, i in d.typed_params {
                if i > 0 { fmt.sbprintf(b, ", ") }
                fmt.sbprintf(b, "%s: %s", p.name, type_expr_str(p.type_expr))
            }
            fmt.sbprintf(b, ")")
            ret := type_expr_str(d.return_type)
            if ret != "_" { fmt.sbprintf(b, " -> %s", ret) }
            fmt.sbprintln(b)
        }
        fmt.sbprintf(b, "%s}\n", indent)


    case ^Stmt_Union_Def:
        fmt.sbprintf(b, "%s%s :: union", indent, s.name)
        if s.tag_type != "" { fmt.sbprintf(b, "(%s)", s.tag_type) }
        if s.min_size > 0 { fmt.sbprintf(b, " [min_size=%d]", s.min_size) }
        strings.write_string(b, " {\n")
        for v in s.variants {
            fmt.sbprintf(b, "%s  %s", indent, v.name)
            if v.has_tag { fmt.sbprintf(b, " = %d", v.tag) }
            if len(v.fields) > 0 {
                strings.write_string(b, " {")
                for f, i in v.fields {
                    if i > 0 { strings.write_string(b, ",") }
                    fmt.sbprintf(b, " %s: %s", f.name, type_expr_str(f.type_expr))
                }
                strings.write_string(b, " }")
            }
            strings.write_string(b, "\n")
        }
        fmt.sbprintf(b, "%s", indent)
        strings.write_string(b, "}\n")

    case ^Stmt_Distinct_Def:
        fmt.sbprintf(b, "%s%s :: distinct %s\n", indent, s.name, type_expr_str(s.base_type))

    case ^Stmt_Dispatch_Def:
        fmt.sbprintf(b, "%s%s :: dispatch ", indent, s.name)
        strings.write_string(b, "{ ")
        strings.write_string(b, strings.join(s.functions[:], ", "))
        strings.write_string(b, " }\n")

    case Stmt_Overload:
        fmt.sbprintf(b, "%soverload %s %s\n", indent, op_str(s.op), s.dispatch_name)

    case Stmt_Module:
        fmt.sbprintf(b, "%smodule %s\n", indent, s.name)

    case ^Stmt_Decl:
        fmt.sbprintf(b, "%s", indent)
        for n, i in s.names {
            if i > 0 { fmt.sbprintf(b, ", ") }
            fmt.sbprintf(b, "%s", n)
        }
        if s.type_expr != nil {
            te := type_expr_str(s.type_expr)
            if te != "_" { fmt.sbprintf(b, " : %s", te) } else { fmt.sbprintf(b, " :") }
        } else {
            fmt.sbprintf(b, " :")
        }
        if len(s.init_values) > 0 {
            fmt.sbprintf(b, "= ")
            for v, i in s.init_values {
                if i > 0 { fmt.sbprintf(b, ", ") }
                dump_parse_expr(b, v)
            }
        }
        fmt.sbprintln(b)
    case ^Stmt_Define:
        fmt.sbprintf(b, "%s%s ::", indent, s.name)
        te := type_expr_str(s.type_expr)
        if te != "_" { fmt.sbprintf(b, " %s", te) }
        fmt.sbprintf(b, " ")
        dump_parse_expr(b, s.value)
        fmt.sbprintln(b)
    }
}

dump_parse_if_chain :: proc(b: ^strings.Builder, s: ^Stmt_If, depth: int, is_else_if: bool = false) {
    indent := make_indent(depth)
    if is_else_if {
        strings.write_string(b, "} else if ")
    } else {
        fmt.sbprintf(b, "%sif ", indent)
    }
    dump_parse_expr(b, s.condition)
    strings.write_string(b, " {\n")
    for child in s.body {
        dump_parse_stmt(b, child, depth + 1)
    }
    if len(s.else_body) > 0 {
        if len(s.else_body) == 1 {
            if nested_if, is_if := s.else_body[0].(^Stmt_If); is_if {
                fmt.sbprintf(b, "%s", indent)
                dump_parse_if_chain(b, nested_if, depth, true)
                return
            }
        }
        fmt.sbprintf(b, "%s", indent)
        strings.write_string(b, "} else {\n")
        for child in s.else_body {
            dump_parse_stmt(b, child, depth + 1)
        }
    }
    fmt.sbprintf(b, "%s", indent)
    strings.write_string(b, "}\n")
}

dump_parse_stmt_inline :: proc(b: ^strings.Builder, stmt: Stmt) {
    #partial switch s in stmt {
    case ^Stmt_Assign:
        if s.target != nil {
            dump_parse_expr(b, s.target)
            fmt.sbprintf(b, " = ")
            dump_parse_expr(b, s.value)
            return
        }
        fmt.sbprintf(b, "%s", s.name)
        te := type_expr_str(s.type_expr)
        if te != "_" { fmt.sbprintf(b, " : %s", te) }
        fmt.sbprintf(b, " = ")
        dump_parse_expr(b, s.value)
    case:
        fmt.sbprintf(b, "%v", stmt)
    }
}

dump_parse_expr :: proc(b: ^strings.Builder, expr: Expr) {
    switch e in expr {
    case ^Expr_Number:
        if e.is_float {
            fmt.sbprintf(b, "%f", e.value)
        } else {
            fmt.sbprintf(b, "%d", int(e.value))
        }

    case ^Expr_String:
        fmt.sbprintf(b, "\"%s\"", e.value)

    case ^Expr_Char:
        if e.value == '\n' { fmt.sbprintf(b, "'\\n'") }
        else if e.value == '\t' { fmt.sbprintf(b, "'\\t'") }
        else if e.value == 0 { fmt.sbprintf(b, "'\\0'") }
        else if e.value == '\\' { fmt.sbprintf(b, "'\\\\'") }
        else if e.value == '\'' { fmt.sbprintf(b, "'\\''") }
        else { fmt.sbprintf(b, "'%c'", e.value) }

    case ^Expr_Bool:
        fmt.sbprintf(b, "%v", e.value)

    case ^Expr_Uninit:
        fmt.sbprintf(b, "---")

    case ^Expr_Ident:
        fmt.sbprintf(b, "%s", e.name)

    case ^Expr_Unary:
        fmt.sbprintf(b, "(%s ", op_str(e.op))
        dump_parse_expr(b, e.operand)
        fmt.sbprintf(b, ")")

    case ^Expr_Binary:
        fmt.sbprintf(b, "(")
        dump_parse_expr(b, e.left)
        fmt.sbprintf(b, " %s ", op_str(e.op))
        dump_parse_expr(b, e.right)
        fmt.sbprintf(b, ")")

    case ^Expr_Call:
        if e.qualifier != nil {
            dump_parse_expr(b, e.qualifier)
            fmt.sbprintf(b, ".")
        }
        fmt.sbprintf(b, "%s(", e.name)
        for arg, i in e.args {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_parse_expr(b, arg)
        }
        fmt.sbprintf(b, ")")

    case ^Expr_Array:
        fmt.sbprintf(b, "[")
        for elem, i in e.elements {
            if i > 0 { fmt.sbprintf(b, ", ") }
            dump_parse_expr(b, elem)
        }
        fmt.sbprintf(b, "]")

    case ^Expr_Index:
        dump_parse_expr(b, e.expr)
        fmt.sbprintf(b, "[")
        dump_parse_expr(b, e.index)
        fmt.sbprintf(b, "]")

    case ^Expr_Slice:
        dump_parse_expr(b, e.expr)
        fmt.sbprintf(b, "[")
        if e.low != nil { dump_parse_expr(b, e.low) }
        fmt.sbprintf(b, ":")
        if e.high != nil { dump_parse_expr(b, e.high) }
        fmt.sbprintf(b, "]")

    case ^Expr_Struct_Literal:
        if e.name != "" { strings.write_string(b, e.name) }
        strings.write_string(b, "{")
        for f, i in e.fields {
            if i > 0 { strings.write_string(b, ", ") }
            strings.write_string(b, f.name)
            strings.write_string(b, ": ")
            dump_parse_expr(b, f.value)
        }
        strings.write_string(b, "}")

    case ^Expr_Field_Access:
        dump_parse_expr(b, e.expr)
        fmt.sbprintf(b, ".%s", e.field)

    case ^Expr_Size_Of:
        fmt.sbprintf(b, "size_of(%s)", type_expr_str(e.type_expr))

    case ^Expr_Take:
        fmt.sbprintf(b, "take(%s, ", type_expr_str(e.type_expr))
        dump_parse_expr(b, e.storage)
        fmt.sbprintf(b, ")")

    case ^Expr_If:
        fmt.sbprintf(b, "(if ")
        dump_parse_expr(b, e.condition)
        fmt.sbprintf(b, " do ")
        dump_parse_expr(b, e.then_expr)
        fmt.sbprintf(b, " else ")
        dump_parse_expr(b, e.else_expr)
        fmt.sbprintf(b, ")")

    case ^Expr_Compiler_Intrinsic:
        switch e.kind {
        case .Caller_Name: fmt.sbprintf(b, "#caller_name")
        case .Caller_Span: fmt.sbprintf(b, "#caller_span")
        case .Web:         fmt.sbprintf(b, "#web")
        case .Native:      fmt.sbprintf(b, "#native")
        case .Windows:     fmt.sbprintf(b, "#windows")
        case .Linux:       fmt.sbprintf(b, "#linux")
        case .Mac:         fmt.sbprintf(b, "#mac")
        }

    case ^Expr_Include:
        fmt.sbprintf(b, "include(%s)", e.path)

    case ^Expr_Type_Name:
        fmt.sbprintf(b, "type:%s", type_name(e.type_))

    case nil:
        fmt.sbprintf(b, "<nil>")
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

make_indent :: proc(depth: int) -> string {
    @(static) indents := [?]string{
        "",
        "  ",
        "    ",
        "      ",
        "        ",
        "          ",
        "            ",
        "              ",
        "                ",
        "                  ",
        "                    ",
    }
    if depth <= 0 { return "" }
    if depth < len(indents) { return indents[depth] }
    return indents[len(indents) - 1]
}
