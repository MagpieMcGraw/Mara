package mara

import "core:fmt"
import "core:strings"

// Parse-level formatting helpers used by the type checker when it needs
// to quote a source expression back to the user in a diagnostic
// (e.g. a comparison chain like `a < b < c` is reformatted into the
// `(a < b) and (b < c)` shape so the message reads with the right
// associativity). The two `_str` helpers convert Token_Kind ops and
// Type_Expr ASTs to source-like text; dump_parse_expr walks an Expr
// tree and writes a readable form into the caller's builder.
//
// Nothing here is wired to a CLI flag — the dump_checked_program and
// dump_parse_tree entry points were removed along with the `-dump`
// option since they hadn't been used. Anything that needs to inspect
// post-type-check state can read the AST directly or revisit those
// dumpers from git history.

// Source-level representation of a binary/unary operator token.
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

// Source-level representation of a parser Type_Expr. Recursive — handles
// arrays, slices, partial arrays, pointers, tuples, generic instances,
// function types.
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
            return fmt.tprintf("[, %d]%s", v.sentinel, type_expr_str(v.elem))
        }
        return fmt.tprintf("[]%s", type_expr_str(v.elem))
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

// Walk an Expr (parser AST) and write a readable, source-like form into
// `b`. Used by check_error sites that want to quote an expression back
// to the user (currently only the comparison-chain reformatter; other
// diagnostics can use it freely).
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

    case ^Expr_Skip_Constructor:
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

    case ^Expr_Tuple_Default:
        fmt.sbprintf(b, "tuple_default[%d](", e.index)
        dump_parse_expr(b, e.source)
        fmt.sbprintf(b, ")")

    case ^Expr_Self:
        fmt.sbprintf(b, "#self")

    case nil:
        fmt.sbprintf(b, "<nil>")
    }
}
