package mara

import "core:fmt"
import "core:strings"

// ============================================================
// Diagnostic queue — buffered emission with explicit flush
// ============================================================
//
// Every error and warning the compiler emits goes through emit_diagnostic
// here. The message is formatted (printf-style) at the call site and
// stashed on g_diagnostics; nothing prints until flush_diagnostics() is
// called. This keeps inline error/warning text from interleaving with
// the streaming perf-timer phase prints — main.odin flushes at well-
// defined points (after perf_timer_end on success, before each abort
// summary on failure). codegen_fatal flushes itself before os.exit.

Diagnostic_Kind :: enum {
    Parse_Error,
    Type_Error,
    Warning,
    Codegen_Error,
}

Diagnostic :: struct {
    kind:     Diagnostic_Kind,
    location: string, // "file:line:col", or "" for codegen with no source span
    message:  string, // already-formatted message body (printf applied)
}

@(private="file")
g_diagnostics: [dynamic]Diagnostic

// Queue one diagnostic. msg + args are formatted now (so the args
// don't have to outlive the call); the resulting string lives until
// flush. Order at flush time is the order emitted.
emit_diagnostic :: proc(kind: Diagnostic_Kind, location: string, msg: string, args: ..any) {
    body := fmt.aprintf(msg, ..args)
    append(&g_diagnostics, Diagnostic{kind = kind, location = location, message = body})
}

// Print every queued diagnostic and clear the queue. Safe to call
// multiple times — second call has nothing to print.
flush_diagnostics :: proc() {
    for d in g_diagnostics {
        label: string
        switch d.kind {
        case .Parse_Error:   label = "Parse error"
        case .Type_Error:    label = "Type error"
        case .Warning:       label = "Warning"
        case .Codegen_Error: label = "Codegen error"
        }
        if d.location != "" {
            fmt.printf("[%s] %s: %s\n", d.location, label, d.message)
        } else {
            fmt.printf("%s: %s\n", label, d.message)
        }
    }
    clear(&g_diagnostics)
}

// All compiler diagnostics — errors and warnings — live in this file.
// Call sites reference these constants; edits to wording happen here only.
//
// Each constant is the **body** of the message — the location prefix
// (`[file:line:col] `), the phase tag (`Parse error: `, `Type error: `,
// `Warning: `, etc.), and the trailing newline are added by the emit
// helper for that phase (parse_error / check_error / check_warning /
// codegen_fatal). Format placeholders (%s, %d, %v, ...) are passed
// positionally at the call site, same as before.
//
// Naming:
//   PARSE_<topic>     — parser errors  → parse_error
//   TYPE_<topic>      — type-checker errors → check_error
//   CODE_<topic>      — codegen fatals → codegen_fatal
//   WARN_<topic>      — warnings (any phase) → check_warning
//
// The TODO of writing every message in a single authorial voice
// happens by editing the strings below in place. No call sites
// need to change when wording shifts.

// ============================================================
// Parser-AST formatting helpers — quote source back at the user
// ============================================================
//
// Used by check_error sites that need to reformat a parsed expression
// or type back into source-shape text (e.g. the comparison-chain
// reformatter at type_checker.odin's chained-comparison handling
// turns `a < b < c` into `(a < b) and (b < c)` for the diagnostic).

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
        return fmt.tprintf("[]%s", type_expr_str(v.elem))
    case ^Type_Partial_Array_Expr:
        size_str: string
        if v.size_name != "" {
            size_str = v.size_name
        } else {
            size_str = fmt.tprintf("%d", v.size)
        }
        return fmt.tprintf("[..%s]%s", size_str, type_expr_str(v.elem))
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
        if len(v.return_types) > 0 {
            strings.write_string(&b, " -> ")
            for rt, i in v.return_types {
                if i > 0 { strings.write_string(&b, ", ") }
                strings.write_string(&b, type_expr_str(rt))
            }
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
// `b`. The companion to op_str/type_expr_str for expressions.
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

    case ^Expr_Assert:
        fmt.sbprintf(b, "assert(%s)", e.cond_text)

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
        kw := e.keyword if e.keyword != "" else "let"
        fmt.sbprintf(b, "%s(%s, ", kw, type_expr_str(e.type_expr))
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

    case ^Expr_Try:
        dump_parse_expr(b, e.inner)
        fmt.sbprintf(b, "?")

    case nil:
        fmt.sbprintf(b, "<nil>")
    }
}

// ============================================================
// Parser errors
// ============================================================

PARSE_EXPECTED_TOKEN              :: "expected %v, got %v \"%s\""
PARSE_EXPECTED_INTRINSIC_AFTER_AT :: "expected intrinsic name part after `@`, got `%s`"
PARSE_EXPECTED_INTRINSIC_AFTER_DOT :: "expected intrinsic name part after `.`, got `%s`"
PARSE_BARE_INTRINSIC_REMOVED      :: "bare `intrinsic` body is no longer supported — use `{{ @llvm.<name> }}` instead"
PARSE_MALFORMED_USE_INCLUDE       :: "malformed use/include statement"
PARSE_EXPOSE_NEEDS_FUN_DECL       :: "`#expose` must precede a `name :: fun(...)` declaration"
PARSE_PACKED_NEEDS_STRUCT_DECL    :: "`#packed` goes after '::', as in `Name :: #packed struct`"
PARSE_SENTINEL_REMOVED            :: "sentinel arrays were removed — use the plain array/slice type; cstring conversion writes the terminator at the FFI boundary"
TYPE_CSTRING_FOREIGN_ONLY         :: "`cstring` is the C boundary type — only `foreign` signatures may declare it. Take `[]utf8` and convert at the C call with `cstring(s)`"
TYPE_CSTRING_ARG_EXPLICIT         :: "a runtime string doesn't convert to `cstring` implicitly — wrap the argument: `cstring(s)` copies it and writes the terminator. String literals pass free"
TYPE_CSTRING_CTOR_ARGUMENT        :: "cstring() takes a utf8/byte string (slice, partial array, or literal), got %s"
TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL :: "cannot take the address of a string literal — its bytes are read-only. Bind it first (`s := \"...\"`) for a mutable copy"
TYPE_SLICE_CANNOT_BIND_STRING_LITERAL :: "a string literal is `[..N]utf8` storage, not a `[]utf8` view — a slice here would alias read-only bytes. Use `s := \"...\"` for a mutable copy, or `[:N]utf8` to copy into sized backing"
PARSE_BIG_ENDIAN_NEEDS_BYTE_READ  :: "`#big_endian` must precede a byte-buffer read — `buf[off]` or `buf[lo:hi]`"
PARSE_USING_NOT_ALLOWED_ON_INCLUDE :: "`using` is not allowed before `use`/`include` — use bare `use %s` (private) or `include %s` (re-export), or `name :: use path` for qualified access"
PARSE_INCLUDE_NEEDS_COLON_COLON   :: "`:=` is not allowed for `use`/`include` — modules are comptime, use `name :: use path` (private) or `name :: include path` (re-export)"
PARSE_UNEXPECTED_TOKEN_STMT       :: "unexpected token %v \"%s\" (expected statement)"
PARSE_DEFAULT_VALUE_COUNT_MISMATCH :: "%d default values for %d names (expected 0, 1, or %d)"
PARSE_UNION_TAG_NEEDS_TYPE        :: "expected type after `tag` in union header, got `%s`"
PARSE_UNION_SIZE_NEEDS_NUM        :: "expected number after `size` in union header, got `%s`"
PARSE_UNION_HEADER_UNKNOWN        :: "union header takes `$T: type`, `tag <type>`, `pad <type>`, `size <N>`; got `%s`"
PARSE_OVERLOAD_EXPECTED_OP        :: "expected operator after 'overload', got '%s'"
PARSE_FOREIGN_NEEDS_STATIC_LIB    :: "foreign block needs `static_lib`, got `%s`"
PARSE_NESTED_IF_EXPR              :: "nested if-expressions are not allowed"
PARSE_RANGE_FOR_ONE_VAR           :: "range-for loop takes one variable, not two"
PARSE_EXPECTED_TYPE               :: "expected type, got %v \"%s\""
PARSE_TUPLE_TYPE_NOT_SUPPORTED    :: "tuple types are not supported — multiple types in parens are only valid in a function's return signature"
PARSE_RANGE_NEEDS_DOTS            :: "expected '..' after `%sin` in range-membership check"
PARSE_STRUCT_LIT_MIXED_FIELDS     :: "struct literal cannot mix positional and named fields"
PARSE_HEX_OVERFLOWS_U64           :: "hex literal '%s' overflows u64 (max 0xFFFFFFFFFFFFFFFF) — Mara's integer-literal precision tops out at 64 bits"
PARSE_DECIMAL_OVERFLOWS_U64       :: "integer literal '%s' overflows u64 (max 18446744073709551615) — Mara's integer-literal precision tops out at 64 bits"
PARSE_INVALID_NUMBER              :: "invalid number '%s'"
PARSE_EXPECTED_VARIANT_NAME       :: "expected variant name after '.'"
PARSE_UNEXPECTED_LBRACE_IN_EXPR   :: "unexpected '{' in expression"
PARSE_EXPECTED_HASH_NAME          :: "expected intrinsic name after '#'"
PARSE_UNKNOWN_INTRINSIC           :: "unknown compiler intrinsic '#%s'"
PARSE_SEALED_NEEDS_USE_INCLUDE    :: "expected `use` or `include` after `sealed`, got `%s`"
PARSE_UNEXPECTED_TOKEN            :: "unexpected token %v \"%s\""
PARSE_STRAY_ELSE                  :: "stray `else` — braces go around the entire if/else block, with `else` inside. Try `if cond {{ body else body }}` instead of `if cond {{ body }} else {{ body }}`."
PARSE_AMBIGUOUS_AMPERSAND         :: "ambiguous '&' — spaced like the start of a new statement (`&name`) but it parses as binary AND continuing the previous expression. Start the address-of/append on its own line, or space it as `a & b` if AND was meant."

// ============================================================
// Type-checker errors and warnings — populated in next pass.
// ============================================================

TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS :: "'.%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s"
TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS :: "Move '%s' below all of the declarations in this class. Trust me."
TYPE_WON_GET_AUTO_CONSTRUCTED_DECLARED :: "'%s' won't get auto-constructed when declared inside of an array. Promise me that you will write valid data to '%s' before you try to read from it."
TYPE_TYPE_SELF_CONSTRUCTING_CALL_LIKE :: "'%s' of type '%s' is self-constructing — call it like a function with the required arguments. Definition: %s. Try: '%s : %s = %s(...)'"
TYPE_ONLY_VALID_TYPE_GENERIC_PARAMETER :: "`~%s` only valid as the type of a generic parameter (e.g. `Foo :: struct (s: ~%s)`)"
TYPE_TYPE_INT_RESERVED_USE_I64 :: "type 'int' is reserved — use 'i64' (or 'isize' for word-sized)"
TYPE_TYPE_UINT_RESERVED_USE_U64 :: "type 'uint' is reserved — use 'u64' (or 'usize' for word-sized)"
TYPE_TYPE_NAME_AMBIGUOUS_DEFINED_USE :: "type name '%s' is ambiguous (defined in: %s). Use a qualified path or seal one of the includes (e.g. `name :: sealed include ...`)."
TYPE_UNKNOWN_TYPE :: "unknown type '%s'"
TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE :: "array size must be a compile-time constant (element type %s) — pick a fixed upper bound"
TYPE_ARRAY_SIZE_CONSTANT_COMPILE_TIME :: "array size constant '%s' is not a compile-time integer"
TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2 :: "array size '%s' must be a compile-time constant (element type %s) — pick a fixed upper bound"
TYPE_PARTIAL_ARRAY_SIZE_CONSTANT_COMPILE :: "partial-array size constant '%s' is not a compile-time integer"
TYPE_EXPECTS_TYPE_ARGUMENT :: "'%s' expects %d type argument(s), got %d"
TYPE_STRUCT_CLASS_CONSTRUCTOR_PARAMS_GENERIC :: "'%s' is a struct/class with constructor params, not a generic type — construct in expression position instead: `field : %s = %s(...)` or `field := %s(...)`"
TYPE_FN_REQUIRES_FUNCTION_VALUED_NAME :: "'fn %s' requires a function-valued name; '%s' has type %s"
TYPE_UNKNOWN_FUNCTION_FN :: "unknown function '%s' in 'fn %s'"
TYPE_UNKNOWN_GENERIC_TYPE :: "unknown generic type '%s'"
TYPE_ARGUMENT_CONST_GENERIC_PARAMETER_REQUIRES :: "argument %d to '%s': const generic parameter '%s' requires a compile-time integer"
TYPE_REQUIRES_GENERIC_PARAMETER_DEFAULT :: "'%s' requires generic parameter '%s' (no default)"
TYPE_COULD_INFER_TYPE_PARAMETER_CALL :: "could not infer type parameter '$%s' in call to '%s'"
TYPE_FAILED_INSTANTIATE_GENERIC_FUNCTION :: "failed to instantiate generic function '%s'"
TYPE_EXPECTS_ARGUMENT :: "'%s' expects %d argument(s), got %d"
TYPE_SHAPE_CONSTRAINT_GENERIC_PARAMETER_COULD :: "shape constraint '%s' on generic parameter '%s' could not be resolved"
TYPE_GENERIC_ARGUMENT_CONCRETE_STRUCT_CLASS :: "generic argument for '%s: ~%s' must be a concrete struct/class, got %s"
TYPE_TYPE_SATISFY_MISSING_METHOD :: "type '%s' does not satisfy `~%s`: missing method '%s'"
TYPE_TYPE_SATISFY_METHOD_EXPECTS_LEAST :: "type '%s' does not satisfy `~%s`: method '%s' expects at least %d param(s), got %d"
TYPE_TYPE_SATISFY_METHOD_EXTRA_PARAM :: "type '%s' does not satisfy `~%s`: method '%s' has extra param '%s' without a default value"
TYPE_TYPE_SATISFY_METHOD_PARAM_EXPECTED :: "type '%s' does not satisfy `~%s`: method '%s' param '%s' expected %s, got %s"
TYPE_TYPE_SATISFY_METHOD_EXPECTED_RETURN :: "type '%s' does not satisfy `~%s`: method '%s' expected return %s, got %s"
TYPE_TYPE_FIT_SIZE_BUDGET_NEEDS :: "type '%s' does not fit `~%s` size budget: needs %d bytes, slot is %d bytes"
TYPE_CANNOT_RETURN_RESULT_RETURN_REFERENCE :: "cannot return result of `%s(...)`: its return may reference local memory via %s — pass caller-rooted %s instead"
TYPE_CANNOT_RETURN_LOCAL_REFERENCE_MEMORY :: "cannot return local reference (memory freed on function return)"
TYPE_CONSTANT_OVERFLOWS_RANGE :: "constant %d overflows %s (range %d..%d)"
TYPE_CONSTANT_OVERFLOWS_RANGE_128 :: "constant %d overflows %s (range 0..2^128-1)"
TYPE_CONSTANT_OVERFLOWS_RANGE_2 :: "constant %d overflows %s (range 0..%d)"
TYPE_CONSTANT_OVERFLOWS_F16 :: "constant %v overflows f16"
TYPE_CONSTANT_OVERFLOWS_F32 :: "constant %v overflows f32"
TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN :: "struct/class '%s' without constructor parameters cannot declare a return type (only a parameterized constructor may return, e.g. a trailing err)"
TYPE_ENUM_ALREADY_DEFINED :: "enum '%s' already defined"
TYPE_UNION_ALREADY_DEFINED :: "union '%s' already defined"
TYPE_ALREADY_DEFINED :: "%s '%s' already defined"
TYPE_TYPE_ALREADY_DEFINED :: "type '%s' already defined"
TYPE_PARAM_TYPE_SKIP_CONSTRUCTOR_REQUIRES :: "param '%s' has no type — `#skip_constructor` requires an explicit type annotation (e.g. `%s : T = #skip_constructor`)"
TYPE_FUNCTION_ALREADY_DEFINED :: "function '%s' already defined"
TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN :: "#if condition must be a comptime-known boolean"
TYPE_MODULE_FOUND :: "module '%s' not found"
TYPE_VARIABLE_ALREADY_DECLARED_SCOPE :: "variable '%s' already declared in this scope"
TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING :: "variable '%s' shadows an enclosing binding"
TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE :: "variable '%s' shadows a constant from an outer scope"
TYPE_CANNOT_ASSIGN_VARIABLE_TYPE :: "cannot assign %s to variable '%s' of type %s"
TYPE_CANNOT_ASSIGN_VARIABLE_TYPE_FROM :: "cannot assign %s to variable '%s' of type %s — from %s"
TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE :: "declaration without initializer requires a type annotation"
TYPE_ARRAY_TOO_LARGE_STACK_BYTES :: "array '%s' is too large for the stack (%d bytes). Set up a scope allocator in main:\n\n    include mara.memory\n    program = Program(Arena_Basic)"
TYPE_SIZE_EXPRESSION_INTEGER :: "size expression must be an integer, got %s"
TYPE_SLICE_CAPACITY_INTEGER :: "slice capacity must be an integer, got %s"
TYPE_CANNOT_COPY_VALUE_CONTAINS_PARTIAL :: "cannot copy '%s' by value — it contains a partial-array field whose `ptr` would still alias the source's elements after the copy; construct in place or assign individual fields"
TYPE_BYTE_BUFFER_READ_BYTES_SLICE :: "byte buffer read: %s is %d bytes, but slice span is %d bytes"
TYPE_BIG_ENDIAN_NEEDS_BYTE_BUFFER :: "#big_endian requires a byte-buffer source, got `%s`"
TYPE_FIELD_ASSIGN_THROUGH_RECEIVER :: "'%s' is a field of '%s'; assign through the receiver (e.g. 'a.%s = ...')"
TYPE_TYPE_SKIP_CONSTRUCTOR_REQUIRES_EXPLICIT :: "'%s' has no type — `#skip_constructor` requires an explicit type annotation (e.g. `%s : T = #skip_constructor`)"
TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING :: "variable '%s' has no concrete type (type checking bypassed)"
TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE :: "multi-return assign: left side has %d names but right side returns %d values"
TYPE_CANNOT_ASSIGN_MULTI_RETURN :: "cannot assign %s to %s in multi-return"
TYPE_MULTI_RETURN_ASSIGN_REQUIRES_FUNCTION :: "multi-return assign requires a function returning multiple values, got %s"
TYPE_DEFAULT_VALUE_FIELD_EXPECTED :: "default value for field '%s': expected %s, got %s"
TYPE_BROADCAST_LITERAL_ALL_FIELD_REQUIRES :: "broadcast literal '{all ...}' for field '%s' requires an array type, got %s"
TYPE_BROADCAST_VALUE_FIELD_TYPE_EXPECTED :: "broadcast value for field '%s' has type %s, expected %s (element of %s)"
TYPE_FIELD_TYPE_SKIP_CONSTRUCTOR_REQUIRES :: "field '%s' has no type — `#skip_constructor` requires an explicit type annotation (e.g. `%s : T = #skip_constructor`)"
TYPE_USING_FIELD_STRUCT_FIXED_ARRAY :: "using field '%s' must be a struct or fixed-array type"
TYPE_FUNCTION_MISSING_RETURN_ALL_CODE :: "function '%s' missing return on all code paths"
TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE :: "cannot iterate over struct type '%s'"
TYPE_CANNOT_ITERATE_OVER_TYPE :: "cannot iterate over type '%s'"
TYPE_RANGE_LOWER_BOUND_NUMERIC :: "range lower bound must be numeric, got %s"
TYPE_RANGE_UPPER_BOUND_NUMERIC :: "range upper bound must be numeric, got %s"
TYPE_CONDITION_BOOL :: "for condition must be bool, got %s"
TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN :: "multi-value return in function that doesn't return a tuple"
TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED :: "return value count %d does not match expected %d"
TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED :: "return value %d: type %s does not match expected %s"
TYPE_RETURN_TYPE_MATCH_EXPECTED :: "return type %s does not match expected %s"
TYPE_CANNOT_RETURN_STRUCT_WHOSE_SLICE :: "cannot return struct whose slice fields point at local memory; the escape mechanism only applies to direct `return Lit[local_arr, ...]` forms (memory freed on function return)"
TYPE_CONDITION_BOOL_2 :: "if condition must be bool, got %s"
TYPE_INVALID_ASSIGNMENT_TARGET :: "invalid assignment target"
TYPE_DISCARDED_RETURN :: "return value of '%s' is discarded — capture it (`x := ...`) or discard it explicitly (`_ = ...`)"
TYPE_DISPATCH_GROUP_FUNCTION :: "dispatch group '%s': '%s' is not a function"
TYPE_DISPATCH_GROUP_FUNCTION_DEFINED :: "dispatch group '%s': function '%s' not defined"
TYPE_OVERLOAD_DISPATCH_GROUP :: "overload: '%s' is not a dispatch group"
TYPE_CANNOT_ASSIGN_CONSTANT_TYPE :: "cannot assign %s to constant '%s' of type %s"
TYPE_CANNOT_WRITE_INDEXED_CONSTANT :: "cannot write through `::` constant '%s' — the value lives in read-only memory. Declare it as a variable (`%s := ...`) if you need to mutate it"
TYPE_INDEX_OUT_OF_BOUNDS_CONST :: "index %d out of bounds — array has %d elements (valid indices 0..%d)"
TYPE_CLASS_FIELDS_POSITIONAL_VALUES :: "class '%s' has %d fields, got %d positional values"
TYPE_FIELD_POSITION_EXPECTED :: "field '%s' (position %d): expected %s, got %s"
TYPE_FIELD_EXPECTED :: "field '%s': expected %s, got %s"
TYPE_CLASS_FIELD :: "class '%s' has no field '%s'"
TYPE_UNION_REQUIRES_NAMED_VARIANT_VARIANT :: "union '%s' requires a named variant, e.g. Variant { ... }"
TYPE_VARIANT_UNION :: "'%s' is not a variant of union '%s'"
TYPE_BROADCAST_VALUE_TYPE_EXPECTED :: "'%s' broadcast value has type %s, expected %s"
TYPE_EXPECTS_POSITIONAL_VALUES :: "'%s' expects %d positional values, got %d"
TYPE_ELEMENT_TYPE_EXPECTED :: "'%s' element %d has type %s, expected %s"
TYPE_FIELD_USE_SWIZZLE_COMPONENTS_WITHIN :: "'%s' has no field '%s' (use swizzle components x/y/z/w or r/g/b/a within [0..<%d])"
TYPE_FIELD_SET_MORE_THAN_ONCE :: "'%s' field '%s' set more than once"
TYPE_FIELD_TYPE_EXPECTED :: "'%s' field '%s' has type %s, expected %s"
TYPE_ARRAY_ELEMENTS_CAPACITY :: "array has %d elements but '%s' has capacity %d"
TYPE_CANNOT_ASSIGN_THROUGH_POINTER :: "cannot assign %s through pointer to %s"
TYPE_CANNOT_DEREFERENCE_ASSIGN_NON_POINTER :: "cannot dereference-assign to non-pointer type %s"
TYPE_CANNOT_WRITE_LOCAL_REFERENCE_THROUGH :: "cannot write local reference through parameter '%s' (would escape function scope)"
TYPE_ARRAY_INDEX_NUMBER :: "array index must be a number, got %s"
TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER :: "cannot write to element of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_ASSIGN_ELEMENT :: "cannot assign %s to element of [%d]%s"
TYPE_CANNOT_ASSIGN_ELEMENT_TYPE :: "cannot assign %s to element of %s (add an explicit cast)"
TYPE_SLICE_LOWER_BOUND_NUMBER :: "slice lower bound must be a number, got %s"
TYPE_SLICE_UPPER_BOUND_NUMBER :: "slice upper bound must be a number, got %s"
TYPE_CANNOT_SLICE_ASSIGN_INTO_IMMUTABLE :: "cannot slice-assign into immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_BYTE_SLICE_WRITE_BYTES_SLICE :: "byte slice write: %s is %d bytes, but slice span is %d bytes"
TYPE_BYTE_ARRAY_WRITE_BYTES_SLICE :: "byte array write: %s is %d bytes, but slice span is %d bytes"
TYPE_CANNOT_SLICE_ASSIGN_INTO :: "cannot slice-assign [%d]%s into [%d]%s"
TYPE_CANNOT_SLICE_ASSIGN_INTO_2 :: "cannot slice-assign []%s into [%d]%s"
TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE :: "slice assignment requires an array or slice on the right-hand side, got %s"
TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER :: "cannot write to field '%s' of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_ASSIGN_FIELD_TYPE :: "cannot assign %s to %s of type %s"
TYPE_INFER_CONFLICTING_WIDTHS :: "inferred binding '%s' is used at conflicting widths: %s at %s and %s at %s — annotate it with an explicit type"
TYPE_CANNOT_WRITE_LOCAL_REFERENCE_FIELD :: "cannot write local reference to field '%s' of parameter '%s' (would escape function scope)"
TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPE :: "cannot assign %s to swizzle '%s' of element type %s"
TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPES :: "cannot assign %s to swizzle '%s': element types differ"
TYPE_CANNOT_ASSIGN_MULTI_COMPONENT_SWIZZLE :: "cannot assign %s to multi-component swizzle '%s': expected array"
TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY :: "swizzle '%s' has component out of range for [%d] array"
TYPE_LAST_ARM_MATCH :: "'else' must be the last arm in a match"
TYPE_ENUM_VARIANT :: "enum '%s' has no variant '%s'"
TYPE_UNION_VARIANT :: "union '%s' has no variant '%s'"
TYPE_DOT_SHORTHAND_ONLY_USED_MATCHING :: "dot shorthand '.%s' can only be used when matching on an enum or union"
TYPE_MATCH_MISSING_VARIANT_ADD_ARM :: "match on '%s' is missing variant '%s' (add an arm, or `else` to opt out)"
TYPE_MATCH_ERR_REQUIRES_ELSE :: "match on `err` requires an `else` arm — the error universe is open, so exhaustive matching is impossible"
TYPE_TRY_OPERAND_MUST_BE_CALL :: "`?` propagation can only be applied to a call expression"
TYPE_TRY_REQUIRES_ERR_RETURN :: "`?` requires the called function's trailing return slot to be an error type"
TYPE_TRY_OUTSIDE_ERR_FUNCTION :: "`?` can only be used inside a function whose trailing return slot is an error type"
TYPE_TRY_TOO_MANY_VALUES :: "`?` on a call with %d non-error return values isn't supported yet (only single-value or err-only)"
TYPE_ALLOWED_MATCH_STRUCT_ARMS_FIRE :: "'else' is not allowed in match on a struct — arms fire independently, so there is no single 'no match' branch"
TYPE_MATCH_STRUCT_EXPECTS_PREDICATE_ARMS :: "match on struct '%s' expects predicate arms (`field do …` or `expr do …`)"
TYPE_PREDICATE_ARM_BOOL_MARA_DOESN :: "predicate arm must be bool, got %s — Mara doesn't auto-truthy non-bool values; write an explicit comparison"
TYPE_CIRCULAR_INCLUDE_MODULE_ALREADY_CHECKED :: "circular include: module '%s' is already being checked"
TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY :: "foreign symbol '%s' is already declared in library '%s' (first declaration at %s); each external symbol may be bound by at most one foreign block"
TYPE_PROGRAM_GLOBAL_REQUIRES_ALLOCATOR_TYPE :: "program global requires an allocator type (e.g. `program = Program(Arena_Basic(<args>))`)"
TYPE_PROGRAM_SCOPE_ALLOCATOR_KNOWN_TYPE :: "program scope allocator: '%s' is not a known type"
TYPE_PROGRAM_SCOPE_ALLOCATOR_MISSING_REQUIRED :: "program scope allocator: '%s' is missing required function '%s'"
TYPE_FUN_MAIN_RETURN_INT_RETURN :: "fun main() must return int or have no return type"
TYPE_FUN_MAIN_TAKE_PARAMETERS :: "fun main() must take no parameters"
TYPE_EXPOSE_FUNCTION_TAKE_FIRST_PARAMETER :: "#expose function '%s' must take its first parameter as `^Program`"
TYPE_EXECUTABLE_STATEMENTS_INSIDE_FUN_MAIN :: "executable statements must be inside fun main()"
TYPE_VISIBLE_ENUM_UNION_VARIANT :: "no visible enum or union has variant '.%s'"
TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED :: "constant '%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s"
TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE :: "variable '%s' is used before being assigned a value"
TYPE_FIELD_ACCESS_THROUGH_RECEIVER :: "'%s' is a field of '%s'; access it through the receiver (e.g. 'a.%s')"
TYPE_TYPE_VALUE_DID_MEAN :: "'%s' is a type, not a value. Did you mean ': %s'?"
TYPE_UNDEFINED_IDENTIFIER :: "undefined identifier '%s'"
TYPE_STRUCT_LITERAL_NAME_NOT_STRUCT :: "'%s{{...}}': '%s' does not name a struct type"
TYPE_STRUCT_COPY_FORM :: "'%s' is a struct variable — copy-with-overrides ('new := %s{{...}}') is not supported. Copy first ('new := %s'), then override in place ('new{{...}}')"
TYPE_CANNOT_NEGATE :: "cannot negate %s"
TYPE_CANNOT_NEGATE_UNSIGNED :: "cannot negate unsigned %s — no representable result; widen to signed first (e.g. -i64(x))"
TYPE_CANNOT_APPLY :: "cannot apply 'not' to %s"
TYPE_CANNOT_APPLY_REQUIRES_INTEGER_TYPE :: "cannot apply '~' to %s, requires integer type"
TYPE_CANNOT_TAKE_ADDRESS_IMMUTABLE_PARAMETER :: "cannot take address of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE :: "cannot dereference non-pointer type %s"
TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED :: "typed array literal: type %s is not a fixed-size array"
TYPE_SIZE_UNKNOWN_TYPE :: "size_of: unknown type"
TYPE_TAKE_UNKNOWN_TYPE :: "let/slice: unknown type"
TYPE_TAKE_COUNT_INTEGER :: "slice count must be an integer, got %s"
TYPE_TAKE_COUNT_REQUIRES_SLICE_TYPE :: "slice([:N]T, ...) requires a slice type, got %s"
TYPE_TAKE_REQUIRES_BYTE_CURSOR_FORM :: "let/slice requires ^[]byte (cursor form, pass &slice_var) or ^byte (positional form), got %s"
TYPE_TAKE_STORAGE_POINTS_INTO_LOCAL :: "let/slice storage points into local stack memory, which would not outlive a returning view"
TYPE_EXPRESSION_CONDITION_BOOL :: "if-expression condition must be bool, got %s"
TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS :: "if-expression branches have incompatible types: %s vs %s"
TYPE_TUPLE_DESTRUCTURE_INDEX_OUT_RANGE :: "tuple-destructure index %d out of range for %d-tuple"
TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT :: "#self is only legal inside a struct/class body"
TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE :: "field '%s' of '%s' is used before being assigned a value"
TYPE_FIELD_ALIASED_VIA_USED_BEFORE :: "field '%s' of '%s' (aliased via '%s') is used before being assigned a value"
TYPE_UNION_TAG_ENUM_INTERNAL_ERROR :: "union '%s' has no tag enum (internal error)"
TYPE_UNION_PADDING_DECLARE_UNION_PAD :: "union '%s' has no padding (declare with `union(... pad T ...)`)"
TYPE_MODULE_SYMBOL :: "module '%s' has no symbol '%s'"
TYPE_CANNOT_ACCESS_FIELD_ARRAY_TYPE :: "cannot access field '%s' on array type %s"
TYPE_SLICE_TYPE_FIELD :: "slice type %s has no field '%s'"
TYPE_PARTIAL_ARRAY_TYPE_FIELD :: "partial array type %s has no field '%s'"
TYPE_CANNOT_ACCESS_FIELD_TYPE :: "cannot access field '%s' on type %s"
TYPE_EXPECTS_ARGUMENT_2 :: "%s() expects %d argument%s, got %d"
TYPE_LEN_EXPECTS_ARGUMENT :: "len() expects 1 argument, got %d"
TYPE_LEN_REQUIRES_ARRAY_SLICE :: "len() requires array or slice, got %s"
TYPE_CAP_EXPECTS_ARGUMENT :: "cap() expects 1 argument, got %d"
TYPE_CAP_REQUIRES_ARRAY_SLICE :: "cap() requires array or slice, got %s"
TYPE_PRINT_FORMAT_STRING_PLACEHOLDER_VALUE :: "print format string has %d `%%` placeholder(s) but %d value(s) were passed"
TYPE_CRASH_EXPECTS_ARGUMENTS :: "crash() expects 0 or 1 arguments, got %d"
TYPE_PRINT_CSTR_EXPECTS_ARGUMENT_BYTE :: "print_cstr() expects 1 argument (^byte), got %d"
TYPE_PRINT_INT_EXPECTS_ARGUMENT_INT :: "print_int() expects 1 argument (int), got %d"
TYPE_PRINT_FLOAT_EXPECTS_ARGUMENT_FLOAT :: "print_float() expects 1 argument (float), got %d"
TYPE_SLICE_PTR_EXPECTS_ARGUMENTS_PTR :: "slice_from_ptr() expects 2 arguments (ptr, size), got %d"
TYPE_SLICE_PTR_FIRST_ARGUMENT_POINTER :: "slice_from_ptr() first argument must be a pointer, got %s"
TYPE_SLICE_PTR_SECOND_ARGUMENT_NUMERIC :: "slice_from_ptr() second argument must be numeric, got %s"
TYPE_SLICE_PTR_SECOND_ARGUMENT_WIDTH :: "slice_from_ptr() second argument must be %s to match slice header width, got %s — add an explicit cast"
TYPE_INDEX_WIDTH :: "array/slice index must be %s to match slice header width, got %s — add an explicit cast"
TYPE_SLICE_PTR_OUTSIDE_OS_MODULE :: "slice_from_ptr() outside the os module requires a comptime-known size "
TYPE_EXPECTS_ARGUMENT_3 :: "%s() expects 1 argument, got %d"
TYPE_LEFT_OPERAND_BOOL :: "left operand of '%s' must be bool, got %s"
TYPE_DID_MEAN_EACH_OPERAND_NEEDS :: "did you mean `%s`? Each operand of `%s` needs its own comparison."
TYPE_RIGHT_OPERAND_BOOL :: "right operand of '%s' must be bool, got %s"
TYPE_CANNOT_COMPARE_USING :: "cannot compare %s with %s using '%s'"
TYPE_LEFT_OPERAND_COMPARISON_NUMERIC :: "left operand of comparison must be numeric, got %s"
TYPE_RIGHT_OPERAND_COMPARISON_NUMERIC :: "right operand of comparison must be numeric, got %s"
TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT :: "mismatched types for '+': %s and %s - did you forget to import the package that defines the overload?"
TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2 :: "mismatched types for '%s': %s and %s - did you forget to import the package that defines the overload?"
TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS :: "bitwise operators require integer operands, got %s"
TYPE_MISMATCHED_TYPES_ARITHMETIC_USE_EXPLICIT :: "mismatched types in arithmetic: %s and %s (use an explicit cast)"
TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER :: "argument %d of '%s': '_' requires a default value, but parameter '%s' has none"
TYPE_EXPECTS_ARGS :: "'%s' expects %d args, got %d"
TYPE_ARGUMENT_EXPECTED :: "argument %d%s of '%s': parameter '%s' expects %s, got %s"
TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE :: "method '%s' requires a pointer receiver — take an address with `&` (or use a `^%s` local) before calling"
TYPE_MODULE_FUNCTION :: "module '%s' has no function '%s'"
TYPE_MATCHING_FUNCTION_DISPATCH_GROUP_ARGUMENT :: "no matching function in dispatch group '%s' for argument types (%s)"
TYPE_AMBIGUOUS_DISPATCH_MATCHES_MULTIPLE_OVERLOADS :: "ambiguous dispatch '%s' — matches multiple overloads: %s"
TYPE_UNDEFINED_FUNCTION :: "undefined function '%s'"
TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE :: "cannot construct %s from %s; underlying type is %s"
TYPE_FUNCTION :: "'%s' is not a function"
TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED :: "function '%s' is ambiguous (defined in: %s). Use a qualified call (e.g. `%s.%s(...)`) or seal one of the includes."
TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID :: "'%s' field-override block is only valid on struct construction"
TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_FIELD :: "argument %d of '%s': '_' requires a default value, but field '%s' has none"
TYPE_FIELD_ARGUMENT :: "'%s' has %d field(s), got %d argument(s)"
TYPE_REQUIRES_LEAST_ARGUMENT :: "'%s' requires at least %d argument(s), got %d"
TYPE_ARRAY_ELEMENT_TYPE_EXPECTED :: "array element %d has type %s, expected %s"
TYPE_INDEX_NUMBER :: "index must be a number, got %s"
TYPE_CANNOT_INDEX_INTO :: "cannot index into %s"
TYPE_CANNOT_SLICE :: "cannot slice %s"
TYPE_SLICE_LOW_BOUND_NUMERIC :: "slice low bound must be numeric, got %s"
TYPE_SLICE_HIGH_BOUND_NUMERIC :: "slice high bound must be numeric, got %s"


// ============================================================
// Codegen fatals — populated in next pass.
// ============================================================

CODE_DLL_EXPOSE_FN_USES_ARENA :: "DLL with #expose fn(s) uses arena-needing code but no allocator type is declared — add `program = Program(ArenaType(<args>))` somewhere in this module to specify the Context layout (must match the host's allocator type)"
CODE_ARENA_ALLOCATION_REQUESTED_SCOPE_ALLOCATOR :: "arena allocation requested but no scope_allocator declared"
CODE_ARRAY :: "'%s' is not an array"
CODE_INDEX_ASSIGNMENT_TARGET_VARIABLE :: "index assignment target must be a variable"
CODE_SLICE_ASSIGNMENT_TARGET_VARIABLE :: "slice assignment target must be a variable"
CODE_ARRAY_ARRAY_CLASS_SLICE :: "'%s' is not an array, array class, or slice"
CODE_ARRAY_SLICE :: "'%s' is not an array or slice"
CODE_SLICE_RHS_NAMED_ARRAY_SLICE :: "slice RHS must be a named array, slice, or array literal"
CODE_INDEX_TARGET_VARIABLE :: "index target must be a variable"
CODE_CANNOT_TAKE_ADDRESS_INDEX_EXPRESSION :: "cannot take address of this index expression"
CODE_POSITIONAL_TAKE_REQUIRES_BUF_SOURCE :: "positional let/slice requires a &buf[i] source (byte slice or [N]byte) so the carve can be bounds-checked"
CODE_TAKE_STORAGE_SLICE_VAR_SLICE :: "let/slice storage must be &slice_var or a slice-pointer parameter"
CODE_TAKE_SLICE_VARIABLE :: "let/slice: '%s' is not a slice variable"
CODE_SLICE_TARGET_VARIABLE :: "slice target must be a variable"
CODE_SLICE_TARGET_ARRAY_SLICE :: "slice target is not an array or slice"
CODE_BYTE_VIEW_SOURCE_BYTE_SLICE :: "byte view source must be a byte slice or [N]byte"
CODE_BYTE_BUFFER_WRITE_TARGET_BYTE :: "byte buffer write target must be a byte slice or [N]byte"
CODE_BYTE_BUFFER_READ_SOURCE_BYTE :: "byte buffer read source must be a byte slice or [N]byte"
CODE_COLLECTION_REQUIRES_IDENTIFIER_FIELD_ACCESS :: "collection-for requires an identifier or field access"
CODE_UNKNOWN_COLLECTION_VARIABLE :: "unknown collection variable '%s'"
CODE_UNDEFINED_VARIABLE :: "undefined variable '%s'"
CODE_CANNOT_TAKE_ADDRESS_EXPRESSION :: "cannot take the address of this expression — `&` needs a named variable (or a field/element of one), not a temporary value"
CODE_CANNOT_TAKE_ADDRESS_SLICE_TEMP :: "cannot take the address of a temporary slice — `buf[a:b]` builds a fresh slice header with no address to point at. To pass it to a `^[]T` parameter, bind it first (`s := buf[a:b]; f(&s)`), or — if the callee only reads it — make the parameter `[]T` and pass the slice directly (no `&`)"
CODE_TUPLE_DEFAULT_INDEX_OUT_RANGE :: "tuple-default index %d out of range"
CODE_CALL_UNKNOWN_FUNCTION_FUN_INFO :: "call to unknown function '%s' — no fun_info and no function-pointer variable"
CODE_FORMAT_STRING_MORE_PLACEHOLDERS_THAN :: "format string has more `%%` placeholders than args"
CODE_PRINT_ARRAY_EXPRESSION_DID_RESOLVE :: "print: array expression did not resolve to an Array_Var"
CODE_PRINT_UNSUPPORTED_VALUE :: "print: no print rule for a value of type %s"
CODE_CANNOT_MATCH_KIND_UNION_EXPRESSION :: "cannot match on this kind of union expression"
CODE_PARTIAL_ARRAY_INITIALIZER_STRING_LITERAL :: "partial array '%s' initializer must be a string literal or another partial array, got %s"
CODE_BREAK_OUTSIDE_LOOP :: "break outside of loop"
CODE_CONTINUE_OUTSIDE_LOOP :: "continue outside of loop"
CODE_DEFER_OUTSIDE_ANY_SCOPE :: "defer outside of any scope"
CODE_MULTI_ASSIGN_RHS_VALUES :: "multi-assign has no RHS values"
CODE_MULTI_ASSIGN_RHS_FUNCTION_CALL :: "multi-assign RHS must be a function call"
CODE_MULTI_ASSIGN_CALL_DID_PRODUCE :: "multi-assign call did not produce tuple results"
CODE_STRUCT_MULTI_RETURN_TARGET_EXPRESSION :: "struct in multi-return can't target an expression yet"
CODE_MULTI_RETURN_TARGET_FIELD_ACCESS :: "multi-return target field access — cannot resolve struct"
CODE_STRUCT_FIELD :: "struct '%s' has no field '%s'"
CODE_INDEX_TARGET_MULTI_RETURN_ASSIGN :: "index target in multi-return assign not yet supported"
CODE_UNARY_OP_VALID_MULTI_RETURN :: "unary op '%v' is not a valid multi-return target"
CODE_UNSUPPORTED_MULTI_RETURN_TARGET_EXPRESSION :: "unsupported multi-return target expression"
CODE_SPREAD_SET_LIT_FIELDS_CALL :: "is_spread set but lit.fields[0] is not a call"
CODE_STRUCT_LITERAL_UNTYPED_EXPR :: "struct literal in expression position has no resolved struct type — codegen cannot materialize it (would otherwise silently pass a null pointer)"
CODE_SPREAD_CALL_TUPLE_RETURN_INFO :: "spread call has no tuple return info"
CODE_ADDRESS_CHAIN_ENDED_SLICE_STEPS :: "address chain ended at .Slice with no steps — cannot determine elem type"
CODE_ADDRESS_CHAIN_ENDED_SLICE_LAST :: "address chain ended at .Slice but last step is not a field — cannot determine elem type"
CODE_ADDRESS_CHAIN_ENDED_SLICE_LAST_2 :: "address chain ended at .Slice but last field is neither Type_Slice nor Type_Partial_Array"
CODE_FIELD_ARRAY_ELEMENT_VALID_SWIZZLE :: "field '.%s' on array element is not a valid swizzle and not a struct field"
CODE_FIELD_ACCESS_INDEXED_ELEMENT_UNKNOWN :: "field access '.%s' on indexed element of unknown shape"
CODE_FIELD_ACCESS_TARGET_VARIABLE :: "field access target must be a variable"
CODE_STRUCT_POINTER_STRUCT :: "'%s' is not a struct or pointer to struct"
CODE_CLASS_FIELD :: "class '%s' has no field '%s'"
CODE_GEN_STRUCT_STORE_UNKNOWN_STRUCT :: "gen_struct_store_at: unknown struct '%s'"
CODE_GEN_STORE_ARRAY_UNHANDLED_RHS :: "gen_store_array_into: unhandled RHS expression shape — codegen has no path for this kind of value flowing into a fixed-array destination"
CODE_GEN_RETURN_ARRAY_UNHANDLED_VALUE :: "gen_return_array: unhandled return value shape for a fixed-array return — codegen has no path to materialize this value into the return slot (would otherwise silently return a zeroed array)"
CODE_CANNOT_ASSIGN_SLICE_FIELD_ONLY :: "cannot assign to slice field '.%s' (only .len and .cap)"
CODE_ARRAY_VALID_SWIZZLE_USE_XYZW :: "'%s' is an array — '.%s' is not a valid swizzle (use xyzw/rgba, indices 0-3)"
CODE_FIELD_STRUCT_ARRAY :: "'%s' has no field '%s' (not a struct or array)"
CODE_FIELD_ASSIGNMENT_TARGET_STRUCT_POINTER :: "field assignment target must be a struct or pointer to struct"
CODE_MULTI_COMPONENT_SWIZZLE_WRITE_REQUIRES :: "multi-component swizzle write requires array source"
CODE_UNION_ASSIGNMENT_REQUIRES_NAMED_STRUCT :: "union assignment requires named struct literal"
CODE_VARIANT_UNION :: "'%s' is not a variant of union '%s'"


// ============================================================
// Build / orchestration messages (main.odin, dump.odin)
//
// Different shape from the rest — no Span, no error counter. Each
// constant is the FULL string passed to fmt.printf at the call site
// (prefix, format placeholders, trailing newline). The convention
// is "Error: " for hard failures and "Found ... Aborting." for
// summary counts; both styles are kept verbatim until the user
// rewrites them.
// ============================================================

BUILD_CLANG_FAILED                :: "Error: clang failed to compile '%s'\n"
BUILD_ARCHIVE_FAILED              :: "Error: archive creation failed for '%s'\n"
BUILD_FOREIGN_FILE_NOT_FOUND      :: "Error: foreign file '%s' not found under %s\n"
BUILD_FORCED_RECOMPILE_FAILED     :: "Error: forced recompile of '%s' failed\n"
BUILD_STATIC_LIB_FAILED           :: "Error: failed to build static lib from '%s'\n"
BUILD_NO_EMCC_EQUIVALENT          :: "Error: foreign library '%s' has no known emscripten equivalent.\n"
BUILD_FOREIGN_SOURCE_NOT_FOUND    :: "Error: foreign source '%s' not found under code/\n"
BUILD_PARSE_ERRORS_ABORT          :: "Found %d parse error(s) in '%s'. Aborting.\n"
BUILD_NO_ENTRY_POINT              :: "Error: package '%s' has no `main` and no `#expose` function. Add an entry point, or pass `-shared` to build an empty DLL.\n"
BUILD_TYPE_ERRORS_ABORT           :: "Found %d type error(s). Aborting.\n"
