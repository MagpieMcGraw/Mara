package mara

import "core:fmt"
import "core:slice"
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
    Graph_Error,     // building the program graph (graph.odin) — a compiler bug
}

Diagnostic :: struct {
    kind:     Diagnostic_Kind,
    location: string, // "file:line:col", or "" for codegen with no source span
    message:  string, // already-formatted message body (printf applied)
    at:       Token_Id, // where, as a token: what diagnostics_sort orders by (0: nowhere)
}

@(private="file")
g_diagnostics: [dynamic]Diagnostic

// Where take_diagnostics also puts what it takes, when somewhere: a check
// that keeps its diagnostics by place (mara lsp publishes them).
@(private="file")
g_keep: ^[dynamic]Diagnostic

// What's taken from now on kept in `into` too (diagnostics_keep_end stops).
diagnostics_keep :: proc(into: ^[dynamic]Diagnostic) {
    g_keep = into
}

// Keeping stopped — what's queued still, untaken, kept first: a check that
// went well leaves its warnings queued.
diagnostics_keep_end :: proc() {
    if g_keep != nil { append(g_keep, ..g_diagnostics[:]) }
    g_keep = nil
}

// The queue let go of, unread: a new check's (mara serve) starts its own.
reset_diagnostics :: proc() {
    g_diagnostics = {}
}

// Queue one diagnostic. msg + args are formatted now (so the args
// don't have to outlive the call); the resulting string lives until
// flush. Order at flush time is the order emitted.
emit_diagnostic :: proc(kind: Diagnostic_Kind, location: string, msg: string, args: ..any) {
    body := fmt.aprintf(msg, ..args)
    // (Its own copy of where: a location is often a temporary string, and a
    // phase's scratch is let go of before the queue is printed.)
    append(&g_diagnostics, Diagnostic{kind = kind, location = strings.clone(location), message = body})
}

// Queue a diagnostic at a place unless the same one is queued there already;
// whether it was queued.
emit_diagnostic_once :: proc(kind: Diagnostic_Kind, span: Span, msg: string, args: ..any) -> bool {
    body := fmt.aprintf(msg, ..args)
    location := span_location(span)
    for d in g_diagnostics {
        if d.kind == kind && d.location == location && d.message == body { return false }
    }
    append(&g_diagnostics, Diagnostic{kind = kind, location = strings.clone(location), message = body, at = span.at})
    return true
}

// A diagnostic at a place.
emit_diagnostic_at :: proc(kind: Diagnostic_Kind, span: Span, msg: string, args: ..any) {
    body := fmt.aprintf(msg, ..args)
    append(&g_diagnostics, Diagnostic{kind = kind, location = strings.clone(span_location(span)), message = body, at = span.at})
}

// How many diagnostics are queued: where a phase's begin (diagnostics_sort).
diagnostics_count :: proc() -> int {
    return len(g_diagnostics)
}

// The diagnostics queued since `from` in source order: by the token each is
// at — a file's in order, the files as they were read — those at the same
// place as they were queued. (A check's: the order it meets them in is its
// own business.)
diagnostics_sort :: proc(from: int) {
    if from >= len(g_diagnostics) { return }
    slice.stable_sort_by(g_diagnostics[from:], proc(a, b: Diagnostic) -> bool { return a.at < b.at })
}

// Print every queued diagnostic and clear the queue. Safe to call
// multiple times — second call has nothing to print.
flush_diagnostics :: proc() {
    fmt.print(take_diagnostics())
}

// The queued diagnostics as text, one a line — taken: the queue is empty
// after. (A check that fails says what's wrong with them first.)
take_diagnostics :: proc() -> string {
    b := strings.builder_make()
    for d in g_diagnostics {
        label: string
        switch d.kind {
        case .Parse_Error:   label = "Parse error"
        case .Type_Error:    label = "Type error"
        case .Warning:       label = "Warning"
        case .Codegen_Error: label = "Codegen error"
        case .Graph_Error:   label = "Graph error"
        }
        if d.location != "" {
            fmt.sbprintf(&b, "[%s] %s: %s\n", d.location, label, d.message)
        } else {
            fmt.sbprintf(&b, "%s: %s\n", label, d.message)
        }
    }
    if g_keep != nil { append(g_keep, ..g_diagnostics[:]) }
    clear(&g_diagnostics)
    return strings.to_string(b)
}

// All compiler diagnostics — errors and warnings — live in this file.
// Call sites reference these constants; edits to wording happen here only.
//
// Each constant is the **body** of the message — the location prefix
// (`[file:line:col] `), the phase tag (`Parse error: `, `Type error: `,
// `Warning: `, etc.), and the trailing newline are added by the emit
// helper for that phase (tp_error / check_error / check_warning /
// codegen_fatal). Format placeholders (%s, %d, %v, ...) are passed
// positionally at the call site.
//
// Naming:
//   PARSE_<topic>     — parser errors  → tp_error
//   TYPE_<topic>      — type-checker errors → check_error
//   CODE_<topic>      — codegen fatals → codegen_fatal
//   WARN_<topic>      — warnings (any phase) → check_warning
//
// The TODO of writing every message in a single authorial voice
// happens by editing the strings below in place. No call sites
// need to change when wording shifts.

// ============================================================
// Operators as written — quoting source back at the user
// ============================================================

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

PARSE_EXPECTED_TOKEN              :: "expected %v, got %v \"%s\""
PARSE_LIST_DOTS                   :: "a list is written `[n]T` now, no `..` — up to n (an array of exactly n: `[n!]T`)"
PARSE_ASSIGN_TO_RESULT            :: "can't assign to what a call gives back: it's a value, gone after the line — a pointer it gives is written through with `^`: `next(&list)^ = …`"
PARSE_EXPECTED_INTRINSIC_AFTER_AT :: "expected intrinsic name part after `@`, got `%s`"
PARSE_EXPECTED_INTRINSIC_AFTER_DOT :: "expected intrinsic name part after `.`, got `%s`"
PARSE_BARE_INTRINSIC_REMOVED      :: "bare `intrinsic` body is no longer supported — use `{{ @llvm.<name> }}` instead"
PARSE_EXPOSE_NEEDS_FUN_DECL       :: "`#expose` must precede a `name :: fun(...)` declaration"
PARSE_PACKED_NEEDS_STRUCT_DECL    :: "`#packed` goes after '::', as in `Name :: #packed struct`"
PARSE_SENTINEL_REMOVED            :: "sentinel arrays were removed — use the plain array/slice type; cstring conversion writes the terminator at the FFI boundary"
PARSE_SKIP_CONSTRUCTOR_REMOVED    :: "`#skip_constructor` was removed — initialize with `void` instead: `x : T = void` declares x uninitialized"
TYPE_VOID_INIT_REQUIRES_EXPLICIT  :: "`%s := void` has no type to infer — annotate it: `%s : T = void` declares uninitialized storage"
TYPE_CSTRING_FOREIGN_ONLY         :: "`cstring` is the C boundary type — only `foreign` signatures may declare it. Take `[]utf8` and convert at the C call with `cstring(s)`"
TYPE_CSTRING_ARG_EXPLICIT         :: "a runtime string doesn't convert to `cstring` implicitly — wrap the argument: `cstring(s)` copies it and writes the terminator. String literals pass free"
TYPE_CSTRING_CTOR_ARGUMENT        :: "cstring() takes a utf8/byte string (slice, partial array, or literal), got %s"
TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL :: "cannot take the address of a string literal — its bytes are read-only. Bind it first (`s := \"...\"`) for a mutable copy"
TYPE_SLICE_CANNOT_BIND_STRING_LITERAL :: "a string literal is `[N]utf8` storage, not a `[]utf8` view — a slice here would alias read-only bytes. Use `s := \"...\"` for a mutable copy, or `s : [N]utf8 = \"...\"` for one with room to grow"
PARSE_BIG_ENDIAN_NEEDS_BYTE_READ  :: "`#big_endian` must precede a byte-buffer read — `buf[off]` or `buf[lo:hi]`"
PARSE_USING_NOT_ALLOWED_ON_INCLUDE :: "`using` is not allowed before `use`/`include` — use bare `use %s` (private) or `include %s` (re-export), or `name :: use path` for qualified access"
PARSE_INCLUDE_NEEDS_COLON_COLON   :: "`:=` is not allowed for `use`/`include` — modules are comptime, use `name :: use path` (private) or `name :: include path` (re-export)"
PARSE_UNEXPECTED_TOKEN_STMT       :: "unexpected token %v \"%s\" (expected statement)"
PARSE_DEFAULT_VALUE_COUNT_MISMATCH :: "%d default values for %d names (expected 0, 1, or %d)"
PARSE_UNION_TAG_NEEDS_TYPE        :: "expected type after `tag` in union header, got `%s`"
PARSE_UNION_SIZE_NEEDS_NUM        :: "expected number after `size` in union header, got `%s`"
PARSE_UNION_HEADER_UNKNOWN        :: "union header takes `$T: type`, `tag <type>`, `pad <type>`, `size <N>`; got `%s`"
TYPE_VARIANT_NEEDS_ARGS           :: "'%s' is built by its params: write `%s(…)`"
TYPE_VARIANT_TAKES_NO_ARGS        :: "'%s' has no params: write `%s%s` or `.%s`"
PARSE_VARIANT_INTRINSIC_BODY      :: "a union variant's body is its fields, not an intrinsic"
PARSE_OVERLOAD_EXPECTED_OP        :: "expected operator after 'overload', got '%s'"
PARSE_TYPE_KEYWORD_ALIAS          :: "`type` isn't written for another name of a type any more: `Name :: T` (`Label :: [16]utf8`, `Fixed :: i32`)"
PARSE_FOREIGN_NEEDS_STATIC_LIB    :: "foreign block needs `static_lib`, got `%s`"
PARSE_NESTED_IF_EXPR              :: "nested if-expressions are not allowed"
PARSE_MATCH_NEEDS_SUBJECT         :: "match needs a subject value to dispatch on — write `match <union-value> {{ ... }}`; subject-less `match {{ }}` was removed, use if/elif for predicate branching"
PARSE_RANGE_FOR_ONE_VAR           :: "range-for loop takes one variable, not two"
PARSE_EXPECTED_TYPE               :: "expected type, got %v \"%s\""
PARSE_TUPLE_TYPE_NOT_SUPPORTED    :: "tuple types are not supported — multiple types in parens are only valid in a function's return signature"
PARSE_RANGE_NEEDS_DOTS            :: "expected '..' after `%sin` in range-membership check"
PARSE_STRUCT_LIT_MIXED_FIELDS     :: "struct literal cannot mix positional and named fields"
PARSE_HEX_OVERFLOWS_U64           :: "hex literal '%s' overflows u64 (max 0xFFFFFFFFFFFFFFFF) — Mara's integer-literal precision tops out at 64 bits"
PARSE_DECIMAL_OVERFLOWS_U64       :: "integer literal '%s' overflows u64 (max 18446744073709551615) — Mara's integer-literal precision tops out at 64 bits"
PARSE_BINARY_OVERFLOWS_U64        :: "binary literal '%s' overflows u64 (more than 64 bits) — Mara's integer-literal precision tops out at 64 bits"
PARSE_INVALID_NUMBER              :: "invalid number '%s'"
LEX_UNTERMINATED_COMMENT          :: "a `/*` comment that never ends — each `/*` needs its `*/` (they nest: one inside another needs its own)"
LEX_UNKNOWN_ESCAPE                :: `unknown escape '\%c' — the escapes are \n \t \r \0 \\ \' \"  (for a literal backslash, write \\)`
PARSE_EXPECTED_VARIANT_NAME       :: "expected variant name after '.'"
PARSE_UNEXPECTED_LBRACE_IN_EXPR   :: "unexpected '{{' in expression"
PARSE_EXPECTED_HASH_NAME          :: "expected intrinsic name after '#'"
PARSE_UNKNOWN_INTRINSIC           :: "unknown compiler intrinsic '#%s'"
PARSE_UNEXPECTED_TOKEN            :: "unexpected token %v \"%s\""
PARSE_BANG_NOT                    :: "`!` is no operator in Mara: negate with `not`"
PARSE_TYPE_AS_VALUE               :: "the type '%s' is no value"
PARSE_STRAY_ELSE                  :: "stray `else` — braces go around the entire if/else block, with `else` inside. Try `if cond {{ body else body }}` instead of `if cond {{ body }} else {{ body }}` — or, after `if cond do s`, `else do s`."
PARSE_AMBIGUOUS_AMPERSAND         :: "ambiguous '&' — spaced like the start of a new statement (`&name`) but it parses as binary AND continuing the previous expression. Start the address-of/append on its own line, or space it as `a & b` if AND was meant."

// ============================================================
// Type-checker errors and warnings
// ============================================================

TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS :: "'%s%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s"
TYPE_AMBIGUOUS_VARIANT_LITERAL :: "ambiguous variant '%s' (defined in: %s) — qualify it as %s.%s{{...}} or annotate the binding's type"
TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS :: "Move '%s' below all of the declarations in this class. Trust me."
TYPE_ONLY_VALID_TYPE_GENERIC_PARAMETER :: "`~%s` only valid as the type of a generic parameter (e.g. `Foo :: struct (s: ~%s)`)"
TYPE_TYPE_INT_RESERVED_USE_I64 :: "type 'int' is reserved — use 'i64' (or 'isize' for word-sized)"
TYPE_TYPE_UINT_RESERVED_USE_U64 :: "type 'uint' is reserved — use 'u64' (or 'usize' for word-sized)"
TYPE_TYPE_NAME_AMBIGUOUS_DEFINED_USE :: "type name '%s' is ambiguous (defined in: %s). Use a qualified path: name the module (`m :: use ...`) and write `m.%s`."
TYPE_UNKNOWN_TYPE :: "unknown type '%s'"
TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE :: "array size must be a compile-time constant (element type %s) — pick a fixed upper bound"
TYPE_ARRAY_SIZE_CONSTANT_COMPILE_TIME :: "array size constant '%s' is not a compile-time integer"
TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2 :: "array size '%s' must be a compile-time constant (element type %s) — pick a fixed upper bound"
TYPE_EXPECTS_TYPE_ARGUMENT :: "'%s' expects %d type argument(s), got %d"
TYPE_STRUCT_CLASS_CONSTRUCTOR_PARAMS_GENERIC :: "'%s' is a struct/class with constructor params, not a generic type — construct in expression position instead: `field : %s = %s(...)` or `field := %s(...)`"
TYPE_FN_REQUIRES_FUNCTION_VALUED_NAME :: "'fn %s' requires a function-valued name; '%s' has type %s"
TYPE_UNKNOWN_FUNCTION_FN :: "unknown function '%s' in 'fn %s'"
TYPE_COULD_INFER_TYPE_PARAMETER_CALL :: "could not infer type parameter '$%s' in call to '%s'"
TYPE_GENERIC_PARAM_POINTER :: "could not infer type parameter '$%s' in call to '%s': its param '%s' takes a pointer, and %s isn't one — pass its address, %s"
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
TYPE_RETURN_TEXT_AS_SLICE :: "can't return text written here as a %s: text given back is copied into the caller's room, not a view of the program's literals — say how much room it gets: `-> str64` (str256, any `[N]utf8`)"
TYPE_RETURN_ARRAY_AS_SLICE :: "can't return %s as a %s: an array doesn't turn into a view when it's given back — return it as itself (`-> %s`), or write the view you mean (`x[:]`, of memory that outlives the call)"
TYPE_ESCAPE_STORE :: "reference to %s would escape into `%s`, which outlives it"
TYPE_ESCAPE_STORE_ANON :: "reference to %s would escape into memory that outlives it"
TYPE_ESCAPE_CALL_STORE :: "`%s(...)` stores its `%s` argument into its `%s` argument: reference to %s would escape into memory that outlives it"
TYPE_ESCAPE_CALL_STORE_GLOBAL :: "`%s(...)` stores its `%s` argument into global memory: reference to %s would escape"
TYPE_CONSTANT_DEFINED_ITSELF :: "constant '%s' is defined in terms of itself"
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
TYPE_FUNCTION_ALREADY_DEFINED :: "function '%s' already defined"
TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN :: "#if condition must be a comptime-known boolean"
TYPE_MODULE_FOUND :: "module '%s' not found"
TYPE_DECLARATION_NAMES_PARAM :: "'%s' is already a param of %s: give this %s a name of its own"
TYPE_VARIABLE_ALREADY_DECLARED_SCOPE :: "variable '%s' already declared in this scope"
TYPE_ASSIGN_UNDECLARED_VARIABLE :: "cannot assign to '%s' — it is not declared in this scope; use ':=' to declare it"
TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING :: "variable '%s' shadows an enclosing binding"
TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE :: "variable '%s' shadows a constant from an outer scope"
TYPE_CANNOT_ASSIGN_VARIABLE_TYPE :: "cannot assign %s to variable '%s' of type %s"
TYPE_CANNOT_ASSIGN_VARIABLE_TYPE_FROM :: "cannot assign %s to variable '%s' of type %s — from %s"
TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE :: "declaration without initializer requires a type annotation"
TYPE_VALUE_TOO_LARGE_STACK_BYTES :: "value '%s' is too large for the stack (%d bytes). Route big values through the program's arena — add `include mara.memory`, then at the module's top:\n\n    #allocator Arena_Basic(64 * MB)"
TYPE_SIZE_EXPRESSION_INTEGER :: "size expression must be an integer, got %s"
TYPE_SLICE_COUNT_SPELLING :: "'%s(n)' is no type: n of %s are written `[:n]%s` (a slice of n)"
TYPE_SLICE_ALIAS_CAPACITY :: "a slice has no storage of its own, so a type can't carry a count: slice an array that has the room, `a[0:n]`"
TYPE_SLICE_SIZED_DECLARATION :: "'%s' is declared a sized slice, but a slice has no storage of its own: declare an array with the room, `a : [N!]%s`, and slice it, `a[0:n]`"
TYPE_BYTE_BUFFER_READ_BYTES_SLICE :: "byte buffer read: %s is %d bytes, but slice span is %d bytes"
TYPE_BYTE_READ_REFERENCE :: "cannot read a `%s` out of bytes: %s — a slice header taken from bytes has a garbage length and pointer, which bounds checks would then trust"
TYPE_BYTE_READ_SLICE_BY_INDEX :: "cannot read a `%s` out of bytes: a slice is a (len, cap, ptr) header, not data — to view the bytes, slice them: bytes[lo:hi]"
TYPE_BYTE_WRITE_REFERENCE :: "cannot write a `%s` into bytes: %s — its bytes are a pointer and lengths, not the data it views"
TYPE_VOID_INTO_POINTER :: "cannot store `void` in %s, a `%s`: a pointer always points at something — `void` only de-initializes a variable, or passes a C function a null"
TYPE_BYTE_VIEW_WIDE_ELEM :: "a range of bytes can only be viewed as a slice of byte / utf8 / u8 / i8, not as `%s` — to view the bytes as %s, use slice([:n]%s, &bytes[lo])"
TYPE_BIG_ENDIAN_NEEDS_BYTE_BUFFER :: "#big_endian requires a byte-buffer source, got `%s`"
TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING :: "variable '%s' has no concrete type (type checking bypassed)"
TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE :: "multi-return assign: left side has %d names but right side returns %d values"
TYPE_CANNOT_ASSIGN_MULTI_RETURN :: "cannot assign %s to %s in multi-return"
TYPE_FROM_TEXT_NEEDS_ZERO :: "%s needs a variant of %s written `= 0` — what it gives when the text names none (e.g. `none = 0`)"
TYPE_RETURN_SEVERAL_COUNT :: "a call returning %d values can't be returned whole from a fun returning %d — take them apart first (`a, b := %s(…)`) and return the ones it returns"
TYPE_MULTI_RETURN_AS_ONE :: "a call returning %d values can't be used as a single value — destructure it first (e.g. `a, b := %s`)"
TYPE_BROADCAST_LITERAL_ALL_FIELD_REQUIRES :: "broadcast literal '{{all ...}}' for field '%s' requires an array type, got %s"
TYPE_BROADCAST_VALUE_FIELD_TYPE_EXPECTED :: "broadcast value for field '%s' has type %s, expected %s (element of %s)"
TYPE_USING_FIELD_STRUCT_FIXED_ARRAY :: "using field '%s' must be a struct or fixed-array type"
TYPE_FUNCTION_MISSING_RETURN_ALL_CODE :: "function '%s' missing return on all code paths"
TYPE_UNREACHABLE_CODE :: "unreachable code: it follows a return, break or continue"
TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE :: "cannot iterate over struct type '%s'"
TYPE_CANNOT_ITERATE_OVER_TYPE :: "cannot iterate over type '%s'"
TYPE_CANNOT_LOOP_OVER_CALL :: "cannot loop over %s's result, a %s — a loop over a call needs it to give back a value and a bool each round: `-> %s, bool` (false: no more)"
TYPE_LOOP_CALL_RESULTS :: "a loop over a call takes one bool from it each round (false: done), and its other results as its values — %s gives %s"
TYPE_LOOP_CALL_NAMES :: "%s gives %d value%s each round: a name for each, and one more after them for the round if you want it — not %d"
TYPE_LOOP_CALL_WRITTEN_TYPE :: "a loop over a call: its variable is the call's value, a %s — not %s"
TYPE_LOOP_CALL_WRITTEN_TYPES :: "a loop over a call of several values: its names are typed as the call gives them — no type written"
TYPE_LOOP_ITEM_NAMES :: "a loop over items takes one or two names, the item and its position — not %d"
TYPE_RANGE_LOWER_BOUND_NUMERIC :: "range lower bound must be numeric, got %s"
TYPE_RANGE_UPPER_BOUND_NUMERIC :: "range upper bound must be numeric, got %s"
TYPE_DESCENDING_RANGE :: "descending range `%d..%d` -- `..` only counts up, so this would silently iterate zero times. To count down, use a C-style for, e.g. `for i := %d; i > %d; i -= 1`"
TYPE_CONDITION_BOOL :: "for condition must be bool (or an error), got %s"
TYPE_RETURN_FROM_NO_RESULT :: "this return gives back %s, but its fun has no result — declare it after the params: `-> %s`"
TYPE_RETURN_SEVERAL_FOR_ONE :: "this return gives back %d values, but its fun gives back one: `-> %s`"
TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED :: "return value count %d does not match expected %d"
TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED :: "return value %d: type %s does not match expected %s"
TYPE_RETURN_TYPE_MATCH_EXPECTED :: "return type %s does not match expected %s"
TYPE_CONDITION_BOOL_2 :: "if condition must be bool (or an error), got %s"
TYPE_DISCARDED_RETURN :: "return value of '%s' is discarded — capture it (`x := ...`) or discard it explicitly (`_ = ...`)"
TYPE_UNUSED_ERR :: "error value '%s' is unused — check it, propagate with `?`, or discard with `_`"
TYPE_DEFER_CHANGES_RETURNED :: "a defer can't change '%s': the return on line %d returns it, and defers run after it takes its value"
TYPE_DISPATCH_GROUP_FUNCTION :: "dispatch group '%s': '%s' is not a function"
TYPE_DISPATCH_GROUP_FUNCTION_DEFINED :: "dispatch group '%s': function '%s' not defined"
TYPE_OVERLOAD_DISPATCH_GROUP :: "overload: '%s' is not a dispatch group"
TYPE_CANNOT_ASSIGN_CONSTANT_TYPE :: "cannot assign %s to constant '%s' of type %s"
TYPE_CANNOT_WRITE_INDEXED_CONSTANT :: "cannot write through `::` constant '%s' — the value lives in read-only memory. Declare it as a variable (`%s := ...`) if you need to mutate it"
TYPE_INDEX_OUT_OF_BOUNDS_CONST :: "index %d out of bounds — array has %d elements (valid indices 0..%d)"
TYPE_FLOAT_DOESNT_FIT_CONST :: "%v doesn't fit in %s"
TYPE_SHIFT_COUNT_CONST :: "shift by %d, outside 0..%d for %s"
TYPE_SLICE_OUT_OF_BOUNDS_CONST :: "slice [%d:%d] out of bounds — array has %d elements (needs 0 <= low <= high <= %d)"
TYPE_CLASS_FIELDS_POSITIONAL_VALUES :: "class '%s' has %d fields, got %d positional values"
TYPE_FIELD_POSITION_EXPECTED :: "field '%s' (position %d): expected %s, got %s"
TYPE_FIELD_EXPECTED :: "field '%s': expected %s, got %s"
TYPE_CLASS_FIELD :: "class '%s' has no field '%s'"
TYPE_UNION_REQUIRES_NAMED_VARIANT_VARIANT :: "union '%s' requires a named variant, e.g. Variant {{ ... }}"
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
TYPE_ARRAY_INDEX_NUMBER :: "array index must be a number, got %s"
TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER :: "cannot write to element of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER :: "cannot assign to immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_ASSIGN_PARAMETER      :: "cannot assign to parameter '%s': a param can't be changed — copy it into a variable (`x := %s`) and change that"
TYPE_CANNOT_ASSIGN_ELEMENT :: "cannot assign %s to element of [%d!]%s"
TYPE_CANNOT_ASSIGN_ELEMENT_TYPE :: "cannot assign %s to element of %s (add an explicit cast)"
TYPE_SLICE_LOWER_BOUND_NUMBER :: "slice lower bound must be a number, got %s"
TYPE_SLICE_UPPER_BOUND_NUMBER :: "slice upper bound must be a number, got %s"
TYPE_CANNOT_SLICE_ASSIGN_INTO_IMMUTABLE :: "cannot slice-assign into immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_BYTE_SLICE_WRITE_BYTES_SLICE :: "byte slice write: %s is %d bytes, but slice span is %d bytes"
TYPE_BYTE_ARRAY_WRITE_BYTES_SLICE :: "byte array write: %s is %d bytes, but slice span is %d bytes"
TYPE_CANNOT_SLICE_ASSIGN_INTO :: "cannot slice-assign [%d!]%s into [%d!]%s"
TYPE_CANNOT_SLICE_ASSIGN_INTO_2 :: "cannot slice-assign []%s into [%d!]%s"
TYPE_SLICE_ASSIGN_VALUE_SHORT :: "slice assignment [%d:%d] fills %d elements, but the value has %d"
TYPE_SLICE_ASSIGN_ELEMENTS :: "cannot slice-assign []%s into a run of %s"
TYPE_BYTE_READ_RUN_SIZE :: "byte read: a run of %d %s is %d bytes, but the bytes are %d"
TYPE_BYTE_READ_RUN_WHOLE :: "byte read: %d bytes aren't a whole number of %s (%d bytes each)"
TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE :: "slice assignment requires an array or slice on the right-hand side, got %s"
TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER :: "cannot write to field '%s' of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_ASSIGN_FIELD_TYPE :: "cannot assign %s to %s of type %s"
TYPE_INFER_CONFLICTING_WIDTHS :: "inferred binding '%s' is used at conflicting widths: %s at %s and %s at %s — annotate it with an explicit type"
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
TYPE_MATCH_REQUIRES_UNION :: "match requires a union value, got `%s` — match is for union variant dispatch; use if/elif for value or predicate branching"
TYPE_TRY_OPERAND_MUST_BE_CALL :: "`?` propagation can only be applied to a call expression"
TYPE_TRY_REQUIRES_ERR_RETURN :: "`?` requires the called function's trailing return slot to be an error type"
TYPE_TRY_OUTSIDE_ERR_FUNCTION :: "`?` can only be used inside a function whose trailing return slot is an error type"
TYPE_DEFER_ERR_OUTSIDE_ERR_FUNCTION :: "`defer?` can only be used inside a function whose trailing return slot is an error type — it runs when the function fails"
TYPE_DEFER_ERR_IN_DEFER :: "`defer?` inside a defer's block would never run — the block doesn't fail; use `defer`"
TYPE_TRY_IN_DEFER :: "`?` can't be used in a defer's block — the block runs as the function ends and can't fail it; check the err where it's made"
TYPE_RETURN_IN_DEFER :: "`return` can't be used in a defer's block — the block runs as the function ends, after its return"
TYPE_LOOP_EXIT_OUTSIDE_LOOP :: "`%s` outside any loop"
TYPE_LOOP_EXIT_IN_DEFER :: "`%s` in a defer's block can only leave a loop inside the block — the block can't break or continue a loop around it"
TYPE_CIRCULAR_INCLUDE_MODULE_ALREADY_CHECKED :: "circular include: module '%s' is already being checked"
TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY :: "foreign symbol '%s' is already declared in library '%s' (first declaration at %s); each external symbol may be bound by at most one foreign block"
TYPE_PROGRAM_GLOBAL_REQUIRES_ALLOCATOR_TYPE :: "#allocator names an arena: `#allocator Arena_Basic(16 * MB)`"
TYPE_PROGRAM_SCOPE_ALLOCATOR_KNOWN_TYPE :: "#allocator %s: no such arena type"
TYPE_PROGRAM_SCOPE_ALLOCATOR_MISSING_REQUIRED :: "#allocator %s: an arena has mark, alloc and reset — it has no %s"
TYPE_WITH_NEEDS_MEMORY :: "`with` needs mara.memory (its arena_swap): `use mara.memory`"
TYPE_WITH_NEEDS_ALLOCATOR :: "`with` runs its block on another arena of the program's kind: name the program's first — `#allocator Arena_Basic(16 * MB)` at the module's top, or main's"
TYPE_WITH_NEEDS_ARENA_ADDRESS :: "`with` takes the arena's address: `with &%s`"
TYPE_WITH_NEEDS_ARENA_POINTER :: "`with` runs its block on another arena: give it a ^%s, of the program's kind (got %s)"
TYPE_ALLOCATOR_IN_MAIN_MODULE :: "#allocator names the program's arena: it goes in the module main is in (a DLL's: the module built)"
TYPE_ALLOCATOR_TWICE :: "the program's arena is named once: an #allocator came before this one"
TYPE_ALLOCATOR_NEEDS_SIZE :: "#allocator %s needs its size: `#allocator %s(16 * MB)` (a DLL's names the kind alone: its host's arena runs)"
TYPE_ALLOCATOR_AT_TOP :: "#allocator goes at a module's top, or among main's own statements: not in another fun, or in a block"
TYPE_THIS_PROGRAM_GONE :: "'%s' is gone: the program's arena is named at the module's top or main's — `#allocator Arena_Basic(16 * MB)` — another arena is a value (`a := Arena_Basic(1 * MB)`) a block runs on with `with &a`, and the command line is main's parameter: `main :: (args: [][]utf8)`"
TYPE_FUN_MAIN_RETURN_INT_RETURN :: "fun main() must return int or have no return type"
TYPE_FUN_MAIN_TAKE_PARAMETERS :: "main takes no parameters, or the command line: `main :: (args: [][]utf8)`"
TYPE_EXPOSE_FUNCTION_TAKE_FIRST_PARAMETER :: "#expose function '%s' takes its host's arena first: `^%s`, the kind #allocator names"
TYPE_VISIBLE_ENUM_UNION_VARIANT :: "no visible enum or union has variant '.%s'"
TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED :: "constant '%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s"
TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE :: "variable '%s' is used before being assigned a value"
TYPE_TYPE_VALUE_DID_MEAN :: "'%s' is a type, not a value. Did you mean ': %s'?"
TYPE_TYPE_NOT_VALUE :: "'%s' is a type, not a value"
TYPE_MODULE_NOT_VALUE :: "'%s' is a module, not a value"
TYPE_CALL_NO_VALUE :: "'%s' returns no value"
TYPE_PRINT_FUN :: "can't print '%s': it is a fun — call it to print what it returns"
TYPE_UNDEFINED_IDENTIFIER :: "undefined identifier '%s'"
TYPE_LOCAL_OF_ENCLOSING_SCOPE :: "'%s' is a local of '%s': a function sees the outside world only through its arguments; pass it in"
TYPE_STRUCT_LITERAL_NAME_NOT_STRUCT :: "'%s{{...}}': '%s' does not name a struct type"
TYPE_STRUCT_COPY_FORM :: "'%s' is a struct variable — copy-with-overrides ('new := %s{{...}}') is not supported. Copy first ('new := %s'), then override in place ('new{{...}}')"
TYPE_CANNOT_NEGATE :: "cannot negate %s"
TYPE_CANNOT_NEGATE_UNSIGNED :: "cannot negate unsigned %s — no representable result; widen to signed first (e.g. -i64(x))"
TYPE_CANNOT_APPLY :: "cannot apply 'not' to %s: it takes a bool (or an error)"
TYPE_CANNOT_APPLY_REQUIRES_INTEGER_TYPE :: "cannot apply '~' to %s, requires integer type"
TYPE_CANNOT_TAKE_ADDRESS_IMMUTABLE_PARAMETER :: "cannot take address of immutable parameter '%s' (declare it with ^ to allow mutation)"
TYPE_CANNOT_TAKE_ADDRESS_PARAMETER :: "cannot take the address of parameter '%s': a param can't be changed — copy it into a variable (`x := %s`) and take its address"
TYPE_CANNOT_WRITE_CONSTANT :: "cannot write into constant '%s' — copy it into a variable to change it"
TYPE_CANNOT_TAKE_ADDRESS_CONSTANT :: "cannot take address of constant '%s' — copy it into a variable to get storage"
TYPE_SLICE_CANNOT_BIND_CONSTANT :: "a slice here would be a writable view of constant '%s', which is read-only — copy it into a variable first (`x := %s`) and slice that"
TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE :: "cannot dereference non-pointer type %s"
TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED :: "typed array literal: type %s is not a fixed-size array"
TYPE_SIZE_UNKNOWN_TYPE :: "size_of: unknown type"
TYPE_TAKE_UNKNOWN_TYPE :: "let/slice: unknown type"
TYPE_LET_SLICE :: "let can't take a slice (%s): it names a value living in the storage, and a slice there would be only its header — for a slice over the storage, `slice([:n]T, &bytes[i])` (n already there) or `slice([:n]T, &storage)` (room for n)"
TYPE_TAKE_COUNT_INTEGER :: "slice count must be an integer, got %s"
TYPE_TAKE_REQUIRES_BYTE_CURSOR_FORM :: "let/slice requires ^[]byte or ^[N]byte (cursor form, pass &buffer) or ^byte (positional form), got %s%s"
TYPE_EXPRESSION_CONDITION_BOOL :: "if-expression condition must be bool (or an error), got %s"
TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS :: "if-expression branches have incompatible types: %s vs %s"
TYPE_TUPLE_DESTRUCTURE_INDEX_OUT_RANGE :: "tuple-destructure index %d out of range for %d-tuple"
TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT :: "#self is only legal directly in a constructor body (a method or nested helper must take an explicit ^Self)"
TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE :: "field '%s' of '%s' is used before being assigned a value"
TYPE_LITERAL_LEAVES_UNSET :: "%s has %d %s but %s. %s %s not set."
TYPE_FIELD_ALIASED_VIA_USED_BEFORE :: "field '%s' of '%s' (aliased via '%s') is used before being assigned a value"
TYPE_UNION_TAG_ENUM_INTERNAL_ERROR :: "union '%s' has no tag enum (internal error)"
TYPE_UNION_PADDING_DECLARE_UNION_PAD :: "union '%s' has no padding (declare with `union(... pad T ...)`)"
TYPE_MODULE_SYMBOL :: "module '%s' has no symbol '%s'"
TYPE_CANNOT_ACCESS_FIELD_ARRAY_TYPE :: "cannot access field '%s' on array type %s"
TYPE_SLICE_TYPE_FIELD :: "slice type %s has no field '%s'"
TYPE_PARTIAL_ARRAY_TYPE_FIELD :: "partial array type %s has no field '%s'"
TYPE_CANNOT_ACCESS_FIELD_TYPE :: "cannot access field '%s' on type %s"
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
TYPE_BYTE_BUFFER_WRITE_UNTYPED :: "writing an untyped number into a byte buffer has no defined width — `buf[i] = N` won't guess one. Cast to pin the byte count: u8(N) writes 1, u16(N) 2, u32(N) 4, u64(N) 8"
TYPE_BYTE_BUFFER_COPY_UNTYPED :: "copying untyped numbers into a byte buffer has no defined width — give the literal its element type: [%d!]u8{{...}}"
TYPE_SLICE_PTR_OUTSIDE_OS_MODULE :: "slice_from_ptr() outside the os module requires a comptime-known size "
TYPE_EXPECTS_ARGUMENT_3 :: "%s() expects 1 argument, got %d"
TYPE_LEFT_OPERAND_BOOL :: "left operand of '%s' must be bool (or an error), got %s"
TYPE_DID_MEAN_EACH_OPERAND_NEEDS :: "did you mean `%s`? Each operand of `%s` needs its own comparison."
TYPE_RIGHT_OPERAND_BOOL :: "right operand of '%s' must be bool (or an error), got %s"
TYPE_CANNOT_COMPARE_USING :: "cannot compare %s with %s using '%s'"
TYPE_LEFT_OPERAND_COMPARISON_NUMERIC :: "left operand of comparison must be numeric, got %s"
TYPE_RIGHT_OPERAND_COMPARISON_NUMERIC :: "right operand of comparison must be numeric, got %s"
TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT :: "mismatched types for '+': %s and %s - did you forget to import the module that defines the overload?"
TYPE_APPEND_CHAIN :: "`%s` appends, and an append gives nothing back, so there's nothing to add %s to: put each append on a line of its own"
TYPE_APPEND_CHAIN_SUM :: "`%s` appends, and an append gives nothing back, so there's nothing to add %s to: put each append on a line of its own, or for a sum write `%s + (%s + %s)`"
TYPE_JOIN_VIEW ::"can't join onto a view (%s): a view has no room of its own — make one first, `Path(dir) + …` (or str256(…), any partial array), or add into a buffer you have: `&buf + …`"
TYPE_APPEND_TO_FIXED_ARRAY :: "mismatched types for '+': %s and %s%s"
TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2 :: "mismatched types for '%s': %s and %s - did you forget to import the module that defines the overload?"
TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS :: "bitwise operators require integer operands, got %s"
TYPE_MISMATCHED_TYPES_ARITHMETIC_USE_EXPLICIT :: "mismatched types in arithmetic: %s and %s (use an explicit cast)"
TYPE_WRAPPING_REQUIRES_INTEGER :: "wrapping operator `%s%%` requires integer operands, got %s and %s"
TYPE_WRAPPING_REQUIRES_INTEGER_UNARY :: "wrapping negate `-%%` requires an integer operand, got %s"
TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER :: "argument %d of '%s': '_' requires a default value, but parameter '%s' has none"
TYPE_EXPECTS_ARGS :: "'%s' expects %d argument(s) (%s), got %d"
TYPE_ARGUMENT_EXPECTED :: "argument %d%s of '%s': parameter '%s' expects %s, got %s%s"
TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE :: "method '%s' requires a pointer receiver — take an address with `&` (or use a `^%s` local) before calling"
TYPE_MODULE_FUNCTION :: "module '%s' has no function '%s'"
TYPE_MATCHING_FUNCTION_DISPATCH_GROUP_ARGUMENT :: "no matching function in dispatch group '%s' for argument types (%s)"
TYPE_AMBIGUOUS_DISPATCH_MATCHES_MULTIPLE_OVERLOADS :: "ambiguous dispatch '%s' — matches multiple overloads: %s"
TYPE_UNDEFINED_FUNCTION :: "undefined function '%s'"
TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE :: "cannot construct %s from %s; underlying type is %s"
TYPE_FUNCTION :: "'%s' is not a function"
TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED :: "function '%s' is ambiguous (defined in: %s). Use a qualified call (e.g. `%s.%s(...)`), or use only one of the modules here."
TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID :: "'%s' field-override block is only valid on struct construction"
TYPE_ARRAY_ELEMENT_TYPE_EXPECTED :: "array element %d has type %s, expected %s"
TYPE_INDEX_NUMBER :: "index must be a number, got %s"
TYPE_CANNOT_INDEX_INTO :: "cannot index into %s"
TYPE_CANNOT_SLICE :: "cannot slice %s"
TYPE_SLICE_LOW_BOUND_NUMERIC :: "slice low bound must be numeric, got %s"
TYPE_SLICE_HIGH_BOUND_NUMERIC :: "slice high bound must be numeric, got %s"


// ============================================================
// Warnings — non-fatal, via check_warning.
// ============================================================

// An identity cast: the operand already has the target type, so the cast is a
// no-op in every context and can be dropped. (Value-preserving WIDENING casts
// are NOT flagged — `i64(x) * y` promotes the multiply to avoid overflow,
// `len = i64(x)` does not, and the cast site can't distinguish the two.)
TYPE_IN_NEEDS_ITEMS :: "`in` takes a range, `x in lo .. hi`, or something with items to look among — a list, an array, a view: `x in xs` — and %s has none"
TYPE_IN_ITEM_TYPE :: "can't look for a %s among %s items: `==` doesn't compare them"
WARN_LOOP_NEVER_LOOPS :: "this loop never runs a second time: every run ends in a `break` or `return` — was a statement meant inside a block? (code that runs once reads better as an `if`)"
WARN_CHAIN_MISALIGNED :: "this `%s` belongs to the `if` on line %d, but is indented differently. Was it meant for another `if`?"
WARN_REDUNDANT_CAST ::"redundant cast to %s — %s already has that type, drop the `%s(...)`"

TYPE_CANNOT_TAKE_ADDRESS_EXPRESSION :: "cannot take the address of this expression — `&` needs a named variable (or a field/element of one), not a temporary value"
TYPE_CANNOT_TAKE_ADDRESS_SLICE_TEMP :: "cannot take the address of a temporary slice — `buf[a:b]` builds a fresh slice header with no address to point at. To pass it to a `^[]T` parameter, bind it first (`s := buf[a:b]; f(&s)`), or — if the callee only reads it — make the parameter `[]T` and pass the slice directly (no `&`)"
TYPE_ARENA_SIZE_CONSTANT :: "the program's arena size must be a constant"
TYPE_CONST_NOT_COMPILE_TIME :: "constant '%s': its value must be known at compile time — literals, other constants and arithmetic on them (a call, or a struct with constructor params or statements in its body, needs code to run)"

// ============================================================
// Codegen fatals
// ============================================================

CODE_DLL_EXPOSE_FN_USES_ARENA :: "a DLL's #expose funs use an arena, but its kind isn't named: `#allocator Arena_Basic` at the module's top — each #expose fun then takes its host's arena first"
CODE_ARENA_ALLOCATION_REQUESTED_SCOPE_ALLOCATOR :: "arena allocation requested but the program names no arena: `#allocator Arena_Basic(16 * MB)` at the module's top"
CODE_FORMAT_STRING_MORE_PLACEHOLDERS_THAN :: "format string has more `%%` placeholders than args"
CODE_PRINT_UNSUPPORTED_VALUE :: "print: no print rule for a value of type %s"
CODE_GRAPH_UNLOWERED :: "can't lower '%s' from the program graph: its %s '%s'%s"
TYPE_RESULT_READS_DEST :: "'%s' is handed &%s while its result is written into %s: it would read what it overwrites. Build it under a name of its own (`r := %s(…)`), then assign it to %s"
CODE_TEMPORARY_NO_ARENA :: "a %s (%d bytes) is held in a temporary here, too large for the stack: it lives on the program's arena, and there is none — name one at the module's top (`#allocator Arena_Basic(16 * MB)`)"
CODE_TEMPORARY_UNLISTED :: "a %s (%d bytes) is held in a temporary here, and isn't one of its fun's big temporaries (a compiler bug: storage_calls missed it)"
CODE_GRAPH_NO_SCOPE :: "'%s' has no scope in the program graph"
CODE_GRAPH_NO_CODE :: "'%s' has no code in the program graph"
CODE_TEXT_LONGER_THAN_ARRAY :: "text of %d bytes into an array of %d"
CODE_BARE_CONSTRUCTION_ARGUMENT :: "'%s' is built without arguments, but its param '%s' has no default"
CODE_CONST_TABLE_UNNAMED :: "internal: aggregate constant has no entry in the constant table"
CODE_CONST_TABLE_SHAPE :: "internal: a constant table of a shape the emitter can't lay out"
BUILD_CLANG_FAILED                :: "Error: clang failed to compile '%s'\n"
BUILD_ARCHIVE_FAILED              :: "Error: archive creation failed for '%s'\n"
BUILD_FOREIGN_FILE_NOT_FOUND      :: "Error: foreign file '%s' not found under %s\n"
BUILD_FORCED_RECOMPILE_FAILED     :: "Error: forced recompile of '%s' failed\n"
BUILD_STATIC_LIB_FAILED           :: "Error: failed to build static lib from '%s'\n"
BUILD_NO_EMCC_EQUIVALENT          :: "Error: foreign library '%s' has no known emscripten equivalent.\n"
BUILD_FOREIGN_SOURCE_NOT_FOUND    :: "Error: foreign source '%s' not found under code/\n"
BUILD_PARSE_ERRORS_ABORT          :: "Found %d parse error(s) in '%s'. Aborting.\n"
BUILD_NO_ENTRY_POINT              :: "Error: module '%s' has no `main` and no `#expose` function. Add an entry point, or pass `-shared` to build an empty DLL.\n"
BUILD_TYPE_ERRORS_ABORT           :: "Found %d type error(s). Aborting.\n"
VIEW_NOT_BUILT                    :: "mara view: the window isn't built: there is no %s. Build it there (`mara build view` in %s).\n"
VIEW_NOT_STARTED                  :: "mara view: %s didn't start.\n"
