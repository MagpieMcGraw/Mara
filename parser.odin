package mara

import "core:fmt"
import "core:strconv"
import "core:strings"

// A source location, as tokens (ids in build_tokens). `at` is the REPORT POINT
// every diagnostic prints (its file, line and column: span_location). `tok` to
// `end` is a half-open range of tokens — the EXTENT, which a start point alone
// cannot express.
//
// The two are independent on purpose. A node's report point is not always its
// first token: Expr_Binary anchors on its operator so an error lands on the
// `==` rather than the left operand. The extent still has to begin at the
// leftmost token, so `m == void` reports at the `==` but covers `m`.
//
// Extents exist for the editor queries: resolving a cursor to a node means
// asking which nodes contain a position. With token ids that is integer
// containment (tok <= i < end) rather than comparing (line, col) pairs, and
// the innermost node is simply the smallest containing range.
//
// A Span{} is no place: no report point (at = 0), and no extent (end <= tok).
// Everything the parser produces has a real extent: leaves from token_span,
// compound nodes from cover_span.
Span :: struct {
    at:  Token_Id,
    tok: Token_Id,
    end: Token_Id,
}

span_file :: proc(s: Span) -> string {
    return build_files[build_tokens[s.at].file].path if s.at != 0 else ""
}

span_line :: proc(s: Span) -> int {
    return token_line(build_tokens[s.at]) if s.at != 0 else 0
}

span_col :: proc(s: Span) -> int {
    return token_col(build_tokens[s.at]) if s.at != 0 else 0
}

// "file:line:col" of a span's report point.
span_location :: proc(s: Span) -> string {
    return format_location(span_file(s), span_line(s), span_col(s))
}

// Format a source location as "file:line:col" or "line:col".
format_location :: proc(file: string, line: int, col: int) -> string {
    if file != "" {
        return fmt.tprintf("%s:%d:%d", file, line, col)
    }
    return fmt.tprintf("%d:%d", line, col)
}

// Type annotation AST
Type_Expr :: union {
    Type_Name,                  // int, f64, bool, string
    Type_Of_Name,               // fn game_run — nominal type of a named function
    ^Type_Array,                // [N]T — fixed-size array
    ^Type_Pointer,              // ^T — pointer to T
    ^Type_Slice_Expr,           // [:]T — slice (view into array)
    ^Type_Partial_Array_Expr,   // [..N]T — partial array (inline storage + cursor)
    ^Type_Generic_Instance,     // Array(int), Map(string, int) — parameterized type
    ^Type_Func_Expr,            // fun(int, int) -> int — function type
    Type_Const_Value,           // 256 — compile-time integer value in generic args
    Type_Const_Expr,            // runtime expression in generic args (e.g., String(n))
}

Type_Name :: struct {
    name: string,
    span: Span,
    tilde: bool,  // `~T` at type-expr position — T must be a constraint type
                  // (`~struct/~class`). Stylistic marker that makes the
                  // interface-shaped slot visible at the use site.
}

// `fn game_run` — extracts the nominal function type from a named function
// or a function-valued binding. Resolution (env lookup or c.table.funs) happens
// in the type checker. This is a syntactic marker: the parser only records the
// name; the checker enforces that the name refers to a function.
Type_Of_Name :: struct {
    name: string, // may be dotted ("sdl.init") for qualified access
    span: Span,
}

Type_Array :: struct {
    size:         int,       // the N in [N]T (0 when size_name or size_expr is set)
    size_name:    string,    // identifier name when size is a constant reference
    size_expr:    Expr,      // runtime expression for VLA size (nil for fixed arrays)
    index_type:   Type_Expr, // index type for [N IT]T form (nil = plain integer index)
    elem:         Type_Expr, // element type
    span:         Span,
}

Type_Pointer :: struct {
    elem: Type_Expr, // the pointed-to type
    span: Span,
}

Type_Slice_Expr :: struct {
    elem:         Type_Expr, // element type
    cap_expr:     Expr,      // [:N]T — cap stored in the slice header; nil for plain []T
    span:         Span,
}

// [..N]T — partial array. Value type with inline backing storage and a cursor
// (len). Layout at IR level: {ptr, len, cap, elements: [N x T]}, with ptr
// initialised to &elements at decl time so the first 24 bytes are layout-
// compatible with a slice header. See project_mara_slice_model for design.
Type_Partial_Array_Expr :: struct {
    size:         int,       // the N in [..N]T (0 when size_name or size_expr is set)
    size_name:    string,    // identifier name when size is a constant reference
    size_expr:    Expr,      // runtime expression for VLA-sized partial arrays
    elem:         Type_Expr, // element type
    span:         Span,
}

Type_Func_Expr :: struct {
    params:       [dynamic]Type_Expr,  // parameter types
    return_types: [dynamic]Type_Expr,  // return types (empty = void)
    span:         Span,
}

Type_Generic_Instance :: struct {
    name:      string,                  // "Array", "Map"
    type_args: [dynamic]Type_Expr,      // [Type_Name{name="int"}]
    span:      Span,
}

Type_Const_Value :: struct {
    value: int,
    span:  Span,
}

Type_Const_Expr :: struct {
    expr: Expr,
    span: Span,
}

Scope_Binding :: struct {
    name:          string,
    type_expr:     Type_Expr, // nil union if untyped
    default_value: Expr,      // nil if no default
    is_using:      bool,      // only meaningful for data-type funs (struct fields)
    span:          Span,      // its declaration (zero where none was kept)
}

Generic_Param :: struct {
    name:               string,    // "T", "K", "V" for type params; "n", "cap" for const params
    span:               Span,
    is_const:           bool,      // true for value params (n: uint) vs type params ($T: type)
    const_type:         string,    // "uint", "int", etc. — only when is_const
    default_value:      int,       // default value for const params (only valid when has_default)
    has_default:        bool,      // whether default_value is set
    shape_constraint:   string,    // for `name: ~T` shape-constrained type params: the constraint
                                   // type's name (e.g. "Arena"). Instantiation must satisfy T's
                                   // API + size budget. Empty for unconstrained type params.
    default_type_expr:  Type_Expr, // for type params (incl. ~T): default type when caller omits
                                   // the arg. Stored as a Type_Expr so it resolves through the
                                   // standard pipeline at instantiation time. nil when no default.
}

Union_Variant_Def :: struct {
    name:    string,                    // e.g. "Quit", "KeyDown", "Red"
    tag:     int,                       // explicit or auto-assigned tag value
    has_tag: bool,                      // true if = N was specified
    fields:  [dynamic]Scope_Binding, // empty for pure-enum variants
    span:    Span,                      // the variant name's source location (for the synthetic variant struct)
}

// AST node types

Expr :: union {
    ^Expr_Number,
    ^Expr_String,
    ^Expr_Char,
    ^Expr_Ident,
    ^Expr_Bool,
    ^Expr_Skip_Constructor,
    ^Expr_Unary,
    ^Expr_Binary,
    ^Expr_Call,
    ^Expr_Array,
    ^Expr_Index,
    ^Expr_Slice,
    ^Expr_Struct_Literal,
    ^Expr_Field_Access,
    ^Expr_Size_Of,
    ^Expr_Assert,
    ^Expr_Take,
    ^Expr_If,
    ^Expr_Compiler_Intrinsic,
    ^Expr_Include,
    ^Expr_Type_Name,
    ^Expr_Tuple_Default,
    ^Expr_Self,
    ^Expr_Try,
}

// Every expression has an id, given when it is made (new_expr): what the
// checker finds about it is kept by it (expr_type). Ids are dense and never
// reused; 0 is no expression's.
Expr_Id :: distinct u32

Expr_Number :: struct {
    id: Expr_Id,
    value:     f64,    // f64 form (authoritative when is_float = true)
    int_value: i128,   // exact integer form (authoritative when is_float = false).
                       // Wide enough for u64 hex literals (`0xFFFFFFFFFFFFFFFF`) and
                       // their negations, with headroom for future widening if needed.
    is_float:  bool,
    span:      Span,
}

Expr_String :: struct {
    id: Expr_Id,
    value: string,
    span:  Span,
}

Expr_Char :: struct {
    id: Expr_Id,
    value: u8,
    span:  Span,
}

Expr_Ident :: struct {
    id: Expr_Id,
    name:     string,
    span:     Span,
    is_dot:   bool,           // .Variant shorthand: resolve via expected type or visible-variant search
}

Expr_Unary :: struct {
    id: Expr_Id,
    op:      Token_Kind,
    operand: Expr,
    span:    Span,
    wrapping:    bool,         // `-%x`: wrapping negate, codegen skips the overflow check
}

Expr_Bool :: struct {
    id: Expr_Id,
    value: bool,
    span:  Span,
}

// `#skip_constructor` — explicit "skip the constructor body for this slot."
// Used as a default or initializer to suppress automatic construction
// (constructor calls, field defaults). Structural setup (slice/partial-array
// header init) still runs; only the per-field construction logic is skipped.
// The user takes responsibility for assigning before reading.
Expr_Skip_Constructor :: struct {
    id: Expr_Id,
    span:  Span,
}

Expr_Binary :: struct {
    id: Expr_Id,
    op:          Token_Kind,
    left:        Expr,
    right:       Expr,
    span:        Span,
    wrapping:    bool,         // `+%`/`-%`/`*%`: two's-complement wrap, codegen skips the overflow check
}

Expr_Call :: struct {
    id: Expr_Id,
    name:      string,
    qualifier: Expr,          // nil for unqualified, Expr_Ident for pkg.func()
    args:      [dynamic]Expr,
    overrides: ^Expr_Struct_Literal,      // optional `{...}` field override after the call
    span:      Span,
}

Expr_Array :: struct {
    id: Expr_Id,
    elements: [dynamic]Expr,
    span:     Span,
}

Expr_Index :: struct {
    id: Expr_Id,
    expr:  Expr,
    index: Expr,
    span:  Span,
    // `#big_endian buf[off]` — byte-buffer reinterpret read that byte-swaps every
    // multi-byte integer in the destination after the load/memcpy. Only meaningful
    // when the index targets a byte buffer; the type checker rejects other shapes.
    is_big_endian: bool,
}

Expr_Slice :: struct {
    id: Expr_Id,
    expr:  Expr,   // the array/slice being sliced
    low:   Expr,   // start index (nil = 0)
    high:  Expr,   // end index (nil = len)
    span:  Span,
    // `#big_endian buf[lo:hi]` — see Expr_Index above.
    is_big_endian: bool,
}

Struct_Field :: struct {
    name:  string,
    value: Expr,
}

Expr_Struct_Literal :: struct {
    id: Expr_Id,
    name:       string,               // variant name (e.g. "Circle") or "" for anonymous
    fields:     [dynamic]Struct_Field,
    positional: bool,                 // true if the fields list was parsed as positional values (name == "")
    zero_init:  bool,                 // true for {0} — explicit zero-init, no defaults
    // Broadcast literal: `{all <expr>}`. The single value fills every slot
    // (every element of an array, or — future — every field of a same-typed
    // struct). The checker expands `broadcast_value` into `array_values`
    // once the target's element count is known.
    is_broadcast:    bool,
    broadcast_value: Expr,
    // Inline type expression for typed array literals like `[3]f32{0.9, 0.2, 0.6}`.
    // When set, name is "" and the checker resolves type_expr to determine the
    // literal's type rather than looking up name.
    type_expr:  Type_Expr,
    span:       Span,
}

Expr_Field_Access :: struct {
    id: Expr_Id,
    expr:     Expr,
    field:    string,
    span:     Span,
}

Expr_Size_Of :: struct {
    id: Expr_Id,
    type_expr:     Type_Expr,
    span:          Span,
}

// Re-escape processed literal text for display: the lexer stores '\n' as the
// raw byte, but a failure message must show the source spelling, not emit a
// real newline mid-line. Mirrors the lexer's escape set; `quote` is the
// enclosing quote character, escaped when it appears in the content.
assert_escape_literal :: proc(text: string, quote: u8) -> string {
    sb := strings.builder_make()
    for i in 0..<len(text) {
        c := text[i]
        switch {
        case c == '\n':  strings.write_string(&sb, "\\n")
        case c == '\t':  strings.write_string(&sb, "\\t")
        case c == '\r':  strings.write_string(&sb, "\\r")
        case c == '\\':  strings.write_string(&sb, "\\\\")
        case c == 0:     strings.write_string(&sb, "\\0")
        case c == quote: strings.write_byte(&sb, '\\'); strings.write_byte(&sb, quote)
        case:            strings.write_byte(&sb, c)
        }
    }
    return strings.to_string(sb)
}

// Display form of one token: char/string literals get their quotes back and
// their content re-escaped (each lexer escape was 2 source chars and
// re-escapes to 2 chars, so the display width matches the source width —
// which the spacing math below relies on).
assert_token_display :: proc(tok: Token) -> string {
    #partial switch tok.kind {
    case .Char:
        return strings.concatenate({"'", assert_escape_literal(token_text(tok), '\''), "'"})
    case .String:
        return strings.concatenate({"\"", assert_escape_literal(token_text(tok), '"'), "\""})
    }
    return token_text(tok)
}

token_range_text :: proc(lo, hi: int) -> string {
    sb := strings.builder_make()
    for i in lo..<hi {
        if i > lo {
            prev := build_tokens[i - 1]
            cur  := build_tokens[i]
            if token_line(cur) != token_line(prev) || token_col(cur) > token_col(prev) + len(assert_token_display(prev)) {
                strings.write_byte(&sb, ' ')
            }
        }
        strings.write_string(&sb, assert_token_display(build_tokens[i]))
    }
    return strings.clone(strings.to_string(sb))
}

// `assert(cond)` — debug-only runtime invariant check. cond_text is the
// condition's source text (captured at parse time, since later phases have no
// source) for the failure message. When cond is a comparison, lhs_text and
// rhs_text carry each operand's source text so the failure can name the
// operand next to its value ("but game.running was true"); both empty
// otherwise. On in every build mode; `-no assert` compiles them out.
Expr_Assert :: struct {
    id: Expr_Id,
    cond:          Expr,
    cond_text:     string,
    lhs_text:      string,
    rhs_text:      string,
    span:          Span,
}

// take(T, storage) — carve a typed view from storage's current cursor,
// advancing storage.len. The result aliases storage's bytes; it does not
// copy. Caller must keep storage alive for the result's lifetime.
//
// Three shapes for the type argument:
//   take([N]T, storage)    — fixed: advances by sizeof([N]T), returns [N]T
//   take([]T(n), storage)  — runtime-counted: advances by n*sizeof(T),
//                            returns []T with len=cap=n. n is a runtime
//                            or compile-time integer expression. The type
//                            checker reads it as type []T, count n.
Expr_Take :: struct {
    id: Expr_Id,
    type_expr:     Type_Expr,
    storage:       Expr,
    count_expr:    Expr,      // set for the slice form `slice([:n]T, ...)`
    keyword:       string,    // "let" or "slice" — discriminates value vs slice carve
    span:          Span,
}

Expr_If :: struct {
    id: Expr_Id,
    condition: Expr,
    then_expr: Expr,
    else_expr: Expr,
    span:      Span,
}

Intrinsic_Kind :: enum {
    Caller_Name,
    Caller_Span,
    Web,     // #web — true when building with -web, else false
    Native,  // #native — opposite of #web (any non-web target)
    Windows, // #windows — target OS is Windows (orthogonal to #web/#native)
    Linux,   // #linux   — target OS is Linux   (orthogonal to #web/#native)
    Mac,     // #mac     — target OS is Mac     (orthogonal to #web/#native)
}

Expr_Compiler_Intrinsic :: struct {
    id: Expr_Id,
    kind:           Intrinsic_Kind,
    span:           Span,
}

// Bare type-keyword in expression context: `Array(byte, 64)` parses with a
// `byte` value-arg. The expression evaluates (at type-check time) to the
// corresponding builtin Type, letting primitive type names flow through
// expression positions the same way user-defined type names (Player, etc.)
// do via Expr_Ident → env lookup → Type_Scope.
Expr_Type_Name :: struct {
    id: Expr_Id,
    kind: Token_Kind,   // Bool_Type / I8 / I64 / U8 / Byte / F32 / F64 / Utf8 etc.
    span: Span,
}

Expr_Include :: struct {
    id: Expr_Id,
    path:        string,   // dotted module name: "mara.time", "gfx.vao", "camera", etc.
    is_sealed:   bool,     // `name :: sealed use path` — module reachable only via name.X (no bare-name leak)
    is_reexport: bool,     // true for `include` (re-export); false for `use` (private). Re-export adds names to the module's public surface.
    span:        Span,
}

// Synthetic default for one binding in a tuple-destructure param group.
// `source` is a call returning a tuple; `index` is this binding's slot.
// All N bindings in a destructure group share the SAME `source` pointer
// (not clones), which the codegen uses to dedup: first occurrence at a
// call site evaluates the source once into a temp, subsequent ones reuse
// it. Created by stmt_decl_to_bindings when a param/return group has
// init_n=1 and n_names>1 — the statement-level path uses Stmt_Multi_Return_Assign
// for the same shape and doesn't need this node.
Expr_Tuple_Default :: struct {
    id: Expr_Id,
    source: Expr,   // shared by identity across the group
    index:  int,    // 0..N-1
    span:   Span,
}

// `#self` — compiler-injected pointer to the under-construction instance,
// valid only inside a struct/class body. Resolves to type ^Self (the
// enclosing struct's Type_Scope wrapped in Type_Ptr). Codegen emits %sret,
// the destination pointer the constructor is writing into. Nested funs
// inside the struct body are reparented past the class_scope env at check
// time, so #self in a nested fun fails the lookup — explicit ^Self params
// are still the way to thread the instance through helpers.
Expr_Self :: struct {
    id: Expr_Id,
    span:  Span,
}

// Postfix `?` err-propagation. The inner expression must produce a value
// whose trailing return slot is `err`-compatible (concrete error_kind or the
// open `err` type). At codegen, the call is evaluated, the err slot tested
// against 0, and on non-zero the enclosing function returns immediately with
// that err in its own trailing slot. The expression's value is whatever the
// inner expression yielded *without* the err slot.
Expr_Try :: struct {
    id: Expr_Id,
    inner: Expr,
    span:  Span,
}

Stmt :: union {
    ^Stmt_Assign,
    ^Stmt_Multi_Assign,
    ^Stmt_Multi_Return_Assign,
    ^Stmt_Decl,
    ^Stmt_Define,
    Stmt_Call,
    ^Stmt_If,
    ^Stmt_For,
    ^Stmt_Scope,
    Stmt_Return,
    Stmt_Break,
    Stmt_Continue,
    ^Stmt_Defer,
    ^Stmt_Match,
    ^Stmt_Foreign,
    ^Stmt_Union_Def,
    ^Stmt_Distinct_Def,
    ^Stmt_Dispatch_Def,
    Stmt_Overload,
    Stmt_Module,
}

// Every statement has an id too, given when it is made (new_stmt, or
// next_stmt_id for one held by value): what a pass finds about it is kept by
// it. 0 is no statement's.
Stmt_Id :: distinct u32

// The last id given.
last_stmt_id: Stmt_Id

next_stmt_id :: proc() -> Stmt_Id {
    last_stmt_id += 1
    return last_stmt_id
}

// A statement of its own, with the next id: every statement held by pointer
// is made here, a clone too.
new_stmt :: proc(v: $T) -> ^T {
    n := new_clone(v)
    n.id = next_stmt_id()
    return n
}

Stmt_Assign :: struct {
    id: Stmt_Id,
    name:          string,
    value:         Expr,
    type_expr:     Type_Expr, // nil if untyped (e.g. x = 10)
    span:          Span,
    slice_cap_expr: Expr,      // capacity expression for `name : []T(N)` — allocates backing storage + slice header
    is_using:      bool,       // true for `using name := include ...`
    is_decl:       bool,       // true for desugared Stmt_Decl entries; false for reassignment (`x = 10`)
    // Complex LHS assignment (field/index/slice/deref). When non-nil, `name`,
    // `type_expr`, etc. are unused and the check procs pull
    // sub-expressions out of target and operate on it directly.
    target:        Expr,
    // True when the parser desugared `lhs op= rhs` into `lhs = lhs op rhs`.
    // `value` is always an Expr_Binary whose `left` is the same AST node as
    // `target` (or, for the simple-name path, a fresh Expr_Ident referring to
    // the same variable). Codegen uses this flag to hoist side-effectful
    // sub-expressions of the LHS into temps so the LHS is evaluated once.
    is_compound:   bool,
}

// Runtime binding. Always mutable. Covers single- and multi-name declarations
// with optional type annotation and optional initializer.
//   x := 10             -> names=[x], type=nil, init=[10]
//   x, y := f()         -> names=[x,y], type=nil, init=[f()]
//   x : int             -> names=[x], type=int, init=[]
Stmt_Decl :: struct {
    id: Stmt_Id,
    names:         [dynamic]string,
    type_expr:     Type_Expr,       // nil if inferred from init
    init_values:   [dynamic]Expr,   // empty if uninitialized; len 1 for tuple destructure
    slice_cap_expr: Expr,           // capacity expression for `name : []T(N)`
    is_using:      bool,
    span:          Span,
}

// Compile-time constant binding (`x :: 42`). Value is required and must be
// evaluable at compile time.
Stmt_Define :: struct {
    id: Stmt_Id,
    name:      string,
    type_expr: Type_Expr, // nil if untyped
    value:     Expr,
    span:      Span,
}

// Multiple assignment: x, y := get_pair()  or  x, y := a, b  or  x, y : int = a, b
// Wrapper for multi-name syntax: a, b : int  or  a, b := 1, 2
// Desugared into individual Stmt_Assign nodes; preserves grouping for source tools.
Stmt_Multi_Assign :: struct {
    id: Stmt_Id,
    assigns: [dynamic]^Stmt_Assign,
    span:    Span,
}

// Multi-return function call: x, y := call()  or  frame.x, frame.y = get_pair()
Stmt_Multi_Return_Assign :: struct {
    id: Stmt_Id,
    names:     [dynamic]string,
    targets:   [dynamic]Expr,   // parallel to names: non-nil for field/index/deref LHS targets
    values:    [dynamic]Expr,
    type_expr: Type_Expr,
    span:      Span,
    is_decl:   bool,            // true for the `:=` forms (`x, y := ...`): bare names
                                // are DECLARED. False for `=` reassignment, where each
                                // bare name must already be a binding (else a hard error).
}

Stmt_Call :: struct {
    id: Stmt_Id,
    expr: Expr, // must be an Expr_Call
    span: Span,
}

Stmt_If :: struct {
    id: Stmt_Id,
    condition:   Expr,
    body:        [dynamic]Stmt,
    else_body:   [dynamic]Stmt,
    is_comptime: bool,           // true for `#if` — type checker picks one branch, codegen drops the other
    span:        Span,
}

// Scope_Kind distinguishes struct-shape scopes (data layout) from fun-shape
// scopes (callable body). Set by the parser from the declaration keyword:
//   `struct` / `class`  → .Struct
//   `fun`               → .Fun
// Only codegen cares about the distinction — the type checker treats both
// kinds of scope the same (same field resolution, same name lookup, same
// Self binding, etc.). See project_mara_history.md for the design rationale.
Scope_Kind :: enum { Struct, Fun, Block }   // Block = an if/for/defer body — locals only (in .types), no members/params/returns

Stmt_Scope :: struct {
    id: Stmt_Id,
    name:           string,
    kind:           Scope_Kind,
    generic_params: [dynamic]Generic_Param, // empty for non-generic funs
    typed_params:    [dynamic]Scope_Binding, // callable params (in parens) — empty for data-type funs
    return_types:    [dynamic]Type_Expr,     // function return types: void = empty, single = 1 elem, multi-return = 2+
    return_bindings: [dynamic]Scope_Binding, // named return values: fun() -> (x, y: int)
    body:           [dynamic]Stmt,
    defs:           [dynamic]Stmt, // compile-time `::` decls (funs/structs/consts/...) pulled out of body
                                   // at parse time so scope-walks iterate only defs. STEP 1: these are an
                                   // index — the same nodes still appear in `body` too (not yet a partition).
    has_parens:     bool,      // true if fun was written with parens: fun() vs fun
    is_intrinsic:   bool,      // body was `{ @llvm.<name> }` — compiler generates body at call sites
    intrinsic_name: string,    // LLVM intrinsic mnemonic (e.g. "llvm.sqrt.f32"); set when is_intrinsic is true
    is_exposed:    bool,      // `#expose fun ...` — DLL entry point: dllexport linkage, unmangled symbol name
    is_packed:     bool,      // `#packed struct ...` — drop inter-field alignment padding (maps 1:1 to packed binary formats)
    span:           Span,
}

Stmt_Union_Def :: struct {
    id: Stmt_Id,
    name:           string,
    tag_type:       string,                        // "" = default (i64), or "i32", "i16", etc.
    min_size:       int,                           // 0 = no minimum, otherwise minimum payload size in bytes
    tag_pad:        Type_Expr,                     // type of padding between tag and payload (nil = none)
    variants:       [dynamic]Union_Variant_Def,    // variant definitions with fields
    generic_params: [dynamic]Generic_Param,        // non-empty for `Name :: union($T: type) { ... }` — monomorphized per use
    is_error_kind:  bool,                          // true for `Name :: error { ... }` — flat tag set, contributes to global `err`
    span:           Span,
}

Stmt_Distinct_Def :: struct {
    id: Stmt_Id,
    name:             string,
    base_type:        Type_Expr,
    default_cap_expr: Expr,       // for sized-slice aliases — `String :: distinct [, 0]utf8(128)` or `type([, 0]utf8)(128)`
    is_alias:         bool,       // true for `Name :: type(T)` — transparent alias; false for `Name :: distinct T` — nominal newtype
    span:             Span,
}

Stmt_Dispatch_Def :: struct {
    id: Stmt_Id,
    name:      string,
    functions: [dynamic]string,
    span:      Span,
}

Stmt_Overload :: struct {
    id: Stmt_Id,
    op:            Token_Kind,
    dispatch_name: string,
    span:          Span,
}

Stmt_Module :: struct {
    id: Stmt_Id,
    name: string,   // e.g. "game"
    span: Span,
}

Stmt_Return :: struct {
    id: Stmt_Id,
    values: [dynamic]Expr,   // return values (1 for single, N for tuple)
    span:   Span,
}

Stmt_Break :: struct {
    id: Stmt_Id,
    span: Span,
}

Stmt_Continue :: struct {
    id: Stmt_Id,
    span: Span,
}

// `defer <stmt>` or `defer { ... }` — registers a body of statements that run
// on enclosing-scope exit (LIFO across multiple defers in the same scope).
// Codegen appends body to the current Scope_Entry.deferred_blocks; the existing
// pop_scope / emit_return_resets / emit_loop_exit machinery emits them before
// arena reset.
Stmt_Defer :: struct {
    id: Stmt_Id,
    body: [dynamic]Stmt,
    span: Span,
}

Stmt_For :: struct {
    id: Stmt_Id,
    init:      Stmt,           // nil for simple `for cond {}`
    condition: Expr,
    post:      Stmt,           // nil for simple `for cond {}`
    body:      [dynamic]Stmt,
    span:      Span,
    // Range-for fields: `for i in 0..10 { }` — half-open, iterates 0..9.
    is_range:   bool,
    loop_var:   string,
    iter_type:  Type_Expr,     // optional type annotation: `for i : i32 in ...`
    range_low:  Expr,
    range_high: Expr,
    // Collection-for fields: `for elem, idx in collection { }`
    is_collection_for: bool,
    elem_var:          string,    // element variable name ("" if `_`)
    index_var:         string,    // index variable name ("" if not provided or `_`)
    collection:        Expr,
}

Match_Arm :: struct {
    value:           Expr,       // for value matching; also: predicate expr for namespace-form bool arms
    variant_name:    string,     // for union matching: e.g. "Circle"
    binding_name:    string,     // for union matching: e.g. "c"
    is_union_arm:    bool,       // true when this is a union pattern arm
    dot_shorthand:   string,     // for .Variant shorthand in value match (e.g. ".Red")
    is_else:         bool,       // true for wildcard else arm
    body:            [dynamic]Stmt,
}

Stmt_Match :: struct {
    id: Stmt_Id,
    subject: Expr,
    arms:    [dynamic]Match_Arm,
    span:    Span,
}

Foreign_Fun :: struct {
    name:         string,
    typed_params: [dynamic]Scope_Binding,
    return_types: [dynamic]Type_Expr,  // empty = void; foreign C funs are always 0 or 1
    span:         Span,
}

Stmt_Foreign :: struct {
    id: Stmt_Id,
    library:    string,              // e.g. "SDL2"
    prefix:     string,              // link prefix: prefix SDL_ → C symbol = "SDL_" + name
    decls:      [dynamic]Foreign_Fun,
    span:       Span,
}

// A program is just a list of statements
Program :: [dynamic]Stmt

// ---------------------------------------------------------------------------
// Parser state — now operates on a pre-built token array
// ---------------------------------------------------------------------------

Parser :: struct {
    tokens: []Token,   // the build's, to the end of this file (positions are token ids)
    file:   string,    // source file these tokens came from
    first:  int,       // its first token
    pos:    int,
    errors: int,
    // Accumulates $T generic param bindings found inside type expressions during function param parsing
    dollar_params: [dynamic]Generic_Param,
    // Accumulates named return bindings found during return type parsing: fun() -> (x, y: int)
    return_bindings: [dynamic]Scope_Binding,
    // When true, a `{` following an expression is NOT parsed as a struct literal —
    // the `{` belongs to the enclosing loop/if body. Set during condition parsing.
    no_struct_lit: bool,
}

// Get a Span from a Token. The extent is the token itself — exact for every
// leaf node. Nodes that go on to consume more tokens get widened by cover_span
// at the parse dispatch points; see parse_stmt / parse_expr.
token_span :: proc(tok: Token) -> Span {
    return Span{at = tok.id, tok = tok.id, end = tok.id + 1}
}

// Map compound assignment tokens to their binary operator
compound_assign_op :: proc(kind: Token_Kind) -> (Token_Kind, bool) {
    #partial switch kind {
    case .Plus_Equal:        return .Plus, true
    case .Minus_Equal:       return .Minus, true
    case .Mul_Equal:         return .Star, true
    case .Div_Equal:         return .Slash, true
    case .Mod_Equal:         return .Modulo, true
    case .And_Equal:         return .Ampersand, true
    case .Or_Equal:          return .Pipe, true
    case .Xor_Equal:         return .Tilde, true
    case .Shift_Left_Equal:  return .Shift_Left, true
    case .Shift_Right_Equal: return .Shift_Right, true
    }
    return .EOF, false
}

// ---------------------------------------------------------------------------
// Token access helpers
// ---------------------------------------------------------------------------

// Return the current token without consuming it
current :: proc(p: ^Parser) -> Token {
    if p.pos < len(p.tokens) {
        return p.tokens[p.pos]
    }
    return p.tokens[len(p.tokens) - 1]   // past the end: its EOF
}

// Consume the current token and return it
advance :: proc(p: ^Parser) -> Token {
    tok := current(p)
    if p.pos < len(p.tokens) {
        p.pos += 1
    }
    return tok
}

// Outcome of parsing a Number token's text.
Number_Parse_Error :: enum {
    None,
    Invalid,        // malformed text (empty hex digits, garbage)
    Hex_Overflow,   // well-formed hex but > u64 max — beyond the simple wide-literal tier
    Dec_Overflow,   // well-formed decimal integer but > u64 max — same tier as Hex_Overflow
    Bin_Overflow,   // well-formed binary but > u64 max (more than 64 significant bits)
}

// Parse a Number token's text into both an f64 and an i128 form. Hex literals
// (`0x...`) and decimal-without-dot integers fill the i128 form exactly;
// floats fill only the f64 form (i128 is set to the truncating cast for
// fallback but should never be read when is_float is true). Integer values
// up to u64 max (`0xFFFFFFFFFFFFFFFF` / `18446744073709551615`) round-trip
// exactly; anything wider is flagged as Hex_Overflow/Dec_Overflow.
parse_number_text :: proc(text_in: string) -> (f_val: f64, i_val: i128, err: Number_Parse_Error) {
    // Strip digit-group separators (`1_000`, `0xFF_FF`, `0b1010_0000`) once, up
    // front, so every base below parses clean digits.
    text := text_in
    has_sep := false
    for i := 0; i < len(text_in); i += 1 {
        if text_in[i] == '_' { has_sep = true; break }
    }
    if has_sep {
        b: strings.Builder
        for i := 0; i < len(text_in); i += 1 {
            if text_in[i] != '_' { strings.write_byte(&b, text_in[i]) }
        }
        text = strings.to_string(b)
    }
    if len(text) > 2 && text[0] == '0' && (text[1] == 'x' || text[1] == 'X') {
        digits := text[2:]
        // More than 16 significant hex digits doesn't fit in u64. Strip leading
        // zeros first so `0x000…FFFF...F` isn't false-flagged.
        clean := digits
        for len(clean) > 0 && clean[0] == '0' { clean = clean[1:] }
        if len(clean) > 16 {
            return 0, 0, .Hex_Overflow
        }
        n, parse_ok := strconv.parse_u64_of_base(digits, 16)
        if !parse_ok {
            return 0, 0, .Invalid
        }
        return f64(n), i128(n), .None
    }
    if len(text) > 2 && text[0] == '0' && (text[1] == 'b' || text[1] == 'B') {
        digits := text[2:]
        // More than 64 significant binary digits doesn't fit in u64.
        clean := digits
        for len(clean) > 0 && clean[0] == '0' { clean = clean[1:] }
        if len(clean) > 64 {
            return 0, 0, .Bin_Overflow
        }
        n, parse_ok := strconv.parse_u64_of_base(digits, 2)
        if !parse_ok {
            return 0, 0, .Invalid
        }
        return f64(n), i128(n), .None
    }
    // Decimal: all-digits text is an integer literal — accumulate it in i128
    // so values up to u64 max round-trip exactly (strconv.parse_int caps at
    // i64 and silently wraps, which turned 18446744073709551615 into -1).
    // Anything past u64 max is Dec_Overflow, the same precision tier as hex.
    // Non-digit text (has `.`) falls back to parse_f64 — int_value gets a
    // truncating cast that shouldn't be read for is_float = true anyway.
    is_int := len(text) > 0
    for i := 0; i < len(text); i += 1 {
        if !(text[i] >= '0' && text[i] <= '9') {
            is_int = false
            break
        }
    }
    if is_int {
        DEC_U64_MAX :: i128(max(u64))
        n: i128
        for i := 0; i < len(text); i += 1 {
            n = n * 10 + i128(text[i] - '0')
            if n > DEC_U64_MAX {
                return 0, 0, .Dec_Overflow
            }
        }
        return f64(n), n, .None
    }
    f, f_ok := strconv.parse_f64(text)
    if !f_ok {
        return 0, 0, .Invalid
    }
    return f, i128(f), .None
}

