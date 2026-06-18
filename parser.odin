package mara

import "core:fmt"
import "core:strconv"
import "core:strings"

// Source position
Span :: struct {
    line: int,
    col:  int,
    file: string,
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

Expr_Number :: struct {
    value:     f64,    // f64 form (authoritative when is_float = true)
    int_value: i128,   // exact integer form (authoritative when is_float = false).
                       // Wide enough for u64 hex literals (`0xFFFFFFFFFFFFFFFF`) and
                       // their negations, with headroom for future widening if needed.
    is_float:  bool,
    span:      Span,
    type_:     Type,   // filled by type checker
}

Expr_String :: struct {
    value: string,
    span:  Span,
    type_: Type,
}

Expr_Char :: struct {
    value: u8,
    span:  Span,
    type_: Type,
}

Expr_Ident :: struct {
    name:     string,
    span:     Span,
    type_:    Type,
    resolved: Resolved_Name,  // filled by type checker (enum variants, constants)
    is_dot:   bool,           // .Variant shorthand: resolve via expected type or visible-variant search
}

Expr_Unary :: struct {
    op:      Token_Kind,
    operand: Expr,
    span:    Span,
    type_:   Type,
    // Set by the type checker when `&buf[i]` is implicitly widened from
    // ^byte to a typed pointer ^T at a typed-decl/assignment site. Codegen
    // reads this to emit a runtime byte-buffer bounds check before producing
    // the pointer. Zero means no widening — use the regular &-of-index path.
    byte_view_size: int,
    // Set by the type checker when unary `-` resolves through an `overload -`
    // dispatch (e.g. `-v3` → `vec3_negate(v3)`). Codegen reads this to emit a
    // call instead of fneg / `sub 0, x`.
    overload_fn: Maybe(Resolved_Func),
    wrapping:    bool,         // `-%x`: wrapping negate, codegen skips the overflow check
}

Expr_Bool :: struct {
    value: bool,
    span:  Span,
    type_: Type,
}

// `#skip_constructor` — explicit "skip the constructor body for this slot."
// Used as a default or initializer to suppress automatic construction
// (constructor calls, field defaults). Structural setup (slice/partial-array
// header init) still runs; only the per-field construction logic is skipped.
// The user takes responsibility for assigning before reading.
Expr_Skip_Constructor :: struct {
    span:  Span,
    type_: Type,
}

Expr_Binary :: struct {
    op:          Token_Kind,
    left:        Expr,
    right:       Expr,
    span:        Span,
    type_:       Type,
    overload_fn: Maybe(Resolved_Func),
    wrapping:    bool,         // `+%`/`-%`/`*%`: two's-complement wrap, codegen skips the overflow check
}

Expr_Call :: struct {
    name:      string,
    qualifier: Expr,          // nil for unqualified, Expr_Ident for pkg.func()
    args:      [dynamic]Expr,
    overrides: ^Expr_Struct_Literal,      // optional `{...}` field override after the call
    span:      Span,
    type_:     Type,                      // return type, filled by type checker
    resolved_func: Maybe(Resolved_Func),  // filled by type checker (UFCS, package resolution)
    desugared: Expr,                      // if set, codegen evaluates this instead of the call
}

Expr_Array :: struct {
    elements: [dynamic]Expr,
    span:     Span,
    type_:    Type,
}

Expr_Index :: struct {
    expr:  Expr,
    index: Expr,
    span:  Span,
    type_: Type,   // element type
    // `#big_endian buf[off]` — byte-buffer reinterpret read that byte-swaps every
    // multi-byte integer in the destination after the load/memcpy. Only meaningful
    // when the index targets a byte buffer; the type checker rejects other shapes.
    is_big_endian: bool,
}

Expr_Slice :: struct {
    expr:  Expr,   // the array/slice being sliced
    low:   Expr,   // start index (nil = 0)
    high:  Expr,   // end index (nil = len)
    span:  Span,
    type_: Type,
    // `#big_endian buf[lo:hi]` — see Expr_Index above.
    is_big_endian: bool,
}

Struct_Field :: struct {
    name:  string,
    value: Expr,
}

Expr_Struct_Literal :: struct {
    name:       string,               // variant name (e.g. "Circle") or "" for anonymous
    fields:     [dynamic]Struct_Field,
    positional: bool,                 // true if the fields list was parsed as positional values (name == "")
    zero_init:  bool,                 // true for {0} — explicit zero-init, no defaults
    // Multi-return spread: `Foo{call()}` where call's tuple matches Foo's fields
    // one-to-one. Set by the type checker; codegen materializes temps for the
    // call's sret slots and fills each struct field from the corresponding temp.
    is_spread:  bool,
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
    // For distinct-fixed-array literals (Quat{...}, Vec3{...}, etc.): ordered
    // element values after swizzle-name → index resolution. nil entries mean
    // "zero this slot". Populated by the checker; codegen emits from this.
    array_values: [dynamic]Expr,
    // In-place override target: set by the type checker when `name` resolves to
    // a local VARIABLE of struct type (not a type name) — `var{ a = x; b = y }`
    // updates the variable's fields in place. Codegen applies the field writes
    // to that variable's storage via apply_struct_literal_fields and yields no
    // value (statement-position mutation).
    override_target: string,
    span:       Span,
    type_:      Type,
}

Expr_Field_Access :: struct {
    expr:     Expr,
    field:    string,
    span:     Span,
    type_:    Type,
    resolved: Resolved_Name,  // filled by type checker (enum/union variants, constants)
}

Expr_Size_Of :: struct {
    type_expr:     Type_Expr,
    span:          Span,
    type_:         Type,
    resolved_type: Type,      // the resolved type argument (filled by type checker)
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
        return strings.concatenate({"'", assert_escape_literal(tok.text, '\''), "'"})
    case .String:
        return strings.concatenate({"\"", assert_escape_literal(tok.text, '"'), "\""})
    }
    return tok.text
}

// Reconstruct source text for tokens [lo, hi): any gap (or line break)
// between consecutive tokens becomes one space, adjacent tokens stay fused —
// `x < y` keeps its spacing, `a.b[i]` stays tight. Used by assert to carry
// condition/operand text into the runtime failure message.
assert_token_text :: proc(p: ^Parser, lo, hi: int) -> string {
    sb := strings.builder_make()
    for i in lo..<hi {
        if i > lo {
            prev := p.tokens[i - 1]
            cur  := p.tokens[i]
            if cur.line != prev.line || cur.col > prev.col + len(assert_token_display(prev)) {
                strings.write_byte(&sb, ' ')
            }
        }
        strings.write_string(&sb, assert_token_display(p.tokens[i]))
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
    cond:          Expr,
    cond_text:     string,
    lhs_text:      string,
    rhs_text:      string,
    span:          Span,
    type_:         Type,      // always Type_Void — assert is a statement, no value
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
//                            checker lifts n out of the type expr into
//                            count_expr and rewrites type_expr to bare []T.
Expr_Take :: struct {
    type_expr:     Type_Expr,
    storage:       Expr,
    count_expr:    Expr,      // set for the slice form `slice([:n]T, ...)`
    keyword:       string,    // "let" or "slice" — discriminates value vs slice carve
    span:          Span,
    type_:         Type,
    resolved_type: Type,      // the resolved type argument (filled by type checker)
}

Expr_If :: struct {
    condition: Expr,
    then_expr: Expr,
    else_expr: Expr,
    span:      Span,
    type_:     Type,
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
    kind:           Intrinsic_Kind,
    resolved_value: string,   // filled by type checker: "my_func" or "test.mara:42:15"
    bool_value:     bool,     // for kind = .Web / .Native / .Windows / .Linux / .Mac
    span:           Span,
    type_:          Type,
}

// Bare type-keyword in expression context: `Array(byte, 64)` parses with a
// `byte` value-arg. The expression evaluates (at type-check time) to the
// corresponding builtin Type, letting primitive type names flow through
// expression positions the same way user-defined type names (Player, etc.)
// do via Expr_Ident → env lookup → Type_Scope.
Expr_Type_Name :: struct {
    kind: Token_Kind,   // Bool_Type / I8 / I64 / U8 / Byte / F32 / F64 / Utf8 etc.
    span: Span,
    type_: Type,        // filled by type checker
}

Expr_Include :: struct {
    path:        string,   // dotted module name: "mara.time", "gfx.vao", "camera", etc.
    is_sealed:   bool,     // `name :: sealed use path` — module reachable only via name.X (no bare-name leak)
    is_reexport: bool,     // true for `include` (re-export); false for `use` (private). Re-export adds names to the module's public surface.
    span:        Span,
    type_:       Type,
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
    source: Expr,   // shared by identity across the group
    index:  int,    // 0..N-1
    span:   Span,
    type_:  Type,   // filled by type checker — the i-th tuple slot
}

// `#self` — compiler-injected pointer to the under-construction instance,
// valid only inside a struct/class body. Resolves to type ^Self (the
// enclosing struct's Type_Scope wrapped in Type_Ptr). Codegen emits %sret,
// the destination pointer the constructor is writing into. Nested funs
// inside the struct body are reparented past the class_scope env at check
// time, so #self in a nested fun fails the lookup — explicit ^Self params
// are still the way to thread the instance through helpers.
Expr_Self :: struct {
    span:  Span,
    type_: Type,    // filled by type checker — ^Type_Scope of enclosing struct
}

// Postfix `?` err-propagation. The inner expression must produce a value
// whose trailing return slot is `err`-compatible (concrete error_kind or the
// open `err` type). At codegen, the call is evaluated, the err slot tested
// against 0, and on non-zero the enclosing function returns immediately with
// that err in its own trailing slot. The expression's value is whatever the
// inner expression yielded *without* the err slot.
Expr_Try :: struct {
    inner: Expr,
    span:  Span,
    type_: Type,    // filled by type checker — inner type minus the trailing err
}

// Statements

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

Stmt_Assign :: struct {
    name:          string,
    value:         Expr,
    type_expr:     Type_Expr, // nil if untyped (e.g. x = 10)
    span:          Span,
    var_type:      Type,       // resolved type (distinct-unwrapped), filled by type checker
    env_type:      Type,       // full type for env updates (preserves distinct), filled by type checker
    slice_cap_expr: Expr,      // capacity expression for `name : []T(N)` — allocates backing storage + slice header
    is_using:      bool,       // true for `using name := include ...`
    is_decl:       bool,       // true for desugared Stmt_Decl entries; false for reassignment (`x = 10`)
    // Complex LHS assignment (field/index/slice/deref). When non-nil, `name`,
    // `type_expr`, `var_type`, etc. are unused and the check/gen procs pull
    // sub-expressions out of target and operate on it directly.
    target:        Expr,
    target_type:   Type,       // resolved type of the target (field/container/pointee), filled by type checker
    assign_value_type:  Type,  // solid RHS type for byte-slice reinterpret writes, filled by type checker
    // True when the parser desugared `lhs op= rhs` into `lhs = lhs op rhs`.
    // `value` is always an Expr_Binary whose `left` is the same AST node as
    // `target` (or, for the simple-name path, a fresh Expr_Ident referring to
    // the same variable). Codegen uses this flag to hoist side-effectful
    // sub-expressions of the LHS into temps so the LHS is evaluated once.
    is_compound:   bool,
    checked:       [dynamic]Stmt,
}

// Runtime binding. Always mutable. Covers single- and multi-name declarations
// with optional type annotation and optional initializer.
//   x := 10             -> names=[x], type=nil, init=[10]
//   x, y := f()         -> names=[x,y], type=nil, init=[f()]
//   x : int             -> names=[x], type=int, init=[]
Stmt_Decl :: struct {
    names:         [dynamic]string,
    type_expr:     Type_Expr,       // nil if inferred from init
    init_values:   [dynamic]Expr,   // empty if uninitialized; len 1 for tuple destructure
    slice_cap_expr: Expr,           // capacity expression for `name : []T(N)`
    is_using:      bool,
    span:          Span,
    // Type checker fills `checked` with the desugared underlying statements
    // (one or more Stmt_Assign, or a Stmt_Multi_Return_Assign for tuple
    // destructure). Codegen and dumps iterate these instead of reprocessing
    // names/init_values. This lets Stmt_Decl be the public AST shape while
    // keeping the existing per-assign checker/codegen logic intact.
    checked:       [dynamic]Stmt,
}

// Compile-time constant binding (`x :: 42`). Value is required and must be
// evaluable at compile time.
Stmt_Define :: struct {
    name:      string,
    type_expr: Type_Expr, // nil if untyped
    value:     Expr,
    span:      Span,
    var_type:  Type,      // resolved type (distinct-unwrapped), filled by checker
    env_type:  Type,      // env type preserving distinct
}

// Multiple assignment: x, y := get_pair()  or  x, y := a, b  or  x, y : int = a, b
// Wrapper for multi-name syntax: a, b : int  or  a, b := 1, 2
// Desugared into individual Stmt_Assign nodes; preserves grouping for source tools.
Stmt_Multi_Assign :: struct {
    assigns: [dynamic]^Stmt_Assign,
    span:    Span,
}

// Multi-return function call: x, y := call()  or  frame.x, frame.y = get_pair()
Stmt_Multi_Return_Assign :: struct {
    names:     [dynamic]string,
    targets:   [dynamic]Expr,   // parallel to names: non-nil for field/index/deref LHS targets
    values:    [dynamic]Expr,
    type_expr: Type_Expr,
    span:      Span,
    var_types: [dynamic]Type,   // per-name resolved types, filled by type checker (destructure only)
    is_decl:   bool,            // true for the `:=` forms (`x, y := ...`): bare names
                                // are DECLARED. False for `=` reassignment, where each
                                // bare name must already be a binding (else a hard error).
    checked:   [dynamic]Stmt,   // broadcast desugaring: one Stmt_Assign per target, filled by
                                // the type checker. Non-empty ⟺ broadcast; codegen iterates it
                                // instead of special-casing. Empty for destructure (call-once).
}

Stmt_Call :: struct {
    expr: Expr, // must be an Expr_Call
    span: Span,
}

Stmt_If :: struct {
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
Scope_Kind :: enum { Struct, Fun }

Stmt_Scope :: struct {
    name:           string,
    kind:           Scope_Kind,
    generic_params: [dynamic]Generic_Param, // empty for non-generic funs
    typed_params:    [dynamic]Scope_Binding, // callable params (in parens) — empty for data-type funs
    fields:          [dynamic]Scope_Binding, // data fields — non-empty means this is a data-type (struct-like) fun
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
    name:             string,
    base_type:        Type_Expr,
    default_cap_expr: Expr,       // for sized-slice aliases — `String :: distinct [, 0]utf8(128)` or `type([, 0]utf8)(128)`
    is_alias:         bool,       // true for `Name :: type(T)` — transparent alias; false for `Name :: distinct T` — nominal newtype
    span:             Span,
}

Stmt_Dispatch_Def :: struct {
    name:      string,
    functions: [dynamic]string,
    span:      Span,
}

Stmt_Overload :: struct {
    op:            Token_Kind,
    dispatch_name: string,
    span:          Span,
}

Stmt_Module :: struct {
    name: string,   // e.g. "game"
    span: Span,
}

Stmt_Return :: struct {
    values: [dynamic]Expr,   // return values (1 for single, N for tuple)
    span:   Span,
}

Stmt_Break :: struct {
    span: Span,
}

Stmt_Continue :: struct {
    span: Span,
}

// `defer <stmt>` or `defer { ... }` — registers a body of statements that run
// on enclosing-scope exit (LIFO across multiple defers in the same scope).
// Codegen appends body to the current Scope_Entry.deferred_blocks; the existing
// pop_scope / emit_return_resets / emit_loop_exit machinery emits them before
// arena reset.
Stmt_Defer :: struct {
    body: [dynamic]Stmt,
    span: Span,
}

Stmt_For :: struct {
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
    var_type:   Type,          // resolved type, filled by type checker
    // Collection-for fields: `for elem, idx in collection { }`
    is_collection_for: bool,
    elem_var:          string,    // element variable name ("" if `_`)
    index_var:         string,    // index variable name ("" if not provided or `_`)
    collection:        Expr,
    collection_len:    Expr,      // if set, use as loop bound instead of compile-time capacity
    elem_type_:        Type,      // resolved element type, filled by type checker
    collection_type:   Type,      // resolved collection type, filled by type checker
}

Match_Arm :: struct {
    value:           Expr,       // for value matching; also: predicate expr for namespace-form bool arms
    variant_name:    string,     // for union matching: e.g. "Circle"
    binding_name:    string,     // for union matching: e.g. "c"
    is_union_arm:    bool,       // true when this is a union pattern arm
    dot_shorthand:   string,     // for .Variant shorthand in value match (e.g. ".Red")
    is_else:         bool,       // true for wildcard else arm
    body:            [dynamic]Stmt,
    // Populated by type checker — codegen reads these directly
    resolved_tag:    int,        // tag value for enum/union variant arms
    resolved_struct: string,     // variant struct name for union binding arms
}

Stmt_Match :: struct {
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
    tokens: []Token,
    file:   string, // source file these tokens came from; supplies Span.file (was a per-token field)
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

// Get a Span from a Token
token_span :: proc(p: ^Parser, tok: Token) -> Span {
    return Span{line = tok.line, col = tok.col, file = p.file}
}

// Takes a pointer to the lexer's token array so we can chain without copying
// or re-slicing across the FFI boundary. Returns a heap-allocated Parser so
// the internal dynamic arrays (dollar_params, return_bindings) stay valid
// after the call returns.
parser_init :: proc(tokens: ^[dynamic]Token, file: string) -> ^Parser {
    p := new(Parser)
    p.tokens = tokens^[:]
    p.file = file
    p.pos = 0
    return p
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

// Return just the current token kind without copying the full Token struct
current_kind :: proc(p: ^Parser) -> Token_Kind {
    return p.tokens[p.pos].kind if p.pos < len(p.tokens) else .EOF
}

// Peek ahead and return just the token kind
peek_kind :: proc(p: ^Parser, offset: int = 1) -> Token_Kind {
    i := p.pos + offset
    return p.tokens[i].kind if i < len(p.tokens) else .EOF
}

// Return the current token without consuming it
current :: proc(p: ^Parser) -> Token {
    if p.pos < len(p.tokens) {
        return p.tokens[p.pos]
    }
    // Past the end — return EOF
    last := p.tokens[len(p.tokens) - 1]
    return Token{kind = .EOF, line = last.line, col = last.col}
}

// Peek ahead by offset tokens (0 = current, 1 = next, ...)
// Sentinel-terminated array/slice types (`[N, 0]T`, `[..N, 0]T`, `[:N, 0]T`,
// `[, 0]T`) were removed — plain arrays/slices plus terminator-writing
// cstring conversion at the FFI boundary replaced them. Catch the old
// syntax with a pointed error and recover by parsing the plain form.
consume_removed_sentinel :: proc(p: ^Parser) {
    if current_kind(p) != .Comma { return }
    parse_error(p, current(p), PARSE_SENTINEL_REMOVED)
    advance(p) // consume ','
    skip_newlines(p)
    _ = expect(p, .Number)
}

peek_token :: proc(p: ^Parser, offset: int = 1) -> Token {
    i := p.pos + offset
    if i < len(p.tokens) {
        return p.tokens[i]
    }
    last := p.tokens[len(p.tokens) - 1]
    return Token{kind = .EOF, line = last.line, col = last.col}
}

// Consume the current token and return it
advance :: proc(p: ^Parser) -> Token {
    tok := current(p)
    if p.pos < len(p.tokens) {
        p.pos += 1
    }
    return tok
}

// Parse a token text as a non-negative integer without going through f64
parse_int_token :: proc(text: string) -> int {
    result := 0
    for ch in transmute([]u8)text {
        if ch >= '0' && ch <= '9' {
            result = result * 10 + int(ch - '0')
        }
    }
    return result
}

// Format error location prefix from a Token.
error_prefix :: proc(p: ^Parser, tok: Token) -> string {
    return format_location(p.file, tok.line, tok.col)
}

// Emit a parser error: `[file:line:col] Parse error: <msg>` + newline,
// and increment p.errors. `msg` is the message body (see diagnostics.odin
// for the PARSE_* constants used at call sites); positional args fill its
// format placeholders. Replaces the inline fmt.printf + counter idiom
// at the dozens of parser error sites — wording changes happen in
// diagnostics.odin, not here.
parse_error :: proc(p: ^Parser, tok: Token, msg: string, args: ..any) {
    emit_diagnostic(.Parse_Error, error_prefix(p, tok), msg, ..args)
    p.errors += 1
}

// Expect the current token to be of a certain kind, consume it, or report an error
expect :: proc(p: ^Parser, kind: Token_Kind) -> Token {
    tok := current(p)
    if tok.kind != kind {
        parse_error(p, tok, PARSE_EXPECTED_TOKEN, kind, tok.kind, tok.text)
    }
    advance(p)
    return tok
}

// Expect a field name: an identifier token (used after '.' in field access).
expect_field_name :: proc(p: ^Parser) -> Token {
    return expect(p, .Identifier)
}

// Skip any newline tokens
skip_newlines :: proc(p: ^Parser) {
    for current_kind(p) == .Newline {
        advance(p)
    }
}

// Consume statement separators: newlines and semicolons.
skip_separator :: proc(p: ^Parser) {
    for current_kind(p) == .Newline || current_kind(p) == .Semicolon || current_kind(p) == .Comma {
        advance(p)
    }
}

// Panic-mode recovery: after a parse error inside a statement, skip tokens
// until we reach a plausible statement boundary. Stops AT (does not consume)
// Newline, Semicolon, Right_Brace, and EOF — the caller's skip_separator /
// block-terminator check resumes cleanly from there.
recover_to_stmt_boundary :: proc(p: ^Parser) {
    for {
        kind := current_kind(p)
        if kind == .Newline || kind == .Semicolon || kind == .Right_Brace || kind == .EOF {
            return
        }
        advance(p)
    }
}

// ---------------------------------------------------------------------------
// Top-level parsing
// ---------------------------------------------------------------------------

parse_program :: proc(p: ^Parser) -> ^Program {
    stmts := new(Program)

    skip_newlines(p)
    for current_kind(p) != .EOF {
        errs_before := p.errors
        append(stmts, parse_stmt(p))
        if p.errors > errs_before {
            recover_to_stmt_boundary(p)
        }
        skip_separator(p)
    }

    return stmts
}

// is_scope_def reports whether a statement is a compile-time `::` definition
// (nested fun/struct, const, union/distinct/dispatch, foreign, overload) rather
// than a runtime statement. Scope bodies record their defs separately (into
// Stmt_Scope.defs) so registration/resolution passes walk only the defs.
is_scope_def :: proc(s: Stmt) -> bool {
    #partial switch _ in s {
    case ^Stmt_Scope, ^Stmt_Define, ^Stmt_Union_Def, ^Stmt_Distinct_Def,
         ^Stmt_Dispatch_Def, ^Stmt_Foreign, Stmt_Overload:
        return true
    }
    return false
}

// parse_block parses `{ stmt* }` into a flat list. The defs/body partition is
// done later, authoritatively, by fold_comptime_ifs in the checker (it has to
// run after `#if` folding anyway), so the parser doesn't classify here.
parse_block :: proc(p: ^Parser) -> [dynamic]Stmt {
    expect(p, .Left_Brace)
    skip_newlines(p)

    stmts: [dynamic]Stmt
    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        errs_before := p.errors
        append(&stmts, parse_stmt(p))
        if p.errors > errs_before {
            recover_to_stmt_boundary(p)
        }
        skip_separator(p)
    }

    expect(p, .Right_Brace)
    return stmts
}

// is_intrinsic_part_kind reports whether a token kind can appear as one
// dotted segment of an `@llvm.<...>.<...>` intrinsic name. Type keywords like
// f32/f64/i64 are valid suffix segments even though they are reserved words
// in normal source.
is_intrinsic_part_kind :: proc(kind: Token_Kind) -> bool {
    #partial switch kind {
    case .Identifier, .Int, .F64, .F32,
         .I8, .I16, .I32, .I64,
         .U8, .U16, .U32, .U64,
         .Utf8, .Byte, .Bool_Type,
         .Number:
        return true
    }
    return false
}

// parse_scope_body parses a function body, recognising `{ @llvm.<name> }` as a
// compiler-generated intrinsic body (returned as an empty stmts list with
// is_intrinsic=true and the dotted LLVM name in intrinsic_name).
// Any other body is parsed as a normal block.
parse_scope_body :: proc(p: ^Parser) -> (stmts: [dynamic]Stmt, is_intrinsic: bool, intrinsic_name: string) {
    if current_kind(p) == .Left_Brace {
        save := p.pos
        advance(p) // consume '{'
        skip_newlines(p)
        if current_kind(p) == .At {
            at_tok := advance(p) // consume '@'
            // Read dotted name: any-token ('.' any-token)*. Accept type
            // keywords (f32/f64/i64/...) as parts so we can write `f32`, not
            // a backticked identifier, in the suffix.
            sb: strings.Builder
            if !is_intrinsic_part_kind(current_kind(p)) {
                tok := current(p)
                parse_error(p, at_tok, PARSE_EXPECTED_INTRINSIC_AFTER_AT, tok.text)
                skip_newlines(p)
                expect(p, .Right_Brace)
                return nil, true, ""
            }
            first := advance(p)
            strings.write_string(&sb, first.text)
            for current_kind(p) == .Dot {
                advance(p) // consume '.'
                if !is_intrinsic_part_kind(current_kind(p)) {
                    tok := current(p)
                    parse_error(p, tok, PARSE_EXPECTED_INTRINSIC_AFTER_DOT, tok.text)
                    skip_newlines(p)
                    expect(p, .Right_Brace)
                    return nil, true, ""
                }
                part := advance(p)
                strings.write_byte(&sb, '.')
                strings.write_string(&sb, part.text)
            }
            skip_newlines(p)
            expect(p, .Right_Brace)
            return nil, true, strings.clone(strings.to_string(sb))
        }
        if current_kind(p) == .Intrinsic {
            tok := current(p)
            parse_error(p, tok, PARSE_BARE_INTRINSIC_REMOVED)
            advance(p) // consume 'intrinsic' to attempt recovery
            skip_newlines(p)
            expect(p, .Right_Brace)
            return nil, true, ""
        }
        // Not an intrinsic body — rewind and delegate to parse_block
        p.pos = save
    }
    stmts = parse_block(p)
    return stmts, false, ""
}

// ---------------------------------------------------------------------------
// Statement parsing — dispatches to individual parse functions
// ---------------------------------------------------------------------------

parse_module :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'module'
    // Module names can start with digits (e.g., "1M"), which the lexer
    // tokenizes as .Number + .Identifier. Concatenate them.
    name := ""
    if current_kind(p) == .Number {
        num_tok := advance(p)
        if current_kind(p) == .Identifier {
            ident_tok := advance(p)
            name = strings.concatenate({num_tok.text, ident_tok.text})
        } else {
            name = num_tok.text
        }
    } else {
        name = expect(p, .Identifier).text
    }
    // Allow dotted names: `module mara.math`. Each dot-separated segment is
    // its own identifier token; concatenate them into the full name.
    for current_kind(p) == .Dot {
        advance(p) // consume '.'
        seg := expect(p, .Identifier).text
        name = strings.concatenate({name, ".", seg})
    }
    return Stmt_Module{name = name, span = start}
}

// Build a single-name Stmt_Decl. Most callers want this shape.
make_single_decl :: proc(name: string, type_expr: Type_Expr, value: Expr, span: Span, is_using := false, slice_cap_expr: Expr = nil) -> ^Stmt_Decl {
    names: [dynamic]string
    append(&names, name)
    init_values: [dynamic]Expr
    if value != nil {
        append(&init_values, value)
    }
    return new_clone(Stmt_Decl{
        names          = names,
        type_expr      = type_expr,
        init_values    = init_values,
        slice_cap_expr = slice_cap_expr,
        is_using       = is_using,
        span           = span,
    })
}

// After parsing a type expression in a declaration, return the slice cap from
// the `[:N]T` form (cap was parsed into Type_Slice_Expr.cap_expr). Caller
// lifts the returned expression onto Stmt_Decl/Stmt_Assign's slice_cap_expr
// field so downstream codegen reads it the same way it always has.
try_parse_slice_cap_suffix :: proc(p: ^Parser, type_expr: Type_Expr) -> Expr {
    ts, is_slice := type_expr.(^Type_Slice_Expr)
    if !is_slice { return nil }
    if ts.cap_expr != nil {
        cap := ts.cap_expr
        ts.cap_expr = nil  // single-source-of-truth: cap lives on Stmt_Decl now.
        return cap
    }
    return nil
}

// Parse the RHS of a multi-name declaration or assignment after the '='.
// Handles three forms:
//   all <expr>      — broadcast: emit n_names clones of <expr>
//   a, b, c         — parallel: n RHS values (caller checks n == n_names)
//   call()          — single call producing a tuple (multi-return destructure)
// Returns len == n_names for broadcast/parallel, len == 1 for multi-return.
//
// When `stop_at_group_break` is true (param/return context), the comma-loop
// stops if it sees `<ident> <colon-or-comma>` after a comma — that pattern
// marks the start of the next param/return group, not another RHS value.
// At statement context the flag stays false: commas eat everything to end-
// of-statement, and count mismatches surface as type errors.
parse_multi_rhs :: proc(p: ^Parser, n_names: int, stop_at_group_break: bool = false) -> [dynamic]Expr {
    vals: [dynamic]Expr
    if current_kind(p) == .Identifier && current(p).text == "all" {
        advance(p) // consume 'all'
        val := parse_expr(p)
        for i := 0; i < n_names; i += 1 {
            v := i == 0 ? val : clone_expr(val)
            append(&vals, v)
        }
        return vals
    }
    append(&vals, parse_expr(p))
    for current_kind(p) == .Comma {
        if stop_at_group_break {
            // Look past the comma, skipping any newlines (multi-line param
            // lists wrap one group per line). If the next non-newline tokens
            // are `<ident> <:|,>`, that's the start of the next group, not
            // another RHS value — bail and let the caller resume group parsing.
            ofs := 1
            for peek_kind(p, ofs) == .Newline { ofs += 1 }
            if peek_kind(p, ofs) == .Identifier {
                next_ofs := ofs + 1
                for peek_kind(p, next_ofs) == .Newline { next_ofs += 1 }
                k := peek_kind(p, next_ofs)
                if k == .Colon || k == .Comma {
                    break
                }
            }
        }
        advance(p) // consume ','
        append(&vals, parse_expr(p))
    }
    return vals
}

parse_stmt :: proc(p: ^Parser) -> Stmt {
    #partial switch current_kind(p) {
    case .Module:   return parse_module(p)
    case .Use, .Include:
        // Bare `use mara.time` (private) or `include mara.time` (re-export):
        // → Stmt_Decl with inferred name and the Expr_Include as init value.
        // The type checker recognizes Expr_Include and routes per is_reexport:
        //   is_reexport=false → flatten into the file env only (private)
        //   is_reexport=true  → flatten into file env AND module's pub env
        // Distinguishing bare from explicit `name := use ...` is done by which
        // parser branch was taken: this branch always means bare; .Identifier
        // rejects any Expr_Include reaching it.
        start := token_span(p,current(p))
        inc_expr := parse_primary(p)  // parses the keyword + path as Expr_Include
        inc, ok := inc_expr.(^Expr_Include)
        if !ok {
            // parse_primary on .Use / .Include normally returns Expr_Include;
            // reaching here means a parse error earlier in the path. Report
            // so the user sees a real diagnostic instead of a downstream type
            // error from a malformed Stmt_Decl.
            parse_error(p, current(p), PARSE_MALFORMED_USE_INCLUDE)
            return Stmt_Call{expr = inc_expr, span = start}
        }
        // Infer name from last segment: "mara.time" → "time", "math" → "math"
        name := inc.path
        if dot := strings.last_index(inc.path, "."); dot >= 0 {
            name = inc.path[dot+1:]
        }
        return make_single_decl(name, nil, inc_expr, start)
    case .Foreign:  return parse_foreign(p)
    case .Return:   return parse_return(p)
    case .Break:    return parse_break(p)
    case .Continue: return parse_continue(p)
    case .Defer:    return parse_defer(p)
    case .If:       return parse_if(p)
    case .Hash:
        // `#if` is a comptime if — the type checker evaluates the condition
        // and drops the dead arm before codegen. Other `#name` forms are
        // expressions, parsed via the normal expression path.
        if peek_kind(p, 1) == .If {
            advance(p) // consume '#'
            return parse_if(p, is_comptime = true)
        }
        // `#expose name :: fun ...` — decorator that marks a top-level fun for
        // DLL export (dllexport linkage + unmangled symbol). The decorator can
        // sit on the same line as the decl or on its own line above it; we
        // skip newlines between them so both styles parse identically.
        if peek_kind(p, 1) == .Identifier && peek_token(p, 1).text == "expose" {
            hash_tok := current(p)
            advance(p) // consume '#'
            advance(p) // consume 'expose'
            skip_newlines(p)
            inner := parse_stmt(p)
            scope, ok := inner.(^Stmt_Scope)
            if !ok || scope.kind != .Fun {
                parse_error(p, hash_tok, PARSE_EXPOSE_NEEDS_FUN_DECL)
                return inner
            }
            scope.is_exposed = true
            return scope
        }
        // `#packed` lives on the RHS of the declaration (`Name :: #packed
        // struct { ... }`). Catch the old prefix placement with a pointed
        // error instead of a generic expression-parse failure.
        if peek_kind(p, 1) == .Identifier && peek_token(p, 1).text == "packed" {
            parse_error(p, current(p), PARSE_PACKED_NEEDS_STRUCT_DECL)
            advance(p) // consume '#'
            advance(p) // consume 'packed'
            skip_newlines(p)
            return parse_stmt(p)
        }
        // Fall through to the expression-statement path below.
    case .Match:    return parse_match(p)
    case .For:      return parse_for(p)
    case .Overload: return parse_overload(p)
    case .Using:
        // `using` keyword for struct field embedding: `using foo: T` /
        // `using foo := value`. The user-visible `using` form on includes
        // (both `using x :: include path` and `using x := include path`)
        // has been dropped — file privacy makes it redundant. Bare
        // `include path` still flattens module exports as a parser
        // convenience; that path doesn't go through this branch.
        if peek_kind(p, 1) == .Identifier {
            saved_using := p.pos
            advance(p) // consume 'using'
            result, ok := try_parse_assign(p)
            if ok {
                // Reject `using ... include ...` — user-visible
                // using-include has been removed.
                value: Expr = nil
                if decl, is_decl := result.(^Stmt_Decl); is_decl {
                    decl.is_using = true
                    if len(decl.init_values) > 0 { value = decl.init_values[0] }
                }
                if def, is_def := result.(^Stmt_Define); is_def {
                    value = def.value
                }
                if _, is_inc := value.(^Expr_Include); is_inc {
                    tok := current(p)
                    parse_error(p, tok, PARSE_USING_NOT_ALLOWED_ON_INCLUDE, "...", "...")
                }
                return result
            }
            // Not a valid using-assign — restore
            p.pos = saved_using
        }
    case .Identifier:
        // Try assignment / compound assignment / index assignment / :: declarations
        result, ok := try_parse_assign(p)
        if ok {
            // Reject `name := use path` and `name := include path` (and the
            // typed `name : T = ...` variants). Modules are comptime-only —
            // the only honest spelling is `name :: use path` (or `:: include`).
            // Bare keyword forms go through the .Use/.Include branch above,
            // never here, so any Expr_Include reaching this point came from
            // an explicit user-written assignment.
            if decl, is_decl := result.(^Stmt_Decl); is_decl {
                for v in decl.init_values {
                    if _, is_inc := v.(^Expr_Include); is_inc {
                        tok := current(p)
                        parse_error(p, tok, PARSE_INCLUDE_NEEDS_COLON_COLON)
                        break
                    }
                }
            }
            return result
        }
        // Not an assignment — fall through to expression statement below
    }

    // Expression statement: function calls (including &expr.method(), name(), name.func())
    if current_kind(p) == .Identifier || current_kind(p) == .Ampersand {
        start := token_span(p,current(p))
        expr := parse_expr(p)
        return Stmt_Call{expr = expr, span = start}
    }

    // Fall through: not a valid statement
    tok := current(p)
    // Common shape mistake: `if cond { body } else { body }` (C-style).
    // The closing `}` already terminated the if and consumed it, so `else`
    // arrives here as a stand-alone token with no enclosing if to bind to.
    // Catch it specifically — the generic "unexpected token" message
    // doesn't hint at the actual fix.
    if tok.kind == .Else {
        parse_error(p, tok, PARSE_STRAY_ELSE)
    } else {
        parse_error(p, tok, PARSE_UNEXPECTED_TOKEN_STMT, tok.kind, tok.text)
    }
    advance(p)
    return Stmt_Call{span = token_span(p,tok)}
}

// ---------------------------------------------------------------------------
// Individual statement parsers
// ---------------------------------------------------------------------------

// parse_data_body and parse_inner_def removed — all fun bodies use parse_block now.

// Unified parse function for all `fun` / `struct` / `class` definitions.
// Handles both data-type scopes (structs) and executable scopes (functions).
//
//   fun { fields }                     — data-type, no generics
//   fun($T: type) { fields }          — data-type, generic
//   fun(a: int) -> int { body }       — executable, with params
//   fun($T: type, a: T) -> T { body } — executable, generic + params
//   fun() { body }                    — executable, no params
//
// `kind` comes from the declaration keyword and is stamped on the produced
// Stmt_Scope. struct/class → .Struct, fun → .Fun. Not yet read downstream
// (Step 1 of the unified-scope refactor).

// Parse a typed parameter group: `a, b, c: T` or `a: T = default`.
// `allow_defaults` controls whether `= expr` is accepted (only for regular
// fun declarations, not foreign ones).
// Parse the inner body of a typed parameter list, between caller-consumed
// parens. Tolerates newlines after the opening paren and between params, so
// callers can write either single-line or multi-line lists. Closing paren is
// the caller's responsibility — this just stops when it sees `.Right_Paren`.
parse_typed_param_loop :: proc(p: ^Parser, typed_params: ^[dynamic]Scope_Binding, allow_defaults: bool) {
    skip_newlines(p)
    if current_kind(p) == .Right_Paren { return }
    parse_typed_decl_group(p, typed_params, nil, allow_defaults, true)
    for current_kind(p) == .Comma || current_kind(p) == .Newline {
        if current_kind(p) == .Comma { advance(p) }
        skip_newlines(p)
        if current_kind(p) == .Right_Paren { break }
        parse_typed_decl_group(p, typed_params, nil, allow_defaults, true)
    }
    skip_newlines(p)
}

// Parse an optional `-> Type` or bare `Type` return clause. Appends parsed
// return types to `out` — void returns leave it empty, single-return appends
// one element, multi-return appends multiple. Used after every parameter list
// — function definitions, foreign-block prototypes, lambda signatures.
//
// After `->`, supports four shapes:
//   single:                -> Type
//   positional multi:      -> Type1, Type2
//   named multi:           -> name: Type, name: Type   (populates return_bindings)
//   parenthesized:         -> (Type1, Type2, ...)      — cosmetic parens around any of the above
//
// Newlines are tolerated between `)` and `->` and between `->` and the type,
// so wide signatures can wrap. We peek past newlines for an arrow or type
// starter; if neither follows, the position is restored so the trailing
// newline stays available for the caller's body parser.
parse_optional_return_types :: proc(p: ^Parser, out: ^[dynamic]Type_Expr) {
    saved := p.pos
    for current_kind(p) == .Newline { advance(p) }
    if current_kind(p) == .Arrow {
        advance(p) // consume '->'
        skip_newlines(p)
        parse_return_type_clause(p, out)
        return
    }
    if can_start_type_expr(p) {
        append(out, parse_type_expr(p))
        return
    }
    p.pos = saved
}

parse_return_type_clause :: proc(p: ^Parser, out: ^[dynamic]Type_Expr) {
    // Cosmetic outer parens: `-> (T, U)` and `-> T, U` are equivalent.
    // Parens are pure decoration — they do not produce a tuple type.
    wrapped := false
    if current_kind(p) == .Left_Paren {
        wrapped = true
        advance(p) // consume the wrapping '('
        skip_newlines(p)
    }

    // Named multi-return detection: `name:` or `name, name, ... : T`
    // Walk identifier-comma pairs until we see a colon (named) or anything
    // else (positional). Necessary because `Mat4, Mat4, Mat4` and
    // `a, b, c : T` share the leading `Ident, Ident, Ident, ...` shape — a
    // fixed-depth peek can't tell them apart once you go past two names.
    is_named := false
    if current_kind(p) == .Identifier {
        if peek_kind(p, 1) == .Colon {
            is_named = true
        } else if peek_kind(p, 1) == .Comma {
            i := 2
            for {
                if peek_kind(p, i) != .Identifier { break }      // positional
                i += 1
                if peek_kind(p, i) == .Colon { is_named = true; break }
                if peek_kind(p, i) != .Comma { break }           // positional
                i += 1
            }
        }
    }

    if is_named {
        clear(&p.return_bindings)
        parse_typed_decl_group(p, &p.return_bindings, out, false, false)
        for current_kind(p) == .Comma {
            advance(p)
            skip_newlines(p)
            parse_typed_decl_group(p, &p.return_bindings, out, false, false)
        }
    } else {
        // Positional: parse first type, then optional commas for multi-return
        append(out, parse_type_expr(p))
        for current_kind(p) == .Comma {
            advance(p)
            skip_newlines(p)
            append(out, parse_type_expr(p))
        }
    }

    if wrapped {
        skip_newlines(p)
        expect(p, .Right_Paren)
    }
}

// Parse one group of typed declarations: `name [, name ...] : [var]? T [= default]?`
// (or the `name(s) := default` short form when allow_defaults). Each name
// in the group produces a Scope_Binding appended to `out_bindings`.
//
// This is the single shared parser for param lists AND named-return lists.
// Both shapes are `name : Type` groups with the same name-loop, the same
// optional `var` modifier, and (for params) the same default-value tail.
// The two contexts differ only in which features they whitelist:
//
//   out_types     : non-nil for named-return parsing — the resolved type
//                   is also pushed once per name so the caller's positional
//                   type-list stays aligned with `p.return_bindings`. nil
//                   for params (which don't need a parallel type array).
//   allow_defaults: true for params (=default tail, := short form);
//                   false for returns (no defaults today).
//   allow_var     : true for params (var Type opts into runtime-sized
//                   aggregate instantiations); false for returns.
//
// `var` between the colon and the type opts the group into accepting
// VLA-shaped instantiations (`dst: var ^String` accepts a String
// parameterized by a runtime size). Without it, the binding refuses
// runtime-sized aggregate instantiations — runtime-length attack surface
// stays explicitly opt-in. Position mirrors local declarations
// (`x : var Array(byte, n)`).
//
// Open follow-up (TODO line "Unify declaration parsing..."): the statement-
// level decl path (try_parse_assign) still uses its own machinery because
// its multi-LHS shape is tuple-destructure (`x, y := call()`), not multi-
// name-shared-type. A deeper unification would need to reconcile those two
// "multi" forms or change one's surface.
// Parse the post-`:` tail of a multi-name declaration. Caller has already
// consumed the names and the colon. Returns the parsed shape as a neutral
// ^Stmt_Decl carrier — statement contexts use it directly, param/return
// contexts convert via stmt_decl_to_bindings.
//
// Shape parsed: [= RHS] | [var]? Type [= RHS]?
//
// `allow_defaults` allows the `= RHS` tail (and the bare `:=` short form,
// which is detected here by seeing `=` immediately after the colon).
// `allow_var` allows `var` before the type. `stop_at_group_break` is forwarded
// to parse_multi_rhs so param/return RHS parsing knows when to bail and let
// the caller resume group iteration.
//
// Init count is validated here once instead of at every caller: a group of
// N names accepts 0, 1, or N RHS values. Anything else is a parse error
// with an explicit message — surfaces earlier than the type checker would.
parse_decl_tail :: proc(p: ^Parser, names: [dynamic]string, start: Span, allow_var: bool, allow_defaults: bool, stop_at_group_break: bool) -> ^Stmt_Decl {
    decl := new(Stmt_Decl)
    decl.names = names
    decl.span = start

    if allow_defaults && current_kind(p) == .Equals {
        // `name(s) := RHS` short form — type inferred from RHS
        advance(p)
        decl.init_values = parse_multi_rhs(p, len(names), stop_at_group_break)
        validate_init_count(p, len(decl.init_values), len(names))
        return decl
    }

    decl.type_expr = parse_type_expr(p)

    if allow_defaults && current_kind(p) == .Equals {
        advance(p)
        decl.init_values = parse_multi_rhs(p, len(names), stop_at_group_break)
        validate_init_count(p, len(decl.init_values), len(names))
    }

    return decl
}

validate_init_count :: proc(p: ^Parser, init_n: int, n_names: int) {
    if init_n != 0 && init_n != 1 && init_n != n_names {
        tok := current(p)
        parse_error(p, tok, PARSE_DEFAULT_VALUE_COUNT_MISMATCH, init_n, n_names, n_names)
    }
}

// Distribute a parsed multi-name decl into the param/return-context
// Scope_Binding shape. Each name gets its own binding with type copied
// from the decl and a default_value taken from
// init_values per the distribution rule:
//
//   N names, init_n=0 → no defaults.
//   N names, init_n=N → parallel (each name takes its own value).
//   N names, init_n=1, N=1 → single value to single name.
//   N names, init_n=1, N>1 → tuple-destructure: emit Expr_Tuple_Default
//                            per binding, all referencing the SAME source
//                            (identity-shared, not cloned) so codegen
//                            evaluates the source once at each call site
//                            and routes its tuple slots to the bindings.
//
// out_types is optional — non-nil for named-return parsing, which keeps
// a parallel type list alongside p.return_bindings.
stmt_decl_to_bindings :: proc(decl: ^Stmt_Decl, out_bindings: ^[dynamic]Scope_Binding, out_types: ^[dynamic]Type_Expr) {
    init_n := len(decl.init_values)
    is_tuple_destructure := init_n == 1 && len(decl.names) > 1
    for name, i in decl.names {
        dv: Expr
        if is_tuple_destructure {
            dv = new_clone(Expr_Tuple_Default{
                source = decl.init_values[0],
                index  = i,
                span   = decl.span,
            })
        } else if init_n == 1 {
            dv = i == 0 ? decl.init_values[0] : clone_expr(decl.init_values[0])
        } else if init_n == len(decl.names) {
            dv = decl.init_values[i]
        }
        append(out_bindings, Scope_Binding{
            name          = name,
            type_expr     = decl.type_expr,
            default_value = dv,
        })
        if out_types != nil {
            append(out_types, decl.type_expr)
        }
    }
}

// Param/return entry point for the unified declaration parser. Parses the
// name list (with the param-specific lookahead — only consume `, name`
// when the next token is `,` or `:`), consumes the colon, delegates the
// tail to parse_decl_tail, and converts the result into the Scope_Binding
// shape that param/return contexts expect.
parse_typed_decl_group :: proc(p: ^Parser, out_bindings: ^[dynamic]Scope_Binding, out_types: ^[dynamic]Type_Expr, allow_defaults: bool, allow_var: bool) {
    start := token_span(p,current(p))
    names: [dynamic]string
    append(&names, expect(p, .Identifier).text)
    for current_kind(p) == .Comma {
        if peek_kind(p, 1) == .Identifier && (peek_kind(p, 2) == .Comma || peek_kind(p, 2) == .Colon) {
            advance(p) // consume ','
            skip_newlines(p)
            append(&names, expect(p, .Identifier).text)
        } else {
            break
        }
    }
    expect(p, .Colon)

    decl := parse_decl_tail(p, names, start, allow_var, allow_defaults, true)
    stmt_decl_to_bindings(decl, out_bindings, out_types)
}

// Returns true if `te` (or any nested type expression inside it) references
// the bare type name `name`. Used by struct param promotion to decide whether
// a non-`$` typed_param is actually a compile-time generic (used in a type
// position somewhere in the struct body, like `[n]item`) or just a runtime
// constructor arg (used only in value positions like `sys_alloc(cap)`).
type_expr_refs_name :: proc(te: Type_Expr, name: string) -> bool {
    switch t in te {
    case Type_Name:
        return t.name == name
    case Type_Of_Name:
        return false
    case ^Type_Array:
        if t.size_name == name { return true }
        return type_expr_refs_name(t.elem, name)
    case ^Type_Pointer:
        return type_expr_refs_name(t.elem, name)
    case ^Type_Slice_Expr:
        return type_expr_refs_name(t.elem, name)
    case ^Type_Partial_Array_Expr:
        if t.size_name == name { return true }
        return type_expr_refs_name(t.elem, name)
    case ^Type_Generic_Instance:
        for arg in t.type_args {
            if type_expr_refs_name(arg, name) { return true }
        }
        return false
    case ^Type_Func_Expr:
        for pt in t.params {
            if type_expr_refs_name(pt, name) { return true }
        }
        for rt in t.return_types {
            if type_expr_refs_name(rt, name) { return true }
        }
        return false
    case Type_Const_Value:
        return false
    case Type_Const_Expr:
        return false
    }
    return false
}

// Walk `body` looking for field-shaped statements (Stmt_Assign, Stmt_Multi_Assign,
// Stmt_Decl) and record which `params` names appear in any field's type expression.
// Used by parse_scope_def to decide which typed_params to promote to generic_params.
collect_body_type_refs :: proc(body: [dynamic]Stmt, params: []Scope_Binding, refs: ^map[string]bool) {
    for stmt in body {
        #partial switch s in stmt {
        case ^Stmt_Assign:
            for p in params {
                if type_expr_refs_name(s.type_expr, p.name) { refs[p.name] = true }
            }
        case ^Stmt_Multi_Assign:
            for a in s.assigns {
                for p in params {
                    if type_expr_refs_name(a.type_expr, p.name) { refs[p.name] = true }
                }
            }
        case ^Stmt_Decl:
            for p in params {
                if type_expr_refs_name(s.type_expr, p.name) { refs[p.name] = true }
            }
        }
    }
}

parse_scope_def :: proc(p: ^Parser, name: string, start: Span, kind: Scope_Kind) -> Stmt {
    advance(p) // consume 'fun' / 'struct' / 'class'

    // p.dollar_params is the parser-wide buffer collecting `$T` introductions
    // during parse_type_expr. It belongs to *this* scope_def — save and
    // reset on entry, restore on exit so a previous sibling's leftovers
    // don't bleed into us (the bug: an empty-param-list scope after a
    // generic sibling would inherit the sibling's $T's into its own
    // generic_params merge below) and a nested scope_def can't trample
    // its parent's accumulating set during body parsing.
    saved_dollar := p.dollar_params
    p.dollar_params = {}
    defer p.dollar_params = saved_dollar

    // Case 1: fun { ... } — data-type fun, no params
    if current_kind(p) == .Left_Brace {
        body, is_intrinsic, intrinsic_name := parse_scope_body(p)
        stmt := new(Stmt_Scope)
        stmt.name = name
        stmt.kind = kind
        stmt.body = body
        stmt.is_intrinsic = is_intrinsic
        stmt.intrinsic_name = intrinsic_name
        stmt.span = start
        return stmt
    }

    // Case 2: fun(...) — parse parens content to determine kind
    expect(p, .Left_Paren)
    skip_newlines(p)

    // Parse leading generic parameters: $T: type, $N: int = 256
    generic_params: [dynamic]Generic_Param
    for current_kind(p) == .Dollar {
        advance(p) // consume '$'
        gname_tok := expect(p, .Identifier)
        expect(p, .Colon)
        type_tok := expect(p, .Identifier) // "type", "uint", "int", etc.
        if type_tok.text == "type" {
            append(&generic_params, Generic_Param{name = gname_tok.text, span = token_span(p,gname_tok)})
        } else {
            gp := Generic_Param{
                name = gname_tok.text,
                span = token_span(p,gname_tok),
                is_const = true,
                const_type = type_tok.text,
            }
            if current_kind(p) == .Equals {
                advance(p) // consume '='
                val_tok := expect(p, .Number)
                gp.default_value = parse_int_token(val_tok.text)
                gp.has_default = true
            }
            append(&generic_params, gp)
        }
        if current_kind(p) == .Comma {
            advance(p) // consume ','
            skip_newlines(p)
        }
    }

    // If we've reached ')' with only $-params, check what follows to decide kind
    if current_kind(p) == .Right_Paren {
        advance(p) // consume ')'
        skip_newlines(p)

        if current_kind(p) == .Arrow || can_start_type_expr(p) {
            // fun($T: type) -> T { body } or fun($T: type) T { body }
            // Also: fun() -> Type, Type ... { body } — multi-return appends
            // each type into return_types directly (no tuple wrapping).
            if current_kind(p) == .Arrow {
                advance(p) // consume optional '->'
                skip_newlines(p) // allow newline between -> and the return type
            }
            return_types: [dynamic]Type_Expr
            parse_return_type_clause(p, &return_types)
            for dp in p.dollar_params {
                already_exists := false
                for gp in generic_params { if gp.name == dp.name { already_exists = true; break } }
                if !already_exists { append(&generic_params, dp) }
            }
            skip_newlines(p)
            body, is_intrinsic, intrinsic_name := parse_scope_body(p)
            stmt := new(Stmt_Scope)
            stmt.name = name
            stmt.kind = kind
            stmt.generic_params = generic_params
            stmt.return_types = return_types
            stmt.return_bindings = p.return_bindings
            p.return_bindings = {}
            stmt.body = body
            stmt.is_intrinsic = is_intrinsic
            stmt.intrinsic_name = intrinsic_name
            stmt.has_parens = true
            stmt.span = start
            return stmt
        }

        if len(generic_params) > 0 {
            // fun($T: type) { fields } — data-type fun with generic params only
            skip_newlines(p)
            body, is_intrinsic, intrinsic_name := parse_scope_body(p)
            stmt := new(Stmt_Scope)
            stmt.name = name
            stmt.kind = kind
            stmt.generic_params = generic_params
            stmt.body = body
            stmt.is_intrinsic = is_intrinsic
            stmt.intrinsic_name = intrinsic_name
            stmt.has_parens = true
            stmt.span = start
            return stmt
        }

        // fun() Type { body } or fun() -> Type { body } or fun() { body }
        return_types: [dynamic]Type_Expr
        parse_optional_return_types(p, &return_types)
        skip_newlines(p)
        body, is_intrinsic, intrinsic_name := parse_scope_body(p)
        stmt := new(Stmt_Scope)
        stmt.name = name
        stmt.kind = kind
        stmt.return_types = return_types
        stmt.return_bindings = p.return_bindings
        p.return_bindings = {}
        stmt.body = body
        stmt.is_intrinsic = is_intrinsic
        stmt.intrinsic_name = intrinsic_name
        stmt.has_parens = true
        stmt.span = start
        return stmt
    }

    // We have non-$ params after the generics — this is an executable fun
    clear(&p.dollar_params)

    typed_params: [dynamic]Scope_Binding
    parse_typed_param_loop(p, &typed_params, true)
    expect(p, .Right_Paren)

    return_types: [dynamic]Type_Expr
    parse_optional_return_types(p, &return_types)

    skip_newlines(p)
    body, is_intrinsic, intrinsic_name := parse_scope_body(p)

    // For struct/class kind: promote typed_params to generic_params when they're
    // either introduced as type variables (`name: $T`) or referenced in a type
    // position somewhere in the body (e.g. `using items: [n]item`). Plain runtime
    // ctor args (like `Arena_Basic :: class(cap: i64)` where cap is only used in
    // value-position expressions like `sys_alloc(cap)`) stay as typed_params.
    // (struct and class are synonymous in Mara — same rule for both.)
    if kind == .Struct && len(typed_params) > 0 {
        // Collect param names referenced in any field's type expression.
        type_referenced: map[string]bool
        defer delete(type_referenced)
        collect_body_type_refs(body, typed_params[:], &type_referenced)

        skip_dollar: map[string]bool
        defer delete(skip_dollar)
        promoted: [dynamic]Scope_Binding
        for tp in typed_params {
            if tn, ok := tp.type_expr.(Type_Name); ok {
                // Case 0: `name: ~T` — shape-constrained type parameter.
                // The `~` makes this an interface-shaped slot: any concrete
                // type satisfying T's API + size budget binds at instantiation.
                // `~T` here is the *declaration* — separate from `~T` at
                // use-sites (which is rejected; see resolve_type_expr).
                //
                // An optional default like `name: ~T = void` (or any other
                // type name) is parsed as an Expr in tp.default_value; we
                // pluck the identifier out and stash it as a Type_Expr so
                // the resolver can fill it in when the caller omits the
                // type-arg (e.g. bare `Program` or `Program()` instantiation).
                if tn.tilde {
                    gp := Generic_Param{
                        name             = tp.name,
                        span             = tn.span,
                        shape_constraint = tn.name,
                    }
                    if id, id_ok := tp.default_value.(^Expr_Ident); id_ok {
                        gp.default_type_expr = Type_Name{name = id.name, span = id.span}
                    }
                    append(&generic_params, gp)
                    continue
                }
                // Case 1: `name: $T` pattern — type was introduced via $ here.
                is_dollar := false
                for dp in p.dollar_params {
                    if dp.name == tn.name { is_dollar = true; break }
                }
                if is_dollar {
                    append(&generic_params, Generic_Param{
                        name = tp.name,
                        span = tn.span,
                    })
                    skip_dollar[tn.name] = true
                    continue
                }
                // Case 2: `name: prim` and the body uses `name` in a type position.
                if type_referenced[tp.name] {
                    gp := Generic_Param{
                        name = tp.name,
                        span = tn.span,
                        is_const = true,
                        const_type = tn.name,
                    }
                    if num, num_ok := tp.default_value.(^Expr_Number); num_ok {
                        gp.default_value = int(i64(num.int_value))
                        gp.has_default = true
                    }
                    append(&generic_params, gp)
                    continue
                }
            }
            // Otherwise: leave as typed_param (runtime ctor arg).
            append(&promoted, tp)
        }
        typed_params = promoted

        // Drop promoted $-introductions from dollar_params before merge.
        new_dollar: [dynamic]Generic_Param
        for dp in p.dollar_params {
            if !skip_dollar[dp.name] { append(&new_dollar, dp) }
        }
        p.dollar_params = new_dollar
    }

    // Merge inferred generic params from types
    for dp in p.dollar_params {
        already_exists := false
        for gp in generic_params { if gp.name == dp.name { already_exists = true; break } }
        if !already_exists { append(&generic_params, dp) }
    }

    stmt := new(Stmt_Scope)
    stmt.name = name
    stmt.kind = kind
    stmt.generic_params = generic_params
    stmt.typed_params = typed_params
    stmt.return_types = return_types
    stmt.return_bindings = p.return_bindings
    p.return_bindings = {}
    stmt.body = body
    stmt.is_intrinsic = is_intrinsic
    stmt.intrinsic_name = intrinsic_name
    stmt.has_parens = true
    stmt.span = start
    return stmt
}

// Parse union definition: Name :: union(optional_size) { Variant = tag { fields }, ... }
// Produces a single Stmt_Union_Def holding [dynamic]Union_Variant_Def.
parse_union_def_with_name :: proc(p: ^Parser, name: string, start: Span) -> Stmt {
    advance(p) // consume 'union'

    // Header options, all comma-separated:
    //   $T: type      — generic type parameter (monomorphized per use)
    //   $N: int = 256 — generic const parameter (currently unused on unions, kept for parity)
    //   tag <type>    — discriminant type (e.g. `tag u32`); default i64
    //   pad <type>    — typed padding between tag and payload (e.g. `pad u32`,
    //                   reachable from user code via `value.pad`)
    //   size <N>      — minimum total size in bytes
    // Examples:
    //   union(tag u32) { ... }
    //   union($T: type) { None, Some { value: T } }
    //   union($T: type, tag i8) { ... }
    min_size := 0
    tag_type := ""
    tag_pad: Type_Expr
    generic_params: [dynamic]Generic_Param
    if current_kind(p) == .Left_Paren {
        advance(p) // consume '('
        for current_kind(p) != .Right_Paren && current_kind(p) != .EOF {
            tok := current(p)
            if tok.kind == .Dollar {
                advance(p) // consume '$'
                gname_tok := expect(p, .Identifier)
                expect(p, .Colon)
                type_tok := expect(p, .Identifier) // "type", "int", "uint", etc.
                if type_tok.text == "type" {
                    append(&generic_params, Generic_Param{name = gname_tok.text, span = token_span(p,gname_tok)})
                } else {
                    gp := Generic_Param{
                        name = gname_tok.text,
                        span = token_span(p,gname_tok),
                        is_const = true,
                        const_type = type_tok.text,
                    }
                    if current_kind(p) == .Equals {
                        advance(p) // consume '='
                        val_tok := expect(p, .Number)
                        gp.default_value = parse_int_token(val_tok.text)
                        gp.has_default = true
                    }
                    append(&generic_params, gp)
                }
            } else if tok.kind == .Identifier && tok.text == "tag" {
                advance(p)
                if is_type_keyword(current_kind(p)) {
                    tag_type = current(p).text
                    advance(p)
                } else {
                    parse_error(p, current(p), PARSE_UNION_TAG_NEEDS_TYPE, current(p).text)
                }
            } else if tok.kind == .Identifier && tok.text == "pad" {
                advance(p)
                tag_pad = parse_type_expr(p)
            } else if tok.kind == .Identifier && tok.text == "size" {
                advance(p)
                if current_kind(p) == .Number {
                    min_size = parse_int_token(current(p).text)
                    advance(p)
                } else {
                    parse_error(p, current(p), PARSE_UNION_SIZE_NEEDS_NUM, current(p).text)
                }
            } else {
                parse_error(p, tok, PARSE_UNION_HEADER_UNKNOWN, tok.text)
                advance(p) // skip unrecognized token to avoid infinite loop
            }
            if current_kind(p) == .Comma { advance(p) }
            skip_newlines(p)
        }
        expect(p, .Right_Paren)
    }

    skip_newlines(p)
    expect(p, .Left_Brace)
    skip_newlines(p)

    // Parse variant definitions
    variant_defs: [dynamic]Union_Variant_Def
    auto_tag := 0

    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        variant_name := expect(p, .Identifier).text

        // Optional explicit tag: = N
        tag := auto_tag
        has_tag := false
        if current_kind(p) == .Equals {
            advance(p) // consume '='
            negative := false
            if current_kind(p) == .Minus {
                advance(p)
                negative = true
            }
            val_tok := expect(p, .Number)
            val := parse_int_token(val_tok.text)
            if negative { val = -val }
            tag = val
            has_tag = true
            auto_tag = val + 1
        } else {
            auto_tag = tag + 1
        }

        // Optional inline fields: { field: type, ... }
        fields: [dynamic]Scope_Binding
        if current_kind(p) == .Left_Brace {
            advance(p) // consume '{'
            skip_newlines(p)
            for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
                field_name := expect(p, .Identifier).text
                expect(p, .Colon)
                type_expr := parse_type_expr(p)
                default_val: Expr = nil
                if current_kind(p) == .Equals {
                    advance(p)
                    default_val = parse_expr(p)
                }
                append(&fields, Scope_Binding{name = field_name, type_expr = type_expr, default_value = default_val})
                if current_kind(p) == .Comma { advance(p) }
                skip_newlines(p)
            }
            expect(p, .Right_Brace)
        }

        append(&variant_defs, Union_Variant_Def{name = variant_name, tag = tag, has_tag = has_tag, fields = fields})
        if current_kind(p) == .Comma { advance(p) }
        skip_newlines(p)
    }

    expect(p, .Right_Brace)

    union_stmt := new(Stmt_Union_Def)
    union_stmt.name = name
    union_stmt.tag_type = tag_type
    union_stmt.min_size = min_size
    union_stmt.tag_pad = tag_pad
    union_stmt.variants = variant_defs
    union_stmt.generic_params = generic_params
    union_stmt.span = start
    return union_stmt
}

// `Name :: error { Variant_A, Variant_B, ... }`. Flat tag set — no header
// options, no payloads, no explicit tag assignments. Variants get globally
// unique u32 IDs at type-check time so any error_kind variant satisfies the
// open `err` type (Stage 2). Lowers to Stmt_Union_Def with is_error_kind=true
// so downstream stages share the existing enum machinery.
parse_error_def_with_name :: proc(p: ^Parser, name: string, start: Span) -> Stmt {
    advance(p) // consume 'error'
    skip_newlines(p)
    expect(p, .Left_Brace)
    skip_newlines(p)

    variant_defs: [dynamic]Union_Variant_Def
    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        variant_name := expect(p, .Identifier).text
        // Tag value is filled in at type-check time (set_id<<16 | local_tag).
        append(&variant_defs, Union_Variant_Def{name = variant_name})
        if current_kind(p) == .Comma { advance(p) }
        skip_newlines(p)
    }
    expect(p, .Right_Brace)

    s := new(Stmt_Union_Def)
    s.name = name
    s.tag_type = "u32"   // packed (set_id, tag) — see type-checker for assignment
    s.variants = variant_defs
    s.is_error_kind = true
    s.span = start
    return s
}

parse_dispatch_def_with_name :: proc(p: ^Parser, name: string, start: Span) -> Stmt {
    advance(p) // consume 'dispatch'
    expect(p, .Left_Brace)
    skip_newlines(p)

    functions: [dynamic]string
    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        fn_tok := expect(p, .Identifier)
        append(&functions, fn_tok.text)
        skip_separator(p)
    }
    expect(p, .Right_Brace)

    stmt := new(Stmt_Dispatch_Def)
    stmt.name = name
    stmt.functions = functions
    stmt.span = start
    return stmt
}

parse_overload :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'overload'

    op_tok := advance(p)
    op: Token_Kind
    #partial switch op_tok.kind {
    case .Star:   op = .Star
    case .Plus:   op = .Plus
    case .Minus:  op = .Minus
    case .Slash:  op = .Slash
    case .Modulo: op = .Modulo
    case:
        parse_error(p, op_tok, PARSE_OVERLOAD_EXPECTED_OP, op_tok.text)
    }

    dispatch_name := expect(p, .Identifier).text
    return Stmt_Overload{op = op, dispatch_name = dispatch_name, span = start}
}


parse_foreign :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'foreign'

    // Syntax: foreign static_lib "name" [prefix Foo_] { ... }
    //
    // The linker resolves the library via the import lib at link time; Windows
    // / the loader handle DLL load + symbol resolution at process load. If a
    // user wants runtime loading (plugin systems, "don't crash if libfoo isn't
    // installed"), they call mara.os.load_library + find_symbol themselves.
    kind_tok := current(p)
    if kind_tok.kind == .Identifier && kind_tok.text == "static_lib" {
        advance(p)
    } else {
        parse_error(p, kind_tok, PARSE_FOREIGN_NEEDS_STATIC_LIB, kind_tok.text)
    }

    // Library name as string literal
    lib_tok := expect(p, .String)

    // Optional `prefix <ident>` clause: defaults to no prefix.
    prefix := ""
    if current_kind(p) == .Identifier && current(p).text == "prefix" {
        advance(p) // consume `prefix`
        prefix_tok := expect(p, .Identifier)
        prefix = prefix_tok.text
    }

    skip_newlines(p)
    expect(p, .Left_Brace)
    skip_newlines(p)

    decls: [dynamic]Foreign_Fun

    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        // Each foreign decl is a Mara function signature with no body —
        // `fun Name(params) -> Type`. Sharing the param-loop and return-type
        // helpers with parse_scope_def means multi-line param lists work
        // (newlines after `(` and between params are tolerated) and any future
        // signature improvements automatically apply here too.
        fun_start := token_span(p,current(p))
        expect(p, .Fun)
        name_tok := expect(p, .Identifier)
        expect(p, .Left_Paren)

        typed_params: [dynamic]Scope_Binding
        parse_typed_param_loop(p, &typed_params, false)
        expect(p, .Right_Paren)

        return_types: [dynamic]Type_Expr
        parse_optional_return_types(p, &return_types)

        append(&decls, Foreign_Fun{
            name = name_tok.text,
            typed_params = typed_params,
            return_types = return_types,
            span = fun_start,
        })
        skip_newlines(p)
    }

    expect(p, .Right_Brace)

    stmt := new(Stmt_Foreign)
    stmt.library = lib_tok.text
    stmt.prefix = prefix
    stmt.decls = decls
    stmt.span = start
    return stmt
}

parse_return :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'return'
    values: [dynamic]Expr
    // Bare `return` in a void function: no expression follows. Detect by
    // peeking for statement-terminator tokens. Without this, `return` would
    // greedily call parse_expr which errors on the trailing newline.
    kind := current_kind(p)
    if kind == .Newline || kind == .Right_Brace || kind == .Semicolon || kind == .EOF {
        return Stmt_Return{values = values, span = start}
    }
    append(&values, parse_expr(p))
    for current_kind(p) == .Comma {
        advance(p) // consume ','
        append(&values, parse_expr(p))
    }
    return Stmt_Return{values = values, span = start}
}

parse_break :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p)
    return Stmt_Break{span = start}
}

parse_continue :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p)
    return Stmt_Continue{span = start}
}

// `defer <stmt>` or `defer { ... }`. The body runs on enclosing-scope exit
// (LIFO across defers in the same scope). Single-statement form is same-line;
// block form may span lines.
parse_defer :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'defer'
    body: [dynamic]Stmt

    skip_newlines(p)
    if current_kind(p) == .Left_Brace {
        advance(p) // consume '{'
        skip_newlines(p)
        for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
            append(&body, parse_stmt(p))
            skip_separator(p)
        }
        expect(p, .Right_Brace)
    } else {
        append(&body, parse_stmt(p))
    }

    stmt := new(Stmt_Defer)
    stmt.body = body
    stmt.span = start
    return stmt
}


is_if_branch_end :: proc(p: ^Parser) -> bool {
    kind := current_kind(p)
    if kind == .Right_Brace do return true
    if kind == .Else do return true
    if kind == .Elif do return true
    if kind == .EOF do return true
    return false
}

parse_if_branch_body :: proc(p: ^Parser) -> [dynamic]Stmt {
    skip_newlines(p)
    body: [dynamic]Stmt
    for !is_if_branch_end(p) {
        append(&body, parse_stmt(p))
        skip_separator(p)
    }
    return body
}

// if cond do then_expr else else_expr — expression form (used in expression context only)
parse_if_expr :: proc(p: ^Parser) -> Expr {
    tok := advance(p) // consume 'if'
    p.no_struct_lit = true
    condition := parse_expr(p)
    p.no_struct_lit = false
    expect(p, .Do)
    then_expr := parse_expr(p)
    if _, is_if := then_expr.(^Expr_If); is_if {
        parse_error(p, tok, PARSE_NESTED_IF_EXPR)
    }
    expect(p, .Else)
    else_expr := parse_expr(p)
    if _, is_if := else_expr.(^Expr_If); is_if {
        parse_error(p, tok, PARSE_NESTED_IF_EXPR)
    }
    e := new(Expr_If)
    e.condition = condition
    e.then_expr = then_expr
    e.else_expr = else_expr
    e.span = token_span(p,tok)
    return e
}

parse_if :: proc(p: ^Parser, is_comptime := false) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'if'
    p.no_struct_lit = true
    condition := parse_expr(p)
    p.no_struct_lit = false
    skip_newlines(p)

    // Single-statement form: if cond do stmt
    if current_kind(p) == .Do {
        advance(p) // consume 'do'
        body: [dynamic]Stmt
        append(&body, parse_stmt(p))
        stmt := new(Stmt_If)
        stmt.condition = condition
        stmt.body = body
        stmt.is_comptime = is_comptime
        stmt.span = start
        return stmt
    }

    expect(p, .Left_Brace)
    skip_newlines(p)

    body := parse_if_branch_body(p)

    // Parse elif/else chain (all inside the outer { }). `elif` is the chain
    // keyword; a plain `else` is the final branch — so an `if` appearing inside
    // an `else` body is now just an ordinary nested if-statement.
    else_body: [dynamic]Stmt
    if current_kind(p) == .Elif {
        append(&else_body, parse_elif_chain(p))
    } else if current_kind(p) == .Else {
        advance(p) // consume 'else'
        skip_newlines(p)
        else_body = parse_if_branch_body(p)
    }

    expect(p, .Right_Brace)

    stmt := new(Stmt_If)
    stmt.condition = condition
    stmt.body = body
    stmt.else_body = else_body
    stmt.is_comptime = is_comptime
    stmt.span = start
    return stmt
}

// Helper for elif chains (3+ branches)
parse_elif_chain :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'elif'
    p.no_struct_lit = true
    condition := parse_expr(p)
    p.no_struct_lit = false
    skip_newlines(p)
    body := parse_if_branch_body(p)

    else_body: [dynamic]Stmt
    if current_kind(p) == .Elif {
        append(&else_body, parse_elif_chain(p))
    } else if current_kind(p) == .Else {
        advance(p) // consume 'else'
        skip_newlines(p)
        else_body = parse_if_branch_body(p)
    }

    stmt := new(Stmt_If)
    stmt.condition = condition
    stmt.body = body
    stmt.else_body = else_body
    stmt.span = start
    return stmt
}

is_match_arm_start :: proc(p: ^Parser) -> bool {
    kind := current_kind(p)
    if kind == .Right_Brace do return true
    if kind == .EOF do return true
    if kind == .Dot && peek_kind(p) == .Identifier do return true
    if kind == .Identifier {
        pk := peek_kind(p)
        if pk == .Identifier || pk == .Newline do return true
        // Bare variant followed by a statement keyword (e.g. X return [...])
        if pk == .Return || pk == .If || pk == .For || pk == .Match || pk == .Break || pk == .Continue do return true
        // Bare variant followed by a brace-delimited body
        if pk == .Left_Brace do return true
        // Bare variant followed by `do stmt` (single-statement arm body)
        if pk == .Do do return true
        // Field-path or indexed predicate (e.g. `keyboard.pressed[W] do …`).
        // Scan ahead through `.field` and `[…]` segments and accept if the
        // chain ends on `do` or a body-opening newline (arm-pattern shape) —
        // reject if it ends on `=` or other assignment-like tokens (statement
        // shape inside a body).
        if pk == .Dot || pk == .Left_Bracket {
            return scan_path_arm_terminator(p)
        }
    }
    if kind == .Number || kind == .String || kind == .Char do return true
    if kind == .Else do return true
    return false
}

// Look ahead through a path-like prefix (`.field`, `[…]` segments) to see if
// it terminates at an arm-pattern marker (`do`, `\n`) or at a statement-like
// continuation (`=`, `+=`, etc.). Used by is_match_arm_start to distinguish
// `keyboard.pressed[W] do moveUp()` (a new arm) from `game.running = false`
// (a statement inside the previous arm's body).
scan_path_arm_terminator :: proc(p: ^Parser) -> bool {
    pos := p.pos + 1  // start after the leading identifier
    bracket_depth := 0
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        if bracket_depth > 0 {
            #partial switch k {
            case .Left_Bracket:  bracket_depth += 1
            case .Right_Bracket: bracket_depth -= 1
            case .EOF:           return false
            }
            pos += 1
            continue
        }
        #partial switch k {
        case .Dot, .Identifier:
            pos += 1
            continue
        case .Left_Bracket:
            bracket_depth += 1
            pos += 1
            continue
        case .Do, .Newline:
            return true
        case .Left_Brace:
            // `path { … }` — a brace body would only be valid as an arm if
            // the parser supported it for predicate arms (it doesn't today,
            // but accepting here keeps is_match_arm_start permissive).
            return true
        }
        // Anything else (Equals, Plus_Equal, Left_Paren for a call, etc.) —
        // this is statement continuation, not a new arm.
        return false
    }
    return false
}

parse_match_arm_body :: proc(p: ^Parser) -> [dynamic]Stmt {
    skip_newlines(p)
    body: [dynamic]Stmt
    for !is_match_arm_start(p) {
        append(&body, parse_stmt(p))
        skip_separator(p)
    }
    return body
}

parse_match :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'match'

    // Strict-default: every match covers all variants of its union subject
    // (or uses `else` as an explicit opt-out). match dispatches on a union
    // value, so it always needs a subject — subject-less `match { }` and the
    // other non-union forms were removed; use if/elif for value or predicate
    // branching.
    subject: Expr
    for current_kind(p) == .Newline { advance(p) }
    if current_kind(p) == .Left_Brace {
        parse_error(p, current(p), PARSE_MATCH_NEEDS_SUBJECT)
    } else {
        p.no_struct_lit = true
        subject = parse_expr(p)
        p.no_struct_lit = false
        skip_newlines(p)
    }
    expect(p, .Left_Brace)
    skip_newlines(p)

    arms: [dynamic]Match_Arm

    for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
        skip_newlines(p)
        if current_kind(p) == .Else {
            // Wildcard arm: else (must be last)
            // Note: when an arm body ends with an `if` that has no `else` of
            // its own, the dangling-else rule means the next `else` is
            // consumed by the if-statement's else-branch, not as a match
            // wildcard. To get a match-wildcard `else` after an if-arm body,
            // the inner if must terminate (have its own else, or use a do-form
            // without else). Standard C-family behavior.
            advance(p) // consume 'else'
            body: [dynamic]Stmt
            // Allow `else do <stmt>` as a single-line arm, mirroring the value-arm
            // shape. Without this, `else` is forced into a multi-line indented
            // body block — fine for big handlers, awkward when you just want
            // "anything else, do this one thing."
            if current_kind(p) == .Do {
                advance(p) // consume 'do'
                append(&body, parse_stmt(p))
                skip_newlines(p)
            } else {
                body = parse_match_arm_body(p)
            }
            append(&arms, Match_Arm{is_else = true, body = body})
        } else if current_kind(p) == .Dot && peek_kind(p) == .Identifier {
            // Dot shorthand arm: .Variant
            advance(p) // consume '.'
            variant_tok := advance(p)
            body := parse_match_arm_body(p)
            append(&arms, Match_Arm{dot_shorthand = variant_tok.text, body = body})
        } else if current_kind(p) == .Identifier && peek_kind(p) == .Identifier {
            // Union arm with binding: VariantName bindingName [do stmt | <indented body>]
            variant_tok := advance(p)
            binding_tok := advance(p)
            body: [dynamic]Stmt
            if current_kind(p) == .Do {
                advance(p) // consume 'do'
                append(&body, parse_stmt(p))
                skip_newlines(p)
            } else {
                body = parse_match_arm_body(p)
            }
            append(&arms, Match_Arm{
                variant_name = variant_tok.text,
                binding_name = binding_tok.text,
                is_union_arm = true,
                body = body,
            })
        } else if current_kind(p) == .Identifier && (peek_kind(p) == .Newline || peek_kind(p) == .Do) {
            // Union arm without binding:
            //   VariantName            (on its own line, body indented)
            //   VariantName do stmt    (single-statement form, same line)
            variant_tok := advance(p)
            body: [dynamic]Stmt
            if current_kind(p) == .Do {
                advance(p) // consume 'do'
                append(&body, parse_stmt(p))
                skip_newlines(p)
            } else {
                body = parse_match_arm_body(p)
            }
            append(&arms, Match_Arm{
                variant_name = variant_tok.text,
                binding_name = "",
                is_union_arm = true,
                body = body,
            })
        } else {
            // Variant pattern in value position (e.g. a literal that resolves
            // to a union/enum variant). Boundary detectable via number/string/
            // char. Non-union subjects are rejected by the type checker.
            value := parse_expr(p)

            body: [dynamic]Stmt
            if current_kind(p) == .Do {
                advance(p) // consume 'do'
                append(&body, parse_stmt(p))
                skip_newlines(p)
            } else {
                body = parse_match_arm_body(p)
            }
            append(&arms, Match_Arm{value = value, body = body})
        }
    }
    expect(p, .Right_Brace)

    stmt := new(Stmt_Match)
    stmt.subject = subject
    stmt.arms = arms
    stmt.span = start
    return stmt
}

// Loop body: single-statement `do stmt` form or a `{ ... }` block.
// Shared by all four for-loop forms so `do` behaves uniformly.
parse_loop_body :: proc(p: ^Parser) -> [dynamic]Stmt {
    skip_newlines(p)
    if current_kind(p) == .Do {
        advance(p) // consume 'do'
        body: [dynamic]Stmt
        append(&body, parse_stmt(p))
        return body
    }
    return parse_block(p)
}

parse_for :: proc(p: ^Parser) -> Stmt {
    start := token_span(p,current(p))
    advance(p) // consume 'for'

    // Try range-for: `for i in 0..<10 { }` or `for i : i32 in 0..10 { }`
    // Or collection-for: `for elem in coll { }` or `for elem, idx in coll { }`
    // Detection: identifier followed by `in`, `, ident in`, or `: type in`
    saved := p.pos
    if current_kind(p) == .Identifier {
        range_saved := p.pos
        first_var := advance(p).text // consume first identifier

        // Check for second variable: `for elem, idx in ...`
        second_var := ""
        has_second := false
        if current_kind(p) == .Comma {
            advance(p) // consume ','
            if current_kind(p) == .Identifier {
                second_var = advance(p).text
                has_second = true
            }
        }

        // Check for optional type annotation: `i : i32 in ...`.
        // `:` followed by `=` is a C-style init (`for k := 0; ...`), not an
        // annotation — parsing a type there would record a hard error before
        // the C-style backtrack below gets its turn.
        iter_type_expr: Type_Expr = nil
        if current_kind(p) == .Colon && peek_kind(p) != .Equals {
            advance(p) // consume ':'
            iter_type_expr = parse_type_expr(p)
        }

        if current_kind(p) == .In {
            advance(p) // consume 'in'
            p.no_struct_lit = true
            expr_after_in := parse_expr(p)
            p.no_struct_lit = false

            // Check if this is a range-for (`for i in 0..10 { }`) or collection-for.
            // Range is exclusive: 0..n iterates 0,1,...,n-1 — matches slice
            // half-open semantics. For an inclusive endpoint, write `n+1`.
            if current_kind(p) == .Dot_Dot {
                if has_second {
                    tok := current(p)
                    parse_error(p, tok, PARSE_RANGE_FOR_ONE_VAR)
                }
                advance(p)

                p.no_struct_lit = true
                high := parse_expr(p)
                p.no_struct_lit = false
                body := parse_loop_body(p)

                stmt := new(Stmt_For)
                stmt.is_range = true
                stmt.loop_var = first_var
                stmt.iter_type = iter_type_expr
                stmt.range_low = expr_after_in
                stmt.range_high = high
                stmt.body = body
                stmt.span = start
                return stmt
            } else {
                // Collection-for: `for elem in coll { }` or `for elem, idx in coll { }`
                body := parse_loop_body(p)

                elem_var := first_var
                index_var := has_second ? second_var : ""
                if elem_var == "_" do elem_var = ""
                if index_var == "_" do index_var = ""

                stmt := new(Stmt_For)
                stmt.is_collection_for = true
                stmt.elem_var = elem_var
                stmt.index_var = index_var
                stmt.iter_type = iter_type_expr
                stmt.collection = expr_after_in
                stmt.body = body
                stmt.span = start
                return stmt
            }
        }

        // Not a range-for or collection-for, restore position
        p.pos = range_saved
    }

    // Try C-style: for init; cond; post { body }
    // Save position so we can backtrack if it's a simple for-condition loop.
    saved = p.pos
    init_stmt, init_ok := try_parse_assign(p)
    if init_ok && current_kind(p) == .Semicolon {
        advance(p) // consume ';'
        p.no_struct_lit = true
        condition := parse_expr(p)
        p.no_struct_lit = false
        expect(p, .Semicolon)
        post_stmt, _ := try_parse_assign(p)
        body := parse_loop_body(p)

        stmt := new(Stmt_For)
        stmt.init = init_stmt
        stmt.condition = condition
        stmt.post = post_stmt
        stmt.body = body
        stmt.span = start
        return stmt
    }

    // Not C-style: restore and parse as simple `for condition { body }`
    p.pos = saved
    p.no_struct_lit = true
    condition := parse_expr(p)
    p.no_struct_lit = false
    body := parse_loop_body(p)

    stmt := new(Stmt_For)
    stmt.condition = condition
    stmt.body = body
    stmt.span = start
    return stmt
}

// Try to parse a statement starting with an identifier:
// declarations (::, :, :=), assignments (=, +=, etc.),
// Dispatch an assignment to the right Stmt type based on the LHS expression.
// Returns the statement and true if the LHS is a field access, index, or deref.
make_lhs_assign :: proc(lhs: Expr, value: Expr, start: Span, is_compound: bool = false) -> (Stmt, bool) {
    #partial switch t in lhs {
    case ^Expr_Field_Access:
        return new_clone(Stmt_Assign{target = lhs, value = value, span = start, is_compound = is_compound}), true
    case ^Expr_Index:
        return new_clone(Stmt_Assign{target = lhs, value = value, span = start, is_compound = is_compound}), true
    case ^Expr_Unary:
        if t.op == .Caret {
            return new_clone(Stmt_Assign{target = lhs, value = value, span = start, is_compound = is_compound}), true
        }
    }
    return {}, false
}

// Parse the lvalue chain of a destructure item whose leading identifier is
// already consumed: `font.metrics`, `cells[i]`, `ptr^.field`, combinations.
// The slice form `a[lo:hi]` is not a bind target — fails out so the caller
// can restore and reject the statement.
parse_bind_target_chain :: proc(p: ^Parser, first_tok: Token) -> (Expr, bool) {
    lhs: Expr = new_clone(Expr_Ident{name = first_tok.text, span = token_span(p,first_tok)})
    for {
        #partial switch current_kind(p) {
        case .Dot:
            advance(p) // consume '.'
            field_tok := expect_field_name(p)
            lhs = new_clone(Expr_Field_Access{expr = lhs, field = field_tok.text, span = token_span(p,first_tok)})
        case .Left_Bracket:
            advance(p) // consume '['
            idx := parse_expr(p)
            if current_kind(p) != .Right_Bracket {
                return {}, false
            }
            advance(p) // consume ']'
            lhs = new_clone(Expr_Index{expr = lhs, index = idx, span = token_span(p,first_tok)})
        case .Caret:
            advance(p) // consume '^'
            lhs = new_clone(Expr_Unary{op = .Caret, operand = lhs, span = token_span(p,first_tok)})
        case:
            return lhs, true
        }
    }
}

// index/field assignments, or bare function calls.
// Returns the statement and true if successful, or nil and false
// if the identifier doesn't start a recognized statement.
try_parse_assign :: proc(p: ^Parser) -> (Stmt, bool) {
    start := token_span(p,current(p))
    saved_pos := p.pos

    name_tok := advance(p) // consume identifier

    // Multi-assignment: x, y := call()  or  x, y := a, b  or  x, y : type = a, b
    // Items may also be lvalue chains: `atlas, font.metrics := load()` declares
    // the bare names and stores into the expression targets.
    if current_kind(p) == .Comma {
        // Speculatively parse: item, item, ... followed by := or : type = or =
        names: [dynamic]string
        targets: [dynamic]Expr
        has_target := false
        append(&names, name_tok.text)
        append(&targets, Expr{})
        is_multi := true
        for current_kind(p) == .Comma {
            advance(p) // consume ','
            if current_kind(p) != .Identifier {
                is_multi = false
                break
            }
            item_tok := advance(p)
            if current_kind(p) == .Dot || current_kind(p) == .Left_Bracket || current_kind(p) == .Caret {
                chain, chain_ok := parse_bind_target_chain(p, item_tok)
                if !chain_ok {
                    is_multi = false
                    break
                }
                append(&names, "")
                append(&targets, chain)
                has_target = true
            } else {
                append(&names, item_tok.text)
                append(&targets, Expr{})
            }
        }
        if is_multi && has_target {
            // Mixed bind: bare names declare, expression targets store. Only
            // the infer-decl (`:=`) and reassign (`=`) forms exist here — a
            // typed decl can't target a field, the field already has a type.
            if current_kind(p) == .Colon {
                advance(p) // consume ':'
                if current_kind(p) == .Equals {
                    advance(p) // consume '='
                    mt_vals: [dynamic]Expr
                    append(&mt_vals, parse_expr(p))
                    return new_clone(Stmt_Multi_Return_Assign{
                        names   = names,
                        targets = targets,
                        values  = mt_vals,
                        span    = start,
                        is_decl = true,   // `:=` — bare names are declared
                    }), true
                }
                p.pos = saved_pos
                return {}, false
            }
            if current_kind(p) == .Equals {
                advance(p) // consume '='
                first := parse_expr(p)
                if current_kind(p) != .Comma {
                    // Single RHS (multi-return call or broadcast)
                    mt_vals: [dynamic]Expr
                    append(&mt_vals, first)
                    return new_clone(Stmt_Multi_Return_Assign{
                        names   = names,
                        targets = targets,
                        values  = mt_vals,
                        span    = start,
                    }), true
                }
                // Parallel RHS: one assignment per item
                vals: [dynamic]Expr
                append(&vals, first)
                for current_kind(p) == .Comma {
                    advance(p) // consume ','
                    append(&vals, parse_expr(p))
                }
                assigns: [dynamic]^Stmt_Assign
                for i := 0; i < len(names) && i < len(vals); i += 1 {
                    if names[i] != "" {
                        append(&assigns, new_clone(Stmt_Assign{name = names[i], value = vals[i], span = start}))
                    } else if assign_stmt, lhs_ok := make_lhs_assign(targets[i], vals[i], start); lhs_ok {
                        append(&assigns, assign_stmt.(^Stmt_Assign))
                    }
                }
                return new_clone(Stmt_Multi_Assign{assigns = assigns, span = start}), true
            }
            p.pos = saved_pos
            return {}, false
        }
        if is_multi && current_kind(p) == .Colon {
            advance(p) // consume ':'
            // Statement-context decl tail. Same shared parser as param/return
            // contexts; the only difference is stop_at_group_break=false here
            // (statements don't have a "next param group" — commas in RHS
            // belong to this decl).
            return parse_decl_tail(p, names, start, true, true, false), true
        }
        if is_multi && current_kind(p) == .Equals {
            // x, y = expr  or  x, y = a, b  or  x, y = all expr  (reassignment)
            advance(p) // consume '='
            if current_kind(p) == .Identifier && p.tokens[p.pos].text == "all" {
                // Broadcast reassignment: x, y = all expr
                advance(p) // consume 'all'
                val := parse_expr(p)
                assigns: [dynamic]^Stmt_Assign
                for i := 0; i < len(names); i += 1 {
                    v := i == 0 ? val : clone_expr(val)
                    append(&assigns, new_clone(Stmt_Assign{name = names[i], value = v, span = start}))
                }
                return new_clone(Stmt_Multi_Assign{assigns = assigns, span = start}), true
            }
            first := parse_expr(p)
            if current_kind(p) == .Comma {
                // Multiple RHS: wrap in Stmt_Multi_Assign
                vals: [dynamic]Expr
                append(&vals, first)
                for current_kind(p) == .Comma {
                    advance(p) // consume ','
                    append(&vals, parse_expr(p))
                }
                assigns: [dynamic]^Stmt_Assign
                for i := 0; i < len(names) && i < len(vals); i += 1 {
                    append(&assigns, new_clone(Stmt_Assign{name = names[i], value = vals[i], span = start}))
                }
                return new_clone(Stmt_Multi_Assign{assigns = assigns, span = start}), true
            }
            // Single RHS (multi-return call): x, y = call()
            reassign_vals: [dynamic]Expr
            append(&reassign_vals, first)
            return new_clone(Stmt_Multi_Return_Assign{names = names, values = reassign_vals, span = start}), true
        }
        // Not a multi-assign — restore and fall through to single-assign handling
        p.pos = saved_pos
        name_tok = advance(p)
    }

    #partial switch current_kind(p) {

    // name :: fun/union/value
    case .Double_Colon:
        advance(p) // consume '::'
        #partial switch current_kind(p) {
        case .Fun:
            return parse_scope_def(p, name_tok.text, start, .Fun), true
        case .Struct:
            return parse_scope_def(p, name_tok.text, start, .Struct), true
        case .Hash:
            // `Name :: #packed struct { ... }` — decorator on the struct type
            // itself: drop inter-field alignment padding so the layout maps
            // 1:1 onto packed binary formats (e.g. on-disk file headers read
            // via `#big_endian`).
            if peek_kind(p, 1) == .Identifier && peek_token(p, 1).text == "packed" {
                hash_tok := current(p)
                advance(p) // consume '#'
                advance(p) // consume 'packed'
                if current_kind(p) != .Struct {
                    parse_error(p, hash_tok, PARSE_PACKED_NEEDS_STRUCT_DECL)
                }
                def := parse_scope_def(p, name_tok.text, start, .Struct)
                if scope, ok := def.(^Stmt_Scope); ok { scope.is_packed = true }
                return def, true
            }
            // Other `#x` RHS forms fall through to the expression path below.
        case .Union:    return parse_union_def_with_name(p, name_tok.text, start), true
        case .Error:    return parse_error_def_with_name(p, name_tok.text, start), true
        case .Dispatch: return parse_dispatch_def_with_name(p, name_tok.text, start), true
        case .Distinct:
            advance(p) // consume 'distinct'
            base_type := parse_type_expr(p)
            // Optional sized-slice default cap: `Name :: distinct [, 0]T(N)`.
            // Lets `x : Name` decl form pick up N without writing `Name(N)`.
            default_cap := try_parse_slice_cap_suffix(p, base_type)
            return new_clone(Stmt_Distinct_Def{name = name_tok.text, base_type = base_type, default_cap_expr = default_cap, span = start}), true
        }

        // `Name :: type(<type_expr>)` — transparent type alias. `type` is a
        // special identifier rather than a reserved keyword so struct fields
        // named `type` (SDL events, etc.) keep working. Parens are optional
        // sugar; `Name :: type <type_expr>` parses too. A `(N)` sized-slice
        // cap suffix is parsed AS PART OF the type spec (inside the outer
        // parens): `type([, 0]utf8(128))`.
        if current_kind(p) == .Identifier && current(p).text == "type" {
            advance(p) // consume 'type'
            has_outer_paren := current_kind(p) == .Left_Paren
            if has_outer_paren { advance(p) }
            base_type := parse_type_expr(p)
            default_cap := try_parse_slice_cap_suffix(p, base_type)
            if has_outer_paren { expect(p, .Right_Paren) }
            return new_clone(Stmt_Distinct_Def{
                name             = name_tok.text,
                base_type        = base_type,
                default_cap_expr = default_cap,
                is_alias         = true,
                span             = start,
            }), true
        }
        // name :: expr (constant)
        value := parse_expr(p)
        return new_clone(Stmt_Define{name = name_tok.text, value = value, span = start}), true

    // name : type = expr  OR  name := expr
    case .Colon:
        advance(p) // consume ':'
        if current_kind(p) == .Equals {
            // x := expr (infer type)
            advance(p) // consume '='
            value := parse_expr(p)
            return make_single_decl(name_tok.text, nil, value, start), true
        }
        // x : type = expr  OR  x : type : expr  OR  x : type (uninitialized)
        type_expr := parse_type_expr(p)
        slice_cap := try_parse_slice_cap_suffix(p, type_expr)
        if current_kind(p) == .Equals {
            advance(p) // consume '='
            value := parse_expr(p)
            return make_single_decl(name_tok.text, type_expr, value, start, slice_cap_expr = slice_cap), true
        }
        if current_kind(p) == .Colon {
            // x : type : expr — typed comptime constant
            advance(p) // consume ':'
            value := parse_expr(p)
            return new_clone(Stmt_Define{name = name_tok.text, type_expr = type_expr, value = value, span = start}), true
        }
        // No '=' — declaration without initializer (e.g. ev : SDL_Event)
        return make_single_decl(name_tok.text, type_expr, nil, start, slice_cap_expr = slice_cap), true

    // name = expr
    case .Equals:
        advance(p) // consume '='
        value := parse_expr(p)
        return new_clone(Stmt_Assign{name = name_tok.text, value = value, span = start}), true

    // name += expr  (and other compound assignments)
    case .Plus_Equal, .Minus_Equal, .Mul_Equal, .Div_Equal, .Mod_Equal,
         .And_Equal, .Or_Equal, .Xor_Equal, .Shift_Left_Equal, .Shift_Right_Equal:
        compound_op, _ := compound_assign_op(current_kind(p))
        op_tok := advance(p)
        rhs := parse_expr(p)
        bin := new(Expr_Binary)
        bin.left = new_clone(Expr_Ident{name = name_tok.text, span = token_span(p,name_tok)})
        bin.op = compound_op
        bin.right = rhs
        bin.span = token_span(p,op_tok)
        return new_clone(Stmt_Assign{name = name_tok.text, value = bin, span = start, is_compound = true}), true

    // name[...] or name.field or name^ — could be index/field/deref assignment
    case .Left_Bracket, .Dot, .Caret:
        lhs: Expr = new_clone(Expr_Ident{name = name_tok.text, span = token_span(p,name_tok)})

        for current_kind(p) == .Left_Bracket || current_kind(p) == .Dot || current_kind(p) == .Caret {
            if current_kind(p) == .Left_Bracket {
                advance(p) // consume '['
                low := parse_expr(p)
                // Detect slice syntax: [low:high] or [low:]
                if current_kind(p) == .Colon {
                    advance(p) // consume ':'
                    high: Expr
                    if current_kind(p) != .Right_Bracket {
                        high = parse_expr(p)
                    }
                    expect(p, .Right_Bracket)
                    // Must be immediately followed by '=' to be a slice assign
                    if current_kind(p) == .Equals {
                        advance(p) // consume '='
                        value := parse_expr(p)
                        slice_target := new_clone(Expr_Slice{expr = lhs, low = low, high = high, span = start})
                        return new_clone(Stmt_Assign{target = slice_target, value = value, span = start}), true
                    }
                    // Not an assignment — can't use slice syntax as an expression statement
                    p.pos = saved_pos
                    return {}, false
                }
                expect(p, .Right_Bracket)
                idx := new(Expr_Index)
                idx.expr = lhs
                idx.index = low
                idx.span = start
                lhs = idx
            } else if current_kind(p) == .Dot {
                advance(p) // consume '.'
                field_tok := expect_field_name(p)
                fa := new(Expr_Field_Access)
                fa.expr = lhs
                fa.field = field_tok.text
                fa.span = start
                lhs = fa
            } else if current_kind(p) == .Caret {
                advance(p) // consume '^'
                unary := new(Expr_Unary)
                unary.op = .Caret
                unary.operand = lhs
                unary.span = start
                lhs = unary
            }
        }

        // If it's a call (Left_Paren after dot chain), backtrack — expression parser handles it
        if current_kind(p) == .Left_Paren {
            p.pos = saved_pos
            return {}, false
        }

        // Multi-target assignment with expression LHS: frame.x, frame.y = get_pair()
        // Mixed bind also lands here when the expression target comes first:
        // `frame.x, atlas := get_pair()` — `:=` declares the bare names.
        if current_kind(p) == .Comma {
            lhs_exprs: [dynamic]Expr
            append(&lhs_exprs, lhs)
            for current_kind(p) == .Comma {
                advance(p) // consume ','
                append(&lhs_exprs, parse_expr(p))
            }
            saw_colon := false
            if current_kind(p) == .Colon {
                advance(p) // consume ':'
                if current_kind(p) != .Equals {
                    p.pos = saved_pos
                    return {}, false
                }
                saw_colon = true
                // fall through to the '=' handling below
            }
            if current_kind(p) == .Equals {
                advance(p) // consume '='
                rhs := parse_expr(p)
                // Build names/targets arrays
                mt_names: [dynamic]string
                mt_targets: [dynamic]Expr
                for expr in lhs_exprs {
                    if ident, ident_ok := expr.(^Expr_Ident); ident_ok {
                        append(&mt_names, ident.name)
                        append(&mt_targets, Expr{})
                    } else {
                        append(&mt_names, "")
                        append(&mt_targets, expr)
                    }
                }
                mt_vals: [dynamic]Expr
                append(&mt_vals, rhs)
                return new_clone(Stmt_Multi_Return_Assign{
                    names   = mt_names,
                    targets = mt_targets,
                    values  = mt_vals,
                    span    = start,
                    is_decl = saw_colon,   // `:=` declares the bare names; `=` reassigns
                }), true
            }
            // Comma but no '=' — not a valid statement
            p.pos = saved_pos
            return {}, false
        }

        if current_kind(p) == .Equals {
            advance(p) // consume '='
            value := parse_expr(p)
            if stmt, ok := make_lhs_assign(lhs, value, start); ok {
                return stmt, true
            }
        }

        // name.field += expr  (and other compound assignments on complex LHS)
        #partial switch current_kind(p) {
        case .Plus_Equal, .Minus_Equal, .Mul_Equal, .Div_Equal, .Mod_Equal,
             .And_Equal, .Or_Equal, .Xor_Equal, .Shift_Left_Equal, .Shift_Right_Equal:
            compound_op, _ := compound_assign_op(current_kind(p))
            op_tok := advance(p)
            rhs := parse_expr(p)
            bin := new(Expr_Binary)
            bin.left = lhs
            bin.op = compound_op
            bin.right = rhs
            bin.span = token_span(p,op_tok)
            if stmt, ok := make_lhs_assign(lhs, bin, start, is_compound = true); ok {
                return stmt, true
            }
        }

        // Not an assignment — restore and let expression parser handle it
        p.pos = saved_pos
        return {}, false
    }

    // Not any kind of assignment — restore
    p.pos = saved_pos
    return {}, false
}

// ---------------------------------------------------------------------------
// Type expression parsing
// ---------------------------------------------------------------------------

is_type_keyword :: proc(kind: Token_Kind) -> bool {
    #partial switch kind {
    case .Int, .F64, .Bool_Type,
         .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .Utf8, .Byte: return true
    }
    return false
}

// Can the current token start a type expression? Used to detect optional arrow syntax.
// Excludes Left_Brace so `fun() { body }` still parses as a no-return-type function.
can_start_type_expr :: proc(p: ^Parser) -> bool {
    if is_type_keyword(current_kind(p)) { return true }
    #partial switch current_kind(p) {
    case .Identifier, .Caret, .Left_Bracket, .Left_Paren, .Dollar: return true
    case .Fun: return peek_kind(p) == .Left_Paren  // fun(...) -> R type
    }
    return false
}

// Parse a generic type argument: could be a type expr (int, ^T, [N]T) or a const value/expression.
// Number literals → Type_Const_Value, type keywords/pointers/arrays → type expr,
// bare identifiers followed by ) or , → Type_Name (type checker decides if type or const param),
// anything else (function calls, binary exprs) → Type_Const_Expr (runtime expression).
parse_generic_arg :: proc(p: ^Parser) -> Type_Expr {
    // Number literal: 256, 1024, etc. — always a const value
    if current_kind(p) == .Number {
        // Check if it's a simple number (followed by , or )) or part of an expression
        if peek_kind(p) == .Right_Paren || peek_kind(p) == .Comma {
            val_tok := advance(p)
            return Type_Const_Value{value = parse_int_token(val_tok.text), span = token_span(p,val_tok)}
        }
        // Complex expression starting with a number (e.g., 256 * 4)
        start := token_span(p,current(p))
        expr := parse_expr(p, 0)
        return Type_Const_Expr{expr = expr, span = start}
    }
    // Type keywords (int, f64, etc.), pointers (^T), arrays ([N]T), tuples ((T, U)), fun(...) → type expr
    if is_type_keyword(current_kind(p)) || current_kind(p) == .Caret ||
       current_kind(p) == .Left_Bracket || current_kind(p) == .Left_Paren ||
       current_kind(p) == .Dollar || (current_kind(p) == .Fun && peek_kind(p) == .Left_Paren) {
        return parse_type_expr(p)
    }
    // Identifier: could be a type name (String, Vec3) or a const variable (n, size)
    if current_kind(p) == .Identifier {
        // If followed by ( → could be generic type like Map(int, int) — parse as type expr
        if peek_kind(p) == .Left_Paren {
            // Ambiguous: could be generic type or function call like megabytes(50)
            // Save position and try as type expr first; if it works, use it
            // For now, parse as expression (function calls are more likely for const params)
            start := token_span(p,current(p))
            expr := parse_expr(p, 0)
            return Type_Const_Expr{expr = expr, span = start}
        }
        // Bare identifier followed by , or ) — could be type or variable
        // If followed by ) or , with no further tokens, it's a simple name
        if peek_kind(p) == .Right_Paren || peek_kind(p) == .Comma {
            // Parse as Type_Name — type checker will resolve based on param kind
            tok := advance(p)
            return Type_Name{name = tok.text, span = token_span(p,tok)}
        }
        // Identifier followed by operator etc. — parse as expression
        start := token_span(p,current(p))
        expr := parse_expr(p, 0)
        return Type_Const_Expr{expr = expr, span = start}
    }
    // Fallback: parse as type expression
    return parse_type_expr(p)
}

// Parse a type expression: int, f64, bool, string, [N]T, [N!]T, ^T, or (T, U) tuple
parse_type_expr :: proc(p: ^Parser) -> Type_Expr {
    // Generic type parameter binding: $T (used inside function param types like ^Pair($T))
    if current_kind(p) == .Dollar {
        start := token_span(p,current(p))
        advance(p) // consume '$'
        name_tok := expect(p, .Identifier)
        // Record this as a generic param binding (collected by parse_scope_def)
        append(&p.dollar_params, Generic_Param{name = name_tok.text, span = start})
        // Return as a plain Type_Name — the type checker resolves it from the substitution map
        return Type_Name{name = name_tok.text, span = start}
    }

    // Constraint reference: `~T` at type-expression position. T must resolve
    // to a constraint type (`Name :: ~struct/~class { ... }`) at type-check
    // time; the tilde is a visible marker that this slot holds an interface,
    // not a concrete type. The checker enforces the constraint requirement;
    // the parser just stamps the flag onto the Type_Name so the resolver can
    // tell `~T` apart from plain `T` for diagnostics and rule enforcement.
    if current_kind(p) == .Tilde {
        start := token_span(p,current(p))
        advance(p) // consume '~'
        name_tok := expect(p, .Identifier)
        return Type_Name{name = name_tok.text, span = start, tilde = true}
    }

    // Parenthesized type expression: `(T)` is cosmetic — same as bare `T`.
    // Mara has no tuple type, so `(T, U)` in a non-return position is a
    // syntax error. Multi-return is handled by parse_return_type_clause,
    // which strips its own outer parens before this point.
    if current_kind(p) == .Left_Paren {
        paren_tok := current(p)
        start := token_span(p,paren_tok)
        advance(p) // consume '('
        inner := parse_type_expr(p)
        if current_kind(p) == .Comma {
            parse_error(p, paren_tok, PARSE_TUPLE_TYPE_NOT_SUPPORTED)
            // Consume the rest of the bogus list so error recovery has a chance.
            for current_kind(p) == .Comma {
                advance(p)
                skip_newlines(p)
                _ = parse_type_expr(p)
            }
            expect(p, .Right_Paren)
            return Type_Name{name = "_error_", span = start}
        }
        expect(p, .Right_Paren)
        return inner
    }

    // Pointer type: ^T
    if current_kind(p) == .Caret {
        start := token_span(p,current(p))
        advance(p) // consume '^'
        elem := parse_type_expr(p) // recursive: ^int, ^^int, ^[N]int, etc.
        tp := new(Type_Pointer)
        tp.elem = elem
        tp.span = start
        return tp
    }

    // Function types — two forms after `fn`:
    //   fn name              — nominal type tied to a named function
    //   fn(T1, T2 -> R)      — structural; arrow inside the parens, return
    //                          after it. `fn(T)` is void-return; `fn(-> R)`
    //                          is no-param; `fn()` is void-void.
    if current_kind(p) == .Fn {
        start := token_span(p,current(p))
        advance(p) // consume 'fn'

        if current_kind(p) == .Left_Paren {
            advance(p) // consume '('
            params: [dynamic]Type_Expr
            return_types: [dynamic]Type_Expr
            // Params (optional). Stop at -> or ).
            if current_kind(p) != .Arrow && current_kind(p) != .Right_Paren {
                append(&params, parse_type_expr(p))
                for current_kind(p) == .Comma {
                    advance(p) // consume ','
                    append(&params, parse_type_expr(p))
                }
            }
            if current_kind(p) == .Arrow {
                advance(p) // consume '->'
                parse_return_type_clause(p, &return_types)
            }
            expect(p, .Right_Paren)
            fe := new(Type_Func_Expr)
            fe.params = params
            fe.return_types = return_types
            fe.span = start
            return fe
        }

        // Nominal: fn name (optionally qualified).
        name_tok := expect(p, .Identifier)
        name := name_tok.text
        if current_kind(p) == .Dot && peek_kind(p) == .Identifier {
            advance(p) // consume '.'
            qual := advance(p)
            name = strings.concatenate({name, ".", qual.text})
        }
        return Type_Of_Name{name = name, span = start}
    }

    // Function type: fun(T, U) -> R
    if current_kind(p) == .Fun && peek_kind(p) == .Left_Paren {
        start := token_span(p,current(p))
        advance(p) // consume 'fun'
        advance(p) // consume '('
        params: [dynamic]Type_Expr
        if current_kind(p) != .Right_Paren {
            append(&params, parse_type_expr(p))
            for current_kind(p) == .Comma {
                advance(p) // consume ','
                append(&params, parse_type_expr(p))
            }
        }
        expect(p, .Right_Paren)
        return_types: [dynamic]Type_Expr
        if current_kind(p) == .Arrow {
            advance(p) // consume '->'
            parse_return_type_clause(p, &return_types)
        }
        fe := new(Type_Func_Expr)
        fe.params = params
        fe.return_types = return_types
        fe.span = start
        return fe
    }

    // Slice type: []T or Array type: [N]T or [IndexType:N]T
    if current_kind(p) == .Left_Bracket {
        start := token_span(p,current(p))
        advance(p) // consume '['
        // Slice type: []T — empty brackets. Since partial arrays share the
        // first 24 bytes of slice layout, []T flows through to either form
        // at the IR level.
        if current_kind(p) == .Right_Bracket || current_kind(p) == .Comma {
            consume_removed_sentinel(p)
            expect(p, .Right_Bracket)
            elem := parse_type_expr(p)
            ts := new(Type_Slice_Expr)
            ts.elem = elem
            ts.span = start
            return ts
        }
        // Sized slice header: [:N]T — slice with cap = N at construction.
        // No backing storage is allocated; the header lives in writable
        // memory and its ptr/len are populated by assignment (e.g. from a
        // `take`). Replaces the older `[]T(N)` suffix syntax.
        if current_kind(p) == .Colon {
            advance(p) // consume ':'
            cap_expr := parse_expr(p, 0)
            consume_removed_sentinel(p)
            expect(p, .Right_Bracket)
            elem := parse_type_expr(p)
            ts := new(Type_Slice_Expr)
            ts.elem = elem
            ts.cap_expr = cap_expr
            ts.span = start
            return ts
        }
        // Partial array: [..N]T — value type, inline storage, cursor.
        if current_kind(p) == .Dot_Dot {
            advance(p) // consume '..'
            pa_size_val := 0
            pa_size_name: string
            pa_size_expr: Expr
            if current_kind(p) == .Number && (peek_kind(p) == .Right_Bracket || peek_kind(p) == .Comma) {
                pa_size_val = parse_int_token(advance(p).text)
            } else if current_kind(p) == .Identifier && (peek_kind(p) == .Right_Bracket || peek_kind(p) == .Comma) {
                pa_size_name = advance(p).text
            } else {
                pa_size_expr = parse_expr(p, 0)
                if num, ok := pa_size_expr.(^Expr_Number); ok {
                    pa_size_val = int(num.value)
                    pa_size_expr = nil
                } else if ident, ok := pa_size_expr.(^Expr_Ident); ok {
                    pa_size_name = ident.name
                    pa_size_expr = nil
                }
            }
            consume_removed_sentinel(p)
            expect(p, .Right_Bracket)
            elem := parse_type_expr(p)
            pa := new(Type_Partial_Array_Expr)
            pa.size = pa_size_val
            pa.size_name = pa_size_name
            pa.size_expr = pa_size_expr
            pa.elem = elem
            pa.span = start
            return pa
        }
        // Parse the array size — can be a number literal, identifier, or expression
        size_val := 0
        size_name: string
        size_expr: Expr
        // Lookahead-friendly fast paths: terminator can be `]`, `,` (removed
        // sentinel syntax — caught with a pointed error), or an Identifier
        // (typed index).
        size_terminates :: proc(p: ^Parser) -> bool {
            k := peek_kind(p)
            return k == .Right_Bracket || k == .Comma || k == .Identifier
        }
        if current_kind(p) == .Number && size_terminates(p) {
            // Simple number literal: [8]T, [8 IT]T, [8, 0]T
            size_tok := advance(p)
            size_val = parse_int_token(size_tok.text)
        } else if current_kind(p) == .Identifier && size_terminates(p) {
            // Simple identifier (constant name): [MAX_SIZE]T, [MAX IT]T
            size_name = advance(p).text
        } else {
            // Expression (VLA or complex constant): [megabytes(50)]T, [n * 2]T
            size_expr = parse_expr(p, 0)
            // Extract simple cases for backward compat
            if num, ok := size_expr.(^Expr_Number); ok {
                size_val = int(num.value)
                size_expr = nil
            } else if ident, ok := size_expr.(^Expr_Ident); ok {
                size_name = ident.name
                size_expr = nil
            }
        }
        // Optional typed index: [N IT]T — identifier follows the size with
        // whitespace, no punctuation.
        index_type: Type_Expr
        if current_kind(p) == .Identifier {
            index_type = parse_type_expr(p)
        }
        consume_removed_sentinel(p)
        expect(p, .Right_Bracket)
        elem := parse_type_expr(p)
        ta := new(Type_Array)
        ta.size = size_val
        ta.size_name = size_name
        ta.size_expr = size_expr
        ta.index_type = index_type
        ta.elem = elem
        ta.span = start
        return ta
    }

    // Named type: int, f64, bool, string
    if is_type_keyword(current_kind(p)) {
        tok := advance(p)
        return Type_Name{name = tok.text, span = token_span(p,tok)}
    }

    // User-defined type name (e.g. Point, Color) or qualified (cam.Camera) or generic (Array(int))
    if current_kind(p) == .Identifier {
        tok := advance(p)
        if current_kind(p) == .Dot && peek_kind(p) == .Identifier {
            advance(p) // consume '.'
            type_tok := advance(p)
            return Type_Name{name = strings.concatenate({tok.text, ".", type_tok.text}), span = token_span(p,tok)}
        }
        // Parameterized type: Array(int), Array(int, 256), Map(string, int), String(n)
        if current_kind(p) == .Left_Paren {
            advance(p) // consume '('
            type_args: [dynamic]Type_Expr
            if current_kind(p) != .Right_Paren {
                append(&type_args, parse_generic_arg(p))
                for current_kind(p) == .Comma {
                    advance(p) // consume ','
                    append(&type_args, parse_generic_arg(p))
                }
            }
            expect(p, .Right_Paren)
            gi := new(Type_Generic_Instance)
            gi.name = tok.text
            gi.type_args = type_args
            gi.span = token_span(p,tok)
            return gi
        }
        return Type_Name{name = tok.text, span = token_span(p,tok)}
    }

    tok := current(p)
    parse_error(p, tok, PARSE_EXPECTED_TYPE, tok.kind, tok.text)
    advance(p)
    return Type_Name{name = "int", span = token_span(p,tok)}
}

// ---------------------------------------------------------------------------
// Expression parsing — Pratt / precedence climbing
// ---------------------------------------------------------------------------

get_precedence :: proc(kind: Token_Kind) -> int {
    #partial switch kind {
    case .Or:  return 1
    case .And: return 2
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal: return 3
    case .Pipe: return 4
    case .Tilde: return 5
    case .Ampersand: return 6
    case .Shift_Left, .Shift_Right: return 7
    case .Plus, .Minus, .Wrap_Plus, .Wrap_Minus:  return 8
    case .Star, .Slash, .Modulo, .Wrap_Star:  return 9
    case: return -1
    }
}

parse_expr :: proc(p: ^Parser, min_prec: int = 0) -> Expr {
    left := parse_primary(p)

    for {
        // Range-membership: `x in a..b` and `x not in a..b`. Desugar at parse
        // time to (x >= a) and (x < b) (or its negation). Half-open match —
        // same range shape as for-loops and slice indexing. Precedence is the
        // same as the comparison operators (3) since the result is a bool.
        is_in     := current_kind(p) == .In
        is_not_in := current_kind(p) == .Not && peek_kind(p, 1) == .In
        if is_in || is_not_in {
            if 3 < min_prec { break }
            start := token_span(p,current(p))
            advance(p) // consume `in` or `not`
            if is_not_in { advance(p) /* consume `in` */ }
            lo := parse_expr(p, 4) // anything tighter than comparison, but `..` isn't a Pratt op
            if current_kind(p) != .Dot_Dot {
                parse_error(p, current(p), PARSE_RANGE_NEEDS_DOTS, "not " if is_not_in else "")
                left = lo
                continue
            }
            advance(p) // consume `..`
            hi := parse_expr(p, 4)

            // LHS is used twice; clone the second occurrence so codegen and
            // any later AST traversals don't share node identity. Side-effecting
            // LHS would evaluate twice — accept that for the simple-ident case
            // that dominates bounds checks; revisit if it bites.
            ge := new(Expr_Binary)
            ge.op = .Greater_Equal
            ge.left = left
            ge.right = lo
            ge.span = start

            lt := new(Expr_Binary)
            lt.op = .Less
            lt.left = clone_expr(left)
            lt.right = hi
            lt.span = start

            and_expr := new(Expr_Binary)
            and_expr.op = .And
            and_expr.left = ge
            and_expr.right = lt
            and_expr.span = start

            if is_not_in {
                neg := new(Expr_Unary)
                neg.op = .Not
                neg.operand = and_expr
                neg.span = start
                left = neg
            } else {
                left = and_expr
            }
            continue
        }

        prec := get_precedence(current_kind(p))
        if prec < min_prec {
            break
        }

        // `&` is both binary AND and the start of an address-of/append
        // statement, so on a multi-statement line `x := 5 &nums + 7` parses
        // as `5 & nums + 7` — almost never what was meant. Disambiguate by
        // spacing (the Swift rule): space before but glued after (`a &b`)
        // reads as a prefix `&`, so reject it here rather than letting it
        // surface as a confusing type error (or, on integer operands,
        // silently compute an AND).
        if current_kind(p) == .Ampersand && p.pos > 0 {
            amp := current(p)
            prev := p.tokens[p.pos - 1]
            next := peek_token(p, 1)
            if amp.line == prev.line && next.line == amp.line {
                spaced_before := amp.col > prev.col + len(prev.text)
                glued_after := next.col == amp.col + 1
                if spaced_before && glued_after {
                    parse_error(p, amp, PARSE_AMBIGUOUS_AMPERSAND)
                }
            }
        }

        op := advance(p) // consume the operator
        right := parse_expr(p, prec + 1) // +1 for left-associativity

        bin := new(Expr_Binary)
        // Wrapping operators carry the same op kind as their checked counterpart
        // plus a `wrapping` flag; all type-checking then reuses the `.Plus` etc.
        // paths and only codegen diverges (plain op, no overflow trap).
        #partial switch op.kind {
        case .Wrap_Plus:  bin.op = .Plus;  bin.wrapping = true
        case .Wrap_Minus: bin.op = .Minus; bin.wrapping = true
        case .Wrap_Star:  bin.op = .Star;  bin.wrapping = true
        case:             bin.op = op.kind
        }
        bin.left = left
        bin.right = right
        bin.span = token_span(p,op)
        left = bin
    }

    return left
}

// Check if the current '{' starts a struct literal rather than a block.
// Detect positional brace constructor: Type{expr, expr, ...}
// Peek past newlines: {} is an empty struct, { ident : is a struct with fields.
// Positional form (Type { v1, v2 }) is also accepted — the first token is a
// value expression rather than a `name :` pair.
is_struct_literal :: proc(p: ^Parser) -> bool {
    if current_kind(p) != .Left_Brace { return false }
    if p.no_struct_lit { return false }
    // Peek past the '{' and any newlines
    offset := 1
    for peek_kind(p, offset) == .Newline {
        offset += 1
    }
    next_kind := peek_kind(p, offset)
    // Empty struct: {}
    if next_kind == .Right_Brace { return true }
    // Zero-init: {0}
    if next_kind == .Number && peek_token(p, offset).text == "0" && peek_kind(p, offset + 1) == .Right_Brace { return true }
    // Named field: { ident = value  (but NOT { ident == which is equality).
    if next_kind == .Identifier {
        name_offset := offset + 1
        for peek_kind(p, name_offset) == .Newline {
            name_offset += 1
        }
        // `ident =` is a struct field. `ident ==` is equality — not a struct.
        if peek_kind(p, name_offset) == .Equals {
            return true
        }
    }
    // Positional: `{ expr , ... }` or `{ expr }` (single value) — accept any
    // content starting with an expression-shaped token. Control-flow contexts
    // (if/for) set p.no_struct_lit to disambiguate from their body `{}`, so a
    // single-expression block can't be misread here. Standalone `{...}` in
    // expression position is always a struct literal in Mara — there's no
    // block-as-expression syntax.
    #partial switch next_kind {
    case .Number, .String, .Char, .True, .False, .Identifier,
         .Left_Bracket, .Left_Paren, .Minus, .Ampersand, .Caret, .Bang:
        return true
    }
    return false
}

// What tokens can begin the broadcast value in `all <expr>` (parser-level
// disambiguation against bare `all` as an identifier or `all(x)` as a call).
// Conservative: identifiers, literals, unary/grouping/composite starters,
// and the type keywords that can sit at the head of a value expression.
is_broadcast_value_start :: proc(k: Token_Kind) -> bool {
    #partial switch k {
    case .Identifier, .Number, .String, .Char,
         .True, .False,
         .Minus, .Caret, .Ampersand,
         .Left_Bracket, .Left_Brace,
         .Fun, .Match, .If, .Hash,
         .Bool_Type, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64,
         .F32, .F64, .Utf8, .Byte:
        return true
    }
    return false
}

parse_struct_literal :: proc(p: ^Parser) -> Expr {
    tok := advance(p) // consume '{'
    skip_newlines(p)
    fields: [dynamic]Struct_Field
    is_zero_init := false
    is_positional := false
    is_broadcast := false
    broadcast_value: Expr
    if current_kind(p) != .Right_Brace {
        // Check for {0} — explicit zero-init syntax
        if current_kind(p) == .Number && current(p).text == "0" && peek_kind(p) == .Right_Brace {
            advance(p) // consume '0'
            is_zero_init = true
        } else if current_kind(p) == .Identifier && current(p).text == "all" && peek_kind(p) != .Equals {
            // `{all <expr>}` — broadcast one value to every slot. Element
            // count comes from the target type; the checker expands into
            // array_values once it knows.
            advance(p) // consume 'all'
            broadcast_value = parse_expr(p)
            is_broadcast = true
            skip_newlines(p)
        } else {
            // Peek first element to decide named vs positional. Named fields look
            // like `ident =` (but not `==`); anything else parses as a value.
            first_is_named := false
            if current_kind(p) == .Identifier && peek_kind(p) == .Equals {
                first_is_named = true
            }
            is_positional = !first_is_named
            parse_field := proc(p: ^Parser, positional: bool) -> Struct_Field {
                if positional {
                    value := parse_expr(p)
                    return Struct_Field{name = "", value = value}
                }
                name := expect(p, .Identifier)
                expect(p, .Equals)
                value := parse_expr(p)
                return Struct_Field{name = name.text, value = value}
            }
            append(&fields, parse_field(p, is_positional))
            // Parse remaining entries separated by comma or newline
            for current_kind(p) != .Right_Brace && current_kind(p) != .EOF {
                if current_kind(p) == .Comma {
                    advance(p) // consume ','
                }
                skip_newlines(p)
                if current_kind(p) == .Right_Brace { break }
                // Detect mixed named/positional — error out, everything in one
                // literal must use the same form.
                this_is_named := false
                if current_kind(p) == .Identifier && peek_kind(p) == .Equals {
                    this_is_named = true
                }
                if this_is_named == is_positional {
                    tok := current(p)
                    parse_error(p, tok, PARSE_STRUCT_LIT_MIXED_FIELDS)
                }
                append(&fields, parse_field(p, is_positional))
            }
        }
    }
    expect(p, .Right_Brace)
    s := new(Expr_Struct_Literal)
    s.fields = fields
    s.zero_init = is_zero_init
    s.positional = is_positional
    s.is_broadcast = is_broadcast
    s.broadcast_value = broadcast_value
    s.span = token_span(p,tok)
    return s
}

// Join a pure ident-dot chain (`Holder.Inner.Deep`) into a dotted name for a
// qualified struct literal. Fails when the chain contains anything but plain
// identifiers (calls, indexing, deref, `.Variant` shorthand) — a type path
// can't contain those.
dotted_ident_path :: proc(e: Expr) -> (string, bool) {
    #partial switch t in e {
    case ^Expr_Ident:
        if t.is_dot { return "", false }
        return t.name, true
    case ^Expr_Field_Access:
        prefix, ok := dotted_ident_path(t.expr)
        if !ok { return "", false }
        return strings.concatenate({prefix, ".", t.field}), true
    }
    return "", false
}

// Postfix operators: indexing (a[0]), field/method access (a.b, a.f()), dereference (p^).
// allow_dot controls whether . is consumed — false for & operands so that
// &events.process() parses as (&events).process() while &arr[0] stays &(arr[0]).
parse_postfix :: proc(p: ^Parser, expr: Expr, allow_dot: bool) -> Expr {
    result := expr
    for current_kind(p) == .Left_Bracket || (allow_dot && current_kind(p) == .Dot) || current_kind(p) == .Caret || current_kind(p) == .Question {
        if current_kind(p) == .Question {
            // Postfix `?` — err propagation. Wraps the LHS in an Expr_Try
            // which the type checker validates and codegen lowers to a
            // check-and-return-early sequence.
            q_span := token_span(p,current(p))
            advance(p) // consume '?'
            try_node := new(Expr_Try)
            try_node.inner = result
            try_node.span = q_span
            result = try_node
        } else if current_kind(p) == .Caret {
            // Postfix dereference: expr^
            caret_span := token_span(p,current(p))
            advance(p) // consume '^'
            unary := new(Expr_Unary)
            unary.op = .Caret
            unary.operand = result
            unary.span = caret_span
            result = unary
        } else if current_kind(p) == .Left_Bracket {
            bracket_span := token_span(p,current(p))
            advance(p) // consume '['
            saved_nsl := p.no_struct_lit
            p.no_struct_lit = false
            // Check for slice expressions: arr[low:high], arr[:high], arr[low:], arr[:]
            if current_kind(p) == .Colon {
                // arr[:high] or arr[:]
                advance(p) // consume ':'
                high: Expr
                if current_kind(p) != .Right_Bracket {
                    high = parse_expr(p)
                }
                p.no_struct_lit = saved_nsl
                expect(p, .Right_Bracket)
                sl := new(Expr_Slice)
                sl.expr = result
                sl.high = high
                sl.span = bracket_span
                result = sl
            } else {
                index := parse_expr(p)
                if current_kind(p) == .Colon {
                    // arr[low:high] or arr[low:]
                    advance(p) // consume ':'
                    high: Expr
                    if current_kind(p) != .Right_Bracket {
                        high = parse_expr(p)
                    }
                    p.no_struct_lit = saved_nsl
                    expect(p, .Right_Bracket)
                    sl := new(Expr_Slice)
                    sl.expr = result
                    sl.low = index
                    sl.high = high
                    sl.span = bracket_span
                    result = sl
                } else {
                    p.no_struct_lit = saved_nsl
                    expect(p, .Right_Bracket)
                    idx := new(Expr_Index)
                    idx.expr = result
                    idx.index = index
                    idx.span = bracket_span
                    result = idx
                }
            }
        } else {
            // Dot access: expr.field or expr.field(args) (qualified call)
            dot_span := token_span(p,current(p))
            advance(p) // consume '.'
            field_tok := expect_field_name(p)

            if current_kind(p) == .Left_Paren {
                // Qualified call: expr.func(args)
                advance(p) // consume '('
                skip_newlines(p)
                saved_nsl := p.no_struct_lit
                p.no_struct_lit = false
                args: [dynamic]Expr
                if current_kind(p) != .Right_Paren {
                    append(&args, parse_expr(p))
                    for current_kind(p) == .Comma || current_kind(p) == .Newline {
                        if current_kind(p) == .Comma { advance(p) }
                        skip_newlines(p)
                        if current_kind(p) == .Right_Paren { break }
                        append(&args, parse_expr(p))
                    }
                }
                skip_newlines(p)
                p.no_struct_lit = saved_nsl
                expect(p, .Right_Paren)
                call := new(Expr_Call)
                call.name = field_tok.text
                call.qualifier = result
                call.args = args
                call.span = dot_span
                // Optional `{...}` field override: Foo.bar() { x: 1 }
                if is_struct_literal(p) {
                    if sl, ok := parse_struct_literal(p).(^Expr_Struct_Literal); ok {
                        call.overrides = sl
                    }
                }
                result = call
            } else {
                fa := new(Expr_Field_Access)
                fa.expr = result
                fa.field = field_tok.text
                fa.span = dot_span
                result = fa
                // Dotted named literal: `Parent.Inner{...}` — same production
                // as the bare `Name{...}` primary, the name is just qualified.
                // Only when the whole chain is a pure ident path; control-flow
                // scrutinees are protected by no_struct_lit like everywhere.
                if is_struct_literal(p) {
                    if path, path_ok := dotted_ident_path(result); path_ok {
                        if sl, ok := parse_struct_literal(p).(^Expr_Struct_Literal); ok {
                            sl.name = path
                            result = sl
                        }
                    }
                }
            }
        }
    }
    return result
}

// Look past the matching `]` to see if a typed-array-literal shape follows:
// `[ ... ] <type-token> [<type-stuff>]* {`. Used to disambiguate
// `[3]f32{0.9, 0.2, 0.6}` (typed array literal) from `[1, 2, 3]` (untyped).
peek_typed_array_literal :: proc(p: ^Parser) -> bool {
    if current_kind(p) != .Left_Bracket { return false }
    // Skip past the matched `[ ... ]`. Handles nested brackets.
    depth := 0
    pos := p.pos
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        if k == .Left_Bracket {
            depth += 1
        } else if k == .Right_Bracket {
            depth -= 1
            if depth == 0 { pos += 1; break }
        }
        pos += 1
    }
    if pos >= len(p.tokens) { return false }
    // Walk past pointer prefixes (^T) and any nested array types ([M]X)
    // until we hit a token that should be followed by `{` to count as
    // a typed array literal.
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        #partial switch k {
        case .Caret:
            pos += 1
            continue
        case .Left_Bracket:
            // Nested array type; skip its matched `]`
            depth = 0
            for pos < len(p.tokens) {
                kk := p.tokens[pos].kind
                if kk == .Left_Bracket {
                    depth += 1
                } else if kk == .Right_Bracket {
                    depth -= 1
                    if depth == 0 { pos += 1; break }
                }
                pos += 1
            }
            continue
        }
        break
    }
    if pos >= len(p.tokens) { return false }
    // Must end on a type-name-like token followed by `{`.
    if !is_type_token(p.tokens[pos].kind) { return false }
    if pos + 1 >= len(p.tokens) { return false }
    return p.tokens[pos + 1].kind == .Left_Brace
}

is_type_token :: proc(k: Token_Kind) -> bool {
    #partial switch k {
    case .Identifier, .Int, .F64, .F32, .Bool_Type,
         .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64,
         .Utf8, .Byte:
        return true
    }
    return false
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

// Emit the appropriate parse-time diagnostic for a Number token whose text
// failed to parse. Shared between the positive-literal and negative-fold
// sites so the wording stays consistent.
report_number_parse_error :: proc(p: ^Parser, tok: Token, err: Number_Parse_Error) {
    switch err {
    case .None:
        // nothing to report
    case .Hex_Overflow:
        parse_error(p, tok, PARSE_HEX_OVERFLOWS_U64, tok.text)
    case .Dec_Overflow:
        parse_error(p, tok, PARSE_DECIMAL_OVERFLOWS_U64, tok.text)
    case .Bin_Overflow:
        parse_error(p, tok, PARSE_BINARY_OVERFLOWS_U64, tok.text)
    case .Invalid:
        parse_error(p, tok, PARSE_INVALID_NUMBER, tok.text)
    }
}

parse_primary :: proc(p: ^Parser, allow_dot: bool = true) -> Expr {
    result: Expr
    start := token_span(p,current(p))

    #partial switch current_kind(p) {
    case .Number:
        tok := advance(p)
        f_val, i_val, err := parse_number_text(tok.text)
        report_number_parse_error(p, tok, err)
        result = new_clone(Expr_Number{value = f_val, int_value = i_val, is_float = strings.index_byte(tok.text, '.') >= 0, span = token_span(p,tok)})

    case .Identifier:
        tok := advance(p)
        // Special case: size_of(Type) — argument is a type expression, not a value
        if tok.text == "size_of" && current_kind(p) == .Left_Paren {
            advance(p) // consume '('
            type_arg := parse_type_expr(p)
            expect(p, .Right_Paren)
            so := new(Expr_Size_Of)
            so.type_expr = type_arg
            so.span = token_span(p,tok)
            result = so
        } else if tok.text == "assert" && current_kind(p) == .Left_Paren {
            // `assert(cond)` — capture the condition's source text now (later
            // phases have no source) by concatenating the tokens it spans.
            // Token positions reconstruct the original spacing: any gap (or a
            // line break) becomes one space, adjacent tokens stay fused — so
            // `x < y` prints spaced while `a.b[i]` stays tight.
            advance(p) // consume '('
            cond_start := p.pos
            cond := parse_expr(p)
            cond_end := p.pos
            expect(p, .Right_Paren)
            a := new(Expr_Assert)
            a.cond = cond
            a.cond_text = assert_token_text(p, cond_start, cond_end)
            // For a comparison, also capture each operand's text by splitting
            // at the top operator token: the LAST depth-0 token of the op's
            // kind (left-associativity puts the tree root rightmost; anything
            // further right would itself be the root).
            if bin, is_bin := cond.(^Expr_Binary); is_bin && is_comparison_op(bin.op) {
                op_idx := -1
                depth := 0
                for i in cond_start..<cond_end {
                    k := p.tokens[i].kind
                    if k == .Left_Paren || k == .Left_Bracket || k == .Left_Brace {
                        depth += 1
                    } else if k == .Right_Paren || k == .Right_Bracket || k == .Right_Brace {
                        depth -= 1
                    } else if depth == 0 && k == bin.op {
                        op_idx = i
                    }
                }
                if op_idx > cond_start && op_idx < cond_end - 1 {
                    a.lhs_text = assert_token_text(p, cond_start, op_idx)
                    a.rhs_text = assert_token_text(p, op_idx + 1, cond_end)
                }
            }
            a.span = token_span(p,tok)
            result = a
        } else if (tok.text == "let" || tok.text == "slice") && current_kind(p) == .Left_Paren {
            // `let(T, storage)` — carve a value of type T from `storage`.
            // `slice([:N]T, storage)` — carve N elements as a slice header.
            // `slice(storage)` — 1-arg form: element type and cap come from the
            //                    assignment LHS (the field/var being assigned to).
            //                    Only valid in assignment context.
            //
            // The 2-arg form's storage shapes:
            //   cursor form: `^[]byte` slice variable (advances .len cursor).
            //   exact form:  `&buf[off]` (typed pointer at offset; no cursor).
            //
            // Shared AST (Expr_Take); the type checker validates that:
            //   - `let` has a non-slice type and no count_expr.
            //   - `slice` 2-arg has a slice type and count_expr (from [:N]T).
            //   - `slice` 1-arg has nil type_expr; LHS-driven inference in checker.
            //
            // Replaces the older `take` keyword, which conflated both.
            kind := tok.text
            advance(p) // consume '('
            // Disambiguate by the first token after `(`:
            //   `[` starts a type expression (the 2-arg form's [:N]T).
            //   anything else starts a value expression (the 1-arg form's source).
            // `let` always requires the type-arg form — it has no LHS-cap
            // story, so a bare value source would have nowhere to derive T.
            is_one_arg := kind == "slice" && current_kind(p) != .Left_Bracket
            tk := new(Expr_Take)
            tk.keyword = kind
            tk.span = token_span(p,tok)
            if is_one_arg {
                tk.type_expr = nil
                tk.count_expr = nil
                tk.storage = parse_expr(p)
            } else {
                type_arg := parse_type_expr(p)
                count_arg: Expr
                if ts, is_slice := type_arg.(^Type_Slice_Expr); is_slice && ts.cap_expr != nil {
                    count_arg = ts.cap_expr
                    ts.cap_expr = nil
                }
                expect(p, .Comma)
                skip_newlines(p)
                tk.type_expr = type_arg
                tk.count_expr = count_arg
                tk.storage = parse_expr(p)
            }
            expect(p, .Right_Paren)
            result = tk
        } else if tok.text == "all" && is_broadcast_value_start(current_kind(p)) {
            // Bare `all <expr>` desugars to the `{all <expr>}` broadcast struct
            // literal. Only triggered when the following token plausibly starts
            // an expression — `all(x)` stays a function call.
            val := parse_expr(p)
            lit := new(Expr_Struct_Literal)
            lit.is_broadcast = true
            lit.broadcast_value = val
            lit.span = token_span(p,tok)
            result = lit
        } else if current_kind(p) == .Left_Paren {
        // Check if this is a function call: name(args)
            advance(p) // consume '('
            skip_newlines(p)
            saved_nsl := p.no_struct_lit
            p.no_struct_lit = false
            args: [dynamic]Expr
            if current_kind(p) != .Right_Paren {
                append(&args, parse_expr(p))
                for current_kind(p) == .Comma || current_kind(p) == .Newline {
                    if current_kind(p) == .Comma { advance(p) }
                    skip_newlines(p)
                    if current_kind(p) == .Right_Paren { break }
                    append(&args, parse_expr(p))
                }
            }
            skip_newlines(p)
            p.no_struct_lit = saved_nsl
            expect(p, .Right_Paren)
            call := new(Expr_Call)
            call.name = tok.text
            call.args = args
            call.span = token_span(p,tok)
            // Optional `{...}` field override: Foo() { x: 1 }
            if is_struct_literal(p) {
                if sl, ok := parse_struct_literal(p).(^Expr_Struct_Literal); ok {
                    call.overrides = sl
                }
            }
            result = call
        } else if is_struct_literal(p) {
            // Named struct literal: Circle { radius: 3.14 }
            lit := parse_struct_literal(p)
            if sl, ok := lit.(^Expr_Struct_Literal); ok {
                sl.name = tok.text
            }
            result = lit
        } else {
            result = new_clone(Expr_Ident{name = tok.text, span = token_span(p,tok)})
        }

    case .Dot:
        // .Variant shorthand in expression position: resolves against the
        // expected type at this site (function arg, assignment target, etc.).
        // If no expected type is in play, the type checker falls back to a
        // variant_to_enum search across visible unions/enums.
        dot_tok := advance(p) // consume '.'
        if current_kind(p) != .Identifier {
            parse_error(p, current(p), PARSE_EXPECTED_VARIANT_NAME)
            result = new_clone(Expr_Number{value = 0, span = token_span(p,dot_tok)})
        } else {
            name_tok := advance(p)
            result = new_clone(Expr_Ident{name = name_tok.text, span = token_span(p,dot_tok), is_dot = true})
        }

    case .True:
        tok := advance(p)
        result = new_clone(Expr_Bool{value = true, span = token_span(p,tok)})

    case .False:
        tok := advance(p)
        result = new_clone(Expr_Bool{value = false, span = token_span(p,tok)})

    case .String:
        tok := advance(p)
        result = new_clone(Expr_String{value = tok.text, span = token_span(p,tok)})

    case .Char:
        tok := advance(p)
        char_val: u8 = len(tok.text) > 0 ? tok.text[0] : 0
        result = new_clone(Expr_Char{value = char_val, span = token_span(p,tok)})

    case .Left_Paren:
        advance(p) // consume '('
        saved_nsl := p.no_struct_lit
        p.no_struct_lit = false
        inner := parse_expr(p)
        p.no_struct_lit = saved_nsl
        expect(p, .Right_Paren) // consume ')'
        result = inner

    case .Left_Bracket:
        // Could be one of:
        //   [a, b, c]          — untyped array literal (Expr_Array)
        //   [N]T{a, b, c}      — typed array literal: parse [N]T as a type
        //                        expression, then the {...} as a struct literal
        //                        carrying the inline type_expr.
        // Disambiguate by looking past the matching ']' for an immediate
        // type-token-then-`{` pattern.
        if peek_typed_array_literal(p) {
            start := token_span(p,current(p))
            type_expr := parse_type_expr(p)
            sl_lit := parse_struct_literal(p)
            if sl, ok := sl_lit.(^Expr_Struct_Literal); ok {
                sl.type_expr = type_expr
                sl.span = start
            }
            result = sl_lit
        } else {
            tok := advance(p) // consume '['
            skip_newlines(p)
            saved_nsl := p.no_struct_lit
            p.no_struct_lit = false
            elements: [dynamic]Expr
            if current_kind(p) != .Right_Bracket {
                append(&elements, parse_expr(p))
                for current_kind(p) == .Comma || current_kind(p) == .Newline {
                    if current_kind(p) == .Comma { advance(p) }
                    skip_newlines(p)
                    if current_kind(p) == .Right_Bracket { break }
                    append(&elements, parse_expr(p))
                }
            }
            p.no_struct_lit = saved_nsl
            expect(p, .Right_Bracket)
            arr := new(Expr_Array)
            arr.elements = elements
            arr.span = token_span(p,tok)
            result = arr
        }

    case .Left_Brace:
        // Struct literal: { key: expr, ... } or empty {}
        // Disambiguate from blocks by peeking: { ident : means struct
        if is_struct_literal(p) {
            result = parse_struct_literal(p)
        } else {
            tok := current(p)
            parse_error(p, tok, PARSE_UNEXPECTED_LBRACE_IN_EXPR)
            advance(p)
            result = new_clone(Expr_Number{value = 0, span = start})
        }

    case .Minus:
        tok := advance(p)
        // Fold negative number literals: -3.14 becomes Expr_Number{-3.14}
        if current_kind(p) == .Number {
            num_tok := advance(p)
            f_val, i_val, err := parse_number_text(num_tok.text)
            report_number_parse_error(p, num_tok, err)
            result = new_clone(Expr_Number{value = -f_val, int_value = -i_val, is_float = strings.index_byte(num_tok.text, '.') >= 0, span = token_span(p,tok)})
        } else {
            operand := parse_primary(p)
            unary := new(Expr_Unary)
            unary.op = .Minus
            unary.operand = operand
            unary.span = token_span(p,tok)
            result = unary
        }

    case .Wrap_Minus:
        // Prefix `-%x`: wrapping negate. Not literal-folded — the wrap semantics
        // (no trap on MIN, two's-complement on unsigned) are the whole point, so
        // it stays an Expr_Unary the checker/codegen handle explicitly.
        tok := advance(p)
        operand := parse_primary(p)
        unary := new(Expr_Unary)
        unary.op = .Minus
        unary.operand = operand
        unary.span = token_span(p,tok)
        unary.wrapping = true
        result = unary

    case .Not:
        tok := advance(p)
        operand := parse_primary(p)
        unary := new(Expr_Unary)
        unary.op = .Not
        unary.operand = operand
        unary.span = token_span(p,tok)
        result = unary

    case .Tilde:
        tok := advance(p)
        operand := parse_primary(p)
        unary := new(Expr_Unary)
        unary.op = .Tilde
        unary.operand = operand
        unary.span = token_span(p,tok)
        result = unary

    case .Ampersand:
        tok := advance(p) // consume '&'
        // Parse operand with full postfix (including dot) so that
        // &state.vao parses as &(state.vao) — address of a struct field.
        // If the result is a call like &events.process(), restructure so
        // & applies to the receiver: process(&events) — not &(events.process()).
        operand := parse_primary(p, allow_dot = true)
        if call, call_ok := operand.(^Expr_Call); call_ok && call.qualifier != nil {
            // &obj.method(args) -> method(&obj, args)
            addr_of := new(Expr_Unary)
            addr_of.op = .Ampersand
            addr_of.operand = call.qualifier
            addr_of.span = token_span(p,tok)
            call.qualifier = addr_of
            result = call
        } else {
            unary := new(Expr_Unary)
            unary.op = .Ampersand
            unary.operand = operand
            unary.span = token_span(p,tok)
            result = unary
        }

    case .If:
        result = parse_if_expr(p)

    case .Int, .F64, .Bool_Type,
         .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .Utf8, .Byte:
        // Type keyword in expression context. With `(` it's a cast call —
        // i32(x), f64(y) — same form for any user-facing primitive. Without
        // `(` it's a type-as-value, useful as a generic-call argument like
        // `Array(byte, 64)` (parallel to user-defined type names like
        // `Array(Player, 64)`, which flow as Expr_Ident).
        tok := advance(p)
        if current_kind(p) == .Left_Paren {
            advance(p) // consume '('
            skip_newlines(p)
            args: [dynamic]Expr
            if current_kind(p) != .Right_Paren {
                append(&args, parse_expr(p))
                for current_kind(p) == .Comma || current_kind(p) == .Newline {
                    if current_kind(p) == .Comma { advance(p) }
                    skip_newlines(p)
                    if current_kind(p) == .Right_Paren { break }
                    append(&args, parse_expr(p))
                }
            }
            skip_newlines(p)
            expect(p, .Right_Paren)
            call := new(Expr_Call)
            call.name = tok.text
            call.args = args
            call.span = token_span(p,tok)
            result = call
        } else {
            tn := new(Expr_Type_Name)
            tn.kind = tok.kind
            tn.span = token_span(p,tok)
            result = tn
        }

    case .Hash:
        hash_tok := advance(p) // consume '#'
        if current_kind(p) != .Identifier {
            parse_error(p, hash_tok, PARSE_EXPECTED_HASH_NAME)
            result = new_clone(Expr_Number{value = 0, span = token_span(p,hash_tok)})
        } else {
            name_tok := advance(p)
            // #skip_constructor is value-position only: marks a field as
            // "don't run the constructor body" (the field still gets header
            // setup for slices/partial arrays). Parsed as Expr_Skip_Constructor,
            // which the rest of the pipeline already understands.
            if name_tok.text == "skip_constructor" {
                // `#skip_constructor` folded into `void` — one absence
                // concept for null pointers, uninitialized storage, and
                // absent generic args. The node survives internally as the
                // checker's desugar target for `= void`.
                parse_error(p, hash_tok, PARSE_SKIP_CONSTRUCTOR_REMOVED)
                result = new_clone(Expr_Skip_Constructor{span = token_span(p,hash_tok)})
            } else if name_tok.text == "self" {
                result = new_clone(Expr_Self{span = token_span(p,hash_tok)})
            } else if name_tok.text == "big_endian" {
                // `#big_endian buf[off]` / `#big_endian buf[lo:hi]` — decorator
                // on a byte-buffer reinterpret read. Parsed as a prefix on a
                // primary expression; we expect the next thing to parse as an
                // Expr_Index or Expr_Slice (the byte-buffer read forms). The
                // flag flows through to codegen, which emits bswap on every
                // multi-byte integer leaf of the destination after the load.
                inner := parse_primary(p, allow_dot)
                #partial switch v in inner {
                case ^Expr_Index:
                    v.is_big_endian = true
                case ^Expr_Slice:
                    v.is_big_endian = true
                case:
                    parse_error(p, hash_tok, PARSE_BIG_ENDIAN_NEEDS_BYTE_READ)
                }
                result = inner
            } else {
                intrinsic_kind: Intrinsic_Kind
                intrinsic_ok := true
                switch name_tok.text {
                case "caller_name":
                    intrinsic_kind = .Caller_Name
                case "caller_span":
                    intrinsic_kind = .Caller_Span
                case "web":
                    intrinsic_kind = .Web
                case "native":
                    intrinsic_kind = .Native
                case "windows":
                    intrinsic_kind = .Windows
                case "linux":
                    intrinsic_kind = .Linux
                case "mac":
                    intrinsic_kind = .Mac
                case:
                    parse_error(p, hash_tok, PARSE_UNKNOWN_INTRINSIC, name_tok.text)
                    result = new_clone(Expr_Number{value = 0, span = token_span(p,hash_tok)})
                    intrinsic_ok = false
                }
                if intrinsic_ok {
                    result = new_clone(Expr_Compiler_Intrinsic{
                        kind = intrinsic_kind,
                        span = token_span(p,hash_tok),
                    })
                }
            }
        }

    case .Use, .Include, .Sealed:
        // `use path`     — private import; names visible in this file only.
        // `include path` — re-export; names visible here AND in the module's
        //                  public surface (consumers see them via mod.X).
        // `sealed use path` — qualified-only access via `name.X`, no flatten.
        //                  Used to keep colliding bindings isolated (SDL2 vs SDL3).
        is_sealed := false
        if current_kind(p) == .Sealed {
            advance(p) // consume 'sealed'
            is_sealed = true
        }
        kw_kind := current_kind(p)
        if kw_kind != .Use && kw_kind != .Include {
            tok := current(p)
            parse_error(p, tok, PARSE_SEALED_NEEDS_USE_INCLUDE, tok.text)
            advance(p)
            result = new_clone(Expr_Number{value = 0, span = start})
            return result
        }
        tok := advance(p)  // consume `use` or `include`
        is_reexport := kw_kind == .Include
        // Parse the dotted path: `use mara.time`, `use gfx.vao`, plain `use camera`.
        // Submodule collection means there's nothing special about the `mara.`
        // prefix anymore — any dotted form is valid, including deeper paths.
        name_tok := expect(p, .Identifier)
        path := name_tok.text
        for current_kind(p) == .Dot {
            advance(p) // consume '.'
            seg_tok := expect(p, .Identifier)
            path = strings.concatenate({path, ".", seg_tok.text})
        }
        result = new_clone(Expr_Include{path = path, is_sealed = is_sealed, is_reexport = is_reexport, span = token_span(p,tok)})

    case:
        tok := current(p)
        parse_error(p, tok, PARSE_UNEXPECTED_TOKEN, tok.kind, tok.text)
        advance(p)
        result = new_clone(Expr_Number{value = 0, span = start})
    }

    // Postfix: index expressions (a[0]), field access (a.b), dereference (p^)
    result = parse_postfix(p, result, allow_dot)

    return result
}

// ---------------------------------------------------------------------------
// AST deep clone — used by generic function monomorphization so each
// instantiation gets its own AST nodes with independent type annotations.
// ---------------------------------------------------------------------------

clone_exprs :: proc(exprs: [dynamic]Expr) -> [dynamic]Expr {
    result: [dynamic]Expr
    for e in exprs { append(&result, clone_expr(e)) }
    return result
}

clone_stmts :: proc(stmts: [dynamic]Stmt) -> [dynamic]Stmt {
    result: [dynamic]Stmt
    for s in stmts { append(&result, clone_stmt(s)) }
    return result
}

clone_expr :: proc(e: Expr) -> Expr {
    switch v in e {
    case ^Expr_Number:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_String:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Char:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Ident:
        c := new_clone(v^)
        c.type_ = nil
        c.resolved = nil
        return c
    case ^Expr_Bool:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Skip_Constructor:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Unary:
        c := new_clone(v^)
        c.operand = clone_expr(v.operand)
        c.type_ = nil
        return c
    case ^Expr_Assert:
        c := new_clone(v^)
        c.cond = clone_expr(v.cond)
        c.type_ = nil
        return c
    case ^Expr_Binary:
        c := new_clone(v^)
        c.left = clone_expr(v.left)
        c.right = clone_expr(v.right)
        c.type_ = nil
        c.overload_fn = nil
        return c
    case ^Expr_Call:
        c := new_clone(v^)
        c.qualifier = clone_expr(v.qualifier)
        c.args = clone_exprs(v.args)
        c.type_ = nil
        c.resolved_func = nil
        return c
    case ^Expr_Array:
        c := new_clone(v^)
        c.elements = clone_exprs(v.elements)
        c.type_ = nil
        return c
    case ^Expr_Index:
        c := new_clone(v^)
        c.expr = clone_expr(v.expr)
        c.index = clone_expr(v.index)
        c.type_ = nil
        return c
    case ^Expr_Slice:
        c := new_clone(v^)
        c.expr = clone_expr(v.expr)
        c.low = clone_expr(v.low)
        c.high = clone_expr(v.high)
        c.type_ = nil
        return c
    case ^Expr_Struct_Literal:
        c := new_clone(v^)
        c.fields = {}
        for f in v.fields {
            append(&c.fields, Struct_Field{name = f.name, value = clone_expr(f.value)})
        }
        c.type_ = nil
        return c
    case ^Expr_Field_Access:
        c := new_clone(v^)
        c.expr = clone_expr(v.expr)
        c.type_ = nil
        c.resolved = nil
        return c
    case ^Expr_Size_Of:
        c := new_clone(v^)
        c.type_ = nil
        c.resolved_type = nil
        return c
    case ^Expr_Take:
        c := new_clone(v^)
        c.storage = clone_expr(v.storage)
        if v.count_expr != nil { c.count_expr = clone_expr(v.count_expr) }
        c.type_ = nil
        c.resolved_type = nil
        return c
    case ^Expr_If:
        c := new_clone(v^)
        c.condition = clone_expr(v.condition)
        c.then_expr = clone_expr(v.then_expr)
        c.else_expr = clone_expr(v.else_expr)
        c.type_ = nil
        return c
    case ^Expr_Compiler_Intrinsic:
        c := new_clone(v^)
        c.type_ = nil
        c.resolved_value = ""
        return c
    case ^Expr_Include:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Type_Name:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Tuple_Default:
        // Preserve `source` by reference — the whole point of this node is
        // that multiple bindings in a group share the SAME source so codegen
        // can dedup. Cloning the source here would defeat that.
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Self:
        c := new_clone(v^)
        c.type_ = nil
        return c
    case ^Expr_Try:
        c := new_clone(v^)
        c.inner = clone_expr(v.inner)
        c.type_ = nil
        return c
    }
    return nil
}

clone_stmt :: proc(s: Stmt) -> Stmt {
    switch v in s {
    case ^Stmt_Assign:
        c := new_clone(v^)
        c.value = clone_expr(v.value)
        c.target = clone_expr(v.target)
        c.checked = {}
        c.var_type = nil
        c.env_type = nil
        c.target_type = nil
        c.assign_value_type = nil
        return c
    case ^Stmt_Multi_Assign:
        c := new_clone(v^)
        c.assigns = {}
        for a in v.assigns {
            ca := new_clone(a^)
            ca.value = clone_expr(a.value)
            ca.var_type = nil
            ca.env_type = nil
            append(&c.assigns, ca)
        }
        return c
    case ^Stmt_Multi_Return_Assign:
        c := new_clone(v^)
        c.targets = clone_exprs(v.targets)
        c.values = clone_exprs(v.values)
        c.var_types = {}
        return c
    case Stmt_Call:
        return Stmt_Call{expr = clone_expr(v.expr), span = v.span}
    case ^Stmt_If:
        c := new_clone(v^)
        c.condition = clone_expr(v.condition)
        c.body = clone_stmts(v.body)
        c.else_body = clone_stmts(v.else_body)
        return c
    case ^Stmt_For:
        c := new_clone(v^)
        c.init = clone_stmt(v.init)
        c.condition = clone_expr(v.condition)
        c.post = clone_stmt(v.post)
        c.body = clone_stmts(v.body)
        c.range_low = clone_expr(v.range_low)
        c.range_high = clone_expr(v.range_high)
        c.var_type = nil
        return c
    case ^Stmt_Scope:
        c := new_clone(v^)
        // defs and body are disjoint arrays of distinct nodes; clone each so the
        // clone owns its own nodes (new_clone only shallow-copied the slices).
        c.body = clone_stmts(v.body)
        c.defs = clone_stmts(v.defs)
        return c
    case Stmt_Return:
        return Stmt_Return{values = clone_exprs(v.values), span = v.span}
    case Stmt_Break:
        return s
    case Stmt_Continue:
        return s
    case ^Stmt_Defer:
        c := new_clone(v^)
        c.body = clone_stmts(v.body)
        return c
    case ^Stmt_Match:
        c := new_clone(v^)
        c.subject = clone_expr(v.subject)
        c.arms = {}
        for arm in v.arms {
            ca := Match_Arm{
                value         = clone_expr(arm.value),
                variant_name  = arm.variant_name,
                binding_name  = arm.binding_name,
                is_union_arm  = arm.is_union_arm,
                dot_shorthand = arm.dot_shorthand,
                is_else       = arm.is_else,
                body          = clone_stmts(arm.body),
            }
            append(&c.arms, ca)
        }
        return c
    case ^Stmt_Foreign:
        return s  // not expected inside function bodies
    case ^Stmt_Union_Def:
        return s  // not expected inside function bodies
    case ^Stmt_Distinct_Def:
        return s  // not expected inside function bodies
    case ^Stmt_Dispatch_Def:
        return s  // not expected inside function bodies
    case Stmt_Overload:
        return s
    case Stmt_Module:
        return s
    case ^Stmt_Decl:
        c := new_clone(v^)
        c.names = {}
        for n in v.names { append(&c.names, n) }
        c.init_values = clone_exprs(v.init_values)
        c.checked = {}
        return c
    case ^Stmt_Define:
        c := new_clone(v^)
        c.value = clone_expr(v.value)
        c.var_type = nil
        c.env_type = nil
        return c
    }
    return nil
}
