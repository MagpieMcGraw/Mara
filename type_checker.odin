package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

Type :: union {
    Type_F64,
    Type_Infer_Int,   // numeric literal (integer) — adopts concrete type from context
    Type_Infer_Float, // numeric literal (float) — adopts concrete float type from context
    Type_Bool,
    Type_CString,
    Type_C8,          // 8-bit character (ASCII byte)
    Type_Utf8,        // UTF-8 byte (used as element type for strings)
    Type_Byte,        // raw memory byte — no arithmetic, used in []byte for reinterpret
    Type_Numeric,
    ^Type_Ptr,
    ^Type_Scope,        // unified scope type: data struct/class (kind=.Struct) or callable fun (kind=.Fun)
    ^Type_Fixed_Array,
    ^Type_Slice,      // [:]T — slice (view into array: {ptr, len, cap})
    ^Type_Partial_Array, // [..N]T — partial array (value with inline storage + cursor)
    ^Type_Enum,
    ^Type_Union,
    ^Type_Distinct,   // named wrapper around another type (same layout, different identity)
    Type_Const_Int,      // compile-time integer value — used as const generic param (e.g., n=256)
    Type_Runtime_Size,   // runtime-sized const generic param (e.g., String(n) where n is a variable)
    Type_Any,            // for opaque pointer elements only (ptr → ^Type_Ptr{elem=Type_Any{}})
    Type_Void,           // zero-sized "nothing here" — used as the default for `~T`
                         //   shape-constrained generic params. Satisfies any `~T`
                         //   trivially; reading or method-calling a void value is
                         //   a type error.
    Type_Error,       // error recovery — suppresses cascading type errors
    Type_Err,         // open error type — accepts any variant from any `error { ... }` decl
}

Type_F64 :: struct {}
Type_Infer_Int :: struct { cell: ^Infer_Cell }    // nil cell = anonymous literal/const; non-nil = a deferred `:=` binding
Type_Infer_Float :: struct { cell: ^Infer_Cell }
Type_Bool :: struct {}
Type_CString :: struct {}
Type_C8 :: struct {}
Type_Utf8 :: struct {}
Type_Byte :: struct {}
Type_Const_Int :: struct {
    value: int,  // compile-time integer value used as const generic parameter
}
Type_Runtime_Size :: struct {
    expr: Expr,  // runtime expression for size (evaluated at codegen time)
}
Type_Any :: struct {}
Type_Void :: struct {}
Type_Error :: struct {}
Type_Err :: struct {}

Numeric_Kind :: enum { Signed, Unsigned, Float }
Type_Numeric :: struct {
    kind: Numeric_Kind,
    bits: int,           // 8, 16, 32
}

Type_Ptr :: struct {
    elem: Type,    // the pointed-to type
}

Type_Fixed_Array :: struct {
    size:         int,
    elem:         Type,
    has_sentinel: bool,       // true for [N, 0]T sentinel-terminated arrays
    sentinel:     int,        // sentinel value (e.g. 0 for null-terminated)
    index_type:   Type,       // index type for [N IT]T (nil = plain integer index)
}

Type_Slice :: struct {
    elem:         Type,
    has_sentinel: bool,   // true for [:, 0]T sentinel-terminated slices
    sentinel:     int,    // sentinel value (e.g. 0 for null-terminated)
}

// [..N]T — partial array. IR layout: {ptr, len, cap, elements: [N x T]}, with
// ptr initialised to &elements at decl time. First 24 bytes match Type_Slice's
// {ptr, len, cap} shape so partial arrays can flow through `^[]T` (umbrella)
// without monomorphization. Pinned in practice: moving the value breaks ptr.
Type_Partial_Array :: struct {
    size:         int,
    elem:         Type,
    has_sentinel: bool,
    sentinel:     int,
}

Struct_Type_Field :: struct {
    name:          string,
    type_:         Type,
    default_value: Expr, // nil if no default
    is_using:      bool,
}

// The body of a Type_Scope — embedded via `using sd: Scope_Body`.
// Holds the fields, nested defs, methods, and other content shared
// between data-layout scopes (struct/class) and callable scopes (fun).
Scope_Body :: struct {
    name:           string,  // C-ified flat name (e.g. "game_Point", "sdl_Init"), "" for anonymous

    // Owning module's flat package name (e.g. "iso_000", "mara_math"). Empty
    // for anonymous scopes that don't belong to a single module. Set at every
    // construction site that has access to the surrounding package context;
    // downstream phases (codegen module split, incremental rebuild) use this
    // to partition symbols by their compilation unit.
    home_package:   string,

    // Data fields — the members of a struct/class, or extracted locals on a fun scope
    fields:         [dynamic]Struct_Type_Field,
    field_map:      map[string]int,  // field name -> index into fields (for O(1) lookup)

    // `#packed`: drop inter-field alignment padding so the layout maps 1:1 onto
    // packed binary formats. Set from the AST decorator in register_scope_defs;
    // consumed by every layout computation (size/offset/alignment) and by the
    // LLVM struct-type emission (`<{ ... }>`).
    is_packed:      bool,

    backing_bytes:  int,     // size of hidden trailing buffer for sized-slice fields' backing
                             // storage. Computed by codegen at register-struct time so the
                             // backing rides along with the struct on sret/memcpy — slice
                             // headers point at &struct.backing[offset] using the struct's
                             // own address (correct under RVO; stale after a downstream copy).

    // Associated definitions (scoped :: defs).
    // Values point to the actual Type the bare name resolves to — read
    // `.name` off the pointer when codegen needs the flat/mangled string.
    // (Was `map[string]string` carrying the flat name redundantly with
    // Type_Scope.name etc. — consolidated as part of the Mara2-style
    // env-pointer cleanup.)
    functions:      map[string]^Type_Scope, // bare name -> callable fun/struct
    types:    map[string]Type,         // bare name -> nested type (struct/enum/union/distinct)
    // Class-internal `name :: value` constants. Tracked separately from
    // functions because constants are AST-level values, not Types.
    consts:         map[string]^Stmt_Define,

    // Module scope (non-nil for module-structs created by `include`)
    scope:          ^Type_Env,         // module namespace scope — nil for normal structs

    // Module dispatch groups (stored on module-struct for propagation on `using include`)
    dispatch_groups:    map[string][dynamic]string,
    operator_overloads: map[Token_Kind][dynamic]string,

    // Generic monomorphization metadata
    generic_base:   string,        // "Array" if monomorphized from a template, "" otherwise
    generic_args:   [dynamic]Type, // e.g. [i64] for an Array(i64) instance — for reverse inference
}

// Unified scope type — holds struct/class definitions and callable funs.
// The `kind` tag (set by the parser from the source keyword) tells codegen
// whether to emit a data layout or a function body:
//   .Struct → data/struct layout (pure struct, class with or without ctor)
//   .Fun    → callable function body
// Structural combinations:
//   .Struct, no params:   struct / class without constructor args
//   .Struct, with params: class with constructor args (`class Foo(a: int)`)
//   .Fun,    with params: regular function (`fun add(x,y: int) -> int`)
//   .Fun,    no params:   nullary function (`fun hello() { ... }`)
Type_Scope :: struct {
    using sd: Scope_Body,
    kind:           Scope_Kind, // .Struct = data layout, .Fun = callable body
    has_parens:     bool,       // true if declared with parens — affects callable detection

    // Callable params (function parameters / constructor params)
    params:         [dynamic]Struct_Type_Field,

    // Return types for callable scopes (kind=.Fun). Empty for data scopes and
    // for void-returning funs. Single-return funs have one element; multi-return
    // funs have N. Mara has no tuple type — multi-return is a list, not a tuple.
    return_types:   [dynamic]Type,

    // ABI calling convention. Defaults to .Mara (zero value). Foreign declarations
    // set this to .C so the codegen lowers the signature per the platform C ABI.
    // See abi.odin for the classifier; phases 3+ consume this at signature /
    // call-site emission time.
    calling_conv:   Calling_Conv,
}

// True if a callable scope returns more than one value.
fn_has_multi_return :: proc(ft: ^Type_Scope) -> bool {
    return len(ft.return_types) > 1
}

// Primary return type — the only return for single-return funs, the first for
// multi-return funs, nil for void. Multi-return callers should iterate the list
// directly rather than relying on this.
fn_primary_return :: proc(ft: ^Type_Scope) -> Type {
    if len(ft.return_types) == 0 { return nil }
    return ft.return_types[0]
}

// A parameterized constructor's effective return list as callers see it: the
// struct itself (the implicit, in-place sret slot 0) followed by its declared
// returns (the trailing err). The constructor BODY only ever returns the
// declared slots — Self is built in place, never named in a `return` — so this
// prepend lives at the call boundary, not in the stored return_types. Returns
// (nil, false) for anything that isn't a fallible constructor.
constructor_effective_returns :: proc(ft: ^Type_Scope) -> ([]Type, bool) {
    if ft == nil || ft.kind != .Struct || len(ft.params) == 0 || len(ft.return_types) == 0 {
        return nil, false
    }
    list := make([]Type, 1 + len(ft.return_types))
    list[0] = ft
    for rt, i in ft.return_types { list[i + 1] = rt }
    return list, true
}

// If `e` is a call to a callable scope, return that callee's return-types list.
// Returns nil for non-calls, calls whose callee can't be resolved, or non-fun
// callees (struct constructors). The caller decides whether nil + non-call vs
// nil + bad-call is an error.
//
// Must be invoked AFTER check_expr on the call, so resolved_func is populated
// (UFCS / package-qualified call names like `string.find` get rewritten to a
// flat name like `mara_string_find` during type checking).
call_return_list :: proc(c: ^Checker, e: Expr, env: ^Type_Env) -> []Type {
    call, ok := e.(^Expr_Call)
    if !ok { return nil }
    // Prefer the resolved flat name (set by check_expr) over the AST name.
    lookup_name := call.name
    if rf, rf_ok := call.resolved_func.?; rf_ok && rf.name != "" {
        lookup_name = rf.name
    }
    if lookup_name == "" { return nil }
    // Global function table is keyed by flat name — covers module-qualified
    // calls (e.g. `string.find` → `mara_string_find`) that the local env
    // doesn't expose under their flat name.
    if ft, ok2 := c.table.funs[lookup_name]; ok2 {
        if list, is_ctor := constructor_effective_returns(ft); is_ctor {
            return list
        }
        if ft.kind == .Fun {
            return ft.return_types[:]
        }
    }
    // Env fallbacks for locally-visible names (UFCS, generics, etc.).
    t, t_ok := type_env_get(env, lookup_name)
    if !t_ok && c.current_package != "" {
        t, t_ok = type_env_get(env, make_flat_name(c.current_package, lookup_name))
    }
    if !t_ok && c.top_env != nil {
        t, t_ok = type_env_get(c.top_env, lookup_name)
    }
    if !t_ok { return nil }
    ft, ft_ok := t.(^Type_Scope)
    if !ft_ok { return nil }
    if list, is_ctor := constructor_effective_returns(ft); is_ctor {
        return list
    }
    if ft.kind != .Fun { return nil }
    return ft.return_types[:]
}

// Get the C-ified flat/mangled name of a named Type. Returns "" for
// nameless type variants (primitives, slices, etc.). Used by callers that
// need a string key (codegen lookups, error messages) when they have a
// Type pointer instead of a Type_Scope.
type_flat_name :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    return v.name
    case ^Type_Enum:     return v.name
    case ^Type_Union:    return v.name
    case ^Type_Distinct: return v.name
    }
    return ""
}

// Get the Scope_Body from a Type that represents a data-layout scope.
// Returns nil if the type is not a data-layout scope. Used by codegen where
// struct/fun distinction matters.
as_struct_body :: proc(t: Type) -> ^Scope_Body {
    if ft, ok := t.(^Type_Scope); ok && ft.kind == .Struct { return &ft.sd }
    return nil
}

// Get the Scope_Body from any scope-like Type (^Type_Scope, regardless of kind).
// Returns nil if the type is not ^Type_Scope.
// Unlike as_struct_body, does NOT require .Struct kind — used by the type checker
// which relies on structural checks (len(fields) > 0, scope != nil) to discriminate.
as_scope_body :: proc(t: Type) -> ^Scope_Body {
    if ft, ok := t.(^Type_Scope); ok { return &ft.sd }
    return nil
}

// Check if a Type is a data-layout scope.
is_struct_type :: proc(t: Type) -> bool {
    return as_struct_body(t) != nil
}

// Check if a fun's return type is its own name (self-returning data fun pattern).
is_self_return :: proc(s: ^Stmt_Scope) -> bool {
    if len(s.return_types) != 1 { return false }
    if tn, ok := s.return_types[0].(Type_Name); ok && tn.name == s.name { return true }
    return false
}

// Extract field declarations from a fun body (Stmt_Assign nodes become fields).
extract_fields_from_body :: proc(body: [dynamic]Stmt) -> [dynamic]Scope_Binding {
    fields: [dynamic]Scope_Binding
    for stmt in body {
        #partial switch s in stmt {
        case ^Stmt_Assign:
            // Only a genuine declaration introduces a field:
            //   name := value        (inferred type)
            //   name : type = value  (explicit type)
            // A reassignment (is_decl == false) mutates an existing binding and
            // is NOT a new field — whether simple (`x = 10`) or to a complex
            // target (`h.tables = ...`, `arr[i] = v`). Complex targets also
            // carry name == "", so extracting them minted a bogus empty-named
            // field whose default couldn't be inferred → Type_Any → codegen panic.
            if s.is_decl {
                append(&fields, Scope_Binding{
                    name          = s.name,
                    type_expr     = s.type_expr,
                    default_value = s.value,
                    is_using      = s.is_using,
                })
            }
        case ^Stmt_Multi_Assign:
            // x, y, z : type → multiple fields
            for a in s.assigns {
                append(&fields, Scope_Binding{
                    name          = a.name,
                    type_expr     = a.type_expr,
                    default_value = a.value,
                    is_using      = a.is_using,
                })
            }
        case ^Stmt_Decl:
            // x : T, x := v, x, y : T, x, y := a, b → one field per name
            // x, y, z := call() — single-init multi-name is tuple-destructure:
            // each binding gets an Expr_Tuple_Default so infer_field_type_from_default
            // unwraps the i-th slot of the call's tuple return type. Same wrapper
            // shape that stmt_decl_to_bindings produces for params/named returns.
            is_tuple_destructure := len(s.init_values) == 1 && len(s.names) > 1
            for name, i in s.names {
                val: Expr = nil
                if is_tuple_destructure {
                    val = new_clone(Expr_Tuple_Default{
                        source = s.init_values[0],
                        index  = i,
                        span   = s.span,
                    })
                } else if i < len(s.init_values) {
                    val = s.init_values[i]
                }
                append(&fields, Scope_Binding{
                    name          = name,
                    type_expr     = s.type_expr,
                    default_value = val,
                    is_using      = s.is_using,
                })
            }
        }
        // Nested :: defs (Stmt_Scope, etc.) are handled separately by register_scope_defs
    }
    return fields
}

Type_Enum :: struct {
    name:          string,  // C-ified flat name
    source_name:   string,  // user-written name (used for namespaced printing of error_kinds)
    home_package:  string,  // owning module flat name (see Scope_Body.home_package)
    tag_type:      string,                    // "" = default (i64), or "i32", "i16", etc.
    variants:      map[string]int,
    is_error_kind: bool,    // true for `Name :: error { ... }` — flat tag set in the global `err` type
    error_set_id:  int,     // 1-based set ID assigned at type-check end; 0 = not an error_kind
}

Type_Union :: struct {
    name:            string,             // C-ified flat name
    home_package:    string,             // owning module flat name (see Scope_Body.home_package)
    tag_type:        string,             // "" = default (i64), or "i32", "i16", etc.
    min_size:        int,                // 0 = no minimum, otherwise minimum total size in bytes (from union(128))
    tag_pad:         Type,               // type of padding between tag and payload (nil = none); reachable as `value.pad`
    variants:        [dynamic]string,    // variant names in declaration order
    tag_map:         map[string]int,     // variant name -> tag value
    variant_structs: map[string]string,  // variant name -> struct name
}

// Byte size of a union's tag_pad field. Returns 0 when no pad was declared.
union_tag_pad_bytes :: proc(ut: ^Type_Union) -> int {
    if ut.tag_pad == nil { return 0 }
    return checker_type_byte_size(ut.tag_pad)
}

Type_Distinct :: struct {
    name:             string,  // C-ified flat name
    home_package:     string,  // owning module flat name (see Scope_Body.home_package)
    base_type:        Type,    // the underlying type (transparent at codegen level)
    default_cap_expr: Expr,    // for sized-slice aliases: default cap when decl omits `(N)`
    is_alias:         bool,    // true for `Name :: type(T)` — transparent in types_equal; false for `distinct T` — nominal
}

// OS target — drives #windows / #linux / #mac comptime predicates. Defaults
// to the host OS (read from ODIN_OS in main); cross-compilation flags would
// override it when added.
Target_OS :: enum {
    Windows,
    Linux,
    Mac,
}

// ---------------------------------------------------------------------------
// Generic templates — stored during registration, instantiated on use
// ---------------------------------------------------------------------------

Generic_Template :: struct {
    name:           string,
    generic_params: [dynamic]Generic_Param,
    ast:            ^Stmt_Scope,
    home_package:   string,
}

// Parallel template for `Name :: union($T: type) { ... }`. Kept separate from
// Generic_Template so the existing struct/fun monomorphization path stays
// untouched; instantiate_generic_union handles unions independently.
Generic_Union_Template :: struct {
    name:           string,
    generic_params: [dynamic]Generic_Param,
    ast:            ^Stmt_Union_Def,
    home_package:   string,
}

// ---------------------------------------------------------------------------
// Resolved names — the result of name resolution
// ---------------------------------------------------------------------------

Resolved_Name :: union {
    Resolved_Enum_Variant,
    Resolved_Union_Variant,
    Resolved_Union_Tag,
    Resolved_Union_Pad,
    Resolved_Constant,
    Resolved_Func,
}

Resolved_Enum_Variant :: struct {
    enum_name: string,    // "Color"
    variant:   string,    // "Red"
    value:     int,       // 0
}

Resolved_Union_Variant :: struct {
    union_name:  string,  // "Shape"
    variant:     string,  // "Circle"
    tag_value:   int,     // 0
    struct_name: string,  // "Shape_Circle"
}

// `union_value.tag` accessor — reads the discriminant of a union value as
// its corresponding `<Union>_Tag` enum value.
Resolved_Union_Tag :: struct {
    union_name: string,  // flat name, e.g. "mara_sdl_Event"
}

// `union_value.pad` accessor — reads the typed padding bytes between the tag
// and the payload, as the type declared by `union(... pad T ...)`. Useful for
// inspecting reserved bytes the host writes (e.g. SDL3's reserved u32).
Resolved_Union_Pad :: struct {
    union_name: string,
}

Resolved_Constant :: struct {
    name:      string,
    int_value: int,
}

Resolved_Func :: struct {
    name:         string,  // flat name: "add" or "math_add"
}

// ---------------------------------------------------------------------------
// Type environment (scope chain)
// ---------------------------------------------------------------------------

// Where a pointer/slice's backing data lives, tracked as a stack-depth
// integer. Lower depth = lives in an outer scope = outlives more inner
// scopes. The return-from-function check is:
//
//     reject iff value.depth >= env.scope_depth
//
// i.e. data that lives in our frame (or any inner scope of it) can't
// outlive us. Param refs are conventionally one shallower than our frame
// (caller-owned). Globals / literals / external returns are depth 0,
// outliving everything in the program.
//
// Encoded as a struct to leave headroom: a future sibling-region story
// (multiple arenas at the same depth) can drop a region id alongside
// `depth` without changing the rest of the analysis.
Provenance :: struct {
    depth: int,
}

PROV_GLOBAL  :: Provenance{depth = 0}                                    // outlives everything

prov_local :: proc(env: ^Type_Env) -> Provenance { return Provenance{depth = env.scope_depth} }
prov_param :: proc(env: ^Type_Env) -> Provenance { return Provenance{depth = env.scope_depth - 1} }

Type_Env :: struct {
    types:        map[string]Type,
    parent:       ^Type_Env,
    return_types: [dynamic]Type, // expected return types for current function (empty = void)
    param_names: map[string]bool, // function parameter names (for escape analysis)
    let_names:   map[string]bool, // take-bound view names (storage aliased at source bytes); kept for legacy field name
    provenance:  map[string]Provenance, // where pointer/slice data lives
    scope_depth: int,        // stack depth for escape analysis; module = 0, function body = 1+
    // Locals whose struct value has slice fields pointing into our frame's
    // sibling/pool buffers (set when bound from a call with escape locals).
    // Returning such a local would dangle once the frame pops.
    local_slice_backed: map[string]bool,
    invalid_refs: map[string]bool, // ptr/slice vars without a usable value at this point
                                  // (declared without initializer, OR pointer-typed and
                                  // currently assigned the `void` null literal — both
                                  // are "not safe to read" by the same definition).
                                  // Read = error. Deref counts as read via the Expr_Ident
                                  // path that fires is_invalid_ref.
    newly_inited: map[string]bool, // ancestor uninit vars initialized in THIS scope (for definite assignment)
    aliases:      map[string]string, // simple intra-procedural points-to: `it = &root` records
                                     // aliases[it] = "root". Empty-string value means the alias
                                     // was explicitly cleared in this scope (shadows parent).
                                     // Lets field-access uninit checks see through pointer aliases.
    fn_name: string,             // enclosing function name (for #caller_name)
    class_scope: ^Type_Scope,    // when non-nil, this env is the body of that class/struct — field names
                                 // in this env should not leak to nested method bodies as bare identifiers.
    is_module_scope: bool,       // true on the env of a module/package — name lookup terminates here.
                                 // File envs (which hold a file's private include names) sit BELOW the
                                 // module env and walk through it; consumers cross module boundaries
                                 // only via explicit includes.
    includes:    [dynamic]^Type_Env, // pointers to envs of bare-`include`d modules. Lookup at each
                                 // env walks own names, then each include's own names (non-transitive,
                                 // matches Mara2). Bare includes set this; `name :: include path` and
                                 // `name := include path` only install the named handle and skip this list.
    // When this env is the `mod_env` of a module (set by check_module), this
    // points back at the module's Type_Scope so consumers walking env.includes
    // can reach the module's dispatch_groups / operator_overloads tables for
    // include-scoped lookup. nil for non-module envs.
    owner_module: ^Type_Scope,
}

type_env_get :: proc(env: ^Type_Env, name: string) -> (Type, bool) {
    cur := env
    for cur != nil {
        if t, ok := cur.types[name]; ok {
            return t, true
        }
        for inc in cur.includes {
            if t, ok := inc.types[name]; ok {
                return t, true
            }
        }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    return nil, false
}

// Same as type_env_get but also returns the env in which the name was found,
// so callers can inspect that env (e.g. to detect class-scope field leaks).
type_env_locate :: proc(env: ^Type_Env, name: string) -> (Type, ^Type_Env, bool) {
    cur := env
    for cur != nil {
        if t, ok := cur.types[name]; ok {
            return t, cur, true
        }
        for inc in cur.includes {
            if t, ok := inc.types[name]; ok {
                return t, inc, true
            }
        }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    return nil, nil, false
}

// Like type_env_locate but stops BEFORE entering the enclosing module scope —
// matches the shadowing-check policy (function bodies are allowed to shadow
// module-level names). Used for `:=` declarations so e.g. a local `shader :=
// gl.CreateShader(...)` doesn't conflate with the module's own auto-injected
// name binding (when the file's module is `gfx.shader`).
type_env_locate_below_module :: proc(env: ^Type_Env, name: string) -> (Type, ^Type_Env, bool) {
    cur := env
    for cur != nil {
        if cur.is_module_scope { break }
        if t, ok := cur.types[name]; ok {
            return t, cur, true
        }
        for inc in cur.includes {
            if t, ok := inc.types[name]; ok {
                return t, inc, true
            }
        }
        cur = cur.parent
    }
    return nil, nil, false
}

// Like type_env_get but with own-types-first semantics across the whole chain:
// every enclosing scope's own definitions are checked BEFORE any scope's
// includes. Used by type-name resolution so a local `Timer :: struct {...}`
// in mod_env beats an enum-variant Timer that flowed in via a per-file
// `sdl :: include mara.sdl2`. The default lookup uses the current order
// (own-then-includes per level) because flipping it globally regresses
// class-body field resolution and other paths that rely on cur.includes
// being checked before walking to cur.parent.types.
type_env_get_owned_first :: proc(env: ^Type_Env, name: string) -> (Type, bool) {
    // Phase 1: own definitions up the chain.
    cur := env
    for cur != nil {
        if t, ok := cur.types[name]; ok {
            return t, true
        }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    // Phase 2: included names up the chain.
    cur = env
    for cur != nil {
        for inc in cur.includes {
            if t, ok := inc.types[name]; ok {
                return t, true
            }
        }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    return nil, false
}

// Resolve a bare name across env-chain own definitions and includes, with
// ambiguity detection. Returns:
//   - typ, ok=true:                name resolves unambiguously
//   - ok=false, ambiguous_owners:  name has multiple include matches at the
//                                  same lookup level (caller should error)
//   - ok=false, nil ambiguous:     name not found anywhere
//
// Own definitions in any enclosing scope still win over imports — those are
// never ambiguous because the user explicitly wrote the local definition.
// Ambiguity only fires when the name comes from imports and 2+ imports
// expose it (e.g. `include mara.sdl3 + include mara.sdl2`, both with
// `PollEvent`).
//
// Variant aliases (enum entries written into env.types so `Init_Flags.Timer`
// can be referenced bare as `Timer` in expression position) are filtered out
// when a real type with the same name is also visible — the user almost
// always means the type. If only variant aliases remain, fall back to one
// of them so the original variant-shorthand semantics still work.
resolve_with_ambiguity :: proc(c: ^Checker, env: ^Type_Env, name: string) -> (typ: Type, ok: bool, ambiguous_owners: [dynamic]string) {
    Match :: struct {
        typ:   Type,
        owner: string,
    }
    matches: [dynamic]Match
    cur := env
    // Walk the parent chain with lexical shadowing: collect matches at the
    // current level (own .types + sibling includes), and if any are found,
    // stop. Otherwise climb to the parent. Without the stop, an inner
    // `Self` binding (set per-class by register_scope_defs / check_scope_body)
    // appears alongside the enclosing class's `Self`, the same-name pair gets
    // flagged as ambiguous, and both lookups fail — breaking `^Self` in any
    // nested type.
    for cur != nil {
        level_start := len(matches)
        if t, found := cur.types[name]; found {
            owner: string
            if cur.owner_module != nil {
                owner = cur.owner_module.name
            } else {
                owner = "<local>"
            }
            append(&matches, Match{typ = t, owner = owner})
        }
        for inc in cur.includes {
            if t, found := inc.types[name]; found {
                owner := inc.owner_module.name if inc.owner_module != nil else "<anonymous-include>"
                append(&matches, Match{typ = t, owner = owner})
            }
        }
        if len(matches) > level_start { break }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    if len(matches) == 0 { return nil, false, nil }
    if len(matches) == 1 { return matches[0].typ, true, nil }
    // Pointer dedup so re-exports of the same declaration don't trigger.
    distinct_typs: map[rawptr]bool
    distinct_owners: map[string]bool
    owner_list: [dynamic]string
    for m in matches {
        key := raw_type_key(m.typ)
        if key in distinct_typs { continue }
        distinct_typs[key] = true
        if m.owner not_in distinct_owners {
            distinct_owners[m.owner] = true
            append(&owner_list, m.owner)
        }
    }
    if len(distinct_typs) == 1 { return matches[0].typ, true, nil }
    return nil, false, owner_list
}

raw_type_key :: proc(t: Type) -> rawptr {
    #partial switch v in t {
    case ^Type_Scope:    return rawptr(v)
    case ^Type_Enum:     return rawptr(v)
    case ^Type_Union:    return rawptr(v)
    case ^Type_Distinct: return rawptr(v)
    case ^Type_Ptr:      return rawptr(v)
    case ^Type_Slice:    return rawptr(v)
    case ^Type_Fixed_Array: return rawptr(v)
    }
    return nil
}

type_env_set :: proc(env: ^Type_Env, name: string, t: Type) {
    env.types[name] = t
}

// Check if a variable is an uninitialized pointer/slice (walks scope chain).
// Respects newly_inited: if a child scope initialized it, it's not uninit in that scope.
is_invalid_ref :: proc(env: ^Type_Env, name: string) -> bool {
    cur := env
    for cur != nil {
        if name in cur.newly_inited { return false } // shadowed by init in this scope
        if name in cur.invalid_refs { return true }
        cur = cur.parent
    }
    return false
}

// True if the expression is exactly the `void` literal — Mara's null
// pointer constant. Treated semantically as "no usable value": assigning
// it to a pointer is equivalent to leaving the pointer uninitialized.
is_void_literal :: proc(e: Expr) -> bool {
    if id, ok := e.(^Expr_Ident); ok && id.name == "void" { return true }
    return false
}

// Mark a variable as initialized. If declared in this scope, removes directly.
// If declared in an ancestor scope, records in newly_inited (doesn't mutate parent).
mark_initialized :: proc(env: ^Type_Env, name: string) {
    // Local scope: delete directly
    if name in env.invalid_refs {
        delete_key(&env.invalid_refs, name)
        return
    }
    // Ancestor scope: record locally, don't mutate parent
    cur := env.parent
    for cur != nil {
        if name in cur.invalid_refs {
            env.newly_inited[name] = true
            return
        }
        // Also check if an intermediate scope already has it in newly_inited
        if name in cur.newly_inited {
            env.newly_inited[name] = true
            return
        }
        cur = cur.parent
    }
}

// Track uninitialized pointer/slice fields inside a struct variable.
// `provided` is the set of field names explicitly initialized (from a struct literal).
add_struct_invalid_fields :: proc(env: ^Type_Env, var_name: string, st: ^Scope_Body, provided: map[string]bool = nil) {
    for &f in st.fields {
        if provided != nil && f.name in provided { continue }
        if f.default_value != nil { continue }
        // Sized-slice fields (`field : String` where `String :: type([,0]utf8(128))`)
        // are auto-initialized by codegen — backing storage and header set up at
        // the parent struct's alloca. Don't mark them as uninit-on-read.
        if dt, ok := f.type_.(^Type_Distinct); ok {
            if _, sl_ok := dt.base_type.(^Type_Slice); sl_ok && dt.default_cap_expr != nil {
                continue
            }
        }
        base := distinct_base(f.type_)
        is_ref := false
        if _, is_ptr := base.(^Type_Ptr); is_ptr { is_ref = true }
        if _, is_slice := base.(^Type_Slice); is_slice { is_ref = true }
        if is_ref {
            key := strings.concatenate({var_name, ".", f.name})
            env.invalid_refs[key] = true
        }
    }
}

// Clear all field-level uninit entries for a variable (e.g. when the whole struct is reassigned).
// Local entries are deleted directly; ancestor entries are recorded in newly_inited.
clear_struct_invalid_fields :: proc(env: ^Type_Env, var_name: string) {
    prefix := strings.concatenate({var_name, "."})
    // Clear from current scope directly
    keys_to_delete: [dynamic]string
    for key in env.invalid_refs {
        if strings.has_prefix(key, prefix) {
            append(&keys_to_delete, key)
        }
    }
    for key in keys_to_delete {
        delete_key(&env.invalid_refs, key)
    }
    // For ancestor scopes, record in newly_inited
    cur := env.parent
    for cur != nil {
        for key in cur.invalid_refs {
            if strings.has_prefix(key, prefix) {
                env.newly_inited[key] = true
            }
        }
        cur = cur.parent
    }
}

// Look up the target a local variable currently aliases via `&ident` assignment.
// Walks the scope chain; an empty-string entry means the alias was explicitly
// cleared in that scope (the variable was reassigned to something else).
lookup_alias :: proc(env: ^Type_Env, name: string) -> (target: string, ok: bool) {
    cur := env
    for cur != nil {
        if t, found := cur.aliases[name]; found {
            if t == "" { return "", false }
            return t, true
        }
        cur = cur.parent
    }
    return "", false
}

// Record `name` as aliasing `target` (from `name = &target`). Writes to current
// scope's map; lookups walk up and find this entry before any parent.
record_alias :: proc(env: ^Type_Env, name, target: string) {
    env.aliases[name] = target
}

// Mark `name`'s alias as cleared in the current scope. Lookups stop at this
// shadow entry instead of reaching an outer-scope alias.
clear_alias :: proc(env: ^Type_Env, name: string) {
    env.aliases[name] = ""
}

// If `e` is `&<ident>` for a plain identifier, return that name. Used to detect
// simple pointer aliasing for the uninit-field check.
address_of_ident :: proc(e: Expr) -> (name: string, ok: bool) {
    if u, u_ok := e.(^Expr_Unary); u_ok && u.op == .Ampersand {
        if id, id_ok := u.operand.(^Expr_Ident); id_ok {
            return id.name, true
        }
    }
    return "", false
}

// Refresh the alias entry for `name` after an assignment. If the RHS is `&ident`,
// record the alias; otherwise clear any prior alias (the variable now points
// somewhere the analysis can't follow).
update_alias_from_value :: proc(env: ^Type_Env, name: string, value: Expr) {
    if target, ok := address_of_ident(value); ok {
        record_alias(env, name, target)
    } else {
        clear_alias(env, name)
    }
}

// Check if a variable has any uninitialized pointer/slice fields.
// Returns the first uninit field name, or nil. Respects newly_inited shadowing.
first_invalid_field :: proc(env: ^Type_Env, var_name: string) -> Maybe(string) {
    prefix := strings.concatenate({var_name, "."})
    // Collect all newly_inited keys from this scope up
    inited: map[string]bool
    cur := env
    for cur != nil {
        for key in cur.newly_inited {
            if strings.has_prefix(key, prefix) { inited[key] = true }
        }
        cur = cur.parent
    }
    // Find first uninit that isn't shadowed
    cur = env
    for cur != nil {
        for key in cur.invalid_refs {
            if strings.has_prefix(key, prefix) && key not_in inited {
                return key[len(prefix):]
            }
        }
        cur = cur.parent
    }
    return nil
}

type_env_child :: proc(parent: ^Type_Env) -> Type_Env {
    // Inner blocks (if/for/match) inherit their parent's frame depth. Only
    // function-body envs bump scope_depth — see the explicit bump in
    // check_scope_body's `.Fun` path.
    return Type_Env{parent = parent, return_types = parent.return_types, fn_name = parent.fn_name, scope_depth = parent.scope_depth}
}

// Walk up the env chain to find the enclosing function name (for #caller_name).
enclosing_fn_name :: proc(env: ^Type_Env) -> string {
    cur := env
    for cur != nil {
        if cur.fn_name != "" { return cur.fn_name }
        cur = cur.parent
    }
    return "main" // top-level code runs in main
}

// Check if a statement body always diverges (return/break/continue as last statement).
// Conservative: only detects these as the final statement.
branch_diverges :: proc(body: [dynamic]Stmt) -> bool {
    if len(body) == 0 { return false }
    last := body[len(body) - 1]
    #partial switch _ in last {
    case Stmt_Return:   return true
    case Stmt_Break:    return true
    case Stmt_Continue: return true
    }
    return false
}

// Check if a statement body guarantees a return on all code paths.
// Used to detect missing returns in non-void functions.
always_returns :: proc(body: [dynamic]Stmt) -> bool {
    // Walk backward, treating comptime-`#if` whose live arm is empty (i.e.,
    // the dead branch in this build) as a no-op so an earlier `#if` with a
    // return still satisfies the analysis. Reads bool_value, which Pass 2 has
    // already populated by the time this runs.
    for i := len(body) - 1; i >= 0; i -= 1 {
        last := body[i]
        if sif, ok := last.(^Stmt_If); ok && sif.is_comptime {
            cond_true := false
            #partial switch v in sif.condition {
            case ^Expr_Bool:               cond_true = v.value
            case ^Expr_Compiler_Intrinsic: cond_true = v.bool_value
            }
            live := sif.body if cond_true else sif.else_body
            if len(live) == 0 { continue }
            return always_returns(live)
        }
        #partial switch s in last {
        case Stmt_Return:
            return true
        case ^Stmt_If:
            // Both branches must exist and both must always return
            if len(s.else_body) == 0 { return false }
            return always_returns(s.body) && always_returns(s.else_body)
        case ^Stmt_Match:
            // Subject-less / namespace form has no exhaustiveness guarantee
            // (each arm is an independent bool predicate, no arm is forced
            // to fire), so the match can't be proven to always return.
            if s.subject == nil { return false }
            // Strict-default match on enum/union: every match either covers
            // all variants (enforced by the type checker) or has an else arm.
            // So if every arm always returns, the match as a whole does too.
            for arm in s.arms {
                if !always_returns(arm.body) { return false }
            }
            return len(s.arms) > 0
        }
        return false
    }
    return false
}

// After checking branches (if/else, match arms), promote initializations to the parent scope.
// A name is promoted only if ALL branches either initialize it or diverge (return/break/continue).
promote_branch_inits :: proc(env: ^Type_Env, branch_inits: []map[string]bool, diverges: []bool) {
    if len(branch_inits) == 0 { return }
    // Collect union of all names any branch initialized
    all_names: map[string]bool
    for inits in branch_inits {
        for name in inits { all_names[name] = true }
    }
    // Promote only names that ALL branches cover (init or diverge)
    for name in all_names {
        promoted := true
        for inits, i in branch_inits {
            if diverges[i] { continue } // diverging branch covers everything
            if name not_in inits {
                promoted = false
                break
            }
        }
        if promoted {
            mark_initialized(env, name)
        }
    }
}

// Build "prefix_name" without fmt.tprintf (avoids temp allocator overhead).
// Returns name unchanged if prefix is empty.
make_flat_name :: proc(prefix, name: string) -> string {
    if prefix == "" { return name }
    // Module names may be dotted (e.g. "mara.math"); LLVM symbol names use
    // underscore as the separator, so convert dots in the prefix.
    flat_prefix, _ := strings.replace_all(prefix, ".", "_")
    return strings.concatenate({flat_prefix, "_", name})
}

// Resolve a user-written type name to its canonical flat map key.
// If qualifier is non-empty, looks up the import alias to find the package.
// Returns "" when qualifier is not an import alias (caller handles union inner types etc.).
resolve_type_name :: proc(c: ^Checker, bare_name: string, qualifier: string = "", env: ^Type_Env = nil) -> string {
    if qualifier != "" {
        // Try module-qualified resolution: look up qualifier in env
        if env != nil {
            qual_type, found := type_env_get(env, qualifier)
            if found {
                if mod_sd := as_scope_body(qual_type); mod_sd != nil && mod_sd.scope != nil {
                    return make_flat_name(mod_sd.name, bare_name)
                }
            }
        }
        return ""
    }
    // Walk the env chain (own types + includes) to find which module owns
    // this bare name. This matches the actual visibility for the call site,
    // which is important when two modules export the same name (e.g. `Event`
    // in both mara_sdl and mara_sdl2).
    if env != nil {
        cur := env
        for cur != nil {
            if cur.owner_module != nil {
                if _, found := cur.types[bare_name]; found {
                    return make_flat_name(cur.owner_module.name, bare_name)
                }
            }
            for inc in cur.includes {
                if inc.owner_module == nil { continue }
                if _, found := inc.types[bare_name]; found {
                    return make_flat_name(inc.owner_module.name, bare_name)
                }
            }
            if cur.is_module_scope { break }
            cur = cur.parent
        }
    }
    // Local fallback for purely-local names (callers without env, or names
    // declared in the current package itself).
    return make_flat_name(c.current_package, bare_name)
}

// Resolve a type to its underlying Scope_Body, handling pointers (auto-deref).
// Returns nil if the type is not a struct.
resolve_to_struct_type :: proc(c: ^Checker, t: Type) -> ^Scope_Body {
    inner := t
    if pt, pt_ok := t.(^Type_Ptr); pt_ok {
        inner = pt.elem
    }
    if sd := as_scope_body(inner); sd != nil && len(sd.fields) > 0 { return sd }
    // Check by type name in the struct table
    tn := type_name(t)
    if st, ok := c.table.structs[tn]; ok { return &st.sd }
    if st, ok := c.table.funs[tn]; ok { return &st.sd }
    return nil
}

// Resolve a dotted name like "game.test_print" or "Widget.greet" to a flat function name.
// Checks: variable.assoc_fn, then StructName.assoc_fn.
resolve_fn_type_name :: proc(c: ^Checker, dotted: string, env: ^Type_Env) -> string {
    dot := strings.index_byte(dotted, '.')
    if dot < 0 { return "" }
    left := dotted[:dot]
    right := dotted[dot+1:]
    // Try as variable name: game.test_print where game is a local var
    if env != nil {
        if var_type, var_ok := type_env_get(env, left); var_ok {
            if var_sd := as_scope_body(var_type); var_sd != nil {
                if fn, fn_ok := var_sd.functions[right]; fn_ok && fn != nil {
                    return fn.name
                }
            }
        }
    }
    // Try as struct name: Widget.greet
    flat := resolve_type_name(c, left, "", env)
    parent_sd: ^Scope_Body
    if pss, pss_ok := c.table.structs[flat]; pss_ok {
        parent_sd = &pss.sd
    } else if psf, psf_ok := c.table.funs[flat]; psf_ok {
        parent_sd = &psf.sd
    }
    if parent_sd != nil {
        if fn, fn_ok := parent_sd.functions[right]; fn_ok && fn != nil {
            return fn.name
        }
    }
    return ""
}

// evaluate_comptime_int resolves a comptime-known integer expression. Used
// by sites like `slice_from_ptr` that need to refuse runtime-derived values
// — accepting an attacker-controlled length there is a classic OOB-read/write
// foot-gun. Handles literals, unary minus, named `::` constants (recursively),
// and basic arithmetic + bit-shift operators on comptime operands. Anything
// else returns ok=false; callers should emit a "comptime-known integer
// expected" error so the user gets a clear diagnostic.
evaluate_comptime_int :: proc(c: ^Checker, e: Expr) -> (value: i64, ok: bool) {
    #partial switch v in e {
    case ^Expr_Number:
        return i64(v.value), true
    case ^Expr_Unary:
        if v.op == .Minus {
            inner, inner_ok := evaluate_comptime_int(c, v.operand)
            if inner_ok { return -inner, true }
        }
    case ^Expr_Ident:
        if const_expr, found := c.table.constants[v.name]; found {
            return evaluate_comptime_int(c, const_expr)
        }
    case ^Expr_Binary:
        l, l_ok := evaluate_comptime_int(c, v.left)
        if !l_ok { return 0, false }
        r, r_ok := evaluate_comptime_int(c, v.right)
        if !r_ok { return 0, false }
        #partial switch v.op {
        case .Plus:        return l + r, true
        case .Minus:       return l - r, true
        case .Star:        return l * r, true
        case .Slash:
            if r == 0 { return 0, false }
            return l / r, true
        case .Modulo:
            if r == 0 { return 0, false }
            return l % r, true
        case .Shift_Left:  return l << uint(r), true
        case .Shift_Right: return l >> uint(r), true
        case .Pipe:        return l | r, true
        case .Ampersand:   return l & r, true
        case .Caret:       return l ~ r, true
        }
    case ^Expr_Size_Of:
        // size_of(T) is comptime-known by definition; resolve via the
        // fully-checked size if available, else give up.
        if v.resolved_type != nil {
            return i64(elem_byte_size(llvm_type_from_checker(v.resolved_type), c.checked)), true
        }
    }
    return 0, false
}

// evaluate_comptime_bool resolves a comptime-known boolean expression. Today
// this covers the small surface needed by `#if`: the `#web`/`#native`
// intrinsics, plain bool literals, and `not` of either. Compound boolean
// operators (`and`/`or`) and parens are easy extensions when there's a real
// use case — kept minimal so the failure mode for unsupported expressions is
// a clear "comptime-known boolean expected" error rather than a partial
// evaluation that gives wrong answers.
evaluate_comptime_bool :: proc(c: ^Checker, e: Expr) -> (value: bool, ok: bool) {
    #partial switch v in e {
    case ^Expr_Bool:
        return v.value, true
    case ^Expr_Compiler_Intrinsic:
        #partial switch v.kind {
        case .Web:     return c.target_web, true
        case .Native:  return !c.target_web, true
        case .Windows: return c.target_os == .Windows, true
        case .Linux:   return c.target_os == .Linux,   true
        case .Mac:     return c.target_os == .Mac,     true
        }
    case ^Expr_Unary:
        if v.op == .Not {
            inner, inner_ok := evaluate_comptime_bool(c, v.operand)
            if inner_ok { return !inner, true }
        }
    }
    return false, false
}

// Like resolve_fn_home but reports ambiguity when 2+ visible includes provide
// the same function name. Mirrors resolve_with_ambiguity for type names —
// own definitions in any enclosing scope still win unambiguously; ambiguity
// only fires when the name comes from imports and 2+ imports expose it
// (e.g. `include mara.sdl + include mara.sdl2`, both with PollEvent).
resolve_fn_home_with_ambiguity :: proc(c: ^Checker, env: ^Type_Env, name: string) -> (home: string, ok: bool, ambiguous_owners: [dynamic]string) {
    // Phase 1: own definitions in any enclosing module (always unambiguous).
    if env != nil {
        cur := env
        for cur != nil {
            if cur.owner_module != nil {
                if t, found := cur.types[name]; found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        return cur.owner_module.name, true, nil
                    }
                }
            }
            if cur.is_module_scope { break }
            cur = cur.parent
        }
    }
    // Phase 2: gather distinct include owners exposing this fn.
    distinct_owners: map[string]bool
    owner_list: [dynamic]string
    if env != nil {
        cur := env
        for cur != nil {
            for inc in cur.includes {
                if inc.owner_module == nil { continue }
                if t, found := inc.types[name]; found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        owner := inc.owner_module.name
                        if owner not_in distinct_owners {
                            distinct_owners[owner] = true
                            append(&owner_list, owner)
                        }
                    }
                }
            }
            if cur.is_module_scope { break }
            cur = cur.parent
        }
    }
    if len(owner_list) == 0 {
        // Fall back to fun_homes (registration-time table) for sites that
        // couldn't reach the right env, then to current_package.
        if h, found := c.table.fun_homes[name]; found && h != "" { return h, true, nil }
        return c.current_package, true, nil
    }
    if len(owner_list) == 1 { return owner_list[0], true, nil }
    return "", false, owner_list
}

// Resolve the package prefix for a function name. Walks the env chain (own
// types + includes) to find the module that owns this name at the call site.
// This is critical when two modules export the same name (e.g. PollEvent in
// mara_sdl and mara_sdl2). Falls back to fun_homes (populated at registration
// time) for sites that were unable to thread env through, then to current
// package.
resolve_fn_home :: proc(c: ^Checker, env: ^Type_Env, name: string) -> string {
    if env != nil {
        cur := env
        for cur != nil {
            if cur.owner_module != nil {
                if t, found := cur.types[name]; found {
                    if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun {
                        return cur.owner_module.name
                    }
                }
            }
            for inc in cur.includes {
                if inc.owner_module == nil { continue }
                if t, found := inc.types[name]; found {
                    if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun {
                        return inc.owner_module.name
                    }
                }
            }
            if cur.is_module_scope { break }
            cur = cur.parent
        }
    }
    if h, ok := c.table.fun_homes[name]; ok && h != "" { return h }
    return c.current_package
}


// Populate a fun's field_map from its fields array for O(1) field lookup.
build_field_map :: proc(st: ^Scope_Body) {
    for f, i in st.fields {
        st.field_map[f.name] = i
    }
}

// Populate a callable fun's field_map from its params for O(1) param lookup.
build_param_map :: proc(ft: ^Type_Scope) {
    for p, i in ft.params {
        if p.name != "" {
            ft.field_map[p.name] = i
        }
    }
}

// True iff `name` is a real data field of `sd` (not a class param, not an assoc fn/type
// that happens to have been recorded in field_map).
is_real_field :: proc(sd: ^Scope_Body, name: string) -> bool {
    for f in sd.fields {
        if f.name == name { return true }
    }
    return false
}

// ---------------------------------------------------------------------------
// Checked program output — the result of type checking
// ---------------------------------------------------------------------------

// A resolved function parameter with name and type.
Checked_Param :: struct {
    name:  string,
    type_: Type,
}

// Where this function comes from. Codegen branches on the variant:
//   Source    → emit a normal function body in IR
//   Intrinsic → emit a call to the LLVM intrinsic with `llvm_name`
//   Foreign   → emit `declare`s and call the external symbol via static
//               import lib (the linker writes the DLL/SO dep into the binary)
//
// Foreign-only metadata (library, link_name, prefix) lives in the Foreign
// variant rather than on Checked_Scope itself, so source funs don't carry
// empty fields they never use.
Function_Origin :: union {
    Origin_Source,
    Origin_Intrinsic,
    Origin_Foreign,
}

Origin_Source :: struct {}

Origin_Intrinsic :: struct {
    llvm_name: string,                 // e.g. "llvm.sqrt.f32"
}

Origin_Foreign :: struct {
    library:    string,                // "kernel32", "SDL3", etc.
    link_name:  string,                // C symbol name (prefix + decl name)
    prefix:     string,                // foreign-block prefix, kept for re-emission/diagnostics
}

// A fully resolved function: signature, parameter names, body AST, and the
// origin classification that drives codegen behaviour. Foreigns and
// intrinsics have empty bodies; their work is dictated by the origin tag.
Checked_Scope :: struct {
    name:         string,
    home_package: string,                // owning module flat name; mirrored from the Type_Scope at registration so post-check phases can partition by module without env lookups
    type_:        ^Type_Scope,           // resolved param + return types
    params:       [dynamic]Checked_Param,
    return_types: [dynamic]Type,         // empty = void; len 1 = single; len > 1 = multi-return
    body:         [dynamic]Stmt,         // original AST body
    ast:          ^Stmt_Scope,           // original AST node (for auto-monomorphization)
    origin:       Function_Origin,       // Source / Intrinsic / Foreign — codegen dispatch
    span:         Span,
}

// Checked info for an aliased import package.
// The complete output of check_program. Captures everything the type checker
// knows about the program — type definitions, function signatures, variable
// types, package info. Downstream consumers (codegen, tools) can read this
// instead of re-walking the raw AST.
Checked_Program :: struct {
    // Shared symbol table (type definitions, constants, generics, etc.)
    table:          ^SymbolTable,

    errors:         int,

    // Functions — source, foreign, and intrinsic all live here, distinguished
    // by Checked_Scope.origin. Codegen iterates this map and dispatches on the
    // origin variant when emitting bodies, declares, and the dynamic loader.
    functions:      map[string]Checked_Scope,
    foreign_libs:   map[string]bool,

    // Ordered list of main-package function names (preserves AST order for emission)
    function_order: [dynamic]string,

    // Compile-time constants: name -> resolved integer value (derived from table.constants)
    constant_values: map[string]int,

    // Target platform — drives ABI lowering for .C-convention functions.
    // Inherited from the checker; stamped at check completion.
    target_os:      Target_OS,

    // The main package name (e.g. "Pounce" or "test_1M"). Used by codegen as
    // the default home for symbols not attributable to any specific module
    // — compiler-synthesized helpers, @main, etc. — so per-module emission
    // has a single canonical "main TU" to drop them into.
    main_package:   string,
}

// ---------------------------------------------------------------------------
// Symbol table — single source of truth for all type/symbol information.
// Persists across checking phases; shared between Checker and Checked_Program.
// ---------------------------------------------------------------------------

SymbolTable :: struct {
    // Type registries
    structs:        map[string]^Type_Scope,      // data-layout scopes (struct/class with or without params)
    funs:           map[string]^Type_Scope,      // callable funs and struct constructors (kind=.Struct + params, or kind=.Fun)
    enums:          map[string]^Type_Enum,
    unions:         map[string]^Type_Union,
    distinct_types: map[string]^Type_Distinct,

    // Error_kind set ID assignment counter — incremented as each
    // `Name :: error { ... }` is registered. Encoded as the high 16 bits of
    // each variant's u32 tag so any error_kind variant fits in the open
    // `err` type with a globally unique value.
    error_set_counter: int,

    // Generic templates (unified — data-type and callable)
    generic_templates:       map[string]Generic_Template,
    generic_union_templates: map[string]Generic_Union_Template,

    // Constants
    constants:       map[string]Expr,
    // bare-name -> owning module (flat package name), or "" if multiple
    // modules define the same bare constant name. Bare-name uses error when
    // this maps to "" — the user must qualify with `Module.const_name`.
    constant_owners: map[string]string,

    // Name resolution helpers
    variant_to_enum: map[string]string,

    // Monomorphization cache
    mono_cache:       map[string]^Type_Scope,        // unified: both data and callable monomorphizations
    mono_union_cache: map[string]^Type_Union,        // monomorphized union templates (Maybe(int) -> ^Type_Union)
    mono_fun_cache:   map[string]string,
    mono_fun_bodies: map[string][dynamic]Stmt,    // cloned AST bodies per monomorphization
    fun_asts:       map[string]^Stmt_Scope,         // bare name -> AST for auto-monomorphization
    fun_homes:      map[string]string,              // bare name -> home package; used by post-check phases that lack env

    // Provenance propagation through call boundaries. For functions returning
    // a ref type (slice/ptr), records the SET of parameter indices the return
    // value could trace back to. A call's depth at the site is the max over
    // depth(call.args[i]) for i in the set. Empty set = no tracked sources,
    // depth defaults to 0 (globals / literals / external).
    //
    // The set captures the conditional case: when different control-flow
    // paths assign different params, the union of contributors propagates.
    // Computed lazily on first lookup; pending guards against cycles.
    fun_return_arg_set:     map[^Stmt_Scope][]int,
    fun_return_arg_pending: map[^Stmt_Scope]bool,

    // Config
    has_scope_allocator: bool,
    scope_allocator_name: string,        // bare name from source ("Arena_Basic")
    scope_allocator_type: ^Type_Scope,     // resolved allocator fun (Arena_Basic, Arena_Debug, etc.)
    scope_allocator_args: [dynamic]Expr, // constructor args from Arena_Basic(192 * MB)

    // Shared (DLL/SO) build with `#expose` fn(s) present: the host promises
    // to pass a real Context at runtime, so arena-using constructs (`var`,
    // big-array auto-promotion) are permitted inside the DLL without a local
    // `context.scope_allocator = X` declaration. Gated separately from
    // has_scope_allocator so the *codegen* path still requires the type to
    // be declared (errors at codegen if arena calls would be emitted).
    context_expected_at_runtime: bool,

    // Root type environment (top-level scope)
    root_env: ^Type_Env,
}

// ---------------------------------------------------------------------------
// Checker state — transient state used during a single checking pass.
// Holds a pointer to the shared SymbolTable plus per-check mutable state.
// ---------------------------------------------------------------------------

Checker :: struct {
    table:           ^SymbolTable,
    errors:          int,
    current_package: string,
    target_web:      bool,                // -web build flag, drives #web / #native intrinsics
    target_shared:   bool,                // -shared build flag — package compiles to a DLL/SO; no `main` required
    target_os:       Target_OS,           // OS target, drives #windows / #linux / #mac intrinsics
    type_params:     map[string]Type,
    top_env:         ^Type_Env,
    declared_funs:   map[string]bool,  // bare names of Stmt_Scope declarations (direct calls vs variables)
    // True during the register-pass scan over a function's body fields.
    // Field types are resolved in declaration order, so annotations like
    // `h : fn g` may reference locals not yet added to env. Unresolved names
    // in this pass return Type_Error{} silently; the body-check pass re-runs
    // resolution with all locals in scope and emits real errors then.
    in_register_pass: bool,
    // Namespace-form match arm context: when set, identifier resolution falls
    // back to looking up the name as a field of namespace_subject's struct
    // type (after env/local lookup misses). Lets arm bodies/predicates write
    // bare `quit` instead of `game.events.quit`. Saved/restored when entering
    // and leaving a namespace match's arms.
    namespace_subject:      Expr,
    namespace_subject_type: ^Type_Scope,
    // Dispatch and operator overloading (per-package, saved/restored on module boundaries)
    dispatch_groups:    map[string][dynamic]string,
    operator_overloads: map[Token_Kind][dynamic]string,
    // Module system — all modules are pre-discovered, lexed, and parsed before
    // check_program runs. The checker is a pure consumer of `programs`.
    checked:              ^Checked_Program,        // output: codegen-ready data
    checked_modules:      map[string]^Type_Scope,  // cache: flat name -> checked module-struct
    modules_in_progress:  map[string]bool,         // circular dependency detection
    pre_registered_stmts: map[rawptr]bool,         // stmts whose type allocation was done by register_type_names; Pass 1b finds existing entries and skips re-allocation
    programs:             map[string]^Program,     // every parsed module: dotted name -> merged Program
    compiler_dir:         string,                  // compiler exe dir (kept for diagnostics)
    search_dir:           string,                  // user source dir (kept for diagnostics)
    // Program structure: mara :: fun { std :: fun { ... }, user_modules... }
    mara_env:             ^Type_Env,               // root scope (contains std + user modules)
    std_fun:              ^Type_Scope,               // std module (contains stdlib modules)
    // Expected type hint for the next check_expr call. Set by sites that know
    // the target type (function args, typed assignments, return statements,
    // index expressions). Lets a bare identifier `Video` resolve as
    // `Init_Flags.Video` when the param expects `Init_Flags`, and lets
    // `.Core` find its owner union by name when the expected type isn't a
    // union/enum. Push with `with_expected_hint`; the helper restores after.
    expected_hint: Type,
}

// Set the expected-type hint for the next check_expr call, returning the
// previous value so the caller can restore it. Use `defer c.expected_hint = old`.
push_expected_hint :: proc(c: ^Checker, hint: Type) -> Type {
    old := c.expected_hint
    c.expected_hint = hint
    return old
}

// Variant lookup helpers for `.Variant` and bare-with-expected-type resolution.
// Tries the hint first (a Type_Enum or Type_Union); if that fails (or the hint
// isn't a variant-bearing type), and `dot` is true, searches all visible
// enums/unions in scope. Returns the resolved type and writes Resolved_Name
// metadata onto the ident. Returns nil + false if not resolved.
resolve_variant_ident :: proc(c: ^Checker, e: ^Expr_Ident, hint: Type, env: ^Type_Env, dot: bool) -> (Type, bool) {
    // 1. Try the hint directly.
    if hint != nil {
        if et, ok := hint.(^Type_Enum); ok {
            if val, v_ok := et.variants[e.name]; v_ok {
                e.resolved = Resolved_Enum_Variant{
                    enum_name = et.name,
                    variant   = e.name,
                    value     = val,
                }
                return et, true
            }
        }
        if ut, ok := hint.(^Type_Union); ok {
            if _, v_ok := ut.tag_map[e.name]; v_ok {
                // Data-union variant — return the union type. Codegen for
                // a bare/dot variant value isn't fully meaningful (no payload
                // fields), but match arms / payload-free uses can still
                // reference the variant by name.
                return ut, true
            }
        }
        // Open `err` hint: the slot doesn't pin down a single enum, so we
        // search visible error_kind enums by name — same shape as the
        // dot-fallback below, but restricted to error sets so a non-error
        // variant with a matching name can't accidentally satisfy the slot.
        // Lets `return File_Open_Failed` work in an err return position
        // without requiring the `.` prefix.
        if _, is_err := hint.(Type_Err); is_err {
            err_owners: [dynamic]string
            defer delete(err_owners)
            for ename, edef in c.table.enums {
                if !edef.is_error_kind { continue }
                if e.name not_in edef.variants { continue }
                if is_enum_visible(env, ename) { append(&err_owners, ename) }
            }
            if len(err_owners) > 1 {
                owners := strings.join(err_owners[:], ", ")
                check_error(c, e.span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS,
                    e.name, owners, err_owners[0], e.name)
                return Type_Error{}, true
            }
            if len(err_owners) == 1 {
                ename := err_owners[0]
                if et, et_ok := c.table.enums[ename]; et_ok {
                    if val, v_ok := et.variants[e.name]; v_ok {
                        e.resolved = Resolved_Enum_Variant{
                            enum_name = ename,
                            variant   = e.name,
                            value     = val,
                        }
                        return et, true
                    }
                }
            }
        }
    }
    if !dot { return nil, false }
    // 2. Dot-shorthand fallback: search all visible enums/unions.
    visible_owners: [dynamic]string
    defer delete(visible_owners)
    for ename, edef in c.table.enums {
        if e.name not_in edef.variants { continue }
        if is_enum_visible(env, ename) { append(&visible_owners, ename) }
    }
    if len(visible_owners) > 1 {
        owners := strings.join(visible_owners[:], ", ")
        check_error(c, e.span, TYPE_AMBIGUOUS_DEFINED_USE_QUALIFIED_ACCESS,
            e.name, owners, visible_owners[0], e.name)
        return Type_Error{}, true
    }
    if len(visible_owners) == 1 {
        ename := visible_owners[0]
        if et, et_ok := c.table.enums[ename]; et_ok {
            if val, v_ok := et.variants[e.name]; v_ok {
                e.resolved = Resolved_Enum_Variant{
                    enum_name = ename,
                    variant   = e.name,
                    value     = val,
                }
                return et, true
            }
        }
    }
    return nil, false
}

check_error :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    emit_diagnostic(.Type_Error, format_location(span.file, span.line, span.col), msg, ..args)
    c.errors += 1
}

check_warning :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    emit_diagnostic(.Warning, format_location(span.file, span.line, span.col), msg, ..args)
}

// Render a readable source-level name for an expression used in a diagnostic —
// e.g. `dst_x`, `glyphs[i].x`, `ttf.head`. Returns "" for expressions with no
// natural name (literals, calls, arithmetic) so callers can omit the clause.
expr_diag_name :: proc(e: Expr) -> string {
    #partial switch v in e {
    case ^Expr_Ident:
        return v.name
    case ^Expr_Field_Access:
        base := expr_diag_name(v.expr)
        if base == "" { return v.field }
        return fmt.tprintf("%s.%s", base, v.field)
    case ^Expr_Index:
        base := expr_diag_name(v.expr)
        if base == "" { return "" }
        idx := expr_diag_name(v.index)
        if idx == "" { return base }
        return fmt.tprintf("%s[%s]", base, idx)
    case ^Expr_Call:
        if v.name != "" { return fmt.tprintf("%s()", v.name) }
    }
    return ""
}

// Collect the named sub-expressions of `e` whose stamped type is a wider
// numeric than `target` can hold — the operands that pushed a compound
// expression past the assignment's width. Each renders as "name (type)". Used
// to point a numeric-mismatch error at where the offending width entered.
collect_wide_sources :: proc(e: Expr, target: Type, out: ^[dynamic]string) {
    #partial switch v in e {
    case ^Expr_Binary:
        collect_wide_sources(v.left, target, out)
        collect_wide_sources(v.right, target, out)
    case ^Expr_Unary:
        collect_wide_sources(v.operand, target, out)
    case:
        p := expr_type_ptr(e)
        if p == nil { return }
        t := p^
        if t == nil || !is_numeric(t) || is_infer(t) { return }
        if !types_incompatible(target, t) || value_preserving_widen(t, target) { return }
        name := expr_diag_name(e)
        if name == "" { return }
        entry := fmt.tprintf("%s (%s)", name, type_name(t))
        for s in out^ { if s == entry { return } }   // dedup
        append(out, entry)
    }
}

// "atlas.per_row (i64), atlas.cell (i64)" for the operands of `e` that don't
// fit `target`, or "" if none are nameable. Best-effort: literals and
// unnameable sub-expressions are skipped.
wide_source_clause :: proc(e: Expr, target: Type) -> string {
    srcs: [dynamic]string
    defer delete(srcs)
    collect_wide_sources(e, target, &srcs)
    if len(srcs) == 0 { return "" }
    return strings.join(srcs[:], ", ")
}

// Emit "cannot assign X to variable 'v' of type Y", appending a "— from
// <sources>" trailer that names the wide operands when the RHS is a compound
// expression whose extra width traces to named sub-expressions.
emit_assign_var_error :: proc(c: ^Checker, span: Span, val_type: Type, name: string, target: Type, rhs: Expr) {
    if clause := wide_source_clause(rhs, target); clause != "" {
        check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE_FROM,
            type_name(val_type), name, type_name(target), clause)
    } else {
        check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
            type_name(val_type), name, type_name(target))
    }
}

// "name (type)" when the source expression has a nameable form, else just the
// bare type. Used by assignment/field diagnostics so the offending variable is
// visible next to its inferred type.
assign_source_desc :: proc(e: Expr, t: Type) -> string {
    n := expr_diag_name(e)
    if n == "" { return type_name(t) }
    return fmt.tprintf("%s (%s)", n, type_name(t))
}

// Walk an expression looking for `Expr_Call` whose direct args include
// `Expr_Self`. Returns the call's name on first hit. DFS order means
// nested-most hits first — `wrap(view_and_projections(#self))` reports
// "view_and_projections" (the actual #self consumer), not the wrapper.
find_self_call_name :: proc(e: Expr) -> (name: string, found: bool) {
    if e == nil { return "", false }
    #partial switch v in e {
    case ^Expr_Call:
        for arg in v.args {
            if n, ok := find_self_call_name(arg); ok { return n, true }
        }
        for arg in v.args {
            if _, is_self := arg.(^Expr_Self); is_self {
                return v.name, true
            }
        }
    case ^Expr_Binary:
        if n, ok := find_self_call_name(v.left); ok { return n, true }
        return find_self_call_name(v.right)
    case ^Expr_Unary:
        return find_self_call_name(v.operand)
    case ^Expr_Field_Access:
        return find_self_call_name(v.expr)
    case ^Expr_Index:
        if n, ok := find_self_call_name(v.expr); ok { return n, true }
        return find_self_call_name(v.index)
    case ^Expr_Slice:
        if n, ok := find_self_call_name(v.expr); ok { return n, true }
        if n, ok := find_self_call_name(v.low); ok { return n, true }
        return find_self_call_name(v.high)
    case ^Expr_Struct_Literal:
        for f in v.fields {
            if n, ok := find_self_call_name(f.value); ok { return n, true }
        }
        if v.is_broadcast {
            return find_self_call_name(v.broadcast_value)
        }
    case ^Expr_Array:
        for elem in v.elements {
            if n, ok := find_self_call_name(elem); ok { return n, true }
        }
    case ^Expr_If:
        if n, ok := find_self_call_name(v.then_expr); ok { return n, true }
        return find_self_call_name(v.else_expr)
    case ^Expr_Take:
        return find_self_call_name(v.storage)
    case ^Expr_Tuple_Default:
        return find_self_call_name(v.source)
    }
    return "", false
}

// True if `#self` appears anywhere in `e`. Used to catch the inline form
// (`x := #self.fov_y * 2`) that doesn't go through a function call.
contains_self_anywhere :: proc(e: Expr) -> bool {
    if e == nil { return false }
    #partial switch v in e {
    case ^Expr_Self:
        return true
    case ^Expr_Call:
        for arg in v.args { if contains_self_anywhere(arg) { return true } }
    case ^Expr_Binary:
        return contains_self_anywhere(v.left) || contains_self_anywhere(v.right)
    case ^Expr_Unary:
        return contains_self_anywhere(v.operand)
    case ^Expr_Field_Access:
        return contains_self_anywhere(v.expr)
    case ^Expr_Index:
        return contains_self_anywhere(v.expr) || contains_self_anywhere(v.index)
    case ^Expr_Slice:
        return contains_self_anywhere(v.expr) || contains_self_anywhere(v.low) || contains_self_anywhere(v.high)
    case ^Expr_Struct_Literal:
        for f in v.fields { if contains_self_anywhere(f.value) { return true } }
        if v.is_broadcast { return contains_self_anywhere(v.broadcast_value) }
    case ^Expr_Array:
        for elem in v.elements { if contains_self_anywhere(elem) { return true } }
    case ^Expr_If:
        return contains_self_anywhere(v.condition) ||
               contains_self_anywhere(v.then_expr) ||
               contains_self_anywhere(v.else_expr)
    case ^Expr_Take:
        return contains_self_anywhere(v.storage)
    case ^Expr_Tuple_Default:
        return contains_self_anywhere(v.source)
    }
    return false
}

// Warn when a struct field initializer hands `#self` to anything that
// could read partially-constructed state, while other field decls
// still follow. The function-call form (`x := helper(#self)`) is the
// silent-zero case from the Camera porting session — helper reads
// `cam.fov_y` etc. and gets zeros because later decls haven't written
// yet. The inline shape (`x := #self.fov_y * 2`) is caught by the
// same check via `contains_self_anywhere` as a fallback.
check_early_self_decls :: proc(c: ^Checker, body: [dynamic]Stmt) {
    n := len(body)
    if n == 0 { return }
    // Single backward scan so each later "does any Stmt_Decl follow?"
    // probe is O(1). Without this, the check is O(n^2) over the body.
    has_decl_after: [dynamic]bool
    defer delete(has_decl_after)
    resize(&has_decl_after, n)
    seen := false
    for i := n - 1; i >= 0; i -= 1 {
        has_decl_after[i] = seen
        if _, is_decl := body[i].(^Stmt_Decl); is_decl {
            seen = true
        }
    }
    for stmt, i in body {
        decl, is_decl := stmt.(^Stmt_Decl)
        if !is_decl { continue }
        if len(decl.init_values) == 0 { continue }
        if !has_decl_after[i] { continue }
        for init in decl.init_values {
            if call_name, ok := find_self_call_name(init); ok {
                check_warning(c, decl.span,
                    TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS,
                    call_name)
                break
            } else if contains_self_anywhere(init) {
                names := strings.join(decl.names[:], ", ")
                defer delete(names)
                check_warning(c, decl.span,
                    TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS,
                    names)
                break
            }
        }
    }
}

// Reject an uninitialized declaration whose type is a class that requires
// ctor arguments without defaults.
//
// `field: Arena_Basic` means "use constructor defaults", but if the ctor has
// a required arg with no default (e.g. `class(cap: int)`), no valid defaults
// exist — the declaration is unresolvable. Catch it here rather than letting
// codegen walk the class body and fail with nonsense "undefined variable"
// errors about ctor args the user never wrote.
//
// Only applies to Type_Scope with kind=.Struct and params (i.e. classes with ctor args).
// Pure data structs (kind=.Struct, no params) and callable funs aren't affected.
check_uninitialized_class_decl :: proc(c: ^Checker, span: Span, name: string, field_type: Type) {
    // Walk through fixed-array and partial-array layers: `[6]Camera` and
    // `[..6]Camera` need the same check as bare `Camera` — every element
    // requires construction, and the array can't bulk-default-construct.
    elem_type := field_type
    is_array := false
    for {
        base := distinct_base(elem_type)
        if fa, ok := base.(^Type_Fixed_Array); ok {
            elem_type = fa.elem
            is_array = true
            continue
        }
        if pa, ok := base.(^Type_Partial_Array); ok {
            elem_type = pa.elem
            is_array = true
            continue
        }
        break
    }
    class_ft, ok := elem_type.(^Type_Scope)
    if !ok || class_ft.kind != .Struct { return }
    if len(class_ft.params) == 0 { return }
    for p in class_ft.params {
        if p.default_value == nil {
            // Build a signature like `Camera(w: f32, h: f32, fovy: f32)` so the
            // user can see exactly what to pass.
            sig: strings.Builder
            strings.builder_init(&sig)
            strings.write_string(&sig, class_ft.name)
            strings.write_string(&sig, "(")
            for pp, i in class_ft.params {
                if i > 0 { strings.write_string(&sig, ", ") }
                strings.write_string(&sig, pp.name)
                if pp.type_ != nil {
                    strings.write_string(&sig, ": ")
                    strings.write_string(&sig, type_name(pp.type_))
                }
            }
            strings.write_string(&sig, ")")

            if is_array {
                check_warning(c, span,
                    TYPE_WON_GET_AUTO_CONSTRUCTED_DECLARED,
                    class_ft.name, name)
            } else {
                check_error(c, span,
                    TYPE_TYPE_SELF_CONSTRUCTING_CALL_LIKE,
                    name, class_ft.name, strings.to_string(sig), name, class_ft.name, class_ft.name)
            }
            return
        }
    }
}


// ---------------------------------------------------------------------------
// Resolve a parser Type_Expr to a checker Type
// ---------------------------------------------------------------------------

resolve_type_expr :: proc(te: Type_Expr, c: ^Checker = nil, span: Span = {}, const_values: ^map[string]int = nil, env: ^Type_Env = nil) -> Type {
    // `~T` outside a generic-parameter declaration: the tilde modifier is
    // only meaningful as a shape constraint on a generic param's type
    // (`Foo :: struct (s: ~T)`). At any other use site it's a syntax
    // error — the promotion to a generic param has to happen at the
    // declaration, not at the use, so the type-checker can monomorphize.
    if tn, is_tn := te.(Type_Name); is_tn && tn.tilde {
        if c != nil {
            check_error(c, span,
                TYPE_ONLY_VALID_TYPE_GENERIC_PARAMETER,
                tn.name, tn.name)
        }
        return Type_Error{}
    }

    switch t in te {
    case Type_Name:
        switch t.name {
        case "int":
            // Reserved keyword; not a valid type today. Kept in the lexer
            // so the name is available if word-sized `int` returns later.
            if c != nil {
                check_error(c, span, TYPE_TYPE_INT_RESERVED_USE_I64)
            }
            return Type_Error{}
        case "f64":    return Type_F64{}
        case "bool":   return Type_Bool{}
        case "c8":     return Type_C8{}
        case "utf8":   return Type_Utf8{}
        case "byte":   return Type_Byte{}
        case "void":   return Type_Void{}
        case "err":    return Type_Err{}
        case "i8":     return Type_Numeric{kind = .Signed,   bits = 8}
        case "i16":    return Type_Numeric{kind = .Signed,   bits = 16}
        case "i32":    return Type_Numeric{kind = .Signed,   bits = 32}
        case "i64":    return Type_Numeric{kind = .Signed,   bits = 64}
        case "i128":   return Type_Numeric{kind = .Signed,   bits = 128}
        case "u8":     return Type_Numeric{kind = .Unsigned, bits = 8}
        case "u16":    return Type_Numeric{kind = .Unsigned, bits = 16}
        case "u32":    return Type_Numeric{kind = .Unsigned, bits = 32}
        case "u64":    return Type_Numeric{kind = .Unsigned, bits = 64}
        case "u128":   return Type_Numeric{kind = .Unsigned, bits = 128}
        case "uint":
            // Reserved keyword; same retired status as `int`. Use 'u64' or 'usize'.
            if c != nil {
                check_error(c, span, TYPE_TYPE_UINT_RESERVED_USE_U64)
            }
            return Type_Error{}
        case "f16":    return Type_Numeric{kind = .Float,    bits = 16}
        case "f32":    return Type_Numeric{kind = .Float,    bits = 32}
        // Word-sized (target-dependent: i64 on x86-64, i32 on wasm32). bits=0
        // is the marker; codegen picks the actual width per build.
        case "usize":  return Type_Numeric{kind = .Unsigned, bits = 0}
        case "isize":  return Type_Numeric{kind = .Signed,   bits = 0}
        // "IO" removed — functions without return type have nil return_type
        }
        // Check for qualified type name (e.g. "cam.Camera" -> look up in package)
        dot := strings.index_byte(t.name, '.')
        if c != nil && dot >= 0 {
            alias := t.name[:dot]
            type_name_str := t.name[dot+1:]
            // Try import alias: alias.TypeName -> flat key
            // Pass env so `sdl := include mara.sdl` -style aliases resolve.
            flat := resolve_type_name(c, type_name_str, alias, env)
            if flat != "" {
                if st, ok := c.table.structs[flat]; ok { return st }
                if st, ok := c.table.funs[flat]; ok { return st }
                if ut, ok := c.table.unions[flat]; ok { return ut }
                if et, ok := c.table.enums[flat]; ok { return et }
                if dt, ok := c.table.distinct_types[flat]; ok { return dt }
            }
            // Resolve the alias itself as a type name (for Union.Variant and Struct.AssocType)
            alias_flat := resolve_type_name(c, alias, "", env)
            // Check for union variant type: UnionName.VariantName -> synthetic struct
            if ut, ut_ok := c.table.unions[alias_flat]; ut_ok {
                if vs_key, vs_ok := ut.variant_structs[type_name_str]; vs_ok {
                    if st, ok := c.table.structs[vs_key]; ok {
                        return st
                    }
                    if st, ok := c.table.funs[vs_key]; ok {
                        return st
                    }
                }
            }
            // Check for struct associated type: StructName.Type -> associated type
            parent_sd: ^Scope_Body
            if pss, pss_ok := c.table.structs[alias_flat]; pss_ok {
                parent_sd = &pss.sd
            } else if psf, psf_ok := c.table.funs[alias_flat]; psf_ok {
                parent_sd = &psf.sd
            }
            if parent_sd != nil {
                if inner_t, at_ok := parent_sd.types[type_name_str]; at_ok {
                    return inner_t
                }
                // Check for associated function: StructName.fn_name -> Type_Func
                if fn, fn_ok := parent_sd.functions[type_name_str]; fn_ok && fn != nil {
                    return fn
                }
            }
            // Check for variable.assoc_fn: game.test_print where game is a local variable
            if env != nil {
                if var_type, var_ok := type_env_get(env, alias); var_ok {
                    if var_sd := as_scope_body(var_type); var_sd != nil {
                        if fn, fn_ok := var_sd.functions[type_name_str]; fn_ok && fn != nil {
                            return fn
                        }
                    }
                }
            }
        }
        // Check local env for bare type names (nested types in scope).
        // Owned-first semantics: a local `Timer :: struct {...}` in mod_env
        // beats an enum-variant `Timer` that flowed into the file_env via
        // `sdl :: include mara.sdl2`. Without this, the per-file env's
        // includes shadow the parent module env's own type definitions.
        // Also detects multi-import ambiguity (`include mara.sdl3` +
        // `include mara.sdl2` both exposing `PollEvent`) and errors with a
        // disambiguation hint instead of silently picking one.
        if env != nil {
            local_type, local_ok, ambiguous_owners := resolve_with_ambiguity(c, env, t.name)
            if local_ok { return local_type }
            if len(ambiguous_owners) > 1 {
                if c != nil {
                    owner_list := strings.join(ambiguous_owners[:], ", ")
                    check_error(c, span, TYPE_TYPE_NAME_AMBIGUOUS_DEFINED_USE, t.name, owner_list)
                }
                return Type_Error{}
            }
        }
        // Check for user-defined struct/enum/union/distinct type
        if c != nil {
            flat := resolve_type_name(c, t.name, "", env)
            if st, ok := c.table.structs[flat]; ok {
                return st
            }
            if st, ok := c.table.funs[flat]; ok {
                return st
            }
            if ut, ok := c.table.unions[flat]; ok {
                return ut
            }
            if et, ok := c.table.enums[flat]; ok {
                return et
            }
            if dt, ok := c.table.distinct_types[flat]; ok {
                return dt
            }
            // Bare-name fallback for compiler-synthesized globals like
            // `Context` and `Args` — they're registered in c.table.funs
            // without a package prefix and would otherwise miss the lookup.
            if st, ok := c.table.funs[t.name]; ok {
                return st
            }
            // Check active generic type parameters (during generic function body checking)
            if tp, tp_ok := c.type_params[t.name]; tp_ok {
                return tp
            }
            // Generic struct with all-defaulted params: bare `String` -> `String(256)`
            // or bare `Program` -> `Program(void)`.
            if tmpl, tmpl_ok := &c.table.generic_templates[t.name]; tmpl_ok {
                all_defaulted := true
                type_args: [dynamic]Type
                for param in tmpl.generic_params {
                    if param.is_const && param.has_default {
                        append(&type_args, Type_Const_Int{value = param.default_value})
                    } else if !param.is_const && param.default_type_expr != nil {
                        append(&type_args, resolve_type_expr(param.default_type_expr, c, span, env = env))
                    } else {
                        all_defaulted = false
                        break
                    }
                }
                if all_defaulted && len(type_args) == len(tmpl.generic_params) {
                    return instantiate_generic_struct(c, tmpl, type_args[:], span)
                }
                delete(type_args)
            }
            check_error(c, span, TYPE_UNKNOWN_TYPE, t.name)
        }
        return Type_Error{}
    case ^Type_Array:
        elem := resolve_type_expr(t.elem, c, span, const_values = const_values, env = env)
        fa := new(Type_Fixed_Array)
        fa.has_sentinel = t.has_sentinel
        fa.sentinel = t.sentinel
        if t.index_type != nil {
            fa.index_type = resolve_type_expr(t.index_type, c, span, env = env)
        }
        // Expression-based size: try comptime evaluation first (handles
        // `17 * MB`, named `::` constants, bit-shifts, etc.). Only error
        // if the expression genuinely depends on runtime values.
        if t.size_expr != nil {
            if c != nil {
                if val, comptime_ok := evaluate_comptime_int(c, t.size_expr); comptime_ok {
                    fa.size = int(val)
                    fa.elem = elem
                    return fa
                }
                check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
            }
            return Type_Error{}
        }
        if t.size_name != "" {
            resolved := false
            // Path 1: checker available (type checking phase)
            if c != nil {
                if const_expr, found := c.table.constants[t.size_name]; found {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        fa.size = int(i_val)
                        resolved = true
                    } else {
                        check_error(c, span, TYPE_ARRAY_SIZE_CONSTANT_COMPILE_TIME, t.size_name)
                    }
                } else {
                    // Not a constant — runtime-sized arrays must use var Array
                    check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2, t.size_name, type_name(elem))
                    return Type_Error{}
                }
            }
            // Path 2: pre-resolved constant values (codegen phase)
            if !resolved && const_values != nil {
                if val, found := const_values[t.size_name]; found {
                    fa.size = val
                }
            }
        } else {
            fa.size = t.size
        }
        fa.elem = elem
        return fa
    case ^Type_Pointer:
        elem := resolve_type_expr(t.elem, c, span, env = env)
        pt := new(Type_Ptr)
        pt.elem = elem
        return pt
    case ^Type_Slice_Expr:
        elem := resolve_type_expr(t.elem, c, span, env = env)
        sl := new(Type_Slice)
        sl.elem = elem
        sl.has_sentinel = t.has_sentinel
        sl.sentinel = t.sentinel
        return sl
    case ^Type_Partial_Array_Expr:
        elem := resolve_type_expr(t.elem, c, span, env = env)
        pa := new(Type_Partial_Array)
        pa.elem = elem
        pa.has_sentinel = t.has_sentinel
        pa.sentinel = t.sentinel
        if t.size_expr != nil {
            if c != nil {
                if val, comptime_ok := evaluate_comptime_int(c, t.size_expr); comptime_ok {
                    pa.size = int(val)
                    return pa
                }
                // Runtime partial-array size: must be a compile-time constant.
                check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
            }
            return Type_Error{}
        }
        if t.size_name != "" {
            if c != nil {
                if const_expr, found := c.table.constants[t.size_name]; found {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        pa.size = int(i_val)
                        return pa
                    }
                    check_error(c, span, TYPE_PARTIAL_ARRAY_SIZE_CONSTANT_COMPILE, t.size_name)
                    return Type_Error{}
                }
                // Non-constant named partial-array size: must be a compile-time constant.
                check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE_2, t.size_name, type_name(elem))
                return Type_Error{}
            }
            if const_values != nil {
                if val, found := const_values[t.size_name]; found {
                    pa.size = val
                    return pa
                }
            }
            return Type_Error{}
        }
        pa.size = t.size
        return pa
    case ^Type_Generic_Instance:
        if c == nil {
            return Type_Error{}
        }
        // Look up generic struct template first to know which params are const
        tmpl_ptr: ^Generic_Template
        if tp, tp_ok := &c.table.generic_templates[t.name]; tp_ok {
            tmpl_ptr = tp
        }
        // Resolve type arguments — const params that are bare identifiers become runtime size refs
        type_args: [dynamic]Type
        for arg, i in t.type_args {
            is_const_param := tmpl_ptr != nil && i < len(tmpl_ptr.generic_params) && tmpl_ptr.generic_params[i].is_const
            if is_const_param {
                // Const param position: resolve as const value or runtime expression
                if tn, tn_ok := arg.(Type_Name); tn_ok {
                    // Bare identifier in const position — check if it's a compile-time constant
                    if const_expr, found := c.table.constants[tn.name]; found {
                        if _, i_val, ok := extract_constant_value(const_expr); ok {
                            append(&type_args, Type_Const_Int{value = int(i_val)})
                            continue
                        }
                    }
                    // Not a constant — treat as runtime variable reference
                    ident := new_clone(Expr_Ident{name = tn.name, span = tn.span})
                    append(&type_args, Type_Runtime_Size{expr = ident})
                    continue
                }
            }
            append(&type_args, resolve_type_expr(arg, c, span, env = env))
        }
        // Look up generic struct template
        if tmpl_ptr != nil {
            tmpl := tmpl_ptr
            // Fill in missing params from defaults: const defaults stamp a
            // Type_Const_Int, type defaults (incl. `~T = void`) resolve their
            // stashed default_type_expr through the standard pipeline.
            for i := len(type_args); i < len(tmpl.generic_params); i += 1 {
                param := tmpl.generic_params[i]
                if param.is_const && param.has_default {
                    append(&type_args, Type_Const_Int{value = param.default_value})
                } else if param.default_type_expr != nil {
                    append(&type_args, resolve_type_expr(param.default_type_expr, c, span, env = env))
                }
            }
            if len(type_args) != len(tmpl.generic_params) {
                check_error(c, span, TYPE_EXPECTS_TYPE_ARGUMENT,
                    t.name, len(tmpl.generic_params), len(type_args))
                return Type_Error{}
            }
            return instantiate_generic_struct(c, tmpl, type_args[:], span)
        }
        // Generic union template: `Maybe(int)` / `Maybe(^Foo)`. Parallel path
        // to generic structs — each (template, type-args) tuple monomorphizes
        // to a concrete Type_Union, cached in mono_union_cache.
        if utmpl_ptr, utmpl_ok := &c.table.generic_union_templates[t.name]; utmpl_ok {
            if len(type_args) != len(utmpl_ptr.generic_params) {
                check_error(c, span, TYPE_EXPECTS_TYPE_ARGUMENT,
                    t.name, len(utmpl_ptr.generic_params), len(type_args))
                return Type_Error{}
            }
            return instantiate_generic_union(c, utmpl_ptr, type_args[:], span)
        }
        // Sized-slice on distinct slice alias: `String2(N)` where
        // `String2 :: distinct [, 0]utf8`. Return the distinct type; the
        // capacity is captured separately on Stmt_Decl.slice_cap_expr.
        if c != nil && len(t.type_args) == 1 {
            flat := resolve_type_name(c, t.name, "", env)
            if flat == "" { flat = t.name }
            if dt, found := c.table.distinct_types[flat]; found {
                if _, is_slice := dt.base_type.(^Type_Slice); is_slice {
                    return dt
                }
            }
            // `[]Mesh_Data(12)` — non-generic struct as a sized-slice element.
            // Resolve to the bare struct type; the (12) is allocation info
            // that Stmt_Decl.slice_cap_expr captures separately on the decl
            // (see the slice-elem rewrite in register_and_check_declarations).
            // For struct-field contexts (where there's no slice_cap_expr slot)
            // the (12) is silently ignored — the field is just a slice header.
            if ss, ss_ok := c.table.structs[flat]; ss_ok {
                return ss
            }
            if env != nil {
                if t_val, t_ok := type_env_get(env, t.name); t_ok {
                    if _, ts_ok := t_val.(^Type_Scope); ts_ok {
                        return t_val
                    }
                }
            }
        }
        // If the name resolves to a struct/class with constructor params, the
        // user has written `field: Name(args)` thinking of it as a
        // constructor call — that's the expression-position form, not type
        // position. Point them at the right syntax.
        if env != nil {
            if t_val, t_ok := type_env_get(env, t.name); t_ok {
                if ts, ts_ok := t_val.(^Type_Scope); ts_ok && ts.kind == .Struct && len(ts.params) > 0 {
                    check_error(c, span,
                        TYPE_STRUCT_CLASS_CONSTRUCTOR_PARAMS_GENERIC,
                        t.name, t.name, t.name, t.name)
                    return Type_Error{}
                }
            }
        }
        check_error(c, span, TYPE_UNKNOWN_TYPE, t.name)
        return Type_Error{}
    case ^Type_Func_Expr:
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in t.params {
            append(&ft.params, Struct_Type_Field{type_ = resolve_type_expr(p, c, span, env = env)})
        }
        for rte in t.return_types {
            append(&ft.return_types, resolve_type_expr(rte, c, span, env = env))
        }
        return ft
    case Type_Of_Name:
        // `fn name` — resolves to the nominal function type of a named function
        // or function-valued alias. Env first (catches local aliases like
        // `game_frame := game_run` then `x : fn game_frame`); falls back to the
        // module function table for `fn game_run`. Qualified names like
        // `fn sdl.init` resolve through the alias env or package.
        //
        // During register-pass scanning of a function body's fields, locals
        // may not yet be in env — we return Type_Error silently and let the
        // body-check pass emit real errors.
        silent := c != nil && c.in_register_pass
        dot := strings.index_byte(t.name, '.')
        if dot < 0 {
            if env != nil {
                if val_type, ok := type_env_get(env, t.name); ok {
                    if sc, sc_ok := val_type.(^Type_Scope); sc_ok && sc.kind == .Fun {
                        return sc
                    }
                    if c != nil && !silent {
                        check_error(c, span,
                            TYPE_FN_REQUIRES_FUNCTION_VALUED_NAME,
                            t.name, t.name, type_name(val_type))
                    }
                    return Type_Error{}
                }
            }
            if c != nil {
                flat := resolve_type_name(c, t.name, "", env)
                if fn_type, ok := c.table.funs[flat]; ok && fn_type.kind == .Fun {
                    return fn_type
                }
                if !silent {
                    check_error(c, span, TYPE_UNKNOWN_FUNCTION_FN, t.name, t.name)
                }
            }
            return Type_Error{}
        }
        // Qualified: fn alias.name — alias is either a module include or a local
        // struct variable exposing functions.
        alias := t.name[:dot]
        bare := t.name[dot+1:]
        if c != nil {
            flat := resolve_type_name(c, bare, alias, env)
            if flat != "" {
                if fn_type, ok := c.table.funs[flat]; ok && fn_type.kind == .Fun {
                    return fn_type
                }
            }
            // Try variable.assoc_fn: local var whose type exposes an assoc fn
            if env != nil {
                if var_type, var_ok := type_env_get(env, alias); var_ok {
                    if var_sd := as_scope_body(var_type); var_sd != nil {
                        if fn, fn_ok := var_sd.functions[bare]; fn_ok && fn != nil && fn.kind == .Fun {
                            return fn
                        }
                    }
                }
            }
            if !silent {
                check_error(c, span, TYPE_UNKNOWN_FUNCTION_FN, t.name, t.name)
            }
        }
        return Type_Error{}
    case Type_Const_Value:
        return Type_Const_Int{value = t.value}
    case Type_Const_Expr:
        if val, ok := const_eval_int(t.expr, c); ok {
            return Type_Const_Int{value = val}
        }
        return Type_Runtime_Size{expr = t.expr}
    }
    return Type_Error{}
}

// ---------------------------------------------------------------------------
// Generic monomorphization
// ---------------------------------------------------------------------------

// Build a mangled name for a generic instantiation: "Array" + [int] -> "Array__int"
mangle_generic_name :: proc(base: string, type_args: []Type) -> string {
    parts: [dynamic]string
    defer delete(parts)
    append(&parts, base)
    for arg in type_args {
        append(&parts, sanitize_for_identifier(type_name(arg)))
    }
    return strings.join(parts[:], "__")
}

// Mara type names like `^Box` or `[]Foo` contain characters LLVM rejects in
// identifiers. Replace them with safe equivalents so mangled names are usable
// as LLVM struct names.
sanitize_for_identifier :: proc(s: string) -> string {
    if strings.index_any(s, "^[]., ") < 0 {
        return s
    }
    b: strings.Builder
    strings.builder_init(&b)
    for r in s {
        switch r {
        case '^': strings.write_string(&b, "ptr_")
        case '[': strings.write_string(&b, "arr_")
        case ']': // drop
        case ',': strings.write_string(&b, "_")
        case '.': strings.write_string(&b, "_")
        case ' ': // drop
        case:     strings.write_rune(&b, r)
        }
    }
    return strings.to_string(b)
}

// Resolve a type expression with generic type parameter substitutions.
// Used during monomorphization to replace T with the concrete type.
resolve_type_expr_with_subst :: proc(te: Type_Expr, c: ^Checker, span: Span, subst: ^map[string]Type) -> Type {
    // `~T` outside a generic-param decl: same rejection as the non-subst
    // path. Substitutions never reintroduce tilde.
    if tn, is_tn := te.(Type_Name); is_tn && tn.tilde {
        if c != nil {
            check_error(c, span,
                TYPE_ONLY_VALID_TYPE_GENERIC_PARAMETER,
                tn.name, tn.name)
        }
        return Type_Error{}
    }

    switch t in te {
    case Type_Name:
        // Check substitution map first (for generic type params like T, K, V)
        if sub_type, ok := subst[t.name]; ok {
            return sub_type
        }
        // Fall through to normal resolution
        return resolve_type_expr(te, c, span)
    case ^Type_Array:
        elem := resolve_type_expr_with_subst(t.elem, c, span, subst)
        fa := new(Type_Fixed_Array)
        fa.has_sentinel = t.has_sentinel
        fa.sentinel = t.sentinel
        if t.index_type != nil {
            fa.index_type = resolve_type_expr_with_subst(t.index_type, c, span, subst)
        }
        if t.size_name != "" {
            resolved := false
            // First check substitution map (for const generic params like n)
            if sub_type, ok := subst[t.size_name]; ok {
                if ci, ci_ok := sub_type.(Type_Const_Int); ci_ok {
                    fa.size = ci.value
                    resolved = true
                } else if _, rs_ok := sub_type.(Type_Runtime_Size); rs_ok {
                    check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
                    return Type_Error{}
                }
            }
            // Fall back to named constants
            if !resolved && c != nil {
                if const_expr, found := c.table.constants[t.size_name]; found {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        fa.size = int(i_val)
                    }
                }
            }
        } else if t.size_expr != nil {
            check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
            return Type_Error{}
        } else {
            fa.size = t.size
        }
        fa.elem = elem
        return fa
    case ^Type_Pointer:
        elem := resolve_type_expr_with_subst(t.elem, c, span, subst)
        pt := new(Type_Ptr)
        pt.elem = elem
        return pt
    case ^Type_Slice_Expr:
        elem := resolve_type_expr_with_subst(t.elem, c, span, subst)
        sl := new(Type_Slice)
        sl.elem = elem
        sl.has_sentinel = t.has_sentinel
        sl.sentinel = t.sentinel
        return sl
    case ^Type_Partial_Array_Expr:
        elem := resolve_type_expr_with_subst(t.elem, c, span, subst)
        pa := new(Type_Partial_Array)
        pa.elem = elem
        pa.has_sentinel = t.has_sentinel
        pa.sentinel = t.sentinel
        if t.size_name != "" {
            if val, found := subst[t.size_name]; found {
                if cv, ok := val.(Type_Const_Int); ok {
                    pa.size = cv.value
                } else if _, rt_ok := val.(Type_Runtime_Size); rt_ok {
                    check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
                    return Type_Error{}
                }
            } else if c != nil {
                if const_expr, found2 := c.table.constants[t.size_name]; found2 {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        pa.size = int(i_val)
                    }
                }
            }
        } else if t.size_expr != nil {
            check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
            return Type_Error{}
        } else {
            pa.size = t.size
        }
        return pa
    case ^Type_Generic_Instance:
        // Recursive generic instantiation: a field type like Map(T, int) inside a generic
        type_args: [dynamic]Type
        for arg in t.type_args {
            append(&type_args, resolve_type_expr_with_subst(arg, c, span, subst))
        }
        if tmpl, tmpl_ok := &c.table.generic_templates[t.name]; tmpl_ok {
            // Fill in missing params from subst or defaults
            for i := len(type_args); i < len(tmpl.generic_params); i += 1 {
                param := tmpl.generic_params[i]
                if val, val_ok := subst[param.name]; val_ok && val != nil {
                    append(&type_args, val)
                } else if param.is_const && param.has_default {
                    append(&type_args, Type_Const_Int{value = param.default_value})
                }
            }
            return instantiate_generic_struct(c, tmpl, type_args[:], span)
        }
        check_error(c, span, TYPE_UNKNOWN_GENERIC_TYPE, t.name)
        return Type_Error{}
    case ^Type_Func_Expr:
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in t.params {
            append(&ft.params, Struct_Type_Field{type_ = resolve_type_expr_with_subst(p, c, span, subst)})
        }
        for rte in t.return_types {
            append(&ft.return_types, resolve_type_expr_with_subst(rte, c, span, subst))
        }
        return ft
    case Type_Of_Name:
        // `fn name` inside a generic: substitutions don't affect it — the name
        // refers to a specific function, not a type parameter. Delegate to the
        // non-subst resolver.
        return resolve_type_expr(te, c, span)
    case Type_Const_Value:
        return Type_Const_Int{value = t.value}
    case Type_Const_Expr:
        if val, ok := const_eval_int(t.expr, c); ok {
            return Type_Const_Int{value = val}
        }
        return Type_Runtime_Size{expr = t.expr}
    }
    return Type_Error{}
}

// Instantiate a generic struct template with concrete type arguments.
// Returns a cached result if this instantiation was already created.
instantiate_generic_struct :: proc(c: ^Checker, tmpl: ^Generic_Template, type_args: []Type, span: Span) -> ^Type_Scope {
    // Build mangled name
    mangled := mangle_generic_name(tmpl.name, type_args)

    // Cache check
    if cached, ok := c.table.mono_cache[mangled]; ok {
        return cached
    }

    // Build substitution map: "T" -> i64, etc.
    subst: map[string]Type
    for param, i in tmpl.generic_params {
        subst[param.name] = type_args[i]
    }

    // Shape-constraint check: for each `name: ~Constraint` param, verify the
    // concrete type arg has every method the constraint declares (name match)
    // and fits in the constraint's declared byte size. Runs once per (template,
    // type-args) pair courtesy of mono_cache above.
    for param, i in tmpl.generic_params {
        if param.shape_constraint == "" { continue }
        check_shape_constraint(c, param, type_args[i], tmpl.home_package, span)
    }

    // Create concrete Type_Scope with C-ified name
    st := new(Type_Scope)
    st.name = make_flat_name(tmpl.home_package, mangled)
    st.home_package = tmpl.home_package
    st.kind = .Struct
    st.generic_base = tmpl.name
    for arg in type_args {
        append(&st.generic_args, arg)
    }

    tmpl_fields := tmpl.ast.fields if len(tmpl.ast.fields) > 0 else extract_fields_from_body(tmpl.ast.body)
    for field in tmpl_fields {
        ft := resolve_type_expr_with_subst(field.type_expr, c, span, &subst)
        // Substitute generic value params in default values: a field default
        // like `cap: i64 = n` references the const generic n; at instantiation
        // we replace that ident with the bound value (e.g. 256) so codegen
        // doesn't try to look up `n` as a runtime variable.
        dv := field.default_value
        if ident, ok := dv.(^Expr_Ident); ok {
            if sub, sub_ok := subst[ident.name]; sub_ok {
                if ci, ci_ok := sub.(Type_Const_Int); ci_ok {
                    new_num := new(Expr_Number)
                    new_num.int_value = i128(ci.value)
                    new_num.value = f64(ci.value)
                    new_num.span = ident.span
                    dv = new_num
                }
            }
        }
        append(&st.fields, Struct_Type_Field{
            name = field.name,
            type_ = ft,
            default_value = dv,
            is_using = field.is_using,
        })
    }

    // Cache and register
    build_field_map(&st.sd)
    c.table.mono_cache[mangled] = st
    c.table.funs[st.name] = st
    if c.top_env != nil {
        type_env_set(c.top_env, mangled, st)
    }

    return st
}

// Instantiate a generic union template with concrete type arguments. Mirrors
// instantiate_generic_struct but produces a Type_Union — builds variant structs
// with substituted field types, the tag enum, and registers everything into
// c.table.unions / c.table.structs / c.table.enums under mangled names.
instantiate_generic_union :: proc(c: ^Checker, tmpl: ^Generic_Union_Template, type_args: []Type, span: Span) -> ^Type_Union {
    mangled := mangle_generic_name(tmpl.name, type_args)

    // Cache check
    if cached, ok := c.table.mono_union_cache[mangled]; ok {
        return cached
    }

    // Substitution map
    subst: map[string]Type
    for param, i in tmpl.generic_params {
        subst[param.name] = type_args[i]
    }

    s := tmpl.ast

    ut := new(Type_Union)
    ut.name = make_flat_name(tmpl.home_package, mangled)
    ut.home_package = tmpl.home_package
    ut.tag_type = s.tag_type
    ut.min_size = s.min_size
    if s.tag_pad != nil {
        ut.tag_pad = resolve_type_expr_with_subst(s.tag_pad, c, span, &subst)
    }

    // Tag enum (Maybe__int_Tag, etc.). Variants registered into the global
    // variant_to_enum map so the dot-shorthand and bare-name lookups work.
    tag_enum_name := strings.concatenate({mangled, "_Tag"})
    tag_et := new(Type_Enum)
    tag_et.name = make_flat_name(tmpl.home_package, tag_enum_name)
    tag_et.home_package = tmpl.home_package
    tag_et.tag_type = s.tag_type
    for vdef in s.variants {
        tag_et.variants[vdef.name] = vdef.tag
    }
    c.table.enums[tag_et.name] = tag_et

    // Variant structs with substituted field types.
    for vdef in s.variants {
        struct_name := strings.concatenate({mangled, "_", vdef.name})
        vst := new(Type_Scope)
        vst.name = make_flat_name(tmpl.home_package, struct_name)
        vst.home_package = tmpl.home_package
        vst.kind = .Struct
        for field in vdef.fields {
            ft := resolve_type_expr_with_subst(field.type_expr, c, span, &subst)
            append(&vst.fields, Struct_Type_Field{
                name          = field.name,
                type_         = ft,
                default_value = field.default_value,
                is_using      = field.is_using,
            })
        }
        build_field_map(&vst.sd)
        c.table.structs[vst.name] = vst
        append(&ut.variants, vdef.name)
        ut.tag_map[vdef.name] = vdef.tag
        ut.variant_structs[vdef.name] = vst.name
    }

    c.table.unions[ut.name] = ut
    c.table.mono_union_cache[mangled] = ut
    if c.top_env != nil {
        type_env_set(c.top_env, mangled, ut)
    }

    return ut
}

// Infer generic type parameters by walking a type expression and actual type in parallel.
// Fills in the substitution map with discovered bindings.
infer_type_params :: proc(subst: ^map[string]Type, type_expr: Type_Expr, actual: Type, c: ^Checker) {
    switch t in type_expr {
    case Type_Name:
        // Check if this is a generic type param name (single uppercase letter or known param)
        // During generic function checking, param names like "T" appear as bare Type_Name
        if _, ok := subst[t.name]; !ok {
            // Only infer if this name is already a key in subst (even if nil)
            // The caller pre-populates subst with nil values for all generic param names
        }
        if t.name in subst^ && subst[t.name] == nil {
            subst[t.name] = actual
        }
    case ^Type_Pointer:
        if pt, ok := actual.(^Type_Ptr); ok {
            infer_type_params(subst, t.elem, pt.elem, c)
        }
    case ^Type_Array:
        if fa, ok := actual.(^Type_Fixed_Array); ok {
            infer_type_params(subst, t.elem, fa.elem, c)
        }
    case ^Type_Slice_Expr:
        if sl, ok := actual.(^Type_Slice); ok {
            infer_type_params(subst, t.elem, sl.elem, c)
        } else if fa, ok := actual.(^Type_Fixed_Array); ok {
            // Fixed arrays are compatible with slices for inference
            infer_type_params(subst, t.elem, fa.elem, c)
        }
    case ^Type_Partial_Array_Expr:
        if pa, ok := actual.(^Type_Partial_Array); ok {
            infer_type_params(subst, t.elem, pa.elem, c)
        }
    case ^Type_Generic_Instance:
        // e.g., Array(T) matched against Array__int__256 (a monomorphized struct)
        // Supports partial matching: Array($T) matches Array__int__256 even though
        // the type expression only mentions T, not the const param n.
        if sd := as_scope_body(actual); sd != nil {
            if sd.generic_base == t.name && len(t.type_args) <= len(sd.generic_args) {
                // Match provided type_args against generic_args
                for arg_expr, i in t.type_args {
                    infer_type_params(subst, arg_expr, sd.generic_args[i], c)
                }
                // Auto-capture unmentioned params (e.g., const params like n=256)
                // from the concrete struct's generic_args
                if c != nil {
                    if tmpl, tmpl_ok := c.table.generic_templates[t.name]; tmpl_ok {
                        for i := len(t.type_args); i < len(tmpl.generic_params); i += 1 {
                            if i < len(sd.generic_args) {
                                param_name := tmpl.generic_params[i].name
                                if param_name not_in subst^ || subst[param_name] == nil {
                                    subst[param_name] = sd.generic_args[i]
                                }
                            }
                        }
                    }
                }
            }
        }
    case Type_Const_Value:
        // Nothing to infer — this is a concrete value
        break
    case Type_Const_Expr:
        // Nothing to infer — this is a runtime expression
        break
    case ^Type_Func_Expr:
        if ft, ok := actual.(^Type_Scope); ok {
            for p, i in t.params {
                if i < len(ft.params) {
                    infer_type_params(subst, p, ft.params[i].type_, c)
                }
            }
            for rt, i in t.return_types {
                if i < len(ft.return_types) {
                    infer_type_params(subst, rt, ft.return_types[i], c)
                }
            }
        }
    case Type_Of_Name:
        // `fn name` is nominal — no type parameters to infer through it.
    }
}

// Instantiate a generic function template with concrete type substitutions.
// Creates a Checked_Scope stored in checked.functions with the mangled name.
instantiate_generic_fun :: proc(c: ^Checker, tmpl: ^Generic_Template, subst: ^map[string]Type, mangled: string, env: ^Type_Env) {
    ast := tmpl.ast

    // Build concrete function type
    fun_type := new(Type_Scope)
    fun_type.kind = .Fun
    fun_type.home_package = tmpl.home_package
    for tp in ast.typed_params {
        pt := resolve_type_expr_with_subst(tp.type_expr, c, ast.span, subst)
        append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
    }
    for rte in ast.return_types {
        append(&fun_type.return_types, resolve_type_expr_with_subst(rte, c, ast.span, subst))
    }
    build_param_map(fun_type)

    // Register in type env and cache for Phase 2.5 extraction.
    if c.top_env != nil {
        type_env_set(c.top_env, mangled, fun_type)
    } else {
        // During package checking, top_env may be nil — register in local env
        type_env_set(env, mangled, fun_type)
    }
    // Also register in the call-site env. The env chain terminates at the
    // enclosing module scope (is_module_scope), so a top_env-only registration
    // is invisible from inside a module-scoped function body. Belt-and-braces
    // registration here covers both reachability paths without disturbing
    // existing callers that walk to top_env directly.
    if env != c.top_env {
        type_env_set(env, mangled, fun_type)
    }
    c.table.mono_cache[mangled] = fun_type

    // Create child scope for body checking
    child := type_env_child(env)
    clear(&child.return_types)
    for rt in fun_type.return_types { append(&child.return_types, rt) }
    child.fn_name = ast.name

    // Bind regular params with their concrete types
    for tp, i in ast.typed_params {
        if i < len(fun_type.params) {
            type_env_set(&child, tp.name, fun_type.params[i].type_)
        }
    }

    // Bind generic type param names so they resolve in the body
    // (e.g., `x : T = ...` inside a generic function should know T is int)
    for name, t in subst {
        type_env_set(&child, name, t)
    }

    // Set active type params so resolve_type_expr can find them during body checking
    saved_type_params := c.type_params
    c.type_params = {}
    for name, t in subst {
        c.type_params[name] = t
    }

    // Clone the body so each monomorphization gets independent type annotations
    cloned_body := clone_stmts(ast.body)

    // Type-check the cloned function body
    check_scope(c, cloned_body, &child)

    // Store cloned body for codegen extraction
    c.table.mono_fun_bodies[mangled] = cloned_body

    // Restore type params
    c.type_params = saved_type_params
}

// Auto-monomorphize a concrete function when called with a structurally-compatible but
// differently-instantiated generic struct (e.g. add_string(^String(256)) called with ^String(64)).
// Returns the flat mangled name of the specialized function, or "" if no specialization needed.
auto_monomorphize_for_struct :: proc(c: ^Checker, fn_name: string, ft: ^Type_Scope, actual_types: []Type, env: ^Type_Env) -> string {
    // Check if any param needs specialization
    needs_spec := false
    for p, i in ft.params {
        if i >= len(actual_types) { break }
        pt, pt_ok := p.type_.(^Type_Ptr)
        if !pt_ok { continue }
        param_sd := as_scope_body(pt.elem)
        if param_sd == nil || param_sd.generic_base == "" { continue }
        at, at_ok := actual_types[i].(^Type_Ptr)
        if !at_ok { continue }
        actual_sd := as_scope_body(at.elem)
        if actual_sd == nil { continue }
        if param_sd.name != actual_sd.name && param_sd.generic_base == actual_sd.generic_base {
            needs_spec = true
            break
        }
    }
    if !needs_spec { return "" }

    // Build mangled name from function name + actual struct type args
    parts: [dynamic]string
    append(&parts, fn_name)
    for p, i in ft.params {
        if i >= len(actual_types) { break }
        pt, pt_ok := p.type_.(^Type_Ptr)
        if !pt_ok { continue }
        param_sd := as_scope_body(pt.elem)
        if param_sd == nil || param_sd.generic_base == "" { continue }
        at, at_ok := actual_types[i].(^Type_Ptr)
        if !at_ok { continue }
        actual_sd := as_scope_body(at.elem)
        if actual_sd == nil { continue }
        for arg in actual_sd.generic_args {
            append(&parts, type_name(arg))
        }
    }
    mangled := strings.join(parts[:], "__")

    // Cache check
    if mangled in c.table.mono_fun_cache {
        home := resolve_fn_home(c, env,fn_name)
        return make_flat_name(home, mangled)
    }

    // Look up the original function's AST
    home := resolve_fn_home(c, env,fn_name)
    ast, ast_ok := c.table.fun_asts[fn_name]
    if !ast_ok || ast == nil { return "" }

    // Build concrete function type with actual param types
    mono_ft := new(Type_Scope)
    mono_ft.kind = .Fun
    mono_ft.home_package = home
    for tp, i in ast.typed_params {
        if i < len(actual_types) {
            // Use actual type for params that need specialization
            pt, pt_ok := ft.params[i].type_.(^Type_Ptr)
            at, at_ok := actual_types[i].(^Type_Ptr)
            if pt_ok && at_ok {
                ps := as_scope_body(pt.elem)
                as_ := as_scope_body(at.elem)
                if ps != nil && as_ != nil && ps.generic_base != "" && ps.generic_base == as_.generic_base && ps.name != as_.name {
                    append(&mono_ft.params, Struct_Type_Field{name = ft.params[i].name, type_ = actual_types[i]})
                    continue
                }
            }
        }
        // Keep original type
        if i < len(ft.params) {
            append(&mono_ft.params, ft.params[i])
        }
    }
    for rt in ft.return_types { append(&mono_ft.return_types, rt) }
    build_param_map(mono_ft)

    // Register in type env
    if c.top_env != nil {
        type_env_set(c.top_env, mangled, mono_ft)
    } else {
        type_env_set(env, mangled, mono_ft)
    }
    c.table.mono_cache[mangled] = mono_ft
    c.table.mono_fun_cache[mangled] = fn_name

    // Clone body and type-check with new param types
    child := type_env_child(env)
    clear(&child.return_types)
    for rt in mono_ft.return_types { append(&child.return_types, rt) }
    child.fn_name = ast.name
    for tp, i in ast.typed_params {
        if i < len(mono_ft.params) {
            type_env_set(&child, tp.name, mono_ft.params[i].type_)
        }
    }
    cloned_body := clone_stmts(ast.body)
    check_scope(c, cloned_body, &child)
    c.table.mono_fun_bodies[mangled] = cloned_body

    return make_flat_name(home, mangled)
}

// Check a call to a generic function: infer type params, instantiate, rewrite call.
check_generic_call :: proc(c: ^Checker, e: ^Expr_Call, tmpl: ^Generic_Template, args: []Expr, env: ^Type_Env) -> Type {
    // Step 1: Check all argument types
    arg_types: [dynamic]Type
    defer delete(arg_types)
    for arg in args {
        append(&arg_types, check_expr(c, arg, env))
    }

    // Step 2: Build substitution map by inferring from arg types.
    // Pre-populate with nil for all generic param names so infer_type_params knows what to fill.
    subst: map[string]Type
    for param in tmpl.generic_params {
        subst[param.name] = nil
    }

    // Walk function param type expressions in parallel with actual arg types to infer
    for tp, i in tmpl.ast.typed_params {
        if i >= len(arg_types) { break }
        infer_type_params(&subst, tp.type_expr, arg_types[i], c)
    }

    // Struct-kind generic templates often have *every* typed_param promoted to
    // a generic_param by the parser (Array's `item: $T, n: i64 = 256` → both
    // become generic_params, typed_params empty). In that shape the call's
    // args are positional generic bindings — `Array(Player, 64)` means
    // item=Player, n=64. Route directly through instantiate_generic_struct,
    // the same path resolve_type_expr_with_subst uses for type-position
    // `Array(byte, 256)`. That path does the const-ident-to-literal field
    // default substitution that the value-position fun-instantiation path
    // doesn't, so the body of Array (`cap : i64 = n`) checks correctly.
    if tmpl.ast != nil && tmpl.ast.kind == .Struct && len(tmpl.ast.typed_params) == 0 && len(tmpl.generic_params) > 0 {
        type_args: [dynamic]Type
        for param, i in tmpl.generic_params {
            if i < len(args) {
                if param.is_const {
                    if v, ok := const_eval_int(args[i], c); ok {
                        append(&type_args, Type_Const_Int{value = v})
                    } else {
                        check_error(c, e.span, TYPE_ARGUMENT_CONST_GENERIC_PARAMETER_REQUIRES, i, tmpl.name, param.name)
                        return Type_Error{}
                    }
                } else {
                    append(&type_args, arg_types[i])
                }
            } else if param.is_const && param.has_default {
                append(&type_args, Type_Const_Int{value = param.default_value})
            } else {
                check_error(c, e.span, TYPE_REQUIRES_GENERIC_PARAMETER_DEFAULT, tmpl.name, param.name)
                return Type_Error{}
            }
        }
        st := instantiate_generic_struct(c, tmpl, type_args[:], e.span)
        // Args were consumed as generic bindings, not field initializers.
        // Clear them and rewrite the call as a parameterless Foo() on the
        // instantiated struct's flat name — same shape Point() takes.
        e.args = {}
        e.name = st.name
        e.resolved_func = Resolved_Func{name = st.name}

        // Codegen needs an init function for the instantiated struct so the
        // call site has something to call. Type-position uses (e.g. `var
        // Array(byte, 256)`) inline default-init at the alloca and never
        // need this; expression-position calls do. Source-defined structs
        // get a Checked_Scope from extract_module_into_checked; instantiated
        // generics need one synthesised here. Codegen's is_pure_struct_init
        // path emits the body (apply field defaults, ret void).
        if c.checked != nil {
            if _, exists := c.checked.functions[st.name]; !exists {
                cs := Checked_Scope{
                    name         = st.name,
                    home_package = tmpl.home_package,
                    type_        = st,
                    body         = tmpl.ast.body,
                    ast          = tmpl.ast,
                    origin       = Origin_Source{},
                    span         = e.span,
                }
                append(&cs.return_types, Type(st))
                c.checked.functions[st.name] = cs
                append(&c.checked.function_order, st.name)
            }
        }

        return check_pure_struct_construction(c, e, st, env)
    }

    // Also try to infer from the return type context if needed (future enhancement)

    // Step 3: Verify all type params were resolved
    for param in tmpl.generic_params {
        if subst[param.name] == nil {
            check_error(c, e.span, TYPE_COULD_INFER_TYPE_PARAMETER_CALL, param.name, e.name)
            return Type_Error{}
        }
    }

    // Step 4: Build mangled name — include both declared params and auto-captured const params
    type_args: [dynamic]Type
    defer delete(type_args)
    for param in tmpl.generic_params {
        append(&type_args, subst[param.name])
    }
    // Add auto-captured params (e.g., const params from struct types like n=256)
    // Sort by name for deterministic mangling
    extra_names: [dynamic]string
    defer delete(extra_names)
    for name, t in subst {
        already := false
        for param in tmpl.generic_params {
            if param.name == name { already = true; break }
        }
        if !already && t != nil {
            append(&extra_names, name)
        }
    }
    // Simple insertion sort for determinism
    for i := 1; i < len(extra_names); i += 1 {
        for j := i; j > 0 && extra_names[j] < extra_names[j-1]; j -= 1 {
            extra_names[j], extra_names[j-1] = extra_names[j-1], extra_names[j]
        }
    }
    for name in extra_names {
        append(&type_args, subst[name])
    }
    mangled := mangle_generic_name(tmpl.name, type_args[:])

    // Step 5: Instantiate if not already cached
    if mangled not_in c.table.mono_fun_cache {
        instantiate_generic_fun(c, tmpl, &subst, mangled, env)
        c.table.mono_fun_cache[mangled] = tmpl.name
    }

    // Step 6: Resolve the concrete function type
    fun_type_raw, ok := type_env_get(env, mangled)
    if !ok {
        check_error(c, e.span, TYPE_FAILED_INSTANTIATE_GENERIC_FUNCTION, e.name)
        return Type_Error{}
    }
    fun_type, fun_ok := fun_type_raw.(^Type_Scope)
    if !fun_ok {
        check_error(c, e.span, TYPE_FAILED_INSTANTIATE_GENERIC_FUNCTION, e.name)
        return Type_Error{}
    }
    // Generic constructor call: e.g. Pair(int)(1, 2)
    if len(fun_type.fields) > 0 && len(fun_type.params) == 0 {
        return check_pure_struct_construction(c, e, fun_type, env)
    }

    // Step 7: Rewrite the call to target the mangled name
    e.name = mangled
    fn_flat_name := make_flat_name(tmpl.home_package, mangled)
    e.resolved_func = Resolved_Func{name = fn_flat_name}

    // Step 8: Validate arg count matches concrete param count
    if len(args) != len(fun_type.params) {
        check_error(c, e.span, TYPE_EXPECTS_ARGUMENT, tmpl.name, len(fun_type.params), len(args))
    }

    return fn_primary_return(fun_type)
}

// ---------------------------------------------------------------------------
// Type comparison
// ---------------------------------------------------------------------------

// Flat name of the one and only cstring type — the stdlib's
// `mara.string.cstring :: distinct ^utf8`. Name-matched here rather
// than recognized structurally; a structural rule ("any nominal
// distinct ^utf8") would also accept unrelated user types that happen
// to wrap ^utf8 and silently grant them utf8 sentinel coercion, which
// is exactly the kind of accidental coupling we don't want.
CSTRING_FLAT_NAME :: "mara_string_cstring"

// Recognize the cstring type — either the legacy built-in (Type_CString,
// no longer produced from source after the keyword removal but retained
// for transitional safety) or the stdlib's named distinct decl. The
// conversion rule (utf8 sentinel storage → cstring via data-pointer
// extraction) lives in the matching `case` arms below; pointed at from
// a comment near the stdlib decl.
is_cstring :: proc(t: Type) -> bool {
    if _, ok := t.(Type_CString); ok { return true }
    if dt, ok := t.(^Type_Distinct); ok && !dt.is_alias {
        return dt.name == CSTRING_FLAT_NAME
    }
    return false
}

// True for the open `err` type and for any concrete `error { ... }` decl.
// Used at the `?` propagation boundary: both the inner call's trailing
// return slot and the enclosing function's trailing return slot must be
// err-compatible for the propagation to type-check.
is_err_type :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Err); ok { return true }
    if et, ok := distinct_base(t).(^Type_Enum); ok { return et.is_error_kind }
    return false
}

types_equal :: proc(a: Type, b: Type) -> bool {
    // nil return type (void) — only matches itself
    if a == nil && b == nil { return true }
    if a == nil || b == nil { return false }

    // Error type matches everything (suppress cascading errors)
    if _, ok := a.(Type_Error); ok { return true }
    if _, ok := b.(Type_Error); ok { return true }

    // Open `err` type accepts any error_kind variant. Symmetric: a value of
    // a specific error_kind flows into an `err`-typed slot, and `err`-typed
    // values compare against specific error_kind variants. Both directions
    // route through the same u32 IR shape, so codegen treats this as a
    // no-op coercion.
    if _, ok := a.(Type_Err); ok {
        if _, ok2 := b.(Type_Err); ok2 { return true }
        if et, ok2 := b.(^Type_Enum); ok2 { return et.is_error_kind }
    }
    if _, ok := b.(Type_Err); ok {
        if et, ok2 := a.(^Type_Enum); ok2 { return et.is_error_kind }
    }

    // Transparent type aliases (`Name :: type(T)`) unwrap to their base
    // before any other comparison. They have no nominal identity — they
    // exist purely as renames. `distinct` types do not unwrap here.
    a := unwrap_alias(resolve_infer(a))
    b := unwrap_alias(resolve_infer(b))

    switch va in a {
    case Type_Infer_Int:
        // Infer int is compatible with any numeric type
        return is_numeric(b)
    case Type_Infer_Float:
        // Infer float is compatible with float types and other infer types
        if _, ok := b.(Type_F64); ok { return true }
        if _, ok := b.(Type_Infer_Float); ok { return true }
        if _, ok := b.(Type_Infer_Int); ok { return true }
        if nb, ok := b.(Type_Numeric); ok { return nb.kind == .Float }
        return false
    case Type_Numeric:
        // Same numeric type (exact match on kind and bits)
        if vb, ok := b.(Type_Numeric); ok {
            return va.kind == vb.kind && va.bits == vb.bits
        }
        // Infer int compatible with all numeric kinds
        if _, ok := b.(Type_Infer_Int); ok { return true }
        // Infer float compatible with float numeric types only
        if _, ok := b.(Type_Infer_Float); ok { return va.kind == .Float }
        // c8 is compatible with i8/u8
        if _, ok := b.(Type_C8); ok {
            return (va.kind == .Unsigned || va.kind == .Signed) && va.bits == 8
        }
        // utf8 is compatible with i8/u8
        if _, ok := b.(Type_Utf8); ok {
            return (va.kind == .Unsigned || va.kind == .Signed) && va.bits == 8
        }
        // Symmetric with the Type_Enum case below: enums coerce to integer types.
        if _, ok := b.(^Type_Enum); ok {
            return va.kind == .Signed || va.kind == .Unsigned
        }
        return false
    case Type_F64:
        if _, ok := b.(Type_Infer_Int); ok { return true }
        if _, ok := b.(Type_Infer_Float); ok { return true }
        _, ok := b.(Type_F64)
        return ok
    case Type_Bool:
        _, ok := b.(Type_Bool)
        return ok
    case Type_CString:
        // Legacy built-in path (kept while Type_CString might still appear
        // in some legacy site); the equivalent rule for the stdlib
        // distinct `cstring` lives at the top of types_equal below.
        if is_cstring(b) { return true }
        if fa, ok := b.(^Type_Fixed_Array); ok {
            if _, utf8_ok := fa.elem.(Type_Utf8); utf8_ok && fa.has_sentinel { return true }
        }
        if pa, ok := b.(^Type_Partial_Array); ok {
            if _, utf8_ok := pa.elem.(Type_Utf8); utf8_ok && pa.has_sentinel { return true }
        }
        if sl, ok := b.(^Type_Slice); ok {
            if _, utf8_ok := sl.elem.(Type_Utf8); utf8_ok && sl.has_sentinel { return true }
        }
        return false
    case Type_C8:
        if _, ok := b.(Type_C8); ok { return true }
        if _, ok := b.(Type_Infer_Int); ok { return true }
        // c8 is compatible with u8 (same underlying size)
        if nb, ok := b.(Type_Numeric); ok {
            return (nb.kind == .Unsigned || nb.kind == .Signed) && nb.bits == 8
        }
        return false
    case Type_Utf8:
        if _, ok := b.(Type_Utf8); ok { return true }
        if _, ok := b.(Type_Infer_Int); ok { return true }
        if nb, ok := b.(Type_Numeric); ok {
            return (nb.kind == .Unsigned || nb.kind == .Signed) && nb.bits == 8
        }
        return false
    case Type_Byte:
        _, ok := b.(Type_Byte)
        return ok
    case ^Type_Ptr:
        vb, ok := b.(^Type_Ptr)
        if !ok { return false }
        // Opaque pointers (elem=Type_Any) are compatible with all pointer types
        if _, oa := va.elem.(Type_Any); oa { return true }
        if _, ob := vb.elem.(Type_Any); ob { return true }
        // ^byte accepts any pointer (all memory is bytes)
        if _, ba := va.elem.(Type_Byte); ba { return true }
        if _, bb := vb.elem.(Type_Byte); bb { return true }
        return types_equal(va.elem, vb.elem)
    case ^Type_Scope:
        vb, ok := b.(^Type_Scope)
        if !ok { return false }
        // Nominal: if both have names, compare by name
        if va.name != "" && vb.name != "" {
            if va.name == vb.name { return true }
            return false
        }
        // Structural: compare params + return types (for anonymous/callable funs)
        if len(va.params) != len(vb.params) { return false }
        for p, i in va.params {
            if !types_equal(p.type_, vb.params[i].type_) { return false }
        }
        if len(va.return_types) != len(vb.return_types) { return false }
        for rt, i in va.return_types {
            if !types_equal(rt, vb.return_types[i]) { return false }
        }
        return true
    case ^Type_Fixed_Array:
        // A slice (`[]T`) is NOT accepted as a fixed-array source: a fixed
        // array is a value (N inline elements) and a slice is a reference
        // ({ptr,len,cap}). Converting one to the other is a copy with a
        // runtime-length question, so it must be explicit — never an implicit
        // coercion. (This arm used to accept []T; codegen then silently
        // dropped the copy on the return path and zeroed the result.)
        // Implicit coercion: [N]T is compatible with [..M]T (partial array
        // view). Lets fixed-array decls take partial-array sources — most
        // importantly `fa : [N, 0]utf8 = "lit"` after the literal-type
        // change made literals partial. Sentinel direction matches the
        // partial-to-partial rule.
        if pa, pa_ok := b.(^Type_Partial_Array); pa_ok {
            if !buffer_elem_compatible(va.elem, pa.elem) { return false }
            if va.has_sentinel && !pa.has_sentinel { return false }
            return true
        }
        vb, ok := b.(^Type_Fixed_Array)
        if !ok { return false }
        return buffer_elem_compatible(va.elem, vb.elem)
        // Note: we don't compare size here — arrays of same elem type are compatible
        // Size checking is done at assignment/init time
    case ^Type_Slice:
        // Implicit coercion: [:]T is compatible with [N]T (slice ← array).
        // A fixed array is fully-populated by contract — `[N]T` means N
        // elements, period. So a slice header {len = N, cap = N} reading
        // off it is honest by the type's own promise. Callers who want
        // variable-length tracking use partial arrays (`[..N]T`).
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return buffer_elem_compatible(va.elem, fa.elem)
        }
        // Implicit coercion: [:]T is compatible with [..N]T (slice ← partial array view).
        // Sentinel direction matches partial-to-partial: source can drop a
        // sentinel guarantee, but can't synthesize one — reject when dest
        // expects a sentinel the source doesn't have.
        if pa, pa_ok := b.(^Type_Partial_Array); pa_ok {
            if !buffer_elem_compatible(va.elem, pa.elem) { return false }
            if va.has_sentinel && !pa.has_sentinel { return false }
            return true
        }
        vb, ok := b.(^Type_Slice)
        if !ok { return false }
        return buffer_elem_compatible(va.elem, vb.elem)
    case ^Type_Partial_Array:
        // Partial arrays coerce to [:]T (slice view) and to [N]T (fixed array)
        // by element type. The first 24 bytes of a partial array's layout
        // match a slice header, so `^[..N]T` flows safely into `^[:]T` param
        // slots — cursor mutations propagate back through the aliased memory.
        if sl, sl_ok := b.(^Type_Slice); sl_ok {
            if !buffer_elem_compatible(va.elem, sl.elem) { return false }
            if va.has_sentinel && !sl.has_sentinel { return false }
            return true
        }
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            if !buffer_elem_compatible(va.elem, fa.elem) { return false }
            // Sentinel direction matches the mirror rule (fixed ← partial)
            // above: if the dest demands a terminator the source can't
            // promise, reject. Without this, `cstr` (`[..N, 0]utf8`) would
            // silently accept any `[N]utf8` and downstream C consumers
            // walking until `\0` could run off the end.
            if va.has_sentinel && !fa.has_sentinel { return false }
            return true
        }
        if pa, ok := b.(^Type_Partial_Array); ok {
            // Partial-to-partial interop is by header shape: same elem
            // type and a permissible sentinel direction. In a types_equal
            // call from assignment / parameter passing, `va` is the
            // destination's expected type and `pa` is the source's
            // actual type. Allow source-sentinel-drop (source has the
            // terminator, dest doesn't care) — safe, the dest just
            // ignores the trailing-slot guarantee. Reject the reverse:
            // dest expects a sentinel the source can't synthesize.
            // Size doesn't gate compatibility because params are passed
            // by header pointer (cap is read at runtime); assignment
            // paths in codegen are responsible for fitting source bytes
            // into dest storage.
            if !buffer_elem_compatible(va.elem, pa.elem) { return false }
            if va.has_sentinel && !pa.has_sentinel { return false }
            return true
        }
        return false
    case ^Type_Enum:
        // Enums are compatible with infer_int, numeric integer types, and the same enum
        if _, ok := b.(Type_Infer_Int); ok { return true }
        if nb, ok := b.(Type_Numeric); ok {
            return nb.kind == .Signed || nb.kind == .Unsigned
        }
        if vb, ok := b.(^Type_Enum); ok { return va.name == vb.name }
        return false
    case ^Type_Union:
        vb, ok := b.(^Type_Union)
        if !ok { return false }
        return va.name == vb.name  // nominal typing
    case ^Type_Distinct:
        // After unwrap_alias at types_equal's entry, only nominal distinct
        // types reach this case. Match strictly by name.
        if vb, ok := b.(^Type_Distinct); ok {
            return va.name == vb.name
        }
        // Stdlib `cstring :: distinct ^utf8` is the FFI boundary type; it
        // accepts utf8 storage with a sentinel via data-pointer extraction
        // in codegen. Same rule as the legacy Type_CString case above.
        // Comment near the decl in code/string.mara points here.
        if is_cstring(va) {
            if _, ok := b.(Type_CString); ok { return true }
            if fa, ok := b.(^Type_Fixed_Array); ok {
                if _, utf8_ok := fa.elem.(Type_Utf8); utf8_ok && fa.has_sentinel { return true }
            }
            if pa, ok := b.(^Type_Partial_Array); ok {
                if _, utf8_ok := pa.elem.(Type_Utf8); utf8_ok && pa.has_sentinel { return true }
            }
            if sl, ok := b.(^Type_Slice); ok {
                if _, utf8_ok := sl.elem.(Type_Utf8); utf8_ok && sl.has_sentinel { return true }
            }
        }
        return false
    case Type_Const_Int:
        // Const int values are equal when they have the same value
        if vb, ok := b.(Type_Const_Int); ok { return va.value == vb.value }
        return false
    case Type_Runtime_Size:
        // All runtime sizes are considered the same type (mangled as "vla")
        if _, ok := b.(Type_Runtime_Size); ok { return true }
        return false
    case Type_Any:
        // Type_Any no longer acts as a wildcard — only used as opaque ptr element.
        // Matching Type_Any with Type_Any is OK (e.g. two opaque ptrs).
        if _, ok := b.(Type_Any); ok { return true }
        return false
    case Type_Void:
        // Void matches itself only.
        _, ok := b.(Type_Void)
        return ok
    case Type_Error:
        return true
    case Type_Err:
        // Symmetric handling lives at the top of types_equal so we can short-
        // circuit before alias unwrapping; reaching this arm means neither
        // side matched there — be conservative and report inequality.
        return false
    }
    return false
}

// Unwrap a Type_Distinct to its base type (recursively).
// For non-distinct types, returns the input unchanged.
distinct_base :: proc(t: Type) -> Type {
    dt, ok := t.(^Type_Distinct)
    if !ok { return t }
    return distinct_base(dt.base_type)
}

// True when `t` transitively contains a `Type_Partial_Array` somewhere in
// its layout. Used to reject struct-copy assignments that would silently
// break the inner partial array's self-referential ptr field. The top-level
// partial-array case is NOT flagged here — direct partial-to-partial copy
// has a dedicated codegen helper (`partial_array_copy`) that re-anchors ptr.
type_contains_partial_array :: proc(t: Type) -> bool {
    if t == nil { return false }
    #partial switch v in t {
    case ^Type_Partial_Array:
        return true
    case ^Type_Distinct:
        return type_contains_partial_array(v.base_type)
    case ^Type_Scope:
        if v.kind == .Struct {
            for &f in v.fields {
                if type_contains_partial_array(f.type_) { return true }
            }
        }
    case ^Type_Fixed_Array:
        return type_contains_partial_array(v.elem)
    }
    return false
}

// True when `t` is a struct (or distinct-of-struct) that holds a partial
// array somewhere inside. A top-level `Type_Partial_Array` returns false —
// only wrapped occurrences matter, since the direct case has its own copy
// path.
struct_contains_partial_array :: proc(t: Type) -> bool {
    base := distinct_base(t)
    if _, is_pa := base.(^Type_Partial_Array); is_pa { return false }
    sd := as_scope_body(base)
    if sd == nil { return false }
    for &f in sd.fields {
        if type_contains_partial_array(f.type_) { return true }
    }
    return false
}

// Unwrap transparent type aliases (`Name :: type(T)`) — recursively — to
// reveal the underlying type. Distinct types (with is_alias=false) are
// preserved so their nominal identity is kept intact for type-equality
// checks; aliases dissolve.
unwrap_alias :: proc(t: Type) -> Type {
    dt, ok := t.(^Type_Distinct)
    if !ok { return t }
    if !dt.is_alias { return t }
    return unwrap_alias(dt.base_type)
}

type_name :: proc(t: Type) -> string {
    t := resolve_infer(t)
    switch v in t {
    case Type_F64:          return "f64"
    case Type_Infer_Int:    return "infer_int"
    case Type_Infer_Float:  return "infer_float"
    case Type_Numeric:
        switch v.kind {
        case .Signed:
            if v.bits == 0 { return "isize" }
            return fmt.tprintf("i%d", v.bits)
        case .Unsigned:
            if v.bits == 0 { return "usize" }
            return fmt.tprintf("u%d", v.bits)
        case .Float:    return fmt.tprintf("f%d", v.bits)
        }
    case Type_Bool:         return "bool"
    case Type_CString:      return "cstring"
    case Type_C8:           return "c8"
    case Type_Utf8:         return "utf8"
    case Type_Byte:         return "byte"
    case ^Type_Ptr:         return fmt.tprintf("^%s", type_name(v.elem))
    case ^Type_Scope:
        if v.name != "" {
            return v.name
        }
        b := strings.builder_make()
        strings.write_string(&b, "fun(")
        for p, i in v.params {
            if i > 0 { strings.write_string(&b, ", ") }
            strings.write_string(&b, type_name(p.type_))
        }
        strings.write_string(&b, ")")
        switch len(v.return_types) {
        case 0:
            // void: omit
        case 1:
            strings.write_string(&b, " -> ")
            strings.write_string(&b, type_name(v.return_types[0]))
        case:
            // Multi-return: `fun(...) -> T, U` — parens are cosmetic at the
            // source level so we leave them out here.
            strings.write_string(&b, " -> ")
            for rt, i in v.return_types {
                if i > 0 { strings.write_string(&b, ", ") }
                strings.write_string(&b, type_name(rt))
            }
        }
        return strings.to_string(b)
    case ^Type_Fixed_Array:
        if v.has_sentinel {
            return fmt.tprintf("[%d, %d]%s", v.size, v.sentinel, type_name(v.elem))
        }
        return fmt.tprintf("[%d]%s", v.size, type_name(v.elem))
    case ^Type_Slice:
        if v.has_sentinel {
            return fmt.tprintf("[, %d]%s", v.sentinel, type_name(v.elem))
        }
        return fmt.tprintf("[]%s", type_name(v.elem))
    case ^Type_Partial_Array:
        if v.has_sentinel {
            return fmt.tprintf("[..%d, %d]%s", v.size, v.sentinel, type_name(v.elem))
        }
        return fmt.tprintf("[..%d]%s", v.size, type_name(v.elem))
    case ^Type_Enum:        return v.name
    case ^Type_Union:       return v.name
    case ^Type_Distinct:
        if v.is_alias { return v.name }
        return fmt.tprintf("distinct %s", v.name)
    case Type_Const_Int:    return fmt.tprintf("const_%d", v.value)
    case Type_Runtime_Size: return "vla"
    case Type_Any:          return "any"
    case Type_Void:         return "void"
    case Type_Error:        return "<error>"
    case Type_Err:          return "err"
    }
    return "void"
}

// Is this a numeric type?
is_numeric :: proc(t: Type) -> bool {
    if _, ok := t.(Type_F64); ok { return true }
    if _, ok := t.(Type_Infer_Int); ok { return true }
    if _, ok := t.(Type_Infer_Float); ok { return true }
    if _, ok := t.(Type_Numeric); ok { return true }
    if _, ok := t.(^Type_Enum); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
    return false
}

// True for the 8-bit "memory view" scalar types — byte, utf8, c8, u8/i8.
// All four occupy one byte with the same memory layout; they differ only in
// what operations the type system permits on the scalar.
is_byte_sized_memory_type :: proc(t: Type) -> bool {
    base := distinct_base(t)
    if _, ok := base.(Type_Byte); ok { return true }
    if _, ok := base.(Type_Utf8); ok { return true }
    if _, ok := base.(Type_C8); ok { return true }
    if n, ok := base.(Type_Numeric); ok {
        return (n.kind == .Signed || n.kind == .Unsigned) && n.bits == 8
    }
    return false
}

// Element compatibility for buffer types (slice / fixed-array / partial-array).
// Looser than scalar types_equal: any two 8-bit memory-view types are mutually
// compatible at the buffer element level, so `[]u8 → []byte`, `[8]u8 → []byte`,
// `[]byte → []utf8` etc. all flow without explicit casts. The arithmetic
// restriction on byte still holds at the scalar binop level (is_numeric
// excludes Type_Byte), so this doesn't enable `byte + byte` — it only enables
// reinterpreting a buffer's element view, which is the natural shape for
// raw-memory work like file parsing.
buffer_elem_compatible :: proc(a, b: Type) -> bool {
    if types_equal(a, b) { return true }
    return is_byte_sized_memory_type(a) && is_byte_sized_memory_type(b)
}

is_integer :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Infer_Int); ok { return true }
    if n, ok := t.(Type_Numeric); ok { return n.kind != .Float }
    if _, ok := t.(^Type_Enum); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
    return false
}

// Slice header width — kept in sync with codegen's slice_layout.len_ir.
// Currently i32; flip both sides together when widening to i64.
slice_header_width_type :: Type_Numeric{kind = .Signed, bits = 64}

// Does `t` coerce to slice-header width without an implicit cast at the
// codegen boundary? Used by indexing / slice-bound / take-count / slice_from_ptr
// — every site where the codegen used to silently sext/trunc.
// Width, kind, and "is it numeric" for a scalar numeric type. Peels distinct
// for the width/kind read, but value_preserving_widen guards distinctness
// separately so a `distinct i32` stays nominal.
numeric_info :: proc(t: Type) -> (bits: int, kind: Numeric_Kind, ok: bool) {
    #partial switch v in distinct_base(resolve_infer(t)) {
    case Type_Numeric:                   return v.bits, v.kind, true
    case Type_Byte, Type_C8, Type_Utf8:  return 8, .Unsigned, true
    case Type_F64:                       return 64, .Float, true
    }
    return 0, .Signed, false
}

// True when a value of type `from` converts to `to` with NO loss — the rule
// for implicit widening (everything else stays an explicit cast). Same-kind
// only: int→int and float→float. int↔float is always explicit (its lossless
// cases are a precision table, not a rule). The integer test is value-
// preserving, which is about representable range, not just bit width:
//   signed → wider signed         (sign-extend)
//   unsigned → wider-or-eq... no: wider unsigned (zero-extend)
//   unsigned → STRICTLY wider signed (every unsigned value fits)
//   signed → unsigned             : never (negatives have no representation)
//   same width across signedness  : never (e.g. u32→i32 overflows)
value_preserving_widen :: proc(from: Type, to: Type) -> bool {
    // Distinct numerics are nominal — don't silently widen across the boundary.
    if _, ok := from.(^Type_Distinct); ok { return false }
    if _, ok := to.(^Type_Distinct);   ok { return false }
    fb, fk, fok := numeric_info(from)
    tb, tk, tok := numeric_info(to)
    if !fok || !tok { return false }
    if fk == .Float || tk == .Float {
        return fk == .Float && tk == .Float && tb > fb   // f32 → f64 (and f16 → f32)
    }
    if fk == .Signed   && tk == .Signed   { return tb > fb }
    if fk == .Unsigned && tk == .Unsigned { return tb > fb }
    if fk == .Unsigned && tk == .Signed   { return tb > fb }  // strictly wider holds all
    return false  // signed → unsigned: never
}

// The smallest numeric type that represents EVERY value of both a and b — the
// common type for value-preserving operand mixing in binary ops. (nil,false)
// when none exists, so the op stays an explicit cast. Same-kind → the wider;
// cross-sign → a SIGNED type wide enough for the unsigned operand's range and
// the signed operand (u32 vs i32 → i64; i64 vs u64 → none); int↔float → none.
// Two-sided analogue of value_preserving_widen, and the rule that keeps mixed
// arithmetic out of C's "unsigned wins" swamp: -1 stays -1, 4e9 stays 4e9.
common_numeric_type :: proc(a: Type, b: Type) -> (Type, bool) {
    if _, ok := a.(^Type_Distinct); ok { return nil, false }
    if _, ok := b.(^Type_Distinct); ok { return nil, false }
    ab, ak, aok := numeric_info(a)
    bb, bk, bok := numeric_info(b)
    if !aok || !bok { return nil, false }
    if ak == .Float || bk == .Float {
        if ak == .Float && bk == .Float { return ab >= bb ? a : b, true }
        return nil, false  // int <-> float stays explicit
    }
    if ak == bk { return ab >= bb ? a : b, true }  // same signedness → wider
    // cross-sign: signed type strictly wider than the unsigned operand AND at
    // least as wide as the signed operand.
    ubits := ak == .Unsigned ? ab : bb
    sbits := ak == .Signed   ? ab : bb
    need := ubits + 1
    if need < sbits { need = sbits }
    w := 0
    if need <= 8 {
        w = 8
    } else if need <= 16 {
        w = 16
    } else if need <= 32 {
        w = 32
    } else if need <= 64 {
        w = 64
    } else {
        return nil, false  // u64 vs a signed type: no value-preserving common
    }
    return Type_Numeric{kind = .Signed, bits = w}, true
}

// A subscript index may be ANY integer: the runtime bounds check makes a
// too-wide value safe (codegen bounds-checks at the index's width, before any
// narrowing, so an out-of-range value traps rather than wrapping). This is
// looser than coerces_to_slice_width, which still gates counts / sizes /
// capacities — those have no bounds check to lean on, so a silent narrow there
// could under-allocate. Floats are excluded (callers check is_numeric first,
// then this rejects the non-integer). infer/any/error pass for flexibility.
coerces_to_index_width :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_Infer_Int, Type_Any, Type_Error: return true
    case Type_Numeric:                         return true
    case Type_Byte, Type_C8, Type_Utf8:        return true
    case ^Type_Enum, ^Type_Union:              return true  // index by integer tag
    }
    return false
}

coerces_to_slice_width :: proc(t: Type) -> bool {
    #partial switch v in t {
    case Type_Infer_Int: return true   // comptime literal
    case Type_Any:       return true   // error recovery
    case Type_Error:     return true   // error suppression
    case ^Type_Enum:
        // Enums lower to their tag width — accept if tag IR matches.
        return tag_type_matches_slice_width(v.tag_type)
    case ^Type_Union:
        // Tagged unions used as indices (e.g. SDL's `union(tag u32) Scancode`)
        // — accept if the tag IR matches.
        return tag_type_matches_slice_width(v.tag_type)
    case ^Type_Distinct:
        return coerces_to_slice_width(v.base_type)
    }
    // Numeric scalars (incl. `int`, byte/char): the exact header width, or any
    // integer that value-preservingly WIDENS into it (codegen sext/zext at the
    // boundary). With an i64 header that's every signed <=64 / unsigned <64, so a
    // plain `n := 0` (i64) or a legacy i32 both flow into a count / bound / size
    // losslessly. Genuine narrowing (i64->i32 header, or u64) stays an explicit
    // cast. Brings counts/bounds in line with coerces_to_index_width — lossless only.
    bits, kind, ok := numeric_info(t)
    if !ok { return false }   // floats / non-numerics rejected
    if kind == slice_header_width_type.kind && bits == slice_header_width_type.bits {
        return true
    }
    return value_preserving_widen(t, slice_header_width_type)
}

// `tag_type` strings on Type_Enum/Type_Union are "" (default, currently i64),
// "i8"/"i16"/"i32"/"i64", or "u8"/.../u64. Width comparison only — sign
// doesn't matter at the GEP-index level.
tag_type_matches_slice_width :: proc(tag: string) -> bool {
    // Default tag is i64, and the slice header is also i64, so a default-tag
    // enum/union coerces to a slice index; a narrower tag (e.g. i32) does not.
    expected_bits := slice_header_width_type.bits
    switch tag {
    case "":               return expected_bits == 64
    case "i8",  "u8":      return expected_bits == 8
    case "i16", "u16":     return expected_bits == 16
    case "i32", "u32":     return expected_bits == 32
    case "i64", "u64":     return expected_bits == 64
    }
    return false
}

// Check if the checker is currently processing a given package. Accepts the
// bare name (e.g. "os") and matches when current_package is either the bare
// name (user packages) or its dotted stdlib form ("mara.os").
is_package :: proc(c: ^Checker, name: string) -> bool {
    return c.current_package == name ||
           c.current_package == strings.concatenate({"mara.", name})
}

is_comparison_op :: proc(op: Token_Kind) -> bool {
    #partial switch op {
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
        return true
    }
    return false
}

is_any :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Any); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
    // Opaque pointers (ptr) pass all type checks (compatible with everything).
    // Also handle ^<error> recursively so a poisoned root type silences
    // cascading errors from operations on the resulting pointer (field
    // access, indexing, etc.) — the user has the original error and doesn't
    // need a chain of dependent ones.
    if pt, pt_ok := t.(^Type_Ptr); pt_ok {
        return is_any(pt.elem)
    }
    return false
}

is_error_type :: proc(t: Type) -> bool {
    _, ok := t.(Type_Error)
    return ok
}

is_array_type :: proc(t: Type) -> bool {
    if _, ok := t.(^Type_Fixed_Array); ok { return true }
    if _, ok := t.(^Type_Slice); ok { return true }
    return false
}

// True for composite types that cannot be compared with == or !=.
is_composite :: proc(t: Type) -> bool {
    if sd := as_scope_body(t); sd != nil && len(sd.fields) > 0 { return true }
    if _, ok := t.(^Type_Union); ok { return true }
    if _, ok := t.(^Type_Fixed_Array); ok { return true }
    return false
}

// Strict check: true only for error-recovery or genuinely untyped variables.
// Unlike is_any, this returns false for opaque pointers (^Type_Ptr{elem=Type_Any{}}).
// Used by codegen to decide whether to trust type info.
is_untyped :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Any); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
    return false
}

// True for inferred-type constants (literals that adopt type from context)
is_infer :: proc(t: Type) -> bool {
    rt := resolve_infer(t)
    if _, ok := rt.(Type_Infer_Int); ok { return true }
    if _, ok := rt.(Type_Infer_Float); ok { return true }
    return false
}

// True when a type is a byte slice ([]byte). Auto-derefs one level of ^Ptr
// (so `^[]byte` is recognized — codegen already binds it as a Slice_Var via
// slice_through_distinct_and_ptr) and unwraps distinct/alias wrappers so
// user-named byte containers (`Block :: type [16]byte`, etc.) get the
// reinterpret-read/write machinery too.
is_byte_slice :: proc(t: Type) -> bool {
    cur := distinct_base(t)
    if pt, ok := cur.(^Type_Ptr); ok { cur = distinct_base(pt.elem) }
    sl, ok := cur.(^Type_Slice)
    if !ok { return false }
    _, is_byte := sl.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element fixed array [N]byte. Same unwrap
// shape as is_byte_slice so named-byte-container types work.
is_byte_fixed_array :: proc(t: Type) -> bool {
    cur := distinct_base(t)
    if pt, ok := cur.(^Type_Ptr); ok { cur = distinct_base(pt.elem) }
    fa, ok := cur.(^Type_Fixed_Array)
    if !ok { return false }
    _, is_byte := fa.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element partial array [..N]byte. Same unwrap
// shape as the slice / fixed-array helpers — distinct/alias wrappers,
// auto-deref of one ^Ptr.
is_byte_partial_array :: proc(t: Type) -> bool {
    cur := distinct_base(t)
    if pt, ok := cur.(^Type_Ptr); ok { cur = distinct_base(pt.elem) }
    pa, ok := cur.(^Type_Partial_Array)
    if !ok { return false }
    _, is_byte := pa.elem.(Type_Byte)
    return is_byte
}

// True when a type is any byte-addressable buffer — shares the same
// reinterpret read/write semantics as []byte.
is_byte_buffer :: proc(t: Type) -> bool {
    return is_byte_slice(t) || is_byte_fixed_array(t) || is_byte_partial_array(t)
}

// True when an expression is an index into a byte slice (e.g. mem[0]).
is_byte_slice_index_read :: proc(e: Expr) -> bool {
    idx, ok := e.(^Expr_Index)
    if !ok { return false }
    return is_byte_slice(expr_type(idx.expr))
}

// True when an expression is an index into any byte buffer (mem[0], wb[0]).
is_byte_buffer_index_read :: proc(e: Expr) -> bool {
    idx, ok := e.(^Expr_Index)
    if !ok { return false }
    return is_byte_buffer(expr_type(idx.expr))
}

// True when `e` is a `#big_endian` decorated byte-buffer read.
expr_is_big_endian :: proc(e: Expr) -> bool {
    #partial switch v in e {
    case ^Expr_Index: return v.is_big_endian
    case ^Expr_Slice: return v.is_big_endian
    }
    return false
}

// When a typed-pointer site receives `&buf[i]` over a byte buffer, the existing
// ^byte → ^T compatibility rule (types_equal) accepts the assignment but loses
// the size information needed for a runtime bounds check. Stamp the address-of
// node so codegen emits the check before producing the pointer.
maybe_stamp_byte_view :: proc(c: ^Checker, expected: Type, value: Expr) {
    pt, ptr_ok := expected.(^Type_Ptr)
    if !ptr_ok { return }
    // No widening when the destination is itself ^byte.
    if _, byte_target := pt.elem.(Type_Byte); byte_target { return }
    addr, addr_ok := value.(^Expr_Unary)
    if !addr_ok || addr.op != .Ampersand { return }
    idx, idx_ok := addr.operand.(^Expr_Index)
    if !idx_ok { return }
    src_type := expr_type(idx.expr)
    if !is_byte_slice(src_type) && !is_byte_fixed_array(src_type) { return }
    addr.byte_view_size = checker_type_byte_size(pt.elem)
}

// Compute struct byte size with alignment padding (matches LLVM/C layout).
checker_struct_data_byte_size :: proc(sd: ^Scope_Body) -> int {
    offset := 0
    max_align := 1
    for &f in sd.fields {
        a := checker_type_alignment(f.type_)
        if a > max_align { max_align = a }
        if !sd.is_packed && offset % a != 0 {
            offset += a - (offset % a)
        }
        offset += checker_type_byte_size(f.type_)
    }
    if !sd.is_packed && max_align > 0 && offset % max_align != 0 {
        offset += max_align - (offset % max_align)
    }
    return offset
}

checker_struct_byte_size :: proc(st: ^Type_Scope) -> int {
    return checker_struct_data_byte_size(&st.sd)
}

// Alignment of a checker Type (matches LLVM defaults).
checker_type_alignment :: proc(t: Type) -> int {
    switch v in t {
    case Type_F64, Type_Infer_Int, Type_Infer_Float,
         Type_CString, ^Type_Ptr, ^Type_Slice, ^Type_Partial_Array,
         ^Type_Enum, ^Type_Union,
         Type_Const_Int, Type_Runtime_Size,
         Type_Any, Type_Error:
        return 8
    case Type_Err:
        return 4   // u32 (set_id<<16 | tag)
    case Type_Void:
        return 1
    case Type_Numeric:
        switch v.bits {
        case 128: return 16
        case 64: return 8
        case 32: return 4
        case 16: return 2
        case 8:  return 1
        }
    case Type_Bool, Type_C8, Type_Utf8, Type_Byte:
        return 1
    case ^Type_Fixed_Array:
        return checker_type_alignment(v.elem)
    case ^Type_Scope:
        if len(v.fields) > 0 {
            max_a := 1
            for &f in v.fields {
                a := checker_type_alignment(f.type_)
                if a > max_a { max_a = a }
            }
            return max_a
        }
        return 8  // callable fun (function pointer)
    case ^Type_Distinct:
        return checker_type_alignment(v.base_type)
    }
    return 8
}

// Try to evaluate a constant integer expression at compile time.
// Handles number literals and simple binary +/-/* on constants.
const_eval_int :: proc(e: Expr, c: ^Checker = nil) -> (int, bool) {
    if e == nil { return 0, false }
    if num, ok := e.(^Expr_Number); ok {
        if !num.is_float {
            // int_value is exact i64; num.value (f64) loses precision above 2^53.
            return int(num.int_value), true
        }
    }
    if un, ok := e.(^Expr_Unary); ok && un.op == .Minus {
        if v, v_ok := const_eval_int(un.operand, c); v_ok { return -v, true }
    }
    if un, ok := e.(^Expr_Unary); ok && un.op == .Tilde {
        if v, v_ok := const_eval_int(un.operand, c); v_ok { return ~v, true }
    }
    if bin, ok := e.(^Expr_Binary); ok {
        l, l_ok := const_eval_int(bin.left, c)
        r, r_ok := const_eval_int(bin.right, c)
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
    // Named constant: walk into its defining expression.
    if c != nil {
        if ident, ok := e.(^Expr_Ident); ok {
            if const_expr, found := c.table.constants[ident.name]; found {
                return const_eval_int(const_expr, c)
            }
        }
    }
    return 0, false
}

// True when two types are genuinely incompatible — neither is untyped
// (Type_Any, Type_Error, opaque pointer) and they don't match.
// Strict nominal equality: checks struct/enum/union names match exactly.
// Unlike types_equal, does not allow structural compatibility for array classes.
types_name_equal :: proc(a: Type, b: Type) -> bool {
    if is_any(a) || is_any(b) { return true }
    pa, pa_ok := a.(^Type_Ptr)
    pb, pb_ok := b.(^Type_Ptr)
    if pa_ok && pb_ok {
        return types_name_equal(pa.elem, pb.elem)
    }
    sa := as_scope_body(a)
    sb := as_scope_body(b)
    if sa != nil && sb != nil && sa.name != "" && sb.name != "" {
        return sa.name == sb.name
    }
    // For non-struct types, delegate to types_equal
    return types_equal(a, b)
}

types_incompatible :: proc(a: Type, b: Type) -> bool {
    if is_any(a) || is_any(b) { return false }
    // Allow `^byte → fn(...)` for raw-pointer-to-function-pointer assignments.
    // This is the unsafe coercion that lets `game_run : fn(...) = find_symbol(...)`
    // work. The type annotation IS the user's assertion of the function's
    // shape; codegen lowers it as a no-op since `ptr` is `ptr` in LLVM IR.
    if ts, ok := a.(^Type_Scope); ok && ts.kind == .Fun {
        if pt, p_ok := b.(^Type_Ptr); p_ok {
            if _, byte_ok := pt.elem.(Type_Byte); byte_ok { return false }
        }
    }
    return !types_equal(a, b)
}

// Shape shortcut: `p : Foo(Bar(args))` desugars to `p : Foo(Bar)` plus a
// synthetic `{ field = Bar(args) }` struct literal pinned to s.init_values.
// Fires only when:
//   - The Stmt_Decl's type annotation is a Type_Generic_Instance.
//   - The template is a known generic struct.
//   - At a slot with a `~T` shape constraint, the type-arg is a
//     Type_Const_Expr wrapping an Expr_Call.
//   - The user hasn't supplied an init.
// Idempotent — after the first run the args are Type_Name, so re-running
// is a no-op. Multiple shape-constrained slots stack their bindings into
// one literal.
desugar_shape_shortcut :: proc(c: ^Checker, s: ^Stmt_Decl) {
    if c == nil { return }
    if len(s.init_values) != 0 { return }
    gi, gi_ok := s.type_expr.(^Type_Generic_Instance)
    if !gi_ok { return }
    tmpl, tmpl_ok := c.table.generic_templates[gi.name]
    if !tmpl_ok { return }
    lit: ^Expr_Struct_Literal
    for arg_i in 0..<len(gi.type_args) {
        if arg_i >= len(tmpl.generic_params) { break }
        param := tmpl.generic_params[arg_i]
        if param.shape_constraint == "" { continue }
        ce, ce_ok := gi.type_args[arg_i].(Type_Const_Expr)
        if !ce_ok { continue }
        call, call_ok := ce.expr.(^Expr_Call)
        if !call_ok { continue }
        tmpl_fields := tmpl.ast.fields
        if len(tmpl_fields) == 0 {
            tmpl_fields = extract_fields_from_body(tmpl.ast.body)
        }
        bound_any := false
        for f in tmpl_fields {
            tn, tn_ok := f.type_expr.(Type_Name)
            if !tn_ok || tn.name != param.name { continue }
            if lit == nil {
                lit = new(Expr_Struct_Literal)
                lit.span = s.span
            }
            append(&lit.fields, Struct_Field{name = f.name, value = call})
            bound_any = true
        }
        if bound_any {
            gi.type_args[arg_i] = Type_Name{name = call.name, span = ce.span}
        }
    }
    if lit != nil {
        append(&s.init_values, lit)
    }
}

// Compare two types under "Self substitution": occurrences of `ct_self`
// inside `ct_type` correspond to occurrences of `arg_self` inside
// `arg_type`. Walks pointers and slices recursively; bottoms out at
// types_equal for everything else. Used by the shape-constraint method
// signature check, where the constraint's `^Self` resolves to the
// constraint's own scope and the concrete impl's `^Self` resolves to its
// own scope — naively types_equal would never match them.
self_equivalent :: proc(ct_type, arg_type: Type, ct_self, arg_self: ^Type_Scope) -> bool {
    if ts, ok := ct_type.(^Type_Scope); ok && ts == ct_self {
        if ts2, ok2 := arg_type.(^Type_Scope); ok2 && ts2 == arg_self { return true }
        return false
    }
    if pt1, ok := ct_type.(^Type_Ptr); ok {
        pt2, ok2 := arg_type.(^Type_Ptr)
        if !ok2 { return false }
        return self_equivalent(pt1.elem, pt2.elem, ct_self, arg_self)
    }
    if sl1, ok := ct_type.(^Type_Slice); ok {
        sl2, ok2 := arg_type.(^Type_Slice)
        if !ok2 { return false }
        return self_equivalent(sl1.elem, sl2.elem, ct_self, arg_self)
    }
    return types_equal(ct_type, arg_type)
}

// Enforce a `name: ~Constraint` shape-constraint at generic instantiation.
// The concrete `arg` must be a struct/class type that:
//   - declares every method the constraint type declares;
//   - each shared method's signature is equivalent under Self substitution
//     (param count + param types + return type, treating the receiver and
//     any other Self occurrences as positionally compatible);
//   - fits within the constraint's declared byte size (the constraint type
//     reserves the budget explicitly, most commonly via a `size: [N]byte`
//     filler field).
// Each shortcoming surfaces as its own diagnostic at `span`.
check_shape_constraint :: proc(c: ^Checker, param: Generic_Param, arg: Type, home_package: string, span: Span) {
    // `void` is the universal subtype for shape constraints — used as the
    // default type-arg when the user writes `p : Program` (no arena).
    // Trivially satisfies any `~T` requirement (no API to miss, zero size
    // to budget). Reads / method calls on the resulting void slot are
    // gated separately (see field access and call sites).
    if _, is_void := arg.(Type_Void); is_void { return }
    constraint_name := param.shape_constraint
    // Resolve the constraint type by name. The bare identifier in `~T` is
    // looked up against the home package of the template that declared the
    // constraint — that's the only module the parser could have referenced
    // when stamping `shape_constraint`. We try the flat key first; if that
    // misses, fall back to a bare-name search across both tables to cover
    // intrinsic-style types registered without a package prefix.
    flat := make_flat_name(home_package, constraint_name)
    ct: ^Type_Scope
    if ts, ok := c.table.structs[flat]; ok { ct = ts }
    else if ts, ok := c.table.funs[flat]; ok { ct = ts }
    else if ts, ok := c.table.structs[constraint_name]; ok { ct = ts }
    else if ts, ok := c.table.funs[constraint_name]; ok { ct = ts }
    if ct == nil {
        // Couldn't find the constraint — the parser stashed a bare name, so
        // a typo or unimported module slips through to here. Bail loud.
        check_error(c, span,
            TYPE_SHAPE_CONSTRAINT_GENERIC_PARAMETER_COULD,
            constraint_name, param.name)
        return
    }
    arg_scope, arg_ok := distinct_base(arg).(^Type_Scope)
    if !arg_ok || arg_scope.kind != .Struct {
        check_error(c, span,
            TYPE_GENERIC_ARGUMENT_CONCRETE_STRUCT_CLASS,
            param.name, constraint_name, type_name(arg))
        return
    }
    for fn_name, ct_fn in ct.functions {
        arg_fn, arg_has := arg_scope.functions[fn_name]
        if !arg_has || arg_fn == nil {
            check_error(c, span,
                TYPE_TYPE_SATISFY_MISSING_METHOD,
                arg_scope.name, constraint_name, fn_name)
            continue
        }
        // Extra trailing params on the concrete are fine — provided they
        // all have defaults. A caller using the constraint's signature
        // omits them, and Mara's default-arg lowering fills them in.
        // Fewer params, or extras without defaults, breaks the API.
        if len(arg_fn.params) < len(ct_fn.params) {
            check_error(c, span,
                TYPE_TYPE_SATISFY_METHOD_EXPECTS_LEAST,
                arg_scope.name, constraint_name, fn_name, len(ct_fn.params), len(arg_fn.params))
            continue
        }
        extras_ok := true
        for i in len(ct_fn.params)..<len(arg_fn.params) {
            if arg_fn.params[i].default_value == nil {
                check_error(c, span,
                    TYPE_TYPE_SATISFY_METHOD_EXTRA_PARAM,
                    arg_scope.name, constraint_name, fn_name, arg_fn.params[i].name)
                extras_ok = false
            }
        }
        if !extras_ok { continue }
        for i in 0..<len(ct_fn.params) {
            ct_p  := ct_fn.params[i].type_
            arg_p := arg_fn.params[i].type_
            if !self_equivalent(ct_p, arg_p, ct, arg_scope) {
                check_error(c, span,
                    TYPE_TYPE_SATISFY_METHOD_PARAM_EXPECTED,
                    arg_scope.name, constraint_name, fn_name,
                    ct_fn.params[i].name, type_name(ct_p), type_name(arg_p))
            }
        }
        // Return-type compatibility. Same arity, each Self-equivalent.
        // Void (empty list) matches void.
        ret_mismatch := len(ct_fn.return_types) != len(arg_fn.return_types)
        if !ret_mismatch {
            for ct_ret, i in ct_fn.return_types {
                arg_ret := arg_fn.return_types[i]
                if !self_equivalent(ct_ret, arg_ret, ct, arg_scope) {
                    ret_mismatch = true
                    break
                }
            }
        }
        if ret_mismatch {
            ct_ret  := fn_primary_return(ct_fn)
            arg_ret := fn_primary_return(arg_fn)
            check_error(c, span,
                TYPE_TYPE_SATISFY_METHOD_EXPECTED_RETURN,
                arg_scope.name, constraint_name, fn_name, type_name(ct_ret), type_name(arg_ret))
        }
    }
    ct_size  := checker_struct_byte_size(ct)
    arg_size := checker_struct_byte_size(arg_scope)
    if arg_size > ct_size {
        check_error(c, span,
            TYPE_TYPE_FIT_SIZE_BUDGET_NEEDS,
            arg_scope.name, constraint_name, arg_size, ct_size)
    }
}

// Byte size of a checker type (for big-array threshold checks).
checker_type_byte_size :: proc(t: Type) -> int {
    switch v in t {
    case Type_Infer_Int, Type_F64, Type_Infer_Float,
         ^Type_Ptr, Type_CString,
         ^Type_Union,
         Type_Const_Int, Type_Runtime_Size,
         Type_Any, Type_Error, nil:
        return 8
    case Type_Err:         return 4
    case Type_Void:
        return 0
    case Type_Numeric:     return v.bits / 8
    case Type_C8, Type_Utf8, Type_Byte, Type_Bool:
        return 1
    case ^Type_Slice:      return slice_header_bytes
    case ^Type_Partial_Array:
        // { len, cap, ptr, [N x T] } — slice_header_bytes for the header,
        // followed by N * sizeof(elem) backing storage (plus sentinel slot
        // if applicable).
        total := v.size
        if v.has_sentinel { total += 1 }
        return slice_header_bytes + total * checker_type_byte_size(v.elem)
    case ^Type_Scope:      return checker_struct_byte_size(v)
    case ^Type_Fixed_Array:
        total := v.size
        if v.has_sentinel { total += 1 }
        return total * checker_type_byte_size(v.elem)
    case ^Type_Enum:
        switch v.tag_type {
        case "u8", "i8":   return 1
        case "u16", "i16": return 2
        case "u32", "i32": return 4
        }
        return 8  // default i64
    case ^Type_Distinct:   return checker_type_byte_size(v.base_type)
    }
    return 8
}

// Check if a variable is defined at global (root) scope.
// Returns true for top-level variables, false for locals and parameters.
is_global_var :: proc(c: ^Checker, name: string) -> bool {
    if c.table.root_env == nil { return false }
    _, in_root := c.table.root_env.types[name]
    return in_root
}

// Check if a variable name is a function parameter (walks env chain).
is_param :: proc(env: ^Type_Env, name: string) -> bool {
    cur := env
    for cur != nil {
        if name in cur.param_names { return true }
        cur = cur.parent
    }
    return false
}

// Check if a variable was declared with `name : let T = src` — i.e. its storage
// aliases an existing source pointer rather than being a fresh allocation.
is_let_name :: proc(env: ^Type_Env, name: string) -> bool {
    cur := env
    for cur != nil {
        if name in cur.let_names { return true }
        cur = cur.parent
    }
    return false
}

// True if `name` is a parameter of a reference-type (aggregate or slice)
// without `^`. These params are passed as pointers under the hood for
// performance, but the missing `^` is the read-only contract — writes through
// this name are rejected. `^T` params remain mutable; scalar params are
// unaffected (writes only touch the local copy and aren't caller-visible).
//
// Slices participate in the same rule: `s: []T` is read-only (no element
// writes, no header reassign, no `&s`); `s: ^[]T` is mutable. Without this,
// slice param writes would silently propagate to the caller (slices are
// reference types at the ABI), making slices the odd one out.
is_immutable_param :: proc(env: ^Type_Env, name: string) -> bool {
    if !is_param(env, name) { return false }
    t, ok := type_env_get(env, name)
    if !ok { return false }
    base := distinct_base(t)
    if _, is_ptr := base.(^Type_Ptr); is_ptr { return false }
    if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 { return true }
    if _, is_union := base.(^Type_Union); is_union { return true }
    if _, is_slice := base.(^Type_Slice); is_slice { return true }
    return false
}

// Walk an assignment LHS down to its root identifier. Returns (name, true) if
// the write lands on an immutable param's storage WITHOUT crossing a pointer
// (which would shift the write to the pointed-to memory, not the param).
write_root_immutable_param :: proc(e: Expr, env: ^Type_Env) -> (name: string, ok: bool) {
    cur := e
    for {
        #partial switch v in cur {
        case ^Expr_Field_Access:
            if _, is_ptr := distinct_base(expr_type(v.expr)).(^Type_Ptr); is_ptr {
                return "", false
            }
            cur = v.expr
        case ^Expr_Index:
            if _, is_ptr := distinct_base(expr_type(v.expr)).(^Type_Ptr); is_ptr {
                return "", false
            }
            cur = v.expr
        case ^Expr_Slice:
            if _, is_ptr := distinct_base(expr_type(v.expr)).(^Type_Ptr); is_ptr {
                return "", false
            }
            cur = v.expr
        case ^Expr_Ident:
            if is_immutable_param(env, v.name) {
                return v.name, true
            }
            return "", false
        case:
            return "", false
        }
    }
}

// Look up provenance for a variable name (walks env chain).
get_provenance :: proc(env: ^Type_Env, name: string) -> Provenance {
    cur := env
    for cur != nil {
        if p, ok := cur.provenance[name]; ok { return p }
        cur = cur.parent
    }
    return PROV_GLOBAL
}

// Walk the env chain for the local-slice-backed flag — true means the named
// variable holds a struct whose slice fields point at frame-local memory and
// thus must not flow into a longer-lived scope (return, longer-lived field).
get_local_slice_backed :: proc(env: ^Type_Env, name: string) -> bool {
    cur := env
    for cur != nil {
        if v, ok := cur.local_slice_backed[name]; ok { return v }
        cur = cur.parent
    }
    return false
}

set_local_slice_backed :: proc(env: ^Type_Env, name: string) {
    env.local_slice_backed[name] = true
}

// Mark `name` if `value` would leave it holding slice fields pointing at
// frame-local memory. The two paths that produce this today are calls to
// functions with escape locals (sibling/pool storage in the caller frame)
// and struct literals whose slice-field sources are themselves local-
// slice-backed. Anything else: leave the flag unset (assume safe).
mark_local_slice_backed_if_needed :: proc(c: ^Checker, env: ^Type_Env, name: string, value: Expr) {
    if name == "" || value == nil { return }
    if call, ok := value.(^Expr_Call); ok {
        if call_has_local_escape(c, call) {
            set_local_slice_backed(env, name)
        }
        return
    }
    if lit, ok := value.(^Expr_Struct_Literal); ok {
        for field in lit.fields {
            if ident, id_ok := field.value.(^Expr_Ident); id_ok {
                if get_local_slice_backed(env, ident.name) {
                    set_local_slice_backed(env, name)
                    return
                }
            }
        }
        return
    }
    if ident, ok := value.(^Expr_Ident); ok {
        if get_local_slice_backed(env, ident.name) {
            set_local_slice_backed(env, name)
        }
        return
    }
}

// Set provenance for a variable in the current env scope.
set_provenance :: proc(env: ^Type_Env, name: string, p: Provenance) {
    env.provenance[name] = p
}

// For a function returning a ref-typed value, find the parameter index
// whose provenance the return value follows. Returns -1 if the return
// doesn't track a single parameter (constant, multiple sources, an opaque
// callee, etc.). Result cached on the SymbolTable; cycles get -1.
//
// Catches the otherwise-laundered case where a stack-allocated buffer is
// passed through one or more functions before being viewed:
//   outer { storage : [..N]byte; return helper(&storage) }
// Without this, helper's call result would land at depth 0 (global-like)
// and outer's return would silently pass the static checker.
fun_return_arg_set :: proc(c: ^Checker, scope: ^Stmt_Scope) -> []int {
    if scope == nil { return nil }
    if set, ok := c.table.fun_return_arg_set[scope]; ok { return set }
    if c.table.fun_return_arg_pending[scope] { return nil }
    c.table.fun_return_arg_pending[scope] = true
    defer delete_key(&c.table.fun_return_arg_pending, scope)

    // Flow-sensitive walk: each local carries a SET of parameter indices
    // it could trace back to. Branch merges are unions — if one path
    // assigns `out` from param 0 and another from param 1, post-join out
    // tracks {0, 1}. Empty set = no tracked source (depth 0 at call sites).
    //
    // The set encoding captures both:
    //   - straight-line reassignment, where the last write shadows
    //     previous ones (set replaces, doesn't union, on sequential
    //     writes);
    //   - conditional reassignment, where different branches contribute
    //     different params (set unions at the branch join).
    tracking: map[string][dynamic]int
    defer cleanup_arg_set_tracking(&tracking)
    consensus: [dynamic]int
    defer delete(consensus)
    walk_for_return_arg_sets(c, scope.body[:], scope, &tracking, &consensus)

    final := arg_set_freeze(consensus[:])
    c.table.fun_return_arg_set[scope] = final
    return final
}

cleanup_arg_set_tracking :: proc(t: ^map[string][dynamic]int) {
    for _, set in t^ { delete(set) }
    delete(t^)
}

// Walk `stmts` in program order. `tracking[name]` is the current set of
// param indices that `name` could trace back to. At each return, the
// return expression's set is unioned into `consensus`.
walk_for_return_arg_sets :: proc(c: ^Checker, stmts: []Stmt, fn_scope: ^Stmt_Scope, tracking: ^map[string][dynamic]int, consensus: ^[dynamic]int) {
    for s in stmts {
        #partial switch v in s {
        case ^Stmt_Assign:
            if v.value == nil || v.name == "" || v.target != nil { continue }
            new_set := eval_expr_arg_set(c, v.value, fn_scope, tracking)
            // Sequential write: replace (shadows previous value at this name).
            if existing, ok := tracking^[v.name]; ok { delete(existing) }
            tracking^[v.name] = new_set
        case Stmt_Return:
            if len(v.values) == 0 { continue }
            set := eval_expr_arg_set(c, v.values[0], fn_scope, tracking)
            for idx in set { append_unique(consensus, idx) }
            delete(set)
        case ^Stmt_If:
            pre := clone_arg_set_tracking(tracking^)
            walk_for_return_arg_sets(c, v.body[:], fn_scope, tracking, consensus)
            then_state := move_arg_set_tracking(tracking)
            // Reset to pre for else branch
            tracking^ = clone_arg_set_tracking(pre)
            walk_for_return_arg_sets(c, v.else_body[:], fn_scope, tracking, consensus)
            // tracking now holds the else state; merge then into it.
            merge_arg_set_branches(tracking, &then_state, pre)
            cleanup_arg_set_tracking(&then_state)
            cleanup_local_pre(pre)
        case ^Stmt_Decl:
            walk_for_return_arg_sets(c, v.checked[:], fn_scope, tracking, consensus)
        }
    }
}

cleanup_local_pre :: proc(m: map[string][dynamic]int) {
    m := m
    for _, set in m { delete(set) }
    delete(m)
}

clone_arg_set_tracking :: proc(m: map[string][dynamic]int) -> map[string][dynamic]int {
    out: map[string][dynamic]int
    for k, set in m {
        cloned: [dynamic]int
        for idx in set { append(&cloned, idx) }
        out[k] = cloned
    }
    return out
}

// Take ownership of the maps contents into a fresh map; leave the source empty.
move_arg_set_tracking :: proc(m: ^map[string][dynamic]int) -> map[string][dynamic]int {
    out := m^
    m^ = make(map[string][dynamic]int)
    return out
}

// Union the then-branch state into the else-branch result (in `target`),
// using `pre` to fill in keys that one branch didn't touch. Set semantics:
// post-if set = union(then-effective set, else-effective set), where a
// branch that didn't touch a key has that key's pre-if set as effective.
merge_arg_set_branches :: proc(target: ^map[string][dynamic]int, then_state: ^map[string][dynamic]int, pre: map[string][dynamic]int) {
    keys: map[string]bool
    defer delete(keys)
    for k in target^    { keys[k] = true }
    for k in then_state^ { keys[k] = true }
    for k in pre        { keys[k] = true }

    for k in keys {
        then_set: []int
        if s, ok := then_state^[k]; ok { then_set = s[:] }
        else if s, ok := pre[k];   ok { then_set = s[:] }
        else_set: []int
        if s, ok := target^[k]; ok { else_set = s[:] }
        else if s, ok := pre[k]; ok { else_set = s[:] }

        merged: [dynamic]int
        for idx in then_set { append_unique(&merged, idx) }
        for idx in else_set { append_unique(&merged, idx) }

        if existing, ok := target^[k]; ok { delete(existing) }
        target^[k] = merged
    }
}

append_unique :: proc(arr: ^[dynamic]int, x: int) {
    for v in arr { if v == x { return } }
    append(arr, x)
}

// Freeze a [dynamic]int into a sorted, deduplicated []int suitable for
// long-lived storage (the per-function cache). Returns nil for empty.
arg_set_freeze :: proc(set: []int) -> []int {
    if len(set) == 0 { return nil }
    copy := make([]int, len(set))
    for idx, i in set { copy[i] = idx }
    slice.sort(copy)
    // Dedup in place (already deduped by append_unique, but defensive).
    n := 1
    for i in 1..<len(copy) {
        if copy[i] != copy[n-1] { copy[n] = copy[i]; n += 1 }
    }
    return copy[:n]
}

// Evaluate an expression's source arg-set in the current tracking context.
eval_expr_arg_set :: proc(c: ^Checker, e: Expr, fn_scope: ^Stmt_Scope, tracking: ^map[string][dynamic]int) -> [dynamic]int {
    out: [dynamic]int
    if e == nil { return out }
    if ident, ok := e.(^Expr_Ident); ok {
        for p, i in fn_scope.typed_params {
            if p.name == ident.name { append(&out, i); return out }
        }
        if existing, ok := tracking^[ident.name]; ok {
            for idx in existing { append(&out, idx) }
        }
        return out
    }
    if t, ok := e.(^Expr_Take); ok {
        delete(out)
        return eval_expr_arg_set(c, t.storage, fn_scope, tracking)
    }
    if sl, ok := e.(^Expr_Slice); ok {
        delete(out)
        return eval_expr_arg_set(c, sl.expr, fn_scope, tracking)
    }
    if lit, ok := e.(^Expr_Struct_Literal); ok {
        // Union over ref fields.
        for field, i in lit.fields {
            ft := struct_lit_field_type(c, lit, i)
            if ft == nil || !is_ref_type(ft) { continue }
            field_set := eval_expr_arg_set(c, field.value, fn_scope, tracking)
            for idx in field_set { append_unique(&out, idx) }
            delete(field_set)
        }
        return out
    }
    if call, ok := e.(^Expr_Call); ok {
        callee := lookup_callee_scope(c, call)
        if callee == nil { return out }
        callee_set := fun_return_arg_set(c, callee)
        // For each callee arg index in the set, recurse into the matching
        // call argument expression and union.
        for ci in callee_set {
            if ci < 0 || ci >= len(call.args) { continue }
            arg_set := eval_expr_arg_set(c, call.args[ci], fn_scope, tracking)
            for idx in arg_set { append_unique(&out, idx) }
            delete(arg_set)
        }
        return out
    }
    return out
}

// Resolve a struct literal's i-th literal field to its declared field type.
// For positional literals, that's the i-th struct field; for named, lookup
// by name. Returns nil when the type isn't a known struct shape.
struct_lit_field_type :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, lit_idx: int) -> Type {
    sd := as_struct_body(distinct_base(lit.type_))
    if sd == nil { return nil }
    if lit.positional {
        if lit_idx >= 0 && lit_idx < len(sd.fields) { return sd.fields[lit_idx].type_ }
        return nil
    }
    name := lit.fields[lit_idx].name
    for &f in sd.fields {
        if f.name == name { return f.type_ }
    }
    return nil
}

is_ref_type :: proc(t: Type) -> bool {
    bt := distinct_base(t)
    if _, ok := bt.(^Type_Ptr);   ok { return true }
    if _, ok := bt.(^Type_Slice); ok { return true }
    return false
}

struct_has_ref_field :: proc(sd: ^Scope_Body) -> bool {
    for &f in sd.fields {
        if is_ref_type(f.type_) { return true }
    }
    return false
}

// Resolve a call to the callee's source AST, mirroring call_has_local_escape's
// dispatch order: resolved name → source name → resolved_func name → stripped.
lookup_callee_scope :: proc(c: ^Checker, call: ^Expr_Call) -> ^Stmt_Scope {
    if scope, ok := c.table.fun_asts[call_resolved_name(call)]; ok { return scope }
    if scope, ok := c.table.fun_asts[call.name]; ok { return scope }
    if rf, rf_ok := call.resolved_func.?; rf_ok {
        if scope, ok := c.table.fun_asts[rf.name]; ok { return scope }
        n := rf.name
        if idx := strings.last_index_byte(n, '_'); idx >= 0 {
            if scope, ok := c.table.fun_asts[n[idx+1:]]; ok { return scope }
        }
    }
    return nil
}

// Determine the provenance of an expression as a stack-depth integer.
// Lower depth = lives in an outer scope = outlives more.
//   depth = 0           — global / literal / external (outlives the program)
//   depth = N (0 < N)   — backing data lives in a scope at depth N
// The return-from-function check is `depth >= env.scope_depth`. Within a
// function body, locals are at env.scope_depth and refs from params are
// (conservatively) at env.scope_depth - 1.
expr_provenance :: proc(c: ^Checker, e: Expr, env: ^Type_Env) -> Provenance {
    // &x — address-of always points to the local copy, even for params.
    // Parameters are passed by value, so &param is a pointer to stack memory.
    if unary, ok := e.(^Expr_Unary); ok && unary.op == .Ampersand {
        // &slice[i] / &arr[i] — the address points into the indexed thing's
        // storage, so provenance follows the source. For a param slice the
        // data pointer lives in the caller's memory (safe to return); for a
        // local array it's still local (and rightly flagged on return).
        if idx, idx_ok := unary.operand.(^Expr_Index); idx_ok {
            return expr_provenance(c, idx.expr, env)
        }
        if ident, id_ok := unary.operand.(^Expr_Ident); id_ok {
            if is_global_var(c, ident.name) { return PROV_GLOBAL }
            // `name : let T = src` aliases src's storage; &name returns src,
            // so the resulting pointer inherits src's provenance.
            if is_let_name(env, ident.name) { return get_provenance(env, ident.name) }
            // &slice_param / &ptr_param: slice and ptr params are reference
            // types — their header lives in the caller's frame, so the
            // address-of is a caller-owned pointer, not stack-local.
            if is_param(env, ident.name) {
                t := expr_type(unary.operand)
                if _, ok := t.(^Type_Slice); ok { return prov_param(env) }
                if _, ok := t.(^Type_Ptr);   ok { return prov_param(env) }
            }
            return prov_local(env) // &local and &value_param are both at our depth
        }
        if fa, fa_ok := unary.operand.(^Expr_Field_Access); fa_ok {
            if ident, id_ok := fa.expr.(^Expr_Ident); id_ok {
                if is_global_var(c, ident.name) { return PROV_GLOBAL }
                if is_let_name(env, ident.name) { return get_provenance(env, ident.name) }
                return prov_local(env) // &param.field and &local.field are both at our depth
            }
        }
        return prov_local(env)
    }
    // arr[low:high] — slice of an array/slice. The resulting slice's data pointer
    // points into the source's memory, so inherit provenance from the source.
    if sl, ok := e.(^Expr_Slice); ok {
        return expr_provenance(c, sl.expr, env)
    }
    // Variable reference — look up its tracked provenance
    if ident, ok := e.(^Expr_Ident); ok {
        if is_param(env, ident.name) {
            // Reference-type params (ptr, slice): data lives in caller's frame.
            // Value-type params (int, struct, array): local copy at our depth.
            t := expr_type(e)
            if _, ok := t.(^Type_Ptr); ok { return prov_param(env) }
            if _, ok := t.(^Type_Slice); ok { return prov_param(env) }
            return prov_local(env)
        }
        if is_global_var(c, ident.name) { return PROV_GLOBAL }
        return get_provenance(env, ident.name)
    }
    // Field access on a struct — the slice/ptr field's data could point anywhere.
    // We can't determine the backing memory from the field access alone.
    // Exception: if the root variable has known provenance, inherit it for ptr fields.
    if fa, ok := e.(^Expr_Field_Access); ok {
        t := expr_type(e)
        // A pointer field inherits from the root variable
        if _, pt_ok := t.(^Type_Ptr); pt_ok {
            return expr_provenance(c, fa.expr, env)
        }
        // A slice field's data pointer is independent of the struct's location.
        // e.g., arena.base — the struct is on the stack but the slice data is from vm_reserve.
        // We can't trace through the slice data pointer statically, so global.
        return PROV_GLOBAL
    }
    // Literals (array, number, string) — backing memory at our depth.
    if _, ok := e.(^Expr_Array); ok { return prov_local(env) }
    if _, ok := e.(^Expr_Number); ok { return prov_local(env) }
    if _, ok := e.(^Expr_String); ok { return prov_local(env) }
    // Struct literal — for structs with ref fields, the value's effective
    // depth is the max over the EXPLICITLY-ASSIGNED ref fields (those are
    // what would dangle; the struct's bytes are sret-copied at return).
    // Ref fields with no explicit value zero-init to null/empty — safe.
    // So a `Megastruct{}` zero-init literal returns PROV_GLOBAL even if
    // the type has slice fields.
    if lit, ok := e.(^Expr_Struct_Literal); ok {
        max_depth := -1
        for field, i in lit.fields {
            ft := struct_lit_field_type(c, lit, i)
            if ft == nil || !is_ref_type(ft) { continue }
            d := expr_provenance(c, field.value, env).depth
            if d > max_depth { max_depth = d }
        }
        if max_depth >= 0 { return Provenance{depth = max_depth} }
        return PROV_GLOBAL
    }
    // Function call — the callee's return value depth bounds by the max
    // depth of the arguments at the indices the callee can return from.
    // Set encoding handles both straight-line (single tracked index) and
    // conditional reassignment (union across branches). Empty set →
    // PROV_GLOBAL (the function's return is rooted in literals/globals
    // / external sources, none of which can dangle from the caller).
    if call, ok := e.(^Expr_Call); ok {
        if callee := lookup_callee_scope(c, call); callee != nil {
            arg_set := fun_return_arg_set(c, callee)
            max_d := 0
            for ci in arg_set {
                if ci < 0 || ci >= len(call.args) { continue }
                d := expr_provenance(c, call.args[ci], env).depth
                if d > max_d { max_d = d }
            }
            return Provenance{depth = max_d}
        }
        return PROV_GLOBAL
    }
    return PROV_GLOBAL
}

// Emit the type error for a `return value` where `value` would dangle.
// For calls, look up the callee's tracked arg-set and name the specific
// parameter(s) bound to local data — turns a generic message into one
// that points at exactly which argument is the problem.
report_return_escape :: proc(c: ^Checker, val: Expr, span: Span, env: ^Type_Env) {
    if call, ok := val.(^Expr_Call); ok {
        callee := lookup_callee_scope(c, call)
        arg_set := fun_return_arg_set(c, callee) if callee != nil else nil
        if callee != nil && len(arg_set) > 0 {
            // Find which tracked args are local at the call site.
            sb: strings.Builder
            strings.builder_init(&sb)
            defer strings.builder_destroy(&sb)
            unsafe_count := 0
            for ci in arg_set {
                if ci < 0 || ci >= len(call.args) { continue }
                if expr_provenance(c, call.args[ci], env).depth < env.scope_depth { continue }
                if unsafe_count > 0 { strings.write_string(&sb, ", ") }
                pname := callee.typed_params[ci].name if ci < len(callee.typed_params) else "?"
                fmt.sbprintf(&sb, "parameter `%s`", pname)
                unsafe_count += 1
            }
            if unsafe_count > 0 {
                noun := "argument" if unsafe_count == 1 else "arguments"
                check_error(c, span,
                    TYPE_CANNOT_RETURN_RESULT_RETURN_REFERENCE,
                    call.name, strings.to_string(sb), noun)
                return
            }
        }
    }
    check_error(c, span,
        TYPE_CANNOT_RETURN_LOCAL_REFERENCE_MEMORY)
}

// Walk a function's body looking for a `return Foo{a, b}` where Foo has slice
// fields filled by local fixed-array idents. Same shape that codegen detects
// to drive escape-local sibling/pool allocation; here we use it to decide
// whether the call's result has caller-local backing. True ⇒ the returned
// struct's slice fields point into the caller's frame, so returning the
// result further would dangle.
function_has_local_escape :: proc(scope: ^Stmt_Scope) -> bool {
    if scope == nil { return false }
    return scope_has_escape_return(scope.body[:])
}

scope_has_escape_return :: proc(stmts: []Stmt) -> bool {
    // Index local typed declarations by name for return-site lookup.
    local_decls := make(map[string]^Stmt_Assign)
    defer delete(local_decls)
    collect_typed_local_decls(stmts, &local_decls)
    for s in stmts {
        if ret, ok := s.(Stmt_Return); ok {
            if len(ret.values) == 0 { continue }
            lit, lit_ok := ret.values[0].(^Expr_Struct_Literal)
            if !lit_ok { continue }
            for field in lit.fields {
                ident, id_ok := field.value.(^Expr_Ident)
                if !id_ok { continue }
                decl, has_decl := local_decls[ident.name]
                if !has_decl { continue }
                if _, is_fa := decl.var_type.(^Type_Fixed_Array); !is_fa { continue }
                // Distinguish a TRUE local array decl (`verts : [4]Vertex`,
                // s.value == nil) from a take-bound view (`verts := take(...)`)
                // — the latter's storage is caller-provided and the returned
                // slice is safe to escape through.
                if decl.value == nil {
                    return true
                }
            }
        }
        if decl, ok := s.(^Stmt_Decl); ok {
            if scope_has_escape_return(decl.checked[:]) { return true }
        }
        if if_stmt, ok := s.(^Stmt_If); ok {
            if scope_has_escape_return(if_stmt.body[:]) { return true }
            if scope_has_escape_return(if_stmt.else_body[:]) { return true }
        }
    }
    return false
}

collect_typed_local_decls :: proc(stmts: []Stmt, out: ^map[string]^Stmt_Assign) {
    for s in stmts {
        if decl, ok := s.(^Stmt_Decl); ok {
            collect_typed_local_decls(decl.checked[:], out)
            continue
        }
        if assign, ok := s.(^Stmt_Assign); ok {
            if assign.name != "" && assign.var_type != nil {
                out[assign.name] = assign
            }
        }
    }
}

// True if a call's result lives in the caller's frame because the callee
// allocates its escape backing through the calling convention's hidden
// trailing args. Walks the callee's AST through c.table.fun_asts. The
// table uses both flat (`gfx_primitive_quad2`) and bare (`primitive_quad2`)
// keys depending on the registration path, so we try the resolved name,
// the source-level name, and a stripped-suffix fallback in turn.
call_has_local_escape :: proc(c: ^Checker, call: ^Expr_Call) -> bool {
    if scope, ok := c.table.fun_asts[call_resolved_name(call)]; ok {
        return function_has_local_escape(scope)
    }
    if scope, ok := c.table.fun_asts[call.name]; ok {
        return function_has_local_escape(scope)
    }
    if rf, rf_ok := call.resolved_func.?; rf_ok {
        if scope, ok := c.table.fun_asts[rf.name]; ok {
            return function_has_local_escape(scope)
        }
        // Strip the longest `prefix_` from rf.name and retry as bare.
        n := rf.name
        if idx := strings.last_index_byte(n, '_'); idx >= 0 {
            if scope, ok := c.table.fun_asts[n[idx+1:]]; ok {
                return function_has_local_escape(scope)
            }
        }
    }
    return false
}

// Check if an expression is a pointer/slice to local stack memory that won't
// survive the current function return. Only applies to ref types (ptr, slice) —
// returning a struct by value is safe (copied via sret).
is_local_ref :: proc(c: ^Checker, e: Expr, env: ^Type_Env) -> bool {
    t := expr_type(e)
    is_ref := false
    if _, ok := t.(^Type_Ptr); ok { is_ref = true }
    if _, ok := t.(^Type_Slice); ok { is_ref = true }
    // Struct values with ref fields: the struct's bytes are sret-copied at
    // return, but the ref-content can still dangle. Treat as ref-like for
    // the depth check — EXCEPT when the value is a struct literal directly
    // at the return site. Codegen's escape mechanism relocates the local
    // backing storage of `return Foo{verts_uninit_local}` to the caller's
    // sret region; static rejection here would block that legitimate
    // pattern. Indirected forms (`t := Foo{verts}; return t`, or a call
    // result) still go through the depth check.
    if !is_ref {
        if sd := as_struct_body(distinct_base(t)); sd != nil && struct_has_ref_field(sd) {
            if _, lit_ok := e.(^Expr_Struct_Literal); lit_ok { return false }
            is_ref = true
        }
    }
    if !is_ref { return false }
    return expr_provenance(c, e, env).depth >= env.scope_depth
}

// Check if returning `e` would leak slice fields whose backing is in our
// frame. The escape mechanism handles direct `return StructLit{local_arr,..}`
// (the compiler relocates the storage to the caller's sret region), but the
// passthrough form `data := call_with_escape(); return data` doesn't — data
// holds slice headers pointing at our locally-allocated sibling/pool buffers.
// Same for `return call_with_escape()` when the result isn't bound: the
// returned struct's slice fields would dangle past our frame.
returns_locally_backed_struct :: proc(c: ^Checker, e: Expr, env: ^Type_Env) -> bool {
    if e == nil { return false }
    t := expr_type(e)
    sd := as_struct_body(distinct_base(t))
    if sd == nil { return false }
    has_slice := false
    for &f in sd.fields {
        if _, sl_ok := f.type_.(^Type_Slice); sl_ok { has_slice = true; break }
    }
    if !has_slice { return false }
    // Direct call result: callee returned a struct whose slice fields
    // point into our frame because its own escape mechanism relocated
    // them here. Re-returning that further would dangle. The depth-based
    // laundering check is handled by is_local_ref (which treats structs
    // with ref fields as ref-like, except for direct struct literals).
    if call, call_ok := e.(^Expr_Call); call_ok {
        return call_has_local_escape(c, call)
    }
    // Identifier: see if it was tagged as locally-slice-backed at its binding.
    if ident, id_ok := e.(^Expr_Ident); id_ok {
        return get_local_slice_backed(env, ident.name)
    }
    return false
}

// Solidify inferred types to their defaults (for := variable declarations)
solidify_type :: proc(t: Type) -> Type {
    rt := resolve_infer(t)
    if _, ok := rt.(Type_Infer_Int); ok { return Type_Numeric{kind = .Signed, bits = 64} }
    if _, ok := rt.(Type_Infer_Float); ok { return Type_F64{} }
    return rt
}

// ---------------------------------------------------------------------------
// Deferred integer/float inference (the `:=` binding width problem)
// ---------------------------------------------------------------------------
// A `:=` binding whose initializer is an untyped literal/const no longer
// solidifies to i64 at the declaration. It gets a fresh Infer_Cell and stays
// open; its width is decided the first time it flows into a concrete context —
// arithmetic against a sized operand, an argument, an assignment, a return.
// Still open at codegen → i64/f64. Two open bindings combined in arithmetic are
// union-find linked so they resolve together. A binding pinned to one width and
// then used at a narrower / cross-sign width is a hard error asking for an
// explicit annotation (no silent narrowing). Literals and constant references
// stay ANONYMOUS (nil cell): each use adopts its own context independently, as
// before — only a named binding carries a cell, since only it has one storage
// slot to pin.
Infer_Cell :: struct {
    resolved:      Type,        // concrete type once decided; nil while open
    resolved_span: Span,        // where `resolved` was first pinned — for the conflict diagnostic
    link:          ^Infer_Cell, // union-find parent; nil at the root
    name:          string,      // binding name — for the conflict diagnostic
    span:          Span,        // binding decl site — for the conflict diagnostic
}

infer_cell_of :: proc(t: Type) -> ^Infer_Cell {
    #partial switch v in t {
    case Type_Infer_Int:   return v.cell
    case Type_Infer_Float: return v.cell
    }
    return nil
}

infer_root :: proc(cell: ^Infer_Cell) -> ^Infer_Cell {
    root := cell
    for root.link != nil { root = root.link }
    node := cell
    for node.link != nil { next := node.link; node.link = root; node = next } // path-compress
    return root
}

// Follow a bound inference cell to its concrete type. Unbound / anonymous /
// non-infer types return unchanged. Every helper that inspects a type's
// concreteness routes through here, so a pinned binding behaves as its width.
resolve_infer :: proc(t: Type) -> Type {
    cell := infer_cell_of(t)
    if cell == nil { return t }
    r := infer_root(cell)
    if r.resolved != nil { return resolve_infer(r.resolved) }
    return t
}

// Pin (or re-check) an open binding's cell against a concrete numeric target.
// Widening from the decided width is fine; a narrower / cross-sign target is
// the conflict case. Callers pass a target already known to be numeric.
unify_infer_concrete :: proc(c: ^Checker, cell: ^Infer_Cell, target: Type, span: Span) {
    tgt := resolve_infer(target)
    if is_infer(tgt) { return }   // target still open — nothing concrete to pin to yet
    r := infer_root(cell)
    if r.resolved == nil {
        r.resolved = tgt
        r.resolved_span = span   // remember where the width was first fixed
        return
    }
    if types_equal(r.resolved, tgt) || value_preserving_widen(r.resolved, tgt) { return }
    if c != nil {
        check_error(c, span, TYPE_INFER_CONFLICTING_WIDTHS,
            r.name, type_name(r.resolved), span_loc(r.resolved_span), type_name(tgt), span_loc(span))
    }
}

// Union two open bindings so they resolve to a single width.
unify_infer_cells :: proc(c: ^Checker, a: ^Infer_Cell, b: ^Infer_Cell, span: Span) {
    ra := infer_root(a); rb := infer_root(b)
    if ra == rb { return }
    if ra.resolved != nil && rb.resolved != nil {
        if types_equal(ra.resolved, rb.resolved) ||
           value_preserving_widen(ra.resolved, rb.resolved) ||
           value_preserving_widen(rb.resolved, ra.resolved) { return }
        if c != nil {
            check_error(c, span, TYPE_INFER_CONFLICTING_WIDTHS,
                ra.name, type_name(ra.resolved), span_loc(ra.resolved_span),
                type_name(rb.resolved), span_loc(rb.resolved_span))
        }
        return
    }
    if rb.resolved != nil { ra.link = rb } else { rb.link = ra }
}

// At a site where `val` flows into a concrete `target` (argument, assignment,
// field init, return): if val is a deferred binding whose family matches the
// target's (int→int, float→float), pin its cell to target and report handled,
// so the caller skips its normal compat check (the pin owns the diagnostic).
// Anonymous infers, concretes, and cross-family (int↔float) return false so the
// normal check still runs.
coerce_deferred :: proc(c: ^Checker, val: Type, target: Type, span: Span) -> bool {
    cell := infer_cell_of(val)
    if cell == nil { return false }
    tgt := resolve_infer(target)
    _, tkind, tok := numeric_info(tgt)
    if !tok { return false }
    _, is_float_infer := val.(Type_Infer_Float)
    if is_float_infer != (tkind == .Float) { return false }   // int↔float stays explicit
    unify_infer_concrete(c, cell, tgt, span)
    return true
}

// Pin any deferred (inference-cell) struct fields referenced in `expr` to the
// concrete `target` width — so an annotated field's default settles the fields
// that feed it (`per_row : i32 = size / cell` → size and cell become i32). Runs
// during the register loop, where field_map isn't built yet, so it linear-scans
// ft.fields.
pin_field_refs :: proc(c: ^Checker, expr: Expr, target: Type, ft: ^Type_Scope, span: Span) {
    #partial switch v in expr {
    case ^Expr_Binary:
        pin_field_refs(c, v.left, target, ft, span)
        pin_field_refs(c, v.right, target, ft, span)
    case ^Expr_Unary:
        pin_field_refs(c, v.operand, target, ft, span)
    case ^Expr_Ident:
        for &f in ft.fields {
            if f.name == v.name {
                if cell := infer_cell_of(f.type_); cell != nil {
                    unify_infer_concrete(c, cell, target, span)
                }
                break
            }
        }
    }
}

// Try to extract a compile-time constant numeric value from an expression.
// Returns both forms — f64 (for fractional/range-vs-float comparisons) and
// i128 (exact for integer literals up to u64 width). Callers use whichever
// matches the type they're checking. f64 is lossy above 2^53 but i128 stays
// exact for the full u64-width literal range and its negation.
extract_constant_value :: proc(expr: Expr) -> (f_val: f64, i_val: i128, ok: bool) {
    if num, n_ok := expr.(^Expr_Number); n_ok {
        return num.value, num.int_value, true
    }
    if un, u_ok := expr.(^Expr_Unary); u_ok {
        if un.op == .Minus {
            if num, num_ok := un.operand.(^Expr_Number); num_ok {
                return -num.value, -num.int_value, true
            }
        }
    }
    return 0, 0, false
}

// Check that a constant value fits in the target type's range.
// Only checks when the value expression is a compile-time constant (literal)
// and the target is a concrete sized type.
check_literal_overflow :: proc(c: ^Checker, expr: Expr, target: Type, span: Span) {
    val, i_val, is_const := extract_constant_value(expr)
    // If not a direct literal, check if it's a reference to an infer constant
    if !is_const {
        if ident, ok := expr.(^Expr_Ident); ok {
            if const_expr, found := c.table.constants[ident.name]; found {
                check_literal_overflow(c, const_expr, target, span)
            }
        }
        return
    }

    tn := type_name(target)

    #partial switch v in target {
    case Type_Numeric:
        // Word-sized (bits=0): skip — width is decided at codegen, and the 32-bit
        // case is conservative (anything that would overflow there already
        // overflows on the 64-bit case worth catching).
        if v.bits == 0 { return }
        switch v.kind {
        case .Signed:
            // i128 covers the storage range exactly — anything that reached us
            // already fits. Width=128 also skips the formula below where
            // `1 << 127` would wrap.
            if v.bits == 128 { return }
            max_v := (i128(1) << uint(v.bits - 1)) - 1
            min_v := -(i128(1) << uint(v.bits - 1))
            if i_val < min_v || i_val > max_v {
                check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE, i_val, tn, min_v, max_v)
            }
        case .Unsigned:
            // For u128, the i128 storage caps at 2^127-1, so the parser's u64
            // ceiling is already much tighter. Just sanity-check non-negative.
            if v.bits == 128 {
                if i_val < 0 {
                    check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE_128, i_val, tn)
                }
                return
            }
            max_v := (i128(1) << uint(v.bits)) - 1
            if i_val < 0 || i_val > max_v {
                check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE_2, i_val, tn, max_v)
            }
        case .Float:
            // f16: ~65504 max magnitude.
            if v.bits == 16 {
                if val > 65504 || val < -65504 {
                    check_error(c, span, TYPE_CONSTANT_OVERFLOWS_F16, val)
                }
            } else if v.bits == 32 {
                if val > 3.4028235e+38 || val < -3.4028235e+38 {
                    check_error(c, span, TYPE_CONSTANT_OVERFLOWS_F32, val)
                }
            }
        }
    case Type_F64:
        // f64 — no meaningful overflow from a literal
    case:
        // Non-numeric target — nothing to check
    }
}

// ---------------------------------------------------------------------------
// Scope-based checking: register declarations, then check bodies
// ---------------------------------------------------------------------------

// check_scope processes a list of statements in two passes:
//   Pass 1 (register): Record all declarations (functions, structs, enums,
//           unions, variables, foreign blocks) into the scope. Function bodies
//           and block bodies are NOT entered yet.
//   Pass 2 (check):    Check all statements fully — validate expressions,
//           descend into function bodies and block bodies (which themselves
//           go through check_scope recursively).
//
// This means by the time we check a function body, every sibling declaration
// at the same scope level is already known. Forward references just work.

// Param-only variant: an integer-literal default takes the slice-header width
// (`slice_header_width_type` — i64 since the 8-8-8 migration; was i32 under
// 4-4-8). It tracks the slice width on purpose: `name := 0` is overwhelmingly
// an index / offset / count, so a slice length flows into the param cast-free.
// Want a narrower param? annotate it: `name: i32 = 0`.
// Floats and non-literal defaults fall through to infer_field_type_from_default.
infer_param_type_from_default :: proc(c: ^Checker, value: Expr, env: ^Type_Env) -> Type {
    if n, ok := value.(^Expr_Number); ok && !n.is_float {
        return slice_header_width_type
    }
    return infer_field_type_from_default(c, value, env)
}

// The result type of a primitive cast `name(x)` — f32(x) → f32, i32(x) → i32.
// Returns (_, false) for non-cast names. Pure mapping, no checks/side effects;
// shared by the cast checker and the field-default mini-evaluator so the latter
// doesn't mistake a cast for an unknown function and fall back to `any`.
cast_result_type :: proc(name: string) -> (Type, bool) {
    switch name {
    case "i8":   return Type_Numeric{kind = .Signed,   bits = 8},   true
    case "i16":  return Type_Numeric{kind = .Signed,   bits = 16},  true
    case "i32":  return Type_Numeric{kind = .Signed,   bits = 32},  true
    case "i64":  return Type_Numeric{kind = .Signed,   bits = 64},  true
    case "i128": return Type_Numeric{kind = .Signed,   bits = 128}, true
    case "isize": return Type_Numeric{kind = .Signed,  bits = 0},   true
    case "u8":   return Type_Numeric{kind = .Unsigned, bits = 8},   true
    case "u16":  return Type_Numeric{kind = .Unsigned, bits = 16},  true
    case "u32":  return Type_Numeric{kind = .Unsigned, bits = 32},  true
    case "u64":  return Type_Numeric{kind = .Unsigned, bits = 64},  true
    case "u128": return Type_Numeric{kind = .Unsigned, bits = 128}, true
    case "usize": return Type_Numeric{kind = .Unsigned, bits = 0},  true
    case "f16":  return Type_Numeric{kind = .Float,    bits = 16},  true
    case "f32":  return Type_Numeric{kind = .Float,    bits = 32},  true
    case "f64":  return Type_F64{},  true
    case "c8":   return Type_C8{},   true
    case "utf8": return Type_Utf8{}, true
    case "bool": return Type_Bool{}, true
    }
    return nil, false
}

// Infer a field's type from its default value without full check_expr
// (which would fail because the enclosing fun's params/locals aren't in scope yet).
// Handles: identifiers (constants/variables in env), number/string/bool literals,
// and calls to known struct constructors / functions with a return type.
infer_field_type_from_default :: proc(c: ^Checker, value: Expr, env: ^Type_Env, ft: ^Type_Scope = nil) -> Type {
    if ident, id_ok := value.(^Expr_Ident); id_ok {
        if t, t_ok := type_env_get(env, ident.name); t_ok {
            return t
        }
        // Try flat name lookup (for imported constants like QUAT_IDENTITY)
        if c.current_package != "" {
            flat := make_flat_name(c.current_package, ident.name)
            if t, t_ok := type_env_get(env, flat); t_ok {
                return t
            }
        }
        // Fall back to the in-progress struct's already-typed fields. Lets
        // `fov_x := fov_y * w_width / w_height` see the earlier `fov_y` field
        // — without this it would resolve to Type_Any → IR `i64` and the
        // float multiplication would lower to `smul.with.overflow.i64`.
        if ft != nil {
            if idx, fm_ok := ft.field_map[ident.name]; fm_ok && idx < len(ft.fields) {
                return ft.fields[idx].type_
            }
            for &f in ft.fields {
                if f.name == ident.name {
                    return f.type_
                }
            }
        }
    }
    if n, ok := value.(^Expr_Number); ok {
        // Struct field (ft != nil): defer to an inference cell so a later
        // annotated field's default can pin it (e.g. `per_row : i32 = size /
        // cell` pinning size/cell). Finalized to concrete right after the
        // register loop. Param defaults (ft == nil) keep the eager width.
        if ft != nil {
            if n.is_float { return Type_Infer_Float{cell = new(Infer_Cell)} }
            return Type_Infer_Int{cell = new(Infer_Cell)}
        }
        if n.is_float { return Type_F64{} }
        return Type_Numeric{kind = .Signed, bits = 64}
    }
    // A bare string-literal default takes the `cstr` shape (`[..128, 0]utf8`):
    // a stable field layout independent of the literal's length, unlike
    // check_expr's literal-sized `[..len, 0]utf8`. (Annotated string fields like
    // `name : [..16, 0]utf8 = "..."` take the type_expr branch instead.) A
    // string default longer than 128 bytes is a fixed-size overflow to be
    // handled later. Without this the field fell through to Type_Any → i64.
    if _, ok := value.(^Expr_String); ok {
        pa := new(Type_Partial_Array)
        pa.size = 128
        pa.elem = Type_Utf8{}
        pa.has_sentinel = true
        pa.sentinel = 0
        return pa
    }
    // Char literal default — an 8-bit character. Without this it fell through
    // to Type_Any → i64 (wrong width: a char field is i8, not i64).
    if _, ok := value.(^Expr_Char); ok {
        return Type_C8{}
    }
    if _, ok := value.(^Expr_Bool); ok {
        return Type_Bool{}
    }
    // Call expressions: look up the callee's Type_Scope in the env.
    //   struct constructor (kind=.Struct with params)  → the struct type itself
    //   function call       (kind=.Fun with returns)   → primary return type
    if call, ok := value.(^Expr_Call); ok && call.name != "" {
        // Primitive cast: f32(x) → f32, i32(x) → i32. Must precede the env
        // lookup — the cast name isn't a function symbol, so the lookup would
        // miss and the proc would silently fall through to Type_Any.
        if ct, is_cast := cast_result_type(call.name); is_cast {
            return ct
        }
        lookup := proc(env: ^Type_Env, name: string) -> (Type, bool) {
            return type_env_get(env, name)
        }
        t, t_ok := lookup(env, call.name)
        if !t_ok && c.current_package != "" {
            t, t_ok = lookup(env, make_flat_name(c.current_package, call.name))
        }
        if t_ok {
            if ft, ft_ok := t.(^Type_Scope); ft_ok {
                if ft.kind == .Struct { return ft }
                if ft.kind == .Fun && len(ft.return_types) > 0 { return ft.return_types[0] }
            }
        }
    }
    // `field := call()?` — the `?` strips the trailing err, so the field's type
    // is the inner call's first (non-err) return, mirroring check_try. Without
    // this the Expr_Try falls through to the int default and a fallible helper's
    // i32 result would size the field as i64. A fallible constructor inner
    // yields Self (the struct).
    if try_node, ok := value.(^Expr_Try); ok {
        if call, call_ok := try_node.inner.(^Expr_Call); call_ok && call.name != "" {
            t, t_ok := type_env_get(env, call.name)
            if !t_ok && c.current_package != "" {
                t, t_ok = type_env_get(env, make_flat_name(c.current_package, call.name))
            }
            if t_ok {
                if fnt, fnt_ok := t.(^Type_Scope); fnt_ok {
                    if fnt.kind == .Struct { return fnt }
                    if fnt.kind == .Fun && len(fnt.return_types) > 0 { return fnt.return_types[0] }
                }
            }
        }
    }
    // Struct literals: `obj := Object { ... }` — look up the named struct
    // type. Without this, the field's type falls through to Type_Any and
    // lowers to i64 in IR, which silently corrupts later nested-field
    // accesses (e.g. `cam.obj.pos` loads 8 bytes from Camera[0] instead
    // of GEPing into the Object slot). Mirrors the Expr_Call branch.
    if sl, ok := value.(^Expr_Struct_Literal); ok && sl.name != "" {
        if t, t_ok := type_env_get(env, sl.name); t_ok {
            return t
        }
        if c.current_package != "" {
            flat := make_flat_name(c.current_package, sl.name)
            if t, t_ok := type_env_get(env, flat); t_ok {
                return t
            }
        }
    }
    // Binary ops: arithmetic / bitwise / shift preserve the operand type.
    // Comparison ops produce bool. Recurse on the left operand so e.g.
    // `1 << 16` (Number << Number) → i64.
    if bin, ok := value.(^Expr_Binary); ok {
        #partial switch bin.op {
        case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal, .And, .Or:
            return Type_Bool{}
        case:
            return infer_field_type_from_default(c, bin.left, env, ft)
        }
    }
    // Unary ops: same idea — type follows the operand.
    if un, ok := value.(^Expr_Unary); ok {
        return infer_field_type_from_default(c, un.operand, env, ft)
    }
    // Multi-return destructure default: source is a multi-return call. Look
    // up the call's resolved fun to pick the i-th return type. Non-call
    // source is the broadcast case (`a, b := 1 << 16` — three names sharing
    // one scalar default), so each binding takes the source's type directly.
    if td, ok := value.(^Expr_Tuple_Default); ok {
        if call, call_ok := td.source.(^Expr_Call); call_ok && call.name != "" {
            t, t_ok := type_env_get(env, call.name)
            if !t_ok && c.current_package != "" {
                t, t_ok = type_env_get(env, make_flat_name(c.current_package, call.name))
            }
            if t_ok {
                if fnt, fnt_ok := t.(^Type_Scope); fnt_ok && fnt.kind == .Fun {
                    if td.index >= 0 && td.index < len(fnt.return_types) {
                        return fnt.return_types[td.index]
                    }
                }
            }
        }
        return infer_field_type_from_default(c, td.source, env, ft)
    }
    // Unhandled default-expr form. Stay Type_Any (NOT Type_Error): codegen now
    // panics on a Type_Any value type, so an unhandled form surfaces as a loud
    // abort rather than a silent miscompile. Type_Error would be worse here —
    // it lowers to i64 silently in codegen, reintroducing the fallback. The
    // right long-term fix is a real "cannot infer field type — annotate it"
    // diagnostic, but the register pass silences errors (check_expr can't run:
    // the enclosing scope's locals aren't bound yet), so that belongs in a
    // later body-pass refinement.
    return Type_Any{}
}

check_scope :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env, owner: ^Type_Scope = nil, public_env: ^Type_Env = nil) {
    // Pass 1a: pre-register every `name :: ...` definition in this scope —
    // nested funs, unions, distincts — and resolve fun signatures so any
    // statement in the body can call them via forward reference regardless
    // of source order. Module scope already does this via check_module's
    // explicit register_type_names call (no eager signatures there because
    // includes haven't been processed yet — types like `cstr` aren't in
    // env until Pass 1b runs them). Nested scopes opt into eager
    // signatures because by the time we're inside a function body, all
    // upstream includes are already resolved.
    register_type_names(c, stmts, env, owner, public_env, eager_signatures = true)

    // Pass 1a.5: signature-only pass on nested struct definitions, so their
    // fields are populated before Stmt_Decl defaults that reference them get
    // type-checked. Without this, `body := head.count` (where `head` is a
    // sibling of type `Inner`, and `Inner` is defined later in the same
    // scope) fails with "cannot access field" because Inner's field list
    // is still empty when the default expression is checked.
    for stmt in stmts {
        if s, ok := stmt.(^Stmt_Scope); ok && s.kind == .Struct &&
            len(s.typed_params) == 0 && len(s.generic_params) == 0 {
            check_scope_body(c, s, env, signature_only = true)
        }
    }

    // Pass 1b: register the rest (Stmt_Decl, Stmt_Assign, includes, etc.)
    // and run the deferred-body work for any Stmt_Scope that was pre-
    // registered above. The pre_registered_stmts map drives that handoff.
    register_and_check_declarations(c, stmts, env, owner, public_env)

    // Pass 2: check everything, descending into child scopes
    check_bodies(c, stmts, env)
}

// ---------------------------------------------------------------------------
// Shared helpers for type registration
// ---------------------------------------------------------------------------

// Track variant ownership in c.table.variant_to_enum so the dot-shorthand
// fallback (`.Core` with no expected type) can find variants by name across
// visible enums/unions. We deliberately do NOT bind variants as bare names in
// any env: bare variant resolution must go through an expected type.
register_enum_variants :: proc(c: ^Checker, et: ^Type_Enum, env: ^Type_Env, enum_key: string = "", skip_func_names := false, public_env: ^Type_Env = nil) {
    key := enum_key if enum_key != "" else et.name
    for vname in et.variants {
        if existing_enum, mapped := c.table.variant_to_enum[vname]; mapped {
            if existing_enum != "" && existing_enum != key {
                c.table.variant_to_enum[vname] = "" // ambiguous — different enum
            }
        } else {
            c.table.variant_to_enum[vname] = key
        }
    }
}


// Register :: definitions from a fun's scope as top-level entities with mangled names.
// e.g., Mega :: fun { test_print :: fun() { ... } } → registers "Mega_test_print" as a function.
// self_type is the Type value wrapping `st` (always ^Type_Scope). It gets bound to
// the name "Self" in this scope so methods can reference `^Self` / `Self` inside.
register_scope_defs :: proc(c: ^Checker, self_type: Type, st: ^Scope_Body, defs: [dynamic]Stmt, env: ^Type_Env) {
    // Phase 1 only: mangle names and register in scope. No type resolution.
    // Type resolution happens in Phase 2 (check_bodies) uniformly for all funs.
    scope_env := Type_Env{parent = env}
    if self_type != nil {
        type_env_set(&scope_env, "Self", self_type)
    }
    // Find the persistent root env (the module env) so mangled names survive
    // past this call. scope_envs created in recursive calls are stack-local.
    root_env := env
    for root_env.parent != nil { root_env = root_env.parent }
    for def in defs {
        #partial switch s in def {
        case ^Stmt_Scope:
            bare_name := s.name
            mangled := fmt.aprintf("%s_%s", st.name, bare_name)
            s.name = mangled
            // Data/layout vs callable is now determined by the AST kind tag
            // set by the parser from the declaration keyword:
            //   struct / class  → .Struct (data layout)
            //   fun             → .Fun    (callable)
            // This replaces the old body-walking heuristic (which couldn't
            // tell a method's `:=` locals from a class body's init computation).
            def_is_struct := s.kind == .Struct
            // A parameterized constructor MAY declare return types (its trailing
            // err); a pure-data struct (no params) may not — there's no body to
            // run, so nothing to return besides the layout.
            if def_is_struct && len(s.return_types) > 0 && len(s.typed_params) == 0 {
                check_error(c, s.span, TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN, bare_name)
                clear(&s.return_types)  // suppress cascading return-path errors
            }
            if def_is_struct && len(s.typed_params) == 0 {
                // Pure data struct — create Type_Scope with kind=.Struct, no params
                // Phase 2 (check_bodies) resolves fields; we only register the name here.
                def_st := new(Type_Scope)
                def_st.name = mangled
                def_st.home_package = c.current_package
                def_st.kind = .Struct
                def_st.is_packed = s.is_packed
                c.table.structs[mangled] = def_st
                if st.types == nil { st.types = make(map[string]Type) }
                st.types[bare_name] = def_st
                // Nested `::` defs are compile-time names, not runtime data.
                // resolve_struct_field falls through to st.types for field-style
                // lookup, so `Parent.Inner` still works without an entry here.
                if len(s.body) > 0 {
                    register_scope_defs(c, def_st, &def_st.sd, s.body, &scope_env)
                }
                // Register mangled name in the root (persistent) env, bare name in scope env
                type_env_set(root_env, mangled, def_st)
                type_env_set(&scope_env, bare_name, def_st)
                c.table.fun_asts[mangled] = s
            } else {
                // Function or struct constructor (has params) — create Type_Scope
                def_ft := new(Type_Scope)
                def_ft.name = mangled
                def_ft.home_package = c.current_package
                def_ft.has_parens = s.has_parens
                if def_is_struct {
                    def_ft.kind = .Struct
                    def_ft.is_packed = s.is_packed
                    // Phase 2 (check_bodies) resolves fields; we only register the name here.
                    c.table.funs[mangled] = def_ft
                    if st.types == nil { st.types = make(map[string]Type) }
                    st.types[bare_name] = def_ft
                    // Nested `::` defs don't claim runtime storage in the parent.
                    if len(s.body) > 0 {
                        register_scope_defs(c, def_ft, &def_ft.sd, s.body, &scope_env)
                    }
                } else {
                    def_ft.kind = .Fun
                }
                is_callable := !def_is_struct || len(s.typed_params) > 0
                // Resolve params and return type (signatures needed for forward references)
                if len(s.typed_params) > 0 {
                    for tp in s.typed_params {
                        pt := resolve_type_expr(tp.type_expr, c, s.span, env=&scope_env)
                        append(&def_ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
                    }
                    build_param_map(def_ft)
                }
                if is_callable && len(s.return_types) > 0 {
                    for rte in s.return_types {
                        append(&def_ft.return_types, resolve_type_expr(rte, c, s.span, env=&scope_env))
                    }
                }
                // Register mangled name in the root (persistent) env, bare name in scope env
                type_env_set(root_env, mangled, def_ft)
                type_env_set(&scope_env, bare_name, def_ft)
                c.table.fun_asts[mangled] = s
                if is_callable {
                    c.declared_funs[mangled] = true
                }
                if is_callable {
                    if st.functions == nil { st.functions = make(map[string]^Type_Scope) }
                    st.functions[bare_name] = def_ft
                }
            }
        case ^Stmt_Define:
            bare_name := s.name
            mangled := fmt.aprintf("%s_%s", st.name, bare_name)
            s.name = mangled
            // Constants don't have a Type_Scope to point at — track them in a
            // dedicated map so the body-check pass can materialize bare-name
            // aliases (see check_callable_body's consts loop).
            if st.consts == nil { st.consts = make(map[string]^Stmt_Define) }
            st.consts[bare_name] = s
        case ^Stmt_Foreign:
            // Foreign block inside a struct body — register each foreign decl
            // as if it were a method of the parent struct. Mirrors the module-
            // level handling at the Stmt_Foreign case in register_and_check_
            // declarations: build a Type_Scope per decl, register in
            // st.functions[bare] so sibling wrappers can resolve the symbol by
            // bare name, and use a nested mangled name so the codegen-side
            // foreign_funs key (extract_module_into_checked) lines up with
            // what call_resolved_name produces at call sites.
            for decl in s.decls {
                fun_type := new(Type_Scope)
                fun_type.kind = .Fun
                fun_type.calling_conv = .C
                fun_type.home_package = c.current_package
                bare_name := decl.name
                mangled := fmt.aprintf("%s_%s", st.name, bare_name)
                fun_type.name = mangled
                for tp in decl.typed_params {
                    pt := resolve_type_expr(tp.type_expr, c, decl.span, env=&scope_env)
                    append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt})
                }
                for rte in decl.return_types {
                    append(&fun_type.return_types, resolve_type_expr(rte, c, decl.span, env=&scope_env))
                }
                build_param_map(fun_type)
                if st.functions == nil { st.functions = make(map[string]^Type_Scope) }
                st.functions[bare_name] = fun_type
                c.declared_funs[mangled] = true
                c.table.fun_homes[mangled] = c.current_package
                // Bare name in the struct's local scope env so wrapper bodies
                // checked under ns_env (which copies st.functions) can resolve
                // the symbol; mangled name in the persistent root_env so
                // codegen lookups via call_resolved_name resolve.
                type_env_set(&scope_env, bare_name, fun_type)
                type_env_set(root_env, mangled, fun_type)
            }
        }
    }
}

// flatten_module_exports — make an included module's exports reachable in the
// includer's scope. Both bare `include path` and named `name :: include path`
// call this; the only difference between them is whether the module is also
// addressable by an alias (named) or by its own bare name (bare). Without this
// step, `name :: include path` would force qualified `name.X` access for every
// member, which makes stdlib swaps (SDL3 → SDL2 et al.) ripple through every
// caller — see TODO note on module aliasing.
flatten_module_exports :: proc(c: ^Checker, env: ^Type_Env, mod_sd: ^Scope_Body, mod_name: string, is_aliased := false, is_sealed := false) {
    assert(mod_sd.scope != nil, "module-struct must have scope")
    // Sealed includes (`name :: sealed include path`) skip the env.includes
    // append AND the c.declared_funs writes — bare names from the included
    // module are not made available at the call site, only `name.X` access.
    // Used to keep colliding bindings (SDL2 vs SDL3, etc.) properly isolated.
    if is_sealed { return }
    append(&env.includes, mod_sd.scope)
    for name, t in mod_sd.scope.types {
        if name == "void" { continue }  // don't re-export the void null-pointer literal
        if tf, is_func := t.(^Type_Scope); is_func && (len(tf.params) > 0 || tf.has_parens) {
            c.declared_funs[name] = true
        }
    }
    // Dispatches and operator overloads stay on the included module's struct
    // (see Scope_Body.dispatch_groups). Lookups in the includer walk
    // env.includes' owner_modules at call time, so we don't merge here —
    // matches the non-transitive include semantics used elsewhere.
}

// is_enum_visible reports whether the enum identified by `flat_name`
// (e.g. "mara_sdl_Init_Flags") is reachable from `env` via the include chain
// or its parents. Used by the variant-ambiguity check so that a globally
// ambiguous variant (same name in two enums) only errors when both owners
// are actually in scope here.
is_enum_visible :: proc(env: ^Type_Env, flat_name: string) -> bool {
    has_enum :: proc(e: ^Type_Env, flat: string) -> bool {
        if e == nil { return false }
        for _, t in e.types {
            if et, ok := t.(^Type_Enum); ok && et.name == flat { return true }
        }
        return false
    }
    cur := env
    for cur != nil {
        if has_enum(cur, flat_name) { return true }
        for inc in cur.includes {
            if has_enum(inc, flat_name) { return true }
        }
        if cur.is_module_scope { break }
        cur = cur.parent
    }
    return false
}

// find_dispatch collects all functions associated with a dispatch group `name`,
// visible at `env`. Sources walked: the current module's own dispatches
// (c.dispatch_groups), then bare-`include`d modules' dispatches via env.includes.
// Multiple modules may contribute candidates to the same dispatch name; all
// matches are merged so a stdlib dispatch (e.g. `sqrt :: dispatch { sqrt_f32,
// sqrt_f64 }`) can be extended by user code that includes the stdlib module.
// Non-transitive: we don't follow inc.includes — re-export of re-exports is
// opt-in (the user would `include` again themselves), matching type_env_get.
find_dispatch :: proc(c: ^Checker, env: ^Type_Env, name: string) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if fns, ok := c.dispatch_groups[name]; ok {
        for f in fns { append(&result, f) }
    }
    for cur := env; cur != nil; cur = cur.parent {
        for inc in cur.includes {
            if inc.owner_module != nil {
                if fns, ok := inc.owner_module.dispatch_groups[name]; ok {
                    for f in fns { append(&result, f) }
                }
            }
        }
    }
    return result, len(result) > 0
}

// find_operator_overload mirrors find_dispatch for `overload OP name` decls.
find_operator_overload :: proc(c: ^Checker, env: ^Type_Env, op: Token_Kind) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if names, ok := c.operator_overloads[op]; ok {
        for n in names { append(&result, n) }
    }
    for cur := env; cur != nil; cur = cur.parent {
        for inc in cur.includes {
            if inc.owner_module != nil {
                if names, ok := inc.owner_module.operator_overloads[op]; ok {
                    for n in names { append(&result, n) }
                }
            }
        }
    }
    return result, len(result) > 0
}

// ---------------------------------------------------------------------------
// Pass 1a: Register type/function names across files in a module, without
// resolving body fields, base types, param types, or return types. Creates
// empty allocations in c.table.* keyed by flat name, registers them in
// pub env, and attaches them to owner. Pass 1b
// (register_and_check_declarations) sees pre-registered entries and fills
// in the deferred type information.
//
// Used by check_module / check_program for multi-file modules so cross-file
// forward references resolve regardless of file order. Single-pass callers
// (nested scopes inside function bodies) skip this and let
// register_and_check_declarations handle both halves in one go.
// ---------------------------------------------------------------------------

register_type_names :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env, owner: ^Type_Scope = nil, public_env: ^Type_Env = nil, eager_signatures: bool = false) {
    pub := public_env if public_env != nil else env
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Union_Def:
            // Generic union: register as a template and skip concrete
            // registration. Each `Maybe(int)` etc. instantiates the template
            // via resolve_type_expr -> instantiate_generic_union.
            if len(s.generic_params) > 0 {
                if _, exists := c.table.generic_union_templates[s.name]; !exists {
                    c.table.generic_union_templates[s.name] = Generic_Union_Template{
                        name           = s.name,
                        generic_params = s.generic_params,
                        ast            = s,
                        home_package   = c.current_package,
                    }
                }
                c.pre_registered_stmts[rawptr(s)] = true
                continue
            }
            // Determine if pure-enum or data union (matches Phase 1b shape)
            has_data := false
            for vdef in s.variants {
                if len(vdef.fields) > 0 { has_data = true; break }
            }
            if !has_data {
                flat := make_flat_name(c.current_package, s.name)
                if flat in c.table.enums {
                    check_error(c, s.span, TYPE_ENUM_ALREADY_DEFINED, s.name)
                    continue
                }
                et := new(Type_Enum)
                et.name = flat
                et.source_name = s.name
                et.home_package = c.current_package
                et.tag_type = s.tag_type
                et.is_error_kind = s.is_error_kind
                if s.is_error_kind {
                    // Assign 1-based set_id; high 16 bits of each variant's
                    // u32 value. set_id 0 + tag 0 reserved for the universal
                    // `.Ok` zero-value (added implicitly below).
                    c.table.error_set_counter += 1
                    et.error_set_id = c.table.error_set_counter
                    et.variants["Ok"] = 0
                    for vdef, i in s.variants {
                        et.variants[vdef.name] = (et.error_set_id << 16) | (i + 1)
                    }
                } else {
                    for vdef in s.variants {
                        et.variants[vdef.name] = vdef.tag
                    }
                }
                c.table.enums[flat] = et
                type_env_set(pub, s.name, et)
                register_enum_variants(c, et, env, flat, public_env = public_env)
                if owner != nil {
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[s.name] = et
                }
                c.pre_registered_stmts[rawptr(s)] = true
            } else {
                flat := make_flat_name(c.current_package, s.name)
                if flat in c.table.unions {
                    check_error(c, s.span, TYPE_UNION_ALREADY_DEFINED, s.name)
                    continue
                }
                ut := new(Type_Union)
                ut.name = flat
                ut.home_package = c.current_package
                ut.tag_type = s.tag_type
                ut.min_size = s.min_size
                // tag_pad: deferred to Pass 1b (type expr)
                // Tag enum can be fully built — variant tags are integers, no type refs.
                tag_enum_name := strings.concatenate({s.name, "_Tag"})
                tag_et := new(Type_Enum)
                tag_et.name = make_flat_name(c.current_package, tag_enum_name)
                tag_et.home_package = c.current_package
                tag_et.tag_type = s.tag_type
                for vdef in s.variants {
                    tag_et.variants[vdef.name] = vdef.tag
                }
                c.table.enums[tag_et.name] = tag_et
                register_enum_variants(c, tag_et, env, tag_et.name, public_env = public_env)
                // Variant structs registered as empty placeholders; their fields
                // get resolved in Pass 1b.
                for vdef in s.variants {
                    struct_name := strings.concatenate({s.name, "_", vdef.name})
                    vst := new(Type_Scope)
                    vst.name = make_flat_name(c.current_package, struct_name)
                    vst.home_package = c.current_package
                    vst.kind = .Struct
                    c.table.structs[vst.name] = vst
                    append(&ut.variants, vdef.name)
                    ut.tag_map[vdef.name] = vdef.tag
                    ut.variant_structs[vdef.name] = vst.name
                }
                c.table.unions[flat] = ut
                type_env_set(pub, s.name, ut)
                if owner != nil {
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[s.name] = ut
                }
                c.pre_registered_stmts[rawptr(s)] = true
            }
        case ^Stmt_Distinct_Def:
            flat := make_flat_name(c.current_package, s.name)
            if flat in c.table.distinct_types {
                kind := "type" if s.is_alias else "distinct type"
                check_error(c, s.span, TYPE_ALREADY_DEFINED, kind, s.name)
                continue
            }
            dt := new(Type_Distinct)
            dt.name = flat
            dt.home_package = c.current_package
            dt.default_cap_expr = s.default_cap_expr
            dt.is_alias = s.is_alias
            // base_type: deferred to Pass 1b
            c.table.distinct_types[flat] = dt
            type_env_set(pub, s.name, dt)
            c.pre_registered_stmts[rawptr(s)] = true
        case ^Stmt_Scope:
            // Already registered by a parent struct's register_scope_defs
            // pass (e.g. AllocHeader inside Arena_Debug). Its s.name has
            // been mutated to the mangled form and re-running registration
            // here would prepend the package prefix a second time, creating
            // duplicate empty entries. Mirrors the matching guard in
            // register_and_check_declarations.
            if s.name in c.table.fun_asts && c.table.fun_asts[s.name] == s {
                continue
            }
            // Generic templates store the AST — no resolution to defer.
            if len(s.generic_params) > 0 {
                if _, exists := c.table.generic_templates[s.name]; exists { continue }
                c.table.generic_templates[s.name] = Generic_Template{
                    name           = s.name,
                    generic_params = s.generic_params,
                    ast            = s,
                    home_package   = c.current_package,
                }
                if len(s.typed_params) > 0 { c.declared_funs[s.name] = true }
                c.pre_registered_stmts[rawptr(s)] = true
                continue
            }
            is_struct_type := s.kind == .Struct
            if is_struct_type && len(s.return_types) > 0 {
                // Will diagnose properly in Pass 1b; suppress here.
                continue
            }
            if is_struct_type && len(s.typed_params) == 0 {
                flat := make_flat_name(c.current_package, s.name)
                if flat in c.table.structs || flat in c.table.funs {
                    check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, s.name)
                    continue
                }
                struct_type := new(Type_Scope)
                struct_type.name = flat
                struct_type.home_package = c.current_package
                struct_type.kind = .Struct
                struct_type.is_packed = s.is_packed
                c.table.structs[flat] = struct_type
                // Body fields deferred to Pass 1b (register_scope_defs).
                type_env_set(pub, s.name, struct_type)
                c.table.fun_asts[s.name] = s
                c.table.fun_homes[s.name] = c.current_package
                if owner != nil {
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[s.name] = struct_type
                    append(&owner.fields, Struct_Type_Field{name = s.name, type_ = struct_type})
                    owner.field_map[s.name] = len(owner.fields) - 1
                }
                c.pre_registered_stmts[rawptr(s)] = true
            } else {
                flat_name := make_flat_name(c.current_package, s.name)
                if is_struct_type {
                    if flat_name in c.table.funs || flat_name in c.table.structs {
                        check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, s.name)
                        continue
                    }
                } else {
                    if flat_name in c.table.funs {
                        // Function name collisions — Pass 1b will diagnose with
                        // proper context (env lookup, etc.). Skip here.
                        continue
                    }
                }
                fun_type := new(Type_Scope)
                fun_type.has_parens = s.has_parens
                fun_type.name = flat_name
                fun_type.home_package = c.current_package
                if is_struct_type {
                    fun_type.kind = .Struct
                } else {
                    fun_type.kind = .Fun
                }
                c.table.funs[flat_name] = fun_type
                // params and return_type deferred to Pass 1b.
                type_env_set(pub, s.name, fun_type)
                c.table.fun_asts[s.name] = s
                c.table.fun_homes[s.name] = c.current_package
                is_callable := !is_struct_type || len(s.typed_params) > 0
                if is_callable { c.declared_funs[s.name] = true }
                if owner != nil {
                    if is_struct_type {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[s.name] = fun_type
                        append(&owner.fields, Struct_Type_Field{name = s.name, type_ = fun_type})
                        owner.field_map[s.name] = len(owner.fields) - 1
                    }
                    if is_callable {
                        if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
                        owner.functions[s.name] = fun_type
                    }
                }
                // Resolve params and return_types eagerly for non-struct funs
                // so any statement in this scope (including a Stmt_Decl init
                // expression sitting BEFORE this Stmt_Scope in source order)
                // sees the fully-typed signature at type-check time. The
                // deferred Pass 1b handler below is now idempotent on these
                // fields — re-running on already-populated lists is a no-op.
                //
                // Only fires for nested scopes (check_scope passes
                // eager_signatures=true). Top-level callers leave it false
                // because at top-level Pass 1a runs BEFORE includes are
                // processed; trying to resolve `filepath: cstr` here would
                // fail because cstr isn't yet visible from mara.string.
                if !is_struct_type && eager_signatures {
                    if len(s.typed_params) > 0 {
                        for tp in s.typed_params {
                            pt: Type
                            if tp.type_expr != nil {
                                pt = resolve_type_expr(tp.type_expr, c, s.span, env = env)
                            } else if tp.default_value != nil {
                                if _, is_uninit := tp.default_value.(^Expr_Skip_Constructor); is_uninit {
                                    check_error(c, s.span, TYPE_PARAM_TYPE_SKIP_CONSTRUCTOR_REQUIRES, tp.name, tp.name)
                                    pt = Type_Error{}
                                } else {
                                    pt = infer_param_type_from_default(c, tp.default_value, env)
                                }
                            } else {
                                pt = Type_Error{}
                            }
                            append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
                        }
                        build_param_map(fun_type)
                    }
                    if len(s.return_types) > 0 {
                        for rte in s.return_types {
                            rt := resolve_type_expr(rte, c, s.span, env = env)
                            append(&fun_type.return_types, rt)
                        }
                    }
                }
                c.pre_registered_stmts[rawptr(s)] = true
            }
        case ^Stmt_If:
            // Comptime #if: recurse into the live arm so its declarations
            // pre-register at the surrounding scope. Same shape as Pass 1b.
            if !s.is_comptime { continue }
            live, ok := evaluate_comptime_bool(c, s.condition)
            if !ok { continue }  // Pass 1b will report the error.
            if live {
                register_type_names(c, s.body, env, owner, public_env, eager_signatures)
            } else if len(s.else_body) > 0 {
                register_type_names(c, s.else_body, env, owner, public_env, eager_signatures)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Pass 1b: Resolve body fields, base types, param/return types, and check
// statement-level declarations. When called after register_type_names (the
// two-pass module path), allocations are already in c.table.* and we just
// fill them in. When called in single-pass mode (nested scopes), we
// allocate fresh — same as before.
// ---------------------------------------------------------------------------

register_and_check_declarations :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env, owner: ^Type_Scope = nil, public_env: ^Type_Env = nil) {
    // pub: where defined names (fun/struct/type/foreign/constants) get registered.
    // - In single-env mode (callers from inside fun bodies, struct bodies): public_env is nil
    //   and pub == env, so behavior is unchanged.
    // - In per-file mode (callers from check_module / check_program): public_env is the module
    //   env and env is the file env — defined names go to the module env (visible to siblings
    //   via the chain file_env -> mod_env), include names stay in the file env (private).
    pub := public_env if public_env != nil else env
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Union_Def:
            // Generic union: registration happens in Pass 1a (template only).
            // Each instantiation creates its own concrete Type_Union via
            // instantiate_generic_union, so there's nothing to resolve here.
            if len(s.generic_params) > 0 {
                if _, exists := c.table.generic_union_templates[s.name]; !exists {
                    c.table.generic_union_templates[s.name] = Generic_Union_Template{
                        name           = s.name,
                        generic_params = s.generic_params,
                        ast            = s,
                        home_package   = c.current_package,
                    }
                }
                delete_key(&c.pre_registered_stmts, rawptr(s))
                continue
            }
            // Pre-registered by Pass 1a (multi-file module path): pure-enum
            // case is fully resolved at Pass 1a (no type refs); data-union
            // case still needs tag_pad and variant struct fields resolved.
            if c.pre_registered_stmts[rawptr(s)] {
                has_data := false
                for vdef in s.variants {
                    if len(vdef.fields) > 0 { has_data = true; break }
                }
                if has_data {
                    flat := make_flat_name(c.current_package, s.name)
                    if ut, ok := c.table.unions[flat]; ok {
                        if s.tag_pad != nil {
                            ut.tag_pad = resolve_type_expr(s.tag_pad, c, s.span)
                        }
                        for vdef in s.variants {
                            vst_name := ut.variant_structs[vdef.name]
                            if vst, vst_ok := c.table.structs[vst_name]; vst_ok {
                                for field in vdef.fields {
                                    ft := resolve_type_expr(field.type_expr, c, s.span)
                                    append(&vst.fields, Struct_Type_Field{name = field.name, type_ = ft, default_value = field.default_value, is_using = field.is_using})
                                }
                                build_field_map(&vst.sd)
                            }
                        }
                    }
                }
                delete_key(&c.pre_registered_stmts, rawptr(s))
                continue
            }
            // Determine if pure-enum or data union
            has_data := false
            for vdef in s.variants {
                if len(vdef.fields) > 0 { has_data = true; break }
            }

            if !has_data {
                // Pure-enum union: register as a Type_Enum with the union's name
                et := new(Type_Enum)
                et.name = make_flat_name(c.current_package, s.name)
                et.source_name = s.name
                et.home_package = c.current_package
                et.tag_type = s.tag_type
                et.is_error_kind = s.is_error_kind
                if et.name in c.table.enums {
                    check_error(c, s.span, TYPE_ENUM_ALREADY_DEFINED, s.name)
                } else {
                    if s.is_error_kind {
                        c.table.error_set_counter += 1
                        et.error_set_id = c.table.error_set_counter
                        et.variants["Ok"] = 0
                        for vdef, i in s.variants {
                            et.variants[vdef.name] = (et.error_set_id << 16) | (i + 1)
                        }
                    } else {
                        for vdef in s.variants {
                            et.variants[vdef.name] = vdef.tag
                        }
                    }
                    c.table.enums[et.name] = et
                    type_env_set(pub, s.name, et)
                    register_enum_variants(c, et, env, et.name, public_env = public_env)
                    // Attach to enclosing module struct (if any).
                    if owner != nil {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[s.name] = et
                    }
                }
            } else {
                // Data union: create tag enum, variant structs, and union type
                ut := new(Type_Union)
                ut.name = make_flat_name(c.current_package, s.name)
                ut.home_package = c.current_package
                if ut.name in c.table.unions {
                    check_error(c, s.span, TYPE_UNION_ALREADY_DEFINED, s.name)
                } else {
                    // 1. Create tag enum (Name_Tag)
                    tag_enum_name := strings.concatenate({s.name, "_Tag"})
                    tag_et := new(Type_Enum)
                    tag_et.name = make_flat_name(c.current_package, tag_enum_name)
                    tag_et.home_package = c.current_package
                    tag_et.tag_type = s.tag_type
                    for vdef in s.variants {
                        tag_et.variants[vdef.name] = vdef.tag
                    }
                    c.table.enums[tag_et.name] = tag_et
                    register_enum_variants(c, tag_et, env, tag_et.name, public_env = public_env)

                    // 2. Create variant structs (Name_Variant)
                    ut.tag_type = s.tag_type
                    ut.min_size = s.min_size
                    if s.tag_pad != nil {
                        ut.tag_pad = resolve_type_expr(s.tag_pad, c, s.span)
                    }
                    for vdef in s.variants {
                        struct_name := strings.concatenate({s.name, "_", vdef.name})
                        vst := new(Type_Scope)
                        vst.name = make_flat_name(c.current_package, struct_name)
                        vst.home_package = c.current_package
                        vst.kind = .Struct
                        for field in vdef.fields {
                            ft := resolve_type_expr(field.type_expr, c, s.span)
                            append(&vst.fields, Struct_Type_Field{name = field.name, type_ = ft, default_value = field.default_value, is_using = field.is_using})
                        }
                        build_field_map(&vst.sd)
                        c.table.structs[vst.name] = vst
                        append(&ut.variants, vdef.name)
                        ut.tag_map[vdef.name] = vdef.tag
                        ut.variant_structs[vdef.name] = vst.name
                    }

                    // 3. Register Type_Union
                    c.table.unions[ut.name] = ut
                    type_env_set(pub, s.name, ut)
                    // Attach to enclosing module struct (if any).
                    if owner != nil {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[s.name] = ut
                    }
                }
            }
        case ^Stmt_Distinct_Def:
            // Pre-registered by Pass 1a (multi-file module path): retrieve
            // the placeholder allocation and just fill in base_type. Single-
            // pass mode (nested scopes): allocate fresh, same as before.
            if c.pre_registered_stmts[rawptr(s)] {
                flat := make_flat_name(c.current_package, s.name)
                if dt, ok := c.table.distinct_types[flat]; ok {
                    dt.base_type = resolve_type_expr(s.base_type, c, s.span)
                }
                delete_key(&c.pre_registered_stmts, rawptr(s))
                continue
            }
            base := resolve_type_expr(s.base_type, c, s.span)
            dt := new(Type_Distinct)
            dt.name = make_flat_name(c.current_package, s.name)
            dt.home_package = c.current_package
            dt.base_type = base
            dt.default_cap_expr = s.default_cap_expr
            dt.is_alias = s.is_alias
            if dt.name in c.table.distinct_types {
                kind := "type" if s.is_alias else "distinct type"
                check_error(c, s.span, TYPE_ALREADY_DEFINED, kind, s.name)
            } else {
                c.table.distinct_types[dt.name] = dt
                type_env_set(pub, s.name, dt)
            }
        case ^Stmt_Scope:
            // Pre-registered by Pass 1a (multi-file module path): the type
            // allocation, table entries, env binding, and owner attachment
            // are already done. Resolve only the deferred body (struct
            // fields via register_scope_defs, fun params, return type).
            if c.pre_registered_stmts[rawptr(s)] {
                delete_key(&c.pre_registered_stmts, rawptr(s))
                if len(s.generic_params) > 0 { continue }  // generic — nothing more to do
                is_struct := s.kind == .Struct
                flat := make_flat_name(c.current_package, s.name)
                if is_struct && len(s.typed_params) == 0 {
                    if struct_type, ok := c.table.structs[flat]; ok {
                        register_scope_defs(c, struct_type, &struct_type.sd, s.body, env)
                    }
                } else {
                    if fun_type, ok := c.table.funs[flat]; ok {
                        if is_struct {
                            register_scope_defs(c, fun_type, &fun_type.sd, s.body, env)
                        }
                        // Idempotent: register_type_names resolves these
                        // eagerly for nested-scope funs (so forward refs from
                        // sibling Stmt_Decls find a fully-typed signature).
                        // Skip re-resolution if params/return_types are
                        // already populated.
                        if len(s.typed_params) > 0 && len(fun_type.params) == 0 {
                            for tp in s.typed_params {
                                pt: Type
                                if tp.type_expr != nil {
                                    pt = resolve_type_expr(tp.type_expr, c, s.span, env = env)
                                } else if tp.default_value != nil {
                                    if _, is_uninit := tp.default_value.(^Expr_Skip_Constructor); is_uninit {
                                        check_error(c, s.span, TYPE_PARAM_TYPE_SKIP_CONSTRUCTOR_REQUIRES, tp.name, tp.name)
                                        pt = Type_Error{}
                                    } else {
                                        pt = infer_param_type_from_default(c, tp.default_value, env)
                                    }
                                } else {
                                    pt = Type_Error{}
                                }
                                append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
                            }
                            build_param_map(fun_type)
                        }
                        is_callable := !is_struct || len(s.typed_params) > 0
                        if is_callable && len(s.return_types) > 0 && len(fun_type.return_types) == 0 {
                            for rte in s.return_types {
                                rt := resolve_type_expr(rte, c, s.span, env = env)
                                append(&fun_type.return_types, rt)
                            }
                        }
                    }
                }
                continue
            }
            // Generic template — store and continue
            if len(s.generic_params) > 0 {
                c.table.generic_templates[s.name] = Generic_Template{
                    name           = s.name,
                    generic_params = s.generic_params,
                    ast            = s,
                    home_package   = c.current_package,
                }
                if len(s.typed_params) > 0 { c.declared_funs[s.name] = true }
                continue
            }
            // Already registered by a parent's register_scope_defs pass — skip.
            // That pass resolves params and return type as well.
            if s.name in c.table.fun_asts && c.table.fun_asts[s.name] == s {
                continue
            }
            existing_fn, existing_fn_found := type_env_get(env, s.name)
            if existing_fn_found {
                if tf, is_fn := existing_fn.(^Type_Scope); is_fn && len(tf.params) > 0 && len(s.typed_params) > 0 {
                    check_error(c, s.span, TYPE_FUNCTION_ALREADY_DEFINED, s.name)
                    continue
                }
            }
            // Data/layout vs callable is now determined by the AST kind tag
            // set by the parser from the declaration keyword (see the matching
            // comment in register_scope_defs for details).
            is_struct_type := s.kind == .Struct
            // Parameterized constructors may declare returns (trailing err);
            // pure-data structs (no params) may not.
            if is_struct_type && len(s.return_types) > 0 && len(s.typed_params) == 0 {
                check_error(c, s.span, TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN, s.name)
                clear(&s.return_types)  // suppress cascading return-path errors
            }
            if is_struct_type && len(s.typed_params) == 0 {
                // Pure data struct — create Type_Scope with kind=.Struct, no params
                struct_type := new(Type_Scope)
                struct_type.name = make_flat_name(c.current_package, s.name)
                struct_type.home_package = c.current_package
                struct_type.kind = .Struct
                struct_type.is_packed = s.is_packed
                if struct_type.name in c.table.structs || struct_type.name in c.table.funs {
                    check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, s.name)
                    continue
                }
                c.table.structs[struct_type.name] = struct_type
                register_scope_defs(c, struct_type, &struct_type.sd, s.body, env)
                type_env_set(pub, s.name, struct_type)
                c.table.fun_asts[s.name] = s
                c.table.fun_homes[s.name] = c.current_package
                // Attach as a member of the enclosing module struct (if any).
                // Mirrors the work extract_module_into_checked used to do post-hoc.
                if owner != nil {
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[s.name] = struct_type
                    append(&owner.fields, Struct_Type_Field{name = s.name, type_ = struct_type})
                    owner.field_map[s.name] = len(owner.fields) - 1
                }
            } else {
                // Function or struct constructor (has params)
                if is_struct_type {
                    flat_name := make_flat_name(c.current_package, s.name)
                    if flat_name in c.table.funs || flat_name in c.table.structs {
                        check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, s.name)
                        continue
                    }
                }
                fun_type := new(Type_Scope)
                fun_type.has_parens = s.has_parens
                // Name is set for both struct and fun kinds so types_equal
                // compares them nominally (two funs with same shape but different
                // names are distinct — honors `fn name` identity). Only struct
                // kinds are added to c.table.funs (the map is used by codegen
                // to emit LLVM struct types; funs are emitted separately).
                fun_type.name = make_flat_name(c.current_package, s.name)
                fun_type.home_package = c.current_package
                if is_struct_type {
                    fun_type.kind = .Struct
                    c.table.funs[fun_type.name] = fun_type
                    register_scope_defs(c, fun_type, &fun_type.sd, s.body, env)
                } else {
                    fun_type.kind = .Fun
                    // Also register in the global funs table so post-check
                    // passes (extract_checked_scope, codegen helpers) can
                    // find nested funs whose registering env is a function
                    // body — those envs aren't reachable from the package
                    // env's chain. Top-level funs go in here too; the env
                    // chain lookup just happens to work for them.
                    c.table.funs[fun_type.name] = fun_type
                }
                // Resolve params and return type now (Phase 1) — needed for forward references.
                // Body-extracted fields are deferred to Phase 2.
                // Pass env so `fn game_run` annotations on params find sibling
                // functions that were registered earlier in this scope.
                if len(s.typed_params) > 0 {
                    for tp in s.typed_params {
                        pt: Type
                        if tp.type_expr != nil {
                            pt = resolve_type_expr(tp.type_expr, c, s.span, env = env)
                        } else if tp.default_value != nil {
                            if _, is_uninit := tp.default_value.(^Expr_Skip_Constructor); is_uninit {
                                check_error(c, s.span, TYPE_PARAM_TYPE_SKIP_CONSTRUCTOR_REQUIRES, tp.name, tp.name)
                                pt = Type_Error{}
                            } else {
                                // `name(s) := default` — infer the param's type from the default expression.
                                pt = infer_param_type_from_default(c, tp.default_value, env)
                            }
                        } else {
                            pt = Type_Error{}
                        }
                        append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
                    }
                    build_param_map(fun_type)
                }
                is_callable := !is_struct_type || len(s.typed_params) > 0
                if is_callable && len(s.return_types) > 0 {
                    for rte in s.return_types {
                        rt := resolve_type_expr(rte, c, s.span, env = env)
                        append(&fun_type.return_types, rt)
                    }
                }
                // Register name in scope
                type_env_set(pub, s.name, fun_type)
                c.table.fun_asts[s.name] = s
                c.table.fun_homes[s.name] = c.current_package
                if is_callable { c.declared_funs[s.name] = true }
                // Attach as a member of the enclosing module struct (if any).
                // Mirrors the work extract_module_into_checked used to do post-hoc.
                if owner != nil {
                    if is_struct_type {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[s.name] = fun_type
                        append(&owner.fields, Struct_Type_Field{name = s.name, type_ = fun_type})
                        owner.field_map[s.name] = len(owner.fields) - 1
                    }
                    if is_callable {
                        if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
                        owner.functions[s.name] = fun_type
                    }
                }
            }
        case ^Stmt_Foreign:
            // Foreigns inside a struct/class body are registered by Phase 1's
            // register_scope_defs (with mangled names). Phase 2 walks the same
            // body via check_scope → register_and_check_declarations; if we
            // re-ran the module-level handler here, bare names like
            // `CreateFileA` would land in c.declared_funs and the call-site
            // resolution would route bare-name calls back to the module
            // package (mara_os_CreateFileA) instead of the struct-mangled
            // form (mara_os_platform_win32_CreateFileA). Detect class scope
            // up the env chain and skip — Phase 1 already did the work.
            in_class_scope := false
            for cur := env; cur != nil; cur = cur.parent {
                if cur.class_scope != nil { in_class_scope = true; break }
                if cur.is_module_scope { break }
            }
            if in_class_scope { continue }
            // Register each foreign function in the type environment.
            // Pass env to resolve_type_expr so type names like `Event` resolve
            // to the current module's flavor when multiple modules export the
            // same name (otherwise the global symbol_home picks first-loader,
            // which is wrong for SDL2-vs-SDL3 setups).
            for decl in s.decls {
                fun_type := new(Type_Scope)
                fun_type.kind = .Fun
                fun_type.calling_conv = .C
                fun_type.home_package = c.current_package
                fun_type.name = make_flat_name(c.current_package, decl.name)
                for tp in decl.typed_params {
                    pt := resolve_type_expr(tp.type_expr, c, decl.span, env = env)
                    append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt})
                }
                for rte in decl.return_types {
                    append(&fun_type.return_types, resolve_type_expr(rte, c, decl.span, env = env))
                }
                build_param_map(fun_type)
                type_env_set(pub, decl.name, fun_type)
                c.declared_funs[decl.name] = true
                c.table.fun_homes[decl.name] = c.current_package
                // Attach to enclosing module struct (if any).
                if owner != nil {
                    if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
                    owner.functions[decl.name] = fun_type
                }
            }
        case ^Stmt_If:
            // Comptime `#if`: recurse into the live arm so its declarations
            // register at the surrounding scope, exactly as if the `#if`
            // weren't there. Without this, decls inside (e.g.,
            // `#if #native { foreign ... }` at module scope, or
            // `#if #web { loop_iter :: fun(...) }` inside a function body)
            // never reach the env, and later references fail with
            // "undefined". The Pass 2 handler in check_bodies handles only
            // the live arm's body checks (not registrations) to avoid double
            // registration here.
            if !s.is_comptime { continue }
            live, ok := evaluate_comptime_bool(c, s.condition)
            if !ok {
                check_error(c, s.span, TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN)
                continue
            }
            if live {
                register_and_check_declarations(c, s.body, env, owner, public_env)
            } else if len(s.else_body) > 0 {
                register_and_check_declarations(c, s.else_body, env, owner, public_env)
            }
        case ^Stmt_Define:
            // Include expressions: scope-based resolution.
            // Mirrors the Stmt_Assign + Expr_Include path so `name :: include path`
            // behaves the same as `name := include path` (the latter is the older
            // spelling; `::` is the comptime-correct one since includes are
            // comptime-only).
            if inc, is_include := s.value.(^Expr_Include); is_include {
                // `name :: use path` — explicit aliasing form. Resolve `path`
                // to exactly that module (no parent-glob; submodules are pulled
                // in by their own explicit `use`), load and flatten it. That
                // module binds to s.name so qualified access like `name.X` works.
                matching := find_matching_modules(c, inc.path)
                defer delete(matching)
                if len(matching) == 0 {
                    check_error(c, inc.span, TYPE_MODULE_FOUND, inc.path)
                    continue
                }
                main_mod: Type
                for sub_name in matching {
                    m := check_module(c, sub_name, inc.span)
                    if m == nil { continue }
                    sd := as_scope_body(m)
                    if sd == nil { continue }
                    // `name :: use path` makes the module reachable both as
                    // `name.member` AND via bare-name lookup. is_aliased keeps
                    // the names local (no global symbol_home claim);
                    // is_sealed restricts access to `name.X` only.
                    // is_reexport (`name :: include path`) additionally
                    // flattens into pub.
                    flatten_module_exports(c, env, sd, sub_name, is_aliased = true, is_sealed = inc.is_sealed)
                    if inc.is_reexport && pub != env {
                        flatten_module_exports(c, pub, sd, sub_name, is_aliased = true, is_sealed = inc.is_sealed)
                    }
                    if sub_name == inc.path { main_mod = m }
                }
                // Synthetic-parent fallback (same as the Stmt_Assign path).
                if main_mod == nil {
                    if synth, ok := c.checked_modules[inc.path]; ok {
                        main_mod = synth
                    }
                }
                if main_mod != nil {
                    type_env_set(env, s.name, main_mod)
                    s.var_type = main_mod
                    s.env_type = main_mod
                    inc.type_ = main_mod
                    if c.mara_env != nil {
                        type_env_set(c.mara_env, inc.path, main_mod)
                    }
                }
                continue
            }
            check_define(c, s, env, public_env = public_env)
        case ^Stmt_Decl:
            // Sized-slice on a distinct slice alias: `name : String2(N)` parses
            // as `Type_Generic_Instance{name=String2, args=[N]}` (the parser
            // greedily reads `Name(args)` as a generic instantiation). When
            // the name resolves to a distinct slice alias and there's a single
            // numeric arg, rewrite to the sized-slice decl form before normal
            // type resolution: type_expr becomes just `Type_Name{String2}`,
            // slice_cap_expr captures the cap.
            if gi, gi_ok := s.type_expr.(^Type_Generic_Instance); gi_ok && len(gi.type_args) == 1 && s.slice_cap_expr == nil {
                if _, is_generic := c.table.generic_templates[gi.name]; !is_generic {
                    // Resolve the bare name through includes / aliases to the
                    // flat key used in distinct_types (e.g. "String2" ->
                    // "test_string_String2").
                    flat := resolve_type_name(c, gi.name, "", env)
                    if flat == "" { flat = gi.name }
                    if dt, found := c.table.distinct_types[flat]; found {
                        if _, is_slice := dt.base_type.(^Type_Slice); is_slice {
                            cap_expr: Expr
                            if cv, cv_ok := gi.type_args[0].(Type_Const_Value); cv_ok {
                                num := new(Expr_Number)
                                num.int_value = i128(cv.value)
                                num.value = f64(cv.value)
                                num.span = cv.span
                                cap_expr = num
                            } else if ce, ce_ok := gi.type_args[0].(Type_Const_Expr); ce_ok {
                                cap_expr = ce.expr
                            }
                            if cap_expr != nil {
                                s.type_expr = Type_Name{name = gi.name, span = gi.span}
                                s.slice_cap_expr = cap_expr
                            }
                        }
                    }
                }
            }
            // Bare distinct slice alias with a default cap: `s : String` where
            // `String :: distinct [,0]utf8(128)` — pick up the default.
            if tn, tn_ok := s.type_expr.(Type_Name); tn_ok && s.slice_cap_expr == nil {
                flat := resolve_type_name(c, tn.name, "", env)
                if flat == "" { flat = tn.name }
                if dt, found := c.table.distinct_types[flat]; found {
                    if _, is_slice := dt.base_type.(^Type_Slice); is_slice && dt.default_cap_expr != nil {
                        s.slice_cap_expr = dt.default_cap_expr
                    }
                }
            }
            // Sized slice on a non-generic element type: `name : []Mesh_Data(12)`
            // parses as `[]Type_Generic_Instance{Mesh_Data, [12]}` because the
            // parser is greedy about `Name(args)`. When the elem name doesn't
            // resolve as generic and there's exactly one numeric arg, lift the
            // arg into slice_cap_expr and replace the elem with the bare name.
            if ts, ts_ok := s.type_expr.(^Type_Slice_Expr); ts_ok && s.slice_cap_expr == nil {
                if gi, gi_ok := ts.elem.(^Type_Generic_Instance); gi_ok && len(gi.type_args) == 1 {
                    if _, is_generic := c.table.generic_templates[gi.name]; !is_generic {
                        cap_expr: Expr
                        if cv, cv_ok := gi.type_args[0].(Type_Const_Value); cv_ok {
                            num := new(Expr_Number)
                            num.int_value = i128(cv.value)
                            num.value = f64(cv.value)
                            num.span = cv.span
                            cap_expr = num
                        } else if ce, ce_ok := gi.type_args[0].(Type_Const_Expr); ce_ok {
                            cap_expr = ce.expr
                        }
                        if cap_expr != nil {
                            ts.elem = Type_Name{name = gi.name, span = gi.span}
                            s.slice_cap_expr = cap_expr
                        }
                    }
                }
            }

            // Shape-shortcut: `p : Foo(Bar(args))` desugars in place to
            // `p : Foo(Bar) = { field = Bar(args) }`. The actual work lives
            // in desugar_shape_shortcut so the same transform fires from
            // check_scope_body's early field-resolution pre-pass (which sees
            // the decl before this branch runs). Idempotent: subsequent
            // invocations see Type_Name and bail.
            desugar_shape_shortcut(c, s)

            // Synth-and-delegate: expand Stmt_Decl into equivalent
            // Stmt_Assign / Stmt_Multi_Return_Assign nodes stored on s.checked,
            // then run the existing per-assign logic on them. Codegen and
            // dump iterate s.checked the same way.
            //
            // Multi-package builds run the checker once per package, and a
            // shared AST node (e.g. a stdlib decl reached from two packages)
            // would hit this code twice. Skip the synthesis if s.checked is
            // already populated — the prior run did it and the desugared
            // statements still apply.
            if len(s.checked) == 0 {
                if len(s.init_values) == 1 && len(s.names) > 1 {
                    // Multi-return destructure: x, y := call()
                    mra := new(Stmt_Multi_Return_Assign)
                    mra.span = s.span
                    mra.type_expr = s.type_expr
                    for n in s.names { append(&mra.names, n) }
                    for v in s.init_values { append(&mra.values, v) }
                    append(&s.checked, Stmt(mra))
                } else {
                    // Parallel or single-name: one Stmt_Assign per name
                    for name, i in s.names {
                        a := new(Stmt_Assign)
                        a.name = name
                        a.span = s.span
                        a.type_expr = s.type_expr
                        a.is_using = s.is_using
                        a.is_decl = true
                        a.slice_cap_expr = s.slice_cap_expr
                        if i < len(s.init_values) { a.value = s.init_values[i] }
                        append(&s.checked, Stmt(a))
                    }
                }
            }
            register_and_check_declarations(c, s.checked, env, owner, public_env)
        case ^Stmt_Assign:
            // Complex LHS (field / index / slice / deref): registration is a
            // no-op — no new binding enters scope. The typing logic runs in
            // check_bodies via per-target-kind dispatch.
            if s.target != nil {
                continue
            }
            // `this_program = Program(...)` is a compiler-managed marker —
            // Phase 0 already extracted the arena type info; the assignment
            // is a no-op at codegen, the storage gets synthesized in main's
            // entry. Skip the regular type-check so the user can write the
            // configuration line without satisfying a strict LHS type.
            if s.name == "this_program" && !s.is_decl { continue }
            // Include expressions: scope-based resolution.
            // mara.X → look up X in std scope (stdlib modules)
            // bare Y → walk scope chain for sibling, lazy-load if not found
            if inc, is_include := s.value.(^Expr_Include); is_include {
                // Bare `use path` — the path is a dotted module name. Resolve
                // it to exactly that module (no parent-glob; submodules are
                // pulled in by their own explicit `use`), load and flatten it.
                matching := find_matching_modules(c, inc.path)
                defer delete(matching)
                if len(matching) == 0 {
                    check_error(c, inc.span, TYPE_MODULE_FOUND, inc.path)
                    continue
                }
                main_mod: Type
                for sub_name in matching {
                    m := check_module(c, sub_name, inc.span)
                    if m == nil { continue }
                    sd := as_scope_body(m)
                    if sd == nil { continue }
                    flatten_module_exports(c, env, sd, sub_name)
                    if inc.is_reexport && pub != env {
                        flatten_module_exports(c, pub, sd, sub_name)
                    }
                    if sub_name == inc.path { main_mod = m }
                }
                // If no file declared exactly `inc.path` but submodules under
                // it were loaded, the synthetic parent scope was created as a
                // side effect (register_in_parent_scopes). Pick it up so
                // `m := use mara` binds m to the synth scope.
                if main_mod == nil {
                    if synth, ok := c.checked_modules[inc.path]; ok {
                        main_mod = synth
                    }
                }
                if main_mod != nil {
                    type_env_set(env, s.name, main_mod)
                    s.var_type = main_mod
                    inc.type_ = main_mod
                    if c.mara_env != nil {
                        type_env_set(c.mara_env, inc.path, main_mod)
                    }
                }
                continue
            }

            // Register variable with its declared or inferred type.
            // We check the value expression here because variable initializers
            // at the same scope level can reference each other's types,
            // and we need to know the type to register it.

            ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)

            // Reject same-scope redeclarations (`x := 5` then `x := 7`) and shadowing
            // of any local binding in an enclosing scope up to the module boundary.
            // Reassignment with `=` is unaffected — those parse as Stmt_Assign with
            // is_decl=false and never reach this branch's Stmt_Decl-derived path.
            if s.is_decl && s.name in env.types {
                check_error(c, s.span, TYPE_VARIABLE_ALREADY_DECLARED_SCOPE, s.name)
                continue
            }
            // Struct field declarations live in their own namespace (accessed
            // via `obj.field`, never as a bare identifier), so they can't
            // shadow file-scope or module-scope bindings. Skip the walk when
            // the immediate parent is a class/struct scope.
            in_struct_body := env.parent != nil && env.parent.class_scope != nil
            if s.is_decl && !env.is_module_scope && !in_struct_body {
                outer := env.parent
                for outer != nil {
                    if outer.is_module_scope { break }
                    if s.name in outer.types {
                        check_error(c, s.span, TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING, s.name)
                        break
                    }
                    outer = outer.parent
                }
            }

            // Nothing can shadow a constant from an outer scope
            if s.name in c.table.constants && s.name not_in env.types {
                check_error(c, s.span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, s.name)
                continue
            }

            // Take binding: `name := take(T, storage)` (or with an annotation).
            // Same alias-into-caller-storage semantics as let — mark the name
            // as a view binding so it can't escape via return.
            if take_expr, is_take := s.value.(^Expr_Take); is_take {
                val_type := check_expr(c, s.value, env)
                // If an annotation was given, it must match take's resolved type.
                if !is_any(ann_type) {
                    if types_incompatible(ann_type, val_type) && !value_preserving_widen(val_type, ann_type) {
                        check_error(c, s.span,
                            TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
                            type_name(val_type), s.name, type_name(ann_type))
                    }
                }
                final_type := ann_type
                if is_any(ann_type) { final_type = val_type }
                s.var_type = distinct_base(final_type)
                s.env_type = final_type
                type_env_set(env, s.name, final_type)
                env.let_names[s.name] = true
                set_provenance(env, s.name, expr_provenance(c, take_expr.storage, env))
                continue
            }

            // Declaration without initializer (e.g. ev : SDL_Event)
            if s.value == nil {
                if _, is_err := ann_type.(Type_Error); is_err {
                    // Type resolution already reported an error — skip further checks
                    s.var_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    continue
                }
                if is_any(ann_type) {
                    check_error(c, s.span, TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE)
                }
                // Big-array check for uninitialized arrays (unwrap distinct)
                base_ann := distinct_base(ann_type)
                if fa, ok := base_ann.(^Type_Fixed_Array); ok {
                    total_bytes := fa.size * checker_type_byte_size(fa.elem)
                    if total_bytes >= 1024 && !c.table.has_scope_allocator && !c.table.context_expected_at_runtime {
                        check_error(c, s.span,
                            TYPE_ARRAY_TOO_LARGE_STACK_BYTES,
                            s.name, total_bytes)
                    }
                }
                // Function type from named source: auto-initialize to the function itself.
                // e.g. `remote_print : game.test_print` → value is game.test_print
                if tf, is_func := ann_type.(^Type_Scope); is_func && len(tf.params) > 0 {
                    if tn, tn_ok := s.type_expr.(Type_Name); tn_ok {
                        dot := strings.index_byte(tn.name, '.')
                        if dot >= 0 {
                            fn_name := resolve_fn_type_name(c, tn.name, env)
                            if fn_name != "" {
                                synth := new(Expr_Ident)
                                synth.name = fn_name
                                synth.span = s.span
                                synth.type_ = ann_type
                                synth.resolved = Resolved_Func{name = fn_name}
                                s.value = synth
                            }
                        }
                    }
                }
                // Sized slice decl `name : []T(N)` — validate N is numeric.
                if s.slice_cap_expr != nil {
                    cap_type := check_expr(c, s.slice_cap_expr, env)
                    if !is_any(cap_type) && !is_numeric(cap_type) {
                        check_error(c, s.span,
                            TYPE_SLICE_CAPACITY_INTEGER, type_name(cap_type))
                    }
                }
                s.var_type = distinct_base(ann_type)
                s.env_type = ann_type
                type_env_set(env, s.name, ann_type)
                set_provenance(env, s.name, prov_local(env)) // uninitialized local is at our depth
                // Track uninitialized pointers/slices — reading before assignment is an error
                base := distinct_base(ann_type)
                if _, is_ptr := base.(^Type_Ptr); is_ptr {
                    env.invalid_refs[s.name] = true
                } else if _, is_slice := base.(^Type_Slice); is_slice {
                    // Sized slices `name : []T(N)` allocate storage at decl time,
                    // so they're not uninitialized.
                    if s.slice_cap_expr == nil {
                        env.invalid_refs[s.name] = true
                    }
                } else if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 {
                    // Track uninit ptr/slice fields inside a struct declared without initializer
                    add_struct_invalid_fields(env, s.name, sd)
                }
                continue
            }

            // Sized slice cap: validate N is numeric and stamp its expression's
            // type before the value check runs. Same shape as the no-initializer
            // branch above; without this, `name : [:N]T = ...` left
            // slice_cap_expr's ident untyped and codegen fell back to i64 loads
            // for the cap, mismatching i32-typed cap variables.
            if s.slice_cap_expr != nil {
                cap_type := check_expr(c, s.slice_cap_expr, env)
                if !is_any(cap_type) && !is_numeric(cap_type) {
                    check_error(c, s.span,
                        TYPE_SLICE_CAPACITY_INTEGER, type_name(cap_type))
                }
            }
            c.expected_hint = ann_type
            val_type := check_expr(c, s.value, env)
            // `#big_endian buf[off]` / `#big_endian buf[lo:hi]` — the flag has
            // no meaning unless the source is a byte buffer. Codegen would
            // silently drop the flag in that case; flag it loudly here.
            if expr_is_big_endian(s.value) {
                src_type: Type
                #partial switch v in s.value {
                case ^Expr_Index: src_type = expr_type(v.expr)
                case ^Expr_Slice: src_type = expr_type(v.expr)
                }
                if !is_byte_buffer(src_type) {
                    check_error(c, s.span, TYPE_BIG_ENDIAN_NEEDS_BYTE_BUFFER,
                        type_name(src_type))
                }
            }
            // Reject single-name binding from a multi-return call. Without
            // this, the binding would silently take on the call's primary
            // (first) return type and the user would lose the rest with no
            // diagnostic. `x, y := f()` (multi-return assign) is the supported
            // form — that path goes through Stmt_Multi_Return_Assign.
            if s.is_decl {
                if returns := call_return_list(c, s.value, env); len(returns) > 1 {
                    check_error(c, s.span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE,
                        1, len(returns))
                    type_env_set(env, s.name, Type_Error{})
                    continue
                }
            }
            // Reject copies of structs whose layout transitively contains a
            // partial-array field. A byte-for-byte copy of such a struct would
            // leave the inner partial array's `ptr` still aliasing the source's
            // elements — subsequent reads/writes through the copy would silently
            // hit (and clobber) the source. Only flag when the RHS is reading
            // from existing storage (ident or field access); literals and calls
            // construct in place and are fine.
            is_copy_source := false
            if _, ok := s.value.(^Expr_Ident); ok { is_copy_source = true }
            if _, ok := s.value.(^Expr_Field_Access); ok { is_copy_source = true }
            if is_copy_source && struct_contains_partial_array(val_type) {
                check_error(c, s.span,
                    TYPE_CANNOT_COPY_VALUE_CONTAINS_PARTIAL,
                    type_name(val_type))
            }
            if !is_any(ann_type) {
                // If ann_type is distinct and val_type is NOT a literal (array/struct),
                // skip structural checks — use nominal comparison directly.
                // Also take the nominal path when the literal already produced a
                // matching distinct type (e.g. `bar : Vec3 = Vec3{1,2,3}`): the
                // RHS constructor's check_array_struct_literal validated element
                // shape and returned ^Type_Distinct, so the unwrap-to-base path
                // would wrongly reject the tagged value against the bare array.
                _, ann_is_distinct := ann_type.(^Type_Distinct)
                _, val_is_array := s.value.(^Expr_Array)
                _, val_is_struct_lit := s.value.(^Expr_Struct_Literal)
                val_carries_matching_distinct := ann_is_distinct && types_equal(ann_type, val_type)
                if ann_is_distinct && (!val_is_array && !val_is_struct_lit || val_carries_matching_distinct) {
                    // Byte-buffer reinterpret read overrides the nominal type
                    // match — `win : sdl.Window = mem[0]` reads sizeof(Window)
                    // bytes regardless of the distinct wrapper.
                    is_byte_read := is_byte_buffer(val_type) || is_byte_buffer_index_read(s.value)
                    if is_byte_read {
                        if sl, ok := s.value.(^Expr_Slice); ok {
                            if low_num, low_ok := const_eval_int(sl.low); low_ok {
                                if high_num, high_ok := const_eval_int(sl.high); high_ok {
                                    span_size := high_num - low_num
                                    ann_size := checker_type_byte_size(ann_type)
                                    if span_size != ann_size {
                                        check_error(c, s.span,
                                            TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                            type_name(ann_type), ann_size, span_size)
                                    }
                                }
                            }
                        }
                    } else if !coerce_deferred(c, val_type, ann_type, s.span) && types_incompatible(ann_type, val_type) && !value_preserving_widen(val_type, ann_type) {
                        emit_assign_var_error(c, s.span, val_type, s.name, ann_type, s.value)
                    }
                    if is_infer(val_type) {
                        check_literal_overflow(c, s.value, ann_type, s.span)
                    }
                    s.var_type = distinct_base(ann_type)
                    s.env_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    set_provenance(env, s.name, expr_provenance(c, s.value, env))
                    continue
                }
                // Unwrap distinct types for structural checking (but store the distinct type)
                check_ann := distinct_base(ann_type)
                // Validate assignment compatibility (same as in check_assign)
                if sd := as_scope_body(check_ann); sd != nil && len(sd.fields) > 0 {
                    check_struct_literal_assign(c, s.span, s.value, sd, env)
                    // Byte-buffer reinterpret read into a struct (slice form): a
                    // span shorter than the struct is a partial fill (tail zero);
                    // only a span LARGER than the struct overruns it -> error.
                    if sl, sl_ok := s.value.(^Expr_Slice); sl_ok && (is_byte_buffer(val_type) || is_byte_buffer_index_read(s.value)) {
                        if low_num, low_ok := const_eval_int(sl.low); low_ok {
                            if high_num, high_ok := const_eval_int(sl.high); high_ok {
                                span_size := high_num - low_num
                                ann_size := checker_type_byte_size(check_ann)
                                if span_size > ann_size {
                                    check_error(c, s.span,
                                        TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                        type_name(check_ann), ann_size, span_size)
                                }
                            }
                        }
                    }
                    s.var_type = distinct_base(ann_type)
                    s.env_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    set_provenance(env, s.name, prov_local(env)) // struct literal is local
                    // Track uninit ptr/slice fields not provided in the literal
                    if lit, lit_ok := s.value.(^Expr_Struct_Literal); lit_ok {
                        provided: map[string]bool
                        for field in lit.fields { provided[field.name] = true }
                        add_struct_invalid_fields(env, s.name, sd, provided)
                    }
                    continue
                }
                if ut, ok := check_ann.(^Type_Union); ok {
                    check_union_literal_assign(c, s.span, s.value, ut, env)
                    s.var_type = distinct_base(ann_type)
                    s.env_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    set_provenance(env, s.name, prov_local(env)) // union literal is local
                    continue
                }
                if fa, ok := check_ann.(^Type_Fixed_Array); ok {
                    // Byte-buffer reinterpret read into a fixed-array destination:
                    // `arr : [2]byte = bytes[0]` reads sizeof([2]byte) = 2 bytes
                    // from `bytes` at offset 0. Same shape as the scalar
                    // reinterpret-read paths below, generalized: destination
                    // type drives read size, fixed-array fits the pattern.
                    is_byte_reinterpret := is_byte_buffer_index_read(s.value) || is_byte_buffer(val_type)
                    if is_byte_reinterpret {
                        if sl, sl_ok := s.value.(^Expr_Slice); sl_ok {
                            ann_size := checker_type_byte_size(check_ann)
                            if low_num, low_ok := const_eval_int(sl.low); low_ok {
                                if high_num, high_ok := const_eval_int(sl.high); high_ok {
                                    span_size := high_num - low_num
                                    // Aggregate target: a shorter span partial-fills
                                    // (tail zero); only an over-large span errors.
                                    if span_size > ann_size {
                                        check_error(c, s.span,
                                            TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                            type_name(check_ann), ann_size, span_size)
                                    }
                                }
                            }
                        }
                    } else {
                        check_array_assign(c, s.span, s.name, fa, val_type)
                    }
                    // Big-array check: require scope allocator for large stack arrays
                    total_bytes := fa.size * checker_type_byte_size(fa.elem)
                    if total_bytes >= 1024 && !c.table.has_scope_allocator && !c.table.context_expected_at_runtime {
                        check_error(c, s.span,
                            TYPE_ARRAY_TOO_LARGE_STACK_BYTES,
                            s.name, total_bytes)
                    }
                } else if pa, ok := check_ann.(^Type_Partial_Array); ok && is_byte_buffer(val_type) {
                    // Partial-array byte-buffer reinterpret read:
                    //   arr : [..N]T = bytes[lo:hi]
                    // Source bytes must divide evenly by sizeof(T) and yield
                    // at most N elements. Runtime sets arr.len += (count read);
                    // cap stays at the compile-time N.
                    elem_size := checker_type_byte_size(pa.elem)
                    backing_bytes := pa.size * elem_size
                    if sl, sl_ok := s.value.(^Expr_Slice); sl_ok {
                        if low_num, low_ok := const_eval_int(sl.low); low_ok {
                            if high_num, high_ok := const_eval_int(sl.high); high_ok {
                                span_size := high_num - low_num
                                if elem_size > 0 && span_size % elem_size != 0 {
                                    check_error(c, s.span,
                                        TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                        type_name(check_ann), backing_bytes, span_size)
                                } else if span_size > backing_bytes {
                                    check_error(c, s.span,
                                        TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                        type_name(check_ann), backing_bytes, span_size)
                                }
                            }
                        }
                    }
                } else if is_byte_buffer(val_type) {
                    // Byte buffer reinterpret read: x : i64 = mem[0:8]
                    // Works for []byte, [N]byte, and Array(byte, N) (post-desugar source)
                    ann_size := checker_type_byte_size(check_ann)
                    if sl, ok := s.value.(^Expr_Slice); ok {
                        if low_num, low_ok := const_eval_int(sl.low); low_ok {
                            if high_num, high_ok := const_eval_int(sl.high); high_ok {
                                span_size := high_num - low_num
                                if span_size != ann_size {
                                    check_error(c, s.span,
                                        TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                        type_name(check_ann), ann_size, span_size)
                                }
                            }
                        }
                    }
                } else if is_byte_buffer_index_read(s.value) {
                    // Byte buffer reinterpret read via index: x : int = mem[0]
                    // Size comes from the annotation type; bounds checked at runtime
                } else if !coerce_deferred(c, val_type, ann_type, s.span) && types_incompatible(ann_type, val_type) && !value_preserving_widen(val_type, ann_type) {
                    emit_assign_var_error(c, s.span, val_type, s.name, ann_type, s.value)
                }
                // Tag `&buf[i]` widened from ^byte to a typed pointer so codegen
                // emits a runtime bounds check against the byte buffer's capacity.
                maybe_stamp_byte_view(c, ann_type, s.value)
                // Check that infer literals fit in the target type
                if is_infer(val_type) {
                    check_literal_overflow(c, s.value, ann_type, s.span)
                }
                s.var_type = distinct_base(ann_type)
                s.env_type = ann_type
                type_env_set(env, s.name, ann_type)
                set_provenance(env, s.name, expr_provenance(c, s.value, env))
                mark_local_slice_backed_if_needed(c, env, s.name, s.value)
                update_alias_from_value(env, s.name, s.value)
                // Pointer-typed and assigned `void` (the null literal) is
                // semantically "no usable value yet" — same definition as
                // declared-without-initializer. Route through the existing
                // invalid_refs path so the deref check at the Expr_Ident site
                // catches it with the same error.
                if _, is_ptr := distinct_base(ann_type).(^Type_Ptr); is_ptr {
                    if is_void_literal(s.value) {
                        env.invalid_refs[s.name] = true
                    }
                }
            } else {
                // No type annotation: variables solidify.
                // But DON'T overwrite if the variable already has a declared type
                // (e.g. verts2 += [...] should not replace verts2's [6]f32 type).
                //
                // Struct field declarations live in their own namespace, so a
                // `field := value` decl shouldn't be misread as a reassignment of
                // a same-named binding in an outer file / module scope. Suppress
                // the walk-up lookup when we're directly inside a struct body.
                in_struct_body := env.parent != nil && env.parent.class_scope != nil
                // Un-annotated struct field: adopt the finalized layout width
                // (resolved in the register pass) for numeric fields, so the
                // constructor local's var_type matches the field slot codegen
                // GEPs into. Slice/struct fields fall through to the normal decl
                // path (which sets up slice-backing / aliasing).
                if in_struct_body {
                    if cs := env.parent.class_scope; cs != nil {
                        if idx, fm := cs.field_map[s.name]; fm && idx < len(cs.fields) && is_numeric(cs.fields[idx].type_) {
                            lt := cs.fields[idx].type_
                            s.var_type = distinct_base(lt)
                            s.env_type = lt
                            type_env_set(env, s.name, lt)
                            if is_infer(val_type) {
                                check_literal_overflow(c, s.value, lt, s.span)
                            }
                            continue
                        }
                    }
                }
                existing_type: Type
                loc_env: ^Type_Env
                already_declared: bool
                if in_struct_body {
                    if t, ok := env.types[s.name]; ok {
                        existing_type = t
                        loc_env = env
                        already_declared = true
                    }
                } else if s.is_decl {
                    // Declarations skip module-scope bindings: function bodies
                    // are free to shadow module-level names (including the
                    // module's own self-binding, e.g. `shader` inside
                    // `module gfx.shader`). Matches the shadowing-check
                    // policy at the top of this branch.
                    existing_type, loc_env, already_declared = type_env_locate_below_module(env, s.name)
                } else {
                    existing_type, loc_env, already_declared = type_env_locate(env, s.name)
                }
                // Field-leak guard: reassignment targeting a name that lives in
                // an ancestor class scope is a field written without receiver.
                if already_declared && loc_env != env && loc_env.class_scope != nil {
                    if is_real_field(&loc_env.class_scope.sd, s.name) {
                        check_error(c, s.span,
                            TYPE_FIELD_ASSIGN_THROUGH_RECEIVER,
                            s.name, loc_env.class_scope.name, s.name)
                        continue
                    }
                }
                if !already_declared {
                    // `x := #skip_constructor` has no type to infer from. Require
                    // an explicit annotation: `x : T = #skip_constructor`.
                    if _, is_skip := s.value.(^Expr_Skip_Constructor); is_skip {
                        check_error(c, s.span, TYPE_TYPE_SKIP_CONSTRUCTOR_REQUIRES_EXPLICIT, s.name, s.name)
                        type_env_set(env, s.name, Type_Error{})
                        continue
                    }
                    // Deferred inference: an un-annotated binding whose
                    // initializer is still open (untyped literal/const, or
                    // another open binding) gets a fresh inference cell rather
                    // than solidifying to i64 here — its width is decided by the
                    // first concrete use; unbound at codegen → i64/f64.
                    binding_type: Type
                    if is_infer(val_type) {
                        cell := new(Infer_Cell)
                        cell.name = s.name
                        cell.span = s.span
                        if src := infer_cell_of(val_type); src != nil {
                            unify_infer_cells(c, cell, src, s.span)  // `y := x`: co-resolve
                        }
                        if _, is_f := val_type.(Type_Infer_Float); is_f {
                            binding_type = Type_Infer_Float{cell = cell}
                        } else {
                            binding_type = Type_Infer_Int{cell = cell}
                        }
                    } else {
                        binding_type = solidify_type(val_type)
                        if is_untyped(binding_type) {
                            check_warning(c, s.span, TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING, s.name)
                        }
                    }
                    s.var_type = distinct_base(binding_type)
                    s.env_type = binding_type
                    type_env_set(env, s.name, binding_type)
                    set_provenance(env, s.name, expr_provenance(c, s.value, env))
                    mark_local_slice_backed_if_needed(c, env, s.name, s.value)
                    update_alias_from_value(env, s.name, s.value)
                    if _, is_ptr := distinct_base(binding_type).(^Type_Ptr); is_ptr {
                        if is_void_literal(s.value) {
                            env.invalid_refs[s.name] = true
                        }
                    }
                } else {
                    // Reassignment: pointers assigned `void` re-enter the
                    // uninit pool; anything else clears them.
                    is_ptr := false
                    if _, ok := distinct_base(existing_type).(^Type_Ptr); ok { is_ptr = true }
                    if is_ptr && is_void_literal(s.value) {
                        env.invalid_refs[s.name] = true
                        // Don't clear field-uninit either — but this branch
                        // only applies to scalar ptrs anyway.
                    } else {
                        // Reassignment: mark as initialized (clears invalid_refs for ptr/slice)
                        mark_initialized(env, s.name)
                        // Also clear any field-level uninit entries (whole struct reassignment)
                        clear_struct_invalid_fields(env, s.name)
                    }
                    // Reassignment: check value type matches existing variable type.
                    // A byte-buffer reinterpret read (off16 = mem[off] or mem[lo:hi])
                    // is recognized here too — same as the decl-init and field-assign
                    // paths: the read size comes from the target type, not the byte
                    // value. Without this the RHS types as a bare `byte` and fails.
                    is_byte_reinterpret := is_byte_buffer(val_type) || is_byte_buffer_index_read(s.value)
                    if !is_byte_reinterpret && !coerce_deferred(c, val_type, existing_type, s.span) && !coerce_deferred(c, existing_type, val_type, s.span) && types_incompatible(existing_type, val_type) && !value_preserving_widen(val_type, existing_type) {
                        emit_assign_var_error(c, s.span, val_type, s.name, existing_type, s.value)
                    }
                    maybe_stamp_byte_view(c, existing_type, s.value)
                    if is_infer(val_type) {
                        check_literal_overflow(c, s.value, existing_type, s.span)
                    }
                    s.var_type = distinct_base(existing_type)
                    s.env_type = existing_type
                    set_provenance(env, s.name, expr_provenance(c, s.value, env))
                    update_alias_from_value(env, s.name, s.value)
                }
            }
        case ^Stmt_Multi_Assign:
            // Wrapper of individual assigns — check each one
            inner: [dynamic]Stmt
            for a in s.assigns { append(&inner, Stmt(a)) }
            register_and_check_declarations(c, inner, env, public_env = public_env)
        case ^Stmt_Multi_Return_Assign:
            ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)

            if len(s.values) == 1 {
                // Detect Expr_Try wrapping a multi-return call: `x, y := foo()?`.
                // The trailing err is consumed by propagation; the LHS binds
                // the remaining values. We bypass check_expr on the Try here
                // because check_try restricts single-bind to 0 or 1 non-err
                // values — the destructure context is precisely where 2+
                // non-err values is legal.
                try_node, is_try := s.values[0].(^Expr_Try)
                inner_call: ^Expr_Call
                if is_try {
                    inner_call, _ = try_node.inner.(^Expr_Call)
                }

                if is_try && inner_call != nil {
                    check_call(c, inner_call, env)
                    returns := call_return_list(c, inner_call, env)
                    if len(returns) == 0 || !is_err_type(returns[len(returns)-1]) {
                        check_error(c, s.span, TYPE_TRY_REQUIRES_ERR_RETURN)
                    } else if len(env.return_types) == 0 || !is_err_type(env.return_types[len(env.return_types)-1]) {
                        check_error(c, s.span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
                    } else {
                        non_err := returns[:len(returns)-1]
                        // Set Try's type to the first non-err return so any
                        // downstream code reading it (codegen) has a sensible
                        // value. The full destructure uses call_return_list.
                        if len(non_err) > 0 {
                            set_expr_type(try_node, non_err[0])
                        } else {
                            set_expr_type(try_node, Type_Void{})
                        }
                        if len(s.names) != len(non_err) {
                            check_error(c, s.span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE,
                                len(s.names), len(non_err))
                        } else {
                            for name, i in s.names {
                                resolved_type := solidify_type(non_err[i])
                                if name != "" {
                                    type_env_set(env, name, resolved_type)
                                } else if i < len(s.targets) && s.targets[i] != nil {
                                    target_type := check_expr(c, s.targets[i], env)
                                    if !is_any(target_type) && !is_any(resolved_type) {
                                        if !types_equal(target_type, resolved_type) {
                                            check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_RETURN,
                                                type_name(resolved_type), type_name(target_type))
                                        }
                                    }
                                }
                                append(&s.var_types, distinct_base(resolved_type))
                            }
                        }
                    }
                } else {
                    // Single RHS (multi-return call): x, y := call()
                    val_type := check_expr(c, s.values[0], env)
                    // Source the return arity from the resolved fun directly —
                    // there is no tuple value on the frontend. The call must be
                    // an Expr_Call whose callee is a multi-return fun.
                    returns := call_return_list(c, s.values[0], env)
                    if returns != nil {
                        if len(s.names) != len(returns) {
                            check_error(c, s.span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE,
                                len(s.names), len(returns))
                        } else {
                            for name, i in s.names {
                                resolved_type := solidify_type(returns[i])
                                if name != "" {
                                    type_env_set(env, name, resolved_type)
                                } else if i < len(s.targets) && s.targets[i] != nil {
                                    target_type := check_expr(c, s.targets[i], env)
                                    if !is_any(target_type) && !is_any(resolved_type) {
                                        if !types_equal(target_type, resolved_type) {
                                            check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_RETURN,
                                                type_name(resolved_type), type_name(target_type))
                                        }
                                    }
                                }
                                append(&s.var_types, distinct_base(resolved_type))
                            }
                        }
                    } else if is_any(val_type) {
                        for name in s.names {
                            if name != "" {
                                type_env_set(env, name, Type_Error{})
                            }
                        }
                    } else {
                        // Broadcast: `a, b = single_value` — store the same value
                        // into every target. Each target must accept val_type. New
                        // names get val_type bound. Expression targets get type-
                        // checked against val_type for compatibility. The
                        // codegen path uses is_broadcast to choose the right
                        // generation (one RHS eval, N stores).
                        s.is_broadcast = true
                        target_val_type := distinct_base(val_type)
                        for name, i in s.names {
                            if name != "" {
                                type_env_set(env, name, val_type)
                                append(&s.var_types, target_val_type)
                            } else if i < len(s.targets) && s.targets[i] != nil {
                                target_type := check_expr(c, s.targets[i], env)
                                if !is_any(target_type) && types_incompatible(target_type, val_type) {
                                    check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_RETURN,
                                        type_name(val_type), type_name(target_type))
                                }
                                append(&s.var_types, distinct_base(target_type))
                            } else {
                                append(&s.var_types, target_val_type)
                            }
                        }
                    }
                }
            }
        case ^Stmt_Dispatch_Def:
            if s.name not_in c.dispatch_groups {
                c.dispatch_groups[s.name] = {}
            }
            for f in s.functions {
                append(&c.dispatch_groups[s.name], f)
            }
        case Stmt_Overload:
            if s.op not_in c.operator_overloads {
                c.operator_overloads[s.op] = {}
            }
            append(&c.operator_overloads[s.op], s.dispatch_name)
        case Stmt_Module:
            // Module declaration — nothing to register
        }
    }
}

// ---------------------------------------------------------------------------
// Pass 2: Check all statement bodies (descend into child scopes)
// ---------------------------------------------------------------------------

check_struct_defaults :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env) {
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            if len(s.typed_params) > 0 { continue } // only funs with fields have struct defaults
            if len(s.generic_params) > 0 { continue }
            st_name := make_flat_name(c.current_package, s.name)
            sd: ^Scope_Body
            if ss, ss_ok := c.table.structs[st_name]; ss_ok {
                sd = &ss.sd
            } else if sf, sf_ok := c.table.funs[st_name]; sf_ok {
                sd = &sf.sd
            }
            if sd == nil { continue }
            for &field in sd.fields {
                if field.default_value == nil { continue }
                // Broadcast literal targeting a fixed- or partial-array field:
                // expand `{all <expr>}` into per-slot entries on the literal so
                // codegen can emit element-by-element stores. Handles the case
                // `cameras: [..6]Camera = {all Camera(1280, 720, 90)}`.
                if lit, lit_ok := field.default_value.(^Expr_Struct_Literal); lit_ok && lit.is_broadcast {
                    expand_broadcast_array_literal(c, lit, field.type_, field.name, s.span, env)
                    continue
                }
                dt := check_expr(c, field.default_value, env)
                if types_incompatible(field.type_, dt) && !is_any(dt) {
                    check_error(c, s.span, TYPE_DEFAULT_VALUE_FIELD_EXPECTED,
                        field.name, type_name(field.type_), type_name(dt))
                }
            }
        }
    }
}

// Expand `{all <expr>}` into per-element entries on `lit.array_values`. The
// expression is type-checked once against the array's element type; codegen
// emits N independent stores (clones share the same checked AST node).
expand_broadcast_array_literal :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, field_type: Type, field_name: string, span: Span, env: ^Type_Env) {
    size := 0
    elem_type: Type
    base := distinct_base(field_type)
    if fa, ok := base.(^Type_Fixed_Array); ok {
        size = fa.size
        elem_type = fa.elem
    } else if pa, ok := base.(^Type_Partial_Array); ok {
        size = pa.size
        elem_type = pa.elem
    } else {
        check_error(c, span,
            TYPE_BROADCAST_LITERAL_ALL_FIELD_REQUIRES,
            field_name, type_name(field_type))
        return
    }
    val_type := check_expr(c, lit.broadcast_value, env)
    if !is_any(val_type) && types_incompatible(elem_type, val_type) {
        check_error(c, span,
            TYPE_BROADCAST_VALUE_FIELD_TYPE_EXPECTED,
            field_name, type_name(val_type), type_name(elem_type), type_name(field_type))
        return
    }
    if is_infer(val_type) {
        check_literal_overflow(c, lit.broadcast_value, elem_type, span)
    }
    clear(&lit.array_values)
    resize(&lit.array_values, size)
    for i in 0..<size {
        if i == 0 {
            lit.array_values[0] = lit.broadcast_value
        } else {
            // clone_expr clears `resolved_func` and `type_` on each Expr_Call
            // it copies — re-run check_expr so each clone has its own
            // resolution before codegen sees it.
            cloned := clone_expr(lit.broadcast_value)
            check_expr(c, cloned, env)
            lit.array_values[i] = cloned
        }
    }
    lit.type_ = field_type
}

// Phase-2 checker for a single function/method/struct/module body.
// check_scope_body resolves a scope's signature (fields/params/return) and
// then — unless signature_only is set — checks the body. Set signature_only
// from the Phase-2 pre-pass to populate struct fields before any function
// body is checked, so forward references to structs work regardless of
// declaration order.
check_scope_body :: proc(c: ^Checker, s: ^Stmt_Scope, env: ^Type_Env, signature_only: bool = false) {
    if len(s.generic_params) > 0 { return }
    if s.is_intrinsic {
        // Body is compiler-generated. Validate the declared signature against
        // the LLVM intrinsic's expected shape (arity + element types).
        if !signature_only {
            fun_type_raw, _ := type_env_get(env, s.name)
            if ft, ft_ok := fun_type_raw.(^Type_Scope); ft_ok {
                check_llvm_intrinsic_signature(c, ft, s.intrinsic_name, s.span)
            }
        }
        return
    }
    // Owned-first lookup: when checking the body of `Timer :: struct {...}`,
    // a per-file env's includes (e.g. an open `sdl :: include mara.sdl2`)
    // can shadow the struct's own Type_Scope with an unrelated enum-variant
    // entry (Init_Flags.Timer). Without owned-first, the bare lookup would
    // return Init_Flags, ft_ok would fail, and the function would silently
    // bail — leaving the struct's fields uninitialized.
    fun_type_raw, _ := type_env_get_owned_first(env, s.name)

    ft, ft_ok := fun_type_raw.(^Type_Scope)
    if !ft_ok { return }

    // Env structure for callable scopes:
    //
    //   class:   [ns_env: Self/types/methods/consts] <- [child: params/lets/body]
    //   fun:                                            [child: Self/own-types/funcs/params/body]
    //   method:  [class's ns_env, already on chain]  <- [child: own-types/funcs/params/body]
    //
    // The class's namespace and its constructor body are distinct envs: the
    // namespace holds the shared surface (Self, nested types, sibling methods,
    // constants) and is the parent of both the constructor body and any method
    // bodies. The constructor body env adds constructor-only bindings (params,
    // class-body `let`/`:=` decls) without leaking them to siblings.
    //
    // For a method's recursive check_scope_body call, env is the class body
    // env, env.class_scope is nil, env.parent is the class ns_env (where
    // class_scope was set). Detecting this lets us reparent past the class body.
    is_method := ft.kind == .Fun && env.class_scope == nil && env.parent != nil && env.parent.class_scope != nil

    ns_env: Type_Env
    parent_env := env
    if ft.kind == .Struct {
        ns_env = type_env_child(env)
        ns_env.class_scope = ft
        type_env_set(&ns_env, "Self", ft)
        if ft.types != nil {
            for bare, t in ft.types { type_env_set(&ns_env, bare, t) }
        }
        if ft.functions != nil {
            for bare, fn in ft.functions {
                if fn != nil { type_env_set(&ns_env, bare, fn) }
            }
        }
        parent_env = &ns_env
    } else if is_method {
        parent_env = env.parent
    } else if ft.kind == .Fun {
        // Nested funs (e.g., `loop_iter :: fun(...)` inside another function
        // body) get lifted to module scope at codegen — see
        // extract_scope_fun_defs. The env chain should reflect that: walk
        // past enclosing function bodies to the file env, so the inner fun
        // sees module-level decls + per-file includes but not the outer
        // function's locals. Without this, the shadow check at
        // register_and_check_declarations finds outer locals and rejects
        // legitimate same-name decls in the inner fun.
        walk := env
        for walk != nil && walk.parent != nil && !walk.parent.is_module_scope {
            walk = walk.parent
        }
        if walk != nil {
            parent_env = walk
        }
    }

    child := type_env_child(parent_env)
    // Function bodies open a new stack frame for escape analysis. Class
    // bodies are just namespaces — fields don't live at a deeper depth.
    if ft.kind == .Fun {
        child.scope_depth = parent_env.scope_depth + 1
    }
    // Top-level functions get Self / their own ft.types / ft.functions on the body
    // env directly. Methods reach the class's Self via parent walk-up. For classes,
    // these all live on ns_env above.
    if ft.kind == .Fun && !is_method {
        type_env_set(&child, "Self", ft)
    }
    // A struct's nested defs are registered into ft.types during module
    // registration (register_scope_defs); a function's are NOT. Without that,
    // a body-local type used in the function's own local declarations — e.g.
    // `nodes : [..N]Node` where `Node :: struct {…}` is defined in the same
    // body — can't be resolved by the field loop below (it runs before the
    // body pass that would otherwise hoist these). Register them here, ahead
    // of that loop, mirroring the struct path. The ft.types guard keeps a
    // re-entry from re-mangling the nested names. (TTF is the precedent that
    // register_scope_defs + the later body pass coexist safely.)
    if ft.kind == .Fun && ft.types == nil && len(s.body) > 0 {
        register_scope_defs(c, ft, &ft.sd, s.body, parent_env)
    }
    if ft.kind == .Fun {
        if ft.types != nil {
            for bare, t in ft.types { type_env_set(&child, bare, t) }
        }
        if ft.functions != nil {
            for bare, fn in ft.functions {
                if fn != nil { type_env_set(&child, bare, fn) }
            }
        }
    }

    // Pre-register struct params in the field-resolution scope so that
    // field defaults / field types can reference them (e.g.
    // `max_vertices := max_v` or `using items: [n]item`).
    if ft.kind == .Struct {
        for p in ft.params {
            type_env_set(&child, p.name, p.type_)
        }
    }

    // Shape-shortcut pre-pass: rewrite `p : Foo(Bar(args))` decls in the
    // body to `p : Foo(Bar)` plus a synthesized init. Must precede the
    // field-resolution loop below — that loop resolves each Stmt_Decl's
    // type_expr and would otherwise hit the un-desugared Type_Const_Expr
    // and fail the shape-constraint check with a "got vla" diagnostic.
    for stmt in s.body {
        if d, ok := stmt.(^Stmt_Decl); ok {
            desugar_shape_shortcut(c, d)
        }
    }

    // Phase 2: resolve data fields (Phase 1 may have already registered
    // nested types as pseudo-fields, so append per-field rather than
    // gated on empty .fields).
    data_fields := s.fields if len(s.fields) > 0 else extract_fields_from_body(s.body)
    added_any_field := false
    // Register-pass flag: `fn <name>` annotations may reference later locals
    // that haven't been added to env yet. Suppress errors during this scan;
    // the body-check pass re-resolves with all locals visible.
    prev_in_register := c.in_register_pass
    c.in_register_pass = true
    defer c.in_register_pass = prev_in_register
    for field in data_fields {
        if _, already := ft.field_map[field.name]; already { continue }
        field_type: Type
        if field.type_expr != nil {
            field_type = resolve_type_expr(field.type_expr, c, s.span, env=&child)
            if field.default_value == nil {
                check_uninitialized_class_decl(c, s.span, field.name, field_type)
            } else if is_numeric(field_type) {
                // Pin earlier deferred fields feeding this annotated field's
                // default to its width: `per_row : i32 = size / cell` settles
                // size and cell at i32.
                pin_field_refs(c, field.default_value, field_type, ft, s.span)
            }
        } else if field.default_value != nil {
            if _, is_uninit := field.default_value.(^Expr_Skip_Constructor); is_uninit {
                check_error(c, s.span, TYPE_FIELD_TYPE_SKIP_CONSTRUCTOR_REQUIRES, field.name, field.name)
                field_type = Type_Error{}
            } else {
                field_type = infer_field_type_from_default(c, field.default_value, &child, ft)
            }
        } else {
            field_type = Type_Any{}
        }
        if field.is_using {
            if _, fa_ok := field_type.(^Type_Fixed_Array); fa_ok {
                // array class — validated below
            } else if using_sd := as_scope_body(field_type); using_sd == nil || len(using_sd.fields) == 0 {
                check_error(c, s.span, TYPE_USING_FIELD_STRUCT_FIXED_ARRAY, field.name)
            }
        }
        // Tag a freshly-minted field cell with its name/span for diagnostics.
        if cell := infer_cell_of(field_type); cell != nil && cell.name == "" {
            cell.name = field.name
            cell.span = s.span
        }
        append(&ft.fields, Struct_Type_Field{name = field.name, type_ = field_type, default_value = field.default_value, is_using = field.is_using})
        added_any_field = true
    }
    if added_any_field {
        build_field_map(&ft.sd)
    }
    // Finalize deferred field-default widths: resolve each inference cell to its
    // pinned width (or i64/f64 if never pinned). After this the layout is
    // concrete, so external `obj.field` readers — checked in a later pass —
    // never see a pinnable cell (which would be unsound cross-scope adoption).
    for &f in ft.fields {
        f.type_ = solidify_type(f.type_)
    }
    if len(ft.params) == 0 && len(s.typed_params) > 0 {
        for tp in s.typed_params {
            pt := resolve_type_expr(tp.type_expr, c, s.span, env=&child)
            append(&ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
        }
        build_param_map(ft)
    }
    if len(ft.return_types) == 0 && len(s.return_types) > 0 {
        for rte in s.return_types {
            rt := resolve_type_expr(rte, c, s.span, env=&child)
            append(&ft.return_types, rt)
        }
    }

    // Recurse into nested struct definitions so their field lists are populated
    // too — a sibling field default or a forward-referencing outer function that
    // reaches `x.nested.field` needs the nested type's fields, not just its name.
    // Mirrors the module-level signature hoist (check_module Pass 2a), one level
    // down. Idempotent: the field loop skips already-mapped fields.
    for stmt in s.body {
        if nested, ok := stmt.(^Stmt_Scope); ok && nested.kind == .Struct &&
            len(nested.typed_params) == 0 && len(nested.generic_params) == 0 {
            check_scope_body(c, nested, &child, signature_only = true)
        }
    }

    // Pre-pass bails here — signature resolved, body deferred to main pass.
    if signature_only { return }

    if len(s.body) == 0 { return }

    // Footgun check (struct only): warn when a field initializer hands
    // #self to anything that could read partially-constructed state
    // while later field decls still come below it. Lives after the
    // signature_only bail so it fires once per struct (the pre-pass and
    // full pass both reach this function — only the full pass continues
    // past the bail).
    if ft.kind == .Struct {
        check_early_self_decls(c, s.body)
    }

    // Register params in scope
    clear(&child.return_types)
    for rt in ft.return_types { append(&child.return_types, rt) }
    child.fn_name = s.name
    for tp, i in s.typed_params {
        if i < len(ft.params) {
            type_env_set(&child, tp.name, ft.params[i].type_)
            child.param_names[tp.name] = true
        }
    }

    // Register named return bindings as fields in the function scope
    for rb in s.return_bindings {
        rb_type := resolve_type_expr(rb.type_expr, c, s.span, env=&child)
        type_env_set(&child, rb.name, rb_type)
    }

    // Pre-register constants with bare-name aliases for sibling access.
    // ft.consts maps bare → ^Stmt_Define (s.name has been mangled by
    // register_scope_defs at this point, so we register both forms).
    // For classes, the canonical home is the namespace env so methods reach
    // them via walk-up. We also mirror onto child (the constructor body env)
    // so check_define's "already pre-registered" early-return — which checks
    // pub.types directly without walking — still recognises them.
    if ft.consts != nil {
        for bare, def in ft.consts {
            if def.value == nil { continue }
            val_type := check_expr(c, def.value, &child)
            def.var_type = val_type
            c.table.constants[def.name] = def.value
            c.table.constants[bare] = def.value
            type_env_set(&child, def.name, val_type)
            type_env_set(&child, bare, val_type)
            if ft.kind == .Struct {
                type_env_set(&ns_env, def.name, val_type)
                type_env_set(&ns_env, bare, val_type)
            }
        }
    }

    check_scope(c, s.body, &child)

    // Return check — void functions (return_types empty) don't need return statements.
    // Functions whose return slots are all err can also fall off the end —
    // each slot gets implicitly filled with `.Ok`.
    if len(ft.return_types) > 0 && !is_any(ft.return_types[0]) && !always_returns(s.body) {
        if !all_err_returns(ft.return_types) {
            check_error(c, s.span, TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, s.name)
        }
    }
}

// True when every return slot is err-typed — the function can fall off the
// end and each slot gets implicitly filled with `.Ok`.
all_err_returns :: proc(types: [dynamic]Type) -> bool {
    if len(types) == 0 { return false }
    for t in types {
        if !is_err_type(t) { return false }
    }
    return true
}

// Phase-2 checker for a `for` statement: dispatches to collection-for, range-for, or C-style.
check_for_body :: proc(c: ^Checker, s: ^Stmt_For, env: ^Type_Env) {
    child := type_env_child(env)
    if s.is_collection_for {
        coll_type := check_expr(c, s.collection, &child)

        elem_type: Type
        switch ct in coll_type {
        case ^Type_Fixed_Array:
            elem_type = ct.elem
        case ^Type_Slice:
            elem_type = ct.elem
        case ^Type_Partial_Array:
            elem_type = ct.elem
        case ^Type_Scope:
            check_error(c, s.span, TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE, ct.name)
            elem_type = Type_Error{}  // error recovery: suppress cascades (Type_Any would lower to i64)
        case Type_F64, Type_Infer_Int, Type_Infer_Float, Type_Bool,
             Type_CString, Type_C8, Type_Utf8, Type_Byte, Type_Numeric,
             ^Type_Ptr, ^Type_Enum, ^Type_Union, ^Type_Distinct,
             Type_Const_Int, Type_Runtime_Size, Type_Any, Type_Void, Type_Error, Type_Err,
             nil:
            check_error(c, s.span, TYPE_CANNOT_ITERATE_OVER_TYPE, type_name(coll_type))
            elem_type = Type_Error{}  // error recovery: suppress cascades (Type_Any would lower to i64)
        }

        if s.iter_type != nil {
            elem_type = resolve_type_expr(s.iter_type, c, s.span)
        }

        if s.elem_var != "" {
            type_env_set(&child, s.elem_var, elem_type)
        }
        if s.index_var != "" {
            // Index lives at slice header width — that's what codegen allocates
            // the counter as. Typing it as i64 here would force users to cast
            // when feeding it back into other slice ops.
            type_env_set(&child, s.index_var, Type_Numeric{kind = .Signed, bits = 32})
        }

        s.elem_type_ = distinct_base(elem_type)
        s.collection_type = coll_type

        check_scope(c, s.body, &child)
    } else if s.is_range {
        low_type  := check_expr(c, s.range_low, &child)
        high_type := check_expr(c, s.range_high, &child)

        iter_type: Type
        if s.iter_type != nil {
            iter_type = resolve_type_expr(s.iter_type, c, s.span)
        } else {
            // Silent promote — the loop will gracefully fall back to slice
            // header width if low/high don't agree (common when one side is
            // an `int` default param and the other is an i32-typed `.len`).
            // Users who genuinely want i64 spell it: `for k: i64 in a..b`.
            iter_type = try_promote_numeric(low_type, high_type)
            if _, ok := iter_type.(Type_Error); ok {
                iter_type = slice_header_width_type
            }
            if is_infer(iter_type) {
                iter_type = slice_header_width_type
            }
        }

        if !is_numeric(low_type) && !is_infer(low_type) && !is_any(low_type) {
            check_error(c, s.span, TYPE_RANGE_LOWER_BOUND_NUMERIC, type_name(low_type))
        }
        if !is_numeric(high_type) && !is_infer(high_type) && !is_any(high_type) {
            check_error(c, s.span, TYPE_RANGE_UPPER_BOUND_NUMERIC, type_name(high_type))
        }

        type_env_set(&child, s.loop_var, iter_type)
        s.var_type = distinct_base(iter_type)

        check_scope(c, s.body, &child)
    } else {
        // C-style for or simple for-condition loop.
        // Register init in the loop scope so the loop var is visible in
        // condition, post, and body.
        if s.init != nil {
            init_stmts: [dynamic]Stmt
            append(&init_stmts, s.init)
            register_and_check_declarations(c, init_stmts, &child)
            check_bodies(c, init_stmts, &child)
        }
        cond_type := check_expr(c, s.condition, &child)
        if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
            check_error(c, s.span, TYPE_CONDITION_BOOL, type_name(cond_type))
        }
        if s.post != nil {
            post_stmts: [dynamic]Stmt
            append(&post_stmts, s.post)
            check_bodies(c, post_stmts, &child)
        }
        check_scope(c, s.body, &child)
    }
}

// Phase-2 checker for a `return` statement.
check_return_body :: proc(c: ^Checker, s: Stmt_Return, env: ^Type_Env) {
    n_expected := len(env.return_types)
    n_supplied := len(s.values)

    // Trailing err return slots can be implicitly filled with `.Ok` (the err
    // type's zero value), so `return id` in a `(File_Id, err)` fn is shorthand
    // for `return id, .Ok`. n_min is the minimum number of values a return
    // must supply: everything except trailing err slots.
    n_err_trailing := 0
    for i := n_expected - 1; i >= 0; i -= 1 {
        if is_err_type(env.return_types[i]) {
            n_err_trailing += 1
        } else {
            break
        }
    }
    n_min := n_expected - n_err_trailing

    count_ok := true
    if n_expected == 0 {
        if n_supplied > 0 {
            check_error(c, s.span, TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN)
            count_ok = false
        }
    } else if n_expected == 1 {
        if n_supplied > 1 {
            check_error(c, s.span, TYPE_MULTI_VALUE_RETURN_FUNCTION_DOESN)
            count_ok = false
        } else if n_supplied == 0 && n_min > 0 {
            check_error(c, s.span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED,
                n_supplied, n_expected)
            count_ok = false
        }
    } else {
        if n_supplied > n_expected || n_supplied < n_min {
            check_error(c, s.span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED,
                n_supplied, n_expected)
            count_ok = false
        }
    }

    // Per-value type check for each supplied value against its positional slot.
    // Skip when count is wrong — the count error already explains the shape.
    if count_ok {
        for val, i in s.values {
            if i >= n_expected { break }
            expected := env.return_types[i]
            c.expected_hint = expected
            vt := check_expr(c, val, env)
            if !is_any(vt) && !is_any(expected) {
                if !coerce_deferred(c, vt, expected, s.span) && !types_equal(expected, vt) && !value_preserving_widen(vt, expected) {
                    if n_expected > 1 {
                        check_error(c, s.span, TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED,
                            i+1, type_name(vt), type_name(expected))
                    } else {
                        check_error(c, s.span, TYPE_RETURN_TYPE_MATCH_EXPECTED,
                            type_name(vt), type_name(expected))
                    }
                }
            }
            maybe_stamp_byte_view(c, expected, val)
            if is_infer(vt) {
                check_literal_overflow(c, val, expected, s.span)
            }
        }
    }
    // Escape analysis: prevent returning pointers/slices to local memory.
    // Exempt: memory package (arena_alloc must return slices).
    if c.current_package != "memory" {
        for val in s.values {
            if is_local_ref(c, val, env) {
                report_return_escape(c, val, s.span, env)
            }
            // Struct-with-slice-fields escape: a `return StructLit{local_arr,..}`
            // is OK (the compiler relocates storage to the caller's sret), but
            // returning an intermediate variable that holds such a struct
            // would dangle. Same for the bare `return call_with_escape()`
            // passthrough where this function doesn't itself participate in
            // the escape relocation.
            if returns_locally_backed_struct(c, val, env) {
                check_error(c, s.span,
                    TYPE_CANNOT_RETURN_STRUCT_WHOSE_SLICE)
            }
        }
    }
    // Note: returning a take-bound view by value used to be rejected here as
    // "view binding is scoped to the function." That was a redundancy concern
    // (the caller could read the memory directly) dressed up as a safety rule.
    // The actual dangling cases — returning `&local_view` or a struct whose
    // slice fields point at local memory — are caught by is_local_ref and
    // returns_locally_backed_struct above. A bare `return p` where p is a
    // take-bound struct copies the bytes into the caller's sret slot just
    // like any other by-value return; nothing dangles. So the blanket rule
    // is gone.
}

check_bodies :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env) {
    // Phase 2a: resolve struct signatures (fields) before any function body
    // is checked. Without this, forward references to a struct declared later
    // in the scope would see an empty fields list and fail field access.
    // Function signatures (params/return) are already resolved in Phase 1.
    for stmt in stmts {
        if s, ok := stmt.(^Stmt_Scope); ok && s.kind == .Struct {
            check_scope_body(c, s, env, signature_only = true)
        }
    }

    // Type-check struct field default values (must run after all declarations registered)
    check_struct_defaults(c, stmts, env)

    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            check_scope_body(c, s, env)

        case ^Stmt_If:
            // `#if` (comptime): evaluate the condition now and only check the
            // live arm. The dead arm is left in the AST but never visited by
            // the body checker — lets it reference target-specific symbols
            // (e.g. emscripten_set_main_loop in a #if #web arm) that wouldn't
            // resolve on the other build.
            if s.is_comptime {
                // Type-check the condition first so any compiler intrinsic
                // (#web, #native) gets its bool_value populated — codegen
                // reads that field, not the result we evaluate here.
                check_expr(c, s.condition, env)
                live, ok := evaluate_comptime_bool(c, s.condition)
                if !ok {
                    check_error(c, s.span, TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN)
                    break
                }
                // Pass 1 (register_and_check_declarations) already recursed
                // into the live arm and registered its decls in `env`, so
                // here we only need the body-check pass — calling check_scope
                // would re-run Pass 1 and trip "already declared" / shadow
                // diagnostics. Same env, not a child: comptime-`#if` is
                // text-substitution; the live arm should behave as if its
                // statements were written inline.
                if live {
                    check_bodies(c, s.body, env)
                } else if len(s.else_body) > 0 {
                    check_bodies(c, s.else_body, env)
                }
                break
            }
            cond_type := check_expr(c, s.condition, env)
            if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
                check_error(c, s.span, TYPE_CONDITION_BOOL_2, type_name(cond_type))
            }
            child := type_env_child(env)
            check_scope(c, s.body, &child)
            if len(s.else_body) > 0 {
                else_child := type_env_child(env)
                check_scope(c, s.else_body, &else_child)
                // Promote initializations that BOTH branches performed
                inits := [2]map[string]bool{ child.newly_inited, else_child.newly_inited }
                divs := [2]bool{ branch_diverges(s.body), branch_diverges(s.else_body) }
                promote_branch_inits(env, inits[:], divs[:])
            }
            // No else → the "fall-through" path initializes nothing → no promotion

        case ^Stmt_For:
            check_for_body(c, s, env)

        case ^Stmt_Match:
            check_match(c, s, env)

        case Stmt_Call:
            rt := check_expr(c, s.expr, env)
            // Must-use: a bare call that yields a value silently discards it.
            // void calls (the side-effect case) type to nil and are fine, as
            // are append-style operator statements (`&slice + x`), which are
            // Expr_Binary, not Expr_Call. Capture the value (`x := f()`) or
            // discard it explicitly (`_ = f()`). Skip Type_Error so a failed
            // call doesn't draw a second, redundant diagnostic.
            if call, is_call := s.expr.(^Expr_Call); is_call && rt != nil {
                _, is_void := rt.(Type_Void)
                _, is_errd := rt.(Type_Error)
                if !is_void && !is_errd {
                    check_error(c, s.span, TYPE_DISCARDED_RETURN, call.name)
                }
            }

        case ^Stmt_Multi_Assign:
            // Already checked in register_and_check_declarations (iterates assigns)
        case ^Stmt_Multi_Return_Assign:
            // Already checked in register_and_check_declarations

        case Stmt_Return:
            check_return_body(c, s, env)

        case Stmt_Break:
            // nothing to check
        case Stmt_Continue:
            // nothing to check

        case ^Stmt_Defer:
            // Body is checked in a child env so any declarations inside the
            // defer stay scoped to the deferred block. At runtime the body
            // executes on scope exit (LIFO across defers in the same scope).
            child := type_env_child(env)
            check_scope(c, s.body, &child)

        // Declarations were already fully handled in register_and_check_declarations
        case ^Stmt_Assign:
            // Complex LHS: dispatch on target kind. Simple reassignment falls
            // through to the env-update path below.
            if s.target != nil {
                #partial switch t in s.target {
                case ^Expr_Field_Access: check_field_assign(c, s, env)
                case ^Expr_Index:        check_index_assign(c, s, env)
                case ^Expr_Slice:        check_slice_assign(c, s, env)
                case ^Expr_Unary:
                    if t.op == .Caret {
                        check_deref_assign(c, s, env)
                    } else {
                        check_error(c, s.span, TYPE_INVALID_ASSIGNMENT_TARGET)
                    }
                case:
                    check_error(c, s.span, TYPE_INVALID_ASSIGNMENT_TARGET)
                }
                continue
            }
            // Include assignments are fully handled in register_and_check_declarations.
            if _, is_include := s.value.(^Expr_Include); is_include {
                continue
            }
            // Update the type env sequentially so that re-declared variables
            // (same name, different type) reflect the correct type at each point.
            // Use env_type (preserves distinct) instead of var_type (unwrapped for codegen).
            if s.env_type != nil && !is_untyped(s.env_type) {
                type_env_set(env, s.name, s.env_type)
            }
        case ^Stmt_Decl:
            // Already expanded during register_and_check_declarations. Run
            // check_bodies on the desugared statements so their env updates
            // (e.g. sequential shadowing via Stmt_Assign) are applied.
            check_bodies(c, s.checked, env)
        case ^Stmt_Union_Def:
            // already registered
        case ^Stmt_Foreign:
            // already registered
        case ^Stmt_Dispatch_Def:
            // Validate all target functions exist (concrete or generic template)
            for fn_name in s.functions {
                ft_raw, found := type_env_get(env, fn_name)
                if found {
                    if tf, ok := ft_raw.(^Type_Scope); !ok || len(tf.params) == 0 {
                        check_error(c, s.span, TYPE_DISPATCH_GROUP_FUNCTION, s.name, fn_name)
                    }
                } else if fn_name not_in c.table.generic_templates {
                    check_error(c, s.span, TYPE_DISPATCH_GROUP_FUNCTION_DEFINED, s.name, fn_name)
                }
            }
        case Stmt_Overload:
            if _, ok := find_dispatch(c, env, s.dispatch_name); !ok {
                check_error(c, s.span, TYPE_OVERLOAD_DISPATCH_GROUP, s.dispatch_name)
            }
        case Stmt_Module:
            // nothing to check
        }
    }
}

// ---------------------------------------------------------------------------
// Assignment checking helpers (extracted from the old monolithic check_stmt)
// ---------------------------------------------------------------------------

check_define :: proc(c: ^Checker, s: ^Stmt_Define, env: ^Type_Env, public_env: ^Type_Env = nil) {
    // pub: where the constant binding is registered. In module-scope mode this
    // is the module env (so siblings see it); otherwise it's env (back-compat).
    pub := public_env if public_env != nil else env
    // Skip if already pre-registered (parent's body scan)
    if s.name in pub.types {
        return
    }
    // Cross-module bare-name collisions are tracked in c.table.constant_owners
    // (set by the top-level registration pass) and reported at the use site.
    // We deliberately don't error here so different modules can each have
    // their own constant of the same name; the user disambiguates with
    // `Module.name` when both are visible.

    // `::` is constant-by-definition — register the value expression so
    // codegen can inline-substitute every use site. Module-level constants
    // are pre-registered by register_module_constant; this covers function-
    // body and nested-scope `::` declarations regardless of value type.
    c.table.constants[s.name] = s.value

    ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)
    val_type := check_expr(c, s.value, env)

    if !is_any(ann_type) {
        // Distinct + non-literal: use nominal compatibility (mirrors Stmt_Assign path)
        _, ann_is_distinct := ann_type.(^Type_Distinct)
        _, val_is_array := s.value.(^Expr_Array)
        _, val_is_struct_lit := s.value.(^Expr_Struct_Literal)

        if ann_is_distinct && !val_is_array && !val_is_struct_lit {
            if types_incompatible(ann_type, val_type) {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE,
                    type_name(val_type), s.name, type_name(ann_type))
            }
            if is_infer(val_type) {
                check_literal_overflow(c, s.value, ann_type, s.span)
            }
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, s.name, ann_type)
            return
        }

        // Literal assignment: delegate to structural check helpers (unwrap distinct)
        check_ann := distinct_base(ann_type)
        if sd := as_scope_body(check_ann); sd != nil && len(sd.fields) > 0 {
            check_struct_literal_assign(c, s.span, s.value, sd, env)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, s.name, ann_type)
            return
        }
        if ut, ok := check_ann.(^Type_Union); ok {
            check_union_literal_assign(c, s.span, s.value, ut, env)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, s.name, ann_type)
            return
        }
        if fa, ok := check_ann.(^Type_Fixed_Array); ok {
            check_array_assign(c, s.span, s.name, fa, val_type)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, s.name, ann_type)
            return
        }

        // Fallback: simple structural compatibility
        if types_incompatible(ann_type, val_type) {
            check_error(c, s.span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE,
                type_name(val_type), s.name, type_name(ann_type))
        }
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, ann_type, s.span)
        }
        s.var_type = distinct_base(ann_type)
        s.env_type = ann_type
        type_env_set(pub, s.name, ann_type)
        return
    }

    s.var_type = distinct_base(val_type)
    s.env_type = val_type
    type_env_set(pub, s.name, val_type)
    set_provenance(env, s.name, expr_provenance(c, s.value, env))
}

// Validate that a struct literal's fields match a struct definition:
// every literal field exists and has the right type, and no struct fields are missing.
check_struct_literal_fields :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, st: ^Scope_Body, span: Span, env: ^Type_Env) {
    // Positional form (`Foo{a, b, c}`): match entries to struct fields by index.
    if lit.positional {
        // Multi-return spread: `Foo{call()}` where call's return list matches
        // Foo's fields one-to-one (with normal compatibility, including
        // array→slice coercion). Codegen detects the same pattern and routes
        // the call's sret args into temps then into the struct.
        if len(lit.fields) == 1 && len(st.fields) > 1 {
            single_val := lit.fields[0].value
            check_expr(c, single_val, env)
            returns := call_return_list(c, single_val, env)
            if len(returns) == len(st.fields) {
                all_ok := true
                for sf, i in st.fields {
                    if types_incompatible(sf.type_, returns[i]) {
                        all_ok = false
                        break
                    }
                }
                if all_ok {
                    lit.is_spread = true
                    return
                }
            }
            // Fall through to the regular positional path so the user gets a
            // useful error if the call's return list doesn't match the struct.
        }
        if len(lit.fields) > len(st.fields) {
            check_error(c, span, TYPE_CLASS_FIELDS_POSITIONAL_VALUES,
                st.name, len(st.fields), len(lit.fields))
        }
        for field, i in lit.fields {
            if i >= len(st.fields) { break }
            sf := st.fields[i]
            // Only set the hint for anonymous nested literals — these need
            // the field type to determine their shape. Other expression
            // shapes (idents, calls, field-accesses, arithmetic) self-type
            // and a stray hint can mistype intermediate sub-expressions.
            if needs_field_type_hint(field.value) {
                c.expected_hint = sf.type_
            }
            ft := check_expr(c, field.value, env)
            if !coerce_deferred(c, ft, sf.type_, span) && types_incompatible(sf.type_, ft) && !value_preserving_widen(ft, sf.type_) {
                check_error(c, span, TYPE_FIELD_POSITION_EXPECTED,
                    sf.name, i, type_name(sf.type_), type_name(ft))
            }
            maybe_stamp_byte_view(c, sf.type_, field.value)
            if is_infer(ft) {
                check_literal_overflow(c, field.value, sf.type_, span)
            }
        }
        return
    }
    // Named form: O(literal_fields) — validate each literal field against
    // struct definition via field_map.
    provided: map[string]bool
    for field in lit.fields {
        if idx, ok := st.field_map[field.name]; ok {
            sf := st.fields[idx]
            provided[field.name] = true
            if needs_field_type_hint(field.value) {
                c.expected_hint = sf.type_
            }
            ft := check_expr(c, field.value, env)
            if !coerce_deferred(c, ft, sf.type_, span) && types_incompatible(sf.type_, ft) && !value_preserving_widen(ft, sf.type_) {
                check_error(c, span, TYPE_FIELD_EXPECTED,
                    field.name, type_name(sf.type_), type_name(ft))
            }
            maybe_stamp_byte_view(c, sf.type_, field.value)
            if is_infer(ft) {
                check_literal_overflow(c, field.value, sf.type_, span)
            }
        } else {
            check_error(c, span, TYPE_CLASS_FIELD, st.name, field.name)
        }
    }
    // No missing-field check: all struct literals are zero-initialized first,
    // then defaults are applied for unspecified fields. Partial literals are allowed.
}

check_struct_literal_assign :: proc(c: ^Checker, span: Span, value: Expr, st: ^Scope_Body, env: ^Type_Env) {
    lit, lit_ok := value.(^Expr_Struct_Literal)
    if !lit_ok { return }
    check_struct_literal_fields(c, lit, st, span, env)
}

check_union_literal_assign :: proc(c: ^Checker, span: Span, value: Expr, ut: ^Type_Union, env: ^Type_Env) {
    lit, lit_ok := value.(^Expr_Struct_Literal)
    if !lit_ok { return }

    if lit.name == "" {
        check_error(c, span, TYPE_UNION_REQUIRES_NAMED_VARIANT_VARIANT, ut.name)
    } else if lit.name not_in ut.tag_map {
        check_error(c, span, TYPE_VARIANT_UNION, lit.name, ut.name)
    } else {
        // Look up struct via variant_structs mapping
        struct_name := ut.variant_structs[lit.name]
        if st, st_ok := c.table.structs[struct_name]; st_ok {
            check_struct_literal_fields(c, lit, &st.sd, span, env)
        } else if st, st_ok := c.table.funs[struct_name]; st_ok {
            check_struct_literal_fields(c, lit, &st.sd, span, env)
        }
    }
}

// True when an expression needs a type hint from its surrounding context to
// be type-checked correctly. Today this is only anonymous struct/array
// literals (`{a, b, c}` with no leading name and no inline `[N]T`) — the
// type checker uses the hint at check_expr's Expr_Struct_Literal branch to
// dispatch to check_array_struct_literal. Idents, field accesses, calls,
// arithmetic, etc. all self-type without a hint, so we don't propagate one
// to them (a stray hint can mistype intermediate sub-expressions).
needs_field_type_hint :: proc(e: Expr) -> bool {
    lit, ok := e.(^Expr_Struct_Literal)
    if !ok { return false }
    return lit.name == "" && lit.type_expr == nil && !lit.is_broadcast
}

// Validate a `Quat{...}` / `Vec3{...}` style literal that constructs a value of
// a distinct fixed array type. Populates lit.array_values with positional
// entries (nil means "zero this slot" — codegen fills from memset).
//
// Three surface forms are accepted:
//   Name{}            — zero-init every slot
//   Name{v0, v1, ...} — positional; must have exactly fa.size entries
//   Name{x: v, ...}   — named; each name must be a swizzle char (x/y/z/w or
//                       r/g/b/a) whose index is within fa.size; duplicates
//                       rejected; missing slots zero-fill
check_array_struct_literal :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, fa: ^Type_Fixed_Array, env: ^Type_Env) {
    clear(&lit.array_values)
    resize(&lit.array_values, fa.size)

    // Broadcast: `{all <expr>}` — check the expression once against the
    // element type, then fill every slot with a clone so codegen emits
    // independent stores per element.
    if lit.is_broadcast {
        val_type := check_expr(c, lit.broadcast_value, env)
        if types_incompatible(fa.elem, val_type) {
            check_error(c, lit.span, TYPE_BROADCAST_VALUE_TYPE_EXPECTED,
                lit.name, type_name(val_type), type_name(fa.elem))
            return
        }
        if is_infer(val_type) {
            check_literal_overflow(c, lit.broadcast_value, fa.elem, lit.span)
        }
        for i in 0..<fa.size {
            lit.array_values[i] = i == 0 ? lit.broadcast_value : clone_expr(lit.broadcast_value)
        }
        return
    }

    // Zero-init or empty — all slots stay nil
    if lit.zero_init || len(lit.fields) == 0 { return }

    if lit.positional {
        if len(lit.fields) != fa.size {
            check_error(c, lit.span, TYPE_EXPECTS_POSITIONAL_VALUES,
                lit.name, fa.size, len(lit.fields))
            return
        }
        for field, i in lit.fields {
            val_type := check_expr(c, field.value, env)
            if types_incompatible(fa.elem, val_type) {
                check_error(c, lit.span, TYPE_ELEMENT_TYPE_EXPECTED,
                    lit.name, i, type_name(val_type), type_name(fa.elem))
            }
            if is_infer(val_type) {
                check_literal_overflow(c, field.value, fa.elem, lit.span)
            }
            lit.array_values[i] = field.value
        }
        return
    }

    // Named form: each name must be a single swizzle char
    for field in lit.fields {
        if len(field.name) != 1 || !is_swizzle_field(field.name, fa.size) {
            check_error(c, lit.span, TYPE_FIELD_USE_SWIZZLE_COMPONENTS_WITHIN,
                lit.name, field.name, fa.size)
            continue
        }
        idx := swizzle_char_to_index(field.name[0])
        if lit.array_values[idx] != nil {
            check_error(c, lit.span, TYPE_FIELD_SET_MORE_THAN_ONCE, lit.name, field.name)
            continue
        }
        val_type := check_expr(c, field.value, env)
        if types_incompatible(fa.elem, val_type) {
            check_error(c, lit.span, TYPE_FIELD_TYPE_EXPECTED,
                lit.name, field.name, type_name(val_type), type_name(fa.elem))
        }
        if is_infer(val_type) {
            check_literal_overflow(c, field.value, fa.elem, lit.span)
        }
        lit.array_values[idx] = field.value
    }
}

check_array_assign :: proc(c: ^Checker, span: Span, name: string, fa: ^Type_Fixed_Array, val_type: Type) {
    if fv, ok2 := val_type.(^Type_Fixed_Array); ok2 {
        if types_incompatible(fa.elem, fv.elem) {
            check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
                type_name(val_type), name, type_name(fa))
        } else if fv.size > 0 && fv.size > fa.size {
            // Literal must not have more elements than capacity
            check_error(c, span, TYPE_ARRAY_ELEMENTS_CAPACITY,
                fv.size, name, fa.size)
        }
    } else if pv, pv_ok := val_type.(^Type_Partial_Array); pv_ok {
        // Source is a partial array (e.g. a string literal post the
        // literal-type change). Same element check; size check ensures
        // the source content fits in the fixed-array storage.
        if types_incompatible(fa.elem, pv.elem) {
            check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
                type_name(val_type), name, type_name(fa))
        } else if pv.size > 0 && pv.size > fa.size {
            check_error(c, span, TYPE_ARRAY_ELEMENTS_CAPACITY,
                pv.size, name, fa.size)
        }
    } else if !is_any(val_type) {
        check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
            type_name(val_type), name, type_name(fa))
    }
}

check_deref_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    un := s.target.(^Expr_Unary)
    ptr_type := check_expr(c, un.operand, env)
    val_type := check_expr(c, s.value, env)
    if p, ok := ptr_type.(^Type_Ptr); ok {
        s.target_type = p.elem
        if types_incompatible(p.elem, val_type) {
            check_error(c, s.span, TYPE_CANNOT_ASSIGN_THROUGH_POINTER,
                type_name(val_type), type_name(p.elem))
        }
        // Check that infer literal fits in the pointed-to type
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, p.elem, s.span)
        }
    } else if !is_any(ptr_type) {
        check_error(c, s.span, TYPE_CANNOT_DEREFERENCE_ASSIGN_NON_POINTER, type_name(ptr_type))
    }
    // Escape analysis: prevent writing local references through param pointers.
    // e.g., param^ = &local_var would let a local reference escape.
    if c.current_package != "memory" {
        if is_local_ref(c, s.value, env) {
            if ident, ok := un.operand.(^Expr_Ident); ok {
                if is_param(env, ident.name) {
                    check_error(c, s.span,
                        TYPE_CANNOT_WRITE_LOCAL_REFERENCE_THROUGH,
                        ident.name)
                }
            }
        }
    }
}

check_index_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    ix := s.target.(^Expr_Index)
    // `::` constants can be read by index — the codegen routes that through
    // the literal's .rodata global. But writing through one would attempt
    // to mutate read-only memory at runtime, so reject at the type-check
    // stage with a hint about how to fix.
    if ident, ok := ix.expr.(^Expr_Ident); ok {
        if _, is_const := c.table.constants[ident.name]; is_const {
            check_error(c, s.span, TYPE_CANNOT_WRITE_INDEXED_CONSTANT, ident.name, ident.name)
            return
        }
    }
    target_type := distinct_base(check_expr(c, ix.expr, env))
    s.target_type = target_type
    if fa, ok := target_type.(^Type_Fixed_Array); ok && fa.index_type != nil {
        c.expected_hint = fa.index_type
    }
    idx_type := check_expr(c, ix.index, env)
    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        c.expected_hint = fa.elem
    }
    val_type := check_expr(c, s.value, env)

    if !is_numeric(idx_type) && !is_any(idx_type) {
        check_error(c, s.span, TYPE_ARRAY_INDEX_NUMBER, type_name(idx_type))
    } else if !coerces_to_index_width(idx_type) {
        check_error(c, s.span, TYPE_INDEX_WIDTH,
            type_name(slice_header_width_type), type_name(idx_type))
    }

    if pname, immut := write_root_immutable_param(s.target, env); immut {
        check_error(c, s.span,
            TYPE_CANNOT_WRITE_ELEMENT_IMMUTABLE_PARAMETER,
            pname)
    }

    // Byte slice reinterpret write: mem[offset] = value
    if is_byte_slice(target_type) {
        solid_val_type := solidify_type(val_type)
        s.assign_value_type = solid_val_type
        return
    }

    // Byte partial-array reinterpret write: same semantics as []byte slice.
    if is_byte_partial_array(target_type) {
        s.assign_value_type = solidify_type(val_type)
        return
    }

    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        // Byte fixed-array reinterpret write: buf[i] = value (any type)
        // Mirrors the []byte reinterpret semantics used throughout memory.mara.
        if _, is_byte := fa.elem.(Type_Byte); is_byte {
            s.assign_value_type = solidify_type(val_type)
            return
        }
        if types_incompatible(fa.elem, val_type) {
            check_error(c, s.span, TYPE_CANNOT_ASSIGN_ELEMENT,
                type_name(val_type), fa.size, type_name(fa.elem))
        }
        // Check that infer literal fits in the array element type
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, fa.elem, s.span)
        }
    }

}

check_slice_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    sl := s.target.(^Expr_Slice)
    target_type := check_expr(c, sl.expr, env)
    s.target_type = target_type
    low_type    := check_expr(c, sl.low,  env)
    high_type: Type
    if sl.high != nil {
        high_type = check_expr(c, sl.high, env)
    }
    val_type    := check_expr(c, s.value, env)

    if !is_numeric(low_type) && !is_any(low_type) {
        check_error(c, s.span, TYPE_SLICE_LOWER_BOUND_NUMBER, type_name(low_type))
    } else if !coerces_to_slice_width(low_type) {
        check_error(c, s.span, TYPE_INDEX_WIDTH,
            type_name(slice_header_width_type), type_name(low_type))
    }
    if sl.high != nil && !is_numeric(high_type) && !is_any(high_type) {
        check_error(c, s.span, TYPE_SLICE_UPPER_BOUND_NUMBER, type_name(high_type))
    } else if sl.high != nil && !coerces_to_slice_width(high_type) {
        check_error(c, s.span, TYPE_INDEX_WIDTH,
            type_name(slice_header_width_type), type_name(high_type))
    }

    if pname, immut := write_root_immutable_param(s.target, env); immut {
        check_error(c, s.span,
            TYPE_CANNOT_SLICE_ASSIGN_INTO_IMMUTABLE,
            pname)
    }

    // Byte slice reinterpret write: mem[off:off+N] = value
    if is_byte_slice(target_type) {
        solid_val_type := solidify_type(val_type)
        s.assign_value_type = solid_val_type
        // Compile-time size check when bounds are constant
        if low_num, low_ok := const_eval_int(sl.low); low_ok {
            if high_num, high_ok := const_eval_int(sl.high); high_ok {
                span_size := high_num - low_num
                val_size := checker_type_byte_size(solid_val_type)
                if span_size != val_size {
                    check_error(c, s.span,
                        TYPE_BYTE_SLICE_WRITE_BYTES_SLICE,
                        type_name(solid_val_type), val_size, span_size)
                }
            }
        }
        return
    }

    // Byte partial-array reinterpret write: same semantics as []byte. Partial
    // arrays carry a slice header at the front of their inline storage and
    // codegen treats them as Slice_Vars, so the byte-target write helper
    // resolves the data pointer the same way.
    if is_byte_partial_array(target_type) {
        solid_val_type := solidify_type(val_type)
        s.assign_value_type = solid_val_type
        if low_num, low_ok := const_eval_int(sl.low); low_ok {
            if high_num, high_ok := const_eval_int(sl.high); high_ok {
                span_size := high_num - low_num
                val_size := checker_type_byte_size(solid_val_type)
                if span_size != val_size {
                    check_error(c, s.span,
                        TYPE_BYTE_SLICE_WRITE_BYTES_SLICE,
                        type_name(solid_val_type), val_size, span_size)
                }
            }
        }
        return
    }

    // Byte fixed-array reinterpret write: buf[off:off+N] = value
    // (array-class byte buffers reach here post-desugar as [N]byte)
    // Reinterpret only applies to scalar/struct writes — fixed-array or slice
    // RHS values fall through to the regular array-copy path below.
    if is_byte_fixed_array(target_type) {
        _, rhs_is_fa := val_type.(^Type_Fixed_Array)
        _, rhs_is_sl := val_type.(^Type_Slice)
        if !rhs_is_fa && !rhs_is_sl {
            solid_val_type := solidify_type(val_type)
            s.assign_value_type = solid_val_type
            if low_num, low_ok := const_eval_int(sl.low); low_ok {
                if high_num, high_ok := const_eval_int(sl.high); high_ok {
                    span_size := high_num - low_num
                    val_size := checker_type_byte_size(solid_val_type)
                    if span_size != val_size {
                        check_error(c, s.span,
                            TYPE_BYTE_ARRAY_WRITE_BYTES_SLICE,
                            type_name(solid_val_type), val_size, span_size)
                    }
                }
            }
            return
        }
    }

    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        // RHS must also be a fixed array with matching element type
        if rhs, rhs_ok := val_type.(^Type_Fixed_Array); rhs_ok {
            if types_incompatible(fa.elem, rhs.elem) {
                check_error(c, s.span, TYPE_CANNOT_SLICE_ASSIGN_INTO,
                    rhs.size, type_name(rhs.elem), fa.size, type_name(fa.elem))
            }
        } else if rhs_sl, rhs_sl_ok := val_type.(^Type_Slice); rhs_sl_ok {
            if types_incompatible(fa.elem, rhs_sl.elem) {
                check_error(c, s.span, TYPE_CANNOT_SLICE_ASSIGN_INTO_2,
                    type_name(rhs_sl.elem), fa.size, type_name(fa.elem))
            }
        } else if !is_any(val_type) {
            check_error(c, s.span, TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE, type_name(val_type))
        }
    }
}

check_field_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    fa_expr := s.target.(^Expr_Field_Access)
    obj_type := check_expr(c, fa_expr.expr, env)

    // Pre-resolve the field's type so check_expr(s.value) can pick it up via
    // c.expected_hint. The 1-arg `slice(source)` form needs this to infer
    // its element type; without the hint it has nowhere to derive T from.
    pre_st: ^Scope_Body
    if sd := as_scope_body(obj_type); sd != nil && len(sd.fields) > 0 {
        pre_st = sd
    } else if pt, ok := obj_type.(^Type_Ptr); ok {
        if sd := as_scope_body(pt.elem); sd != nil && len(sd.fields) > 0 {
            pre_st = sd
        }
    }
    if pre_st != nil {
        if ft := resolve_struct_field(pre_st, fa_expr.field, c.table); ft != nil {
            c.expected_hint = ft
        }
    }
    val_type := check_expr(c, s.value, env)
    c.expected_hint = nil

    // Same partial-array-aliasing rejection as the simple-target path: a
    // memcpy of a struct containing a `Type_Partial_Array` field would leave
    // the field's `ptr` aliasing the source's elements.
    is_copy_source := false
    if _, ok := s.value.(^Expr_Ident); ok { is_copy_source = true }
    if _, ok := s.value.(^Expr_Field_Access); ok { is_copy_source = true }
    if is_copy_source && struct_contains_partial_array(val_type) {
        check_error(c, s.span,
            TYPE_CANNOT_COPY_VALUE_CONTAINS_PARTIAL,
            type_name(val_type))
    }

    // Auto-deref: if obj is ^Struct, check field on the inner struct
    st: ^Scope_Body = pre_st

    if st != nil {
        ft := resolve_struct_field(st, fa_expr.field, c.table)
        if ft != nil {
            s.target_type = ft
            if pname, immut := write_root_immutable_param(s.target, env); immut {
                check_error(c, s.span,
                    TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER,
                    fa_expr.field, pname)
            }
            // Mark field as initialized (clears invalid_refs for ptr/slice struct fields)
            if ident, ident_ok := fa_expr.expr.(^Expr_Ident); ident_ok {
                field_key := strings.concatenate({ident.name, ".", fa_expr.field})
                mark_initialized(env, field_key)
            }
            if is_byte_buffer(val_type) {
                // Byte buffer reinterpret read via slice: obj.field = mem[lo:hi]
                field_size := checker_type_byte_size(ft)
                if sl, ok := s.value.(^Expr_Slice); ok {
                    if low_num, low_ok := const_eval_int(sl.low); low_ok {
                        if high_num, high_ok := const_eval_int(sl.high); high_ok {
                            span_size := high_num - low_num
                            if span_size != field_size {
                                check_error(c, s.span,
                                    TYPE_BYTE_BUFFER_READ_BYTES_SLICE,
                                    type_name(ft), field_size, span_size)
                            }
                        }
                    }
                }
            } else if is_byte_buffer_index_read(s.value) {
                // Byte buffer reinterpret read via index: obj.field = mem[off]
                // Size comes from field type; bounds checked at runtime
            } else if !coerce_deferred(c, val_type, ft, s.span) && types_incompatible(ft, val_type) && !value_preserving_widen(val_type, ft) {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_FIELD_TYPE,
                    assign_source_desc(s.value, val_type), expr_diag_name(fa_expr), type_name(ft))
            }
            // Check that infer literal fits in the field type
            if is_infer(val_type) {
                check_literal_overflow(c, s.value, ft, s.span)
            }
            // Escape analysis: prevent writing local refs into param struct fields.
            // e.g., param.ptr_field = &local_var
            if c.current_package != "memory" {
                is_ref_field := false
                if ft != nil {
                    if _, ptr_ok := ft.(^Type_Ptr); ptr_ok { is_ref_field = true }
                    if _, sl_ok := ft.(^Type_Slice); sl_ok { is_ref_field = true }
                }
                if is_ref_field && is_local_ref(c, s.value, env) {
                    if ident, ok := fa_expr.expr.(^Expr_Ident); ok {
                        if is_param(env, ident.name) {
                            check_error(c, s.span,
                                TYPE_CANNOT_WRITE_LOCAL_REFERENCE_FIELD,
                                fa_expr.field, ident.name)
                        }
                    }
                }
            }
        } else {
            check_error(c, s.span, TYPE_CLASS_FIELD, st.name, fa_expr.field)
        }
        return
    }

    // Auto-deref ^Slice / ^Partial_Array — `data.len = ...` where data is
    // `^[]byte` writes through the pointer. Mirrors the read-side unwrap in
    // check_field_access.
    if pt, ok := obj_type.(^Type_Ptr); ok {
        inner := pt.elem
        if dt, dt_ok := inner.(^Type_Distinct); dt_ok {
            inner = dt.base_type
        }
        obj_type = inner
    }
    if dt, dt_ok := obj_type.(^Type_Distinct); dt_ok {
        obj_type = distinct_base(dt)
    }

    // Slice / partial-array .len / .cap / .ptr writes. Previously this path
    // had no type check at all — any value type silently flowed into the
    // slice's narrow header fields, and the codegen had to trunc/widen at
    // its end with no real ABI contract. Match the read-side type the
    // field-access resolver returns and run the standard compat check.
    is_slice_or_partial := false
    field_type: Type
    elem: Type
    if sl, ok := obj_type.(^Type_Slice); ok {
        is_slice_or_partial = true
        elem = sl.elem
    } else if pa, ok := obj_type.(^Type_Partial_Array); ok {
        is_slice_or_partial = true
        elem = pa.elem
    }
    if is_slice_or_partial {
        switch fa_expr.field {
        case "len", "cap": field_type = slice_header_width_type
        case "ptr":
            pt := new(Type_Ptr)
            pt.elem = elem
            field_type = pt
        case:
            // Unknown field on a slice/partial. Read path would error;
            // mirror that here for symmetry.
            check_error(c, s.span, TYPE_SLICE_TYPE_FIELD, type_name(obj_type), fa_expr.field)
            return
        }
        s.target_type = field_type
        if !coerce_deferred(c, val_type, field_type, s.span) && types_incompatible(field_type, val_type) && !is_infer(val_type) && !value_preserving_widen(val_type, field_type) {
            check_error(c, s.span, TYPE_CANNOT_ASSIGN_FIELD_TYPE,
                assign_source_desc(s.value, val_type), expr_diag_name(fa_expr), type_name(field_type))
        }
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, field_type, s.span)
        }
        return
    }

    // Array swizzle assignment: arr.x = val, arr.xy = [a, b]
    if fa, fa_ok := obj_type.(^Type_Fixed_Array); fa_ok {
        if is_swizzle_field(fa_expr.field, fa.size) {
            if len(fa_expr.field) == 1 {
                // Single-component write: value must match element type
                if types_incompatible(fa.elem, val_type) && !is_infer(val_type) {
                    check_error(c, s.span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPE,
                        type_name(val_type), fa_expr.field, type_name(fa.elem))
                }
                if is_infer(val_type) {
                    check_literal_overflow(c, s.value, fa.elem, s.span)
                }
            } else {
                // Multi-component write: value must be an array with matching element type
                if va, va_ok := val_type.(^Type_Fixed_Array); va_ok {
                    if types_incompatible(fa.elem, va.elem) {
                        check_error(c, s.span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPES,
                            type_name(val_type), fa_expr.field)
                    }
                } else if !is_any(val_type) && !is_infer(val_type) {
                    check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_COMPONENT_SWIZZLE,
                        type_name(val_type), fa_expr.field)
                }
            }
            return
        }
        if is_all_swizzle_chars(fa_expr.field) {
            check_error(c, s.span, TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY, fa_expr.field, fa.size)
            return
        }
    }
}

check_match :: proc(c: ^Checker, s: ^Stmt_Match, env: ^Type_Env) {
    // Subject-less form: `match { cond1 ...; cond2 ... }` — each arm is a
    // standalone bool predicate, multi-fire semantics (every true arm runs
    // its body). Routed through check_namespace_match for the predicate
    // validation since the arm shape and semantics are identical to the
    // struct-namespace form.
    if s.subject == nil {
        check_namespace_match(c, s, env, nil)
        return
    }
    subj_type := check_expr(c, s.subject, env)
    ut, is_union_match := subj_type.(^Type_Union)
    et, is_enum_match := subj_type.(^Type_Enum)
    _, is_err_match := subj_type.(Type_Err)

    // Open `err` matches can never be exhaustive — the universe of error
    // variants is open across the whole program. Force an explicit `else`
    // arm so unhandled errors stay structurally visible rather than
    // silently falling through.
    if is_err_match {
        has_else := false
        for arm in s.arms {
            if arm.is_else { has_else = true; break }
        }
        if !has_else {
            check_error(c, s.span, TYPE_MATCH_ERR_REQUIRES_ELSE)
        }
    }

    // Namespace-form match: subject is a struct. Each arm is a bool predicate
    // — either an explicit expression (`expr do stmt`) or a bare field name
    // (`quit do stmt`, which the parser produces as an is_union_arm with
    // variant_name="quit"). All predicate arms fire independently — multi-fire
    // semantics, like each-index over a struct's bool fields.
    if scope, is_struct := subj_type.(^Type_Scope); is_struct && scope.kind == .Struct {
        check_namespace_match(c, s, env, scope)
        return
    }

    // Validate wildcard 'else' arms. Empty body is fine — it's the explicit
    // no-op opt-out ("ignore unhandled variants on purpose"), same idiom as
    // Rust's `_ => {}`.
    for arm, i in s.arms {
        if arm.is_else && i != len(s.arms) - 1 {
            check_error(c, s.span, TYPE_LAST_ARM_MATCH)
        }
    }

    // Track per-arm initializations for definite assignment promotion
    arm_inits: [dynamic]map[string]bool
    arm_divs: [dynamic]bool

    for &arm in s.arms {
        if arm.dot_shorthand != "" {
            // Dot shorthand arm: .Variant — resolve against subject's enum or union type
            if is_enum_match {
                if tag_val, v_ok := et.variants[arm.dot_shorthand]; v_ok {
                    arm.resolved_tag = tag_val
                } else {
                    check_error(c, s.span, TYPE_ENUM_VARIANT, et.name, arm.dot_shorthand)
                }
            } else if is_union_match {
                if tag_val, v_ok := ut.tag_map[arm.dot_shorthand]; v_ok {
                    arm.resolved_tag = tag_val
                    ds_struct := ut.variant_structs[arm.dot_shorthand] or_else arm.dot_shorthand
                    if arm_st, arm_st_ok := c.table.structs[ds_struct]; arm_st_ok {
                        arm.resolved_struct = arm_st.name
                    } else if arm_st, arm_st_ok := c.table.funs[ds_struct]; arm_st_ok {
                        arm.resolved_struct = arm_st.name
                    }
                } else {
                    check_error(c, s.span, TYPE_UNION_VARIANT, ut.name, arm.dot_shorthand)
                }
            } else {
                check_error(c, s.span, TYPE_DOT_SHORTHAND_ONLY_USED_MATCHING, arm.dot_shorthand)
            }
            child := type_env_child(env)
            check_scope(c, arm.body, &child)
            append(&arm_inits, child.newly_inited)
            append(&arm_divs, branch_diverges(arm.body))
        } else if arm.is_union_arm {
            // Union pattern arm: VariantName [bindingName] { body }
            if is_union_match {
                if tag_val, tv_ok := ut.tag_map[arm.variant_name]; tv_ok {
                    arm.resolved_tag = tag_val
                } else {
                    check_error(c, s.span, TYPE_VARIANT_UNION, arm.variant_name, ut.name)
                }
            }
            // No-binding form: `KeyDown` (no binding name) on a bare-ident
            // subject `e` rebinds `e` to the variant struct view inside this
            // arm's body. The arm body can then access variant fields through
            // the subject's existing name (`e.scancode`) instead of needing a
            // dedicated alias (`KeyDown key` + `key.scancode`). Only triggers
            // when the subject is a simple identifier — non-ident subjects
            // have no name to rebind, so the user falls back to the explicit
            // binding form.
            if arm.binding_name == "" {
                if subj_ident, sok := s.subject.(^Expr_Ident); sok {
                    arm.binding_name = subj_ident.name
                }
            }
            child := type_env_child(env)
            // Bind the payload variable as the variant's struct type
            struct_name := arm.variant_name
            if is_union_match {
                if sn, sn_ok := ut.variant_structs[arm.variant_name]; sn_ok {
                    struct_name = sn
                }
            }
            // Store flat name for codegen and bind payload variable
            if st, st_ok := c.table.structs[struct_name]; st_ok {
                arm.resolved_struct = st.name
                if arm.binding_name != "" {
                    type_env_set(&child, arm.binding_name, st)
                }
            } else if st, st_ok := c.table.funs[struct_name]; st_ok {
                arm.resolved_struct = st.name
                if arm.binding_name != "" {
                    type_env_set(&child, arm.binding_name, st)
                }
            }
            check_scope(c, arm.body, &child)
            append(&arm_inits, child.newly_inited)
            append(&arm_divs, branch_diverges(arm.body))
        } else if arm.is_else {
            // Else (wildcard) arm — just type-check the body
            child := type_env_child(env)
            check_scope(c, arm.body, &child)
            append(&arm_inits, child.newly_inited)
            append(&arm_divs, branch_diverges(arm.body))
        } else {
            // Value match arm — try to infer bare identifiers as enum/union variants
            if ident, ident_ok := arm.value.(^Expr_Ident); ident_ok {
                if is_enum_match {
                    if tag_val, v_ok := et.variants[ident.name]; v_ok {
                        // Promote bare ident to dot_shorthand arm
                        arm.dot_shorthand = ident.name
                        arm.resolved_tag = tag_val
                        child := type_env_child(env)
                        check_scope(c, arm.body, &child)
                        append(&arm_inits, child.newly_inited)
                        append(&arm_divs, branch_diverges(arm.body))
                        continue
                    }
                } else if is_union_match {
                    if tag_val, v_ok := ut.tag_map[ident.name]; v_ok {
                        // Promote bare ident to dot_shorthand arm
                        arm.dot_shorthand = ident.name
                        arm.resolved_tag = tag_val
                        ds_struct := ut.variant_structs[ident.name] or_else ident.name
                        if arm_st, arm_st_ok := c.table.structs[ds_struct]; arm_st_ok {
                            arm.resolved_struct = arm_st.name
                        } else if arm_st, arm_st_ok := c.table.funs[ds_struct]; arm_st_ok {
                            arm.resolved_struct = arm_st.name
                        }
                        child := type_env_child(env)
                        check_scope(c, arm.body, &child)
                        append(&arm_inits, child.newly_inited)
                        append(&arm_divs, branch_diverges(arm.body))
                        continue
                    }
                }
            }
            // Regular value match arm
            check_expr(c, arm.value, env)
            child := type_env_child(env)
            check_scope(c, arm.body, &child)
            append(&arm_inits, child.newly_inited)
            append(&arm_divs, branch_diverges(arm.body))
        }
    }
    // An else arm (with or without a body) opts out of the variant-coverage
    // check below — its presence is the explicit acknowledgment that the
    // user is not covering every variant on purpose.
    has_wildcard := false
    for arm in s.arms {
        if arm.is_else {
            has_wildcard = true
            break
        }
    }
    // Promote definite assignments if the match is exhaustive — either via
    // an else wildcard with a body or (below) by covering every variant.
    if has_wildcard && len(arm_inits) > 0 {
        promote_branch_inits(env, arm_inits[:], arm_divs[:])
    }
    // Strict-default exhaustiveness: when the subject is an enum or union and
    // there's no else wildcard, every variant must have an arm. else is the
    // only opt-out — write `else do {…}` to acknowledge you're not covering
    // every variant on purpose.
    if !has_wildcard && (is_enum_match || is_union_match) {
        // Collect covered variant names from match arms
        covered: map[string]bool
        for arm in s.arms {
            if arm.dot_shorthand != "" {
                covered[arm.dot_shorthand] = true
            } else if arm.is_union_arm {
                covered[arm.variant_name] = true
            } else if fa, fa_ok := arm.value.(^Expr_Field_Access); fa_ok {
                covered[fa.field] = true
            }
        }
        // Check all variants are covered
        if is_enum_match {
            for name in et.variants {
                if name not_in covered {
                    check_error(c, s.span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, et.name, name)
                }
            }
        } else if is_union_match {
            for variant in ut.variants {
                if variant not_in covered {
                    check_error(c, s.span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, ut.name, variant)
                }
            }
        }
        // Match passed exhaustiveness — promote definite assignments.
        if len(arm_inits) > 0 {
            promote_branch_inits(env, arm_inits[:], arm_divs[:])
        }
    }
}

// Namespace-form match: subject is a struct, arms are bool predicates that
// resolve against the subject's fields. All arms fire independently when
// their predicate is true (multi-fire — same cardinality as each-index).
//
// Two arm shapes valid here:
//   <field> do <stmt>     — bare identifier, parser tagged it as is_union_arm
//                           with variant_name=<field>; we look up <field> on
//                           the subject struct and use it as the predicate.
//   <expr>  do <stmt>     — explicit predicate expression; parser set
//                           is_predicate_arm with arm.value=<expr>. The
//                           predicate must type as bool.
//
// `else` is not allowed in namespace match — there's no "no match" branch
// when arms are independent. If you want a default action, write it after
// the match block.
//
// Inside the arms (both predicates and bodies), the subject acts like an
// implicit `using` binding: a bare identifier that doesn't resolve in the
// local env is looked up as a field of the subject's struct. So
// `match game.events { dropfile.was_dropped do print(dropfile.name) }` works
// without re-typing `game.events.` in either the predicate or the body.
// Locals declared in the arm body shadow subject fields normally.
check_namespace_match :: proc(c: ^Checker, s: ^Stmt_Match, env: ^Type_Env, scope: ^Type_Scope) {
    for arm in s.arms {
        if arm.is_else {
            check_error(c, s.span, TYPE_ALLOWED_MATCH_STRUCT_ARMS_FIRE)
        }
    }

    // Set up the namespace context so identifier resolution falls back to
    // subject-field lookup. Saved/restored to handle nested namespace matches.
    // Subject-less form (scope == nil) doesn't have a namespace fallback —
    // every predicate resolves through the normal env, which is what you
    // want: it's a flat if-chain replacement, not a field shortcut.
    saved_subject      := c.namespace_subject
    saved_subject_type := c.namespace_subject_type
    c.namespace_subject      = s.subject
    c.namespace_subject_type = scope
    defer {
        c.namespace_subject      = saved_subject
        c.namespace_subject_type = saved_subject_type
    }

    for &arm in s.arms {
        if arm.is_else { continue }

        // Resolve the predicate. Bare-identifier arms (parsed as is_union_arm
        // with variant_name set) are normalized to a uniform predicate-arm
        // shape with arm.value carrying the predicate Expr. The Expr_Ident
        // fallback then handles the namespace lookup at type-check time.
        predicate: Expr
        if arm.is_predicate_arm {
            predicate = arm.value
        } else if arm.is_union_arm && arm.variant_name != "" {
            ident := new_clone(Expr_Ident{name = arm.variant_name, span = s.span})
            predicate            = ident
            arm.value            = ident
            arm.is_predicate_arm = true
            arm.is_union_arm     = false
            arm.variant_name     = ""
        } else if arm.value != nil {
            predicate            = arm.value
            arm.is_predicate_arm = true
        } else {
            ctx_name := scope.name if scope != nil else "match"
            check_error(c, s.span, TYPE_MATCH_STRUCT_EXPECTS_PREDICATE_ARMS, ctx_name)
            continue
        }

        pred_type := check_expr(c, predicate, env)
        if _, is_bool := pred_type.(Type_Bool); !is_bool {
            check_error(c, s.span, TYPE_PREDICATE_ARM_BOOL_MARA_DOESN, type_name(pred_type))
        }

        child := type_env_child(env)
        check_scope(c, arm.body, &child)
    }
}


// ---------------------------------------------------------------------------
// Check program — entry point
// ---------------------------------------------------------------------------

// Helper: extract a Checked_Scope from a Stmt_Scope using resolved types from an env.
// Extract function definitions from a scope's body into checked.functions.
extract_scope_fun_defs :: proc(checked: ^Checked_Program, defs: [dynamic]Stmt, env: ^Type_Env, main_package: string) {
    for def in defs {
        #partial switch s in def {
        case ^Stmt_Scope:
            // Always recurse into body for nested defs
            extract_scope_fun_defs(checked, s.body, env, main_package)
            // Extract callable funs as Checked_Scope
            cf, cf_ok := extract_checked_scope(s, env, checked.table)
            if cf_ok {
                fn_key := s.name
                // Prefix check uses the flat (underscored) form so dotted
                // module names like "mara.memory" match against already-flat
                // nested names like "mara_memory_Arena_Basic_mark".
                flat_pkg, _ := strings.replace_all(main_package, ".", "_")
                if main_package != "" && !strings.has_prefix(fn_key, fmt.tprintf("%s_", flat_pkg)) {
                    fn_key = make_flat_name(main_package, fn_key)
                }
                cf.name = fn_key
                checked.functions[fn_key] = cf
                append(&checked.function_order, fn_key)
            }
        case ^Stmt_If:
            // Comptime `#if`: recurse into the live arm so nested funs inside
            // (e.g., `#if #web { loop_iter :: fun(...) }`) get extracted for
            // codegen. Without this, the call site references a function that
            // was never emitted to the IR.
            if !s.is_comptime { continue }
            cond_true := false
            #partial switch v in s.condition {
            case ^Expr_Bool:               cond_true = v.value
            case ^Expr_Compiler_Intrinsic: cond_true = v.bool_value
            }
            live := s.body if cond_true else s.else_body
            extract_scope_fun_defs(checked, live, env, main_package)
        }
    }
}

extract_checked_scope :: proc(s: ^Stmt_Scope, env: ^Type_Env, table: ^SymbolTable = nil) -> (Checked_Scope, bool) {
    ft: ^Type_Scope
    if fun_type_raw, found := type_env_get(env, s.name); found {
        if v, ok := fun_type_raw.(^Type_Scope); ok { ft = v }
    }
    // Nested funs register their Type_Scope in body envs that aren't reachable
    // from the extract-time env. Fall back to the global table, looked up by
    // flat name (package + bare).
    if ft == nil && table != nil {
        if home, hok := table.fun_homes[s.name]; hok {
            ft = table.funs[make_flat_name(home, s.name)]
        }
    }
    if ft == nil { return {}, false }
    // Skip funs that have no callable signature (pure parameterless data funs without parens)
    // Exception: struct-kind scopes (struct/class) always get an init function emitted so
    // every construction path (including bare declaration `x: Foo`) can go through it.
    if len(ft.params) == 0 && len(ft.return_types) == 0 && !s.has_parens && ft.kind != .Struct {
        return {}, false
    }

    origin: Function_Origin = Origin_Source{}
    if s.is_intrinsic {
        origin = Origin_Intrinsic{llvm_name = s.intrinsic_name}
    }
    cf := Checked_Scope{
        name         = s.name,
        home_package = ft.home_package,
        type_        = ft,
        body         = s.body,
        ast          = s,
        origin       = origin,
        span         = s.span,
    }
    // Returns. Data funs with fields produce their own layout via sret when
    // the fun has no declared return.
    if len(ft.return_types) == 0 && ft.kind == .Struct && len(ft.fields) > 0 {
        append(&cf.return_types, distinct_base(Type(ft)))
    } else if len(ft.return_types) > 0 && ft.kind == .Struct {
        // Fallible constructor: Self is the implicit, in-place sret slot 0,
        // then the declared returns (the trailing err) follow. The body only
        // ever returns the declared slots — Self is built in place — so this
        // prepend is the codegen-facing mirror of constructor_effective_returns.
        append(&cf.return_types, distinct_base(Type(ft)))
        for rt in ft.return_types {
            append(&cf.return_types, distinct_base(rt))
        }
    } else {
        for rt in ft.return_types {
            append(&cf.return_types, distinct_base(rt))
        }
    }

    for p in ft.params {
        append(&cf.params, Checked_Param{name = p.name, type_ = distinct_base(p.type_)})
    }

    return cf, true
}

// ---------------------------------------------------------------------------
// Module system — modules are pre-parsed; checker looks up by name
// ---------------------------------------------------------------------------

// Resolve a `use <path>` to the module it names. Matching is EXACT: `use foo`
// pulls in the module declared `module foo` and nothing else. A submodule
// `foo.bar` is an independent module, reached only by an explicit `use foo.bar`
// (typically written inside `foo` itself — the way `gfx` does `use gfx.shader`).
// So a submodule stays private to whoever uses it, like any other dependency;
// there is no parent-glob that drags `foo.*` into a `use foo`.
//
// Returned as a 0-or-1 element list because the call sites iterate the result
// (empty = no such module; the caller reports TYPE_MODULE_FOUND).
find_matching_modules :: proc(c: ^Checker, path: string) -> [dynamic]string {
    result: [dynamic]string
    if path in c.programs {
        append(&result, path)
    }
    return result
}

// Get the Type_Scope for `name`, creating an empty synthetic scope if no
// module file declared exactly that name. Synthetic scopes exist purely to
// give dotted-module namespaces a real Type_Scope value — so a user can
// write `m := mara` even though there's no `module mara` file, and so
// qualified access like `mara.math.sin` flows through normal scope-member
// lookup instead of a parallel namespace-label mechanism.
get_or_synth_module_scope :: proc(c: ^Checker, name: string) -> ^Type_Scope {
    if existing, ok := c.checked_modules[name]; ok { return existing }
    synth := new(Type_Scope)
    synth.name = name
    synth.home_package = name  // module is its own home
    synth.kind = .Struct
    // Empty body — no fields, no top-level decls. Submodules will be
    // registered as members by register_in_parent_scopes.
    c.checked_modules[name] = synth
    c.table.funs[name] = synth
    if c.mara_env != nil {
        type_env_set(c.mara_env, name, synth)
    }
    // Recurse: synth's own parents also need it registered as a member.
    register_in_parent_scopes(c, name, synth)
    return synth
}

// For a dotted module name like "mara.gpu.opengl", register the loaded
// module as a member of every proper-prefix scope: `gpu` in mara, `opengl`
// in mara.gpu. Intermediate scopes are synthesized on demand. Called once
// per module load (at the end of check_module).
register_in_parent_scopes :: proc(c: ^Checker, module_name: string, mod: ^Type_Scope) {
    for i in 0..<len(module_name) {
        if module_name[i] != '.' { continue }
        prefix := module_name[:i]
        // Segment between this dot and the next dot (or end of name)
        seg_start := i + 1
        seg_end := len(module_name)
        for j in seg_start..<len(module_name) {
            if module_name[j] == '.' { seg_end = j; break }
        }
        seg := module_name[seg_start:seg_end]
        child_full := module_name[:seg_end]
        parent := get_or_synth_module_scope(c, prefix)
        child: ^Type_Scope = mod if child_full == module_name else get_or_synth_module_scope(c, child_full)
        if parent.types == nil { parent.types = make(map[string]Type) }
        parent.types[seg] = child
    }
}

// (lazy_load_module_program removed — all modules are pre-parsed and looked up
// from c.programs directly in check_module.)

// Type-check a module on demand (lazily, triggered by include).
// Returns a Type_Scope (module-struct) with scope set to the module's checked env.
// Modules are funs — Type_Scope with no data fields, only functions/types/scope.
check_module :: proc(c: ^Checker, module_name: string, span: Span) -> ^Type_Scope {
    // Return cached if already checked
    if existing, ok := c.checked_modules[module_name]; ok {
        return existing
    }

    // Circular dependency detection
    if module_name in c.modules_in_progress {
        check_error(c, span, TYPE_CIRCULAR_INCLUDE_MODULE_ALREADY_CHECKED, module_name)
        return nil
    }

    // The parsed program for this module is in c.programs (eagerly populated
    // before check_program ran).
    mod_program_ptr, found := c.programs[module_name]
    if !found {
        check_error(c, span, TYPE_MODULE_FOUND, module_name)
        return nil
    }
    mod_program := mod_program_ptr^

    c.modules_in_progress[module_name] = true

    // Create isolated env for this module. is_module_scope=true means the
    // env lookup walker stops here when looking up unqualified names —
    // module locals don't leak into sibling modules' lookup chains. But
    // we DO want module bodies to see the build-wide globals (context,
    // Context, std, void), which live in c.top_env (root) and otherwise
    // sit on the other side of the is_module_scope barrier. Copy them in
    // so the module's own functions can reference `context.X` etc., same
    // as a main package's file_env can.
    mod_env := new(Type_Env)
    mod_env.is_module_scope = true

    if c.top_env != nil {
        for name in ([]string{"this_program", "Program", "std", "void"}) {
            if t, ok := c.top_env.types[name]; ok {
                type_env_set(mod_env, name, t)
            }
        }
    }

    // If `void` wasn't in c.top_env yet (early in setup), register a fresh
    // null-pointer type so the module body's void literals still type-check.
    if _, has_void := mod_env.types["void"]; !has_void {
        void_type := new(Type_Ptr)
        void_type.elem = Type_Any{}
        type_env_set(mod_env, "void", void_type)
    }

    // Create module-struct upfront so it can own top-level declarations
    // during registration. Dispatch groups / operator overloads filled after
    // check_scope completes.
    mod_struct := new(Type_Scope)
    mod_struct.name = module_name
    mod_struct.home_package = module_name  // module is its own home
    mod_struct.kind = .Struct
    mod_struct.scope = mod_env
    mod_env.owner_module = mod_struct

    // Self-binding under the module's bare name was removed: the feature
    // (write `time.Timer` inside `module mara.time` to disambiguate from a
    // same-named imported type) cost more friction than it earned. Locals
    // and params named after the module's last path segment (e.g. `shader`
    // inside `module gfx.shader`) collided with the magic binding, and
    // undefined-identifier bugs got absorbed into confusing "expected u32,
    // got <module-type>" errors instead of surfacing as missing decls.
    // Authors can still disambiguate via fully-qualified `pkg.sub.Name` or
    // by renaming one side of the collision.

    // Save/restore checker state
    saved_package := c.current_package
    saved_dispatch := c.dispatch_groups
    saved_overloads := c.operator_overloads
    c.current_package = module_name
    c.dispatch_groups = {}
    c.operator_overloads = {}

    // Type-check the module's declarations and bodies, with mod_struct as
    // the owner so top-level decls are attached as functions/types.
    //
    // Per-file scoping: each .mara file in the module gets its own file_env
    // (parent = mod_env). Defined names (functions, structs, types, constants)
    // register into mod_env so siblings can see them. Include-introduced names
    // register into the originating file's file_env, so they stay private to
    // that file. Lookup chain inside a function body: body -> file_env ->
    // mod_env -> STOP (mod_env is_module_scope=true).
    files_by_src: map[string][dynamic]Stmt
    file_order: [dynamic]string
    for stmt in mod_program {
        src := stmt_span(stmt).file
        if _, exists := files_by_src[src]; !exists {
            files_by_src[src] = make([dynamic]Stmt)
            append(&file_order, src)
        }
        bucket := &files_by_src[src]
        append(bucket, stmt)
    }

    file_envs: map[string]^Type_Env
    for src in file_order {
        fe := new(Type_Env)
        fe.parent = mod_env
        file_envs[src] = fe
    }

    // Pass 1a: pre-register type and function NAMES across all files first,
    // so cross-file forward references in Pass 1b resolve regardless of
    // file order. Multi-file modules need this because file iteration order
    // is map-driven (hash-seeded, not deterministic). Single-file modules
    // run through the same path harmlessly — pre-registration just primes
    // the entries that Pass 1b would have allocated anyway.
    for src in file_order {
        register_type_names(c, files_by_src[src], file_envs[src], mod_struct, mod_env)
    }

    // Pass 1b: resolve body fields, base types, param/return types, and
    // check statement-level declarations. Pre-registered entries get filled
    // in; everything else (Stmt_Decl, Stmt_Assign, Stmt_Foreign, etc.)
    // runs the original allocation-and-resolve flow.
    for src in file_order {
        register_and_check_declarations(c, files_by_src[src], file_envs[src], mod_struct, mod_env)
    }

    // Pass 2a: resolve struct signatures (field types) across ALL files
    // before any file's Pass 2b body-check runs. Without this, a body in
    // one file that does `^OtherStruct`-field access against a struct
    // declared in another file may see an empty fields list — the per-file
    // check_bodies does its own Phase 2a, but that's too late: by the time
    // file A's check_bodies runs Phase 2a for file A's structs, file B's
    // check_bodies has already run Phase 2b body checks that may have
    // tried to resolve those fields. Hoisting Phase 2a to the module
    // level fixes the same cross-file forward-ref class of bug that the
    // Pass 1a hoist fixed for registration.
    for src in file_order {
        for stmt in files_by_src[src] {
            if sc, ok := stmt.(^Stmt_Scope); ok && sc.kind == .Struct {
                check_scope_body(c, sc, file_envs[src], signature_only = true)
            }
        }
    }

    // Pass 2: type-check function bodies per-file under the file's env.
    for src in file_order {
        check_bodies(c, files_by_src[src], file_envs[src])
    }

    // Preserve module's dispatch groups for propagation on `using include`
    mod_struct.dispatch_groups = c.dispatch_groups
    mod_struct.operator_overloads = c.operator_overloads

    // Restore checker state
    c.current_package = saved_package
    c.dispatch_groups = saved_dispatch
    c.operator_overloads = saved_overloads
    delete_key(&c.modules_in_progress, module_name)

    // Extract functions/types into checked and populate functions/types
    extract_module_into_checked(c, mod_program, mod_env, module_name, mod_struct)

    // Cache and register in struct table so type-qualified lookup works
    c.checked_modules[module_name] = mod_struct
    c.table.funs[module_name] = mod_struct

    // Register in the appropriate scope for scope-based include resolution.
    // Stdlib modules (dotted "mara.X") get the leaf segment in std_fun scope
    // so qualified access like `math.sin` works inside includer code.
    // Other modules go into mara_env (root scope) under their full name.
    if strings.has_prefix(module_name, "mara.") && c.std_fun != nil {
        bare := module_name[len("mara."):]  // "mara.math" -> "math"
        type_env_set(c.std_fun.scope, bare, mod_struct)
    } else if c.mara_env != nil {
        type_env_set(c.mara_env, module_name, mod_struct)
    }

    // Walk up the dotted name and register this module as a member of every
    // proper-prefix scope. For "mara.gpu.opengl" this registers `gpu` in
    // mara (synthesizing mara as an empty scope if no file declared it) and
    // `opengl` in mara.gpu. Lets `mara.gpu.opengl.X` flow through normal
    // scope-member access without a parallel namespace-label mechanism.
    register_in_parent_scopes(c, module_name, mod_struct)

    return mod_struct
}

// Build a Checked_Scope for a single foreign function declaration. Handles
// link-name prefix concatenation and propagates origin metadata.
//
// Enforces the global link_name uniqueness rule: each external symbol may be
// declared by exactly one `foreign` block across the program. If another
// foreign with the same link_name is already registered, this surfaces a
// type error pointing at both definition sites. SDL2/SDL3 dual support is
// not provided — projects that genuinely need to load both versions must
// rename one side via `prefix`.
make_foreign_checked_scope :: proc(c: ^Checker, decl: Foreign_Fun, ft: ^Type_Scope, library, prefix: string) -> Checked_Scope {
    ln := decl.name
    if prefix != "" {
        ln = strings.concatenate({prefix, decl.name})
    }
    if c.checked != nil {
        for _, existing in c.checked.functions {
            fo, is_foreign := existing.origin.(Origin_Foreign)
            if !is_foreign { continue }
            if fo.link_name != ln { continue }
            check_error(c, decl.span,
                TYPE_FOREIGN_SYMBOL_ALREADY_DECLARED_LIBRARY,
                ln, fo.library, span_loc(existing.span))
            break
        }
    }
    cs := Checked_Scope{
        name         = decl.name,
        home_package = ft.home_package,
        type_        = ft,
        ast          = nil,
        origin       = Origin_Foreign{
            library    = library,
            link_name  = ln,
            prefix     = prefix,
        },
        span        = decl.span,
    }
    for rt in ft.return_types { append(&cs.return_types, distinct_base(rt)) }
    for p in ft.params {
        append(&cs.params, Checked_Param{name = p.name, type_ = distinct_base(p.type_)})
    }
    return cs
}

// Walk a struct/class body for foreign blocks and register their decls in
// checked.functions with origin=Origin_Foreign and a flat key prefixed by
// the enclosing struct's flat name. The key matches what register_scope_defs
// stamped onto the foreign's Type_Scope.name and what call_resolved_name
// produces at the call site. Recurses into nested struct bodies so deeper
// nesting works without further changes. (Module-level foreign extraction
// is handled directly in extract_module_into_checked.)
extract_nested_foreigns_into_checked :: proc(c: ^Checker, body: [dynamic]Stmt, mod_env: ^Type_Env, struct_flat_name: string) {
    checked := c.checked
    if checked == nil { return }
    for stmt in body {
        #partial switch s in stmt {
        case ^Stmt_Foreign:
            checked.foreign_libs[s.library] = true
            for decl in s.decls {
                ff_key := make_flat_name(struct_flat_name, decl.name)
                ft_raw, ft_found := type_env_get(mod_env, ff_key)
                if !ft_found {
                    // Fall back to the global tables — register_scope_defs
                    // wrote root_env, which may not be reachable from mod_env
                    // when the struct sits inside a sealed/private file scope.
                    if t, ok := c.table.funs[ff_key]; ok { ft_raw = t; ft_found = true }
                }
                ft, ft_ok := ft_raw.(^Type_Scope)
                if !ft_ok { continue }
                checked.functions[ff_key] = make_foreign_checked_scope(c, decl, ft, s.library, s.prefix)
            }
        case ^Stmt_Scope:
            if s.kind == .Struct {
                inner_flat := make_flat_name(struct_flat_name, s.name)
                extract_nested_foreigns_into_checked(c, s.body, mod_env, inner_flat)
            }
        case ^Stmt_If:
            if !s.is_comptime { continue }
            live, ok := evaluate_comptime_bool(c, s.condition)
            if !ok { continue }
            if live {
                extract_nested_foreigns_into_checked(c, s.body, mod_env, struct_flat_name)
            } else if len(s.else_body) > 0 {
                extract_nested_foreigns_into_checked(c, s.else_body, mod_env, struct_flat_name)
            }
        }
    }
}

// Extract all declarations from a checked module into the Checked_Program for codegen.
// Handles: functions, foreign declarations, types, constants, and variables.
// Also populates the module-struct's functions/types.
extract_module_into_checked :: proc(c: ^Checker, stmts: [dynamic]Stmt, mod_env: ^Type_Env, module_name: string, mod_struct: ^Type_Scope = nil) {
    checked := c.checked
    if checked == nil { return }

    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            // Always extract scoped function defs from body
            extract_scope_fun_defs(checked, s.body, mod_env, module_name)
            // Foreign blocks inside a struct body are registered by
            // register_scope_defs against the struct's mangled name; mirror
            // that here for the codegen side so foreign_funs is keyed under
            // the nested flat name that call_resolved_name produces.
            if s.kind == .Struct {
                struct_flat := make_flat_name(module_name, s.name)
                extract_nested_foreigns_into_checked(c, s.body, mod_env, struct_flat)
            }
            // mod_struct.types / functions attachments are handled by
            // register_and_check_declarations' owner-threading (Step B).
            // Extract as Checked_Scope — extract_checked_scope decides based on
            // kind/params/has_parens whether this scope is callable. Pure struct
            // scopes are now always extracted so every construction path goes
            // through a generated init function.
            cf, cf_ok := extract_checked_scope(s, mod_env, c.table)
            // `main` is special — it's the program entry point, only meaningful
            // when extracted via extract_main_program_stmts (which registers it
            // under the bare key "main", consumed by the @main codegen wrapper).
            // Skip it when walked as a regular module here.
            if cf_ok && s.name != "main" {
                flat_key := make_flat_name(module_name, s.name)
                // Dedup: a main package can also be imported as a module by
                // another main package, in which case the same function gets
                // walked twice — once here, once via extract_main_program_stmts.
                // Same content either way; just don't add to function_order
                // twice or codegen emits the function definition twice.
                _, already := checked.functions[flat_key]
                cf.name = flat_key
                checked.functions[flat_key] = cf
                if !already {
                    append(&checked.function_order, flat_key)
                }
            }
        case ^Stmt_Foreign:
            checked.foreign_libs[s.library] = true
            for decl in s.decls {
                fun_type_raw, _ := type_env_get(mod_env, decl.name)
                ft, ft_ok := fun_type_raw.(^Type_Scope)
                if !ft_ok { continue }
                ff_key := make_flat_name(module_name, decl.name)
                checked.functions[ff_key] = make_foreign_checked_scope(c, decl, ft, s.library, s.prefix)
                // Owner attachment is handled by register_and_check_declarations.
            }
        case ^Stmt_If:
            // Top-level comptime `#if`: extract decls from the live arm so
            // functions / constants from `#if #native { ... }`
            // make it into the codegen output. Mirrors the Pass 1 recursion.
            if !s.is_comptime { continue }
            live, ok := evaluate_comptime_bool(c, s.condition)
            if !ok { continue }
            if live {
                extract_module_into_checked(c, s.body, mod_env, module_name, mod_struct)
            } else if len(s.else_body) > 0 {
                extract_module_into_checked(c, s.else_body, mod_env, module_name, mod_struct)
            }
            continue
        // Stmt_Union_Def owner attachment is handled by register_and_check_declarations.
        }

        // Handle top-level variable/constant declarations.
        // Module variables are effectively compile-time values — store in constants
        // so codegen can resolve them cross-function (g.all_vars is per-function).
        if assign, ok := stmt.(^Stmt_Assign); ok {
            if _, is_include := assign.value.(^Expr_Include); !is_include && assign.value != nil {
                register_module_constant(c, module_name, assign.name, assign.value)
            }
        }
        // Multi-assign: flatten each inner assign
        if multi, ok := stmt.(^Stmt_Multi_Assign); ok {
            for a in multi.assigns {
                if a.value != nil {
                    register_module_constant(c, module_name, a.name, a.value)
                }
            }
        }
        // Stmt_Decl: iterate the desugared entries (same shape as Stmt_Assign / Stmt_Multi_Assign cases above).
        if decl, ok := stmt.(^Stmt_Decl); ok {
            for inner in decl.checked {
                if a, aok := inner.(^Stmt_Assign); aok {
                    if _, is_include := a.value.(^Expr_Include); !is_include && a.value != nil {
                        register_module_constant(c, module_name, a.name, a.value)
                    }
                }
            }
        }
        // Stmt_Define: `name :: value` or `name : Type : value` — always a compile-time constant.
        // Skip include forms (`name :: include path`) — those are handled by the
        // include-processing path in register_and_check_declarations, same as
        // `name := include path`.
        if def, ok := stmt.(^Stmt_Define); ok {
            if _, is_include := def.value.(^Expr_Include); !is_include && def.value != nil {
                register_module_constant(c, module_name, def.name, def.value)
            }
        }
    }
}

// Walk a main-package file's top-level statements and register every constant
// definition (Stmt_Define / Stmt_Assign / Stmt_Decl / Stmt_Multi_Assign) into
// c.table.constants. Mirrors the loop in extract_module_into_checked that
// runs for imported modules — the main package didn't have an equivalent
// hook before this pass.
register_main_top_level_constants :: proc(c: ^Checker, stmts: [dynamic]Stmt, module_name: string) {
    if module_name == "" { return }
    for stmt in stmts {
        if assign, ok := stmt.(^Stmt_Assign); ok {
            if _, is_include := assign.value.(^Expr_Include); !is_include && assign.value != nil {
                register_module_constant(c, module_name, assign.name, assign.value)
            }
        }
        if multi, ok := stmt.(^Stmt_Multi_Assign); ok {
            for a in multi.assigns {
                if a.value != nil {
                    register_module_constant(c, module_name, a.name, a.value)
                }
            }
        }
        if decl, ok := stmt.(^Stmt_Decl); ok {
            for inner in decl.checked {
                if a, aok := inner.(^Stmt_Assign); aok {
                    if _, is_include := a.value.(^Expr_Include); !is_include && a.value != nil {
                        register_module_constant(c, module_name, a.name, a.value)
                    }
                }
            }
        }
        if def, ok := stmt.(^Stmt_Define); ok {
            if _, is_include := def.value.(^Expr_Include); !is_include && def.value != nil {
                register_module_constant(c, module_name, def.name, def.value)
            }
        }
    }
}

// Insert a top-level module constant into c.table.constants. The flat
// (mangled) name is always inserted. The bare name is inserted only when no
// other module has registered the same bare name; subsequent registrations
// from a different module flag the bare name as ambiguous in
// c.table.constant_owners, so bare-name uses error and the user must qualify.
register_module_constant :: proc(c: ^Checker, module_name: string, bare: string, value: Expr) {
    flat := make_flat_name(module_name, bare)
    c.table.constants[flat] = value
    if existing, mapped := c.table.constant_owners[bare]; mapped {
        if existing == module_name {
            // Same module re-registering: idempotent.
            return
        }
        // Different module already owns this bare name — ambiguous.
        c.table.constant_owners[bare] = ""
        return
    }
    c.table.constant_owners[bare] = module_name
    c.table.constants[bare] = value
}

// Validate that the scope allocator fun has the expected API:
// Arena (inner type), new, mark, alloc, reset (assoc fns).
validate_scope_allocator :: proc(c: ^Checker) {
    name := c.table.scope_allocator_name
    if name == "" {
        check_error(c, {},
            TYPE_PROGRAM_GLOBAL_REQUIRES_ALLOCATOR_TYPE)
        c.table.has_scope_allocator = false
        return
    }

    // Find any flat name matching `*_<name>`. validate runs after all type
    // tables are built; we scan funs directly rather than relying on a
    // resolution helper, since main's env isn't readily available here.
    suffix := strings.concatenate({"_", name})
    alloc_type: ^Type_Scope
    for fname, ft in c.table.funs {
        if ft.functions == nil { continue }
        if strings.has_suffix(fname, suffix) || fname == name {
            alloc_type = ft
            break
        }
    }
    if alloc_type == nil {
        check_error(c, {},
            TYPE_PROGRAM_SCOPE_ALLOCATOR_KNOWN_TYPE, name)
        c.table.has_scope_allocator = false
        return
    }

    // Flat form: the allocator class itself is the arena — methods (mark,
    // alloc, reset) take ^Self as first param. No inner Arena type needed.

    // Check required functions (new is no longer required — the allocator's
    // constructor is the class itself)
    required_fns := [?]string{"mark", "alloc", "reset"}
    for req in required_fns {
        if alloc_type.functions == nil || req not_in alloc_type.functions {
            check_error(c, {},
                TYPE_PROGRAM_SCOPE_ALLOCATOR_MISSING_REQUIRED, name, req)
            c.table.has_scope_allocator = false
            return
        }
    }

    c.table.scope_allocator_type = alloc_type
}

// Extract top-level decls from the main package's program into Checked_Program.
// Recurses through comptime `#if` so e.g. shader source `::` constants and
// foreign decls inside `#if #web { ... }` reach codegen. Mirrors the analogous
// gap that was already fixed in extract_module_into_checked.
extract_main_program_stmts :: proc(c: ^Checker, checked: ^Checked_Program, stmts: [dynamic]Stmt, env: ^Type_Env, main_package: string) {
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            extract_scope_fun_defs(checked, s.body, env, main_package)
            cf, cf_ok := extract_checked_scope(s, env, c.table)
            if cf_ok {
                fn_key := s.name
                if s.name != "main" && main_package != "" {
                    fn_key = make_flat_name(main_package, s.name)
                }
                // Dedup: if this main package was also walked as an imported
                // module (when another main package's `use` brought it in),
                // its non-main functions are already in function_order under
                // the same flat key. See the matching guard in
                // extract_module_into_checked.
                _, already := checked.functions[fn_key]
                cf.name = fn_key
                checked.functions[fn_key] = cf
                if !already {
                    append(&checked.function_order, fn_key)
                }
            }
        case ^Stmt_Foreign:
            checked.foreign_libs[s.library] = true
            for decl in s.decls {
                fun_type_raw, _ := type_env_get(env, decl.name)
                ft, ft_ok := fun_type_raw.(^Type_Scope)
                if !ft_ok { continue }
                ff_key := decl.name
                if main_package != "" {
                    ff_key = make_flat_name(main_package, decl.name)
                }
                checked.functions[ff_key] = make_foreign_checked_scope(c, decl, ft, s.library, s.prefix)
            }
        case ^Stmt_If:
            if !s.is_comptime { continue }
            cond_true := false
            #partial switch v in s.condition {
            case ^Expr_Bool:               cond_true = v.value
            case ^Expr_Compiler_Intrinsic: cond_true = v.bool_value
            }
            if cond_true {
                extract_main_program_stmts(c, checked, s.body, env, main_package)
            } else if len(s.else_body) > 0 {
                extract_main_program_stmts(c, checked, s.else_body, env, main_package)
            }
            continue
        }
        if def, ok := stmt.(^Stmt_Define); ok {
            if _, is_include := def.value.(^Expr_Include); !is_include && def.value != nil {
                if main_package != "" {
                    flat := make_flat_name(main_package, def.name)
                    checked.table.constants[flat] = def.value
                }
                checked.table.constants[def.name] = def.value
            }
        }
    }
}

// Validate top-level statements are declarations (no bare executable code).
// Recurses through comptime `#if` so decls inside `#if #web { ... }` etc. count
// as top-level for validation purposes.
validate_top_level_stmts :: proc(c: ^Checker, stmts: [dynamic]Stmt, found_main: ^bool) {
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            if s.name == "main" {
                found_main^ = true
                is_void := len(s.return_types) == 0
                is_int := false
                if !is_void {
                    if len(s.return_types) > 1 {
                        check_error(c, s.span, TYPE_FUN_MAIN_RETURN_INT_RETURN)
                    } else {
                        ret := resolve_type_expr(s.return_types[0], c, s.span)
                        if is_any(ret) { is_void = true }
                        // main may return i64 — the process exit code.
                        if vn, ok := ret.(Type_Numeric); ok && vn.kind == .Signed && vn.bits == 64 { is_int = true }
                    }
                }
                if !is_void && !is_int {
                    check_error(c, s.span, TYPE_FUN_MAIN_RETURN_INT_RETURN)
                }
                if len(s.typed_params) != 0 {
                    check_error(c, s.span, TYPE_FUN_MAIN_TAKE_PARAMETERS)
                }
            }
            // `#expose fun foo(ctx: ^Context, ...)` — DLL entry points must
            // take a Context pointer as their first param. Each call stores it
            // into the DLL's @__mara_context, so internal Mara code inside the
            // DLL sees the host's context. Skipping the param means the global
            // is never populated and the first internal `context.X` access
            // dereferences null.
            if s.is_exposed {
                ok := false
                if len(s.typed_params) > 0 {
                    first := s.typed_params[0]
                    pt := resolve_type_expr(first.type_expr, c, s.span)
                    if ptr, is_ptr := pt.(^Type_Ptr); is_ptr {
                        if ts, is_scope := ptr.elem.(^Type_Scope); is_scope && ts.name == "Program" {
                            ok = true
                        }
                    }
                }
                if !ok {
                    check_error(c, s.span, TYPE_EXPOSE_FUNCTION_TAKE_FIRST_PARAMETER, s.name)
                }
            }
        case ^Stmt_If:
            if !s.is_comptime {
                check_error(c, s.span, TYPE_EXECUTABLE_STATEMENTS_INSIDE_FUN_MAIN)
                continue
            }
            // Recurse into the live arm. Pass 1 already evaluated and the
            // condition's bool_value is populated; we only need to walk one
            // arm to mirror what register/codegen actually keep.
            cond_true := false
            #partial switch v in s.condition {
            case ^Expr_Bool:               cond_true = v.value
            case ^Expr_Compiler_Intrinsic: cond_true = v.bool_value
            }
            if cond_true {
                validate_top_level_stmts(c, s.body, found_main)
            } else if len(s.else_body) > 0 {
                validate_top_level_stmts(c, s.else_body, found_main)
            }
        case ^Stmt_Assign, ^Stmt_Multi_Assign, ^Stmt_Multi_Return_Assign,
             ^Stmt_Decl, ^Stmt_Define, ^Stmt_Foreign, ^Stmt_Union_Def,
             Stmt_Module, ^Stmt_Dispatch_Def, Stmt_Overload, ^Stmt_Distinct_Def:
            // Allowed at top level.
        case:
            check_error(c, stmt_span(stmt), TYPE_EXECUTABLE_STATEMENTS_INSIDE_FUN_MAIN)
        }
    }
}

// Type-check the requested main package in a single pass. Imports reached
// via `use`/`include` are processed exactly once via c.checked_modules.
check_program :: proc(programs: map[string]^Program, main_package: string,
                      compiler_dir: string = "", search_dir: string = "", web: bool = false,
                      shared: bool = false,
                      target_os: Target_OS = .Windows) -> ^Checked_Program {
    table := new(SymbolTable)
    env := new(Type_Env)       // heap-allocated so it outlives check_program
    env.is_module_scope = true // root env is the main package's module scope; lookup terminates here
    table.root_env = env

    c := Checker{ table = table }
    checked := new(Checked_Program)
    checked.table = table
    checked.target_os = target_os
    checked.main_package = main_package
    c.checked = checked
    c.programs = programs
    c.compiler_dir = compiler_dir
    c.search_dir = search_dir
    c.target_web    = web
    // target_shared relaxes the "scope_allocator must live in main" rule
    // so DLLs can declare it in any top-level fn.
    c.target_shared = shared
    c.target_os     = target_os

    main_prog, prog_ok := programs[main_package]
    if !prog_ok {
        check_error(&c, {}, "no parsed program for main package '%s'", main_package)
        checked.errors = c.errors
        return checked
    }

    // Program structure: mara :: fun { std :: fun { ... }, user_modules... }
    // mara_env is the root scope containing std and user modules.
    // The main package is checked inside mara_env.
    c.mara_env = env  // for now, reuse root env as mara scope
    std_fun := new(Type_Scope)
    std_fun.name = "std"
    std_fun.home_package = "std"
    std_fun.kind = .Struct
    std_fun.scope = new(Type_Env)
    std_fun.scope.parent = env
    c.std_fun = std_fun
    type_env_set(env, "std", std_fun)

    // Phase 0: Pre-scan main's body for `this_program = Program(...)` setup.
    // Must happen before package checking so big-array errors in imported
    // packages know whether a scope allocator is available.
    //
    // Two shapes accepted (both supplied by the shape-shortcut desugar at
    // type-check time, but Phase 0 runs before desugar — so we peel the
    // shapes here directly):
    //
    //   this_program = Program(Arena_Debug(50 * MB))   // shortcut form
    //   this_program = Program(Arena_Debug)            // type-only; user
    //                                                  //   assigns to
    //                                                  //   this_program.scope_allocator
    //                                                  //   later (not yet supported
    //                                                  //   in this scan)
    //
    // Bare `this_program = Program()` and `this_program : Program` mean the
    // void default — no arena, allocation sites fail with a clear diagnostic.
    scan_allocator :: proc(c: ^Checker, target: Expr, value: Expr) {
        ident, id_ok := target.(^Expr_Ident)
        if !id_ok || ident.name != "this_program" { return }
        // Drill: `this_program = Program(<arena_ctor_or_type>)`.
        outer_call, outer_ok := value.(^Expr_Call)
        if !outer_ok || outer_call.name != "Program" { return }
        if len(outer_call.args) == 0 { return } // Program() -> void default
        // The arena spec is the first arg. Two valid shapes: another call
        // (the shortcut form: Arena_Debug(50 * MB)) or a bare ident (just
        // the type). Either way, the arena type's NAME is what we record.
        arena_arg := outer_call.args[0]
        c.table.has_scope_allocator = true
        if inner_call, ic_ok := arena_arg.(^Expr_Call); ic_ok {
            c.table.scope_allocator_name = inner_call.name
            c.table.scope_allocator_args = inner_call.args
        } else if inner_ident, ii_ok := arena_arg.(^Expr_Ident); ii_ok {
            c.table.scope_allocator_name = inner_ident.name
        }
    }
    // Scope_allocator scan: walk the main package plus the `main`s of every
    // module reachable transitively via `use`/`include`.
    scan_visited: map[string]bool
    scan_queue: [dynamic]string
    scan_visited[main_package] = true
    append(&scan_queue, main_package)
    qi := 0
    for qi < len(scan_queue) {
        pkg := scan_queue[qi]
        qi += 1
        prog, ok := programs[pkg]
        if !ok { continue }
        for stmt in prog^ {
            // Bare `use path` / `include path` lower to Stmt_Decl whose
            // init value is an Expr_Include; aliased `name :: use path`
            // becomes Stmt_Define. Both forms count as edges.
            if decl, is_decl := stmt.(^Stmt_Decl); is_decl {
                for v in decl.init_values {
                    if inc, is_inc := v.(^Expr_Include); is_inc {
                        if inc.path not_in scan_visited {
                            scan_visited[inc.path] = true
                            append(&scan_queue, inc.path)
                        }
                    }
                }
            } else if def, is_def := stmt.(^Stmt_Define); is_def {
                if inc, is_inc := def.value.(^Expr_Include); is_inc {
                    if inc.path not_in scan_visited {
                        scan_visited[inc.path] = true
                        append(&scan_queue, inc.path)
                    }
                }
            }
        }
    }
    for pkg, _ in scan_visited {
        prog, ok := programs[pkg]
        if !ok { continue }
        for stmt in prog^ {
            if fn_stmt, ok := stmt.(^Stmt_Scope); ok {
                if fn_stmt.name != "main" && !c.target_shared { continue }
                for body_stmt in fn_stmt.body {
                    if a, a_ok := body_stmt.(^Stmt_Assign); a_ok && a.target == nil && !a.is_decl {
                        // Bare-name reassignment: synthesise an Expr_Ident for
                        // the LHS so scan_allocator can match against `this_program`.
                        synth := new(Expr_Ident)
                        synth.name = a.name
                        synth.span = a.span
                        scan_allocator(&c, synth, a.value)
                    }
                }
            }
        }
    }

    // #expose-presence scan: the flag affects compile-time gates for this
    // binary's body. Only meaningful when this build target is a DLL.
    if c.target_shared {
        for stmt in main_prog^ {
            if fn_stmt, ok := stmt.(^Stmt_Scope); ok && fn_stmt.is_exposed {
                c.table.context_expected_at_runtime = true
                break
            }
        }
    }

    // Build Context struct: { arena? , args: [..64][, 0]utf8 }
    {
        ARGS_CAP :: 64
        // Element type: [, 0]utf8 sentinel-terminated slice
        arg_slice := new(Type_Slice)
        arg_slice.elem = Type_Byte{}
        arg_slice.has_sentinel = true
        arg_slice.sentinel = 0

        // Args is a partial array: [..64][, 0]utf8 — header {len,cap,ptr}
        // followed by inline [64 x slice] storage.
        args_type := new(Type_Partial_Array)
        args_type.size = ARGS_CAP
        args_type.elem = arg_slice

        // Program struct (the compiler-managed global). Shape mirrors the
        // user's `Program` declaration in mara.core (a generic struct over
        // `~Arena`). Here we synthesize a parallel type bound in env as
        // `this_program` so allocation sites can resolve
        // `this_program.scope_allocator` and `this_program.args` without
        // depending on the user having loaded mara.core. The user's generic
        // `Program` template stays in generic_templates under the bare name
        // "Program" — separate path.
        prog_type := new(Type_Scope)
        prog_type.name = "Program"
        // Synthetic Program belongs to the main package — that's the only TU
        // that will emit its init body, so cross-module references resolve
        // there. Without a real home_package, the per-module IR split has
        // nowhere to put its definition and downstream modules can't extern
        // it.
        prog_type.home_package = main_package
        prog_type.kind = .Struct
        field_idx := 0
        if c.table.has_scope_allocator {
            append(&prog_type.fields, Struct_Type_Field{name = "scope_allocator", type_ = Type_Any{}})
            prog_type.field_map["scope_allocator"] = field_idx
            field_idx += 1
        }
        append(&prog_type.fields, Struct_Type_Field{name = "args", type_ = args_type})
        prog_type.field_map["args"] = field_idx
        c.table.funs["Program"] = prog_type
        type_env_set(env, "this_program", prog_type)
        // Expose `Program` (the type name) for cross-DLL signatures like
        // `game_run : fn(^Program, ...)`. The user's generic Program template
        // also lives in c.table.generic_templates under the same bare name —
        // env binding wins for type-expr lookups via resolve_type_expr, so
        // `^Program` here resolves to the synthesized program-global type.
        type_env_set(env, "Program", prog_type)
    }

    // Register `void` as the built-in null-pointer literal. Reads as
    // "this pointer points into the void — no data to be read there".
    void_type := new(Type_Ptr)
    void_type.elem = Type_Any{}
    type_env_set(env, "void", void_type)

    // Phase 1: Scope-based checking of every main package, in turn.
    // Imports reached from any of them go through check_module which caches
    // results in c.checked_modules — so a stdlib AST that's used by two
    // main packages is processed exactly once.
    c.top_env = env

    // Per-file scoping: each .mara file in the main package gets its own
    // file_env (parent = root env). Defined names register into the package
    // env via public_env; include-introduced names stay file-private.
    c.current_package = main_package
    {
        main_files_by_src: map[string][dynamic]Stmt
        main_file_order: [dynamic]string
        for stmt in main_prog^ {
            src := stmt_span(stmt).file
            if _, exists := main_files_by_src[src]; !exists {
                main_files_by_src[src] = make([dynamic]Stmt)
                append(&main_file_order, src)
            }
            bucket := &main_files_by_src[src]
            append(bucket, stmt)
        }

        main_file_envs: map[string]^Type_Env
        for src in main_file_order {
            fe := new(Type_Env)
            fe.parent = env
            main_file_envs[src] = fe
        }

        // Pass 1a: pre-register names across all files in this package.
        for src in main_file_order {
            register_type_names(&c, main_files_by_src[src], main_file_envs[src], nil, env)
        }

        // Pass 1b: register declarations per-file.
        for src in main_file_order {
            register_and_check_declarations(&c, main_files_by_src[src], main_file_envs[src], nil, env)
        }

        // Pass 1.5: register main package's top-level constants in
        // c.table.constants so body-check-time lookups can find them.
        for src in main_file_order {
            register_main_top_level_constants(&c, main_files_by_src[src], main_package)
        }

        // Pass 2a: resolve struct signatures across this package's files
        // before any Pass 2b body-check runs.
        for src in main_file_order {
            for stmt in main_files_by_src[src] {
                if sc, ok := stmt.(^Stmt_Scope); ok && sc.kind == .Struct {
                    check_scope_body(&c, sc, main_file_envs[src], signature_only = true)
                }
            }
        }

        // Pass 2: type-check function bodies per-file under the file's env.
        for src in main_file_order {
            check_bodies(&c, main_files_by_src[src], main_file_envs[src])
        }

        // Register a synthetic module-struct for any `use` of this package
        // (still possible from imported modules that happen to reference it).
        if _, already := c.checked_modules[main_package]; !already {
            mod_struct := new(Type_Scope)
            mod_struct.name = main_package
            mod_struct.home_package = main_package
            mod_struct.kind = .Struct
            mod_struct.scope = new(Type_Env)
            mod_struct.scope.is_module_scope = true
            c.checked_modules[main_package] = mod_struct
        }
    }

    // Validate scope allocator API after all types are resolved.
    if c.table.has_scope_allocator {
        validate_scope_allocator(&c)
    }

    // Phase 2: Extract checked info from the completed scope.
    // Type definitions are already shared via table pointer — no copying needed.
    // Extract resolved constant values for codegen.
    for name, expr in c.table.constants {
        if _, i_val, ok := extract_constant_value(expr); ok {
            checked.constant_values[name] = int(i_val)
        }
    }

    // Extract functions, foreign declarations, and globals from the main
    // package's program. They contribute to checked.functions under the
    // package's flat-name prefix (with `main` itself staying unprefixed).
    c.current_package = main_package
    extract_main_program_stmts(&c, checked, main_prog^, env, main_package)

    // Phase 2.5: Extract monomorphized generic functions into checked.functions.
    for mangled_name, tmpl_name in c.table.mono_fun_cache {
        ft, ft_ok := c.table.mono_cache[mangled_name]
        if !ft_ok { continue }

        // Direct lookup of the template AST by stored template name
        tmpl_ast: ^Stmt_Scope
        tmpl_home := ""
        if tmpl, ok := c.table.generic_templates[tmpl_name]; ok {
            tmpl_ast = tmpl.ast
            tmpl_home = tmpl.home_package
        }
        // Also check concrete function ASTs (for auto-monomorphized functions)
        if tmpl_ast == nil {
            if fun_ast, fa_ok := c.table.fun_asts[tmpl_name]; fa_ok {
                tmpl_ast = fun_ast
                tmpl_home = c.table.fun_homes[tmpl_name]
            }
        }
        if tmpl_ast == nil { continue }

        // Use flat name (package-prefixed) as key so codegen lookups match resolved_func names
        flat_key := make_flat_name(tmpl_home, mangled_name)
        // Use cloned body if available (each monomorphization has independent type annotations)
        body := c.table.mono_fun_bodies[mangled_name] if mangled_name in c.table.mono_fun_bodies else tmpl_ast.body
        cf := Checked_Scope{
            name         = flat_key,
            home_package = tmpl_home,
            type_        = ft,
            body         = body,
            span         = tmpl_ast.span,
        }
        for rt in ft.return_types { append(&cf.return_types, distinct_base(rt)) }
        for p in ft.params {
            append(&cf.params, Checked_Param{name = p.name, type_ = distinct_base(p.type_)})
        }
        checked.functions[flat_key] = cf
    }

    // Phase 3: Validate the main package's program structure. Exe packages
    // (non-shared) must define fun main(); DLL packages can rely on #expose
    // and don't require main.
    found_main := false
    validate_top_level_stmts(&c, main_prog^, &found_main)
    if !found_main && !shared {
        check_error(&c, {}, "package '%s' must define fun main()", main_package)
    }

    // Sanity check (debug builds only): every named entity should have a
    // home_package set. Empty home_package on a registered named entity
    // indicates a missed population site. Built-in primitives ("Program",
    // anonymous fn-pointer types from Type_Func_Expr) are expected to be
    // empty and skipped here.
    when ODIN_DEBUG {
        audit_home_package(checked)
    }

    checked.errors = c.errors
    return checked
}

@(private="file")
audit_home_package :: proc(checked: ^Checked_Program) {
    skip :: proc(name: string) -> bool {
        // Compiler-synthesized + structural-anonymous types that legitimately
        // have no home module.
        return name == "" || name == "Program" || name == "std"
    }
    missing := 0
    for k, st in checked.table.structs {
        if skip(k) { continue }
        if st.home_package == "" {
            fmt.printf("audit: struct '%s' has no home_package\n", k)
            missing += 1
        }
    }
    for k, ft in checked.table.funs {
        if skip(k) { continue }
        if ft.home_package == "" {
            fmt.printf("audit: fun '%s' has no home_package\n", k)
            missing += 1
        }
    }
    for k, et in checked.table.enums {
        if skip(k) { continue }
        if et.home_package == "" {
            fmt.printf("audit: enum '%s' has no home_package\n", k)
            missing += 1
        }
    }
    for k, ut in checked.table.unions {
        if skip(k) { continue }
        if ut.home_package == "" {
            fmt.printf("audit: union '%s' has no home_package\n", k)
            missing += 1
        }
    }
    for k, dt in checked.table.distinct_types {
        if skip(k) { continue }
        if dt.home_package == "" {
            fmt.printf("audit: distinct '%s' has no home_package\n", k)
            missing += 1
        }
    }
    for k, cf in checked.functions {
        if skip(k) { continue }
        if cf.home_package == "" {
            fmt.printf("audit: checked fn '%s' has no home_package\n", k)
            missing += 1
        }
    }
    if missing > 0 {
        fmt.printf("audit: %d named entities missing home_package\n", missing)
    }
}


// Get the span from any statement variant
stmt_span :: proc(stmt: Stmt) -> Span {
    switch s in stmt {
    case ^Stmt_Assign:       return s.span
    case ^Stmt_Multi_Assign: return s.span
    case ^Stmt_Multi_Return_Assign: return s.span
    case Stmt_Call:         return s.span
    case ^Stmt_If:          return s.span
    case ^Stmt_For:         return s.span
    case ^Stmt_Scope:         return s.span
    case Stmt_Return:       return s.span
    case Stmt_Break:        return s.span
    case Stmt_Continue:     return s.span
    case ^Stmt_Defer:       return s.span
    case ^Stmt_Match:       return s.span
    case ^Stmt_Foreign:     return s.span
    case ^Stmt_Union_Def:     return s.span
    case ^Stmt_Distinct_Def:  return s.span
    case Stmt_Module:          return s.span
    case ^Stmt_Dispatch_Def:   return s.span
    case Stmt_Overload:        return s.span
    case ^Stmt_Decl:           return s.span
    case ^Stmt_Define:         return s.span
    }
    return Span{}
}

// ---------------------------------------------------------------------------
// Check expressions — returns the inferred type
// ---------------------------------------------------------------------------

// Return a pointer to the type_ field of any expression node.
expr_type_ptr :: proc(e: Expr) -> ^Type {
    switch v in e {
    case ^Expr_Number:             return &v.type_
    case ^Expr_String:             return &v.type_
    case ^Expr_Char:               return &v.type_
    case ^Expr_Ident:              return &v.type_
    case ^Expr_Bool:               return &v.type_
    case ^Expr_Skip_Constructor:             return &v.type_
    case ^Expr_Unary:              return &v.type_
    case ^Expr_Binary:             return &v.type_
    case ^Expr_Call:               return &v.type_
    case ^Expr_Array:              return &v.type_
    case ^Expr_Index:              return &v.type_
    case ^Expr_Slice:              return &v.type_
    case ^Expr_Struct_Literal:     return &v.type_
    case ^Expr_Field_Access:       return &v.type_
    case ^Expr_Size_Of:            return &v.type_
    case ^Expr_Assert:             return &v.type_
    case ^Expr_Take:                return &v.type_
    case ^Expr_If:                 return &v.type_
    case ^Expr_Compiler_Intrinsic: return &v.type_
    case ^Expr_Include:            return &v.type_
    case ^Expr_Type_Name:          return &v.type_
    case ^Expr_Tuple_Default:      return &v.type_
    case ^Expr_Self:               return &v.type_
    case ^Expr_Try:                return &v.type_
    case nil:                      return nil
    }
    return nil
}

// Extract the resolved type from an already-checked expression node.
expr_type :: proc(e: Expr) -> Type {
    if p := expr_type_ptr(e); p != nil { return p^ }
    return nil
}

// Store the resolved type back onto an expression node.
set_expr_type :: proc(expr: Expr, t: Type) {
    if p := expr_type_ptr(expr); p != nil { p^ = t }
}

check_expr :: proc(c: ^Checker, expr: Expr, env: ^Type_Env) -> Type {
    result := check_expr_impl(c, expr, env)
    set_expr_type(expr, result)
    return result
}

check_expr_impl :: proc(c: ^Checker, expr: Expr, env: ^Type_Env) -> Type {
    switch e in expr {
    case ^Expr_Number:
        if e.is_float {
            return Type_Infer_Float{}
        }
        return Type_Infer_Int{}
    case ^Expr_String:
        // String literals are sentinel-terminated partial arrays of utf8 —
        // shape `[..N, 0]utf8`. The bytes live in rodata (one global per
        // unique literal, deduped at codegen), and the partial-array
        // header is synthesized on the stack at the use site, pointing at
        // the global. Choosing partial-array over fixed-array makes the
        // literal's type match the `cstr` shape directly (and via the
        // header-compatible drop, the `str` shape too), so `&s + "x"`
        // and `c_func("y")` and `s : str = "z"` all flow through one
        // type-checking rule.
        byte_len := len(e.value)
        pa := new(Type_Partial_Array)
        pa.size = byte_len
        pa.elem = Type_Utf8{}
        pa.has_sentinel = true
        pa.sentinel = 0
        return pa
    case ^Expr_Char:
        return Type_C8{}
    case ^Expr_Bool:
        return Type_Bool{}
    case ^Expr_Skip_Constructor:
        // `---` carries no intrinsic type — the type comes from the LHS
        // (a field's declared type or a local's type annotation). The
        // checker treats it as Type_Any so any LHS accepts it; codegen
        // recognizes the marker and skips constructor / default emission.
        return Type_Any{}
    case ^Expr_Ident:
        // Snapshot the hint for this expression and clear it on the checker so
        // child calls within this branch don't accidentally inherit it.
        hint := c.expected_hint
        c.expected_hint = nil

        // .Variant shorthand: resolve via hint first, then fall back to a
        // visible-variant search. Required form when no hint is in play.
        if e.is_dot {
            if t, ok := resolve_variant_ident(c, e, hint, env, dot = true); ok {
                return t
            }
            check_error(c, e.span, TYPE_VISIBLE_ENUM_UNION_VARIANT, e.name)
            return Type_Error{}
        }

        // Bare ident with a union/enum expected type: resolve as a variant.
        // Lets `Init(Video)` work because the param type is Init_Flags.
        if hint != nil {
            if t, ok := resolve_variant_ident(c, e, hint, env, dot = false); ok {
                return t
            }
        }

        // Cross-module bare constant collision: two or more visible modules
        // define the same bare name. Force the user to qualify (Module.name)
        // so it's unambiguous which constant they meant.
        if owner, mapped := c.table.constant_owners[e.name]; mapped && owner == "" {
            owners: [dynamic]string
            defer delete(owners)
            suffix := strings.concatenate({"_", e.name})
            for flat, _ in c.table.constants {
                if strings.has_suffix(flat, suffix) && flat != e.name {
                    pkg := flat[:len(flat) - len(suffix)]
                    // Flat names use underscore as separator; dotted-name
                    // modules like "mara.memory" appear here as
                    // "mara_memory". Convert to the user-facing dotted form
                    // for the diagnostic so they see "mara.memory" rather
                    // than the internal flat encoding.
                    if strings.has_prefix(pkg, "mara_") {
                        pkg = strings.concatenate({"mara.", pkg[len("mara_"):]})
                    }
                    append(&owners, pkg)
                }
            }
            if len(owners) > 1 {
                joined := strings.join(owners[:], ", ")
                check_error(c, e.span,
                    TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED,
                    e.name, joined, owners[0], e.name)
                return Type_Error{}
            }
        }

        // Check for reading an uninitialized pointer/slice
        if is_invalid_ref(env, e.name) {
            check_error(c, e.span, TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE, e.name)
        }
        // Check env (common case: local vars, params, functions)
        t, loc_env, ok := type_env_locate(env, e.name)
        if ok {
            // Field-leak guard: if the name was found in an ancestor env that belongs
            // to a class body, AND the name is a field of that class, the caller is
            // a nested scope (method body) trying to access a field as a bare name.
            // Require receiver access instead.
            if loc_env != env && loc_env.class_scope != nil {
                if is_real_field(&loc_env.class_scope.sd, e.name) {
                    check_error(c, e.span,
                        TYPE_FIELD_ACCESS_THROUGH_RECEIVER,
                        e.name, loc_env.class_scope.name, e.name)
                    return Type_Error{}
                }
            }
            // Set variant resolution metadata if this is an enum variant.
            // Only attach when the env binding actually IS the enum — without
            // this guard, any local `N :: 1000` would silently get overridden
            // by an imported `Scancode.N` variant of the same name. The
            // variant_to_enum table is meant for the `.N` dot-shorthand
            // fallback, not bare names that already resolved to something else.
            if owner_enum, mapped := c.table.variant_to_enum[e.name]; mapped {
                if et, t_ok := t.(^Type_Enum); t_ok && et.name == owner_enum {
                    if val, v_ok := et.variants[e.name]; v_ok {
                        e.resolved = Resolved_Enum_Variant{
                            enum_name = owner_enum,
                            variant   = e.name,
                            value     = val,
                        }
                    }
                }
            }
            // Resolve function references (for function-as-value usage).
            // Use env-aware lookup so we pick the binding visible at this call
            // site, not whichever one happened to register first in the global
            // symbol_home table (e.g. SDL3 vs SDL2 both export GL_GetProcAddress).
            if tf, is_func := t.(^Type_Scope); is_func && len(tf.params) > 0 && e.name in c.declared_funs {
                home := resolve_fn_home(c, env,e.name)
                flat := make_flat_name(home, e.name)
                e.resolved = Resolved_Func{name = flat}
            }
            return t
        }
        // Namespace-match fallback: bare identifier inside a `match struct { … }`
        // arm resolves as a field of the subject when the local env doesn't
        // know it. Lets `dropfile do print(dropfile.name)` work without
        // re-typing `game.events.` everywhere.
        if c.namespace_subject != nil && c.namespace_subject_type != nil {
            for f in c.namespace_subject_type.sd.fields {
                if f.name == e.name {
                    fa := new_clone(Expr_Field_Access{
                        expr  = c.namespace_subject,
                        field = e.name,
                        span  = e.span,
                    })
                    e.desugared = fa
                    e.type_     = f.type_
                    return f.type_
                }
            }
        }
        // Not in env — check for better error messages
        ident_flat := resolve_type_name(c, e.name, "", env)
        if ident_flat in c.table.funs {
            check_error(c, e.span, TYPE_TYPE_VALUE_DID_MEAN, e.name, e.name)
        } else if ident_flat in c.table.enums {
            check_error(c, e.span, TYPE_TYPE_VALUE_DID_MEAN, e.name, e.name)
        } else if ident_flat in c.table.unions {
            check_error(c, e.span, TYPE_TYPE_VALUE_DID_MEAN, e.name, e.name)
        } else {
            check_error(c, e.span, TYPE_UNDEFINED_IDENTIFIER, e.name)
        }
        return Type_Error{}
    case ^Expr_Unary:
        operand_type := check_expr(c, e.operand, env)
        #partial switch e.op {
        case .Minus:
            if !is_numeric(operand_type) {
                // Try `overload -` dispatch with a single-arg function (e.g.
                // mara.math's `vec3_negate`). Falls through to the standard
                // not-numeric error if no overload matches.
                if dispatch_names, has_overload := find_operator_overload(c, env, e.op); has_overload {
                    best_flat := ""
                    best_ret: Type = nil
                    best_score := 0  // 0=none, 2=concrete structural, 3=concrete exact
                    for dispatch_name in dispatch_names {
                        if fn_names, is_dispatch := find_dispatch(c, env, dispatch_name); is_dispatch {
                            for fn_name in fn_names {
                                ft_raw, ft_found := type_env_get(env, fn_name)
                                if !ft_found { continue }
                                ft, ft_ok := ft_raw.(^Type_Scope)
                                if !ft_ok { continue }
                                if len(ft.params) != 1 { continue }
                                if types_incompatible(ft.params[0].type_, operand_type) { continue }
                                score := 2
                                if types_name_equal(ft.params[0].type_, operand_type) { score = 3 }
                                if score > best_score {
                                    best_flat = make_flat_name(resolve_fn_home(c, env, fn_name), fn_name)
                                    best_ret = fn_primary_return(ft)
                                    best_score = score
                                }
                            }
                        }
                    }
                    if best_score > 0 {
                        e.overload_fn = Resolved_Func{name = best_flat}
                        return best_ret
                    }
                }
                check_error(c, e.span, TYPE_CANNOT_NEGATE, type_name(operand_type))
            }
            return operand_type
        case .Not:
            if _, ok := operand_type.(Type_Bool); !ok && !is_any(operand_type) {
                check_error(c, e.span, TYPE_CANNOT_APPLY, type_name(operand_type))
            }
            return Type_Bool{}
        case .Tilde:
            if !is_integer(operand_type) && !is_any(operand_type) {
                check_error(c, e.span, TYPE_CANNOT_APPLY_REQUIRES_INTEGER_TYPE, type_name(operand_type))
            }
            return operand_type
        case .Ampersand:
            // Address-of: &x produces ^T. Reject if the address would land in
            // immutable-param storage — letting `&t` escape would silently
            // grant the mutation that declaring `t` without `^` denied.
            if pname, immut := write_root_immutable_param(e.operand, env); immut {
                check_error(c, e.span,
                    TYPE_CANNOT_TAKE_ADDRESS_IMMUTABLE_PARAMETER,
                    pname)
            }
            pt := new(Type_Ptr)
            pt.elem = operand_type
            return pt
        case .Caret:
            // Dereference: p^ — operand must be a pointer. The Expr_Ident
            // check at the operand site already fires is_invalid_ref, which
            // covers both no-initializer pointers and pointers currently
            // holding `void` (see invalid_refs comment on Type_Env).
            if p, ok := operand_type.(^Type_Ptr); ok {
                return p.elem
            }
            // Allow deref on Type_Any (backwards compat with raw ptr)
            if is_any(operand_type) {
                return Type_Error{}
            }
            check_error(c, e.span, TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE, type_name(operand_type))
            return Type_Error{}
        }
    case ^Expr_Binary:
        return check_binary(c, e, env)
    case ^Expr_Call:
        return check_call(c, e, env)
    case ^Expr_Try:
        return check_try(c, e, env)
    case ^Expr_Array:
        return check_array_literal(c, e, env)
    case ^Expr_Index:
        return check_index(c, e, env)
    case ^Expr_Slice:
        return check_slice(c, e, env)
    case ^Expr_Struct_Literal:
        // Broadcast literal `{all <expr>}`: expand_broadcast_array_literal
        // has already validated and populated array_values, and set e.type_
        // to the surrounding field/decl type. Don't re-check (which would
        // return Type_Error for the anonymous shape) and overwrite the type.
        if e.is_broadcast && e.type_ != nil {
            if _, is_err := e.type_.(Type_Error); !is_err {
                return e.type_
            }
        }
        // Inline typed-array literal: `[3]f32{0.9, 0.2, 0.6}`. The parser
        // attaches the inline type expression; resolve it and reuse the
        // array-literal validation path used by named distinct array types.
        if e.type_expr != nil {
            resolved := resolve_type_expr(e.type_expr, c, e.span, env = env)
            if fa, fa_ok := resolved.(^Type_Fixed_Array); fa_ok {
                check_array_struct_literal(c, e, fa, env)
                e.type_ = resolved
                return resolved
            }
            // Empty partial-array literal: `[..N]T{}` — a default-init
            // constructor that yields a fresh partial array with .len = 0,
            // .cap = N, .ptr aimed at the destination's inline elements.
            // Codegen emits the in-place init; the literal itself doesn't
            // need any element values (any fields would currently be
            // rejected as the codegen doesn't fill elements through this
            // path).
            if _, pa_ok := resolved.(^Type_Partial_Array); pa_ok {
                if len(e.fields) > 0 {
                    check_error(c, e.span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(resolved))
                    return Type_Error{}
                }
                e.type_ = resolved
                return resolved
            }
            check_error(c, e.span, TYPE_TYPED_ARRAY_LITERAL_TYPE_FIXED, type_name(resolved))
            return Type_Error{}
        }
        // Distinct-fixed-array literal: Quat{1,2,3,4} / Quat{w: 1} / Quat{}.
        // Detected by resolving e.name to a Type_Distinct wrapping Type_Fixed_Array
        // (or a plain Type_Fixed_Array via alias). Validates and normalizes the
        // fields into e.array_values for codegen.
        if e.name != "" {
            flat := resolve_type_name(c, e.name, "", env)
            if dt, ok := c.table.distinct_types[flat]; ok {
                if fa, fa_ok := dt.base_type.(^Type_Fixed_Array); fa_ok {
                    check_array_struct_literal(c, e, fa, env)
                    return dt
                }
            }
        }
        // Named struct literal: run the full field-matching check (positional vs
        // named, multi-return spread, types). Without this, `x := Foo{call()}`
        // with no annotation would skip the structural check and is_spread
        // never gets set by the spread-detection branch.
        if e.name != "" {
            flat := resolve_type_name(c, e.name, "", env)
            if st, ok := c.table.structs[flat]; ok {
                check_struct_literal_fields(c, e, &st.sd, e.span, env)
                return st
            }
            if st, ok := c.table.funs[flat]; ok {
                check_struct_literal_fields(c, e, &st.sd, e.span, env)
                return st
            }
        }
        // Anonymous literal with a context-supplied type. Used for things like
        // `quat_from_fwd_and_up({0, 1, 0}, {0, 0, 1})` where the parameter type
        // (Vec3 :: distinct [3]f32) is the only source of shape information.
        // Without this, array_values would never be populated and codegen
        // would emit a bare `0` for the aggregate.
        if hint := c.expected_hint; hint != nil {
            if fa, fa_ok := distinct_base(hint).(^Type_Fixed_Array); fa_ok {
                check_array_struct_literal(c, e, fa, env)
                e.type_ = hint
                return hint
            }
        }
        // Anonymous struct literal: just check each field value.
        for field in e.fields {
            check_expr(c, field.value, env)
        }
        return Type_Error{}
    case ^Expr_Field_Access:
        return check_field_access(c, e, env)
    case ^Expr_Size_Of:
        // size_of(Type) — compile-time constant, infers type from context (like Zig's @sizeOf)
        resolved := resolve_type_expr(e.type_expr, c, e.span, env=env)
        if _, is_err := resolved.(Type_Error); is_err {
            check_error(c, e.span, TYPE_SIZE_UNKNOWN_TYPE)
        }
        e.resolved_type = resolved
        return Type_Infer_Int{}
    case ^Expr_Assert:
        // assert(cond) — cond must be boolean; the expression yields no value.
        cond_type := check_expr(c, e.cond, env)
        if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
            check_error(c, e.span, TYPE_CONDITION_BOOL, type_name(cond_type))
        }
        e.type_ = Type_Void{}
        return Type_Void{}
    case ^Expr_Take:
        // Two forms:
        //   take(T, slice)      — carve from slice's cursor; advances slice.len
        //   take(T, &slice[i])  — positional view at a specific address; no
        //                         cursor mutation. Subsumes the old `let`
        //                         behavior; useful for the "same location
        //                         every call" pattern (game state, etc.).
        // The type arg comes in three shapes:
        //   take([N]T, ...)     — fixed-size array; resolves to [N]T.
        //   take([]T(n), ...)   — runtime-counted slice; n is lifted out into
        //                         count_expr, type_expr is rewritten to a bare
        //                         []T, and the result is a slice with len=cap=n.
        //   take(T, ...)        — any other type; the byte size is sizeof(T).
        // Detect the slice form before resolution: `[]Vertex(n)` parses as
        // Type_Slice_Expr{elem = Type_Generic_Instance{Vertex, [n]}}. When the
        // elem name is not a generic template and there's exactly one type-arg,
        // we treat the arg as a runtime count and rewrite to bare []Vertex.
        if e.count_expr == nil {
            if ts, ts_ok := e.type_expr.(^Type_Slice_Expr); ts_ok {
                if gi, gi_ok := ts.elem.(^Type_Generic_Instance); gi_ok && len(gi.type_args) == 1 {
                    if _, is_generic := c.table.generic_templates[gi.name]; !is_generic {
                        // Arg shapes from parse_generic_arg:
                        //   Type_Const_Value  — number literal: take([]T(4), ...)
                        //   Type_Name         — bare identifier:  take([]T(n), ...)
                        //   Type_Const_Expr   — anything else:    take([]T(n*2), ...), take([]T(f(x)), ...)
                        if cv, cv_ok := gi.type_args[0].(Type_Const_Value); cv_ok {
                            num := new(Expr_Number)
                            num.int_value = i128(cv.value)
                            num.value = f64(cv.value)
                            num.span = cv.span
                            e.count_expr = num
                        } else if tn, tn_ok := gi.type_args[0].(Type_Name); tn_ok {
                            e.count_expr = new_clone(Expr_Ident{name = tn.name, span = tn.span})
                        } else if ce, ce_ok := gi.type_args[0].(Type_Const_Expr); ce_ok {
                            e.count_expr = ce.expr
                        }
                        if e.count_expr != nil {
                            ts.elem = Type_Name{name = gi.name, span = gi.span}
                        }
                    }
                }
            }
        }
        // 1-arg `slice(source)` — no type_expr. Pull the slice's element type
        // from the expected_hint set by check_field_assign (the LHS field
        // being assigned to). Without the hint there's nowhere to derive T,
        // so we error.
        resolved: Type
        if e.type_expr == nil {
            if hint := c.expected_hint; hint != nil {
                if _, is_slice := distinct_base(hint).(^Type_Slice); is_slice {
                    resolved = hint
                } else {
                    check_error(c, e.span, TYPE_TAKE_UNKNOWN_TYPE)
                    resolved = Type_Error{}
                }
            } else {
                check_error(c, e.span, TYPE_TAKE_UNKNOWN_TYPE)
                resolved = Type_Error{}
            }
        } else {
            resolved = resolve_type_expr(e.type_expr, c, e.span, env=env)
            if _, is_err := resolved.(Type_Error); is_err {
                check_error(c, e.span, TYPE_TAKE_UNKNOWN_TYPE)
            }
        }
        // Runtime-counted form: validate count is integer at slice header
        // width, resolved is a slice. Codegen does NOT emit an implicit
        // narrow/widen on the count.
        if e.count_expr != nil {
            count_type := check_expr(c, e.count_expr, env)
            if !is_any(count_type) && !is_numeric(count_type) {
                check_error(c, e.span,
                    TYPE_TAKE_COUNT_INTEGER, type_name(count_type))
            } else if !coerces_to_slice_width(count_type) {
                check_error(c, e.span, TYPE_INDEX_WIDTH,
                    type_name(slice_header_width_type), type_name(count_type))
            }
            if _, is_slice := distinct_base(resolved).(^Type_Slice); !is_slice {
                check_error(c, e.span,
                    TYPE_TAKE_COUNT_REQUIRES_SLICE_TYPE, type_name(resolved))
            }
        }
        e.resolved_type = resolved
        src_type := check_expr(c, e.storage, env)
        src_base := distinct_base(src_type)
        // Cursor form needs ^[]byte (or ^distinct-byte-slice). Passing []byte
        // directly would let array→slice coercion create a fresh header per
        // call site, each with cursor=0, silently clobbering prior takes —
        // and mutating a bare []byte param would violate the immutable-param
        // rule anyway. ^byte is the positional form (no cursor mutation).
        is_slice_ptr_arg := false
        is_byte_ptr_arg  := false
        if pt, ok := src_base.(^Type_Ptr); ok {
            elem_base := distinct_base(pt.elem)
            if sl, sl_ok := elem_base.(^Type_Slice); sl_ok {
                if _, is_byte := sl.elem.(Type_Byte); is_byte { is_slice_ptr_arg = true }
            } else if _, is_byte := elem_base.(Type_Byte); is_byte {
                is_byte_ptr_arg = true
            }
        }
        if !is_slice_ptr_arg && !is_byte_ptr_arg && !is_any(src_type) {
            check_error(c, e.span,
                TYPE_TAKE_REQUIRES_BYTE_CURSOR_FORM,
                type_name(src_type))
        }
        // Lifetime: storage must not point into our own frame (or deeper) —
        // a slice carved from it would dangle after this function returns.
        src_prov := expr_provenance(c, e.storage, env)
        if src_prov.depth >= env.scope_depth {
            check_error(c, e.span,
                TYPE_TAKE_STORAGE_POINTS_INTO_LOCAL)
        }
        e.type_ = resolved
        return resolved
    case ^Expr_If:
        cond_type := check_expr(c, e.condition, env)
        if !is_any(cond_type) {
            if _, is_bool := cond_type.(Type_Bool); !is_bool {
                check_error(c, e.span, TYPE_EXPRESSION_CONDITION_BOOL, type_name(cond_type))
            }
        }
        then_type := check_expr(c, e.then_expr, env)
        else_type := check_expr(c, e.else_expr, env)
        // Unify: if either is untyped/infer, adopt the other
        if is_untyped(then_type) || is_infer(then_type) { return else_type }
        if is_untyped(else_type) || is_infer(else_type) { return then_type }
        if types_incompatible(then_type, else_type) {
            check_error(c, e.span, TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS,
                type_name(then_type), type_name(else_type))
        }
        return then_type
    case ^Expr_Compiler_Intrinsic:
        switch e.kind {
        case .Caller_Name:
            e.resolved_value = strings.clone(enclosing_fn_name(env))
        case .Caller_Span:
            e.resolved_value = strings.clone(format_location(e.span.file, e.span.line, e.span.col))
        case .Web:
            e.bool_value = c.target_web
            e.type_ = Type_Bool{}
            return Type_Bool{}
        case .Native:
            e.bool_value = !c.target_web
            e.type_ = Type_Bool{}
            return Type_Bool{}
        case .Windows:
            e.bool_value = c.target_os == .Windows
            e.type_ = Type_Bool{}
            return Type_Bool{}
        case .Linux:
            e.bool_value = c.target_os == .Linux
            e.type_ = Type_Bool{}
            return Type_Bool{}
        case .Mac:
            e.bool_value = c.target_os == .Mac
            e.type_ = Type_Bool{}
            return Type_Bool{}
        }
        // Caller_* intrinsics resolve to string literals but codegen emits a
        // pointer (GEP). Return ^byte so they can be passed to functions
        // expecting ^byte.
        return new_clone(Type_Ptr{elem = Type_Byte{}})
    case ^Expr_Include:
        // Scope-based include resolution. The path is the dotted module name;
        // check_module accepts dotted names directly (mara.X submodules and
        // user modules use the same resolution path).
        if existing, found := type_env_get(env, e.path); found {
            if existing_sd := as_scope_body(existing); existing_sd != nil && existing_sd.scope != nil {
                return existing
            }
        }
        mod := check_module(c, e.path, e.span)
        if mod == nil { return Type_Error{} }
        return mod
    case ^Expr_Type_Name:
        // Bare primitive type-keyword used as a value (e.g. `Array(byte, 64)`
        // where `byte` is the generic-arg). Resolves to the corresponding
        // builtin Type so generic-template binding and other consumers can
        // treat it the same as a user-defined type-name flowed through an
        // Expr_Ident.
        #partial switch e.kind {
        case .Bool_Type: return Type_Bool{}
        case .I8:        return Type_Numeric{kind = .Signed,   bits = 8}
        case .I16:       return Type_Numeric{kind = .Signed,   bits = 16}
        case .I32:       return Type_Numeric{kind = .Signed,   bits = 32}
        case .I64:       return Type_Numeric{kind = .Signed,   bits = 64}
        case .U8:        return Type_Numeric{kind = .Unsigned, bits = 8}
        case .U16:       return Type_Numeric{kind = .Unsigned, bits = 16}
        case .U32:       return Type_Numeric{kind = .Unsigned, bits = 32}
        case .U64:       return Type_Numeric{kind = .Unsigned, bits = 64}
        case .F32:       return Type_Numeric{kind = .Float,    bits = 32}
        case .F64:       return Type_F64{}
        case .C8:        return Type_C8{}
        case .Utf8:      return Type_Utf8{}
        case .Byte:      return Type_Byte{}
        case .Int:
            check_error(c, e.span, TYPE_TYPE_INT_RESERVED_USE_I64)
            return Type_Error{}
        }
        return Type_Error{}
    case ^Expr_Tuple_Default:
        // Type-check the source once (idempotent — the same source pointer is
        // shared by every binding in the destructure group). If the source is
        // a multi-return call, this binding's type is the i-th return slot.
        // Otherwise the user wrote a single non-multi value with N names —
        // that's the broadcast case (`a, b: i64 = 7`), so each binding takes
        // the source's type directly and codegen re-evaluates per binding.
        src_type := check_expr(c, e.source, env)
        if _, is_err := src_type.(Type_Error); is_err { return Type_Error{} }
        returns := call_return_list(c, e.source, env)
        if len(returns) > 1 {
            if e.index < 0 || e.index >= len(returns) {
                check_error(c, e.span,
                    TYPE_TUPLE_DESTRUCTURE_INDEX_OUT_RANGE,
                    e.index, len(returns))
                return Type_Error{}
            }
            return returns[e.index]
        }
        return src_type
    case ^Expr_Self:
        // `#self` — pointer the constructor is writing into. Walk the env
        // chain for the nearest class_scope (set on a struct/class body's
        // ns_env). Nested funs are reparented past the class ns_env at
        // check_scope_body, so the lookup fails inside them — explicit
        // ^Self params are still required for helpers.
        cur := env
        for cur != nil {
            if cur.class_scope != nil {
                t := new_clone(Type_Ptr{elem = cur.class_scope})
                e.type_ = t
                return t
            }
            cur = cur.parent
        }
        check_error(c, e.span, TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT)
        return Type_Error{}
    }
    return Type_Error{}
}

// Shared struct field access logic — used for both direct and auto-deref (^Struct) paths.
// Handles uninit checks, field resolution, and associated function lookup.
check_struct_field_access :: proc(c: ^Checker, e: ^Expr_Field_Access, st: ^Scope_Body, env: ^Type_Env) -> Type {
    // Check for reading an uninitialized pointer/slice field.
    // If the receiver is a pointer alias (e.g. `it = &root`), look through the
    // alias too — `it.next` should fire the same error as `root.next`.
    if ident, ident_ok := e.expr.(^Expr_Ident); ident_ok {
        field_key := strings.concatenate({ident.name, ".", e.field})
        if is_invalid_ref(env, field_key) {
            check_error(c, e.span, TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, e.field, ident.name)
        } else if target, has_alias := lookup_alias(env, ident.name); has_alias {
            aliased_key := strings.concatenate({target, ".", e.field})
            if is_invalid_ref(env, aliased_key) {
                check_error(c, e.span,
                    TYPE_FIELD_ALIASED_VIA_USED_BEFORE,
                    e.field, target, ident.name)
            }
        }
    }
    ft := resolve_struct_field(st, e.field, c.table)
    if ft != nil { return ft }
    // Associated function access (function as value)
    if st.functions != nil {
        if fn, found := st.functions[e.field]; found && fn != nil {
            e.resolved = Resolved_Func{name = fn.name}
            return fn
        }
    }
    check_error(c, e.span, TYPE_CLASS_FIELD, st.name, e.field)
    return Type_Error{}
}

check_field_access :: proc(c: ^Checker, e: ^Expr_Field_Access, env: ^Type_Env) -> Type {
    // Self-module qualification: `<current_package>.X` resolves X via the
    // current module's flat-name table or env directly. The main package
    // doesn't get a synthesized mod_struct (unlike imported modules), so its
    // own name isn't in env — we intercept the qualifier here. Imported
    // modules already have mod_struct registered, so they fall through to
    // the normal field-access flow.
    if ident, ok := e.expr.(^Expr_Ident); ok && ident.name == c.current_package && c.current_package != "" {
        flat := make_flat_name(c.current_package, e.field)
        if const_expr, ce_ok := c.table.constants[flat]; ce_ok {
            // Mirror the inference behavior used at module-qualified access
            // sites: integer constants get a Resolved_Constant annotation;
            // string and other constants stay as referenced expressions and
            // get their type from the constant's value at codegen time.
            if _, i_val, is_const := extract_constant_value(const_expr); is_const {
                e.resolved = Resolved_Constant{
                    name      = e.field,
                    int_value = int(i_val),
                }
            }
            // Best-effort type: re-check the constant value's expression.
            return check_expr(c, const_expr, env)
        }
    }
    obj_type := check_expr(c, e.expr, env)
    // Qualified enum access: EnumName.Variant
    if et, ok := obj_type.(^Type_Enum); ok {
        if val, v_ok := et.variants[e.field]; v_ok {
            resolved := Resolved_Enum_Variant{
                enum_name = et.name,
                variant   = e.field,
                value     = val,
            }
            e.resolved = resolved
            return et
        }
        check_error(c, e.span, TYPE_ENUM_VARIANT, et.name, e.field)
        return Type_Error{}
    }
    // Qualified union variant access: UnionName.Variant
    if ut, ok := obj_type.(^Type_Union); ok {
        // Special accessor: union_value.tag — reads the discriminant as the
        // corresponding `<Union>_Tag` enum value. Reserves "tag" as a name
        // (no payloaded union variant may be named "tag"; Mara variants are
        // capitalized by convention, so the collision risk is minimal).
        if e.field == "tag" {
            tag_enum_name := strings.concatenate({ut.name, "_Tag"})
            if tag_et, found := c.table.enums[tag_enum_name]; found {
                e.resolved = Resolved_Union_Tag{union_name = ut.name}
                return tag_et
            }
            check_error(c, e.span, TYPE_UNION_TAG_ENUM_INTERNAL_ERROR, ut.name)
            return Type_Error{}
        }
        if e.field == "pad" {
            if ut.tag_pad == nil {
                check_error(c, e.span, TYPE_UNION_PADDING_DECLARE_UNION_PAD, ut.name)
                return Type_Error{}
            }
            e.resolved = Resolved_Union_Pad{union_name = ut.name}
            return ut.tag_pad
        }
        if tag_val, v_ok := ut.tag_map[e.field]; v_ok {
            struct_name := ut.variant_structs[e.field] or_else e.field
            resolved := Resolved_Union_Variant{
                union_name  = ut.name,
                variant     = e.field,
                tag_value   = tag_val,
                struct_name = struct_name,
            }
            e.resolved = resolved
            return ut
        }
        check_error(c, e.span, TYPE_UNION_VARIANT, ut.name, e.field)
        return Type_Error{}
    }
    if sd := as_scope_body(obj_type); sd != nil && (len(sd.fields) > 0 || sd.scope != nil) {
        // Module-struct field access: look up in scope (env)
        if sd.scope != nil {
            t, found := type_env_get(sd.scope, e.field)
            if !found {
                // Fallback: variants are no longer registered as bare names in
                // a module's scope, so `mara_open_gl.ARRAY_BUFFER` won't find
                // ARRAY_BUFFER directly. Walk the module's types for an enum
                // or union containing this variant name.
                for _, mt in sd.scope.types {
                    if et, et_ok := mt.(^Type_Enum); et_ok {
                        if val, v_ok := et.variants[e.field]; v_ok {
                            e.resolved = Resolved_Enum_Variant{
                                enum_name = et.name,
                                variant   = e.field,
                                value     = val,
                            }
                            return et
                        }
                    } else if ut, ut_ok := mt.(^Type_Union); ut_ok {
                        if tag_val, v_ok := ut.tag_map[e.field]; v_ok {
                            struct_name := ut.variant_structs[e.field] or_else e.field
                            e.resolved = Resolved_Union_Variant{
                                union_name  = ut.name,
                                variant     = e.field,
                                tag_value   = tag_val,
                                struct_name = struct_name,
                            }
                            return ut
                        }
                    }
                }
                check_error(c, e.span, TYPE_MODULE_SYMBOL, sd.name, e.field)
                return Type_Error{}
            }
            // Resolve enum types from this module
            if et, et_ok := t.(^Type_Enum); et_ok {
                if val, v_ok := et.variants[e.field]; v_ok {
                    e.resolved = Resolved_Enum_Variant{
                        enum_name = et.name,
                        variant   = e.field,
                        value     = val,
                    }
                    return t
                }
            }
            // Resolve constants for codegen
            flat := make_flat_name(sd.name, e.field)
            if const_expr, ce_ok := c.table.constants[flat]; ce_ok {
                _, i_val, is_const := extract_constant_value(const_expr)
                if is_const {
                    e.resolved = Resolved_Constant{
                        name      = e.field,
                        int_value = int(i_val),
                    }
                }
            }
            return t
        }
        return check_struct_field_access(c, e, sd, env)
    }
    // Auto-deref: if obj is ^T (including ^DistinctOf<T>), look up field on
    // the pointee. Mirrors the value-side distinct unwrap below so `^String`
    // (where String is `distinct [, 0]utf8`) finds .ptr / .len / .cap on the
    // underlying slice the same way bare `String` does.
    if pt, ok := obj_type.(^Type_Ptr); ok {
        inner := pt.elem
        if dt, dt_ok := inner.(^Type_Distinct); dt_ok {
            inner = dt.base_type
        }
        if sd := as_scope_body(inner); sd != nil && len(sd.fields) > 0 {
            return check_struct_field_access(c, e, sd, env)
        }
        // Continue field-access logic against the pointee so the same
        // slice / fixed-array branches below handle it.
        obj_type = inner
    }
    // Unwrap distinct types for field access (swizzle, struct fields, etc.)
    if dt, dt_ok := obj_type.(^Type_Distinct); dt_ok {
        obj_type = distinct_base(dt)
    }
    // Array swizzle: arr.x, arr.xy, arr.rgba, etc.
    if fa, fa_ok := obj_type.(^Type_Fixed_Array); fa_ok {
        // Fixed arrays have no distinct len (cap == len always). Accept both names.
        if e.field == "len" || e.field == "cap" {
            e.resolved = Resolved_Constant{name = e.field, int_value = fa.size}
            return Type_Numeric{kind = .Signed, bits = 64}
        }
        if is_swizzle_field(e.field, fa.size) {
            if len(e.field) == 1 {
                return fa.elem  // single component -> scalar
            } else {
                result := new(Type_Fixed_Array)
                result.size = len(e.field)
                result.elem = fa.elem
                return result
            }
        }
        // Helpful error: all chars are swizzle chars but index out of range
        if is_all_swizzle_chars(e.field) {
            check_error(c, e.span, TYPE_SWIZZLE_COMPONENT_OUT_RANGE_ARRAY, e.field, fa.size)
            return Type_Error{}
        }
        check_error(c, e.span, TYPE_CANNOT_ACCESS_FIELD_ARRAY_TYPE, e.field, type_name(obj_type))
        return Type_Error{}
    }
    // Slice .len / .cap match the header's storage width (slice_header_width_type).
    // Typed codegen operates at this width throughout; a narrower value widens
    // losslessly into it (value_preserving_widen), so `n := s.len` infers i64.
    if sl, ok := obj_type.(^Type_Slice); ok {
        if e.field == "ptr" {
            pt := new(Type_Ptr)
            pt.elem = sl.elem
            return pt
        }
        if e.field == "len" || e.field == "cap" {
            return slice_header_width_type
        }
        check_error(c, e.span, TYPE_SLICE_TYPE_FIELD, type_name(obj_type), e.field)
        return Type_Error{}
    }
    if pa, ok := obj_type.(^Type_Partial_Array); ok {
        if e.field == "ptr" {
            pt := new(Type_Ptr)
            pt.elem = pa.elem
            return pt
        }
        if e.field == "len" || e.field == "cap" {
            // Constant-string `.len` / `.cap` folds to the literal's byte
            // count: `TAG :: "hello"` then `TAG.len` is the compile-time
            // value 5, not a runtime header read. Codegen consumes the
            // Resolved_Constant annotation directly.
            if ident, id_ok := e.expr.(^Expr_Ident); id_ok {
                if const_expr, ck := c.table.constants[ident.name]; ck {
                    if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                        e.resolved = Resolved_Constant{name = e.field, int_value = len(lit.value)}
                    }
                }
            }
            return slice_header_width_type
        }
        check_error(c, e.span, TYPE_PARTIAL_ARRAY_TYPE_FIELD, type_name(obj_type), e.field)
        return Type_Error{}
    }
    if !is_any(obj_type) {
        check_error(c, e.span, TYPE_CANNOT_ACCESS_FIELD_TYPE, e.field, type_name(obj_type))
    }
    return Type_Error{}
}

// Check a call against all built-in functions. Returns (result_type, true) if the
// name matched a builtin, or (_, false) if it should be resolved as a user function.
check_builtin_call :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Env) -> (Type, bool) {
    check_args_n :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Env, n: int) {
        if len(args) != n {
            check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_2,
                e.name, n, n == 1 ? "" : "s", len(args))
        } else {
            for arg in args {
                check_expr(c, arg, env)
            }
        }
    }

    opaque_ptr :: proc() -> Type {
        pt := new(Type_Ptr)
        pt.elem = Type_Any{}
        return pt
    }

    switch e.name {
    case "len":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_LEN_EXPECTS_ARGUMENT, len(args))
        } else {
            arg_type := check_expr(c, args[0], env)
            if !is_array_type(arg_type) && !is_any(arg_type) {
                check_error(c, e.span, TYPE_LEN_REQUIRES_ARRAY_SLICE, type_name(arg_type))
            }
        }
        // Match the slice header's len width so codegen and the type
        // checker agree on the SSA width.
        return slice_header_width_type, true
    case "cap":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_CAP_EXPECTS_ARGUMENT, len(args))
        } else {
            arg_type := check_expr(c, args[0], env)
            if !is_array_type(arg_type) && !is_any(arg_type) {
                check_error(c, e.span, TYPE_CAP_REQUIRES_ARRAY_SLICE, type_name(arg_type))
            }
        }
        return slice_header_width_type, true
    case "print":
        for arg in args { check_expr(c, arg, env) }
        // Format-string mode: when the first arg resolves to a string literal
        // (either inline, or an identifier bound to a `name :: "..."`
        // constant) containing unescaped `%`, validate placeholder count
        // matches the value-arg count.
        if len(args) > 0 {
            fmt_value := ""
            ok := false
            if lit, lit_ok := args[0].(^Expr_String); lit_ok {
                fmt_value = lit.value
                ok = true
            } else if ident, id_ok := args[0].(^Expr_Ident); id_ok {
                // Skip if the bare name is ambiguous — the Expr_Ident path
                // already reported it, and looking up c.table.constants
                // would silently pick a stale module's value.
                ambiguous := false
                if owner, mapped := c.table.constant_owners[ident.name]; mapped && owner == "" {
                    ambiguous = true
                }
                if !ambiguous {
                    if const_expr, found := c.table.constants[ident.name]; found {
                        if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                            fmt_value = lit.value
                            ok = true
                        }
                    }
                }
            } else if fa, fa_ok := args[0].(^Expr_Field_Access); fa_ok {
                if qual, q_ok := fa.expr.(^Expr_Ident); q_ok {
                    flat := make_flat_name(qual.name, fa.field)
                    if const_expr, found := c.table.constants[flat]; found {
                        if lit, lit_ok := const_expr.(^Expr_String); lit_ok {
                            fmt_value = lit.value
                            ok = true
                        }
                    }
                }
            }
            if ok {
                pct_count := 0
                i := 0
                for i < len(fmt_value) {
                    if fmt_value[i] == '%' {
                        if i+1 < len(fmt_value) && fmt_value[i+1] == '%' {
                            i += 2
                            continue
                        }
                        pct_count += 1
                    }
                    i += 1
                }
                if pct_count > 0 && pct_count != len(args) - 1 {
                    check_error(c, e.span,
                        TYPE_PRINT_FORMAT_STRING_PLACEHOLDER_VALUE,
                        pct_count, len(args) - 1)
                }
            }
        }
        return Type_Error{}, true
    case "crash":
        if len(args) > 1 {
            check_error(c, e.span, TYPE_CRASH_EXPECTS_ARGUMENTS, len(args))
        } else if len(args) == 1 {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_cstr":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_CSTR_EXPECTS_ARGUMENT_BYTE, len(args))
        } else {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_int":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_INT_EXPECTS_ARGUMENT_INT, len(args))
        } else {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_float":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_FLOAT_EXPECTS_ARGUMENT_FLOAT, len(args))
        } else {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "slice_from_ptr":
        // Outside os.mara, the size argument must be comptime-known. The os
        // module needs runtime sizes for sys_alloc's variable-sized chunks;
        // everywhere else, accepting a runtime length opens the classic
        // OOB-read/write attack vector when that length traces back to
        // untrusted input. Constraining to comptime constants closes the
        // entire size-control attack class outside one well-audited file.
        if len(args) != 2 {
            check_error(c, e.span, TYPE_SLICE_PTR_EXPECTS_ARGUMENTS_PTR, len(args))
        } else {
            ptr_type := check_expr(c, args[0], env)
            _, ptr_ok := ptr_type.(^Type_Ptr)
            if !ptr_ok && !is_any(ptr_type) {
                check_error(c, e.span, TYPE_SLICE_PTR_FIRST_ARGUMENT_POINTER, type_name(ptr_type))
            }
            size_type := check_expr(c, args[1], env)
            if !is_numeric(size_type) && !is_any(size_type) {
                check_error(c, e.span, TYPE_SLICE_PTR_SECOND_ARGUMENT_NUMERIC, type_name(size_type))
            } else if !coerces_to_slice_width(size_type) {
                // Codegen does NOT emit an implicit narrow/widen — user must
                // cast at the boundary.
                check_error(c, e.span,
                    TYPE_SLICE_PTR_SECOND_ARGUMENT_WIDTH,
                    type_name(slice_header_width_type),
                    type_name(size_type))
            }
            if !is_package(c, "os") {
                if _, comptime_ok := evaluate_comptime_int(c, args[1]); !comptime_ok {
                    check_error(c, e.span,
                        TYPE_SLICE_PTR_OUTSIDE_OS_MODULE +
                        "(literal, '::' constant, or comptime arithmetic). Runtime-derived lengths " +
                        "are restricted because they're the classic source of OOB-access bugs at C boundaries.")
                }
            }
        }
        byte_slice := new(Type_Slice)
        byte_slice.elem = Type_Byte{}
        return byte_slice, true
    }

    // Type casts: i32(x), f64(x), etc.
    is_type_cast :: proc(name: string) -> bool {
        switch name {
        case "int", "uint",
             "i8", "i16", "i32", "i64", "i128",
             "u8", "u16", "u32", "u64", "u128",
             "usize", "isize",
             "f16", "f32", "f64", "c8", "utf8", "bool":
            return true   // int / uint kept here so the cast site emits the
                          // same "reserved" error as a type position would,
                          // instead of a generic "unknown function".
        }
        return false
    }
    if is_type_cast(e.name) {
        if len(args) != 1 {
            check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_3, e.name, len(args))
            return Type_Error{}, true
        }
        check_expr(c, args[0], env)
        switch e.name {
        case "int":
            check_error(c, e.span, TYPE_TYPE_INT_RESERVED_USE_I64)
            return Type_Error{}, true
        case "i64": return Type_Numeric{kind = .Signed, bits = 64}, true
        case "uint":
            check_error(c, e.span, TYPE_TYPE_UINT_RESERVED_USE_U64)
            return Type_Error{}, true
        case "i8":  return Type_Numeric{kind = .Signed, bits = 8}, true
        case "i16": return Type_Numeric{kind = .Signed, bits = 16}, true
        case "i32": return Type_Numeric{kind = .Signed, bits = 32}, true
        case "i128": return Type_Numeric{kind = .Signed, bits = 128}, true
        case "u8":  return Type_Numeric{kind = .Unsigned, bits = 8}, true
        case "u16": return Type_Numeric{kind = .Unsigned, bits = 16}, true
        case "u32": return Type_Numeric{kind = .Unsigned, bits = 32}, true
        case "u64": return Type_Numeric{kind = .Unsigned, bits = 64}, true
        case "u128": return Type_Numeric{kind = .Unsigned, bits = 128}, true
        case "usize": return Type_Numeric{kind = .Unsigned, bits = 0}, true
        case "isize": return Type_Numeric{kind = .Signed,   bits = 0}, true
        case "f16": return Type_Numeric{kind = .Float, bits = 16}, true
        case "f32": return Type_Numeric{kind = .Float, bits = 32}, true
        case "f64": return Type_F64{}, true
        case "c8":  return Type_C8{}, true
        case "utf8": return Type_Utf8{}, true
        case "bool": return Type_Bool{}, true
        }
    }

    return Type_Error{}, false
}

check_binary :: proc(c: ^Checker, e: ^Expr_Binary, env: ^Type_Env) -> Type {
    // Propagate the hint to both sides so `OpenGL | Resizable` resolves both
    // operands against the surrounding `WindowFlags` expectation.
    hint := c.expected_hint
    c.expected_hint = hint
    left_type := check_expr(c, e.left, env)
    c.expected_hint = hint
    right_type := check_expr(c, e.right, env)

    // Operator overload check: try before built-in arithmetic when at least one
    // operand is non-numeric (so int*int always uses the fast built-in path).
    if !is_numeric(left_type) || !is_numeric(right_type) {
        if dispatch_names, has_overload := find_operator_overload(c, env, e.op); has_overload {
            // Collect all matching candidates, then pick the best (most specific) one.
            // Priority: concrete exact > concrete structural > generic
            best_flat := ""
            best_ret: Type = nil
            best_score := 0  // 0=none, 1=generic, 2=concrete structural, 3=concrete exact

            for dispatch_name in dispatch_names {
                if fn_names, is_dispatch := find_dispatch(c, env, dispatch_name); is_dispatch {
                    for fn_name in fn_names {
                        // Try concrete function first
                        ft_raw, ft_found := type_env_get(env, fn_name)
                        if ft_found {
                            ft, ft_ok := ft_raw.(^Type_Scope)
                            if !ft_ok { continue }
                            if len(ft.params) != 2 { continue }
                            if !types_incompatible(ft.params[0].type_, left_type) &&
                               !types_incompatible(ft.params[1].type_, right_type) {
                                // Score: exact name match (3) vs structural match (2)
                                score := 2
                                p0_exact := types_name_equal(ft.params[0].type_, left_type)
                                p1_exact := types_name_equal(ft.params[1].type_, right_type)
                                if p0_exact && p1_exact { score = 3 }
                                if score > best_score {
                                    // Check if auto-monomorphization is needed
                                    actual_types := [2]Type{left_type, right_type}
                                    mono_flat := auto_monomorphize_for_struct(c, fn_name, ft, actual_types[:], env)
                                    if mono_flat != "" {
                                        best_flat = mono_flat
                                    } else {
                                        best_flat = make_flat_name(resolve_fn_home(c, env,fn_name), fn_name)
                                    }
                                    best_ret = fn_primary_return(ft)
                                    best_score = score
                                }
                            }
                            continue
                        }
                        // Try generic function template
                        if gtmpl, gtmpl_ok := &c.table.generic_templates[fn_name]; gtmpl_ok {
                            if len(gtmpl.ast.typed_params) != 2 { continue }
                            subst: map[string]Type
                            for param in gtmpl.generic_params {
                                subst[param.name] = nil
                            }
                            infer_type_params(&subst, gtmpl.ast.typed_params[0].type_expr, left_type, c)
                            infer_type_params(&subst, gtmpl.ast.typed_params[1].type_expr, right_type, c)
                            // Check all declared type params resolved
                            all_resolved := true
                            for param in gtmpl.generic_params {
                                if subst[param.name] == nil { all_resolved = false; break }
                            }
                            if !all_resolved { continue }
                            // Pre-check: resolve param types with subst and verify compatibility
                            // before instantiating (avoids crashes from nonsensical type params)
                            pre_param0 := resolve_type_expr_with_subst(gtmpl.ast.typed_params[0].type_expr, c, e.span, &subst)
                            pre_param1 := resolve_type_expr_with_subst(gtmpl.ast.typed_params[1].type_expr, c, e.span, &subst)
                            if types_incompatible(pre_param0, left_type) || types_incompatible(pre_param1, right_type) {
                                continue
                            }
                            // Build mangled name including auto-captured const params
                            type_args: [dynamic]Type
                            for param in gtmpl.generic_params {
                                append(&type_args, subst[param.name])
                            }
                            // Add auto-captured params sorted by name
                            dispatch_extra: [dynamic]string
                            for sname, st in subst {
                                already := false
                                for param in gtmpl.generic_params {
                                    if param.name == sname { already = true; break }
                                }
                                if !already && st != nil {
                                    append(&dispatch_extra, sname)
                                }
                            }
                            for i := 1; i < len(dispatch_extra); i += 1 {
                                for j := i; j > 0 && dispatch_extra[j] < dispatch_extra[j-1]; j -= 1 {
                                    dispatch_extra[j], dispatch_extra[j-1] = dispatch_extra[j-1], dispatch_extra[j]
                                }
                            }
                            for sname in dispatch_extra {
                                append(&type_args, subst[sname])
                            }
                            mangled := mangle_generic_name(gtmpl.name, type_args[:])
                            if mangled not_in c.table.mono_fun_cache {
                                instantiate_generic_fun(c, gtmpl, &subst, mangled, env)
                                c.table.mono_fun_cache[mangled] = gtmpl.name
                            }
                            fun_type_raw, ok := type_env_get(env, mangled)
                            if !ok {
                                // Fallback: check top_env (monomorphized fn may be registered there
                                // when instantiated from inside a module's scope)
                                if c.top_env != nil {
                                    fun_type_raw, ok = type_env_get(c.top_env, mangled)
                                }
                            }
                            if !ok { continue }
                            fun_type, fun_ok := fun_type_raw.(^Type_Scope)
                            if !fun_ok || len(fun_type.params) != 2 { continue }
                            if !types_incompatible(fun_type.params[0].type_, left_type) &&
                               !types_incompatible(fun_type.params[1].type_, right_type) {
                                if best_score < 1 {
                                    best_flat = make_flat_name(gtmpl.home_package, mangled)
                                    best_ret = fn_primary_return(fun_type)
                                    best_score = 1
                                }
                            }
                        }
                    }
                }
            }
            // Use best match if found
            if best_score > 0 {
                e.overload_fn = Resolved_Func{name = best_flat}
                return best_ret
            }
        }
    }

    #partial switch e.op {
    case .And, .Or:
        op_word := "and" if e.op == .And else "or"
        if _, ok := left_type.(Type_Bool); !ok && !is_any(left_type) {
            check_error(c, e.span, TYPE_LEFT_OPERAND_BOOL,
                op_word, type_name(left_type))
            // Educational hint for the classic novice trap:
            //   `if x and y == 0`  parses as  `x and (y == 0)`
            // The user usually meant "compare both x and y against 0". When
            // the left is numeric and the right is a comparison, show them
            // the corrected form. Build the suggestion manually so the
            // comparisons don't get wrapped in parens (dump_parse_expr's
            // default for AST dumps).
            if right_bin, rb_ok := e.right.(^Expr_Binary); rb_ok {
                if is_comparison_op(right_bin.op) && is_numeric(left_type) {
                    b: strings.Builder
                    strings.builder_init(&b)
                    dump_parse_expr(&b, e.left)
                    fmt.sbprintf(&b, " %s ", op_str(right_bin.op))
                    dump_parse_expr(&b, right_bin.right)
                    fmt.sbprintf(&b, " %s ", op_word)
                    dump_parse_expr(&b, right_bin.left)
                    fmt.sbprintf(&b, " %s ", op_str(right_bin.op))
                    dump_parse_expr(&b, right_bin.right)
                    check_warning(c, e.span,
                        TYPE_DID_MEAN_EACH_OPERAND_NEEDS,
                        strings.to_string(b), op_word)
                }
            }
        }
        if _, ok := right_type.(Type_Bool); !ok && !is_any(right_type) {
            check_error(c, e.span, TYPE_RIGHT_OPERAND_BOOL,
                op_word, type_name(right_type))
        }
        return Type_Bool{}

    case .Equal_Equal, .Not_Equal:
        // Reject comparisons involving composite types (structs, unions, arrays, tuples)
        if !is_any(left_type) && !is_any(right_type) {
            left_composite := is_composite(left_type)
            right_composite := is_composite(right_type)
            if left_composite || right_composite {
                check_error(c, e.span, TYPE_CANNOT_COMPARE_USING,
                    type_name(left_type), type_name(right_type),
                    e.op == .Equal_Equal ? "==" : "!=")
            }
            // Require matching numeric types (no implicit widening in comparisons)
            if is_numeric(left_type) && is_numeric(right_type) {
                promote_numeric(c, left_type, right_type, e.span)
            }
        }
        return Type_Bool{}

    case .Less, .Less_Equal, .Greater, .Greater_Equal:
        if !is_numeric(left_type) {
            check_error(c, e.span, TYPE_LEFT_OPERAND_COMPARISON_NUMERIC, type_name(left_type))
        }
        if !is_numeric(right_type) {
            check_error(c, e.span, TYPE_RIGHT_OPERAND_COMPARISON_NUMERIC, type_name(right_type))
        }
        // Require matching types (infer literals adopt the concrete side)
        if is_numeric(left_type) && is_numeric(right_type) {
            promote_numeric(c, left_type, right_type, e.span)
        }
        return Type_Bool{}

    case .Plus:
        // Numeric addition
        if !is_numeric(left_type) || !is_numeric(right_type) {
            check_error(c, e.span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT,
                type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
        return coerce_infer_to_hint(promote_numeric(c, left_type, right_type, e.span), hint)

    case .Minus, .Star, .Slash, .Modulo:
        if !is_numeric(left_type) || !is_numeric(right_type) {
            op_sym := e.op == .Minus ? "-" : e.op == .Star ? "*" : e.op == .Slash ? "/" : "%%"
            check_error(c, e.span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2,
                op_sym, type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
        return coerce_infer_to_hint(promote_numeric(c, left_type, right_type, e.span), hint)

    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(left_type) && !is_any(left_type) {
            check_error(c, e.span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(left_type))
            return Type_Error{}
        }
        if !is_integer(right_type) && !is_any(right_type) {
            check_error(c, e.span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(right_type))
            return Type_Error{}
        }
        return coerce_infer_to_hint(promote_numeric(c, left_type, right_type, e.span), hint)
    }
    return Type_Error{}
}

// When promote_numeric leaves the result as an infer type (both operands were
// untyped literals), adopt the surrounding expected hint so e.type_ carries
// concrete signedness/width to codegen. Without this, `c : u8 = 200 + 100`
// would type-check as Type_Infer_Int and codegen would default to signed
// arithmetic — silently giving the wrong overflow semantics.
coerce_infer_to_hint :: proc(t, hint: Type) -> Type {
    if _, ok := t.(Type_Infer_Int); ok {
        if n, n_ok := distinct_base(hint).(Type_Numeric); n_ok && n.kind != .Float {
            return hint
        }
    }
    if _, ok := t.(Type_Infer_Float); ok {
        if n, n_ok := distinct_base(hint).(Type_Numeric); n_ok && n.kind == .Float {
            return hint
        }
    }
    return t
}

// Promote numeric types for binary operations.
// Infer types yield to concrete types; if both infer, stay inferred.
// Both concrete operands must have matching types (no implicit widening/narrowing).
// Silent variant: returns Type_Error on irreconcilable mismatch without
// emitting a diagnostic. Used by callers that want to inspect-and-recover
// (the for-range loop falls back to slice-header width). Same rules
// otherwise: float beats int among inferred sides, infer adopts concrete,
// concrete requires exact match.
try_promote_numeric :: proc(a: Type, b: Type) -> Type {
    a_infer := is_infer(a)
    b_infer := is_infer(b)

    if a_infer && b_infer {
        if _, ok := a.(Type_Infer_Float); ok { return Type_Infer_Float{} }
        if _, ok := b.(Type_Infer_Float); ok { return Type_Infer_Float{} }
        return Type_Infer_Int{}
    }

    if a_infer { return b }
    if b_infer { return a }

    if is_any(a) || is_any(b) { return Type_Error{} }

    if types_equal(a, b) { return a }

    // Value-preserving operand mixing: widen both to the smallest type that
    // holds every value of both (i32 vs i64 → i64, i32 vs u32 → i64). No such
    // type (i64 vs u64, int vs float) → Type_Error → explicit cast required.
    if common, ok := common_numeric_type(a, b); ok { return common }

    return Type_Error{}
}

promote_numeric :: proc(c: ^Checker, a: Type, b: Type, span: Span) -> Type {
    // Deferred-inference aware: an open binding meeting a sized operand is
    // pinned to that width; two open bindings are union-linked so they
    // co-resolve. ca/cb are the raw cells (nil for anonymous/concrete); a_open
    // / b_open ask whether each side is still unbound after resolution.
    ca := infer_cell_of(a)
    cb := infer_cell_of(b)
    ra := resolve_infer(a)
    rb := resolve_infer(b)
    a_open := is_infer(ra)
    b_open := is_infer(rb)
    if a_open && b_open {
        if ca != nil && cb != nil { unify_infer_cells(c, ca, cb, span) }
        if ca != nil { return a }   // carry a binding cell so the result still defers
        if cb != nil { return b }
        return ra
    }
    if a_open {
        if ca != nil { unify_infer_concrete(c, ca, rb, span) }
        return rb
    }
    if b_open {
        if cb != nil { unify_infer_concrete(c, cb, ra, span) }
        return ra
    }
    result := try_promote_numeric(ra, rb)
    if _, ok := result.(Type_Error); ok && !is_any(ra) && !is_any(rb) {
        check_error(c, span, TYPE_MISMATCHED_TYPES_ARITHMETIC_USE_EXPLICIT,
            type_name(ra), type_name(rb))
    }
    return result
}

// Check if any param has a default value.
has_param_defaults :: proc(fun_type: ^Type_Scope) -> bool {
    for p in fun_type.params {
        if p.default_value != nil { return true }
    }
    return false
}

// Count how many required (non-default) params a function has.
count_required_params :: proc(fun_type: ^Type_Scope) -> int {
    required := len(fun_type.params)
    for i := len(fun_type.params) - 1; i >= 0; i -= 1 {
        if fun_type.params[i].default_value != nil {
            required -= 1
        } else {
            break
        }
    }
    return required
}

// Substitute `_` arguments with the corresponding parameter's default value.
// Run before fill_default_args + check_call_args so type-checking sees the
// default expressions in place of the underscores.
//
// Mutates e.args in-place; the caller resyncs check_args afterward to keep
// both views consistent.
substitute_underscore_args :: proc(c: ^Checker, e: ^Expr_Call, fun_type: ^Type_Scope, param_offset: int, display_name: string) {
    for i in 0..<len(e.args) {
        param_idx := i + param_offset
        if param_idx >= len(fun_type.params) { break }
        ident, id_ok := e.args[i].(^Expr_Ident)
        if !id_ok || ident.name != "_" { continue }
        def := fun_type.params[param_idx].default_value
        if def == nil {
            check_error(c, e.span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER,
                i + 1, display_name, fun_type.params[param_idx].name)
            continue
        }
        // Compiler intrinsic defaults need a fresh node with the call site's span.
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            e.args[i] = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = ident.span,
            })
        } else {
            e.args[i] = def
        }
    }
}

// Fill in default args for a call that has fewer args than params.
// Creates fresh intrinsic nodes resolved at the call site.
fill_default_args :: proc(c: ^Checker, e: ^Expr_Call, fun_type: ^Type_Scope, env: ^Type_Env) {
    for i := len(e.args); i < len(fun_type.params); i += 1 {
        def := fun_type.params[i].default_value
        if def == nil { continue }
        // Compiler intrinsic defaults (#caller_name / #caller_span) need fresh
        // nodes whose span resolves at the call site.
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            fresh := new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = e.span,
            })
            check_expr(c, fresh, env)
            append(&e.args, Expr(fresh))
            continue
        }
        // Regular expression default: type-check at the call site and append.
        // Sharing the AST node across call sites is fine for literals and
        // pure expressions; check_expr is idempotent for those.
        check_expr(c, def, env)
        append(&e.args, def)
    }
}

// Shared helper: check that args match a function's parameter types.
check_call_args :: proc(c: ^Checker, args: []Expr, fun_type: ^Type_Scope, display_name: string, span: Span, env: ^Type_Env) {
    required := count_required_params(fun_type)
    if len(args) < required || len(args) > len(fun_type.params) {
        check_error(c, span, TYPE_EXPECTS_ARGS, display_name, len(fun_type.params), len(args))
    } else {
        for arg, i in args {
            // Hand the parameter type down so bare variant idents like
            // `Init(Video)` can resolve `Video` against `Init_Flags`.
            c.expected_hint = fun_type.params[i].type_
            arg_type := check_expr(c, arg, env)
            // Byte-buffer reinterpret-read at the call boundary: a param
            // typed `[N]T` accepts `buf[off]` or `buf[lo:hi]` from a byte
            // buffer — same shape as `arr : [N]T = buf[off]` at decl sites.
            // The size is in the param type; codegen materializes the
            // fixed-array value via alloca + memcpy + load.
            is_byte_reinterpret := false
            if _, fa_ok := fun_type.params[i].type_.(^Type_Fixed_Array); fa_ok {
                if is_byte_buffer_index_read(arg) { is_byte_reinterpret = true }
                if _, sl_ok := arg.(^Expr_Slice); sl_ok && is_byte_buffer(arg_type) {
                    is_byte_reinterpret = true
                }
            }
            if !is_byte_reinterpret && !coerce_deferred(c, arg_type, fun_type.params[i].type_, span) && types_incompatible(fun_type.params[i].type_, arg_type) && !value_preserving_widen(arg_type, fun_type.params[i].type_) {
                arg_clause := ""
                if an := expr_diag_name(arg); an != "" {
                    arg_clause = fmt.tprintf(" ('%s')", an)
                }
                check_error(c, span, TYPE_ARGUMENT_EXPECTED,
                    i + 1, arg_clause, display_name, fun_type.params[i].name,
                    type_name(fun_type.params[i].type_), type_name(arg_type))
            }
            maybe_stamp_byte_view(c, fun_type.params[i].type_, arg)
            // Check that infer literal args fit in the parameter type
            if is_infer(arg_type) {
                check_literal_overflow(c, arg, fun_type.params[i].type_, span)
            }
        }
    }
}

// Resolve a qualified call (x.f(args) / Type.f(args) / module.f(args)).
// Mutates e to rewrite the call target, then fills `check_args` with the
// effective arg list (UFCS prepends the qualifier). Returns the resolved
// func name to write into e.resolved_func later, the resolved Type_Scope
// (so the caller can skip an env lookup with the now-flat e.name — env
// keys functions by bare name through the includes pointer chain, not by
// flat key), and an error flag if the qualifier named a module that
// doesn't contain the requested function.
resolve_qualified_call :: proc(
    c: ^Checker, e: ^Expr_Call, env: ^Type_Env, check_args: ^[dynamic]Expr,
) -> (resolution: Maybe(Resolved_Func), fn_type: ^Type_Scope, qual_dispatch_fns: [dynamic]string, error: bool) {
    resolved_assoc := false

    // Type-qualified call (TypeName.method or mod.func) — check before
    // check_expr to avoid "type is not a value" errors.
    if ident, ok := e.qualifier.(^Expr_Ident); ok {
        qual_type, qual_found := type_env_get(env, ident.name)
        if qual_found {
            if qual_sd := as_scope_body(qual_type); qual_sd != nil {
                if fn, found := qual_sd.functions[e.name]; found && fn != nil {
                    fn_type = fn
                    resolution = Resolved_Func{name = fn.name}
                    e.name = fn.name

                    // Both type qualifiers (TypeName.method) and value qualifiers
                    // (instance.method, where instance has a struct type) bind the
                    // same Type_Scope in env, so they reach this branch
                    // indistinguishably. Disambiguate by checking the symbol tables:
                    // if ident.name is a registered type, this is a static call.
                    // Otherwise it's an instance call and the qualifier needs to be
                    // prepended as the receiver.
                    is_type_qualifier := false
                    {
                        flat := resolve_type_name(c, ident.name, "", env)
                        if flat != "" {
                            if _, ok := c.table.structs[flat]; ok { is_type_qualifier = true }
                            if !is_type_qualifier {
                                if _, ok := c.table.funs[flat]; ok { is_type_qualifier = true }
                            }
                        }
                    }

                    if !is_type_qualifier && qual_sd.scope == nil {
                        // Instance-method detection: first param Self / ^Self.
                        first_param_is_self := false
                        first_param_wants_ptr := false
                        if len(fn.params) > 0 {
                            pt_inner := fn.params[0].type_
                            if pt, is_ptr := fn.params[0].type_.(^Type_Ptr); is_ptr {
                                pt_inner = pt.elem
                                first_param_wants_ptr = true
                            }
                            if as_scope_body(pt_inner) == qual_sd {
                                first_param_is_self = true
                            }
                        }
                        if first_param_is_self {
                            _, qual_is_ptr := qual_type.(^Type_Ptr)
                            if first_param_wants_ptr && !qual_is_ptr {
                                check_error(c, e.span,
                                    TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE,
                                    e.name, qual_sd.name)
                                e.qualifier = nil
                                return nil, nil, nil, true
                            }
                            new_args: [dynamic]Expr
                            append(&new_args, e.qualifier)
                            for a in e.args { append(&new_args, a) }
                            e.args = new_args
                        }
                    }

                    e.qualifier = nil
                    for a in e.args { append(check_args, a) }
                    resolved_assoc = true
                } else if t, found := qual_sd.types[e.name]; found {
                    flat := type_flat_name(t)
                    resolution = Resolved_Func{name = flat}
                    if ts, ts_ok := t.(^Type_Scope); ts_ok { fn_type = ts }
                    e.name = flat
                    e.qualifier = nil
                    for a in e.args { append(check_args, a) }
                    resolved_assoc = true
                } else if fns, found := qual_sd.dispatch_groups[e.name]; found {
                    // Qualified dispatch (e.g. `m.sqrt(x)`): pick from this
                    // module's dispatch candidates only — don't merge with
                    // the includer's other visible dispatches of the same name.
                    e.qualifier = nil
                    for a in e.args { append(check_args, a) }
                    qual_dispatch_fns = fns
                    resolved_assoc = true
                } else if qual_sd.scope != nil {
                    check_error(c, e.span, TYPE_MODULE_FUNCTION, qual_sd.name, e.name)
                    return nil, nil, nil, true
                }
            }
        }
        // Try type-qualified call (TypeName.method) via struct/fun tables
        if !resolved_assoc {
            type_flat := resolve_type_name(c, ident.name, "", env)
            assoc_sd: ^Scope_Body
            if assoc_ss, assoc_ss_ok := c.table.structs[type_flat]; assoc_ss_ok {
                assoc_sd = &assoc_ss.sd
            } else if assoc_sf, assoc_sf_ok := c.table.funs[type_flat]; assoc_sf_ok {
                assoc_sd = &assoc_sf.sd
            }
            if assoc_sd != nil {
                if fn, found := assoc_sd.functions[e.name]; found && fn != nil {
                    fn_type = fn
                    resolution = Resolved_Func{name = fn.name}
                    e.name = fn.name
                    e.qualifier = nil
                    for a in e.args { append(check_args, a) }
                    resolved_assoc = true
                }
            }
        }
    }
    // Value-qualified call (obj.method) — type-check qualifier to find struct type.
    if !resolved_assoc {
        qual_type := check_expr(c, e.qualifier, env)
        if assoc_st := resolve_to_struct_type(c, qual_type); assoc_st != nil {
            if fn, found := assoc_st.functions[e.name]; found && fn != nil {
                fn_type = fn
                resolution = Resolved_Func{name = fn.name}
                e.name = fn.name

                // Instance method detection: a method whose first param is the owning
                // struct (Self) or a pointer to it (^Self) is an instance method, and
                // the qualifier should be prepended as the receiver. Static methods
                // (no params, or first param of a different type) leave args alone.
                first_param_is_self := false
                first_param_wants_ptr := false
                if len(fn.params) > 0 {
                    pt_inner := fn.params[0].type_
                    if pt, is_ptr := fn.params[0].type_.(^Type_Ptr); is_ptr {
                        pt_inner = pt.elem
                        first_param_wants_ptr = true
                    }
                    if as_scope_body(pt_inner) == assoc_st {
                        first_param_is_self = true
                    }
                }

                if first_param_is_self {
                    // Method requires a pointer receiver, but qualifier is a value:
                    // surface a clear error rather than auto-taking-address (matches
                    // the existing "no implicit & on call args" rule per
                    // test_param_passthrough_fail).
                    _, qual_is_ptr := qual_type.(^Type_Ptr)
                    if first_param_wants_ptr && !qual_is_ptr {
                        check_error(c, e.span,
                            TYPE_METHOD_REQUIRES_POINTER_RECEIVER_TAKE,
                            e.name, assoc_st.name)
                        e.qualifier = nil
                        return nil, nil, nil, true
                    }
                    // Prepend qualifier as receiver.
                    new_args: [dynamic]Expr
                    append(&new_args, e.qualifier)
                    for a in e.args { append(&new_args, a) }
                    e.args = new_args
                }
                e.qualifier = nil
                for a in e.args { append(check_args, a) }
                resolved_assoc = true
            }
        }
    }
    if !resolved_assoc {
        // Not a package alias or associated function — UFCS: x.f(args) -> f(x, args).
        // Rewrite the AST so codegen sees a plain call with qualifier prepended as first arg.
        //
        // For the flat (mangled) name, prefer a direct env lookup: a function
        // declared in an enclosing class/struct body is registered there under
        // its bare name with a mangled `.name` like
        // `<module>_<parent>_<bare>` — make_flat_name(home, bare) would mint
        // `<module>_<bare>` and miss it. Fall back to the home-based mint only
        // when the bare name doesn't resolve to a known function in scope.
        ufcs_flat := ""
        if t, found := type_env_get(env, e.name); found {
            if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun && ts.name != "" {
                ufcs_flat = ts.name
            }
        }
        if ufcs_flat == "" {
            ufcs_flat = make_flat_name(resolve_fn_home(c, env, e.name), e.name)
        }
        resolution = Resolved_Func{name = ufcs_flat}
        new_args: [dynamic]Expr
        append(&new_args, e.qualifier)
        for a in e.args { append(&new_args, a) }
        e.args = new_args
        e.qualifier = nil
        for a in e.args { append(check_args, a) }
    }
    return resolution, fn_type, qual_dispatch_fns, false
}

// Pick the correct overload in a dispatch group based on argument types.
// Rewrites `e.name` and `e.resolved_func` to the matched overload.
//
// `_` placeholders are resolved per-candidate: each `_` arg matches any
// candidate that has a default for that param position. Trailing args may
// also be omitted as long as the missing positions have defaults — those
// fill in after the candidate is picked. All matching candidates are
// collected; if more than one matches, the call is rejected as ambiguous.
check_dispatch_call :: proc(c: ^Checker, e: ^Expr_Call, fn_names: [dynamic]string, check_args: []Expr, env: ^Type_Env) -> Type {
    // Mark underscore positions — they can't be typed without knowing which
    // overload (and therefore which default) they'll take. Non-underscore
    // args get typed once; their arg_types slot stays nil for underscores.
    is_underscore := make([]bool, len(check_args))
    defer delete(is_underscore)
    has_underscore := false
    for arg, i in check_args {
        if ident, ok := arg.(^Expr_Ident); ok && ident.name == "_" {
            is_underscore[i] = true
            has_underscore = true
        }
    }

    arg_types: [dynamic]Type
    defer delete(arg_types)
    for arg, i in check_args {
        if is_underscore[i] {
            append(&arg_types, nil)
        } else {
            append(&arg_types, check_expr(c, arg, env))
        }
    }

    matched_fns: [dynamic]string
    defer delete(matched_fns)
    matched_fts: [dynamic]^Type_Scope
    defer delete(matched_fts)

    for fn_name in fn_names {
        ft_raw, ft_found := type_env_get(env, fn_name)
        if !ft_found { continue }
        ft, ft_ok := ft_raw.(^Type_Scope)
        if !ft_ok { continue }
        // Too many args = candidate's param count must be >= supplied args.
        if len(ft.params) < len(arg_types) { continue }
        // Trailing-default check: every position beyond the supplied args must
        // have a default. Otherwise the candidate can't be called with this
        // few args.
        trailing_ok := true
        for i := len(arg_types); i < len(ft.params); i += 1 {
            if ft.params[i].default_value == nil {
                trailing_ok = false
                break
            }
        }
        if !trailing_ok { continue }

        all_match := true
        for i := 0; i < len(arg_types); i += 1 {
            if is_underscore[i] {
                // `_` requires a default at this position on this candidate.
                if ft.params[i].default_value == nil {
                    all_match = false
                    break
                }
                continue
            }
            if types_incompatible(ft.params[i].type_, arg_types[i]) {
                all_match = false
                break
            }
        }
        if all_match {
            append(&matched_fns, fn_name)
            append(&matched_fts, ft)
        }
    }

    if len(matched_fns) == 0 {
        type_strs: [dynamic]string
        defer delete(type_strs)
        for at, i in arg_types {
            if is_underscore[i] {
                append(&type_strs, "_")
            } else {
                append(&type_strs, type_name(at))
            }
        }
        check_error(c, e.span, TYPE_MATCHING_FUNCTION_DISPATCH_GROUP_ARGUMENT,
            e.name, strings.join(type_strs[:], ", "))
        return Type_Error{}
    }

    if len(matched_fns) > 1 {
        // Two or more candidates can serve this call shape — usually because a
        // trailing-default overload overlaps an exact-arity overload. Mara
        // doesn't pick a winner; the user disambiguates by supplying the
        // distinguishing arg explicitly or removing the default.
        check_error(c, e.span, TYPE_AMBIGUOUS_DISPATCH_MATCHES_MULTIPLE_OVERLOADS,
            e.name, strings.join(matched_fns[:], ", "))
        return Type_Error{}
    }

    fn_name := matched_fns[0]
    ft := matched_fts[0]

    // Substitute `_` against the chosen candidate's defaults. Mirrors
    // substitute_underscore_args + fill_default_args' span/intrinsic handling.
    // Re-runs check_expr on the substituted node so codegen sees the resolved
    // type metadata, same as fill_default_args does.
    if has_underscore {
        for i in 0..<len(e.args) {
            if !is_underscore[i] { continue }
            def := ft.params[i].default_value
            new_arg: Expr
            if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
                span := e.span
                if ident, id_ok := e.args[i].(^Expr_Ident); id_ok {
                    span = ident.span
                }
                new_arg = new_clone(Expr_Compiler_Intrinsic{
                    kind = intr.kind,
                    span = span,
                })
            } else {
                new_arg = def
            }
            check_expr(c, new_arg, env)
            e.args[i] = new_arg
        }
    }

    // Trailing default fill: append each missing slot's default expression so
    // codegen sees a fully-saturated arg list. Mirrors fill_default_args.
    for i := len(e.args); i < len(ft.params); i += 1 {
        def := ft.params[i].default_value
        new_arg: Expr
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            new_arg = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = e.span,
            })
        } else {
            new_arg = def
        }
        check_expr(c, new_arg, env)
        append(&e.args, new_arg)
    }

    disp_flat := make_flat_name(resolve_fn_home(c, env, fn_name), fn_name)
    e.name = fn_name  // rewrite call target for codegen
    e.resolved_func = Resolved_Func{name = disp_flat}
    return fn_primary_return(ft)
}

// `?` postfix propagation. Validates that the inner expression produces an
// err-compatible trailing slot AND that the enclosing function has an
// err-compatible trailing return slot to bubble into. The Expr_Try's value
// type is the inner return list minus the trailing err — void for err-only
// calls, the single value for `(T, err)` calls. Multi-value calls (`(T, U,
// err)`) aren't supported yet since Mara doesn't have true value tuples; the
// flat err-set design is what the user signed up for and that's covered.
check_try :: proc(c: ^Checker, e: ^Expr_Try, env: ^Type_Env) -> Type {
    inner_t := check_expr(c, e.inner, env)
    _ = inner_t

    call, is_call := e.inner.(^Expr_Call)
    if !is_call {
        check_error(c, e.span, TYPE_TRY_OPERAND_MUST_BE_CALL)
        return Type_Error{}
    }
    rets := call_return_list(c, call, env)
    if len(rets) == 0 || !is_err_type(rets[len(rets)-1]) {
        check_error(c, e.span, TYPE_TRY_REQUIRES_ERR_RETURN)
        return Type_Error{}
    }
    if len(env.return_types) == 0 || !is_err_type(env.return_types[len(env.return_types)-1]) {
        check_error(c, e.span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
        return Type_Error{}
    }
    if len(rets) == 1 { return Type_Void{} }    // err-only call: `?` discards err
    // For 1+ non-err returns the Try's value is the first; multi-bind
    // destructuring (Stmt_Multi_Return_Assign) consults the full return list
    // directly, so 2+ non-err returns are still legal in that context.
    // Single-bind callers (`x := foo()?` on a 2+ non-err call) get only the
    // first value bound — flagged at the multi-vs-single assignment layer
    // (the bind shape determines the right error message, not us here).
    return rets[0]
}

check_call :: proc(c: ^Checker, e: ^Expr_Call, env: ^Type_Env) -> Type {
    // Phase 1: Resolve which function we're calling.
    // Build effective args (UFCS prepends qualifier) and determine resolution.
    // Resolution is written to e.resolved_func at the end.
    check_args: [dynamic]Expr
    defer delete(check_args)
    resolution: Maybe(Resolved_Func)
    // For assoc-fn / module-qualified calls, resolve_qualified_call hands us
    // the Type_Scope directly: e.name has been rewritten to the flat key,
    // but env doesn't carry flat keys (lookups walk the includes chain by
    // bare name), so an env lookup with the rewritten name would miss.
    // UFCS leaves this nil and falls through to the bare-name env lookup.
    qual_fn_type: ^Type_Scope

    qual_dispatch_fns: [dynamic]string
    if e.qualifier != nil {
        res, ft, qfns, err := resolve_qualified_call(c, e, env, &check_args)
        if err { return Type_Error{} }
        resolution = res
        qual_fn_type = ft
        qual_dispatch_fns = qfns
    } else {
        for a in e.args { append(&check_args, a) }
    }

    // Phase 2: Check the call — builtins, then user-defined functions.
    builtin_result, is_builtin := check_builtin_call(c, e, check_args[:], env)
    if is_builtin { return builtin_result }

    // Qualified dispatch (e.g. `m.sqrt(x)`): resolve_qualified_call set
    // qual_dispatch_fns to the qualified module's candidates (only).
    if len(qual_dispatch_fns) > 0 {
        return check_dispatch_call(c, e, qual_dispatch_fns, check_args[:], env)
    }

    // Dispatch group resolution: mul(a,b) -> mat4_mul(a,b)
    // Only fires for unqualified calls — qualified resolution already picked
    // a specific function.
    if qual_fn_type == nil {
        if fn_names, is_dispatch := find_dispatch(c, env, e.name); is_dispatch {
            return check_dispatch_call(c, e, fn_names, check_args[:], env)
        }

        // Generic function instantiation
        if gtmpl, gtmpl_ok := &c.table.generic_templates[e.name]; gtmpl_ok {
            return check_generic_call(c, e, gtmpl, check_args[:], env)
        }
    }

    fun_type: ^Type_Scope
    fun_ok: bool
    if qual_fn_type != nil {
        fun_type = qual_fn_type
        fun_ok = true
    } else {
        fun_type_raw, ok := type_env_get(env, e.name)
        if !ok {
            check_error(c, e.span, TYPE_UNDEFINED_FUNCTION, e.name)
            for arg in check_args {
                check_expr(c, arg, env)
            }
            return Type_Error{}
        }

        // Distinct type construction: Foo(x) where Foo :: distinct T.
        // Same surface syntax as a primitive-type cast (i64(x)), uniformly
        // mapped over for user-defined named wrappers. Single arg required;
        // type must be compatible with the underlying. At IR level this is
        // a no-op (codegen just evaluates the arg in the underlying's IR
        // type) — the distinct-ness is purely a type-system identity.
        if dt, is_distinct := fun_type_raw.(^Type_Distinct); is_distinct {
            if len(check_args) != 1 {
                check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_3, e.name, len(check_args))
                return Type_Error{}
            }
            saved_hint := c.expected_hint
            c.expected_hint = dt.base_type
            arg_type := check_expr(c, check_args[0], env)
            c.expected_hint = saved_hint
            if !is_any(arg_type) && !is_infer(arg_type) {
                if types_incompatible(dt.base_type, arg_type) {
                    check_error(c, e.span,
                        TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE,
                        e.name, type_name(arg_type), type_name(dt.base_type))
                }
            }
            e.type_ = dt
            e.resolved_func = Resolved_Func{name = dt.name}
            return dt
        }

        fun_type, fun_ok = fun_type_raw.(^Type_Scope)
        if !fun_ok {
            check_error(c, e.span, TYPE_FUNCTION, e.name)
            return Type_Error{}
        }
    }

    // For bare calls (no qualifier), annotate with flat package-qualified name for codegen.
    // Skip if this is a function-value variable (indirect call) — leave resolution nil
    // so codegen knows to emit an indirect call through the pointer.
    if resolution == nil {
        // Only annotate if env actually bound `e.name` to a declared function.
        // A local variable with `fn(args -> ret)` annotation has a structural
        // fun_type whose .name is empty, so it must NOT be promoted to a
        // direct call even when a same-named declared function exists in
        // c.declared_funs (the local shadows). Without this, a load-and-call
        // through a function-pointer variable gets miscodegen'd as a direct
        // call to a global that doesn't exist in this binary.
        if e.name in c.declared_funs && fun_type.name != "" {
            home, home_ok, ambiguous_owners := resolve_fn_home_with_ambiguity(c, env, e.name)
            if !home_ok && len(ambiguous_owners) > 1 {
                owner_list := strings.join(ambiguous_owners[:], ", ")
                check_error(c, e.span, TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED, e.name, owner_list, ambiguous_owners[0], e.name)
                return Type_Error{}
            }
            flat := make_flat_name(home, e.name)
            resolution = Resolved_Func{name = flat}
        } else if fun_type.name != "" && fun_type.name in c.declared_funs {
            // Bare name resolved via scope (e.g. sibling function in data fun body)
            resolution = Resolved_Func{name = fun_type.name}
        }
    }

    // Single write: record resolution for codegen
    if res, res_ok := resolution.?; res_ok {
        e.resolved_func = res
    }

    // Pure data struct construction: args map directly to fields.
    // Fires for struct-like scopes (kind=.Struct) with no constructor params but
    // which have data fields. Codegen can skip the call overhead and write
    // fields directly to memory. Covers old Type_Struct usages plus classes
    // declared with empty parens `class Foo() { x: int }`.
    if fun_type.kind == .Struct && len(fun_type.params) == 0 && len(fun_type.fields) > 0 && len(fun_type.return_types) == 0 {
        return check_pure_struct_construction(c, e, fun_type, env)
    }

    // `_` at any positional arg means "use the parameter's default value here."
    // Substitute before filling tail defaults so the two mechanisms compose
    // (caller wrote some args, asked for defaults at specific slots, omitted
    // trailing args that fall back to defaults via fill_default_args).
    param_offset := len(check_args) - len(e.args)
    substitute_underscore_args(c, e, fun_type, param_offset, e.name)
    for i in 0..<len(e.args) {
        check_args[i + param_offset] = e.args[i]
    }

    // Args map to params
    if len(check_args) < len(fun_type.params) && has_param_defaults(fun_type) {
        fill_default_args(c, e, fun_type, env)
        clear(&check_args)
        for a in e.args { append(&check_args, a) }
    }

    check_call_args(c, check_args[:], fun_type, e.name, e.span, env)

    // Constructor with params: the call's value IS the struct itself (Self).
    // A fallible constructor also declares a trailing err — that's exposed to
    // `?` and `t, e := ...` via constructor_effective_returns / call_return_list;
    // in plain scalar context the result type is still Self.
    if fun_type.kind == .Struct && len(fun_type.params) > 0 {
        e.type_ = fun_type
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &fun_type.sd, e.span, env)
        }
        return fun_type
    }

    if e.overrides != nil {
        check_error(c, e.span, TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID, e.name)
    }
    // Multi-return call in scalar context: caller must destructure via
    // `x, y := f()`. Single-return funs return their one type; void returns nil.
    if fn_has_multi_return(fun_type) {
        return fn_primary_return(fun_type)
    }
    return fn_primary_return(fun_type)
}

// Pure-struct positional construction: parameterless struct called with positional
// args mapped to fields. Single entry point used by check_call's pure-struct
// branch and check_generic_call's post-instantiation calls (Array(Player, 64),
// Pair(int)(1, 2)).
//
// Supports `_` substitution against field defaults — same surface as the
// regular function call path applies to parameter defaults.
check_pure_struct_construction :: proc(c: ^Checker, e: ^Expr_Call, st: ^Type_Scope, env: ^Type_Env) -> Type {
    e.type_ = st
    if e.resolved_func == nil && st.name != "" {
        e.resolved_func = Resolved_Func{name = st.name}
    }

    // `Foo()` (no args) is always valid — equivalent to bare declaration `x : Foo`.
    // Init function applies defaults and zero-inits fields without defaults.
    if len(e.args) == 0 {
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env)
        }
        return st
    }

    // `_` at any positional arg means "use the field's default value here."
    // Mirrors substitute_underscore_args for parameters.
    for i in 0..<len(e.args) {
        if i >= len(st.fields) { break }
        ident, id_ok := e.args[i].(^Expr_Ident)
        if !id_ok || ident.name != "_" { continue }
        def := st.fields[i].default_value
        if def == nil {
            check_error(c, e.span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_FIELD,
                i + 1, st.name, st.fields[i].name)
            continue
        }
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            e.args[i] = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = ident.span,
            })
        } else {
            e.args[i] = def
        }
    }

    num_required := 0
    for f in st.fields {
        if f.default_value == nil { num_required += 1 }
    }
    if len(e.args) > len(st.fields) {
        check_error(c, e.span, TYPE_FIELD_ARGUMENT, st.name, len(st.fields), len(e.args))
    } else if len(e.args) < num_required {
        check_error(c, e.span, TYPE_REQUIRES_LEAST_ARGUMENT, st.name, num_required, len(e.args))
    }
    for arg, i in e.args {
        if i < len(st.fields) {
            c.expected_hint = st.fields[i].type_
        }
        arg_type := check_expr(c, arg, env)
        if i < len(st.fields) {
            field := st.fields[i]
            if !coerce_deferred(c, arg_type, field.type_, e.span) && types_incompatible(field.type_, arg_type) && !is_any(arg_type) && !value_preserving_widen(arg_type, field.type_) {
                check_error(c, e.span, TYPE_FIELD_EXPECTED,
                    field.name, type_name(field.type_), type_name(arg_type))
            }
        }
    }
    if e.overrides != nil {
        check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env)
    }
    return st
}

// check_module_call removed — module calls now resolve through the unified
// assoc_fn/types path in check_call, same as type-qualified calls.
check_array_literal :: proc(c: ^Checker, e: ^Expr_Array, env: ^Type_Env) -> Type {
    if len(e.elements) == 0 {
        // Empty array literal — type is unknown until assigned
        return Type_Error{}
    }

    // Infer element type from first element
    elem_type := check_expr(c, e.elements[0], env)
    for i := 1; i < len(e.elements); i += 1 {
        et := check_expr(c, e.elements[i], env)
        if types_incompatible(elem_type, et) {
            check_error(c, e.span, TYPE_ARRAY_ELEMENT_TYPE_EXPECTED,
                i, type_name(et), type_name(elem_type))
        }
    }

    // Array literals produce a fixed array with size == len
    result := new(Type_Fixed_Array)
    result.size = len(e.elements)
    result.elem = elem_type
    return result
}

check_index :: proc(c: ^Checker, e: ^Expr_Index, env: ^Type_Env) -> Type {
    target_type := distinct_base(check_expr(c, e.expr, env))
    // Auto-deref: `^[]T` and `^[N]T` index like their pointee. Mirrors the
    // field-access auto-deref so `s[i]` for `s: ^[]T` (the mutable slice
    // param form) works without a manual `s^[i]`.
    if pt, ok := target_type.(^Type_Ptr); ok {
        inner := distinct_base(pt.elem)
        if _, sl_ok := inner.(^Type_Slice); sl_ok { target_type = inner }
        else if _, fa_ok := inner.(^Type_Fixed_Array); fa_ok { target_type = inner }
    }
    // If the array declares a typed index ([N IT]T), surface it as the hint so
    // a bare `keys.pressed[Escape]` resolves `Escape` against `Scancode`.
    if fa, ok := target_type.(^Type_Fixed_Array); ok && fa.index_type != nil {
        c.expected_hint = fa.index_type
    }
    idx_type := check_expr(c, e.index, env)

    if !is_numeric(idx_type) {
        check_error(c, e.span, TYPE_INDEX_NUMBER, type_name(idx_type))
    } else if !coerces_to_index_width(idx_type) {
        // Index may be any integer; the runtime bounds check (emitted at the
        // index's width before narrowing) makes a too-wide value safe.
        check_error(c, e.span, TYPE_INDEX_WIDTH,
            type_name(slice_header_width_type),
            type_name(idx_type))
    }

    // Array indexing returns element type
    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        // Compile-time bounds check when we have both pieces — the
        // array's visible size is fa.size (sentinel slot, if any, is
        // not addressable), and a literal/const index folds via
        // evaluate_comptime_int. Lets `s := "hello"; s[5]` be a
        // compile error instead of a runtime trap.
        if idx_val, idx_ok := evaluate_comptime_int(c, e.index); idx_ok {
            if idx_val < 0 || idx_val >= i64(fa.size) {
                check_error(c, e.span, TYPE_INDEX_OUT_OF_BOUNDS_CONST,
                    idx_val, fa.size, fa.size - 1)
            }
        }
        return fa.elem
    }

    // Slice indexing returns element type
    if sl, ok := target_type.(^Type_Slice); ok {
        // Byte slice index: returns Type_Byte; actual reinterpret type comes from annotation
        return sl.elem
    }

    // Partial array indexing — same as slice; the header has matching first
    // slice_header_bytes so codegen can reuse the slice indexing path.
    if pa, ok := target_type.(^Type_Partial_Array); ok {
        return pa.elem
    }

    if !is_any(target_type) {
        check_error(c, e.span, TYPE_CANNOT_INDEX_INTO, type_name(target_type))
    }
    return Type_Error{}
}

check_slice :: proc(c: ^Checker, e: ^Expr_Slice, env: ^Type_Env) -> Type {
    target_type := check_expr(c, e.expr, env)
    // Auto-deref: `s[lo:hi]` for `s: ^[]T` or `s: ^[N]T` slices the pointee.
    if pt, ok := target_type.(^Type_Ptr); ok {
        inner := distinct_base(pt.elem)
        if _, sl_ok := inner.(^Type_Slice); sl_ok { target_type = inner }
        else if _, fa_ok := inner.(^Type_Fixed_Array); fa_ok { target_type = inner }
    }


    // Determine element type from source (array or slice)
    elem_type: Type = nil
    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        elem_type = fa.elem
    } else if sl, ok := target_type.(^Type_Slice); ok {
        elem_type = sl.elem
    } else if pa, ok := target_type.(^Type_Partial_Array); ok {
        elem_type = pa.elem
    } else if !is_any(target_type) {
        check_error(c, e.span, TYPE_CANNOT_SLICE, type_name(target_type))
        return Type_Error{}
    }

    // Check that low/high are numeric AND match slice header width — codegen
    // does NOT emit an implicit narrow/widen.
    if e.low != nil {
        lt := check_expr(c, e.low, env)
        if !is_numeric(lt) && !is_any(lt) {
            check_error(c, e.span, TYPE_SLICE_LOW_BOUND_NUMERIC, type_name(lt))
        } else if !coerces_to_slice_width(lt) {
            check_error(c, e.span, TYPE_INDEX_WIDTH,
                type_name(slice_header_width_type), type_name(lt))
        }
    }
    if e.high != nil {
        ht := check_expr(c, e.high, env)
        if !is_numeric(ht) && !is_any(ht) {
            check_error(c, e.span, TYPE_SLICE_HIGH_BOUND_NUMERIC, type_name(ht))
        } else if !coerces_to_slice_width(ht) {
            check_error(c, e.span, TYPE_INDEX_WIDTH,
                type_name(slice_header_width_type), type_name(ht))
        }
    }

    if elem_type == nil {
        return Type_Error{}
    }
    result := new(Type_Slice)
    result.elem = elem_type
    return result
}

// Check if we can assign a value type to an annotated array type.
// Full arrays: requires exact size match.
// ---------------------------------------------------------------------------
// Using field resolution
// ---------------------------------------------------------------------------

// Resolve a field name on a struct, searching direct fields first, then
// recursively into using-marked embedded struct fields.
// Returns the field type, or nil if not found.
resolve_struct_field :: proc(st: ^Scope_Body, field_name: string, table: ^SymbolTable = nil) -> Type {
    // O(1) direct field lookup via field_map
    if idx, ok := st.field_map[field_name]; ok {
        return st.fields[idx].type_
    }
    // Check associated types (scoped :: defs accessible as fields)
    if st.types != nil {
        if inner, at_ok := st.types[field_name]; at_ok {
            return inner
        }
    }
    // Search using-marked fields (embedded structs)
    for f in st.fields {
        if f.is_using {
            if inner_sd := as_scope_body(f.type_); inner_sd != nil && len(inner_sd.fields) > 0 {
                result := resolve_struct_field(inner_sd, field_name, table)
                if result != nil {
                    return result
                }
            }
        }
    }
    return nil
}

// ---------------------------------------------------------------------------
// Swizzle helpers (xyzw / rgba)
// ---------------------------------------------------------------------------

// Maps a swizzle character to an array index, or -1 if invalid.
swizzle_char_to_index :: proc(ch: u8) -> int {
    switch ch {
    case 'x', 'r': return 0
    case 'y', 'g': return 1
    case 'z', 'b': return 2
    case 'w', 'a': return 3
    }
    return -1
}

// Returns true if `field` is a valid swizzle for an array of the given capacity.
// Every character must be a valid swizzle char (xyzw or rgba) with index < capacity.
is_swizzle_field :: proc(field: string, capacity: int) -> bool {
    if len(field) == 0 { return false }
    for ch in transmute([]u8)field {
        idx := swizzle_char_to_index(ch)
        if idx < 0 || idx >= capacity { return false }
    }
    return true
}

// Returns true if every character in `field` is a swizzle char (regardless of capacity).
is_all_swizzle_chars :: proc(field: string) -> bool {
    if len(field) == 0 { return false }
    for ch in transmute([]u8)field {
        if swizzle_char_to_index(ch) < 0 { return false }
    }
    return true
}

