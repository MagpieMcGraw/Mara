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
    Type_Int,
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
    ^Type_Tuple,      // (int, string) — tuple for multi-return
    ^Type_Distinct,   // named wrapper around another type (same layout, different identity)
    Type_Const_Int,      // compile-time integer value — used as const generic param (e.g., n=256)
    Type_Runtime_Size,   // runtime-sized const generic param (e.g., String(n) where n is a variable)
    Type_Any,            // for opaque pointer elements only (ptr → ^Type_Ptr{elem=Type_Any{}})
    Type_Error,       // error recovery — suppresses cascading type errors
}

Type_Int :: struct {}
Type_F64 :: struct {}
Type_Infer_Int :: struct {}
Type_Infer_Float :: struct {}
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
Type_Error :: struct {}

Type_Tuple :: struct {
    elems: [dynamic]Type,
}

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
    is_vla:       bool,       // true for variable-length arrays (runtime size)
    size_expr:    Expr,       // AST expression for runtime size (VLA only)
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
    is_vla:       bool,       // true for variable-length partial arrays (runtime size)
    size_expr:    Expr,       // AST expression for runtime size (VLA only)
    has_sentinel: bool,
    sentinel:     int,
}

Struct_Type_Field :: struct {
    name:          string,
    type_:         Type,
    default_value: Expr, // nil if no default
    is_using:      bool,
    is_var:        bool, // on fun params: caller may pass VLA-shaped instantiations
}

// The body of a Type_Scope — embedded via `using sd: Scope_Body`.
// Holds the fields, nested defs, methods, and other content shared
// between data-layout scopes (struct/class) and callable scopes (fun).
Scope_Body :: struct {
    name:           string,  // C-ified flat name (e.g. "game_Point", "sdl_Init"), "" for anonymous

    // Data fields — the members of a struct/class, or extracted locals on a fun scope
    fields:         [dynamic]Struct_Type_Field,
    field_map:      map[string]int,  // field name -> index into fields (for O(1) lookup)

    has_vla_field:  bool,    // true if any field is a VLA (struct must be arena-allocated)
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
    generic_args:   [dynamic]Type, // [Type_Int{}] for Array__int — for reverse inference
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

    // Return type — data types return themselves, functions return their declared type
    return_type:    Type,

    // ABI calling convention. Defaults to .Mara (zero value). Foreign declarations
    // set this to .C so the codegen lowers the signature per the platform C ABI.
    // See abi.odin for the classifier; phases 3+ consume this at signature /
    // call-site emission time.
    calling_conv:   Calling_Conv,
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
    if tn, ok := s.return_type.(Type_Name); ok && tn.name == s.name { return true }
    return false
}

// Extract field declarations from a fun body (Stmt_Assign nodes become fields).
extract_fields_from_body :: proc(body: [dynamic]Stmt) -> [dynamic]Scope_Binding {
    fields: [dynamic]Scope_Binding
    for stmt in body {
        #partial switch s in stmt {
        case ^Stmt_Assign:
            // name : type = value → field (explicit type)
            // name := value → field (inferred type)
            append(&fields, Scope_Binding{
                name          = s.name,
                type_expr     = s.type_expr,
                default_value = s.value,
                is_using      = s.is_using,
            })
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
            for name, i in s.names {
                val: Expr = nil
                if i < len(s.init_values) { val = s.init_values[i] }
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
    name:         string,  // C-ified flat name
    tag_type:     string,                    // "" = default (i64), or "i32", "i16", etc.
    variants:     map[string]int,
}

Type_Union :: struct {
    name:            string,             // C-ified flat name
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
    types:       map[string]Type,
    parent:      ^Type_Env,
    return_type: Type,       // expected return type for current function
    param_names: map[string]bool, // function parameter names (for escape analysis)
    let_names:   map[string]bool, // take-bound view names (storage aliased at source bytes); kept for legacy field name
    provenance:  map[string]Provenance, // where pointer/slice data lives
    scope_depth: int,        // stack depth for escape analysis; module = 0, function body = 1+
    // Locals whose struct value has slice fields pointing into our frame's
    // sibling/pool buffers (set when bound from a call with escape locals).
    // Returning such a local would dangle once the frame pops.
    local_slice_backed: map[string]bool,
    uninit_refs: map[string]bool, // ptr/slice vars declared without initializer (read = error)
    newly_inited: map[string]bool, // ancestor uninit vars initialized in THIS scope (for definite assignment)
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
    for cur != nil {
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
    case ^Type_Tuple:    return rawptr(v)
    case ^Type_Fixed_Array: return rawptr(v)
    }
    return nil
}

type_env_set :: proc(env: ^Type_Env, name: string, t: Type) {
    env.types[name] = t
}

// Check if a variable is an uninitialized pointer/slice (walks scope chain).
// Respects newly_inited: if a child scope initialized it, it's not uninit in that scope.
is_uninit_ref :: proc(env: ^Type_Env, name: string) -> bool {
    cur := env
    for cur != nil {
        if name in cur.newly_inited { return false } // shadowed by init in this scope
        if name in cur.uninit_refs { return true }
        cur = cur.parent
    }
    return false
}

// Mark a variable as initialized. If declared in this scope, removes directly.
// If declared in an ancestor scope, records in newly_inited (doesn't mutate parent).
mark_initialized :: proc(env: ^Type_Env, name: string) {
    // Local scope: delete directly
    if name in env.uninit_refs {
        delete_key(&env.uninit_refs, name)
        return
    }
    // Ancestor scope: record locally, don't mutate parent
    cur := env.parent
    for cur != nil {
        if name in cur.uninit_refs {
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
add_struct_uninit_fields :: proc(env: ^Type_Env, var_name: string, st: ^Scope_Body, provided: map[string]bool = nil) {
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
            env.uninit_refs[key] = true
        }
    }
}

// Clear all field-level uninit entries for a variable (e.g. when the whole struct is reassigned).
// Local entries are deleted directly; ancestor entries are recorded in newly_inited.
clear_struct_uninit_fields :: proc(env: ^Type_Env, var_name: string) {
    prefix := strings.concatenate({var_name, "."})
    // Clear from current scope directly
    keys_to_delete: [dynamic]string
    for key in env.uninit_refs {
        if strings.has_prefix(key, prefix) {
            append(&keys_to_delete, key)
        }
    }
    for key in keys_to_delete {
        delete_key(&env.uninit_refs, key)
    }
    // For ancestor scopes, record in newly_inited
    cur := env.parent
    for cur != nil {
        for key in cur.uninit_refs {
            if strings.has_prefix(key, prefix) {
                env.newly_inited[key] = true
            }
        }
        cur = cur.parent
    }
}

// Check if a variable has any uninitialized pointer/slice fields.
// Returns the first uninit field name, or nil. Respects newly_inited shadowing.
first_uninit_field :: proc(env: ^Type_Env, var_name: string) -> Maybe(string) {
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
        for key in cur.uninit_refs {
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
    return Type_Env{parent = parent, return_type = parent.return_type, fn_name = parent.fn_name, scope_depth = parent.scope_depth}
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
            // Strict-default match: every match either covers all variants
            // (enforced by the type checker) or has an else arm. So if every
            // arm always returns, the match as a whole always returns too.
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
    name:        string,
    type_:       ^Type_Scope,            // resolved param + return types
    params:      [dynamic]Checked_Param,
    return_type: Type,
    body:        [dynamic]Stmt,        // original AST body
    ast:         ^Stmt_Scope,            // original AST node (for auto-monomorphization)
    origin:      Function_Origin,      // Source / Intrinsic / Foreign — codegen dispatch
    span:        Span,
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
        check_error(c, e.span, "'.%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s",
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
    fmt.printf("[%s] Type error: ", format_location(span.file, span.line, span.col))
    fmt.printf(msg, ..args)
    fmt.println()
    c.errors += 1
}

check_warning :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    fmt.printf("[%s] Warning: ", format_location(span.file, span.line, span.col))
    fmt.printf(msg, ..args)
    fmt.println()
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
    class_ft, ok := field_type.(^Type_Scope)
    if !ok || class_ft.kind != .Struct { return }
    if len(class_ft.params) == 0 { return }
    for p in class_ft.params {
        if p.default_value == nil {
            check_error(c, span, "'%s' of type '%s' has no initializer, but constructor requires argument '%s' (no default) — supply constructor arguments", name, class_ft.name, p.name)
            return
        }
    }
}


// ---------------------------------------------------------------------------
// Resolve a parser Type_Expr to a checker Type
// ---------------------------------------------------------------------------

resolve_type_expr :: proc(te: Type_Expr, c: ^Checker = nil, span: Span = {}, const_values: ^map[string]int = nil, env: ^Type_Env = nil) -> Type {
    switch t in te {
    case Type_Name:
        switch t.name {
        case "int":
            // Reserved keyword; not a valid type today. Kept in the lexer
            // so the name is available if word-sized `int` returns later.
            if c != nil {
                check_error(c, span, "type 'int' is reserved — use 'i64' (or 'isize' for word-sized)")
            }
            return Type_Error{}
        case "f64":    return Type_F64{}
        case "bool":   return Type_Bool{}
        case "cstring": return Type_CString{}
        case "c8":     return Type_C8{}
        case "utf8":   return Type_Utf8{}
        case "byte":   return Type_Byte{}
        case "i8":     return Type_Numeric{kind = .Signed,   bits = 8}
        case "i16":    return Type_Numeric{kind = .Signed,   bits = 16}
        case "i32":    return Type_Numeric{kind = .Signed,   bits = 32}
        case "i64":    return Type_Numeric{kind = .Signed,   bits = 64}
        case "u8":     return Type_Numeric{kind = .Unsigned, bits = 8}
        case "u16":    return Type_Numeric{kind = .Unsigned, bits = 16}
        case "u32":    return Type_Numeric{kind = .Unsigned, bits = 32}
        case "u64":    return Type_Numeric{kind = .Unsigned, bits = 64}
        case "uint":
            // Reserved keyword; same retired status as `int`. Use 'u64' or 'usize'.
            if c != nil {
                check_error(c, span, "type 'uint' is reserved — use 'u64' (or 'usize' for word-sized)")
            }
            return Type_Error{}
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
                    check_error(c, span, "type name '%s' is ambiguous (defined in: %s). Use a qualified path or seal one of the includes (e.g. `name :: sealed include ...`).", t.name, owner_list)
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
            if tmpl, tmpl_ok := &c.table.generic_templates[t.name]; tmpl_ok {
                all_defaulted := true
                type_args: [dynamic]Type
                for param in tmpl.generic_params {
                    if param.is_const && param.has_default {
                        append(&type_args, Type_Const_Int{value = param.default_value})
                    } else if !param.is_const {
                        all_defaulted = false
                        break
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
            check_error(c, span, "unknown type '%s'", t.name)
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
                check_error(c, span, "runtime-sized arrays are not supported. Use 'var' with Array instead:\n\n    import \"array\"\n    name : var [N]%s", type_name(elem))
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
                        check_error(c, span, "array size constant '%s' is not a compile-time integer", t.size_name)
                    }
                } else {
                    // Not a constant — runtime-sized arrays must use var Array
                    check_error(c, span, "runtime-sized arrays are not supported. Use 'var' with Array instead:\n\n    import \"array\"\n    name : var [%s]%s", t.size_name, type_name(elem))
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
                pa.is_vla = true
                pa.size_expr = t.size_expr
                return pa
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
                    check_error(c, span, "partial-array size constant '%s' is not a compile-time integer", t.size_name)
                    return Type_Error{}
                }
                pa.is_vla = true
                pa.size_expr = new_clone(Expr_Ident{name = t.size_name, span = span})
                return pa
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
    case ^Type_Tuple_Expr:
        tt := new(Type_Tuple)
        for e in t.elems {
            append(&tt.elems, resolve_type_expr(e, c, span, env = env))
        }
        return tt
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
            append(&type_args, resolve_type_expr(arg, c, span))
        }
        // Look up generic struct template
        if tmpl_ptr != nil {
            tmpl := tmpl_ptr
            // Fill in missing const params from defaults
            for i := len(type_args); i < len(tmpl.generic_params); i += 1 {
                param := tmpl.generic_params[i]
                if param.is_const && param.has_default {
                    append(&type_args, Type_Const_Int{value = param.default_value})
                }
            }
            if len(type_args) != len(tmpl.generic_params) {
                check_error(c, span, "'%s' expects %d type argument(s), got %d",
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
                check_error(c, span, "'%s' expects %d type argument(s), got %d",
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
        check_error(c, span, "unknown generic type '%s'", t.name)
        return Type_Error{}
    case ^Type_Func_Expr:
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in t.params {
            append(&ft.params, Struct_Type_Field{type_ = resolve_type_expr(p, c, span)})
        }
        if t.return_type != nil {
            ft.return_type = resolve_type_expr(t.return_type, c, span)
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
                            "'fn %s' requires a function-valued name; '%s' has type %s",
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
                    check_error(c, span, "unknown function '%s' in 'fn %s'", t.name, t.name)
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
                check_error(c, span, "unknown function '%s' in 'fn %s'", t.name, t.name)
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
                } else if rs, rs_ok := sub_type.(Type_Runtime_Size); rs_ok {
                    // Runtime-sized: mark as VLA
                    fa.is_vla = true
                    fa.size_expr = rs.expr
                    resolved = true
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
            // Expression-based size (VLA)
            fa.is_vla = true
            fa.size_expr = t.size_expr
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
                } else if rt, ok := val.(Type_Runtime_Size); ok {
                    pa.is_vla = true
                    pa.size_expr = rt.expr
                }
            } else if c != nil {
                if const_expr, found2 := c.table.constants[t.size_name]; found2 {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        pa.size = int(i_val)
                    }
                }
            }
        } else if t.size_expr != nil {
            pa.is_vla = true
            pa.size_expr = t.size_expr
        } else {
            pa.size = t.size
        }
        return pa
    case ^Type_Tuple_Expr:
        tt := new(Type_Tuple)
        for e in t.elems {
            append(&tt.elems, resolve_type_expr_with_subst(e, c, span, subst))
        }
        return tt
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
        check_error(c, span, "unknown generic type '%s'", t.name)
        return Type_Error{}
    case ^Type_Func_Expr:
        ft := new(Type_Scope)
        ft.kind = .Fun
        for p in t.params {
            append(&ft.params, Struct_Type_Field{type_ = resolve_type_expr_with_subst(p, c, span, subst)})
        }
        if t.return_type != nil {
            ft.return_type = resolve_type_expr_with_subst(t.return_type, c, span, subst)
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

    // Build substitution map: "T" -> Type_Int{}, etc.
    subst: map[string]Type
    for param, i in tmpl.generic_params {
        subst[param.name] = type_args[i]
    }

    // Create concrete Type_Scope with C-ified name
    st := new(Type_Scope)
    st.name = make_flat_name(tmpl.home_package, mangled)
    st.kind = .Struct
    st.generic_base = tmpl.name
    for arg in type_args {
        append(&st.generic_args, arg)
    }

    tmpl_fields := tmpl.ast.fields if len(tmpl.ast.fields) > 0 else extract_fields_from_body(tmpl.ast.body)
    for field in tmpl_fields {
        ft := resolve_type_expr_with_subst(field.type_expr, c, span, &subst)
        // Check for VLA fields
        if fa, fa_ok := ft.(^Type_Fixed_Array); fa_ok && fa.is_vla {
            st.has_vla_field = true
        }
        // Substitute generic value params in default values: a field default
        // like `cap: i64 = n` references the const generic n; at instantiation
        // we replace that ident with the bound value (e.g. 256) so codegen
        // doesn't try to look up `n` as a runtime variable.
        dv := field.default_value
        if ident, ok := dv.(^Expr_Ident); ok {
            if sub, sub_ok := subst[ident.name]; sub_ok {
                if ci, ci_ok := sub.(Type_Const_Int); ci_ok {
                    new_num := new(Expr_Number)
                    new_num.int_value = i64(ci.value)
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
    case ^Type_Tuple_Expr:
        if tup, ok := actual.(^Type_Tuple); ok {
            for e, i in t.elems {
                if i < len(tup.elems) {
                    infer_type_params(subst, e, tup.elems[i], c)
                }
            }
        }
    case ^Type_Func_Expr:
        if ft, ok := actual.(^Type_Scope); ok {
            for p, i in t.params {
                if i < len(ft.params) {
                    infer_type_params(subst, p, ft.params[i].type_, c)
                }
            }
            if t.return_type != nil && ft.return_type != nil {
                infer_type_params(subst, t.return_type, ft.return_type, c)
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
    for tp in ast.typed_params {
        pt := resolve_type_expr_with_subst(tp.type_expr, c, ast.span, subst)
        append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value, is_var = tp.is_var})
    }
    fun_type.return_type = resolve_type_expr_with_subst(ast.return_type, c, ast.span, subst)
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
    child.return_type = fun_type.return_type
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
    mono_ft.return_type = ft.return_type
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
    child.return_type = mono_ft.return_type
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
                        check_error(c, e.span, "argument %d to '%s': const generic parameter '%s' requires a compile-time integer", i, tmpl.name, param.name)
                        return Type_Error{}
                    }
                } else {
                    append(&type_args, arg_types[i])
                }
            } else if param.is_const && param.has_default {
                append(&type_args, Type_Const_Int{value = param.default_value})
            } else {
                check_error(c, e.span, "'%s' requires generic parameter '%s' (no default)", tmpl.name, param.name)
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
                    name        = st.name,
                    type_       = st,
                    return_type = st,
                    body        = tmpl.ast.body,
                    ast         = tmpl.ast,
                    origin      = Origin_Source{},
                    span        = e.span,
                }
                c.checked.functions[st.name] = cs
                append(&c.checked.function_order, st.name)
            }
        }

        return check_constructor_call(c, e, st, {}, env)
    }

    // Also try to infer from the return type context if needed (future enhancement)

    // Step 3: Verify all type params were resolved
    for param in tmpl.generic_params {
        if subst[param.name] == nil {
            check_error(c, e.span, "could not infer type parameter '$%s' in call to '%s'", param.name, e.name)
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
        check_error(c, e.span, "failed to instantiate generic function '%s'", e.name)
        return Type_Error{}
    }
    fun_type, fun_ok := fun_type_raw.(^Type_Scope)
    if !fun_ok {
        check_error(c, e.span, "failed to instantiate generic function '%s'", e.name)
        return Type_Error{}
    }
    // Generic constructor call: e.g. Pair(int)(1, 2)
    if len(fun_type.fields) > 0 && len(fun_type.params) == 0 {
        return check_constructor_call(c, e, fun_type, args, env)
    }

    // Step 7: Rewrite the call to target the mangled name
    e.name = mangled
    fn_flat_name := make_flat_name(tmpl.home_package, mangled)
    e.resolved_func = Resolved_Func{name = fn_flat_name}

    // Step 8: Validate arg count matches concrete param count
    if len(args) != len(fun_type.params) {
        check_error(c, e.span, "'%s' expects %d argument(s), got %d", tmpl.name, len(fun_type.params), len(args))
    }

    return fun_type.return_type
}

// ---------------------------------------------------------------------------
// Type comparison
// ---------------------------------------------------------------------------

types_equal :: proc(a: Type, b: Type) -> bool {
    // nil return type (void) — only matches itself
    if a == nil && b == nil { return true }
    if a == nil || b == nil { return false }

    // Error type matches everything (suppress cascading errors)
    if _, ok := a.(Type_Error); ok { return true }
    if _, ok := b.(Type_Error); ok { return true }

    // Transparent type aliases (`Name :: type(T)`) unwrap to their base
    // before any other comparison. They have no nominal identity — they
    // exist purely as renames. `distinct` types do not unwrap here.
    a := unwrap_alias(a)
    b := unwrap_alias(b)

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
    case Type_Int:
        if _, ok := b.(Type_Int); ok { return true }
        if _, ok := b.(Type_Infer_Int); ok { return true }
        // Enums are compatible with int (symmetric with the Type_Enum case)
        if _, ok := b.(^Type_Enum); ok { return true }
        // `int` and `i64` are the same type — Type_Int is the special-cased
        // form, Type_Numeric{Signed, 64} is the same value spelled with the
        // exact-width name. Builtin returns (slice.len, len(), etc.) still
        // produce Type_Int; user code now writes i64 — they need to match.
        if vb, vb_ok := b.(Type_Numeric); vb_ok && vb.kind == .Signed && vb.bits == 64 { return true }
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
        // Symmetric with the Type_Int case above: i64 == int.
        if _, ok := b.(Type_Int); ok { return va.kind == .Signed && va.bits == 64 }
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
        if _, ok := b.(Type_CString); ok { return true }
        // cstring is compatible with utf8 arrays (full or partial) — pass data_ptr as C string
        if fa, ok := b.(^Type_Fixed_Array); ok {
            if _, utf8_ok := fa.elem.(Type_Utf8); utf8_ok { return true }
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
        // Structural: compare params + return type (for anonymous/callable funs)
        if len(va.params) != len(vb.params) { return false }
        for p, i in va.params {
            if !types_equal(p.type_, vb.params[i].type_) { return false }
        }
        return types_equal(va.return_type, vb.return_type)
    case ^Type_Fixed_Array:
        // utf8 arrays are compatible with cstring (pass data_ptr as C string)
        if _, utf8_ok := va.elem.(Type_Utf8); utf8_ok {
            if _, ok := b.(Type_CString); ok { return true }
        }
        // Implicit coercion: [N]T is compatible with []T (array → slice)
        if sl, sl_ok := b.(^Type_Slice); sl_ok {
            return types_equal(va.elem, sl.elem)
        }
        vb, ok := b.(^Type_Fixed_Array)
        if !ok { return false }
        return types_equal(va.elem, vb.elem)
        // Note: we don't compare size here — arrays of same elem type are compatible
        // Size checking is done at assignment/init time
    case ^Type_Slice:
        // Implicit coercion: [:]T is compatible with [N]T (slice ← array)
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return types_equal(va.elem, fa.elem)
        }
        // Implicit coercion: [:]T is compatible with [..N]T (slice ← partial array view)
        if pa, pa_ok := b.(^Type_Partial_Array); pa_ok {
            return types_equal(va.elem, pa.elem) && va.has_sentinel == pa.has_sentinel
        }
        vb, ok := b.(^Type_Slice)
        if !ok { return false }
        return types_equal(va.elem, vb.elem)
    case ^Type_Partial_Array:
        // Partial arrays coerce to [:]T (slice view) and to [N]T (fixed array)
        // by element type. The first 24 bytes of a partial array's layout
        // match a slice header, so `^[..N]T` flows safely into `^[:]T` param
        // slots — cursor mutations propagate back through the aliased memory.
        if sl, sl_ok := b.(^Type_Slice); sl_ok {
            return types_equal(va.elem, sl.elem) && va.has_sentinel == sl.has_sentinel
        }
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return types_equal(va.elem, fa.elem)
        }
        if pa, ok := b.(^Type_Partial_Array); ok {
            return va.size == pa.size && types_equal(va.elem, pa.elem) &&
                   va.has_sentinel == pa.has_sentinel
        }
        return false
    case ^Type_Enum:
        // Enums are compatible with int, infer_int, numeric integer types, and the same enum
        if _, ok := b.(Type_Int); ok { return true }
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
    case ^Type_Tuple:
        vb, ok := b.(^Type_Tuple)
        if !ok { return false }
        if len(va.elems) != len(vb.elems) { return false }
        for e, i in va.elems {
            if !types_equal(e, vb.elems[i]) { return false }
        }
        return true
    case ^Type_Distinct:
        // After unwrap_alias at types_equal's entry, only nominal distinct
        // types reach this case. Match strictly by name.
        if vb, ok := b.(^Type_Distinct); ok {
            return va.name == vb.name
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
    case Type_Error:
        return true
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
    switch v in t {
    case Type_Int:          return "int"
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
    case ^Type_Tuple:
        b := strings.builder_make()
        strings.write_byte(&b, '(')
        for e, i in v.elems {
            if i > 0 { strings.write_string(&b, ", ") }
            strings.write_string(&b, type_name(e))
        }
        strings.write_byte(&b, ')')
        return strings.to_string(b)
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
        strings.write_string(&b, ") -> ")
        strings.write_string(&b, type_name(v.return_type))
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
    case Type_Error:        return "<error>"
    }
    return "void"
}

// Is this a numeric type?
is_numeric :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Int); ok { return true }
    if _, ok := t.(Type_F64); ok { return true }
    if _, ok := t.(Type_Infer_Int); ok { return true }
    if _, ok := t.(Type_Infer_Float); ok { return true }
    if _, ok := t.(Type_Numeric); ok { return true }
    if _, ok := t.(^Type_Enum); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
    return false
}

is_integer :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Int); ok { return true }
    if _, ok := t.(Type_Infer_Int); ok { return true }
    if n, ok := t.(Type_Numeric); ok { return n.kind != .Float }
    if _, ok := t.(^Type_Enum); ok { return true }
    if _, ok := t.(Type_Error); ok { return true }
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
    if _, ok := t.(^Type_Tuple); ok { return true }
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
    if _, ok := t.(Type_Infer_Int); ok { return true }
    if _, ok := t.(Type_Infer_Float); ok { return true }
    return false
}

// True when a type is a byte slice ([]byte). Auto-derefs one level of ^Ptr
// so `^[]byte` (the "mutable slice" parameter shape) is recognized too —
// codegen already binds it as a Slice_Var via slice_through_distinct_and_ptr.
is_byte_slice :: proc(t: Type) -> bool {
    cur := t
    if pt, ok := cur.(^Type_Ptr); ok { cur = pt.elem }
    sl, ok := cur.(^Type_Slice)
    if !ok { return false }
    _, is_byte := sl.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element fixed array [N]byte. Auto-derefs ^Ptr.
is_byte_fixed_array :: proc(t: Type) -> bool {
    cur := t
    if pt, ok := cur.(^Type_Ptr); ok { cur = pt.elem }
    fa, ok := cur.(^Type_Fixed_Array)
    if !ok { return false }
    _, is_byte := fa.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element partial array [..N]byte. Auto-derefs ^Ptr.
// Distinct aliases unwrap so `^String`-style mutable buffer params register too.
is_byte_partial_array :: proc(t: Type) -> bool {
    cur := t
    if pt, ok := cur.(^Type_Ptr); ok { cur = pt.elem }
    if dt, ok := cur.(^Type_Distinct); ok { cur = dt.base_type }
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
        if offset % a != 0 {
            offset += a - (offset % a)
        }
        offset += checker_type_byte_size(f.type_)
    }
    if max_align > 0 && offset % max_align != 0 {
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
    case Type_Int, Type_F64, Type_Infer_Int, Type_Infer_Float,
         Type_CString, ^Type_Ptr, ^Type_Slice, ^Type_Partial_Array,
         ^Type_Enum, ^Type_Union, ^Type_Tuple,
         Type_Const_Int, Type_Runtime_Size,
         Type_Any, Type_Error:
        return 8
    case Type_Numeric:
        switch v.bits {
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

// Byte size of a checker type (for big-array threshold checks).
checker_type_byte_size :: proc(t: Type) -> int {
    switch v in t {
    case Type_Int, Type_Infer_Int, Type_F64, Type_Infer_Float,
         ^Type_Ptr, Type_CString,
         ^Type_Union, ^Type_Tuple,
         Type_Const_Int, Type_Runtime_Size,
         Type_Any, Type_Error, nil:
        return 8
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
                    "cannot return result of `%s(...)`: its return may reference local memory via %s — pass caller-rooted %s instead",
                    call.name, strings.to_string(sb), noun)
                return
            }
        }
    }
    check_error(c, span,
        "cannot return local reference (memory freed on function return)")
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
    if _, ok := t.(Type_Infer_Int); ok { return Type_Int{} }
    if _, ok := t.(Type_Infer_Float); ok { return Type_F64{} }
    return t
}

// Try to extract a compile-time constant numeric value from an expression.
// Returns both forms — f64 (for fractional/range-vs-float comparisons) and
// i64 (exact for integer literals). Callers use whichever matches the type
// they're checking. f64 is lossy above 2^53 but i64 stays exact.
extract_constant_value :: proc(expr: Expr) -> (f_val: f64, i_val: i64, ok: bool) {
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
    val, _, is_const := extract_constant_value(expr)
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
        // 64-bit types: skip overflow check (f64 can't precisely represent the boundary)
        if v.bits >= 64 { return }
        // Word-sized (bits=0): skip too. Width is decided at codegen, and the
        // 32-bit case is conservative — anything that would overflow there
        // already overflows on the 64-bit case worth catching.
        if v.bits == 0 { return }
        switch v.kind {
        case .Signed:
            max := f64(int(1) << uint(v.bits - 1) - 1)
            min := -max - 1
            if val < min || val > max {
                check_error(c, span, "constant %v overflows %s (range %v..%v)", int(val), tn, int(min), int(max))
            }
        case .Unsigned:
            max := f64(int(1) << uint(v.bits) - 1)
            if val < 0 || val > max {
                check_error(c, span, "constant %v overflows %s (range 0..%v)", int(val), tn, int(max))
            }
        case .Float:
            // f32 range check
            if v.bits == 32 {
                if val > 3.4028235e+38 || val < -3.4028235e+38 {
                    check_error(c, span, "constant %v overflows f32", val)
                }
            }
        }
    case Type_Int:
        // i64 — f64 can't precisely represent the boundary, skip
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

// Infer a field's type from its default value without full check_expr
// (which would fail because the enclosing fun's params/locals aren't in scope yet).
// Handles: identifiers (constants/variables in env), number/string/bool literals,
// and calls to known struct constructors / functions with a return type.
infer_field_type_from_default :: proc(c: ^Checker, value: Expr, env: ^Type_Env) -> Type {
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
    }
    if n, ok := value.(^Expr_Number); ok {
        if n.is_float { return Type_F64{} }
        return Type_Int{}
    }
    // String literals default to Type_Any (no simple string type)

    if _, ok := value.(^Expr_Bool); ok {
        return Type_Bool{}
    }
    // Call expressions: look up the callee's Type_Scope in the env.
    //   struct constructor (kind=.Struct with params)  → the struct type itself
    //   function call       (kind=.Fun with return_type) → the return type
    if call, ok := value.(^Expr_Call); ok && call.name != "" {
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
                if ft.kind == .Fun && ft.return_type != nil { return ft.return_type }
            }
        }
    }
    // Binary ops: arithmetic / bitwise / shift preserve the operand type.
    // Comparison ops produce bool. Recurse on the left operand so e.g.
    // `1 << 16` (Number << Number) → Type_Int.
    if bin, ok := value.(^Expr_Binary); ok {
        #partial switch bin.op {
        case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal, .And, .Or:
            return Type_Bool{}
        case:
            return infer_field_type_from_default(c, bin.left, env)
        }
    }
    // Unary ops: same idea — type follows the operand.
    if un, ok := value.(^Expr_Unary); ok {
        return infer_field_type_from_default(c, un.operand, env)
    }
    return Type_Any{}
}

check_scope :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env, owner: ^Type_Scope = nil, public_env: ^Type_Env = nil) {
    // Pass 1: register all declarations in this scope.
    // When owner is non-nil, top-level decls are attached to it as
    // functions/types/pseudo-fields (so modules own their members
    // uniformly with nested-struct ownership via register_scope_defs).
    // public_env (when non-nil) is the scope that should receive top-level
    // PUBLIC defined names (functions, types, constants) — used by check_module
    // so file privates land in env (file_env) while public defs land in mod_env.
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
            if def_is_struct && s.return_type != nil {
                check_error(c, s.span, "struct/class '%s' cannot declare a return type", bare_name)
                s.return_type = nil  // suppress cascading return-path errors
            }
            if def_is_struct && len(s.typed_params) == 0 {
                // Pure data struct — create Type_Scope with kind=.Struct, no params
                // Phase 2 (check_bodies) resolves fields; we only register the name here.
                def_st := new(Type_Scope)
                def_st.name = mangled
                def_st.kind = .Struct
                c.table.structs[mangled] = def_st
                if st.types == nil { st.types = make(map[string]Type) }
                st.types[bare_name] = def_st
                append(&st.fields, Struct_Type_Field{name = bare_name, type_ = def_st})
                st.field_map[bare_name] = len(st.fields) - 1
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
                def_ft.has_parens = s.has_parens
                if def_is_struct {
                    def_ft.kind = .Struct
                    // Phase 2 (check_bodies) resolves fields; we only register the name here.
                    c.table.funs[mangled] = def_ft
                    if st.types == nil { st.types = make(map[string]Type) }
                    st.types[bare_name] = def_ft
                    append(&st.fields, Struct_Type_Field{name = bare_name, type_ = def_ft})
                    st.field_map[bare_name] = len(st.fields) - 1
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
                        append(&def_ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value, is_var = tp.is_var})
                    }
                    build_param_map(def_ft)
                }
                if is_callable && s.return_type != nil {
                    def_ft.return_type = resolve_type_expr(s.return_type, c, s.span, env=&scope_env)
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
                bare_name := decl.name
                mangled := fmt.aprintf("%s_%s", st.name, bare_name)
                fun_type.name = mangled
                for tp in decl.typed_params {
                    pt := resolve_type_expr(tp.type_expr, c, decl.span, env=&scope_env)
                    append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt})
                }
                fun_type.return_type = resolve_type_expr(decl.return_type, c, decl.span, env=&scope_env)
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

register_type_names :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Env, owner: ^Type_Scope = nil, public_env: ^Type_Env = nil) {
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
                    check_error(c, s.span, "enum '%s' already defined", s.name)
                    continue
                }
                et := new(Type_Enum)
                et.name = flat
                et.tag_type = s.tag_type
                for vdef in s.variants {
                    et.variants[vdef.name] = vdef.tag
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
                    check_error(c, s.span, "union '%s' already defined", s.name)
                    continue
                }
                ut := new(Type_Union)
                ut.name = flat
                ut.tag_type = s.tag_type
                ut.min_size = s.min_size
                // tag_pad: deferred to Pass 1b (type expr)
                // Tag enum can be fully built — variant tags are integers, no type refs.
                tag_enum_name := strings.concatenate({s.name, "_Tag"})
                tag_et := new(Type_Enum)
                tag_et.name = make_flat_name(c.current_package, tag_enum_name)
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
                check_error(c, s.span, "%s '%s' already defined", kind, s.name)
                continue
            }
            dt := new(Type_Distinct)
            dt.name = flat
            dt.default_cap_expr = s.default_cap_expr
            dt.is_alias = s.is_alias
            // base_type: deferred to Pass 1b
            c.table.distinct_types[flat] = dt
            type_env_set(pub, s.name, dt)
            c.pre_registered_stmts[rawptr(s)] = true
        case ^Stmt_Scope:
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
            if is_struct_type && s.return_type != nil {
                // Will diagnose properly in Pass 1b; suppress here.
                continue
            }
            if is_struct_type && len(s.typed_params) == 0 {
                flat := make_flat_name(c.current_package, s.name)
                if flat in c.table.structs || flat in c.table.funs {
                    check_error(c, s.span, "type '%s' already defined", s.name)
                    continue
                }
                struct_type := new(Type_Scope)
                struct_type.name = flat
                struct_type.kind = .Struct
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
                        check_error(c, s.span, "type '%s' already defined", s.name)
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
                c.pre_registered_stmts[rawptr(s)] = true
            }
        case ^Stmt_If:
            // Comptime #if: recurse into the live arm so its declarations
            // pre-register at the surrounding scope. Same shape as Pass 1b.
            if !s.is_comptime { continue }
            live, ok := evaluate_comptime_bool(c, s.condition)
            if !ok { continue }  // Pass 1b will report the error.
            if live {
                register_type_names(c, s.body, env, owner, public_env)
            } else if len(s.else_body) > 0 {
                register_type_names(c, s.else_body, env, owner, public_env)
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
                et.tag_type = s.tag_type
                if et.name in c.table.enums {
                    check_error(c, s.span, "enum '%s' already defined", s.name)
                } else {
                    for vdef in s.variants {
                        et.variants[vdef.name] = vdef.tag
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
                if ut.name in c.table.unions {
                    check_error(c, s.span, "union '%s' already defined", s.name)
                } else {
                    // 1. Create tag enum (Name_Tag)
                    tag_enum_name := strings.concatenate({s.name, "_Tag"})
                    tag_et := new(Type_Enum)
                    tag_et.name = make_flat_name(c.current_package, tag_enum_name)
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
            dt.base_type = base
            dt.default_cap_expr = s.default_cap_expr
            dt.is_alias = s.is_alias
            if dt.name in c.table.distinct_types {
                kind := "type" if s.is_alias else "distinct type"
                check_error(c, s.span, "%s '%s' already defined", kind, s.name)
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
                        if len(s.typed_params) > 0 {
                            for tp in s.typed_params {
                                pt: Type
                                if tp.type_expr != nil {
                                    pt = resolve_type_expr(tp.type_expr, c, s.span, env = env)
                                } else if tp.default_value != nil {
                                    if _, is_uninit := tp.default_value.(^Expr_Uninit); is_uninit {
                                        check_error(c, s.span, "param '%s' has no type — `---` requires an explicit type annotation (e.g. `%s : T = ---`)", tp.name, tp.name)
                                        pt = Type_Error{}
                                    } else {
                                        pt = infer_field_type_from_default(c, tp.default_value, env)
                                    }
                                } else {
                                    pt = Type_Error{}
                                }
                                append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value, is_var = tp.is_var})
                            }
                            build_param_map(fun_type)
                        }
                        is_callable := !is_struct || len(s.typed_params) > 0
                        if is_callable && s.return_type != nil {
                            fun_type.return_type = resolve_type_expr(s.return_type, c, s.span, env = env)
                            if fa, fa_ok := fun_type.return_type.(^Type_Fixed_Array); fa_ok && fa.is_vla {
                                check_error(c, s.span, "variable-length arrays cannot be returned from functions")
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
                    check_error(c, s.span, "function '%s' already defined", s.name)
                    continue
                }
            }
            // Data/layout vs callable is now determined by the AST kind tag
            // set by the parser from the declaration keyword (see the matching
            // comment in register_scope_defs for details).
            is_struct_type := s.kind == .Struct
            if is_struct_type && s.return_type != nil {
                check_error(c, s.span, "struct/class '%s' cannot declare a return type", s.name)
                s.return_type = nil  // suppress cascading return-path errors
            }
            if is_struct_type && len(s.typed_params) == 0 {
                // Pure data struct — create Type_Scope with kind=.Struct, no params
                struct_type := new(Type_Scope)
                struct_type.name = make_flat_name(c.current_package, s.name)
                struct_type.kind = .Struct
                if struct_type.name in c.table.structs || struct_type.name in c.table.funs {
                    check_error(c, s.span, "type '%s' already defined", s.name)
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
                        check_error(c, s.span, "type '%s' already defined", s.name)
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
                            if _, is_uninit := tp.default_value.(^Expr_Uninit); is_uninit {
                                check_error(c, s.span, "param '%s' has no type — `---` requires an explicit type annotation (e.g. `%s : T = ---`)", tp.name, tp.name)
                                pt = Type_Error{}
                            } else {
                                // `name(s) := default` — infer the param's type from the default expression.
                                pt = infer_field_type_from_default(c, tp.default_value, env)
                            }
                        } else {
                            pt = Type_Error{}
                        }
                        append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value, is_var = tp.is_var})
                    }
                    build_param_map(fun_type)
                }
                is_callable := !is_struct_type || len(s.typed_params) > 0
                if is_callable && s.return_type != nil {
                    fun_type.return_type = resolve_type_expr(s.return_type, c, s.span, env = env)
                    if fa, fa_ok := fun_type.return_type.(^Type_Fixed_Array); fa_ok && fa.is_vla {
                        check_error(c, s.span, "variable-length arrays cannot be returned from functions")
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
                fun_type.name = make_flat_name(c.current_package, decl.name)
                for tp in decl.typed_params {
                    pt := resolve_type_expr(tp.type_expr, c, decl.span, env = env)
                    append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt})
                }
                fun_type.return_type = resolve_type_expr(decl.return_type, c, decl.span, env = env)
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
                check_error(c, s.span, "#if condition must be a comptime-known boolean")
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
                // `name :: use path` — explicit aliasing form. Find every
                // matching module (parent + parent.* submodules), load and
                // flatten each. The "main" module (name == inc.path) is what
                // binds to s.name so qualified access like `name.X` works.
                matching := find_matching_modules(c, inc.path)
                defer delete(matching)
                if len(matching) == 0 {
                    check_error(c, inc.span, "module '%s' not found", inc.path)
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
                                num.int_value = i64(cv.value)
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
                            num.int_value = i64(cv.value)
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
                        a.is_var = s.is_var
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
            // Include expressions: scope-based resolution.
            // mara.X → look up X in std scope (stdlib modules)
            // bare Y → walk scope chain for sibling, lazy-load if not found
            if inc, is_include := s.value.(^Expr_Include); is_include {
                // Bare `use path` (mara-prefixed or not — the path is just a
                // dotted module name now). Find every matching module
                // (parent + parent.* submodules), load and flatten each.
                matching := find_matching_modules(c, inc.path)
                defer delete(matching)
                if len(matching) == 0 {
                    check_error(c, inc.span, "module '%s' not found", inc.path)
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

            // `var` keyword: rewrite fixed arrays to Array class, force arena allocation
            if s.is_var {
                if s.type_expr == nil {
                    check_error(c, s.span, "'var' requires a type annotation")
                } else if ta, ta_ok := s.type_expr.(^Type_Array); ta_ok {
                    // var [N]T -> Array(T, N) — rewrite to generic Array class
                    gi := new(Type_Generic_Instance)
                    gi.name = "Array"
                    gi.span = ta.span
                    append(&gi.type_args, ta.elem)
                    append(&gi.type_args, Type_Const_Value{value = ta.size, span = ta.span})
                    s.type_expr = gi
                }
                if !c.table.has_scope_allocator && !c.table.context_expected_at_runtime {
                    check_error(c, s.span,
                        "'var' requires a scope allocator. Set up in main:\n\n    include mara.memory\n    context.scope_allocator = Arena_Basic")
                }
            }

            ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)

            // `var` only allowed on Array and String types
            if s.is_var {
                _, is_type_err := ann_type.(Type_Error)
                if !is_type_err && ann_type != nil {
                    base := distinct_base(ann_type)
                    is_var_type := false
                    if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 {
                        is_var_type = sd.generic_base == "Array" || sd.generic_base == "String"
                    }
                    if !is_var_type {
                        check_error(c, s.span, "'var' can only be used with Array or String types, got %s", type_name(ann_type))
                    }
                }
            }

            // For VLA struct instantiations (e.g. String(n)), extract the runtime size
            // expression and store it on the Stmt_Assign for codegen.
            if gi, gi_ok := s.type_expr.(^Type_Generic_Instance); gi_ok {
                if tmpl, tmpl_ok := &c.table.generic_templates[gi.name]; tmpl_ok {
                    for arg, i in gi.type_args {
                        if i < len(tmpl.generic_params) && tmpl.generic_params[i].is_const {
                            if ce, ce_ok := arg.(Type_Const_Expr); ce_ok {
                                s.vla_size_expr = ce.expr
                            } else if tn, tn_ok := arg.(Type_Name); tn_ok {
                                // Check if it's a runtime variable (not a compile-time constant)
                                if _, found := c.table.constants[tn.name]; !found {
                                    s.vla_size_expr = new_clone(Expr_Ident{name = tn.name, span = tn.span})
                                }
                            }
                        }
                    }
                }
            }

            // Reject same-scope redeclarations (`x := 5` then `x := 7`) and shadowing
            // of any local binding in an enclosing scope up to the module boundary.
            // Reassignment with `=` is unaffected — those parse as Stmt_Assign with
            // is_decl=false and never reach this branch's Stmt_Decl-derived path.
            if s.is_decl && s.name in env.types {
                check_error(c, s.span, "variable '%s' already declared in this scope", s.name)
                continue
            }
            if s.is_decl && !env.is_module_scope {
                outer := env.parent
                for outer != nil {
                    if outer.is_module_scope { break }
                    if s.name in outer.types {
                        check_error(c, s.span, "variable '%s' shadows an enclosing binding", s.name)
                        break
                    }
                    outer = outer.parent
                }
            }

            // Nothing can shadow a constant from an outer scope
            if s.name in c.table.constants && s.name not_in env.types {
                check_error(c, s.span, "variable '%s' shadows a constant from an outer scope", s.name)
                continue
            }

            // Take binding: `name := take(T, storage)` (or with an annotation).
            // Same alias-into-caller-storage semantics as let — mark the name
            // as a view binding so it can't escape via return.
            if take_expr, is_take := s.value.(^Expr_Take); is_take {
                val_type := check_expr(c, s.value, env)
                // If an annotation was given, it must match take's resolved type.
                if !is_any(ann_type) {
                    if types_incompatible(ann_type, val_type) {
                        check_error(c, s.span,
                            "cannot assign %s to variable '%s' of type %s",
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
                    check_error(c, s.span, "declaration without initializer requires a type annotation")
                }
                // Big-array check for uninitialized arrays (unwrap distinct)
                base_ann := distinct_base(ann_type)
                if fa, ok := base_ann.(^Type_Fixed_Array); ok {
                    total_bytes := fa.size * checker_type_byte_size(fa.elem)
                    if total_bytes >= 1024 && !c.table.has_scope_allocator && !c.table.context_expected_at_runtime {
                        check_error(c, s.span,
                            "array '%s' is too large for the stack (%d bytes). Set up a scope allocator in main:\n\n    include mara.memory\n    context.scope_allocator = Arena_Basic",
                            s.name, total_bytes)
                    }
                }
                // VLA struct: require var keyword, type-check size expression
                if sd := as_scope_body(base_ann); sd != nil && sd.has_vla_field {
                    if !s.is_var {
                        // Use the generic base name for a cleaner error message
                        user_type := sd.generic_base != "" ? sd.generic_base : type_name(ann_type)
                        check_error(c, s.span,
                            "runtime-sized types require the 'var' keyword:\n\n    %s : var %s",
                            s.name, user_type)
                    }
                    if s.vla_size_expr != nil {
                        size_type := check_expr(c, s.vla_size_expr, env)
                        if !is_any(size_type) && !is_numeric(size_type) {
                            check_error(c, s.span, "size expression must be an integer, got %s", type_name(size_type))
                        }
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
                            "slice capacity must be an integer, got %s", type_name(cap_type))
                    }
                }
                s.var_type = distinct_base(ann_type)
                s.env_type = ann_type
                type_env_set(env, s.name, ann_type)
                set_provenance(env, s.name, prov_local(env)) // uninitialized local is at our depth
                // Track uninitialized pointers/slices — reading before assignment is an error
                base := distinct_base(ann_type)
                if _, is_ptr := base.(^Type_Ptr); is_ptr {
                    env.uninit_refs[s.name] = true
                } else if _, is_slice := base.(^Type_Slice); is_slice {
                    // Sized slices `name : []T(N)` allocate storage at decl time,
                    // so they're not uninitialized.
                    if s.slice_cap_expr == nil {
                        env.uninit_refs[s.name] = true
                    }
                } else if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 {
                    // Track uninit ptr/slice fields inside a struct declared without initializer
                    add_struct_uninit_fields(env, s.name, sd)
                }
                continue
            }

            c.expected_hint = ann_type
            val_type := check_expr(c, s.value, env)
            if !is_any(ann_type) {
                // If ann_type is distinct and val_type is NOT a literal (array/struct),
                // skip structural checks — use nominal comparison directly.
                _, ann_is_distinct := ann_type.(^Type_Distinct)
                _, val_is_array := s.value.(^Expr_Array)
                _, val_is_struct_lit := s.value.(^Expr_Struct_Literal)
                if ann_is_distinct && !val_is_array && !val_is_struct_lit {
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
                                            "byte buffer read: %s is %d bytes, but slice span is %d bytes",
                                            type_name(ann_type), ann_size, span_size)
                                    }
                                }
                            }
                        }
                    } else if types_incompatible(ann_type, val_type) {
                        check_error(c, s.span, "cannot assign %s to variable '%s' of type %s",
                            type_name(val_type), s.name, type_name(ann_type))
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
                    s.var_type = distinct_base(ann_type)
                    s.env_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    set_provenance(env, s.name, prov_local(env)) // struct literal is local
                    // Track uninit ptr/slice fields not provided in the literal
                    if lit, lit_ok := s.value.(^Expr_Struct_Literal); lit_ok {
                        provided: map[string]bool
                        for field in lit.fields { provided[field.name] = true }
                        add_struct_uninit_fields(env, s.name, sd, provided)
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
                    check_array_assign(c, s.span, s.name, fa, val_type)
                    // Big-array check: require scope allocator for large stack arrays
                    total_bytes := fa.size * checker_type_byte_size(fa.elem)
                    if total_bytes >= 1024 && !c.table.has_scope_allocator && !c.table.context_expected_at_runtime {
                        check_error(c, s.span,
                            "array '%s' is too large for the stack (%d bytes). Set up a scope allocator in main:\n\n    include mara.memory\n    context.scope_allocator = Arena_Basic",
                            s.name, total_bytes)
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
                                        "byte buffer read: %s is %d bytes, but slice span is %d bytes",
                                        type_name(check_ann), ann_size, span_size)
                                }
                            }
                        }
                    }
                } else if is_byte_buffer_index_read(s.value) {
                    // Byte buffer reinterpret read via index: x : int = mem[0]
                    // Size comes from the annotation type; bounds checked at runtime
                } else if types_incompatible(ann_type, val_type) {
                    check_error(c, s.span, "cannot assign %s to variable '%s' of type %s",
                        type_name(val_type), s.name, type_name(ann_type))
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
            } else {
                // No type annotation: variables solidify.
                // But DON'T overwrite if the variable already has a declared type
                // (e.g. verts2 += [...] should not replace verts2's [6]f32 type).
                existing_type, loc_env, already_declared := type_env_locate(env, s.name)
                // Field-leak guard: reassignment targeting a name that lives in
                // an ancestor class scope is a field written without receiver.
                if already_declared && loc_env != env && loc_env.class_scope != nil {
                    if is_real_field(&loc_env.class_scope.sd, s.name) {
                        check_error(c, s.span,
                            "'%s' is a field of '%s'; assign through the receiver (e.g. 'a.%s = ...')",
                            s.name, loc_env.class_scope.name, s.name)
                        continue
                    }
                }
                if !already_declared {
                    // `x := ---` has no type to infer from. Require an
                    // explicit annotation: `x : T = ---`.
                    if _, is_uninit := s.value.(^Expr_Uninit); is_uninit {
                        check_error(c, s.span, "'%s' has no type — `---` requires an explicit type annotation (e.g. `%s : T = ---`)", s.name, s.name)
                        type_env_set(env, s.name, Type_Error{})
                        continue
                    }
                    solid := solidify_type(val_type)
                    if is_untyped(solid) {
                        check_warning(c, s.span, "variable '%s' has no concrete type (type checking bypassed)", s.name)
                    }
                    s.var_type = distinct_base(solid)
                    s.env_type = solid
                    type_env_set(env, s.name, solid)
                    set_provenance(env, s.name, expr_provenance(c, s.value, env))
                    mark_local_slice_backed_if_needed(c, env, s.name, s.value)
                } else {
                    // Reassignment: mark as initialized (clears uninit_refs for ptr/slice)
                    mark_initialized(env, s.name)
                    // Also clear any field-level uninit entries (whole struct reassignment)
                    clear_struct_uninit_fields(env, s.name)
                    // Reassignment: check value type matches existing variable type
                    if types_incompatible(existing_type, val_type) {
                        check_error(c, s.span, "cannot assign %s to variable '%s' of type %s",
                            type_name(val_type), s.name, type_name(existing_type))
                    }
                    maybe_stamp_byte_view(c, existing_type, s.value)
                    if is_infer(val_type) {
                        check_literal_overflow(c, s.value, existing_type, s.span)
                    }
                    s.var_type = distinct_base(existing_type)
                    s.env_type = existing_type
                    set_provenance(env, s.name, expr_provenance(c, s.value, env))
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
                // Single RHS (multi-return call): x, y := call()
                val_type := check_expr(c, s.values[0], env)
                if tup, ok := val_type.(^Type_Tuple); ok {
                    if len(s.names) != len(tup.elems) {
                        check_error(c, s.span, "multi-return assign: left side has %d names but right side returns %d values",
                            len(s.names), len(tup.elems))
                    } else {
                        for name, i in s.names {
                            resolved_type := solidify_type(tup.elems[i])
                            if name != "" {
                                // Bare identifier: declare new variable
                                type_env_set(env, name, resolved_type)
                            } else if i < len(s.targets) && s.targets[i] != nil {
                                // Expression target (field access, index, etc.): check type compatibility
                                target_type := check_expr(c, s.targets[i], env)
                                if !is_any(target_type) && !is_any(resolved_type) {
                                    if !types_equal(target_type, resolved_type) {
                                        check_error(c, s.span, "cannot assign %s to %s in multi-return",
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
                    check_error(c, s.span, "multi-return assign requires a function returning multiple values, got %s",
                        type_name(val_type))
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
                dt := check_expr(c, field.default_value, env)
                if types_incompatible(field.type_, dt) && !is_any(dt) {
                    check_error(c, s.span, "default value for field '%s': expected %s, got %s",
                        field.name, type_name(field.type_), type_name(dt))
                }
            }
        }
    }
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
            }
        } else if field.default_value != nil {
            if _, is_uninit := field.default_value.(^Expr_Uninit); is_uninit {
                check_error(c, s.span, "field '%s' has no type — `---` requires an explicit type annotation (e.g. `%s : T = ---`)", field.name, field.name)
                field_type = Type_Error{}
            } else {
                field_type = infer_field_type_from_default(c, field.default_value, &child)
            }
        } else {
            field_type = Type_Any{}
        }
        if field.is_using {
            if _, fa_ok := field_type.(^Type_Fixed_Array); fa_ok {
                // array class — validated below
            } else if using_sd := as_scope_body(field_type); using_sd == nil || len(using_sd.fields) == 0 {
                check_error(c, s.span, "using field '%s' must be a struct or fixed-array type", field.name)
            }
        }
        append(&ft.fields, Struct_Type_Field{name = field.name, type_ = field_type, default_value = field.default_value, is_using = field.is_using})
        added_any_field = true
    }
    if added_any_field {
        build_field_map(&ft.sd)
    }
    if len(ft.params) == 0 && len(s.typed_params) > 0 {
        for tp in s.typed_params {
            pt := resolve_type_expr(tp.type_expr, c, s.span, env=&child)
            append(&ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value, is_var = tp.is_var})
        }
        build_param_map(ft)
    }
    if ft.return_type == nil && s.return_type != nil {
        ft.return_type = resolve_type_expr(s.return_type, c, s.span, env=&child)
        if fa, fa_ok := ft.return_type.(^Type_Fixed_Array); fa_ok && fa.is_vla {
            check_error(c, s.span, "variable-length arrays cannot be returned from functions")
        }
    }

    // Pre-pass bails here — signature resolved, body deferred to main pass.
    if signature_only { return }

    if len(s.body) == 0 { return }

    // Register params in scope
    child.return_type = ft.return_type
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

    // Return check — functions with nil return_type don't need return statements
    if ft.return_type != nil && !is_any(ft.return_type) && !always_returns(s.body) {
        check_error(c, s.span, "function '%s' missing return on all code paths", s.name)
    }
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
            check_error(c, s.span, "cannot iterate over struct type '%s'", ct.name)
            elem_type = Type_Any{}
        case Type_Int, Type_F64, Type_Infer_Int, Type_Infer_Float, Type_Bool,
             Type_CString, Type_C8, Type_Utf8, Type_Byte, Type_Numeric,
             ^Type_Ptr, ^Type_Enum, ^Type_Union, ^Type_Tuple, ^Type_Distinct,
             Type_Const_Int, Type_Runtime_Size, Type_Any, Type_Error,
             nil:
            check_error(c, s.span, "cannot iterate over type '%s'", type_name(coll_type))
            elem_type = Type_Any{}
        }

        if s.iter_type != nil {
            elem_type = resolve_type_expr(s.iter_type, c, s.span)
        }

        if s.elem_var != "" {
            type_env_set(&child, s.elem_var, elem_type)
        }
        if s.index_var != "" {
            type_env_set(&child, s.index_var, Type_Int{})
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
            iter_type = promote_numeric(c, low_type, high_type, s.span)
            if _, ok := iter_type.(Type_Error); ok {
                iter_type = Type_Int{}
            }
            if is_infer(iter_type) {
                iter_type = Type_Int{}
            }
        }

        if !is_numeric(low_type) && !is_infer(low_type) && !is_any(low_type) {
            check_error(c, s.span, "range lower bound must be numeric, got %s", type_name(low_type))
        }
        if !is_numeric(high_type) && !is_infer(high_type) && !is_any(high_type) {
            check_error(c, s.span, "range upper bound must be numeric, got %s", type_name(high_type))
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
            check_error(c, s.span, "for condition must be bool, got %s", type_name(cond_type))
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
    if len(s.values) > 1 {
        tup, is_tup := env.return_type.(^Type_Tuple)
        if !is_tup && !is_any(env.return_type) {
            check_error(c, s.span, "multi-value return in function that doesn't return a tuple")
        } else if is_tup && len(s.values) != len(tup.elems) {
            check_error(c, s.span, "return value count %d does not match expected %d",
                len(s.values), len(tup.elems))
        } else if is_tup {
            for val, i in s.values {
                c.expected_hint = tup.elems[i]
                vt := check_expr(c, val, env)
                if !is_any(vt) && !is_any(tup.elems[i]) {
                    if !types_equal(tup.elems[i], vt) {
                        check_error(c, s.span, "return value %d: type %s does not match expected %s",
                            i+1, type_name(vt), type_name(tup.elems[i]))
                    }
                }
                maybe_stamp_byte_view(c, tup.elems[i], val)
                if is_infer(vt) {
                    check_literal_overflow(c, val, tup.elems[i], s.span)
                }
            }
        } else {
            for val in s.values {
                check_expr(c, val, env)
            }
        }
    } else if len(s.values) == 1 {
        c.expected_hint = env.return_type
        val_type := check_expr(c, s.values[0], env)
        if !is_any(env.return_type) && !is_any(val_type) {
            if !types_equal(env.return_type, val_type) {
                check_error(c, s.span, "return type %s does not match expected %s",
                    type_name(val_type), type_name(env.return_type))
            }
        }
        maybe_stamp_byte_view(c, env.return_type, s.values[0])
        if is_infer(val_type) {
            check_literal_overflow(c, s.values[0], env.return_type, s.span)
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
                    "cannot return struct whose slice fields point at local memory; the escape mechanism only applies to direct `return Lit[local_arr, ...]` forms (memory freed on function return)")
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
                    check_error(c, s.span, "#if condition must be a comptime-known boolean")
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
                check_error(c, s.span, "if condition must be bool, got %s", type_name(cond_type))
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
            check_expr(c, s.expr, env)

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
                        check_error(c, s.span, "invalid assignment target")
                    }
                case:
                    check_error(c, s.span, "invalid assignment target")
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
                        check_error(c, s.span, "dispatch group '%s': '%s' is not a function", s.name, fn_name)
                    }
                } else if fn_name not_in c.table.generic_templates {
                    check_error(c, s.span, "dispatch group '%s': function '%s' not defined", s.name, fn_name)
                }
            }
        case Stmt_Overload:
            if _, ok := find_dispatch(c, env, s.dispatch_name); !ok {
                check_error(c, s.span, "overload: '%s' is not a dispatch group", s.dispatch_name)
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

    ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)
    val_type := check_expr(c, s.value, env)

    if !is_any(ann_type) {
        // Distinct + non-literal: use nominal compatibility (mirrors Stmt_Assign path)
        _, ann_is_distinct := ann_type.(^Type_Distinct)
        _, val_is_array := s.value.(^Expr_Array)
        _, val_is_struct_lit := s.value.(^Expr_Struct_Literal)

        if ann_is_distinct && !val_is_array && !val_is_struct_lit {
            if types_incompatible(ann_type, val_type) {
                check_error(c, s.span, "cannot assign %s to constant '%s' of type %s",
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
            check_error(c, s.span, "cannot assign %s to constant '%s' of type %s",
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
    if is_infer(val_type) {
        c.table.constants[s.name] = s.value
    }
}

// Validate that a struct literal's fields match a struct definition:
// every literal field exists and has the right type, and no struct fields are missing.
check_struct_literal_fields :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, st: ^Scope_Body, span: Span, env: ^Type_Env) {
    // Positional form (`Foo{a, b, c}`): match entries to struct fields by index.
    if lit.positional {
        // Multi-return spread: `Foo{call()}` where call returns a tuple whose
        // shape matches Foo's fields one-to-one (with normal compatibility,
        // including array→slice coercion). Codegen detects the same pattern
        // and routes the call's sret args into temps then into the struct.
        if len(lit.fields) == 1 && len(st.fields) > 1 {
            single_val := lit.fields[0].value
            single_type := check_expr(c, single_val, env)
            if tup, tup_ok := single_type.(^Type_Tuple); tup_ok && len(tup.elems) == len(st.fields) {
                all_ok := true
                for sf, i in st.fields {
                    if types_incompatible(sf.type_, tup.elems[i]) {
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
            // useful error if the tuple shape doesn't match the struct.
        }
        if len(lit.fields) > len(st.fields) {
            check_error(c, span, "class '%s' has %d fields, got %d positional values",
                st.name, len(st.fields), len(lit.fields))
        }
        for field, i in lit.fields {
            if i >= len(st.fields) { break }
            sf := st.fields[i]
            ft := check_expr(c, field.value, env)
            if types_incompatible(sf.type_, ft) {
                check_error(c, span, "field '%s' (position %d): expected %s, got %s",
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
            ft := check_expr(c, field.value, env)
            if types_incompatible(sf.type_, ft) {
                check_error(c, span, "field '%s': expected %s, got %s",
                    field.name, type_name(sf.type_), type_name(ft))
            }
            maybe_stamp_byte_view(c, sf.type_, field.value)
            if is_infer(ft) {
                check_literal_overflow(c, field.value, sf.type_, span)
            }
        } else {
            check_error(c, span, "class '%s' has no field '%s'", st.name, field.name)
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
        check_error(c, span, "union '%s' requires a named variant, e.g. Variant { ... }", ut.name)
    } else if lit.name not_in ut.tag_map {
        check_error(c, span, "'%s' is not a variant of union '%s'", lit.name, ut.name)
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

    // Zero-init or empty — all slots stay nil
    if lit.zero_init || len(lit.fields) == 0 { return }

    if lit.positional {
        if len(lit.fields) != fa.size {
            check_error(c, lit.span, "'%s' expects %d positional values, got %d",
                lit.name, fa.size, len(lit.fields))
            return
        }
        for field, i in lit.fields {
            val_type := check_expr(c, field.value, env)
            if types_incompatible(fa.elem, val_type) {
                check_error(c, lit.span, "'%s' element %d has type %s, expected %s",
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
            check_error(c, lit.span, "'%s' has no field '%s' (use swizzle components x/y/z/w or r/g/b/a within [0..<%d])",
                lit.name, field.name, fa.size)
            continue
        }
        idx := swizzle_char_to_index(field.name[0])
        if lit.array_values[idx] != nil {
            check_error(c, lit.span, "'%s' field '%s' set more than once", lit.name, field.name)
            continue
        }
        val_type := check_expr(c, field.value, env)
        if types_incompatible(fa.elem, val_type) {
            check_error(c, lit.span, "'%s' field '%s' has type %s, expected %s",
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
            check_error(c, span, "cannot assign %s to variable '%s' of type %s",
                type_name(val_type), name, type_name(fa))
        } else if fv.size > 0 && fv.size > fa.size {
            // Literal must not have more elements than capacity
            check_error(c, span, "array has %d elements but '%s' has capacity %d",
                fv.size, name, fa.size)
        }
    } else if !is_any(val_type) {
        check_error(c, span, "cannot assign %s to variable '%s' of type %s",
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
            check_error(c, s.span, "cannot assign %s through pointer to %s",
                type_name(val_type), type_name(p.elem))
        }
        // Check that infer literal fits in the pointed-to type
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, p.elem, s.span)
        }
    } else if !is_any(ptr_type) {
        check_error(c, s.span, "cannot dereference-assign to non-pointer type %s", type_name(ptr_type))
    }
    // Escape analysis: prevent writing local references through param pointers.
    // e.g., param^ = &local_var would let a local reference escape.
    if c.current_package != "memory" {
        if is_local_ref(c, s.value, env) {
            if ident, ok := un.operand.(^Expr_Ident); ok {
                if is_param(env, ident.name) {
                    check_error(c, s.span,
                        "cannot write local reference through parameter '%s' (would escape function scope)",
                        ident.name)
                }
            }
        }
    }
}

check_index_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    ix := s.target.(^Expr_Index)
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
        check_error(c, s.span, "array index must be a number, got %s", type_name(idx_type))
    }

    if pname, immut := write_root_immutable_param(s.target, env); immut {
        check_error(c, s.span,
            "cannot write to element of immutable parameter '%s' (declare it with ^ to allow mutation)",
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
            check_error(c, s.span, "cannot assign %s to element of [%d]%s",
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
        check_error(c, s.span, "slice lower bound must be a number, got %s", type_name(low_type))
    }
    if sl.high != nil && !is_numeric(high_type) && !is_any(high_type) {
        check_error(c, s.span, "slice upper bound must be a number, got %s", type_name(high_type))
    }

    if pname, immut := write_root_immutable_param(s.target, env); immut {
        check_error(c, s.span,
            "cannot slice-assign into immutable parameter '%s' (declare it with ^ to allow mutation)",
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
                        "byte slice write: %s is %d bytes, but slice span is %d bytes",
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
                            "byte array write: %s is %d bytes, but slice span is %d bytes",
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
                check_error(c, s.span, "cannot slice-assign [%d]%s into [%d]%s",
                    rhs.size, type_name(rhs.elem), fa.size, type_name(fa.elem))
            }
        } else if rhs_sl, rhs_sl_ok := val_type.(^Type_Slice); rhs_sl_ok {
            if types_incompatible(fa.elem, rhs_sl.elem) {
                check_error(c, s.span, "cannot slice-assign []%s into [%d]%s",
                    type_name(rhs_sl.elem), fa.size, type_name(fa.elem))
            }
        } else if !is_any(val_type) {
            check_error(c, s.span, "slice assignment requires an array or slice on the right-hand side, got %s", type_name(val_type))
        }
    }
}

check_field_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Env) {
    fa_expr := s.target.(^Expr_Field_Access)
    obj_type := check_expr(c, fa_expr.expr, env)
    val_type := check_expr(c, s.value, env)

    // Auto-deref: if obj is ^Struct, check field on the inner struct
    st: ^Scope_Body
    if sd := as_scope_body(obj_type); sd != nil && len(sd.fields) > 0 {
        st = sd
    } else if pt, ok := obj_type.(^Type_Ptr); ok {
        if sd := as_scope_body(pt.elem); sd != nil && len(sd.fields) > 0 {
            st = sd
        }
    }

    if st != nil {
        ft := resolve_struct_field(st, fa_expr.field, c.table)
        if ft != nil {
            s.target_type = ft
            if pname, immut := write_root_immutable_param(s.target, env); immut {
                check_error(c, s.span,
                    "cannot write to field '%s' of immutable parameter '%s' (declare it with ^ to allow mutation)",
                    fa_expr.field, pname)
            }
            // Mark field as initialized (clears uninit_refs for ptr/slice struct fields)
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
                                    "byte buffer read: %s is %d bytes, but slice span is %d bytes",
                                    type_name(ft), field_size, span_size)
                            }
                        }
                    }
                }
            } else if is_byte_buffer_index_read(s.value) {
                // Byte buffer reinterpret read via index: obj.field = mem[off]
                // Size comes from field type; bounds checked at runtime
            } else if types_incompatible(ft, val_type) {
                check_error(c, s.span, "cannot assign %s to field '%s' of type %s",
                    type_name(val_type), fa_expr.field, type_name(ft))
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
                                "cannot write local reference to field '%s' of parameter '%s' (would escape function scope)",
                                fa_expr.field, ident.name)
                        }
                    }
                }
            }
        } else {
            check_error(c, s.span, "class '%s' has no field '%s'", st.name, fa_expr.field)
        }
        return
    }

    // Unwrap distinct types for swizzle assignment
    if dt, dt_ok := obj_type.(^Type_Distinct); dt_ok {
        obj_type = distinct_base(dt)
    }
    // Array swizzle assignment: arr.x = val, arr.xy = [a, b]
    if fa, fa_ok := obj_type.(^Type_Fixed_Array); fa_ok {
        if is_swizzle_field(fa_expr.field, fa.size) {
            if len(fa_expr.field) == 1 {
                // Single-component write: value must match element type
                if types_incompatible(fa.elem, val_type) && !is_infer(val_type) {
                    check_error(c, s.span, "cannot assign %s to swizzle '%s' of element type %s",
                        type_name(val_type), fa_expr.field, type_name(fa.elem))
                }
                if is_infer(val_type) {
                    check_literal_overflow(c, s.value, fa.elem, s.span)
                }
            } else {
                // Multi-component write: value must be an array with matching element type
                if va, va_ok := val_type.(^Type_Fixed_Array); va_ok {
                    if types_incompatible(fa.elem, va.elem) {
                        check_error(c, s.span, "cannot assign %s to swizzle '%s': element types differ",
                            type_name(val_type), fa_expr.field)
                    }
                } else if !is_any(val_type) && !is_infer(val_type) {
                    check_error(c, s.span, "cannot assign %s to multi-component swizzle '%s': expected array",
                        type_name(val_type), fa_expr.field)
                }
            }
            return
        }
        if is_all_swizzle_chars(fa_expr.field) {
            check_error(c, s.span, "swizzle '%s' has component out of range for [%d] array", fa_expr.field, fa.size)
            return
        }
    }
}

check_match :: proc(c: ^Checker, s: ^Stmt_Match, env: ^Type_Env) {
    subj_type := check_expr(c, s.subject, env)
    ut, is_union_match := subj_type.(^Type_Union)
    et, is_enum_match := subj_type.(^Type_Enum)

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
            check_error(c, s.span, "'else' must be the last arm in a match")
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
                    check_error(c, s.span, "enum '%s' has no variant '%s'", et.name, arm.dot_shorthand)
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
                    check_error(c, s.span, "union '%s' has no variant '%s'", ut.name, arm.dot_shorthand)
                }
            } else {
                check_error(c, s.span, "dot shorthand '.%s' can only be used when matching on an enum or union", arm.dot_shorthand)
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
                    check_error(c, s.span, "'%s' is not a variant of union '%s'", arm.variant_name, ut.name)
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
                    check_error(c, s.span, "match on '%s' is missing variant '%s' (add an arm, or `else` to opt out)", et.name, name)
                }
            }
        } else if is_union_match {
            for variant in ut.variants {
                if variant not_in covered {
                    check_error(c, s.span, "match on '%s' is missing variant '%s' (add an arm, or `else` to opt out)", ut.name, variant)
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
            check_error(c, s.span, "'else' is not allowed in match on a struct — arms fire independently, so there is no single 'no match' branch")
        }
    }

    // Set up the namespace context so identifier resolution falls back to
    // subject-field lookup. Saved/restored to handle nested namespace matches.
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
            check_error(c, s.span, "match on struct '%s' expects predicate arms (`field do …` or `expr do …`)", scope.name)
            continue
        }

        pred_type := check_expr(c, predicate, env)
        if _, is_bool := pred_type.(Type_Bool); !is_bool {
            check_error(c, s.span, "predicate arm must be bool, got %s — Mara doesn't auto-truthy non-bool values; write an explicit comparison", type_name(pred_type))
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
    if len(ft.params) == 0 && ft.return_type == nil && !s.has_parens && ft.kind != .Struct {
        return {}, false
    }

    // Data funs with fields return their own layout via sret.
    // Bound calls get the struct; unbound calls discard it (dummy alloca).
    ret_type := ft.return_type
    if ret_type == nil && ft.kind == .Struct && len(ft.fields) > 0 {
        ret_type = ft
    }

    origin: Function_Origin = Origin_Source{}
    if s.is_intrinsic {
        origin = Origin_Intrinsic{llvm_name = s.intrinsic_name}
    }
    cf := Checked_Scope{
        name        = s.name,
        type_       = ft,
        return_type = distinct_base(ret_type),
        body        = s.body,
        ast         = s,
        origin      = origin,
        span        = s.span,
    }

    for p in ft.params {
        append(&cf.params, Checked_Param{name = p.name, type_ = distinct_base(p.type_)})
    }

    return cf, true
}

// ---------------------------------------------------------------------------
// Module system — modules are pre-parsed; checker looks up by name
// ---------------------------------------------------------------------------

// Find all module names whose declared package name equals `prefix` OR starts
// with `prefix.`. Returns the dotted names (e.g. for prefix "gfx", returns
// ["gfx", "gfx.vao", "gfx.prim"] if all three exist).
//
// Used by `use parent` to collect the parent module AND all parent.X
// submodules in one go. Output is sorted for reproducible load order.
find_matching_modules :: proc(c: ^Checker, prefix: string) -> [dynamic]string {
    result: [dynamic]string
    prefix_dot := strings.concatenate({prefix, "."})
    for pkg in c.programs {
        if pkg == prefix || strings.has_prefix(pkg, prefix_dot) {
            append(&result, pkg)
        }
    }
    slice.sort(result[:])
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
        check_error(c, span, "circular include: module '%s' is already being checked", module_name)
        return nil
    }

    // The parsed program for this module is in c.programs (eagerly populated
    // before check_program ran).
    mod_program_ptr, found := c.programs[module_name]
    if !found {
        check_error(c, span, "module '%s' not found", module_name)
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
        for name in ([]string{"context", "Context", "std", "void"}) {
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
    mod_struct.kind = .Struct
    mod_struct.scope = mod_env
    mod_env.owner_module = mod_struct

    // Self-registration: register the module under its bare name in its own
    // env so code inside the module can disambiguate via `<modname>.X` —
    // useful when a local type collides with an imported one (e.g.
    // time.Timer vs SDL2's Init_Flags.Timer enum-variant alias). For dotted
    // module names, the bare name is the last segment.
    bare_name := module_name
    if dot := strings.last_index(module_name, "."); dot >= 0 {
        bare_name = module_name[dot+1:]
    }
    if bare_name != "" {
        type_env_set(mod_env, bare_name, mod_struct)
    }

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
                "foreign symbol '%s' is already declared in library '%s' (first declaration at %s); each external symbol may be bound by at most one foreign block",
                ln, fo.library, span_loc(existing.span))
            break
        }
    }
    cs := Checked_Scope{
        name        = decl.name,
        type_       = ft,
        return_type = distinct_base(ft.return_type),
        ast         = nil,
        origin      = Origin_Foreign{
            library    = library,
            link_name  = ln,
            prefix     = prefix,
        },
        span        = decl.span,
    }
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
            "context.scope_allocator requires an allocator fun (e.g. Arena_Basic)")
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
            "context.scope_allocator: '%s' is not a known type", name)
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
                "context.scope_allocator: '%s' is missing required function '%s'", name, req)
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
                ret := resolve_type_expr(s.return_type, c, s.span)
                is_void := ret == nil || is_any(ret)
                is_int := false
                if _, ok := ret.(Type_Int); ok { is_int = true }
                // i64 is the same type as int — accept it spelled either way.
                if vn, ok := ret.(Type_Numeric); ok && vn.kind == .Signed && vn.bits == 64 { is_int = true }
                if !is_void && !is_int {
                    check_error(c, s.span, "fun main() must return int or have no return type")
                }
                if len(s.typed_params) != 0 {
                    check_error(c, s.span, "fun main() must take no parameters")
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
                        if ts, is_scope := ptr.elem.(^Type_Scope); is_scope && ts.name == "Context" {
                            ok = true
                        }
                    }
                }
                if !ok {
                    check_error(c, s.span, "#expose function '%s' must take `ctx: ^Context` as its first parameter", s.name)
                }
            }
        case ^Stmt_If:
            if !s.is_comptime {
                check_error(c, s.span, "executable statements must be inside fun main()")
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
            check_error(c, stmt_span(stmt), "executable statements must be inside fun main()")
        }
    }
}

// Type-check one or more main packages in a single pass. Imports reached
// from any main package are processed exactly once via c.checked_modules,
// so two main packages that both `use mara.memory` walk that AST once.
// Each main_package contributes its top-level functions under its own
// flat-name prefix; codegen filters per binary by prefix.
//
// `shared_packages` is the per-package shared-flag (true => DLL, false =>
// exe). When omitted, each package is treated as non-shared. Length must
// match main_packages.
check_program :: proc(programs: map[string]^Program, main_packages: []string,
                      compiler_dir: string = "", search_dir: string = "", web: bool = false,
                      shared_packages: []bool = nil,
                      target_os: Target_OS = .Windows) -> ^Checked_Program {
    table := new(SymbolTable)
    env := new(Type_Env)       // heap-allocated so it outlives check_program
    env.is_module_scope = true // root env is the main package's module scope; lookup terminates here
    table.root_env = env

    c := Checker{ table = table }
    checked := new(Checked_Program)
    checked.table = table
    checked.target_os = target_os
    c.checked = checked
    c.programs = programs
    c.compiler_dir = compiler_dir
    c.search_dir = search_dir
    c.target_web    = web
    // target_shared is true if ANY main package is a DLL. Used to relax the
    // "scope_allocator must live in main" rule (so DLLs can declare it in any
    // top-level fn). Per-binary linkage decisions happen at codegen time.
    any_shared := false
    for sb in shared_packages {
        if sb { any_shared = true; break }
    }
    c.target_shared = any_shared
    c.target_os     = target_os

    // Resolve every main package's parsed program up front so the rest of the
    // pass can iterate without re-doing lookups (and so missing-package errors
    // surface here in one block).
    main_programs: [dynamic]^Program
    for pkg, i in main_packages {
        prog, prog_ok := programs[pkg]
        if !prog_ok {
            check_error(&c, {}, "no parsed program for main package '%s'", pkg)
            checked.errors = c.errors
            return checked
        }
        append(&main_programs, prog)
        _ = i
    }
    if len(main_programs) == 0 {
        check_error(&c, {}, "check_program called with no main packages")
        checked.errors = c.errors
        return checked
    }

    // Program structure: mara :: fun { std :: fun { ... }, user_modules... }
    // mara_env is the root scope containing std and user modules.
    // The main package is checked inside mara_env.
    c.mara_env = env  // for now, reuse root env as mara scope
    std_fun := new(Type_Scope)
    std_fun.name = "std"
    std_fun.kind = .Struct
    std_fun.scope = new(Type_Env)
    std_fun.scope.parent = env
    c.std_fun = std_fun
    type_env_set(env, "std", std_fun)

    // Phase 0: Pre-scan main's body for context.scope_allocator setup.
    // Must happen before package checking so big-array errors in imported
    // packages know whether a scope allocator is available.
    scan_allocator :: proc(c: ^Checker, expr: Expr, value: Expr) {
        fa, fa_ok := expr.(^Expr_Field_Access)
        if !fa_ok { return }
        ident, id_ok := fa.expr.(^Expr_Ident)
        if !id_ok { return }
        if ident.name != "context" || fa.field != "scope_allocator" { return }
        c.table.has_scope_allocator = true
        if val_call, vc_ok := value.(^Expr_Call); vc_ok {
            c.table.scope_allocator_name = val_call.name
            c.table.scope_allocator_args = val_call.args
        } else if val_ident, vi_ok := value.(^Expr_Ident); vi_ok {
            c.table.scope_allocator_name = val_ident.name
        }
    }
    // Scope_allocator scan: walk every main package's `main` function plus
    // the `main`s of every module reachable transitively via `use`/`include`.
    // This is the explicit-import path: a DLL package that wants to inherit
    // its Context layout from a host says `use <host>`, and the import edge
    // pulls that host into the scan closure. Sibling files that aren't
    // imported don't influence layout — no "load whatever happens to be
    // parsed" spookiness.
    scan_visited: map[string]bool
    scan_queue: [dynamic]string
    for pkg in main_packages {
        if pkg not_in scan_visited {
            scan_visited[pkg] = true
            append(&scan_queue, pkg)
        }
    }
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
                    if a, a_ok := body_stmt.(^Stmt_Assign); a_ok && a.target != nil {
                        scan_allocator(&c, a.target, a.value)
                    }
                }
            }
        }
    }

    // #expose-presence scan: limited to packages actually being built (the
    // flag affects compile-time gates for THIS binary's body, not sibling
    // modules' decisions).
    for prog in main_programs {
        for stmt in prog^ {
            if fn_stmt, ok := stmt.(^Stmt_Scope); ok && fn_stmt.is_exposed {
                if c.target_shared {
                    c.table.context_expected_at_runtime = true
                    break
                }
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

        // Context struct
        ctx_type := new(Type_Scope)
        ctx_type.name = "Context"
        ctx_type.kind = .Struct
        field_idx := 0
        if c.table.has_scope_allocator {
            append(&ctx_type.fields, Struct_Type_Field{name = "arena", type_ = Type_Any{}})
            ctx_type.field_map["arena"] = field_idx
            ctx_type.field_map["scope_allocator"] = field_idx
            field_idx += 1
        }
        append(&ctx_type.fields, Struct_Type_Field{name = "args", type_ = args_type})
        ctx_type.field_map["args"] = field_idx
        c.table.funs["Context"] = ctx_type
        type_env_set(env, "context", ctx_type)
        // Also expose `Context` (the type) by name so users can write
        // `ctx: ^Context` in source — required to annotate the first param
        // of a `#expose` function in a DLL build.
        type_env_set(env, "Context", ctx_type)
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

    // Per-file scoping is per-package: each .mara file in a main package
    // gets its own file_env (parent = root env). Defined names register
    // into the package env (visible to all of the package's files) via
    // public_env; include-introduced names stay file-private.
    for prog, i in main_programs {
        pkg := main_packages[i]
        c.current_package = pkg

        // If this package was already processed via check_module (because an
        // earlier main_package `use`d it and triggered the full check), don't
        // walk its AST a second time — the per-file processing below would
        // re-mutate state set during the check_module path. The earlier path
        // produced an equivalent result; just leave it.
        if _, already_checked := c.checked_modules[pkg]; already_checked {
            continue
        }

        main_files_by_src: map[string][dynamic]Stmt
        main_file_order: [dynamic]string
        for stmt in prog^ {
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
            register_main_top_level_constants(&c, main_files_by_src[src], pkg)
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

        // Register a synthetic module-struct so `use this_pkg` from another
        // main_package short-circuits in check_module instead of re-walking.
        // Scope intentionally empty for now — main packages don't currently
        // expose their public symbols this way (callers reference them
        // through root env / flat-name table). The struct exists only so
        // c.checked_modules has a non-nil entry to satisfy the cache check.
        if _, already := c.checked_modules[pkg]; !already {
            mod_struct := new(Type_Scope)
            mod_struct.name = pkg
            mod_struct.kind = .Struct
            mod_struct.scope = new(Type_Env)
            mod_struct.scope.is_module_scope = true
            c.checked_modules[pkg] = mod_struct
        }
    }

    // Validate scope allocator API after all types are resolved (once,
    // across all main packages — the allocator type is global to the build).
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

    // Extract functions, foreign declarations, and globals from each main
    // package's program. Each contributes to checked.functions under its own
    // flat-name prefix; codegen filters per binary at emit time.
    for prog, i in main_programs {
        c.current_package = main_packages[i]
        extract_main_program_stmts(&c, checked, prog^, env, main_packages[i])
    }

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
            name        = flat_key,
            type_       = ft,
            return_type = distinct_base(ft.return_type),
            body        = body,
            span        = tmpl_ast.span,
        }
        for p in ft.params {
            append(&cf.params, Checked_Param{name = p.name, type_ = distinct_base(p.type_)})
        }
        checked.functions[flat_key] = cf
    }

    // Phase 3: Validate each main package's program structure. Exe packages
    // (non-shared) must define fun main(); DLL packages can rely on #expose
    // and don't require main.
    for prog, i in main_programs {
        pkg_is_shared := false
        if i < len(shared_packages) { pkg_is_shared = shared_packages[i] }

        found_main := false
        validate_top_level_stmts(&c, prog^, &found_main)
        if !found_main && !pkg_is_shared {
            check_error(&c, {}, "package '%s' must define fun main()", main_packages[i])
        }
    }

    checked.errors = c.errors
    return checked
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
    case ^Expr_Uninit:             return &v.type_
    case ^Expr_Unary:              return &v.type_
    case ^Expr_Binary:             return &v.type_
    case ^Expr_Call:               return &v.type_
    case ^Expr_Array:              return &v.type_
    case ^Expr_Index:              return &v.type_
    case ^Expr_Slice:              return &v.type_
    case ^Expr_Struct_Literal:     return &v.type_
    case ^Expr_Field_Access:       return &v.type_
    case ^Expr_Size_Of:            return &v.type_
    case ^Expr_Take:                return &v.type_
    case ^Expr_If:                 return &v.type_
    case ^Expr_Compiler_Intrinsic: return &v.type_
    case ^Expr_Include:            return &v.type_
    case ^Expr_Type_Name:          return &v.type_
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
        // String literals are full arrays of utf8 bytes (including null terminator)
        byte_len := len(e.value)  // UTF-8 byte count (already decoded by lexer)
        fa := new(Type_Fixed_Array)
        fa.size = byte_len + 1    // +1 for null terminator
        fa.elem = Type_Utf8{}
        return fa
    case ^Expr_Char:
        return Type_C8{}
    case ^Expr_Bool:
        return Type_Bool{}
    case ^Expr_Uninit:
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
            check_error(c, e.span, "no visible enum or union has variant '.%s'", e.name)
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
                    "constant '%s' is ambiguous (defined in: %s). Use qualified access, e.g. %s.%s",
                    e.name, joined, owners[0], e.name)
                return Type_Error{}
            }
        }

        // Check for reading an uninitialized pointer/slice
        if is_uninit_ref(env, e.name) {
            check_error(c, e.span, "variable '%s' is used before being assigned a value", e.name)
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
                        "'%s' is a field of '%s'; access it through the receiver (e.g. 'a.%s')",
                        e.name, loc_env.class_scope.name, e.name)
                    return Type_Error{}
                }
            }
            // Set variant resolution metadata if this is an enum variant
            if owner_enum, mapped := c.table.variant_to_enum[e.name]; mapped {
                if et, et_ok := c.table.enums[owner_enum]; et_ok {
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
            check_error(c, e.span, "'%s' is a type, not a value. Did you mean ': %s'?", e.name, e.name)
        } else if ident_flat in c.table.enums {
            check_error(c, e.span, "'%s' is a type, not a value. Did you mean ': %s'?", e.name, e.name)
        } else if ident_flat in c.table.unions {
            check_error(c, e.span, "'%s' is a type, not a value. Did you mean ': %s'?", e.name, e.name)
        } else {
            check_error(c, e.span, "undefined identifier '%s'", e.name)
        }
        return Type_Error{}
    case ^Expr_Unary:
        operand_type := check_expr(c, e.operand, env)
        #partial switch e.op {
        case .Minus:
            if !is_numeric(operand_type) {
                check_error(c, e.span, "cannot negate %s", type_name(operand_type))
            }
            return operand_type
        case .Not:
            if _, ok := operand_type.(Type_Bool); !ok && !is_any(operand_type) {
                check_error(c, e.span, "cannot apply 'not' to %s", type_name(operand_type))
            }
            return Type_Bool{}
        case .Tilde:
            if !is_integer(operand_type) && !is_any(operand_type) {
                check_error(c, e.span, "cannot apply '~' to %s, requires integer type", type_name(operand_type))
            }
            return operand_type
        case .Ampersand:
            // Address-of: &x produces ^T. Reject if the address would land in
            // immutable-param storage — letting `&t` escape would silently
            // grant the mutation that declaring `t` without `^` denied.
            if pname, immut := write_root_immutable_param(e.operand, env); immut {
                check_error(c, e.span,
                    "cannot take address of immutable parameter '%s' (declare it with ^ to allow mutation)",
                    pname)
            }
            pt := new(Type_Ptr)
            pt.elem = operand_type
            return pt
        case .Caret:
            // Dereference: p^ — operand must be a pointer
            if p, ok := operand_type.(^Type_Ptr); ok {
                return p.elem
            }
            // Allow deref on Type_Any (backwards compat with raw ptr)
            if is_any(operand_type) {
                return Type_Error{}
            }
            check_error(c, e.span, "cannot dereference non-pointer type %s", type_name(operand_type))
            return Type_Error{}
        }
    case ^Expr_Binary:
        return check_binary(c, e, env)
    case ^Expr_Call:
        return check_call(c, e, env)
    case ^Expr_Array:
        return check_array_literal(c, e, env)
    case ^Expr_Index:
        return check_index(c, e, env)
    case ^Expr_Slice:
        return check_slice(c, e, env)
    case ^Expr_Struct_Literal:
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
            check_error(c, e.span, "typed array literal: type %s is not a fixed-size array", type_name(resolved))
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
            check_error(c, e.span, "size_of: unknown type")
        }
        e.resolved_type = resolved
        return Type_Infer_Int{}
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
                            num.int_value = i64(cv.value)
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
        resolved := resolve_type_expr(e.type_expr, c, e.span, env=env)
        if _, is_err := resolved.(Type_Error); is_err {
            check_error(c, e.span, "take: unknown type")
        }
        // Runtime-counted form: validate count is integer, resolved is a slice.
        if e.count_expr != nil {
            count_type := check_expr(c, e.count_expr, env)
            if !is_any(count_type) && !is_numeric(count_type) {
                check_error(c, e.span,
                    "take count must be an integer, got %s", type_name(count_type))
            }
            if _, is_slice := distinct_base(resolved).(^Type_Slice); !is_slice {
                check_error(c, e.span,
                    "take with a count requires a slice type, got %s", type_name(resolved))
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
                "take requires ^[]byte (cursor form, pass &slice_var) or ^byte (positional form), got %s",
                type_name(src_type))
        }
        // Lifetime: storage must not point into our own frame (or deeper) —
        // a slice carved from it would dangle after this function returns.
        src_prov := expr_provenance(c, e.storage, env)
        if src_prov.depth >= env.scope_depth {
            check_error(c, e.span,
                "take storage points into local stack memory, which would not outlive a returning view")
        }
        e.type_ = resolved
        return resolved
    case ^Expr_If:
        cond_type := check_expr(c, e.condition, env)
        if !is_any(cond_type) {
            if _, is_bool := cond_type.(Type_Bool); !is_bool {
                check_error(c, e.span, "if-expression condition must be bool, got %s", type_name(cond_type))
            }
        }
        then_type := check_expr(c, e.then_expr, env)
        else_type := check_expr(c, e.else_expr, env)
        // Unify: if either is untyped/infer, adopt the other
        if is_untyped(then_type) || is_infer(then_type) { return else_type }
        if is_untyped(else_type) || is_infer(else_type) { return then_type }
        if types_incompatible(then_type, else_type) {
            check_error(c, e.span, "if-expression branches have incompatible types: %s vs %s",
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
            check_error(c, e.span, "type 'int' is reserved — use 'i64' (or 'isize' for word-sized)")
            return Type_Error{}
        }
        return Type_Error{}
    }
    return Type_Error{}
}

// Shared struct field access logic — used for both direct and auto-deref (^Struct) paths.
// Handles uninit checks, field resolution, and associated function lookup.
check_struct_field_access :: proc(c: ^Checker, e: ^Expr_Field_Access, st: ^Scope_Body, env: ^Type_Env) -> Type {
    // Check for reading an uninitialized pointer/slice field
    if ident, ident_ok := e.expr.(^Expr_Ident); ident_ok {
        field_key := strings.concatenate({ident.name, ".", e.field})
        if is_uninit_ref(env, field_key) {
            check_error(c, e.span, "field '%s' of '%s' is used before being assigned a value", e.field, ident.name)
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
    check_error(c, e.span, "class '%s' has no field '%s'", st.name, e.field)
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
        check_error(c, e.span, "enum '%s' has no variant '%s'", et.name, e.field)
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
            check_error(c, e.span, "union '%s' has no tag enum (internal error)", ut.name)
            return Type_Error{}
        }
        if e.field == "pad" {
            if ut.tag_pad == nil {
                check_error(c, e.span, "union '%s' has no padding (declare with `union(... pad T ...)`)", ut.name)
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
        check_error(c, e.span, "union '%s' has no variant '%s'", ut.name, e.field)
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
                check_error(c, e.span, "module '%s' has no symbol '%s'", sd.name, e.field)
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
            return Type_Int{}
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
            check_error(c, e.span, "swizzle '%s' has component out of range for [%d] array", e.field, fa.size)
            return Type_Error{}
        }
        check_error(c, e.span, "cannot access field '%s' on array type %s", e.field, type_name(obj_type))
        return Type_Error{}
    }
    // Slice field access: sl.ptr, sl.len, sl.cap
    if sl, ok := obj_type.(^Type_Slice); ok {
        if e.field == "ptr" {
            pt := new(Type_Ptr)
            pt.elem = sl.elem
            return pt
        }
        if e.field == "len" || e.field == "cap" {
            return Type_Int{}
        }
        check_error(c, e.span, "slice type %s has no field '%s'", type_name(obj_type), e.field)
        return Type_Error{}
    }
    // Partial array field access: pa.ptr, pa.len, pa.cap — shape matches slice.
    if pa, ok := obj_type.(^Type_Partial_Array); ok {
        if e.field == "ptr" {
            pt := new(Type_Ptr)
            pt.elem = pa.elem
            return pt
        }
        if e.field == "len" || e.field == "cap" {
            return Type_Int{}
        }
        check_error(c, e.span, "partial array type %s has no field '%s'", type_name(obj_type), e.field)
        return Type_Error{}
    }
    if !is_any(obj_type) {
        check_error(c, e.span, "cannot access field '%s' on type %s", e.field, type_name(obj_type))
    }
    return Type_Error{}
}

// Check a call against all built-in functions. Returns (result_type, true) if the
// name matched a builtin, or (_, false) if it should be resolved as a user function.
check_builtin_call :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Env) -> (Type, bool) {
    check_args_n :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Env, n: int) {
        if len(args) != n {
            check_error(c, e.span, "%s() expects %d argument%s, got %d",
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
            check_error(c, e.span, "len() expects 1 argument, got %d", len(args))
        } else {
            arg_type := check_expr(c, args[0], env)
            if !is_array_type(arg_type) && !is_any(arg_type) {
                check_error(c, e.span, "len() requires array or slice, got %s", type_name(arg_type))
            }
        }
        return Type_Int{}, true
    case "cap":
        if len(args) != 1 {
            check_error(c, e.span, "cap() expects 1 argument, got %d", len(args))
        } else {
            arg_type := check_expr(c, args[0], env)
            if !is_array_type(arg_type) && !is_any(arg_type) {
                check_error(c, e.span, "cap() requires array or slice, got %s", type_name(arg_type))
            }
        }
        return Type_Int{}, true
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
                        "print format string has %d `%%` placeholder(s) but %d value(s) were passed",
                        pct_count, len(args) - 1)
                }
            }
        }
        return Type_Error{}, true
    case "crash":
        if len(args) > 1 {
            check_error(c, e.span, "crash() expects 0 or 1 arguments, got %d", len(args))
        } else if len(args) == 1 {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_cstr":
        if len(args) != 1 {
            check_error(c, e.span, "print_cstr() expects 1 argument (^byte), got %d", len(args))
        } else {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_int":
        if len(args) != 1 {
            check_error(c, e.span, "print_int() expects 1 argument (int), got %d", len(args))
        } else {
            check_expr(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_float":
        if len(args) != 1 {
            check_error(c, e.span, "print_float() expects 1 argument (float), got %d", len(args))
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
            check_error(c, e.span, "slice_from_ptr() expects 2 arguments (ptr, size), got %d", len(args))
        } else {
            ptr_type := check_expr(c, args[0], env)
            _, ptr_ok := ptr_type.(^Type_Ptr)
            if !ptr_ok && !is_any(ptr_type) {
                check_error(c, e.span, "slice_from_ptr() first argument must be a pointer, got %s", type_name(ptr_type))
            }
            size_type := check_expr(c, args[1], env)
            if !is_numeric(size_type) && !is_any(size_type) {
                check_error(c, e.span, "slice_from_ptr() second argument must be numeric, got %s", type_name(size_type))
            }
            if !is_package(c, "os") {
                if _, comptime_ok := evaluate_comptime_int(c, args[1]); !comptime_ok {
                    check_error(c, e.span,
                        "slice_from_ptr() outside the os module requires a comptime-known size " +
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
             "i8", "i16", "i32", "i64",
             "u8", "u16", "u32", "u64",
             "usize", "isize",
             "f32", "f64", "c8", "utf8", "bool":
            return true   // int / uint kept here so the cast site emits the
                          // same "reserved" error as a type position would,
                          // instead of a generic "unknown function".
        }
        return false
    }
    if is_type_cast(e.name) {
        if len(args) != 1 {
            check_error(c, e.span, "%s() expects 1 argument, got %d", e.name, len(args))
            return Type_Error{}, true
        }
        check_expr(c, args[0], env)
        switch e.name {
        case "int":
            check_error(c, e.span, "type 'int' is reserved — use 'i64' (or 'isize' for word-sized)")
            return Type_Error{}, true
        case "i64": return Type_Numeric{kind = .Signed, bits = 64}, true
        case "uint":
            check_error(c, e.span, "type 'uint' is reserved — use 'u64' (or 'usize' for word-sized)")
            return Type_Error{}, true
        case "i8":  return Type_Numeric{kind = .Signed, bits = 8}, true
        case "i16": return Type_Numeric{kind = .Signed, bits = 16}, true
        case "i32": return Type_Numeric{kind = .Signed, bits = 32}, true
        case "u8":  return Type_Numeric{kind = .Unsigned, bits = 8}, true
        case "u16": return Type_Numeric{kind = .Unsigned, bits = 16}, true
        case "u32": return Type_Numeric{kind = .Unsigned, bits = 32}, true
        case "u64": return Type_Numeric{kind = .Unsigned, bits = 64}, true
        case "usize": return Type_Numeric{kind = .Unsigned, bits = 0}, true
        case "isize": return Type_Numeric{kind = .Signed,   bits = 0}, true
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
                                    best_ret = ft.return_type
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
                                    best_ret = fun_type.return_type
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
            check_error(c, e.span, "left operand of '%s' must be bool, got %s",
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
                        "did you mean `%s`? Each operand of `%s` needs its own comparison.",
                        strings.to_string(b), op_word)
                }
            }
        }
        if _, ok := right_type.(Type_Bool); !ok && !is_any(right_type) {
            check_error(c, e.span, "right operand of '%s' must be bool, got %s",
                op_word, type_name(right_type))
        }
        return Type_Bool{}

    case .Equal_Equal, .Not_Equal:
        // Reject comparisons involving composite types (structs, unions, arrays, tuples)
        if !is_any(left_type) && !is_any(right_type) {
            left_composite := is_composite(left_type)
            right_composite := is_composite(right_type)
            if left_composite || right_composite {
                check_error(c, e.span, "cannot compare %s with %s using '%s'",
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
            check_error(c, e.span, "left operand of comparison must be numeric, got %s", type_name(left_type))
        }
        if !is_numeric(right_type) {
            check_error(c, e.span, "right operand of comparison must be numeric, got %s", type_name(right_type))
        }
        // Require matching types (infer literals adopt the concrete side)
        if is_numeric(left_type) && is_numeric(right_type) {
            promote_numeric(c, left_type, right_type, e.span)
        }
        return Type_Bool{}

    case .Plus:
        // Numeric addition
        if !is_numeric(left_type) || !is_numeric(right_type) {
            check_error(c, e.span, "mismatched types for '+': %s and %s - did you forget to import the package that defines the overload?",
                type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
        return promote_numeric(c, left_type, right_type, e.span)

    case .Minus, .Star, .Slash, .Modulo:
        if !is_numeric(left_type) || !is_numeric(right_type) {
            op_sym := e.op == .Minus ? "-" : e.op == .Star ? "*" : e.op == .Slash ? "/" : "%%"
            check_error(c, e.span, "mismatched types for '%s': %s and %s - did you forget to import the package that defines the overload?",
                op_sym, type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
        return promote_numeric(c, left_type, right_type, e.span)

    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(left_type) && !is_any(left_type) {
            check_error(c, e.span, "bitwise operators require integer operands, got %s", type_name(left_type))
            return Type_Error{}
        }
        if !is_integer(right_type) && !is_any(right_type) {
            check_error(c, e.span, "bitwise operators require integer operands, got %s", type_name(right_type))
            return Type_Error{}
        }
        return promote_numeric(c, left_type, right_type, e.span)
    }
    return Type_Error{}
}

// Promote numeric types for binary operations.
// Infer types yield to concrete types; if both infer, stay inferred.
// Both concrete operands must have matching types (no implicit widening/narrowing).
promote_numeric :: proc(c: ^Checker, a: Type, b: Type, span: Span) -> Type {
    a_infer := is_infer(a)
    b_infer := is_infer(b)

    // Both infer: float wins over int
    if a_infer && b_infer {
        if _, ok := a.(Type_Infer_Float); ok { return Type_Infer_Float{} }
        if _, ok := b.(Type_Infer_Float); ok { return Type_Infer_Float{} }
        return Type_Infer_Int{}
    }

    // One side infer, one side concrete: adopt the concrete type
    if a_infer { return b }
    if b_infer { return a }

    // Either side is untyped: suppress error
    if is_any(a) || is_any(b) { return Type_Error{} }

    // Both concrete: require exact match
    if types_equal(a, b) { return a }

    check_error(c, span, "mismatched types in arithmetic: %s and %s (use an explicit cast)",
        type_name(a), type_name(b))
    return Type_Error{}
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
            check_error(c, e.span, "argument %d of '%s': '_' requires a default value, but parameter '%s' has none",
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

// is_vla_shape reports whether a type carries any runtime-sized aggregate
// component — a VLA fixed-array directly, a struct (or pointer to one) whose
// instantiation has any VLA field, or a pointer chain to either. Used to gate
// VLA values against parameters that didn't opt in via `var`.
//
// Slices (`[]T`) are intentionally NOT counted: their runtime length is
// part of how slices work everywhere, and forcing every slice-taking
// function to mark its param `var` would be pure noise.
is_vla_shape :: proc(t: Type) -> bool {
    if fa, ok := t.(^Type_Fixed_Array); ok && fa.is_vla { return true }
    if pt, ok := t.(^Type_Ptr); ok { return is_vla_shape(pt.elem) }
    if sd := as_scope_body(t); sd != nil { return sd.has_vla_field }
    return false
}

// Shared helper: check that args match a function's parameter types.
check_call_args :: proc(c: ^Checker, args: []Expr, fun_type: ^Type_Scope, display_name: string, span: Span, env: ^Type_Env) {
    required := count_required_params(fun_type)
    if len(args) < required || len(args) > len(fun_type.params) {
        check_error(c, span, "'%s' expects %d args, got %d", display_name, len(fun_type.params), len(args))
    } else {
        for arg, i in args {
            // Hand the parameter type down so bare variant idents like
            // `Init(Video)` can resolve `Video` against `Init_Flags`.
            c.expected_hint = fun_type.params[i].type_
            arg_type := check_expr(c, arg, env)
            if types_incompatible(fun_type.params[i].type_, arg_type) {
                check_error(c, span, "argument %d of '%s': expected %s, got %s",
                    i + 1, display_name, type_name(fun_type.params[i].type_), type_name(arg_type))
            }
            maybe_stamp_byte_view(c, fun_type.params[i].type_, arg)
            // Check that infer literal args fit in the parameter type
            if is_infer(arg_type) {
                check_literal_overflow(c, arg, fun_type.params[i].type_, span)
            }
            // VLA-vs-var: refuse runtime-sized aggregate instantiations unless
            // the parameter binding is marked `var`. The param signature is
            // the public contract; a caller passing a VLA Array/Struct should
            // see the rule at the call site rather than discover it later via
            // a runtime bug.
            if is_vla_shape(arg_type) && !fun_type.params[i].is_var {
                check_error(c, span,
                    "argument %d of '%s': value has VLA-shaped type %s; mark the parameter `var` to accept runtime-sized instantiations",
                    i + 1, display_name, type_name(arg_type))
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
                                    "method '%s' requires a pointer receiver — take an address with `&` (or use a `^%s` local) before calling",
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
                    check_error(c, e.span, "module '%s' has no function '%s'", qual_sd.name, e.name)
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
                            "method '%s' requires a pointer receiver — take an address with `&` (or use a `^%s` local) before calling",
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
        // Leave fn_type nil — UFCS keeps e.name bare, so the env lookup in
        // check_call will resolve it through the includes chain.
        ufcs_flat := make_flat_name(resolve_fn_home(c, env,e.name), e.name)
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
check_dispatch_call :: proc(c: ^Checker, e: ^Expr_Call, fn_names: [dynamic]string, check_args: []Expr, env: ^Type_Env) -> Type {
    arg_types: [dynamic]Type
    defer delete(arg_types)
    for arg in check_args {
        append(&arg_types, check_expr(c, arg, env))
    }
    for fn_name in fn_names {
        ft_raw, ft_found := type_env_get(env, fn_name)
        if !ft_found { continue }
        ft, ft_ok := ft_raw.(^Type_Scope)
        if !ft_ok { continue }
        if len(ft.params) != len(arg_types) { continue }

        all_match := true
        for i := 0; i < len(ft.params); i += 1 {
            if types_incompatible(ft.params[i].type_, arg_types[i]) {
                all_match = false
                break
            }
        }
        if all_match {
            disp_flat := make_flat_name(resolve_fn_home(c, env,fn_name), fn_name)
            e.name = fn_name  // rewrite call target for codegen
            e.resolved_func = Resolved_Func{name = disp_flat}
            return ft.return_type
        }
    }
    type_strs: [dynamic]string
    defer delete(type_strs)
    for at in arg_types {
        append(&type_strs, type_name(at))
    }
    check_error(c, e.span, "no matching function in dispatch group '%s' for argument types (%s)",
        e.name, strings.join(type_strs[:], ", "))
    return Type_Error{}
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
            check_error(c, e.span, "undefined function '%s'", e.name)
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
                check_error(c, e.span, "%s() expects 1 argument, got %d", e.name, len(check_args))
                return Type_Error{}
            }
            saved_hint := c.expected_hint
            c.expected_hint = dt.base_type
            arg_type := check_expr(c, check_args[0], env)
            c.expected_hint = saved_hint
            if !is_any(arg_type) && !is_infer(arg_type) {
                if types_incompatible(dt.base_type, arg_type) {
                    check_error(c, e.span,
                        "cannot construct %s from %s; underlying type is %s",
                        e.name, type_name(arg_type), type_name(dt.base_type))
                }
            }
            e.type_ = dt
            e.resolved_func = Resolved_Func{name = dt.name}
            return dt
        }

        fun_type, fun_ok = fun_type_raw.(^Type_Scope)
        if !fun_ok {
            check_error(c, e.span, "'%s' is not a function", e.name)
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
                check_error(c, e.span, "function '%s' is ambiguous (defined in: %s). Use a qualified call (e.g. `%s.%s(...)`) or seal one of the includes.", e.name, owner_list, ambiguous_owners[0], e.name)
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
    if fun_type.kind == .Struct && len(fun_type.params) == 0 && len(fun_type.fields) > 0 && fun_type.return_type == nil {
        e.type_ = fun_type
        // Annotate with mangled name for codegen — old Type_Struct branch did this.
        if e.resolved_func == nil && fun_type.name != "" {
            e.resolved_func = Resolved_Func{name = fun_type.name}
        }

        // `Foo()` (no args) is always valid — equivalent to bare declaration `x : Foo`.
        // Init function applies defaults and zero-inits fields without defaults.
        if len(check_args) == 0 {
            if e.overrides != nil {
                check_struct_literal_fields(c, e.overrides, &fun_type.sd, e.span, env)
            }
            return fun_type
        }

        num_required := 0
        for f in fun_type.fields {
            if f.default_value == nil { num_required += 1 }
        }
        if len(check_args) > len(fun_type.fields) {
            check_error(c, e.span, "'%s' has %d field(s), got %d argument(s)", fun_type.name, len(fun_type.fields), len(check_args))
        } else if len(check_args) < num_required {
            check_error(c, e.span, "'%s' requires at least %d argument(s), got %d", fun_type.name, num_required, len(check_args))
        }
        for arg, i in check_args {
            if i < len(fun_type.fields) {
                c.expected_hint = fun_type.fields[i].type_
            }
            arg_type := check_expr(c, arg, env)
            if i < len(fun_type.fields) {
                field := fun_type.fields[i]
                if types_incompatible(field.type_, arg_type) && !is_any(arg_type) {
                    check_error(c, e.span, "field '%s': expected %s, got %s",
                        field.name, type_name(field.type_), type_name(arg_type))
                }
            }
        }
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &fun_type.sd, e.span, env)
        }
        return fun_type
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

    // Constructor with params: returns the struct type itself
    if fun_type.return_type == nil && fun_type.kind == .Struct && len(fun_type.params) > 0 {
        e.type_ = fun_type
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &fun_type.sd, e.span, env)
        }
        return fun_type
    }

    if e.overrides != nil {
        check_error(c, e.span, "'%s' field-override block is only valid on struct construction", e.name)
    }
    return fun_type.return_type
}

// Constructor call: data fun called with positional args.
// Parameterless: Point(1, 2) — args mapped to fields.
// Array class: Vec3(0, 1, 0) — args mapped to array elements.
// With params: Arena(4096) — args mapped to constructor params, fields initialized by body.
check_constructor_call :: proc(c: ^Checker, e: ^Expr_Call, st: ^Type_Scope, args: []Expr, env: ^Type_Env) -> Type {
    e.type_ = st

    // Constructor with params: args map to params, not fields
    if len(st.params) > 0 {
        check_call_args(c, args, st, st.name, e.span, env)
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env)
        }
        return st
    }

    // Parameterless constructor: args map to fields positionally.
    // `Foo()` (no args) is always valid — equivalent to bare declaration `x : Foo`.
    // The init function handles defaults and zero-inits fields without defaults.
    if len(args) == 0 {
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env)
        }
        return st
    }

    num_required := 0
    for f in st.fields {
        if f.default_value == nil { num_required += 1 }
    }

    if len(args) > len(st.fields) {
        check_error(c, e.span, "'%s' has %d field(s), got %d argument(s)", st.name, len(st.fields), len(args))
    } else if len(args) < num_required {
        check_error(c, e.span, "'%s' requires at least %d argument(s), got %d", st.name, num_required, len(args))
    }

    // Type-check each positional arg against the corresponding field
    for arg, i in args {
        if i < len(st.fields) {
            c.expected_hint = st.fields[i].type_
        }
        arg_type := check_expr(c, arg, env)
        if i < len(st.fields) {
            field := st.fields[i]
            if types_incompatible(field.type_, arg_type) && !is_any(arg_type) {
                check_error(c, e.span, "field '%s': expected %s, got %s",
                    field.name, type_name(field.type_), type_name(arg_type))
            }
        }
    }

    if e.overrides != nil {
        check_struct_literal_fields(c, e.overrides, st, e.span, env)
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
            check_error(c, e.span, "array element %d has type %s, expected %s",
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
        check_error(c, e.span, "index must be a number, got %s", type_name(idx_type))
    }

    // Array indexing returns element type
    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        return fa.elem
    }

    // Slice indexing returns element type
    if sl, ok := target_type.(^Type_Slice); ok {
        // Byte slice index: returns Type_Byte; actual reinterpret type comes from annotation
        return sl.elem
    }

    // Partial array indexing — same as slice; the header has matching first
    // 24 bytes so codegen can reuse the slice indexing path.
    if pa, ok := target_type.(^Type_Partial_Array); ok {
        return pa.elem
    }

    if !is_any(target_type) {
        check_error(c, e.span, "cannot index into %s", type_name(target_type))
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
        check_error(c, e.span, "cannot slice %s", type_name(target_type))
        return Type_Error{}
    }

    // Check that low/high are numeric
    if e.low != nil {
        lt := check_expr(c, e.low, env)
        if !is_numeric(lt) && !is_any(lt) {
            check_error(c, e.span, "slice low bound must be numeric, got %s", type_name(lt))
        }
    }
    if e.high != nil {
        ht := check_expr(c, e.high, env)
        if !is_numeric(ht) && !is_any(ht) {
            check_error(c, e.span, "slice high bound must be numeric, got %s", type_name(ht))
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

