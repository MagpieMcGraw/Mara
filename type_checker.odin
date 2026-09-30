package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:reflect"
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
    Type_Utf8,        // UTF-8 byte: string element type AND the type of a character literal ('A')
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
    index_type:   Type,       // index type for [N IT]T (nil = plain integer index)
}

Type_Slice :: struct {
    elem:         Type,
}

// [..N]T — partial array. IR layout: {ptr, len, cap, elements: [N x T]}, with
// ptr initialised to &elements at decl time. First 24 bytes match Type_Slice's
// {ptr, len, cap} shape so partial arrays can flow through `^[]T` (umbrella)
// without monomorphization. Pinned in practice: moving the value breaks ptr.
Type_Partial_Array :: struct {
    size:         int,
    elem:         Type,
}

Struct_Type_Field :: struct {
    name:          string,
    type_:         Type,
    default_value: Expr, // nil if no default
    is_using:      bool,
}

// Demand-driven resolution state for a scope's signature (a struct's fields, a
// fun's params/returns). Unresolved → In_Progress → Resolved. The In_Progress
// state is the cycle guard: re-entering a scope that's mid-resolution (a type
// that refers to itself through a value field) is detected here rather than
// recursing forever. This is the substrate for replacing the fixed signature
// pre-passes (the old "1a.5"/"2a"/check_bodies hoists) with on-demand resolution.
Resolution_State :: enum {
    Unresolved,
    In_Progress,
    Resolved,
}

// The body of a Type_Scope — embedded via `using sd: Scope_Body`.
// Holds the fields, nested defs, methods, and other content shared
// between data-layout scopes (struct/class) and callable scopes (fun).
Scope_Body :: struct {
    name:           string,  // C-ified flat name (e.g. "game_Point", "sdl_Init"), "" for anonymous
    source_name:    string,  // user-written bare name (e.g. "Point", "Init") for diagnostics; mirrors Type_Enum.source_name. "" falls back to name.

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

    // Union-variant marker. A union's variant struct carries the tag (+pad) as
    // its first field(s) — `__tag` at index 0, `__pad` next when the union has
    // padding — so the variant IS the union value and rides struct codegen.
    // codegen writes `union_variant_tag` into field 0 at construction time
    // (the tag isn't a user-set field). False/0 for ordinary structs.
    is_union_variant:  bool,
    union_variant_tag: i64,

    backing_bytes:  int,     // size of hidden trailing buffer for sized-slice fields' backing
                             // storage. Computed by codegen at register-struct time so the
                             // backing rides along with the struct on sret/memcpy — slice
                             // headers point at &struct.backing[offset] using the struct's
                             // own address (correct under RVO; stale after a downstream copy).

    // Back-reference to the declaring AST node (the `fun`/`struct`/`class`
    // statement). Set at registration alongside the fun_asts entry. nil for
    // types with no single source statement (foreign decls, the synthetic
    // Program global, etc.). Lets a resolved call reach the callee's body by
    // pointer instead of re-keying fun_asts by name.
    ast:            ^Stmt_Scope,

    // Signature (field) resolution state — memoizes check_scope_body's
    // signature pass so it runs exactly once per scope regardless of how many
    // call sites demand it, and breaks cycles. Zero value Unresolved.
    sig_state:      Resolution_State,

    // The (persistent) env this scope was declared in — the env its field
    // TYPES resolve against. Captured at registration for top-level structs,
    // whose file/module env outlives the check, so a use site in another file
    // can demand this struct's signature on the spot (ensure_struct_signature).
    // nil for nested scopes (their decl env is transient) — those resolve
    // through their parent (parent_scope) instead.
    decl_env:       ^Type_Scope,

    // Enclosing scope for a nested struct (`Inner` inside `Box`). A nested
    // struct's decl_env is transient, so on-demand resolution walks up to a
    // parent that has a decl_env and resolves THAT — its signature pass recurses
    // back down into this one. nil for top-level scopes.
    parent_scope:   ^Type_Scope,

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

    // Bare-`include`d modules' durable scopes, visible from this scope (a file
    // scope holds that file's private includes; a module scope holds re-exports).
    // Name resolution walks parent_scope and checks each scope's includes —
    // non-transitive (we don't follow inc.includes).
    includes:       [dynamic]^Scope_Body,

    // Module dispatch groups (stored on module-struct for propagation on `using include`)
    dispatch_groups:    map[string][dynamic]string,
    operator_overloads: map[Token_Kind][dynamic]string,

    // Generic monomorphization metadata
    generic_base:   string,        // "Array" if monomorphized from a template, "" otherwise
    generic_args:   [dynamic]Type, // e.g. [i64] for an Array(i64) instance — for reverse inference

    // --- Codegen unit (formerly the separate Checked_Scope bundle) -----------
    // A Type_Scope IS what codegen emits: the typed signature/layout PLUS its
    // body. checked.functions points straight at the ^Type_Scope — no wrapper
    // carrying a parallel copy of the AST. Populated at extract time (check
    // phase, stable allocator) so codegen reads them directly.
    body:                 [dynamic]Stmt,    // the scope's runtime statements (a struct's are its field decls)
    origin:               Function_Origin,  // Source / Intrinsic / Foreign — codegen dispatch
    body_span:            Span,             // span of the declaring statement (diagnostics)
    is_exposed:           bool,             // `#expose` → dllexport linkage + unmangled symbol
    return_binding_names: [dynamic]string,  // named-return locals (`fun() -> (fwd, up: Vec3)`)
    // Codegen-facing signature caches (see populate_cg_signature). cg_returns
    // prepends a struct ctor's Self (sret slot 0); both pre-unwrap distinct.
    // Built at CHECK time so they stay stable when aliased into the cached
    // Fun_Info. Replace the deleted Checked_Scope.return_types / .params.
    cg_returns:           [dynamic]Type,
    cg_params:            [dynamic]Struct_Type_Field,
}

// Build the codegen-facing signature caches (cg_returns + cg_params) into ft.
// Both pre-unwrap distinct wrappers; cg_returns Self-prepends a struct ctor's
// sret slot 0. Runs at CHECK time so the slices stay stable when codegen aliases
// them into the cached Fun_Info — computing them during codegen under a transient
// arena dangles. These are the exact transforms the deleted Checked_Scope caches
// used, relocated onto the Type_Scope.
populate_cg_signature :: proc(ft: ^Type_Scope) {
    clear(&ft.cg_returns)
    if len(ft.return_types) == 0 && ft.kind == .Struct {
        append(&ft.cg_returns, distinct_base(Type(ft)))
    } else if len(ft.return_types) > 0 && ft.kind == .Struct {
        append(&ft.cg_returns, distinct_base(Type(ft)))
        for rt in ft.return_types {
            append(&ft.cg_returns, distinct_base(rt))
        }
    } else {
        for rt in ft.return_types {
            append(&ft.cg_returns, distinct_base(rt))
        }
    }
    clear(&ft.cg_params)
    for p in ft.params {
        pp := p
        pp.type_ = distinct_base(p.type_)
        append(&ft.cg_params, pp)
    }
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
//
// ARCHITECTURE — the DURABLE half of the checker's analysis split (see Type_Env
// for the transient half). Type_Scope is the typed-AST node: one per
// declaration, it persists past checking and is what codegen consumes. Every
// fact that is FIXED-at-declaration or MONOTONE-ACCUMULATING over a body belongs
// here — the signature, body, members/layout, the per-declaration analysis facts
// (is_param, `read`, ...), and the per-function interprocedural summaries
// (purity, arg-sets). The symbol table and per-decl facts that Type_Env still
// MIRRORS are migrating onto this struct / the durable scope graph.
//
// It must NOT hold point-sensitive flow state: "is x initialized HERE" has a
// different value at every program point and forks at branches, so it can't live
// on a single per-declaration record — that's Type_Env's job.
Type_Scope :: struct {
    using sd: Scope_Body,
    kind:           Scope_Kind, // .Struct = data layout, .Fun = callable body
    is_module:      bool,       // true for a package/module namespace scope (top of the parent_scope chain)
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

// Whether a struct can be built without arguments — as a bare declaration, a
// field, an array's element is: each constructor param has a default, and the
// constructor can't fail (nothing would take its err).
constructs_bare :: proc(ft: ^Type_Scope) -> bool {
    for p in ft.params { if p.default_value == nil { return false } }
    return len(ft.return_types) == 0
}

// If `e` is a call to a callable scope, return that callee's return-types list.
// Returns nil for non-calls, calls whose callee can't be resolved, or non-fun
// callees (struct constructors). The caller decides whether nil + non-call vs
// nil + bad-call is an error.
//
// Must be invoked AFTER check_expr on the call, so resolved_func is populated
// (UFCS / package-qualified call names like `string.find` get rewritten to a
// flat name like `mara_string_find` during type checking).
call_return_list :: proc(c: ^Checker, e: Expr, env: ^Type_Scope) -> []Type {
    call, ok := e.(^Expr_Call)
    if !ok { return nil }
    // Prefer the resolved flat name (set by check_expr) over the AST name.
    lookup_name := call_name(call)
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

// A Scope_Body is always the offset-0 `sd` head of a Type_Scope (as_scope_body
// returns &ft.sd; Type_Scope embeds `using sd: Scope_Body`), so we can recover the
// containing Type_Scope by transmute — the same trick ensure_struct_signature uses.
// `is_module` (the namespace marker) lives on Type_Scope, so a ^Scope_Body reaches
// it through here. This replaces the old `sd.scope != nil` test, which used a
// back-ref env field purely as a "this is a module namespace" proxy.
sd_type_scope :: proc(sd: ^Scope_Body) -> ^Type_Scope {
    return transmute(^Type_Scope)sd if sd != nil else nil
}
sd_is_module :: proc(sd: ^Scope_Body) -> bool {
    ts := sd_type_scope(sd)
    return ts != nil && ts.is_module
}
// The module namespace scope to resolve members against, or nil if `sd` is not a
// module-struct (was: the back-ref env, whose .scope was this very Type_Scope).
sd_module_scope :: proc(sd: ^Scope_Body) -> ^Type_Scope {
    ts := sd_type_scope(sd)
    return ts if (ts != nil && ts.is_module) else nil
}

// Check if a Type is a data-layout scope.
is_struct_type :: proc(t: Type) -> bool {
    return as_struct_body(t) != nil
}

// Check if a fun's return type is its own name (self-returning data fun pattern).
is_self_return :: proc(s: ^Stmt_Scope) -> bool {
    if len(s.return_types) != 1 { return false }
    if tn, ok := s.return_types[0].(Type_Name); ok && tn.name == scope_name(s) { return true }
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
                    span          = s.span,
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
                    span          = a.span,
                })
            }
        case ^Stmt_Decl:
            // x : T, x := v, x, y : T, x, y := a, b → one field per name
            // x, y, z := call() — single-init multi-name is tuple-destructure:
            // each binding gets an Expr_Tuple_Default so infer_field_type_from_default
            // unwraps the i-th slot of the call's tuple return type. Same wrapper
            // shape that stmt_decl_to_bindings produces for params/named returns.
            inits := decl_init(s)
            is_tuple_destructure := len(inits) == 1 && len(s.names) > 1
            for name, i in s.names {
                val: Expr = nil
                if is_tuple_destructure {
                    val = new_clone(Expr_Tuple_Default{
                        source = inits[0],
                        index  = i,
                        span   = s.span,
                    })
                } else if i < len(inits) {
                    val = inits[i]
                }
                append(&fields, Scope_Binding{
                    name          = name,
                    type_expr     = decl_type(s),
                    default_value = val,
                    is_using      = s.is_using,
                    span          = s.span,
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
    span:          Span,    // declaring statement's span (diagnostics / `mara ask` locations)
    tag_type:      string,                    // "" = default (i64), or "i32", "i16", etc.
    variants:      map[string]int,
    is_error_kind: bool,    // true for `Name :: error { ... }` — flat tag set in the global `err` type
    error_set_id:  int,     // 1-based set ID assigned at type-check end; 0 = not an error_kind
    is_synthetic:  bool,    // compiler-generated, not a user declaration (e.g. a union's `_Tag` discriminant)
}

Type_Union :: struct {
    name:            string,             // C-ified flat name
    source_name:     string,             // user-written bare name for diagnostics ("" falls back to name)
    home_package:    string,             // owning module flat name (see Scope_Body.home_package)
    span:            Span,               // declaring statement's span (diagnostics / `mara ask` locations)
    tag_type:        string,             // "" = default (i64), or "i32", "i16", etc.
    min_size:        int,                // 0 = no minimum, otherwise minimum total size in bytes (from union(128))
    tag_pad:         Type,               // type of padding between tag and payload (nil = none); reachable as `value.pad`
    variants:        [dynamic]string,    // variant names in declaration order
    tag_map:         map[string]int,     // variant name -> tag value
    variant_structs: map[string]string,  // variant name -> struct name
    tag_enum:        ^Type_Enum,         // the <Name>_Tag enum; type of each variant struct's prepended tag field
    // Set by the checker when the union is niche-laid-out: the variant whose
    // single pointer IS the union's storage — null means the other, fieldless
    // variant, so no tag is stored. "" for a tagged union. See union_niche_variant.
    niche_some:      string,
}

// The niche layout: a union of exactly two variants, one fieldless (None) and
// one holding a single pointer (Some), is stored as that pointer alone —
// `^T` is never null, so null is free to mean None. Returns the Some variant,
// or "" when the union is tagged. A union that spells out its layout — a tag
// type, padding, a minimum size — keeps it: that is how a union mirrors a C
// layout. Runs on the resolved, pre-header variant structs; the one place the
// decision is made (codegen reads ut.niche_some).
union_niche_variant :: proc(c: ^Checker, ut: ^Type_Union) -> string {
    if len(ut.variants) != 2 { return "" }
    if ut.tag_type != "" || ut.tag_pad != nil || ut.min_size > 0 { return "" }
    some, has_empty := "", false
    for vname in ut.variants {
        vst, ok := c.table.structs[ut.variant_structs[vname]]
        if !ok { return "" }
        switch len(vst.fields) {
        case 0:
            has_empty = true
        case 1:
            if _, is_ptr := vst.fields[0].type_.(^Type_Ptr); !is_ptr { return "" }
            some = vname
        case:
            return ""
        }
    }
    return some if has_empty else ""
}

// Once a union's variant structs have their user fields resolved, fold the tag
// (+pad) into each as LEADING fields so the variant IS the union value and
// rides struct codegen: `__tag` at index 0 (typed as the union's tag enum),
// `__pad` next when the union declares padding. The reserved names can't
// collide with user fields; codegen writes the tag value, so neither header
// field needs a default. Niche unions (Maybe(^T)) keep their bare-pointer
// layout and are skipped — their `is_union_variant` stays false, which is how
// codegen tells the two representations apart.
finalize_union_variant_headers :: proc(c: ^Checker, ut: ^Type_Union) {
    ut.niche_some = union_niche_variant(c, ut)
    if ut.niche_some != "" { return }
    for vname in ut.variants {
        vst, ok := c.table.structs[ut.variant_structs[vname]]
        if !ok || vst.is_union_variant { continue }   // idempotent
        vst.is_union_variant = true
        vst.union_variant_tag = i64(ut.tag_map[vname])
        with_header := make([dynamic]Struct_Type_Field)
        append(&with_header, Struct_Type_Field{name = "__tag", type_ = ut.tag_enum})
        if ut.tag_pad != nil {
            append(&with_header, Struct_Type_Field{name = "__pad", type_ = ut.tag_pad})
        }
        for f in vst.fields { append(&with_header, f) }
        vst.fields = with_header
        build_field_map(&vst.sd)
    }
}

// Index of a struct's first user field — past a union variant's `__tag` (and
// `__pad`) header. A positional literal's values map to fields from here.
first_user_field :: proc(sd: ^Scope_Body) -> int {
    if !sd.is_union_variant { return 0 }
    if len(sd.fields) > 1 && sd.fields[1].name == "__pad" { return 2 }
    return 1
}

// Byte size of a union's tag_pad field. Returns 0 when no pad was declared.
union_tag_pad_bytes :: proc(ut: ^Type_Union) -> int {
    if ut.tag_pad == nil { return 0 }
    return checker_type_byte_size(ut.tag_pad)
}

Type_Distinct :: struct {
    name:             string,  // C-ified flat name
    source_name:      string,  // user-written bare name for diagnostics ("" falls back to name)
    home_package:     string,  // owning module flat name (see Scope_Body.home_package)
    span:             Span,    // declaring statement's span (diagnostics / `mara ask` locations)
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
    env:            ^Type_Scope,   // where it is defined: a struct instance's body is checked there
}

Broadcast_Field :: struct {
    name: string,
    span: Span,
}

// A generic struct's instance, its body waiting to be checked
// (check_struct_instances).
Struct_Instance :: struct {
    tmpl:  Generic_Template,
    st:    ^Type_Scope,
    subst: map[string]Type,
    defs:  [dynamic]Stmt,   // its methods (and nested types): its own copies
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

// A reference (however spelled — bare `X`, `Module.X`, `Self.X`) that the checker
// has resolved to a single constant. Codegen just inlines `value_expr`; it never
// looks a constant up by name or knows anything about module qualifiers.
Resolved_Constant :: struct {
    value_expr: Expr,   // the constant's value expression — inline this
    int_value:  int,    // computed integer (fixed-array .len/.cap) when value_expr == nil
}

Resolved_Func :: struct {
    name:         string,        // flat name: "add" or "math_add" — the codegen symbol key
    // Resolved callee signature (pointer identity). Set for direct function /
    // constructor calls AND operator-overload edges so consumers use the pointer
    // instead of re-deriving from `name`: codegen reads the symbol off
    // `callee.name`, and the program graph links the call to its callee's node
    // with it. nil only for non-function resolutions (distinct-type casts) and
    // un-annotated / foreign calls with no callee Type_Scope.
    callee:       ^Type_Scope,
}

// ---------------------------------------------------------------------------
// Type environment (scope chain)
// ---------------------------------------------------------------------------

// Type_Env is GONE. It was a transient per-scope handle carrying resolution state
// during checking; over the teardown every field it held moved onto the durable
// graph or out to a post-check pass (types -> the scope graph; parent -> the
// parent_scope chain; class/fun_scope, is_module_scope, block_scope -> derived
// from scope kind/is_module; return_types -> enclosing_return_types; includes ->
// Scope_Body.includes; bindings -> the escape/flow pass frame stacks). Once it was
// a one-field wrapper `{ scope }`, the wrapper itself was redundant: `env` IS the
// durable ^Type_Scope it pointed at. The checker now threads ^Type_Scope directly
// as the "current scope" handle, walking parent_scope for resolution and
// registering top-level names straight onto the scope.

// Durable scope-member lookup: a scope's nested types + funs live on its
// Does scope `s` define `name` directly (its own types or functions)? One level,
// no parent_scope walk — the durable equivalent of a single env's own .types.
scope_defines :: proc(s: ^Type_Scope, name: string) -> (Type, bool) {
    if s == nil { return nil, false }
    if s.types != nil { if t, ok := s.types[name]; ok { return t, true } }
    if s.functions != nil { if f, ok := s.functions[name]; ok && f != nil { return f, true } }
    return nil, false
}

// True if this env is a module/package namespace — name lookup terminates here.
// Derived purely from the durable scope: each file now gets its OWN .Block scope
// chained to the module (partition_package_files), so a file scope is never the
// module scope — `is_module` alone distinguishes them, no env-identity back-ref.
env_is_module :: proc(env: ^Type_Scope) -> bool {
    return env != nil && env != nil && env.is_module
}

// Look up a bare name exported by an included module — off the module's own
// DURABLE scope (inc.types), which check_module finalizes to the full name
// surface (types + funs + distincts + const/late-bound types) at the end of the
// module's check. A scope holds its names; resolution reads them there.
include_lookup :: proc(inc: ^Scope_Body, name: string) -> (Type, bool) {
    if inc == nil { return nil, false }
    if t, ok := inc.types[name]; ok { return t, true }
    return nil, false
}

// Block-scoped LOCAL lookup over the DURABLE scope graph — the migration target
// for the env.parent walk. From the starting block scope, walk parent_scope
// checking each .Block's locals (.types) and STOP at the first non-.Block (the
// enclosing fun/ctor/struct). The stop encodes "no closures": a block sees its
// own + enclosing blocks' + the function's top-level locals (all .Block scopes),
// but never an outer function's. Members (nested ::types/funs) are NOT here —
// that is scope_member's job, walking past the function boundary.
scope_local_lookup :: proc(start: ^Type_Scope, name: string) -> (Type, bool) {
    for s := start; s != nil && s.kind == .Block; s = s.parent_scope {
        if s.types != nil {
            if t, ok := s.types[name]; ok { return t, true }
        }
    }
    return nil, false
}

// THE durable name-lookup walk: from the current scope up the parent_scope graph
// (own .types/.functions at each level — definitions beat includes), then bare
// includes up the env chain. Returns the SCOPE the name was found in (nil for an
// include hit or a not-found), so callers can ask "was this a field of an
// enclosing class?" without an env back-reference.
//
// `below_module` stops BEFORE the enclosing module scope — the `:=` shadowing
// policy, so a local `shader := gl.CreateShader(...)` doesn't conflate with the
// module's own auto-injected binding.
// Bare-included names via the DURABLE scope graph: walk parent_scope, check each
// scope's own includes, stop at the module. The migration target for the legacy
// env.parent + cur.includes walk (now that decls chain through their file scope,
// the scope chain reaches every include-holding scope the env chain did).
// A block's names are its locals, seen only from inside its own function
// (scope_local_lookup). Past a function boundary a block shows just the
// modules it names (a file's `gl :: use mara.open_gl`): a function sees the
// outside world through its arguments, never an enclosing scope's locals —
// a module's variables included, since a module is a scope like any other.
names_module :: proc(t: Type) -> bool {
    m, ok := t.(^Type_Scope)
    return ok && m.is_module
}

// When `name` is a local of a scope past the function boundary — the one
// thing scope_resolve won't show — the scope that owns it (the module or
// function the block belongs to); nil otherwise.
outer_local_owner :: proc(env: ^Type_Scope, name: string) -> ^Type_Scope {
    s := env
    for s != nil && s.kind == .Block { s = s.parent_scope }
    for ; s != nil; s = s.parent_scope {
        if s.kind != .Block || s.types == nil { continue }
        if t, ok := s.types[name]; !ok || names_module(t) { continue }
        owner := s
        for owner != nil && owner.kind == .Block { owner = owner.parent_scope }
        return owner
    }
    return nil
}

// A name that didn't resolve. When it is an enclosing scope's local, that is
// the rule it broke, so say so instead of `msg`.
report_unresolved :: proc(c: ^Checker, span: Span, env: ^Type_Scope, name: string, msg: string) {
    if owner := outer_local_owner(env, name); owner != nil {
        where_ := owner.source_name if owner.source_name != "" else owner.name
        check_error(c, span, TYPE_LOCAL_OF_ENCLOSING_SCOPE, name, where_)
        return
    }
    check_error(c, span, msg, name)
}

scope_includes_lookup :: proc(env: ^Type_Scope, name: string, below_module: bool) -> (Type, bool) {
    for s := env; s != nil; s = s.parent_scope {
        if below_module && s.is_module { break }
        for inc in s.includes { if t, ok := include_lookup(inc, name); ok { return t, true } }
        if s.is_module { break }
    }
    return nil, false
}

scope_resolve :: proc(env: ^Type_Scope, name: string, below_module := false) -> (Type, ^Type_Scope, bool) {
    for s := env; s != nil; s = s.parent_scope {
        if below_module && s.is_module { break }
        if s.types != nil {
            t, ok := s.types[name]
            if ok && (s.kind != .Block || names_module(t)) { return t, s, true }
        }
        if s.functions != nil { if f, ok := s.functions[name]; ok && f != nil { return f, s, true } }
    }
    if t, ok := scope_includes_lookup(env, name, below_module); ok { return t, nil, true }
    return nil, nil, false
}

// THE name-lookup walk (type_env_get / type_env_locate_below_module are thin
// wrappers). LOCALS first over the block-scope graph (stops at the function
// boundary — no closures), then the durable scope_resolve walk (enclosing class
// members + module names + bare includes). Returns the SCOPE the name was found
// in — nil for a local or an include hit — so the field-leak guards can ask
// "is this a field of an enclosing class?" (a non-module .Struct scope).
//
// This is the env→scope-graph switch: name resolution no longer reads env.types;
// it walks the durable parent_scope graph that runs parallel to the env chain
// (validated under MARA_WALK_CHECK: zero gaps and zero type-identity mismatches
// vs the old env.types walk across every fixture, Pounce, and all.mara).
type_env_locate :: proc(env: ^Type_Scope, name: string, below_module := false) -> (Type, ^Type_Scope, bool) {
    // LOCALS first: scope_local_lookup self-guards on .Block (the env's scope is a
    // .Block iff this is a block body), so an enclosing fun/class/module scope
    // stops the walk immediately and falls through to scope_resolve.
    if t, ok := scope_local_lookup(env, name); ok {
        return t, nil, true  // a local never lives in a class namespace
    }
    return scope_resolve(env, name, below_module)
}

type_env_get :: proc(env: ^Type_Scope, name: string) -> (Type, bool) {
    t, _, ok := type_env_locate(env, name)
    return t, ok
}

type_env_locate_below_module :: proc(env: ^Type_Scope, name: string) -> (Type, ^Type_Scope, bool) {
    return type_env_locate(env, name, below_module = true)
}

// Like type_env_get but with own-types-first semantics across the whole chain:
// every enclosing scope's own definitions are checked BEFORE any scope's
// includes. Used by type-name resolution so a local `Timer :: struct {...}`
// in mod_env beats an enum-variant Timer that flowed in via a per-file
// `sdl :: include mara.sdl2`. The default lookup uses the current order
// (own-then-includes per level) because flipping it globally regresses
// class-body field resolution and other paths that rely on cur.includes
// being checked before walking to cur.parent.types.
type_env_get_owned_first :: proc(env: ^Type_Scope, name: string) -> (Type, bool) {
    // scope_resolve IS owned-first by construction (all own definitions up the
    // parent_scope graph, then all includes up the env chain) — exactly this
    // proc's two-phase shape. Delegate to the durable walk.
    t, _, ok := scope_resolve(env, name)
    return t, ok
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
resolve_with_ambiguity :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> (typ: Type, ok: bool, ambiguous_owners: [dynamic]string) {
    // `Self` is the enclosing struct/fun's own scope — derive it from the durable
    // graph (the nearest class_scope/fun_scope marker) rather than an env binding.
    if name == "Self" {
        if s := enclosing_callable_scope(env); s != nil { return s, true, nil }
        return nil, false, nil
    }
    // An OWN definition (a local type, an enclosing class member, or a module
    // definition) wins unambiguously over any import — walk the durable scope
    // graph own-only, inner-to-outer (lexical shadowing built in).
    for s := env; s != nil; s = s.parent_scope {
        if t, found := scope_defines(s, name); found {
            typ, ok = t, true
            break
        }
    }
    if !ok {
        // No own definition: gather distinct include owners at the nearest env
        // level that provides the name (the per-level stop). Two+ distinct
        // imports of the same name = ambiguous; the caller errors.
        owner_list: [dynamic]string
        distinct_typs: map[rawptr]bool
        distinct_owners: map[string]bool
        first_typ: Type
        for s := env; s != nil; s = s.parent_scope {
            found_any := false
            for inc in s.includes {
                if t, found := include_lookup(inc, name); found {
                    found_any = true
                    if first_typ == nil { first_typ = t }
                    key := raw_type_key(t)
                    if key not_in distinct_typs {
                        distinct_typs[key] = true
                        owner := inc.name if inc != nil else "<anonymous-include>"
                        if owner not_in distinct_owners {
                            distinct_owners[owner] = true
                            append(&owner_list, owner)
                        }
                    }
                }
            }
            if found_any { break }  // stop at nearest level with includes
            if s.is_module { break }
        }
        if len(distinct_typs) == 1 { typ, ok = first_typ, true }
        else if len(distinct_typs) > 1 { ambiguous_owners = owner_list }
    }
    return
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

type_env_set :: proc(s: ^Type_Scope, name: string, t: Type) {
    // Names live on the durable scope graph — what resolution walks.
    if s != nil {
        if s.types == nil { s.types = make(map[string]Type) }
        s.types[name] = t
    }
}

// True if the expression is exactly the `void` literal — Mara's null
// pointer constant. Treated semantically as "no usable value": assigning
// it to a pointer is equivalent to leaving the pointer uninitialized.
is_void_literal :: proc(e: Expr) -> bool {
    if id, ok := e.(^Expr_Ident); ok && id.name == "void" { return true }
    return false
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

type_env_child :: proc(parent: ^Type_Scope) -> ^Type_Scope {
    // Every child scope is chained to the parent's, so the durable graph carries
    // the nesting. Specific creators (block/ns/module) use a concrete scope
    // directly; this is the default shadow.
    s := new(Type_Scope)
    s.parent_scope = parent
    return s
}

// Like type_env_child but also mints the durable .Block Type_Scope this block
// env shadows, linked into the parent_scope graph at the nearest enclosing scope
// (a containing block if there is one, else the enclosing fun/ctor). Used at the
// if/for/defer block sites; locals declared in the block land on bs.types via
// type_env_set. Additive for now — name lookup still runs off the env chain; the
// block scope is built so the kind-gated parent_scope walk can be validated
// against it before the env walk is retired.
type_env_block_child :: proc(parent: ^Type_Scope) -> ^Type_Scope {
    child := type_env_child(parent) // minted, parent_scope = parent
    // The minted durable scope IS the block scope. parent already equals the
    // nearest enclosing scope (a containing block, else the enclosing fun/ctor),
    // so the chain matches the old enclosing-scope link.
    child.kind = .Block
    return child
}

// The enclosing function's user name (for #caller_name), read from the DURABLE
// scope graph — the nearest fun/ctor's Type_Scope — instead of a per-env mirror.
// (Frame-lift: Type_Env no longer carries an fn_name copy.)
enclosing_fn_name :: proc(env: ^Type_Scope) -> string {
    if s := enclosing_callable_scope(env); s != nil {
        return s.source_name if s.source_name != "" else s.name
    }
    return "main" // top-level code runs in main
}

// The expected return types of the nearest enclosing function / constructor body,
// A callable scope: a fun, or a non-module struct/class (a ctor body). Modules
// are .Struct too but never a callable. This is what the old class_scope/fun_scope
// env markers identified — they were always set to the env's own .scope, which is
// a non-module struct (class defs layer) or a fun. Derive instead of storing.
scope_is_callable :: proc(s: ^Type_Scope) -> bool {
    return s != nil && (s.kind == .Fun || (s.kind == .Struct && !s.is_module))
}

// The module scope at the top of a scope's parent_scope chain (the durable
// equivalent of "walk env.parent to the root env"). nil if `s` is nil.
module_scope :: proc(start: ^Type_Scope) -> ^Type_Scope {
    s := start
    for s != nil && s.parent_scope != nil { s = s.parent_scope }
    return s
}

// Register a (mangled) name persistently on the module scope.
register_on_module :: proc(root: ^Type_Scope, name: string, t: Type) {
    if root == nil { return }
    if root.types == nil { root.types = make(map[string]Type) }
    root.types[name] = t
}

// The class/struct scope an env is the defs layer of — nil unless env is a
// non-module struct. Replaces the old env.class_scope marker (a class ns_env set
// class_scope = its own ft = env).
env_class_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env != nil && env != nil && env.kind == .Struct && !env.is_module {
        return env
    }
    return nil
}

// The nearest enclosing struct/class scope, walking the durable scope graph
// (uniform — modules/funs/blocks in the chain are just skipped). For `#self` and
// "am I inside a class body" — find-nearest-struct, a query over the one chain.
enclosing_struct_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil { return nil }
    for s := env; s != nil; s = s.parent_scope {
        if s.kind == .Struct && !s.is_module { return s }
    }
    return nil
}

// The struct scope this env's block sits DIRECTLY inside (its scope's immediate
// parent), or nil — for "is this decl in a struct body" (a field decl).
parent_struct_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil || env == nil { return nil }
    p := env.parent_scope
    if p != nil && p.kind == .Struct && !p.is_module { return p }
    return nil
}

// DERIVED from the durable scope graph: walk from this env's scope up parent_scope
// to the nearest callable (fun/ctor) and read its return_types. Empty = void.
enclosing_return_types :: proc(env: ^Type_Scope) -> []Type {
    if env == nil { return nil }
    for s := env; s != nil; s = s.parent_scope {
        if scope_is_callable(s) { return s.return_types[:] }
    }
    return nil
}

// The nearest enclosing callable scope — the fun / ctor whose body we're checking.
// The "caller" for call-graph edges. nil at module level (a call in a top-level
// const value etc. has no enclosing function node). Walks the durable scope graph.
enclosing_callable_scope :: proc(env: ^Type_Scope) -> ^Type_Scope {
    if env == nil { return nil }
    for s := env; s != nil; s = s.parent_scope {
        if scope_is_callable(s) { return s }
    }
    return nil
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
resolve_type_name :: proc(c: ^Checker, bare_name: string, qualifier: string = "", env: ^Type_Scope = nil) -> string {
    if qualifier != "" {
        // Try module-qualified resolution: look up qualifier in env
        if env != nil {
            qual_type, found := type_env_get(env, qualifier)
            if found {
                if mod_sd := as_scope_body(qual_type); sd_is_module(mod_sd) {
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
        for s := env; s != nil; s = s.parent_scope {
            if s.is_module {
                if _, found := scope_defines(s, bare_name); found {
                    return make_flat_name(c.current_package, bare_name)
                }
            }
            for inc in s.includes {
                if inc == nil { continue }
                if _, found := include_lookup(inc, bare_name); found {
                    return make_flat_name(inc.name, bare_name)
                }
            }
            if s.is_module { break }
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
resolve_fn_type_name :: proc(c: ^Checker, dotted: string, env: ^Type_Scope) -> string {
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
// basic arithmetic + bit-shift operators on comptime operands, and — when the
// caller passes its env — `.cap`/`.len` of a variable whose type carries a
// static size (fixed array, partial array), so one array's bound can derive
// from another's (`is_corner : [..edges.cap]bool`). Anything else returns
// ok=false; callers should emit a "comptime-known integer expected" error so
// the user gets a clear diagnostic.
evaluate_comptime_int :: proc(c: ^Checker, e: Expr, env: ^Type_Scope = nil) -> (value: i64, ok: bool) {
    #partial switch v in e {
    case ^Expr_Number:
        return i64(v.value), true
    case ^Expr_Unary:
        if v.op == .Minus {
            inner, inner_ok := evaluate_comptime_int(c, v.operand, env)
            if inner_ok { return -inner, true }
        }
    case ^Expr_Ident:
        if const_expr, found := c.table.constants[v.name]; found {
            return evaluate_comptime_int(c, const_expr, env)
        }
    case ^Expr_Field_Access:
        // `arr.cap` (or `arr.len` of a FIXED array, where len == cap == N) is
        // part of arr's TYPE, not its runtime state. A partial array's .len is
        // runtime — only its capacity folds.
        if env != nil && (v.field == "cap" || v.field == "len") {
            if base, base_ok := v.expr.(^Expr_Ident); base_ok {
                if bt, found := type_env_get(env, base.name); found {
                    t := bt
                    if dt, dt_ok := t.(^Type_Distinct); dt_ok { t = dt.base_type }
                    if pa, pa_ok := t.(^Type_Partial_Array); pa_ok && v.field == "cap" && pa.size > 0 {
                        return i64(pa.size), true
                    }
                    if fa, fa_ok := t.(^Type_Fixed_Array); fa_ok && fa.size > 0 {
                        return i64(fa.size), true
                    }
                }
            }
        }
    case ^Expr_Binary:
        l, l_ok := evaluate_comptime_int(c, v.left, env)
        if !l_ok { return 0, false }
        r, r_ok := evaluate_comptime_int(c, v.right, env)
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

// fold_comptime_ifs resolves every comptime `#if` in `stmts` in place, BEFORE the
// checker runs. The live arm's statements replace the `#if` (so they keep source
// order); the dead arm is dropped entirely — it is never checked, so its
// platform-specific names that don't exist on this target never need to resolve.
// Recurses through every nested body so no comptime `#if` survives to the checker
// (the def/runtime split downstream then never has to treat `#if` as a hybrid).
// Returns true if THIS list's shape changed (a top-level `#if` was folded here),
// so a Stmt_Scope can rebuild its defs index from the new body.
fold_comptime_ifs :: proc(c: ^Checker, stmts: ^[dynamic]Stmt) -> (folded_here: bool) {
    any_if := false
    for s in stmts^ {
        if cif, ok := s.(^Stmt_If); ok && cif.is_comptime { any_if = true; break }
    }
    if !any_if {
        for s in stmts^ { fold_comptime_ifs_children(c, s) }
        return false
    }
    out: [dynamic]Stmt
    for s in stmts^ {
        if cif, ok := s.(^Stmt_If); ok && cif.is_comptime {
            live, eval_ok := evaluate_comptime_bool(c, cif.condition)
            if !eval_ok {
                append(&out, s)   // unevaluable — leave it for the checker to report
                continue
            }
            arm := &cif.body if live else &cif.else_body
            fold_comptime_ifs(c, arm)               // fold nested #if in the live arm
            for inner in arm^ { append(&out, inner) }
            continue
        }
        fold_comptime_ifs_children(c, s)
        append(&out, s)
    }
    stmts^ = out
    return true
}

// fold_comptime_ifs_children recurses into a statement's nested bodies. For a
// Stmt_Scope whose body changed, it rebuilds the defs index from the folded body.
fold_comptime_ifs_children :: proc(c: ^Checker, s: Stmt) {
    #partial switch v in s {
    case ^Stmt_Scope:
        fold_comptime_ifs(c, &v.body)   // recurses into nested scopes too
        // Partition the (folded) body into compile-time defs and runtime body —
        // disjoint, each kept in source order. Scope-walks read defs; codegen and
        // the runtime passes read body.
        new_defs: [dynamic]Stmt
        new_body: [dynamic]Stmt
        for st in v.body {
            if is_scope_def(st) { append(&new_defs, st) } else { append(&new_body, st) }
        }
        v.defs = new_defs
        v.body = new_body
    case ^Stmt_If:
        fold_comptime_ifs(c, &v.body)
        fold_comptime_ifs(c, &v.else_body)
    case ^Stmt_For:
        fold_comptime_ifs(c, &v.body)
    case ^Stmt_Match:
        for i in 0 ..< len(v.arms) {
            fold_comptime_ifs(c, &v.arms[i].body)
        }
    case ^Stmt_Defer:
        fold_comptime_ifs(c, &v.body)
    }
}

// Like resolve_fn_home but reports ambiguity when 2+ visible includes provide
// the same function name. Mirrors resolve_with_ambiguity for type names —
// own definitions in any enclosing scope still win unambiguously; ambiguity
// only fires when the name comes from imports and 2+ imports expose it
// (e.g. `include mara.sdl + include mara.sdl2`, both with PollEvent).
resolve_fn_home_with_ambiguity :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> (home: string, ok: bool, ambiguous_owners: [dynamic]string) {
    // Phase 1: own definitions in any enclosing module (always unambiguous).
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            if s.is_module {
                if t, found := scope_defines(s, name); found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        return c.current_package, true, nil
                    }
                }
                break
            }
        }
    }
    // Phase 2: gather distinct include owners exposing this fn.
    distinct_owners: map[string]bool
    owner_list: [dynamic]string
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            for inc in s.includes {
                if inc == nil { continue }
                if t, found := include_lookup(inc, name); found {
                    if ts, fok := t.(^Type_Scope); fok && ts.kind == .Fun {
                        owner := inc.name
                        if owner not_in distinct_owners {
                            distinct_owners[owner] = true
                            append(&owner_list, owner)
                        }
                    }
                }
            }
            if s.is_module { break }
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
resolve_fn_home :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> string {
    if env != nil {
        for s := env; s != nil; s = s.parent_scope {
            if s.is_module {
                if t, found := scope_defines(s, name); found {
                    if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun {
                        return c.current_package
                    }
                }
            }
            for inc in s.includes {
                if inc == nil { continue }
                if t, found := include_lookup(inc, name); found {
                    if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun {
                        return inc.name
                    }
                }
            }
            if s.is_module { break }
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
    functions:      map[string]^Type_Scope,
    foreign_libs:   map[string]bool,

    // Ordered list of main-package function names (preserves AST order for emission)
    function_order: [dynamic]string,

    // Materialized call graph (nodes = callable scopes, edges = resolved calls,
    // + strongly-connected components): an index over the program graph's calls.
    // See callgraph.odin / design/mara_ask.md §12.
    call_graph:     Call_Graph,

    // The program graph (graph.odin) — built after checking; nothing reads it
    // yet (design/graph_retrofit.md, phase 1).
    graph:          Program_Graph,

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

    // Def-use over the program graph (defuse.odin), built per function on the
    // first `mara ask` flow query that needs it: what the flow views slice.
    du:             Def_Use,
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
    root_env: ^Type_Scope,
}

// ---------------------------------------------------------------------------
// Checker state — transient state used during a single checking pass.
// Holds a pointer to the shared SymbolTable plus per-check mutable state.
// ---------------------------------------------------------------------------

Checker :: struct {
    // MARA_CHECK_ONCE=1 (debug builds): each statement of a body's code is
    // numbered, and an expression checked twice within one is reported — the
    // walk that builds the graph must meet each once (design/graph_retrofit.md,
    // phase 4).
    once_stmt:       int,
    once_seen:       map[rawptr][2]int,   // an expression → the statement it was last checked in, and how often
    once_on:         bool,
    // A method call's receiver, checked to find its struct: the argument it
    // becomes is not checked again (check_call_args), one check per node.
    receiver:        Expr,
    receiver_type:   Type,
    receiver_fused:  Fused,              // (building) what its check built
    receiver_want:   Maybe(Written),     // (building) a qualified call's: build its receiver
    // The program graph's builder, made before checking: the bodies it can,
    // the checker builds as it checks them (graph_fuse_begin). What the walk
    // asks of the next expression it checks (fuse_expr), what the one being
    // checked was asked (fuse_asked), what it built; the call whose arguments
    // are being checked.
    gb:              ^Graph_Builder,
    want:            Fuse_Want,
    want_written:    Written,
    want_dest:       Dest,
    want_temp:       bool,             // (with .Into) the destination holds a value: build in a temporary
    want_span:       Span,             // … at the store's span
    asked:           Fuse_Want,
    asked_written:   Written,
    asked_dest:      Dest,
    asked_temp:      bool,
    asked_span:      Span,
    lit:             ^Fuse_Lit,        // the literal whose fields are being built
    fused:           Fused,
    call:            ^Fuse_Call,
    compound:        Graph_Compound,   // a compound assignment's target and the place built for it
    byte_addrs:      map[rawptr][2]Node_Id,   // `&bytes[i]` built: its address and element operations
    struct_instances: [dynamic]Struct_Instance,   // generic struct instances made, their bodies checked last
    parallel:        ^Fuse_Parallel,    // several reassigned together: their stores held (fuse_parallel_hold)
    broadcast_fields: map[rawptr]Broadcast_Field, // a field's `{all <expr>}`: its field, its value checked with the field's
    span_read:       Fuse_Span_Read,   // the span of bytes last built to be read as its destination's type
    table:           ^SymbolTable,
    errors:          int,
    current_package: string,
    target_web:      bool,                // -web build flag, drives #web / #native intrinsics
    target_shared:   bool,                // -shared build flag — package compiles to a DLL/SO; no `main` required
    target_os:       Target_OS,           // OS target, drives #windows / #linux / #mac intrinsics
    analysis_only:   bool,                // `mara ask` — read-only static analysis; never emits or runs code, so runtime-shape guards (e.g. the arena/stack-size routing check) that assume an executable with a `main` are skipped
    type_params:     map[string]Type,
    top_env:         ^Type_Scope,
    declared_funs:   map[string]bool,  // bare names of Stmt_Scope declarations (direct calls vs variables)
    // The materialized call graph (set post-check, after build_call_graph) — its
    // bottom-up summaries back the escape pass and the `ask` slicer. Points at
    // checked.call_graph.
    cg:              ^Call_Graph,
    // True during the register-pass scan over a function's body fields.
    // Field types are resolved in declaration order, so annotations like
    // `h : fn g` may reference locals not yet added to env. Unresolved names
    // in this pass return Type_Error{} silently; the body-check pass re-runs
    // resolution with all locals in scope and emits real errors then.
    in_register_pass: bool,
    // True while resolving a `foreign` declaration's signature — the only
    // context where `cstring` may be named as a type (see resolve_type_expr).
    in_foreign_sig: bool,
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
    mara_env:             ^Type_Scope,               // root scope (contains std + user modules)
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
resolve_variant_ident :: proc(c: ^Checker, e: ^Expr_Ident, hint: Type, env: ^Type_Scope, dot: bool) -> (Type, bool) {
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
            if tag_val, v_ok := ut.tag_map[e.name]; v_ok {
                // Data-union variant: the union value holding that variant
                // with its defaults (`.Rect` == `Rect{}`), as `Shape.Rect`
                // resolves in check_field_access.
                e.resolved = Resolved_Union_Variant{
                    union_name  = ut.name,
                    variant     = e.name,
                    tag_value   = tag_val,
                    struct_name = ut.variant_structs[e.name] or_else e.name,
                }
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
    // Once per place: two checks can reach one node (a declaration's
    // literal is checked as a value and as what the declaration holds).
    if emit_diagnostic_once(.Type_Error, format_location(span.file, span.line, span.col), msg, ..args) {
        c.errors += 1
    }
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
        if call_name(v) != "" { return fmt.tprintf("%s()", call_name(v)) }
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
        for arg in call_args(v) {
            if n, ok := find_self_call_name(arg); ok { return n, true }
        }
        for arg in call_args(v) {
            if _, is_self := arg.(^Expr_Self); is_self {
                return call_name(v), true
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
        for arg in call_args(v) { if contains_self_anywhere(arg) { return true } }
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
        if len(decl_init(decl)) == 0 { continue }
        if !has_decl_after[i] { continue }
        for init in decl_init(decl) {
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
// A constructor that can fail can't run bare either: nothing takes its err.
// An array's elements that can't be built bare are left zero (a warning).
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
    type_shown := class_ft.source_name if class_ft.source_name != "" else class_ft.name
    if is_array && !constructs_bare(class_ft) {
        check_warning(c, span, TYPE_WON_GET_AUTO_CONSTRUCTED_DECLARED, type_shown, name)
        return
    }
    for p in class_ft.params {
        if p.default_value == nil {
            // Build a signature like `Camera(w: f32, h: f32, fovy: f32)` so the
            // user can see exactly what to pass.
            sig: strings.Builder
            strings.builder_init(&sig)
            strings.write_string(&sig, type_shown)
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

            check_error(c, span,
                TYPE_TYPE_SELF_CONSTRUCTING_CALL_LIKE,
                name, type_shown, strings.to_string(sig), name, type_shown, type_shown)
            return
        }
    }
    if len(class_ft.return_types) > 0 {
        check_error(c, span, TYPE_BARE_CAN_FAIL, name, type_shown, name, type_shown)
    }
}


// ---------------------------------------------------------------------------
// Resolve a parser Type_Expr to a checker Type
// ---------------------------------------------------------------------------

// `cstring` is the C boundary type: only `foreign` signatures may declare it
// (c.in_foreign_sig is set around their resolution). Regular Mara code takes
// `[]utf8` and lets the call-site conversion write the terminator — without
// this gate the type leaks up every call chain that eventually touches C.
// Checked here, at the single entry point every source type annotation
// passes through; recursion re-enters via the public name so nested
// positions (`^cstring`, fields, fn types) are covered too.
resolve_type_expr :: proc(te: Type_Expr, c: ^Checker = nil, span: Span = {}, const_values: ^map[string]int = nil, env: ^Type_Scope = nil) -> Type {
    t := resolve_type_expr_impl(te, c, span, const_values, env)
    if c != nil && !c.in_foreign_sig && is_cstring(t) {
        check_error(c, span, TYPE_CSTRING_FOREIGN_ONLY)
    }
    return t
}

resolve_type_expr_impl :: proc(te: Type_Expr, c: ^Checker = nil, span: Span = {}, const_values: ^map[string]int = nil, env: ^Type_Scope = nil) -> Type {
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
        case "utf8":   return Type_Utf8{}
        case "byte":   return Type_Byte{}
        case "void":   return Type_Void{}
        case "err":    return Type_Err{}
        case "cstring":
            // Built-in C boundary type — no stdlib decl, no import needed.
            // The foreign-only placement rule lives in the resolve_type_expr
            // wrapper (is_cstring check); the `cstring(s)` constructor is a
            // builtin call handled in check_call.
            return Type_CString{}
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
            } else if env != nil {
                // Function-local / nested parent: resolve_type_name's flat key
                // only covers module-level types, so the table lookups above
                // miss a parent defined inside a fun body. Find it directly in
                // the lexical env, where local nested types live.
                if alias_t, alias_ok := type_env_get(env, alias); alias_ok {
                    parent_sd = as_scope_body(alias_t)
                }
            }
            if parent_sd != nil {
                // type_name_str may itself be dotted for deeply-nested types
                // (Parent.Inner.Innermost): index_byte above split off only the
                // first segment as `alias`. Walk each intermediate segment
                // through the nested `types` map, then resolve the final one.
                cur_sd := parent_sd
                rest := type_name_str
                for {
                    next_dot := strings.index_byte(rest, '.')
                    if next_dot < 0 { break }
                    seg_t, seg_ok := cur_sd.types[rest[:next_dot]]
                    if !seg_ok { break }
                    next_sd := as_scope_body(seg_t)
                    if next_sd == nil { break }
                    cur_sd = next_sd
                    rest = rest[next_dot+1:]
                }
                if inner_t, at_ok := cur_sd.types[rest]; at_ok {
                    return inner_t
                }
                // Check for associated function: StructName.fn_name -> Type_Func
                if fn, fn_ok := cur_sd.functions[rest]; fn_ok && fn != nil {
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
        if t.index_type != nil {
            fa.index_type = resolve_type_expr(t.index_type, c, span, env = env)
        }
        // Expression-based size: try comptime evaluation first (handles
        // `17 * MB`, named `::` constants, bit-shifts, etc.). Only error
        // if the expression genuinely depends on runtime values.
        if t.size_expr != nil {
            if c != nil {
                if bad, has_bad := first_invisible_const_ref(c, env, t.size_expr); has_bad {
                    check_error(c, span, TYPE_UNDEFINED_IDENTIFIER, bad)
                    return Type_Error{}
                }
                if val, comptime_ok := evaluate_comptime_int(c, t.size_expr, env); comptime_ok {
                    fa.size = int(val)
                    fa.elem = elem
                    return fa
                }
                // Register-pass scan of a scope body: locals the size refers
                // to (`other.cap`) may not be in env yet — stay silent; the
                // body-check pass re-resolves with all locals visible and
                // emits the real error at the decl's own span.
                if !c.in_register_pass {
                    check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
                }
            }
            return Type_Error{}
        }
        if t.size_name != "" {
            resolved := false
            // Path 1: checker available (type checking phase)
            if c != nil {
                if _, is_const := c.table.constant_owners[t.size_name]; is_const && !module_constant_visible(c, env, t.size_name) {
                    check_error(c, span, TYPE_UNDEFINED_IDENTIFIER, t.size_name)
                    return Type_Error{}
                }
                if const_expr, found := c.table.constants[t.size_name]; found {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        fa.size = int(i_val)
                        resolved = true
                    } else if val, comptime_ok := evaluate_comptime_int(c, const_expr); comptime_ok {
                        // Constant defined by an expression (1 << 16, 3 * MB):
                        // fold it like an inline size expression would be.
                        fa.size = int(val)
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
        return sl
    case ^Type_Partial_Array_Expr:
        elem := resolve_type_expr(t.elem, c, span, env = env)
        pa := new(Type_Partial_Array)
        pa.elem = elem
        if t.size_expr != nil {
            if c != nil {
                if bad, has_bad := first_invisible_const_ref(c, env, t.size_expr); has_bad {
                    check_error(c, span, TYPE_UNDEFINED_IDENTIFIER, bad)
                    return Type_Error{}
                }
                if val, comptime_ok := evaluate_comptime_int(c, t.size_expr, env); comptime_ok {
                    pa.size = int(val)
                    return pa
                }
                // Runtime partial-array size: must be a compile-time constant.
                // Silent during the register-pass scan (locals not in env yet);
                // the body-check pass re-resolves with all locals visible.
                if !c.in_register_pass {
                    check_error(c, span, TYPE_RUNTIME_SIZED_ARRAYS_SUPPORTED_USE, type_name(elem))
                }
            }
            return Type_Error{}
        }
        if t.size_name != "" {
            if c != nil {
                if _, is_const := c.table.constant_owners[t.size_name]; is_const && !module_constant_visible(c, env, t.size_name) {
                    check_error(c, span, TYPE_UNDEFINED_IDENTIFIER, t.size_name)
                    return Type_Error{}
                }
                if const_expr, found := c.table.constants[t.size_name]; found {
                    if _, i_val, ok := extract_constant_value(const_expr); ok {
                        pa.size = int(i_val)
                        return pa
                    }
                    // Constant defined by an expression (1 << 16, 3 * MB):
                    // fold it like an inline size expression would be.
                    if val, comptime_ok := evaluate_comptime_int(c, const_expr); comptime_ok {
                        pa.size = int(val)
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
                    // Visibility gate: a registered module constant used as a
                    // const generic arg must be reachable from env, same as in
                    // array sizes / ordinary expressions.
                    if _, is_const := c.table.constant_owners[tn.name]; is_const && !module_constant_visible(c, env, tn.name) {
                        check_error(c, span, TYPE_UNDEFINED_IDENTIFIER, tn.name)
                        append(&type_args, Type_Const_Int{value = 0})
                        continue
                    }
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
        populate_cg_signature(ft)
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
        return sl
    case ^Type_Partial_Array_Expr:
        elem := resolve_type_expr_with_subst(t.elem, c, span, subst)
        pa := new(Type_Partial_Array)
        pa.elem = elem
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
        populate_cg_signature(ft)
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
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
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
    st.source_name = mangled
    st.home_package = tmpl.home_package
    st.kind = .Struct
    st.ast = tmpl.ast
    st.body_span = tmpl.ast.span   // an instance is declared where its template is
    st.generic_base = tmpl.name
    for arg in type_args {
        append(&st.generic_args, arg)
    }

    tmpl_fields := extract_fields_from_body(tmpl.ast.body)
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
    // Its methods: the template's, its own copies, registered now (a call
    // names one before the body is checked) — its type params seen from
    // them, its scope the template's.
    if st.parent_scope == nil { st.parent_scope = tmpl.env }
    for name, t in subst { type_env_set(st, name, t) }
    defs := clone_stmts(tmpl.ast.defs)
    if len(defs) > 0 {
        saved_package := c.current_package
        c.current_package = tmpl.home_package
        register_scope_defs(c, st, &st.sd, defs)
        c.current_package = saved_package
    }
    append(&c.struct_instances, Struct_Instance{tmpl = tmpl^, st = st, subst = subst, defs = defs})   // (its body: check_struct_instances)

    return st
}

// The program's struct (the compiler's): built from mara.core's declaration
// of it — its fields, no code — whose body the checker checks for no type.
fuse_program_struct :: proc(c: ^Checker) {
    pt := c.table.funs["Program"] or_else nil
    if c.gb == nil || pt == nil || pt.body_span == {} { return }
    for _, tmpl in c.table.generic_templates {
        if tmpl.ast.span != pt.body_span { continue }
        f := graph_fuse_begin(c.gb, pt, tmpl.ast, tmpl.ast.body[:], .Synthetic)
        if f == nil { return }
        graph_fuse_program_fields(c.gb, tmpl.ast.body[:])
        fuse_end(c, f)
        return
    }
}

// Each generic struct instance's body, checked as its own copy — in its
// template's scope, its type params bound — its graph built as it is (as a
// generic fun's instance is). Instances are made as signatures resolve, so
// their bodies are checked once every package's are; one may make more.
// Its methods are checked with it, and extracted for codegen as a fun's are.
check_struct_instances :: proc(c: ^Checker) {
    for i := 0; i < len(c.struct_instances); i += 1 {
        inst := c.struct_instances[i]
        if inst.tmpl.env == nil { continue }
        s := new_clone(inst.tmpl.ast^)
        s.body = clone_stmts(inst.tmpl.ast.body)
        s.defs = inst.defs
        saved_params, saved_package := c.type_params, c.current_package
        c.type_params, c.current_package = inst.subst, inst.tmpl.home_package
        check_scope_body(c, s, inst.tmpl.env, instance = &inst)
        if c.checked != nil && len(inst.defs) > 0 { extract_scope_fun_defs(c.checked, inst.defs, inst.st, inst.tmpl.home_package) }
        // (Its init, for codegen — as a construction call's instance has:
        // one declared bare, `b : Buf(i64)`, runs it too, its fields' values
        // and partial arrays' headers.)
        if c.checked != nil {
            if _, exists := c.checked.functions[inst.st.name]; !exists {
                st := inst.st
                st.home_package = inst.tmpl.home_package
                st.body = s.body
                st.ast = inst.tmpl.ast
                st.origin = Origin_Source{}
                st.body_span = inst.tmpl.ast.span
                populate_cg_signature(st)   // Self prepended for .Struct
                c.checked.functions[st.name] = st
                append(&c.checked.function_order, st.name)
            }
        }
        c.type_params, c.current_package = saved_params, saved_package
    }
}

// Instantiate a generic union template with concrete type arguments. Mirrors
// instantiate_generic_struct but produces a Type_Union — builds variant structs
// with substituted field types, the tag enum, and registers everything into
// c.table.unions / c.table.structs / c.table.enums under mangled names.
instantiate_generic_union :: proc(c: ^Checker, tmpl: ^Generic_Union_Template, type_args: []Type, span: Span) -> ^Type_Union {
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
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
    ut.source_name = mangled
    ut.home_package = tmpl.home_package
    ut.span = s.span
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
    tag_et.span = s.span   // synthetic discriminant: locate at the union decl
    tag_et.is_synthetic = true
    for vdef in s.variants {
        tag_et.variants[vdef.name] = vdef.tag
    }
    c.table.enums[tag_et.name] = tag_et
    ut.tag_enum = tag_et

    // Variant structs with substituted field types.
    for vdef in s.variants {
        struct_name := strings.concatenate({mangled, "_", vdef.name})
        vst := new(Type_Scope)
        vst.name = make_flat_name(tmpl.home_package, struct_name)
        vst.home_package = tmpl.home_package
        vst.kind = .Struct
        vst.body_span = vdef.span
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
    finalize_union_variant_headers(c, ut)

    c.table.unions[ut.name] = ut
    c.table.mono_union_cache[mangled] = ut
    if c.top_env != nil {
        type_env_set(c.top_env, mangled, ut)
    }

    return ut
}

// Infer generic type parameters by walking a type expression and actual type in parallel.
// Fills in the substitution map with discovered bindings.
infer_type_params :: proc(subst: ^map[string]Type, type_expr: Type_Expr, actual_raw: Type, c: ^Checker) {
    // Transparent aliases (str = [..128]utf8) match through their underlying
    // shape; true distinct types stay nominal (unwrap_alias leaves them).
    actual := unwrap_alias(actual_raw)
    switch t in type_expr {
    case Type_Name:
        // Check if this is a generic type param name (single uppercase letter or known param)
        // During generic function checking, param names like "T" appear as bare Type_Name
        if _, ok := subst[t.name]; !ok {
            // Only infer if this name is already a key in subst (even if nil)
            // The caller pre-populates subst with nil values for all generic param names
        }
        if t.name in subst^ && subst[t.name] == nil {
            // (An untyped argument — a literal, an open binding — binds its
            // settled type, as a declaration would; it converts at the call.)
            subst[t.name] = solidify_type(actual)
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
            // Fixed arrays decay to slices by value (header materialised);
            // drives slice-shaped inference. Pointer case stays closed.
            infer_type_params(subst, t.elem, fa.elem, c)
        } else if pa, ok := actual.(^Type_Partial_Array); ok {
            // Partial arrays coerce to slice views (`[]$T` ← [..N]T), so
            // they drive slice-shaped inference too. This is what lets the
            // generic slice_add serve `&s + "lit"` — string literals are
            // partial arrays of utf8.
            infer_type_params(subst, t.elem, pa.elem, c)
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

// Build the body-check env for a monomorphized function — the SAME two-layer
// shape as a regular fun (check_scope_body): the mono fun IS the defs layer (kind
// .Fun, the enclosing-callable marker), and a .Block body chains under it. Effects:
//  - enclosing_callable_scope / enclosing_return_types find the MONO FUN, not the
//    call site (the latent bug this fixes — a mono body had no marker at all),
//  - locals resolve via scope_local_lookup and STOP at the fun boundary (no
//    call-site leak; the old raw .Struct shadow scope hid this by not being a
//    .Block at all),
//  - scope_is_callable(fun) recognises the layer just like a real fun's ns layer.
// The mono fun chains to the call-site scope so module-level names resolve exactly
// as before; fun.types/functions are empty, so interposing it adds no resolvable
// names (resolution-preserving).
mono_body_env :: proc(env: ^Type_Scope, fun: ^Type_Scope) -> ^Type_Scope {
    if fun.parent_scope == nil { fun.parent_scope = env }
    return type_env_block_child(fun)
}

// Instantiate a generic function template with concrete type substitutions.
// Registers a ^Type_Scope in checked.functions under the mangled name.
instantiate_generic_fun :: proc(c: ^Checker, tmpl: ^Generic_Template, subst: ^map[string]Type, mangled: string, env: ^Type_Scope) {
    ast := tmpl.ast
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)

    // Build concrete function type
    fun_type := new(Type_Scope)
    fun_type.kind = .Fun
    fun_type.home_package = tmpl.home_package
    fun_type.ast = ast  // template AST — structural escape check is clone-invariant
    // Its name now (its definitions are named inside it: each instance's its
    // own — `twice__i64_help`).
    fun_type.name = make_flat_name(tmpl.home_package, mangled)
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

    // Body-check scope: two-layer (defs layer = fun_type, .Block body) — see
    // mono_body_env.
    child := mono_body_env(env, fun_type)

    // Bind regular params with their concrete types
    for tp, i in ast.typed_params {
        if i < len(fun_type.params) {
            type_env_set(child, tp.name, fun_type.params[i].type_)
        }
    }

    // Bind generic type param names so they resolve in the body
    // (e.g., `x : T = ...` inside a generic function should know T is int)
    for name, t in subst {
        type_env_set(child, name, t)
    }

    // Set active type params so resolve_type_expr can find them during body checking
    saved_type_params := c.type_params
    c.type_params = {}
    for name, t in subst {
        c.type_params[name] = t
    }

    // Clone the body and defs so each monomorphization gets independent type
    // annotations; defs and body are disjoint (split mode).
    cloned_body := clone_stmts(ast.body)
    cloned_defs := clone_stmts(ast.defs)

    // Type-check the cloned function body, building its graph (its
    // definitions: its own copies).
    f: ^Graph_Fuse
    if c.gb != nil { f = graph_fuse_begin(c.gb, fun_type, ast, cloned_body[:], .Synthetic) }
    // (Its nested funs and structs registered under it, as a fun's are
    // before its body — check_scope_body; its constants bind as checked.)
    nested: [dynamic]Stmt
    defer delete(nested)
    for d in cloned_defs {
        if _, is_scope := d.(^Stmt_Scope); is_scope { append(&nested, d) }
    }
    if len(nested) > 0 { register_scope_defs(c, fun_type, &fun_type.sd, nested) }
    check_scope(c, cloned_body, child, scope_defs = cloned_defs)
    // (Its nested funs, for codegen: extracted as a fun's are.)
    if c.checked != nil && len(nested) > 0 { extract_scope_fun_defs(c.checked, nested, fun_type, tmpl.home_package) }
    if f != nil { fuse_end(c, f) }

    // Store cloned body for codegen extraction
    c.table.mono_fun_bodies[mangled] = cloned_body

    // Restore type params
    c.type_params = saved_type_params
}

// Auto-monomorphize a concrete function when called with a structurally-compatible but
// differently-instantiated generic struct (e.g. add_string(^String(256)) called with ^String(64)).
// Returns (flat mangled name, specialized fn Type_Scope), or ("", nil) when no
// specialization is needed.
auto_monomorphize_for_struct :: proc(c: ^Checker, fn_name: string, ft: ^Type_Scope, actual_types: []Type, env: ^Type_Scope) -> (string, ^Type_Scope) {
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
    if !needs_spec { return "", nil }

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
        return make_flat_name(home, mangled), c.table.mono_cache[mangled]
    }

    // Look up the original function's AST
    home := resolve_fn_home(c, env,fn_name)
    ast, ast_ok := c.table.fun_asts[fn_name]
    if !ast_ok || ast == nil { return "", nil }

    // Build concrete function type with actual param types
    mono_ft := new(Type_Scope)
    mono_ft.kind = .Fun
    mono_ft.home_package = home
    mono_ft.ast = ast  // template AST — structural escape check is clone-invariant
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

    // Body-check scope: two-layer (defs layer = mono_ft, .Block body) — see
    // mono_body_env.
    child := mono_body_env(env, mono_ft)
    for tp, i in ast.typed_params {
        if i < len(mono_ft.params) {
            type_env_set(child, tp.name, mono_ft.params[i].type_)
        }
    }
    cloned_body := clone_stmts(ast.body)
    cloned_defs := clone_stmts(ast.defs)
    // (Its graph is the builder's: it builds the template's body for it.)
    outer := fuse_suspend(c)
    check_scope(c, cloned_body, child, scope_defs = cloned_defs)
    fuse_resume(c, outer)
    c.table.mono_fun_bodies[mangled] = cloned_body

    return make_flat_name(home, mangled), mono_ft
}

// Check a call to a generic function: infer type params, instantiate, rewrite call.
check_generic_call :: proc(c: ^Checker, e: ^Expr_Call, tmpl: ^Generic_Template, args: []Expr, env: ^Type_Scope, want := Fuse_Want.None, w := Written.Explicit) -> Type {
    // Built: each argument as it is checked, at its param's type once the
    // instance is known (graph_fuse_as, as a dispatch's), then the call.
    b := fusing(c) if want != .None else nil
    if b != nil && want == .Place {
        fuse_fail(c, "a call's place")
        b = nil
    }
    vals: [dynamic]Operand
    defer delete(vals)
    as_: [dynamic]int
    defer delete(as_)
    array_values: [dynamic]bool   // (an argument that is an array's value, no place)
    defer delete(array_values)
    literal_args: [dynamic]Fuse_Literal_Arg
    defer delete(literal_args)
    // Step 1: Check all argument types
    arg_types: [dynamic]Type
    defer delete(arg_types)
    for arg, i in args {
        if b != nil && fusing(c) != nil {
            from := b.nodes
            t, r := fuse_expr(c, arg, env, .Either, w)
            append(&arg_types, t)
            if fusing(c) == nil { continue }
            _, is_literal := arg.(^Expr_Array)
            _, is_array := distinct_base(t).(^Type_Fixed_Array)
            if fuse_byte_index(arg) {
                fuse_fail(c, "bytes as a generic's argument")
                continue
            }
            v, k := graph_fuse_as(b, r.v, r.place, t, expr_span(arg)^, e.span, {})
            append(&vals, v)
            append(&as_, k)
            append(&array_values, is_array && !r.place)
            // (An array literal: built at its own type, retyped as its
            // param's once the instance is known.)
            if is_literal { append(&literal_args, Fuse_Literal_Arg{i, from, b.nodes, t}) }
        } else {
            append(&arg_types, check_expr(c, arg, env))
        }
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
        call_args_mut(e)^ = {}
        e.lowered_name = st.name
        e.resolved_func = Resolved_Func{name = st.name, callee = st}

        // Codegen needs an init function for the instantiated struct so the
        // call site has something to call. Type-position uses (e.g. `var
        // Array(byte, 256)`) inline default-init at the alloca and never
        // need this; expression-position calls do. Source-defined structs
        // get a Checked_Scope from extract_module_into_checked; instantiated
        // generics need one synthesised here. Codegen's is_pure_struct_init
        // path emits the body (apply field defaults, ret void).
        if c.checked != nil {
            if _, exists := c.checked.functions[st.name]; !exists {
                st.home_package = tmpl.home_package
                st.body = tmpl.ast.body
                st.ast = tmpl.ast
                st.origin = Origin_Source{}
                st.body_span = tmpl.ast.span
                populate_cg_signature(st)   // Self prepended for .Struct
                c.checked.functions[st.name] = st
                append(&c.checked.function_order, st.name)
            }
        }

        return check_pure_struct_construction(c, e, st, env)
    }

    // Also try to infer from the return type context if needed (future enhancement)

    // Step 3: Verify all type params were resolved
    for param in tmpl.generic_params {
        if subst[param.name] == nil {
            check_error(c, e.span, TYPE_COULD_INFER_TYPE_PARAMETER_CALL, param.name, call_name(e))
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
        check_error(c, e.span, TYPE_FAILED_INSTANTIATE_GENERIC_FUNCTION, call_name(e))
        return Type_Error{}
    }
    fun_type, fun_ok := fun_type_raw.(^Type_Scope)
    if !fun_ok {
        check_error(c, e.span, TYPE_FAILED_INSTANTIATE_GENERIC_FUNCTION, call_name(e))
        return Type_Error{}
    }
    // Generic constructor call: e.g. Pair(int)(1, 2)
    if len(fun_type.fields) > 0 && len(fun_type.params) == 0 {
        if b != nil { fuse_fail(c, "a generic construction") }
        return check_pure_struct_construction(c, e, fun_type, env)
    }

    // Step 7: Rewrite the call to target the mangled name
    e.lowered_name = mangled
    fn_flat_name := make_flat_name(tmpl.home_package, mangled)
    e.resolved_func = Resolved_Func{name = fn_flat_name, callee = fun_type}

    // Step 8: Validate arg count matches concrete param count
    if len(args) != len(fun_type.params) {
        check_error(c, e.span, TYPE_EXPECTS_ARGUMENT, tmpl.name, len(fun_type.params), len(args))
    }

    if fb := fusing(c); fb != nil && b != nil {
        for k, i in as_ {
            if k >= 0 { fb.fuse.widens[k].sig, fb.fuse.widens[k].param = fun_type, i }
        }
        for la in literal_args {
            if la.arg >= len(fun_type.params) { continue }
            pt := fun_type.params[la.arg].type_
            if graph_aggregate(pt) && pt != la.t { graph_fuse_retype_literal(fb, la.from, la.to, pt) }
        }
        if fuse_views_value(fun_type, array_values[:]) {
            fuse_fail(c, "an array's value viewed by a generic's param")
        } else {
            fuse_done(c, {graph_call_op(fb, .Call, w, e.span, fun_type, fn_primary_return(fun_type), ..vals[:]), 0})
        }
    }
    return fn_primary_return(fun_type)
}

// ---------------------------------------------------------------------------
// Type comparison
// ---------------------------------------------------------------------------

// Recognize the built-in cstring type. (Historically this also matched a
// stdlib `distinct ^utf8` decl by flat name — that decl is gone; the type
// is fully built-in again and Type_CString is its only spelling.)
is_cstring :: proc(t: Type) -> bool {
    _, ok := t.(Type_CString)
    return ok
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

// Through a pointer there is no array→slice decay: the pointee must already
// have the target's memory layout. A fixed array `[N]T` is N inline elements
// with NO {ptr,len,cap} header, so `^[N]T` cannot stand in for `^[]T` or
// `^[..M]T` — doing so let `&fixed + x` bind to core's `slice_add` (param
// `^[]$T`) and then read a header off raw inline elements. Returns true for
// that mismatch: exactly one side a fixed array, the other a header-shaped
// buffer (slice / partial array). Fixed↔fixed and slice↔partial (both
// consistent layouts) are NOT mismatches and keep flowing.
ptr_pointee_layout_mismatch :: proc(a, b: Type) -> bool {
    _, a_fixed := a.(^Type_Fixed_Array)
    _, b_fixed := b.(^Type_Fixed_Array)
    if a_fixed == b_fixed { return false }
    other := a
    if a_fixed { other = b }
    #partial switch _ in other {
    case ^Type_Slice, ^Type_Partial_Array:
        return true
    }
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
        // utf8 (incl. char literals) is compatible with i8/u8
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
        if is_cstring(b) { return true }
        // utf8 partial arrays are TYPE-compatible so string LITERALS (typed
        // [..tier]utf8) pass free — their rodata globals carry the \0. The
        // call-site argument check restricts the implicit path to literal
        // EXPRESSIONS; every runtime string goes through the explicit
        // `cstring(s)` constructor (copy + terminator), so codegen never
        // converts a runtime value implicitly.
        if pa, ok := b.(^Type_Partial_Array); ok {
            if _, utf8_ok := pa.elem.(Type_Utf8); utf8_ok { return true }
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
        // No array→slice decay through a pointer: ^[N]T must not satisfy
        // ^[]T / ^[..M]T (a fixed array has no slice header to alias).
        if ptr_pointee_layout_mismatch(va.elem, vb.elem) { return false }
        return types_equal(va.elem, vb.elem)
    case ^Type_Scope:
        vb, ok := b.(^Type_Scope)
        if !ok { return false }
        // Interned nominal identity: every logical named type resolves to one
        // canonical ^Type_Scope, so pointer equality IS type equality — no flat
        // name string needed. (Verified: zero name-equal-but-pointer-different
        // comparisons across the whole test suite + Pounce.)
        if va == vb { return true }
        // Two distinct named types are never equal.
        if va.name != "" && vb.name != "" { return false }
        // Structural: compare params + return types (for anonymous/callable funs,
        // which carry no nominal name).
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
        // importantly `fa : [N]utf8 = "lit"` after the literal-type
        // change made literals partial.
        if pa, pa_ok := b.(^Type_Partial_Array); pa_ok {
            return buffer_elem_compatible(va.elem, pa.elem)
        }
        vb, ok := b.(^Type_Fixed_Array)
        if !ok { return false }
        return buffer_elem_compatible(va.elem, vb.elem)
        // Note: we don't compare size here — arrays of same elem type are compatible
        // Size checking is done at assignment/init time
    case ^Type_Slice:
        // By-value fixed-array -> slice decay: `[N]T` materialises a slice
        // header {ptr=&arr[0], len=cap=N} — honest, since [N]T is exactly N
        // elements (e.g. Mesh_Data{primitive_quad()}). The source is hoisted to
        // a scope-lived local, and lifetime past that scope is policed by
        // return-escape analysis. NOT allowed THROUGH A POINTER (^[N]T has no
        // header to alias) — that gate is ptr_pointee_layout_mismatch above,
        // which short-circuits before this case is ever reached for ^[]T.
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return buffer_elem_compatible(va.elem, fa.elem)
        }
        if pa, pa_ok := b.(^Type_Partial_Array); pa_ok {
            return buffer_elem_compatible(va.elem, pa.elem)
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
            return buffer_elem_compatible(va.elem, sl.elem)
        }
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return buffer_elem_compatible(va.elem, fa.elem)
        }
        if pa, ok := b.(^Type_Partial_Array); ok {
            // Partial-to-partial interop is by header shape: same elem
            // type. Size doesn't gate compatibility because params are
            // passed by header pointer (cap is read at runtime);
            // assignment paths in codegen are responsible for fitting
            // source bytes into dest storage.
            return buffer_elem_compatible(va.elem, pa.elem)
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
    case Type_Utf8:         return "utf8"
    case Type_Byte:         return "byte"
    case ^Type_Ptr:         return fmt.tprintf("^%s", type_name(v.elem))
    case ^Type_Scope:
        if v.name != "" {
            return v.source_name if v.source_name != "" else v.name
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
        return fmt.tprintf("[%d]%s", v.size, type_name(v.elem))
    case ^Type_Slice:
        return fmt.tprintf("[]%s", type_name(v.elem))
    case ^Type_Partial_Array:
        return fmt.tprintf("[..%d]%s", v.size, type_name(v.elem))
    case ^Type_Enum:        return v.source_name if v.source_name != "" else v.name
    case ^Type_Union:       return v.source_name if v.source_name != "" else v.name
    case ^Type_Distinct:
        disp := v.source_name if v.source_name != "" else v.name
        if v.is_alias { return disp }
        return fmt.tprintf("distinct %s", disp)
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
// Quantized capacity tier for an inferred string-literal type: the smallest
// of 64/256/1024 STRICTLY larger than the byte length, so a `:=` copy always
// has headroom for appends and the cstring terminator. Three types cover
// every literal; giants (≥1024) fall back to exact size — rare, and usually
// passed straight to a call rather than bound.
string_literal_cap :: proc(byte_len: int) -> int {
    if byte_len < 64 { return 64 }
    if byte_len < 256 { return 256 }
    if byte_len < 1024 { return 1024 }
    return byte_len
}

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

// True when `t` is an integer-family operand a wrapping op (`+%`/`-%`/`*%`)
// accepts: any signed/unsigned int, byte/utf8, enum tag, an untyped int literal
// (which adopts the other operand's width), or a distinct over one. Floats —
// including untyped float literals — and non-numerics are rejected. Error/any
// pass through so a wrapping op on already-errored operands doesn't double-report.
is_wrap_operand :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(resolve_infer(t)) {
    case Type_Infer_Int:       return true
    case Type_Numeric:         return v.kind != .Float
    case Type_Byte, Type_Utf8: return true
    case ^Type_Enum:           return true
    case Type_Error, Type_Any: return true
    }
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
    case Type_Byte, Type_Utf8:  return 8, .Unsigned, true
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
    case Type_Byte, Type_Utf8:        return true
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

// True when t is array-shaped: a fixed array, slice, or partial array. On the
// byte-target assignment path this tells a content copy (`buf[lo:hi] = src` —
// copy the bytes src points AT) from a reinterpret span write
// (`buf[lo:hi] = structVal` — blit the value's own bytes).
is_array_shaped :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(t) {
    case ^Type_Fixed_Array, ^Type_Slice, ^Type_Partial_Array: return true
    }
    return false
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

// --- byte reinterpretation: no slice headers --------------------------------
// Reading a value out of a byte buffer (`h : Head = bytes[off]`) or writing one
// into it (`bytes[off] = v`) reinterprets raw bytes. A SLICE header can't take
// part: its len/cap are exactly what bounds checks trust, so one taken from
// bytes (a file's, typically) silently defeats them — the recurring bug of this
// family (ba666db, 72dbe81, 870972a, 471f615, 470f3c0 each patched one shape).
// A partial array is fine when its elements are: its header is stamped by the
// compiler after the copy, never taken from bytes. Pointers are deliberately
// allowed: in-process memory legitimately holds them (Arena_Debug keeps its
// AllocHeader's name/span pointers in the arena's own bytes), and a raw pointer
// is raw territory either way. Every assignment-like site asks check_byte_flow /
// check_byte_write, so the rule lives here once.

// Why `t` can't be reinterpreted from/to bytes — the first slice in its layout —
// or "" when it can.
byte_slice_reason :: proc(c: ^Checker, t: Type, path: string = "") -> string {
    #partial switch v in distinct_base(t) {
    case ^Type_Slice:
        if path == "" { return "a slice is a (len, cap, ptr) header, not data" }
        return fmt.tprintf("`%s` is a slice", path)
    case ^Type_Fixed_Array:
        return byte_slice_reason(c, v.elem, fmt.tprintf("%s[i]", path))
    case ^Type_Partial_Array:
        return byte_slice_reason(c, v.elem, fmt.tprintf("%s[i]", path))
    case ^Type_Union:
        for vname, sname in v.variant_structs {
            if st, ok := c.table.structs[sname]; ok {
                if r := byte_slice_reason(c, st, path == "" ? vname : fmt.tprintf("%s.%s", path, vname)); r != "" { return r }
            }
        }
    case ^Type_Scope:
        sd := as_struct_body(v)
        if sd == nil { return "" }
        for &f in sd.fields {
            if f.name == "__tag" || f.name == "__pad" { continue }
            if r := byte_slice_reason(c, f.type_, path == "" ? f.name : fmt.tprintf("%s.%s", path, f.name)); r != "" { return r }
        }
    }
    return ""
}

Byte_Flow :: enum { None, View, Read }

// The one rule for a byte buffer — or a range or element of one — flowing into
// a destination of type `dest`:
//   - a RANGE into a slice is a VIEW of those bytes, so its elements must be of
//     the byte family — byte / utf8 / u8 / i8 (a view as any other element type
//     is spelled `slice([:n]T, &bytes[lo])`);
//   - anything else is a READ of sizeof(dest) bytes, which can't hold a slice header.
// Reports its own errors. Callers apply their byte-read size rules for .Read
// and treat .View / .None as an ordinary assignment.
check_byte_flow :: proc(c: ^Checker, dest: Type, value: Expr, val_type: Type, span: Span) -> Byte_Flow {
    flow := byte_flow(dest, value, val_type)
    #partial switch flow {
    case .View:
        sl := distinct_base(dest).(^Type_Slice)
        if !is_byte_sized_memory_type(sl.elem) {
            en := type_name(sl.elem)
            check_error(c, span, TYPE_BYTE_VIEW_WIDE_ELEM, type_name(dest), en, en)
        }
    case .Read:
        if _, to_slice := distinct_base(dest).(^Type_Slice); to_slice {
            check_error(c, span, TYPE_BYTE_READ_SLICE_BY_INDEX, type_name(dest)) // `s : []T = bytes[i]`
        } else if why := byte_slice_reason(c, dest); why != "" {
            check_error(c, span, TYPE_BYTE_READ_REFERENCE, type_name(dest), why)
        }
    }
    return flow
}

// The rule above without its diagnostics: which flow `value` makes into
// `dest`. Shared with the program graph (a Read is its `byte read` operation).
byte_flow :: proc(dest: Type, value: Expr, val_type: Type) -> Byte_Flow {
    index_read := is_byte_buffer_index_read(value)
    if !index_read && !is_byte_buffer(val_type) { return .None }
    if _, to_slice := distinct_base(dest).(^Type_Slice); to_slice && !index_read { return .View }
    return .Read
}

// A value written into a byte buffer (`bytes[off] = v`, `bytes[lo:hi] = v`) is
// stored as its raw bytes, so it can't hold a slice header.
check_byte_write :: proc(c: ^Checker, val_type: Type, span: Span) {
    if why := byte_slice_reason(c, val_type); why != "" {
        check_error(c, span, TYPE_BYTE_WRITE_REFERENCE, type_name(val_type), why)
    }
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
    if !is_byte_buffer(src_type) { return }
    addr.byte_view_size = checker_type_byte_size(pt.elem)
    addr.byte_view_type = pt.elem
    // Built: the address is the view's, of the bytes as that type.
    if b := fusing(c); b != nil {
        if ops, built := c.byte_addrs[rawptr(addr)]; built {
            graph_fuse_view(b, {ops[1], 0}, pt.elem, idx.is_big_endian, addr.span)
            b.g.type_[ops[0]] = new_clone(Type_Ptr{elem = pt.elem})
        }
    }
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
    case Type_Bool, Type_Utf8, Type_Byte:
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
        // Interned identity: same logical type ⟺ same Scope_Body pointer.
        return sa == sb
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

// Sized-slice declarations, lowered into s.lowered_type / s.lowered_cap. The
// parser reads `Name(args)` greedily as a generic instantiation, so when Name
// is not a generic, the single argument is a capacity:
//   `name : String2(N)` on a distinct slice alias → type String2, cap N
//   `name : []Mesh_Data(12)`                       → type []Mesh_Data, cap 12
// and a bare distinct slice alias with a default cap, `s : String` where
// `String :: distinct [,0]utf8(128)`, picks up that default. Idempotent: each
// case reads the lowered form, which no longer matches once lowered.
lower_sized_slice :: proc(c: ^Checker, s: ^Stmt_Decl, env: ^Type_Scope) {
    // The capacity a single generic-style argument stands for, if it is one.
    arg_cap :: proc(arg: Type_Expr) -> Expr {
        #partial switch a in arg {
        case Type_Const_Value:
            num := new(Expr_Number)
            num.int_value = i128(a.value)
            num.value = f64(a.value)
            num.span = a.span
            return num
        case Type_Const_Expr:
            return a.expr
        }
        return nil
    }
    distinct_slice :: proc(c: ^Checker, name: string, env: ^Type_Scope) -> (^Type_Distinct, bool) {
        // Resolve the bare name through includes / aliases to the flat key
        // used in distinct_types (e.g. "String2" -> "test_string_String2").
        flat := resolve_type_name(c, name, "", env)
        if flat == "" { flat = name }
        dt, found := c.table.distinct_types[flat]
        if !found { return nil, false }
        _, is_slice := dt.base_type.(^Type_Slice)
        return dt, is_slice
    }

    if decl_cap(s) != nil { return }
    #partial switch t in decl_type(s) {
    case ^Type_Generic_Instance:
        if len(t.type_args) != 1 { return }
        if _, is_generic := c.table.generic_templates[t.name]; is_generic { return }
        if _, ok := distinct_slice(c, t.name, env); !ok { return }
        if cap := arg_cap(t.type_args[0]); cap != nil {
            s.lowered_type = Type_Name{name = t.name, span = t.span}
            s.lowered_cap = cap
        }
    case ^Type_Slice_Expr:
        gi, gi_ok := t.elem.(^Type_Generic_Instance)
        if !gi_ok || len(gi.type_args) != 1 { return }
        if _, is_generic := c.table.generic_templates[gi.name]; is_generic { return }
        if cap := arg_cap(gi.type_args[0]); cap != nil {
            lowered := new_clone(t^)
            lowered.elem = Type_Name{name = gi.name, span = gi.span}
            s.lowered_type = lowered
            s.lowered_cap = cap
        }
    }
    // A distinct slice alias, bare or just lowered, without a capacity yet.
    if tn, ok := decl_type(s).(Type_Name); ok && decl_cap(s) == nil {
        if dt, is_slice := distinct_slice(c, tn.name, env); is_slice && dt.default_cap_expr != nil {
            s.lowered_cap = dt.default_cap_expr
        }
    }
}

// Shape shortcut: `p : Foo(Bar(args))` lowers to `p : Foo(Bar)` plus a
// synthetic `{ field = Bar(args) }` struct literal — s.lowered_type and
// s.lowered_init; the source declaration is untouched. Fires only when:
//   - The Stmt_Decl's type annotation is a Type_Generic_Instance.
//   - The template is a known generic struct.
//   - At a slot with a `~T` shape constraint, the type-arg is a
//     Type_Const_Expr wrapping an Expr_Call.
//   - The user hasn't supplied an init.
// Idempotent — once lowered, re-running is a no-op. Multiple
// shape-constrained slots stack their bindings into one literal. The literal
// holds a copy of each call: the source call stays where it was written, and
// a cloned declaration lowers into nodes of its own.
desugar_shape_shortcut :: proc(c: ^Checker, s: ^Stmt_Decl) {
    if c == nil { return }
    if s.lowered_type != nil { return }
    if len(s.init_values) != 0 { return }
    gi, gi_ok := s.type_expr.(^Type_Generic_Instance)
    if !gi_ok { return }
    tmpl, tmpl_ok := c.table.generic_templates[gi.name]
    if !tmpl_ok { return }
    lowered: ^Type_Generic_Instance   // gi with each bound slot's call replaced by its type
    lit: ^Expr_Struct_Literal
    for arg_i in 0..<len(gi.type_args) {
        if arg_i >= len(tmpl.generic_params) { break }
        param := tmpl.generic_params[arg_i]
        if param.shape_constraint == "" { continue }
        ce, ce_ok := gi.type_args[arg_i].(Type_Const_Expr)
        if !ce_ok { continue }
        call, call_ok := ce.expr.(^Expr_Call)
        if !call_ok { continue }
        tmpl_fields := extract_fields_from_body(tmpl.ast.body)
        bound_any := false
        for f in tmpl_fields {
            tn, tn_ok := f.type_expr.(Type_Name)
            if !tn_ok || tn.name != param.name { continue }
            if lit == nil {
                lit = new(Expr_Struct_Literal)
                lit.span = s.span
            }
            append(&lit.fields, Struct_Field{name = f.name, value = clone_expr(call)})
            bound_any = true
        }
        if bound_any {
            if lowered == nil {
                lowered = new_clone(gi^)
                lowered.type_args = {}
                for a in gi.type_args { append(&lowered.type_args, a) }
            }
            lowered.type_args[arg_i] = Type_Name{name = call_name(call), span = ce.span}
        }
    }
    if lit != nil {
        s.lowered_type = lowered
        append(&s.lowered_init, lit)
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
    case Type_Utf8, Type_Byte, Type_Bool:
        return 1
    case ^Type_Slice:      return slice_header_bytes
    case ^Type_Partial_Array:
        // { len, cap, ptr, [N x T] } — slice_header_bytes for the header,
        // followed by N * sizeof(elem) backing storage.
        return slice_header_bytes + v.size * checker_type_byte_size(v.elem)
    case ^Type_Scope:      return checker_struct_byte_size(v)
    case ^Type_Fixed_Array:
        return v.size * checker_type_byte_size(v.elem)
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

// ---------------------------------------------------------------------------
// Storage routing — two operations, one policy
// ---------------------------------------------------------------------------
// Every value's size is knowable at compile time (no runtime-sized types), so
// the whole "stack vs arena" decision reduces to two operations:
//
//   1. Find the value's size       — checker_type_byte_size, above. It returns
//      the TOTAL inline footprint: struct padding, fixed-array storage, and
//      partial-array backing are all counted; a slice is just its header (its
//      backing is a separate allocation, routed on its own).
//   2. Route it to the right store — routes_to_arena, below.
//
// Both the type checker (check_storage_sizes — the early "declare an allocator"
// error) and codegen (alloca vs arena_bump) gate on routes_to_arena, so the
// threshold lives in exactly one place and the two stages can't drift.

// Values at or above this many bytes route through the scope arena, never the
// stack. The single source of truth for "big".
ARENA_THRESHOLD :: 1024

routes_to_arena :: proc(t: Type) -> bool {
    return checker_type_byte_size(t) >= ARENA_THRESHOLD
}

// Check if a variable is defined at global (root) scope.
// Returns true for top-level variables, false for locals and parameters.
is_global_var :: proc(c: ^Checker, name: string) -> bool {
    if c.table.root_env == nil { return false }
    _, in_root := scope_defines(c.table.root_env, name)
    return in_root
}

// Check if a variable name is a function parameter (walks env chain).
// Is `name` a parameter of the function/ctor whose body we're in? Derived from
// the durable scope (the enclosing callable's params) rather than a per-env flag
// — no closures, so the nearest callable IS the one that owns the params.
is_param :: proc(env: ^Type_Scope, name: string) -> bool {
    ft := enclosing_callable_scope(env)
    if ft == nil { return false }
    for p in ft.params { if p.name == name { return true } }
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
is_immutable_param :: proc(env: ^Type_Scope, name: string) -> bool {
    if !is_param(env, name) { return false }
    t, ok := type_env_get(env, name)
    if !ok { return false }
    base := distinct_base(t)
    if _, is_ptr := base.(^Type_Ptr); is_ptr { return false }
    // Passed by address (an immutable pointer to the caller's storage), so a
    // write would land in the caller's value.
    if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 { return true }
    #partial switch _ in base {
    case ^Type_Union, ^Type_Slice, ^Type_Fixed_Array, ^Type_Partial_Array:
        return true
    }
    return false
}

// Walk an assignment LHS down to its root identifier. Returns (name, true) if
// the write lands on an immutable param's storage WITHOUT crossing a pointer
// (which would shift the write to the pointed-to memory, not the param).
write_root_immutable_param :: proc(e: Expr, env: ^Type_Scope) -> (name: string, ok: bool) {
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

// The constant a write target or `&` operand is rooted at: `K.a`, `K.b[i]`,
// `mod.K.a`. A constant is a value — codegen reads its fields from storage it
// builds per function, and a write would silently change what later reads
// see. Runs after the path is checked (the resolver stamps constants on it).
// Crossing a pointer ends the search: what it points at isn't the constant.
// A function-local constant isn't stamped; it's known by name (no variable
// may shadow a constant, so the name is unambiguous).
write_root_constant :: proc(c: ^Checker, e: Expr) -> (name: string, ok: bool) {
    cur := e
    for {
        inner: Expr
        #partial switch v in cur {
        case ^Expr_Field_Access:
            if rc, is_const := v.resolved.(Resolved_Constant); is_const && rc.value_expr != nil {
                return v.field, true
            }
            inner = v.expr
        case ^Expr_Index: inner = v.expr
        case ^Expr_Slice: inner = v.expr
        case ^Expr_Ident:
            if rc, is_const := v.resolved.(Resolved_Constant); is_const && rc.value_expr != nil {
                return v.name, true
            }
            return v.name, v.name in c.table.constants
        case:
            return "", false
        }
        if _, is_ptr := distinct_base(expr_type(inner)).(^Type_Ptr); is_ptr { return "", false }
        cur = inner
    }
}

// Solidify inferred types to their defaults (for := variable declarations)
solidify_type :: proc(t: Type) -> Type {
    rt := resolve_infer(t)
    if _, ok := rt.(Type_Infer_Int); ok { return Type_Numeric{kind = .Signed, bits = 64} }
    if _, ok := rt.(Type_Infer_Float); ok { return Type_F64{} }
    // An array of untyped elements (`[1, 2, 3]` held as itself): its storage
    // needs a width — the elements' default.
    if fa, ok := rt.(^Type_Fixed_Array); ok && is_infer(fa.elem) {
        return new_clone(Type_Fixed_Array{size = fa.size, elem = solidify_type(fa.elem), index_type = fa.index_type})
    }
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

// Whether a constant's value expression is a float literal — drives whether a
// Resolved_Constant lowers as a float (math.PI) or an integer at codegen.
const_is_float :: proc(expr: Expr) -> bool {
    if num, n_ok := expr.(^Expr_Number); n_ok {
        return num.is_float
    }
    if un, u_ok := expr.(^Expr_Unary); u_ok && un.op == .Minus {
        if num, num_ok := un.operand.(^Expr_Number); num_ok {
            return num.is_float
        }
    }
    return false
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
    check_value_range(c, val, i_val, target, span)
}

// Check that a constant's value fits the target type's range (as an integer,
// i_val; as a float, val).
check_value_range :: proc(c: ^Checker, val: f64, i_val: i128, target: Type, span: Span) {
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
infer_param_type_from_default :: proc(c: ^Checker, value: Expr, env: ^Type_Scope) -> Type {
    if n, ok := value.(^Expr_Number); ok && !n.is_float {
        return slice_header_width_type
    }
    return infer_field_type_from_default(c, value, env)
}

// Resolve a callable parameter's declared type — the single cascade shared by
// every registration path (register_type_names, register_and_check_declarations,
// register_scope_defs):
//   - explicit `p: T`       → resolve the annotation
//   - untyped with default  → infer from the default value
//   - neither               → Type_Error (an un-annotated, un-defaulted param)
// An untyped numeric default seeds a deferred inference cell instead of
// solidifying to i64 right now, so the param adopts the width it's used at in the
// body — exactly like a `:=` local. This applies to struct CONSTRUCTORS too: a
// parameterized struct has a body (its field initializers) that uses the param,
// so `Grid :: struct(size := 16) { per_row : i32 = size }` settles size at i32
// rather than rejecting an i64-into-i32 narrowing. solidify_param_defaults freezes
// the cell back into the signature once the body is checked.
resolve_param_type :: proc(c: ^Checker, tp: Scope_Binding, env: ^Type_Scope, span: Span) -> Type {
    if tp.type_expr != nil {
        return resolve_type_expr(tp.type_expr, c, span, env = env)
    }
    if tp.default_value != nil {
        if _, is_uninit := tp.default_value.(^Expr_Skip_Constructor); is_uninit {
            check_error(c, span, TYPE_PARAM_TYPE_SKIP_CONSTRUCTOR_REQUIRES, tp.name, tp.name)
            return Type_Error{}
        }
        if n, n_ok := tp.default_value.(^Expr_Number); n_ok && !n.is_float {
            cell := new(Infer_Cell)
            cell.name = tp.name
            cell.span = span
            return Type_Infer_Int{cell = cell}
        }
        return infer_param_type_from_default(c, tp.default_value, env)
    }
    return Type_Error{}
}

// Freeze a callable's deferred default-param cells once its body is checked.
// Each untyped numeric default seeded an Infer_Cell (resolve_param_type); the
// body has since pinned it to the width it's used at (arithmetic against a sized
// operand, an argument, an assignment, a return, a field initializer). Resolve
// that to a concrete type and write it back into the signature, so callers and
// codegen (extract_checked_scope) never see an open cell. A FUNCTION param that
// flowed into no concrete context falls back to the function's sole numeric
// return type (the int↔float guard lives in coerce_deferred), then to i64 via
// solidify_type. Constructors return Self, not a scalar, so they skip that
// fallback — an unused constructor param just lands on i64.
solidify_param_defaults :: proc(c: ^Checker, ft: ^Type_Scope) {
    ret_fallback: Type
    if ft.kind == .Fun && len(ft.return_types) == 1 {
        ret_fallback = resolve_infer(ft.return_types[0])
    }
    for i in 0 ..< len(ft.params) {
        cell := infer_cell_of(ft.params[i].type_)
        if cell == nil { continue }
        if ret_fallback != nil && infer_root(cell).resolved == nil {
            coerce_deferred(c, ft.params[i].type_, ret_fallback, cell.span)
        }
        ft.params[i].type_ = solidify_type(ft.params[i].type_)
    }
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
    case "utf8": return Type_Utf8{}, true
    case "bool": return Type_Bool{}, true
    }
    return nil, false
}

// Strict same-type test for the redundant-cast warning. NOT types_equal —
// that's a COMPATIBILITY test (it reports Type_Infer_Int as equal to every
// numeric, floats included), which would flag `f32(SOME_INT_CONST)` as an
// identity when it's really an int→float conversion. This is true only when
// `src` is ALREADY the exact concrete type the cast produces:
//   - infer/untyped operands → false: the cast is the literal's type ascription
//     (`CACHE_MAGIC :: u32(0x...)`, `f32(RASTER_QUAD_STEPS)` where the const is
//     an untyped int), and a pinned `:=` binding has already resolved to a
//     concrete type so it still qualifies.
//   - distinct operands → false: `i32(some_distinct)` is a real unwrap.
//   - the same-width byte/u8/utf8 trio stays distinct (nominally different).
cast_target_same_as_operand :: proc(src_raw: Type, target: Type) -> bool {
    src := resolve_infer(src_raw)
    if is_infer(src) { return false }
    if _, ok := src.(^Type_Distinct); ok { return false }
    #partial switch t in target {
    case Type_Numeric:
        if s, ok := src.(Type_Numeric); ok { return s.kind == t.kind && s.bits == t.bits }
        return false
    case Type_F64:
        if _, ok := src.(Type_F64); ok { return true }
        if s, ok := src.(Type_Numeric); ok { return s.kind == .Float && s.bits == 64 }
        return false
    case Type_Utf8:
        _, ok := src.(Type_Utf8)
        return ok
    case Type_Bool:
        _, ok := src.(Type_Bool)
        return ok
    }
    return false
}

// Infer a field's type from its default value without full check_expr
// (which would fail because the enclosing fun's params/locals aren't in scope yet).
// Handles: identifiers (constants/variables in env), number/string/bool literals,
// and calls to known struct constructors / functions with a return type.
infer_field_type_from_default :: proc(c: ^Checker, value: Expr, env: ^Type_Scope, ft: ^Type_Scope = nil) -> Type {
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
    // A module constant accessed as `Module.X` / `Self.X`: resolve via check_expr
    // to get its type (check_field_access does the constant lookup). Narrowed to
    // ACTUAL module constants — the flat key exists — so other field accesses keep
    // their existing lightweight-inference behavior.
    if fa, ok := value.(^Expr_Field_Access); ok {
        if qual, q_ok := fa.expr.(^Expr_Ident); q_ok {
            if _, found := c.table.constants[make_flat_name(qual.name, fa.field)]; found {
                return check_expr(c, value, env)
            }
            // `Kind.Big` — a variant of a named enum / union: the field is that
            // type (what check_field_access gives it).
            t, t_ok := type_env_get(env, qual.name)
            if !t_ok && c.current_package != "" {
                t, t_ok = type_env_get(env, make_flat_name(c.current_package, qual.name))
            }
            if t_ok {
                #partial switch v in t {
                case ^Type_Enum:  if fa.field in v.variants { return v }
                case ^Type_Union: if fa.field in v.tag_map { return v }
                }
            }
        }
    }
    // A typed literal (`[4]f32{0, 0, 0, 1}`) is its written type; the body
    // pass checks the values against it.
    if sl, ok := value.(^Expr_Struct_Literal); ok && sl.type_expr != nil {
        return resolve_type_expr(sl.type_expr, c, sl.span, env = env)
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
    // A bare string-literal default takes the same quantized tier as any
    // inferred literal binding (string_literal_cap — [..64]/[..256]/
    // [..1024]utf8). (Annotated string fields like `name : [..16]utf8 = ...`
    // take the type_expr branch instead.) Without this the field fell
    // through to Type_Any → i64.
    if s, ok := value.(^Expr_String); ok {
        pa := new(Type_Partial_Array)
        pa.size = string_literal_cap(len(s.value))
        pa.elem = Type_Utf8{}
        return pa
    }
    // Char literal default — an 8-bit character. Without this it fell through
    // to Type_Any → i64 (wrong width: a char field is i8, not i64).
    if _, ok := value.(^Expr_Char); ok {
        return Type_Utf8{}
    }
    if _, ok := value.(^Expr_Bool); ok {
        return Type_Bool{}
    }
    // Call expressions: look up the callee's Type_Scope in the env.
    //   struct constructor (kind=.Struct with params)  → the struct type itself
    //   function call       (kind=.Fun with returns)   → primary return type
    if call, ok := value.(^Expr_Call); ok && call_name(call) != "" {
        // Primitive cast: f32(x) → f32, i32(x) → i32. Must precede the env
        // lookup — the cast name isn't a function symbol, so the lookup would
        // miss and the proc would silently fall through to Type_Any.
        if ct, is_cast := cast_result_type(call_name(call)); is_cast {
            return ct
        }
        lookup := proc(env: ^Type_Scope, name: string) -> (Type, bool) {
            return type_env_get(env, name)
        }
        t, t_ok := lookup(env, call_name(call))
        if !t_ok && c.current_package != "" {
            t, t_ok = lookup(env, make_flat_name(c.current_package, call_name(call)))
        }
        if t_ok {
            if ft, ft_ok := t.(^Type_Scope); ft_ok {
                ensure_fun_signature(c, ft)  // pull the callee's returns on demand before reading them
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
        if call, call_ok := try_node.inner.(^Expr_Call); call_ok && call_name(call) != "" {
            t, t_ok := type_env_get(env, call_name(call))
            if !t_ok && c.current_package != "" {
                t, t_ok = type_env_get(env, make_flat_name(c.current_package, call_name(call)))
            }
            if t_ok {
                if fnt, fnt_ok := t.(^Type_Scope); fnt_ok {
                    ensure_fun_signature(c, fnt)  // pull the callee's returns on demand before reading them
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
    // Slice expressions: `view := buf[lo:hi]` — the field is a []elem view of
    // the source. Mirrors check_slice's result derivation (auto-deref ^[]T /
    // ^[N]T, element from slice / fixed array / partial array); bound checking
    // stays in the body pass. Without this the field fell through to Type_Any
    // and codegen panicked instead of diagnosing.
    if sl, ok := value.(^Expr_Slice); ok {
        base := infer_field_type_from_default(c, sl.expr, env, ft)
        if pt, pt_ok := base.(^Type_Ptr); pt_ok {
            inner := distinct_base(pt.elem)
            if _, inner_sl := inner.(^Type_Slice); inner_sl { base = inner }
            else if _, inner_fa := inner.(^Type_Fixed_Array); inner_fa { base = inner }
        }
        elem: Type
        if fa, fa_ok := base.(^Type_Fixed_Array); fa_ok { elem = fa.elem }
        else if bs, bs_ok := base.(^Type_Slice); bs_ok { elem = bs.elem }
        else if pa, pa_ok := base.(^Type_Partial_Array); pa_ok { elem = pa.elem }
        if elem != nil {
            result := new(Type_Slice)
            result.elem = elem
            return result
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
        if call, call_ok := td.source.(^Expr_Call); call_ok && call_name(call) != "" {
            t, t_ok := type_env_get(env, call_name(call))
            if !t_ok && c.current_package != "" {
                t, t_ok = type_env_get(env, make_flat_name(c.current_package, call_name(call)))
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

// Storage routing, applied uniformly at every local declaration: a value big
// enough to route through the arena (routes_to_arena) needs an allocator to
// route to. With none declared there's nowhere safe to put it, so error at the
// declaration — early and clear — for EVERY value kind (fixed array, partial
// array, struct, …), instead of letting a partial array silently stack-overflow
// or a struct trip a late codegen fatal. When an allocator IS declared this is a
// no-op here; codegen does the actual arena routing on the same predicate.
// Per-scope and top-level only — nested if/for/match bodies re-enter check_scope
// and get their own pass.
check_storage_sizes :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Scope) {
    // `mara ask` only reads source and walks graphs — it never emits or runs code,
    // so the arena/stack-size routing guard (a runtime storage concern) doesn't
    // apply. Skipping it lets analysis re-root at a leaf module that has no `main`
    // to declare the arena, without a spurious "too large for the stack" abort.
    if c.analysis_only { return }
    if c.table.has_scope_allocator || c.table.context_expected_at_runtime { return }
    guard :: proc(c: ^Checker, a: ^Stmt_Assign) {
        // Take-bound views alias existing storage — they don't allocate, so a
        // big viewed type isn't a stack cost.
        if _, is_view := a.value.(^Expr_Take); is_view { return }
        if routes_to_arena(a.var_type) {
            check_error(c, a.span, TYPE_VALUE_TOO_LARGE_STACK_BYTES, a.name, checker_type_byte_size(a.var_type))
        }
    }
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Assign:
            if s.is_decl { guard(c, s) }
        case ^Stmt_Decl:
            for inner in s.checked {
                if a, ok := inner.(^Stmt_Assign); ok && a.is_decl { guard(c, a) }
            }
        }
    }
}

// --- building the graph as the checker checks (design/graph_retrofit.md) ------

// The builder, while the body being checked is one the checker builds and
// nothing has stopped it.
fusing :: proc(c: ^Checker) -> ^Graph_Builder {
    b := c.gb
    if b == nil || b.fuse == nil || b.fuse.failed != "" || c.errors > 0 { return nil }
    return b
}

// What the checker can't build yet: the body is left to the builder.
fuse_fail :: proc(c: ^Checker, reason: string) {
    if b := fusing(c); b != nil { graph_fuse_fail(b, b.fuse, reason) }
}

// What the walk building the graph asks of an expression (fuse_expr): its
// value; its place — a variable, a field, an element; or its place when it
// has one, else its value (its consumer decides: a view, a read).
Fuse_Want :: enum u8 { None, Value, Place, Either, Into }

// What the checker built for an expression: a value, or a place — or
// nothing, built into the destination it was given (.Into: else, as .Either).
Fused :: struct {
    v:     Operand,
    place: bool,
    ok:    bool,
    into:  bool,
    temp:  bool,   // built in a temporary, as storage that holds a value is written (read)
}

// A call being built: its operands (check_call_arg) — each at its param's
// type, or a builtin's as they are.
Fuse_Call :: struct {
    w:      Written,
    ops:    [dynamic]Operand,
    params: bool,
    // A builtin's: its operands as built (a place, for len and cap), their
    // types, and where the build stood before them.
    args:   [dynamic]Fused,
    types:  [dynamic]Type,
    want:   Fuse_Want,
    mark:   Graph_Mark,
    span:   Span,   // the call's: where a builtin's operand with no place is held
}

// Check an expression, building what it computes, in the order it runs.
// Written is the operations' (a default argument's are implied).
fuse_expr :: proc(c: ^Checker, e: Expr, env: ^Type_Scope, want := Fuse_Want.Value, w := Written.Explicit, dest := Dest{}, temp := false, temp_span := Span{}) -> (Type, Fused) {
    b := fusing(c)
    if b == nil { return check_expr(c, e, env), {} }
    // A compound assignment's target, read in its value: through the place
    // already built.
    if c.compound.key != nil && expr_identity(e) == c.compound.key {
        t := check_expr(c, e, env)
        if want == .Value { return t, {graph_read(b, c.compound.place, t, expr_span(e)^), false, true, false, false} }
        return t, {c.compound.place, true, true, false, false}
    }
    // What has no place of its own, asked for one: held (fuse_hold).
    if want == .Place && fuse_holds(e) {
        span := temp_span if temp_span != {} else expr_span(e)^
        t, p := fuse_hold(c, e, env, span)
        return t, {p, true, p != NO_VALUE, false, false}
    }
    c.want, c.want_written, c.want_dest, c.want_temp, c.want_span, c.fused = want, w, dest, temp, temp_span, {}
    t := check_expr(c, e, env)
    r := c.fused
    c.fused = {}
    if !r.ok { fuse_fail(c, fmt.aprintf("%v", reflect.union_variant_typeid(e))) }
    return t, r
}

// A place however its base is reached (graph_place's): a field, an
// element, what a pointer points at.
fuse_is_place_form :: proc(e: Expr) -> bool {
    #partial switch v in e {
    case ^Expr_Field_Access, ^Expr_Index: return true
    case ^Expr_Unary: return v.op == .Caret
    }
    return false
}

// An expression with no place of its own (graph_place's): an operation's
// value, a `?`'s, a slice, an assert, a take.
fuse_holds :: proc(e: Expr) -> bool {
    #partial switch v in e {
    case ^Expr_Binary, ^Expr_Try, ^Expr_Slice, ^Expr_Assert, ^Expr_Take: return true
    case ^Expr_Unary: return v.op != .Caret
    }
    return false
}

// Its place, when it has none (graph_place's): a temporary made first, the
// value stored in it — built there, what builds in place — its variable the
// place, at the use's span.
fuse_hold :: proc(c: ^Checker, e: Expr, env: ^Type_Scope, span: Span) -> (Type, Operand) {
    b := fusing(c)
    if b == nil { return check_expr(c, e, env), NO_VALUE }
    slot := graph_slot(b, "temp", nil, span)
    // (Text, or a slice's elements, filling a new partial array: it is zero
    // first — kept once its type says so.)
    prefix := graph_fuse_prefix(b, "temp", slot, span)
    t := fuse_store_into(c, e, env, graph_dest_var("temp", slot, nil), span)
    b = fusing(c)
    if b == nil { return t, NO_VALUE }
    graph_fuse_prefix_end(b, prefix, is_partial_array(t) && graph_fills_prefix(e), t)
    graph_fuse_typed(b, slot, t)
    return t, graph_var(b, "temp", slot, t, span)
}

// What the expression being checked was asked to build, taken by the
// construct that builds it — before its operands are checked.
fuse_asked :: proc(c: ^Checker) -> (Fuse_Want, Written) {
    want, w := c.asked, c.asked_written
    c.asked = .None
    if fusing(c) == nil { return .None, w }
    return want, w
}

fuse_done :: proc(c: ^Checker, v: Operand, place := false, into := false, temp := false) {
    c.fused = {v, place, true, into, temp}
}

// A built expression's value: a place is read, right after it.
fuse_value :: proc(c: ^Checker, r: Fused, e: Expr, t: Type) -> Operand {
    b := fusing(c)
    if b == nil || !r.place { return r.v }
    return graph_read(b, r.v, t, expr_span(e)^)
}

// A leaf: what the builder builds of it, from what its check found.
fuse_leaf :: proc(c: ^Checker, e: Expr) {
    want, w := fuse_asked(c)
    b := fusing(c)
    if b == nil || want == .None { return }
    #partial switch v in e {
    case ^Expr_Number, ^Expr_Char, ^Expr_Bool, ^Expr_Size_Of, ^Expr_Compiler_Intrinsic:
        if want == .Place { return }
        fuse_done(c, graph_leaf(b, e, w))
    case ^Expr_String:
        // Text is its global: its place and its value.
        fuse_done(c, graph_leaf(b, e, w), want == .Place)
    case ^Expr_Self:
        // `#self`: the address of what is being built; Self itself its place.
        if want == .Place {
            fuse_done(c, graph_plain_place(b, e, v.span), true)
        } else {
            fuse_done(c, graph_leaf(b, e, w))
        }
    case ^Expr_Ident:
        // A variable, or a constant table, is a place; the rest are values
        // (a variant is built where it goes).
        is_place := v.resolved == nil
        if _, is_const := v.resolved.(Resolved_Constant); is_const && graph_aggregate(v.type_) { is_place = true }
        if is_void_literal(e) { is_place = false }
        _, is_variant := v.resolved.(Resolved_Union_Variant)
        switch {
        case want == .Into && is_variant:
            d, temp, at := c.asked_dest, c.asked_temp, c.asked_span
            if temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
            fuse_variant(c, v.type_, v.name, d, v.span)
            if b := fusing(c); b != nil { fuse_built(c, b, want, temp, temp, d, v.type_, at) }
        case is_variant && want != .Place:
            fuse_done(c, fuse_variant_value(c, v.type_, v.name, v.span))
        case want == .Value:  fuse_done(c, graph_leaf(b, e, w))
        case is_place:        fuse_done(c, graph_plain_place(b, e, v.span), true)
        case want != .Place:  fuse_done(c, graph_leaf(b, e, w))
        }
    }
}

// An argument or a returned value at the type its use takes (graph_value_as):
// a view where one is taken, else its value, widened.
fuse_value_as :: proc(c: ^Checker, e: Expr, t: Type, r: Fused, to: Type, span: Span, w: Graph_Widen, held: ^Graph_Later = nil) -> Operand {
    b := fusing(c)
    if b == nil { return NO_VALUE }
    if to != nil {
        _, to_slice := distinct_base(to).(^Type_Slice)
        _, from_array := distinct_base(t).(^Type_Fixed_Array)
        _, is_literal := e.(^Expr_Array)
        // (A literal a slice views, placed at the use — fuse_use_type — is
        // an array's.)
        if _, at := fuse_use_type(e, to, span); at != {} && !from_array {
            fuse_fail(c, "a literal placed at its use, of no array")
            return NO_VALUE
        }
        _, to_ptr := distinct_base(to).(^Type_Ptr)
        _, from_ptr := distinct_base(t).(^Type_Ptr)
        if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(t) {
            return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), fuse_value(c, r, e, t))
        }
        if to_slice && from_array {
            if r.place { return graph_op_value(b, .Slice, .Implied, span, to, "", r.v) }
            // An array's value: held in a temporary made before it (`held`,
            // reserved then — graph_place's), seen whole.
            if held == nil || !held.reserved {
                fuse_fail(c, "a slice of an array value")
                return NO_VALUE
            }
            graph_fuse_later_begin(b, held)
            slot := graph_slot(b, "temp", t, span)
            if !graph_fuse_later_end(b, held) { fuse_fail(c, "an array's value across runs") }
            graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", slot, t, span), r.v)
            return graph_op_value(b, .Slice, .Implied, span, to, "", graph_var(b, "temp", slot, t, span))
        }
        // Bytes taken as an array (a view, into a temporary); a literal
        // built at its use's type.
        _, to_array := distinct_base(to).(^Type_Fixed_Array)
        sl, is_slice := e.(^Expr_Slice)
        if to_array && fuse_byte_index(e) && r.place {
            // That many bytes at the index, seen as the array, copied.
            graph_fuse_view(b, r.v, to, e.(^Expr_Index).is_big_endian, span)
            return graph_fuse_view_temp(b, r.v, to, span)
        }
        if to_array && is_slice && r.v.op != NO_NODE && r.v.op == c.span_read.op && c.span_read.scalar {
            // That many bytes at the span's start, seen as the array, copied.
            return graph_fuse_view_temp(b, graph_fuse_span_view(b, r.v, to, sl.is_big_endian, span), to, span)
        }
        // (A literal asked at it: built so — fuse_use_type.)
        if is_literal && graph_aggregate(to) && r.v.op != NO_NODE && b.g.type_[r.v.op] == to { return r.v }
        if to_array && (fuse_byte_index(e) || is_slice && is_byte_buffer(expr_type(sl.expr))) || is_literal && graph_aggregate(to) {
            fuse_fail(c, "bytes or a literal at its use's type")
            return NO_VALUE
        }
    }
    return graph_fuse_widen(b, fuse_value(c, r, e, t), span, w)
}

// The graph checks the scalars written to a variable; what else a store
// builds (in place, a view, from bytes) waits.
fuse_scalar :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_F64, Type_Infer_Int, Type_Infer_Float, Type_Bool, Type_Utf8, Type_Numeric, ^Type_Ptr, ^Type_Enum:
        return true
    }
    return false
}

// Check with nothing built — a definition, a signature, another scope: what
// the graph holds of them is not the code being checked.
fuse_suspend :: proc(c: ^Checker) -> ^Graph_Fuse {
    if c.gb == nil { return nil }
    f := c.gb.fuse
    c.gb.fuse = nil
    return f
}

fuse_resume :: proc(c: ^Checker, f: ^Graph_Fuse) {
    if c.gb != nil { c.gb.fuse = f }
}

fuse_end :: proc(c: ^Checker, f: ^Graph_Fuse) {
    if c.errors > 0 { graph_fuse_fail(c.gb, f, "errors") }
    graph_fuse_end(c.gb, f)
}

// A statement a pass meets, as the graph enters it (the builder's
// graph_stmt): the one it is in for what the pass builds.
Fuse_Stmt :: struct {
    b:     ^Graph_Builder,
    saved: i32,
}

fuse_stmt :: proc(c: ^Checker, s: Stmt) -> Fuse_Stmt {
    if c.gb == nil || c.gb.fuse == nil || is_scope_def(s) { return {} }
    return {c.gb, graph_fuse_stmt(c.gb, s)}
}

fuse_stmt_end :: proc(fs: Fuse_Stmt) {
    if fs.b != nil { graph_fuse_stmt_end(fs.b, fs.saved) }
}

// Whether a definition is written before a statement.
stmt_before :: proc(x, y: Stmt) -> bool {
    a, b := stmt_span(x), stmt_span(y)
    return a.line < b.line || (a.line == b.line && a.col < b.col)
}

// A statement of the code the checker doesn't build yet: its body is the
// builder's.
fuse_code_stmt :: proc(c: ^Checker, s: Stmt) {
    #partial switch v in s {
    case Stmt_Return, Stmt_Call, ^Stmt_If, ^Stmt_For, Stmt_Break, Stmt_Continue, ^Stmt_Match, ^Stmt_Defer:
        return
    case ^Stmt_Decl, ^Stmt_Multi_Return_Assign:
        return
    case ^Stmt_Assign:
        #partial switch _ in v.target {
        case nil, ^Expr_Field_Access, ^Expr_Index, ^Expr_Unary, ^Expr_Slice: return
        }
        fuse_fail(c, "a store through a slice")
        return
    case ^Stmt_Multi_Assign:
        for a in v.assigns { fuse_code_stmt(c, a) }   // (each in turn)
        return
    }
    fuse_fail(c, fmt.aprintf("%v", reflect.union_variant_typeid(s)))
}

// Several reassigned together (`a, b = b, a`, `a[0], a[1] = a[1], a[0]`):
// each assignment's store held in a temporary at its target's type — its
// value, and a target's place, built as it is checked — then, every value
// in, each target written from its own.
Fuse_Parallel :: struct {
    held: [dynamic]Fuse_Held,
}

Fuse_Held :: struct {
    d:    Dest,
    slot: Node_Id,
    t:    Type,
    span: Span,
}

fuse_is_parallel :: proc(s: ^Stmt_Multi_Assign) -> bool {
    if len(s.assigns) < 2 { return false }
    for a in s.assigns { if a.is_decl { return false } }
    return true
}

// The assignment's own store, where several are assigned together: into a
// temporary of its own (its target's, recorded).
fuse_parallel_hold :: proc(c: ^Checker, d: Dest, span: Span) -> Dest {
    b := fusing(c)
    par := c.parallel
    if b == nil || par == nil { return d }
    t := graph_dest_type(b, d)
    slot := graph_slot(b, "parallel", t, span)
    append(&par.held, Fuse_Held{d, slot, t, span})
    return graph_dest_var("parallel", slot, t)
}

fuse_parallel_end :: proc(c: ^Checker, par: ^Fuse_Parallel) {
    defer delete(par.held)
    b := fusing(c)
    if b == nil { return }
    for h in par.held {
        v := graph_read(b, graph_var(b, "parallel", h.slot, h.t, h.span), h.t, h.span)
        graph_fuse_write_at(b, graph_dest_place(b, h.d, h.span), v, h.span)
    }
}

// A declaration or an assignment to a variable, built: the local (made
// before its value), the value, and — once the statement's check has typed
// it — the store (graph_init, graph_assign).
Fuse_Assign :: struct {
    on:         bool,
    decl:       Node_Id,
    value:      Fused,
    value_type: Type,
    prefix:     [2]Node_Id,   // a new partial array's zero, made before its value
    prefixed:   bool,
    field:      bool,         // the declaration is a struct's field
}

// A constant's value, checked and built: its code (graph_const_begin), the
// value built into the constant — stored once its type is known. (Once: a
// constant checked again builds nothing.)
Fuse_Const :: struct {
    f:     ^Graph_Fuse,
    value: Fused,
    vt:    Type,
}

fuse_const_begin :: proc(c: ^Checker, s: ^Stmt_Define) -> Fuse_Const {
    b := c.gb
    if b == nil || c.errors > 0 || s.value == nil { return {} }
    if _, is_include := s.value.(^Expr_Include); is_include { return {} }
    if rawptr(s) in b.const_segs { return {} }
    return {f = graph_const_begin(b, s)}
}

fuse_const_value :: proc(c: ^Checker, fc: ^Fuse_Const, s: ^Stmt_Define, env: ^Type_Scope, ann: Type) -> Type {
    if fc.f == nil || fusing(c) == nil { return check_expr(c, s.value, env) }
    at := graph_dest_var(s.name, fc.f.root, nil if is_untyped(ann) else ann)
    fc.vt, fc.value = fuse_expr(c, s.value, env, .Into, dest = at, temp_span = s.span)
    return fc.vt
}

fuse_const_end :: proc(c: ^Checker, fc: ^Fuse_Const, s: ^Stmt_Define, t: Type) {
    if fc.f == nil { return }
    if c.errors > 0 {
        graph_fuse_fail(c.gb, fc.f, "errors")
    } else if fusing(c) != nil {
        fuse_store_finish(c, s.value, fc.vt, fc.value, graph_dest_var(s.name, fc.f.root, t), s.span, settle = true)
    }
    graph_const_end(c.gb, fc.f, s, t)
}

// A default, where what leaves it off runs it — a construction written
// without its arguments, as a call leaving them off does (fill_default_args):
// checked there, in its owner's defining scope, and built at the type it
// defaults (`w`: a param's, a field's).
fuse_default :: proc(c: ^Checker, def: Expr, t: Type, owner: ^Type_Scope, span: Span, w: Graph_Widen) -> Operand {
    saved := c.expected_hint
    c.expected_hint = t
    defer c.expected_hint = saved
    use, at := fuse_use_type(def, t, span)
    vt, r := fuse_expr(c, def, callee_def_scope(owner), .Either, .Implied, dest = use, temp_span = at)
    return fuse_value_as(c, def, vt, r, t, span, w)
}

// A construction's arguments: its constructor's params' defaults (the
// checker lets none be built without one — a missing one is reported).
fuse_ctor_args :: proc(c: ^Checker, ts: ^Type_Scope, span: Span) -> []Operand {
    args := make([]Operand, len(ts.params), context.temp_allocator)
    for p, i in ts.params {
        if p.default_value == nil { continue }
        args[i] = fuse_default(c, p.default_value, p.type_, ts, span, {sig = ts, param = i})
    }
    return args
}

// A bare declaration's (graph_construct_bare): a struct's constructor's
// arguments, an array's elements'.
fuse_bare_args :: proc(c: ^Checker, t: Type, span: Span) -> []Operand {
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        if v.kind == .Struct && !v.is_module && constructs_bare(v) { return fuse_ctor_args(c, v, span) }
    case ^Type_Fixed_Array, ^Type_Partial_Array:
        if st := graph_elem_struct(t); st != nil && constructs_bare(st) { return fuse_ctor_args(c, st, span) }
    }
    return nil
}

// A variant's field defaults, each one a literal doesn't give (lit nil:
// none given), written into the variant's place d once it's constructed.
fuse_variant_defaults :: proc(c: ^Checker, st: ^Type_Scope, lit: ^Expr_Struct_Literal, d: Dest, span: Span) {
    if st == nil || fusing(c) == nil { return }
    sd := as_scope_body(st)
    skip := 0
    for f in sd.fields { if strings.has_prefix(f.name, "__") { skip += 1 } }
    for f, i in sd.fields {
        if f.default_value == nil { continue }
        given := false
        if lit != nil {
            for lf, j in lit.fields {
                if lf.name == f.name || (lf.name == "" && skip + j == i) { given = true }
            }
        }
        if given { continue }
        v := fuse_default(c, f.default_value, f.type_, st, span, {to = f.type_})
        if b := fusing(c); b != nil { graph_fuse_field_default(b, d, f.name, f.type_, v, span) }
    }
}

// A variant named where it goes: constructed at d, then its defaults.
fuse_variant :: proc(c: ^Checker, t: Type, name: string, d: Dest, span: Span) {
    b := fusing(c)
    if b == nil { return }
    st := graph_fuse_variant(b, t, name, d, span)
    dd := d
    fuse_variant_defaults(c, st, nil, Dest{kind = .Variant, name = name, type_ = st, parent = &dd}, span)
}

// A variant named as a value: built in a temporary made first, read.
fuse_variant_value :: proc(c: ^Checker, t: Type, name: string, span: Span) -> Operand {
    b := fusing(c)
    if b == nil { return NO_VALUE }
    d := graph_fuse_temp(b, span, t)
    fuse_variant(c, t, name, d, span)
    if b := fusing(c); b != nil { return graph_read(b, graph_dest_place(b, d, span), t, span) }
    return NO_VALUE
}

// The node a declaration declares: a struct's field, made with its
// declaration; else a local, made now.
fuse_decl_node :: proc(b: ^Graph_Builder, s: ^Stmt_Assign, bound := false) -> (Node_Id, bool) {
    if d, is_field := b.fuse.fields[rawptr(s)]; is_field { return d, true }
    return graph_fuse_decl(b, s.name, s.span, bound = bound), false
}

fuse_assign_end :: proc(c: ^Checker, s: ^Stmt_Assign, fa: ^Fuse_Assign) {
    b := fusing(c)
    if b == nil || !fa.on { return }
    _, is_skip := s.value.(^Expr_Skip_Constructor)
    if s.is_decl {
        t := s.env_type if s.env_type != nil else s.var_type
        if fa.field { t = b.g.type_[fa.decl] }   // (a field: its struct's type)
        graph_fuse_typed(b, fa.decl, t)
        if is_skip && fa.field {
            // A field's `= void` is its declaration's, as written: the value
            // stored, unchecked.
            orig := b.fuse.field_inits[rawptr(s)]
            val := graph_leaf(b, orig)
            graph_fuse_write_at(b, graph_var(b, s.name, fa.decl, t, s.span), val, s.span)
            return
        }
        if is_skip {
            graph_fuse_void_decl(b, fa.decl, t, s.span, expr_span(s.value)^)
            return
        }
        // (A text written to a new partial array fills a prefix of it.)
        wrote, zeroed := fuse_store_finish(c, s.value, fa.value_type, fa.value, graph_dest_var(s.name, fa.decl, t), s.span, settle = true)
        if fa.prefixed { graph_fuse_prefix_end(b, fa.prefix, zeroed || wrote && is_partial_array(t) && graph_fills_prefix(s.value), t) }
        if zeroed && !fa.prefixed { fuse_fail(c, "a new partial array read from bytes") }
        // (An array of untyped elements held as itself — `a := [1, 2, 3]`,
        // an if of such literals — built at its own type: its nodes, the
        // store's too, as the declaration's, settled.)
        if va, is_array := distinct_base(fa.value_type).(^Type_Fixed_Array); is_array && is_infer(va.elem) && !fa.field {
            graph_fuse_retype_literal(b, int(fa.decl), b.nodes, t)
        }
        return
    }
    if is_skip || is_void_literal(s.value) {   // `x = void` de-inits
        graph_fuse_void_assign(b, s.name, s.var_type, s.span, expr_span(s.value)^)
        return
    }
    fuse_store_finish(c, s.value, fa.value_type, fa.value, fuse_parallel_hold(c, graph_dest_var(s.name, NO_NODE, s.var_type), s.span), s.span)
}

// A dispatch's array literal argument: its position, its nodes, its type.
Fuse_Literal_Arg :: struct {
    arg, from, to: int,
    t:             Type,
}

// Whether a function's param would view an argument that is an array's
// value (graph_view: its place, a temporary) — a slice over it.
fuse_views_value :: proc(ft: ^Type_Scope, array_values: []bool) -> bool {
    for is_value, i in array_values {
        if !is_value || i >= len(ft.params) { continue }
        if _, to_slice := distinct_base(ft.params[i].type_).(^Type_Slice); to_slice { return true }
    }
    return false
}

// Whether a use of a `from` as a `to` views it (graph_view): a fixed array
// as a slice; a partial array, or a pointer to one, as a slice's header.
fuse_views :: proc(to, from: Type) -> bool {
    if to == nil || from == nil { return false }
    _, to_ptr := distinct_base(to).(^Type_Ptr)
    _, from_ptr := distinct_base(from).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(from) { return true }
    _, to_slice := distinct_base(to).(^Type_Slice)
    _, from_array := distinct_base(from).(^Type_Fixed_Array)
    return to_slice && from_array
}

// What a store builds in place (graph_builds_into): a literal, an array, a
// construction, a variant.
fuse_builds_into :: proc(e: Expr) -> bool {
    #partial switch v in e {
    case ^Expr_Struct_Literal: return v.override_target == ""
    case ^Expr_Array:          return true
    case ^Expr_Call:
        rf, resolved := v.resolved_func.?
        return resolved && rf.callee != nil && rf.callee.kind == .Struct
    case ^Expr_Ident:
        _, is_variant := v.resolved.(Resolved_Union_Variant)
        return is_variant
    case ^Expr_Field_Access:
        _, is_variant := v.resolved.(Resolved_Union_Variant)
        return is_variant
    }
    return false
}

is_partial_array :: proc(t: Type) -> bool {
    _, is_pa := distinct_base(t).(^Type_Partial_Array)
    return is_pa
}

check_scope :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Scope, owner: ^Type_Scope = nil, public_env: ^Type_Scope = nil, scope_defs: [dynamic]Stmt = nil) {
    // SPLIT mode (a Stmt_Scope body): compile-time defs live in `scope_defs`,
    // runtime statements in `stmts`. The registration/check passes run over the
    // defs first (so forward references resolve), then over the body. MIXED mode
    // (module level, control-flow bodies, generic-clone bodies): scope_defs is
    // nil and the single `stmts` list carries both, exactly as before.
    split := scope_defs != nil
    def_list := scope_defs if split else stmts
    // The definitions build nothing of this code: the builder builds them,
    // where they are written.
    fuse := fuse_suspend(c)

    // Pass 1a: pre-register every `name :: ...` definition so any later
    // statement can reference it. Fun signatures are NOT resolved here — they
    // resolve on demand (ensure_fun_signature) at the first use site.
    register_type_names(c, def_list, env, owner, public_env)

    // (Former "Pass 1a.5" nested-struct signature pre-pass removed: a nested
    // struct's fields resolve ON DEMAND when a sibling decl default or a
    // forward-referencing use reaches them — ensure_struct_signature walks up via
    // parent_scope to resolve the enclosing scope, whose signature pass recurses
    // back down. e.g. `body := head.count` with `Inner` defined later.)

    // The definitions first — registered, then checked, descending into child
    // scopes — so code can name one written after it. Then the code, one
    // statement at a time in the order it runs, each checked whole (both
    // passes) before the next: a local is visible from its declaration on, and
    // what the checker finds comes in the order the program does it.
    // (A block — an if's, a loop's, an arm's — holds both: split here.)
    defs, code: [dynamic]Stmt
    defer if !split { delete(defs); delete(code) }
    if split {
        defs, code = def_list, stmts
    } else {
        for s in stmts { append(&defs if is_scope_def(s) else &code, s) }
    }
    register_and_check_declarations(c, defs[:], env, owner, public_env)
    check_bodies(c, defs[:], env)
    fuse_resume(c, fuse)
    if fuse != nil {
        for d in defs { graph_fuse_def_settled(c.gb, d) }   // (its constants, settled: built)
    }
    when ODIN_DEBUG {
        saved_stmt := c.once_stmt   // the enclosing statement's, when this is its block
        defer c.once_stmt = saved_stmt
    }
    b := c.gb if fuse != nil else nil   // this code's graph is built as it is checked
    di := 0
    for i in 0 ..< len(code) {
        when ODIN_DEBUG { c.once_stmt += 1 }
        saved: i32
        if b != nil {
            for ; di < len(defs) && stmt_before(defs[di], code[i]); di += 1 { graph_fuse_def(b, defs[di]) }
            graph_fuse_body_stmt(b, code[i])
            saved = graph_fuse_stmt(b, code[i], fresh = true)
            fuse_code_stmt(c, code[i])
        }
        register_and_check_declarations(c, code[i:i + 1], env, owner, public_env)
        check_bodies(c, code[i:i + 1], env)
        if b != nil { graph_fuse_stmt_end(b, saved) }
    }
    if b != nil {
        for ; di < len(defs); di += 1 { graph_fuse_def(b, defs[di]) }
    }

    // Pass 4 (stack/arena routing) is runtime-only — over the body statements.
    // (Unused-err is now the post-check flow pass's job — see flow.odin.)
    check_storage_sizes(c, stmts, env)
}

// ---------------------------------------------------------------------------
// Shared helpers for type registration
// ---------------------------------------------------------------------------

// Track variant ownership in c.table.variant_to_enum so the dot-shorthand
// fallback (`.Core` with no expected type) can find variants by name across
// visible enums/unions. We deliberately do NOT bind variants as bare names in
// any env: bare variant resolution must go through an expected type.
register_enum_variants :: proc(c: ^Checker, et: ^Type_Enum, env: ^Type_Scope, enum_key: string = "", skip_func_names := false, public_env: ^Type_Scope = nil) {
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


// Pre-register nested struct TYPE NAMES (recursively) so `Parent.Inner`
// resolves in TYPE position — e.g. a `^TTF.Decoded` parameter — even when
// the reference sits ABOVE the parent in the file. Pass 1b
// (register_scope_defs) walks bodies in source order, which is too late for
// forward signatures. Names only: fields/bodies still resolve in 1b/Phase 2,
// and register_scope_defs REUSES these Type_Scopes (same pointer), so type
// identity holds across both passes.
// Mint (or reuse, to preserve type identity for an already-registered forward
// signature) the Type_Scope for a nested struct / parameterized-struct `s`
// declared in `parent`, keyed by its bare name. Sets only the identity fields
// shared by the early name pass and the full register pass; callers fill
// ast/source_name/params as needed. Mangled name = parent.name + "_" + bare.
// One place mints a nested struct scope, so the name pass and register_scope_defs
// can't drift on naming / table keys / parent_scope.
register_nested_struct_scope :: proc(c: ^Checker, parent: ^Type_Scope, bare: string, s: ^Stmt_Scope) -> ^Type_Scope {
    mangled := fmt.aprintf("%s_%s", parent.name, bare)
    ts: ^Type_Scope
    if parent.types != nil {
        if existing, ok := parent.types[bare]; ok {
            if ets, ets_ok := existing.(^Type_Scope); ets_ok { ts = ets }
        }
    }
    if ts == nil { ts = new(Type_Scope) }
    ts.name = mangled
    ts.home_package = c.current_package
    ts.kind = .Struct
    ts.is_packed = s.is_packed
    ts.parent_scope = parent
    if len(s.typed_params) == 0 {
        c.table.structs[mangled] = ts
    } else {
        c.table.funs[mangled] = ts
    }
    if parent.types == nil { parent.types = make(map[string]Type) }
    parent.types[bare] = ts
    return ts
}

pre_register_nested_struct_types :: proc(c: ^Checker, parent: ^Type_Scope, body: [dynamic]Stmt) {
    for def in body {
        s, is_scope := def.(^Stmt_Scope)
        if !is_scope { continue }
        if s.kind != .Struct { continue }
        nested := register_nested_struct_scope(c, parent, scope_name(s), s)
        pre_register_nested_struct_types(c, nested, s.defs)
    }
}

// Register :: definitions from a fun's scope as top-level entities with mangled names.
// e.g., Mega :: fun { test_print :: fun() { ... } } → registers "Mega_test_print" as a function.
// self_type is the Type value wrapping `st` (always ^Type_Scope). It gets bound to
// the name "Self" in this scope so methods can reference `^Self` / `Self` inside.
register_scope_defs :: proc(c: ^Checker, self_type: Type, st: ^Scope_Body, defs: [dynamic]Stmt) {
    // Phase 1 only: mangle names and register in scope. No type resolution.
    // Type resolution happens in Phase 2 (check_bodies) uniformly for all funs.
    parent_ts, _ := self_type.(^Type_Scope)  // the scope these defs nest under (their parent_scope)
    scope_env := new(Type_Scope) // empty transient scope for resolve_type_expr on foreign sigs
    // Mangled names register persistently on the module scope (the top of the
    // durable chain) so they survive past this call and reach codegen.
    root_scope := module_scope(parent_ts)
    for def in defs {
        #partial switch s in def {
        case ^Stmt_Scope:
            bare_name := scope_name(s)
            mangled := fmt.aprintf("%s_%s", st.name, bare_name)
            s.mangled_name = mangled
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
                // Reuse the Type_Scope when pre_register_nested_struct_types already
                // minted it (Pass 2a) — forward signatures captured that pointer,
                // so a fresh object here would split type identity.
                def_st := register_nested_struct_scope(c, parent_ts, bare_name, s)
                def_st.ast = s
                def_st.source_name = bare_name
                // Recurse so this struct's OWN nested `::` defs (deeper types,
                // consts, methods) register into def_st.types — needed for
                // `Parent.Inner.Innermost` type-position resolution. Gate on
                // s.defs, not s.body: a pure-namespace struct (only nested
                // types) has an empty runtime body but non-empty defs.
                if len(s.defs) > 0 {
                    register_scope_defs(c, def_st, &def_st.sd, s.defs)
                }
                // Mangled name persists on the module scope; the bare name is already
                // on parent_ts.types via register_nested_struct_scope.
                register_on_module(root_scope, mangled, def_st)
                c.table.fun_asts[mangled] = s
            } else {
                // Function or struct constructor (has params) — create Type_Scope.
                // Struct kinds may have been pre-registered by Pass 2a (see the
                // pure-data branch above) — reuse to keep type identity.
                def_ft: ^Type_Scope
                if def_is_struct {
                    // Parameterized struct constructor — mint via the shared helper
                    // (reuses a pre-registered pointer; sets name / kind / is_packed
                    // / parent_scope / c.table.funs / st.types), then fill the
                    // def-specific fields and recurse into its own nested defs.
                    def_ft = register_nested_struct_scope(c, parent_ts, bare_name, s)
                    def_ft.has_parens = s.has_parens
                    def_ft.ast = s
                    def_ft.source_name = bare_name
                    if len(s.defs) > 0 {
                        register_scope_defs(c, def_ft, &def_ft.sd, s.defs)
                    }
                } else {
                    // Plain nested fun — not a data type, so no c.table.funs / st.types
                    // entry here (registered in st.functions + root_env below).
                    def_ft = new(Type_Scope)
                    def_ft.name = mangled
                    def_ft.home_package = c.current_package
                    def_ft.has_parens = s.has_parens
                    def_ft.ast = s
                    def_ft.source_name = bare_name
                    def_ft.parent_scope = parent_ts
                    def_ft.kind = .Fun
                }
                is_callable := !def_is_struct || len(s.typed_params) > 0
                // Funs AND parameterized-struct constructors both resolve their
                // signature (params + returns) ON DEMAND now — funs via
                // ensure_fun_signature, ctors via ensure_struct_signature ->
                // check_scope_body — so neither resolves eagerly here. (A ctor's
                // field initializers reference its params, so the param pass runs
                // inside check_scope_body right before the field pass; see the
                // `ft.kind == .Struct` block there.)
                // Mangled name persists on the module scope; plain funs live in
                // st.functions (below) for bare-name resolution.
                register_on_module(root_scope, mangled, def_ft)
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
            bare_name := define_name(s)
            mangled := fmt.aprintf("%s_%s", st.name, bare_name)
            s.mangled_name = mangled
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
            c.in_foreign_sig = true
            for decl in s.decls {
                fun_type := new(Type_Scope)
                fun_type.kind = .Fun
                fun_type.calling_conv = .C
                fun_type.home_package = c.current_package
                bare_name := decl.name
                mangled := fmt.aprintf("%s_%s", st.name, bare_name)
                fun_type.name = mangled
                for tp in decl.typed_params {
                    pt := resolve_type_expr(tp.type_expr, c, decl.span, env=scope_env)
                    append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt})
                }
                for rte in decl.return_types {
                    append(&fun_type.return_types, resolve_type_expr(rte, c, decl.span, env=scope_env))
                }
                build_param_map(fun_type)
                if st.functions == nil { st.functions = make(map[string]^Type_Scope) }
                st.functions[bare_name] = fun_type
                c.declared_funs[mangled] = true
                c.table.fun_homes[mangled] = c.current_package
                // Bare name in st.functions (above) for wrapper-body resolution;
                // mangled name on the module scope so codegen lookups via
                // call_resolved_name resolve.
                register_on_module(root_scope, mangled, fun_type)
            }
            c.in_foreign_sig = false
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
flatten_module_exports :: proc(c: ^Checker, env: ^Type_Scope, mod_sd: ^Scope_Body, mod_name: string, is_aliased := false, is_sealed := false) {
    assert(sd_is_module(mod_sd), "module-struct must have scope")
    // Sealed includes (`name :: sealed include path`) skip the env.includes
    // append AND the c.declared_funs writes — bare names from the included
    // module are not made available at the call site, only `name.X` access.
    // Used to keep colliding bindings (SDL2 vs SDL3, etc.) properly isolated.
    if is_sealed { return }
    if env != nil { append(&env.includes, mod_sd) }
    for name, t in mod_sd.types {
        if name == "void" { continue }  // don't re-export the void null-pointer literal
        if tf, is_func := t.(^Type_Scope); is_func && (len(tf.params) > 0 || tf.has_parens) {
            c.declared_funs[name] = true
        }
    }
    // Dispatches and operator overloads stay on the included module's struct
    // (see Scope_Body.dispatch_groups). Lookups in the includer walk
    // env.includes (the durable module scopes) at call time, so we don't merge
    // here — matches the non-transitive include semantics used elsewhere.
}

// is_enum_visible reports whether the enum identified by `flat_name`
// (e.g. "mara_sdl_Init_Flags") is reachable from `env` via the include chain
// or its parents. Used by the variant-ambiguity check so that a globally
// ambiguous variant (same name in two enums) only errors when both owners
// are actually in scope here.
is_enum_visible :: proc(env: ^Type_Scope, flat_name: string) -> bool {
    scope_has_enum :: proc(s: ^Scope_Body, flat: string) -> bool {
        if s == nil { return false }
        for _, t in s.types {
            if et, ok := t.(^Type_Enum); ok && et.name == flat { return true }
        }
        return false
    }
    // Own definitions + each scope's includes up the durable scope graph.
    for s := env; s != nil; s = s.parent_scope {
        if scope_has_enum(s, flat_name) { return true }
        for inc in s.includes {
            if scope_has_enum(inc, flat_name) { return true }
        }
        if s.is_module { break }
    }
    return false
}

// module_constant_visible reports whether a bare module constant `bare` is
// reachable from `env` — i.e. defined by the current module or by one that's
// been `use`/`include`d. Constants live in the global c.table.constants under
// both a flat (module-qualified) and a bare key, so unlike types they are NOT
// gated by the env walk at lookup time; this is what reintroduces visibility.
// It mirrors type_env_get / is_enum_visible: own scope, then each include's
// scope, stop at the module boundary. Matching is by the flat key
// make_flat_name(M.name, bare): the own module qualifies with c.current_package,
// each include with its durable scope's name (inc.name).
module_constant_visible :: proc(c: ^Checker, env: ^Type_Scope, bare: string) -> bool {
    if env == nil { return true }  // no env context to gate against — don't reject
    // The package being checked always sees its own constants. The own-module
    // branch below (env_is_module(cur)) covers this for module envs, but it's
    // kept explicit so the main package's top-level constants are visible in
    // size position even before the env walk.
    if owner, mapped := c.table.constant_owners[bare]; mapped && owner != "" && owner == c.current_package {
        return true
    }
    for s := env; s != nil; s = s.parent_scope {
        if s.is_module {
            if _, ok := c.table.constants[make_flat_name(c.current_package, bare)]; ok { return true }
        }
        for inc in s.includes {
            if inc != nil {
                if _, ok := c.table.constants[make_flat_name(inc.name, bare)]; ok { return true }
            }
        }
        if s.is_module { break }
    }
    return false
}

// resolve_const_ref resolves a bare module-constant name through the SCOPE — the
// reference's own module plus each `use`d include — making the scope the single
// resolver (the global table is just a flat value index keyed by the result).
// Returns the unique definer's flat key and how many VISIBLE modules define it:
//   0 -> not a visible module constant
//   1 -> unambiguous; `flat` is the key codegen/comptime should use
//   2+ -> ambiguous; the user must qualify (Module.name)
// The own module is derived from `env` (home_package), NOT c.current_package,
// which is the CALLER during cross-module default-argument resolution.
resolve_const_ref :: proc(c: ^Checker, env: ^Type_Scope, bare: string) -> (flat: string, count: int) {
    if env == nil { return "", 0 }
    own_mod := ""
    for s := env; s != nil; s = s.parent_scope {
        if s.home_package != "" { own_mod = s.home_package; break }
        if s.is_module { break }
    }
    if own_mod == "" { own_mod = c.current_package }

    seen: map[string]bool
    defer delete(seen)
    seen[own_mod] = true
    if _, ok := c.table.constants[make_flat_name(own_mod, bare)]; ok {
        flat = make_flat_name(own_mod, bare)
        count += 1
    }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc == nil || seen[inc.name] { continue }
            seen[inc.name] = true
            fk := make_flat_name(inc.name, bare)
            if _, ok := c.table.constants[fk]; ok {
                flat = fk
                count += 1
            }
        }
        if s.is_module { break }
    }
    return
}

// first_invisible_const_ref walks an array-size / const-generic expression and
// returns the first bare identifier that names a registered module constant
// which is NOT visible from `env`. Array sizes and const-generic args resolve
// constants straight out of the global table (bypassing the env walk that gates
// ordinary expression idents), so without this a module could size an array
// with another module's constant it never `use`d. Returns ("", false) when
// every constant ref is visible (or the name isn't a module constant at all,
// in which case evaluate_comptime_int / the size-name path handles it).
first_invisible_const_ref :: proc(c: ^Checker, env: ^Type_Scope, e: Expr) -> (string, bool) {
    if env == nil { return "", false }
    #partial switch v in e {
    case ^Expr_Ident:
        if _, is_const := c.table.constant_owners[v.name]; is_const {
            if !module_constant_visible(c, env, v.name) { return v.name, true }
        }
    case ^Expr_Binary:
        if n, ok := first_invisible_const_ref(c, env, v.left);  ok { return n, true }
        if n, ok := first_invisible_const_ref(c, env, v.right); ok { return n, true }
    case ^Expr_Unary:
        return first_invisible_const_ref(c, env, v.operand)
    }
    return "", false
}

// find_dispatch collects all functions associated with a dispatch group `name`,
// visible at `env`. Sources walked: the current module's own dispatches
// (c.dispatch_groups), then bare-`include`d modules' dispatches via env.includes.
// Multiple modules may contribute candidates to the same dispatch name; all
// matches are merged so a stdlib dispatch (e.g. `sqrt :: dispatch { sqrt_f32,
// sqrt_f64 }`) can be extended by user code that includes the stdlib module.
// Non-transitive: we don't follow inc.includes — re-export of re-exports is
// opt-in (the user would `include` again themselves), matching type_env_get.
find_dispatch :: proc(c: ^Checker, env: ^Type_Scope, name: string) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if fns, ok := c.dispatch_groups[name]; ok {
        for f in fns { append(&result, f) }
    }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc != nil {
                if fns, ok := inc.dispatch_groups[name]; ok {
                    for f in fns { append(&result, f) }
                }
            }
        }
    }
    return result, len(result) > 0
}

// find_operator_overload mirrors find_dispatch for `overload OP name` decls.
find_operator_overload :: proc(c: ^Checker, env: ^Type_Scope, op: Token_Kind) -> ([dynamic]string, bool) {
    result: [dynamic]string
    if names, ok := c.operator_overloads[op]; ok {
        for n in names { append(&result, n) }
    }
    for s := env; s != nil; s = s.parent_scope {
        for inc in s.includes {
            if inc != nil {
                if names, ok := inc.operator_overloads[op]; ok {
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

register_type_names :: proc(c: ^Checker, stmts: [dynamic]Stmt, env: ^Type_Scope, owner: ^Type_Scope = nil, public_env: ^Type_Scope = nil) {
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
                et.span = s.span
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
                ut.source_name = s.name
                ut.home_package = c.current_package
                ut.span = s.span
                ut.tag_type = s.tag_type
                ut.min_size = s.min_size
                // tag_pad: deferred to Pass 1b (type expr)
                // Tag enum can be fully built — variant tags are integers, no type refs.
                tag_enum_name := strings.concatenate({s.name, "_Tag"})
                tag_et := new(Type_Enum)
                tag_et.name = make_flat_name(c.current_package, tag_enum_name)
                tag_et.home_package = c.current_package
                tag_et.tag_type = s.tag_type
                tag_et.span = s.span   // synthetic discriminant: locate at the union decl
                tag_et.is_synthetic = true
                for vdef in s.variants {
                    tag_et.variants[vdef.name] = vdef.tag
                }
                c.table.enums[tag_et.name] = tag_et
                register_enum_variants(c, tag_et, env, tag_et.name, public_env = public_env)
                ut.tag_enum = tag_et
                // Variant structs registered as empty placeholders; their fields
                // get resolved in Pass 1b.
                for vdef in s.variants {
                    struct_name := strings.concatenate({s.name, "_", vdef.name})
                    vst := new(Type_Scope)
                    vst.name = make_flat_name(c.current_package, struct_name)
                    vst.home_package = c.current_package
                    vst.kind = .Struct
                    vst.body_span = vdef.span
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
            dt.source_name = s.name
            dt.span = s.span
            dt.home_package = c.current_package
            dt.default_cap_expr = s.default_cap_expr
            dt.is_alias = s.is_alias
            // base_type: deferred to Pass 1b
            c.table.distinct_types[flat] = dt
            type_env_set(pub, s.name, dt)
            if owner != nil {
                if owner.types == nil { owner.types = make(map[string]Type) }
                owner.types[s.name] = dt
            }
            c.pre_registered_stmts[rawptr(s)] = true
        case ^Stmt_Scope:
            // Already registered by a parent struct's register_scope_defs
            // pass (e.g. AllocHeader inside Arena_Debug). Its s.name has
            // been mutated to the mangled form and re-running registration
            // here would prepend the package prefix a second time, creating
            // duplicate empty entries. Mirrors the matching guard in
            // register_and_check_declarations.
            if scope_name(s) in c.table.fun_asts && c.table.fun_asts[scope_name(s)] == s {
                continue
            }
            // Generic templates store the AST — no resolution to defer.
            if len(s.generic_params) > 0 {
                if _, exists := c.table.generic_templates[scope_name(s)]; exists { continue }
                c.table.generic_templates[scope_name(s)] = Generic_Template{
                    name           = scope_name(s),
                    generic_params = s.generic_params,
                    ast            = s,
                    home_package   = c.current_package,
                    env            = env,
                }
                if len(s.typed_params) > 0 { c.declared_funs[scope_name(s)] = true }
                c.pre_registered_stmts[rawptr(s)] = true
                continue
            }
            is_struct_type := s.kind == .Struct
            if is_struct_type && len(s.return_types) > 0 {
                // Will diagnose properly in Pass 1b; suppress here.
                continue
            }
            if is_struct_type && len(s.typed_params) == 0 {
                flat := make_flat_name(c.current_package, scope_name(s))
                if flat in c.table.structs || flat in c.table.funs {
                    check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, scope_name(s))
                    continue
                }
                struct_type := new(Type_Scope)
                struct_type.name = flat
                struct_type.home_package = c.current_package
                struct_type.kind = .Struct
                struct_type.is_packed = s.is_packed
                struct_type.ast = s
                struct_type.source_name = scope_name(s)
                struct_type.decl_env = env
                c.table.structs[flat] = struct_type
                // Body fields deferred to Pass 1b (register_scope_defs).
                type_env_set(pub, scope_name(s), struct_type)
                c.table.fun_asts[scope_name(s)] = s
                c.table.fun_homes[scope_name(s)] = c.current_package
                if owner != nil {
                    struct_type.parent_scope = env if env != nil else owner // file/enclosing scope -> module
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[scope_name(s)] = struct_type
                }
                pre_register_nested_struct_types(c, struct_type, s.defs)
                c.pre_registered_stmts[rawptr(s)] = true
            } else {
                flat_name := make_flat_name(c.current_package, scope_name(s))
                if is_struct_type {
                    if flat_name in c.table.funs || flat_name in c.table.structs {
                        check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, scope_name(s))
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
                fun_type.ast = s
                fun_type.source_name = scope_name(s)
                fun_type.decl_env = env   // parameterized structs resolve fields on demand from here
                if is_struct_type {
                    fun_type.kind = .Struct
                } else {
                    fun_type.kind = .Fun
                }
                c.table.funs[flat_name] = fun_type
                // params and return_type deferred to Pass 1b.
                type_env_set(pub, scope_name(s), fun_type)
                c.table.fun_asts[scope_name(s)] = s
                c.table.fun_homes[scope_name(s)] = c.current_package
                is_callable := !is_struct_type || len(s.typed_params) > 0
                if is_callable { c.declared_funs[scope_name(s)] = true }
                if owner != nil {
                    fun_type.parent_scope = env if env != nil else owner // file/enclosing scope -> module
                    if is_struct_type {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[scope_name(s)] = fun_type
                    }
                    if is_callable {
                        if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
                        owner.functions[scope_name(s)] = fun_type
                    }
                }
                if is_struct_type { pre_register_nested_struct_types(c, fun_type, s.defs) }
                // A fun's signature (params + return types) resolves ON DEMAND —
                // ensure_fun_signature -> resolve_fun_signature reconstructs the
                // decl env from the durable parent_scope graph at the first use
                // site (a call, a dispatch match, a field-type inference reading
                // its return). No eager pre-pass: a forward reference pulls the
                // signature when it needs it. (This also dissolved the old
                // top-level-vs-nested split — top-level Pass 1a couldn't resolve
                // eagerly anyway because includes weren't processed yet.)
                c.pre_registered_stmts[rawptr(s)] = true
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

// True when `name` is the LHS of a `=` reassignment with no existing binding —
// a genuine "assign to undeclared variable" error. Exempts declarations (`:=`,
// is_decl), the blank discard `_`, the empty name used for expression targets,
// and `::` constants (left to the shadowing check). The single-assign path and
// both multi-assign branches (destructure, broadcast) share this one rule so
// the exemptions can't drift apart.
is_undeclared_reassign :: proc(c: ^Checker, env: ^Type_Scope, name: string, is_decl: bool) -> bool {
    if is_decl || name == "" || name == "_" { return false }
    if name in c.table.constants { return false }
    _, found := type_env_get(env, name)
    return !found
}

register_and_check_declarations :: proc(c: ^Checker, stmts: []Stmt, env: ^Type_Scope, owner: ^Type_Scope = nil, public_env: ^Type_Scope = nil) {
    // pub: where defined names (fun/struct/type/foreign/constants) get registered.
    // - In single-env mode (callers from inside fun bodies, struct bodies): public_env is nil
    //   and pub == env, so behavior is unchanged.
    // - In per-file mode (callers from check_module / check_program): public_env is the module
    //   env and env is the file env — defined names go to the module env (visible to siblings
    //   via the chain file_env -> mod_env), include names stay in the file env (private).
    pub := public_env if public_env != nil else env
    for stmt in stmts {
        fs := fuse_stmt(c, stmt)
        defer fuse_stmt_end(fs)
        defer if c.gb != nil { graph_module_stmt(c.gb, stmt) }   // (a module's, settled: its declarations)
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
                        finalize_union_variant_headers(c, ut)
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
                et.span = s.span
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
                ut.source_name = s.name
                ut.home_package = c.current_package
                ut.span = s.span
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
                    ut.tag_enum = tag_et
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
                        vst.body_span = vdef.span
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
                    finalize_union_variant_headers(c, ut)

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
            dt.source_name = s.name
            dt.home_package = c.current_package
            dt.span = s.span
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
                flat := make_flat_name(c.current_package, scope_name(s))
                if is_struct && len(s.typed_params) == 0 {
                    if struct_type, ok := c.table.structs[flat]; ok {
                        register_scope_defs(c, struct_type, &struct_type.sd, s.defs)
                    }
                } else {
                    if fun_type, ok := c.table.funs[flat]; ok {
                        if is_struct {
                            register_scope_defs(c, fun_type, &fun_type.sd, s.defs)
                        }
                        // FUN signatures: resolve params/returns for a pre-registered
                        // top-level fun (idempotent — skips if a demand pull already
                        // populated them). STRUCT ctors skip here: their params +
                        // returns resolve ON DEMAND in check_scope_body, right before
                        // the field pass, since field initializers reference the params.
                        if !is_struct && len(s.typed_params) > 0 && len(fun_type.params) == 0 {
                            for tp in s.typed_params {
                                pt := resolve_param_type(c, tp, env, s.span)
                                append(&fun_type.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
                            }
                            build_param_map(fun_type)
                        }
                        if !is_struct && len(s.return_types) > 0 && len(fun_type.return_types) == 0 {
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
                c.table.generic_templates[scope_name(s)] = Generic_Template{
                    name           = scope_name(s),
                    generic_params = s.generic_params,
                    ast            = s,
                    home_package   = c.current_package,
                    env            = env,
                }
                if len(s.typed_params) > 0 { c.declared_funs[scope_name(s)] = true }
                continue
            }
            // Already registered by a parent's register_scope_defs pass — skip.
            // That pass resolves params and return type as well.
            if scope_name(s) in c.table.fun_asts && c.table.fun_asts[scope_name(s)] == s {
                continue
            }
            existing_fn, existing_fn_found := type_env_get(env, scope_name(s))
            if existing_fn_found {
                if tf, is_fn := existing_fn.(^Type_Scope); is_fn && len(tf.params) > 0 && len(s.typed_params) > 0 {
                    check_error(c, s.span, TYPE_FUNCTION_ALREADY_DEFINED, scope_name(s))
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
                check_error(c, s.span, TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN, scope_name(s))
                clear(&s.return_types)  // suppress cascading return-path errors
            }
            if is_struct_type && len(s.typed_params) == 0 {
                // Pure data struct — create Type_Scope with kind=.Struct, no params
                struct_type := new(Type_Scope)
                struct_type.name = make_flat_name(c.current_package, scope_name(s))
                struct_type.home_package = c.current_package
                struct_type.kind = .Struct
                struct_type.is_packed = s.is_packed
                struct_type.ast = s
                struct_type.source_name = scope_name(s)
                struct_type.decl_env = env
                if struct_type.name in c.table.structs || struct_type.name in c.table.funs {
                    check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, scope_name(s))
                    continue
                }
                c.table.structs[struct_type.name] = struct_type
                register_scope_defs(c, struct_type, &struct_type.sd, s.defs)
                type_env_set(pub, scope_name(s), struct_type)
                c.table.fun_asts[scope_name(s)] = s
                c.table.fun_homes[scope_name(s)] = c.current_package
                // Attach as a member of the enclosing module struct (if any).
                // Mirrors the work extract_module_into_checked used to do post-hoc.
                if owner != nil {
                    if owner.types == nil { owner.types = make(map[string]Type) }
                    owner.types[scope_name(s)] = struct_type
                }
            } else {
                // Function or struct constructor (has params)
                if is_struct_type {
                    flat_name := make_flat_name(c.current_package, scope_name(s))
                    if flat_name in c.table.funs || flat_name in c.table.structs {
                        check_error(c, s.span, TYPE_TYPE_ALREADY_DEFINED, scope_name(s))
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
                fun_type.name = make_flat_name(c.current_package, scope_name(s))
                fun_type.home_package = c.current_package
                fun_type.ast = s
                fun_type.source_name = scope_name(s)
                fun_type.decl_env = env   // parameterized structs resolve fields on demand from here
                if is_struct_type {
                    fun_type.kind = .Struct
                    c.table.funs[fun_type.name] = fun_type
                    register_scope_defs(c, fun_type, &fun_type.sd, s.defs)
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
                // Resolve the signature now ONLY for parameterized structs — their
                // params feed on-demand field resolution (ensure_struct_signature).
                // FUNS resolve on demand at their call / body sites
                // (ensure_fun_signature), so a top-level fun whose param type comes
                // from an include resolves after includes are in, not before.
                if is_struct_type {
                    resolve_fun_signature(c, fun_type)
                }
                is_callable := !is_struct_type || len(s.typed_params) > 0
                // Register name in scope
                type_env_set(pub, scope_name(s), fun_type)
                c.table.fun_asts[scope_name(s)] = s
                c.table.fun_homes[scope_name(s)] = c.current_package
                if is_callable { c.declared_funs[scope_name(s)] = true }
                // Attach as a member of the enclosing module struct (if any).
                // Mirrors the work extract_module_into_checked used to do post-hoc.
                if owner != nil {
                    fun_type.parent_scope = env if env != nil else owner // file/enclosing scope -> module
                    if is_struct_type {
                        if owner.types == nil { owner.types = make(map[string]Type) }
                        owner.types[scope_name(s)] = fun_type
                    }
                    if is_callable {
                        if owner.functions == nil { owner.functions = make(map[string]^Type_Scope) }
                        owner.functions[scope_name(s)] = fun_type
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
            if enclosing_struct_scope(env) != nil { continue } // inside a class body
            // Register each foreign function in the type environment.
            // Pass env to resolve_type_expr so type names like `Event` resolve
            // to the current module's flavor when multiple modules export the
            // same name (otherwise the global symbol_home picks first-loader,
            // which is wrong for SDL2-vs-SDL3 setups).
            c.in_foreign_sig = true
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
            c.in_foreign_sig = false
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
                if main_mod != nil {
                    type_env_set(env, define_name(s), main_mod)
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
            // Sized slices and the shape shortcut lower into s.lowered_*; the
            // source declaration stays as written. See lower_sized_slice and
            // desugar_shape_shortcut — the shortcut also fires from
            // check_scope_body's early field-resolution pre-pass, which sees
            // the decl before this branch runs. Both are idempotent.
            lower_sized_slice(c, s, env)
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
                inits := decl_init(s)
                if len(inits) == 1 && len(s.names) > 1 {
                    // Multi-return destructure: x, y := call()
                    mra := new(Stmt_Multi_Return_Assign)
                    mra.span = s.span
                    mra.type_expr = decl_type(s)
                    mra.is_decl = true   // derived from a Stmt_Decl — bare names are declared
                    for n in s.names { append(&mra.names, n) }
                    for v in inits { append(&mra.values, v) }
                    append(&s.checked, Stmt(mra))
                } else {
                    // Parallel or single-name: one Stmt_Assign per name
                    for name, i in s.names {
                        a := new(Stmt_Assign)
                        a.name = name
                        a.span = s.span
                        a.type_expr = decl_type(s)
                        a.is_using = s.is_using
                        a.is_decl = true
                        a.slice_cap_expr = decl_cap(s)
                        if i < len(inits) { a.value = inits[i] }
                        append(&s.checked, Stmt(a))
                    }
                }
            }
            // Built, a struct's own declarations: its fields (typed as the
            // struct's), each value stored into one; the declaration is one
            // statement (its lowering's are that one).
            if b := fusing(c); b != nil && b.fuse.ts.kind == .Struct && b.code.block == b.fuse.root {
                graph_fuse_fields(b, s)
            }
            register_and_check_declarations(c, s.checked[:], env, owner, public_env)
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
            if s.name == "this_program" && !s.is_decl {
                // Its arena's arguments are read at main's entry, before any
                // code runs: checked, so their names resolve (the size is a
                // constant the codegen folds).
                if outer, ok := s.value.(^Expr_Call); ok && call_name(outer) == "Program" && len(call_args(outer)) > 0 {
                    if arena, is_call := call_args(outer)[0].(^Expr_Call); is_call {
                        for a in call_args(arena) { check_expr(c, a, env) }
                    }
                }
                continue
            }
            // Include expressions: scope-based resolution.
            // mara.X → look up X in std scope (stdlib modules)
            // bare Y → walk scope chain for sibling, lazy-load if not found
            if inc, is_include := s.value.(^Expr_Include); is_include {
                fuse_fail(c, "an include")
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

            // A bare-name assignment with `=` (is_decl == false) is a
            // REASSIGNMENT: the name must already be a binding. Without this
            // guard the registration path below would `type_env_set` a brand-new
            // binding for it, so `x = 7` on an undeclared `x` silently declared
            // it (and broadcast `x, y = 7` minted two locals — the bug that
            // motivated this). Bind it to Type_Error to recover.
            if is_undeclared_reassign(c, env, s.name, s.is_decl) {
                report_unresolved(c, s.span, env, s.name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
                type_env_set(env, s.name, Type_Error{})
                continue
            }
            // `_ = e` is a discard: `e` is checked for its own sake and nothing
            // is bound. `_` never enters scope, so one discard can't type the
            // next — `_ = f()` then `_ = g()` with different returns is fine.
            if s.name == "_" && !s.is_decl {
                c.expected_hint = nil
                dt, _ := fuse_expr(c, s.value, env)   // (built: its value, dropped)
                s.var_type = distinct_base(solidify_type(dt))
                continue
            }
            // Reassigning a by-address param would overwrite the caller's value.
            if !s.is_decl && is_immutable_param(env, s.name) {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, s.name)
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
            _, declared_here := scope_defines(env, s.name)
            if s.is_decl && declared_here {
                check_error(c, s.span, TYPE_VARIABLE_ALREADY_DECLARED_SCOPE, s.name)
                continue
            }
            // Struct field declarations live in their own namespace (accessed
            // via `obj.field`, never as a bare identifier), so they can't
            // shadow file-scope or module-scope bindings. Skip the walk when
            // the immediate parent is a class/struct scope.
            in_struct_body := parent_struct_scope(env) != nil
            if s.is_decl && !env_is_module(env) && !in_struct_body {
                // Shadowing of an enclosing local: walk the durable scope chain
                // above the current scope, below the module. Past the function
                // boundary a block's locals are out of sight (names_module), so
                // there is nothing there to shadow.
                start: ^Type_Scope = env.parent_scope if env != nil else nil
                crossed := false
                for sc := start; sc != nil && !sc.is_module; sc = sc.parent_scope {
                    if sc.kind != .Block { crossed = true }
                    t, found := scope_defines(sc, s.name)
                    out_of_sight := crossed && sc.kind == .Block && !names_module(t)
                    if found && !out_of_sight {
                        check_error(c, s.span, TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING, s.name)
                        break
                    }
                }
            }

            // Nothing can shadow a constant from an outer scope
            if s.name in c.table.constants && !declared_here {
                check_error(c, s.span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, s.name)
                continue
            }

            // Take binding: `name := take(T, storage)` (or with an annotation).
            // Same alias-into-caller-storage semantics as let — mark the name
            // as a view binding so it can't escape via return.
            if take_expr, is_take := s.value.(^Expr_Take); is_take {
                // Built as a declaration's value (a `let` binds the memory it
                // takes: no space of its own on the arena).
                fa: Fuse_Assign
                if b := fusing(c); b != nil {
                    fa.on = true
                    if s.is_decl { fa.decl, fa.field = fuse_decl_node(b, s, bound = take_expr.keyword == "let") }
                }
                defer fuse_assign_end(c, s, &fa)
                val_type: Type
                if fa.on && s.is_decl {
                    val_type, fa.value = fuse_expr(c, s.value, env, .Into, dest = graph_dest_var(s.name, fa.decl, nil if is_untyped(ann_type) else ann_type))
                } else if fa.on {
                    val_type, fa.value = fuse_expr(c, s.value, env, .Into, dest = graph_dest_var(s.name, NO_NODE, nil), temp = true, temp_span = s.span)
                } else {
                    val_type = check_expr(c, s.value, env)
                }
                fa.value_type = val_type
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
                // Built: the local, then its zero or its construction (a sized
                // slice's zero takes its capacity).
                bare := NO_NODE
                field := false
                if b := fusing(c); b != nil { bare, field = fuse_decl_node(b, s) }
                // (Large-value stack/arena routing is handled uniformly for
                // every value kind in check_storage_sizes — Pass 4 of check_scope.)
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
                cap: Maybe(Operand)
                if s.slice_cap_expr != nil {
                    cap_type, n := fuse_expr(c, s.slice_cap_expr, env)
                    if !is_any(cap_type) && !is_numeric(cap_type) {
                        check_error(c, s.span,
                            TYPE_SLICE_CAPACITY_INTEGER, type_name(cap_type))
                    }
                    cap = n.v
                }
                if b := fusing(c); b != nil && bare != NO_NODE {
                    if s.value != nil {
                        fuse_fail(c, "a function value's declaration")
                    } else if field {
                        // (A field is its struct's type; its capacity is
                        // the struct's to give.)
                        graph_fuse_bare(b, bare, b.g.type_[bare], nil, fuse_bare_args(c, b.g.type_[bare], s.span), s.span)
                    } else {
                        graph_fuse_typed(b, bare, ann_type)
                        args := fuse_bare_args(c, ann_type, s.span) if cap == nil else nil
                        if b := fusing(c); b != nil { graph_fuse_bare(b, bare, ann_type, cap, args, s.span) }
                    }
                }
                s.var_type = distinct_base(ann_type)
                s.env_type = ann_type
                type_env_set(env, s.name, ann_type)
                // (Uninit ptr/slice/field read-before-init tracking now lives in
                // the post-check flow pass — flow.odin.)
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
            // `x : T = void` (non-pointer T) — void is the universal
            // uninitialized marker: desugar to the skip-constructor node the
            // rest of the pipeline already understands (no construction, no
            // stores). Pointer targets keep void's null-init meaning.
            // (Read-before-write tracking for aggregates waits for the
            // zero-init stage — today's invalid_refs machinery flags
            // element WRITES as uses, which would forbid filling the
            // storage `= void` exists to leave fillable.) Declarations only:
            // this statement is then a Stmt_Decl's lowering, not source. A
            // reassignment `x = void` keeps its void (see check_bodies).
            if s.is_decl && is_void_literal(s.value) {
                if _, t_is_ptr := distinct_base(ann_type).(^Type_Ptr); !t_is_ptr {
                    s.value = new_clone(Expr_Skip_Constructor{span = s.span})
                }
            }
            // A bare reassignment (`q = expr`) carries no annotation, so
            // ann_type is untyped — but the target already has a type. Use it
            // as the hint so an all-infer RHS (e.g. `128 >> 1`) adopts the
            // target's signedness/width, matching the annotated-declaration
            // path. Without it the literal stays infer and codegen defaults to
            // signed — wrong shift (ashr vs lshr) and wrong overflow semantics.
            assign_hint := ann_type
            if !s.is_decl {
                if existing, ok := type_env_get(env, s.name); ok && !is_untyped(existing) {
                    assign_hint = existing
                }
            }
            c.expected_hint = assign_hint
            errors_before_value := c.errors
            // Built: a declaration's local, then its value, then the value
            // stored — once the statement is checked (its type known).
            fa: Fuse_Assign
            _, is_skip := s.value.(^Expr_Skip_Constructor)
            if b := fusing(c); b != nil {
                fa.on = true
                if s.is_decl {
                    fa.decl, fa.field = fuse_decl_node(b, s)
                    // Text or a slice's elements fill only a prefix of a new
                    // partial array: it is zero first — kept once the value's
                    // type says so. (Declared by its value, it is one only
                    // when that is text.)
                    may_be_text := false
                    #partial switch _ in s.value {
                    case ^Expr_String, ^Expr_Ident, ^Expr_Field_Access: may_be_text = true
                    }
                    if !is_skip && (is_untyped(ann_type) && may_be_text || is_partial_array(ann_type)) {
                        fa.prefix, fa.prefixed = graph_fuse_prefix(b, s.name, fa.decl, s.span), true
                    }
                }
            }
            defer fuse_assign_end(c, s, &fa)
            val_type: Type
            if fa.on && !is_skip && !(!s.is_decl && is_void_literal(s.value)) {
                // A declaration's value is built where it goes (its type,
                // when not written, known once it is).
                if s.is_decl {
                    at := graph_dest_var(s.name, fa.decl, nil if is_untyped(ann_type) else ann_type)
                    val_type, fa.value = fuse_expr(c, s.value, env, .Into, dest = at, temp_span = s.span)
                } else {
                    // (Into a variable that holds a value: what builds in
                    // place builds in a temporary, then is written.)
                    vt: Type = distinct_base(assign_hint) if !is_untyped(assign_hint) else nil
                    val_type, fa.value = fuse_expr(c, s.value, env, .Into, dest = graph_dest_var(s.name, NO_NODE, vt), temp = true, temp_span = s.span)
                }
            } else {
                val_type = check_expr(c, s.value, env)
            }
            fa.value_type = val_type
            // `x : []utf8 = "lit"` — writable view over rodata; sized slices
            // (`[:N]utf8`, cap_expr set) copy into owned backing and pass.
            if s.slice_cap_expr == nil {
                // Unannotated (`s := RED[:]`): the value's own type is the slot's.
                check_no_literal_slice_binding(c, val_type if is_untyped(ann_type) else ann_type, s.value, s.span)
            }
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
                byte_flow := check_byte_flow(c, ann_type, s.value, val_type, s.span)
                byte_read := byte_flow == .Read
                if ann_is_distinct && (!val_is_array && !val_is_struct_lit || val_carries_matching_distinct) {
                    // Byte-buffer reinterpret read overrides the nominal type
                    // match — `t : Tag = mem[0]` reads sizeof(Tag) bytes
                    // regardless of the distinct wrapper (no slice headers).
                    if byte_read {
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
                    continue
                }
                // Unwrap distinct types for structural checking (but store the distinct type)
                check_ann := distinct_base(ann_type)
                // The struct/union-literal and byte-buffer-reinterpret branches below
                // only apply when the value IS a literal or a byte read. A plain value
                // (call, variable, field) must fall through to the general nominal
                // compatibility check — the literal helpers no-op on non-literals, so
                // without this gate `p : Point = Color()` slipped through unchecked.
                value_needs_literal_handling := val_is_struct_lit || byte_read
                // Validate assignment compatibility (same as in check_assign)
                if sd := as_scope_body(check_ann); sd != nil && len(sd.fields) > 0 && value_needs_literal_handling {
                    if !literal_matched(s.value, check_ann) { check_struct_literal_assign(c, s.span, s.value, sd, env) }
                    // Byte-buffer reinterpret read into a struct (slice form): a
                    // span shorter than the struct is a partial fill (tail zero);
                    // only a span LARGER than the struct overruns it -> error.
                    if sl, sl_ok := s.value.(^Expr_Slice); sl_ok && byte_read {
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
                    continue
                }
                if ut, ok := check_ann.(^Type_Union); ok && value_needs_literal_handling {
                    if !literal_matched(s.value, check_ann) { check_union_literal_assign(c, s.span, s.value, ut, env) }
                    s.var_type = distinct_base(ann_type)
                    s.env_type = ann_type
                    type_env_set(env, s.name, ann_type)
                    continue
                }
                if fa, ok := check_ann.(^Type_Fixed_Array); ok {
                    // Byte-buffer reinterpret read into a fixed-array destination:
                    // `arr : [2]byte = bytes[0]` reads sizeof([2]byte) = 2 bytes
                    // from `bytes` at offset 0. Same shape as the scalar
                    // reinterpret-read paths below, generalized: destination
                    // type drives read size, fixed-array fits the pattern.
                    if byte_read {
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
                        check_array_assign(c, s.span, s.name, fa, val_type, s.value)
                    }
                    // (Large-value stack/arena routing handled uniformly in
                    // check_storage_sizes — Pass 4 of check_scope.)
                } else if pa, ok := check_ann.(^Type_Partial_Array); ok && byte_read && is_byte_buffer(val_type) {
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
                } else if byte_read && is_byte_buffer(val_type) {
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
                } else if byte_read {
                    // Byte buffer reinterpret read via index: x : int = mem[0]
                    // Size comes from the annotation type; bounds checked at runtime
                } else if byte_flow == .View {
                    // A range of bytes viewed as a 1-byte-element slice
                    // (check_byte_flow vetted the element width): the byte
                    // family is mutually compatible, nothing more to check.
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
            } else {
                // No type annotation: variables solidify.
                // But DON'T overwrite if the variable already has a declared type
                // (e.g. verts2 += [...] should not replace verts2's [6]f32 type).
                //
                // Struct field declarations live in their own namespace, so a
                // `field := value` decl shouldn't be misread as a reassignment of
                // a same-named binding in an outer file / module scope. Suppress
                // the walk-up lookup when we're directly inside a struct body.
                in_struct_body := parent_struct_scope(env) != nil
                // Un-annotated struct field: adopt the finalized layout width
                // (resolved in the register pass) for numeric fields, so the
                // constructor local's var_type matches the field slot codegen
                // GEPs into. Slice/struct fields fall through to the normal decl
                // path (which sets up slice-backing / aliasing).
                if in_struct_body {
                    if cs := parent_struct_scope(env); cs != nil {
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
                loc_scope: ^Type_Scope
                already_declared: bool
                if in_struct_body {
                    // A field redecl inside its own struct body — never a leak
                    // (loc_scope stays nil), just records the prior binding. Reads
                    // this env level's own durable scope (== the old env.types).
                    if env != nil {
                        if t, ok := env.types[s.name]; ok {
                            existing_type = t
                            already_declared = true
                        }
                    }
                } else if s.is_decl {
                    // Declarations skip module-scope bindings: function bodies
                    // are free to shadow module-level names (including the
                    // module's own self-binding, e.g. `shader` inside
                    // `module gfx.shader`). Matches the shadowing-check
                    // policy at the top of this branch.
                    existing_type, loc_scope, already_declared = type_env_locate_below_module(env, s.name)
                } else {
                    existing_type, loc_scope, already_declared = type_env_locate(env, s.name)
                }
                // Field-leak guard: reassignment targeting a name that resolves in
                // an ancestor class scope is a field written without receiver.
                if already_declared && loc_scope != nil && loc_scope.kind == .Struct && !loc_scope.is_module {
                    if is_real_field(&loc_scope.sd, s.name) {
                        check_error(c, s.span,
                            TYPE_FIELD_ASSIGN_THROUGH_RECEIVER,
                            s.name, loc_scope.name, s.name)
                        continue
                    }
                }
                if !already_declared {
                    // `x := void` has no type to infer from. Require an
                    // explicit annotation: `x : T = void` declares x
                    // uninitialized. (Same rule the old #skip_constructor had.)
                    _, is_skip := s.value.(^Expr_Skip_Constructor)
                    if is_skip || is_void_literal(s.value) {
                        check_error(c, s.span, TYPE_VOID_INIT_REQUIRES_EXPLICIT, s.name, s.name)
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
                        // Only warn about a silently-untyped binding when the
                        // value checked cleanly. If checking it already emitted a
                        // diagnostic (e.g. `d := Nonexist{...}` now reports the
                        // unknown type), "type checking bypassed" is both false
                        // and redundant noise.
                        if is_untyped(binding_type) && c.errors == errors_before_value {
                            check_warning(c, s.span, TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING, s.name)
                        }
                        // Storing a cstring (e.g. `e := GetError()`) is banned
                        // — the pointer's terminator is only fresh at the
                        // moment of the call. Convert at the boundary instead
                        // (scan to []utf8, or pass straight to another C call).
                        if is_cstring(binding_type) {
                            check_error(c, s.span, TYPE_CSTRING_FOREIGN_ONLY)
                        }
                    }
                    s.var_type = distinct_base(binding_type)
                    s.env_type = binding_type
                    type_env_set(env, s.name, binding_type)
                } else {
                    // Reassignment with `void` DE-INITIALIZES. Scalars and
                    // pointers re-enter the read-before-write pool (the
                    // existing tracking handles whole-name reads/writes);
                    // aggregates skip the marking for now — element writes
                    // would be flagged as uses by today's machinery. For
                    // non-pointers codegen emits nothing (see gen_stmt);
                    // pointer `p = void` keeps its null store.
                    if is_void_literal(s.value) {
                        s.var_type = distinct_base(existing_type)
                        s.env_type = existing_type
                        continue
                    }
                    // Reassigning a slice var with a literal would repoint its
                    // header at rodata (and silently drop any sized backing).
                    check_no_literal_slice_binding(c, existing_type, s.value, s.span)
                    // Reassignment: check value type matches existing variable type.
                    // A byte-buffer reinterpret read (off16 = mem[off] or mem[lo:hi])
                    // is recognized here too — same as the decl-init and field-assign
                    // paths: the read size comes from the target type, not the byte
                    // value. Without this the RHS types as a bare `byte` and fails.
                    is_byte_flow := check_byte_flow(c, existing_type, s.value, val_type, s.span) != .None
                    if !is_byte_flow && !coerce_deferred(c, val_type, existing_type, s.span) && !coerce_deferred(c, existing_type, val_type, s.span) && types_incompatible(existing_type, val_type) && !value_preserving_widen(val_type, existing_type) {
                        emit_assign_var_error(c, s.span, val_type, s.name, existing_type, s.value)
                    }
                    maybe_stamp_byte_view(c, existing_type, s.value)
                    if is_infer(val_type) {
                        check_literal_overflow(c, s.value, existing_type, s.span)
                    }
                    s.var_type = distinct_base(existing_type)
                    s.env_type = existing_type
                }
            }
        case ^Stmt_Multi_Assign:
            // Its assignments, each checked whole (both passes: a target's
            // store is typed by the second) in turn. Several reassigned
            // together (`a, b = b, a`) take every value first: each held in
            // a temporary at its target's type, then each target written
            // from its own (fuse_parallel_end).
            par: Fuse_Parallel
            parallel := fusing(c) != nil && fuse_is_parallel(s)
            saved_parallel := c.parallel
            if parallel { c.parallel = &par }
            for a in s.assigns {
                one := []Stmt{a}
                register_and_check_declarations(c, one, env, public_env = public_env)
                check_bodies(c, one, env)
            }
            c.parallel = saved_parallel
            if parallel { fuse_parallel_end(c, &par) }
        case ^Stmt_Multi_Return_Assign:
            ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)
            // (Built below: one call's outputs. `?` on it, and values
            // assigned in parallel, are the builder's.)
            if len(s.values) != 1 { fuse_fail(c, "a destructure of several values") }

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
                    // Built: the names it declares, the call, the branch on
                    // its err, then each other output written in turn.
                    mr: Graph_Destructure
                    if b := fusing(c); b != nil { mr = graph_fuse_destructure(b, s) }
                    // (The call is checked as a call, not an expression: it has
                    // no type of its own here.)
                    if fusing(c) != nil { c.asked, c.asked_written, c.fused = .Value, .Explicit, {} }
                    check_call(c, inner_call, env)
                    call := c.fused
                    c.fused = {}
                    if b := fusing(c); b != nil && mr.on {
                        if !call.ok {
                            fuse_fail(c, "a `?` on no call built")
                        } else {
                            b.g.type_[call.v.op] = nil
                            mr.call = graph_try_after(b, try_node, call.v)
                        }
                    }
                    returns := call_return_list(c, inner_call, env)
                    rts := enclosing_return_types(env)
                    if len(returns) == 0 || !is_err_type(returns[len(returns)-1]) {
                        check_error(c, s.span, TYPE_TRY_REQUIRES_ERR_RETURN)
                    } else if len(rts) == 0 || !is_err_type(rts[len(rts)-1]) {
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
                                    target_type, at := fuse_expr(c, s.targets[i], env, .Place)
                                    mr.place = at.v
                                    if cname, is_const := write_root_constant(c, s.targets[i]); is_const {
                                        check_error(c, s.span, TYPE_CANNOT_WRITE_CONSTANT, cname)
                                    }
                                    if !is_any(target_type) && !is_any(resolved_type) {
                                        if !types_equal(target_type, resolved_type) {
                                            check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_RETURN,
                                                type_name(resolved_type), type_name(target_type))
                                        }
                                    }
                                }
                                append(&s.var_types, distinct_base(resolved_type))
                                if b := fusing(c); b != nil && mr.on { graph_fuse_destructure_write(b, &mr, s, i) }
                            }
                        }
                    }
                } else {
                    // Single RHS (multi-return call): x, y := call()
                    // Built: the names it declares, the call, then each of
                    // its outputs written to its name — or its target — in
                    // turn. (A broadcast of one value is the builder's.)
                    // (A broadcast's value is built in each target's copy,
                    // not here: a call's, built before that was known, is
                    // left out.)
                    mr: Graph_Destructure
                    mark: Graph_Mark
                    _, of_call := s.values[0].(^Expr_Call)
                    if b := fusing(c); b != nil {
                        mark = graph_fuse_mark(b)
                        if of_call { mr = graph_fuse_destructure(b, s) }
                    }
                    val_type: Type
                    call: Fused
                    if of_call {
                        val_type, call = fuse_expr(c, s.values[0], env)
                    } else {
                        val_type = check_expr(c, s.values[0], env)
                    }
                    mr.call = call.v
                    if b := fusing(c); b != nil && mr.on && call_return_list(c, s.values[0], env) == nil {
                        graph_fuse_drop_since(b, mark)
                        mr.on = false
                    }
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
                                    if is_undeclared_reassign(c, env, name, s.is_decl) {
                                        report_unresolved(c, s.span, env, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
                                    } else if !s.is_decl && is_immutable_param(env, name) {
                                        check_error(c, s.span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name)
                                    }
                                    type_env_set(env, name, resolved_type)
                                } else if i < len(s.targets) && s.targets[i] != nil {
                                    if pname, immut := write_root_immutable_param(s.targets[i], env); immut {
                                        check_error(c, s.span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, pname)
                                    }
                                    target_type, at := fuse_expr(c, s.targets[i], env, .Place)
                                    mr.place = at.v
                                    if cname, is_const := write_root_constant(c, s.targets[i]); is_const {
                                        check_error(c, s.span, TYPE_CANNOT_WRITE_CONSTANT, cname)
                                    }
                                    if !is_any(target_type) && !is_any(resolved_type) {
                                        if !types_equal(target_type, resolved_type) {
                                            check_error(c, s.span, TYPE_CANNOT_ASSIGN_MULTI_RETURN,
                                                type_name(resolved_type), type_name(target_type))
                                        }
                                    }
                                }
                                append(&s.var_types, distinct_base(resolved_type))
                                if b := fusing(c); b != nil && mr.on { graph_fuse_destructure_write(b, &mr, s, i) }
                            }
                        }
                    } else if is_any(val_type) {
                        for name in s.names {
                            if name != "" {
                                type_env_set(env, name, Type_Error{})
                            }
                        }
                    } else {
                        // Broadcast: `a, b = v` (or `a, b := v`). Desugar into one
                        // assignment per target that shares the RHS, then register +
                        // check + (later) codegen those Stmt_Assigns directly — codegen
                        // never sees a broadcast. Routing through the normal single-
                        // assign path is what gives each target its declare-vs-reassign
                        // rule (the undeclared-on-`=` guard, `:=` declares) and its type
                        // check for free, and it fixes the old non-main-fn segfault:
                        // gen_broadcast_assign built Stmt_Assigns at codegen time with
                        // hand-set fields; real type-checked assigns lower correctly.
                        // The RHS is re-evaluated per target — bind an effectful RHS to
                        // a local first if exactly-once evaluation matters. Each
                        // target's is a copy, checked once as its own (the value
                        // itself was checked above, to tell the forms apart).
                        for name, i in s.names {
                            a := new(Stmt_Assign)
                            a.span = s.span
                            a.is_decl = s.is_decl
                            a.value = clone_expr(s.values[0])
                            if name != "" {
                                a.name = name
                            } else if i < len(s.targets) && s.targets[i] != nil {
                                a.target = s.targets[i]
                            }
                            append(&s.checked, Stmt(a))
                        }
                        // (Its statement is its copies': graph_stmt_kind's Other.)
                        if b := fusing(c); b != nil { graph_fuse_stmt_kind(b, graph_stmt_kind(s)) }
                        register_and_check_declarations(c, s.checked[:], env, owner, public_env)
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

// Fill lit.array_values[0..<size] with the broadcast value: slot 0 reuses the
// original expr, later slots are independent clones. clone_expr clears
// `resolved_func` and `type_` on each Expr_Call it copies, so each clone is
// re-checked here — without this a constructing broadcast (`all Cell()`) would
// reach codegen with an unresolved call ("unknown function"). The caller must
// have already type-checked lit.broadcast_value against the element type.
fill_broadcast_array_slots :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, size: int, elem: Type, env: ^Type_Scope) {
    clear(&lit.array_values)
    resize(&lit.array_values, size)
    for i in 0..<size {
        if i == 0 {
            lit.array_values[0] = lit.broadcast_value
        } else {
            cloned := clone_expr(lit.broadcast_value)
            if is_anonymous_literal(cloned) { c.expected_hint = elem }
            check_expr(c, cloned, env)
            lit.array_values[i] = cloned
        }
    }
}

// A field's `{all <expr>}`, in the field pass: typed as its field, an array.
// Its value is checked where the field's value is (check_field_broadcast).
expand_broadcast_array_literal :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, field_type: Type, field_name: string, span: Span, env: ^Type_Scope) {
    #partial switch _ in distinct_base(field_type) {
    case ^Type_Fixed_Array, ^Type_Partial_Array:
        lit.type_ = field_type
        c.broadcast_fields[rawptr(lit)] = {field_name, span}
    case:
        check_error(c, span,
            TYPE_BROADCAST_LITERAL_ALL_FIELD_REQUIRES,
            field_name, type_name(field_type))
    }
}

// A field's `{all <expr>}` (typed by expand_broadcast_array_literal): the
// expression checked once against the array's element type — built, then the
// fill — and each slot given a checked clone.
check_field_broadcast :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, env: ^Type_Scope, fl: ^Fuse_Lit) {
    field := c.broadcast_fields[rawptr(lit)]
    field_type := lit.type_
    size := 0
    elem_type: Type
    #partial switch t in distinct_base(field_type) {
    case ^Type_Fixed_Array:   size, elem_type = t.size, t.elem
    case ^Type_Partial_Array: size, elem_type = t.size, t.elem
    }
    if is_anonymous_literal(lit.broadcast_value) { c.expected_hint = elem_type }
    val_type: Type
    if b := fusing(c); b != nil && fl != nil {
        val: Fused
        val_type, val = fuse_expr(c, lit.broadcast_value, env)
        if b := fusing(c); b != nil { graph_fuse_fill(b, lit, field_type, fl.dest, val.v) }
        fl.built = true
    } else {
        val_type = check_expr(c, lit.broadcast_value, env)
    }
    // (Its slots' copies are checked, not built: the fill is.)
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
    if !is_any(val_type) && types_incompatible(elem_type, val_type) {
        check_error(c, field.span,
            TYPE_BROADCAST_VALUE_FIELD_TYPE_EXPECTED,
            field.name, type_name(val_type), type_name(elem_type), type_name(field_type))
        return
    }
    if is_infer(val_type) {
        check_literal_overflow(c, lit.broadcast_value, elem_type, field.span)
    }
    fill_broadcast_array_slots(c, lit, size, elem_type, env)
}

// Phase-2 checker for a single function/method/struct/module body.
// check_scope_body resolves a scope's signature (fields/params/return) and
// then — unless signature_only is set — checks the body. Set signature_only
// from the Phase-2 pre-pass to populate struct fields before any function
// body is checked, so forward references to structs work regardless of
// declaration order.
check_scope_body :: proc(c: ^Checker, s: ^Stmt_Scope, env: ^Type_Scope, signature_only: bool = false, instance: ^Struct_Instance = nil) {
    if len(s.generic_params) > 0 && instance == nil { return }
    // A scope's body builds its own graph, or none: not its parent's.
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
    if s.is_intrinsic {
        // Body is compiler-generated. Validate the declared signature against
        // the LLVM intrinsic's expected shape (arity + element types).
        if !signature_only {
            fun_type_raw, _ := type_env_get(env, scope_name(s))
            if ft, ft_ok := fun_type_raw.(^Type_Scope); ft_ok {
                check_llvm_intrinsic_signature(c, ft, s.intrinsic_name, s.span)
                // (Its graph: its params and results, no code.)
                if c.gb != nil {
                    if f := graph_fuse_begin(c.gb, ft, s, s.body[:], .Explicit); f != nil { fuse_end(c, f) }
                }
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
    fun_type_raw, _ := type_env_get_owned_first(env, scope_name(s))

    ft, ft_ok := fun_type_raw.(^Type_Scope)
    if instance != nil { ft, ft_ok = instance.st, true }   // (a struct instance: its own)
    if !ft_ok { return }

    // On-demand: a fun's body binds its params and reads its returns, so resolve
    // its signature here if no call site demanded it first.
    if ft.kind == .Fun { ensure_fun_signature(c, ft) }

    // On-demand: a parameterized struct's ctor params (and trailing-err returns)
    // resolve here too — its field initializers reference the params, so they
    // must be ready before the field pass and the param pre-registration below
    // read them. Same resolve_param_type / Infer_Cell machinery as funs, so an
    // untyped numeric ctor param settles at the width the body pins it to
    // (solidify_param_defaults, after the body check). Resolved against the decl
    // env (`env`), exactly like the fields. Idempotent via the len==0 guard.
    if ft.kind == .Struct && len(ft.params) == 0 && len(s.typed_params) > 0 {
        for tp in s.typed_params {
            pt := resolve_param_type(c, tp, env, s.span)
            append(&ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
        }
        build_param_map(ft)
    }
    if ft.kind == .Struct && len(ft.return_types) == 0 && len(s.return_types) > 0 {
        for rte in s.return_types {
            append(&ft.return_types, resolve_type_expr(rte, c, s.span, env = env))
        }
    }

    // On-demand signature resolution: memoize the signature pass so it runs once
    // per scope no matter how many sites demand it, and break cycles. Only the
    // signature_only pre-pass is gated — the full body check below always runs.
    if signature_only && ft.kind == .Struct {
        if ft.sig_state != .Unresolved { return }  // already Resolved, or In_Progress = cycle
        ft.sig_state = .In_Progress
    }
    // Function-scoped (not inside the if): never strand a scope In_Progress —
    // any exit from the signature pass (the bail below, or an early return on an
    // error path) marks it Resolved so a later demand doesn't mistake a finished
    // scope for an unbreakable cycle. (Struct fields only; fun param/return
    // signatures own sig_state via ensure_fun_signature.) No-op otherwise.
    defer if signature_only && ft.kind == .Struct && ft.sig_state == .In_Progress { ft.sig_state = .Resolved }

    // Env structure for callable scopes:
    //
    //   class:   [ns_env: Self/types/methods/consts] <- [child: params/lets/body]
    //   fun:     [ns_env: Self/own-types/funcs]      <- [child: params/body]
    //   method:  same shape as fun — its ns_env just parents to the class's ns_env
    //
    // The class's namespace and its constructor body are distinct envs: the
    // namespace holds the shared surface (Self, nested types, sibling methods,
    // constants) and is the parent of both the constructor body and any method
    // bodies. The constructor body env adds constructor-only bindings (params,
    // class-body `let`/`:=` decls) without leaking them to siblings.
    //
    // A method is just a fun whose enclosing scope is a struct — it takes the
    // ft.kind == .Fun path below with no special-casing. The defs-parent walk
    // stops at the class's ns_env (a class_scope marker), so the method's defs
    // layer parents to the class and sees its members.

    // One shape for structs AND funs (class is a struct alias; a method is just a
    // fun nested in a struct): a defs layer (ns_env) whose durable `scope` IS this
    // scope's own ft — so its members / nested ::defs / Self resolve, and the
    // no-closures rule + nesting fall out of the parent_scope graph uniformly,
    // with no struct-vs-fun branch on how scopes chain.
    parent_env := env
    if ft.kind == .Struct || ft.kind == .Fun {
        parent_env = ft   // the defs layer IS this scope's own ft (members/::defs/Self)
        // Funs register their nested ::defs lazily here; structs already did at
        // module-registration time (so ft.types is populated). Gate on s.defs,
        // not s.body — a pure type-namespace fun has defs but no runtime body.
        if ft.kind == .Fun && ft.types == nil && len(s.defs) > 0 {
            register_scope_defs(c, ft, &ft.sd, s.defs)
        }
    }

    // The body is the function/ctor's OUTERMOST block: params + top-level locals
    // land on its .Block scope (parent_scope = ft, via enclosing_callable_scope of
    // the defs layer), and nested if/for/defer blocks chain to it. So the durable
    // scope_local_lookup walk reaches every local of the current function and
    // stops at ft (the no-closures boundary).
    child := type_env_block_child(parent_env)
    if instance != nil {
        for name, t in instance.subst { type_env_set(child, name, t) }   // (its type params)
    }

    // Pre-register struct params in the field-resolution scope so that
    // field defaults / field types can reference them (e.g.
    // `max_vertices := max_v` or `using items: [n]item`).
    if ft.kind == .Struct {
        for p in ft.params {
            type_env_set(child, p.name, p.type_)
        }
    }

    // Pre-register constants with bare-name aliases for sibling access.
    // ft.consts maps bare → ^Stmt_Define (s.name has been mangled by
    // register_scope_defs at this point, so we register both forms).
    // For classes, the canonical home is the namespace env so methods reach
    // them via walk-up. We also mirror onto child (the constructor body env)
    // so check_define's "already pre-registered" early-return — which checks
    // pub.types directly without walking — still recognises them.
    // MUST run before the field-resolution loop below: a field declared as
    // `pool : [..CAP]T` with `CAP :: 1 << 16` a sibling const needs CAP in
    // c.table.constants when its array size resolves — scope consts Just
    // Work regardless of where in the body they sit.
    if ft.consts != nil {
        for bare, def in ft.consts {
            if def.value == nil { continue }
            // Feed the annotation as an expected-type hint, mirroring check_define
            // and the runtime-decl path. This loop — not check_define — is where
            // a LOCAL `::` const's value is actually checked (it registers the
            // const into the scope, so check_define then early-returns on it), so
            // an annotated `FOO : A : Dup{...}` needs the hint here to resolve the
            // bare variant literal to its union instead of falling through to the
            // hint-less inference / ambiguity path.
            ann := resolve_type_expr(def.type_expr, c, def.span, env = child)
            c.expected_hint = ann if !is_any(ann) else nil
            fc := fuse_const_begin(c, def)
            val_type := fuse_const_value(c, &fc, def, child, ann)
            fuse_const_end(c, &fc, def, val_type)
            def.var_type = val_type
            c.table.constants[define_name(def)] = def.value
            c.table.constants[bare] = def.value
            type_env_set(child, define_name(def), val_type)
            type_env_set(child, bare, val_type)
            // A use resolves to this declaration through the scope (not by name).
            if child.sd.consts == nil { child.sd.consts = make(map[string]^Stmt_Define) }
            child.sd.consts[bare] = def
            // Mirror onto the defs layer (ft) whenever there is one — structs and
            // funs (methods included) — so sibling methods / nested funs reach the
            // const by bare name.
            if parent_env == ft {
                type_env_set(ft, define_name(def), val_type)
                type_env_set(ft, bare, val_type)
            }
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
    data_fields := extract_fields_from_body(s.body)
    added_any_field := false
    // Register-pass flag: `fn <name>` annotations may reference later locals
    // that haven't been added to env yet. Suppress errors during this scan;
    // the body-check pass re-resolves with all locals visible.
    prev_in_register := c.in_register_pass
    c.in_register_pass = true
    defer c.in_register_pass = prev_in_register
    for &field in data_fields {
        if _, already := ft.field_map[field.name]; already { continue }
        field_type: Type
        if field.type_expr != nil {
            field_type = resolve_type_expr(field.type_expr, c, s.span, env=child)
            // `f : T = void` (non-pointer T) — per-field uninitialized
            // marker: desugar to the skip node the constructor codegen
            // already recognizes (field left unconstructed; the struct
            // memset still zeroes it today). Pointer fields keep void's
            // null meaning.
            if field.default_value != nil && is_void_literal(field.default_value) {
                if _, t_is_ptr := distinct_base(field_type).(^Type_Ptr); !t_is_ptr {
                    field.default_value = new_clone(Expr_Skip_Constructor{span = s.span})
                }
            }
            if field.default_value == nil {
                check_uninitialized_class_decl(c, field.span if field.span.file != "" else s.span, field.name, field_type)
            } else if is_numeric(field_type) {
                // Pin earlier deferred fields feeding this annotated field's
                // default to its width: `per_row : i32 = size / cell` settles
                // size and cell at i32.
                pin_field_refs(c, field.default_value, field_type, ft, s.span)
            }
        } else if field.default_value != nil {
            _, is_uninit := field.default_value.(^Expr_Skip_Constructor)
            if is_uninit || is_void_literal(field.default_value) {
                // No type to infer an uninitialized field from — annotate:
                // `f : T = void`.
                check_error(c, s.span, TYPE_VOID_INIT_REQUIRES_EXPLICIT, field.name, field.name)
                field_type = Type_Error{}
            } else {
                field_type = infer_field_type_from_default(c, field.default_value, child, ft)
                // A struct field's type is its layout: one the default doesn't
                // determine (`k := .Big`, a form inference doesn't cover) needs
                // an annotation — never an untyped field reaching codegen.
                if s.kind == .Struct && is_any(field_type) {
                    check_error(c, expr_span(field.default_value)^, TYPE_FIELD_TYPE_NOT_INFERRED, field.name, field.name)
                    field_type = Type_Error{}
                }
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
    // A fieldless struct is a legal zero-size type — it can be defined, declared
    // (`x : Foo`), constructed (`Foo()`), held as a field, and passed around, the
    // same as Go's `struct{}` or a Rust unit struct. The construction path gives
    // it a self-return + init function below (see extract_checked_scope), so no
    // codegen hazard remains; there is deliberately no "must have a field" error.
    if len(ft.params) == 0 && len(s.typed_params) > 0 {
        for tp in s.typed_params {
            pt := resolve_type_expr(tp.type_expr, c, s.span, env=child)
            append(&ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
        }
        build_param_map(ft)
    }
    if len(ft.return_types) == 0 && len(s.return_types) > 0 {
        for rte in s.return_types {
            rt := resolve_type_expr(rte, c, s.span, env=child)
            append(&ft.return_types, rt)
        }
    }
    // The register-pass scan ends here — the body check below must run with
    // errors ON, or the "body pass re-resolves and emits the real error"
    // contract the scan's silence depends on never happens. (The defer above
    // still guards early exits inside the scan.)
    c.in_register_pass = prev_in_register

    // Recurse into nested struct definitions so their field lists are populated
    // too — a sibling field default or a forward-referencing outer function that
    // reaches `x.nested.field` needs the nested type's fields, not just its name.
    // Mirrors the module-level signature hoist (check_module Pass 2a), one level
    // down. Idempotent: the field loop skips already-mapped fields.
    for stmt in s.defs {
        if nested, ok := stmt.(^Stmt_Scope); ok && nested.kind == .Struct &&
            len(nested.typed_params) == 0 && len(nested.generic_params) == 0 {
            check_scope_body(c, nested, child, signature_only = true)
        }
    }

    // Pre-pass bails here — signature resolved, body deferred to main pass.
    if signature_only {
        ft.sig_state = .Resolved
        return
    }

    // A fun's graph is built as its body is checked.
    f: ^Graph_Fuse
    if c.gb != nil && ft.kind == .Fun {
        record_return_bindings(ft, s)   // (its named results are locals)
        f = graph_fuse_begin(c.gb, ft, s, s.body[:], .Explicit)
    } else if c.gb != nil && ft.kind == .Struct && !ft.is_module {
        // (Its code: its fields' values. An instance's node is the compiler's.)
        f = graph_fuse_begin(c.gb, ft, s, s.body[:], .Synthetic if instance != nil else .Explicit)
    }
    defer if f != nil { fuse_end(c, f) }

    // Nothing to descend into only when BOTH are empty. A pure-namespace struct
    // (only nested `::` defs, no runtime body) still needs check_scope below so
    // its nested types get a full body check — without it their field defaults
    // never desugar and construction zero-inits them.
    if len(s.body) == 0 && len(s.defs) == 0 { return }

    // Footgun check (struct only): warn when a field initializer hands
    // #self to anything that could read partially-constructed state
    // while later field decls still come below it. Lives after the
    // signature_only bail so it fires once per struct (the pre-pass and
    // full pass both reach this function — only the full pass continues
    // past the bail).
    if ft.kind == .Struct {
        check_early_self_decls(c, s.body)
    }

    // Register params in scope (is_param is derived from ft.params, not flagged).
    for tp, i in s.typed_params {
        if i < len(ft.params) {
            type_env_set(child, tp.name, ft.params[i].type_)
        }
    }

    // Register named return bindings as fields in the function scope
    for rb in s.return_bindings {
        rb_type := resolve_type_expr(rb.type_expr, c, s.span, env=child)
        type_env_set(child, rb.name, rb_type)
    }

    // Expand `all <expr>` broadcast defaults on array-typed fields against the
    // field's resolved type, before the body check below reads them: codegen
    // needs array_values populated, and a partial-array target (`[..6]Camera`)
    // isn't handled by the inline literal path. Runs per struct in the full pass
    // (errors on), so a field default is validated as part of checking the
    // constructor — there is no separate struct-default pass.
    if ft.kind == .Struct {
        for field in ft.fields {
            if lit, ok := field.default_value.(^Expr_Struct_Literal); ok && lit.is_broadcast {
                expand_broadcast_array_literal(c, lit, field.type_, field.name, s.span, child)
            }
        }
    }

    // Split mode: compile-time defs come from s.defs, runtime from s.body.
    check_scope(c, s.body, child, scope_defs = s.defs)

    // Freeze any deferred default-param cells now the body has pinned them to the
    // width they're used at (or, for funs, unpinned → the sole numeric return type).
    // After this the signature is concrete, so callers and codegen never see an open
    // cell. Constructors (.Struct) defer their params too — a parameterized struct's
    // field initializers are the body that pins them.
    if ft.kind == .Fun || ft.kind == .Struct {
        solidify_param_defaults(c, ft)
    }

    // Return check (void / all-err functions can fall off the end) now lives in
    // the post-check flow pass (flow.odin, flow_missing_return) — it recomputes
    // the same verdict over the durable ft.body. Removed from the inline walk as
    // the first analysis to migrate off the during-check traversal.
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

// A loop's collection that is no plain place (graph_fuse_items): checked
// into the local the loop walks — a literal built there, text or a call
// seen through its place's view when it has a header, else its value.
fuse_loop_items :: proc(c: ^Checker, fl: ^Graph_For, s: ^Stmt_For, env: ^Type_Scope) -> Type {
    b := fusing(c)
    gi := graph_fuse_items(b, fl)
    #partial switch _ in s.collection {
    case ^Expr_Array, ^Expr_Struct_Literal:
        from := b.nodes
        d := graph_dest_var("items", fl.coll_slot, nil)
        t := fuse_store_into(c, s.collection, env, d, fl.span)
        // (Held as itself: an untyped literal's elements settled.)
        t = solidify_type(t)
        if b := fusing(c); b != nil {
            if graph_loop_view_of(t) != nil { fuse_fail(c, "a literal loop over its view") }
            graph_fuse_retype_literal(b, from, b.nodes, t)
            graph_fuse_typed(b, fl.coll_slot, t)
        }
        return t
    }
    t, r := fuse_expr(c, s.collection, env, .Either)
    if b := fusing(c); b != nil {
        if view := graph_loop_view_of(t); view != nil {
            _, is_self := s.collection.(^Expr_Self)
            fills := is_partial_array(t) && graph_fills_prefix(s.collection)
            graph_fuse_items_view(b, fl, &gi, r.v, r.place, t, view, is_self, fills)
        } else {
            graph_fuse_typed(b, fl.coll_slot, t)
            fuse_store_finish(c, s.collection, t, r, graph_dest_var("items", fl.coll_slot, t), fl.span)
        }
    }
    return t
}

// Phase-2 checker for a `for` statement: dispatches to collection-for, range-for, or C-style.
check_for_body :: proc(c: ^Checker, s: ^Stmt_For, env: ^Type_Scope) {
    child := type_env_block_child(env)
    // Built around its checks (graph_for).
    b := fusing(c)
    fl: Graph_For
    if b != nil { fl = graph_fuse_for(b, s) }
    defer if b != nil { graph_fuse_for_end(b, &fl, s) }
    if s.is_collection_for {
        // (A plain place: walked where the loop needs it, not here. Anything
        // else is held first, in a local the loop walks: fuse_loop_items.)
        coll_type: Type
        if b != nil && !graph_pure_place(s.collection) {
            coll_type = fuse_loop_items(c, &fl, s, child)
        } else {
            coll_type = check_expr(c, s.collection, child)
        }

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
             Type_CString, Type_Utf8, Type_Byte, Type_Numeric,
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
            type_env_set(child, s.elem_var, elem_type)
        }
        if s.index_var != "" {
            // The index counts at slice header width, like a slice's len.
            type_env_set(child, s.index_var, slice_header_width_type)
        }

        s.elem_type_ = distinct_base(elem_type)

        if b != nil { graph_fuse_for_collection(b, &fl, s) }
        check_scope(c, s.body, child)
    } else if s.is_range {
        // The counter first, then each bound at its type (known once both
        // are checked).
        bounds := [2]int{-1, -1}
        if b != nil { graph_fuse_range_counter(b, &fl, s) }
        low_type, lo := fuse_expr(c, s.range_low, child)
        if fusing(c) != nil {
            bounds[0] = len(b.fuse.checks)
            fl.lo = graph_fuse_range_bound(b, lo.v, low_type, s.span)
        }
        high_type, hi := fuse_expr(c, s.range_high, child)
        if fusing(c) != nil {
            bounds[1] = len(b.fuse.checks)
            fl.hi = graph_fuse_range_bound(b, hi.v, high_type, s.span)
        }

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

        // Ban descending ranges where both bounds are compile-time-known: `..`
        // only counts up, so `4..-3` would silently iterate zero times. Catch
        // it loudly at build time (matches Odin's "Invalid interval range").
        // Bounds that aren't comptime-known are left as an empty loop.
        lo_const, lo_ok := evaluate_comptime_int(c, s.range_low, child)
        hi_const, hi_ok := evaluate_comptime_int(c, s.range_high, child)
        if lo_ok && hi_ok && lo_const > hi_const {
            check_error(c, s.span, TYPE_DESCENDING_RANGE, lo_const, hi_const, lo_const, hi_const)
        }

        type_env_set(child, s.loop_var, iter_type)
        s.var_type = distinct_base(iter_type)

        if b != nil { graph_fuse_range(b, &fl, s, bounds) }
        check_scope(c, s.body, child)
    } else {
        // C-style for or simple for-condition loop.
        // Register init in the loop scope so the loop var is visible in
        // condition, post, and body.
        if s.init != nil {
            init_stmts: [dynamic]Stmt
            append(&init_stmts, s.init)
            register_and_check_declarations(c, init_stmts[:], child)
            check_bodies(c, init_stmts[:], child)
        }
        if b != nil { graph_fuse_for_runs(b, &fl, s) }
        cond_type: Type
        cond: Fused
        if s.condition != nil {
            cond_type, cond = fuse_expr(c, s.condition, child)
        } else {
            cond_type = check_expr(c, s.condition, child)
        }
        if b != nil && s.condition != nil { graph_fuse_for_cond(b, &fl, s, cond.v) }
        if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
            check_error(c, s.span, TYPE_CONDITION_BOOL, type_name(cond_type))
        }
        if s.post != nil {
            // Both passes, as the init: a plain reassignment (`k += 1`) is
            // typed by the first (it went unchecked). (Built into the step's
            // run, in a segment of its own put after the body, where it runs.)
            step: Graph_Step
            if b != nil { step = graph_fuse_step(b, &fl) }
            post_stmts: [dynamic]Stmt
            append(&post_stmts, s.post)
            register_and_check_declarations(c, post_stmts[:], child)
            check_bodies(c, post_stmts[:], child)
            if b != nil { graph_fuse_step_end(b, &fl, step) }
        }
        check_scope(c, s.body, child)
    }
}

// Phase-2 checker for a `return` statement.
check_return_body :: proc(c: ^Checker, s: Stmt_Return, env: ^Type_Scope) {
    rts := enclosing_return_types(env)
    n_expected := len(rts)
    n_supplied := len(s.values)

    // Trailing err return slots can be implicitly filled with `.Ok` (the err
    // type's zero value), so `return id` in a `(File_Id, err)` fn is shorthand
    // for `return id, .Ok`. n_min is the minimum number of values a return
    // must supply: everything except trailing err slots.
    n_err_trailing := 0
    for i := n_expected - 1; i >= 0; i -= 1 {
        if is_err_type(rts[i]) {
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
    // Built: each value at its result's type, then the return.
    vals := make([dynamic]Operand, 0, len(s.values), context.temp_allocator)
    if count_ok {
        for val, i in s.values {
            if i >= n_expected { break }
            expected := rts[i]
            c.expected_hint = expected
            // (Text returned as a partial array — a literal, or a constant,
            // known once checked: its temporary and zero reserved before it.)
            text_pa, text_slot := false, NO_NODE
            text_held: Graph_Later
            if b := fusing(c); b != nil && is_partial_array(expected) {
                if _, is_text := val.(^Expr_String); is_text {
                    text_pa, text_slot = true, graph_slot(b, "temp", expected, s.span)
                    graph_fuse_zero_var(b, text_slot, expected, s.span)
                } else {
                    text_held = graph_fuse_later(b)
                }
            }
            use, at := fuse_use_type(val, expected, s.span)
            held: Graph_Later
            if _, to_slice := distinct_base(expected).(^Type_Slice); to_slice {
                if b := fusing(c); b != nil { held = graph_fuse_later(b) }
            }
            vt, r := fuse_expr(c, val, env, .Either, dest = use, temp_span = at)
            if k, folds := graph_constant(val).?; folds && k.is_text && text_held.reserved {
                if b := fusing(c); b != nil {
                    graph_fuse_later_begin(b, &text_held)
                    text_pa, text_slot = true, graph_slot(b, "temp", expected, s.span)
                    graph_fuse_zero_var(b, text_slot, expected, s.span)
                    if !graph_fuse_later_end(b, &text_held) { fuse_fail(c, "a text constant returned across runs") }
                }
            }
            if fusing(c) != nil && !text_pa {
                append(&vals, fuse_value_as(c, val, vt, r, expected, s.span, {to = expected}, &held))
            } else if b := fusing(c); b != nil {
                // Text returned as a partial array: built into one — a
                // temporary, zero, then the text — read.
                fuse_store_finish(c, val, vt, r, graph_dest_var("temp", text_slot, expected), s.span)
                append(&vals, graph_read(b, graph_var(b, "temp", text_slot, expected, s.span), expected, s.span))
            }
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
    if b := fusing(c); b != nil { graph_fuse_return(b, vals[:], s.span) }
    // Escape analysis: prevent returning pointers/slices to local memory.
    // (Return-escape analysis — returning &local / a struct whose slice fields
    //  point at local memory / a laundered call result — now runs in the
    //  post-check escape pass, escape.odin.)
}

check_bodies :: proc(c: ^Checker, stmts: []Stmt, env: ^Type_Scope) {
    // (Former per-scope struct-signature pre-pass removed: struct fields resolve
    // ON DEMAND at the use site via ensure_struct_signature — field access,
    // construction, literal matching each pull the struct's signature when they
    // need it. Field DEFAULTS are no longer checked by a separate pass either:
    // a struct's body IS its constructor, so its field decls — including `all`
    // broadcast defaults — are validated in check_scope_body's full pass, the
    // same path that checks any decl. Function signatures resolve in Phase 1.)

    for stmt in stmts {
        fs := fuse_stmt(c, stmt)
        defer fuse_stmt_end(fs)
        #partial switch s in stmt {
        case ^Stmt_Scope:
            check_scope_body(c, s, env)

        case ^Stmt_If:
            // Comptime `#if` was folded away before the checker ran, so every
            // Stmt_If here is a runtime conditional.
            cond_type, cond := fuse_expr(c, s.condition, env)
            if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
                check_error(c, s.span, TYPE_CONDITION_BOOL_2, type_name(cond_type))
            }
            // Built: the branch, then each block as it is checked.
            b := fusing(c)
            fi: Graph_If
            if b != nil { fi = graph_fuse_if(b, cond.v, s) }
            child := type_env_block_child(env)
            check_scope(c, s.body, child)
            if b != nil { graph_fuse_else(b, &fi, s) }
            if len(s.else_body) > 0 {
                else_child := type_env_block_child(env)
                check_scope(c, s.else_body, else_child)
            }
            if b != nil { graph_fuse_if_end(b, &fi) }
            // (Definite-assignment branch-merge now lives in the flow pass.)

        case ^Stmt_For:
            check_for_body(c, s, env)

        case ^Stmt_Match:
            check_match(c, s, env)

        case Stmt_Call:
            // In-place struct override: `var{ a = x; b = y }` as a statement,
            // where the literal's name is a struct VARIABLE — validate the
            // fields against the variable's struct and tag the node so codegen
            // applies the writes in place. Detected at STATEMENT position so a
            // value-position literal (`p := P{...}`) is never mistaken for an
            // override; codegen's get_struct makes the final var-vs-type call.
            handled_override := false
            if lit, is_lit := s.expr.(^Expr_Struct_Literal); is_lit && lit.name != "" {
                if vt, _, found := type_env_locate(env, lit.name); found {
                    if sd := resolve_to_struct_type(c, vt); sd != nil {
                        lit.type_ = vt   // the variable's: its fields are written
                        // Built: each field's value written into the variable's.
                        ol := Fuse_Lit{e = lit}
                        saved := c.lit
                        if b := fusing(c); b != nil {
                            ol.gl, ol.built = graph_fuse_override(b, graph_dest_var(lit.name, NO_NODE, vt), sd), true
                            c.lit = &ol
                        }
                        check_struct_literal_fields(c, lit, sd, lit.span, env, override = true)
                        c.lit = saved
                        lit.override_target = lit.name
                        handled_override = true
                    }
                }
            }
            if !handled_override {
                rt, _ := fuse_expr(c, s.expr, env)
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
                        check_error(c, s.span, TYPE_DISCARDED_RETURN, call_name(call))
                    }
                }
                // A NAMED struct-literal statement whose name resolved to nothing
                // (Type_Error comes only from the unresolved-name fallthrough; a
                // real construction returns its type) is an undefined name — e.g.
                // `bogus{ x = 1 }`, which used to no-op silently. A struct-variable
                // override was already handled above, so this only fires for genuine
                // garbage (or a variant misused as a bare statement).
                if lit, is_lit := s.expr.(^Expr_Struct_Literal); is_lit && lit.name != "" {
                    // Only "undefined" if the name is truly unbound. A name that
                    // IS a binding — e.g. a local struct variable whose in-place
                    // override didn't resolve — is defined; don't mislabel it.
                    _, _, name_bound := type_env_locate(env, lit.name)
                    if _, is_err := rt.(Type_Error); is_err && !name_bound {
                        check_error(c, s.span, TYPE_UNDEFINED_IDENTIFIER, lit.name)
                    }
                }
            }

        case ^Stmt_Multi_Assign:
            // Already checked in register_and_check_declarations (each
            // assignment, both passes)
        case ^Stmt_Multi_Return_Assign:
            // Destructure was fully checked during registration (s.checked empty).
            // Broadcast desugared into s.checked there; run the body pass on those
            // so field/index targets get their per-target check and bare-name env
            // updates apply (same handoff as Stmt_Decl). Empty list → no-op.
            check_bodies(c, s.checked[:], env)

        case Stmt_Return:
            check_return_body(c, s, env)

        case Stmt_Break:
            if b := fusing(c); b != nil { graph_fuse_loop_exit(b, s.span, is_break = true) }
        case Stmt_Continue:
            if b := fusing(c); b != nil { graph_fuse_loop_exit(b, s.span, is_break = false) }

        case ^Stmt_Defer:
            // Body is checked in a child env so any declarations inside the
            // defer stay scoped to the deferred block. At runtime the body
            // executes on scope exit (LIFO across defers in the same scope).
            // (Built as its own code.)
            child := type_env_block_child(env)
            b := fusing(c)
            gd: Graph_Defer
            if b != nil { gd = graph_fuse_defer(b, s) }
            check_scope(c, s.body, child)
            if b != nil { graph_fuse_defer_end(b, gd) }

        // Declarations were already fully handled in register_and_check_declarations
        case ^Stmt_Assign:
            // Complex LHS: dispatch on target kind. Simple reassignment falls
            // through to the env-update path below.
            if s.target != nil {
                #partial switch t in s.target {
                case ^Expr_Field_Access:
                    check_field_assign(c, s, env)
                    // The target's own type, for the program graph's place.
                    if t.type_ == nil { t.type_ = s.target_type }
                case ^Expr_Index:        check_index_assign(c, s, env)
                case ^Expr_Slice:        check_slice_assign(c, s, env)
                case ^Expr_Unary:
                    if t.op == .Caret {
                        check_deref_assign(c, s, env)
                        if t.type_ == nil { t.type_ = s.target_type }
                    } else {
                        check_error(c, s.span, TYPE_INVALID_ASSIGNMENT_TARGET)
                    }
                case:
                    check_error(c, s.span, TYPE_INVALID_ASSIGNMENT_TARGET)
                }
                if name, is_const := write_root_constant(c, s.target); is_const {
                    check_error(c, s.span, TYPE_CANNOT_WRITE_CONSTANT, name)
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
            check_bodies(c, s.checked[:], env)
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

check_define :: proc(c: ^Checker, s: ^Stmt_Define, env: ^Type_Scope, public_env: ^Type_Scope = nil) {
    // pub: where the constant binding is registered. In module-scope mode this
    // is the module env (so siblings see it); otherwise it's env (back-compat).
    pub := public_env if public_env != nil else env
    // A use resolves to this declaration through its scope (not by name).
    if pub.sd.consts == nil { pub.sd.consts = make(map[string]^Stmt_Define) }
    if s.name not_in pub.sd.consts { pub.sd.consts[s.name] = s }
    // Skip if already pre-registered (parent's body scan)
    _, pre_registered := scope_defines(pub, define_name(s))
    if pre_registered {
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
    c.table.constants[define_name(s)] = s.value

    // Built: its value, as the constant's code (fuse_const_begin).
    fc := fuse_const_begin(c, s)
    defer fuse_const_end(c, &fc, s, s.env_type)

    ann_type := resolve_type_expr(s.type_expr, c, s.span, env = env)
    // Feed the annotation to the value as an expected-type hint, mirroring the
    // runtime-decl path (search `c.expected_hint = assign_hint`). This lets an
    // annotated `::` bound to a bare union-variant literal — `FOO : A : Dup{...}`
    // — resolve at the union-hint branch in check_expr_impl and TYPE the literal
    // as its union, instead of falling through untyped to codegen's null-pointer
    // backstop (CODE_STRUCT_LITERAL_UNTYPED_EXPR): check_union_literal_assign
    // below validates the fields but never sets lit.type_. With no annotation we
    // clear the hint so a genuinely hint-less variant literal (`FOO :: Dup{...}`)
    // reaches the bare-variant inference / ambiguity path cleanly instead of
    // inheriting a stale hint left by a previous statement.
    c.expected_hint = ann_type if !is_any(ann_type) else nil
    val_type := fuse_const_value(c, &fc, s, env, ann_type)

    if !is_any(ann_type) {
        // Distinct + non-literal: use nominal compatibility (mirrors Stmt_Assign path)
        _, ann_is_distinct := ann_type.(^Type_Distinct)
        _, val_is_array := s.value.(^Expr_Array)
        _, val_is_struct_lit := s.value.(^Expr_Struct_Literal)

        if ann_is_distinct && !val_is_array && !val_is_struct_lit {
            if types_incompatible(ann_type, val_type) {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE,
                    type_name(val_type), define_name(s), type_name(ann_type))
            }
            if is_infer(val_type) {
                check_literal_overflow(c, s.value, ann_type, s.span)
            }
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, define_name(s), ann_type)
            return
        }

        // Literal assignment: delegate to structural check helpers (unwrap distinct).
        // A plain (non-literal) value must instead reach the nominal-compatibility
        // fallback below — the literal helpers no-op on non-literals, which let
        // `p : Point = Color()` slip through unchecked.
        check_ann := distinct_base(ann_type)
        value_needs_literal_handling := val_is_struct_lit || is_byte_buffer(val_type) || is_byte_buffer_index_read(s.value)
        if sd := as_scope_body(check_ann); sd != nil && len(sd.fields) > 0 && value_needs_literal_handling {
            check_struct_literal_assign(c, s.span, s.value, sd, env)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, define_name(s), ann_type)
            return
        }
        if ut, ok := check_ann.(^Type_Union); ok && value_needs_literal_handling {
            check_union_literal_assign(c, s.span, s.value, ut, env)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, define_name(s), ann_type)
            return
        }
        if fa, ok := check_ann.(^Type_Fixed_Array); ok {
            check_array_assign(c, s.span, define_name(s), fa, val_type, s.value)
            s.var_type = distinct_base(ann_type)
            s.env_type = ann_type
            type_env_set(pub, define_name(s), ann_type)
            return
        }

        // Fallback: simple structural compatibility
        if types_incompatible(ann_type, val_type) {
            check_error(c, s.span, TYPE_CANNOT_ASSIGN_CONSTANT_TYPE,
                type_name(val_type), define_name(s), type_name(ann_type))
        }
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, ann_type, s.span)
        }
        s.var_type = distinct_base(ann_type)
        s.env_type = ann_type
        type_env_set(pub, define_name(s), ann_type)
        return
    }

    s.var_type = distinct_base(val_type)
    s.env_type = val_type
    type_env_set(pub, define_name(s), val_type)
}

// Validate that a struct literal's fields match a struct definition:
// every literal field exists and has the right type, and no struct fields are missing.
check_struct_literal_fields :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, st: ^Scope_Body, span: Span, env: ^Type_Scope, override := false) {
    ensure_struct_signature(c, st)  // resolve fields on demand before matching the literal
    if !override { check_literal_constructs(c, lit, st) }
    if override && lit.type_ == nil { lit.type_ = sd_type_scope(st) }   // `Foo(){...}`: Foo's fields
    // Built (the literal being built): its construction, then each field
    // stored as it is checked.
    fl := c.lit if c.lit != nil && c.lit.e == lit else nil
    c.lit = nil
    gl: ^Graph_Literal
    if b := fusing(c); b != nil && fl != nil {
        if override {
            gl = fl.gl
        } else {
            // (Its constructor's arguments, then it; a variant's defaults.)
            args: []Operand
            if ts, is_scope := lit.type_.(^Type_Scope); is_scope && ts.kind == .Struct && !ts.is_module && !lit.zero_init {
                args = fuse_ctor_args(c, ts, lit.span)
            }
            if b := fusing(c); b != nil { gl = graph_fuse_literal(b, lit, lit.type_, fl.dest, args) }
            if gl != nil { fuse_variant_defaults(c, gl.variant, lit, gl.parent, lit.span) }
        }
        fl.built = gl != nil
    }
    // Positional form (`Foo{a, b, c}`): match entries to struct fields by index.
    if lit.positional {
        // Multi-return spread: `Foo{call()}` where call's return list matches
        // Foo's fields one-to-one (with normal compatibility, including
        // array→slice coercion). Codegen detects the same pattern and routes
        // the call's sret args into temps then into the struct.
        // (Only a call can be one; its type is the positional path's too.)
        // (Built: the call, once, then each field its result.)
        probed: Type
        if call, is_call := lit.fields[0].value.(^Expr_Call); is_call && len(lit.fields) == 1 && len(st.fields) > 1 {
            single_val := lit.fields[0].value
            spread: Fused
            if gl != nil {
                probed, spread = fuse_expr(c, single_val, env, .Value)
            } else {
                probed = check_expr(c, single_val, env)
            }
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
                    if b := fusing(c); b != nil && gl != nil && !graph_fuse_spread(b, gl, lit, call, spread.v) {
                        fuse_fail(c, "a spread literal of no call")
                    }
                    return
                }
            }
            if gl != nil {
                fuse_fail(c, "a spread literal that doesn't match")   // (its field is checked again)
                gl = nil
            }
            // Fall through to the regular positional path so the user gets a
            // useful error if the call's return list doesn't match the struct.
        }
        user_fields := st.fields[first_user_field(st):]
        if len(lit.fields) > len(user_fields) {
            check_error(c, span, TYPE_CLASS_FIELDS_POSITIONAL_VALUES,
                st.name, len(user_fields), len(lit.fields))
        }
        for field, i in lit.fields {
            if i >= len(user_fields) { break }
            sf := user_fields[i]
            // Only set the hint for anonymous nested literals — these need
            // the field type to determine their shape. Other expression
            // shapes (idents, calls, field-accesses, arithmetic) self-type
            // and a stray hint can mistype intermediate sub-expressions.
            if needs_field_type_hint(field.value) {
                c.expected_hint = sf.type_
            }
            ft: Type
            if i == 0 && probed != nil {
                ft = probed
            } else if gl != nil {
                ft = fuse_store_into(c, field.value, env, graph_fuse_literal_field(gl, "", i), lit.span)
            } else {
                ft = check_expr(c, field.value, env)
            }
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
            if needs_field_type_hint(field.value) || needs_union_variant_hint(sf.type_, field.value) {
                c.expected_hint = sf.type_
            }
            ft: Type
            if gl != nil {
                ft = fuse_store_into(c, field.value, env, graph_fuse_literal_field(gl, field.name, 0), lit.span)
            } else {
                ft = check_expr(c, field.value, env)
            }
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

// A literal builds its struct as a call without arguments does (`Foo{...}`
// is `Foo(){...}`) — unless it is the zero value `Foo{0}`: its constructor
// must need no argument, and can't fail (a literal has no err to hand back).
check_literal_constructs :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, sd: ^Scope_Body) {
    ts := sd_type_scope(sd)
    if lit.zero_init || ts == nil || ts.kind != .Struct || ts.is_module { return }
    name := lit.name
    if name == "" { name = ts.source_name if ts.source_name != "" else ts.name }
    if count_required_params(ts) > 0 {
        qualified := name
        if ts.home_package != "" && strings.index_byte(name, '.') < 0 {
            qualified = fmt.tprintf("%s.%s", ts.home_package, name)
        }
        check_error(c, lit.span, TYPE_EXPECTS_ARGS, qualified, len(ts.params), fn_params_desc(ts), 0)
    } else if len(ts.return_types) > 0 {
        check_error(c, lit.span, TYPE_LITERAL_CAN_FAIL, name, name)
    }
}

// Whether a literal's own check already matched its fields to type t — it
// was typed t there (named, or by the annotation's hint; a union's variant,
// by name): a declaration of type t doesn't match them again, so each node
// is checked once.
literal_matched :: proc(value: Expr, t: Type) -> bool {
    lit, is_lit := value.(^Expr_Struct_Literal)
    if !is_lit || lit.type_ == nil { return false }
    if ut, is_union := t.(^Type_Union); is_union {
        // Typed as the union, or as the variant's own struct (`Circle{1}`).
        if lit.name not_in ut.tag_map { return false }
        if types_equal(distinct_base(lit.type_), t) { return true }
        st, is_struct := lit.type_.(^Type_Scope)
        return is_struct && ut.variant_structs[lit.name] == st.name
    }
    return types_equal(distinct_base(lit.type_), t)
}

check_struct_literal_assign :: proc(c: ^Checker, span: Span, value: Expr, st: ^Scope_Body, env: ^Type_Scope) {
    lit, lit_ok := value.(^Expr_Struct_Literal)
    if !lit_ok { return }
    check_struct_literal_fields(c, lit, st, span, env)
}

check_union_literal_assign :: proc(c: ^Checker, span: Span, value: Expr, ut: ^Type_Union, env: ^Type_Scope) {
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

// Resolve a bare variant name to its owning union, when the name identifies a
// single union across the whole program. register_enum_variants already
// collapses a name shared by two enums/unions to the "" sentinel in
// variant_to_enum, so a non-empty mapping guarantees one owner; we then locate
// that union by its synthetic <Name>_Tag enum. Returns nil for an unknown or
// ambiguous name — those have no single inferred type, so the caller leaves the
// literal untyped (a hinted slot resolves it; a hint-less one is left to the
// existing fallthrough).
variant_owner_union :: proc(c: ^Checker, variant: string) -> ^Type_Union {
    owner_enum, mapped := c.table.variant_to_enum[variant]
    if !mapped || owner_enum == "" { return nil }
    for _, ut in c.table.unions {
        if ut.tag_enum != nil && ut.tag_enum.name == owner_enum {
            return ut
        }
    }
    return nil
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

// An anonymous literal (`{...}` or `{all x}`) takes its shape from the slot it
// fills. A broadcast's value fills element slots, so a nested one
// (`{all {all x}}`) needs the element type as its hint, not the outer target.
is_anonymous_literal :: proc(e: Expr) -> bool {
    lit, ok := e.(^Expr_Struct_Literal)
    return ok && lit.name == "" && lit.type_expr == nil
}

// A NAMED variant literal (`Rect{...}`) in a union-typed field or argument
// needs the union as its hint so check_expr's union-context branch can resolve
// it. Unlike needs_field_type_hint this fires for named literals — the name
// identifies the variant, the hint supplies the owning union.
needs_union_variant_hint :: proc(field_type: Type, value: Expr) -> bool {
    ut, ok := distinct_base(field_type).(^Type_Union)
    if !ok { return false }
    lit, lit_ok := value.(^Expr_Struct_Literal)
    return lit_ok && lit.name != "" && lit.name in ut.tag_map
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
check_array_struct_literal :: proc(c: ^Checker, lit: ^Expr_Struct_Literal, fa: ^Type_Fixed_Array, env: ^Type_Scope, lit_t: Type = nil) {
    clear(&lit.array_values)
    resize(&lit.array_values, fa.size)
    // Built (the literal being built): zero, then each element into its
    // slot, as written; a broadcast, its value then the fill.
    fl := c.lit if c.lit != nil && c.lit.e == lit else nil
    c.lit = nil
    gl: ^Graph_Literal
    if b := fusing(c); b != nil && fl != nil {
        // (A named form's elements in the order they are written.)
        if lit.is_broadcast {
            fl.built = true   // (its value, then the fill: below)
        } else {
            gl = graph_fuse_literal(b, lit, lit_t, fl.dest)
            fl.built = gl != nil
        }
    }
    elem_t := graph_elem_type(lit_t) if gl != nil else nil

    // Broadcast: `{all <expr>}` — check the expression once against the
    // element type, then fill every slot with a clone so codegen emits
    // independent stores per element.
    if lit.is_broadcast {
        if is_anonymous_literal(lit.broadcast_value) { c.expected_hint = fa.elem }
        val_type: Type
        val: Fused
        if fl != nil && fl.built && fusing(c) != nil {
            val_type, val = fuse_expr(c, lit.broadcast_value, env)
            if b := fusing(c); b != nil { graph_fuse_fill(b, lit, lit_t, fl.dest, val.v) }
        } else {
            val_type = check_expr(c, lit.broadcast_value, env)
        }
        // (Its slots' copies are checked, not built: the fill is.)
        outer := fuse_suspend(c)
        defer fuse_resume(c, outer)
        if types_incompatible(fa.elem, val_type) {
            check_error(c, lit.span, TYPE_BROADCAST_VALUE_TYPE_EXPECTED,
                lit.name, type_name(val_type), type_name(fa.elem))
            return
        }
        if is_infer(val_type) {
            check_literal_overflow(c, lit.broadcast_value, fa.elem, lit.span)
        }
        // Re-check each clone (shared with the field-default path) so a
        // constructing broadcast like `all Cell()` keeps its resolved_func per
        // slot; codegen then constructs the element in place per slot.
        fill_broadcast_array_slots(c, lit, fa.size, fa.elem, env)
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
            // An anonymous nested literal (`{{1, 2}, {3, 4}}`) takes its shape
            // from the element type, as a struct field's does.
            if needs_field_type_hint(field.value) { c.expected_hint = fa.elem }
            val_type: Type
            if gl != nil {
                val_type = fuse_store_into(c, field.value, env, graph_fuse_literal_elem(gl, i, elem_t), lit.span)
            } else {
                val_type = check_expr(c, field.value, env)
            }
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
        if needs_field_type_hint(field.value) { c.expected_hint = fa.elem }
        val_type: Type
        if gl != nil {
            val_type = fuse_store_into(c, field.value, env, graph_fuse_literal_elem(gl, idx, elem_t), lit.span)
        } else {
            val_type = check_expr(c, field.value, env)
        }
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

// A string literal may not initialize or be assigned to a plain `[]utf8`
// location: a literal is `[..N]utf8` STORAGE (read-only rodata bytes), not a
// view — a slice binding would be a writable header over those bytes, and
// element writes through it compile and then page-fault at runtime.
// Parameter position stays legal (by-value params are immutable, so the free
// view is safe). Sized-slice decls (`[:N]utf8 = "lit"`) copy into owned
// backing and are exempt — callers gate on slice_cap_expr.
// A slice variable or field is a writable view, so it can't be bound to
// read-only bytes: a string literal, or a constant (`RED`, `RED[1:]`, `K.b`),
// which lives in the program's read-only data. (A slice PARAMETER is
// read-only, so passing either to one is fine.)
check_no_literal_slice_binding :: proc(c: ^Checker, target: Type, value: Expr, span: Span) {
    if value == nil { return }
    if _, is_slice := distinct_base(target).(^Type_Slice); !is_slice { return }
    if _, is_lit := value.(^Expr_String); is_lit {
        check_error(c, span, TYPE_SLICE_CANNOT_BIND_STRING_LITERAL)
    } else if name, is_const := write_root_constant(c, value); is_const {
        check_error(c, span, TYPE_SLICE_CANNOT_BIND_CONSTANT, name, name)
    }
}

check_array_assign :: proc(c: ^Checker, span: Span, name: string, fa: ^Type_Fixed_Array, val_type: Type, value: Expr = nil) {
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
        // literal-type change). Same element check; the size check ensures
        // the source CONTENT fits in the fixed-array storage. A string
        // literal's TYPE carries the quantized tier cap (string_literal_cap)
        // while its content is the byte length — compare the content, so
        // `fa : [16]utf8 = "hi"` doesn't trip over the literal's [..64] tier.
        src_size := pv.size
        if lit, lit_ok := value.(^Expr_String); lit_ok {
            src_size = len(lit.value)
        }
        if types_incompatible(fa.elem, pv.elem) {
            check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
                type_name(val_type), name, type_name(fa))
        } else if src_size > 0 && src_size > fa.size {
            check_error(c, span, TYPE_ARRAY_ELEMENTS_CAPACITY,
                src_size, name, fa.size)
        }
    } else if !is_any(val_type) {
        check_error(c, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE,
            type_name(val_type), name, type_name(fa))
    }
}

check_deref_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Scope) {
    un := s.target.(^Expr_Unary)
    // Built: the place the pointer points at, then the value into it.
    ptr_type, ptr := fuse_expr(c, un.operand, env, .Place, temp_span = un.span)
    place := NO_VALUE
    if b := fusing(c); b != nil {
        if p, ok := ptr_type.(^Type_Ptr); ok { place = graph_op_value(b, .Deref, .Explicit, un.span, p.elem, "", ptr.v) }
    }
    val_type := fuse_store(c, s, place, env)
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
    // (Writing a local ref through a param pointer — `param^ = &local` — is caught
    //  by the post-check escape pass, escape.odin.)
}

check_index_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Scope) {
    ix := s.target.(^Expr_Index)
    lower_subscript_dots(ix.expr, ix.index)
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
    // Built: the element's place — its collection's, the index at the
    // header's width — then the value into it. (Bytes written as another
    // type are a view: the builder's.)
    coll_type, coll := fuse_expr(c, ix.expr, env, .Place, temp_span = ix.span)
    target_type := distinct_base(coll_type)
    s.target_type = target_type
    ix.type_ = index_elem_type(target_type)   // the target names one element
    base := coll.v
    if b := fusing(c); b != nil {

        if pt, is_ptr := target_type.(^Type_Ptr); is_ptr {
            base = graph_op_value(b, .Deref, .Implied, ix.span, pt.elem, "", coll.v)
        }
    }
    if fa, ok := target_type.(^Type_Fixed_Array); ok && fa.index_type != nil {
        c.expected_hint = fa.index_type
    }
    idx_type, at := fuse_expr(c, ix.index, env)
    place := NO_VALUE
    if b := fusing(c); b != nil {
        place = graph_op_value(b, .Index, .Explicit, ix.span, ix.type_, "", base, fuse_index_value(b, at.v, idx_type, ix.span))
    }
    // Hint the value with the element type so an infer literal (`a[i] = 0`)
    // resolves to the element width rather than defaulting. Byte targets are
    // left unhinted — their reinterpret-write path (below) types the value on
    // its own and accepts any width.
    if fa, ok := target_type.(^Type_Fixed_Array); ok {
        c.expected_hint = fa.elem
    } else if pa, ok := target_type.(^Type_Partial_Array); ok {
        if _, is_byte := pa.elem.(Type_Byte); !is_byte { c.expected_hint = pa.elem }
    } else if sl, ok := target_type.(^Type_Slice); ok {
        if _, is_byte := sl.elem.(Type_Byte); !is_byte { c.expected_hint = sl.elem }
    }
    // (Into bytes, the value is written as the type the checker finds it
    // is, below: the element's place is then a view of that.)
    val_type, fs := fuse_store_value(c, s, place, env)
    defer fuse_store_write(c, s, &fs, s.target_type, s.assign_value_type if is_byte_buffer(coll_type) else nil, ix.is_big_endian)

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

    // A byte buffer's indexed write is a reinterpret write of sizeof(value)
    // bytes (`buf[off] = some_u32` writes 4). An untyped number literal has no
    // concrete width — rather than assume one (which silently wrote 8 bytes for
    // `buf[i] = 6`, or trapped at the buffer's end), require an explicit cast to
    // pin the width. Concrete-typed values carry their own width and are fine.
    if is_infer(val_type) {
        byte_target := is_byte_slice(target_type) || is_byte_partial_array(target_type)
        if !byte_target {
            if fa, ok := target_type.(^Type_Fixed_Array); ok {
                if _, is_byte := fa.elem.(Type_Byte); is_byte { byte_target = true }
            }
        }
        if byte_target {
            check_error(c, s.span, TYPE_BYTE_BUFFER_WRITE_UNTYPED)
            return
        }
    }

    // A reinterpret write stores the value's raw bytes: plain data only.
    if is_byte_slice(target_type) || is_byte_partial_array(target_type) || is_byte_fixed_array(target_type) {
        check_byte_write(c, val_type, s.span)
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
    }

    // Non-byte element write into a fixed array, partial array, or slice. The
    // value must reach the element slot without losing information:
    //   - same type, or the 8-bit memory family (byte/c8/utf8/i8/u8) that all
    //     lower to i8 and may alias a slot — buffer_elem_compatible; or
    //   - a value-preserving widen (u16->u32, i32->i64, f32->f64), which
    //     gen_index_assign materializes through gen_expr_coerced (zext/sext/
    //     fpext) at the store.
    // Anything else — narrowing (i64->i32) or a same-width cross-sign
    // (i32->u32) — is a located error: the index-store codegen can't insert
    // that conversion, so without this gate the mismatch reaches codegen and
    // emits a typed store LLVM rejects. An explicit cast is the fix.
    elem_type: Type
    elem_size := -1   // >= 0 marks a fixed array, for the [%d]%s diagnostic
    #partial switch t in target_type {
    case ^Type_Fixed_Array:   elem_type = t.elem; elem_size = t.size
    case ^Type_Partial_Array: elem_type = t.elem
    case ^Type_Slice:         elem_type = t.elem
    }
    if elem_type != nil {
        // Infer literals adopt the element width via the hint above, so they
        // skip the compatibility gate and are range-checked instead.
        if !is_infer(val_type) && !buffer_elem_compatible(elem_type, val_type) && !value_preserving_widen(val_type, elem_type) {
            if elem_size >= 0 {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_ELEMENT,
                    type_name(val_type), elem_size, type_name(elem_type))
            } else {
                check_error(c, s.span, TYPE_CANNOT_ASSIGN_ELEMENT_TYPE,
                    type_name(val_type), type_name(target_type))
            }
        }
        if is_infer(val_type) {
            check_literal_overflow(c, s.value, elem_type, s.span)
        }
    }
}

check_slice_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Scope) {
    sl := s.target.(^Expr_Slice)
    lower_subscript_dots(sl.expr, sl.low)
    lower_subscript_dots(sl.expr, sl.high)
    // Built: the target's slice (its bounds, its collection's place — a
    // plain place, checked first), then the value into its elements. Into
    // bytes, a value no array is written as its own type at lo — a view —
    // known once it is checked: both are built, one left out
    // (graph_fuse_span_target).
    b := fusing(c)
    if b != nil && !graph_pure_place(sl.expr) {
        fuse_fail(c, "a slice of no plain place")
        b = nil
    }
    target_type := check_expr(c, sl.expr, env)
    s.target_type = target_type
    if elem := index_elem_type(target_type); elem != nil {   // the target names a run of elements
        t := new(Type_Slice)
        t.elem = elem
        sl.type_ = t
    }
    bytes := b != nil && fusing(c) != nil && is_byte_buffer(target_type)
    st: Graph_Span_Target
    if bytes { st = graph_fuse_span_target(b, sl.expr, s.span) }
    lo, hi := NO_VALUE, NO_VALUE
    low_type, high_type: Type
    if b != nil { low_type, lo = fuse_bound(c, sl.low, env, .Explicit, sl.span, raw = bytes) } else { low_type = check_expr(c, sl.low, env) }
    if bytes { graph_fuse_span_target_hi(b, &st, lo, sl.span) }
    if sl.high != nil {
        if b != nil { high_type, hi = fuse_bound(c, sl.high, env, .Explicit, sl.span) } else { high_type = check_expr(c, sl.high, env) }
    }
    place := NO_VALUE
    if bytes {
        graph_fuse_span_target_ops(b, &st, hi, sl.expr, sl.type_, sl.is_big_endian, sl.span, s.span)
    } else if b != nil && fusing(c) != nil {
        place = graph_op_value(b, .Slice, .Explicit, sl.span, sl.type_, "", graph_fuse_base_place(b, sl.expr, sl.span), lo, hi)
    }
    val_type, fs := fuse_store_value(c, s, place, env, unplaced = bytes)
    defer {
        if bytes && fusing(c) != nil && fs.on {
            // (`= void` into bytes: the builder's.)
            if fs.void {
                fuse_fail(c, "void written into bytes")
            } else {
                ok: bool
                fs.place, ok = graph_fuse_span_target_end(b, &st, s.assign_value_type, s.span)
                if !ok { fuse_fail(c, "a span's end that branches, viewed") }
            }
        }
        fuse_store_write(c, s, &fs, s.target_type)
    }

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

    // A reinterpret span write stores the value's raw bytes: plain data only.
    // (An array-shaped RHS is an element copy, not a reinterpret — see below.)
    if (is_byte_slice(target_type) || is_byte_partial_array(target_type) || is_byte_fixed_array(target_type)) && !is_array_shaped(val_type) {
        check_byte_write(c, val_type, s.span)
    }
    // Untyped numbers copied into bytes (`bytes[0:3] = [1, 2, 3]`) have no
    // width either, as one written there hasn't: annotate the literal.
    if is_byte_buffer(target_type) {
        if fa, is_array := distinct_base(val_type).(^Type_Fixed_Array); is_array && is_infer(fa.elem) {
            check_error(c, s.span, TYPE_BYTE_BUFFER_COPY_UNTYPED, fa.size)
        }
    }

    // Byte slice reinterpret write: mem[off:off+N] = value.
    // Reinterpret only applies to scalar/struct writes — a fixed-array or slice
    // RHS is an element copy (the bytes the slice points AT, not its header) and
    // falls through to the array-copy path (gen_slice_range_assign).
    if is_byte_slice(target_type) {
        if !is_array_shaped(val_type) {
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
    }

    // Byte partial-array reinterpret write: same semantics as []byte. Partial
    // arrays carry a slice header at the front of their inline storage and
    // codegen treats them as Slice_Vars, so the byte-target write helper
    // resolves the data pointer the same way. Same fixed-array/slice RHS guard
    // as above — those are content copies, not reinterprets.
    if is_byte_partial_array(target_type) {
        if !is_array_shaped(val_type) {
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
    }

    // Byte fixed-array reinterpret write: buf[off:off+N] = value
    // (array-class byte buffers reach here post-desugar as [N]byte)
    // Reinterpret only applies to scalar/struct writes — fixed-array, slice, or
    // partial-array RHS values fall through to the regular array-copy path below.
    if is_byte_fixed_array(target_type) {
        if !is_array_shaped(val_type) {
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
        } else if rhs_pa, rhs_pa_ok := val_type.(^Type_Partial_Array); rhs_pa_ok {
            if types_incompatible(fa.elem, rhs_pa.elem) {
                check_error(c, s.span, TYPE_CANNOT_SLICE_ASSIGN_INTO_2,
                    type_name(rhs_pa.elem), fa.size, type_name(fa.elem))
            }
        } else if !is_any(val_type) {
            check_error(c, s.span, TYPE_SLICE_ASSIGNMENT_REQUIRES_ARRAY_SLICE, type_name(val_type))
        }
    }
}

check_field_assign :: proc(c: ^Checker, s: ^Stmt_Assign, env: ^Type_Scope) {
    fa_expr := s.target.(^Expr_Field_Access)
    // Built: the field's place, then the value into it.
    obj_type, base := fuse_expr(c, fa_expr.expr, env, .Either)

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
    place := NO_VALUE
    if pre_st != nil {
        if ft := resolve_struct_field(pre_st, fa_expr.field, c.table); ft != nil {
            c.expected_hint = ft
            place = fuse_member_place(c, fa_expr, base, obj_type, ft)
        }
    }
    if place == NO_VALUE && fusing(c) != nil {
        // A slice's or partial array's header, or an array's swizzle.
        if t := fuse_target_field_type(obj_type, fa_expr.field); t != nil {
            place = fuse_member_place(c, fa_expr, base, obj_type, t)
        } else {
            fuse_fail(c, "a write to an unknown field")
        }
    }
    val_type := fuse_store(c, s, place, env)
    c.expected_hint = nil

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
            // `obj.view = "lit"` — a slice-typed field would alias rodata.
            check_no_literal_slice_binding(c, ft, s.value, s.span)
            // (Field-init clearing for definite-assignment now in the flow pass.)
            byte_flow := check_byte_flow(c, ft, s.value, val_type, s.span)
            if byte_flow == .View {
                // A range of bytes viewed as a byte-family slice field.
            } else if byte_flow == .Read && is_byte_buffer(val_type) {
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
            } else if byte_flow == .Read {
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
            // (Writing a local ref into a param struct's ref field —
            //  `param.field = &local` — is caught by the post-check escape pass.)
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
        // A slice / partial-array param's header is read-only too: it's the
        // caller's header (passed by address), so `s.len = n` shortened the
        // caller's. A param that should move its cursor takes `^[]T`.
        if pname, immut := write_root_immutable_param(s.target, env); immut {
            check_error(c, s.span, TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER, fa_expr.field, pname)
        }
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
            if pname, immut := write_root_immutable_param(s.target, env); immut {
                check_error(c, s.span,
                    TYPE_CANNOT_WRITE_FIELD_IMMUTABLE_PARAMETER,
                    fa_expr.field, pname)
            }
            if len(fa_expr.field) == 1 {
                fa_expr.type_ = fa.elem   // the target names one element
                // Single-component write: value must match element type
                if types_incompatible(fa.elem, val_type) && !is_infer(val_type) {
                    check_error(c, s.span, TYPE_CANNOT_ASSIGN_SWIZZLE_ELEMENT_TYPE,
                        type_name(val_type), fa_expr.field, type_name(fa.elem))
                }
                if is_infer(val_type) {
                    check_literal_overflow(c, s.value, fa.elem, s.span)
                }
            } else {
                // The target names len(field) elements, as a read of it does.
                fa_expr.type_ = new_clone(Type_Fixed_Array{size = len(fa_expr.field), elem = fa.elem})
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

// A match arm's body, checked in its block (graph_match): its run, its
// block and its binding before, its scope's end and the jump to the join
// after.
fuse_arm_body :: proc(c: ^Checker, gm: ^Graph_Match, s: ^Stmt_Match, arm: ^Match_Arm, i: int, env: ^Type_Scope) {
    b := c.gb if gm != nil else nil
    k: Graph_Block
    if b != nil { k = graph_fuse_arm(b, gm, s, arm, i) }
    check_scope(c, arm.body, env)
    if b != nil { graph_fuse_arm_end(b, gm, k) }
}

check_match :: proc(c: ^Checker, s: ^Stmt_Match, env: ^Type_Scope) {
    // match dispatches on a union value, so it always needs a subject. The
    // parser already reports a missing one; bail here so we don't deref nil.
    if s.subject == nil {
        return
    }
    // Built (graph_match): the subject — a plain place, walked where it is
    // needed; else held in a local made first — then the switch on its tag,
    // each arm's tag filled in as the arm is checked (a value's arm: its
    // value, checked here, before the arms), then each arm's block.
    gm: ^Graph_Match
    b := fusing(c)
    prechecked := make([]bool, len(s.arms), context.temp_allocator)
    slot := NO_NODE
    subj_type: Type
    if b != nil && !graph_pure_place(s.subject) {
        slot = graph_slot(b, "subject", nil, s.span)
        subj_type = fuse_store_into(c, s.subject, env, graph_dest_var("subject", slot, nil), s.span)
        if fusing(c) != nil { graph_fuse_typed(b, slot, subj_type) }
    } else {
        subj_type = check_expr(c, s.subject, env)
    }
    ut, is_union_match := subj_type.(^Type_Union)
    et, is_enum_match := subj_type.(^Type_Enum)
    _, is_err_match := subj_type.(Type_Err)
    if fusing(c) != nil && b != nil {
        gm = graph_fuse_match_begin(b, s, slot)
        for &arm, i in s.arms {
            if arm.is_else { continue }
            if gm.is_union || arm.value == nil {
                graph_fuse_match_tag(b, gm, s, i)
                continue
            }
            // (An enum's variant named bare matches as `.Variant` does: its
            // tag, filled in when the arm is resolved.)
            if ident, is_ident := arm.value.(^Expr_Ident); is_ident && is_enum_match && ident.name in et.variants {
                graph_fuse_match_tag(b, gm, s, i)
                continue
            }
            _, v := fuse_expr(c, arm.value, env)
            graph_fuse_match_value(b, gm, v.v)
            prechecked[i] = true
        }
        graph_fuse_match_switch(b, gm, s)
    }
    defer if gm != nil { graph_fuse_match_end(b, gm) }

    // Union-only: match is for variant dispatch — payload unions, payload-less
    // unions (a.k.a. enums), and open `err`. Structs, scalars, bools, etc. are
    // not matchable; use if/elif for value or predicate branching.
    if !is_union_match && !is_enum_match && !is_err_match {
        check_error(c, s.span, TYPE_MATCH_REQUIRES_UNION, type_name(subj_type))
        return
    }

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

    // Validate wildcard 'else' arms. Empty body is fine — it's the explicit
    // no-op opt-out ("ignore unhandled variants on purpose"), same idiom as
    // Rust's `_ => {}`.
    for arm, i in s.arms {
        if arm.is_else && i != len(s.arms) - 1 {
            check_error(c, s.span, TYPE_LAST_ARM_MATCH)
        }
    }


    for &arm, arm_i in s.arms {
        if arm.dot_shorthand != "" {
            // Dot shorthand arm: .Variant — resolve against subject's enum or union type
            arm.variant = arm.dot_shorthand
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
            child := type_env_block_child(env)
            fuse_arm_body(c, gm, s, &arm, arm_i, child)
        } else if arm.is_union_arm {
            // Union pattern arm: VariantName [bindingName] { body }
            arm.variant = arm.variant_name
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
            arm.bound_name = arm.binding_name
            if arm.bound_name == "" {
                if subj_ident, sok := s.subject.(^Expr_Ident); sok {
                    arm.bound_name = subj_ident.name
                }
            }
            child := type_env_block_child(env)
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
                if arm.bound_name != "" {
                    type_env_set(child, arm.bound_name, st)
                }
            } else if st, st_ok := c.table.funs[struct_name]; st_ok {
                arm.resolved_struct = st.name
                if arm.bound_name != "" {
                    type_env_set(child, arm.bound_name, st)
                }
            }
            fuse_arm_body(c, gm, s, &arm, arm_i, child)
        } else if arm.is_else {
            // Else (wildcard) arm — just type-check the body
            child := type_env_block_child(env)
            fuse_arm_body(c, gm, s, &arm, arm_i, child)
        } else {
            // Value match arm — try to infer bare identifiers as enum/union variants
            if ident, ident_ok := arm.value.(^Expr_Ident); ident_ok {
                if is_enum_match {
                    if tag_val, v_ok := et.variants[ident.name]; v_ok {
                        // A bare variant name matches like `.Variant`
                        arm.variant = ident.name
                        arm.resolved_tag = tag_val
                        child := type_env_block_child(env)
                        fuse_arm_body(c, gm, s, &arm, arm_i, child)
                        continue
                    }
                } else if is_union_match {
                    if tag_val, v_ok := ut.tag_map[ident.name]; v_ok {
                        // A bare variant name matches like `.Variant`
                        arm.variant = ident.name
                        arm.resolved_tag = tag_val
                        ds_struct := ut.variant_structs[ident.name] or_else ident.name
                        if arm_st, arm_st_ok := c.table.structs[ds_struct]; arm_st_ok {
                            arm.resolved_struct = arm_st.name
                        } else if arm_st, arm_st_ok := c.table.funs[ds_struct]; arm_st_ok {
                            arm.resolved_struct = arm_st.name
                        }
                        child := type_env_block_child(env)
                        fuse_arm_body(c, gm, s, &arm, arm_i, child)
                        continue
                    }
                }
            }
            // Regular value match arm (built before the switch: checked there)
            if !prechecked[arm_i] { check_expr(c, arm.value, env) }
            child := type_env_block_child(env)
            fuse_arm_body(c, gm, s, &arm, arm_i, child)
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
    // (Definite-assignment branch-merge across arms now lives in the flow pass.)
    // Strict-default exhaustiveness: when the subject is an enum or union and
    // there's no else wildcard, every variant must have an arm. else is the
    // only opt-out — write `else do {…}` to acknowledge you're not covering
    // every variant on purpose.
    if !has_wildcard && (is_enum_match || is_union_match) {
        // Collect covered variant names from match arms
        covered: map[string]bool
        for arm in s.arms {
            if arm.variant != "" {
                covered[arm.variant] = true
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
    }
}

// ---------------------------------------------------------------------------
// Check program — entry point
// ---------------------------------------------------------------------------

// Helper: extract a Checked_Scope from a Stmt_Scope using resolved types from an env.
// Extract function definitions from a scope's body into checked.functions.
extract_scope_fun_defs :: proc(checked: ^Checked_Program, defs: [dynamic]Stmt, env: ^Type_Scope, main_package: string) {
    for def in defs {
        #partial switch s in def {
        case ^Stmt_Scope:
            // Always recurse into body for nested defs
            extract_scope_fun_defs(checked, s.defs, env, main_package)
            // Extract callable funs as Checked_Scope
            cf, cf_ok := extract_checked_scope(s, env, checked.table)
            if cf_ok {
                fn_key := scope_name(s)
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
        }
    }
}

extract_checked_scope :: proc(s: ^Stmt_Scope, env: ^Type_Scope, table: ^SymbolTable = nil) -> (^Type_Scope, bool) {
    ft: ^Type_Scope
    if fun_type_raw, found := type_env_get(env, scope_name(s)); found {
        if v, ok := fun_type_raw.(^Type_Scope); ok { ft = v }
    }
    // Nested funs register their Type_Scope in body envs that aren't reachable
    // from the extract-time env. Fall back to the global table, looked up by
    // flat name (package + bare).
    if ft == nil && table != nil {
        if home, hok := table.fun_homes[scope_name(s)]; hok {
            ft = table.funs[make_flat_name(home, scope_name(s))]
        }
    }
    if ft == nil { return nil, false }
    // Every declared scope is extracted. A `fun` is callable however it was
    // written — `fun { }` is a function with no params and no returns, its
    // parens omitted — and a struct/class always gets an init function so every
    // construction path (including bare declaration `x: Foo`) can go through it.

    ft.origin = Origin_Source{}
    if s.is_intrinsic {
        ft.origin = Origin_Intrinsic{llvm_name = s.intrinsic_name}
    }
    ft.body = s.body
    ft.body_span = s.span
    ft.is_exposed = s.is_exposed
    record_return_bindings(ft, s)
    populate_cg_signature(ft)
    return ft, true
}

// A fun's named results, by name (its body binds them).
record_return_bindings :: proc(ft: ^Type_Scope, s: ^Stmt_Scope) {
    clear(&ft.return_binding_names)
    for rb in s.return_bindings {
        append(&ft.return_binding_names, rb.name)
    }
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


// (lazy_load_module_program removed — all modules are pre-parsed and looked up
// from c.programs directly in check_module.)

// Partition a package's statements into per-file buckets (preserving first-seen
// file order) and create a file_env per file (parent = pkg_env). Per-file envs
// keep include-introduced names private to their file, while defined names
// register up into pkg_env so sibling files see them. Both the main package
// (check_program) and imported modules (check_module) scope this way.
partition_package_files :: proc(stmts: [dynamic]Stmt, pkg_env: ^Type_Scope) ->
    (files_by_src: map[string][dynamic]Stmt, file_order: [dynamic]string, file_envs: map[string]^Type_Scope) {
    for stmt in stmts {
        src := stmt_span(stmt).file
        if _, exists := files_by_src[src]; !exists {
            files_by_src[src] = make([dynamic]Stmt)
            append(&file_order, src)
        }
        bucket := &files_by_src[src]
        append(bucket, stmt)
    }
    for src in file_order {
        // Each file gets its OWN durable scope, chained to the module scope. It
        // holds the file's private includes (its `use`/`include` imports stay
        // file-local); definitions still register on the module scope (public).
        // kind = .Block / is_module = false so the marker derivations skip it.
        fe := new(Type_Scope)
        fe.kind = .Block
        fe.home_package = pkg_env.home_package if pkg_env != nil else ""
        fe.parent_scope = pkg_env
        file_envs[src] = fe
    }
    return
}

// THE canonical per-file checking pipeline for one package. Both check_program
// (main package) and check_module (imports) drive it, so the phase sequence
// lives in exactly one place. Each phase runs across ALL files before the next
// begins — that whole-package hoisting is what lets cross-file forward
// references resolve regardless of (hash-seeded, non-deterministic) file order:
//
//   1a   register_type_names              — type + fn NAMES (+ eager signatures)
//   1b   register_and_check_declarations  — body fields, base/param/return types,
//                                           statement-level decls and constants
//                                           (a literal's struct resolves its
//                                           fields on demand)
//   (1.5 removed)                         — a main-package constant pass used to
//                                           run here; main-package constants are
//                                           const-folded before codegen, so it was
//                                           dead and is gone.
//   (2a removed)                          — struct field types used to be hoisted
//                                           here so a body in file A could read a
//                                           struct from file B; now they resolve
//                                           ON DEMAND at the use site
//                                           (ensure_struct_signature), so no hoist.
//   2    check_bodies                     — full function-body type-checking
//
// owner is the module-struct that top-level decls attach to (nil for the main
// package, which has no enclosing module-struct); pkg_env is the package scope
// that defined names register into.
check_package_files :: proc(
    c: ^Checker,
    files_by_src: map[string][dynamic]Stmt,
    file_order: [dynamic]string,
    file_envs: map[string]^Type_Scope,
    owner: ^Type_Scope,
    pkg_env: ^Type_Scope,
) {
    for src in file_order {  // 1a
        register_type_names(c, files_by_src[src], file_envs[src], owner, pkg_env)
    }

    for src in file_order {  // 1b
        register_and_check_declarations(c, files_by_src[src][:], file_envs[src], owner, pkg_env)
    }

    // (1.5 main-package constant pass removed — see header. Main-package
    // constants const-fold to literals during checking before codegen consults
    // c.table.constants for them, so the registration was dead.)

    // (Former "2a" cross-file struct-signature hoist removed: struct fields now
    // resolve on demand at the use site — field access, construction, literal
    // matching — via ensure_struct_signature, so a body in one file no longer
    // needs every other file's structs pre-resolved. The struct carries its own
    // decl_env and memoizes via sig_state.)

    for src in file_order {  // 2 — bodies
        check_bodies(c, files_by_src[src][:], file_envs[src])
    }
}

// Type-check a module on demand (lazily, triggered by include).
// Returns a Type_Scope (module-struct) with scope set to the module's checked env.
// Modules are funs — Type_Scope with no data fields, only functions/types/scope.
check_module :: proc(c: ^Checker, module_name: string, span: Span) -> ^Type_Scope {
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
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
    // Create the module-struct upfront so it can own top-level declarations during
    // registration AND serve as the module scope before any name is set. Dispatch
    // groups / operator overloads filled after check_scope completes.
    // (env_is_module(mod_env) derives "module namespace" from mod_struct.is_module.)
    mod_struct := new(Type_Scope)
    mod_struct.name = module_name
    mod_struct.home_package = module_name  // module is its own home
    mod_struct.kind = .Struct
    mod_struct.is_module = true
    mod_env := mod_struct   // the module scope IS the env now

    if c.top_env != nil {
        for name in ([]string{"this_program", "Program", "std", "void"}) {
            if t, ok := scope_defines(c.top_env, name); ok {
                type_env_set(mod_env, name, t)
            }
        }
    }

    // If `void` wasn't in c.top_env yet (early in setup), register a fresh
    // null-pointer type so the module body's void literals still type-check.
    if _, has_void := scope_defines(mod_env, "void"); !has_void {
        void_type := new(Type_Ptr)
        void_type.elem = Type_Any{}
        type_env_set(mod_env, "void", void_type)
    }

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

    // Type-check the module's declarations and bodies via the canonical
    // per-file pipeline (see check_package_files for the phase map). mod_struct
    // owns the top-level decls; mod_env is the module scope names register into.
    // Lookup chain inside a body: body -> file_env -> mod_env -> STOP
    // (mod_env is_module_scope=true). Modules skip the 1.5 constant pass;
    // their constants are registered here, before the bodies are checked, so
    // the module's own functions resolve them (unregistered, a bare reference
    // fell through to whichever module registered the name first).
    register_module_constants(c, mod_program, module_name)
    files_by_src, file_order, file_envs := partition_package_files(mod_program, mod_env)
    check_package_files(c, files_by_src, file_order, file_envs, mod_struct, mod_env)

    // Preserve module's dispatch groups for propagation on `using include`
    mod_struct.dispatch_groups = c.dispatch_groups
    mod_struct.operator_overloads = c.operator_overloads

    // (The module's durable name surface — mod_struct.types/functions — is kept
    // in sync by type_env_set writing through mod_env == mod_struct as the
    // module body is checked, so no end-of-module mirror copy is needed.)

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
        type_env_set(c.std_fun, bare, mod_struct)
    } else if c.mara_env != nil {
        type_env_set(c.mara_env, module_name, mod_struct)
    }

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
make_foreign_checked_scope :: proc(c: ^Checker, decl: Foreign_Fun, ft: ^Type_Scope, library, prefix: string) -> ^Type_Scope {
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
                ln, fo.library, span_loc(existing.body_span))
            break
        }
    }
    ft.origin = Origin_Foreign{
        library    = library,
        link_name  = ln,
        prefix     = prefix,
    }
    ft.body_span = decl.span
    populate_cg_signature(ft)
    return ft
}

// Walk a struct/class body for foreign blocks and register their decls in
// checked.functions with origin=Origin_Foreign and a flat key prefixed by
// the enclosing struct's flat name. The key matches what register_scope_defs
// stamped onto the foreign's Type_Scope.name and what call_resolved_name
// produces at the call site. Recurses into nested struct bodies so deeper
// nesting works without further changes. (Module-level foreign extraction
// is handled directly in extract_module_into_checked.)
extract_nested_foreigns_into_checked :: proc(c: ^Checker, body: [dynamic]Stmt, mod_env: ^Type_Scope, struct_flat_name: string) {
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
                inner_flat := make_flat_name(struct_flat_name, scope_name(s))
                extract_nested_foreigns_into_checked(c, s.body, mod_env, inner_flat)
            }
        }
    }
}

// Extract all declarations from a checked module into the Checked_Program for codegen.
// Handles: functions, foreign declarations, types, constants, and variables.
// Also populates the module-struct's functions/types.
extract_module_into_checked :: proc(c: ^Checker, stmts: [dynamic]Stmt, mod_env: ^Type_Scope, module_name: string, mod_struct: ^Type_Scope = nil) {
    checked := c.checked
    if checked == nil { return }

    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            // Always extract scoped function defs from body
            extract_scope_fun_defs(checked, s.defs, mod_env, module_name)
            // Foreign blocks inside a struct body are registered by
            // register_scope_defs against the struct's mangled name; mirror
            // that here for the codegen side so foreign_funs is keyed under
            // the nested flat name that call_resolved_name produces.
            if s.kind == .Struct {
                struct_flat := make_flat_name(module_name, scope_name(s))
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
            if cf_ok && scope_name(s) != "main" {
                flat_key := make_flat_name(module_name, scope_name(s))
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
        // Stmt_Union_Def owner attachment is handled by register_and_check_declarations.
        }

        register_module_constant_stmt(c, stmt, module_name)
    }
}

// Register a module's top-level constants (run before its bodies are checked,
// so its own functions resolve them, and again as its statements are extracted).
// Registration is idempotent per module.
register_module_constants :: proc(c: ^Checker, stmts: [dynamic]Stmt, module_name: string) {
    for stmt in stmts { register_module_constant_stmt(c, stmt, module_name) }
}

register_module_constant_stmt :: proc(c: ^Checker, stmt: Stmt, module_name: string) {
    // Only definitions are constants. A module's variables (`x := v`,
    // `x : T = v`) are its locals, which no function sees (see names_module).
    // Stmt_Define: `name :: value` or `name : Type : value` — always a compile-time constant.
    // Skip include forms (`name :: include path`) — those are handled by the
    // include-processing path in register_and_check_declarations, same as
    // `name := include path`.
    if def, ok := stmt.(^Stmt_Define); ok {
        if _, is_include := def.value.(^Expr_Include); !is_include && def.value != nil {
            register_module_constant(c, module_name, define_name(def), def.value)
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
extract_main_program_stmts :: proc(c: ^Checker, checked: ^Checked_Program, stmts: [dynamic]Stmt, env: ^Type_Scope, main_package: string) {
    for stmt in stmts {
        #partial switch s in stmt {
        case ^Stmt_Scope:
            extract_scope_fun_defs(checked, s.defs, env, main_package)
            cf, cf_ok := extract_checked_scope(s, env, c.table)
            if cf_ok {
                fn_key := scope_name(s)
                if scope_name(s) != "main" && main_package != "" {
                    fn_key = make_flat_name(main_package, scope_name(s))
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
        }
        if def, ok := stmt.(^Stmt_Define); ok {
            if _, is_include := def.value.(^Expr_Include); !is_include && def.value != nil {
                if main_package != "" {
                    flat := make_flat_name(main_package, define_name(def))
                    checked.table.constants[flat] = def.value
                }
                checked.table.constants[define_name(def)] = def.value
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
            if scope_name(s) == "main" {
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
                    check_error(c, s.span, TYPE_EXPOSE_FUNCTION_TAKE_FIRST_PARAMETER, scope_name(s))
                }
            }
        case ^Stmt_If:
            // A runtime `if` at top level is illegal — comptime `#if` was folded
            // away before this ran, so any Stmt_If here is a runtime conditional.
            check_error(c, s.span, TYPE_EXECUTABLE_STATEMENTS_INSIDE_FUN_MAIN)
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
                      target_os: Target_OS = .Windows,
                      analysis_only: bool = false,
                      perf: ^Performance_Timer = nil) -> ^Checked_Program {
    table := new(SymbolTable)
    // The main package's durable module scope IS the root env, wired upfront so
    // builtins (std / void / Program / this_program) and every top-level name land
    // on it directly via type_env_set. is_module makes env_is_module(env) true: the
    // root scope is the main package's module scope, so lookup terminates here.
    main_mod := new(Type_Scope)
    main_mod.name = main_package
    main_mod.home_package = main_package
    main_mod.kind = .Struct
    main_mod.is_module = true
    env := main_mod            // heap-allocated (new) so it outlives check_program
    table.root_env = env

    c := Checker{ table = table }
    when ODIN_DEBUG { c.once_on = os.get_env("MARA_CHECK_ONCE", context.temp_allocator) == "1" }
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
    c.analysis_only = analysis_only

    // Resolve comptime `#if` up front: fold the live arm inline, drop the dead
    // one. After this no `#if` reaches the checker — the dead arm's platform
    // names never resolve here, and the def/runtime split never sees a hybrid.
    for _, prog in c.programs {
        fold_comptime_ifs(&c, prog)
    }
    ast_shape_begin(c.programs)   // the baseline: parse + fold, before any pass writes

    main_prog, prog_ok := programs[main_package]
    if !prog_ok {
        check_error(&c, {}, "no parsed program for main module '%s'", main_package)
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
        if !outer_ok || call_name(outer_call) != "Program" { return }
        if len(call_args(outer_call)) == 0 { return } // Program() -> void default
        // The arena spec is the first arg. Two valid shapes: another call
        // (the shortcut form: Arena_Debug(50 * MB)) or a bare ident (just
        // the type). Either way, the arena type's NAME is what we record.
        arena_arg := call_args(outer_call)[0]
        c.table.has_scope_allocator = true
        if inner_call, ic_ok := arena_arg.(^Expr_Call); ic_ok {
            c.table.scope_allocator_name = call_name(inner_call)
            c.table.scope_allocator_args = call_args(inner_call)
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
                if scope_name(fn_stmt) != "main" && !c.target_shared { continue }
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

    // The graph is built as the program is checked (its arena known now).
    c.gb = graph_builder_new(checked, programs)

    // Build Context struct: { arena? , args: [..64][]utf8 }
    {
        ARGS_CAP :: 64
        // Element type: []utf8 slice — argv strings are strlen-scanned into
        // plain {len, cap, ptr} headers by the @main prologue.
        arg_slice := new(Type_Slice)
        arg_slice.elem = Type_Utf8{}   // text, as mara.core declares it (was Type_Byte: an inferred `a := this_program.args[i]` printed as numbers)

        // Args is a partial array: [..64][]utf8 — header {len,cap,ptr}
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
        // main_mod was created + wired to env upfront (above); builtins and
        // top-level names already live on it. Just register it as this package's
        // checked module so a `use` of this package finds it.
        c.checked_modules[main_package] = main_mod

        // Forward-register the main package's top-level constants (flat key +
        // owner) BEFORE its bodies are checked. Imported modules registered theirs
        // during their own extraction (which runs earlier), but the main package's
        // extraction (extract_main_program_stmts) runs later — so without this its
        // own constants are invisible to resolve_const_ref while its bodies check,
        // and a main-vs-import name collision goes undetected. The same
        // registration extract_module_into_checked does.
        if main_package != "" { register_module_constants(&c, main_prog^, main_package) }

        // Canonical per-file pipeline (see check_package_files for the phase map).
        main_files_by_src, main_file_order, main_file_envs := partition_package_files(main_prog^, env)
        check_package_files(&c, main_files_by_src, main_file_order, main_file_envs, main_mod, env)
    }
    check_struct_instances(&c)
    fuse_program_struct(&c)

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
        ft.name = flat_key   // codegen emits @mara_<name>; the call site resolves to flat_key
        ft.home_package = tmpl_home
        ft.body = body
        ft.body_span = tmpl_ast.span
        ft.origin = Origin_Source{}
        populate_cg_signature(ft)
        checked.functions[flat_key] = ft
    }

    // Phase 3: Validate the main package's program structure. Exe packages
    // (non-shared) must define fun main(); DLL packages can rely on #expose
    // and don't require main.
    found_main := false
    validate_top_level_stmts(&c, main_prog^, &found_main)
    if !found_main && !shared {
        check_error(&c, {}, "module '%s' must define fun main()", main_package)
    }

    // Sanity check (debug builds only): every named entity should have a
    // home_package set. Empty home_package on a registered named entity
    // indicates a missed population site. Built-in primitives ("Program",
    // anonymous fn-pointer types from Type_Func_Expr) are expected to be
    // empty and skipped here.
    when ODIN_DEBUG {
        audit_home_package(checked)
    }

    // The program graph (graph.odin), built from a clean check, and the
    // analyses that read it (design/graph_retrofit.md, phase 2): the call graph
    // is an index over its calls, and the summaries on it.
    if c.errors == 0 {
        if perf != nil { perf_timer_mark(perf, "graph") }
        checked.graph = build_program_graph(c.gb, programs)
        if perf != nil { perf_timer_mark(perf, "analysis") }
        checked.call_graph = build_call_graph(checked)
        c.cg = &checked.call_graph
    } else {
        graph_builder_free(c.gb)
        if perf != nil { perf_timer_mark(perf, "analysis") }
    }
    c.gb = nil
    flow_analyze_program(&c, checked) // post-check intraproc flow (missing return, err use, init)
    escape_analyze_program(&c, checked) // post-check escape: the lifetime rule + its call summaries
    // NOTE: the slice analysis (def-use + control dependence on the graph) is
    // built lazily per function by the first `mara ask` flow query — du_fn.
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

check_expr :: proc(c: ^Checker, expr: Expr, env: ^Type_Scope) -> Type {
    when ODIN_DEBUG {
        if c.once_on && c.once_stmt > 0 && expr != nil {
            k := expr_identity(expr)
            seen := c.once_seen[k]
            if seen[0] == c.once_stmt {
                seen[1] += 1
                if seen[1] == 2 { fmt.eprintfln("checked twice: %s", format_location(expr_span(expr).file, expr_span(expr).line, expr_span(expr).col)) }
            } else {
                seen = {c.once_stmt, 1}
            }
            c.once_seen[k] = seen
        }
    }
    c.asked, c.asked_written, c.asked_dest, c.asked_temp, c.asked_span, c.want = c.want, c.want_written, c.want_dest, c.want_temp, c.want_span, .None
    result := check_expr_impl(c, expr, env)
    set_expr_type(expr, result)
    // What building asked of it and nothing took: a leaf's, built here.
    if c.asked != .None { fuse_leaf(c, expr) }
    return result
}

// A unary operation, built: its operand's value, then it. (`&x` and `p^`
// name places; an overload is a call.)
Fuse_Unary :: struct {
    w:       Written,
    operand: Operand,
    place:   bool,   // the operand's place is wanted
    either:  bool,   // (`-x`) its place or its value: an overload's param may view it
    fused:   Fused,
    t:       Type,
}

// An index into bytes: what the checker types a byte may be read as another
// type (maybe_stamp_byte_view), once its use is checked. The builder's.
fuse_byte_index :: proc(e: Expr) -> bool {
    ix, is_ix := e.(^Expr_Index)
    return is_ix && is_byte_buffer(expr_type(ix.expr))
}

check_unary :: proc(c: ^Checker, e: ^Expr_Unary, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    if want == .None { return check_unary_impl(c, e, env, nil) }
    // `p^` is the place p points at; `&x` the address of x's place.
    if want == .Place && e.op != .Caret {
        fuse_fail(c, "a unary's place")
        return check_unary_impl(c, e, env, nil)
    }
    fu := Fuse_Unary{w = w, place = e.op == .Caret || e.op == .Ampersand, either = e.op == .Minus && !e.wrapping}
    t := check_unary_impl(c, e, env, &fu)
    b := fusing(c)
    if b == nil { return t }
    if rf, over := e.overload_fn.?; over {
        // A call, its operand at its param's type (graph_operator_arg).
        callee := graph_callee(b, rf)
        if callee == nil {
            fuse_fail(c, "an operator resolved to no function")
            return t
        }
        arg: Operand
        if len(callee.params) > 0 {
            arg = fuse_value_as(c, e.operand, fu.t, fu.fused, callee.params[0].type_, e.span, {to = callee.params[0].type_})
        } else {
            arg = fuse_value(c, fu.fused, e.operand, fu.t)
        }
        if fusing(c) == nil { return t }
        kind: Op_Kind = .Construct if callee.kind == .Struct else .Call
        fuse_done(c, {graph_call_op(b, kind, w, e.span, callee, t, arg), 0})
        return t
    }
    if fu.either { fu.operand = fuse_value(c, fu.fused, e.operand, fu.t) }
    #partial switch e.op {
    case .Caret:
        p := graph_op_value(b, .Deref, .Explicit, e.span, t, "", fu.operand)
        if want == .Value {
            fuse_done(c, graph_read(b, p, t, e.span))
        } else {
            fuse_done(c, p, true)
        }
        return t
    case .Ampersand:
        a := graph_op_value(b, .Address, w, e.span, t, "", fu.operand)
        // Bytes' address: a view of them where its use takes it as another
        // pointer (maybe_stamp_byte_view, once the use is checked).
        if fuse_byte_index(e.operand) { c.byte_addrs[rawptr(e)] = {a.op, fu.operand.op} }
        fuse_done(c, a)
        return t
    }
    op := "-%" if e.op == .Minus && e.wrapping else graph_token_text(e.op)
    fuse_done(c, graph_op_value(b, .Unary, w, e.span, t, op, fu.operand))
    return t
}

fuse_unary_operand :: proc(c: ^Checker, e: ^Expr_Unary, env: ^Type_Scope, fu: ^Fuse_Unary) -> Type {
    if fu == nil { return check_expr(c, e.operand, env) }
    want: Fuse_Want = .Place if fu.place else .Either if fu.either else .Value
    t, r := fuse_expr(c, e.operand, env, want, fu.w, temp_span = e.span)
    fu.operand, fu.fused, fu.t = r.v, r, t
    return t
}

check_unary_impl :: proc(c: ^Checker, e: ^Expr_Unary, env: ^Type_Scope, fu: ^Fuse_Unary) -> Type {
    operand_type := fuse_unary_operand(c, e, env, fu)
    #partial switch e.op {
    case .Minus:
        if e.wrapping {
            // `-%x`: wrapping negate. Integer-only, and unlike plain `-x` it
            // ACCEPTS unsigned (two's-complement negate is well-defined) and
            // won't trap on MIN. No overload dispatch.
            if !is_wrap_operand(operand_type) {
                check_error(c, e.span, TYPE_WRAPPING_REQUIRES_INTEGER_UNARY, type_name(operand_type))
                return Type_Error{}
            }
            return operand_type
        }
        if !is_numeric(operand_type) {
            // Try `overload -` dispatch with a single-arg function (e.g.
            // mara.math's `vec3_negate`). Falls through to the standard
            // not-numeric error if no overload matches.
            if dispatch_names, has_overload := find_operator_overload(c, env, e.op); has_overload {
                best_flat := ""
                best_ft: ^Type_Scope = nil  // resolved callee for the winning best_flat
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
                                best_ft = ft
                                best_ret = fn_primary_return(ft)
                                best_score = score
                            }
                        }
                    }
                }
                if best_score > 0 {
                    e.overload_fn = Resolved_Func{name = best_flat, callee = best_ft}
                    return best_ret
                }
            }
            check_error(c, e.span, TYPE_CANNOT_NEGATE, type_name(operand_type))
        } else if _, kind, k_ok := numeric_info(operand_type); k_ok && kind == .Unsigned {
            // Negating an unsigned value has no representable result
            // (except 0). Binary `0 - x` already traps the underflow at
            // runtime; the unary form is knowable here, so reject it at
            // compile time instead of silently wrapping two's-complement.
            check_error(c, e.span, TYPE_CANNOT_NEGATE_UNSIGNED, type_name(operand_type))
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
        if name, is_const := write_root_constant(c, e.operand); is_const {
            check_error(c, e.span, TYPE_CANNOT_TAKE_ADDRESS_CONSTANT, name)
        }
        // A string literal's bytes live in read-only rodata. `&` is the
        // mutation gate, so an addressed literal (append destination,
        // `^[]utf8` argument) would aim writes at a read-only page.
        if _, is_lit := e.operand.(^Expr_String); is_lit {
            check_error(c, e.span, TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL)
        }
        // A field or element of a ternary or a literal: those are values,
        // not storage — a ternary's is one of its operands', so a write
        // through the address would reach that operand. A slice expression
        // builds a fresh header with nowhere to point at.
        #partial switch _ in access_root(e.operand) {
        case ^Expr_If, ^Expr_Array, ^Expr_Struct_Literal:
            check_error(c, e.span, CODE_CANNOT_TAKE_ADDRESS_EXPRESSION)
        }
        if _, is_slice := e.operand.(^Expr_Slice); is_slice {
            check_error(c, e.span, CODE_CANNOT_TAKE_ADDRESS_SLICE_TEMP)
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
    return Type_Error{}
}

// A literal, built where it goes (graph_into): into its destination, or —
// as a value — into a temporary made before it. Its fields are built as
// check_struct_literal_fields checks them.
Fuse_Lit :: struct {
    e:     rawptr,
    dest:  Dest,
    built: bool,
    gl:    ^Graph_Literal,   // an override block's: the construction's
}

check_struct_literal :: proc(c: ^Checker, e: ^Expr_Struct_Literal, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    d, into_temp := c.asked_dest, c.asked_temp
    b := fusing(c)
    if want == .None || b == nil { return check_struct_literal_impl(c, e, env) }
    if e.override_target != "" {
        fuse_fail(c, "an override in a value's place")
        return check_struct_literal_impl(c, e, env)
    }
    temp := want != .Into || into_temp
    // (A temporary a use places — `T{}[i]`, a slice's view — at the use's
    // span: its place.)
    placed := want != .Into && c.asked_span != {}
    at := c.asked_span if into_temp || placed else e.span
    if temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
    fl := Fuse_Lit{e = e, dest = d}
    saved := c.lit
    c.lit = &fl
    t := check_struct_literal_impl(c, e, env)
    c.lit = saved
    if fusing(c) == nil { return t }
    if !fl.built {
        fuse_fail(c, "a literal the graph builds no way")
        return t
    }
    fuse_built(c, b, want, temp, into_temp, d, t, at, placed)
    return t
}

// Where a value built in place goes: its destination; else a temporary made
// before it — typed as the storage it is then written to (graph_assign), as
// the use that takes it (fuse_use_type), or as itself — read (as a value) or
// its place.
fuse_temp_type :: proc(d: Dest) -> Type {
    if d.type_ != nil && !is_infer(d.type_) { return d.type_ }
    return nil
}

// What a use that takes a value at a type (graph_value_as) asks of it: an
// array literal is built at that type — a short one's other slots zero; a
// literal the use views as a slice (graph_view), in a temporary placed at
// the use's span — an array's at the slice's element type.
fuse_use_type :: proc(e: Expr, t: Type, span: Span) -> (Dest, Span) {
    if t == nil { return {}, {} }
    if sl, to_slice := distinct_base(t).(^Type_Slice); to_slice {
        #partial switch v in e {
        case ^Expr_Array:
            return {type_ = new_clone(Type_Fixed_Array{size = len(v.elements), elem = sl.elem})}, span
        case ^Expr_Struct_Literal:
            return {}, span
        }
        return {}, {}
    }
    if _, is_literal := e.(^Expr_Array); is_literal && graph_aggregate(t) { return {type_ = t}, {} }
    // (A span taken as an array: of bytes, read as it — check_slice.)
    _, is_span := e.(^Expr_Slice)
    if _, to_array := distinct_base(t).(^Type_Fixed_Array); to_array && is_span { return {type_ = t}, {} }
    return {}, {}
}

fuse_built :: proc(c: ^Checker, b: ^Graph_Builder, want: Fuse_Want, temp, into_temp: bool, d: Dest, t: Type, span: Span, placed := false) {
    if !temp {
        fuse_done(c, NO_VALUE, into = true)
        return
    }
    tt := d.type_ if d.type_ != nil else t
    p := graph_fuse_temp_end(b, d, tt, span)
    switch {
    case into_temp:                fuse_done(c, graph_read(b, p, tt, span), temp = true)
    case want == .Place || placed: fuse_done(c, p, true)
    case:                fuse_done(c, graph_read(b, p, tt, span))
    }
}

// An array literal, built as a struct literal is: zero, then each element
// into its slot.
check_array_literal :: proc(c: ^Checker, e: ^Expr_Array, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    d, into_temp := c.asked_dest, c.asked_temp
    b := fusing(c)
    if want == .None || b == nil || len(e.elements) == 0 { return check_array_literal_impl(c, e, env, nil) }
    temp := want != .Into || into_temp
    // (A temporary a use places — `[..][i]`, a slice's view — at the use's
    // span: its place.)
    placed := want != .Into && c.asked_span != {}
    at := c.asked_span if into_temp || placed else e.span
    if temp { d = graph_fuse_temp(b, at, fuse_temp_type(d)) }
    ga := graph_fuse_array(b, e, d)
    t := check_array_literal_impl(c, e, env, ga)
    if fusing(c) == nil { return t }
    if b.g.type_[ga.zero] == nil { b.g.type_[ga.zero] = t }
    fuse_built(c, b, want, temp, into_temp, d, t, at, placed)
    return t
}

// A value stored into a destination (graph_store): what builds in place
// builds there; else a view where one is taken, or the value at the
// destination's type, written. `settle` when the destination's type is a
// declaration's or a place's (the builder's is settled).
fuse_store_into :: proc(c: ^Checker, e: Expr, env: ^Type_Scope, d: Dest, span: Span, settle := false) -> Type {
    t, r := fuse_expr(c, e, env, .Into, dest = d, temp_span = span)
    fuse_store_finish(c, e, t, r, d, span, settle)
    return t
}

fuse_store_finish :: proc(c: ^Checker, e: Expr, t: Type, r: Fused, d: Dest, span: Span, settle := false) -> (wrote: bool, zeroed: bool) {
    b := fusing(c)
    if b == nil || r.into { return }
    if r.temp {
        // Built whole in a temporary, then written (graph_assign).
        graph_fuse_write_at(b, graph_dest_place(b, d, span), r.v, span)
        return true, false
    }
    if fuse_builds_into(e) {
        fuse_fail(c, "a value built in place, taken as one")
        return
    }
    dt := graph_dest_type(b, d)
    _, to_ptr := distinct_base(dt).(^Type_Ptr)
    _, from_ptr := distinct_base(t).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(dt) && graph_partial_of(t) {
        v := graph_op_value(b, .Cast, .Implied, span, dt, type_name(dt), fuse_value(c, r, e, t))
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)   // (the view, then the place)
        return
    }
    _, to_slice := distinct_base(dt).(^Type_Slice)
    _, from_array := distinct_base(t).(^Type_Fixed_Array)
    if to_slice && from_array {
        if !r.place {
            fuse_fail(c, "a slice of an array value")
            return
        }
        v := graph_op_value(b, .Slice, .Implied, span, dt, "", r.v)
        graph_fuse_write_at(b, graph_dest_place(b, d, span), v, span)
        return
    }
    if sl, is_span := e.(^Expr_Slice); is_span && d.type_ != nil && byte_flow(d.type_, e, t) == .Read {
        // A span of bytes: its bytes' place and bounds, as its slice built
        // them; a register value is the bytes at its start seen as it, read,
        // else a byte read — at the span, where its failures say it is. A
        // new partial array is zero first.
        if r.v.op == NO_NODE || r.v.op != c.span_read.op || c.span_read.scalar == graph_aggregate(dt) {
            fuse_fail(c, "a span of bytes read as another type")
            return
        }
        if c.span_read.scalar {
            val := graph_read(b, graph_fuse_span_view(b, r.v, dt, sl.is_big_endian, span), dt, span)
            graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
            return true, false
        }
        buf, lo, hi := graph_fuse_span_operands(b, r.v, span)
        big := "#big_endian" if sl.is_big_endian else ""
        graph_op(b, .Byte_Read, .Explicit, sl.span, d.type_, big, graph_dest_place(b, d, span), buf, lo, hi)
        return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
    }
    if ix, is_index := e.(^Expr_Index); is_index && d.type_ != nil && byte_flow(d.type_, e, t) == .Read {
        // An element of bytes: its place, a view of the bytes as the
        // destination's type, read. (Into a slice or a partial array, a
        // byte read. Other bytes — a pointer to them — are written as they
        // are.)
        _, into_slice := distinct_base(dt).(^Type_Slice)
        if !r.place {
            fuse_fail(c, "bytes read as another type")
            return
        }
        if into_slice || is_partial_array(dt) {
            // Into a slice or a partial array, a byte read: the bytes'
            // place and the index as the builder takes them (the element's
            // read and its index's widening left out), then the read. A new
            // partial array is zero first.
            buf, off := graph_fuse_byte_operands(b, r.v, span)
            graph_op(b, .Byte_Read, .Explicit, span, d.type_, "#big_endian" if ix.is_big_endian else "", graph_dest_place(b, d, span), buf, off)
            return true, is_partial_array(dt) && d.kind == .Var && d.decl != NO_NODE
        }
        graph_fuse_view(b, r.v, dt, ix.is_big_endian, span)
        val := graph_read(b, r.v, dt, span)   // (the read, then the place)
        graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
        return true, false
    }
    val := graph_fuse_widen(b, fuse_value(c, r, e, t), span, {to = dt, settle_to = settle})
    graph_fuse_write_at(b, graph_dest_place(b, d, span), val, span)
    return true, false
}

// An `if` expression, built (graph_if_place): the synthetic local its
// branches write, made first (typed once both are checked), its condition,
// each branch's value stored in a run of its own — at the if's type, known
// then — and the local after them: its place, or read.
Fuse_If :: struct {
    b:     ^Graph_Builder,
    w:     Written,
    slot:  Node_Id,
    gi:    Graph_If_Expr,
    widen: [2]int,
    types: [2]Type,   // each branch's
    prefix: [2][2]Node_Id,   // each branch's zero first, kept when it fills a prefix of a partial array
}

check_if_expr :: proc(c: ^Checker, e: ^Expr_If, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    fi := Fuse_If{w = w, widen = {-1, -1}}
    if b := fusing(c); b != nil && want != .None {
        fi.b = b
        fi.slot = graph_slot(b, "if", nil, e.span)
    }
    t := check_if_expr_impl(c, e, env, &fi)
    b := fi.b
    if b == nil || fusing(c) == nil { return t }
    // (A branch the if's type views — a fixed array's place as a slice, a
    // partial array's header as one: the builder's. One filling a prefix of
    // a partial array — text — is zero first.)
    for bt, k in fi.types {
        branch := e.then_expr if k == 0 else e.else_expr
        if fuse_views(t, bt) {
            fuse_fail(c, "an if's branch viewed")
            return t
        }
        if fi.prefix[k] != {} { graph_fuse_prefix_end(b, fi.prefix[k], is_partial_array(t) && graph_fills_prefix(branch), t) }
    }
    for k in fi.widen { if k >= 0 { b.fuse.widens[k].to = t } }
    // (Its local holds its value: an array of untyped elements settled —
    // a number's width is still its use's.)
    lt := t
    if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array && is_infer(fa.elem) {
        lt = solidify_type(t)
        graph_fuse_retype_literal(b, int(fi.slot), b.nodes, lt)
    }
    graph_fuse_typed(b, fi.slot, lt)
    p := graph_var(b, "if", fi.slot, lt, e.span)
    // (Its place: its local, a fresh one holding its value.)
    if want == .Value {
        fuse_done(c, graph_read(b, p, lt, e.span))
    } else {
        fuse_done(c, p, true)
    }
    return t
}

// Whether a value may fill only a prefix of a partial array (graph_fills_prefix,
// before it is checked): what is no number, literal or operation.
fuse_may_fill_prefix :: proc(e: Expr) -> bool {
    #partial switch _ in e {
    case ^Expr_Number, ^Expr_Char, ^Expr_Bool, ^Expr_Array, ^Expr_Struct_Literal, ^Expr_Binary, ^Expr_Unary: return false
    }
    return true
}

// A branch's value, stored in the if's local, in its run.
fuse_if_branch :: proc(c: ^Checker, e: ^Expr_If, branch: Expr, env: ^Type_Scope, fi: ^Fuse_If, k: int) -> Type {
    if fi.b == nil { return check_expr(c, branch, env) }
    b := fi.b
    // (Text, a slice's elements: a partial array's prefix, zero first — kept
    // once the if's type says so. A literal: built in the if's local.)
    if fuse_may_fill_prefix(branch) { fi.prefix[k] = graph_fuse_prefix(b, "if", fi.slot, e.span) }
    t, r := fuse_expr(c, branch, env, .Into, dest = graph_dest_var("if", fi.slot, nil))
    fi.types[k] = t
    if fusing(c) == nil || r.into { return t }
    if fuse_builds_into(branch) || fuse_byte_index(branch) {
        fuse_fail(c, "an if's branch built in place, or of bytes")
        return t
    }
    n := len(b.fuse.widens)
    val := graph_fuse_widen(b, fuse_value(c, r, branch, t), e.span, {pending = true})
    if len(b.fuse.widens) > n { fi.widen[k] = n }
    graph_fuse_write_at(b, graph_var(b, "if", fi.slot, nil, e.span), val, e.span)
    return t
}

check_if_expr_impl :: proc(c: ^Checker, e: ^Expr_If, env: ^Type_Scope, fi: ^Fuse_If) -> Type {
    cond_type: Type
    cond: Fused
    if fi.b != nil { cond_type, cond = fuse_expr(c, e.condition, env, .Value, fi.w) } else { cond_type = check_expr(c, e.condition, env) }
    if !is_any(cond_type) {
        if _, is_bool := cond_type.(Type_Bool); !is_bool {
            check_error(c, e.span, TYPE_EXPRESSION_CONDITION_BOOL, type_name(cond_type))
        }
    }
    if fi.b != nil && fusing(c) != nil { fi.gi = graph_fuse_if_expr(fi.b, cond.v, fi.w, e.span) }
    then_type := fuse_if_branch(c, e, e.then_expr, env, fi, 0)
    if fi.b != nil && fusing(c) != nil { graph_fuse_if_expr_else(fi.b, &fi.gi) }
    else_type := fuse_if_branch(c, e, e.else_expr, env, fi, 1)
    if fi.b != nil && fusing(c) != nil { graph_fuse_if_expr_end(fi.b, &fi.gi) }
    // Unify: if either is untyped/infer, adopt the other
    if is_untyped(then_type) || is_infer(then_type) { return else_type }
    if is_untyped(else_type) || is_infer(else_type) { return then_type }
    if types_incompatible(then_type, else_type) {
        check_error(c, e.span, TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS,
            type_name(then_type), type_name(else_type))
    }
    return then_type
}

check_struct_literal_impl :: proc(c: ^Checker, e: ^Expr_Struct_Literal, env: ^Type_Scope) -> Type {
    // Broadcast literal `{all <expr>}`: expand_broadcast_array_literal
    // has already validated and populated array_values, and set e.type_
    // to the surrounding field/decl type. Don't re-check (which would
    // return Type_Error for the anonymous shape) and overwrite the type.
    if e.is_broadcast && e.type_ != nil {
        if _, is_err := e.type_.(Type_Error); !is_err {
            // A field's (typed in the field pass): its value checked here.
            fl: ^Fuse_Lit
            if c.lit != nil && c.lit.e == e { fl, c.lit = c.lit, nil }
            if _, is_field := c.broadcast_fields[rawptr(e)]; is_field { check_field_broadcast(c, e, env, fl) }
            return e.type_
        }
    }
    // Inline typed-array literal: `[3]f32{0.9, 0.2, 0.6}`. The parser
    // attaches the inline type expression; resolve it and reuse the
    // array-literal validation path used by named distinct array types.
    if e.type_expr != nil {
        resolved := resolve_type_expr(e.type_expr, c, e.span, env = env)
        if fa, fa_ok := resolved.(^Type_Fixed_Array); fa_ok {
            check_array_struct_literal(c, e, fa, env, resolved)
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
            // (Built: its zero, where it goes.)
            if fl := c.lit; fl != nil && fl.e == e {
                c.lit = nil
                if b := fusing(c); b != nil { fl.built = graph_fuse_literal(b, e, resolved, fl.dest) != nil }
            }
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
                check_array_struct_literal(c, e, fa, env, dt)
                return dt
            }
        }
    }
    // Dotted type path: `Parent.Inner{...}` / `mod.Type{...}` /
    // `Union.Variant{...}` — resolve through the same machinery as type
    // position, which owns all the dotted cases (module aliases, nested
    // types, variant structs). A dotted name can never be a variable or
    // a local, so a resolution miss is a hard error here rather than the
    // suppressed fallthrough bare names get.
    if strings.index_byte(e.name, '.') >= 0 {
        resolved := resolve_type_expr(Type_Name{name = e.name, span = e.span}, c, e.span, env = env)
        if sd := as_scope_body(resolved); sd != nil {
            e.type_ = resolved
            check_struct_literal_fields(c, e, sd, e.span, env)
            return resolved
        }
        if dt, dt_ok := resolved.(^Type_Distinct); dt_ok {
            if fa, fa_ok := dt.base_type.(^Type_Fixed_Array); fa_ok {
                check_array_struct_literal(c, e, fa, env, dt)
                e.type_ = dt
                return dt
            }
        }
        check_error(c, e.span, TYPE_STRUCT_LITERAL_NAME_NOT_STRUCT, e.name, e.name)
        return Type_Error{}
    }
    // Named struct literal: run the full field-matching check (positional vs
    // named, multi-return spread, types). Without this, `x := Foo{call()}`
    // with no annotation would skip the structural check and is_spread
    // never gets set by the spread-detection branch.
    if e.name != "" {
        flat := resolve_type_name(c, e.name, "", env)
        if st, ok := c.table.structs[flat]; ok {
            e.type_ = st
            check_struct_literal_fields(c, e, &st.sd, e.span, env)
            return st
        }
        if st, ok := c.table.funs[flat]; ok {
            e.type_ = st
            check_struct_literal_fields(c, e, &st.sd, e.span, env)
            return st
        }
        // Function-LOCAL struct types are keyed in c.table.structs by a
        // MANGLED name (enclosing + "_" + bare); resolve_type_name produces
        // a module-flat name that doesn't match, so a local `LocalStruct{...}`
        // misses the lookups above. Find it through the env, which binds the
        // nested type directly (codegen's lookup_struct then finds it by the
        // same mangled name). Guard with a name match — the type's mangled
        // name equals or ends with `_<e.name>` — so a VARIABLE of that struct
        // type (`var{...}`, the copy form) isn't silently turned into a
        // construct-new; that stays unsupported for now.
        if tv, found := type_env_get(env, e.name); found {
            if ts, ts_ok := tv.(^Type_Scope); ts_ok && ts.kind == .Struct {
                names_type := ts.name == e.name ||
                    strings.has_suffix(ts.name, strings.concatenate({"_", e.name}))
                if names_type {
                    e.type_ = ts
                    check_struct_literal_fields(c, e, &ts.sd, e.span, env)
                    return ts
                }
                // e.name is a struct VARIABLE in value position — the
                // copy-with-overrides form (`new := var{...}`), which is
                // not implemented. Hard error; the old fallthrough yielded
                // an untyped value with checking bypassed.
                check_error(c, e.span, TYPE_STRUCT_COPY_FORM, e.name, e.name, e.name)
                return Type_Error{}
            }
        }
    }
    // Anonymous literal with a context-supplied type. Used for things like
    // `quat_from_fwd_and_up({0, 1, 0}, {0, 0, 1})` where the parameter type
    // (Vec3 :: distinct [3]f32) is the only source of shape information.
    // Without this, array_values would never be populated and codegen
    // would emit a bare `0` for the aggregate.
    if hint := c.expected_hint; hint != nil {
        if fa, fa_ok := distinct_base(hint).(^Type_Fixed_Array); fa_ok {
            check_array_struct_literal(c, e, fa, env, hint)
            e.type_ = hint
            return hint
        }
        // Struct-typed context (call argument, mainly — assignments,
        // decls and returns have their own special-cased paths): give a
        // bare literal the same field-matching treatment those get. The
        // hinted struct's fields resolve on demand: nested in a constant
        // (`Quad{{{1, 2}, 2}, ...}`) nothing else has asked for them yet.
        if sd := as_scope_body(distinct_base(hint)); sd != nil {
            ensure_struct_signature(c, sd)
            if len(sd.fields) > 0 {
                e.type_ = hint   // (its fields are built at it)
                check_struct_literal_fields(c, e, sd, e.span, env)
                return hint
            }
        }
        // Union-typed context: a variant literal `A{...}` in a return slot,
        // argument, or nested field. Validate the variant's fields and type
        // the node as the UNION so it satisfies the slot; codegen
        // materializes the value from e.name (the tag-inclusive variant for
        // a normal union, the bare pointer for a niche one).
        if ut, ut_ok := distinct_base(hint).(^Type_Union); ut_ok && e.name != "" && e.name in ut.tag_map {
            if st, ok := c.table.structs[ut.variant_structs[e.name]]; ok {
                e.type_ = ut   // (its fields are built at it)
                check_struct_literal_fields(c, e, &st.sd, e.span, env)
                return ut   // node types as the union; codegen materializes the variant from e.name
            }
        }
    }
    // Bare variant literal with no matching type hint — the inferred-type
    // binding positions a `::` constant or `:=` local create, e.g.
    // `FOO :: Circle{r=3}`. When the variant name identifies a single union
    // (variant_owner_union), self-type the node as that union and validate
    // its fields, exactly as the union-hint branch above does for a hinted
    // slot; codegen then materializes the value from e.name. Without this the
    // literal stays Type_Error and codegen hits the null-pointer backstop
    // (CODE_STRUCT_LITERAL_UNTYPED_EXPR) — the silent-accept-then-late-abort
    // anti-pattern. This extends "bare variant resolution goes through an
    // expected type" to the binding positions, where the value's own type IS
    // the inferred type (mirroring how a struct literal `Foo{...}` self-types).
    if e.name != "" {
        if ut := variant_owner_union(c, e.name); ut != nil {
            if st, ok := c.table.structs[ut.variant_structs[e.name]]; ok {
                e.type_ = ut   // (its fields are built at it)
                check_struct_literal_fields(c, e, &st.sd, e.span, env)
                return ut
            }
        }
    }
    // Bare variant literal whose name is shared by 2+ unions/enums — the
    // ambiguity sentinel "" that register_enum_variants writes into
    // variant_to_enum (variant_owner_union returns nil for it). We only
    // reach here HINT-LESS: the union-hint branch above returns for any
    // context that supplies an expected type, and check_define now feeds an
    // annotated `::`'s type as a hint too — so the name has no single
    // inferred owner. Emit a located error pointing at the qualified form
    // (`A.Dup{...}`, handled by the dotted path above) or annotating the
    // binding, mirroring resolve_variant_ident's ambiguity diagnostic for
    // the `.Variant` dot-shorthand. Without this the literal silently stays
    // Type_Error and codegen aborts one phase too late
    // (CODE_STRUCT_LITERAL_UNTYPED_EXPR).
    if e.name != "" {
        if owner, mapped := c.table.variant_to_enum[e.name]; mapped && owner == "" {
            // List only the UNIONS that own this variant: a `{...}` literal
            // constructs a payload, which is meaningful for unions but not
            // plain enums, and the synthetic <Name>_Tag enums each union
            // carries would otherwise pollute the list.
            owners: [dynamic]string
            defer delete(owners)
            for _, ut in c.table.unions {
                if e.name in ut.tag_map {
                    append(&owners, ut.source_name if ut.source_name != "" else ut.name)
                }
            }
            slice.sort(owners[:])
            first := owners[0] if len(owners) > 0 else e.name
            check_error(c, e.span, TYPE_AMBIGUOUS_VARIANT_LITERAL,
                e.name, strings.join(owners[:], ", "), first, e.name)
            return Type_Error{}
        }
    }
    // Anonymous struct literal: just check each field value. A name that
    // matched no type, struct variable, variant, or hint reaches here and
    // stays a suppressed Type_Error (e.g. context-typed variant literals
    // are validated by the enclosing decl, not here) — so we can't turn
    // this into a hard "undefined" error without false-flagging them.
    //
    // BUT a NAMED literal whose name is neither a known variant nor a bound
    // local matched nothing at all — `Nonexist{...}`. That is a genuine
    // unknown type, so emit the same `unknown type 'X'` the type-annotation
    // path gives, one phase before codegen's null-pointer backstop
    // (CODE_STRUCT_LITERAL_UNTYPED_EXPR) would otherwise fire. A bare variant
    // literal (`Circle{...}`) is spared: it is validated later against its
    // union by the enclosing annotated decl / return / arg (check_define
    // runs check_expr hint-lessly first). Variant ownership lives in the same
    // variant→owner index the `.N` dot-shorthand resolves through — union
    // variants land there via each union's synthetic tag enum — so reuse it
    // rather than rescanning the union table.
    _, is_known_variant := c.table.variant_to_enum[e.name]
    if e.name != "" && !is_known_variant {
        if _, _, bound := type_env_locate(env, e.name); !bound {
            check_error(c, e.span, TYPE_UNKNOWN_TYPE, e.name)
        }
    }
    for field in e.fields {
        check_expr(c, field.value, env)
    }
    return Type_Error{}
}

check_expr_impl :: proc(c: ^Checker, expr: Expr, env: ^Type_Scope) -> Type {
    switch e in expr {
    case ^Expr_Number:
        if e.is_float {
            return Type_Infer_Float{}
        }
        return Type_Infer_Int{}
    case ^Expr_String:
        // String literals are partial arrays of utf8 at a QUANTIZED capacity
        // tier — [..64] / [..256] / [..1024]utf8, smallest tier strictly
        // larger than the byte length (see string_literal_cap). Three types
        // serve every literal instead of one per length, and a `:=` copy is
        // born with headroom, so appends and cstring conversion both work
        // on it. The bytes live in rodata (one global per unique literal,
        // deduped at codegen, with a trailing \0 so literal→cstring is
        // free); use sites synthesize an HONEST header — len = cap = byte
        // length — pointing at the global, so the quantized cap only
        // materializes when the literal is copied into storage the user
        // owns (decl init, field default).
        pa := new(Type_Partial_Array)
        pa.size = string_literal_cap(len(e.value))
        pa.elem = Type_Utf8{}
        return pa
    case ^Expr_Char:
        return Type_Utf8{}
    case ^Expr_Bool:
        return Type_Bool{}
    case ^Expr_Skip_Constructor:
        // `---` carries no intrinsic type — the type comes from the LHS
        // (a field's declared type or a local's type annotation). The
        // checker treats it as Type_Any so any LHS accepts it; codegen
        // recognizes the marker and skips constructor / default emission.
        return Type_Any{}
    case ^Expr_Ident:
        // A dot-ref lowered to an expression (`.len` in a subscript) is that
        // expression — typed with the hint still in place, as if written out.
        if e.lowered != nil {
            c.want, c.want_written, c.asked = c.asked, c.asked_written, .None   // (built as it)
            return check_expr(c, e.lowered, env)
        }
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

        // A bare module-constant must resolve to exactly ONE visible module.
        // resolve_const_ref walks the scope (own module + each `use`d include);
        // 2+ visible definers -> force qualification (Module.name). The scope is
        // the resolver; this replaces the old global constant_owners=="" check,
        // which was too coarse (it flagged a name reused by a module out of scope).
        if cflat, vis_count := resolve_const_ref(c, env, e.name); vis_count >= 2 {
            owners: [dynamic]string
            defer delete(owners)
            suffix := strings.concatenate({"_", e.name})
            for flat, _ in c.table.constants {
                if strings.has_suffix(flat, suffix) && flat != e.name {
                    pkg := flat[:len(flat) - len(suffix)]
                    // Flat names use underscore as separator; dotted-name modules
                    // like "mara.memory" appear here as "mara_memory". Convert to
                    // the user-facing dotted form for the diagnostic.
                    if strings.has_prefix(pkg, "mara_") {
                        pkg = strings.concatenate({"mara.", pkg[len("mara_"):]})
                    }
                    append(&owners, pkg)
                }
            }
            joined := strings.join(owners[:], ", ")
            first := owners[0] if len(owners) > 0 else e.name
            check_error(c, e.span,
                TYPE_CONSTANT_AMBIGUOUS_DEFINED_USE_QUALIFIED,
                e.name, joined, first, e.name)
            return Type_Error{}
        } else if vis_count == 1 {
            // Unambiguous module constant: resolve it to THIS module's value
            // expression, so codegen inlines the right value without re-resolving
            // by name (another module out of scope can reuse the name harmlessly).
            if vexpr, vok := c.table.constants[cflat]; vok {
                e.resolved = Resolved_Constant{value_expr = vexpr}
            }
        }

        // (Reading an uninitialized pointer/slice is now caught by the post-check
        // flow pass — flow.odin / definite-assignment.)
        // Check env (common case: local vars, params, functions)
        t, loc_scope, ok := type_env_locate(env, e.name)
        if ok {
            // Field-leak guard: if the name resolved in an ancestor class scope (a
            // non-module .Struct) AND is a field of that class, the caller is a
            // nested scope (method body) trying to access a field as a bare name.
            // Require receiver access instead.
            if loc_scope != nil && loc_scope.kind == .Struct && !loc_scope.is_module {
                if is_real_field(&loc_scope.sd, e.name) {
                    check_error(c, e.span,
                        TYPE_FIELD_ACCESS_THROUGH_RECEIVER,
                        e.name, loc_scope.name, e.name)
                    return Type_Error{}
                }
            }
            // A constant declared in a scope — a struct's, a fun's — resolves to
            // its own declaration's value, not by name: another scope or module
            // can reuse the name (`HEADER_SIZE` in two places read the wrong one),
            // and it shadows a module constant of that name. (A fun body's
            // constants are bound in its module's scope: those, when nothing
            // else resolved the name.)
            // A block local (no scope found): the blocks out to its fun.
            def: ^Stmt_Define
            if loc_scope == nil {
                for s := env; s != nil; s = s.parent_scope {
                    if d, ok := s.sd.consts[e.name]; ok { def = d; break }
                    if s.kind != .Block { break }
                }
            } else if !loc_scope.is_module || e.resolved == nil {
                def = loc_scope.sd.consts[e.name]
            }
            if def != nil && def.value != nil { e.resolved = Resolved_Constant{value_expr = def.value} }
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
        // Resolved above as a module constant (vis_count == 1) but not present in
        // this env — an IMPORTED constant referenced from a module scope (e.g. a
        // default value checked in its callee-module scope, where the env walk
        // doesn't surface the imported name). Its type is its value's type.
        if rc, rc_ok := e.resolved.(Resolved_Constant); rc_ok && rc.value_expr != nil {
            return check_expr(c, rc.value_expr, env)
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
            report_unresolved(c, e.span, env, e.name, TYPE_UNDEFINED_IDENTIFIER)
        }
        return Type_Error{}
    case ^Expr_Unary:
        return check_unary(c, e, env)
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
        return check_struct_literal(c, e, env)
    case ^Expr_Field_Access:
        return check_field_access(c, e, env)
    case ^Expr_Size_Of:
        // size_of(Type) — compile-time constant, infers type from context (like Zig's @sizeOf)
        resolved := resolve_type_expr(e.type_expr, c, e.span, env=env)
        if _, is_err := resolved.(Type_Error); is_err {
            check_error(c, e.span, TYPE_SIZE_UNKNOWN_TYPE)
        }
        ensure_layout(c, resolved)   // (its size: known now)
        e.resolved_type = resolved
        return Type_Infer_Int{}
    case ^Expr_Assert:
        // assert(cond) — cond must be boolean; the expression yields no value.
        // Built: the condition's value, then the assert.
        want, w := fuse_asked(c)
        cond_type: Type
        cond: Fused
        if want == .Value {
            cond_type, cond = fuse_expr(c, e.cond, env, .Value, w)
        } else {
            if want != .None { fuse_fail(c, "an assert's place") }
            cond_type = check_expr(c, e.cond, env)
        }
        if _, ok := cond_type.(Type_Bool); !ok && !is_any(cond_type) {
            check_error(c, e.span, TYPE_CONDITION_BOOL, type_name(cond_type))
        }
        e.type_ = Type_Void{}
        if b := fusing(c); b != nil && want == .Value {
            graph_assert(b, e, cond.v, w)
            fuse_done(c, NO_VALUE)
        }
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
        //   take([]T(n), ...)   — runtime-counted slice; lowered to type []T,
        //                         count n, and the result is a slice with
        //                         len=cap=n.
        //   take(T, ...)        — any other type; the byte size is sizeof(T).
        // Detect the slice form before resolution: `[]Vertex(n)` parses as
        // Type_Slice_Expr{elem = Type_Generic_Instance{Vertex, [n]}}. When the
        // elem name is not a generic template and there's exactly one type-arg,
        // the arg is a runtime count. The source stays as written; the lowered
        // form goes to e.lowered_type / e.lowered_count.
        if e.count_expr == nil {
            if ts, ts_ok := e.type_expr.(^Type_Slice_Expr); ts_ok {
                if gi, gi_ok := ts.elem.(^Type_Generic_Instance); gi_ok && len(gi.type_args) == 1 {
                    if _, is_generic := c.table.generic_templates[gi.name]; !is_generic {
                        // Arg shapes from parse_generic_arg:
                        //   Type_Const_Value  — number literal: take([]T(4), ...)
                        //   Type_Name         — bare identifier:  take([]T(n), ...)
                        //   Type_Const_Expr   — anything else:    take([]T(n*2), ...), take([]T(f(x)), ...)
                        count: Expr
                        if cv, cv_ok := gi.type_args[0].(Type_Const_Value); cv_ok {
                            num := new(Expr_Number)
                            num.int_value = i128(cv.value)
                            num.value = f64(cv.value)
                            num.span = cv.span
                            count = num
                        } else if tn, tn_ok := gi.type_args[0].(Type_Name); tn_ok {
                            count = new_clone(Expr_Ident{name = tn.name, span = tn.span})
                        } else if ce, ce_ok := gi.type_args[0].(Type_Const_Expr); ce_ok {
                            count = ce.expr
                        }
                        if count != nil {
                            bare := new_clone(ts^)
                            bare.elem = Type_Name{name = gi.name, span = gi.span}
                            e.lowered_type = bare
                            e.lowered_count = count
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
            resolved = resolve_type_expr(take_type(e), c, e.span, env=env)
            if _, is_err := resolved.(Type_Error); is_err {
                check_error(c, e.span, TYPE_TAKE_UNKNOWN_TYPE)
            }
        }
        // Built: the count at the header's width, then the storage it
        // carves from (a plain place, checked without building, built after
        // it as the builder walks it), then the carve.
        want, w := fuse_asked(c)
        b := fusing(c) if want != .None else nil
        if b != nil && (want == .Place || !fuse_carves_place(e)) {
            fuse_fail(c, "a take's place, or a take from no plain place")
            b = nil
        }
        count_op := NO_VALUE
        // Runtime-counted form: validate count is integer at slice header
        // width, resolved is a slice. Codegen does NOT emit an implicit
        // narrow/widen on the count.
        if count := take_count(e); count != nil {
            count_type: Type
            if b != nil { count_type, count_op = fuse_bound(c, count, env, w, e.span) } else { count_type = check_expr(c, count, env) }
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
        e.type_ = resolved
        if b != nil && fusing(c) != nil { fuse_done(c, graph_fuse_carve(b, e, count_op, w)) }
        return resolved
    case ^Expr_If:
        return check_if_expr(c, e, env)
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
            if existing_sd := as_scope_body(existing); sd_is_module(existing_sd) {
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
        // Built: the slots of one call share it — built at the first, each
        // slot one of its outputs; a broadcast's is its value, again.
        want, w := fuse_asked(c)
        shared := e.index > 0 && len(call_return_list(c, e.source, env)) > 1
        src_type: Type
        src: Fused
        if want != .None && !shared {
            src_type, src = fuse_expr(c, e.source, env, .Value, w)
        } else {
            src_type = check_expr(c, e.source, env)
        }
        if b := fusing(c); b != nil && want != .None {
            key := rawptr(e.source.(^Expr_Call)) if len(call_return_list(c, e.source, env)) > 1 else nil
            switch {
            case key == nil:  fuse_done(c, src.v)
            case e.index == 0:
                graph_fuse_tuple_set(b, key, src.v.op)
                fuse_done(c, src.v)
            case:
                if op, ok := graph_fuse_tuple_get(b, key); ok {
                    fuse_done(c, {op, i32(e.index)})
                } else {
                    fuse_fail(c, "a default's slot before its call")
                }
            }
        }
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
        // `#self` is the receiver the CONSTRUCTOR is writing into — a FRAME
        // concept, not a namespace one. Resolve it through the nearest enclosing
        // FRAME (enclosing_callable_scope), which stops at the no-closures
        // boundary, rather than the namespace walk to the nearest struct: it's
        // legal iff the frame we are the body of IS a struct (a constructor).
        // A method or a nested helper, whose frame is a .Fun, must take an
        // explicit `^Self` param instead — `#self` there has no sret to point at
        // (codegen would emit an undefined %sret), so reject it here.
        if f := enclosing_callable_scope(env); f != nil && f.kind == .Struct {
            t := new_clone(Type_Ptr{elem = f})
            e.type_ = t
            return t
        }
        check_error(c, e.span, TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT)
        return Type_Error{}
    }
    return Type_Error{}
}

// Demand-driven signature resolution: ensure a struct's fields (and, for a
// parameterized constructor, its ctor params via check_scope_body's .Struct
// block) are resolved before a use site reads them. Memoization + cycle guard
// live in check_scope_body, keyed on sig_state.
ensure_struct_signature :: proc(c: ^Checker, st: ^Scope_Body) {
    if st == nil || st.sig_state != .Unresolved || st.ast == nil { return }
    env := st.decl_env
    if env == nil {
        // Nested struct: its decl env was transient. Reconstruct it from the
        // durable parent_scope graph and resolve THIS struct's body directly.
        // (Recursing to the parent was wrong when the parent is a FUN — a fun's
        // signature_only pass never descends into a nested struct's body, so a
        // parameterized struct nested in a function, `data :: fun() { With_Args
        // :: struct(cap){...} }`, never resolved its fields OR ctor params and
        // construction saw it as 0-field. transmute: st IS a Type_Scope's sd in
        // the nested case — parent_scope is only ever set on a Type_Scope.)
        env = build_scope_decl_env(transmute(^Type_Scope)st)
    }
    if env != nil {
        check_scope_body(c, st.ast, env, signature_only = true)
    }
}

// The scope a scope's signature resolves against. Resolution walks up the durable
// parent_scope chain, so this is just the declaring (parent) scope — a NESTED
// scope resolves on demand against it; top-level scopes keep a persistent
// decl_env pinned at registration time.
build_scope_decl_env :: proc(ft: ^Type_Scope) -> ^Type_Scope {
    if ft == nil { return nil }
    if ft.decl_env != nil { return ft.decl_env }
    return ft.parent_scope
}

// Resolve a fun's signature (param + return types) from its AST, in the env it
// was declared in (build_scope_decl_env — durable, works for nested funs).
// Idempotent: skips a list that's already populated, so repeated demand pulls
// and the cycle guard are no-ops once resolved.
resolve_fun_signature :: proc(c: ^Checker, ft: ^Type_Scope) {
    outer := fuse_suspend(c)
    defer fuse_resume(c, outer)
    if ft.ast == nil { return }
    env := build_scope_decl_env(ft)
    if env == nil { return }
    s := ft.ast
    if len(ft.params) == 0 && len(s.typed_params) > 0 {
        for tp in s.typed_params {
            pt := resolve_param_type(c, tp, env, s.span)
            append(&ft.params, Struct_Type_Field{name = tp.name, type_ = pt, default_value = tp.default_value})
        }
        build_param_map(ft)
    }
    if len(ft.return_types) == 0 && len(s.return_types) > 0 {
        for rte in s.return_types {
            append(&ft.return_types, resolve_type_expr(rte, c, s.span, env = env))
        }
    }
}

// Demand-driven fun-signature resolution: ensure a fun's params/returns are
// resolved before a use site (a call, a dispatch match, the body's own param
// binding, a field-type inference reading its return) reads them. Memoized +
// cycle-guarded via sig_state. Works for ALL funs — top-level ones resolve
// against their persistent decl_env, nested ones against a decl env rebuilt
// from the durable parent_scope graph (build_scope_decl_env). No eager pass.
// A type's layout, complete: each struct in it resolved — for a size taken
// before any use resolved one.
ensure_layout :: proc(c: ^Checker, t: Type) {
    #partial switch v in t {
    case ^Type_Scope:
        if v.kind != .Struct { return }
        ensure_struct_signature(c, &v.sd)
        for f in v.sd.fields { ensure_layout(c, f.type_) }
    case ^Type_Fixed_Array:   ensure_layout(c, v.elem)
    case ^Type_Partial_Array: ensure_layout(c, v.elem)
    case ^Type_Distinct:      ensure_layout(c, v.base_type)
    case ^Type_Union:
        for _, flat in v.variant_structs {
            if st, ok := c.table.structs[flat]; ok { ensure_layout(c, st) }
        }
    }
}

ensure_fun_signature :: proc(c: ^Checker, ft: ^Type_Scope) {
    if ft == nil || ft.kind != .Fun || ft.sig_state != .Unresolved { return }
    ft.sig_state = .In_Progress
    resolve_fun_signature(c, ft)
    ft.sig_state = .Resolved
}

// Shared struct field access logic — used for both direct and auto-deref (^Struct) paths.
// Handles uninit checks, field resolution, and associated function lookup.
check_struct_field_access :: proc(c: ^Checker, e: ^Expr_Field_Access, st: ^Scope_Body, env: ^Type_Scope) -> Type {
    // (Reading an uninitialized pointer/slice field — including through an
    // `it = &root` alias — is now caught by the post-check flow pass.)
    ensure_struct_signature(c, st)  // resolve fields on demand if no pre-pass did
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

// A field access, built: a member is its base's place (through a pointer,
// what it points at), then the field. What names no member — a variant, a
// constant, a module's function — is a value of its own: its base, built
// before that was known, is left out.
Fuse_Field :: struct {
    on:        bool,
    mark:      Graph_Mark,
    base:      Fused,
    base_type: Type,
}

check_field_access :: proc(c: ^Checker, e: ^Expr_Field_Access, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    d, into_temp, temp_span := c.asked_dest, c.asked_temp, c.asked_span
    b := fusing(c)
    if want == .None || b == nil { return check_field_access_impl(c, e, env, nil) }
    ff := Fuse_Field{on = true, mark = graph_fuse_mark(b)}
    t := check_field_access_impl(c, e, env, &ff)
    if fusing(c) == nil { return t }
    set_expr_type(e, t)   // (the builder's reads it)
    if e.resolved == nil || graph_is_member(e.resolved) {
        p := fuse_member_place(c, e, ff.base, ff.base_type, t)
        if p == NO_VALUE { return t }
        if want == .Value {
            fuse_done(c, graph_read(b, p, t, e.span))
        } else {
            fuse_done(c, p, true)
        }
        return t
    }
    graph_fuse_drop_since(b, ff.mark)
    _, is_const := e.resolved.(Resolved_Constant)
    _, is_variant := e.resolved.(Resolved_Union_Variant)
    switch {
    case want == .Into && is_variant:
        if into_temp { d = graph_fuse_temp(b, temp_span, fuse_temp_type(d)) }
        fuse_variant(c, t, e.field, d, e.span)
        if b := fusing(c); b != nil { fuse_built(c, b, want, into_temp, into_temp, d, t, temp_span) }
    case is_variant && want != .Place:    fuse_done(c, fuse_variant_value(c, t, e.field, e.span))
    case want == .Value:                  fuse_done(c, graph_leaf(b, e, w))
    case is_const && graph_aggregate(t):  fuse_done(c, graph_plain_place(b, e, e.span), true)   // a constant table
    case want != .Place:                  fuse_done(c, graph_leaf(b, e, w))
    }
    return t
}

// A member's place (graph_place): its base's — through a pointer, what it
// points at — then the field, or a swizzle of an array.
fuse_member_place :: proc(c: ^Checker, e: ^Expr_Field_Access, base: Fused, base_type: Type, t: Type) -> Operand {
    b := fusing(c)
    if b == nil { return NO_VALUE }
    if !base.ok || !base.place {
        fuse_fail(c, "a field of a value")
        return NO_VALUE
    }
    p := base.v
    if _, is_self := e.expr.(^Expr_Self); !is_self {
        if pt, is_ptr := distinct_base(base_type).(^Type_Ptr); is_ptr {
            p = graph_op_value(b, .Deref, .Implied, e.span, pt.elem, "", p)
        }
    }
    _, is_array := distinct_base(graph_pointee(base_type)).(^Type_Fixed_Array)
    return graph_op_value(b, .Swizzle if is_array else .Field, .Explicit, e.span, t, e.field, p)
}

// The type of a written field that is no struct's (as check_field_assign
// finds it after the value): a header's len, cap or ptr; an array's swizzle.
fuse_target_field_type :: proc(obj_type: Type, field: string) -> Type {
    t := obj_type
    if pt, ok := t.(^Type_Ptr); ok { t = pt.elem }
    t = distinct_base(t)
    elem: Type
    #partial switch v in t {
    case ^Type_Slice:         elem = v.elem
    case ^Type_Partial_Array: elem = v.elem
    case ^Type_Fixed_Array:
        if !is_swizzle_field(field, v.size) { return nil }
        if len(field) == 1 { return v.elem }
        return new_clone(Type_Fixed_Array{size = len(field), elem = v.elem})
    case:
        return nil
    }
    switch field {
    case "len", "cap": return slice_header_width_type
    case "ptr":        return new_clone(Type_Ptr{elem = elem})
    }
    return nil
}

// An index at the header's width (graph_index_value): an enum's value is its
// tag, taken as a number; a narrower number widens.
fuse_index_value :: proc(b: ^Graph_Builder, at: Operand, t: Type, span: Span) -> Operand {
    if _, is_enum := distinct_base(t).(^Type_Enum); is_enum {
        return graph_op_value(b, .Cast, .Implied, span, slice_header_width_type, type_name(slice_header_width_type), at)
    }
    return graph_fuse_widen(b, at, span, {to = slice_header_width_type})
}

// A store's value into the place its target's check built (graph_assign):
// checked, then — a view where one is taken, else at the place's type —
// written. A compound `t op= x` reads the target through that place.
Fuse_Store :: struct {
    on:    bool,
    place: Operand,
    value: Fused,
    vt:    Type,
    void:  bool,
}

fuse_store :: proc(c: ^Checker, s: ^Stmt_Assign, place: Operand, env: ^Type_Scope) -> Type {
    vt, fs := fuse_store_value(c, s, place, env)
    // (Its target's type: a field's, what a pointer points at.)
    fuse_store_write(c, s, &fs, fusing(c).g.type_[place.op] if fs.on && fusing(c) != nil else nil)
    return vt
}

fuse_store_value :: proc(c: ^Checker, s: ^Stmt_Assign, place: Operand, env: ^Type_Scope, unplaced := false) -> (Type, Fuse_Store) {
    b := fusing(c)
    if b == nil || place == NO_VALUE && !unplaced { return check_expr(c, s.value, env), {} }
    // (`= void` writes the uninitialized value: its value isn't built.)
    if _, is_skip := s.value.(^Expr_Skip_Constructor); is_skip || is_void_literal(s.value) {
        return check_expr(c, s.value, env), {on = true, place = place, void = true}
    }
    saved := c.compound
    if s.is_compound { c.compound = {expr_identity(s.target), place} }
    // (What builds in place builds in a temporary, then is written.)
    // (`unplaced`: its target is built once the value is — of no type yet.)
    pt: Type = b.g.type_[place.op] if place.op != NO_NODE else nil
    vt, r := fuse_expr(c, s.value, env, .Into, dest = Dest{kind = .At, at = place, type_ = pt}, temp = true, temp_span = s.span)
    c.compound = saved
    return vt, {true, place, r, vt, false}
}

// The write, `dt` its target's type (the checker's); `view` the type bytes
// are written as (the target's place is then a view of them).
fuse_store_write :: proc(c: ^Checker, s: ^Stmt_Assign, fs: ^Fuse_Store, dt: Type, view: Type = nil, big := false) {
    b := fusing(c)
    if b == nil || !fs.on { return }
    if view != nil { graph_fuse_view(b, fs.place, view, big, s.span) }
    if fs.void {
        // (Its value unbuilt: of its target's type — an element's, where
        // `dt` is its collection's.)
        t := b.g.type_[fs.place.op] if b.g.type_[fs.place.op] != nil else dt
        graph_fuse_write_at(b, fs.place, graph_fuse_void(b, t, expr_span(s.value)^), s.span)
        return
    }
    fuse_store_finish(c, s.value, fs.vt, fs.value, fuse_parallel_hold(c, Dest{kind = .At, at = fs.place, type_ = dt}, s.span), s.span, settle = true)
}

check_field_access_impl :: proc(c: ^Checker, e: ^Expr_Field_Access, env: ^Type_Scope, ff: ^Fuse_Field) -> Type {
    // Self-module qualification: `<current_package>.X` resolves X via the
    // current module's flat-name table or env directly. The main package
    // doesn't get a synthesized mod_struct (unlike imported modules), so its
    // own name isn't in env — we intercept the qualifier here. Imported
    // modules already have mod_struct registered, so they fall through to
    // the normal field-access flow.
    if ident, ok := e.expr.(^Expr_Ident); ok && ident.name == c.current_package && c.current_package != "" {
        flat := make_flat_name(c.current_package, e.field)
        if const_expr, ce_ok := c.table.constants[flat]; ce_ok {
            // Self-module qualifier (`Pkg.X` inside Pkg): resolve to the value
            // expression — codegen inlines it for any type, scalar or aggregate.
            e.resolved = Resolved_Constant{value_expr = const_expr}
            // Best-effort type: re-check the constant value's expression.
            return check_expr(c, const_expr, env)
        }
    }
    obj_type: Type
    if ff != nil {
        // (A call is only a member's base: its place, a temporary; `#self`
        // names Self.)
        _, of_call := e.expr.(^Expr_Call)
        _, of_self := e.expr.(^Expr_Self)
        obj_type, ff.base = fuse_expr(c, e.expr, env, .Place if of_call || of_self || fuse_holds(e.expr) else .Either, temp_span = e.span)
        ff.base_type = obj_type
    } else {
        obj_type = check_expr(c, e.expr, env)
    }
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
    // On-demand: resolve the receiver struct's signature before the dispatch
    // below, which keys on len(fields) — 0 until the struct is resolved. Covers a
    // direct struct receiver and a single-level pointer (^Struct auto-deref).
    {
        rsd := as_scope_body(obj_type)
        if rsd == nil {
            if pt, pt_ok := obj_type.(^Type_Ptr); pt_ok { rsd = as_scope_body(pt.elem) }
        }
        ensure_struct_signature(c, rsd)
    }
    // On-demand: resolve the receiver struct's signature before the dispatch
    // below, which keys on len(fields) — 0 until the struct is resolved. Covers a
    // direct struct receiver and a single-level pointer (^Struct auto-deref).
    {
        rsd := as_scope_body(obj_type)
        if rsd == nil {
            if pt, pt_ok := obj_type.(^Type_Ptr); pt_ok { rsd = as_scope_body(pt.elem) }
        }
        ensure_struct_signature(c, rsd)
    }
    if sd := as_scope_body(obj_type); sd != nil && (len(sd.fields) > 0 || sd_is_module(sd)) {
        // Module-struct field access: look up in the module scope
        if msc := sd_module_scope(sd); msc != nil {
            t, found := type_env_get(msc, e.field)
            if !found {
                // Fallback: variants are no longer registered as bare names in
                // a module's scope, so `mara_open_gl.ARRAY_BUFFER` won't find
                // ARRAY_BUFFER directly. Walk the module's types for an enum
                // or union containing this variant name.
                for _, mt in sd.types {
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
            // Imported qualifier (`mod.X`): resolve to the value expression so
            // codegen inlines it for any type (scalar or aggregate).
            flat := make_flat_name(sd.name, e.field)
            if const_expr, ce_ok := c.table.constants[flat]; ce_ok {
                e.resolved = Resolved_Constant{value_expr = const_expr}
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
            e.resolved = Resolved_Constant{int_value = fa.size}
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
                        e.resolved = Resolved_Constant{int_value = len(lit.value)}
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
check_builtin_call :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Scope) -> (Type, bool) {
    check_args_n :: proc(c: ^Checker, e: ^Expr_Call, args: []Expr, env: ^Type_Scope, n: int) {
        if len(args) != n {
            check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_2,
                call_name(e), n, n == 1 ? "" : "s", len(args))
        } else {
            for arg in args {
                check_call_arg(c, arg, env)
            }
        }
    }

    opaque_ptr :: proc() -> Type {
        pt := new(Type_Ptr)
        pt.elem = Type_Any{}
        return pt
    }

    switch call_name(e) {
    case "len":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_LEN_EXPECTS_ARGUMENT, len(args))
        } else {
            arg_type := check_call_arg(c, args[0], env)
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
            arg_type := check_call_arg(c, args[0], env)
            if !is_array_type(arg_type) && !is_any(arg_type) {
                check_error(c, e.span, TYPE_CAP_REQUIRES_ARRAY_SLICE, type_name(arg_type))
            }
        }
        return slice_header_width_type, true
    case "print":
        for arg in args { check_call_arg(c, arg, env) }
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
            check_call_arg(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_cstr":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_CSTR_EXPECTS_ARGUMENT_BYTE, len(args))
        } else {
            check_call_arg(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_int":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_INT_EXPECTS_ARGUMENT_INT, len(args))
        } else {
            check_call_arg(c, args[0], env)
        }
        return Type_Error{}, true
    case "print_float":
        if len(args) != 1 {
            check_error(c, e.span, TYPE_PRINT_FLOAT_EXPECTS_ARGUMENT_FLOAT, len(args))
        } else {
            check_call_arg(c, args[0], env)
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
            ptr_type := check_call_arg(c, args[0], env)
            _, ptr_ok := ptr_type.(^Type_Ptr)
            if !ptr_ok && !is_any(ptr_type) {
                check_error(c, e.span, TYPE_SLICE_PTR_FIRST_ARGUMENT_POINTER, type_name(ptr_type))
            }
            size_type := check_call_arg(c, args[1], env)
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
    case "cstring":
        // Built-in constructor: cstring(s) — copies a Mara string into a
        // fresh NUL-terminated buffer (scope arena when live, stack
        // otherwise) and yields the C pointer. Literal args skip the copy:
        // their deduped rodata global already ends in \0. The result can
        // only feed argument positions — binding it is caught by the
        // cstring storage ban.
        if len(args) != 1 {
            check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_3, call_name(e), len(args))
            return Type_CString{}, true
        }
        src_type := check_call_arg(c, args[0], env)
        elem: Type
        #partial switch at in distinct_base(src_type) {
        case ^Type_Partial_Array: elem = at.elem
        case ^Type_Slice:         elem = at.elem
        case ^Type_Fixed_Array:   elem = at.elem
        }
        elem_ok := false
        if elem != nil {
            #partial switch _ in elem {
            case Type_Utf8, Type_Byte: elem_ok = true
            }
        }
        if !elem_ok && !is_any(src_type) {
            check_error(c, e.span, TYPE_CSTRING_CTOR_ARGUMENT, type_name(src_type))
        }
        // A runtime string's NUL-terminated copy bump-allocates from the
        // scope arena — no arena, no allocation (a runtime-sized stack
        // alloca would be a VLA: unbounded, input-driven growth; rejected).
        // The requirement is enforced at RUNTIME by codegen (loud crash at
        // the conversion site) rather than here: a compile-time rule would
        // need call-graph reachability, and without it merely importing a
        // module that contains a conversion would break arena-less builds.
        return Type_CString{}, true
    }

    // Type casts: i32(x), f64(x), etc.
    is_type_cast :: proc(name: string) -> bool {
        switch name {
        case "int", "uint",
             "i8", "i16", "i32", "i64", "i128",
             "u8", "u16", "u32", "u64", "u128",
             "usize", "isize",
             "f16", "f32", "f64", "utf8", "bool":
            return true   // int / uint kept here so the cast site emits the
                          // same "reserved" error as a type position would,
                          // instead of a generic "unknown function".
        }
        return false
    }
    if is_type_cast(call_name(e)) {
        if len(args) != 1 {
            check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_3, call_name(e), len(args))
            return Type_Error{}, true
        }
        src_type := check_call_arg(c, args[0], env)
        // Redundant-cast warning: an identity cast — the operand already has the
        // target type — is a no-op in every context, so the fossil can be
        // dropped. cast_target_same_as_operand is a STRICT same-type test (not
        // types_equal, which treats untyped literals as every numeric): it skips
        // literal/const ascriptions, distinct unwraps, and the byte/u8/utf8
        // trio. Widening casts are left alone — their removability is
        // context-dependent (see WARN_REDUNDANT_CAST).
        if target_t, t_ok := cast_result_type(call_name(e)); t_ok {
            if cast_target_same_as_operand(src_type, target_t) {
                operand := expr_diag_name(args[0])
                if operand == "" { operand = "the operand" }
                check_warning(c, e.span, WARN_REDUNDANT_CAST, call_name(e), operand, call_name(e))
            }
        }
        switch call_name(e) {
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
        case "utf8": return Type_Utf8{}, true
        case "bool": return Type_Bool{}, true
        }
    }

    return Type_Error{}, false
}

// A binary operation, built: each side's value, widened to the type it works
// in (decided once that is known), then it. (`and` / `or` run their right
// side only when needed; an overload is a call.)
Fuse_Binary :: struct {
    w:     Written,
    span:  Span,
    sides: [2]Operand,
    types: [2]Type,
    widen: [2]int,   // each side's widening, in the body's list; -1 for none
    and:   Maybe(Graph_And),   // `and` / `or`: the right side runs when needed
    array: [2]bool,  // the side is an array's value, no place
}

check_binary :: proc(c: ^Checker, e: ^Expr_Binary, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    b := fusing(c)
    if want == .None || b == nil { return check_binary_impl(c, e, env, nil) }
    if want == .Place {
        fuse_fail(c, "a binary's place")
        return check_binary_impl(c, e, env, nil)
    }
    fb := Fuse_Binary{w = w, span = e.span, widen = {-1, -1}}
    if e.op == .And || e.op == .Or { fb.and = graph_fuse_and(b, e.op == .And, w, e.span) }
    t := check_binary_impl(c, e, env, &fb)
    if fusing(c) == nil { return t }
    if sa, is_and := &fb.and.?; is_and {
        if _, is_bool := t.(Type_Bool); !is_bool {
            fuse_fail(c, "and / or of no bool")
            return t
        }
        fuse_done(c, graph_fuse_and_end(b, sa, fb.sides[1]))
        return t
    }
    // Each side at the type the operation works in; an overload's, at its
    // param's (a call).
    if rf, over := e.overload_fn.?; over {
        callee := graph_callee(b, rf)
        if callee == nil {
            fuse_fail(c, "an operator resolved to no function")
            return t
        }
        for k, i in fb.widen {
            if k >= 0 && i < len(callee.params) { b.fuse.widens[k].sig, b.fuse.widens[k].param = callee, i }
        }
        for is_array, i in fb.array {
            if !is_array || i >= len(callee.params) { continue }
            if _, to_slice := distinct_base(callee.params[i].type_).(^Type_Slice); to_slice {
                fuse_fail(c, "an array's value viewed by an operator")
                return t
            }
        }
        kind: Op_Kind = .Construct if callee.kind == .Struct else .Call
        fuse_done(c, {graph_call_op(b, kind, w, e.span, callee, t, fb.sides[0], fb.sides[1]), 0})
        return t
    }
    work := Graph_Work{e.op, t, fb.types[0], fb.types[1]}
    for k in fb.widen {
        if k >= 0 { b.fuse.widens[k].work, b.fuse.widens[k].binary, b.fuse.widens[k].views = work, true, false }
    }
    kind: Op_Kind = .Compare if is_comparison_op(e.op) else .Arith
    word := graph_token_text(e.op)
    if e.wrapping { word = strings.concatenate({word, "%"}) }   // `+%` `-%` `*%` wrap
    fuse_done(c, graph_op_value(b, kind, w, e.span, t, word, fb.sides[0], fb.sides[1]))
    return t
}

fuse_side :: proc(c: ^Checker, e: Expr, env: ^Type_Scope, fb: ^Fuse_Binary, k: int) -> Type {
    if fb == nil { return check_expr(c, e, env) }
    if fb.and != nil {
        t, r := fuse_expr(c, e, env, .Value, fb.w)
        fb.types[k] = t
        b := fusing(c)
        if b == nil { return t }
        fb.sides[k] = r.v
        if k == 0 { graph_fuse_and_left(b, &fb.and.?, r.v) }
        return t
    }
    // (An overload's param is known once both sides are: a place's view, or
    // its read, is chosen then.)
    t, r := fuse_expr(c, e, env, .Either, fb.w)
    fb.types[k] = t
    b := fusing(c)
    if b == nil { return t }
    if _, is_literal := e.(^Expr_Array); is_literal {
        fuse_fail(c, "an array literal as an operand")
        return t
    }
    _, is_array := distinct_base(t).(^Type_Fixed_Array)
    fb.array[k] = is_array && !r.place
    fb.sides[k], fb.widen[k] = graph_fuse_as(b, r.v, r.place, t, expr_span(e)^, fb.span, {})
    return t
}

check_binary_impl :: proc(c: ^Checker, e: ^Expr_Binary, env: ^Type_Scope, fb: ^Fuse_Binary) -> Type {
    // Propagate the hint to both sides so `OpenGL | Resizable` resolves both
    // operands against the surrounding `WindowFlags` expectation.
    hint := c.expected_hint
    c.expected_hint = hint
    left_type := fuse_side(c, e.left, env, fb, 0)
    c.expected_hint = hint
    right_type := fuse_side(c, e.right, env, fb, 1)

    // Wrapping operators (`+%`/`-%`/`*%`) are integer-only — two's-complement
    // wrap has no meaning for floats, and there's no overload concept. Otherwise
    // they type exactly like `+`/`-`/`*` (op was already mapped), so fall through.
    if e.wrapping {
        if !is_wrap_operand(left_type) || !is_wrap_operand(right_type) {
            check_error(c, e.span, TYPE_WRAPPING_REQUIRES_INTEGER,
                op_str(e.op), type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
    }

    // Operator overload check: try before built-in arithmetic when at least one
    // operand is non-numeric (so int*int always uses the fast built-in path).
    if !is_numeric(left_type) || !is_numeric(right_type) {
        if dispatch_names, has_overload := find_operator_overload(c, env, e.op); has_overload {
            // Collect all matching candidates, then pick the best (most specific) one.
            // Priority: concrete exact > concrete structural > generic
            best_flat := ""
            best_ft: ^Type_Scope = nil  // resolved callee for the winning best_flat
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
                                    mono_flat, mono_ft := auto_monomorphize_for_struct(c, fn_name, ft, actual_types[:], env)
                                    if mono_flat != "" {
                                        best_flat = mono_flat
                                        best_ft = mono_ft
                                    } else {
                                        best_flat = make_flat_name(resolve_fn_home(c, env,fn_name), fn_name)
                                        best_ft = ft
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
                                    best_ft = fun_type
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
                e.overload_fn = Resolved_Func{name = best_flat, callee = best_ft}
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
        return coerce_infer_to_hint(c, promote_numeric(c, left_type, right_type, e.span), hint, e.span)

    case .Minus, .Star, .Slash, .Modulo:
        if !is_numeric(left_type) || !is_numeric(right_type) {
            op_sym := e.op == .Minus ? "-" : e.op == .Star ? "*" : e.op == .Slash ? "/" : "%%"
            check_error(c, e.span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2,
                op_sym, type_name(left_type), type_name(right_type))
            return Type_Error{}
        }
        return coerce_infer_to_hint(c, promote_numeric(c, left_type, right_type, e.span), hint, e.span)

    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(left_type) && !is_any(left_type) {
            check_error(c, e.span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(left_type))
            return Type_Error{}
        }
        if !is_integer(right_type) && !is_any(right_type) {
            check_error(c, e.span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(right_type))
            return Type_Error{}
        }
        return coerce_infer_to_hint(c, promote_numeric(c, left_type, right_type, e.span), hint, e.span)
    }
    return Type_Error{}
}

// When promote_numeric leaves a binary result as an infer type, adopt the
// surrounding expected hint so e.type_ carries concrete signedness/width to
// codegen. Without this, `c : u8 = 200 + 100` would type-check as Type_Infer_Int
// and codegen would default to signed arithmetic — wrong overflow semantics.
// If the infer carries a binding cell (a `:=` local or a deferred default param),
// PIN the cell to the hint as well — otherwise the binding stays open and later
// solidifies to i64, disagreeing with the width the hint forced here (for a param
// that surfaced as a signature-i64-vs-body-i32 mismatch → bad IR). The pin mirrors
// coerce_deferred at a direct decl/arg/return; this is that site reached through
// arithmetic.
coerce_infer_to_hint :: proc(c: ^Checker, t, hint: Type, span: Span) -> Type {
    if _, ok := t.(Type_Infer_Int); ok {
        if n, n_ok := distinct_base(hint).(Type_Numeric); n_ok && n.kind != .Float {
            if cell := infer_cell_of(t); cell != nil { unify_infer_concrete(c, cell, hint, span) }
            return hint
        }
    }
    if _, ok := t.(Type_Infer_Float); ok {
        if n, n_ok := distinct_base(hint).(Type_Numeric); n_ok && n.kind == .Float {
            if cell := infer_cell_of(t); cell != nil { unify_infer_concrete(c, cell, hint, span) }
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
    for i in 0..<len(call_args(e)) {
        param_idx := i + param_offset
        if param_idx >= len(fun_type.params) { break }
        ident, id_ok := call_args(e)[i].(^Expr_Ident)
        if !id_ok || ident.name != "_" { continue }
        def := fun_type.params[param_idx].default_value
        if def == nil {
            check_error(c, e.span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER,
                i + 1, display_name, fun_type.params[param_idx].name)
            continue
        }
        // Compiler intrinsic defaults need a fresh node with the call site's span.
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            call_args_mut(e)[i] = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = ident.span,
            })
        } else {
            call_args_mut(e)[i] = def
        }
    }
}

// Fill in default args for a call that has fewer args than params.
// The scope a callable's signature — including its default-argument values —
// resolves in: the callable's DEFINING scope (its parent_scope, the file scope
// where its `use` imports live). The module scope alone is too high — imports sit
// on the file, a child of the module — so a default referencing an imported
// constant wouldn't resolve there. Falls back to the module scope.
callee_def_scope :: proc(fun_type: ^Type_Scope) -> ^Type_Scope {
    if fun_type == nil { return nil }
    if fun_type.parent_scope != nil { return fun_type.parent_scope }
    return module_scope(fun_type)
}

// Creates fresh intrinsic nodes resolved at the call site.
fill_default_args :: proc(c: ^Checker, e: ^Expr_Call, fun_type: ^Type_Scope, env: ^Type_Scope) {
    // The defaults are appended unchecked: check_call_args checks each argument
    // once, a default in its callee's defining scope — it belongs to the
    // function's DEFINITION, so its names resolve there, not in the caller's
    // `env` (a default naming a module const would bind to whatever the caller
    // has under that name).
    for i := len(call_args(e)); i < len(fun_type.params); i += 1 {
        def := fun_type.params[i].default_value
        if def == nil { continue }
        // Compiler intrinsic defaults (#caller_name / #caller_span) are the one
        // exception: they resolve to CALL-SITE info, so they get a fresh node
        // (checked in the caller's env: it is no default_value).
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            fresh := new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = e.span,
            })
            append(call_args_mut(e), Expr(fresh))
            continue
        }
        // A regular default: the node shared by every call site.
        append(call_args_mut(e), def)
    }
}

// Render a callable's parameter list for diagnostics: "name: Type, name2: Type2"
// (type alone for an unnamed param; "" for a zero-param callable). Lets a
// wrong-arg-count error show what the call actually expects.
fn_params_desc :: proc(ft: ^Type_Scope) -> string {
    b := strings.builder_make()
    for p, i in ft.params {
        if i > 0 { strings.write_string(&b, ", ") }
        if p.name != "" {
            strings.write_string(&b, p.name)
            strings.write_string(&b, ": ")
        }
        strings.write_string(&b, type_name(p.type_))
    }
    return strings.to_string(b)
}

// An argument's type: checked — unless it is a method call's receiver, which
// was checked to find its method (one check per node).
check_call_arg :: proc(c: ^Checker, arg: Expr, env: ^Type_Scope, sig: ^Type_Scope = nil, param := -1, span := Span{}) -> Type {
    if c.receiver != nil && arg == c.receiver {
        // (Built where it was checked, to find its method: its value here.)
        if fc := c.call; fc != nil && fusing(c) != nil {
            pt: Type = sig.params[param].type_ if sig != nil && param >= 0 && param < len(sig.params) else nil
            if !c.receiver_fused.ok {
                fuse_fail(c, "a receiver unbuilt")
            } else if !fc.params {
                // A builtin's: as its other arguments are (a value, read —
                // the first argument, right after its place).
                r := c.receiver_fused
                if fc.want == .Value && r.place { r = Fused{v = fuse_value(c, r, arg, c.receiver_type), ok = true} }
                append(&fc.args, r)
                append(&fc.types, c.receiver_type)
            } else {
                append(&fc.ops, fuse_value_as(c, arg, c.receiver_type, c.receiver_fused, pt, span, {sig = sig, param = param}))
            }
        }
        return c.receiver_type
    }
    // A built call's (fusing): its value, at its param's type.
    fc := c.call
    if fc == nil || fusing(c) == nil { return check_expr(c, arg, env) }
    c.call = nil
    defer c.call = fc
    if !fc.params {
        t, r := fuse_expr(c, arg, env, fc.want, fc.w, temp_span = fc.span)
        append(&fc.args, r)
        append(&fc.types, t)
        return t
    }
    pt: Type
    w := fc.w
    if sig != nil && param >= 0 && param < len(sig.params) {
        pt = sig.params[param].type_
        if arg == sig.params[param].default_value { w = .Implied }   // run at the call, not written there
    }
    use, at := fuse_use_type(arg, pt, span)
    // (A temporary its value may need, before it: an array's a slice param views.)
    held: Graph_Later
    if _, to_slice := distinct_base(pt).(^Type_Slice); to_slice { held = graph_fuse_later(fusing(c)) }
    t, r := fuse_expr(c, arg, env, .Either, w, dest = use, temp_span = at)
    append(&fc.ops, fuse_value_as(c, arg, t, r, pt, span, {sig = sig, param = param}, &held))
    return t
}

// A builtin, built (graph_builtin): its operands, then its operation.
fuse_builtin :: proc(c: ^Checker, e: ^Expr_Call, fc: ^Fuse_Call, t: Type, want: Fuse_Want) {
    defer {
        delete(fc.args)
        delete(fc.types)
    }
    b := fusing(c)
    if b == nil { return }
    if want == .Place {
        fuse_fail(c, "a builtin's place")
        return
    }
    vals := make([]Operand, len(fc.args), context.temp_allocator)
    for r, i in fc.args { vals[i] = r.v }
    name := call_name(e)
    if _, is_cast := cast_result_type(name); is_cast {
        fuse_done(c, graph_op_value(b, .Cast, fc.w, e.span, t, name, ..vals))
        return
    }
    switch name {
    case "print", "print_cstr", "print_float", "print_int", "crash":
        graph_op(b, .Crash if name == "crash" else .Print, fc.w, e.span, nil, name, ..vals)
        fuse_done(c, NO_VALUE)
    case "len", "cap":
        // A fixed array's is its size: its operand, built, is left out.
        if len(fc.args) != 1 { return }
        at := fc.types[0]
        if fa, fixed := distinct_base(graph_pointee(at)).(^Type_Fixed_Array); fixed {
            graph_fuse_drop_since(b, fc.mark)
            fuse_done(c, graph_const(b, fc.w, e.span, t, name, Const_Value{int = i128(fa.size)}))
            return
        }
        if !fc.args[0].place {
            fuse_fail(c, "the length of a value")
            return
        }
        base := fc.args[0].v
        if _, is_self := call_args(e)[0].(^Expr_Self); !is_self {
            if pt, is_ptr := distinct_base(at).(^Type_Ptr); is_ptr {
                base = graph_op_value(b, .Deref, .Implied, e.span, pt.elem, "", base)
            }
        }
        field := graph_op_value(b, .Field, fc.w, e.span, t, name, base)
        fuse_done(c, graph_read(b, field, t, e.span))
    case "int", "uint", "isize", "usize", "bool", "cstring":
        fuse_done(c, graph_op_value(b, .Cast, fc.w, e.span, t, name, ..vals))
    case "slice_from_ptr":
        fuse_done(c, graph_op_value(b, .Slice, fc.w, e.span, t, name, ..vals))
    case:
        fuse_fail(c, fmt.aprintf("the builtin %s", name))
    }
}

// Shared helper: check that args match a function's parameter types.
check_call_args :: proc(c: ^Checker, args: []Expr, fun_type: ^Type_Scope, display_name: string, span: Span, env: ^Type_Scope) {
    required := count_required_params(fun_type)
    if len(args) < required || len(args) > len(fun_type.params) {
        // Show the module-qualified name + the expected parameter list, so the
        // error says which `init` (etc.) this is and what it actually wants.
        qualified := display_name
        if fun_type.home_package != "" {
            qualified = fmt.tprintf("%s.%s", fun_type.home_package, display_name)
        }
        check_error(c, span, TYPE_EXPECTS_ARGS,
            qualified, len(fun_type.params), fn_params_desc(fun_type), len(args))
    } else {
        for arg, i in args {
            // Hand the parameter type down so bare variant idents like
            // `Init(Video)` can resolve `Video` against `Init_Flags`.
            c.expected_hint = fun_type.params[i].type_
            // A filled-in default arg is the SAME node as the param's default
            // expression (fill_default_args appends it). It was written in the
            // callee's module, so resolve it there — resolving in the caller's
            // `env` would bind a `= COLOR_GREEN` default to whatever the CALLER
            // has under that name (the wrong const on a collision).
            arg_env := env
            if arg == fun_type.params[i].default_value {
                if ms := callee_def_scope(fun_type); ms != nil { arg_env = ms }
            }
            arg_type := check_call_arg(c, arg, arg_env, fun_type, i, span)
            // Byte-buffer reinterpret-read at the call boundary: a param
            // typed `[N]T` accepts `buf[off]` or `buf[lo:hi]` from a byte
            // buffer — same shape as `arr : [N]T = buf[off]` at decl sites.
            // The size is in the param type; codegen materializes the
            // fixed-array value via alloca + memcpy + load.
            is_byte_reinterpret := false
            if _, fa_ok := fun_type.params[i].type_.(^Type_Fixed_Array); fa_ok {
                _, sl_ok := arg.(^Expr_Slice)
                if is_byte_buffer_index_read(arg) || sl_ok && is_byte_buffer(arg_type) {
                    is_byte_reinterpret = check_byte_flow(c, fun_type.params[i].type_, arg, arg_type, span) == .Read
                }
            }
            // `cstring` params take literals free (rodata carries the \0)
            // and explicit `cstring(s)` constructions — but NOT runtime
            // strings implicitly: the copy and terminator write should be
            // visible at the call site. Const idents inlining a literal
            // pass like the literal they are.
            if is_cstring(fun_type.params[i].type_) && !is_cstring(arg_type) {
                arg_is_literal := false
                if _, lit_ok := arg.(^Expr_String); lit_ok { arg_is_literal = true }
                if id, id_ok := arg.(^Expr_Ident); id_ok {
                    if cexpr, found := c.table.constants[id.name]; found {
                        if _, s_ok := cexpr.(^Expr_String); s_ok { arg_is_literal = true }
                    }
                }
                if !arg_is_literal {
                    check_error(c, span, TYPE_CSTRING_ARG_EXPLICIT)
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
// Flatten a pure name path to a dotted string: an Ident ("Outer") or a
// Field_Access chain of names ("Outer.Inner.Deep"). Returns "" the moment a
// segment isn't a plain name (a call/index in the chain) — those are value
// expressions, not type paths.
flatten_name_path :: proc(e: Expr) -> string {
    #partial switch v in e {
    case ^Expr_Ident:
        return v.name
    case ^Expr_Field_Access:
        base := flatten_name_path(v.expr)
        if base == "" { return "" }
        return strings.concatenate({base, ".", v.field})
    }
    return ""
}

// Resolve a nested-type-path qualifier (`Outer.Inner`, parsed as a Field_Access
// chain) to the named type's scope body by walking the nested `types` maps.
// Pure name paths only; returns nil for value paths / unknown names so the
// caller falls through to value-qualified resolution. Never emits diagnostics —
// it's a speculative lookup.
resolve_type_path_scope :: proc(c: ^Checker, qualifier: Expr, env: ^Type_Scope) -> ^Scope_Body {
    path := flatten_name_path(qualifier)
    if path == "" { return nil }
    segs := strings.split(path, ".")
    defer delete(segs)
    if len(segs) == 0 { return nil }
    // Root segment: a type in the lexical env, else a module-level type.
    cur_sd: ^Scope_Body
    if root_t, ok := type_env_get(env, segs[0]); ok {
        cur_sd = as_scope_body(root_t)
    }
    if cur_sd == nil {
        flat := resolve_type_name(c, segs[0], "", env)
        if ss, sok := c.table.structs[flat]; sok {
            cur_sd = &ss.sd
        } else if sf, fok := c.table.funs[flat]; fok {
            cur_sd = &sf.sd
        }
    }
    if cur_sd == nil { return nil }
    // Walk the remaining segments through nested types.
    for i in 1..<len(segs) {
        t, found := cur_sd.types[segs[i]]
        if !found { return nil }
        next := as_scope_body(t)
        if next == nil { return nil }
        cur_sd = next
    }
    return cur_sd
}

resolve_qualified_call :: proc(
    c: ^Checker, e: ^Expr_Call, env: ^Type_Scope, check_args: ^[dynamic]Expr,
) -> (resolution: Maybe(Resolved_Func), fn_type: ^Type_Scope, qual_dispatch_fns: [dynamic]string, error: bool) {
    resolved_assoc := false

    // Type-qualified call (TypeName.method or mod.func) — check before
    // check_expr to avoid "type is not a value" errors.
    if ident, ok := call_qualifier(e).(^Expr_Ident); ok {
        qual_type, qual_found := type_env_get(env, ident.name)
        if qual_found {
            if qual_sd := as_scope_body(qual_type); qual_sd != nil {
                if fn, found := qual_sd.functions[call_name(e)]; found && fn != nil {
                    fn_type = fn
                    resolution = Resolved_Func{name = fn.name}
                    e.lowered_name = fn.name

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

                    if !is_type_qualifier && !sd_is_module(qual_sd) {
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
                                    call_name(e), qual_sd.name)
                                e.qualifier_folded = true
                                return nil, nil, nil, true
                            }
                            new_args: [dynamic]Expr
                            append(&new_args, call_qualifier(e))
                            for a in call_args(e) { append(&new_args, a) }
                            call_args_mut(e)^ = new_args
                        }
                    }

                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    resolved_assoc = true
                } else if t, found := qual_sd.types[call_name(e)]; found {
                    flat := type_flat_name(t)
                    resolution = Resolved_Func{name = flat}
                    if ts, ts_ok := t.(^Type_Scope); ts_ok { fn_type = ts }
                    e.lowered_name = flat
                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    resolved_assoc = true
                } else if fns, found := qual_sd.dispatch_groups[call_name(e)]; found {
                    // Qualified dispatch (e.g. `m.sqrt(x)`): pick from this
                    // module's dispatch candidates only — don't merge with
                    // the includer's other visible dispatches of the same name.
                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    qual_dispatch_fns = fns
                    resolved_assoc = true
                } else if sd_is_module(qual_sd) {
                    check_error(c, e.span, TYPE_MODULE_FUNCTION, qual_sd.name, call_name(e))
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
                if fn, found := assoc_sd.functions[call_name(e)]; found && fn != nil {
                    fn_type = fn
                    resolution = Resolved_Func{name = fn.name}
                    e.lowered_name = fn.name
                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    resolved_assoc = true
                }
            }
        }
    }
    // Nested-type-path qualifier: `Outer.Inner.Ctor(args)` parses with the
    // qualifier as a Field_Access chain (Outer.Inner), which the bare-ident
    // branch above can't see. Resolve the chain to its type scope and look up
    // e.name as a nested type (construction) or associated function — the same
    // resolution the ident branch does, one or more levels deeper. Runs before
    // the value-qualified path below so a real type path isn't mis-checked as a
    // field access; a value path resolves to nil here and falls through.
    if !resolved_assoc {
        if _, is_fa := call_qualifier(e).(^Expr_Field_Access); is_fa {
            if qual_sd := resolve_type_path_scope(c, call_qualifier(e), env); qual_sd != nil {
                if t, found := qual_sd.types[call_name(e)]; found {
                    flat := type_flat_name(t)
                    resolution = Resolved_Func{name = flat}
                    if ts, ts_ok := t.(^Type_Scope); ts_ok { fn_type = ts }
                    e.lowered_name = flat
                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    resolved_assoc = true
                } else if fn, found := qual_sd.functions[call_name(e)]; found && fn != nil {
                    fn_type = fn
                    resolution = Resolved_Func{name = fn.name}
                    e.lowered_name = fn.name
                    e.qualifier_folded = true
                    for a in call_args(e) { append(check_args, a) }
                    resolved_assoc = true
                }
            }
        }
    }
    // Value-qualified call (obj.method) — type-check qualifier to find struct type.
    if !resolved_assoc {
        qual_type: Type
        if w, building := c.receiver_want.?; building {
            qual_type, c.receiver_fused = fuse_expr(c, call_qualifier(e), env, .Either, w)
        } else {
            qual_type = check_expr(c, call_qualifier(e), env)
        }
        c.receiver, c.receiver_type = call_qualifier(e), qual_type
        if assoc_st := resolve_to_struct_type(c, qual_type); assoc_st != nil {
            if fn, found := assoc_st.functions[call_name(e)]; found && fn != nil {
                fn_type = fn
                resolution = Resolved_Func{name = fn.name}
                e.lowered_name = fn.name

                // Instance method detection: a method whose first param is the owning
                // struct (Self) or a pointer to it (^Self) is an instance method, and
                // the qualifier should be prepended as the receiver. Static methods
                // (no params, or first param of a different type) leave args alone.
                first_param_is_self := false
                first_param_wants_ptr := false
                // (Its signature, resolved on demand: a method named before
                // any call resolved it — a generic struct instance's.)
                if fn.kind == .Fun { ensure_fun_signature(c, fn) }
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
                            call_name(e), assoc_st.name)
                        e.qualifier_folded = true
                        return nil, nil, nil, true
                    }
                    // Prepend qualifier as receiver.
                    new_args: [dynamic]Expr
                    append(&new_args, call_qualifier(e))
                    for a in call_args(e) { append(&new_args, a) }
                    call_args_mut(e)^ = new_args
                }
                e.qualifier_folded = true
                for a in call_args(e) { append(check_args, a) }
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
        if t, found := type_env_get(env, call_name(e)); found {
            if ts, ok := t.(^Type_Scope); ok && ts.kind == .Fun && ts.name != "" {
                ufcs_flat = ts.name
            }
        }
        if ufcs_flat == "" {
            ufcs_flat = make_flat_name(resolve_fn_home(c, env, call_name(e)), call_name(e))
        }
        resolution = Resolved_Func{name = ufcs_flat}
        new_args: [dynamic]Expr
        append(&new_args, call_qualifier(e))
        for a in call_args(e) { append(&new_args, a) }
        call_args_mut(e)^ = new_args
        e.qualifier_folded = true
        for a in call_args(e) { append(check_args, a) }
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
check_dispatch_call :: proc(c: ^Checker, e: ^Expr_Call, fn_names: [dynamic]string, check_args: []Expr, env: ^Type_Scope, want := Fuse_Want.None, w := Written.Explicit) -> Type {
    // Built: each argument as it is checked, at its param's type once the
    // function is chosen; the defaults the call leaves out; then the call.
    b := fusing(c) if want != .None else nil
    if b != nil && want == .Place {
        fuse_fail(c, "a call's place")
        b = nil
    }
    vals: [dynamic]Operand
    defer delete(vals)
    as_: [dynamic]int
    defer delete(as_)
    array_values: [dynamic]bool   // (an argument that is an array's value, no place)
    defer delete(array_values)
    literal_args: [dynamic]Fuse_Literal_Arg
    defer delete(literal_args)
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

    // (A `_`'s default, checked once the function is chosen, is built
    // where the `_` is: graph_fuse_later.)
    laters := make([]Graph_Later, len(check_args), context.temp_allocator)
    arg_types: [dynamic]Type
    defer delete(arg_types)
    for arg, i in check_args {
        if is_underscore[i] {
            append(&arg_types, nil)
            if b != nil && fusing(c) != nil {
                laters[i] = graph_fuse_later(b)
                append(&vals, NO_VALUE)
                append(&as_, -1)
                append(&array_values, false)
            }
        } else if b != nil && fusing(c) != nil {
            from := b.nodes
            t, r := fuse_expr(c, arg, env, .Either, w)
            append(&arg_types, t)
            if fusing(c) == nil { continue }
            _, is_literal := arg.(^Expr_Array)
            _, is_array := distinct_base(t).(^Type_Fixed_Array)
            sl, is_slice := arg.(^Expr_Slice)
            if fuse_byte_index(arg) || is_slice && is_byte_buffer(expr_type(sl.expr)) {
                fuse_fail(c, "bytes as a dispatch's argument")
                continue
            }
            v, k := graph_fuse_as(b, r.v, r.place, t, expr_span(arg)^, e.span, {})
            append(&vals, v)
            append(&as_, k)
            append(&array_values, is_array && !r.place)
            // (An array literal: built at its own type, retyped as its param's
            // once the function is chosen — as the builder built it there.)
            if is_literal { append(&literal_args, Fuse_Literal_Arg{i, from, b.nodes, t}) }
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
            call_name(e), strings.join(type_strs[:], ", "))
        return Type_Error{}
    }

    if len(matched_fns) > 1 {
        // Two or more candidates can serve this call shape — usually because a
        // trailing-default overload overlaps an exact-arity overload. Mara
        // doesn't pick a winner; the user disambiguates by supplying the
        // distinguishing arg explicitly or removing the default.
        check_error(c, e.span, TYPE_AMBIGUOUS_DISPATCH_MATCHES_MULTIPLE_OVERLOADS,
            call_name(e), strings.join(matched_fns[:], ", "))
        return Type_Error{}
    }

    fn_name := matched_fns[0]
    ft := matched_fts[0]

    // Defaults resolve in the callee's defining scope, not the caller's `env`
    // (see fill_default_args). Intrinsic defaults are the exception — they read
    // call-site info, so they stay on `env`.
    callee_scope := callee_def_scope(ft)
    if callee_scope == nil { callee_scope = env }

    // Substitute `_` against the chosen candidate's defaults. Mirrors
    // substitute_underscore_args + fill_default_args' span/intrinsic handling.
    // Re-runs check_expr on the substituted node so codegen sees the resolved
    // type metadata, same as fill_default_args does.
    if has_underscore {
        for i in 0..<len(call_args(e)) {
            if !is_underscore[i] { continue }
            def := ft.params[i].default_value
            new_arg: Expr
            arg_scope := callee_scope
            if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
                span := e.span
                if ident, id_ok := call_args(e)[i].(^Expr_Ident); id_ok {
                    span = ident.span
                }
                new_arg = new_clone(Expr_Compiler_Intrinsic{
                    kind = intr.kind,
                    span = span,
                })
                arg_scope = env
            } else {
                new_arg = def
            }
            if fusing(c) != nil && b != nil {
                graph_fuse_later_begin(b, &laters[i])
                aw := Written.Implied if new_arg == def else w   // (run at the call, not written there)
                t, r := fuse_expr(c, new_arg, arg_scope, .Either, aw)
                if fusing(c) != nil { vals[i] = fuse_value_as(c, new_arg, t, r, ft.params[i].type_, e.span, {sig = ft, param = i}) }
                if !graph_fuse_later_end(b, &laters[i]) { fuse_fail(c, "a default for `_` across runs") }
            } else {
                check_expr(c, new_arg, arg_scope)
            }
            call_args_mut(e)[i] = new_arg
        }
    }

    if b := fusing(c); b != nil && b == c.gb {
        for k, i in as_ {
            if k >= 0 { b.fuse.widens[k].sig, b.fuse.widens[k].param = ft, i }
        }
        if fuse_views_value(ft, array_values[:]) { fuse_fail(c, "an array's value viewed by a dispatch's param") }
        for la in literal_args {
            if la.arg >= len(ft.params) { continue }
            pt := ft.params[la.arg].type_
            if graph_aggregate(pt) && pt != la.t { graph_fuse_retype_literal(b, la.from, la.to, pt) }
        }
    }
    // Trailing default fill: append each missing slot's default expression so
    // codegen sees a fully-saturated arg list. Mirrors fill_default_args.
    for i := len(call_args(e)); i < len(ft.params); i += 1 {
        def := ft.params[i].default_value
        new_arg: Expr
        arg_scope := callee_scope
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            new_arg = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = e.span,
            })
            arg_scope = env
        } else {
            new_arg = def
        }
        if fusing(c) != nil && b != nil {
            aw := Written.Implied if new_arg == def else w   // (run at the call, not written there)
            t, r := fuse_expr(c, new_arg, arg_scope, .Either, aw)
            append(&vals, fuse_value_as(c, new_arg, t, r, ft.params[i].type_, e.span, {sig = ft, param = i}))
        } else {
            check_expr(c, new_arg, arg_scope)
        }
        append(call_args_mut(e), new_arg)
    }

    disp_flat := make_flat_name(resolve_fn_home(c, env, fn_name), fn_name)
    e.lowered_name = fn_name  // rewrite call target for codegen
    e.resolved_func = Resolved_Func{name = disp_flat, callee = ft}
    if fb := fusing(c); fb != nil && b != nil {
        fuse_done(c, {graph_call_op(fb, .Call, w, e.span, ft, fn_primary_return(ft), ..vals[:]), 0})
    }
    return fn_primary_return(ft)
}

// `?` postfix propagation. Validates that the inner expression produces an
// err-compatible trailing slot AND that the enclosing function has an
// err-compatible trailing return slot to bubble into. The Expr_Try's value
// type is the inner return list minus the trailing err — void for err-only
// calls, the single value for `(T, err)` calls. Multi-value calls (`(T, U,
// err)`) aren't supported yet since Mara doesn't have true value tuples; the
// flat err-set design is what the user signed up for and that's covered.
check_try :: proc(c: ^Checker, e: ^Expr_Try, env: ^Type_Scope) -> Type {
    // Built: the call's value, then the branch on its err (graph_try_after).
    want, w := fuse_asked(c)
    if want == .Place { fuse_fail(c, "a `?`'s place") }
    inner_t: Type
    inner: Fused
    if want != .None && want != .Place {
        inner_t, inner = fuse_expr(c, e.inner, env, .Value, w)
    } else {
        inner_t = check_expr(c, e.inner, env)
    }
    _ = inner_t
    defer if b := fusing(c); b != nil && want != .None && want != .Place && inner.ok { fuse_done(c, graph_try_after(b, e, inner.v)) }

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
    rts := enclosing_return_types(env)
    if len(rts) == 0 || !is_err_type(rts[len(rts)-1]) {
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

check_call :: proc(c: ^Checker, e: ^Expr_Call, env: ^Type_Scope) -> Type {
    // Built (fusing): its arguments' values as they are checked, then it (a
    // construction: into where it goes, or a temporary).
    want, w := fuse_asked(c)
    dest, into_temp, temp_span := c.asked_dest, c.asked_temp, c.asked_span
    // Its place (graph_place's): a temporary made first, the call stored in
    // it — built there, a construction — at the use's span.
    place_slot := NO_NODE
    if b := fusing(c); b != nil && want == .Place {
        if temp_span == {} { temp_span = e.span }
        place_slot = graph_slot(b, "temp", nil, temp_span)
        want, dest = .Into, graph_dest_var("temp", place_slot, nil)
    }
    defer if b := fusing(c); b != nil && place_slot != NO_NODE {
        r := c.fused
        t := e.type_ if e.type_ != nil else fn_primary_return(e.resolved_func.?.callee) if e.resolved_func != nil && e.resolved_func.?.callee != nil else nil
        if !r.ok {
            fuse_fail(c, "a call's place")
        } else {
            if !r.into { graph_fuse_write_at(b, graph_var(b, "temp", place_slot, nil, temp_span), r.v, temp_span) }
            graph_fuse_typed(b, place_slot, t)
            fuse_done(c, graph_var(b, "temp", place_slot, t, temp_span), true)
        }
    }
    fc := Fuse_Call{w = w}
    defer delete(fc.ops)
    saved_call := c.call
    c.call = nil
    defer c.call = saved_call
    saved_receiver, saved_receiver_type, saved_receiver_fused := c.receiver, c.receiver_type, c.receiver_fused
    c.receiver, c.receiver_type, c.receiver_fused = nil, nil, {}
    defer c.receiver, c.receiver_type, c.receiver_fused = saved_receiver, saved_receiver_type, saved_receiver_fused
    // A call that returns multiple values has nowhere to put the extras when
    // used as a single argument — codegen would silently keep only the first.
    // Reject it here (every call form funnels through check_call) so the user
    // destructures first. Valid multi-return positions (`a, b := f()`, `f()?`,
    // struct-literal fields) don't pass the call through `e.args`, so they're
    // unaffected. call_return_list returns >0 only for ^Expr_Call, so the arg
    // is safely an ^Expr_Call when the count exceeds one.
    for arg in call_args(e) {
        if returns := call_return_list(c, arg, env); len(returns) > 1 {
            check_error(c, arg.(^Expr_Call).span, TYPE_MULTI_RETURN_AS_ARG, len(returns))
        }
    }

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
    if call_qualifier(e) != nil {
        // (Built: a receiver is the first argument, built where it is
        // checked; a qualifier that names a type or a module builds none.)
        mark: Graph_Mark
        if b := fusing(c); b != nil && want != .None {
            mark = graph_fuse_mark(b)
            c.receiver_want = w
        }
        res, ft, qfns, err := resolve_qualified_call(c, e, env, &check_args)
        c.receiver_want = nil
        if b := fusing(c); b != nil && want != .None && c.receiver_fused.ok {
            if len(check_args) == 0 || check_args[0] != c.receiver { graph_fuse_drop_since(b, mark) }
        }
        if err { return Type_Error{} }
        resolution = res
        qual_fn_type = ft
        qual_dispatch_fns = qfns
    } else {
        for a in call_args(e) { append(&check_args, a) }
    }

    // Phase 2: Check the call — builtins, then user-defined functions.
    if b := fusing(c); b != nil && want != .None {
        c.call = &fc
        // (len and cap take their operand's place: held, when it has none.)
        fc.want = .Place if call_name(e) == "len" || call_name(e) == "cap" else .Value
        fc.span = e.span
        fc.mark = graph_fuse_mark(b)
    }
    builtin_result, is_builtin := check_builtin_call(c, e, check_args[:], env)
    c.call = nil
    if is_builtin {
        if want != .None { fuse_builtin(c, e, &fc, builtin_result, want) }
        return builtin_result
    }

    // Qualified dispatch (e.g. `m.sqrt(x)`): resolve_qualified_call set
    // qual_dispatch_fns to the qualified module's candidates (only).
    if len(qual_dispatch_fns) > 0 {
        return check_dispatch_call(c, e, qual_dispatch_fns, check_args[:], env, want, w)
    }

    // Dispatch group resolution: mul(a,b) -> mat4_mul(a,b)
    // Only fires for unqualified calls — qualified resolution already picked
    // a specific function.
    if qual_fn_type == nil {
        if fn_names, is_dispatch := find_dispatch(c, env, call_name(e)); is_dispatch {
            return check_dispatch_call(c, e, fn_names, check_args[:], env, want, w)
        }

        // Generic function instantiation. A clone of a checked call (a
        // broadcast's slots) carries the instance name as its lowered name,
        // which is no declared function: find the template by the source name.
        gtmpl, gtmpl_ok := &c.table.generic_templates[call_name(e)]
        if !gtmpl_ok { gtmpl, gtmpl_ok = &c.table.generic_templates[e.name] }
        if gtmpl_ok {
            return check_generic_call(c, e, gtmpl, check_args[:], env, want, w)
        }
    }

    fun_type: ^Type_Scope
    fun_ok: bool
    if qual_fn_type != nil {
        fun_type = qual_fn_type
        fun_ok = true
    } else {
        fun_type_raw, ok := type_env_get(env, call_name(e))
        if !ok {
            check_error(c, e.span, TYPE_UNDEFINED_FUNCTION, call_name(e))
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
                check_error(c, e.span, TYPE_EXPECTS_ARGUMENT_3, call_name(e), len(check_args))
                return Type_Error{}
            }
            saved_hint := c.expected_hint
            c.expected_hint = dt.base_type
            // Built: the argument's value, then the conversion.
            arg_type: Type
            arg: Fused
            if want != .None && want != .Place {
                arg_type, arg = fuse_expr(c, check_args[0], env, .Value, w)
            } else {
                if want == .Place { fuse_fail(c, "a conversion's place") }
                arg_type = check_expr(c, check_args[0], env)
            }
            c.expected_hint = saved_hint
            if b := fusing(c); b != nil && want != .None && want != .Place {
                fuse_done(c, graph_op_value(b, .Cast, w, e.span, dt, call_name(e), arg.v))
            }
            if !is_any(arg_type) && !is_infer(arg_type) {
                if types_incompatible(dt.base_type, arg_type) {
                    check_error(c, e.span,
                        TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE,
                        call_name(e), type_name(arg_type), type_name(dt.base_type))
                }
            }
            e.type_ = dt
            e.resolved_func = Resolved_Func{name = dt.name}
            return dt
        }

        fun_type, fun_ok = fun_type_raw.(^Type_Scope)
        if !fun_ok {
            check_error(c, e.span, TYPE_FUNCTION, call_name(e))
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
        if call_name(e) in c.declared_funs && fun_type.name != "" {
            home, home_ok, ambiguous_owners := resolve_fn_home_with_ambiguity(c, env, call_name(e))
            if !home_ok && len(ambiguous_owners) > 1 {
                owner_list := strings.join(ambiguous_owners[:], ", ")
                check_error(c, e.span, TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED, call_name(e), owner_list, ambiguous_owners[0], call_name(e))
                return Type_Error{}
            }
            flat := make_flat_name(home, call_name(e))
            resolution = Resolved_Func{name = flat}
        } else if fun_type.name != "" && fun_type.name in c.declared_funs {
            // Bare name resolved via scope (e.g. sibling function in data fun body)
            resolution = Resolved_Func{name = fun_type.name}
        }
    }

    // Single write: record resolution for codegen. fun_type is the resolved
    // callee for every path that reaches here (qualified: paired with resolution
    // by resolve_qualified_call; unqualified: the same env lookup resolution was
    // built from), so attach it as the callee pointer. Dispatch/generic paths
    // return earlier and set their own resolved_func.
    if res, res_ok := resolution.?; res_ok {
        res.callee = fun_type
        e.resolved_func = res
    } else {
        e.fn_value = fun_type // an indirect call through a function value
    }

    // Pure data struct construction: args map directly to fields.
    // Fires for struct-like scopes (kind=.Struct) with no constructor params.
    // Codegen can skip the call overhead and write fields directly to memory.
    // Covers old Type_Struct usages plus classes declared with empty parens
    // `class Foo() { x: int }`, and fieldless structs (`Foo()` → zero-size value).
    if fun_type.kind == .Struct {
        ensure_struct_signature(c, &fun_type.sd)  // resolve fields on demand before construction
    } else if fun_type.kind == .Fun {
        ensure_fun_signature(c, fun_type)  // resolve params/returns on demand before arg matching
    }
    // Pure-data and parameterized constructors share ONE construction path: args
    // bind to the constructor's PARAMS (a pure-data struct has none, so `Point()`
    // is the only positional form — `Point(x, y)` fails arg-count below; field
    // values go in the brace override block, `Point(){ x = 1, y = 2 }`). A
    // pure-data struct is just a 0-param constructor whose body codegen skips.

    // `_` at any positional arg means "use the parameter's default value here."
    // Substitute before filling tail defaults so the two mechanisms compose
    // (caller wrote some args, asked for defaults at specific slots, omitted
    // trailing args that fall back to defaults via fill_default_args).
    param_offset := len(check_args) - len(call_args(e))
    substitute_underscore_args(c, e, fun_type, param_offset, call_name(e))
    for i in 0..<len(call_args(e)) {
        check_args[i + param_offset] = call_args(e)[i]
    }

    // Args map to params
    if len(check_args) < len(fun_type.params) && has_param_defaults(fun_type) {
        fill_default_args(c, e, fun_type, env)
        clear(&check_args)
        for a in call_args(e) { append(&check_args, a) }
    }

    fc.params = true
    // (A pure-data struct reaches here as a value — its resolution is set
    // below: it is a construction.)
    if want != .None && (fun_type.kind == .Fun || fun_type.kind == .Struct) { c.call = &fc }
    // (Built into storage that holds a value: a temporary made before the
    // arguments.)
    if b := fusing(c); b != nil && c.call != nil && want == .Into && into_temp && fun_type.kind == .Struct {
        dest = graph_fuse_temp(b, temp_span, fuse_temp_type(dest))
    }
    // (A fixed array its destination views as a slice: held in a temporary
    // made before the arguments, at the store's span — its place, sliced
    // there — graph_view's.)
    view_slot := NO_NODE
    ret := fn_primary_return(fun_type) if fun_type.kind == .Fun else nil
    if b := fusing(c); b != nil && c.call != nil && want == .Into && e.fn_value == nil && ret != nil {
        _, to_slice := distinct_base(graph_dest_type(b, dest)).(^Type_Slice)
        _, from_array := distinct_base(ret).(^Type_Fixed_Array)
        if to_slice && from_array { view_slot = graph_slot(b, "temp", ret, temp_span) }
    }
    check_call_args(c, check_args[:], fun_type, call_name(e), e.span, env)
    construct: ^Graph_Literal
    construct_at: Dest
    if c.call != nil {
        c.call = nil
        if b := fusing(c); b != nil {
            if want == .Place {
                fuse_fail(c, "a call's place")
            } else if fun_type.kind == .Struct {
                construct_at = dest if want == .Into else graph_dest_var("temp", graph_slot(b, "temp", fun_type, e.span), fun_type)
                construct = graph_fuse_construct(b, fun_type, fun_type, construct_at, fc.ops[:], w, e.span)
            } else if e.fn_value != nil {
                // Through a function value: it, read, is the first operand.
                fuse_done(c, graph_fuse_indirect(b, call_name(e), e.fn_value, fn_primary_return(fun_type), fc.ops[:], w, e.span))
            } else if view_slot != NO_NODE {
                v := Operand{graph_call_op(b, .Call, w, e.span, fun_type, ret, ..fc.ops[:]), 0}
                graph_fuse_write_at(b, graph_var(b, "temp", view_slot, ret, temp_span), v, temp_span)
                fuse_done(c, graph_var(b, "temp", view_slot, ret, temp_span), true)
            } else {
                fuse_done(c, {graph_call_op(b, .Call, w, e.span, fun_type, fn_primary_return(fun_type), ..fc.ops[:]), 0})
            }
        }
    }

    // Any struct construction: the call's value IS the struct itself (Self) —
    // pure-data (0 params, args already rejected above) and parameterized alike.
    // A fallible constructor also declares a trailing err — exposed to `?` and
    // `t, e := ...` via constructor_effective_returns / call_return_list; in plain
    // scalar context the result type is still Self. Brace overrides set fields.
    if fun_type.kind == .Struct {
        e.type_ = fun_type
        // A pure-data struct isn't in declared_funs, so the resolution dance above
        // left resolved_func nil — set it here so codegen sees a construction (its
        // callee is a struct) and zero-inits / runs the init fn, rather than
        // emitting a function call to a name with no body (e.g. a fieldless struct).
        if e.resolved_func == nil && fun_type.name != "" {
            e.resolved_func = Resolved_Func{name = fun_type.name, callee = fun_type}
        }
        if e.overrides != nil {
            // (Built: each override written into what it constructed.)
            ol := Fuse_Lit{e = e.overrides, gl = construct, built = construct != nil}
            saved := c.lit
            if construct != nil { c.lit = &ol }
            check_struct_literal_fields(c, e.overrides, &fun_type.sd, e.span, env, override = true)
            c.lit = saved
        }
        if b := fusing(c); b != nil && construct != nil {
            if want == .Into && into_temp {
                fuse_built(c, b, want, true, true, construct_at, fun_type, temp_span)
            } else if want == .Into {
                fuse_done(c, NO_VALUE, into = true)
            } else {
                fuse_done(c, graph_read(b, graph_dest_place(b, construct_at, e.span), fun_type, e.span))
            }
        }
        return fun_type
    }

    if e.overrides != nil {
        check_error(c, e.span, TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID, call_name(e))
    }
    // Multi-return call in scalar context: caller must destructure via
    // `x, y := f()`. Single-return funs return their one type; void returns nil.
    if fn_has_multi_return(fun_type) {
        return fn_primary_return(fun_type)
    }
    return fn_primary_return(fun_type)
}

// Pure-struct positional construction: a parameterless struct called with
// positional args mapped to fields, plus `_` substitution against field defaults
// (the same surface the parameter-default path gives a function call).
//
// DEPRECATED for direct use — function-call syntax on a no-arg struct, `Point(x, y)`,
// is no longer accepted in source. check_call routes ALL struct construction through
// the one constructor path (args bind to params; a pure-data struct has none), so
// `Point()`, the brace literal `Point{...}`, and the override form `Point(){...}` are
// the only spellings. This procedure now survives SOLELY as the generic-
// monomorphization construction path (check_generic_call — e.g. Array(Player, 64),
// Pair(int)(1, 2)), where the freshly instantiated struct is still built positionally
// post-mono. Unify that path through check_call too and this can be deleted.
check_pure_struct_construction :: proc(c: ^Checker, e: ^Expr_Call, st: ^Type_Scope, env: ^Type_Scope) -> Type {
    ensure_struct_signature(c, &st.sd)  // resolve fields on demand before construction
    e.type_ = st
    if e.resolved_func == nil && st.name != "" {
        e.resolved_func = Resolved_Func{name = st.name, callee = st}
    }

    // `Foo()` (no args) is always valid — equivalent to bare declaration `x : Foo`.
    // Init function applies defaults and zero-inits fields without defaults.
    if len(call_args(e)) == 0 {
        if e.overrides != nil {
            check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env, override = true)
        }
        return st
    }

    // `_` at any positional arg means "use the field's default value here."
    // Mirrors substitute_underscore_args for parameters.
    for i in 0..<len(call_args(e)) {
        if i >= len(st.fields) { break }
        ident, id_ok := call_args(e)[i].(^Expr_Ident)
        if !id_ok || ident.name != "_" { continue }
        def := st.fields[i].default_value
        if def == nil {
            check_error(c, e.span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_FIELD,
                i + 1, st.name, st.fields[i].name)
            continue
        }
        if intr, intr_ok := def.(^Expr_Compiler_Intrinsic); intr_ok {
            call_args_mut(e)[i] = new_clone(Expr_Compiler_Intrinsic{
                kind = intr.kind,
                span = ident.span,
            })
        } else {
            call_args_mut(e)[i] = def
        }
    }

    num_required := 0
    for f in st.fields {
        if f.default_value == nil { num_required += 1 }
    }
    if len(call_args(e)) > len(st.fields) {
        check_error(c, e.span, TYPE_FIELD_ARGUMENT, st.name, len(st.fields), len(call_args(e)))
    } else if len(call_args(e)) < num_required {
        check_error(c, e.span, TYPE_REQUIRES_LEAST_ARGUMENT, st.name, num_required, len(call_args(e)))
    }
    for arg, i in call_args(e) {
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
        check_struct_literal_fields(c, e.overrides, &st.sd, e.span, env, override = true)
    }
    return st
}

// check_module_call removed — module calls now resolve through the unified
// assoc_fn/types path in check_call, same as type-qualified calls.
check_array_literal_impl :: proc(c: ^Checker, e: ^Expr_Array, env: ^Type_Scope, ga: ^Graph_Array) -> Type {
    if len(e.elements) == 0 {
        // Empty array literal — type is unknown until assigned
        return Type_Error{}
    }

    // Infer element type from first element (built: each element into its
    // slot; the first's type is the literal's, when its destination gave
    // none — it can't be built in place before that is known).
    elem_type: Type
    if b := fusing(c); b != nil && ga != nil {
        r: Fused
        if ga.elem_t == nil {
            elem_type, r = fuse_expr(c, e.elements[0], env, .Either)
            lit_t := new_clone(Type_Fixed_Array{size = len(e.elements), elem = elem_type})
            fuse_store_finish(c, e.elements[0], elem_type, r, graph_fuse_array_elem(b, ga, 0, elem_type, lit_t), e.span)
        } else {
            elem_type = fuse_store_into(c, e.elements[0], env, graph_fuse_array_elem(b, ga, 0, nil, nil), e.span)
        }
    } else {
        elem_type = check_expr(c, e.elements[0], env)
    }
    for i := 1; i < len(e.elements); i += 1 {
        et: Type
        if b := fusing(c); b != nil && ga != nil {
            et = fuse_store_into(c, e.elements[i], env, graph_fuse_array_elem(b, ga, i, nil, nil), e.span)
        } else {
            et = check_expr(c, e.elements[i], env)
        }
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

// --- subscript `.len` / `.cap` shorthand ------------------------------------
// Inside a subscript — an `arr[...]` index or `arr[lo:hi]` bound — a bare `.len`
// or `.cap` is shorthand for the base array's own `.len` / `.cap`. The parser
// emits these as dot-idents (the `.Variant` shorthand), so before the index is
// resolved (and fails as an unknown variant) each `.len`/`.cap` dot-ref is
// lowered to a field access on the base — `a.fonts[.len]` reads `a.fonts.len` —
// held in the ident's `lowered` slot, which check_expr and codegen follow.
// Recurses through arithmetic so `[.len - 1]` and `[.len:.cap]` work. Only
// pure-lvalue bases (ident or field-access chains) are lowered, so the base
// cloned into the lowering can't double-evaluate a side effect. Idempotent — a
// dot-ref already lowered keeps its lowering.

subscript_base_is_pure :: proc(e: Expr) -> bool {
    #partial switch n in e {
    case ^Expr_Ident:        return !n.is_dot
    case ^Expr_Field_Access: return subscript_base_is_pure(n.expr)
    }
    return false
}

clone_pure_lvalue :: proc(e: Expr) -> Expr {
    #partial switch n in e {
    case ^Expr_Ident:
        return new_clone(n^)
    case ^Expr_Field_Access:
        return new_clone(Expr_Field_Access{expr = clone_pure_lvalue(n.expr), field = n.field, span = n.span})
    }
    return e
}

lower_subscript_dots :: proc(base: Expr, sub: Expr) {
    if sub == nil || !subscript_base_is_pure(base) { return }
    #partial switch n in sub {
    case ^Expr_Ident:
        if n.is_dot && (n.name == "len" || n.name == "cap") && n.lowered == nil {
            n.lowered = new_clone(Expr_Field_Access{expr = clone_pure_lvalue(base), field = n.name, span = n.span})
        }
    case ^Expr_Binary:
        lower_subscript_dots(base, n.left)
        lower_subscript_dots(base, n.right)
    case ^Expr_Unary:
        lower_subscript_dots(base, n.operand)
    }
}

// An element, built: its collection's place (through a pointer, what it
// points at), the index at the header's width, then the element. (Bytes
// indexed as another type are a view: the builder's.)
Fuse_Index :: struct {
    w:     Written,
    base:  Operand,
    index: Operand,
}

check_index :: proc(c: ^Checker, e: ^Expr_Index, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    b := fusing(c)
    if want == .None || b == nil { return check_index_impl(c, e, env, nil) }
    fi := Fuse_Index{w = w}
    t := check_index_impl(c, e, env, &fi)
    if fusing(c) == nil { return t }
    // (A byte, as it is: a use of it as another type sees the element's
    // place as a view — graph_fuse_view.)
    if _, of_byte := distinct_base(t).(Type_Byte); !of_byte && t != nil && !is_infer(t) && is_byte_buffer(expr_type(e.expr)) {
        fuse_fail(c, "bytes indexed as another type")
        return t
    }
    p := graph_op_value(b, .Index, .Explicit, e.span, t, "", fi.base, fi.index)
    if want == .Value {
        fuse_done(c, graph_read(b, p, t, e.span))
    } else {
        fuse_done(c, p, true)
    }
    return t
}

check_index_impl :: proc(c: ^Checker, e: ^Expr_Index, env: ^Type_Scope, fi: ^Fuse_Index) -> Type {
    lower_subscript_dots(e.expr, e.index)
    base_type: Type
    if fi != nil {
        base: Fused
        base_type, base = fuse_expr(c, e.expr, env, .Place, temp_span = e.span)
        fi.base = base.v
        if b := fusing(c); b != nil {
            if pt, is_ptr := distinct_base(base_type).(^Type_Ptr); is_ptr {
                fi.base = graph_op_value(b, .Deref, .Implied, e.span, pt.elem, "", base.v)
            }
        }
    } else {
        base_type = check_expr(c, e.expr, env)
    }
    target_type := distinct_base(base_type)
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
    idx_type: Type
    if fi != nil {
        at: Fused
        idx_type, at = fuse_expr(c, e.index, env, .Value, .Explicit)
        if b := fusing(c); b != nil { fi.index = fuse_index_value(b, at.v, idx_type, e.span) }
    } else {
        idx_type = check_expr(c, e.index, env)
    }

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
        // array's visible size is fa.size, and a literal/const index
        // folds via evaluate_comptime_int. Lets `s := "hello"; s[5]`
        // be a compile error instead of a runtime trap.
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

// A slice, built: its bounds at the header's width, then its collection's
// place — a plain place, checked first and built after them (as the builder
// walks it) — then the slice.
Fuse_Slice :: struct {
    w:       Written,
    lo, hi:  Operand,
    read_as: Type,      // (asked into a destination, or at a use's type) its type
    reads:   bool,      // bytes read as that type: built as the store takes them
    scalar:  bool,      // … a view of its start (a register value, a use's array): its end unbuilt
    view:    bool,      // asked at a use's type: a read is a view of its start
    base:    Operand,
    held:    bool,        // its base is no plain place: held (fuse_hold), built early
    early:   Graph_Early,
}

// A span of bytes read as its destination's type (graph_store): the bytes'
// place, built first, then its bounds as they are (a register value's start
// only), gathered in a slice the store takes apart (fuse_store_finish).
Fuse_Span_Read :: struct {
    op:     Node_Id,
    scalar: bool,
}

check_slice :: proc(c: ^Checker, e: ^Expr_Slice, env: ^Type_Scope) -> Type {
    want, w := fuse_asked(c)
    b := fusing(c)
    if want == .None || b == nil { return check_slice_impl(c, e, env, nil) }
    fs := Fuse_Slice{w = w, lo = NO_VALUE, hi = NO_VALUE, base = NO_VALUE}
    use := want != .Into && c.asked_dest.type_ != nil   // (fuse_use_type)
    if want == .Into || use { fs.read_as = graph_dest_type(b, c.asked_dest) }
    fs.view = use
    t := check_slice_impl(c, e, env, &fs)
    if fusing(c) == nil { return t }
    if fs.reads {
        v := graph_op_value(b, .Slice, w, e.span, t, "", fs.base, fs.lo, fs.hi)
        c.span_read = {v.op, fs.scalar}
        fuse_done(c, v)
        return t
    }
    base: Operand
    if fs.held {
        // (Its base held — built as it was checked — put after its bounds,
        // as the builder built it.)
        if !graph_fuse_early_place(b, &fs.early) {
            fuse_fail(c, "a slice's bounds that branch, of a value")
            return t
        }
        base = fs.base
    } else {
        base = graph_fuse_base_place(b, e.expr, e.span)
    }
    fuse_done(c, graph_op_value(b, .Slice, w, e.span, t, "", base, fs.lo, fs.hi))
    return t
}

// Whether a take's storage is a plain place (`&s`, `&bytes[i]`, `s`): what
// the builder walks where the carve is.
fuse_carves_place :: proc(e: ^Expr_Take) -> bool {
    if u, is_addr := e.storage.(^Expr_Unary); is_addr && u.op == .Ampersand { return graph_pure_place(u.operand) }
    return graph_pure_place(e.storage)
}

// A slice's bound, built: at the header's width (as it is, `raw`).
fuse_bound :: proc(c: ^Checker, e: Expr, env: ^Type_Scope, w: Written, span: Span, raw := false) -> (Type, Operand) {
    t, r := fuse_expr(c, e, env, .Value, w)
    b := fusing(c)
    if b == nil { return t, NO_VALUE }
    if raw { return t, r.v }
    return t, graph_fuse_widen(b, r.v, span, {to = slice_header_width_type})
}

check_slice_impl :: proc(c: ^Checker, e: ^Expr_Slice, env: ^Type_Scope, fs: ^Fuse_Slice) -> Type {
    lower_subscript_dots(e.expr, e.low)
    lower_subscript_dots(e.expr, e.high)
    target_type: Type
    if b := fusing(c); b != nil && fs != nil && !graph_pure_place(e.expr) {
        // A base that is no plain place, built as it is checked, put after
        // the bounds: a field's, an element's, a pointer's place (over a
        // call's result, say) as it is; else — a call's result, text — held
        // in a temporary.
        fs.held, fs.early = true, graph_fuse_early_begin(b)
        base: Operand
        if fuse_is_place_form(e.expr) {
            r: Fused
            target_type, r = fuse_expr(c, e.expr, env, .Place, temp_span = e.span)
            base = r.v
        } else {
            target_type, base = fuse_hold(c, e.expr, env, e.span)
        }
        if pt, ok := distinct_base(target_type).(^Type_Ptr); ok && base != NO_VALUE {
            base = graph_op_value(b, .Deref, .Implied, e.span, pt.elem, "", base)
        }
        fs.base = base
        graph_fuse_early_end(b, &fs.early)
    } else {
        target_type = check_expr(c, e.expr, env)
    }
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
    if b := fusing(c); b != nil && fs != nil && fs.read_as != nil && elem_type != nil {
        probe := Type_Slice{elem = elem_type}
        if byte_flow(fs.read_as, e, &probe) == .Read && fs.held {
            fuse_fail(c, "bytes read from a value's span")
        } else if byte_flow(fs.read_as, e, &probe) == .Read {
            fs.reads, fs.scalar = true, fs.view || !graph_aggregate(fs.read_as)
            fs.base = graph_fuse_base_place(b, e.expr, e.span)
        }
    }

    // Check that low/high are numeric AND match slice header width — codegen
    // does NOT emit an implicit narrow/widen.
    if e.low != nil {
        lt: Type
        if fs != nil { lt, fs.lo = fuse_bound(c, e.low, env, fs.w, e.span, raw = fs.reads) } else { lt = check_expr(c, e.low, env) }
        if !is_numeric(lt) && !is_any(lt) {
            check_error(c, e.span, TYPE_SLICE_LOW_BOUND_NUMERIC, type_name(lt))
        } else if !coerces_to_slice_width(lt) {
            check_error(c, e.span, TYPE_INDEX_WIDTH,
                type_name(slice_header_width_type), type_name(lt))
        }
    }
    if e.high != nil {
        ht: Type
        if fs != nil && fs.scalar {
            f := fuse_suspend(c)   // (unbuilt)
            ht = check_expr(c, e.high, env)
            fuse_resume(c, f)
        } else if fs != nil {
            ht, fs.hi = fuse_bound(c, e.high, env, fs.w, e.span, raw = fs.reads)
        } else {
            ht = check_expr(c, e.high, env)
        }
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

