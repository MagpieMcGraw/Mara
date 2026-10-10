package mara

import "core:fmt"
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

Type_Any :: struct {}
Type_Void :: struct {}
Type_Error :: struct {}
Type_Err :: struct {}

Numeric_Kind :: enum u8 { Signed, Unsigned, Float }
Type_Numeric :: struct {
    kind: Numeric_Kind,
    bits: i32,           // 8, 16, 32, 64 (Type: 16 bytes, every variant 8 or less)
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
    decl:          Token_Id, // the token that declares it; 0 when none does
    type_:         Type,
    default_node:  Tree_Id, // its default in the flat tree; 0 if none
    default_slot:  Maybe(int), // ... one of a group's one value (`x, y := f()`): f's result there, else the value
    is_using:      bool,
}

// Demand-driven resolution state for a scope's signature (a struct's fields, a
// fun's params/returns). Unresolved → In_Progress → Resolved. The In_Progress
// state is the cycle guard: re-entering a scope that's mid-resolution (a type
// that refers to itself through a value field) is detected here rather than
// recursing forever.
Resolution_State :: enum {
    Unresolved,
    In_Progress,
    Resolved,
}

// Scope_Kind distinguishes struct-shape scopes (data layout) from fun-shape
// scopes (callable body). Set from the declaration's keyword:
//   `struct` / `class`  → .Struct
//   `fun`               → .Fun
// Only codegen cares about the distinction — the type checker treats both
// kinds of scope the same (same field resolution, same name lookup, same
// Self binding, etc.).
Scope_Kind :: enum { Struct, Fun, Block }   // Block = an if/for/defer body — locals only (in .types), no members/params/returns

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
    // packed binary formats. Set where the struct is registered
    // (tc_register_scope); read by its layout (layout.odin) and by the LLVM
    // struct-type emission (`<{ ... }>`).
    is_packed:      bool,

    // Union-variant marker. A union's variant struct carries the tag (+pad) as
    // its first field(s) — `__tag` at index 0, `__pad` next when the union has
    // padding — so the variant IS the union value and rides struct codegen.
    // codegen writes `union_variant_tag` into field 0 at construction time
    // (the tag isn't a user-set field). False/0 for ordinary structs.
    is_union_variant:  bool,
    union_variant_tag: i64,


    // Its definition in the flat tree (a Fun_Def, a Struct_Def). 0 for types
    // with no single source statement (foreign decls, the synthetic Program
    // global, etc.).
    node:           Tree_Id,

    // Its body's check (its fields: tc_scope_body) — run once, however many
    // uses need its fields first, and the guard against a struct whose fields
    // need its own. Zero value Unresolved.
    sig_state:      Resolution_State,

    // The scope it is declared in: its file's, or the body it is nested in.
    // Its names resolve through it.
    parent_scope:   ^Type_Scope,

    // Associated definitions (scoped :: defs).
    // Values point to the actual Type the bare name resolves to — read
    // `.name` off the pointer when codegen needs the flat/mangled string.
    // (Was `map[string]string` carrying the flat name redundantly with
    // Type_Scope.name etc. — consolidated as part of the Mara2-style
    // env-pointer cleanup.)
    functions:      map[string]^Type_Scope, // bare name -> callable fun/struct
    types:    map[string]Type,         // bare name -> nested type (struct/enum/union/distinct)
    refs:     map[string]Ref,          // bare name -> what declares it (scope_bind)

    // The token that declares its name (a fun's, a struct's, a variant's);
    // 0 when no source does.
    decl:           Token_Id,

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

    // --- What codegen emits ------------------------------------------------
    // checked.functions points straight at each ^Type_Scope. Populated at
    // extract time (check phase, stable allocator) so codegen reads them
    // directly.

    origin:               Function_Origin,  // Source / Intrinsic / Foreign — codegen dispatch
    body_span:            Span,             // span of the declaring statement (diagnostics)
    is_exposed:           bool,             // `#expose` → dllexport linkage + unmangled symbol
    return_binding_names: [dynamic]string,  // named-return locals (`fun() -> (fwd, up: Vec3)`)
    return_binding_decls: [dynamic]Token_Id,  // ... and the tokens that declare them
    // Codegen-facing signature caches (see populate_cg_signature). cg_returns
    // prepends a struct ctor's Self (sret slot 0); both pre-unwrap distinct.
    // Built at CHECK time: codegen's parallel workers read them, and must
    // not write a shared Type_Scope.
    cg_returns:           [dynamic]Type,
    cg_params:            [dynamic]Struct_Type_Field,
}

// Build the codegen-facing signature caches (cg_returns + cg_params) into ft.
// Both pre-unwrap distinct wrappers; cg_returns Self-prepends a struct ctor's
// sret slot 0. Runs at CHECK time: computing them during codegen, under a
// worker's transient arena, would dangle — and write a shared Type_Scope from
// parallel workers.
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

// A scope: a struct, a fun, a block, a file or a module — one per
// declaration, persisting past checking, what codegen consumes. The `kind`
// tells codegen whether to emit a data layout or a function body:
//   .Struct, no params:   a struct without a constructor
//   .Struct, with params: a struct with constructor args (`Foo :: struct(a: i64)`)
//   .Fun:                 a function
// It holds what is fixed at its declaration — its signature, members and
// layout, its body's place — never point-sensitive flow state ("is x
// initialized HERE" differs at every program point: the graph's analyses').
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

// --- what the checker's types say of their source, for the passes after it ---

// Whether a param or a field has a default.
field_has_default :: proc(f: Struct_Type_Field) -> bool {
    return f.default_node != 0
}

// Whether a scope is written in the source — a fun, a struct, an intrinsic, an
// instance of one: what the analyses can follow into.
scope_is_written :: proc(ts: ^Type_Scope) -> bool {
    return ts.node != 0
}

// Whether a scope is an intrinsic: its body generated at each call.
scope_is_intrinsic :: proc(ts: ^Type_Scope) -> bool {
    return ts.node != 0 && scope_view(&build_tree, ts.node).intrinsic != 0
}

// Whether a scope's body is written empty.
scope_body_is_empty :: proc(ts: ^Type_Scope) -> bool {
    return ts.node == 0 || len(scope_view(&build_tree, ts.node).body) == 0
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
    for p in ft.params { if !field_has_default(p) { return false } }
    return len(ft.return_types) == 0
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
// containing Type_Scope by transmute. `is_module` (the namespace marker) lives
// on Type_Scope, so a ^Scope_Body reaches it through here.
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

Type_Enum :: struct {
    name:          string,  // C-ified flat name
    source_name:   string,  // user-written name (used for namespaced printing of error_kinds)
    home_package:  string,  // owning module flat name (see Scope_Body.home_package)
    span:          Span,    // declaring statement's span (diagnostics / `mara ask` locations)
    tag_type:      string,                    // "" = default (i64), or "i32", "i16", etc.
    variants:      map[string]int,
    variant_decls: map[string]Token_Id,   // the token that declares each
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
    variant_structs: map[string]^Type_Scope,   // each variant's struct, by its name
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
        vst := ut.variant_structs[vname]
        if vst == nil { return "" }
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
        vst := ut.variant_structs[vname]
        if vst == nil || vst.is_union_variant { continue }   // idempotent
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

Type_Distinct :: struct {
    name:             string,  // C-ified flat name
    source_name:      string,  // user-written bare name for diagnostics ("" falls back to name)
    home_package:     string,  // owning module flat name (see Scope_Body.home_package)
    span:             Span,    // declaring statement's span (diagnostics / `mara ask` locations)
    base_type:        Type,    // the underlying type (transparent at codegen level)

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
// Functions: where each comes from
// ---------------------------------------------------------------------------

// Where this function comes from. Codegen branches on the variant:
//   Source    → emit a normal function body in IR
//   Intrinsic → emit a call to the LLVM intrinsic with `llvm_name`
//   Foreign   → emit `declare`s and call the external symbol via static
//               import lib (the linker writes the DLL/SO dep into the binary)
//
// Foreign-only metadata (library, link_name) lives in the Foreign variant, so
// source funs don't carry empty fields they never use.
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
}

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

// Slice header width — kept in sync with codegen's SLICE_LEN_IR.
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
    case Type_Numeric:                   return int(v.bits), v.kind, true
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
    return Type_Numeric{kind = .Signed, bits = i32(w)}, true
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
    if kind == slice_header_width_type.kind && bits == int(slice_header_width_type.bits) {
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

// Whether `==` compares two values of t as they are: a scalar's bits (a
// number, a bool, a character, an enum, a pointer, an err, a fun's value),
// or a value not typed yet. Anything else (text: mara.core's `overload ==`)
// compares only through an overload.
is_comparable :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(resolve_infer(t)) {
    case Type_Numeric, Type_F64, Type_Bool, Type_Utf8, Type_Byte, ^Type_Enum, ^Type_Ptr, Type_CString, Type_Err,
         Type_Infer_Int, Type_Infer_Float, Type_Any, Type_Error:
        return true
    case ^Type_Scope:
        return v.kind == .Fun
    }
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
// (so `^[]byte` is recognized) and unwraps distinct/alias wrappers so
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
        for vname, st in v.variant_structs {
            if r := byte_slice_reason(c, st, path == "" ? vname : fmt.tprintf("%s.%s", path, vname)); r != "" { return r }
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

// A value written into a byte buffer (`bytes[off] = v`, `bytes[lo:hi] = v`) is
// stored as its raw bytes, so it can't hold a slice header.
check_byte_write :: proc(c: ^Checker, val_type: Type, span: Span) {
    if why := byte_slice_reason(c, val_type); why != "" {
        check_error(c, span, TYPE_BYTE_WRITE_REFERENCE, type_name(val_type), why)
    }
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
check_shape_constraint :: proc(c: ^Checker, param_name, constraint_name: string, arg: Type, home_package: string, span: Span) {
    // `void` is the universal subtype for shape constraints — used as the
    // default type-arg when the user writes `p : Program` (no arena).
    // Trivially satisfies any `~T` requirement (no API to miss, zero size
    // to budget). Reads / method calls on the resulting void slot are
    // gated separately (see field access and call sites).
    if _, is_void := arg.(Type_Void); is_void { return }

    // Resolve the constraint type by name. The bare identifier in `~T` is
    // looked up against the home package of the template that declared the
    // constraint — the only module its `~T` could name. We try the flat key first; if that
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
            constraint_name, param_name)
        return
    }
    arg_scope, arg_ok := distinct_base(arg).(^Type_Scope)
    if !arg_ok || arg_scope.kind != .Struct {
        check_error(c, span,
            TYPE_GENERIC_ARGUMENT_CONCRETE_STRUCT_CLASS,
            param_name, constraint_name, type_name(arg))
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
            if !field_has_default(arg_fn.params[i]) {
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
    ct_size  := type_size(ct)
    arg_size := type_size(arg_scope)
    if arg_size > ct_size {
        check_error(c, span,
            TYPE_TYPE_FIT_SIZE_BUDGET_NEEDS,
            arg_scope.name, constraint_name, arg_size, ct_size)
    }
}

// ---------------------------------------------------------------------------
// Storage routing — two operations, one policy
// ---------------------------------------------------------------------------
// Every value's size is knowable at compile time (no runtime-sized types), so
// the whole "stack vs arena" decision reduces to two operations:
//
//   1. Find the value's size       — type_size (layout.odin). It is the
//      TOTAL inline footprint: struct padding, fixed-array storage, and
//      partial-array elements are all counted; a slice is just its header
//      (its elements are a separate allocation, routed on their own).
//   2. Route it to the right store — routes_to_arena, below.
//
// Both the type checker (tc_storage_sizes — the early "declare an allocator"
// error) and codegen (alloca vs emit_arena_bump) gate on routes_to_arena, so the
// threshold lives in exactly one place and the two stages can't drift.

// Values at or above this many bytes route through the scope arena, never the
// stack. The single source of truth for "big".
ARENA_THRESHOLD :: 1024

routes_to_arena :: proc(t: Type) -> bool {
    return type_size(t) >= ARENA_THRESHOLD
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
    t, ok := scope_lookup(env, name)
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

// Check that a constant's value fits the target type's range (as an integer,
// i_val; as a float, val).
check_value_range :: proc(c: ^Checker, val: f64, i_val: i128, target: Type, span: Span) {
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
                check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE, i_val, type_name(target), min_v, max_v)
            }
        case .Unsigned:
            // For u128, the i128 storage caps at 2^127-1, so the parser's u64
            // ceiling is already much tighter. Just sanity-check non-negative.
            if v.bits == 128 {
                if i_val < 0 {
                    check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE_128, i_val, type_name(target))
                }
                return
            }
            max_v := (i128(1) << uint(v.bits)) - 1
            if i_val < 0 || i_val > max_v {
                check_error(c, span, TYPE_CONSTANT_OVERFLOWS_RANGE_2, i_val, type_name(target), max_v)
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
// Checking helpers: what the checker and the passes after it share
// ---------------------------------------------------------------------------

// Freeze a callable's deferred default-param cells once its body is checked.
// Each untyped numeric default seeded an Infer_Cell; the
// body has since pinned it to the width it's used at (arithmetic against a sized
// operand, an argument, an assignment, a return, a field initializer). Resolve
// that to a concrete type and write it back into the signature, so callers and
// codegen never see an open cell. A FUNCTION param that
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

is_partial_array :: proc(t: Type) -> bool {
    _, is_pa := distinct_base(t).(^Type_Partial_Array)
    return is_pa
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

// Count how many required (non-default) params a function has.
count_required_params :: proc(fun_type: ^Type_Scope) -> int {
    required := len(fun_type.params)
    for i := len(fun_type.params) - 1; i >= 0; i -= 1 {
        if field_has_default(fun_type.params[i]) {
            required -= 1
        } else {
            break
        }
    }
    return required
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

// The element type indexing a value of type `t` yields — through one pointer,
// as indexing auto-derefs; nil when `t` isn't indexable.
index_elem_type :: proc(t: Type) -> Type {
    bt := distinct_base(t)
    if p, ok := bt.(^Type_Ptr); ok { bt = distinct_base(p.elem) }
    #partial switch v in bt {
    case ^Type_Slice:         return v.elem
    case ^Type_Fixed_Array:   return v.elem
    case ^Type_Partial_Array: return v.elem
    }
    return nil
}

// Resolve a field name on a struct, searching direct fields first, then
// recursively into using-marked embedded struct fields.
// Returns the field type, or nil if not found.
resolve_struct_field :: proc(st: ^Scope_Body, field_name: string) -> Type {
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
                result := resolve_struct_field(inner_sd, field_name)
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

