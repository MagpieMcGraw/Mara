package mara

import "core:fmt"
import "core:runtime"
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
    ^Type_Partial_Array, // [N]T — partial array (value with inline storage + cursor)
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
    Type_Atom,        // constant text by id: its place in the program's table (checked_atom)
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
Type_Atom :: struct {}

Numeric_Kind :: enum u8 { Signed, Unsigned, Float }
Type_Numeric :: struct {
    kind: Numeric_Kind,
    bits: i32,           // 8, 16, 32, 64 (Type: 16 bytes, every variant 8 or less)
}

// A type as the program holds it (Type_Table): each one once, by its index.
// 0: none.
Type_Id :: distinct u32

// The program's types, each held once: a node's type, in the annotations and
// in the graph, is its id here (type_id).
Type_Table :: struct {
    types: [dynamic]Type,                         // by id; [0]: none
    slots: [dynamic]Type_Slot,                    // (type_id: open-addressed, hashed, probed)
    last:  struct { raw: [2]u64, id: Type_Id },   // (the type asked for last)
    prim:  [TYPE_PRIM_SLOTS]Type_Id,              // (a primitive's, by type_prim_slot: no hashing)
}

// A primitive type's place in Type_Table.prim — a variant that holds
// nothing, an open width of no binding's, a number by its kind and width —
// else -1. (The commonest types by far: their ids found by index.)
@(private="file")
TYPE_PRIM_SLOTS :: 22 + 3 * 6
@(private="file")
type_prim_slot :: #force_inline proc(raw: [2]u64) -> int {
    tag := int(raw[1] & 0xFF)
    switch tag {
    case 1, 4, 5, 6, 7, 18, 19, 20, 21:   // Type_F64, _Bool, _CString, _Utf8, _Byte, _Any, _Void, _Error, _Err
        return tag
    case 2, 3:                            // Type_Infer_Int, _Infer_Float: no cell's
        return tag if raw[0] == 0 else -1
    case 8:                               // Type_Numeric: its kind, its bits
        width := -1
        switch raw[0] >> 32 {
        case 0:   width = 0
        case 8:   width = 1
        case 16:  width = 2
        case 32:  width = 3
        case 64:  width = 4
        case 128: width = 5
        }
        if width < 0 || raw[0] & 0xFF > 2 { return -1 }
        return 22 + int(raw[0] & 0xFF) * 6 + width
    }
    return -1
}

type_table_new :: proc() -> ^Type_Table {
    tt := new(Type_Table)
    append(&tt.types, nil)   // (Type_Id 0: none)
    return tt
}

// A type, as interning tells types apart: which of Type's variants, and its
// value (a pointer, a cell, a width) — none of what it doesn't hold. Its bits:
// the value in the first word, the variant in the second's low byte, numbered
// as Type lists them; of the value, what the variant holds, by this mask.
#assert(size_of(Type) == 16)
@(private="file")
TYPE_VALUE_MASK := [23]u64{
    0,                      // (nil)
    0,                      // Type_F64
    max(u64), max(u64),     // Type_Infer_Int, Type_Infer_Float: their cells
    0, 0, 0, 0,             // Type_Bool, Type_CString, Type_Utf8, Type_Byte
    0xFFFF_FFFF_0000_00FF,  // Type_Numeric: its kind, its bits
    max(u64), max(u64), max(u64), max(u64), // the pointers: ^Type_Ptr, ^Type_Scope,
    max(u64), max(u64), max(u64), max(u64), // ^Type_Fixed_Array, ^Type_Slice, ^Type_Partial_Array,
                                            // ^Type_Enum, ^Type_Union, ^Type_Distinct
    max(u64),               // Type_Const_Int: its value
    0, 0, 0, 0,             // Type_Any, Type_Void, Type_Error, Type_Err
    0,                      // Type_Atom
}

// A composite type made once while the program is checked: the same shape,
// the same one — what type_id and types_equal see as one type. (Its element
// as type_id tells types apart. Once lowering runs — on several threads,
// maybe — each is made anew, as before.)
@(private="file")
Type_Shape :: struct {
    variant:     u8,       // which: Type's variant number (type_id's)
    size:        int,
    elem, index: [2]u64,   // their bits, as type_id keys them
}

@(private="file")
g_type_shapes: map[Type_Shape]rawptr

// The shapes made forgotten: a check of serve's, after another.
types_forget_shapes :: proc() {
    g_type_shapes = make(map[Type_Shape]rawptr, allocator = runtime.heap_allocator())
}

// A type's bits as type_id tells types apart: what its variant holds, the
// variant. (One key per type, for a map of what's made of each.)
type_bits :: proc(t: Type) -> [2]u64 {
    t := t
    raw := (^[2]u64)(&t)^
    tag := raw[1] & 0xFF
    return {raw[0] & TYPE_VALUE_MASK[tag], tag}
}

@(private="file")
type_shape :: proc($T: typeid, variant: u8, size: int, elem, index: Type, made: T) -> ^T {
    if g_infer_frozen { return new_clone(made) }
    key := Type_Shape{variant = variant, size = size, elem = type_bits(elem), index = type_bits(index)}
    if p, ok := g_type_shapes[key]; ok { return (^T)(p) }
    if g_type_shapes == nil { types_forget_shapes() }
    t := new_clone(made, runtime.heap_allocator())   // (outlives the check that made it: the next one's map may name it)
    g_type_shapes[key] = t
    return t
}

type_ptr :: proc(elem: Type) -> ^Type_Ptr {
    return type_shape(Type_Ptr, 9, 0, elem, nil, Type_Ptr{elem = elem})
}

type_slice :: proc(elem: Type) -> ^Type_Slice {
    return type_shape(Type_Slice, 12, 0, elem, nil, Type_Slice{elem = elem})
}

type_fixed_array :: proc(size: int, elem: Type, index_type: Type = nil) -> ^Type_Fixed_Array {
    return type_shape(Type_Fixed_Array, 11, size, elem, index_type, Type_Fixed_Array{size = size, elem = elem, index_type = index_type})
}

type_partial_array :: proc(size: int, elem: Type) -> ^Type_Partial_Array {
    return type_shape(Type_Partial_Array, 13, size, elem, nil, Type_Partial_Array{size = size, elem = elem})
}

// A text literal's type: a list of its quantized room (string_literal_cap)
// where nothing else decides, but its room is its use's — any list it fits
// in. Bound by `:=`, a list of that room (solidify_type).
type_text_list :: proc(bytes: int, elem: Type) -> ^Type_Partial_Array {
    return type_shape(Type_Partial_Array, 14, bytes, elem, nil, Type_Partial_Array{size = string_literal_cap(bytes), elem = elem, text = bytes + 1})
}

// A type's id, made the first time the program has it.
type_id :: proc(tt: ^Type_Table, t: Type) -> Type_Id {
    // (The type asked for last, again: its id, its bits alike.)
    t := t
    raw := (^[2]u64)(&t)^
    p := type_prim_slot(raw)
    if p >= 0 && tt.prim[p] != 0 { return tt.prim[p] }
    if raw == tt.last.raw && tt.last.id != 0 { return tt.last.id }
    defer tt.last.raw = raw
    defer if p >= 0 { tt.prim[p] = tt.last.id }
    tag := raw[1] & 0xFF
    key := [2]u64{tag, raw[0] & TYPE_VALUE_MASK[tag]}
    if key[0] == 0 {
        tt.last.id = 0
        return 0
    }
    if len(tt.slots) == 0 { resize(&tt.slots, 1 << 12) }
    mask := u64(len(tt.slots) - 1)
    h := (key[1] * 0x9E3779B97F4A7C15 ~ key[0] * 0xC2B2AE3D27D4EB4F) >> 20
    for i := h & mask; ; i = (i + 1) & mask {
        slot := &tt.slots[i]
        if slot.id == 0 {   // (none here: made)
            id := Type_Id(len(tt.types))
            append(&tt.types, t)
            slot^ = {key, id}
            tt.last.id = id
            if len(tt.types) * 2 > len(tt.slots) { type_slots_grow(tt) }
            return id
        }
        if slot.key == key {
            tt.last.id = slot.id
            return slot.id
        }
    }
}

@(private="file")
type_slots_grow :: proc(tt: ^Type_Table) {
    old := tt.slots
    tt.slots = make([dynamic]Type_Slot, 2 * len(old))
    mask := u64(len(tt.slots) - 1)
    for s in old {
        if s.id == 0 { continue }
        h := (s.key[1] * 0x9E3779B97F4A7C15 ~ s.key[0] * 0xC2B2AE3D27D4EB4F) >> 20
        i := h & mask
        for tt.slots[i].id != 0 { i = (i + 1) & mask }
        tt.slots[i] = s
    }
    delete(old)
}

@(private="file")
Type_Slot :: struct { key: [2]u64, id: Type_Id }   // (key: its variant, its value)

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

// [N]T — partial array (a list). IR layout: {len, elements: [N x T]}: its cap
// is N, its data its own elements, so nothing in it can point anywhere (bytes
// written over it can only say a len, checked against N where it bounds
// memory). A ^[]T to one carries its len's address, N and its elements
// (slice_ref_ir_type), so lists flow through `^[]T` without monomorphization.
// Copied, it is whole as it is.
Type_Partial_Array :: struct {
    size:         int,
    elem:         Type,
    text:         int,   // a text literal's: its bytes + 1 — its room is its use's, any list it fits in (types_equal); 0: a list
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
// kinds of scope the same (same field resolution, same Self binding, etc.).
Scope_Kind :: enum { Struct, Fun }

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
    variant_of:        ^Type_Union,   // a union's variant's: its union (named `Union.Variant`: scope_display_name)


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

    // The token that declares its name (a fun's, a struct's, a variant's);
    // 0 when no source does.
    decl:           Token_Id,

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
}

// A fun's params and results as codegen passes them — distinct types as
// their bases; among a struct's constructor's results, Self first (its sret
// slot) — read off its one signature as they're asked for. (Reading only:
// codegen's workers share the scopes.)
fn_param :: proc(ft: ^Type_Scope, i: int) -> Struct_Type_Field {
    p := ft.params[i]
    p.type_ = distinct_base(p.type_)
    return p
}

fn_result_count :: proc(ft: ^Type_Scope) -> int {
    if ft.kind == .Struct && !ft.is_module { return 1 + len(ft.return_types) }
    return len(ft.return_types)
}

fn_result :: proc(ft: ^Type_Scope, i: int) -> Type {
    if ft.kind == .Struct && !ft.is_module {
        if i == 0 { return Type(ft) }
        return distinct_base(ft.return_types[i - 1])
    }
    return distinct_base(ft.return_types[i])
}

// ... all of them, in a list of its own: what a fun's emission lays its
// results out by.
fn_results :: proc(ft: ^Type_Scope, allocator := context.temp_allocator) -> []Type {
    out := make([]Type, fn_result_count(ft), allocator)
    for &r, i in out { r = fn_result(ft, i) }
    return out
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
    owner:         ^Type_Scope,   // the fun or struct whose body defines it; nil: its module's
    zero_name:     string,        // its variant written `= 0` — what from_text gives for no name; "": none
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

// A niche union's fieldless variant: the one its null pointer holds.
union_niche_none :: proc(ut: ^Type_Union) -> string {
    for vname in ut.variants { if vname != ut.niche_some { return vname } }
    return ""
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

// A struct's, a fun's or a module's name as the source writes it — a union's
// variant's, `Shape.Rect` — for diagnostics (type_name's, for a named scope).
scope_display_name :: proc(sd: ^Scope_Body) -> string {
    if ut := sd.variant_of; ut != nil && len(sd.source_name) > len(ut.source_name) {
        return fmt.tprintf("%s.%s", ut.source_name, sd.source_name[len(ut.source_name) + 1:])
    }
    return sd.source_name if sd.source_name != "" else sd.name
}

// A fun's name as the profile and the debug info show it: as written, after
// the structs and funs it's in (`Player.update`). A generic's instance has
// its types after it, as its flat name has them (`total_of[i64]`).
scope_path_name :: proc(cf: ^Type_Scope) -> string {
    if cf.source_name == "" && cf.decl != 0 {
        written := tc_text(cf.decl)
        at := strings.index(cf.name, strings.concatenate({written, "__"}))
        if at < 0 { return written }
        args, _ := strings.replace_all(cf.name[at + len(written) + 2:], "__", ", ")
        return strings.concatenate({written, "[", args, "]"})
    }
    name := scope_display_name(cf)
    for p := cf.parent_scope; p != nil && !p.is_module; p = p.parent_scope {
        if outer := scope_display_name(p); outer != "" { name = strings.concatenate({outer, ".", name}) }
    }
    return name
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
//   From_Text → `E.from_text(s)`: no function at all — each call compares
//               the text with E's variants' names where it is
//
// Foreign-only metadata (library, link_name) lives in the Foreign variant, so
// source funs don't carry empty fields they never use.
Function_Origin :: union {
    Origin_Source,
    Origin_Intrinsic,
    Origin_Foreign,
    Origin_From_Text,
}

Origin_Source :: struct {}

Origin_Intrinsic :: struct {
    llvm_name: string,                 // e.g. "llvm.sqrt.f32"
}

Origin_Foreign :: struct {
    library:    string,                // "kernel32", "SDL3", etc.
    link_name:  string,                // C symbol name (prefix + decl name)
}

Origin_From_Text :: struct {
    enum_: ^Type_Enum,                 // whose variants' names the text is compared with
}

// Build a mangled name for a generic instantiation: "Array" + [int] -> "Array__int"
mangle_generic_name :: proc(base: string, type_args: []Type) -> string {
    parts: [dynamic]string
    defer delete(parts)
    append(&parts, base)
    for arg in type_args {
        append(&parts, mangle_type_part(arg))
    }
    return strings.join(parts[:], "__")
}

// A type argument's part of an instance's name: its name — its flat one
// when a body defines it (two funs' own `is_mara`s, two funs' own `Item`s
// are two types: by their names as written, their instances would be one,
// and a call would get the other's).
mangle_type_part :: proc(t: Type) -> string {
    flat, source, pkg: string
    #partial switch v in t {
    case ^Type_Scope:    flat, source, pkg = v.name, v.source_name, v.home_package
    case ^Type_Union:    flat, source, pkg = v.name, v.source_name, v.home_package
    case ^Type_Enum:     flat, source, pkg = v.name, v.source_name, v.home_package
    case ^Type_Distinct: flat, source, pkg = v.name, v.source_name, v.home_package
    }
    if flat != "" && source != "" && flat != make_flat_name(pkg, source) { return sanitize_for_identifier(flat) }
    return sanitize_for_identifier(type_name(t))
}

// Mara type names like `^Box` or `[]Foo` contain characters LLVM rejects in
// identifiers. Replace them with safe equivalents so mangled names are usable
// as LLVM struct names.
sanitize_for_identifier :: proc(s: string) -> string {
    if strings.index_any(s, "^[]., !") < 0 {
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
        case '!': strings.write_string(&b, "_fixed_")   // ([3!]i64: not the list [3]i64's name)
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

// What a condition takes — an if's, a for's, an assert's, an if's as a
// value's, `and` / `or`'s sides, `not`'s: a bool, or an error, true when it
// failed (not Ok), as bool(e) is (lw_truth).
is_condition_type :: proc(t: Type) -> bool {
    if _, ok := t.(Type_Bool); ok { return true }
    return is_any(t) || is_err_type(t)
}

// Through a pointer there is no array→slice decay: the pointee must already
// have the target's memory layout. A fixed array `[N!]T` is N inline elements
// with NO {ptr,len,cap} header, so `^[N!]T` cannot stand in for `^[]T` or
// `^[M]T` — doing so let `&fixed + x` bind to core's `slice_add` (param
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
        // (An enum's value is no integer's: `i64(e)` converts, said so.)
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
        // [tier]utf8) pass free — their rodata globals carry the \0. The
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
        // No array→slice decay through a pointer: ^[N!]T must not satisfy
        // ^[]T / ^[M]T (a fixed array has no slice header to alias).
        if ptr_pointee_layout_mismatch(va.elem, vb.elem) { return false }
        // (A pointee whose width isn't decided yet matches no decided one —
        // what's written through the pointer is the pointee's width:
        // coerce_deferred decides it first, exactly.)
        if is_infer(resolve_infer(va.elem)) != is_infer(resolve_infer(vb.elem)) { return false }
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
        // Implicit coercion: [N!]T is compatible with [M]T (partial array
        // view). Lets fixed-array decls take partial-array sources — most
        // importantly `fa : [N!]utf8 = "lit"` after the literal-type
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
        // (An atom where text goes: the compiler looks its text up.)
        if _, is_atom := b.(Type_Atom); is_atom {
            _, is_text := distinct_base(va.elem).(Type_Utf8)
            return is_text
        }
        // By-value fixed-array -> slice decay: `[N!]T` materialises a slice
        // header {ptr=&arr[0], len=cap=N} — honest, since [N!]T is exactly N
        // elements (e.g. Mesh_Data{primitive_quad()}). The source is hoisted to
        // a scope-lived local, and lifetime past that scope is policed by
        // return-escape analysis. NOT allowed THROUGH A POINTER (^[N!]T has no
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
        // Partial arrays coerce to [:]T (slice view) and to [N!]T (fixed array)
        // by element type. The first 24 bytes of a partial array's layout
        // match a slice header, so `^[N]T` flows safely into `^[:]T` param
        // slots — cursor mutations propagate back through the aliased memory.
        if sl, sl_ok := b.(^Type_Slice); sl_ok {
            return buffer_elem_compatible(va.elem, sl.elem)
        }
        if fa, fa_ok := b.(^Type_Fixed_Array); fa_ok {
            return buffer_elem_compatible(va.elem, fa.elem)
        }
        if pa, ok := b.(^Type_Partial_Array); ok {
            // A list's room is part of its type (its cap is its N): lists
            // of one size — text excepted, whose room is its use's, any
            // list it fits in.
            switch {
            case va.text != 0 && pa.text != 0:
            case va.text != 0: if pa.size < va.text - 1 { return false }
            case pa.text != 0: if va.size < pa.text - 1 { return false }
            case va.size > 0 && pa.size > 0 && va.size != pa.size: return false
            }
            return buffer_elem_compatible(va.elem, pa.elem)
        }
        return false
    case ^Type_Enum:
        // Enums are compatible with infer_int and the same enum — not with an
        // integer type: `i64(e)`, `Kind(n)` convert, said so.
        if _, ok := b.(Type_Infer_Int); ok { return true }
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
    case Type_Atom:
        _, ok := b.(Type_Atom)
        return ok
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
        if v.name != "" { return scope_display_name(v) }
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
        // (Exactly N, `[N!]T`; one for each value of an enum, `[K]T`.)
        if v.index_type != nil { return fmt.tprintf("[%s]%s", type_name(v.index_type), type_name(v.elem)) }
        return fmt.tprintf("[%d!]%s", v.size, type_name(v.elem))
    case ^Type_Slice:
        return fmt.tprintf("[]%s", type_name(v.elem))
    case ^Type_Partial_Array:
        if v.text != 0 { return fmt.tprintf("text (%d bytes)", v.text - 1) }
        return fmt.tprintf("[%d]%s", v.size, type_name(v.elem))
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
    case Type_Atom:         return "atom"
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
// compatible at the buffer element level, so `[]u8 → []byte`, `[8!]u8 → []byte`,
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

// True when a value of type `from` converts to `to` with NO loss — what a
// count, a bound or an index takes into the slice header's width
// (coerces_to_index_width); a value going anywhere else is its own type or an
// explicit cast — no implicit widening (a73f20b and before had it). Same-kind
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
// width lowering compares two operands at (graph_work; the checker makes them
// one type: no mixing). (nil,false) when none exists. Same-kind → the wider;
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
    bt := distinct_base(t)   // (a named one — `type []T` — as its base)
    if _, ok := bt.(^Type_Fixed_Array); ok { return true }
    if _, ok := bt.(^Type_Slice); ok { return true }
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
    case Type_Numeric, Type_F64, Type_Bool, Type_Utf8, Type_Byte, ^Type_Enum, ^Type_Ptr, Type_CString, Type_Err, Type_Atom,
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
// user-named byte containers (`Block :: type [16!]byte`, etc.) get the
// reinterpret-read/write machinery too.
is_byte_slice :: proc(t: Type) -> bool {
    cur := distinct_base(t)
    if pt, ok := cur.(^Type_Ptr); ok { cur = distinct_base(pt.elem) }
    sl, ok := cur.(^Type_Slice)
    if !ok { return false }
    _, is_byte := sl.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element fixed array [N!]byte. Same unwrap
// shape as is_byte_slice so named-byte-container types work.
is_byte_fixed_array :: proc(t: Type) -> bool {
    cur := distinct_base(t)
    if pt, ok := cur.(^Type_Ptr); ok { cur = distinct_base(pt.elem) }
    fa, ok := cur.(^Type_Fixed_Array)
    if !ok { return false }
    _, is_byte := fa.elem.(Type_Byte)
    return is_byte
}

// True when a type is a byte-element partial array [N]byte. Same unwrap
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
        for &f in sd.fields[first_user_field(sd):] {
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
//     reserves the budget explicitly, most commonly via a `size: [N!]byte`
//     filler field).
// Each shortcoming surfaces as its own diagnostic at `span`.
check_shape_constraint :: proc(c: ^Checker, param_name, constraint_name: string, ct: ^Type_Scope, arg: Type, span: Span) {
    // `void` is the universal subtype for shape constraints — used as the
    // default type-arg when the user writes `p : Program` (no arena).
    // Trivially satisfies any `~T` requirement (no API to miss, zero size
    // to budget). Reads / method calls on the resulting void slot are
    // gated separately (see field access and call sites).
    if _, is_void := arg.(Type_Void); is_void { return }

    // (The constraint: what `~T`'s name refers to where it's written — the
    // resolver's. None: a typo, or a module not used there.)
    if ct == nil {
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

// Whether a param of type t can't be written: one passed by address.
is_immutable_param_type :: proc(t: Type) -> bool {
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
        return type_fixed_array(fa.size, solidify_type(fa.elem), fa.index_type)
    }
    // Text bound as itself: a list of its room.
    if pa, ok := rt.(^Type_Partial_Array); ok && pa.text != 0 { return type_partial_array(pa.size, solidify_type(pa.elem)) }
    // A slice or list of them (`[1, 2, 3][:]`): the same.
    if s, ok := rt.(^Type_Slice); ok && is_infer(s.elem) { return type_slice(solidify_type(s.elem)) }
    if pa, ok := rt.(^Type_Partial_Array); ok && is_infer(pa.elem) { return type_partial_array(pa.size, solidify_type(pa.elem)) }
    return rt
}

// ---------------------------------------------------------------------------
// Deferred integer/float inference (the `:=` binding width problem)
// ---------------------------------------------------------------------------
// A `:=` binding whose initializer is an untyped literal/const no longer
// solidifies to i64 at the declaration. It gets a fresh Infer_Cell; its width
// is the one its uses give it — every place it meets a width: arithmetic
// against a sized operand, an argument, an assignment either way, a return, a
// field, an array literal's element, a pointer to it, a dispatch member's
// param. All the same width: Roc's way, a use is a fact, and two that
// disagree are a conflict whichever comes first — the order of the uses
// changes nothing (there is no widening: a value is its type, or a cast).
// No use at all → i64/f64 at codegen. A decision that needs the width before
// any use gave one (a generic's type, a byte view's size, which member of a
// dispatch group) gives it its default then (tc_pin_default). Two bindings
// combined in arithmetic are union-find linked: one width. Literals and
// constant references stay ANONYMOUS (nil cell): each use adopts its own
// context independently — only a named binding carries a cell, since only it
// has one storage slot.
Infer_Cell :: struct {
    resolved:      Type,        // its width, once a use gave it; nil while none has
    resolved_span: Span,        // the use that did — for the conflict diagnostic
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
    if g_infer_frozen { return root }   // (read on several threads: no writes)
    node := cell
    for node.link != nil { next := node.link; node.link = root; node = next } // path-compress
    return root
}

// Inference is done — the program is checked — and its cells are only read:
// while the middle end lowers and analyses codes, on several threads.
g_infer_frozen: bool

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

// A use of a binding of no written width at a width: the first gives it its
// width; any other must be that one — a conflict otherwise, whichever came
// first. (A target of no width yet gives nothing.)
unify_infer_concrete :: proc(c: ^Checker, cell: ^Infer_Cell, target: Type, span: Span) {
    tgt := resolve_infer(target)
    if is_infer(tgt) { return }
    r := infer_root(cell)
    if r.resolved == nil {
        r.resolved, r.resolved_span = tgt, span
        return
    }
    if infer_same(r.resolved, tgt) { return }
    if c != nil {
        check_error(c, span, TYPE_INFER_CONFLICTING_WIDTHS,
            r.name, type_name(r.resolved), span_loc(r.resolved_span), type_name(tgt), span_loc(span))
    }
}

infer_same :: proc(a, b: Type) -> bool {
    return types_equal(a, b) && types_equal(b, a)
}

// Two bindings of no written width that must share one (`m := n`, `a + b`):
// one cell — when both have a width already, the same one.
unify_infer_cells :: proc(c: ^Checker, a: ^Infer_Cell, b: ^Infer_Cell, span: Span) {
    ra := infer_root(a); rb := infer_root(b)
    if ra == rb { return }
    if ra.resolved != nil && rb.resolved != nil && !infer_same(ra.resolved, rb.resolved) {
        if c != nil {
            check_error(c, span, TYPE_INFER_CONFLICTING_WIDTHS,
                ra.name, type_name(ra.resolved), span_loc(ra.resolved_span),
                type_name(rb.resolved), span_loc(rb.resolved_span))
        }
        return
    }
    if rb.resolved != nil { ra.link = rb } else { rb.link = ra }
}

// At a site where `val` meets a concrete `target` (argument, assignment either
// way, field init, return): if val is a deferred binding whose family matches
// the target's (int→int, float→float), the meeting is a use of it at that
// width (unify_infer_concrete) and handled, so the caller skips its normal
// compat check (the use owns the diagnostic). Anonymous infers, concretes,
// and cross-family (int↔float) return false so the normal check still runs.
coerce_deferred :: proc(c: ^Checker, val: Type, target: Type, span: Span) -> bool {
    if _, is_ptr := val.(^Type_Ptr); is_ptr { return coerce_deferred_pointee(c, val, target, span) }
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

// A pointer to a binding whose width isn't given yet, where a pointer to a
// number goes (`n := 0; f(&n)`, f taking ^i32): a use at that width. Whether
// it was such a use.
coerce_deferred_pointee :: proc(c: ^Checker, val: Type, target: Type, span: Span) -> bool {
    vp, is_ptr := val.(^Type_Ptr)
    tp, to_ptr := unwrap_alias(target).(^Type_Ptr)
    if !is_ptr || !to_ptr { return false }
    cell := infer_cell_of(vp.elem)
    if cell == nil { return false }
    tgt := resolve_infer(tp.elem)
    _, tkind, tok := numeric_info(tgt)
    if !tok { return false }
    _, is_float_infer := vp.elem.(Type_Infer_Float)
    if is_float_infer != (tkind == .Float) { return false }   // int↔float stays explicit
    unify_infer_concrete(c, cell, tgt, span)
    return true
}

// Check that a constant's value fits the target type's range (as an integer,
// i_val; as a float, val).
check_value_range :: proc(c: ^Checker, val: f64, i_val: i128, target: Type, span: Span) {
    if msg := value_range_error(val, i_val, target); msg != "" { check_error(c, span, "%s", msg) }
}

// What's wrong with a constant's value at a type it doesn't fit; "" when it
// fits.
value_range_error :: proc(val: f64, i_val: i128, target: Type) -> string {
    #partial switch v in target {
    case Type_Numeric:
        // Word-sized (bits=0): skip — width is decided at codegen, and the 32-bit
        // case is conservative (anything that would overflow there already
        // overflows on the 64-bit case worth catching).
        if v.bits == 0 { return "" }
        switch v.kind {
        case .Signed:
            // i128 covers the storage range exactly — anything that reached us
            // already fits. Width=128 also skips the formula below where
            // `1 << 127` would wrap.
            if v.bits == 128 { return "" }
            max_v := (i128(1) << uint(v.bits - 1)) - 1
            min_v := -(i128(1) << uint(v.bits - 1))
            if i_val < min_v || i_val > max_v {
                return fmt.aprintf(TYPE_CONSTANT_OVERFLOWS_RANGE, i_val, type_name(target), min_v, max_v)
            }
        case .Unsigned:
            // For u128, the i128 storage caps at 2^127-1, so the parser's u64
            // ceiling is already much tighter. Just sanity-check non-negative.
            if v.bits == 128 {
                if i_val < 0 {
                    return fmt.aprintf(TYPE_CONSTANT_OVERFLOWS_RANGE_128, i_val, type_name(target))
                }
                return ""
            }
            max_v := (i128(1) << uint(v.bits)) - 1
            if i_val < 0 || i_val > max_v {
                return fmt.aprintf(TYPE_CONSTANT_OVERFLOWS_RANGE_2, i_val, type_name(target), max_v)
            }
        case .Float:
            // f16: ~65504 max magnitude.
            if v.bits == 16 {
                if val > 65504 || val < -65504 {
                    return fmt.aprintf(TYPE_CONSTANT_OVERFLOWS_F16, val)
                }
            } else if v.bits == 32 {
                if val > 3.4028235e+38 || val < -3.4028235e+38 {
                    return fmt.aprintf(TYPE_CONSTANT_OVERFLOWS_F32, val)
                }
            }
        }
    case Type_F64:
        // f64 — no meaningful overflow from a literal
    case:
        // Non-numeric target — nothing to check
    }
    return ""
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
// the hint is a use of the cell as well (unify_infer_concrete) — otherwise the binding
// may stay open and later solidify to i64, disagreeing with the width the hint
// forced here (for a param that surfaced as a signature-i64-vs-body-i32 mismatch
// → bad IR). The use mirrors coerce_deferred at a direct decl/arg/return; this
// is that site reached through arithmetic.
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
    return Type_Error{}   // (two widths: a cast says which)
}

promote_numeric :: proc(c: ^Checker, a: Type, b: Type, span: Span) -> Type {
    // Deferred-inference aware: an open binding meeting a sized operand is a
    // use of it at that width; two open bindings are union-linked so they
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
    // Through its `using` fields: a struct's field, a fixed array's swizzle.
    if path, through := struct_using_path(st, field_name); through {
        last := distinct_base(path[len(path) - 1].type_)
        if fa, is_array := last.(^Type_Fixed_Array); is_array {
            if len(field_name) == 1 { return fa.elem }
            return type_fixed_array(len(field_name), fa.elem)
        }
        return resolve_struct_field(as_scope_body(last), field_name)
    }
    return nil
}

// The `using` fields a struct reaches a field through, outermost first —
// `p.x`, with `using pos: Place`, is `p.pos.x` — when it has no field of
// that name itself: the last one's type is the struct with the field, or the
// fixed array with that swizzle. through false: no using field has it.
struct_using_path :: proc(st: ^Scope_Body, field_name: string) -> (path: []Struct_Type_Field, through: bool) {
    if field_name in st.field_map { return nil, false }
    for f in st.fields {
        if !f.is_using { continue }
        if fa, is_array := distinct_base(f.type_).(^Type_Fixed_Array); is_array {
            if is_swizzle_field(field_name, fa.size) { return one_field(f), true }
            continue
        }
        inner := as_scope_body(distinct_base(f.type_))
        if inner == nil || len(inner.fields) == 0 { continue }
        if field_name in inner.field_map { return one_field(f), true }
        if rest, found := struct_using_path(inner, field_name); found {
            whole := make([]Struct_Type_Field, len(rest) + 1, context.temp_allocator)
            whole[0] = f
            copy(whole[1:], rest)
            return whole, true
        }
    }
    return nil, false
}

// A path of one field, kept for the caller (temp).
@(private="file")
one_field :: proc(f: Struct_Type_Field) -> []Struct_Type_Field {
    path := make([]Struct_Type_Field, 1, context.temp_allocator)
    path[0] = f
    return path
}

// The token declaring a struct's field — its own, or one a `using` field's
// struct has; 0 for none (a swizzle through a using array).
struct_field_decl :: proc(st: ^Scope_Body, field_name: string) -> Token_Id {
    if i, ok := st.field_map[field_name]; ok { return st.fields[i].decl }
    if path, through := struct_using_path(st, field_name); through {
        if inner := as_scope_body(distinct_base(path[len(path) - 1].type_)); inner != nil {
            if i, ok := inner.field_map[field_name]; ok { return inner.fields[i].decl }
        }
    }
    return 0
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

