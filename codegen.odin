package mara

import "core:fmt"
import "core:slice"
import "core:strings"
import "core:os"

// ---------------------------------------------------------------------------
// LLVM IR Code Generator
//
// Walks the typed AST and emits LLVM IR text (.ll file).
// Supports: int arithmetic, booleans, comparisons, variables,
//           if/else, for loops, functions, print() builtin.
// ---------------------------------------------------------------------------

// Slice / partial-array header layout.
//
// Slices and partial arrays share a { len, cap, ptr } header. Each field's
// width is controlled by Slice_Layout so the layout can be retargeted
// (16-byte slices on 64-bit, 32-bit ptr on embedded, etc.) without touching
// every codegen site.
//
// Defaults are set at package init for 64-bit / i64 len+cap (slice = 24
// bytes). `init_slice_layout` in generate_program updates ptr_size and the
// derived strings for the actual target.
Slice_Layout :: struct {
    len_ir:   string,  // LLVM IR scalar for len  (e.g. "i64", "i32")
    cap_ir:   string,  // LLVM IR scalar for cap
    len_size: int,     // bytes
    cap_size: int,     // bytes
    ptr_size: int,     // bytes (target-dependent — 4 on wasm32 etc.)
}

slice_layout: Slice_Layout = {
    len_ir   = "i32",
    cap_ir   = "i32",
    len_size = 4,
    cap_size = 4,
    ptr_size = 8,
}

// Derived strings and sizes. Set together with slice_layout in
// init_slice_layout; defaults below cover the default 64-bit / i32+i32+ptr
// case (16-byte header) so the type checker (which runs before
// init_slice_layout) sees sensible values.
SLICE_IR_TYPE:               string = "{ i32, i32, ptr }"
PARTIAL_ARRAY_HEADER_PREFIX: string = "{ i32, i32, ptr,"
slice_header_bytes:          int    = 16
slice_header_align:          int    = 8

// Update slice_layout and derived strings for the current target. Called
// once per program at the top of generate_program after word_size_is_32
// is set.
init_slice_layout :: proc() {
    slice_layout.ptr_size = 4 if word_size_is_32 else 8
    SLICE_IR_TYPE = strings.concatenate({
        "{ ", slice_layout.len_ir, ", ", slice_layout.cap_ir, ", ptr }",
    })
    PARTIAL_ARRAY_HEADER_PREFIX = strings.concatenate({
        "{ ", slice_layout.len_ir, ", ", slice_layout.cap_ir, ", ptr,",
    })
    slice_header_bytes = slice_layout.len_size + slice_layout.cap_size + slice_layout.ptr_size
    a := slice_layout.len_size
    if slice_layout.cap_size > a { a = slice_layout.cap_size }
    if slice_layout.ptr_size > a { a = slice_layout.ptr_size }
    slice_header_align = a
}

// Slice header field positions. Partial arrays share these for their first
// `slice_header_bytes` bytes; the elements field follows at
// PARTIAL_ELEMENTS_FIELD.
Slice_Fields :: struct { len, cap, ptr: int }
SLICE :: Slice_Fields{len = 0, cap = 1, ptr = 2}
PARTIAL_ELEMENTS_FIELD :: 3

// Build the LLVM IR type for a `[..N]T` partial array. `cap` includes the
// sentinel slot if applicable; caller must pre-add the +1.
partial_array_ir_type :: proc(elem_ir: string, cap: int) -> string {
    return strings.concatenate({
        "{ ", slice_layout.len_ir, ", ", slice_layout.cap_ir, ", ptr, [",
        fmt.tprintf("%d", cap), " x ", elem_ir, "] }",
    })
}

// Open design note: partial arrays reuse the slice layout via pointer-pun on
// the first 24 bytes, which lets one set of field-access codegen paths serve
// both. Cost: shared code concentrates bugs (see the stale-index bug fixed
// in gen_slice_field_store — it survived because there's no parallel
// partial-array writer to disagree), and the address chain collapses both
// into final_kind=.Slice, losing the distinction. The end-state handler in
// gen_field_access has to re-discriminate via type cast to recover sentinel
// / elem info. Fine while no behaviour needs to branch on slice-vs-partial-
// array, but if per-shape features show up later, tag the chain (e.g.
// .Slice_Header with a source enum) or split the kinds. Revisit when that
// pressure appears.

// Info about a scalar variable in codegen (simple alloca)
Scalar_Var :: struct {
    alloca: string, // %varname
}

// Info about an array variable in codegen
Array_Var :: struct {
    alloca:       string, // alloca name / data pointer for the array
    capacity:     int,    // compile-time capacity N (0 for VLAs)
    capacity_val: string, // LLVM IR value for runtime capacity (VLA only, "" for fixed)
    elem_type:    string, // LLVM element type: "i64", "double", "ptr", etc.
    is_utf8:      bool,   // true for utf8 arrays — last byte reserved for null terminator
    has_sentinel: bool,   // true for [N, 0]T sentinel-terminated arrays
    sentinel:     int,    // sentinel value (e.g. 0 for null-terminated)
}

// Info about a slice variable in codegen
// A slice is a fat pointer: { ptr data, i64 len, i64 cap }
Slice_Var :: struct {
    alloca:       string, // alloca for the { ptr, i64, i64 } struct
    elem_type:    string, // LLVM element type: "i64", "double", etc.
    is_utf8:      bool,   // true for []utf8 slices — affects how print formats elements
    has_sentinel: bool,   // true for [, S]T sentinel-terminated slices — last element reserved
    // Sized slice of slice-bearing struct: the appended elements' slice
    // fields point into this pool buffer instead of fresh per-call allocas.
    // Empty when the slice has no associated pool.
    pool_alloca:  string, // alloca for the pool's { ptr, i64, i64 } slice header
}

// Info about a struct variable in codegen
Struct_Var :: struct {
    alloca:      string,     // %varname
    struct_name: string,     // class name (e.g. "Point")
    vla_cap:     string,     // runtime capacity for VLA array class structs ("" for fixed)
}

// No shadow Struct_Def — codegen reads directly from checked.table.funs (Type_Scope).
// Helper functions compute LLVM-specific info on the fly.

// Info about a union variable in codegen
Union_Var :: struct {
    alloca:     string,
    union_name: string,
}

// Unified variable entry — each codegen variable is exactly one of these kinds.
Var_Entry :: union {
    Scalar_Var,
    Array_Var,
    Struct_Var,
    Union_Var,
    Slice_Var,
}

// ---------------------------------------------------------------------------
// Address chain — unified address resolution for field access and indexing
// ---------------------------------------------------------------------------

// A single step in an address resolution chain
Chain_Step :: union { Step_Field, Step_Index, Step_Slice_Index, Step_Deref }

Step_Field :: struct {
    llvm_type: string,             // e.g. "%class.Outer"
    field_idx: int,
    field_def: ^Struct_Type_Field, // for type info after resolution
}

Step_Index :: struct {
    array_type: string,  // "[8 x i64]"
    elem_type:  string,  // "i64"
    index_expr: Expr,    // AST expr (gen_expr'd during emission)
    capacity:   int,     // compile-time cap for bounds check
    name_hint:  string,  // for error messages
    span:       Span,
}

// Index into a slice (dynamic cap, runtime-loaded). current_ptr points at a
// slice header { ptr, i64 len, i64 cap }; emission loads data+cap, bounds-checks
// against cap (writes-at-len need to be legal so use cap, not len), and GEPs
// elem_type from the data pointer. Resets the index segment so subsequent field
// steps GEP into the element struct.
Step_Slice_Index :: struct {
    elem_type:  string,
    index_expr: Expr,
    name_hint:  string,
    span:       Span,
}

Step_Deref :: struct {
    name_hint:   string,
    span:        Span,
    // LLVM type for the pointee — drives the subsequent GEP segment.
    // Empty when the deref target type isn't useful (e.g. legacy callers).
    result_type: string,
}

// GEP index entry for multi-index emission
GEP_Index :: struct {
    width: string,  // "i32" or "i64"
    value: string,  // "0", "3", or "%t42"
}

// The final kind of the address chain target
Chain_Result :: enum { Scalar, Struct, Array, Slice }

// A resolved address chain ready for emission
Address_Chain :: struct {
    base_ptr:    string,             // alloca or loaded ptr
    base_type:   string,             // LLVM type at base
    steps:       [dynamic]Chain_Step,
    final_type:  string,             // LLVM IR type of the final element
    final_kind:  Chain_Result,
    struct_name: string,             // if final is struct
    array_cap:   int,                // if final is array
    array_elem:  string,             // if final is array
    elem_signed: bool,               // if final scalar is signed
}

// One local variable in a struct-returning function whose backing storage
// escapes via a slice field of the returned struct. The caller supplies
// the buffer as a hidden trailing argument (after %sret), and the callee
// aliases the local to that pointer directly — no separate alloca, no
// GEP. Order in Fun_Info.escape_locals = order in the hidden-arg list.
Escape_Local :: struct {
    name:         string,
    cap:          int,       // logical array capacity
    elem_type:    string,    // LLVM element type
    elem_size:    int,       // bytes per element
    is_utf8:      bool,
    has_sentinel: bool,
    sentinel:     int,
}

// Info about a user-defined function's signature for struct-aware calling
Fun_Info :: struct {
    ret_type:          string,            // LLVM type: "i64", "double", "i1", "ptr", "void"
    ret_struct:        string,            // "" for non-struct, or struct name (e.g. "Point")
    ret_array_cap:     int,              // >0 if returning a fixed array (sret convention)
    ret_array_elem:    string,           // LLVM element type (e.g. "i64", "double")
    ret_tuple:         ^Type_Tuple,      // non-nil if returning a tuple (multi-return)
    ret_slice_elem:    string,           // non-"" if returning a slice (sret convention)
    param_types:       [dynamic]string,   // per-param IR types ("i64", "ptr", etc.)
    param_structs:     [dynamic]string,   // "" or struct name per param
    // Sibling-storage escape analysis: locals referenced through slice fields
    // of a returned struct. The caller allocates each as a fresh sibling
    // (stack or scope arena per size threshold) and passes a pointer as a
    // hidden trailing argument after %sret. The callee aliases the local
    // to that argument directly.
    escape_locals:    [dynamic]Escape_Local,
    // True for struct-returning fns whose body has find_nrvo_candidate hit:
    // the callee constructs directly into %sret, so any caller-side
    // sized-slice header re-init after the call would be a redundant
    // write-of-same-values.
    uses_struct_nrvo: bool,
}

// Control-flow scope tracking for the context system (automatic arena mark/reset).
// Distinct from Scope_Kind in parser.odin, which tags struct vs fun declarations.
Control_Scope_Kind :: enum { Function, If_Then, If_Else, For_Body, Match_Arm, Main_Body }

Scope_Entry :: struct {
    has_mark:        bool,                    // true if this scope emitted an arena mark
    scope_kind:      Control_Scope_Kind,
    deferred_blocks: [dynamic][dynamic]Stmt,  // defer blocks (LIFO order: last block runs first, stmts within block run forward)
}

// Branch targets for the enclosing loop. Pushed by gen_loop_body, popped on
// exit. gen_stmt reads the top entry when emitting `break` / `continue`, so
// these statements work at any depth (inside if / match / etc.), not just at
// the loop's top level.
Loop_Labels :: struct {
    break_label:    string,
    continue_label: string,
}

Codegen :: struct {
    out:         strings.Builder,  // the IR text
    alloca_buf:  strings.Builder,  // hoisted allocas (entry block)
    body_buf:    strings.Builder,  // temporary buffer for function body during alloca hoisting
    hoist_allocas: bool,           // true during function body codegen
    emitted_allocas: map[string]string, // track alloca names emitted in current function (name -> IR type for dedup)
    tmp_counter: int,              // %0, %1, %2 ...
    label_counter: int,            // label numbering
    all_vars:    map[string]Var_Entry,    // unified variable registry (scalars, arrays, structs, unions, slices)
    current_ret_type: string,            // LLVM return type of the current function ("i64", "ptr", etc.)
    // Current function's body — accessible during stmt codegen so pool-sizing
    // analysis at a sized-slice decl can scan forward through its scope.
    current_fun_body: []Stmt,
    // Pool routing context: when a `&pool_slice + call_with_escape()` append
    // is being emitted, escape-storage allocations route through pool_alloca
    // (carving from its cursor) instead of fresh allocas. Empty when no
    // pool routing is active.
    escape_pool_alloca: string,
    // Type info from the type checker
    checked:     ^Checked_Program,       // resolved type info from type checker
    // String literal table: value -> global name
    string_literals: map[string]string,
    string_counter:  int,
    // Track all string globals to emit at top of module
    string_decls: [dynamic]string,
    // Struct support (no shadow map — reads directly from checked.table.funs)
    struct_decls:       [dynamic]string,        // LLVM type definitions
    registered_structs: map[string]bool,         // dedup guard for struct decl emission
    // Enum values: read from checked.enums directly (no shadow map)
    // Union support: read from checked.table.unions directly
    // Context system: automatic scope-based arena mark/reset
    context_enabled:  bool,                       // true when user set context.scope_allocator
    arena_alloc_name: string,                     // flat name for the arena alloc function
    arena_mark_name:  string,                     // flat name for the arena mark function
    arena_reset_name: string,                     // flat name for the arena reset function
    arena_new_name:   string,                     // flat name for the arena new function
    arena_alloc_has_debug: bool,                  // true if alloc() takes name/span debug params
    scope_stack:      [dynamic]Scope_Entry,       // tracks active scopes for mark/reset
    loop_label_stack: [dynamic]Loop_Labels,        // current loop's break/continue branch targets (innermost on top)
    ctx_alloca:       string,                     // LLVM tmp for Context alloca in @main
    // NRVO: name of variable aliased to sret (skipped in scope_has_big_values)
    nrvo_var:         string,
    // Multi-return: tuple type of current function (nil if not a tuple-returning function)
    ret_tuple:        ^Type_Tuple,
    // Tuple call result: temp alloca pointers from the most recent tuple-returning call
    tuple_result_ptrs:  [dynamic]string,  // alloca names for each tuple element
    tuple_result_types: [dynamic]string,  // LLVM types for each tuple element
    // Fun_Info cache: avoids re-deriving from Checked_Scope on every call
    fun_info_cache:   map[string]Fun_Info,
    // Temp results: typed fields replacing magic __call_result / __field_result / __swizzle_result
    // in all_vars. Set by gen_call / gen_field_access / gen_swizzle_read_multi, claimed by callers.
    temp_call_result:    Maybe(Array_Var),   // array-returning function call
    temp_field_result:   Maybe(Var_Entry),   // aggregate field access (array, struct, or slice)
    temp_swizzle_result: Maybe(Array_Var),   // multi-component swizzle read
    // Overflow-checking intrinsics used (for declaration at end of module)
    overflow_intrinsics: map[string]bool,
    // Web build (wasm32-unknown-emscripten): adjusts size_t-shaped libc decls
    // (strlen returns i32 on wasm32, not i64), among other target tweaks.
    web: bool,
    shared: bool,  // -shared build mode — emit a DLL/SO instead of an exe
}

// Look up a foreign function's IR name (link_name or fallback to fn_name).
foreign_ir_name :: proc(g: ^Codegen, fn_name: string) -> (string, bool) {
    cs, ok := g.checked.functions[fn_name]
    if !ok { return "", false }
    fo, is_foreign := cs.origin.(Origin_Foreign)
    if !is_foreign { return "", false }
    ln := fo.link_name
    if ln == "" { ln = fn_name }
    return fmt.tprintf("@%s", ln), true
}

// Check if a function name is a foreign function.
is_foreign_fn :: proc(g: ^Codegen, fn_name: string) -> bool {
    cs, ok := g.checked.functions[fn_name]
    if !ok { return false }
    _, is_foreign := cs.origin.(Origin_Foreign)
    return is_foreign
}

// Get a fresh temporary: %1, %2, etc.
fresh_tmp :: proc(g: ^Codegen) -> string {
    g.tmp_counter += 1
    return fmt.tprintf("%%t%d", g.tmp_counter)
}

// Get a fresh label
fresh_label :: proc(g: ^Codegen, prefix: string) -> string {
    g.label_counter += 1
    return fmt.tprintf("%s%d", prefix, g.label_counter)
}

// Codegen-stage error: print a diagnostic and abort. Codegen runs only after
// type checking has passed, so reaching one of these sites is a compiler bug
// — a missed type checker case or an unimplemented codegen feature. Emitting
// broken IR and letting clang fail with a cryptic message hides the real
// cause. Pass `{}` as span when no source location is available.
codegen_fatal :: proc(g: ^Codegen, span: Span, format: string, args: ..any) -> ! {
    if span.file != "" {
        fmt.printf("%s Codegen error: ", span_loc(span))
    } else {
        fmt.print("Codegen error: ")
    }
    fmt.printf(format, ..args)
    fmt.println()
    os.exit(1)
}

// ---------------------------------------------------------------------------
// GEP / load / store helpers — reduce boilerplate across all codegen files
// ---------------------------------------------------------------------------

// Emit a GEP into a struct field: %tmp = getelementptr %StructType, ptr %base, i32 0, i32 <idx>
emit_field_gep :: proc(g: ^Codegen, llvm_type: string, base_ptr: string, field_idx: int) -> string {
    gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", gep, llvm_type, base_ptr, field_idx)
    return gep
}

// Load a value from a pointer: %tmp = load <ir_type>, ptr %src
emit_load :: proc(g: ^Codegen, ir_type: string, src_ptr: string) -> string {
    val := fresh_tmp(g)
    emit(g, "  %s = load %s, ptr %s", val, ir_type, src_ptr)
    return val
}

// GEP + load in one step: load a struct field by index
emit_field_load :: proc(g: ^Codegen, llvm_type: string, base_ptr: string, field_idx: int, ir_type: string) -> string {
    gep := emit_field_gep(g, llvm_type, base_ptr, field_idx)
    return emit_load(g, ir_type, gep)
}

// GEP + store in one step: store a value into a struct field by index
emit_field_store :: proc(g: ^Codegen, llvm_type: string, base_ptr: string, field_idx: int, ir_type: string, val: string) {
    gep := emit_field_gep(g, llvm_type, base_ptr, field_idx)
    emit(g, "  store %s %s, ptr %s", ir_type, val, gep)
}

// Copy all fields from src to dst (same struct type). Emits GEP+load+store per field.
emit_struct_copy :: proc(g: ^Codegen, sd: ^Scope_Body, llvm_type: string, src_ptr: string, dst_ptr: string) {
    for &field, fi in sd.fields {
        ft := field_ir_type(&field)
        val := emit_field_load(g, llvm_type, src_ptr, fi, ft)
        emit_field_store(g, llvm_type, dst_ptr, fi, ft, val)
    }
}

// Emit a printf call for a scalar value based on its IR type.
// Handles double, float (promoted), i1 (zext), ptr, and integers (sext to i64).
emit_printf_value :: proc(g: ^Codegen, val: string, ir_type: string) {
    switch ir_type {
    case "double":
        fmt_name, fmt_len := get_string_literal(g, "%g")
        fmt_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fmt_ptr, fmt_len, fmt_name)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, double %s)", fmt_ptr, val)
    case "float":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", ext, val)
        fmt_name, fmt_len := get_string_literal(g, "%g")
        fmt_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fmt_ptr, fmt_len, fmt_name)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, double %s)", fmt_ptr, ext)
    case "i1":
        fmt_name, fmt_len := get_string_literal(g, "%d")
        fmt_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fmt_ptr, fmt_len, fmt_name)
        ext := fresh_tmp(g)
        emit(g, "  %s = zext i1 %s to i32", ext, val)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, ext)
    case "ptr":
        fmt_name, fmt_len := get_string_literal(g, "%s")
        fmt_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fmt_ptr, fmt_len, fmt_name)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, ptr %s)", fmt_ptr, val)
    case:
        ext := fresh_tmp(g)
        emit(g, "  %s = sext %s %s to i64", ext, ir_type, val)
        fmt_name, fmt_len := get_string_literal(g, "%lld")
        fmt_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", fmt_ptr, fmt_len, fmt_name)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s)", fmt_ptr, ext)
    }
}

// ---------------------------------------------------------------------------
// Address chain — building and emitting
// ---------------------------------------------------------------------------

// Emit a single GEP instruction with multiple indices.
emit_multi_gep :: proc(g: ^Codegen, base_type: string, base_ptr: string, indices: []GEP_Index) -> string {
    gep := fresh_tmp(g)
    b: strings.Builder
    fmt.sbprintf(&b, "  %s = getelementptr %s, ptr %s", gep, base_type, base_ptr)
    for idx in indices {
        fmt.sbprintf(&b, ", %s %s", idx.width, idx.value)
    }
    emit_raw(g, strings.to_string(b))
    return gep
}

// Build an address chain from an expression tree. Returns false if the
// expression contains patterns the chain cannot handle (swizzle, slice index,
// VLA, function references, etc.) — caller should fall back to existing code.
build_address_chain :: proc(g: ^Codegen, expr: Expr) -> (Address_Chain, bool) {
    chain: Address_Chain

    // Walk the expression bottom-up, building the chain in reverse
    ok := build_chain_walk(g, expr, &chain)
    if !ok {
        return {}, false
    }

    return chain, true
}

// Recursive walk to build chain steps. Sets chain.base_* for the root,
// appends steps for each access level.
build_chain_walk :: proc(g: ^Codegen, expr: Expr, chain: ^Address_Chain) -> bool {
    // If the type checker rewrote this ident (e.g. namespace-match subject
    // shorthand → field access), follow the desugared expression as if it
    // were the original.
    if ident, ok := expr.(^Expr_Ident); ok && ident.desugared != nil {
        return build_chain_walk(g, ident.desugared, chain)
    }
    #partial switch e in expr {
    case ^Expr_Ident:
        // Base case: root of the chain
        if sv, ok := get_struct(g, e.name); ok {
            st, st_ok := lookup_struct(g, sv.struct_name)
            if !st_ok { return false }
            chain.base_ptr = sv.alloca
            chain.base_type = struct_llvm_name(sv.struct_name)
            chain.final_type = chain.base_type
            chain.final_kind = .Struct
            chain.struct_name = sv.struct_name
            return true
        }
        if av, ok := get_array(g, e.name); ok {
            chain.base_ptr = av.alloca
            chain.base_type = array_var_type(&av)
            chain.final_type = av.elem_type
            chain.final_kind = .Array
            chain.array_cap = av.capacity
            chain.array_elem = av.elem_type
            return true
        }
        // Slice as chain base: header lives at sv.alloca; data and cap get
        // loaded when the next step is an index (Step_Slice_Index). A chain
        // that ends *at* the slice (no further indexing) doesn't need this
        // base — the existing slice-header read paths handle it.
        if sl, ok := get_slice(g, e.name); ok {
            chain.base_ptr = sl.alloca
            chain.base_type = ""             // slice header type isn't used for stepping
            chain.final_type = sl.elem_type
            chain.final_kind = .Slice
            chain.array_elem = sl.elem_type
            chain.array_cap = 0              // unused; cap is dynamic
            return true
        }
        // Pointer-to-struct: auto-deref
        if pt, pt_ok := e.type_.(^Type_Ptr); pt_ok {
            if sd := as_struct_body(pt.elem); sd != nil {
                alloca, sc_ok := get_scalar(g, e.name)
                if !sc_ok { return false }
                // Load pointer and null check during emission
                loaded := emit_load(g, "ptr", alloca)
                emit_null_check(g, loaded, e.name, e.span)
                chain.base_ptr = loaded
                chain.base_type = struct_llvm_name(sd.name)
                chain.final_type = chain.base_type
                chain.final_kind = .Struct
                chain.struct_name = sd.name
                return true
            }
        }
        return false

    case ^Expr_Field_Access:
        // Recurse on inner expression
        if !build_chain_walk(g, e.expr, chain) { return false }

        // The current final must be a struct to access a field
        if chain.final_kind != .Struct { return false }
        st, st_ok := lookup_struct(g, chain.struct_name)
        if !st_ok {
            return false
        }
        llvm_type := struct_llvm_name(chain.struct_name)

        // Check for swizzle — bail
        if av, av_ok := get_array(g, ""); false {
            _ = av; _ = av_ok  // unreachable, just suppress
        }

        // Find the field
        idx := struct_field_index(st, e.field)
        if idx >= 0 {
            f := &st.fields[idx]
            ft := field_ir_type(f)

            append(&chain.steps, Step_Field{
                llvm_type = llvm_type,
                field_idx = idx,
                field_def = f,
            })

            // Determine what this field resolves to
            acap := field_array_cap(f)
            if acap > 0 {
                // Array field
                aelem := field_array_elem(f)
                chain.final_type = fmt.tprintf("[%d x %s]", acap, aelem)
                chain.final_kind = .Array
                chain.array_cap = acap
                chain.array_elem = aelem
                chain.struct_name = ""
                return true
            }
            if strings.has_prefix(ft, "%class.") {
                // Nested struct field
                inner_name := ft[len("%class."):]
                chain.final_type = ft
                chain.final_kind = .Struct
                chain.struct_name = inner_name
                return true
            }
            if strings.has_prefix(ft, "{ ") {
                // Slice OR partial-array field — both layouts share the first
                // 24 bytes ({len, cap, ptr}), so the same chain end-state and
                // subsequent .len/.cap/.ptr access work for both.
                chain.final_type = ft
                chain.final_kind = .Slice
                chain.struct_name = ""
                chain.array_cap = 0
                if sl, sl_ok := distinct_base(f.type_).(^Type_Slice); sl_ok {
                    chain.array_elem = llvm_type_from_checker(sl.elem)
                } else if pa, pa_ok := distinct_base(f.type_).(^Type_Partial_Array); pa_ok {
                    chain.array_elem = llvm_type_from_checker(pa.elem)
                } else {
                    return false
                }
                return true
            }
            // Pointer-to-struct field: emit a deref step so subsequent steps
            // operate on the pointee's storage. Lets `obj.ptr_field.inner = X`
            // and the read counterpart flow through the same chain mechanism
            // as inline struct fields.
            if pt, pt_ok := f.type_.(^Type_Ptr); pt_ok {
                if sd := as_struct_body(pt.elem); sd != nil {
                    inner_key := struct_key(sd)
                    inner_llvm := struct_llvm_name(inner_key)
                    append(&chain.steps, Step_Deref{
                        name_hint   = e.field,
                        span        = e.span,
                        result_type = inner_llvm,
                    })
                    chain.final_type = inner_llvm
                    chain.final_kind = .Struct
                    chain.struct_name = inner_key
                    return true
                }
            }
            // Scalar field
            chain.final_type = ft
            chain.final_kind = .Scalar
            chain.struct_name = ""
            chain.elem_signed = field_is_signed(f)
            return true
        }

        // Try using-promoted field
        up, up_ok := resolve_using_field(g, st, e.field)
        if up_ok {
            append(&chain.steps, Step_Field{
                llvm_type = llvm_type,
                field_idx = up.outer_index,
                field_def = &st.fields[up.outer_index],
            })
            append(&chain.steps, Step_Field{
                llvm_type = struct_llvm_name(struct_key(up.inner_st)),
                field_idx = up.inner_index,
                field_def = &up.inner_st.fields[up.inner_index],
            })
            // Mirror the regular-field branch above: a using-promoted field
            // can itself be an array/struct/slice, and subsequent steps in
            // the chain need to keep drilling into it.
            inner_f := &up.inner_st.fields[up.inner_index]
            acap := field_array_cap(inner_f)
            if acap > 0 {
                aelem := field_array_elem(inner_f)
                chain.final_type = fmt.tprintf("[%d x %s]", acap, aelem)
                chain.final_kind = .Array
                chain.array_cap = acap
                chain.array_elem = aelem
                chain.struct_name = ""
                return true
            }
            if strings.has_prefix(up.inner_ir_type, "%class.") {
                inner_name := up.inner_ir_type[len("%class."):]
                chain.final_type = up.inner_ir_type
                chain.final_kind = .Struct
                chain.struct_name = inner_name
                return true
            }
            if strings.has_prefix(up.inner_ir_type, "{ ") {
                chain.final_type = up.inner_ir_type
                chain.final_kind = .Slice
                chain.struct_name = ""
                chain.array_cap = 0
                if sl, sl_ok := distinct_base(inner_f.type_).(^Type_Slice); sl_ok {
                    chain.array_elem = llvm_type_from_checker(sl.elem)
                } else {
                    return false
                }
                return true
            }
            chain.final_type = up.inner_ir_type
            chain.final_kind = .Scalar
            chain.struct_name = ""
            chain.elem_signed = up.inner_signed
            return true
        }

        return false  // field not found

    case ^Expr_Index:
        // Recurse on inner expression
        if !build_chain_walk(g, e.expr, chain) { return false }

        // Slice index: chain.array_elem holds the slice elem type; cap is runtime.
        if chain.final_kind == .Slice {
            elem_ir := chain.array_elem
            name_hint := "slice"
            if id, id_ok := e.expr.(^Expr_Ident); id_ok { name_hint = id.name }
            append(&chain.steps, Step_Slice_Index{
                elem_type  = elem_ir,
                index_expr = e.index,
                name_hint  = name_hint,
                span       = e.span,
            })
            // Determine post-index kind from elem type (mirrors the array path).
            if strings.has_prefix(elem_ir, "%class.") {
                inner_name := elem_ir[len("%class."):]
                chain.final_type = elem_ir
                chain.final_kind = .Struct
                chain.struct_name = inner_name
                chain.array_cap = 0
                chain.array_elem = ""
            } else if inner_cap, inner_elem, is_nested := parse_array_ir_type(elem_ir); is_nested {
                chain.final_type = elem_ir
                chain.final_kind = .Array
                chain.array_cap = inner_cap
                chain.array_elem = inner_elem
                chain.struct_name = ""
            } else {
                chain.final_type = elem_ir
                chain.final_kind = .Scalar
                chain.struct_name = ""
                chain.array_cap = 0
                chain.array_elem = ""
            }
            return true
        }

        // Can only index into arrays
        if chain.final_kind != .Array { return false }
        // Don't handle VLA indexing
        if chain.array_cap == 0 { return false }

        append(&chain.steps, Step_Index{
            array_type = fmt.tprintf("[%d x %s]", chain.array_cap, chain.array_elem),
            elem_type  = chain.array_elem,
            index_expr = e.index,
            capacity   = chain.array_cap,
            name_hint  = "array",
            span       = e.span,
        })

        // After indexing, determine the element type
        elem_ir := chain.array_elem
        if strings.has_prefix(elem_ir, "%class.") {
            inner_name := elem_ir[len("%class."):]
            chain.final_type = elem_ir
            chain.final_kind = .Struct
            chain.struct_name = inner_name
            chain.array_cap = 0
            chain.array_elem = ""
        } else if inner_cap, inner_elem, is_nested := parse_array_ir_type(elem_ir); is_nested {
            chain.final_type = elem_ir
            chain.final_kind = .Array
            chain.array_cap = inner_cap
            chain.array_elem = inner_elem
            chain.struct_name = ""
        } else {
            chain.final_type = elem_ir
            chain.final_kind = .Scalar
            chain.struct_name = ""
            chain.array_cap = 0
            chain.array_elem = ""
        }
        return true
    }

    return false
}

// Emit GEP(s) from the chain. Returns pointer to the final element.
// Consecutive offset steps are merged into a single multi-index GEP.
// Deref steps flush the current GEP, load the pointer, and start fresh.
emit_address_chain :: proc(g: ^Codegen, chain: ^Address_Chain) -> string {
    current_ptr := chain.base_ptr
    current_type := chain.base_type

    indices: [dynamic]GEP_Index
    append(&indices, GEP_Index{"i32", "0"})  // leading zero to enter aggregate

    for &step in chain.steps {
        switch s in step {
        case Step_Field:
            append(&indices, GEP_Index{"i32", fmt.tprintf("%d", s.field_idx)})

        case Step_Index:
            // Evaluate index, bounds check (must happen before the GEP uses it)
            idx_raw := gen_expr(g, s.index_expr)
            idx := ensure_i64(g, idx_raw, s.index_expr)
            emit_bounds_check(g, idx, fmt.tprintf("%d", s.capacity), s.name_hint, s.span)
            append(&indices, GEP_Index{"i64", idx})

        case Step_Slice_Index:
            // Flush any pending GEP first — current_ptr must point at the
            // slice header before we read its fields.
            if len(indices) > 1 {
                current_ptr = emit_multi_gep(g, current_type, current_ptr, indices[:])
            }
            // current_ptr: { ptr, i64 len, i64 cap }*
            data_gep := fresh_tmp(g)
            emit_slice_gep(g, data_gep, current_ptr, SLICE.ptr)
            data_ptr := fresh_tmp(g)
            emit(g, "  %s = load ptr, ptr %s", data_ptr, data_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, current_ptr, SLICE.cap)
            cap_val := fresh_tmp(g)
            emit_typed_load_cap(g, cap_val, cap_gep)
            idx_raw := gen_expr(g, s.index_expr)
            idx := ensure_i64(g, idx_raw, s.index_expr)
            emit_bounds_check(g, idx, cap_val, s.name_hint, s.span)
            elem_ptr := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i64 %s", elem_ptr, s.elem_type, data_ptr, idx)
            current_ptr = elem_ptr
            current_type = s.elem_type
            clear(&indices)
            append(&indices, GEP_Index{"i32", "0"})  // leading zero for subsequent field/index into the element

        case Step_Deref:
            // Flush current GEP segment
            if len(indices) > 1 {
                current_ptr = emit_multi_gep(g, current_type, current_ptr, indices[:])
            }
            // Load pointer
            current_ptr = emit_load(g, "ptr", current_ptr)
            emit_null_check(g, current_ptr, s.name_hint, s.span)
            // Reset for next segment
            clear(&indices)
            append(&indices, GEP_Index{"i32", "0"})
            if s.result_type != "" {
                current_type = s.result_type
            }
        }
    }

    // Flush remaining segment
    if len(indices) > 1 {
        current_ptr = emit_multi_gep(g, current_type, current_ptr, indices[:])
    }

    return current_ptr
}

// Generate the IR name for a user-defined function.
// Names are already flat (e.g., "sdl_Init") from flatten_for_codegen.
mara_fn_name :: proc(g: ^Codegen, name: string) -> string {
    if name == "main" { return "@main" }
    // `#expose fun foo` → unmangled `@foo` so a DLL host can call
    // GetProcAddress("foo") directly without knowing Mara's flat-naming rule.
    // Mara-internal call sites resolve to the same symbol, so callers in the
    // same package stay wired up.
    if cs, ok := g.checked.functions[name]; ok && cs.ast != nil && cs.ast.is_exposed {
        return fmt.tprintf("@%s", cs.ast.name)
    }
    // IR symbols are prefixed with "mara_" to namespace them against system
    // libraries. flat names from stdlib modules (`mara.math`) already include
    // it via make_flat_name's dot→underscore conversion; user-module flats
    // like `camera_init` get prepended here.
    if strings.has_prefix(name, "mara_") { return fmt.tprintf("@%s", name) }
    return fmt.tprintf("@mara_%s", name)
}

// Get the resolved flat name for a call expression.
// Uses resolved_func annotation if available, otherwise falls back to e.name.
call_resolved_name :: proc(e: ^Expr_Call) -> string {
    if rf, rf_ok := e.resolved_func.?; rf_ok {
        return rf.name
    }
    return e.name
}

// Derive Fun_Info from a Checked_Scope, with caching.
// Returns the info and true if found, or zero value and false if not.
lookup_fun_info :: proc(g: ^Codegen, fn_name: string) -> (Fun_Info, bool) {
    // Check cache first
    if cached, cached_ok := g.fun_info_cache[fn_name]; cached_ok {
        return cached, true
    }

    // All functions are in checked.functions with flat keys (after flatten_for_codegen)
    cf, found := g.checked.functions[fn_name]
    if !found { return {}, false }

    info := Fun_Info{}

    // Return type: struct/array/tuple/slice returns use void + sret convention
    if sd := as_struct_body(cf.return_type); sd != nil {
        info.ret_type = "void"
        info.ret_struct = sd.name
    } else if fa, fa_ok := cf.return_type.(^Type_Fixed_Array); fa_ok {
        info.ret_type = "void"
        info.ret_array_cap = fa.size
        info.ret_array_elem = llvm_type_from_checker(fa.elem)
    } else if tup, tup_ok := cf.return_type.(^Type_Tuple); tup_ok {
        info.ret_type = "void"
        info.ret_tuple = tup
    } else if sl, sl_ok := cf.return_type.(^Type_Slice); sl_ok {
        info.ret_type = "void"
        info.ret_slice_elem = llvm_type_from_checker(sl.elem)
    } else if cf.return_type == nil || is_untyped(cf.return_type) {
        info.ret_type = "void"
    } else {
        info.ret_type = llvm_type_from_checker(cf.return_type)
    }

    // Parameter types
    for p in cf.params {
        if sd := as_struct_body(p.type_); sd != nil {
            append(&info.param_types, "ptr")
            append(&info.param_structs, sd.name)
        } else if ut, ut_ok := p.type_.(^Type_Union); ut_ok {
            append(&info.param_types, "ptr")
            append(&info.param_structs, union_key(ut))
        } else if _, pa_ok := partial_through_distinct_and_ptr(p.type_); pa_ok {
            // Partial-array param: same fat-pointer-ref ABI as slices. Mark
            // with SLICE_IR_TYPE so the call-site uses gen_slice_param_arg,
            // which passes a pointer to the partial-array's header. The
            // function declaration receives `ptr` (set in codegen_fn.odin).
            append(&info.param_types, SLICE_IR_TYPE)
            append(&info.param_structs, "")
        } else {
            append(&info.param_types, llvm_type_from_checker(p.type_))
            append(&info.param_structs, "")
        }
    }

    // Escape analysis: functions returning a struct with slice fields, where
    // the slices are filled by local fixed-arrays in a struct literal return.
    // The local backing storage is reserved inside the caller's sret region
    // so the returned slice pointers stay valid past the function's frame.
    if info.ret_struct != "" {
        analyze_escape_locals(g, &cf, &info)
        info.uses_struct_nrvo = find_nrvo_candidate(cf.body[:]) != ""
    }

    // Cache and return
    g.fun_info_cache[fn_name] = info
    return info, true
}

// Walk the function body for one return like `return Foo{a, b}` where Foo has
// slice fields and a/b are local fixed-array idents. Record each escaping
// local's shape; the caller will allocate one sibling buffer per local and
// pass it as a hidden trailing arg.
analyze_escape_locals :: proc(g: ^Codegen, cf: ^Checked_Scope, info: ^Fun_Info) {
    sd, sd_ok := lookup_struct(g, info.ret_struct)
    if !sd_ok { return }
    // Check there's at least one slice field to escape into.
    has_slice_field := false
    for &f in sd.fields {
        if _, ok := f.type_.(^Type_Slice); ok { has_slice_field = true; break }
    }
    if !has_slice_field { return }

    // Find the first `return StructLit{...}` statement in the (desugared) body.
    lit := find_return_struct_literal(cf.body[:])
    if lit == nil { return }

    // Index local declarations by name so we can look up their fixed-array
    // shapes when they appear as slice fillers.
    local_decls := make(map[string]^Stmt_Assign)
    defer delete(local_decls)
    collect_local_decls(cf.body[:], &local_decls)

    for field, pos in lit.fields {
        field_idx: int
        if lit.positional {
            if pos >= len(sd.fields) { break }
            field_idx = pos
        } else {
            field_idx = struct_field_index(sd, field.name)
            if field_idx < 0 { continue }
        }
        // Only slice fields are candidates for escape.
        sd_field := &sd.fields[field_idx]
        if _, is_slice := sd_field.type_.(^Type_Slice); !is_slice { continue }
        // Value must be a bare local-array reference.
        ident, is_ident := field.value.(^Expr_Ident)
        if !is_ident { continue }
        decl, has_decl := local_decls[ident.name]
        if !has_decl { continue }
        fa, is_fa := decl.var_type.(^Type_Fixed_Array)
        if !is_fa { continue }

        elem_ir := llvm_type_from_checker(fa.elem)
        elem_sz := elem_byte_size(elem_ir, g.checked)
        utf8 := false
        if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }

        append(&info.escape_locals, Escape_Local{
            name         = ident.name,
            cap          = fa.size,
            elem_type    = elem_ir,
            elem_size    = elem_sz,
            is_utf8      = utf8,
            has_sentinel = fa.has_sentinel,
            sentinel     = fa.sentinel,
        })
    }
}

// Find the first `return StructLit{...}` in a (possibly Stmt_Decl-wrapped)
// statement list. Returns nil if none.
find_return_struct_literal :: proc(stmts: []Stmt) -> ^Expr_Struct_Literal {
    for s in stmts {
        if decl, ok := s.(^Stmt_Decl); ok {
            if got := find_return_struct_literal(decl.checked[:]); got != nil { return got }
            continue
        }
        ret, is_ret := s.(Stmt_Return)
        if !is_ret { continue }
        if len(ret.values) == 0 { continue }
        if lit, lit_ok := ret.values[0].(^Expr_Struct_Literal); lit_ok { return lit }
    }
    return nil
}

// Walk a statement list (descending into Stmt_Decl.checked) and record every
// Stmt_Assign that introduces a typed local. Used to look up the type of an
// ident referenced from a returned struct literal.
collect_local_decls :: proc(stmts: []Stmt, out: ^map[string]^Stmt_Assign) {
    for s in stmts {
        if decl, ok := s.(^Stmt_Decl); ok {
            collect_local_decls(decl.checked[:], out)
            continue
        }
        if assign, ok := s.(^Stmt_Assign); ok {
            if assign.name != "" && assign.var_type != nil {
                out[assign.name] = assign
            }
        }
    }
}

// True if `t` is a struct type whose fields include any slice. Used to gate
// pool allocation on sized slice decls — `[]T(N)` only needs a pool when
// elements carry slice fields whose backing must outlive a transient call.
struct_has_slice_fields :: proc(t: Type) -> bool {
    sd := as_struct_body(distinct_base(t))
    if sd == nil { return false }
    for &f in sd.fields {
        if _, ok := f.type_.(^Type_Slice); ok { return true }
    }
    return false
}

// Compute the bytes needed by a callee's escape locals (sum across all locals,
// element-bytes × cap). Used to size the pool of a sized slice of slice-bearing
// structs whose appends carve from that pool.
escape_total_bytes :: proc(info: ^Fun_Info) -> int {
    total := 0
    for &el in info.escape_locals {
        alloc_cap := el.cap
        if el.has_sentinel { alloc_cap += 1 }
        total += alloc_cap * el.elem_size
    }
    return total
}

// Walk a statement list and sum escape bytes contributed by every
// `&slice_name + call(...)` append (or `slice_name[i] = call(...)`).
// Each call resolves to its Fun_Info; we sum escape_total_bytes per match.
// Loops: counted once (TODO: multiply by bounded loop counts). Unbounded
// loops over a pool-backed slice are bounded by the slice's cap so the
// loop count is implicitly capped.
sum_pool_appends :: proc(g: ^Codegen, stmts: []Stmt, slice_name: string) -> int {
    total := 0
    for s in stmts {
        total += sum_pool_appends_stmt(g, s, slice_name)
    }
    return total
}

sum_pool_appends_stmt :: proc(g: ^Codegen, s: Stmt, slice_name: string) -> int {
    if call_stmt, ok := s.(Stmt_Call); ok {
        return sum_pool_appends_expr(g, call_stmt.expr, slice_name)
    }
    if assign, ok := s.(^Stmt_Assign); ok {
        // `slice_name[i] = call_with_escape()` is also a pool-affecting write.
        if assign.target != nil {
            if ix, ix_ok := assign.target.(^Expr_Index); ix_ok {
                if ident, id_ok := ix.expr.(^Expr_Ident); id_ok && ident.name == slice_name {
                    if call, call_ok := assign.value.(^Expr_Call); call_ok {
                        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok {
                            return escape_total_bytes(&info)
                        }
                    }
                }
            }
        }
        return sum_pool_appends_expr(g, assign.value, slice_name)
    }
    if decl, ok := s.(^Stmt_Decl); ok {
        return sum_pool_appends(g, decl.checked[:], slice_name)
    }
    if if_stmt, ok := s.(^Stmt_If); ok {
        return sum_pool_appends(g, if_stmt.body[:], slice_name) +
               sum_pool_appends(g, if_stmt.else_body[:], slice_name)
    }
    if for_stmt, ok := s.(^Stmt_For); ok {
        // TODO: multiply by static loop bound when known.
        return sum_pool_appends(g, for_stmt.body[:], slice_name)
    }
    if match_stmt, ok := s.(^Stmt_Match); ok {
        max := 0
        for &arm in match_stmt.arms {
            n := sum_pool_appends(g, arm.body[:], slice_name)
            if n > max { max = n }
        }
        return max
    }
    return 0
}

sum_pool_appends_expr :: proc(g: ^Codegen, e: Expr, slice_name: string) -> int {
    if e == nil { return 0 }
    bin, is_bin := e.(^Expr_Binary)
    if !is_bin || bin.op != .Plus { return 0 }
    // `&slice_name + call_with_escape` — match the address-of pattern.
    un, is_un := bin.left.(^Expr_Unary)
    if !is_un || un.op != .Ampersand { return 0 }
    ident, is_ident := un.operand.(^Expr_Ident)
    if !is_ident || ident.name != slice_name { return 0 }
    call, is_call := bin.right.(^Expr_Call)
    if !is_call { return 0 }
    info, info_ok := lookup_fun_info(g, call_resolved_name(call))
    if !info_ok { return 0 }
    return escape_total_bytes(&info)
}

// Format a span as "[file:line:col]" or "[line:col]" prefix for error messages
span_loc :: proc(span: Span) -> string {
    return fmt.tprintf("[%s]", format_location(span.file, span.line, span.col))
}

// Helper: extract the alloca name (e.g., "%r_36") from a line like "  %r_36 = alloca i32"
extract_alloca_name :: proc(line: string) -> string {
    trimmed := strings.trim_left_space(line)
    eq_pos := strings.index(trimmed, " = alloca ")
    if eq_pos < 0 { return "" }
    return trimmed[:eq_pos]
}

// Helper: extract the alloca type (e.g., "i32") from a line like "  %r_36 = alloca i32"
extract_alloca_type :: proc(line: string) -> string {
    trimmed := strings.trim_left_space(line)
    marker := " = alloca "
    eq_pos := strings.index(trimmed, marker)
    if eq_pos < 0 { return "" }
    return trimmed[eq_pos + len(marker):]
}

// Write a single line to the output, handling alloca hoisting.
emit_line :: proc(g: ^Codegen, line: string) {
    if g.hoist_allocas {
        if strings.contains(line, "= alloca ") {
            // Skip duplicate allocas (e.g., same var declared in both if and else branches)
            name := extract_alloca_name(line)
            if name != "" && name in g.emitted_allocas {
                return  // duplicate — already emitted
            }
            if name != "" { g.emitted_allocas[name] = extract_alloca_type(line) }
            strings.write_string(&g.alloca_buf, line)
            strings.write_byte(&g.alloca_buf, '\n')
        } else {
            strings.write_string(&g.body_buf, line)
            strings.write_byte(&g.body_buf, '\n')
        }
        return
    }
    strings.write_string(&g.out, line)
    strings.write_byte(&g.out, '\n')
}

emit :: proc(g: ^Codegen, s: string, args: ..any) {
    if len(args) == 0 {
        emit_line(g, s)
    } else {
        emit_line(g, fmt.tprintf(s, ..args))
    }
}

emit_raw :: proc(g: ^Codegen, s: string) {
    emit_line(g, s)
}

// Begin alloca hoisting: emit() will redirect allocas to alloca_buf, body code to body_buf.
begin_alloca_hoist :: proc(g: ^Codegen) {
    strings.builder_reset(&g.alloca_buf)
    strings.builder_reset(&g.body_buf)
    g.hoist_allocas = true
}

// End alloca hoisting: flush hoisted allocas first, then body code, into g.out.
end_alloca_hoist :: proc(g: ^Codegen) {
    g.hoist_allocas = false
    alloca_str := strings.to_string(g.alloca_buf)
    if len(alloca_str) > 0 {
        strings.write_string(&g.out, alloca_str)
    }
    body_str := strings.to_string(g.body_buf)
    if len(body_str) > 0 {
        strings.write_string(&g.out, body_str)
    }
}

// ---------------------------------------------------------------------------
// Scope save/restore helpers — lightweight key snapshots instead of full clones
// ---------------------------------------------------------------------------

// Snapshot the current variable bindings. After a branch, call restore to:
//   - remove any variables that were added during the branch, AND
//   - restore the original entry for any variable that was overwritten/shadowed.
// The full entry (not just the key) is captured so a match arm can rebind an
// outer name (e.g. shadow a Union_Var with a Struct_Var) and have the original
// Union_Var come back when the arm ends.
Var_Scope_Snapshot :: struct {
    saved: map[string]Var_Entry,
}

save_var_scope :: proc(g: ^Codegen) -> Var_Scope_Snapshot {
    snap: Var_Scope_Snapshot
    snap.saved = make(map[string]Var_Entry)
    for k, v in g.all_vars { snap.saved[k] = v }
    return snap
}

restore_var_scope :: proc(g: ^Codegen, snap: ^Var_Scope_Snapshot) {
    // Remove keys that didn't exist at snapshot time.
    keys_to_remove: [dynamic]string
    for k, _ in g.all_vars {
        if !(k in snap.saved) {
            append(&keys_to_remove, k)
        }
    }
    for k in keys_to_remove {
        delete_key(&g.all_vars, k)
    }
    // Restore overwritten entries.
    for k, v in snap.saved {
        g.all_vars[k] = v
    }
}

// ---------------------------------------------------------------------------
// Var_Entry accessors — typed access to the unified variable registry
// ---------------------------------------------------------------------------

get_scalar :: proc(g: ^Codegen, name: string) -> (string, bool) {
    if entry, ok := g.all_vars[name]; ok {
        if sv, sv_ok := entry.(Scalar_Var); sv_ok { return sv.alloca, true }
    }
    return "", false
}

get_array :: proc(g: ^Codegen, name: string) -> (Array_Var, bool) {
    if entry, ok := g.all_vars[name]; ok {
        if av, av_ok := entry.(Array_Var); av_ok { return av, true }
    }
    return {}, false
}

get_struct :: proc(g: ^Codegen, name: string) -> (Struct_Var, bool) {
    if entry, ok := g.all_vars[name]; ok {
        if sv, sv_ok := entry.(Struct_Var); sv_ok { return sv, true }
    }
    return {}, false
}

get_union :: proc(g: ^Codegen, name: string) -> (Union_Var, bool) {
    if entry, ok := g.all_vars[name]; ok {
        if uv, uv_ok := entry.(Union_Var); uv_ok { return uv, true }
    }
    return {}, false
}

get_slice :: proc(g: ^Codegen, name: string) -> (Slice_Var, bool) {
    if entry, ok := g.all_vars[name]; ok {
        if sv, sv_ok := entry.(Slice_Var); sv_ok { return sv, true }
    }
    return {}, false
}

is_scalar :: proc(g: ^Codegen, name: string) -> bool {
    if entry, ok := g.all_vars[name]; ok {
        _, sv_ok := entry.(Scalar_Var)
        return sv_ok
    }
    return false
}

is_array :: proc(g: ^Codegen, name: string) -> bool {
    if entry, ok := g.all_vars[name]; ok {
        _, av_ok := entry.(Array_Var)
        return av_ok
    }
    return false
}

// ---------------------------------------------------------------------------
// Temp result helpers — typed replacements for magic __call_result etc.
// ---------------------------------------------------------------------------

// Array-returning call: set by gen_call, claimed by Stmt_Assign / gen_array_assign / gen_return.
set_call_result :: proc(g: ^Codegen, av: Array_Var) {
    g.temp_call_result = av
}

claim_call_result :: proc(g: ^Codegen) -> (Array_Var, bool) {
    if av, ok := g.temp_call_result.?; ok {
        g.temp_call_result = nil
        return av, true
    }
    return {}, false
}

// Field access on aggregate: set by gen_field_access, claimed by index/concat/len/etc.
set_field_result :: proc(g: ^Codegen, entry: Var_Entry) {
    g.temp_field_result = entry
}

claim_field_array :: proc(g: ^Codegen) -> (Array_Var, bool) {
    if entry, ok := g.temp_field_result.?; ok {
        if av, av_ok := entry.(Array_Var); av_ok {
            g.temp_field_result = nil
            return av, true
        }
    }
    return {}, false
}

claim_field_struct :: proc(g: ^Codegen) -> (Struct_Var, bool) {
    if entry, ok := g.temp_field_result.?; ok {
        if sv, sv_ok := entry.(Struct_Var); sv_ok {
            g.temp_field_result = nil
            return sv, true
        }
    }
    return {}, false
}

claim_field_slice :: proc(g: ^Codegen) -> (Slice_Var, bool) {
    if entry, ok := g.temp_field_result.?; ok {
        if sv, sv_ok := entry.(Slice_Var); sv_ok {
            g.temp_field_result = nil
            return sv, true
        }
    }
    return {}, false
}

clear_field_result :: proc(g: ^Codegen) {
    g.temp_field_result = nil
}

// Multi-component swizzle: set by gen_swizzle_read_multi, claimed by Stmt_Assign / gen_array_assign.
set_swizzle_result :: proc(g: ^Codegen, av: Array_Var) {
    g.temp_swizzle_result = av
}

claim_swizzle_result :: proc(g: ^Codegen) -> (Array_Var, bool) {
    if av, ok := g.temp_swizzle_result.?; ok {
        g.temp_swizzle_result = nil
        return av, true
    }
    return {}, false
}

// Get the LLVM array type string for an Array_Var
array_var_type :: proc(av: ^Array_Var) -> string {
    alloc_cap := av.capacity
    if av.has_sentinel { alloc_cap += 1 }
    return fmt.tprintf("[%d x %s]", alloc_cap, av.elem_type)
}

// Usable capacity: for utf8 arrays, reserve the last byte for the null terminator.
usable_cap :: proc(av: ^Array_Var) -> int {
    if av.is_utf8 {
        return av.capacity - 1
    }
    return av.capacity
}

// Codegen key for a struct type — names are already flat after flatten_for_codegen.
struct_key_fun :: proc(st: ^Type_Scope) -> string {
    return st.name
}

struct_key_sd :: proc(sd: ^Scope_Body) -> string {
    return sd.name
}

struct_key :: proc { struct_key_fun, struct_key_sd }

// Codegen key for an enum type.
enum_key :: proc(et: ^Type_Enum) -> string {
    return et.name
}

// Codegen key for a union type.
union_key :: proc(ut: ^Type_Union) -> string {
    return ut.name
}

// Get the LLVM type name for a struct, e.g. "%class.Point"
struct_llvm_name :: proc(key: string) -> string {
    return fmt.tprintf("%%class.%s", key)
}

// Look up a struct from checked data (returns the Scope_Body from either the structs or funs table).
lookup_struct :: proc(g: ^Codegen, name: string) -> (^Scope_Body, bool) {
    if ss, ss_ok := g.checked.table.structs[name]; ss_ok {
        return &ss.sd, true
    }
    if sf, sf_ok := g.checked.table.funs[name]; sf_ok {
        return &sf.sd, true
    }
    return nil, false
}

// Get the LLVM field index of a named field. Returns -1 if not found.
struct_field_index_sd :: proc(st: ^Scope_Body, field_name: string) -> int {
    for _, i in st.fields {
        if st.fields[i].name == field_name { return i }
    }
    return -1
}

struct_field_index_fun :: proc(st: ^Type_Scope, field_name: string) -> int {
    return struct_field_index_sd(&st.sd, field_name)
}

struct_field_index :: proc { struct_field_index_sd, struct_field_index_fun }

// Get the LLVM IR type string for a struct field.
field_ir_type :: proc(f: ^Struct_Type_Field) -> string {
    return llvm_type_from_checker(f.type_)
}

// Check if a struct field's type is signed.
field_is_signed :: proc(f: ^Struct_Type_Field) -> bool {
    if n, n_ok := f.type_.(Type_Numeric); n_ok {
        return n.kind == .Signed
    }
    return true // default signed for int, etc.
}

// Get array capacity for a field (0 if not a fixed-array field).
field_array_cap :: proc(f: ^Struct_Type_Field) -> int {
    if fa, fa_ok := distinct_base(f.type_).(^Type_Fixed_Array); fa_ok {
        return fa.size
    }
    return 0
}

// Get LLVM element type for an array field ("" if not an array).
field_array_elem :: proc(f: ^Struct_Type_Field) -> string {
    if fa, fa_ok := distinct_base(f.type_).(^Type_Fixed_Array); fa_ok {
        return llvm_type_from_checker(fa.elem)
    }
    return ""
}

// Get the LLVM type name for a union, e.g. "%union.Shape"
union_llvm_name :: proc(ukey: string) -> string {
    return fmt.tprintf("%%union.%s", ukey)
}

// Get the IR type for a union's tag field
union_tag_ir_type :: proc(ut: ^Type_Union) -> string {
    if ut.tag_type != "" {
        return tag_type_to_ir(ut.tag_type)
    }
    return "i64"
}

// True when the union qualifies for niche layout: exactly two variants,
// one with no fields (the "None" case) and one with a single pointer field
// (the "Some" case). For such unions, the in-memory representation is just
// a pointer — null for None, the live pointer for Some — instead of the
// generic tag+payload form. The shape detection is structural, so any
// user-defined union matching it gets the optimization too, not just
// stdlib Maybe.
is_niche_layout :: proc(g: ^Codegen, ut: ^Type_Union) -> bool {
    if len(ut.variants) != 2 { return false }
    has_empty := false
    has_ptr   := false
    for vname in ut.variants {
        vst_name, ok := ut.variant_structs[vname]
        if !ok { return false }
        sd, sd_ok := lookup_struct(g, vst_name)
        if !sd_ok { return false }
        switch len(sd.fields) {
        case 0:
            has_empty = true
        case 1:
            if _, is_ptr := sd.fields[0].type_.(^Type_Ptr); is_ptr {
                has_ptr = true
            } else {
                return false
            }
        case:
            return false
        }
    }
    return has_empty && has_ptr
}

// For a niche-laid-out union, returns the variant name carrying the pointer
// field (the "Some" case) and the empty-payload variant (the "None" case).
// Caller must have already verified is_niche_layout.
niche_variants :: proc(g: ^Codegen, ut: ^Type_Union) -> (some_name: string, none_name: string) {
    for vname in ut.variants {
        vst_name := ut.variant_structs[vname]
        if sd, ok := lookup_struct(g, vst_name); ok {
            if len(sd.fields) == 1 {
                some_name = vname
            } else if len(sd.fields) == 0 {
                none_name = vname
            }
        }
    }
    return
}

// Convert a Mara tag_type string (e.g. "u32", "i16") to LLVM IR integer type.
tag_type_to_ir :: proc(tag: string) -> string {
    switch tag {
    case "i8", "u8":   return "i8"
    case "i16", "u16": return "i16"
    case "i32", "u32": return "i32"
    case "i64", "u64": return "i64"
    }
    panic(fmt.tprintf("tag_type_to_ir: unknown tag type '%s'", tag))
}

llvm_type_from_checker :: proc(t: Type) -> string {
    switch v in t {
    case Type_Int:          return "i64"
    case Type_F64:          return "double"
    case Type_Infer_Int:    return "i64"    // default when no context
    case Type_Infer_Float:  return "double" // default when no context
    case Type_Numeric:
        switch v.kind {
        case .Signed, .Unsigned:
            // bits=0 → word-sized (usize/isize). Read the module-local flag
            // set by generate_program — wasm32 → i32, x86-64 → i64.
            if v.bits == 0 { return "i32" if word_size_is_32 else "i64" }
            return fmt.tprintf("i%d", v.bits)
        case .Float:
            if v.bits == 32 { return "float" }
            return "double"
        }
    case Type_Bool:         return "i1"
    case Type_C8:           return "i8"
    case Type_Utf8:         return "i8"
    case Type_Byte:         return "i8"
    case Type_CString:      return "ptr"
    case ^Type_Ptr:         return "ptr"
    case ^Type_Scope:
        if v.kind == .Struct {
            return fmt.tprintf("%%class.%s", struct_key(v))
        }
        return "ptr" // callable fun (function pointer)
    case ^Type_Fixed_Array:
        elem_t := llvm_type_from_checker(v.elem)
        alloc_size := v.size
        if v.is_vla {
            alloc_size = 0 // VLA: [0 x T] in struct layout, actual size at runtime
        } else if v.has_sentinel {
            alloc_size += 1
        }
        return fmt.tprintf("[%d x %s]", alloc_size, elem_t)
    case ^Type_Slice:       return SLICE_IR_TYPE
    case ^Type_Partial_Array:
        elem_t := llvm_type_from_checker(v.elem)
        alloc_size := v.size
        if v.is_vla {
            alloc_size = 0
        } else if v.has_sentinel {
            alloc_size += 1
        }
        return partial_array_ir_type(elem_t, alloc_size)
    case ^Type_Enum:
        if v.tag_type != "" { return tag_type_to_ir(v.tag_type) }
        return "i64"
    case ^Type_Union:       return fmt.tprintf("%%union.%s", union_key(v))
    case ^Type_Tuple:       return "void" // tuple returns use sret convention
    case ^Type_Distinct:    return llvm_type_from_checker(v.base_type)
    case Type_Const_Int:    return "i64" // const generic param — should not appear in codegen
    case Type_Runtime_Size: return "i64" // runtime size — should not appear as field type
    case Type_Any:          return "i64" // default to i64 for untyped
    case Type_Error:        return "i64" // error recovery default
    case nil:               return "i64" // nil type (unresolved)
    }
    unreachable()
}

// ---------------------------------------------------------------------------
// Get or create a string literal global
// ---------------------------------------------------------------------------

get_string_literal :: proc(g: ^Codegen, s: string) -> (global_name: string, byte_len: int) {
    if name, ok := g.string_literals[s]; ok {
        return name, len(s) + 1 // +1 for null terminator
    }
    g.string_counter += 1
    name := fmt.tprintf("@.str.%d", g.string_counter)
    g.string_literals[s] = name

    // Escape the string for LLVM IR
    escaped := llvm_escape_string(s)
    byte_length := llvm_string_byte_length(s)

    decl := fmt.tprintf("%s = private unnamed_addr constant [%d x i8] c\"%s\\00\"", name, byte_length + 1, escaped)
    append(&g.string_decls, decl)

    return name, byte_length + 1
}

// Escape string for LLVM IR constant — iterates over raw bytes to preserve
// multi-byte UTF-8 encoding. Non-printable and non-ASCII bytes are hex-escaped.
llvm_escape_string :: proc(s: string) -> string {
    b: strings.Builder
    for i := 0; i < len(s); i += 1 {
        ch := s[i]
        switch ch {
        case '\n': strings.write_string(&b, "\\0A")
        case '\r': strings.write_string(&b, "\\0D")
        case '\t': strings.write_string(&b, "\\09")
        case '\\': strings.write_string(&b, "\\5C")
        case '"':  strings.write_string(&b, "\\22")
        case:
            if ch >= 0x20 && ch < 0x7F {
                // Printable ASCII — emit directly
                strings.write_byte(&b, ch)
            } else {
                // Non-ASCII or control byte — hex-escape
                strings.write_string(&b, fmt.tprintf("\\%02X", ch))
            }
        }
    }
    return strings.to_string(b)
}

// Count actual bytes (after escape processing)
llvm_string_byte_length :: proc(s: string) -> int {
    return len(s) // source string is already unescaped by lexer
}

// ---------------------------------------------------------------------------
// Runtime safety checks
// ---------------------------------------------------------------------------

// Ensure a value is i64 — if the expression is from a sub-i64 type (i32, i16, i8),
// emit a sext to i64. Used for array index values before bounds checking.
ensure_i64 :: proc(g: ^Codegen, val: string, expr: Expr) -> string {
    ir := expr_ir_type(g, expr)
    if ir == "i64" || ir == "double" || ir == "float" || ir == "ptr" || ir == "i1" {
        return val
    }
    if ir == "i32" || ir == "i16" || ir == "i8" {
        ext := fresh_tmp(g)
        emit(g, "  %s = sext %s %s to i64", ext, ir, val)
        return ext
    }
    codegen_fatal(g, {}, "ensure_i64: unexpected IR type '%s'", ir)
}

// Emit an LLVM type conversion between scalar types.
// Returns the (possibly converted) value register.
emit_type_convert :: proc(g: ^Codegen, val: string, from: string, to: string) -> string {
    if from == to { return val }
    conv := fresh_tmp(g)
    is_int :: proc(t: string) -> bool {
        return t == "i64" || t == "i32" || t == "i16" || t == "i8" || t == "i1"
    }
    is_float :: proc(t: string) -> bool {
        return t == "double" || t == "float"
    }
    int_bits :: proc(t: string) -> int {
        switch t {
        case "i64": return 64
        case "i32": return 32
        case "i16": return 16
        case "i8":  return 8
        case "i1":  return 1
        }
        panic(fmt.tprintf("int_bits: unknown integer type '%s'", t))
    }
    if is_int(from) && is_int(to) {
        fb := int_bits(from)
        tb := int_bits(to)
        if fb > tb {
            emit(g, "  %s = trunc %s %s to %s", conv, from, val, to)
        } else {
            emit(g, "  %s = sext %s %s to %s", conv, from, val, to)
        }
    } else if is_float(from) && is_float(to) {
        if from == "double" && to == "float" {
            emit(g, "  %s = fptrunc double %s to float", conv, val)
        } else {
            emit(g, "  %s = fpext float %s to double", conv, val)
        }
    } else if is_float(from) && is_int(to) {
        emit(g, "  %s = fptosi %s %s to %s", conv, from, val, to)
    } else if is_int(from) && is_float(to) {
        emit(g, "  %s = sitofp %s %s to %s", conv, from, val, to)
    } else {
        codegen_fatal(g, {}, "emit_type_convert: unsupported scalar conversion '%s' -> '%s'", from, to)
    }
    return conv
}

// Emit a runtime bounds check: if idx < 0 or idx >= len, print error and exit(1).
// `idx` is the i64 index value, `len` is the i64 length value (or compile-time constant string).
// `name` is the variable name for the error message.
emit_bounds_check :: proc(g: ^Codegen, idx: string, len_val: string, name: string, span: Span = {}) {
    ok_label := fresh_label(g, "bounds.ok")
    fail_label := fresh_label(g, "bounds.fail")
    neg_label := fresh_label(g, "bounds.neg")

    loc := format_location(span.file, span.line, span.col)

    // Check idx < 0
    neg_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt i64 %s, 0", neg_cmp, idx)
    emit(g, "  br i1 %s, label %%%s, label %%%s", neg_cmp, neg_label, fresh_label(g, "bounds.upper"))

    // Upper bound check
    upper_label := fmt.tprintf("bounds.upper%d", g.label_counter)
    emit(g, "%s:", upper_label)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sge i64 %s, %s", cmp, idx, len_val)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, fail_label, ok_label)

    // Negative index error
    emit(g, "%s:", neg_label)
    neg_msg := fmt.tprintf("%s runtime error: index out of bounds: index %%lld < 0 for '%s'\n", loc, name)
    neg_name, neg_len := get_string_literal(g, neg_msg)
    neg_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", neg_ptr, neg_len, neg_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s)", neg_ptr, idx)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    // Upper bound error
    emit(g, "%s:", fail_label)
    err_msg := fmt.tprintf("%s runtime error: index out of bounds: index %%lld >= length %%lld for '%s'\n", loc, name)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i64 %s, i64 %s)", err_ptr, idx, len_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    emit(g, "%s:", ok_label)
}

// Emit a runtime null pointer check: if ptr == null, print error and exit(1).
// `ptr_val` is the pointer IR value, `name` is the variable name for the error message.
emit_null_check :: proc(g: ^Codegen, ptr_val: string, name: string, span: Span = {}) {
    ok_label := fresh_label(g, "null.ok")
    fail_label := fresh_label(g, "null.fail")

    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp eq ptr %s, null", cmp, ptr_val)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, fail_label, ok_label)

    emit(g, "%s:", fail_label)
    loc := format_location(span.file, span.line, span.col)
    err_msg := fmt.tprintf("%s runtime error: null pointer dereference: '%s' is null\n", loc, name)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    emit(g, "%s:", ok_label)
}

// Emit a runtime division-by-zero check: if divisor == 0, print error and exit(1).
// `divisor` is the IR value, `ir_type` is the integer type (e.g. "i64").
emit_div_zero_check :: proc(g: ^Codegen, divisor: string, ir_type: string) {
    ok_label := fresh_label(g, "divz.ok")
    fail_label := fresh_label(g, "divz.fail")

    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp eq %s %s, 0", cmp, ir_type, divisor)
    emit(g, "  br i1 %s, label %%%s, label %%%s", cmp, fail_label, ok_label)

    emit(g, "%s:", fail_label)
    err_name, err_len := get_string_literal(g, "runtime error: division by zero\n")
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    emit(g, "%s:", ok_label)
}

// Emit an overflow-checked integer arithmetic operation using LLVM intrinsics.
// `op` is "sadd", "ssub", or "smul". Returns the result temporary.
// On overflow: prints error and exits.
emit_checked_arith :: proc(g: ^Codegen, op: string, ir_type: string, left: string, right: string) -> string {
    ok_label := fresh_label(g, "overflow.ok")
    fail_label := fresh_label(g, "overflow.fail")

    // Track this intrinsic for declaration
    intrinsic_name := fmt.tprintf("llvm.%s.with.overflow.%s", op, ir_type)
    g.overflow_intrinsics[intrinsic_name] = true

    // Call the intrinsic — use strings.concatenate to avoid fmt.tprintf brace issues
    pair := fresh_tmp(g)
    ret_type := strings.concatenate({"{ ", ir_type, ", i1 }"})
    emit_raw(g, strings.concatenate({"  ", pair, " = call ", ret_type, " @", intrinsic_name, "(", ir_type, " ", left, ", ", ir_type, " ", right, ")"}))

    // Extract result and overflow flag
    result := fresh_tmp(g)
    overflow := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", result, " = extractvalue ", ret_type, " ", pair, ", 0"}))
    emit_raw(g, strings.concatenate({"  ", overflow, " = extractvalue ", ret_type, " ", pair, ", 1"}))

    // Branch on overflow
    emit(g, "  br i1 %s, label %%%s, label %%%s", overflow, fail_label, ok_label)

    emit(g, "%s:", fail_label)
    err_name, err_len := get_string_literal(g, "runtime error: integer overflow\n")
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")

    emit(g, "%s:", ok_label)
    return result
}


// ---------------------------------------------------------------------------
// Context system: automatic scope-based arena mark/reset
// ---------------------------------------------------------------------------

// Element size in bytes for a given LLVM type string.
elem_byte_size :: proc(elem_type: string, checked: ^Checked_Program = nil) -> int {
    ptr_size := 4 if word_size_is_32 else 8
    switch elem_type {
    case "i64":         return 8
    case "double":      return 8
    case "ptr":         return ptr_size
    case "i32":         return 4
    case "float":       return 4
    case "i16":         return 2
    case "i8":          return 1
    case "i1":          return 1
    case SLICE_IR_TYPE: return slice_header_bytes
    }
    // Handle embedded struct types like %class.Point
    if strings.has_prefix(elem_type, "%class.") {
        sname := elem_type[len("%class."):]
        if checked != nil {
            if st, ok := checked.table.structs[sname]; ok {
                return struct_byte_size_sd(&st.sd, checked)
            }
            if st, ok := checked.table.funs[sname]; ok {
                return struct_byte_size(st, checked)
            }
        }
    }
    // Handle array types like [512 x i1]
    if strings.has_prefix(elem_type, "[") {
        cap, elem, arr_ok := parse_array_ir_type(elem_type)
        if arr_ok {
            return cap * elem_byte_size(elem, checked)
        }
    }
    return ptr_size // default for struct pointers, etc.
}

// Alignment of an LLVM type (matches LLVM's default data layout)
elem_alignment :: proc(elem_type: string, checked: ^Checked_Program = nil) -> int {
    ptr_align := 4 if word_size_is_32 else 8
    switch elem_type {
    case "i64":         return 8
    case "double":      return 8
    case "ptr":         return ptr_align
    case "i32":         return 4
    case "float":       return 4
    case "i16":         return 2
    case "i8":          return 1
    case "i1":          return 1
    case SLICE_IR_TYPE: return slice_header_align
    }
    // Handle embedded struct types — alignment is max alignment of inner fields
    if strings.has_prefix(elem_type, "%class.") {
        sname := elem_type[len("%class."):]
        if checked != nil {
            sd: ^Scope_Body
            if ss, ss_ok := checked.table.structs[sname]; ss_ok {
                sd = &ss.sd
            } else if sf, sf_ok := checked.table.funs[sname]; sf_ok {
                sd = &sf.sd
            }
            if sd != nil {
                max_a := 1
                for &f in sd.fields {
                    a := elem_alignment(field_ir_type(&f), checked)
                    if a > max_a { max_a = a }
                }
                return max_a
            }
        }
    }
    // Handle array types like [512 x i1] — alignment is element alignment
    if strings.has_prefix(elem_type, "[") {
        _, elem, arr_ok := parse_array_ir_type(elem_type)
        if arr_ok {
            return elem_alignment(elem, checked)
        }
    }
    return ptr_align
}

// Compute the byte size of a struct including alignment padding (matches C/LLVM layout).
// Reads directly from Type_Scope fields.
struct_byte_size_sd :: proc(sd: ^Scope_Body, checked: ^Checked_Program = nil) -> int {
    offset := 0
    max_align := 1
    for &f in sd.fields {
        ft := field_ir_type(&f)
        a := elem_alignment(ft, checked)
        if a > max_align { max_align = a }
        // Align the current offset
        if offset % a != 0 {
            offset += a - (offset % a)
        }
        offset += elem_byte_size(ft, checked)
    }
    // Hidden trailing buffer for sized-slice fields' backing storage.
    // Always byte-typed so no alignment bump needed.
    offset += sd.backing_bytes
    // Pad to struct alignment
    if offset % max_align != 0 {
        offset += max_align - (offset % max_align)
    }
    return offset
}

struct_byte_size_fun :: proc(st: ^Type_Scope, checked: ^Checked_Program = nil) -> int {
    return struct_byte_size_sd(&st.sd, checked)
}

struct_byte_size :: proc { struct_byte_size_fun, struct_byte_size_sd }

// Get byte size of an IR integer type string ("i8" -> 1, "i16" -> 2, "i32" -> 4, "i64" -> 8)
ir_type_byte_size :: proc(ir: string) -> int {
    switch ir {
    case "i8":  return 1
    case "i16": return 2
    case "i32": return 4
    case "i64": return 8
    case:       return 8
    }
}

// Check if a statement list contains any "big value" declarations.
// A big value is a fixed-size array whose total byte size >= 1024.
// Skips the NRVO variable since it's aliased to the caller's sret buffer (no allocation).
scope_has_big_values :: proc(stmts: []Stmt, g: ^Codegen) -> bool {
    assign_is_big :: proc(assign: ^Stmt_Assign, g: ^Codegen) -> bool {
        if g.nrvo_var != "" && assign.name == g.nrvo_var { return false }
        vt := assign.var_type
        if fa, fa_ok := vt.(^Type_Fixed_Array); fa_ok {
            if fa.is_vla { return true }
            elem_t := llvm_type_from_checker(fa.elem)
            total := fa.size * elem_byte_size(elem_t)
            if total >= 1024 { return true }
        }
        if sd := as_struct_body(vt); sd != nil {
            if sd.has_vla_field { return true }
            // Match the codegen routing rule in gen_stmt's struct branch:
            // structs over 1024 bytes are auto-routed to the scope arena.
            if struct_byte_size(sd, g.checked) > 1024 { return true }
        }
        if assign.is_var { return true }
        return false
    }
    for stmt in stmts {
        if assign, ok := stmt.(^Stmt_Assign); ok {
            if assign_is_big(assign, g) { return true }
        }
        if decl, ok := stmt.(^Stmt_Decl); ok {
            for inner in decl.checked {
                if a, aok := inner.(^Stmt_Assign); aok && assign_is_big(a, g) {
                    return true
                }
            }
        }
    }
    return false
}

// Load the context's arena pointer (field 0 of Context struct).
get_context_arena_ptr :: proc(g: ^Codegen) -> string {
    ctx_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", ctx_ptr, " = load ptr, ptr @__mara_context"}))
    arena_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", arena_ptr, " = getelementptr %class.Context, ptr ", ctx_ptr, ", i32 0, i32 0"}))
    return arena_ptr
}

// Emit a call to the Mara mark() function from the memory package.
emit_arena_mark :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    mark_ir := mara_fn_name(g, g.arena_mark_name)
    if info, ok := lookup_fun_info(g, g.arena_mark_name); ok && info.ret_struct != "" {
        dummy := fresh_tmp(g)
        emit(g, "  %s = alloca %s", dummy, struct_llvm_name(info.ret_struct))
        emit_raw(g, strings.concatenate({"  call void ", mark_ir, "(ptr ", arena_ptr, ", ptr ", dummy, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", mark_ir, "(ptr ", arena_ptr, ")"}))
    }
}

// Emit a call to arena_alloc() for a compile-time known size. Returns the data pointer.
emit_arena_bump :: proc(g: ^Codegen, size: int, name: string = "<alloc>", loc: string = "<unknown>") -> string {
    return emit_arena_bump_val(g, fmt.tprintf("%d", size), name, loc)
}

// Emit a call to arena_alloc() with a runtime size value (LLVM IR temporary). Returns the data pointer.
emit_arena_bump_runtime :: proc(g: ^Codegen, size_val: string, name: string = "<alloc>", loc: string = "<unknown>") -> string {
    return emit_arena_bump_val(g, size_val, name, loc)
}

// Call the Mara arena_alloc() function from the memory package.
// arena_alloc(a: ^Arena, size: int, name: ^byte, span: ^byte) -> []byte
// Returns the data pointer. Emits OOM check as safety net (arena_alloc crashes first).
emit_arena_bump_val :: proc(g: ^Codegen, size_val: string, name: string = "<alloc>", loc: string = "<unknown>") -> string {
    // Deferred check: only fires if some code actually wants the arena. A
    // shared-build DLL with `#expose` fn(s) but no `context.scope_allocator
    // = X` declaration reaches here with no allocator name. Tell the user
    // what to add; suppressed for DLLs that never touch the arena.
    if g.arena_alloc_name == "" {
        if g.shared {
            codegen_fatal(g, {},
                "DLL with #expose fn(s) uses arena-needing code but no allocator type is declared — add `context.scope_allocator = ArenaType(<args>)` somewhere in this module to specify the Context layout (must match the host's allocator type)")
        }
        codegen_fatal(g, {}, "arena allocation requested but no scope_allocator declared")
    }
    arena_ptr := get_context_arena_ptr(g)
    // Alloca for the sret slice result { ptr, i64 }
    tmp_slice := fresh_tmp(g)
    emit_slice_alloca(g, tmp_slice)
    // Get a pointer to the name string literal
    name_global, name_len := get_string_literal(g, name)
    name_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", name_ptr, name_len, name_global)
    // Get a pointer to the span/location string literal
    span_global, span_len := get_string_literal(g, loc)
    span_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", span_ptr, span_len, span_global)
    // sret goes last, after the regular params
    alloc_ir := mara_fn_name(g, g.arena_alloc_name)
    if g.arena_alloc_has_debug {
        emit_raw(g, strings.concatenate({"  call void ", alloc_ir, "(ptr ", arena_ptr, ", i64 ", size_val, ", ptr ", name_ptr, ", ptr ", span_ptr, ", ptr ", tmp_slice, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", alloc_ir, "(ptr ", arena_ptr, ", i64 ", size_val, ", ptr ", tmp_slice, ")"}))
    }
    // Extract raw data pointer from the returned slice header
    data_ptr_ptr := fresh_tmp(g)
    emit_slice_gep(g, data_ptr_ptr, tmp_slice, SLICE.ptr)
    data_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", data_ptr, " = load ptr, ptr ", data_ptr_ptr}))

    // Check the slice capacity — a zero-cap return means OOM
    cap_ptr := fresh_tmp(g)
    emit_slice_gep(g, cap_ptr, tmp_slice, SLICE.cap)
    cap_val := fresh_tmp(g)
    emit_typed_load_cap(g, cap_val, cap_ptr)
    is_oom := fresh_tmp(g)
    emit(g, "  %s = icmp eq i64 %s, 0", is_oom, cap_val)
    ok_label := fresh_label(g, "arena.ok")
    fail_label := fresh_label(g, "arena.oom")
    emit(g, "  br i1 %s, label %%%s, label %%%s", is_oom, fail_label, ok_label)
    emit(g, "%s:", fail_label)
    err_msg := "runtime error: arena out of memory\n"
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr [%d x i8], ptr %s, i64 0, i64 0", err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit(g, "%s:", ok_label)

    return data_ptr
}

// Emit a call to the Mara reset() function from the memory package.
emit_arena_reset :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    reset_ir := mara_fn_name(g, g.arena_reset_name)
    if info, ok := lookup_fun_info(g, g.arena_reset_name); ok && info.ret_struct != "" {
        dummy := fresh_tmp(g)
        emit(g, "  %s = alloca %s", dummy, struct_llvm_name(info.ret_struct))
        emit_raw(g, strings.concatenate({"  call void ", reset_ir, "(ptr ", arena_ptr, ", ptr ", dummy, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", reset_ir, "(ptr ", arena_ptr, ")"}))
    }
}

// Push a scope onto the stack. If it needs mark/reset (has big values), emit mark.
push_scope :: proc(g: ^Codegen, kind: Control_Scope_Kind, stmts: []Stmt) {
    needs_mark := g.context_enabled && scope_has_big_values(stmts, g)
    append(&g.scope_stack, Scope_Entry{has_mark = needs_mark, scope_kind = kind})
    if needs_mark {
        emit_arena_mark(g)
    }
}

// Emit deferred blocks for a scope entry in reverse (LIFO) order.
// Each block's statements execute in forward order.
emit_scope_defers :: proc(g: ^Codegen, entry: ^Scope_Entry) {
    for i := len(entry.deferred_blocks) - 1; i >= 0; i -= 1 {
        for stmt in entry.deferred_blocks[i] {
            gen_stmt(g, stmt)
        }
    }
}

// Pop the current scope. Emit deferred stmts (LIFO), then arena reset if marked.
pop_scope :: proc(g: ^Codegen) {
    if len(g.scope_stack) == 0 { return }
    entry := pop(&g.scope_stack)
    emit_scope_defers(g, &entry)
    if entry.has_mark {
        emit_arena_reset(g)
    }
}

// Emit cleanup for all scopes in the stack (for early return).
// Walks from innermost to outermost, emitting deferred stmts then arena reset.
// Does NOT pop entries — the caller manages the stack.
emit_return_resets :: proc(g: ^Codegen) {
    for i := len(g.scope_stack) - 1; i >= 0; i -= 1 {
        emit_scope_defers(g, &g.scope_stack[i])
        if g.context_enabled && g.scope_stack[i].has_mark {
            emit_arena_reset(g)
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------


// Generate an LLVM type declaration for a struct from checked type data.
register_struct_decl_sd :: proc(g: ^Codegen, sd: ^Scope_Body) {
    if sd.scope != nil { return }  // module-struct — namespace only, no data layout
    key := sd.name
    if key in g.registered_structs { return }
    g.registered_structs[key] = true
    llvm_name := struct_llvm_name(key)
    field_types: [dynamic]string
    for &f in sd.fields {
        append(&field_types, field_ir_type(&f))
    }
    // Hidden trailing buffer holds backing storage for any sized-slice fields
    // (direct or in fixed-array fields). Sized as i8 bytes regardless of slice
    // elem type — alignment is owner's problem once slice headers point at offsets.
    sd.backing_bytes = compute_struct_backing(g, sd)
    if sd.backing_bytes > 0 {
        append(&field_types, fmt.tprintf("[%d x i8]", sd.backing_bytes))
    }
    fields_joined := strings.join(field_types[:], ", ")
    type_decl := strings.concatenate({llvm_name, " = type { ", fields_joined, " }"})
    append(&g.struct_decls, type_decl)
}

// Sum of bytes needed to back this struct's own sized-slice fields.
// Direct field: alloc_cap * elem_bytes. Fixed-array field [N]Slice: N * that.
// Nested struct fields have their backing in their own layout — not counted here.
compute_struct_backing :: proc(g: ^Codegen, sd: ^Scope_Body) -> int {
    total := 0
    for &f in sd.fields {
        if cap_n, sl, ok := sized_slice_info(g, f.type_); ok {
            alloc_cap := cap_n
            if sl.has_sentinel { alloc_cap += 1 }
            elem_bytes := elem_byte_size(llvm_type_from_checker(sl.elem), g.checked)
            total += alloc_cap * elem_bytes
            continue
        }
        if fa, fa_ok := f.type_.(^Type_Fixed_Array); fa_ok {
            if cap_n, sl, ok := sized_slice_info(g, fa.elem); ok {
                alloc_cap := cap_n
                if sl.has_sentinel { alloc_cap += 1 }
                elem_bytes := elem_byte_size(llvm_type_from_checker(sl.elem), g.checked)
                total += fa.size * alloc_cap * elem_bytes
            }
        }
    }
    return total
}

register_struct_decl :: proc(g: ^Codegen, st: ^Type_Scope) {
    register_struct_decl_sd(g, &st.sd)
}

// Register a union's LLVM type declaration and compute its payload size.
//
// Layout produced:
//   pad bytes == 0: { tag_ir, [payload_bytes x i8] }              — payload at offset tag_bytes
//   pad bytes >  0: { [(tag_bytes+pad_bytes) x i8], [N x i8] }    — payload at offset tag_bytes+pad_bytes
//
// The padded form uses a byte array for the tag area so the typed load/store
// of `tag_ir` at field 0 still works (opaque ptr, type at the access site),
// while shifting the payload start to where the variants' natural alignment
// expects it (e.g. SDL3's u64 timestamp at byte 8 with a u32 tag).
register_union_type :: proc(g: ^Codegen, ukey: string, ut: ^Type_Union) {
    g.registered_structs[ukey] = true
    llvm_name := union_llvm_name(ukey)

    // Niche layout: single pointer slot, no tag. Identifies None via null
    // and Some via a live pointer at the same offset.
    if is_niche_layout(g, ut) {
        type_decl := strings.concatenate({llvm_name, " = type { ptr }"})
        append(&g.struct_decls, type_decl)
        return
    }

    tag_ir := union_tag_ir_type(ut)
    tag_bytes := ir_type_byte_size(tag_ir)
    pad_bytes := union_tag_pad_bytes(ut)
    tag_area_bytes := tag_bytes + pad_bytes

    // Calculate payload size from largest variant struct
    max_bytes := 0
    for _, struct_name in ut.variant_structs {
        if st, st_ok := lookup_struct(g, struct_name); st_ok {
            size := struct_byte_size_sd(st, g.checked)
            if size > max_bytes {
                max_bytes = size
            }
        }
    }
    // Enforce min_size: union(128) means total size >= 128 bytes
    if ut.min_size > 0 {
        min_payload := ut.min_size - tag_area_bytes
        if min_payload > max_bytes {
            max_bytes = min_payload
        }
    }
    payload_str := fmt.tprintf("[%d x i8]", max_bytes)
    tag_field: string
    if pad_bytes > 0 {
        tag_field = fmt.tprintf("[%d x i8]", tag_area_bytes)
    } else {
        tag_field = tag_ir
    }
    type_decl := strings.concatenate({llvm_name, " = type { ", tag_field, ", ", payload_str, " }"})
    append(&g.struct_decls, type_decl)
}

// Module-local target flag, set at the start of generate_program. Read by
// llvm_type_from_checker (and similar context-free helpers) so word-sized
// types (usize/isize) emit the right width without threading `web` through
// ~60 call sites. Reset to false at the end of generate_program so back-to-
// back native/web invocations don't carry stale state.
@(private) word_size_is_32: bool

// Emit LLVM IR for the checked program. Every visible function gets
// emitted; the linker drops unreachable code.
generate_program :: proc(output_path: string, checked: ^Checked_Program, web: bool = false, shared: bool = false) -> bool {
    g := Codegen{}
    g.checked = checked
    g.web = web
    g.shared = shared
    word_size_is_32 = web
    init_slice_layout()

    // Context system: scope allocator setup. Enabled when either:
    //   - the user declared `context.scope_allocator = X` (has_scope_allocator), OR
    //   - we're in shared mode and there's at least one `#expose` fn (host
    //     will pass a Context at runtime).
    g.context_enabled = checked.table.has_scope_allocator || checked.table.context_expected_at_runtime
    if g.context_enabled && checked.table.scope_allocator_type != nil {
        alloc_type := checked.table.scope_allocator_type
        // Find the arena (the struct that holds the bump offset / base buffer).
        //
        // Two forms supported:
        //   - Legacy nested: allocator has types["Arena"] → inner arena struct.
        //   - Flat (Zig-style): the allocator class itself IS the arena.
        arena_key: string
        arena_sd: ^Scope_Body
        arena_ft: ^Type_Scope // only set if arena is a Type_Scope (has params)
        if inner_t, has_inner := alloc_type.types["Arena"]; has_inner {
            arena_key = type_flat_name(inner_t)
            if inner_ts, inner_ts_ok := inner_t.(^Type_Scope); inner_ts_ok {
                arena_sd = &inner_ts.sd
                arena_ft = inner_ts
            } else if arena_ss, arena_ss_ok := checked.table.structs[arena_key]; arena_ss_ok {
                arena_sd = &arena_ss.sd
            } else if arena_sf, arena_sf_ok := checked.table.funs[arena_key]; arena_sf_ok {
                arena_sd = &arena_sf.sd
                arena_ft = arena_sf
            }
        } else {
            // Flat form: allocator class is the arena itself
            arena_key = alloc_type.name
            arena_sd = &alloc_type.sd
            arena_ft = alloc_type
        }
        _ = arena_sd // keep as reference; codegen may read it elsewhere via the key

        // Get function names from the allocator's functions
        if fn, ok := alloc_type.functions["alloc"]; ok && fn != nil { g.arena_alloc_name = fn.name }
        if fn, ok := alloc_type.functions["mark"];  ok && fn != nil { g.arena_mark_name  = fn.name }
        if fn, ok := alloc_type.functions["reset"]; ok && fn != nil { g.arena_reset_name = fn.name }
        // Constructor: either new() function, or the Arena type itself if it has params
        if new_fn, ok := alloc_type.functions["new"]; ok && new_fn != nil {
            g.arena_new_name = new_fn.name
        } else if arena_ft != nil && len(arena_ft.params) > 0 {
            g.arena_new_name = arena_key  // Arena constructor (e.g. Arena_Debug(cap))
        } else {
            g.arena_new_name = alloc_type.name
        }

        // Check if alloc() takes debug params (name/span) beyond (arena, size)
        if alloc_cf, af_ok := checked.functions[g.arena_alloc_name]; af_ok {
            g.arena_alloc_has_debug = len(alloc_cf.params) > 2
        }
    }

    // Patch Context's arena field with the real arena type (checker used Type_Any placeholder)
    if g.context_enabled && checked.table.scope_allocator_type != nil {
        if ctx_st, ctx_ok := checked.table.funs["Context"]; ctx_ok {
            alloc_type := checked.table.scope_allocator_type
            arena_type: Type
            if inner_t, has_inner := alloc_type.types["Arena"]; has_inner {
                arena_type = inner_t
            } else {
                // Flat form: allocator type IS the arena type
                arena_type = alloc_type
            }
            // Field 0 is "arena" — replace its placeholder type
            if len(ctx_st.fields) > 0 && ctx_st.fields[0].name == "arena" {
                ctx_st.fields[0].type_ = arena_type
            }
        }
    }

    // We use two builders: one for functions, one for main
    fn_builder: strings.Builder
    strings.builder_init(&fn_builder)

    main_builder: strings.Builder
    strings.builder_init(&main_builder)

    // Generate LLVM type declarations for all structs from checked type data.
    // Map iteration order is hash-seeded and not deterministic between runs,
    // so collect keys and sort for byte-identical builds.
    struct_keys: [dynamic]string
    defer delete(struct_keys)
    for k in checked.table.structs { append(&struct_keys, k) }
    slice.sort(struct_keys[:])
    for k in struct_keys {
        register_struct_decl(&g, checked.table.structs[k])
    }
    fun_keys: [dynamic]string
    defer delete(fun_keys)
    for k in checked.table.funs { append(&fun_keys, k) }
    slice.sort(fun_keys[:])
    for k in fun_keys {
        st := checked.table.funs[k]
        // Skip Fun-kind entries: they're callable functions registered for
        // post-check lookup (e.g. extract_checked_scope finding nested
        // funs), not data-layout types. Emitting them as LLVM structs
        // produces invalid IR (void return types end up as struct fields).
        if st.kind == .Fun { continue }
        register_struct_decl(&g, st)
    }

    // Register all unions from checked type data (keys are flat after flatten_for_codegen)
    union_keys: [dynamic]string
    defer delete(union_keys)
    for k in checked.table.unions { append(&union_keys, k) }
    slice.sort(union_keys[:])
    for ukey in union_keys {
        if ukey not_in g.registered_structs {
            register_union_type(&g, ukey, checked.table.unions[ukey])
        }
    }

    // Build set of explicitly declared function names (from AST order)
    declared_fns: map[string]bool
    for fn_name in checked.function_order {
        declared_fns[fn_name] = true
    }

    // Phase 1: Emit non-main function definitions (preserving AST order).
    g.out = fn_builder
    for fn_name in checked.function_order {
        if fn_name == "main" { continue }
        if cf, cf_ok := checked.functions[fn_name]; cf_ok {
            gen_scope_def(&g, &cf)
        }
    }

    // Phase 1.5: Emit monomorphized generic function definitions.
    // These have mangled names like "swap__int" and are stored in checked.functions
    // but don't have AST nodes in the program. Sort by name so the emission
    // order is reproducible (map iteration is hash-seeded otherwise).
    mono_names: [dynamic]string
    defer delete(mono_names)
    for fn_name in checked.functions {
        if strings.contains(fn_name, "__") && fn_name not_in declared_fns {
            append(&mono_names, fn_name)
        }
    }
    slice.sort(mono_names[:])
    for fn_name in mono_names {
        cf := checked.functions[fn_name]
        gen_scope_def(&g, &cf)
    }

    fn_builder = g.out

    // Phase 2: Emit @main from user's fn main(). Skipped in shared (DLL) mode —
    // the binary has no entry point; each #expose function does its own ctx
    // handover into @__mara_context on entry, so there's nothing for a single
    // init function to do.
    if !g.shared {

    g.out = main_builder
    g.tmp_counter = 0
    g.all_vars = {}
    g.emitted_allocas = {}
    // On web (wasm32), the C entry point's `int` is i32, not i64. We keep
    // Mara's main internally as i64 so user `return X` and the args-setup
    // size_t handling don't change, and emit a tiny i32 wrapper after.
    if g.web {
        emit_raw(&g, "define i64 @__mara_main(i32 %argc, ptr %argv) {")
    } else {
        emit_raw(&g, "define i64 @main(i32 %argc, ptr %argv) {")
    }
    emit_raw(&g, "entry:")

    // Context: backed by a real LLVM global so it survives main returning.
    // Required for web builds where emscripten owns the main loop —
    // emscripten_set_main_loop_arg returns to JS, the rAF callback runs
    // after main's stack is gone, and any later @__mara_context load would
    // dereference a dangling stack pointer (manifests as arena.base.cap
    // reading 0 and the very first byte-buffer write tripping the bounds
    // check). Native is unaffected: same global lifetime, same fields.
    {
        ctx_alloca := "@__mara_context_storage"
        emit_raw(&g, strings.concatenate({"  store ptr ", ctx_alloca, ", ptr @__mara_context"}))
        g.ctx_alloca = ctx_alloca

        // Register 'context' as a struct var so field access works normally
        g.all_vars["context"] = Struct_Var{alloca = ctx_alloca, struct_name = "Context"}

        // Arena init (if scope allocator is active).
        if g.context_enabled {
            arena_ptr := fresh_tmp(&g)
            emit_raw(&g, strings.concatenate({"  ", arena_ptr, " = getelementptr %class.Context, ptr ", ctx_alloca, ", i32 0, i32 0"}))
            new_ir := mara_fn_name(&g, g.arena_new_name)
            alloc_size := "268435456"  // default 256 MB
            if checked.table.scope_allocator_args != nil && len(checked.table.scope_allocator_args) > 0 {
                size_val := gen_expr(&g, checked.table.scope_allocator_args[0])
                alloc_size = size_val
            }
            emit_raw(&g, strings.concatenate({"  call void ", new_ir, "(i64 ", alloc_size, ", ptr ", arena_ptr, ")"}))
        }

        // Populate context.args — partial array {len, cap, ptr, [64 x slice]}
        // embedded as a field of Context.
        args_field_idx := "1" if g.context_enabled else "0"
        ARGS_CAP :: "64"
        pa_ir := partial_array_ir_type(SLICE_IR_TYPE, 64)

        // GEP to the partial-array field within Context
        args_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", args_ptr, " = getelementptr %class.Context, ptr ", ctx_alloca, ", i32 0, i32 ", args_field_idx}))

        // Compute effective len = min(argc, 64)
        argc_i64 := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argc_i64, " = sext i32 %argc to i64"}))
        argc_cmp := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argc_cmp, " = icmp slt i64 ", argc_i64, ", ", ARGS_CAP}))
        argc_min := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argc_min, " = select i1 ", argc_cmp, ", i64 ", argc_i64, ", i64 ", ARGS_CAP}))

        // Store len at field 0
        len_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", len_ptr, " = getelementptr ", pa_ir, ", ptr ", args_ptr, ", i32 0, i32 0"}))
        emit_typed_store_len(&g, argc_min, len_ptr)

        // Store cap = 64 at field 1
        cap_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", cap_ptr, " = getelementptr ", pa_ir, ", ptr ", args_ptr, ", i32 0, i32 1"}))
        emit_typed_store_cap(&g, ARGS_CAP, cap_ptr)

        // GEP to elements storage (field 3) — also the value we store into ptr (field 2)
        elements_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", elements_ptr, " = getelementptr ", pa_ir, ", ptr ", args_ptr, ", i32 0, i32 3"}))

        // Store ptr = &elements at field 2
        ptr_field := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", ptr_field, " = getelementptr ", pa_ir, ", ptr ", args_ptr, ", i32 0, i32 2"}))
        emit_raw(&g, strings.concatenate({"  store ptr ", elements_ptr, ", ptr ", ptr_field}))

        // Loop: for i = 0; i < len; i++ — fill elements[i] = { strlen, strlen, argv[i] }
        loop_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", loop_i, " = alloca i64"}))
        emit_raw(&g, strings.concatenate({"  store i64 0, ptr ", loop_i}))
        loop_lbl := fmt.tprintf("args_loop_%d", g.label_counter)
        body_lbl := fmt.tprintf("args_body_%d", g.label_counter)
        done_lbl := fmt.tprintf("args_done_%d", g.label_counter)
        g.label_counter += 1
        emit_raw(&g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(&g, strings.concatenate({loop_lbl, ":"}))
        cur_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", cur_i, " = load i64, ptr ", loop_i}))
        cmp := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", cmp, " = icmp slt i64 ", cur_i, ", ", argc_min}))
        emit_raw(&g, strings.concatenate({"  br i1 ", cmp, ", label %", body_lbl, ", label %", done_lbl}))

        emit_raw(&g, strings.concatenate({body_lbl, ":"}))
        argv_i_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argv_i_ptr, " = getelementptr ptr, ptr %argv, i64 ", cur_i}))
        argv_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argv_i, " = load ptr, ptr ", argv_i_ptr}))
        str_len := fresh_tmp(&g)
        if g.web {
            // wasm32 strlen returns i32; sext to i64 to match Mara's int width.
            str_len_32 := fresh_tmp(&g)
            emit_raw(&g, strings.concatenate({"  ", str_len_32, " = call i32 @strlen(ptr ", argv_i, ")"}))
            emit_raw(&g, strings.concatenate({"  ", str_len, " = sext i32 ", str_len_32, " to i64"}))
        } else {
            emit_raw(&g, strings.concatenate({"  ", str_len, " = call i64 @strlen(ptr ", argv_i, ")"}))
        }
        // elements[i] is a slice — write len, cap, ptr.
        elem_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", elem_ptr, " = getelementptr [64 x ", SLICE_IR_TYPE, "], ptr ", elements_ptr, ", i64 0, i64 ", cur_i}))
        slen_ptr := fresh_tmp(&g)
        emit_slice_gep(&g, slen_ptr, elem_ptr, SLICE.len)
        emit_typed_store_len(&g, str_len, slen_ptr)
        scap_ptr := fresh_tmp(&g)
        emit_slice_gep(&g, scap_ptr, elem_ptr, SLICE.cap)
        emit_typed_store_cap(&g, str_len, scap_ptr)
        data_ptr := fresh_tmp(&g)
        emit_slice_gep(&g, data_ptr, elem_ptr, SLICE.ptr)
        emit_raw(&g, strings.concatenate({"  store ptr ", argv_i, ", ptr ", data_ptr}))
        // i++
        next_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", next_i, " = add i64 ", cur_i, ", 1"}))
        emit_raw(&g, strings.concatenate({"  store i64 ", next_i, ", ptr ", loop_i}))
        emit_raw(&g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(&g, strings.concatenate({done_lbl, ":"}))
    }

    // Enable alloca hoisting for main body
    begin_alloca_hoist(&g)

    // Emit the user's main body.
    if main_cf, main_ok := checked.functions["main"]; main_ok {
        has_ret := false
        for s in main_cf.body {
            gen_stmt(&g, s)
            if _, ok := s.(Stmt_Return); ok {
                has_ret = true
            }
        }
        if !has_ret {
            emit(&g, "  ret i64 0")
        }
    }

    // Flush: hoisted allocas first, then body code
    end_alloca_hoist(&g)

    emit(&g, "}")

    // Web wrapper: `i32 @main(i32, ptr)` calling our i64 mara main and
    // truncating the return code so emscripten's runtime sees a regular int.
    if g.web {
        emit_raw(&g, "")
        emit_raw(&g, "define i32 @main(i32 %argc, ptr %argv) {")
        emit_raw(&g, "  %r = call i64 @__mara_main(i32 %argc, ptr %argv)")
        emit_raw(&g, "  %r32 = trunc i64 %r to i32")
        emit_raw(&g, "  ret i32 %r32")
        emit_raw(&g, "}")
    }

    main_builder = g.out

    }  // end `if !g.shared` (Phase 2 — @main / web wrapper)

    // Assemble final module
    final: strings.Builder
    strings.builder_init(&final)

    // Module header
    strings.write_string(&final, "; Mara LLVM IR output\n")
    if web {
        strings.write_string(&final, "target triple = \"wasm32-unknown-emscripten\"\n\n")
    } else {
        // Native triple matches the host OS. Cross-compilation would override.
        native_triple :: "x86_64-pc-windows-msvc" when ODIN_OS == .Windows else
                         "x86_64-pc-linux-gnu"   when ODIN_OS == .Linux   else
                         "x86_64-apple-darwin"
        strings.write_string(&final, "target triple = \"")
        strings.write_string(&final, native_triple)
        strings.write_string(&final, "\"\n\n")
    }

    // Struct type definitions
    for decl in g.struct_decls {
        strings.write_string(&final, decl)
        strings.write_byte(&final, '\n')
    }
    if len(g.struct_decls) > 0 {
        strings.write_byte(&final, '\n')
    }

    // String literal globals
    for decl in g.string_decls {
        strings.write_string(&final, decl)
        strings.write_byte(&final, '\n')
    }
    if len(g.string_decls) > 0 {
        strings.write_byte(&final, '\n')
    }

    // Context global (always present — holds args, and arena when scope allocator is active)
    strings.write_string(&final, "; Context system\n")
    strings.write_string(&final, "@__mara_context = internal global ptr null\n")
    strings.write_string(&final, "@__mara_context_storage = internal global %class.Context zeroinitializer\n\n")

    // External declarations
    strings.write_string(&final, "; External declarations\n")
    strings.write_string(&final, "declare i32 @printf(ptr, ...)\n")
    strings.write_string(&final, "declare void @exit(i32)\n")
    // size_t is i64 on x86_64 but i32 on wasm32. The call site sexts to i64
    // so the rest of the IR doesn't need to know which target it's on.
    if g.web {
        strings.write_string(&final, "declare i32 @strlen(ptr)\n")
    } else {
        strings.write_string(&final, "declare i64 @strlen(ptr)\n")
    }
    // Overflow-checking intrinsics — sort for reproducible IR.
    intr_names: [dynamic]string
    defer delete(intr_names)
    for name in g.overflow_intrinsics { append(&intr_names, name) }
    slice.sort(intr_names[:])
    for name in intr_names {
        // name is e.g. "llvm.sadd.with.overflow.i64"
        // Extract the type suffix (last dot-separated component)
        dot_idx := 0
        for i := len(name) - 1; i >= 0; i -= 1 {
            if name[i] == '.' { dot_idx = i; break }
        }
        it := name[dot_idx+1:]  // e.g. "i64"
        // Use concatenate to avoid fmt.tprintf interpreting braces
        strings.write_string(&final, strings.concatenate({"declare { ", it, ", i1 } @", name, "(", it, ", ", it, ")\n"}))
    }
    // Each foreign symbol has a globally unique link_name (enforced at
    // registration time, see make_foreign_checked_scope), so no dedup pass
    // is needed here — one declare per foreign entry. Dynamic foreigns on
    // native skip; their resolution goes through the loader's fn-pointer
    // globals instead of the linker's import table. Sort by name so the
    // declare order is reproducible across builds.
    foreign_keys: [dynamic]string
    defer delete(foreign_keys)
    for k in checked.functions { append(&foreign_keys, k) }
    slice.sort(foreign_keys[:])
    for k in foreign_keys {
        cs := checked.functions[k]
        fo, is_foreign := cs.origin.(Origin_Foreign)
        if !is_foreign { continue }
        decl_str := build_c_declare(&cs, fo.link_name, checked.target_os)
        strings.write_string(&final, decl_str)
        strings.write_byte(&final, '\n')
    }
    strings.write_byte(&final, '\n')

    // Function definitions
    strings.write_string(&final, strings.to_string(fn_builder))
    strings.write_byte(&final, '\n')

    // Main
    strings.write_string(&final, strings.to_string(main_builder))
    strings.write_byte(&final, '\n')

    // Write to file
    result := strings.to_string(final)
    werr := os.write_entire_file(output_path, transmute([]u8)result)
    if werr != nil {
        fmt.printf("Error: could not write '%s'\n", output_path)
        return false
    }

    return true
}

// NOTE: The following procs have been moved to separate files:
// - gen_scope_def         -> codegen_fn.odin
// - gen_stmt           -> codegen_stmt.odin
// - gen_array_*        -> codegen_array.odin
// - gen_struct_*       -> codegen_struct.odin
// - gen_match/value    -> codegen_match.odin
// - gen_if, gen_for    -> codegen_control.odin
// - gen_expr, gen_call -> codegen_expr.odin
