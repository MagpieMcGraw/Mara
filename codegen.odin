package mara

import "core:fmt"
import "core:slice"
import "core:strconv"
import "core:strings"
import "core:os"
import "core:thread"
import "core:mem/virtual"
import os_old "core:os/old"

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
// Defaults are set at package init for 64-bit / i32 len+cap (slice = 16
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
// the first slice_header_bytes, which lets one set of field-access codegen paths serve
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
// A slice is a fat pointer: { ptr data, <len_ir> len, <cap_ir> cap }
// (widths configured via slice_layout — see codegen.odin top of file).
Slice_Var :: struct {
    alloca:       string, // alloca for the slice header struct
    elem_type:    string, // LLVM element type: "i64", "double", etc.
    is_utf8:      bool,   // true for []utf8 slices — drives string-vs-array print formatting
    has_sentinel: bool,   // true for [, S]T sentinel-terminated slices — last element reserved
    sentinel:     int,    // sentinel value (e.g. 0 for null-terminated utf8). Meaningful only when has_sentinel.
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

// Synthetic binding to a precomputed SSA value (no alloca). Used by compound
// assignment to hold the pre-loaded LHS value without paying for an
// alloca/store/load triple — gen_expr on an Expr_Ident bound to one of these
// returns the SSA directly. The synthetic name lives only as long as its
// surrounding statement; nothing else should produce these.
SSA_Var :: struct {
    ssa:     string, // SSA name, e.g. "%t42"
    ir_type: string, // LLVM type of the value, e.g. "i64" or "[4 x float]"
}

// Unified variable entry — each codegen variable is exactly one of these kinds.
Var_Entry :: union {
    Scalar_Var,
    Array_Var,
    Struct_Var,
    Union_Var,
    Slice_Var,
    SSA_Var,
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
// slice header (see Slice_Var for layout); emission loads data+cap, bounds-checks
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
    array_utf8:        bool,         // if final is array — element type is utf8 (drives string-format print path)
    array_has_sentinel: bool,        // if final is array — sentinel-terminated
    array_sentinel:     int,         // if final is array — sentinel value
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
    ret_types:         []Type,           // multi-return list (len > 1 → multi-return via sret)
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

// One entry in the tuple-default cache: the slot pointers and types from
// a tuple-returning source call evaluated at the current call site.
Tuple_Default_Entry :: struct {
    ptrs:  [dynamic]string,
    types: [dynamic]string,
}

Codegen :: struct {
    out:         strings.Builder,  // current per-module IR buffer (swapped in from module_outs)
    alloca_buf:  strings.Builder,  // hoisted allocas (entry block)
    body_buf:    strings.Builder,  // temporary buffer for function body during alloca hoisting

    // Per-module IR buffers. Each function's IR lands in the buffer keyed by
    // its home_package; g.out is swapped to the right buffer before
    // gen_scope_def runs and copied back after. module_order tracks first-
    // seen order for deterministic final concatenation.
    //
    // Today the final-assembly step concats every buffer in order into a
    // single .ll file (preserving current downstream behaviour). The split
    // exists so a future phase can write each buffer to its own .ll and
    // run clang on them in parallel.
    module_outs:         map[string]strings.Builder,
    module_order:        [dynamic]string,
    current_module_home: string,  // the package whose buffer g.out currently holds (empty = not in a module section)

    // Imports per module: each module's set of `@<symbol>` references that
    // aren't defined locally. Populated by a post-emission walk of each
    // module's buffer. Used by the eventual per-`.ll` writer to emit
    // `declare` lines at the top of each module's file. LLVM intrinsics and
    // libc names (always declared per TU regardless) are excluded from this
    // set.
    module_imports:      map[string]map[string]bool,

    // Filesystem paths produced by generate_program — one .ll per module.
    // Populated at write time; read by main.odin to feed clang.
    module_ll_paths:     [dynamic]string,

    // Parallel-codegen task records. Each task carries per-module outputs
    // produced by the worker pool: the IR buffer, string_decls,
    // overflow_intrinsics used. Read at .ll-write time.
    module_tasks:        []^Module_Task,
    hoist_allocas: bool,           // true during function body codegen
    emitted_allocas: map[string]string, // track alloca names emitted in current function (name -> IR type for dedup)
    tmp_counter: int,              // %0, %1, %2 ...
    tmp_pool:    []string,         // pre-formatted "%tN" names; indexed by tmp_counter
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
    // Per-Codegen prefix for `@.str.N` names. Empty for the main thread
    // (preserves existing IR layout); set to a module-specific tag by
    // parallel codegen workers so each TU's strings live in its own
    // namespace.
    string_name_prefix: string,
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
    // Multi-return: list of return types for current function (empty if not multi-return)
    ret_types:        []Type,
    // Tuple call result: temp alloca pointers from the most recent tuple-returning call
    tuple_result_ptrs:  [dynamic]string,  // alloca names for each tuple element
    tuple_result_types: [dynamic]string,  // LLVM types for each tuple element
    // Per-call cache for Expr_Tuple_Default dedup: when multiple bindings in
    // a param group share one tuple source, the source is evaluated once at
    // each call site and the slot ptrs cached here keyed by source pointer.
    // Saved/restored around nested gen_call invocations so each call site
    // gets a fresh cache.
    tuple_default_cache: map[rawptr]Tuple_Default_Entry,
    // Fun_Info cache: avoids re-deriving from Checked_Scope on every call
    fun_info_cache:   map[string]Fun_Info,
    // Temp results: typed fields replacing magic __call_result / __field_result / __swizzle_result
    // in all_vars. Set by gen_call / gen_field_access / gen_swizzle_read_multi, claimed by callers.
    temp_call_result:    Maybe(Array_Var),   // array-returning function call
    temp_field_result:   Maybe(Var_Entry),   // aggregate field access (array, struct, or slice)
    temp_swizzle_result: Maybe(Array_Var),   // multi-component swizzle read
    // Overflow-checking intrinsics used (for declaration at end of module)
    overflow_intrinsics: map[string]bool,
    // `llvm.bswap.iN` widths used by `#big_endian` byte-buffer reads.
    // Declared per-module the same way overflow_intrinsics is.
    bswap_intrinsics: map[int]bool,
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

// Get a fresh temporary: %t1, %t2, etc.
//
// Called for every GEP, load, and store-to-tmp in codegen — millions of
// times on a large module. Returns a slice into a pre-allocated pool of
// `%t<N>` strings owned by the Codegen. The pool is built once at codegen
// start (see ensure_tmp_pool); subsequent fresh_tmp calls just index in.
// No per-call allocation, no format parsing.
fresh_tmp :: proc(g: ^Codegen) -> string {
    g.tmp_counter += 1
    if g.tmp_counter >= len(g.tmp_pool) {
        grow_tmp_pool(g, g.tmp_counter + 1)
    }
    return g.tmp_pool[g.tmp_counter]
}

// Build (or grow) the tmp-name pool so that every counter value up to
// `min_size - 1` has a pre-formatted `%t<N>` string. Each name is laid out
// in a single contiguous byte slab so the pool is just a `[]string` of
// views into that slab.
@(private="file")
grow_tmp_pool :: proc(g: ^Codegen, min_size: int) {
    new_cap := max(min_size, len(g.tmp_pool) * 2, 16 * 1024)
    new_pool := make([]string, new_cap)
    // Each name fits in 12 bytes ("%t" + up to 10 digits). Slab in one
    // contiguous block so the pool is friendly to the prefetcher.
    slab := make([]byte, new_cap * 12)
    for i in 0..<new_cap {
        off := i * 12
        slab[off]   = '%'
        slab[off+1] = 't'
        digits := strconv.write_int(slab[off+2:off+12], i64(i), 10)
        new_pool[i] = string(slab[off : off + 2 + len(digits)])
    }
    g.tmp_pool = new_pool
}

// Get a fresh label. Same hot-path concern as fresh_tmp.
fresh_label :: proc(g: ^Codegen, prefix: string) -> string {
    g.label_counter += 1
    buf := make([]byte, len(prefix) + 12, context.temp_allocator)
    copy(buf, prefix)
    digits := strconv.write_int(buf[len(prefix):], i64(g.label_counter), 10)
    return string(buf[:len(prefix) + len(digits)])
}

// Codegen-stage error: print a diagnostic and abort. Codegen runs only after
// type checking has passed, so reaching one of these sites is a compiler bug
// — a missed type checker case or an unimplemented codegen feature. Emitting
// broken IR and letting clang fail with a cryptic message hides the real
// cause. Pass `{}` as span when no source location is available.
codegen_fatal :: proc(g: ^Codegen, span: Span, format: string, args: ..any) -> ! {
    loc := ""
    if span.file != "" {
        loc = format_location(span.file, span.line, span.col)
    }
    emit_diagnostic(.Codegen_Error, loc, format, ..args)
    flush_diagnostics()
    os.exit(1)
}

// ---------------------------------------------------------------------------
// GEP / load / store helpers — reduce boilerplate across all codegen files
// ---------------------------------------------------------------------------

// Emit a GEP into a struct field: %tmp = getelementptr %StructType, ptr %base, i32 0, i32 <idx>
emit_field_gep :: proc(g: ^Codegen, llvm_type: string, base_ptr: string, field_idx: int) -> string {
    gep := fresh_tmp(g)
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, gep)
    strings.write_string(b, " = getelementptr ")
    strings.write_string(b, llvm_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, base_ptr)
    strings.write_string(b, ", i32 0, i32 ")
    strings.write_int(b, field_idx)
    strings.write_byte(b, '\n')
    return gep
}

// Load a value from a pointer: %tmp = load <ir_type>, ptr %src
emit_load :: proc(g: ^Codegen, ir_type: string, src_ptr: string) -> string {
    val := fresh_tmp(g)
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, val)
    strings.write_string(b, " = load ")
    strings.write_string(b, ir_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, src_ptr)
    strings.write_byte(b, '\n')
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
    emit_store(g, ir_type, val, gep)
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
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_double(g, fmt_ptr, val)
    case "float":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", ext, val)
        fmt_name, fmt_len := get_string_literal(g, "%g")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_double(g, fmt_ptr, ext)
    case "i1":
        fmt_name, fmt_len := get_string_literal(g, "%d")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        ext := fresh_tmp(g)
        emit(g, "  %s = zext i1 %s to i32", ext, val)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s)", fmt_ptr, ext)
    case "ptr":
        fmt_name, fmt_len := get_string_literal(g, "%s")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_ptr(g, fmt_ptr, val)
    case:
        ext := fresh_tmp(g)
        emit(g, "  %s = sext %s %s to i64", ext, ir_type, val)
        fmt_name, fmt_len := get_string_literal(g, "%lld")
        fmt_ptr := fresh_tmp(g)
        emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
        emit_printf_i64(g, fmt_ptr, ext)
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
            chain.array_utf8 = av.is_utf8
            chain.array_has_sentinel = av.has_sentinel
            chain.array_sentinel = av.sentinel
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
        // Pointer-to-struct: auto-deref. Pointer value may live in a
        // Scalar_Var alloca (mutable local) or directly as an SSA value
        // (immutable param — no alloca emitted, no load needed).
        if pt, pt_ok := e.type_.(^Type_Ptr); pt_ok {
            if sd := as_struct_body(pt.elem); sd != nil {
                ptr_val: string
                entry, entry_ok := g.all_vars[e.name]
                if !entry_ok { return false }
                #partial switch v in entry {
                case SSA_Var:    ptr_val = v.ssa
                case Scalar_Var: ptr_val = emit_load(g, "ptr", v.alloca)
                case:            return false
                }
                emit_null_check(g, ptr_val, e.name, e.span)
                chain.base_ptr = ptr_val
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
            if acap, aelem, autf8, asent, asentv, ok := field_array_info(f); ok {
                // Array field
                chain.final_type = fmt.tprintf("[%d x %s]", acap, aelem)
                chain.final_kind = .Array
                chain.array_cap = acap
                chain.array_elem = aelem
                chain.array_utf8 = autf8
                chain.array_has_sentinel = asent
                chain.array_sentinel = asentv
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
                // slice_header_bytes ({len, cap, ptr}), so the same chain end-state
                // and subsequent .len/.cap/.ptr access work for both.
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
            if acap, aelem, autf8, asent, asentv, ok := field_array_info(inner_f); ok {
                chain.final_type = fmt.tprintf("[%d x %s]", acap, aelem)
                chain.final_kind = .Array
                chain.array_cap = acap
                chain.array_elem = aelem
                chain.array_utf8 = autf8
                chain.array_has_sentinel = asent
                chain.array_sentinel = asentv
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
            // Evaluate index, bounds check (must happen before the GEP uses it).
            // Type checker guarantees idx_expr is already at slice header width.
            idx := gen_expr(g, s.index_expr, slice_layout.len_ir)
            emit_bounds_check(g, idx, fmt.tprintf("%d", s.capacity), s.name_hint, s.span)
            append(&indices, GEP_Index{slice_layout.len_ir, idx})

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
            emit_load_into(g, data_ptr, "ptr", data_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, current_ptr, SLICE.cap)
            cap_val := fresh_tmp(g)
            emit_typed_load_cap(g, cap_val, cap_gep)
            idx := gen_expr(g, s.index_expr, slice_layout.len_ir)
            emit_bounds_check(g, idx, cap_val, s.name_hint, s.span)
            elem_ptr := fresh_tmp(g)
            emit_elem_gep(g, elem_ptr, s.elem_type, data_ptr, idx, slice_layout.len_ir)
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

    // Return type: struct/array/multi-return/slice returns use void + sret convention
    if len(cf.return_types) > 1 {
        info.ret_type = "void"
        info.ret_types = cf.return_types[:]
    } else if len(cf.return_types) == 0 {
        info.ret_type = "void"
    } else {
        single := cf.return_types[0]
        if sd := as_struct_body(single); sd != nil {
            info.ret_type = "void"
            info.ret_struct = sd.name
        } else if fa, fa_ok := single.(^Type_Fixed_Array); fa_ok {
            info.ret_type = "void"
            info.ret_array_cap = fa.size
            info.ret_array_elem = llvm_type_from_checker(fa.elem)
        } else if sl, sl_ok := single.(^Type_Slice); sl_ok {
            info.ret_type = "void"
            info.ret_slice_elem = llvm_type_from_checker(sl.elem)
        } else if single == nil || is_untyped(single) {
            info.ret_type = "void"
        } else {
            info.ret_type = llvm_type_from_checker(single)
        }
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

// ---------------------------------------------------------------------------
// Fast IR emitters — direct builder writes, no fmt.tprintf
//
// emit() routes through fmt.tprintf, which parses the format string and
// reflects on each ..any argument for every call. For the half-dozen IR
// patterns that account for ~250+ call sites and the bulk of generated
// bytes, that overhead adds up — codegen on a 1M-line module spends a
// meaningful fraction of its time in tprintf machinery. These typed
// helpers write straight to the builder with no format parsing or
// reflection. Use them for any pattern that shows up in the hot IR path;
// reach for emit() when the pattern is one-off or fmt's flexibility is
// actually needed.
// ---------------------------------------------------------------------------

// Pick the builder a non-alloca line should land in, honoring the alloca-
// hoist mode. Allocas have their own dedup path through emit_line; non-
// alloca emits can skip that entire branch.
@(private="file")
emit_target :: proc(g: ^Codegen) -> ^strings.Builder {
    if g.hoist_allocas { return &g.body_buf }
    return &g.out
}

// `  store <ir_type> <val>, ptr <ptr>\n`
emit_store :: proc(g: ^Codegen, ir_type, val, ptr: string) {
    b := emit_target(g)
    strings.write_string(b, "  store ")
    strings.write_string(b, ir_type)
    strings.write_byte(b, ' ')
    strings.write_string(b, val)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, ptr)
    strings.write_byte(b, '\n')
}

// `  <dst> = load <ir_type>, ptr <ptr>\n`
// Explicit-dst load. Mirror of emit_load (which allocates a fresh tmp)
// for sites where the caller already has a name picked out.
emit_load_into :: proc(g: ^Codegen, dst, ir_type, src_ptr: string) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = load ")
    strings.write_string(b, ir_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, src_ptr)
    strings.write_byte(b, '\n')
}

// `  <dst> = getelementptr <agg_type>, ptr <base>, i32 0, i32 <idx>\n`
// Explicit-dst struct-field GEP. Mirror of emit_field_gep.
emit_field_gep_into :: proc(g: ^Codegen, dst, agg_type, base: string, idx: int) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = getelementptr ")
    strings.write_string(b, agg_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, base)
    strings.write_string(b, ", i32 0, i32 ")
    strings.write_int(b, idx)
    strings.write_byte(b, '\n')
}

// `  <dst> = getelementptr <arr_type>, ptr <base>, i64 0, i64 <idx>\n`
// Constant-index array GEP. Same shape as emit_field_gep_into but i64 for
// the element index, matching the array-element GEP convention.
emit_array_gep_const :: proc(g: ^Codegen, dst, arr_type, base: string, idx: int) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = getelementptr ")
    strings.write_string(b, arr_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, base)
    strings.write_string(b, ", i64 0, i64 ")
    strings.write_int(b, idx)
    strings.write_byte(b, '\n')
}

// `  <dst> = getelementptr <arr_type>, ptr <base>, i64 0, <idx_ir> <idx>\n`
// Variable-index array GEP — `idx` is an SSA name string, not a constant.
// `idx_ir` is the LLVM IR type of `idx`; callers pass slice_layout.len_ir
// when the index comes from a user expression / slice header, "i32" when
// it comes from a fixed-position counter, etc. No default — every call
// site states the index width explicitly so the slice-header width flip
// (i32 ↔ i64) propagates correctly.
emit_array_gep_var :: proc(g: ^Codegen, dst, arr_type, base, idx, idx_ir: string) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = getelementptr ")
    strings.write_string(b, arr_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, base)
    strings.write_string(b, ", i64 0, ")
    strings.write_string(b, idx_ir)
    strings.write_byte(b, ' ')
    strings.write_string(b, idx)
    strings.write_byte(b, '\n')
}

// `  <dst> = getelementptr <elem_type>, ptr <base>, <idx_ir> <idx>\n`
// Element-step GEP for raw element pointers (slice data pointers, VLA bases).
// One-dimensional version: no outer `i64 0` because base already points at
// the element-typed array. `idx_ir` is the LLVM type of `idx` — no default
// so every call site states the index width.
emit_elem_gep :: proc(g: ^Codegen, dst, elem_type, base, idx, idx_ir: string) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = getelementptr ")
    strings.write_string(b, elem_type)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, base)
    strings.write_string(b, ", ")
    strings.write_string(b, idx_ir)
    strings.write_byte(b, ' ')
    strings.write_string(b, idx)
    strings.write_byte(b, '\n')
}

// `  <dst> = alloca <ir_type>\n`
// Fast alloca emitter — direct write to the right builder, honoring alloca-
// hoist mode. The emit() path was kept on the slow path historically for
// dedup, but the dedup logic is purely about which buffer to write to and
// whether to skip a duplicate name; doing both inline is straightforward.
emit_alloca :: proc(g: ^Codegen, dst, ir_type: string) {
    if g.hoist_allocas {
        // Dedup: same alloca name in multiple branches collapses to one.
        if dst in g.emitted_allocas { return }
        g.emitted_allocas[dst] = ir_type
        b := &g.alloca_buf
        strings.write_string(b, "  ")
        strings.write_string(b, dst)
        strings.write_string(b, " = alloca ")
        strings.write_string(b, ir_type)
        strings.write_byte(b, '\n')
        return
    }
    b := &g.out
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = alloca ")
    strings.write_string(b, ir_type)
    strings.write_byte(b, '\n')
}

// `  <dst> = getelementptr [<byte_len> x i8], ptr <global>, i64 0, i64 0\n`
// String-literal address: turn a `@.strN` global into a `ptr` SSA. Used for
// every printf format reference and string-literal byte buffer.
emit_string_gep :: proc(g: ^Codegen, dst: string, byte_len: int, global: string) {
    b := emit_target(g)
    strings.write_string(b, "  ")
    strings.write_string(b, dst)
    strings.write_string(b, " = getelementptr [")
    strings.write_int(b, byte_len)
    strings.write_string(b, " x i8], ptr ")
    strings.write_string(b, global)
    strings.write_string(b, ", i64 0, i64 0\n")
}

// `  call void @llvm.memcpy.p0.p0.i64(ptr <dst>, ptr <src>, i64 <bytes>, i1 false)\n`
emit_memcpy :: proc(g: ^Codegen, dst, src: string, bytes: int) {
    b := emit_target(g)
    strings.write_string(b, "  call void @llvm.memcpy.p0.p0.i64(ptr ")
    strings.write_string(b, dst)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, src)
    strings.write_string(b, ", i64 ")
    strings.write_int(b, bytes)
    strings.write_string(b, ", i1 false)\n")
}

// `  call void @llvm.memset.p0.i64(ptr <dst>, i8 0, i64 <bytes>, i1 false)\n`
emit_memset_zero :: proc(g: ^Codegen, dst: string, bytes: int) {
    b := emit_target(g)
    strings.write_string(b, "  call void @llvm.memset.p0.i64(ptr ")
    strings.write_string(b, dst)
    strings.write_string(b, ", i8 0, i64 ")
    strings.write_int(b, bytes)
    strings.write_string(b, ", i1 false)\n")
}

// `  br label %<label>\n`
emit_br :: proc(g: ^Codegen, label: string) {
    b := emit_target(g)
    strings.write_string(b, "  br label %")
    strings.write_string(b, label)
    strings.write_byte(b, '\n')
}

// `  br i1 <cond>, label %<true_label>, label %<false_label>\n`
emit_cond_br :: proc(g: ^Codegen, cond, true_label, false_label: string) {
    b := emit_target(g)
    strings.write_string(b, "  br i1 ")
    strings.write_string(b, cond)
    strings.write_string(b, ", label %")
    strings.write_string(b, true_label)
    strings.write_string(b, ", label %")
    strings.write_string(b, false_label)
    strings.write_byte(b, '\n')
}

// `<name>:\n` — basic-block label. No leading indent (it's a target, not an
// instruction).
emit_label :: proc(g: ^Codegen, name: string) {
    b := emit_target(g)
    strings.write_string(b, name)
    strings.write_string(b, ":\n")
}

// printf helpers: each variant matches a specific arg shape used by Mara's
// built-in `print` lowering. The void variant is fmt-only; the others take
// one typed arg of the indicated LLVM type.

// `  call i32 (ptr, ...) @printf(ptr <fmt>)\n`
emit_printf_void :: proc(g: ^Codegen, fmt_ptr: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) @printf(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, i64 <val>)\n`
emit_printf_i64 :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) @printf(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", i64 ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, ptr <val>)\n`
emit_printf_ptr :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) @printf(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, double <val>)\n`
emit_printf_double :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) @printf(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", double ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// Switch g.out to the IR buffer owned by `home_package`. Creates the buffer
// (with the same 4 MB pre-size used for single-file builds) on first use
// and records the package in module_order so the final assembly step gets a
// deterministic emission order.
//
// Pattern at every call site: capture the *previous* buffer state back into
// the map before switching, since [dynamic]u8 growth produces a new backing
// pointer that lives only on the current copy.
switch_to_module :: proc(g: ^Codegen, home_package: string) {
    // Capture growth from the buffer we're leaving. The previously-active
    // module records its state via g.current_module_home (set just below).
    if g.current_module_home != "" {
        g.module_outs[g.current_module_home] = g.out
    }
    if _, exists := g.module_outs[home_package]; !exists {
        b: strings.Builder
        strings.builder_init_len_cap(&b, 0, 4 * 1024 * 1024)
        g.module_outs[home_package] = b
        append(&g.module_order, home_package)
    }
    g.out = g.module_outs[home_package]
    g.current_module_home = home_package
}

// ---------------------------------------------------------------------------
// Parallel per-module codegen
// ---------------------------------------------------------------------------
//
// Each module's functions can be codegen'd independently of every other
// module's. Module_Task carries one module's worth of work + outputs; the
// thread pool dispatches tasks to N worker threads, each running on its
// own virtual.Arena allocator so per-codegen allocations don't contend.
//
// Workers run a stripped-down Codegen with the same read-only state as the
// main thread (checked, target settings, registered struct types) but
// private mutable state (tmp_pool, all_vars, string_decls, etc.). After
// pool_finish, the main thread copies each task's outputs into main_g and
// continues with the sequential @main + .ll write phases.

Module_Task :: struct {
    // Inputs — set by the main thread before spawn
    main_g:      ^Codegen,
    checked:     ^Checked_Program,
    module_name: string,
    fn_names:    []string,
    web:         bool,
    shared_mode: bool,

    // Per-worker arena. Outlives the worker proc so the main thread can
    // read task.out / string_decls / overflow_intrinsics in arena memory.
    // Destroyed when generate_program is fully done (or just left to be
    // reclaimed at process exit — Mara's overall arena does the same).
    arena:       virtual.Arena,

    // Outputs — populated by the worker proc
    out:                 strings.Builder,
    string_literals:     map[string]string,
    string_decls:        [dynamic]string,
    string_counter:      int,
    overflow_intrinsics: map[string]bool,
    bswap_intrinsics:    map[int]bool,
    imports:             map[string]bool,
}

// Worker entry point. Sets up an isolated arena allocator, builds a local
// Codegen with the right read-only state copied from main_g, and emits
// every function assigned to this task.
@(private="file")
module_codegen_worker :: proc(t: thread.Task) {
    task := cast(^Module_Task)t.data

    // Each worker gets its own arena. Allocations (string interning,
    // tmp-pool buffers, all_vars maps, AST clone bookkeeping, etc.) all
    // land here. Outputs we want to survive into the main thread are
    // built directly in this arena; they remain valid as long as the
    // arena does, which is the lifetime of generate_program.
    _ = virtual.arena_init_growing(&task.arena)
    arena_alloc := virtual.arena_allocator(&task.arena)
    context.allocator = arena_alloc
    context.temp_allocator = arena_alloc

    local: Codegen
    init_worker_codegen(&local, task)

    // Emit this module's functions. switch_to_module + flush handle the
    // g.out buffer swap so emit_target routes correctly.
    switch_to_module(&local, task.module_name)
    for fn_name in task.fn_names {
        cf, cf_ok := task.checked.functions[fn_name]
        if !cf_ok { continue }
        gen_scope_def(&local, &cf)
    }
    flush_current_module(&local)

    // Surface the per-module state into the task struct so the main
    // thread can pick it up after pool_finish.
    if buf, ok := local.module_outs[task.module_name]; ok {
        task.out = buf
    }
    task.string_literals     = local.string_literals
    task.string_decls        = local.string_decls
    task.string_counter      = local.string_counter
    task.overflow_intrinsics = local.overflow_intrinsics
    task.bswap_intrinsics    = local.bswap_intrinsics
}

// Build a Codegen suitable for one worker. Read-only fields (checked,
// target flags, arena_*_name, registered struct decls) come straight from
// main_g. Mutable per-function state (tmp_pool, all_vars, …) starts empty
// and lives in the worker's arena.
@(private="file")
init_worker_codegen :: proc(g: ^Codegen, task: ^Module_Task) {
    g.checked            = task.checked
    g.web                = task.web
    g.shared             = task.shared_mode
    g.context_enabled    = task.main_g.context_enabled
    g.arena_alloc_name   = task.main_g.arena_alloc_name
    g.arena_mark_name    = task.main_g.arena_mark_name
    g.arena_reset_name   = task.main_g.arena_reset_name
    g.arena_new_name     = task.main_g.arena_new_name
    g.arena_alloc_has_debug = task.main_g.arena_alloc_has_debug

    // Per-worker string-name prefix so this task's `@.str.N` references
    // can never collide with the main thread's (used by @main emission)
    // or with any other worker's. Sanitize the module name so it's a
    // legal LLVM identifier component.
    safe, _ := strings.replace_all(task.module_name, ".", "_")
    g.string_name_prefix = strings.concatenate({safe, "_"})

    // Struct decls live on main_g; workers reach into g.checked.* for
    // type metadata they need. We deliberately do NOT copy struct_decls
    // here — the .ll-write phase uses main_g.struct_decls as the shared
    // type-definition block in every TU's prelude.
}

// Capture g.out's current state back to its module slot. Call once after the
// last gen_scope_def in a phase so the final assembly step sees the latest
// buffer state.
flush_current_module :: proc(g: ^Codegen) {
    if g.current_module_home != "" {
        g.module_outs[g.current_module_home] = g.out
        g.current_module_home = ""
    }
}

// True if `c` is a legal continuation byte in an LLVM identifier. LLVM
// allows letters, digits, '_', '.', and '$' inside identifiers (and dollars
// don't actually appear in Mara-emitted IR but we keep them for safety).
@(private="file")
is_ir_ident_byte :: proc(c: byte) -> bool {
    return (c >= 'a' && c <= 'z') ||
           (c >= 'A' && c <= 'Z') ||
           (c >= '0' && c <= '9') ||
           c == '_' || c == '.' || c == '$'
}

// True if the `@<name>` token at `at` in `ir` is a definition (the start of
// a `define ...` line or a global-variable assignment `@name = ...`). The
// heuristic: check what's at the start of the current line — `define ` /
// `declare ` mean a function definition/declaration; otherwise look for a
// ` = ` right after the identifier (global initializer). Anything else is a
// reference.
@(private="file")
is_ir_definition :: proc(ir: string, at_token, end_of_token: int) -> bool {
    // Walk back to the start of this line.
    line_start := at_token
    for line_start > 0 && ir[line_start-1] != '\n' { line_start -= 1 }
    line_prefix := ir[line_start:at_token]
    if strings.has_prefix(strings.trim_left(line_prefix, " \t"), "define ") { return true }
    if strings.has_prefix(strings.trim_left(line_prefix, " \t"), "declare ") { return true }
    // Global initializer: `@name = ...`
    j := end_of_token
    for j < len(ir) && (ir[j] == ' ' || ir[j] == '\t') { j += 1 }
    if j < len(ir) && ir[j] == '=' { return true }
    return false
}

// Debug-build summary of per-module imports. Reads cleanly enough to spot-
// check whether a module's imports match what its source code calls.
@(private="file")
dump_module_imports :: proc(g: ^Codegen) {
    fmt.printf("\n=== Per-module imports ===\n")
    for module_name in g.module_order {
        imports := g.module_imports[module_name]
        fmt.printf("[%s] %d imports", module_name, len(imports))
        if len(imports) == 0 {
            fmt.printf("\n")
            continue
        }
        names: [dynamic]string
        defer delete(names)
        for n in imports { append(&names, n) }
        slice.sort(names[:])
        fmt.printf(": ")
        for n, i in names {
            if i > 0 { fmt.printf(", ") }
            fmt.printf("@%s", n)
            if i == 4 && len(names) > 6 {
                fmt.printf(", ... (%d more)", len(names) - 5)
                break
            }
        }
        fmt.printf("\n")
    }
    fmt.printf("===========================\n\n")
}

// Build module_imports by walking each module's buffer for `@<name>`
// references and subtracting the locally-defined names. Skips well-known
// categories every TU declares anyway (libc, LLVM intrinsics, the per-TU
// `@.str.N` globals). Pass `main_extras_ir` to fold extra IR text
// (typically the @main entry-point block) into the main TU's import set.
compute_module_imports :: proc(g: ^Codegen, main_package, main_extras_ir: string) {
    g.module_imports = make(map[string]map[string]bool)
    skip_libc :: proc(name: string) -> bool {
        return name == "printf" || name == "exit" || name == "strlen"
    }
    scan :: proc(ir: string, defined, referenced: ^map[string]bool) {
        i := 0
        for i < len(ir) {
            if ir[i] != '@' { i += 1; continue }
            start := i + 1
            end := start
            for end < len(ir) && is_ir_ident_byte(ir[end]) { end += 1 }
            if end == start { i += 1; continue }
            name := ir[start:end]
            if is_ir_definition(ir, i, end) {
                defined[name] = true
            } else {
                referenced[name] = true
            }
            i = end
        }
    }
    for module_name in g.module_order {
        defined: map[string]bool
        referenced: map[string]bool
        buf := g.module_outs[module_name]
        scan(strings.to_string(buf), &defined, &referenced)
        // The main TU also gets @main's references — those calls
        // (Arena init, args setup, dispatch into user `main`) are emitted
        // into main_builder, not into the module's own buffer.
        if module_name == main_package && main_extras_ir != "" {
            scan(main_extras_ir, &defined, &referenced)
        }
        imports: map[string]bool
        for name in referenced {
            if name in defined { continue }
            if strings.has_prefix(name, "llvm.") { continue }
            // String globals: `.str.N` (main-thread namespace) or
            // `.<module>_str.N` (per-worker namespace). All start with '.'
            // and live in the local TU's `private` linkage block; never
            // imports.
            if len(name) > 0 && name[0] == '.' { continue }
            if skip_libc(name) { continue }
            imports[name] = true
        }
        g.module_imports[module_name] = imports
    }
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

// Usable capacity: hide the sentinel slot from user-facing bounds.
// Switched from is_utf8 to has_sentinel — the bit that actually says "one
// slot is reserved". They coincide for every utf8 array today (the type
// checker forces utf8 storage to declare a sentinel), but a hypothetical
// `[10, -1]i64` would have has_sentinel=true and is_utf8=false; the right
// rule is to hide the slot whenever it exists.
usable_cap :: proc(av: ^Array_Var) -> int {
    if av.has_sentinel {
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

// Pull array-field metadata out of the Mara type. Returns ok=false for
// non-fixed-array fields. Centralises what was previously open-coded at
// each Array_Var construction site, including the brittle inference
// `is_utf8 = (aelem == "i8")` that would have falsely tagged a [N]byte
// field as utf8.
field_array_info :: proc(f: ^Struct_Type_Field) -> (cap: int, elem_ir: string, is_utf8: bool, has_sentinel: bool, sentinel: int, ok: bool) {
    fa, fa_ok := distinct_base(f.type_).(^Type_Fixed_Array)
    if !fa_ok { return }
    _, is_utf8 = fa.elem.(Type_Utf8)
    return fa.size, llvm_type_from_checker(fa.elem), is_utf8, fa.has_sentinel, fa.sentinel, true
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
            // Width comes from a closed set — return interned constants
            // instead of allocating a fresh "i%d" string each call. This is
            // a hot path (every expr_ir_type query).
            // bits=0 → word-sized (usize/isize); read the module-local flag
            // set by generate_program — wasm32 → i32, x86-64 → i64.
            switch v.bits {
            case 0:   return "i32" if word_size_is_32 else "i64"
            case 8:   return "i8"
            case 16:  return "i16"
            case 32:  return "i32"
            case 64:  return "i64"
            case 128: return "i128"
            }
            panic(fmt.tprintf("llvm_type_from_checker: unexpected integer width %d", v.bits))
        case .Float:
            switch v.bits {
            case 16: return "half"
            case 32: return "float"
            case 64: return "double"
            }
            panic(fmt.tprintf("llvm_type_from_checker: unexpected float width %d", v.bits))
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
    case ^Type_Distinct:    return llvm_type_from_checker(v.base_type)
    case Type_Const_Int:    return "i64" // const generic param — should not appear in codegen
    case Type_Runtime_Size: return "i64" // runtime size — should not appear as field type
    case Type_Any:          return "i64" // default to i64 for untyped
    case Type_Void:         return "{}"  // zero-sized struct — LLVM coalesces
    case Type_Error:        return "i64" // error recovery default
    case Type_Err:          return "i32" // open error type — u32 (set_id<<16 | tag)
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
    // Per-worker string-name prefix lets each parallel codegen invent its
    // own @.str.<N> namespace without coordinating with the others. The
    // main thread uses an empty prefix so existing behaviour and tests
    // see `@.str.N` unchanged.
    name: string
    if g.string_name_prefix == "" {
        name = fmt.tprintf("@.str.%d", g.string_counter)
    } else {
        name = fmt.tprintf("@.%sstr.%d", g.string_name_prefix, g.string_counter)
    }
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

// Emit a runtime bounds check: if idx < 0 or idx >= len, print error and exit(1).
// Both `idx` and `len` are at slice header width (slice_layout.len_ir).
// `name` is the variable name for the error message.
// Module-level helpers for the runtime fail blocks. Emitted once per module;
// per-site fail blocks shrink to `call helper(...) + unreachable`. `loc` and
// `name` are passed as ptr args referencing get_string_literal globals —
// those already dedupe, so identical loc/name across many sites share
// storage. Functions are `internal` linkage so the linker dead-strips any
// unused kind. Helper names are constants so call sites stay readable.
__MARA_BOUNDS_FAIL    :: "@__mara_bounds_fail"
__MARA_OVERFLOW_FAIL  :: "@__mara_overflow_fail"
__MARA_NULL_FAIL      :: "@__mara_null_fail"
__MARA_DIVZ_FAIL      :: "@__mara_divz_fail"
__MARA_SLICE_LEN_FAIL :: "@__mara_slice_len_fail"

runtime_fail_helpers_ir :: proc(g: ^Codegen) -> string {
    // Register format strings as deduped globals via the normal literals path.
    fmt_bounds,    _ := get_string_literal(g, "%s runtime error: index %d out of bounds [0, %d) for '%s'\n")
    fmt_overflow,  _ := get_string_literal(g, "%s runtime error: integer overflow\n")
    fmt_null,      _ := get_string_literal(g, "%s runtime error: null pointer dereference: '%s' is null\n")
    fmt_divz,      _ := get_string_literal(g, "%s runtime error: division by zero\n")
    fmt_slice_len, _ := get_string_literal(g, "%s runtime error: slice len %d not in [0, %d] (cap) for '%s'\n")

    b: strings.Builder
    strings.builder_init(&b)
    strings.write_string(&b, "; Runtime fail-block helpers (hoisted)\n")

    // bounds: (loc, idx, len, name). idx / len at slice header width (i32).
    //
    // Default (external) linkage so per-module .ll files can reference these
    // via `declare` lines instead of duplicating the definition. Main TU
    // owns the definition; every other TU gets just the declare.
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_BOUNDS_FAIL)
    strings.write_string(&b, "(ptr %loc, i32 %idx, i32 %len, ptr %name) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_bounds,
        ", ptr %loc, i32 %idx, i32 %len, ptr %name)\n",
    }))
    strings.write_string(&b, "  call void @exit(i32 1)\n  unreachable\n}\n\n")

    // overflow: (loc)
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_OVERFLOW_FAIL)
    strings.write_string(&b, "(ptr %loc) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_overflow, ", ptr %loc)\n",
    }))
    strings.write_string(&b, "  call void @exit(i32 1)\n  unreachable\n}\n\n")

    // null: (loc, name)
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_NULL_FAIL)
    strings.write_string(&b, "(ptr %loc, ptr %name) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_null, ", ptr %loc, ptr %name)\n",
    }))
    strings.write_string(&b, "  call void @exit(i32 1)\n  unreachable\n}\n\n")

    // divz: (loc)
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_DIVZ_FAIL)
    strings.write_string(&b, "(ptr %loc) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_divz, ", ptr %loc)\n",
    }))
    strings.write_string(&b, "  call void @exit(i32 1)\n  unreachable\n}\n\n")

    // slice_len: (loc, new_len, cap, name). Fires on direct `s.len = X` writes
    // where X is outside [0, cap] — keeps the slice invariant honest even when
    // user code (FFI fill patterns, manual bookkeeping) sets len directly.
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_SLICE_LEN_FAIL)
    strings.write_string(&b, "(ptr %loc, i32 %new_len, i32 %cap, ptr %name) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_slice_len,
        ", ptr %loc, i32 %new_len, i32 %cap, ptr %name)\n",
    }))
    strings.write_string(&b, "  call void @exit(i32 1)\n  unreachable\n}\n\n")

    // print_err: prints the qualified name of a u32 error value (set_id<<16 |
    // tag). One switch case per (set_id, tag) pair across all error_kinds
    // in the program; the 0 case is the universal `.Ok` and the default falls
    // back to "?(<val>)" for stray bits / out-of-range tags. Open-`err`-typed
    // print sites call this; concrete error_kind print sites still use the
    // inline switch from gen_print_enum.
    strings.write_string(&b, runtime_print_err_helper_ir(g))

    return strings.to_string(b)
}

runtime_print_err_helper_ir :: proc(g: ^Codegen) -> string {
    Variant_Case :: struct { value: int, qualified_name: string }
    cases := make([dynamic]Variant_Case, 0, 16, context.temp_allocator)
    for _, et in g.checked.table.enums {
        if !et.is_error_kind { continue }
        for vname, value in et.variants {
            if value == 0 { continue }  // .Ok handled once below
            qname := strings.concatenate({et.source_name, ".", vname}, context.temp_allocator)
            append(&cases, Variant_Case{value = value, qualified_name = qname})
        }
    }
    slice.sort_by(cases[:], proc(a, b: Variant_Case) -> bool { return a.value < b.value })

    // Register all the format strings via the global literal cache so each
    // one becomes a stable rodata global the helper can GEP.
    ok_str, _ := get_string_literal(g, "Ok")
    fmt_str_s, _ := get_string_literal(g, "%s")
    fmt_unknown, _ := get_string_literal(g, "?(%u)")
    case_strs := make([dynamic]string, 0, len(cases), context.temp_allocator)
    for c in cases {
        s, _ := get_string_literal(g, c.qualified_name)
        append(&case_strs, s)
    }

    b: strings.Builder
    strings.builder_init(&b)
    strings.write_string(&b, "define void @__mara_print_err(i32 %val) {\nentry:\n")
    strings.write_string(&b, "  switch i32 %val, label %unknown [\n")
    strings.write_string(&b, "    i32 0, label %ok\n")
    for c, i in cases {
        strings.write_string(&b, fmt.tprintf("    i32 %d, label %%case_%d\n", c.value, i))
    }
    strings.write_string(&b, "  ]\nok:\n")
    strings.write_string(&b, strings.concatenate({
        "  %ok_s = getelementptr [3 x i8], ptr ", ok_str, ", i64 0, i64 0\n",
        "  %fmt_s = getelementptr [3 x i8], ptr ", fmt_str_s, ", i64 0, i64 0\n",
        "  call i32 (ptr, ...) @printf(ptr %fmt_s, ptr %ok_s)\n",
        "  ret void\n",
    }))
    for c, i in cases {
        lit_global := case_strs[i]
        lit_len := len(c.qualified_name) + 1
        strings.write_string(&b, fmt.tprintf("case_%d:\n", i))
        strings.write_string(&b, fmt.tprintf("  %%cs_%d = getelementptr [%d x i8], ptr %s, i64 0, i64 0\n", i, lit_len, lit_global))
        strings.write_string(&b, fmt.tprintf("  %%fs_%d = getelementptr [3 x i8], ptr %s, i64 0, i64 0\n", i, fmt_str_s))
        strings.write_string(&b, fmt.tprintf("  call i32 (ptr, ...) @printf(ptr %%fs_%d, ptr %%cs_%d)\n", i, i))
        strings.write_string(&b, "  ret void\n")
    }
    strings.write_string(&b, "unknown:\n")
    strings.write_string(&b, strings.concatenate({
        "  %unk_fmt = getelementptr [6 x i8], ptr ", fmt_unknown, ", i64 0, i64 0\n",
        "  call i32 (ptr, ...) @printf(ptr %unk_fmt, i32 %val)\n",
        "  ret void\n",
    }))
    strings.write_string(&b, "}\n")
    return strings.to_string(b)
}

emit_bounds_check :: proc(g: ^Codegen, idx: string, len_val: string, name: string, span: Span = {}) {
    // Compile-time elision: if both idx and len_val are integer literals
    // and 0 <= idx < len_val, the check would always pass — skip emission
    // entirely. Covers `arr[3]` against a fixed-size array, sentinel index
    // accesses, and other constant-fold paths.
    if can_elide_bounds_check(idx, len_val) {
        return
    }

    ok_label   := fresh_label(g, "bounds.ok")
    fail_label := fresh_label(g, "bounds.fail")

    // Both idx and len_val are at slice_layout.len_ir (i32 today) —
    // caller guarantees by passing values from the natural-width load
    // helpers or matching-width arithmetic.
    w := slice_layout.len_ir
    neg_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, 0", neg_cmp, w, idx)
    upper_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sge %s %s, %s", upper_cmp, w, idx, len_val)
    combined := fresh_tmp(g)
    emit(g, "  %s = or i1 %s, %s", combined, neg_cmp, upper_cmp)
    emit_cond_br(g, combined, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := format_location(span.file, span.line, span.col)
    loc_global,  _ := get_string_literal(g, loc)
    name_global, _ := get_string_literal(g, name)
    emit(g, "  call void %s(ptr %s, %s %s, %s %s, ptr %s)",
        __MARA_BOUNDS_FAIL, loc_global, w, idx, w, len_val, name_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
}

// True if `idx` and `len_val` are both integer-literal IR operands and the
// index would always pass the bounds check. Both come into codegen as
// strings — either SSA tmp names (`%t42`) or literal integer text (`5`).
// `strconv.parse_i64` returns false for SSA tmps (the leading `%` rejects),
// so this is a safe narrow check.
can_elide_bounds_check :: proc(idx: string, len_val: string) -> bool {
    idx_i, idx_ok := strconv.parse_i64(idx)
    if !idx_ok { return false }
    len_i, len_ok := strconv.parse_i64(len_val)
    if !len_ok { return false }
    return idx_i >= 0 && idx_i < len_i
}

// Emit a runtime null pointer check: if ptr == null, dispatch to the hoisted
// fail helper. Per-site cost is the compare + branch + 2 lines fail tail.
emit_null_check :: proc(g: ^Codegen, ptr_val: string, name: string, span: Span = {}) {
    ok_label := fresh_label(g, "null.ok")
    fail_label := fresh_label(g, "null.fail")

    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp eq ptr %s, null", cmp, ptr_val)
    emit_cond_br(g, cmp, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := format_location(span.file, span.line, span.col)
    loc_global,  _ := get_string_literal(g, loc)
    name_global, _ := get_string_literal(g, name)
    emit(g, "  call void %s(ptr %s, ptr %s)", __MARA_NULL_FAIL, loc_global, name_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
}

// Emit a runtime division-by-zero check. Compile-time elide when the divisor
// is a non-zero integer literal — `x / 4` never traps. Per-site cost otherwise
// is the compare + branch + 2 lines fail tail.
emit_div_zero_check :: proc(g: ^Codegen, divisor: string, ir_type: string, span: Span = {}) {
    if d, ok := strconv.parse_i64(divisor); ok && d != 0 {
        return
    }
    ok_label := fresh_label(g, "divz.ok")
    fail_label := fresh_label(g, "divz.fail")

    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp eq %s %s, 0", cmp, ir_type, divisor)
    emit_cond_br(g, cmp, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := format_location(span.file, span.line, span.col)
    loc_global, _ := get_string_literal(g, loc)
    emit(g, "  call void %s(ptr %s)", __MARA_DIVZ_FAIL, loc_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
}

// Emit an overflow-checked integer arithmetic operation using LLVM intrinsics.
// `op` is one of "sadd"/"ssub"/"smul"/"uadd"/"usub"/"umul". Returns the result
// temporary. On overflow: dispatches to the hoisted helper.
//
// Compile-time elision: when both operands are integer literals AND the result
// provably fits in the target type, skip the intrinsic and emit a plain
// add/sub/mul. If the result would overflow, fall through to the runtime check
// (LLVM will then const-fold it to an unconditional trap).
emit_checked_arith :: proc(g: ^Codegen, op: string, ir_type: string, left: string, right: string, span: Span = {}) -> string {
    if can_elide_overflow(op, ir_type, left, right) {
        result := fresh_tmp(g)
        op_short := op[1:]  // "sadd"/"uadd" → "add", etc.
        emit(g, "  %s = %s %s %s, %s", result, op_short, ir_type, left, right)
        return result
    }

    ok_label   := fresh_label(g, "overflow.ok")
    fail_label := fresh_label(g, "overflow.fail")

    intrinsic_name := fmt.tprintf("llvm.%s.with.overflow.%s", op, ir_type)
    g.overflow_intrinsics[intrinsic_name] = true

    pair := fresh_tmp(g)
    ret_type := strings.concatenate({"{ ", ir_type, ", i1 }"})
    emit_raw(g, strings.concatenate({"  ", pair, " = call ", ret_type, " @", intrinsic_name, "(", ir_type, " ", left, ", ", ir_type, " ", right, ")"}))

    result   := fresh_tmp(g)
    overflow := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", result,   " = extractvalue ", ret_type, " ", pair, ", 0"}))
    emit_raw(g, strings.concatenate({"  ", overflow, " = extractvalue ", ret_type, " ", pair, ", 1"}))

    emit_cond_br(g, overflow, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := format_location(span.file, span.line, span.col)
    loc_global, _ := get_string_literal(g, loc)
    emit(g, "  call void %s(ptr %s)", __MARA_OVERFLOW_FAIL, loc_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
    return result
}

// True if both operands are integer literals AND the computed result provably
// fits in `ir_type`. For i64 (or unknown widths) we conservatively decline so
// we never need to detect i64 arithmetic overflow at codegen time; the runtime
// intrinsic handles those cases (LLVM folds it in optimized builds).
can_elide_overflow :: proc(op, ir_type, left, right: string) -> bool {
    l_val, lok := strconv.parse_i64(left)
    if !lok { return false }
    r_val, rok := strconv.parse_i64(right)
    if !rok { return false }

    bits: uint
    switch ir_type {
    case "i8":  bits = 8
    case "i16": bits = 16
    case "i32": bits = 32
    case:       return false   // i64 or unknown — defer to runtime check
    }

    // i32-or-narrower inputs in i64 arithmetic can't overflow i64.
    result: i64
    switch op[1:] {
    case "add": result = l_val + r_val
    case "sub": result = l_val - r_val
    case "mul": result = l_val * r_val
    case:       return false
    }

    if op[0] == 'u' {
        max_excl := i64(1) << bits
        return result >= 0 && result < max_excl
    }
    max_excl := i64(1) << (bits - 1)
    return result >= -max_excl && result < max_excl
}


// ---------------------------------------------------------------------------
// Context system: automatic scope-based arena mark/reset
// ---------------------------------------------------------------------------

// Element size in bytes for a given LLVM type string.
elem_byte_size :: proc(elem_type: string, checked: ^Checked_Program = nil) -> int {
    ptr_size := 4 if word_size_is_32 else 8
    switch elem_type {
    case "i128":        return 16
    case "i64":         return 8
    case "double":      return 8
    case "ptr":         return ptr_size
    case "i32":         return 4
    case "float":       return 4
    case "i16":         return 2
    case "half":        return 2
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
    // Partial-array IR shape: `{ i32, i32, ptr, [N x T] }`. The first three
    // slots are the slice header (size = slice_header_bytes); the trailing
    // [N x T] is the inline storage. Without this branch, the type falls
    // through to ptr_size and a struct holding such a field is sized as if
    // the field were 8 bytes — undersized memsets clobber the storage and
    // leave field headers (ptr/cap) zero. Bit me on String fields.
    if strings.has_prefix(elem_type, PARTIAL_ARRAY_HEADER_PREFIX) {
        cap, elem, ok := parse_partial_array_ir_type(elem_type)
        if ok {
            return slice_header_bytes + cap * elem_byte_size(elem, checked)
        }
    }
    return ptr_size // default for struct pointers, etc.
}

// Parse `{ i32, i32, ptr, [N x T] }` (a partial-array IR type) into N and T.
// Returns ok=false for any other shape, including bare slice headers.
parse_partial_array_ir_type :: proc(ir: string) -> (cap: int, elem: string, ok: bool) {
    if !strings.has_prefix(ir, PARTIAL_ARRAY_HEADER_PREFIX) { return 0, "", false }
    rest := strings.trim_space(ir[len(PARTIAL_ARRAY_HEADER_PREFIX):])
    // rest now starts with `[N x T] }`; drop the trailing brace before parsing.
    end := strings.last_index_byte(rest, '}')
    if end < 0 { return 0, "", false }
    return parse_array_ir_type(strings.trim_space(rest[:end]))
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
    // Partial-array IR: alignment is max(slice header align, inner elem align).
    if strings.has_prefix(elem_type, PARTIAL_ARRAY_HEADER_PREFIX) {
        _, elem, ok := parse_partial_array_ir_type(elem_type)
        if ok {
            a := slice_header_align
            ea := elem_alignment(elem, checked)
            if ea > a { a = ea }
            return a
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
    emit_raw(g, strings.concatenate({"  ", ctx_ptr, " = load ptr, ptr @__mara_program"}))
    arena_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", arena_ptr, " = getelementptr %class.Program, ptr ", ctx_ptr, ", i32 0, i32 0"}))
    return arena_ptr
}

// Emit a call to the Mara mark() function from the memory package.
emit_arena_mark :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    mark_ir := mara_fn_name(g, g.arena_mark_name)
    if info, ok := lookup_fun_info(g, g.arena_mark_name); ok && info.ret_struct != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(info.ret_struct))
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
// Returns the data pointer. arena_alloc is responsible for aborting on
// OOM — it already prints diagnostics with the name / loc strings we
// pass in. No codegen-side check; if the user supplies a buggy arena
// that returns an invalid slice, downstream code crashes when it
// accesses the null ptr, same as any other broken function.
emit_arena_bump_val :: proc(g: ^Codegen, size_val: string, name: string = "<alloc>", loc: string = "<unknown>") -> string {
    // Deferred check: only fires if some code actually wants the arena. A
    // shared-build DLL with `#expose` fn(s) but no `context.scope_allocator
    // = X` declaration reaches here with no allocator name. Tell the user
    // what to add; suppressed for DLLs that never touch the arena.
    if g.arena_alloc_name == "" {
        if g.shared {
            codegen_fatal(g, {},
                CODE_DLL_EXPOSE_FN_USES_ARENA)
        }
        codegen_fatal(g, {}, CODE_ARENA_ALLOCATION_REQUESTED_SCOPE_ALLOCATOR)
    }
    arena_ptr := get_context_arena_ptr(g)
    // Alloca for the sret slice result { ptr, i64, i64 }
    tmp_slice := fresh_tmp(g)
    emit_slice_alloca(g, tmp_slice)
    // Get a pointer to the name string literal
    name_global, name_len := get_string_literal(g, name)
    name_ptr := fresh_tmp(g)
    emit_string_gep(g, name_ptr, name_len, name_global)
    // Get a pointer to the span/location string literal
    span_global, span_len := get_string_literal(g, loc)
    span_ptr := fresh_tmp(g)
    emit_string_gep(g, span_ptr, span_len, span_global)
    // sret goes last, after the regular params. The size operand width matches
    // the arena's declared `alloc(..., size: <int-type>, ...)` — since every
    // alloc hands back a `[]byte`, the size shares the slice header width.
    alloc_ir := mara_fn_name(g, g.arena_alloc_name)
    w := slice_layout.len_ir
    if g.arena_alloc_has_debug {
        emit_raw(g, strings.concatenate({"  call void ", alloc_ir, "(ptr ", arena_ptr, ", ", w, " ", size_val, ", ptr ", name_ptr, ", ptr ", span_ptr, ", ptr ", tmp_slice, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", alloc_ir, "(ptr ", arena_ptr, ", ", w, " ", size_val, ", ptr ", tmp_slice, ")"}))
    }
    // Extract raw data pointer from the returned slice header
    data_ptr_ptr := fresh_tmp(g)
    emit_slice_gep(g, data_ptr_ptr, tmp_slice, SLICE.ptr)
    data_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", data_ptr, " = load ptr, ptr ", data_ptr_ptr}))

    return data_ptr
}

// Emit a call to the Mara reset() function from the memory package.
emit_arena_reset :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    reset_ir := mara_fn_name(g, g.arena_reset_name)
    if info, ok := lookup_fun_info(g, g.arena_reset_name); ok && info.ret_struct != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(info.ret_struct))
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
// emitted; the linker drops unreachable code. Returns the list of per-
// module .ll files produced (one per home_package in g.module_order),
// plus a success flag.
generate_program :: proc(output_path: string, checked: ^Checked_Program, web: bool = false, shared: bool = false) -> ([]string, bool) {
    g := Codegen{}
    g.checked = checked
    g.web = web
    g.shared = shared
    word_size_is_32 = web
    init_slice_layout()

    // g.out is now a swap target driven by switch_to_module; each per-module
    // buffer is pre-sized to 4MB on first creation. No global pre-size here.

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

    // Patch the synthesized Program global's scope_allocator field with the
    // concrete arena type (checker stamped Type_Any as a placeholder; we now
    // have the resolved allocator type from validate_scope_allocator). The
    // LLVM struct layout reads the field types straight from this scope, so
    // the patched type drives the global's storage size.
    if g.context_enabled && checked.table.scope_allocator_type != nil {
        if prog_st, prog_ok := checked.table.funs["Program"]; prog_ok {
            alloc_type := checked.table.scope_allocator_type
            arena_type: Type
            if inner_t, has_inner := alloc_type.types["Arena"]; has_inner {
                arena_type = inner_t
            } else {
                // Flat form: allocator type IS the arena type
                arena_type = alloc_type
            }
            // Field 0 is "scope_allocator" — replace the Type_Any placeholder.
            if len(prog_st.fields) > 0 && prog_st.fields[0].name == "scope_allocator" {
                prog_st.fields[0].type_ = arena_type
            }
        }
    }

    // @main lives in its own builder so the final-assembly step can place it
    // after all per-module function definitions. Non-main user functions now
    // route into per-module buffers in g.module_outs (set up lazily by
    // switch_to_module on first reference).
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

    // Phase 1: Partition every non-main function (including monomorphized
    // generics) by home_package. Each partition becomes one parallel task.
    fns_by_module: map[string][dynamic]string
    for fn_name in checked.function_order {
        if fn_name == "main" { continue }
        cf, cf_ok := checked.functions[fn_name]
        if !cf_ok { continue }
        home := cf.home_package if cf.home_package != "" else checked.main_package
        if home not_in fns_by_module { fns_by_module[home] = make([dynamic]string) }
        append(&fns_by_module[home], fn_name)
    }
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
        home := cf.home_package if cf.home_package != "" else checked.main_package
        if home not_in fns_by_module { fns_by_module[home] = make([dynamic]string) }
        append(&fns_by_module[home], fn_name)
    }

    // Build tasks in a deterministic order so module_order ends up the
    // same regardless of how the pool schedules workers. Sort by module
    // name (matches the byte-level layout previous single-threaded runs
    // produced, modulo AST-order vs alphabetical — close enough for
    // reproducibility and clang-friendly).
    module_names: [dynamic]string
    defer delete(module_names)
    for k in fns_by_module { append(&module_names, k) }
    slice.sort(module_names[:])

    tasks: [dynamic]^Module_Task
    defer delete(tasks)
    for module_name in module_names {
        task := new(Module_Task)
        task.main_g      = &g
        task.checked     = checked
        task.module_name = module_name
        task.fn_names    = fns_by_module[module_name][:]
        task.web         = web
        task.shared_mode = shared
        append(&tasks, task)
    }

    // Spawn worker pool sized to the host's cores. Each worker pops one
    // module task at a time from the queue; tasks are independent so the
    // slowest single module pace-sets total codegen time.
    if len(tasks) > 0 {
        pool: thread.Pool
        num_workers := os_old.processor_core_count()
        if num_workers < 1 { num_workers = 1 }
        if num_workers > len(tasks) { num_workers = len(tasks) }
        thread.pool_init(&pool, context.allocator, num_workers)
        defer thread.pool_destroy(&pool)
        thread.pool_start(&pool)
        for t in tasks {
            thread.pool_add_task(&pool, context.allocator, module_codegen_worker, rawptr(t))
        }
        thread.pool_finish(&pool)
    }

    // Collect each worker's output into main_g. module_outs[name] gets the
    // worker's IR buffer; the per-task string_decls / intrinsics are kept
    // on the task struct itself and read at .ll-write time.
    for t in tasks {
        g.module_outs[t.module_name] = t.out
        append(&g.module_order, t.module_name)
    }
    g.module_tasks = tasks[:]

    // (Phase 1.6 — compute imports — runs after Phase 2 below so the @main
    // body in main_builder is scanned too.)

    // Phase 2: Emit @main from user's fn main(). Skipped in shared (DLL) mode —
    // the binary has no entry point; each #expose function does its own ctx
    // handover into @__mara_program on entry, so there's nothing for a single
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
    // after main's stack is gone, and any later @__mara_program load would
    // dereference a dangling stack pointer (manifests as arena.base.cap
    // reading 0 and the very first byte-buffer write tripping the bounds
    // check). Native is unaffected: same global lifetime, same fields.
    {
        ctx_alloca := "@__mara_program_storage"
        emit_raw(&g, strings.concatenate({"  store ptr ", ctx_alloca, ", ptr @__mara_program"}))
        g.ctx_alloca = ctx_alloca

        // Register 'context' as a struct var so field access works normally
        g.all_vars["context"] = Struct_Var{alloca = ctx_alloca, struct_name = "Context"}

        // Arena init (if scope allocator is active).
        if g.context_enabled {
            arena_ptr := fresh_tmp(&g)
            emit_raw(&g, strings.concatenate({"  ", arena_ptr, " = getelementptr %class.Program, ptr ", ctx_alloca, ", i32 0, i32 0"}))
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
        emit_raw(&g, strings.concatenate({"  ", args_ptr, " = getelementptr %class.Program, ptr ", ctx_alloca, ", i32 0, i32 ", args_field_idx}))

        // Compute effective len = min(argc, 64). argc is already i32 from
        // the main signature; slice header len is i32 too.
        argc_cmp := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argc_cmp, " = icmp slt i32 %argc, ", ARGS_CAP}))
        argc_min := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argc_min, " = select i1 ", argc_cmp, ", i32 %argc, i32 ", ARGS_CAP}))

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
        // Counter is i32 to match argc and the slice header — no widen/trunc.
        loop_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", loop_i, " = alloca i32"}))
        emit_raw(&g, strings.concatenate({"  store i32 0, ptr ", loop_i}))
        loop_lbl := fmt.tprintf("args_loop_%d", g.label_counter)
        body_lbl := fmt.tprintf("args_body_%d", g.label_counter)
        done_lbl := fmt.tprintf("args_done_%d", g.label_counter)
        g.label_counter += 1
        emit_raw(&g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(&g, strings.concatenate({loop_lbl, ":"}))
        cur_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", cur_i, " = load i32, ptr ", loop_i}))
        cmp := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", cmp, " = icmp slt i32 ", cur_i, ", ", argc_min}))
        emit_raw(&g, strings.concatenate({"  br i1 ", cmp, ", label %", body_lbl, ", label %", done_lbl}))

        emit_raw(&g, strings.concatenate({body_lbl, ":"}))
        argv_i_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argv_i_ptr, " = getelementptr ptr, ptr %argv, i32 ", cur_i}))
        argv_i := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", argv_i, " = load ptr, ptr ", argv_i_ptr}))
        // strlen returns size_t (i64 / i32 platform-dependent). Bootstrap
        // narrowing to i32 for the slice header — argv strings fit
        // trivially. Explicit cast, not an implicit codegen widen.
        str_len := fresh_tmp(&g)
        if g.web {
            emit_raw(&g, strings.concatenate({"  ", str_len, " = call i32 @strlen(ptr ", argv_i, ")"}))
        } else {
            str_len_64 := fresh_tmp(&g)
            emit_raw(&g, strings.concatenate({"  ", str_len_64, " = call i64 @strlen(ptr ", argv_i, ")"}))
            emit_raw(&g, strings.concatenate({"  ", str_len, " = trunc i64 ", str_len_64, " to i32"}))
        }
        // elements[i] is a slice — write len, cap, ptr.
        elem_ptr := fresh_tmp(&g)
        emit_raw(&g, strings.concatenate({"  ", elem_ptr, " = getelementptr [64 x ", SLICE_IR_TYPE, "], ptr ", elements_ptr, ", i32 0, i32 ", cur_i}))
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
        emit_raw(&g, strings.concatenate({"  ", next_i, " = add i32 ", cur_i, ", 1"}))
        emit_raw(&g, strings.concatenate({"  store i32 ", next_i, ", ptr ", loop_i}))
        emit_raw(&g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(&g, strings.concatenate({done_lbl, ":"}))
    }

    // Enable alloca hoisting for main body
    begin_alloca_hoist(&g)

    // Emit the user's main body. main lowers to `i64 @main` (C entry-point
    // convention), so a bare `return` inside main must terminate with
    // `ret i64 0`. Setting current_ret_type wires this into the bare-return
    // codepath in gen_return.
    if main_cf, main_ok := checked.functions["main"]; main_ok {
        prev_ret_type := g.current_ret_type
        g.current_ret_type = "i64"
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
        g.current_ret_type = prev_ret_type
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

    // Build the runtime fail-block helpers FIRST so any templates they
    // register (via get_string_literal) land in g.string_decls before the
    // string section below writes it out. The returned text is appended
    // after the external declarations.
    fail_helpers_ir := runtime_fail_helpers_ir(&g)
    main_builder_str := strings.to_string(main_builder)

    // Ensure the main package has an entry in module_outs (and therefore
    // module_order) before computing imports — it might have no user
    // functions of its own (just `use` directives + `fun main`), in which
    // case the function-emission loops never created a buffer for it.
    if checked.main_package not_in g.module_outs {
        switch_to_module(&g, checked.main_package)
        flush_current_module(&g)
    }

    // Phase 1.6: Compute per-module imports now that both function bodies
    // and @main are emitted. The main TU's import set folds in @main's
    // references (arena init, args setup, dispatch into user `main`).
    compute_module_imports(&g, checked.main_package, main_builder_str)

    // Pre-build foreign declares as a name→declare map. Each per-module .ll
    // emits only the foreign symbols its function bodies actually reference,
    // mirroring the cross-module import filtering below.
    foreign_declares := build_foreign_declares(&g, checked)
    defer delete(foreign_declares)

    // Build a name→decl map for struct/union types so each per-module .ll
    // emits only the types it (transitively) references. The IR-level type
    // name namespace is per-TU so the full set isn't needed everywhere;
    // each TU previously paid ~144 decls of duplication.
    struct_decl_by_name := build_struct_decl_index(g.struct_decls[:])
    defer delete(struct_decl_by_name)

    // Walk every module's emitted IR for `define ... @name(args) {` lines
    // and convert each to its corresponding `declare ... @name(args)` form.
    // The per-module `.ll` files use this table to emit extern declares for
    // any cross-module call (the module's import set).
    fn_declares := build_cross_module_declares(&g)
    defer delete(fn_declares)

    // Per-module output: each home_package gets its own .ll file. Main TU
    // owns the runtime helper definitions, @__mara_program globals, and
    // @main; every other TU just declares those externally.

    // Resolve output directory: <output_path stem>_build/ next to the
    // existing output path. Created if missing.
    build_dir := derive_build_dir(output_path)
    if !ensure_dir(build_dir) {
        fmt.printf("Error: could not create build dir '%s'\n", build_dir)
        return nil, false
    }

    // Build a quick name → task lookup so each per-module .ll write can
    // find its own string_decls / overflow_intrinsics blob.
    task_by_module: map[string]^Module_Task
    defer delete(task_by_module)
    for t in g.module_tasks {
        task_by_module[t.module_name] = t
    }

    g.module_ll_paths = make([dynamic]string)
    for module_name in g.module_order {
        is_main_tu := module_name == checked.main_package
        content := build_module_ll(&g, checked, module_name, is_main_tu, web,
                                    fail_helpers_ir, main_builder_str,
                                    foreign_declares,
                                    fn_declares,
                                    struct_decl_by_name,
                                    task_by_module[module_name])
        path := module_ll_path(build_dir, module_name)
        werr := os.write_entire_file(path, transmute([]u8)content)
        if werr != nil {
            fmt.printf("Error: could not write '%s'\n", path)
            return nil, false
        }
        append(&g.module_ll_paths, path)
    }

    return g.module_ll_paths[:], true
}

// Build the LLVM IR contents for a single module's .ll file. The shared
// prelude (target triple, struct decls, string globals, foreign + libc +
// intrinsic declares) appears in every TU. The runtime helper definitions
// + @__mara_program globals live in the main TU only; other TUs see them
// as extern declares. @main lives only in the main TU.
@(private="file")
build_module_ll :: proc(g: ^Codegen, checked: ^Checked_Program,
                        module_name: string, is_main_tu: bool, web: bool,
                        fail_helpers_ir, main_builder_str: string,
                        foreign_declares: map[string]string,
                        fn_declares: map[string]string,
                        struct_decl_by_name: map[string]string,
                        module_task: ^Module_Task) -> string {
    b: strings.Builder
    strings.builder_init_len_cap(&b, 0, 1024 * 1024)

    // Module header
    strings.write_string(&b, "; Mara LLVM IR output — module ")
    strings.write_string(&b, module_name)
    strings.write_byte(&b, '\n')
    if web {
        strings.write_string(&b, "target triple = \"wasm32-unknown-emscripten\"\n\n")
    } else {
        native_triple :: "x86_64-pc-windows-msvc" when ODIN_OS == .Windows else
                         "x86_64-pc-linux-gnu"   when ODIN_OS == .Linux   else
                         "x86_64-apple-darwin"
        strings.write_string(&b, "target triple = \"")
        strings.write_string(&b, native_triple)
        strings.write_string(&b, "\"\n\n")
    }

    // Struct/union type definitions — TU-local LLVM type namespace means we
    // only need the types this module actually references (plus the transitive
    // closure of their field types). Collect from the module's own IR + the
    // main TU's @main / fail-helper IR.
    {
        used := collect_used_types(g.module_outs[module_name], struct_decl_by_name)
        if is_main_tu {
            collect_used_types_into(main_builder_str, struct_decl_by_name, &used)
            collect_used_types_into(fail_helpers_ir, struct_decl_by_name, &used)
        }
        // The `@__mara_program_storage` global below references %class.Program
        // in every TU (main TU defines it, others extern-declare it), so seed
        // its transitive closure into the used set even if the module's body
        // never names the type directly.
        program_name :: "%class.Program"
        if _, ok := struct_decl_by_name[program_name]; ok && !(program_name in used) {
            used[program_name] = true
            seed_ir := struct_decl_by_name[program_name]
            collect_used_types_into(seed_ir, struct_decl_by_name, &used)
        }
        // Emit in the same order as g.struct_decls so the output stays
        // deterministic and matches the original layout for diffability.
        wrote_any := false
        for decl in g.struct_decls {
            name := struct_decl_name(decl)
            if name == "" || !(name in used) { continue }
            strings.write_string(&b, decl)
            strings.write_byte(&b, '\n')
            wrote_any = true
        }
        if wrote_any { strings.write_byte(&b, '\n') }
        delete(used)
    }

    // String literal globals — private linkage means no link collision
    // between TUs. Per-module workers contribute their own @.<module>_str.N
    // entries; the main TU also folds in main_g.string_decls (used by
    // @main emission and the fail-helper format strings).
    wrote_any_string := false
    if module_task != nil {
        for decl in module_task.string_decls {
            strings.write_string(&b, decl)
            strings.write_byte(&b, '\n')
            wrote_any_string = true
        }
    }
    if is_main_tu {
        for decl in g.string_decls {
            strings.write_string(&b, decl)
            strings.write_byte(&b, '\n')
            wrote_any_string = true
        }
    }
    if wrote_any_string { strings.write_byte(&b, '\n') }

    // Context globals: main TU defines, others declare external.
    strings.write_string(&b, "; Context system\n")
    if is_main_tu {
        strings.write_string(&b, "@__mara_program = global ptr null\n")
        strings.write_string(&b, "@__mara_program_storage = global %class.Program zeroinitializer\n\n")
    } else {
        strings.write_string(&b, "@__mara_program = external global ptr\n")
        strings.write_string(&b, "@__mara_program_storage = external global %class.Program\n\n")
    }

    // libc + intrinsic + foreign declares — every TU declares regardless.
    // Intrinsics are per-module (only what this TU actually uses);
    // foreign symbols are program-wide so the same block is included
    // in every TU.
    strings.write_string(&b, "; External declarations\n")
    strings.write_string(&b, "declare i32 @printf(ptr, ...)\n")
    strings.write_string(&b, "declare void @exit(i32)\n")
    if g.web {
        strings.write_string(&b, "declare i32 @strlen(ptr)\n")
    } else {
        strings.write_string(&b, "declare i64 @strlen(ptr)\n")
    }
    {
        // Union of per-module intrinsics plus main_g's (used by @main and
        // fail helpers in the main TU).
        used: map[string]bool
        if module_task != nil {
            for k in module_task.overflow_intrinsics { used[k] = true }
        }
        if is_main_tu {
            for k in g.overflow_intrinsics { used[k] = true }
        }
        intr_names: [dynamic]string
        defer delete(intr_names)
        for k in used { append(&intr_names, k) }
        slice.sort(intr_names[:])
        for name in intr_names {
            dot_idx := 0
            for i := len(name) - 1; i >= 0; i -= 1 {
                if name[i] == '.' { dot_idx = i; break }
            }
            it := name[dot_idx+1:]
            strings.write_string(&b, strings.concatenate({"declare { ", it, ", i1 } @", name, "(", it, ", ", it, ")\n"}))
        }
        // `llvm.bswap.iN` declares — same module-union pattern as overflow.
        bswap_used: map[int]bool
        if module_task != nil {
            for w in module_task.bswap_intrinsics { bswap_used[w] = true }
        }
        if is_main_tu {
            for w in g.bswap_intrinsics { bswap_used[w] = true }
        }
        bswap_widths: [dynamic]int
        defer delete(bswap_widths)
        for w in bswap_used { append(&bswap_widths, w) }
        slice.sort(bswap_widths[:])
        for w in bswap_widths {
            strings.write_string(&b, fmt.tprintf("declare i%d @llvm.bswap.i%d(i%d)\n", w, w, w))
        }
    }
    // Per-module foreign declares: emit only the C symbols this module
    // actually references. Iterate via module_imports (the imports computed
    // by compute_module_imports). Sorted for deterministic output.
    if imports, has_imports := g.module_imports[module_name]; has_imports {
        sorted_foreigns: [dynamic]string
        defer delete(sorted_foreigns)
        for name in imports {
            if _, is_foreign := foreign_declares[name]; is_foreign {
                append(&sorted_foreigns, name)
            }
        }
        slice.sort(sorted_foreigns[:])
        for name in sorted_foreigns {
            strings.write_string(&b, foreign_declares[name])
            strings.write_byte(&b, '\n')
        }
    }
    strings.write_byte(&b, '\n')

    // Runtime helpers: main TU defines, others extern-declare.
    if is_main_tu {
        strings.write_string(&b, fail_helpers_ir)
    } else {
        strings.write_string(&b, "; Runtime fail-block helpers (extern)\n")
        strings.write_string(&b, "declare void @__mara_bounds_fail(ptr, i32, i32, ptr)\n")
        strings.write_string(&b, "declare void @__mara_overflow_fail(ptr)\n")
        strings.write_string(&b, "declare void @__mara_null_fail(ptr, ptr)\n")
        strings.write_string(&b, "declare void @__mara_divz_fail(ptr)\n")
        strings.write_string(&b, "declare void @__mara_slice_len_fail(ptr, i32, i32, ptr)\n")
        strings.write_string(&b, "declare void @__mara_print_err(i32)\n")
    }
    strings.write_byte(&b, '\n')

    // Cross-module extern declares: every symbol this module imports from
    // another TU needs a matching `declare` here. The fn_declares table
    // is the global function-name → declare-line index, built from every
    // module's emitted `define ...` lines. Skip well-known categories
    // already declared above (runtime helpers + the libc trio).
    if imports, has_imports := g.module_imports[module_name]; has_imports && len(imports) > 0 {
        sorted: [dynamic]string
        defer delete(sorted)
        for name in imports { append(&sorted, name) }
        slice.sort(sorted[:])
        wrote_header := false
        for name in sorted {
            // Runtime helpers handled above; libc declared unconditionally.
            if strings.has_prefix(name, "__mara_") { continue }
            if name == "printf" || name == "exit" || name == "strlen" { continue }
            decl, ok := fn_declares[name]
            if !ok { continue }
            if !wrote_header {
                strings.write_string(&b, "; Cross-module imports\n")
                wrote_header = true
            }
            strings.write_string(&b, decl)
            strings.write_byte(&b, '\n')
        }
        if wrote_header { strings.write_byte(&b, '\n') }
    }

    // This module's own function definitions.
    if buf, ok := g.module_outs[module_name]; ok {
        strings.write_string(&b, strings.to_string(buf))
    }

    // @main: only the main TU includes it.
    if is_main_tu {
        strings.write_byte(&b, '\n')
        strings.write_string(&b, main_builder_str)
        strings.write_byte(&b, '\n')
    }

    return strings.to_string(b)
}

// Scan every module's emitted IR for `define ... @name(...) {` headers and
// produce a flat-name → `declare ... @name(...)` map. Each per-module .ll
// uses this to emit extern declares for the cross-module functions it
// imports.
//
// Why text-based: the alternative is rebuilding the declare from the
// Type_Scope + signature info via the same code that builds the define
// header (codegen_fn.odin's `gen_scope_def`). That path is involved
// enough — sret routing, NRVO, escape args, calling-conv lowering — that
// reusing it for declares means refactoring it to take a write-target arg.
// Reading the already-emitted text is simpler and the dependency is just
// "the define line is on the line right after a label-less open." If the
// emission format changes, this breaks loudly at the next clang invocation.
@(private="file")
build_cross_module_declares :: proc(g: ^Codegen) -> map[string]string {
    declares := make(map[string]string)
    for module_name in g.module_order {
        buf := g.module_outs[module_name]
        ir := strings.to_string(buf)
        i := 0
        for i < len(ir) {
            line_end := strings.index_byte(ir[i:], '\n')
            line: string
            if line_end < 0 { line = ir[i:]; i = len(ir) } else { line = ir[i:i+line_end]; i += line_end + 1 }
            if !strings.has_prefix(line, "define ") { continue }
            // Parse "define <linkage>? <retty> @<name>(<params>) {"
            at := strings.index_byte(line, '@')
            if at < 0 { continue }
            // The signature ends just before the trailing " {".
            sig_end := strings.last_index(line, "{")
            if sig_end < 0 { continue }
            sig := strings.trim_right(line[at:sig_end], " ")
            // Extract just the bare name for the map key.
            paren := strings.index_byte(sig, '(')
            if paren < 0 { continue }
            name := sig[1:paren]  // skip the leading '@'
            // Reconstruct the declare with the same return type prefix.
            ret_prefix := strings.trim(line[len("define "):at], " ")
            declares[name] = strings.concatenate({"declare ", ret_prefix, " ", sig})
        }
    }
    return declares
}

// Pre-build the LLVM intrinsic `declare` block: one declare per intrinsic
// used anywhere in the program, sorted for reproducible IR.
@(private="file")
build_intrinsic_declares :: proc(g: ^Codegen) -> string {
    b: strings.Builder
    intr_names: [dynamic]string
    defer delete(intr_names)
    for name in g.overflow_intrinsics { append(&intr_names, name) }
    slice.sort(intr_names[:])
    for name in intr_names {
        dot_idx := 0
        for i := len(name) - 1; i >= 0; i -= 1 {
            if name[i] == '.' { dot_idx = i; break }
        }
        it := name[dot_idx+1:]
        strings.write_string(&b, strings.concatenate({"declare { ", it, ", i1 } @", name, "(", it, ", ", it, ")\n"}))
    }
    return strings.to_string(b)
}

// Extract the type name (`%class.X` or `%union.X`) from a type-decl line
// like `%class.X = type { ... }`. Returns "" if the line isn't shaped that
// way (defensive — every entry in struct_decls follows the convention).
@(private="file")
struct_decl_name :: proc(decl: string) -> string {
    if len(decl) == 0 || decl[0] != '%' { return "" }
    eq := strings.index_byte(decl, '=')
    if eq <= 1 { return "" }
    end := eq
    for end > 1 && decl[end-1] == ' ' { end -= 1 }
    return decl[:end]
}

// Build the name → decl-line index used by per-module struct-decl filtering.
@(private="file")
build_struct_decl_index :: proc(decls: []string) -> map[string]string {
    result := make(map[string]string)
    for d in decls {
        if name := struct_decl_name(d); name != "" {
            result[name] = d
        }
    }
    return result
}

// Collect every `%class.X` / `%union.X` name referenced in `ir`, then add
// the transitive closure (types whose fields mention other types). Anything
// not in `index` (LLVM's own anonymous struct shapes etc.) is ignored.
@(private="file")
collect_used_types :: proc(buf: strings.Builder, index: map[string]string) -> map[string]bool {
    used: map[string]bool
    collect_used_types_into(strings.to_string(buf), index, &used)
    return used
}

@(private="file")
collect_used_types_into :: proc(ir: string, index: map[string]string, used: ^map[string]bool) {
    // Scan `ir` for `%class.<ident>` and `%union.<ident>` occurrences. The
    // hot loop uses strings.index_byte to jump straight from one `%` to the
    // next, skipping the (much more common) non-`%` bytes in one step
    // instead of one-byte-at-a-time.
    add :: proc(name: string, index: map[string]string, used: ^map[string]bool) -> bool {
        if name in used { return false }
        if _, ok := index[name]; !ok { return false }
        used[name] = true
        return true
    }
    scan :: proc(s: string, index: map[string]string, used: ^map[string]bool, worklist: ^[dynamic]string) {
        pos := 0
        for pos < len(s) {
            jump := strings.index_byte(s[pos:], '%')
            if jump < 0 { break }
            i := pos + jump
            j := i + 1
            for j < len(s) && is_ir_ident_byte(s[j]) { j += 1 }
            if j > i + 1 {
                name := s[i:j]
                // Only %class.* / %union.* are user struct/union types.
                if strings.has_prefix(name, "%class.") || strings.has_prefix(name, "%union.") {
                    if add(name, index, used) { append(worklist, name) }
                }
            }
            pos = j
            if pos == i { pos += 1 }  // defensive — never re-scan the same byte
        }
    }
    worklist: [dynamic]string
    defer delete(worklist)
    scan(ir, index, used, &worklist)
    // Transitive closure: each used type's decl may reference more types
    // in its field list (`{ ..., %class.Y, ... }`). Drain the worklist.
    for len(worklist) > 0 {
        name := pop(&worklist)
        scan(index[name], index, used, &worklist)
    }
}

// Pre-build foreign `declare` entries keyed by C link_name (the actual
// IR symbol the import set references). Per-module emission filters this
// to just the foreign symbols the module actually calls — dropping the
// other ~140 dead declares each TU otherwise duplicated.
@(private="file")
build_foreign_declares :: proc(g: ^Codegen, checked: ^Checked_Program) -> map[string]string {
    result := make(map[string]string)
    for k in checked.functions {
        cs := checked.functions[k]
        fo, is_foreign := cs.origin.(Origin_Foreign)
        if !is_foreign { continue }
        result[fo.link_name] = build_c_declare(&cs, fo.link_name, checked.target_os)
    }
    return result
}

// `<output_path>` typically ends in `.ll`; strip that and append `_build`
// to produce the per-module-output directory next to where the caller
// originally wanted the single .ll.
@(private="file")
derive_build_dir :: proc(output_path: string) -> string {
    base := output_path
    if strings.has_suffix(base, ".ll") { base = base[:len(base)-3] }
    return strings.concatenate({base, "_build"})
}

// Produce the on-disk path for a single module's .ll file inside `build_dir`.
// Module names may contain dots (e.g. "mara.core"); replace with `_` so the
// filename is portable across filesystems.
@(private="file")
module_ll_path :: proc(build_dir, module_name: string) -> string {
    safe, _ := strings.replace_all(module_name, ".", "_")
    return strings.concatenate({build_dir, "/", safe, ".ll"})
}

@(private="file")
ensure_dir :: proc(path: string) -> bool {
    if os.exists(path) { return true }
    err := os.make_directory(path)
    return err == os.ERROR_NONE
}

// NOTE: The following procs have been moved to separate files:
// - gen_scope_def         -> codegen_fn.odin
// - gen_stmt           -> codegen_stmt.odin
// - gen_array_*        -> codegen_array.odin
// - gen_struct_*       -> codegen_struct.odin
// - gen_match/value    -> codegen_match.odin
// - gen_if, gen_for    -> codegen_control.odin
// - gen_expr, gen_call -> codegen_expr.odin
