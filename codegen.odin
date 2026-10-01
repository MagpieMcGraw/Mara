package mara

import "core:fmt"
import "core:hash"
import "core:slice"
import "core:strconv"
import "core:strings"
import "core:os"

// ---------------------------------------------------------------------------
// The LLVM IR toolkit the emitter writes with: its state (Codegen), the
// instruction emitters, types' IR names and declarations, string globals,
// the runtime checks and the arena's calls. llvm.odin lowers each function
// from the program graph with it; codegen_module.odin assembles the .ll files.
// ---------------------------------------------------------------------------

// A slice's header, `{ len, cap, ptr }`, its length and capacity i64s on
// every target; a partial array is the header with its elements after.
SLICE_IR_TYPE :: "{ i64, i64, ptr }"
SLICE_LEN_IR  :: "i64"   // a header's len's and cap's IR type

// Slice header field positions. A partial array's elements follow the
// header at PARTIAL_ELEMENTS_FIELD.
Slice_Fields :: struct { len, cap, ptr: int }
SLICE :: Slice_Fields{len = 0, cap = 1, ptr = 2}
PARTIAL_ELEMENTS_FIELD :: 3

// Build the LLVM IR type for a `[..N]T` partial array.
partial_array_ir_type :: proc(elem_ir: string, cap: int) -> string {
    return strings.concatenate({
        "{ ", SLICE_LEN_IR, ", ", SLICE_LEN_IR, ", ptr, [",
        fmt.tprintf("%d", cap), " x ", elem_ir, "] }",
    })
}

Codegen :: struct {
    out:         strings.Builder,  // current per-module IR buffer (swapped in from module_outs)
    alloca_buf:  strings.Builder,  // hoisted allocas (entry block)
    body_buf:    strings.Builder,  // temporary buffer for function body during alloca hoisting
    // Aggregate constants live in read-only tables (codegen_const.odin): the
    // tables this Codegen's functions referenced (symbol -> table).
    const_tables: map[string]Const_Table,

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
    tmp_counter: int,              // bumped per fresh_tmp (and a few inline temp names)
    tmp_pool:    []string,         // pre-formatted "%.tN" names; indexed by tmp_counter
    label_counter: int,            // label numbering
    // Type info from the type checker
    checked:     ^Checked_Program,       // resolved type info from type checker
    // String literal table: value -> global name
    string_literals: map[string]string,
    string_names:    map[string]bool,   // names handed out, to catch a hash collision
    // Per-Codegen prefix for `@.str.<hash>` names. Empty for the main thread;
    // set to a module-specific tag by parallel codegen workers so each TU's
    // strings live in its own namespace.
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

    // Overflow-checking intrinsics used (for declaration at end of module)
    overflow_intrinsics: map[string]bool,
    // `llvm.bswap.iN` widths used by `#big_endian` byte-buffer reads.
    // Declared per-module the same way overflow_intrinsics is.
    bswap_intrinsics: map[int]bool,
    // Web build (wasm32-unknown-emscripten): adjusts size_t-shaped libc decls
    // (strlen returns i32 on wasm32, not i64), among other target tweaks.
    web: bool,
    shared: bool,  // -shared build mode — emit a DLL/SO instead of an exe
    release: bool,   // -release build mode — -O3; asserts stay ON
    no_assert: bool, // -no assert — compile asserts out entirely
    // Every function's code comes from the program graph (llvm.odin).

    // Inside an assert/crash fail block (native builds): print-shaped
    // emissions route through __mara_tee_printf, which mirrors the message
    // into crash.txt (runtime/mara_crash.c). Off everywhere else.
    tee: bool,
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
// `min_size - 1` has a pre-formatted `%.t<N>` string. Each name is laid out
// in a single contiguous byte slab so the pool is just a `[]string` of
// views into that slab.
//
// The `.` matters: a Mara identifier can't contain one, but user locals are
// emitted verbatim as `%<name>`. So a temp (`%.t7`) can never collide with a
// user variable named `t7` — which previously produced two `%t7` defs and an
// LLVM "multiple definition" error. (Functions already live in their own
// `@mara_*` namespace; this gives temps the same guarantee against locals.)
@(private="file")
grow_tmp_pool :: proc(g: ^Codegen, min_size: int) {
    new_cap := max(min_size, len(g.tmp_pool) * 2, 16 * 1024)
    new_pool := make([]string, new_cap)
    // Each name fits in 13 bytes ("%.t" + up to 10 digits). Slab in one
    // contiguous block so the pool is friendly to the prefetcher.
    NAME_W :: 13
    slab := make([]byte, new_cap * NAME_W)
    for i in 0..<new_cap {
        off := i * NAME_W
        slab[off]   = '%'
        slab[off+1] = '.'
        slab[off+2] = 't'
        digits := strconv.write_int(slab[off+3:off+NAME_W], i64(i), 10)
        new_pool[i] = string(slab[off : off + 3 + len(digits)])
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
    if span_file(span) != "" {
        loc = span_location(span)
    }
    emit_diagnostic(.Codegen_Error, loc, format, ..args)
    flush_diagnostics()
    os.exit(1)
}


// Generate the IR name for a user-defined function.
// Names are already flat (e.g., "sdl_Init") — flattened during type-checking
// by make_flat_name at registration.
mara_fn_name :: proc(g: ^Codegen, name: string) -> string {
    if name == "main" { return "@main" }
    // `#expose fun foo` → unmangled `@foo` so a DLL host can call
    // GetProcAddress("foo") directly without knowing Mara's flat-naming rule.
    // Mara-internal call sites resolve to the same symbol, so callers in the
    // same package stay wired up.
    if cs, ok := g.checked.functions[name]; ok && cs.is_exposed {
        return fmt.tprintf("@%s", cs.name)
    }
    // IR symbols are prefixed with "mara_" to namespace them against system
    // libraries. flat names from stdlib modules (`mara.math`) already include
    // it via make_flat_name's dot→underscore conversion; user-module flats
    // like `camera_init` get prepended here.
    if strings.has_prefix(name, "mara_") { return fmt.tprintf("@%s", name) }
    return fmt.tprintf("@mara_%s", name)
}

// The struct a function returns through its sret slot, when its one
// result is one: "" otherwise.
fn_ret_struct :: proc(g: ^Codegen, fn_name: string) -> string {
    cf, found := g.checked.functions[fn_name]
    if !found || len(cf.cg_returns) != 1 { return "" }
    if sd := as_struct_body(cf.cg_returns[0]); sd != nil { return sd.name }
    return ""
}


// Write a line of a function's code (its body, while its allocas are
// hoisted: emit_alloca).
emit_raw :: proc(g: ^Codegen, line: string) {
    b := &g.body_buf if g.hoist_allocas else &g.out
    strings.write_string(b, line)
    strings.write_byte(b, '\n')
}

emit :: proc(g: ^Codegen, s: string, args: ..any) {
    emit_raw(g, s if len(args) == 0 else fmt.tprintf(s, ..args))
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
// `idx_ir` is the LLVM IR type of `idx`; callers pass SLICE_LEN_IR
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
        if alloca_exists(g, dst, ir_type) { return }
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

// Whether `name` is already allocated in this function. Reusing a slot is
// only sound at the same type; a different type means two values would share
// storage sized for one, so it is a compiler bug. Named locals avoid it by
// going through emit_local_alloca.
@(private="file")
alloca_exists :: proc(g: ^Codegen, name, ir_type: string) -> bool {
    have, ok := g.emitted_allocas[name]
    if !ok { return false }
    if have != ir_type {
        codegen_fatal(g, {}, "internal: alloca %s reused as %s (first allocated as %s)", name, ir_type, have)
    }
    return true
}

// Emit an `alloca T, <w> %count` form where the count is a runtime SSA. This
// must stay at the point of use rather than the entry block (the standard
// emit_alloca hoists for static allocas), because an entry-block alloca
// referencing a later-computed SSA would fail LLVM's domination check.
// Writes straight to the body buffer to bypass the hoist.
emit_alloca_runtime :: proc(g: ^Codegen, dst, elem_ir, count_ir, count_ssa: string, align: int) {
    line: string
    if align > 0 {
        line = fmt.tprintf("  %s = alloca %s, %s %s, align %d", dst, elem_ir, count_ir, count_ssa, align)
    } else {
        line = fmt.tprintf("  %s = alloca %s, %s %s", dst, elem_ir, count_ir, count_ssa)
    }
    if g.hoist_allocas {
        strings.write_string(&g.body_buf, line)
        strings.write_byte(&g.body_buf, '\n')
    } else {
        strings.write_string(&g.out, line)
        strings.write_byte(&g.out, '\n')
    }
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
// The printf symbol for the current emission context: @printf normally,
// @__mara_tee_printf inside an assert/crash fail block (g.tee) so the
// message also lands in crash.txt.
printf_sym :: proc(g: ^Codegen) -> string {
    return g.tee ? "@__mara_tee_printf" : "@printf"
}

emit_printf_void :: proc(g: ^Codegen, fmt_ptr: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) ")
    strings.write_string(b, printf_sym(g))
    strings.write_string(b, "(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, i64 <val>)\n`
emit_printf_i64 :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) ")
    strings.write_string(b, printf_sym(g))
    strings.write_string(b, "(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", i64 ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, ptr <val>)\n`
emit_printf_ptr :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) ")
    strings.write_string(b, printf_sym(g))
    strings.write_string(b, "(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", ptr ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// `  call i32 (ptr, ...) @printf(ptr <fmt>, double <val>)\n`
emit_printf_double :: proc(g: ^Codegen, fmt_ptr, val: string) {
    b := emit_target(g)
    strings.write_string(b, "  call i32 (ptr, ...) ")
    strings.write_string(b, printf_sym(g))
    strings.write_string(b, "(ptr ")
    strings.write_string(b, fmt_ptr)
    strings.write_string(b, ", double ")
    strings.write_string(b, val)
    strings.write_string(b, ")\n")
}

// Begin alloca hoisting: emit() will redirect allocas to alloca_buf, body code to body_buf.
begin_alloca_hoist :: proc(g: ^Codegen) {
    strings.builder_reset(&g.alloca_buf)
    strings.builder_reset(&g.body_buf)
    g.hoist_allocas = true
}

// ---------------------------------------------------------------------------
// IR names for types (a type's name is flat already: the checker's)
// ---------------------------------------------------------------------------

// Get the LLVM type name for a struct, e.g. "%class.Point"
struct_llvm_name :: proc(key: string) -> string {
    return fmt.tprintf("%%class.%s", key)
}

// IR type name of the synthetic Program context struct. The type checker names
// the synthetic struct (it may be a bare "Program" or a mangled "mara_core_Program"
// depending on how it interns alongside the user's generic Program template), and
// register_struct_decl emits `%class.<that name>`. Codegen's global + its GEPs must
// follow the SAME name rather than hardcode "%class.Program", or the storage global
// references a type that was emitted under a different name. Falls back to the bare
// name when there's no Program (a context-free build emits no global anyway).
program_ir_name :: proc(checked: ^Checked_Program) -> string {
    if checked != nil && checked.table != nil {
        if prog, ok := checked.table.funs["Program"]; ok && prog != nil {
            return struct_llvm_name(prog.name)
        }
    }
    return "%class.Program"
}

// Get the LLVM field index of a named field. Returns -1 if not found.
struct_field_index :: proc(st: ^Scope_Body, field_name: string) -> int {
    for _, i in st.fields {
        if st.fields[i].name == field_name { return i }
    }
    return -1
}


// Get the LLVM IR type string for a struct field.
field_ir_type :: proc(f: ^Struct_Type_Field) -> string {
    return llvm_type_from_checker(f.type_)
}

// Get the LLVM type name for a union, e.g. "%union.Shape"
union_llvm_name :: proc(ukey: string) -> string {
    return fmt.tprintf("%%union.%s", ukey)
}

// The union a `%union.X` IR type names, for the size/alignment tables. A
// `%union.` type the checked program doesn't know is a compiler bug, not a
// pointer-sized value.
ir_union :: proc(ir_type: string, checked: ^Checked_Program) -> (^Type_Union, bool) {
    if !strings.has_prefix(ir_type, "%union.") { return nil, false }
    if checked == nil {
        fmt.panicf("sizing %s needs the checked program", ir_type)
    }
    ut, ok := checked.table.unions[ir_type[len("%union."):]]
    if !ok { fmt.panicf("sizing %s: no such union", ir_type) }
    return ut, true
}

// Get the IR type for a union's tag field
union_tag_ir_type :: proc(ut: ^Type_Union) -> string {
    if ut.tag_type != "" {
        return tag_type_to_ir(ut.tag_type)
    }
    return "i64"
}

// Niche-laid-out unions (see union_niche_variant — the checker decides) are
// stored as their Some variant's pointer alone: null for None, the live pointer
// for Some. The layout differs; everything else (matching, `.tag`) reads the
// tag through load_union_tag like any other union.
is_niche_layout :: proc(g: ^Codegen, ut: ^Type_Union) -> bool {
    return ut.niche_some != ""
}

// For a niche-laid-out union, the variant carrying the pointer (Some) and the
// fieldless one (None).
niche_variants :: proc(g: ^Codegen, ut: ^Type_Union) -> (some_name: string, none_name: string) {
    some_name = ut.niche_some
    for vname in ut.variants {
        if vname != some_name { none_name = vname }
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
    t := resolve_infer(t)
    switch v in t {
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
    case Type_Utf8:         return "i8"
    case Type_Byte:         return "i8"
    case Type_CString:      return "ptr"
    case ^Type_Ptr:         return "ptr"
    case ^Type_Scope:
        if v.kind == .Struct {
            return fmt.tprintf("%%class.%s", v.name)
        }
        return "ptr" // callable fun (function pointer)
    case ^Type_Fixed_Array:
        elem_t := llvm_type_from_checker(v.elem)
        return fmt.tprintf("[%d x %s]", v.size, elem_t)
    case ^Type_Slice:       return SLICE_IR_TYPE
    case ^Type_Partial_Array:
        elem_t := llvm_type_from_checker(v.elem)
        return partial_array_ir_type(elem_t, v.size)
    case ^Type_Enum:
        if v.tag_type != "" { return tag_type_to_ir(v.tag_type) }
        return "i64"
    case ^Type_Union:       return fmt.tprintf("%%union.%s", v.name)
    case ^Type_Distinct:    return llvm_type_from_checker(v.base_type)
    // The following three never legitimately reach codegen as a value type:
    // codegen only runs when the checker reported zero errors (see main.odin),
    // so any of these arriving here means the checker minted a bad type WITHOUT
    // a diagnostic — a silent miscompile. Abort loudly instead of defaulting to
    // i64 (which silently produced wrong-sized storage). Per "errors over
    // fallbacks": emit and abort, don't continue.
    case Type_Const_Int:
        panic("llvm_type_from_checker: Type_Const_Int reached codegen — a const generic parameter should have been substituted to a concrete value before codegen")

    case Type_Any:
        panic("llvm_type_from_checker: Type_Any reached codegen as a value type — the checker minted an untyped value without a diagnostic. Type_Any is only valid as an opaque-pointer element (^Type_Ptr.elem)")
    case Type_Void:         return "{}"  // zero-sized struct — LLVM coalesces
    case Type_Error:
        panic("llvm_type_from_checker: Type_Error reached codegen — codegen runs only on a clean check")
    case Type_Err:          return "i32" // open error type — u32 (set_id<<16 | tag)
    case nil:
        // An unresolved (nil) type reaching type lowering is the same invariant
        // violation as Type_Any above — abort loudly instead of silently sizing
        // it i64. Callers that legitimately hold a typeless expression (e.g.
        // gen_expr_coerced, where a constant operand may carry no .type_) must
        // guard nil themselves before asking for its IR type.
        panic("llvm_type_from_checker: nil (unresolved) type reached codegen — the checker left a type unresolved without a diagnostic")
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
    // Named by content, not by order: a string's name doesn't depend on the
    // strings emitted before it, so one function's IR stays the same when
    // another changes. The per-worker prefix keeps the parallel codegens'
    // namespaces apart (empty on the main thread: `@.str.<hash>`).
    name := fmt.tprintf("@.%sstr.%016x", g.string_name_prefix, hash.fnv64a(transmute([]byte)s))
    if name in g.string_names {
        codegen_fatal(g, {}, "internal: two string literals hash to %s", name)
    }
    g.string_names[name] = true
    // The table owns its key: callers pass transient views (print's format
    // pieces live in a reused buffer), and a borrowed key changes under the
    // map — `" "` then matched a stale `"="` entry.
    g.string_literals[strings.clone(s)] = name

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
// Both `idx` and `len` are at slice header width (SLICE_LEN_IR).
// `name` is the variable name for the error message.
// Module-level helpers for the runtime fail blocks. Emitted once per module;
// per-site fail blocks shrink to `call helper(...) + unreachable`. `loc` and
// `name` are passed as ptr args referencing get_string_literal globals —
// those already dedupe, so identical loc/name across many sites share
// storage. Functions are `internal` linkage so the linker dead-strips any
// unused kind. Helper names are constants so call sites stay readable.
__MARA_BOUNDS_FAIL    :: "@__mara_bounds_fail"
__MARA_OVERFLOW_FAIL  :: "@__mara_overflow_fail"
__MARA_DIVZ_FAIL      :: "@__mara_divz_fail"
__MARA_SLICE_LEN_FAIL :: "@__mara_slice_len_fail"
__MARA_MATCH_FAIL     :: "@__mara_match_fail"
// (assert has no helper: its failure message is a per-site printf format
// assembled at codegen time — see Expr_Assert in codegen_expr.odin.)

runtime_fail_helpers_ir :: proc(g: ^Codegen) -> string {
    // Register format strings as deduped globals via the normal literals path.
    fmt_bounds,    _ := get_string_literal(g, "%s runtime error: index %d out of bounds [0, %d) for '%s'\n")
    fmt_overflow,  _ := get_string_literal(g, "%s runtime error: integer overflow\n")
    fmt_divz,      _ := get_string_literal(g, "%s runtime error: division by zero\n")
    fmt_slice_len, _ := get_string_literal(g, "%s runtime error: slice len %d not in [0, %d] (cap) for '%s'\n")
    fmt_match,     _ := get_string_literal(g, "%s runtime error: match on an invalid tag %lld\n")

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

    // match: (loc, tag). A match covers every variant, so another tag is
    // corrupt memory (a union read from bytes, say).
    strings.write_string(&b, "define void ")
    strings.write_string(&b, __MARA_MATCH_FAIL)
    strings.write_string(&b, "(ptr %loc, i64 %tag) {\n")
    strings.write_string(&b, strings.concatenate({
        "  call i32 (ptr, ...) @printf(ptr ", fmt_match, ", ptr %loc, i64 %tag)\n",
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
    // entirely. Covers `arr[3]` against a fixed-size array and other
    // constant-fold paths.
    if can_elide_bounds_check(idx, len_val) {
        return
    }

    ok_label   := fresh_label(g, "bounds.ok")
    fail_label := fresh_label(g, "bounds.fail")

    // idx and len_val are both at the slice header's width.
    w := SLICE_LEN_IR
    neg_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, 0", neg_cmp, w, idx)
    upper_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sge %s %s, %s", upper_cmp, w, idx, len_val)
    combined := fresh_tmp(g)
    emit(g, "  %s = or i1 %s, %s", combined, neg_cmp, upper_cmp)
    emit_cond_br(g, combined, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := span_location(span)
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
    loc := span_location(span)
    loc_global, _ := get_string_literal(g, loc)
    emit(g, "  call void %s(ptr %s)", __MARA_DIVZ_FAIL, loc_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
}

// The check that a range counts up: crash, located, when `up` is false.
emit_range_check :: proc(g: ^Codegen, up: string, span: Span) {
    ok_label  := fresh_label(g, "range.ok")
    bad_label := fresh_label(g, "range.bad")
    emit_cond_br(g, up, ok_label, bad_label)

    emit_label(g, bad_label)
    emit_crash_journal_begin(g)
    loc := span_location(span)
    esc_loc, _ := strings.replace_all(loc, "%", "%%")
    msg, _ := get_string_literal(g, strings.concatenate(
        {"Descending range at ", esc_loc, " -- `..` only counts up (low > high); use a C-style for to count down.\n"}))
    emit(g, "  call i32 (ptr, ...) %s(ptr %s)", printf_sym(g), msg)
    emit_crash_journal_end(g)
    emit(g, "  call void @exit(i32 1)")
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
    loc := span_location(span)
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

// Load the context's arena pointer (field 0 of Context struct).
get_context_arena_ptr :: proc(g: ^Codegen) -> string {
    ctx_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", ctx_ptr, " = load ptr, ptr @__mara_program"}))
    arena_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", arena_ptr, " = getelementptr ", program_ir_name(g.checked), ", ptr ", ctx_ptr, ", i32 0, i32 0"}))
    return arena_ptr
}

// Emit a call to the Mara mark() function from the memory package.
emit_arena_mark :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    mark_ir := mara_fn_name(g, g.arena_mark_name)
    if ret := fn_ret_struct(g, g.arena_mark_name); ret != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(ret))
        emit_raw(g, strings.concatenate({"  call void ", mark_ir, "(ptr ", arena_ptr, ", ptr ", dummy, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", mark_ir, "(ptr ", arena_ptr, ")"}))
    }
}

// Emit a call to arena_alloc() for a compile-time known size. Returns the data pointer.
emit_arena_bump :: proc(g: ^Codegen, size: int, name: string = "<alloc>", loc: string = "<unknown>") -> string {
    return emit_arena_bump_val(g, fmt.tprintf("%d", size), name, loc)
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
        codegen_fatal(g, {}, "%s (at %s)",
            CODE_ARENA_ALLOCATION_REQUESTED_SCOPE_ALLOCATOR, loc)
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
    w := SLICE_LEN_IR
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
    if ret := fn_ret_struct(g, g.arena_reset_name); ret != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(ret))
        emit_raw(g, strings.concatenate({"  call void ", reset_ir, "(ptr ", arena_ptr, ", ptr ", dummy, ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", reset_ir, "(ptr ", arena_ptr, ")"}))
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

// Generate an LLVM type declaration for a struct from checked type data.
register_struct_decl_sd :: proc(g: ^Codegen, sd: ^Scope_Body) {
    if sd_is_module(sd) { return }  // module-struct — namespace only, no data layout
    key := sd.name
    if key in g.registered_structs { return }
    g.registered_structs[key] = true
    llvm_name := struct_llvm_name(key)
    field_types: [dynamic]string
    for &f in sd.fields {
        append(&field_types, field_ir_type(&f))
    }
    fields_joined := strings.join(field_types[:], ", ")
    // #packed → LLVM packed struct `<{ ... }>` (no inter-field padding), so
    // field indices map 1:1 to byte offsets and #big_endian reads of on-disk
    // packed formats land correctly.
    type_decl: string
    if sd.is_packed {
        type_decl = strings.concatenate({llvm_name, " = type <{ ", fields_joined, " }>"})
    } else {
        type_decl = strings.concatenate({llvm_name, " = type { ", fields_joined, " }"})
    }
    append(&g.struct_decls, type_decl)
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
    pad_bytes := union_tag_pad_bytes(ut)
    tag_area_bytes := tag_bytes(ut.tag_type) + pad_bytes

    payload_str := fmt.tprintf("[%d x i8]", union_payload_bytes(ut))
    tag_field: string
    if pad_bytes > 0 {
        tag_field = fmt.tprintf("[%d x i8]", tag_area_bytes)
    } else {
        tag_field = tag_ir
    }
    type_decl := strings.concatenate({llvm_name, " = type { ", tag_field, ", ", payload_str, " }"})
    append(&g.struct_decls, type_decl)
}

// ---------------------------------------------------------------------------
// A union's tag, and a match whose subject holds no arm's
// ---------------------------------------------------------------------------

// A union value's tag, read from its storage. A tagged union keeps it in field
// 0. A niche union stores none — its storage is the Some variant's pointer — so
// its tag is whichever variant the pointer's nullness says it holds.
load_union_tag :: proc(g: ^Codegen, ut: ^Type_Union, union_ptr: string) -> string {
    tag_ir := union_tag_ir_type(ut)
    if is_niche_layout(g, ut) {
        some, none := niche_variants(g, ut)
        ptr := fresh_tmp(g)
        emit_load_into(g, ptr, "ptr", union_ptr)
        live := fresh_tmp(g)
        emit(g, "  %s = icmp ne ptr %s, null", live, ptr)
        tag := fresh_tmp(g)
        emit(g, "  %s = select i1 %s, %s %d, %s %d", tag, live,
             tag_ir, ut.tag_map[some], tag_ir, ut.tag_map[none])
        return tag
    }
    tag_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, union_llvm_name(ut.name), union_ptr)
    tag_val := fresh_tmp(g)
    emit_load_into(g, tag_val, tag_ir, tag_ptr)
    return tag_val
}

// A match's failure: its subject holds no arm's tag — corrupt memory, since
// every match covers every variant. `tag` (of IR type `tag_ir`) is reported.
emit_match_fail :: proc(g: ^Codegen, span: Span, tag, tag_ir: string, unsigned: bool) {
    wide := tag
    if tag_ir != "i64" {
        wide = fresh_tmp(g)
        emit(g, "  %s = %s %s %s to i64", wide, "zext" if unsigned else "sext", tag_ir, tag)
    }
    loc_global, _ := get_string_literal(g, span_location(span))
    emit(g, "  call void %s(ptr %s, i64 %s)", __MARA_MATCH_FAIL, loc_global, wide)
    emit(g, "  unreachable")
}

// Whether a union's tag is unsigned (`union(tag u32)`); the default i64 isn't.
union_tag_unsigned :: proc(ut: ^Type_Union) -> bool {
    return strings.has_prefix(ut.tag_type, "u")
}

// Whether a matched value is unsigned: an enum's declared tag type, a number's kind.
match_value_unsigned :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:   return strings.has_prefix(v.tag_type, "u")
    case Type_Numeric: return v.kind == .Unsigned
    case Type_Byte, Type_Utf8, Type_Bool: return true
    }
    return false
}
