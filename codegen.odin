package mara

import "core:fmt"
import "core:hash"
import "core:mem"
import "core:slice"
import "core:strconv"
import "core:strings"
import "core:os"

// ---------------------------------------------------------------------------
// The toolkit the emitter makes a function's instructions with (ir.odin):
// its state (Codegen), the instruction emitters, types' IR names and
// declarations, string globals, the runtime checks and the arena's calls.
// llvm.odin lowers each function from the program graph with it;
// codegen_module.odin assembles the .ll files.
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
    // The function being made: its instructions (ir.odin) — where they're
    // made, its allocas (hoisted to its entry while its body is), its body.
    code:        [dynamic]Ir,
    allocas:     [dynamic]Ir,
    body:        [dynamic]Ir,
    // The x86 backend's object for the module (nil: LLVM's — its text): each
    // function made goes into it (codegen_function).
    x86:         ^X86_Module,
    // Aggregate constants live in read-only tables (codegen_const.odin): the
    // tables this Codegen's functions referenced (symbol -> table).
    const_tables: map[string]Const_Table,

    // Per-module IR buffers. Each function's IR lands in the buffer keyed by
    // its home_package (switch_to_module swaps g.out to it); each buffer
    // becomes its module's .ll, compiled by clang in parallel. module_order
    // keeps first-seen order, for a deterministic build.
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
    tmp_counter: int,              // the function's temporaries so far (fresh_tmp)
    label_counter: int,            // label numbering (fresh_label's names)
    label_ids:   i32,              // the function's labels so far (ir_label)
    // Type info from the type checker
    checked:     ^Checked_Program,       // resolved type info from type checker
    // String literal table: value -> its global's symbol
    string_literals: map[string]string,
    string_names:    map[string]bool,   // symbols handed out, to catch a hash collision
    // Per-Codegen prefix for `@.str.<hash>` names. Empty for the main thread;
    // set to a module-specific tag by parallel codegen workers so each TU's
    // strings live in its own namespace.
    string_name_prefix: string,
    // The module's globals: its string literals (and -profile's slots, which
    // name them: llvm_probe).
    globals: [dynamic]Ir_Global,
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
    // -profile: the build, as the profile's header names it ("" when not
    // profiling). Funs worth timing tell the profiler (runtime/mara_prof.c)
    // when they're entered and left (llvm.odin, llvm_probe).
    profile: string,
    // What each fun's code reaches through its params (llvm.odin,
    // reach_summary): worked out as calls ask, once — each worker its own.
    summaries: map[^Type_Scope]^Fun_Summary,
    // What outlives a function's emission — the module's text, its string
    // literals, constant tables, intrinsics, the temporaries' names — is
    // made with this: a worker's module arena, the build's on the main
    // thread. A function's own emission is scratch (module_codegen_worker).
    keep: mem.Allocator,
    // Every function's code comes from the program graph (llvm.odin).

    // Inside an assert/crash fail block (native builds): print-shaped
    // emissions route through __mara_tee_printf, which mirrors the message
    // into crash.txt (runtime/mara_crash.c). Off everywhere else.
    tee: bool,
}

// What outlives a function's emission is made with (Codegen.keep).
codegen_keep :: proc(g: ^Codegen) -> mem.Allocator {
    return g.keep if g.keep.procedure != nil else context.allocator
}

// A fresh temporary, `%.t<n>`. (The `.` keeps it apart from a local: a
// Mara name has none, and a local is `%<name>`.)
fresh_tmp :: proc(g: ^Codegen) -> Val {
    g.tmp_counter += 1
    return {kind = .Temp, n = i128(g.tmp_counter)}
}

// A fresh label: its prefix, then the function's next label number.
fresh_label :: proc(g: ^Codegen, prefix: string) -> Ir_Label {
    g.label_counter += 1
    return ir_label(g, prefix, g.label_counter)
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


// A user-defined function's symbol. Names are already flat (e.g.,
// "sdl_Init") — flattened during type-checking by make_flat_name at
// registration.
mara_fn_name :: proc(g: ^Codegen, name: string) -> string {
    if name == "main" { return "main" }
    // `#expose fun foo` → unmangled `@foo` so a DLL host can call
    // GetProcAddress("foo") directly without knowing Mara's flat-naming rule.
    // Mara-internal call sites resolve to the same symbol, so callers in the
    // same package stay wired up.
    if cs, ok := g.checked.functions[name]; ok && cs.is_exposed {
        return cs.name
    }
    // IR symbols are prefixed with "mara_" to namespace them against system
    // libraries. flat names from stdlib modules (`mara.math`) already include
    // it via make_flat_name's dot→underscore conversion; user-module flats
    // like `camera_init` get prepended here.
    if strings.has_prefix(name, "mara_") { return name }
    return strings.concatenate({"mara_", name}, context.temp_allocator)
}

// A user-defined function's address.
mara_fn :: proc(g: ^Codegen, name: string) -> Val {
    return ir_global(mara_fn_name(g, name))
}

// The struct a function returns through its sret slot, when its one
// result is one: "" otherwise.
fn_ret_struct :: proc(g: ^Codegen, fn_name: string) -> string {
    cf, found := g.checked.functions[fn_name]
    if !found || fn_result_count(cf) != 1 { return "" }
    if sd := as_struct_body(fn_result(cf, 0)); sd != nil { return sd.name }
    return ""
}


// ---------------------------------------------------------------------------
// The common instructions (ir.odin), by what they do
// ---------------------------------------------------------------------------

// `store <ir_type> <val>, ptr <ptr>`
emit_store :: proc(g: ^Codegen, ir_type: string, val, ptr: Val) {
    ir_store(g, ir_type, val, ptr)
}

// `<dst> = load <ir_type>, ptr <ptr>`: a load into a name the caller has
// picked out.
emit_load_into :: proc(g: ^Codegen, dst: Val, ir_type: string, src_ptr: Val) {
    ir_load(g, dst, ir_type, src_ptr)
}

// A struct field's address, into a name the caller has picked out:
// `getelementptr <agg_type>, ptr <base>, i32 0, i32 <idx>`.
emit_field_gep_into :: proc(g: ^Codegen, dst: Val, agg_type: string, base: Val, idx: int) {
    ir_gep(g, dst, agg_type, base, {"i32", ir_int(0), {}}, {"i32", ir_int(idx), {}})
}

// A constant-index array element's address: `getelementptr <arr_type>, ptr
// <base>, i64 0, i64 <idx>`.
emit_array_gep_const :: proc(g: ^Codegen, dst: Val, arr_type: string, base: Val, idx: int) {
    ir_gep(g, dst, arr_type, base, {"i64", ir_int(0), {}}, {"i64", ir_int(idx), {}})
}

// A variable-index array element's address: `getelementptr <arr_type>, ptr
// <base>, i64 0, <idx_ir> <idx>`. Every call site states the index's width
// (SLICE_LEN_IR for a user's index or a slice header's, "i32" for a
// fixed-position counter).
emit_array_gep_var :: proc(g: ^Codegen, dst: Val, arr_type: string, base, idx: Val, idx_ir: string) {
    ir_gep(g, dst, arr_type, base, {"i64", ir_int(0), {}}, {idx_ir, idx, {}})
}

// An element's address from a raw element pointer (a slice's data):
// `getelementptr <elem_type>, ptr <base>, <idx_ir> <idx>`.
emit_elem_gep :: proc(g: ^Codegen, dst: Val, elem_type: string, base, idx: Val, idx_ir: string) {
    ir_gep(g, dst, elem_type, base, {idx_ir, idx, {}})
}

// `<dst> = alloca <ir_type>[, align <align>]`, with the hoisted allocas while
// hoisting. (Each is made once: llvm_storage names them.)
emit_alloca :: proc(g: ^Codegen, dst: Val, ir_type: string, align: i32 = 0) {
    append(&g.allocas if g.hoist_allocas else &g.code, Ir{op = .Alloca, dest = dst, ty = ir_type, align = align})
}

// `call void @llvm.memcpy.p0.p0.i64(ptr <dst>, ptr <src>, i64 <bytes>, i1 false)`
emit_memcpy :: proc(g: ^Codegen, dst, src: Val, bytes: int) {
    ir_call(g, {}, "void", ir_global("llvm.memcpy.p0.p0.i64"), {"ptr", dst, {}}, {"ptr", src, {}}, {"i64", ir_int(bytes), {}}, {"i1", IR_FALSE, {}})
}

// `call void @llvm.memset.p0.i64(ptr <dst>, i8 0, i64 <bytes>, i1 false)`
emit_memset_zero :: proc(g: ^Codegen, dst: Val, bytes: int) {
    ir_call(g, {}, "void", ir_global("llvm.memset.p0.i64"), {"ptr", dst, {}}, {"i8", ir_int(0), {}}, {"i64", ir_int(bytes), {}}, {"i1", IR_FALSE, {}})
}

emit_br :: proc(g: ^Codegen, label: Ir_Label) {
    ir_emit(g, {op = .Br, l = label})
}

emit_cond_br :: proc(g: ^Codegen, cond: Val, true_label, false_label: Ir_Label) {
    ir_emit(g, {op = .Cond_Br, a = cond, l = true_label, l2 = false_label})
}

// A block's label.
emit_label :: proc(g: ^Codegen, label: Ir_Label) {
    ir_emit(g, {op = .Label, l = label})
}

// The printf symbol for the current emission context: @printf normally,
// @__mara_tee_printf inside an assert/crash fail block (g.tee) so the
// message also lands in crash.txt.
printf_sym :: proc(g: ^Codegen) -> Val {
    return ir_global("__mara_tee_printf" if g.tee else "printf")
}

// `call i32 (ptr, ...) @printf(ptr <format>, <args>)` — `format` a C format
// (a string literal of its own).
emit_printf :: proc(g: ^Codegen, format: string, args: ..Ir_Arg) {
    all := make([]Ir_Arg, len(args) + 1)
    all[0] = {ty = "ptr", v = get_string_literal(g, format)}
    copy(all[1:], args)
    ir_emit(g, {op = .Call, ty = "i32", to = "(ptr, ...)", a = printf_sym(g), args = all})
}

// A function made — its head, its code's parts in order — into the module's
// x86 object, or as LLVM IR into its text: its entry labeled (`entry`), a
// blank line after it (`gap`). Its labels' ids start over for the next.
codegen_function :: proc(g: ^Codegen, head: Ir_Head, code: [][]Ir, entry := true, gap := true) {
    defer g.label_ids = 0
    if g.x86 != nil {
        x86_function(g.x86, head, code)
        return
    }
    b := &g.out
    ir_print_head(b, head)
    strings.write_string(b, "\nentry:\n" if entry else "\n")
    for part in code { ir_print_all(b, part) }
    strings.write_string(b, "}\n")
    if gap { strings.write_string(b, "\n") }
}

// Begin a function's body: its allocas hoisted to its entry (emit_alloca),
// the rest its body.
begin_alloca_hoist :: proc(g: ^Codegen) {
    g.allocas = make([dynamic]Ir)
    g.body = make([dynamic]Ir)
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


// Get the IR type for a union's tag field
union_tag_ir_type :: proc(ut: ^Type_Union) -> string {
    if ut.tag_type != "" {
        return tag_type_to_ir(ut.tag_type)
    }
    return "i64"
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
            // instead of allocating a fresh "i%d" string each call (a hot
            // path).
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
        // it i64.
        panic("llvm_type_from_checker: nil (unresolved) type reached codegen — the checker left a type unresolved without a diagnostic")
    }
    unreachable()
}

// ---------------------------------------------------------------------------
// Get or create a string literal global
// ---------------------------------------------------------------------------

get_string_literal :: proc(g: ^Codegen, s: string) -> Val {
    if name, ok := g.string_literals[s]; ok { return ir_global(name) }
    context.allocator = codegen_keep(g)   // (the module's: it outlives the function being emitted)
    context.temp_allocator = context.allocator
    // Named by content, not by order: a string's name doesn't depend on the
    // strings emitted before it, so one function's IR stays the same when
    // another changes. The per-worker prefix keeps the parallel codegens'
    // namespaces apart (empty on the main thread: `@.str.<hash>`).
    name := fmt.tprintf(".%sstr.%016x", g.string_name_prefix, hash.fnv64a(transmute([]byte)s))
    if name in g.string_names {
        codegen_fatal(g, {}, "internal: two string literals hash to %s", name)
    }
    g.string_names[name] = true
    // The table owns its key: callers pass transient views (print's format
    // pieces live in a reused buffer), and a borrowed key changes under the
    // map — `" "` then matched a stale `"="` entry.
    g.string_literals[strings.clone(s)] = name

    // Its bytes, then a 0.
    append(&g.globals, Ir_Global{name = name, linkage = .Private, unnamed = true, constant = true,
        ty = fmt.tprintf("[%d x i8]", len(s) + 1), init = {kind = .Bytes, bytes = strings.concatenate({s, "\x00"})}})
    return ir_global(name)
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

// ---------------------------------------------------------------------------
// Runtime safety checks
// ---------------------------------------------------------------------------

// The runtime checks' failures, each a function of its own the checks call
// (the main TU defines them, the others declare them): its name, its params
// — where it failed first, a string global's address — and its message.
// Each reports as any runtime failure does (emit_fail). (An assert's message
// is its own, built where it is: emit_assert_fail.)
__MARA_BOUNDS_FAIL    :: "__mara_bounds_fail"
__MARA_OVERFLOW_FAIL  :: "__mara_overflow_fail"
__MARA_DIVZ_FAIL      :: "__mara_divz_fail"
__MARA_SLICE_LEN_FAIL :: "__mara_slice_len_fail"
__MARA_MATCH_FAIL     :: "__mara_match_fail"

Runtime_Fail :: struct { name: string, params: []Runtime_Param, message: string }
Runtime_Param :: struct { ty, name: string }

RUNTIME_FAILS := [?]Runtime_Fail{
    {__MARA_BOUNDS_FAIL,    {{"ptr", "loc"}, {"i64", "idx"}, {"i64", "len"}, {"ptr", "name"}},     "%s runtime error: index %lld out of bounds [0, %lld) for '%s'\n"},
    {__MARA_OVERFLOW_FAIL,  {{"ptr", "loc"}},                                                    "%s runtime error: integer overflow\n"},
    {__MARA_DIVZ_FAIL,      {{"ptr", "loc"}},                                                    "%s runtime error: division by zero\n"},
    {__MARA_SLICE_LEN_FAIL, {{"ptr", "loc"}, {"i64", "new_len"}, {"i64", "cap"}, {"ptr", "name"}}, "%s runtime error: slice len %lld not in [0, %lld] (cap) for '%s'\n"},
    {__MARA_MATCH_FAIL,     {{"ptr", "loc"}, {"i64", "tag"}},                                    "%s runtime error: match on an invalid tag %lld\n"},
}

// The runtime's helpers, made as functions are (codegen_function): into the
// x86 object, or as LLVM IR — the text returned.
runtime_fail_helpers_ir :: proc(g: ^Codegen) -> string {
    saved := g.out
    defer g.out = saved
    g.out = strings.builder_make()
    strings.write_string(&g.out, "; Runtime fail-block helpers (hoisted)\n")
    for f in RUNTIME_FAILS {
        g.code = {}
        if !g.web { ir_call(g, {}, "void", ir_global("__mara_crash_begin")) }
        params := make([]Ir_Arg, len(f.params))
        for p, i in f.params { params[i] = {ty = p.ty, v = ir_local(p.name)} }
        args := make([dynamic]Ir_Arg, context.temp_allocator)
        append(&args, Ir_Arg{ty = "ptr", v = get_string_literal(g, f.message)})
        append(&args, ..params)
        ir_call_va(g, {}, "i32", "(ptr, ...)", ir_global("printf" if g.web else "__mara_tee_printf"), ..args[:])
        if !g.web { ir_call(g, {}, "void", ir_global("__mara_crash_end")) }
        ir_call(g, {}, "void", ir_global("exit"), {"i32", ir_int(1), {}})
        ir_unreachable(g)
        code := [?][]Ir{g.code[:]}
        codegen_function(g, {name = f.name, ret = "void", params = params}, code[:], entry = false)
    }
    // print_err: prints the qualified name of a u32 error value (set_id<<16 |
    // tag). One switch case per (set_id, tag) pair across all error_kinds
    // in the program; the 0 case is the universal `.Ok` and the default falls
    // back to "?(<val>)" for stray bits / out-of-range tags. Open-`err`-typed
    // print sites call this; concrete error_kind print sites still use the
    // inline switch from gen_print_enum.
    runtime_print_err_helper_ir(g)
    g.code = {}
    return strings.to_string(g.out)
}

runtime_print_err_helper_ir :: proc(g: ^Codegen) {
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

    // (Each string a global of the literal cache's: its address.)
    ok_str := get_string_literal(g, "Ok")
    fmt_str_s := get_string_literal(g, "%s")
    fmt_unknown := get_string_literal(g, "?(%u)")
    case_strs := make([dynamic]Val, 0, len(cases), context.temp_allocator)
    for c in cases {
        s := get_string_literal(g, c.qualified_name)
        append(&case_strs, s)
    }

    g.code = {}
    val := ir_local("val")
    ok, unknown := ir_label(g, "ok"), ir_label(g, "unknown")
    arms := make([]Ir_Arg, len(cases) + 1)
    arms[0] = {"i32", ir_int(0), ok}
    for c, i in cases { arms[i + 1] = {"i32", ir_int(c.value), ir_label(g, "case_", i)} }
    ir_switch(g, "i32", val, unknown, arms)
    say :: proc(g: ^Codegen, label: Ir_Label, format: Val, arg: Ir_Arg) {
        emit_label(g, label)
        ir_call_va(g, {}, "i32", "(ptr, ...)", ir_global("printf"), {"ptr", format, {}}, arg)
        ir_ret(g, "void")
    }
    say(g, ok, fmt_str_s, {"ptr", ok_str, {}})
    for s, i in case_strs { say(g, arms[i + 1].l, fmt_str_s, {"ptr", s, {}}) }
    say(g, unknown, fmt_unknown, {"i32", val, {}})
    code := [?][]Ir{g.code[:]}
    params := make([]Ir_Arg, 1)
    params[0] = {ty = "i32", v = val}
    codegen_function(g, {name = "__mara_print_err", ret = "void", params = params}, code[:], gap = false)
}

// A runtime bounds check: idx < 0 or idx >= len fails (__mara_bounds_fail);
// both at slice header width (SLICE_LEN_IR). `name` is the array's, for the
// message.
emit_bounds_check :: proc(g: ^Codegen, idx, len_val: Val, name: string, span: Span = {}) {
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
    ir_icmp(g, neg_cmp, .Slt, w, idx, ir_int(0))
    upper_cmp := fresh_tmp(g)
    ir_icmp(g, upper_cmp, .Sge, w, idx, len_val)
    combined := fresh_tmp(g)
    ir_bin(g, combined, .Or, "i1", neg_cmp, upper_cmp)
    emit_cond_br(g, combined, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := span_location(span)
    loc_global := get_string_literal(g, loc)
    name_global := get_string_literal(g, name)
    ir_call(g, {}, "void", ir_global(__MARA_BOUNDS_FAIL), {"ptr", loc_global, {}}, {w, idx, {}}, {w, len_val, {}}, {"ptr", name_global, {}})
    ir_unreachable(g)

    emit_label(g, ok_label)
}

// True when a slice assignment's value surely holds the run it fills: lo, hi
// and the value's length all integer constants, hi - lo no more than it.
can_elide_source_check :: proc(lo, hi, have: Val) -> bool {
    return lo.kind == .Int && hi.kind == .Int && have.kind == .Int && hi.n - lo.n <= have.n
}

// True when a span written into bytes surely is the value's size: lo and hi
// integer constants (the checker has said so already when they differ).
can_elide_span_check :: proc(lo, hi: Val) -> bool {
    return lo.kind == .Int && hi.kind == .Int
}

// True when an index surely passes its bounds check: it and the length
// integer constants, 0 <= idx < len.
can_elide_bounds_check :: proc(idx, len_val: Val) -> bool {
    return idx.kind == .Int && len_val.kind == .Int && idx.n >= 0 && idx.n < len_val.n
}

// Emit a runtime division-by-zero check. Compile-time elide when the divisor
// is a non-zero integer literal — `x / 4` never traps. Per-site cost otherwise
// is the compare + branch + 2 lines fail tail.
emit_div_zero_check :: proc(g: ^Codegen, divisor: Val, ir_type: string, span: Span = {}) {
    if divisor.kind == .Int && divisor.n != 0 {
        return
    }
    ok_label := fresh_label(g, "divz.ok")
    fail_label := fresh_label(g, "divz.fail")

    cmp := fresh_tmp(g)
    ir_icmp(g, cmp, .Eq, ir_type, divisor, ir_int(0))
    emit_cond_br(g, cmp, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := span_location(span)
    loc_global := get_string_literal(g, loc)
    ir_call(g, {}, "void", ir_global(__MARA_DIVZ_FAIL), {"ptr", loc_global, {}})
    ir_unreachable(g)

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
emit_checked_arith :: proc(g: ^Codegen, op: string, ir_type: string, left, right: Val, span: Span = {}) -> Val {
    if can_elide_overflow(op, ir_type, left, right) {
        result := fresh_tmp(g)
        inst: Ir_Inst   // ("sadd"/"uadd" → add, etc.)
        switch op[1:] {
        case "add": inst = .Add
        case "sub": inst = .Sub
        case "mul": inst = .Mul
        case:       codegen_fatal(g, span, "internal: no checked operation %s", op)
        }
        ir_bin(g, result, inst, ir_type, left, right)
        return result
    }

    ok_label   := fresh_label(g, "overflow.ok")
    fail_label := fresh_label(g, "overflow.fail")

    intrinsic_name := fmt.tprintf("llvm.%s.with.overflow.%s", op, ir_type)
    if intrinsic_name not_in g.overflow_intrinsics { intrinsic_name = strings.clone(intrinsic_name, codegen_keep(g)); g.overflow_intrinsics[intrinsic_name] = true }

    pair := fresh_tmp(g)
    ret_type := strings.concatenate({"{ ", ir_type, ", i1 }"})
    ir_call(g, pair, ret_type, ir_global(intrinsic_name), {ir_type, left, {}}, {ir_type, right, {}})

    result   := fresh_tmp(g)
    overflow := fresh_tmp(g)
    ir_extract(g, result, ret_type, pair, 0)
    ir_extract(g, overflow, ret_type, pair, 1)

    emit_cond_br(g, overflow, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := span_location(span)
    loc_global := get_string_literal(g, loc)
    ir_call(g, {}, "void", ir_global(__MARA_OVERFLOW_FAIL), {"ptr", loc_global, {}})
    ir_unreachable(g)

    emit_label(g, ok_label)
    return result
}

// True if both operands are integer literals AND the computed result provably
// fits in `ir_type`. For i64 (or unknown widths) we conservatively decline so
// we never need to detect i64 arithmetic overflow at codegen time; the runtime
// intrinsic handles those cases (LLVM folds it in optimized builds).
can_elide_overflow :: proc(op, ir_type: string, left, right: Val) -> bool {
    if left.kind != .Int || right.kind != .Int { return false }
    l_val, r_val := i64(left.n), i64(right.n)

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
get_context_arena_ptr :: proc(g: ^Codegen) -> Val {
    ctx_ptr := fresh_tmp(g)
    ir_load(g, ctx_ptr, "ptr", ir_global("__mara_program"))
    arena_ptr := fresh_tmp(g)
    emit_field_gep_into(g, arena_ptr, program_ir_name(g.checked), ctx_ptr, 0)
    return arena_ptr
}

// Emit a call to the Mara mark() function from the memory package.
emit_arena_mark :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    mark_ir := mara_fn(g, g.arena_mark_name)
    if ret := fn_ret_struct(g, g.arena_mark_name); ret != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(ret))
        ir_call(g, {}, "void", mark_ir, {"ptr", arena_ptr, {}}, {"ptr", dummy, {}})
    } else {
        ir_call(g, {}, "void", mark_ir, {"ptr", arena_ptr, {}})
    }
}

// Emit a call to arena_alloc() for a compile-time known size. Returns the data pointer.
emit_arena_bump :: proc(g: ^Codegen, size: int, name: string = "<alloc>", loc: string = "<unknown>") -> Val {
    return emit_arena_bump_val(g, ir_int(size), name, loc)
}

// Call the Mara arena_alloc() function from the memory package.
// arena_alloc(a: ^Arena, size: int, name: ^byte, span: ^byte) -> []byte
// Returns the data pointer. arena_alloc is responsible for aborting on
// OOM — it already prints diagnostics with the name / loc strings we
// pass in. No codegen-side check; if the user supplies a buggy arena
// that returns an invalid slice, downstream code crashes when it
// accesses the null ptr, same as any other broken function.
emit_arena_bump_val :: proc(g: ^Codegen, size_val: Val, name: string = "<alloc>", loc: string = "<unknown>") -> Val {
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
    name_ptr := get_string_literal(g, name)
    // Get a pointer to the span/location string literal
    span_ptr := get_string_literal(g, loc)
    // sret goes last, after the regular params. The size operand width matches
    // the arena's declared `alloc(..., size: <int-type>, ...)` — since every
    // alloc hands back a `[]byte`, the size shares the slice header width.
    alloc_ir := mara_fn(g, g.arena_alloc_name)
    w := SLICE_LEN_IR
    if g.arena_alloc_has_debug {
        ir_call(g, {}, "void", alloc_ir, {"ptr", arena_ptr, {}}, {w, size_val, {}}, {"ptr", name_ptr, {}}, {"ptr", span_ptr, {}}, {"ptr", tmp_slice, {}})
    } else {
        ir_call(g, {}, "void", alloc_ir, {"ptr", arena_ptr, {}}, {w, size_val, {}}, {"ptr", tmp_slice, {}})
    }
    // Extract raw data pointer from the returned slice header
    data_ptr := emit_header_field(g, tmp_slice, SLICE.ptr)

    return data_ptr
}

// Emit a call to the Mara reset() function from the memory package.
emit_arena_reset :: proc(g: ^Codegen) {
    arena_ptr := get_context_arena_ptr(g)
    reset_ir := mara_fn(g, g.arena_reset_name)
    if ret := fn_ret_struct(g, g.arena_reset_name); ret != "" {
        dummy := fresh_tmp(g)
        emit_alloca(g, dummy, struct_llvm_name(ret))
        ir_call(g, {}, "void", reset_ir, {"ptr", arena_ptr, {}}, {"ptr", dummy, {}})
    } else {
        ir_call(g, {}, "void", reset_ir, {"ptr", arena_ptr, {}})
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

// Generate an LLVM type declaration for a struct from checked type data.
register_struct_decl_sd :: proc(g: ^Codegen, sd: ^Scope_Body) {
    context.allocator = codegen_keep(g)   // (the module's: it outlives the function being emitted)
    context.temp_allocator = context.allocator
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
    context.allocator = codegen_keep(g)   // (the module's: it outlives the function being emitted)
    context.temp_allocator = context.allocator
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
    context.allocator = codegen_keep(g)   // (the module's: it outlives the function being emitted)
    context.temp_allocator = context.allocator
    g.registered_structs[ukey] = true
    llvm_name := union_llvm_name(ukey)

    // Niche layout: single pointer slot, no tag. Identifies None via null
    // and Some via a live pointer at the same offset.
    if ut.niche_some != "" {
        type_decl := strings.concatenate({llvm_name, " = type { ptr }"})
        append(&g.struct_decls, type_decl)
        return
    }
    // Its tag (with a pad: the bytes they take), then the rest of its size.
    header := union_header_bytes(ut)
    tag_field := union_tag_ir_type(ut) if ut.tag_pad == nil else fmt.tprintf("[%d x i8]", header)
    type_decl := strings.concatenate({llvm_name, " = type { ", tag_field, ", ", fmt.tprintf("[%d x i8]", type_size(ut) - header), " }"})
    append(&g.struct_decls, type_decl)
}

// ---------------------------------------------------------------------------
// A union's tag, and a match whose subject holds no arm's
// ---------------------------------------------------------------------------

// A union value's tag, read from its storage. A tagged union keeps it in field
// 0. A niche union stores none — its storage is the Some variant's pointer — so
// its tag is whichever variant the pointer's nullness says it holds.
load_union_tag :: proc(g: ^Codegen, ut: ^Type_Union, union_ptr: Val) -> Val {
    tag_ir := union_tag_ir_type(ut)
    if some := ut.niche_some; some != "" {
        none := union_niche_none(ut)
        ptr := fresh_tmp(g)
        emit_load_into(g, ptr, "ptr", union_ptr)
        live := fresh_tmp(g)
        ir_icmp(g, live, .Ne, "ptr", ptr, IR_NULL)
        tag := fresh_tmp(g)
        ir_select(g, tag, live, tag_ir, ir_int(ut.tag_map[some]), ir_int(ut.tag_map[none]))
        return tag
    }
    tag_ptr := fresh_tmp(g)
    emit_field_gep_into(g, tag_ptr, union_llvm_name(ut.name), union_ptr, 0)
    tag_val := fresh_tmp(g)
    emit_load_into(g, tag_val, tag_ir, tag_ptr)
    return tag_val
}

// A match's failure: its subject holds no arm's tag — corrupt memory, since
// every match covers every variant. `tag` (of IR type `tag_ir`) is reported.
emit_match_fail :: proc(g: ^Codegen, span: Span, tag: Val, tag_ir: string, unsigned: bool) {
    wide := tag
    if tag_ir != "i64" {
        wide = fresh_tmp(g)
        ir_cast(g, wide, Ir_Inst.Zext if unsigned else .Sext, tag_ir, tag, "i64")
    }
    loc_global := get_string_literal(g, span_location(span))
    ir_call(g, {}, "void", ir_global(__MARA_MATCH_FAIL), {"ptr", loc_global, {}}, {"i64", wide, {}})
    ir_unreachable(g)
}

// Whether a union's tag is unsigned (`union(tag u32)`); the default i64 isn't.
union_tag_unsigned :: proc(ut: ^Type_Union) -> bool {
    return strings.has_prefix(ut.tag_type, "u")
}

// Whether a matched value is unsigned: an enum's declared tag type, else as
// llvm_unsigned.
match_value_unsigned :: proc(t: Type) -> bool {
    if et, is_enum := distinct_base(t).(^Type_Enum); is_enum { return strings.has_prefix(et.tag_type, "u") }
    return llvm_unsigned(t)
}
