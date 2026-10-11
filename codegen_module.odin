package mara

import "core:fmt"
import "core:slice"
import "core:strings"
import "core:os"
import "core:thread"
import "core:mem/virtual"
import os_old "core:os/old"

// ---------------------------------------------------------------------------
// The program's IR: generate_program emits each module's functions in
// parallel (a worker per module, llvm.odin lowering each function), then
// assembles each module's .ll — its types, constants, string globals and the
// declares of what it uses from other modules — with @main's setup in the
// main module's.
// ---------------------------------------------------------------------------

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
// private mutable state (tmp_pool, string_decls, etc.). After
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
    string_decls:        [dynamic]string,
    overflow_intrinsics: map[string]bool,
    bswap_intrinsics:    map[int]bool,
    imports:             map[string]bool,
    const_tables:        map[string]Const_Table,
}

// Worker entry point. Sets up an isolated arena allocator, builds a local
// Codegen with the right read-only state copied from main_g, and emits
// every function assigned to this task.
@(private="file")
module_codegen_worker :: proc(t: thread.Task) {
    task := cast(^Module_Task)t.data

    // Each worker gets its own arena. Allocations (string interning,
    // tmp-pool buffers, etc.) all
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
        // Foreigns and intrinsics have no body: a call goes through its
        // `declare` and link name, or expands where it is.
        if _, src := cf.origin.(Origin_Source); !src { continue }
        llvm_function(&local, cf)
    }
    flush_current_module(&local)

    // Surface the per-module state into the task struct so the main
    // thread can pick it up after pool_finish.
    if buf, ok := local.module_outs[task.module_name]; ok {
        task.out = buf
    }

    task.string_decls        = local.string_decls
    task.overflow_intrinsics = local.overflow_intrinsics
    task.bswap_intrinsics    = local.bswap_intrinsics
    task.const_tables        = local.const_tables
}

// Build a Codegen suitable for one worker. Read-only fields (checked,
// target flags, arena_*_name, registered struct decls) come straight from
// main_g. Mutable per-function state (tmp_pool, …) starts empty
// and lives in the worker's arena.
@(private="file")
init_worker_codegen :: proc(g: ^Codegen, task: ^Module_Task) {
    g.checked            = task.checked
    g.web                = task.web
    g.shared             = task.shared_mode
    g.profile            = task.main_g.profile

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
// last function in a phase so the final assembly step sees the latest buffer
// state.
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

// Build module_imports by walking each module's buffer for `@<name>`
// references and subtracting the locally-defined names. Skips well-known
// categories every TU declares anyway (libc, LLVM intrinsics, the per-TU
// `@.str.N` globals). Pass `main_extras_ir` to fold extra IR text
// (typically the @main entry-point block) into the main TU's import set.
compute_module_imports :: proc(g: ^Codegen, main_package, main_extras_ir: string) {
    g.module_imports = make(map[string]map[string]bool)
    // Parallel pass: each module with an emission task computes its own import
    // set into its task slot, reusing that task's arena.
    itasks := make([dynamic]^Module_Imports_Task, 0, len(g.module_tasks))
    datas  := make([dynamic]rawptr, 0, len(g.module_tasks))
    in_tasks: map[string]bool
    defer {
        for it in itasks { free(it) }
        delete(itasks)
        delete(datas)
        delete(in_tasks)
    }
    for mt in g.module_tasks {
        in_tasks[mt.module_name] = true
        it := new(Module_Imports_Task)
        it.mt = mt
        it.main_package = main_package
        it.main_extras_ir = main_extras_ir
        append(&itasks, it)
        append(&datas, rawptr(it))
    }
    run_module_pool(datas[:], module_imports_worker)
    for mt in g.module_tasks {
        g.module_imports[mt.module_name] = mt.imports
    }
    // Serial pass: module_order entries without an emission task (e.g. the main
    // TU when the main package has no non-`main` functions — its only content
    // is @main, emitted into main_builder). Few in number; main allocator.
    for module_name in g.module_order {
        if module_name in in_tasks { continue }
        module_ir := ""
        if buf, ok := g.module_outs[module_name]; ok {
            module_ir = strings.to_string(buf)
        }
        g.module_imports[module_name] = imports_from_ir(
            module_ir, main_extras_ir, module_name == main_package)
    }
}

// ---------------------------------------------------------------------------
// Parallel post-emission passes
//
// Import-set computation and per-module .ll assembly are both independent per
// module — each reads already-frozen shared state (g.module_outs, the declare
// indexes) and writes only its own slot — so they reuse the emission phase's
// worker-pool pattern. Each worker allocates into its module's existing
// per-emission arena (alive for all of generate_program); the main thread
// collects results after pool_finish.
// ---------------------------------------------------------------------------

@(private="file")
import_skip_libc :: proc(name: string) -> bool {
    return name == "printf" || name == "exit" || name == "strlen"
}

@(private="file")
scan_ir_symbols :: proc(ir: string, defined, referenced: ^map[string]bool) {
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

// Compute one module's import set: symbols it references but doesn't define,
// minus llvm intrinsics, private `.`-locals, and the libc trio. The main TU
// folds in @main's references (main_extras_ir). Result is allocated in the
// caller's context.allocator.
@(private="file")
imports_from_ir :: proc(module_ir, main_extras_ir: string, is_main: bool) -> map[string]bool {
    defined: map[string]bool
    referenced: map[string]bool
    defer { delete(defined); delete(referenced) }
    scan_ir_symbols(module_ir, &defined, &referenced)
    if is_main && main_extras_ir != "" {
        scan_ir_symbols(main_extras_ir, &defined, &referenced)
    }
    imports: map[string]bool
    for name in referenced {
        if name in defined { continue }
        if strings.has_prefix(name, "llvm.") { continue }
        // String globals (`.str.N` / `.<module>_str.N`) are private-linkage
        // locals, never imports.
        if len(name) > 0 && name[0] == '.' { continue }
        if import_skip_libc(name) { continue }
        imports[name] = true
    }
    return imports
}

// Run `worker` over each pointer in `datas` on a core-sized pool. Pool
// bookkeeping uses the caller's (main-thread) allocator; each worker installs
// its own arena allocator on entry.
@(private="file")
run_module_pool :: proc(datas: []rawptr, worker: thread.Task_Proc) {
    if len(datas) == 0 { return }
    pool: thread.Pool
    num_workers := os_old.processor_core_count()
    if num_workers < 1 { num_workers = 1 }
    if num_workers > len(datas) { num_workers = len(datas) }
    thread.pool_init(&pool, context.allocator, num_workers)
    defer thread.pool_destroy(&pool)
    thread.pool_start(&pool)
    for d in datas {
        thread.pool_add_task(&pool, context.allocator, worker, d)
    }
    thread.pool_finish(&pool)
}

@(private="file")
Module_Imports_Task :: struct {
    mt:             ^Module_Task,
    main_package:   string,
    main_extras_ir: string,
}

@(private="file")
module_imports_worker :: proc(t: thread.Task) {
    it := cast(^Module_Imports_Task)t.data
    mt := it.mt
    context.allocator = virtual.arena_allocator(&mt.arena)
    context.temp_allocator = context.allocator
    mt.imports = imports_from_ir(strings.to_string(mt.out), it.main_extras_ir,
                                 mt.module_name == it.main_package)
}

@(private="file")
Module_Build_Shared :: struct {
    g:                   ^Codegen,
    checked:             ^Checked_Program,
    web:                 bool,
    fail_helpers_ir:     string,
    main_builder_str:    string,
    foreign_declares:    map[string]string,
    fn_declares:         map[string]string,
    struct_decl_by_name: map[string]string,
    build_dir:           string,
}

@(private="file")
Module_Build_Task :: struct {
    shared:    ^Module_Build_Shared,
    mt:        ^Module_Task,
    write_err: bool,
}

@(private="file")
module_build_worker :: proc(t: thread.Task) {
    bt := cast(^Module_Build_Task)t.data
    s := bt.shared
    mt := bt.mt
    context.allocator = virtual.arena_allocator(&mt.arena)
    context.temp_allocator = context.allocator
    is_main_tu := mt.module_name == s.checked.main_package
    content := build_module_ll(s.g, s.checked, mt.module_name, is_main_tu, s.web,
                               s.fail_helpers_ir, s.main_builder_str,
                               s.foreign_declares, s.fn_declares,
                               s.struct_decl_by_name, mt)
    path := module_ll_path(s.build_dir, mt.module_name)
    werr := os.write_entire_file(path, transmute([]u8)content)
    bt.write_err = werr != nil
}

// Emit LLVM IR for the checked program. Every visible function gets
// emitted; the linker drops unreachable code. Returns the list of per-
// module .ll files produced (one per home_package in g.module_order),
// plus a success flag.
generate_program :: proc(output_path: string, checked: ^Checked_Program, web: bool = false, shared: bool = false, profile: string = "") -> ([]string, bool) {
    g := Codegen{}
    g.checked = checked
    g.web = web
    g.shared = shared
    g.profile = profile


    // g.out is now a swap target driven by switch_to_module; each per-module
    // buffer is pre-sized to 4MB on first creation. No global pre-size here.

    // Context system: scope allocator setup. Enabled when either:
    //   - the user declared `context.scope_allocator = X` (has_scope_allocator), OR
    //   - we're in shared mode and there's at least one `#expose` fn (host
    //     will pass a Context at runtime).
    g.context_enabled = checked.table.has_scope_allocator || checked.table.context_expected_at_runtime
    if g.context_enabled && checked.table.scope_allocator_type != nil {
        // The arena: a struct constructed with its size (`Arena_Debug(cap)`),
        // what an arena does its functions.
        alloc_type := checked.table.scope_allocator_type
        g.arena_new_name = alloc_type.name
        if fn, ok := alloc_type.functions["alloc"]; ok && fn != nil { g.arena_alloc_name = fn.name }
        if fn, ok := alloc_type.functions["mark"];  ok && fn != nil { g.arena_mark_name  = fn.name }
        if fn, ok := alloc_type.functions["reset"]; ok && fn != nil { g.arena_reset_name = fn.name }
        // (alloc() may take debug params, name and span, past (arena, size).)
        if alloc_cf, af_ok := checked.functions[g.arena_alloc_name]; af_ok {
            g.arena_alloc_has_debug = len(alloc_cf.cg_params) > 2
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
        // Skip Fun-kind entries: they're callable functions, not data-layout
        // types. Emitting them as LLVM structs produces invalid IR (void
        // return types end up as struct fields).
        if st.kind == .Fun { continue }
        register_struct_decl(&g, st)
    }

    // Register all unions from checked type data (keys are flat — flattened during type-checking)
    union_keys: [dynamic]string
    defer delete(union_keys)
    for k in checked.table.unions { append(&union_keys, k) }
    slice.sort(union_keys[:])
    for ukey in union_keys {
        if ukey not_in g.registered_structs {
            register_union_type(&g, ukey, checked.table.unions[ukey])
        }
    }

    // Build set of explicitly declared function names (in written order)
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

    // Build tasks in a deterministic order (by module name) so module_order
    // ends up the same regardless of how the pool schedules workers.
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
        // Constant tables any worker referenced; the main TU defines them all.
        for name, table in t.const_tables { g.const_tables[name] = table }
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
    g.label_counter = 0
    // On web (wasm32), the C entry point's `int` is i32, not i64. We keep
    // Mara's main internally as i64 so user `return X` and the args-setup
    // size_t handling don't change, and emit a tiny i32 wrapper after.
    if g.web {
        emit_raw(&g, "define i64 @__mara_main(i32 %.argc, ptr %.argv) {")
    } else {
        emit_raw(&g, "define i64 @main(i32 %.argc, ptr %.argv) {")
    }
    emit_raw(&g, "entry:")

    emit_main_prologue(&g, checked)
    if g.profile != "" { emit(&g, "  call void @__mara_prof_start(ptr %s)", get_string_literal(&g, g.profile)) }

    main_cf, main_ok := checked.functions["main"]
    if !main_ok {
        // The package has a `main` (else this is a shared build and @main is
        // skipped), so the checker failed to extract it. Emitting the prologue
        // alone leaves @main without a body or a `ret`, which clang rejects
        // far from the cause.
        codegen_fatal(&g, {}, "`main` was declared but never extracted as a function")
    }
    // Main's body, from the graph.
    llvm_main(&g, main_cf)

    // Web wrapper: `i32 @main(i32, ptr)` calling our i64 mara main and
    // truncating the return code so emscripten's runtime sees a regular int.
    if g.web {
        emit_raw(&g, "")
        emit_raw(&g, "define i32 @main(i32 %.argc, ptr %.argv) {")
        emit_raw(&g, "  %r = call i64 @__mara_main(i32 %.argc, ptr %.argv)")
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

    // Per-module .ll assembly + write, in parallel. Each module reads only
    // frozen shared state (g.module_outs, the declare indexes) and writes its
    // own distinct file, so the work parallelizes like emission. build_module_ll
    // is read-only on `g`; each worker assembles into its module's arena.
    bshared := Module_Build_Shared{
        g                   = &g,
        checked             = checked,
        web                 = web,
        fail_helpers_ir     = fail_helpers_ir,
        main_builder_str    = main_builder_str,
        foreign_declares    = foreign_declares,
        fn_declares         = fn_declares,
        struct_decl_by_name = struct_decl_by_name,
        build_dir           = build_dir,
    }
    btasks := make([dynamic]^Module_Build_Task, 0, len(g.module_tasks))
    bdatas := make([dynamic]rawptr, 0, len(g.module_tasks))
    in_tasks: map[string]bool
    defer {
        for bt in btasks { free(bt) }
        delete(btasks)
        delete(bdatas)
        delete(in_tasks)
    }
    for mt in g.module_tasks {
        in_tasks[mt.module_name] = true
        bt := new(Module_Build_Task)
        bt.shared = &bshared
        bt.mt = mt
        append(&btasks, bt)
        append(&bdatas, rawptr(bt))
    }
    run_module_pool(bdatas[:], module_build_worker)

    // Collect paths serially (in module_tasks order) — module_ll_path is
    // deterministic, so re-derive into the durable allocator here rather than
    // holding the workers' arena-local copies.
    g.module_ll_paths = make([dynamic]string)
    for bt in btasks {
        if bt.write_err {
            fmt.printf("Error: could not write '%s'\n", module_ll_path(build_dir, bt.mt.module_name))
            return nil, false
        }
        append(&g.module_ll_paths, module_ll_path(build_dir, bt.mt.module_name))
    }

    // Serial: module_order entries without an emission task (the main TU's
    // @main lives here). build_module_ll gets a nil task — its strings come
    // from g.string_decls under the is_main_tu branch, matching the prior
    // single-threaded path exactly.
    for module_name in g.module_order {
        if module_name in in_tasks { continue }
        is_main_tu := module_name == checked.main_package
        content := build_module_ll(&g, checked, module_name, is_main_tu, web,
                                    fail_helpers_ir, main_builder_str,
                                    foreign_declares, fn_declares,
                                    struct_decl_by_name, nil)
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

    // Constant tables: all of them defined here in the main TU, extern-declared
    // wherever else they're read.
    const_ir := module_const_ir(g, module_name, is_main_tu)

    // Struct/union type definitions — TU-local LLVM type namespace means we
    // only need the types this module actually references (plus the transitive
    // closure of their field types). Collect from the module's own IR + the
    // main TU's @main / fail-helper IR, and the constant tables' types.
    {
        used := collect_used_types(g.module_outs[module_name], struct_decl_by_name)
        collect_used_types_into(const_ir, struct_decl_by_name, &used)
        if is_main_tu {
            collect_used_types_into(main_builder_str, struct_decl_by_name, &used)
            collect_used_types_into(fail_helpers_ir, struct_decl_by_name, &used)
        }
        // The `@__mara_program_storage` global below references %class.Program
        // in every TU (main TU defines it, others extern-declare it), so seed
        // its transitive closure into the used set even if the module's body
        // never names the type directly.
        program_name := program_ir_name(checked)
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
        strings.write_string(&b, strings.concatenate({"@__mara_program_storage = global ", program_ir_name(checked), " zeroinitializer\n\n"}))
    } else {
        strings.write_string(&b, "@__mara_program = external global ptr\n")
        strings.write_string(&b, strings.concatenate({"@__mara_program_storage = external global ", program_ir_name(checked), "\n\n"}))
    }
    strings.write_string(&b, const_ir)

    // libc + intrinsic + foreign declares — every TU declares regardless.
    // Intrinsics are per-module (only what this TU actually uses);
    // foreign symbols are program-wide so the same block is included
    // in every TU.
    strings.write_string(&b, "; External declarations\n")
    strings.write_string(&b, "declare i32 @printf(ptr, ...)\n")
    strings.write_string(&b, "declare void @exit(i32)\n")
    if !g.web {
        // Crash-journal runtime, defined in runtime/mara_crash.c and linked
        // into every native build (see ensure_crash_runtime in main.odin).
        strings.write_string(&b, "declare void @__mara_crash_begin()\n")
        strings.write_string(&b, "declare i32 @__mara_tee_printf(ptr, ...)\n")
        strings.write_string(&b, "declare void @__mara_crash_end()\n")
    }
    if g.profile != "" {
        // The profiler, runtime/mara_prof.c: linked into a -profile build.
        strings.write_string(&b, "declare void @__mara_prof_start(ptr)\n")
        strings.write_string(&b, "declare void @__mara_prof_enter(ptr)\n")
        strings.write_string(&b, "declare void @__mara_prof_exit(ptr)\n")
    }
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
        for f in RUNTIME_FAILS { fmt.sbprintf(&b, "declare void %s(%s)\n", f.name, f.params) }
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
// header (llvm.odin's). That path is involved
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
        result[fo.link_name] = build_c_declare(cs, fo.link_name, checked.target_os)
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

// The program's setup, at @main's entry: the program global (the context), its
// arena when there is a scope allocator, and context.args from argv. The
// user's main body follows it.
emit_main_prologue :: proc(g: ^Codegen, checked: ^Checked_Program) {
    // Context: backed by a real LLVM global so it survives main returning.
    // Required for web builds where emscripten owns the main loop —
    // emscripten_set_main_loop_arg returns to JS, the rAF callback runs
    // after main's stack is gone, and any later @__mara_program load would
    // dereference a dangling stack pointer (manifests as arena.base.cap
    // reading 0 and the very first byte-buffer write tripping the bounds
    // check). Native is unaffected: same global lifetime, same fields.
    {
        ctx_alloca := "@__mara_program_storage"
        emit_raw(g, strings.concatenate({"  store ptr ", ctx_alloca, ", ptr @__mara_program"}))

        // Arena init (if scope allocator is active).
        if g.context_enabled {
            arena_ptr := fresh_tmp(g)
            emit_raw(g, strings.concatenate({"  ", arena_ptr, " = getelementptr ", program_ir_name(checked), ", ptr ", ctx_alloca, ", i32 0, i32 0"}))
            new_ir := mara_fn_name(g, g.arena_new_name)
            alloc_size := "268435456"  // default 256 MB
            if n, sized := checked.table.scope_allocator_size.?; sized { alloc_size = fmt.tprintf("%d", n) }
            emit_raw(g, strings.concatenate({"  call void ", new_ir, "(i64 ", alloc_size, ", ptr ", arena_ptr, ")"}))
        }

        // Populate context.args — partial array {len, cap, ptr, [64 x slice]}
        // embedded as a field of Context.
        args_field_idx := "1" if g.context_enabled else "0"
        ARGS_CAP :: "64"
        pa_ir := partial_array_ir_type(SLICE_IR_TYPE, 64)

        // GEP to the partial-array field within Context
        args_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", args_ptr, " = getelementptr ", program_ir_name(checked), ", ptr ", ctx_alloca, ", i32 0, i32 ", args_field_idx}))

        // More arguments than the args array holds is an error, not a silent
        // truncation — a program handed a long file list must not quietly
        // miss the tail. (Raise ARGS_CAP if 64 ever proves too few.)
        argc_over := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", argc_over, " = icmp sgt i32 %.argc, ", ARGS_CAP}))
        args_err_lbl := fmt.tprintf("args_too_many_%d", g.label_counter)
        args_ok_lbl := fmt.tprintf("args_ok_%d", g.label_counter)
        emit_raw(g, strings.concatenate({"  br i1 ", argc_over, ", label %", args_err_lbl, ", label %", args_ok_lbl}))
        emit_raw(g, strings.concatenate({args_err_lbl, ":"}))
        emit_fail(g, "runtime error: too many command-line arguments: %d (the limit is " + ARGS_CAP + ")\n", "i32 %.argc")
        emit_raw(g, strings.concatenate({args_ok_lbl, ":"}))
        argc_min := "%.argc" // every argument fits from here on

        // Its header: len argc (i32, as the loop counter below; the header's
        // i64), cap 64, ptr its elements (field 3).
        len_store_val := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", len_store_val, " = sext i32 ", argc_min, " to ", SLICE_LEN_IR}))
        emit_header_set(g, args_ptr, SLICE.len, len_store_val)
        emit_header_set(g, args_ptr, SLICE.cap, ARGS_CAP)
        elements_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr ", pa_ir, ", ptr ", args_ptr, ", i32 0, i32 3"}))
        emit_header_set(g, args_ptr, SLICE.ptr, elements_ptr)

        // Loop: for i = 0; i < len; i++ — fill elements[i] = { strlen, strlen, argv[i] }
        // Counter is i32 to match argc and the slice header — no widen/trunc.
        loop_i := fresh_tmp(g)
        emit_alloca(g, loop_i, "i32")
        emit_raw(g, strings.concatenate({"  store i32 0, ptr ", loop_i}))
        loop_lbl := fmt.tprintf("args_loop_%d", g.label_counter)
        body_lbl := fmt.tprintf("args_body_%d", g.label_counter)
        done_lbl := fmt.tprintf("args_done_%d", g.label_counter)
        g.label_counter += 1
        emit_raw(g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(g, strings.concatenate({loop_lbl, ":"}))
        cur_i := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", cur_i, " = load i32, ptr ", loop_i}))
        cmp := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", cmp, " = icmp slt i32 ", cur_i, ", ", argc_min}))
        emit_raw(g, strings.concatenate({"  br i1 ", cmp, ", label %", body_lbl, ", label %", done_lbl}))

        emit_raw(g, strings.concatenate({body_lbl, ":"}))
        argv_i_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", argv_i_ptr, " = getelementptr ptr, ptr %.argv, i32 ", cur_i}))
        argv_i := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", argv_i, " = load ptr, ptr ", argv_i_ptr}))
        // strlen returns size_t (i64 native, i32 on web), widened to the
        // header's i64 for the len/cap store.
        str_len := fresh_tmp(g)
        if g.web {
            str_len_32 := fresh_tmp(g)
            emit_raw(g, strings.concatenate({"  ", str_len_32, " = call i32 @strlen(ptr ", argv_i, ")"}))
            emit_raw(g, strings.concatenate({"  ", str_len, " = zext i32 ", str_len_32, " to ", SLICE_LEN_IR}))
        } else {
            emit_raw(g, strings.concatenate({"  ", str_len, " = call i64 @strlen(ptr ", argv_i, ")"}))
        }
        // elements[i] is a slice — write len, cap, ptr. cap counts argv's
        // terminating 0 (as a string literal's does), so cstring(arg) finds it
        // at [len] — passing an argument to a file open or any C call works.
        elem_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", elem_ptr, " = getelementptr [64 x ", SLICE_IR_TYPE, "], ptr ", elements_ptr, ", i32 0, i32 ", cur_i}))
        emit_header_set(g, elem_ptr, SLICE.len, str_len)
        str_cap := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", str_cap, " = add ", SLICE_LEN_IR, " ", str_len, ", 1"}))
        emit_header_set(g, elem_ptr, SLICE.cap, str_cap)
        emit_header_set(g, elem_ptr, SLICE.ptr, argv_i)
        // i++
        next_i := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", next_i, " = add i32 ", cur_i, ", 1"}))
        emit_raw(g, strings.concatenate({"  store i32 ", next_i, ", ptr ", loop_i}))
        emit_raw(g, strings.concatenate({"  br label %", loop_lbl}))

        emit_raw(g, strings.concatenate({done_lbl, ":"}))
    }
}
