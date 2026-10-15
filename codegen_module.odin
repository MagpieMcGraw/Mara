package mara

import "base:runtime"
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
        // (A module's text grows by reallocating: the heap's, which gives
        // back what it grew out of — an arena keeps every size it passed.)
        b: strings.Builder
        strings.builder_init_len_cap(&b, 0, 64 * 1024, runtime.heap_allocator())
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
// private mutable state (globals, intrinsics, etc.). After
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
    // read task.out / globals / overflow_intrinsics in arena memory.
    // Destroyed when generate_program is fully done (or just left to be
    // reclaimed at process exit — Mara's overall arena does the same).
    arena:       virtual.Arena,

    // Outputs — populated by the worker proc
    out:                 strings.Builder,
    globals:             [dynamic]Ir_Global,
    overflow_intrinsics: map[string]bool,
    bswap_intrinsics:    map[int]bool,
    const_tables:        map[string]Const_Table,
    // What its functions name (codegen_note): the globals they reference,
    // themselves and their declares, the types they use.
    refs:                map[string]bool,
    defs:                map[string]bool,
    declares:            map[string]string,
    types_used:          [dynamic]bool,

    // The x86 backend: whether it's the one, and the module's object.
    use_x86:             bool,
    debug:               bool,    // (x86) with debug info
    x86:                 ^X86_Module,
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
    if task.use_x86 { local.x86 = x86_begin(x86_program(), task.checked if task.debug else nil, task.module_name) }

    // Emit this module's functions. switch_to_module + flush handle the
    // g.out buffer swap so emit_target routes correctly. Each function's
    // emission — its storage facts, its values, its lines as they're
    // formatted — is scratch, let go of once it's written into the module's
    // text; what outlives it is made in the module's arena (Codegen.keep).
    switch_to_module(&local, task.module_name)
    scratch: virtual.Arena
    _ = virtual.arena_init_growing(&scratch)
    defer virtual.arena_destroy(&scratch)
    for fn_name in task.fn_names {
        cf, cf_ok := task.checked.functions[fn_name]
        if !cf_ok { continue }
        // Foreigns and intrinsics have no body: a call goes through its
        // `declare` and link name, or expands where it is.
        if _, src := cf.origin.(Origin_Source); !src { continue }
        {
            context.allocator = virtual.arena_allocator(&scratch)
            context.temp_allocator = context.allocator
            llvm_function(&local, cf)
        }
        virtual.arena_free_all(&scratch)
    }
    flush_current_module(&local)

    // Surface the per-module state into the task struct so the main
    // thread can pick it up after pool_finish.
    if buf, ok := local.module_outs[task.module_name]; ok {
        task.out = buf
    }

    task.globals             = local.globals
    task.x86                 = local.x86
    task.overflow_intrinsics = local.overflow_intrinsics
    task.bswap_intrinsics    = local.bswap_intrinsics
    task.const_tables        = local.const_tables
    task.refs, task.defs     = local.refs, local.defs
    task.declares            = local.declares
    task.types_used          = local.types_used
}

// Build a Codegen suitable for one worker. Read-only fields (checked,
// target flags, arena_*_name, registered struct decls) come straight from
// main_g. Mutable per-function state starts empty
// and lives in the worker's arena.
@(private="file")
init_worker_codegen :: proc(g: ^Codegen, task: ^Module_Task) {
    // (What outlives a function's emission, made where its module's is —
    // every table made here, so none takes the scratch it's first used in.)
    keep := context.allocator
    g.keep = keep
    g.string_literals = make(map[string]string, keep)
    g.string_names = make(map[string]bool, keep)
    g.globals = make([dynamic]Ir_Global, keep)
    g.registered_structs = make(map[string]bool, keep)
    g.refs, g.defs = make(map[string]bool, keep), make(map[string]bool, keep)
    g.declares = make(map[string]string, keep)
    g.types_used = make([dynamic]bool, keep)
    g.overflow_intrinsics = make(map[string]bool, keep)
    g.bswap_intrinsics = make(map[int]bool, keep)
    g.const_tables = make(map[string]Const_Table, keep)
    g.summaries = make(map[^Type_Scope]^Fun_Summary, keep)
    g.module_outs = make(map[string]strings.Builder, keep)
    g.module_order = make([dynamic]string, keep)
    g.checked            = task.checked
    g.web                = task.web
    g.shared             = task.shared_mode
    g.profile            = task.main_g.profile
    g.profile_memory     = task.main_g.profile_memory
    g.mem_sites          = make(map[string]string, keep)

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

    // The structs and unions the program defines are main_g's (named_types):
    // the .ll-write phase defines each module's from them.
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

// Each module's imports: the globals its functions name but don't define —
// not LLVM's intrinsics, its private strings (`.`-named) or libc's three.
// The main TU's take in @main's (main_refs, main_defs).
compute_module_imports :: proc(g: ^Codegen, main_package: string, main_refs, main_defs: map[string]bool) {
    g.module_imports = make(map[string]map[string]bool)
    none: map[string]bool
    imports_of :: proc(refs, defs, more_refs, more_defs: map[string]bool) -> map[string]bool {
        imports: map[string]bool
        take :: proc(refs, defs, more_defs: map[string]bool, imports: ^map[string]bool) {
            for name in refs {
                if name in defs || name in more_defs { continue }
                if strings.has_prefix(name, "llvm.") { continue }
                if len(name) > 0 && name[0] == '.' { continue }
                if import_skip_libc(name) { continue }
                imports[name] = true
            }
        }
        take(refs, defs, more_defs, &imports)
        take(more_refs, defs, more_defs, &imports)
        return imports
    }
    in_tasks: map[string]bool
    defer delete(in_tasks)
    for mt in g.module_tasks {
        in_tasks[mt.module_name] = true
        main := mt.module_name == main_package
        g.module_imports[mt.module_name] = imports_of(mt.refs, mt.defs, main_refs if main else none, main_defs if main else none)
    }
    // (A module with no emission task — the main TU when the main package has
    // no functions but `main` — has only @main's.)
    for module_name in g.module_order {
        if module_name in in_tasks { continue }
        main := module_name == main_package
        g.module_imports[module_name] = imports_of(none, none, main_refs if main else none, main_defs if main else none)
    }
}

// ---------------------------------------------------------------------------
// Parallel post-emission pass
//
// Per-module .ll assembly is independent per module — each reads
// already-frozen shared state (g.module_outs, the declare index) and writes
// only its own file — so it reuses the emission phase's worker-pool pattern.
// ---------------------------------------------------------------------------

@(private="file")
import_skip_libc :: proc(name: string) -> bool {
    return name == "printf" || name == "exit" || name == "strlen"
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
Module_Build_Shared :: struct {
    g:                   ^Codegen,
    checked:             ^Checked_Program,
    web:                 bool,
    fail_helpers_ir:     string,
    main_builder_str:    string,
    foreign_declares:    map[string]string,
    fn_declares:         map[string]string,
    main_types:          []bool,
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
    // (The module's .ll — its text copied in with what it declares — is
    // only written: assembled in scratch, let go of once it is.)
    scratch: virtual.Arena
    _ = virtual.arena_init_growing(&scratch)
    defer virtual.arena_destroy(&scratch)
    context.allocator = virtual.arena_allocator(&scratch)
    context.temp_allocator = context.allocator
    is_main_tu := mt.module_name == s.checked.main_package
    content := build_module_ll(s.g, s.checked, mt.module_name, is_main_tu, s.web,
                               s.fail_helpers_ir, s.main_builder_str,
                               s.foreign_declares, s.fn_declares, s.main_types, mt)
    path := module_ll_path(s.build_dir, mt.module_name)
    werr := os.write_entire_file(path, transmute([]u8)content)
    bt.write_err = werr != nil
}

// Emit LLVM IR for the checked program. Every visible function gets
// emitted; the linker drops unreachable code. Returns the list of per-
// module .ll files produced (one per home_package in g.module_order),
// plus a success flag.
generate_program :: proc(output_path: string, checked: ^Checked_Program, web: bool = false, shared: bool = false, profile: string = "", profile_memory: string = "", x86 := false, debug := false) -> ([]string, bool) {
    g := Codegen{}
    g.checked = checked
    g.web = web
    g.shared = shared
    g.profile = profile
    g.profile_memory = profile_memory != ""
    g.mem_build = profile_memory
    g.mem_sites = make(map[string]string)


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
            g.arena_alloc_has_debug = len(alloc_cf.params) > 2
        }
    }

    // @main lives in its own builder so the final-assembly step can place it
    // after all per-module function definitions. Non-main user functions now
    // route into per-module buffers in g.module_outs (set up lazily by
    // switch_to_module on first reference).
    main_builder: strings.Builder
    strings.builder_init(&main_builder)
    g.refs, g.defs = make(map[string]bool), make(map[string]bool)
    g.declares = make(map[string]string)
    g.types_used = make([dynamic]bool)

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

    // The x86 backend's layouts of the types, for what isn't a worker's (each
    // worker lays out the types it meets itself).
    x86_types: ^X86_Program
    if x86 { x86_types = x86_program() }

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
        task.use_x86, task.debug = x86, debug
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
    // worker's IR buffer; the per-task globals / intrinsics are kept
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

    // The x86 backend: @main and the runtime's helpers go into the main
    // package's object — its worker's, or one of its own.
    x86_main: ^X86_Module
    if x86 {
        for t in tasks { if t.module_name == checked.main_package { x86_main = t.x86 } }
        if x86_main == nil { x86_main = x86_begin(x86_types, checked if debug else nil, checked.main_package) }
        g.x86 = x86_main
    }

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
    main_params := make([]Ir_Arg, 2)
    main_params[0], main_params[1] = {ty = IR_I32, v = ir_local(".argc")}, {ty = IR_PTR, v = ir_local(".argv")}
    main_head := Ir_Head{name = "__mara_main" if g.web else "main", ret = IR_I64, params = main_params}
    // A crash the program doesn't report itself (a stack overflow, a bad
    // memory access) reported as an assert is (runtime/mara_crash.c).
    if !g.web { ir_call(&g, {}, IR_VOID, ir_global("__mara_crash_install")) }

    emit_main_prologue(&g, checked)
    if g.profile != "" { ir_call(&g, {}, IR_VOID, ir_global("__mara_prof_start"), {IR_PTR, get_string_literal(&g, g.profile), {}}) }
    if g.profile_memory { ir_call(&g, {}, IR_VOID, ir_global("__mara_mem_start"), {IR_PTR, get_string_literal(&g, g.mem_build), {}}) }

    main_cf, main_ok := checked.functions["main"]
    if !main_ok {
        // The package has a `main` (else this is a shared build and @main is
        // skipped), so the checker failed to extract it. Emitting the prologue
        // alone leaves @main without a body or a `ret`, which clang rejects
        // far from the cause.
        codegen_fatal(&g, {}, "`main` was declared but never extracted as a function")
    }
    // Main's body, from the graph.
    llvm_main(&g, main_cf, main_head)

    // Web wrapper: `i32 @main(i32, ptr)` calling our i64 mara main and
    // truncating the return code so emscripten's runtime sees a regular int.
    if g.web {
        strings.write_string(&g.out, "\ndefine i32 @main(i32 %.argc, ptr %.argv) {\n")
        strings.write_string(&g.out, "  %r = call i64 @__mara_main(i32 %.argc, ptr %.argv)\n")
        strings.write_string(&g.out, "  %r32 = trunc i64 %r to i32\n")
        strings.write_string(&g.out, "  ret i32 %r32\n}\n")
    }

    main_builder = g.out

    }  // end `if !g.shared` (Phase 2 — @main / web wrapper)

    // What @main names: the main TU's imports take them in. (The runtime's
    // helpers, next, name only what every TU declares.)
    main_refs, main_defs := g.refs, g.defs
    g.refs, g.defs = make(map[string]bool), make(map[string]bool)

    // Build the runtime fail-block helpers FIRST so any templates they
    // register (via get_string_literal) land in g.globals before the
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

    // The x86 backend: each module's object — its functions in it already,
    // made as they were — given its globals (its strings, its constants; in
    // the main one the program's) and written, one after another. (What only
    // a .ll needs — its imports' declares, the types it names — isn't made.)
    if x86 {
        build_dir := derive_build_dir(output_path)
        if !ensure_dir(build_dir) {
            fmt.printf("Error: could not create build dir '%s'\n", build_dir)
            return nil, false
        }
        g.module_ll_paths = make([dynamic]string)
        if debug { x86_raddbg(x86_main, debug_views(x86_main, g.module_tasks)) }
        named: map[string]bool
        for mt in g.module_tasks {
            named[mt.module_name] = true
            m := x86_main if mt.module_name == checked.main_package else mt.x86
            path := x86_write_module(&g, m, build_dir, mt.module_name, mt) or_else ""
            if path == "" { return nil, false }
            append(&g.module_ll_paths, path)
        }
        for module_name in g.module_order {
            if module_name in named { continue }
            m := x86_main if module_name == checked.main_package else x86_begin(x86_types)
            path := x86_write_module(&g, m, build_dir, module_name, nil) or_else ""
            if path == "" { return nil, false }
            append(&g.module_ll_paths, path)
        }
        return g.module_ll_paths[:], true
    }

    // Phase 1.6: Compute per-module imports now that both function bodies
    // and @main are emitted. The main TU's import set folds in @main's
    // references (arena init, args setup, dispatch into user `main`).
    compute_module_imports(&g, checked.main_package, main_refs, main_defs)

    // Pre-build foreign declares as a name→declare map. Each per-module .ll
    // emits only the foreign symbols its function bodies actually reference,
    // mirroring the cross-module import filtering below.
    foreign_declares := build_foreign_declares(&g, checked)
    defer delete(foreign_declares)

    // Every module's functions' `declare` lines (codegen_note), by name: a
    // module's .ll declares the ones it imports.
    fn_declares := make(map[string]string)
    defer delete(fn_declares)
    for mt in g.module_tasks {
        for name, decl in mt.declares { fn_declares[name] = decl }
    }

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
        main_types          = g.types_used[:],
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
                                    foreign_declares, fn_declares, g.types_used[:], nil)
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

// raddbg's type views every module's types want (codeview.odin), each once,
// in order: what the main module's object holds for the program.
@(private="file")
debug_views :: proc(main: ^X86_Module, tasks: []^Module_Task) -> []string {
    all: map[string]bool
    defer delete(all)
    for v in main.cv.views { all[v] = true }
    for t in tasks {
        if t.x86 != nil && t.x86.cv != nil { for v in t.x86.cv.views { all[v] = true } }
    }
    out := make([]string, len(all))
    i := 0
    for v in all {
        out[i] = v
        i += 1
    }
    slice.sort(out)
    return out
}

// One module's object (x86.odin): its functions in it already; its globals
// — its strings, its constants, the main one's the program's — put in now,
// and it's written, on the heap, let go of once it is.
@(private="file")
x86_write_module :: proc(g: ^Codegen, m: ^X86_Module, build_dir, module_name: string, mt: ^Module_Task) -> (string, bool) {
    path := module_ll_path(build_dir, module_name, ".o")
    main := module_name == g.checked.main_package
    if mt != nil { for gl in mt.globals { x86_global(m, gl) } }
    if main {
        for gl in g.globals { x86_global(m, gl) }
        for gl in program_globals(g.checked, true) { x86_global(m, gl) }
    }
    for gl in module_const_globals(g, module_name, main) { x86_global(m, gl) }
    out := make([dynamic]u8, runtime.heap_allocator())
    defer delete(out)
    x86_finish(m, &out)
    if os.write_entire_file(path, out[:]) != nil {
        fmt.printfln("Error: could not write '%s'", path)
        return path, false
    }
    return path, true
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
                        main_types: []bool,
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
    consts := module_const_globals(g, module_name, is_main_tu)

    // Struct/union type definitions — TU-local LLVM type namespace means we
    // only need the types this module uses (and those their bodies hold):
    // its functions' — the main TU's, @main's and the runtime helpers' too —
    // and its constant tables'. The `@__mara_program_storage` global below
    // names the program's context in every TU (the main TU defines it, the
    // others declare it), so its type is always one. Defined in the order the
    // program's are (g.named_types).
    {
        used: map[Ir_Type]bool
        defer delete(used)
        mark :: proc(t: Ir_Type, used: ^map[Ir_Type]bool) {
            info := ir_type_info(t)
            #partial switch info.kind {
            case .Named:
                if t in used { return }
                used[t] = true
                mark(info.elem, used)
            case .Array, .Vector, .Ptr:
                if info.elem != IR_NONE { mark(info.elem, used) }
            case .Struct:
                for f in info.fields { mark(f, used) }
            }
        }
        mark_all :: proc(types: []bool, used: ^map[Ir_Type]bool) {
            for u, t in types { if u { mark(Ir_Type(t), used) } }
        }
        mark_const :: proc(c: Ir_Const, used: ^map[Ir_Type]bool) {
            mark(c.ty, used)
            mark(c.src, used)
            for part in c.parts { mark_const(part, used) }
        }
        if module_task != nil { mark_all(module_task.types_used[:], &used) }
        if is_main_tu { mark_all(main_types, &used) }
        for gl in consts {
            mark(gl.ty, &used)
            mark_const(gl.init, &used)
        }
        mark(program_ir_name(checked), &used)
        wrote_any := false
        for t in g.named_types {
            if t not_in used { continue }
            ir_print_type_def(&b, t)
            wrote_any = true
        }
        if wrote_any { strings.write_byte(&b, '\n') }
    }

    // String literal globals — private linkage means no link collision
    // between TUs. Per-module workers contribute their own @.<module>_str.N
    // entries; the main TU also folds in main_g.globals (used by
    // @main emission and the fail-helper format strings).
    wrote_any_string := false
    if module_task != nil {
        for gl in module_task.globals {
            ir_print_global(&b, gl)
            wrote_any_string = true
        }
    }
    if is_main_tu {
        for gl in g.globals {
            ir_print_global(&b, gl)
            wrote_any_string = true
        }
    }
    if wrote_any_string { strings.write_byte(&b, '\n') }

    // Context globals: main TU defines, others declare external.
    strings.write_string(&b, "; Context system\n")
    for gl in program_globals(checked, is_main_tu) { ir_print_global(&b, gl) }
    strings.write_byte(&b, '\n')
    if len(consts) > 0 {
        strings.write_string(&b, "; Constant tables\n")
        for gl in consts { ir_print_global(&b, gl) }
        strings.write_byte(&b, '\n')
    }

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
        strings.write_string(&b, "declare void @__mara_crash_install()\n")
    }
    if g.profile != "" {
        // The profiler, runtime/mara_prof.c: linked into a -profile build.
        strings.write_string(&b, "declare void @__mara_prof_start(ptr)\n")
        strings.write_string(&b, "declare void @__mara_prof_enter(ptr)\n")
        strings.write_string(&b, "declare void @__mara_prof_exit(ptr)\n")
    }
    if g.profile_memory {
        // The memory profiler, runtime/mara_mem.c: linked into a -profile
        // memory build.
        strings.write_string(&b, "declare void @__mara_mem_start(ptr)\n")
        strings.write_string(&b, "declare void @__mara_mem_new(ptr, ptr)\n")
        strings.write_string(&b, "declare void @__mara_mem_into(ptr, ptr)\n")
        strings.write_string(&b, "declare void @__mara_mem_len(ptr)\n")
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
        for f in RUNTIME_FAILS {
            fmt.sbprintf(&b, "declare void @%s(", f.name)
            for p, i in f.params { fmt.sbprintf(&b, "%s%s %%%s", ", " if i > 0 else "", ir_type_text(p.ty), p.name) }
            strings.write_string(&b, ")\n")
        }
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
module_ll_path :: proc(build_dir, module_name: string, ext := ".ll") -> string {
    safe, _ := strings.replace_all(module_name, ".", "_")
    return strings.concatenate({build_dir, "/", safe, ext})
}

// The program's globals: its context's pointer and the context itself — the
// main TU's own, every other's to link to.
@(private="file")
program_globals :: proc(checked: ^Checked_Program, own: bool) -> []Ir_Global {
    gls := make([]Ir_Global, 2)
    linkage: Ir_Linkage = .Default if own else .External
    gls[0] = {name = "__mara_program", linkage = linkage, ty = IR_PTR, init = {v = IR_NULL}}
    gls[1] = {name = "__mara_program_storage", linkage = linkage, ty = program_ir_name(checked), init = {v = IR_ZERO}}
    return gls
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
        ctx_alloca := ir_global("__mara_program_storage")
        ir_store(g, IR_PTR, ctx_alloca, ir_global("__mara_program"))

        // Arena init (if scope allocator is active).
        if g.context_enabled {
            arena_ptr := fresh_tmp(g)
            emit_field_gep_into(g, arena_ptr, program_ir_name(checked), ctx_alloca, 0)
            new_ir := mara_fn(g, g.arena_new_name)
            alloc_size := 268435456  // default 256 MB
            if n, sized := checked.table.scope_allocator_size.?; sized { alloc_size = int(n) }
            ir_call(g, {}, IR_VOID, new_ir, {IR_I64, ir_int(alloc_size), {}}, {IR_PTR, arena_ptr, {}})
        }

        // Populate context.args — partial array {len, cap, ptr, [64 x slice]}
        // embedded as a field of Context.
        args_field_idx := 1 if g.context_enabled else 0
        ARGS_CAP :: 64
        pa_ir := partial_array_ir_type(SLICE_IR_TYPE, 64)

        // GEP to the partial-array field within Context
        args_ptr := fresh_tmp(g)
        emit_field_gep_into(g, args_ptr, program_ir_name(checked), ctx_alloca, args_field_idx)

        // More arguments than the args array holds is an error, not a silent
        // truncation — a program handed a long file list must not quietly
        // miss the tail. (Raise ARGS_CAP if 64 ever proves too few.)
        argc_over := fresh_tmp(g)
        argc := ir_local(".argc")
        ir_icmp(g, argc_over, .Sgt, IR_I32, argc, ir_int(ARGS_CAP))
        args_err_lbl := ir_label(g, "args_too_many_", g.label_counter)
        args_ok_lbl := ir_label(g, "args_ok_", g.label_counter)
        emit_cond_br(g, argc_over, args_err_lbl, args_ok_lbl)
        emit_label(g, args_err_lbl)
        emit_fail(g, fmt.tprintf("runtime error: too many command-line arguments: %%d (the limit is %d)\n", ARGS_CAP), {IR_I32, argc, {}})
        emit_label(g, args_ok_lbl)
        argc_min := argc // every argument fits from here on

        // Its header: len argc (i32, as the loop counter below; the header's
        // i64), cap 64, ptr its elements (field 3).
        len_store_val := fresh_tmp(g)
        ir_cast(g, len_store_val, .Sext, IR_I32, argc_min, SLICE_LEN_IR)
        emit_header_set(g, args_ptr, SLICE.len, len_store_val)
        emit_header_set(g, args_ptr, SLICE.cap, ir_int(ARGS_CAP))
        elements_ptr := fresh_tmp(g)
        emit_field_gep_into(g, elements_ptr, pa_ir, args_ptr, 3)
        emit_header_set(g, args_ptr, SLICE.ptr, elements_ptr)

        // Loop: for i = 0; i < len; i++ — fill elements[i] = { strlen, strlen, argv[i] }
        // Counter is i32 to match argc and the slice header — no widen/trunc.
        loop_i := fresh_tmp(g)
        emit_alloca(g, loop_i, IR_I32)
        ir_store(g, IR_I32, ir_int(0), loop_i)
        loop_lbl := ir_label(g, "args_loop_", g.label_counter)
        body_lbl := ir_label(g, "args_body_", g.label_counter)
        done_lbl := ir_label(g, "args_done_", g.label_counter)
        g.label_counter += 1
        emit_br(g, loop_lbl)

        emit_label(g, loop_lbl)
        cur_i := fresh_tmp(g)
        ir_load(g, cur_i, IR_I32, loop_i)
        cmp := fresh_tmp(g)
        ir_icmp(g, cmp, .Slt, IR_I32, cur_i, argc_min)
        emit_cond_br(g, cmp, body_lbl, done_lbl)

        emit_label(g, body_lbl)
        argv_i_ptr := fresh_tmp(g)
        ir_gep(g, argv_i_ptr, IR_PTR, ir_local(".argv"), {IR_I32, cur_i, {}})
        argv_i := fresh_tmp(g)
        ir_load(g, argv_i, IR_PTR, argv_i_ptr)
        // strlen returns size_t (i64 native, i32 on web), widened to the
        // header's i64 for the len/cap store.
        str_len := fresh_tmp(g)
        if g.web {
            str_len_32 := fresh_tmp(g)
            ir_call(g, str_len_32, IR_I32, ir_global("strlen"), {IR_PTR, argv_i, {}})
            ir_cast(g, str_len, .Zext, IR_I32, str_len_32, SLICE_LEN_IR)
        } else {
            ir_call(g, str_len, IR_I64, ir_global("strlen"), {IR_PTR, argv_i, {}})
        }
        // elements[i] is a slice — write len, cap, ptr. cap counts argv's
        // terminating 0 (as a string literal's does), so cstring(arg) finds it
        // at [len] — passing an argument to a file open or any C call works.
        elem_ptr := fresh_tmp(g)
        ir_gep(g, elem_ptr, ir_array_type(64, SLICE_IR_TYPE), elements_ptr, {IR_I32, ir_int(0), {}}, {IR_I32, cur_i, {}})
        emit_header_set(g, elem_ptr, SLICE.len, str_len)
        str_cap := fresh_tmp(g)
        ir_bin(g, str_cap, .Add, SLICE_LEN_IR, str_len, ir_int(1))
        emit_header_set(g, elem_ptr, SLICE.cap, str_cap)
        emit_header_set(g, elem_ptr, SLICE.ptr, argv_i)
        // i++
        next_i := fresh_tmp(g)
        ir_bin(g, next_i, .Add, IR_I32, cur_i, ir_int(1))
        ir_store(g, IR_I32, next_i, loop_i)
        emit_br(g, loop_lbl)

        emit_label(g, done_lbl)
    }
}
