package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// modules.odin — a tool's check in two stages: some modules first, then the
// rest, on one checker.
//
// The first stage's modules are closed under `use`: none uses a module of
// the second's. So what the first stage finds doesn't depend on the second —
// it can be kept while the second's modules change, and they alone checked
// again. (A body doesn't depend on another body either: tc_bodies.) The
// program is what both stages found, finished as one check's is.

// What's sized by the tokens or the tree, grown to hold what was read since
// the check began: the modules' new files, each new module's body's node.
tc_check_grow :: proc(k: ^TC, modules: map[string][]Tree_Id) {
    k.modules = modules
    tc_module_nodes(k)
    grown :: proc(old: []$T, n: int) -> []T {
        if len(old) >= n { return old }
        new := make([]T, n)
        copy(new, old)
        return new
    }
    k.bound = grown(k.bound, len(build_tokens))
    k.lists = grown(k.lists, len(build_tokens))
    nodes := len(k.t.tag)
    k.names.refs = grown(k.names.refs, nodes)
    a := k.annot
    a.types[0], a.refs[0] = grown(a.types[0], nodes), grown(a.refs[0], nodes)
    a.instances[0].hi = Tree_Id(nodes - 1)
}

// The files of the modules reached from `roots` that aren't read yet, lexed:
// added to `files`, the modules read so far. (compute_use_closure, going on.)
closure_more :: proc(all_files: map[string][dynamic]^Source_File, files: ^map[string][dynamic]^Source_File, roots: []string) {
    worklist := make([dynamic]string, context.temp_allocator)
    append(&worklist, ..roots)
    for len(worklist) > 0 {
        module := pop(&worklist)
        if module in files { continue }
        fs, has := all_files[module]
        if !has { continue }
        files[module] = fs
        for f in fs {
            lex_file(f)
            for path in f.imports { if path in all_files && path not_in files { append(&worklist, path) } }
        }
    }
}

// The modules among `files` that `keep` takes (by a file of theirs) and whose
// uses are all taken too: a set closed under `use`.
modules_closed :: proc(files: map[string][dynamic]^Source_File, keep: proc(f: ^Source_File) -> bool) -> []string {
    in_ := make(map[string]bool, context.temp_allocator)
    for name, fs in files { if len(fs) > 0 && keep(fs[0]) { in_[name] = true } }
    for changed := true; changed; {
        changed = false
        for name in in_ {
            if !in_[name] { continue }
            uses: for f in files[name] {
                for path in f.imports {
                    if path in files && !in_[path] { in_[name], changed = false, true; break uses }
                }
            }
        }
    }
    out := make([dynamic]string)
    for name, kept in in_ { if kept { append(&out, name) } }
    slice.sort(out[:])
    return out[:]
}

// A module with its uses, checked into `k`: the main one as the main one.
@(private="file")
staged_module :: proc(k: ^TC, name: string) {
    if name in k.checked_modules || name not_in k.modules { return }
    if name == k.main_package { tc_check_main(k) } else { tc_check_module(k, name, {}) }
}

// (A module with no main is a library: no error of its.)
@(private="file")
staged_entry :: proc(k: ^TC) {
    has_main, _ := module_entries(k.main_package)
    k.shared = !has_main
}

// A check between its stages: the checker with the kept modules checked,
// bodies and all; the modules read so far; their parse errors.
Staged :: struct {
    k:            ^TC,
    files:        map[string][dynamic]^Source_File,
    parse_errors: map[string]int,
}

// A query's check, a server's, in two stages: `kept`, modules closed under
// `use` (each one's uses among them), then the rest of what args.pkg_name
// and args.also reach — check_staged_kept, then check_staged_rest, which
// gives what check_module would of them all. Between the two the kept
// modules are checked and nothing of the rest is read: what serve keeps.
check_staged_kept :: proc(args: CLI_Args, all_files: map[string][dynamic]^Source_File, kept: []string, perf: ^Performance_Timer) -> (st: Staged) {
    perf_timer_mark(perf, "lex")
    // (Room for every file found's tokens and nodes: neither is copied as the
    // second stage adds its own, so what the first made of them stays put.)
    bytes := 0
    for _, fs in all_files { for f in fs { bytes += len(f.source) } }
    lex_reserve(bytes / 2)
    tree_reserve(&build_tree, bytes / 2)
    for name in kept {
        fs, has := all_files[name]
        if !has { continue }
        st.files[name] = fs
        for f in fs { lex_file(f) }
    }
    perf_timer_mark(perf, "parse")
    st.parse_errors = parse_target_files()
    perf_timer_mark(perf, "type check")
    k := tc_check_begin(&build_tree, tc_modules(), args.pkg_name,
                        shared = false, web = args.web, target_os = build_target(), profile_memory = args.profile_memory,
                        analysis_only = true, no_assert = args.no_assert, perf = perf,
                        lower = true, no_crt = false, partial = true, parse_errors = false)
    k.beside = args.also
    if args.pkg_name in st.files { staged_entry(k) }
    names := slice.clone(kept, context.temp_allocator)
    slice.sort(names)
    for name in names { staged_module(k, name) }
    tc_bodies(k)
    perf_timer_mark(perf, "lower")
    tc_check_kept_lowered(k)
    tc_blocks_end(k)   // (its blocks' scratch: the next stage's its own)
    st.k = k
    return
}

check_staged_rest :: proc(args: CLI_Args, all_files: map[string][dynamic]^Source_File, st: ^Staged, perf: ^Performance_Timer) -> (checked: ^Checked_Program, failure: string) {
    k := st.k
    k.run.perf = perf
    k.beside = args.also
    tc_blocks_begin(k)
    perf_timer_mark(perf, "lex")
    read := len(build_files)
    roots := make([dynamic]string, context.temp_allocator)
    append(&roots, args.pkg_name)
    append(&roots, ..args.also)
    closure_more(all_files, &st.files, roots[:])
    perf_timer_mark(perf, "parse")
    queued := diagnostics_count()
    for name, n in parse_target_files(read) { st.parse_errors[name] += n }
    // (Its parse errors queued before the first stage's check's, as one check of it all has them.)
    diagnostics_move_before(k.run.diagnosed, queued)
    k.run.diagnosed += diagnostics_count() - queued
    // (Its parse errors, as check_module takes them: each at a token, or the check stops.)
    parse_total := 0
    for _, n in st.parse_errors { parse_total += n }
    if parse_total > 0 && diagnostics_parse_placed() != parse_total { return nil, parse_errors_said(st.parse_errors) }
    perf_timer_mark(perf, "type check")
    tc_check_grow(k, tc_modules())
    k.run.parse_errors = parse_total > 0
    if args.pkg_name not_in k.modules {
        tc_error(k, {}, "no parsed program for main module '%s'", args.pkg_name)
        k.checked.errors = k.c.errors
        return k.checked, strings.concatenate({take_diagnostics(), fmt.aprintf(BUILD_TYPE_ERRORS_ABORT, k.checked.errors)})
    }
    if args.pkg_name not_in k.checked_modules { staged_entry(k) }
    staged_module(k, args.pkg_name)
    for name in args.also { staged_module(k, name) }
    k.pkg = args.pkg_name
    tc_bodies(k)
    checked = tc_check_finish(k)
    if checked.errors > 0 || parse_total > 0 {
        return checked, strings.concatenate({take_diagnostics(), fmt.aprintf(BUILD_TYPE_ERRORS_ABORT, checked.errors)})
    }
    return checked, ""
}
