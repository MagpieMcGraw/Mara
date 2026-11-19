package mara

import "core:bufio"
import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"
import "core:time"
import "base:runtime"

// ---------------------------------------------------------------------------
// `mara serve [module]`: ask's queries, one a line from stdin, each answered
// as `mara ask <line>` would answer it, then ASK_DONE — against the module as
// it is on disk, checked again when a .mara file changes. A window starts it
// once and talks to it through pipes; it ends when its input does.
// A line can start `-in "<folder>" <module>`: serve goes to that folder and
// checks that module, then answers the rest of the line. So one serve can
// answer for any module, which is how a window follows an editor around.
// ---------------------------------------------------------------------------

// Each answer ends in one of these lines: a client reading them knows where
// one ends, and whether `mara ask` would have failed with it (exit 1) — a
// query it couldn't read, a name not found, a module that doesn't check.
ASK_DONE   :: "-- end of answer --"
ASK_FAILED :: "-- end of answer: failed --"

// One check of the module, in an arena of its own: freed whole when a file
// changes and the next check replaces it.
Serve_Check :: struct {
    arena:   virtual.Arena,
    session: Ask_Session,   // (its program, when there is one, even one with errors)
    failure: string,   // what every answer is instead, when it didn't check
    stamp:   string,   // the sources it read (serve_stamp)
    diagnostics: [dynamic]Diagnostic,   // its errors and warnings, each at its place
    kept:    ^Serve_Kept,   // what serve keeps of it for the next (nil: nothing — a check made once)
}

// What serve keeps of a check for the next, on the heap. Of the last check:
// the sources it read, each module's uses, each file's module — what a
// change is told by. And a check as it was between its stages (modules.odin),
// the modules a change didn't touch checked and nothing else read: the
// arena's bytes, and what of the build's state isn't in it. A change that
// touches none of those modules puts all that back and checks only the rest.
Serve_Kept :: struct {
    stamp:       string,
    pkg:         string,
    graph:       map[string][]string,
    file_module: map[string]string,   // (by its path's key)
    on:          bool,
    modules:     []string,
    bytes:       []byte,
    st:          Staged,
    all_files:   map[string][dynamic]^Source_File,
    files:       [dynamic]^Source_File,
    literals:    map[Token_Id]string,
    diagnostics: [dynamic]Diagnostic,
    tokens:      int,
    tree:        Tree_Mark,
    types:       Types_Held,
    atoms:       int,
}

// The room a kept check's arena has: one block, never moved, so its bytes
// can be put back where they were.
SERVE_ARENA_RESERVE :: 64 << 30

// One folder's set of modules, held: where it is, the module first asked
// about there and those added beside it since (args.pkg_name, args.also),
// its check, and — while another folder's set is the one being answered
// from — the build's globals its check filled. A folder has its own
// build.mara and its own modules of a name, so each has a set of its own;
// serve keeps them side by side, and going back to one checks nothing again
// unless a file changed. The strings in here, and the folders build.mara
// names, live in the arena, which each reading of build.mara replaces.
Serve_Here :: struct {
    arena: virtual.Arena,
    dir:   string,
    args:  CLI_Args,
    check: Serve_Check,
    build: Serve_Build,
}

// The build's globals a check fills — its tokens, files and tree, the types
// it made canonical — taken out so another folder's can be put in.
Serve_Build :: struct {
    tokens:   [dynamic]Token,
    files:    [dynamic]^Source_File,
    literals: map[Token_Id]string,
    tree:     Tree,
    types:    Types_Held,
}

serve_build_take :: proc() -> (b: Serve_Build) {
    b = {build_tokens, build_files, build_literals, build_tree, types_take()}
    serve_build_put({})
    return
}

serve_build_put :: proc(b: Serve_Build) {
    build_tokens, build_files, build_literals, build_tree = b.tokens, b.files, b.literals, b.tree
    types_put(b.types)
    ir_types_forget()   // (made from a check's types: another check's may sit where they did)
}

serve :: proc(args: CLI_Args) {
    compiler := compiler_file()
    sets := make([dynamic]^Serve_Here)
    here := new_clone(Serve_Here{args = args})
    here.dir, _ = os.get_working_directory(context.allocator)
    append(&sets, here)
    serve_check(&here.check, args, serve_stamp(args.compiler_dir, args.search_dirs), keeping = true)
    r: bufio.Reader
    bufio.reader_init(&r, os.to_stream(os.stdin))
    defer bufio.reader_destroy(&r)
    for {
        line, rerr := bufio.reader_read_string(&r, '\n', context.temp_allocator)
        if rerr != nil && line == "" { break }
        // (mara.exe rebuilt: ended, the query unanswered — the window starts
        // the new one and asks it again. Nothing said: serve's stderr reaches
        // the window with its answers, a word of it an answer begun.)
        if compiler_rebuilt(compiler) { os.exit(COMPILER_REBUILT_EXIT) }
        // (A blank line is a query too: `mara ask` alone, the module map.)
        words := ask_words(line)
        dir, module := "", ""
        if len(words) >= 3 && words[0] == "-in" {
            dir, module = words[1], words[2]
            words = words[3:]
        }
        answer, ok := serve_ready(&sets, &here, args, dir, module), false
        if answer == "" { answer, ok = serve_answer(&here.check, words, &here.args, module) }
        fmt.print(answer)
        fmt.println(ASK_DONE if ok else ASK_FAILED)
        free_all(context.temp_allocator)
        if rerr != nil { break }
    }
}

// Gets a set ready for a query. `dir` and `module` are the query's `-in`;
// both are empty when it has none. Another folder: its set, held or new —
// `here` from then on. A module the set doesn't have: added beside its own.
// The set is checked again when it grew or a file has changed. Returns what
// to answer instead when serve can't get there, "" when it's ready.
serve_ready :: proc(sets: ^[dynamic]^Serve_Here, here: ^^Serve_Here, base: CLI_Args, dir, module: string) -> string {
    heap := runtime.heap_allocator()
    fresh := false
    if dir != "" && path_key(dir) != path_key(here^.dir) {
        if os.change_directory(dir) != nil { return fmt.tprintf("mara serve: can't go to the folder %s\n", dir) }
        here^.build = serve_build_take()
        next: ^Serve_Here
        for s in sets { if s.dir != "" && path_key(s.dir) == path_key(dir) { next = s } }
        if next == nil {
            next = new(Serve_Here, heap)
            next.args = base
            next.args.pkg_name, next.args.search_dirs, next.args.also = strings.clone(module, heap), nil, nil
            next.dir = strings.clone(dir, heap)
            append(sets, next)
            fresh = true
        }
        serve_build_put(next.build)
        next.build = {}
        here^ = next
    }
    h := here^
    check := &h.check
    grown := false
    if module != "" && module != h.args.pkg_name && !slice.contains(h.args.also, module) && module not_in check.session.files {
        also := make([dynamic]string, heap)
        append(&also, ..h.args.also)
        append(&also, strings.clone(module, heap))
        h.args.also = also[:]
        grown = true
    }
    stamp := serve_stamp(h.args.compiler_dir, h.args.search_dirs)
    if !fresh && !grown && stamp == check.stamp { return "" }
    if dir != "" {
        // (build.mara read again: a folder new here, or it may have changed.)
        virtual.arena_destroy(&h.arena)
        if err := virtual.arena_init_growing(&h.arena); err != nil {
            fmt.panicf("mara serve: no arena for a module (%v)", err)
        }
        context.allocator = virtual.arena_allocator(&h.arena)
        h.args.search_dirs = nil
        if problem := build_dirs_in(&h.args, h.dir); problem != "" {
            // (The next query tries again. The check kept was of what's gone.)
            check.stamp = ""
            return strings.concatenate({problem, "\n"}, context.temp_allocator)
        }
        stamp = serve_stamp(h.args.compiler_dir, h.args.search_dirs)
    }
    serve_check(check, h.args, stamp, keeping = true)
    // (A module asked for that isn't here: said, and not kept in the set.)
    if grown && check.session.all_files != nil && module not_in check.session.all_files {
        h.args.also = h.args.also[:len(h.args.also) - 1]
        return module_missing(check.session.all_files, module)
    }
    return ""
}

// The compiler a server runs — serve, lsp — as its file was when it
// started: its path, when it was written. Another file there since is a
// rebuild (the running one renamed aside, as Windows allows), and a server
// answering with the old code answers wrong — new syntax in the stdlib its
// errors. So it ends, nonzero, and its client starts the new one: the window
// on its next query, Sublime's LSP at once (a crash it restarts).
Compiler_File :: struct {
    path:    string,
    written: i64,
}

compiler_file :: proc() -> Compiler_File {
    path := get_compiler_exe()
    written, _ := file_written(path)
    return {path, written}
}

// Whether another compiler is at the path now — one written 2 s ago or more,
// so its build is done with it (one mid-link isn't; none there yet isn't).
compiler_rebuilt :: proc(c: Compiler_File) -> bool {
    written, there := file_written(c.path)
    if !there || written == c.written { return false }
    return time.time_to_unix_nano(time.now()) - written >= 2 * i64(time.Second)
}

COMPILER_REBUILT_EXIT :: 3

// A file's key: its whole path's, however it's written from here.
@(private="file")
serve_file_key :: proc(path: string) -> string {
    whole := path
    if !filepath.is_abs(whole) {
        cwd, _ := os.get_working_directory(context.temp_allocator)
        whole, _ = filepath.join({cwd, whole}, context.temp_allocator)
    }
    return path_key(whole)
}

// A stamp's files: each one's line, by its path's key.
@(private="file")
serve_stamp_files :: proc(stamp: string) -> map[string]string {
    out := make(map[string]string, context.temp_allocator)
    for line in strings.split_lines(stamp, context.temp_allocator) {
        // (`<path> <size> <written>`: the path may have spaces, the two numbers none.)
        cut := strings.last_index_byte(line, ' ')
        if cut > 0 { cut = strings.last_index_byte(line[:cut], ' ') }
        if cut > 0 { out[serve_file_key(line[:cut])] = line }
    }
    return out
}

// The modules a change of sources touches, from the last check's stamp to
// this one: each file changed, come or gone — its module then, its module
// now. `known` false: there's no telling (no check before, or of another
// module).
@(private="file")
serve_changed :: proc(kept: ^Serve_Kept, stamp: string, pkg: string) -> (changed: []string, known: bool) {
    if kept.stamp == "" || kept.pkg != pkg { return nil, false }
    out := make([dynamic]string, context.temp_allocator)
    was, now := serve_stamp_files(kept.stamp), serve_stamp_files(stamp)
    touch :: proc(kept: ^Serve_Kept, out: ^[dynamic]string, key, line: string, there: bool) {
        if m := kept.file_module[key] or_else ""; m != "" && !slice.contains(out[:], m) { append(out, m) }
        if !there { return }
        cut := strings.last_index_byte(line, ' ')
        cut = strings.last_index_byte(line[:cut], ' ')
        data, err := os.read_entire_file_from_path(line[:cut], context.temp_allocator)
        if err != nil { return }
        if m := extract_package_name(string(data)); m != "" && !slice.contains(out[:], m) { append(out, m) }
    }
    for key, line in now { if (was[key] or_else "") != line { touch(kept, &out, key, line, true) } }
    for key, line in was { if key not_in now { touch(kept, &out, key, line, false) } }
    return out[:], true
}

// The modules read that use one of `changed`, through any number of uses,
// and those themselves: what a change makes of the last check's graph.
@(private="file")
serve_redo :: proc(kept: ^Serve_Kept, changed: []string) -> map[string]bool {
    redo := make(map[string]bool, context.temp_allocator)
    for m in changed { redo[m] = true }
    for grew := true; grew; {
        grew = false
        for m, uses in kept.graph {
            if redo[m] { continue }
            for u in uses { if redo[u] { redo[m], grew = true, true; break } }
        }
    }
    return redo
}

// What the next check is told a change by: this check's sources, each module's
// uses, each file's module.
@(private="file")
serve_note :: proc(kept: ^Serve_Kept, stamp, pkg: string, all_files, files: map[string][dynamic]^Source_File) {
    heap := runtime.heap_allocator()
    context.allocator = heap
    delete(kept.stamp); delete(kept.pkg)
    for m, uses in kept.graph { delete(m); for u in uses { delete(u) }; delete(uses) }
    for key, m in kept.file_module { delete(key); delete(m) }
    clear(&kept.graph); clear(&kept.file_module)
    kept.stamp, kept.pkg = strings.clone(stamp), strings.clone(pkg)
    for m, fs in files {
        uses := make([dynamic]string)
        for f in fs { for path in f.imports { if path in files && !slice.contains(uses[:], path) { append(&uses, strings.clone(path)) } } }
        kept.graph[strings.clone(m)] = uses[:]
    }
    for m, fs in all_files {
        for f in fs { kept.file_module[strings.clone(serve_file_key(f.path))] = strings.clone(m) }
    }
}

// The check as it is between its stages, kept: the arena's bytes, and what
// of the build's state isn't in them.
@(private="file")
serve_keep :: proc(c: ^Serve_Check, st: Staged, all_files: map[string][dynamic]^Source_File, modules: []string) {
    kept := c.kept
    heap := runtime.heap_allocator()
    serve_unkeep(kept)
    block := c.arena.curr_block
    kept.bytes = make([]byte, block.used, heap)
    copy(kept.bytes, block.base[:block.used])
    kept.st, kept.all_files = st, all_files
    kept.files, kept.literals, kept.diagnostics = build_files, build_literals, diagnostics_held()
    kept.tokens, kept.tree = len(build_tokens), tree_mark(&build_tree)
    kept.types = types_copy()
    kept.atoms = len(st.k.checked.atoms)
    names := make([]string, len(modules), heap)
    for m, i in modules { names[i] = strings.clone(m, heap) }
    kept.modules = names
    kept.on = true
}

@(private="file")
serve_unkeep :: proc(kept: ^Serve_Kept) {
    if !kept.on { return }
    heap := runtime.heap_allocator()
    if mk := kept.st.k.middle_kept; mk != nil { middle_kept_free(mk) }
    delete(kept.bytes, heap)
    delete(kept.types.shapes); delete(kept.types.arrays)
    for m in kept.modules { delete(m, heap) }
    delete(kept.modules, heap)
    kept.on, kept.bytes, kept.modules, kept.types = false, nil, nil, {}
}

// The kept check put back: the arena as it was between the stages, the
// build's state cut back to it. What the last check made after is gone.
@(private="file")
serve_put_back :: proc(c: ^Serve_Check) {
    kept := c.kept
    if c.session.checked != nil { program_code_free(&c.session.checked.code, 1) }   // (its own memory: the kept stage's store stays)
    checked := kept.st.k.checked
    // (The atoms are the heap's, their table's place in the arena: the
    // table as it is now, cut to those the kept part had.)
    atoms, ids := checked.atoms, checked.atom_ids
    virtual.arena_static_reset_to(&c.arena, uint(len(kept.bytes)))
    copy(c.arena.curr_block.base[:len(kept.bytes)], kept.bytes)
    checked.atoms, checked.atom_ids = atoms, ids
    checked_atoms_cut(checked, kept.atoms)
    resize(&build_tokens, kept.tokens)
    tree_reset_to(&build_tree, kept.tree)
    build_files, build_literals = kept.files, kept.literals
    diagnostics_hold(kept.diagnostics)
    types_back_to(kept.types)
    ir_types_forget()
    c.session, c.failure, c.stamp, c.diagnostics = {}, "", "", {}
}

// The module as it is on disk now, checked — the last check's freed first,
// whole. (The build's globals, its tokens, tree and diagnostics, pointed
// into it: emptied, they fill with this check's.) `keeping`: a server's own
// check, of saved files — the modules a change doesn't touch are kept from
// one check to the next (Serve_Kept), and only the rest checked again.
serve_check :: proc(c: ^Serve_Check, args: CLI_Args, stamp: string, overlays: ^map[string]string = nil, keeping := false) {
    heap := runtime.heap_allocator()
    kept := c.kept
    changed: []string
    known, put_back := false, false
    if keeping && os.get_env("MARA_KEEP", context.temp_allocator) != "off" {
        if kept == nil { kept = new(Serve_Kept, heap); kept.graph.allocator, kept.file_module.allocator = heap, heap }
        changed, known = serve_changed(kept, stamp, args.pkg_name)
        put_back = known && kept.on
        if put_back { for m in changed { if slice.contains(kept.modules, m) { put_back = false } } }
    } else {
        kept = nil
    }
    if put_back {
        serve_put_back(c)
    } else {
        // (Its own memory — a kept stage's store apart: serve_unkeep's, while the arena that names it is there.)
        if c.session.checked != nil { program_code_free(&c.session.checked.code, 1 if kept != nil && kept.on else 0) }
        if kept != nil { serve_unkeep(kept) }
        virtual.arena_destroy(&c.arena)
        c^ = {}
        c.kept = kept
        delete(build_tokens)   // (the tokens and the tree are on the heap)
        tree_free(&build_tree)
        build_tokens, build_files, build_literals, build_tree = {}, {}, {}, {}
        reset_diagnostics()
        err := virtual.arena_init_static(&c.arena, SERVE_ARENA_RESERVE) if kept != nil else virtual.arena_init_growing(&c.arena)
        if err != nil { fmt.panicf("mara serve: no arena for a check (%v)", err) }
    }
    context.allocator = virtual.arena_allocator(&c.arena)
    c.stamp = strings.clone(stamp)
    diagnostics_keep(&c.diagnostics)
    defer diagnostics_keep_end()

    perf := Performance_Timer{quiet = true}
    perf_timer_begin(&perf, "discover")
    all_files, found_problem := discover_all_files(args.compiler_dir, ".", args.search_dirs)
    if found_problem != "" {
        c.failure = found_problem
        return
    }
    if overlays != nil { serve_overlay(all_files, overlays^) }
    if args.pkg_name not_in all_files {
        c.failure = module_missing(all_files, args.pkg_name)
        return
    }
    files: map[string][dynamic]^Source_File
    checked: ^Checked_Program
    failure: string
    switch {
    case put_back:
        // (The kept modules' files are the kept check's: read, lexed, parsed.)
        for m in kept.modules { if fs := kept.all_files[m] or_else nil; len(fs) > 0 { all_files[fs[0].module] = fs } }
        st := kept.st
        checked, failure = check_staged_rest(args, all_files, &st, &perf)
        files = st.files
    case known:
        // (What the change doesn't touch first, kept; then the rest.)
        redo := serve_redo(kept, changed)
        keep := make([dynamic]string, context.temp_allocator)
        // (Each by its files' own name for it: the check's, in its arena — the graph's are the heap's, and go.)
        for m in kept.graph { if fs := all_files[m] or_else nil; !redo[m] && len(fs) > 0 { append(&keep, fs[0].module) } }
        slice.sort(keep[:])
        st := check_staged_kept(args, all_files, keep[:], &perf)
        serve_keep(c, st, all_files, keep[:])
        checked, failure = check_staged_rest(args, all_files, &st, &perf)
        files = st.files
    case:
        files = compute_use_closure(all_files, args.pkg_name, &perf, args.also)
        if os.get_env("MARA_STAGED", context.temp_allocator) == "stdlib" {
            // (A test's: the same check in two stages — the compiler's own modules
            // first, then the project's. What was read to find them is forgotten.)
            keep := modules_closed(files, proc(f: ^Source_File) -> bool { return f.stdlib })
            delete(build_tokens)
            build_tokens, build_files, build_literals = {}, {}, {}
            for _, fs in files { for f in fs { f.lines, f.imports, f.first_token, f.end_token, f.lex_errors = {}, {}, 0, 0, 0 } }
            reset_diagnostics()
            st := check_staged_kept(args, all_files, keep, &perf)
            checked, failure = check_staged_rest(args, all_files, &st, &perf)
            files = st.files
        } else {
            checked, _, failure = check_module(args, files, &perf)
        }
    }
    if kept != nil { serve_note(kept, stamp, args.pkg_name, all_files, files) }
    c.session = Ask_Session{checked, all_files, files, args.compiler_dir, args.pkg_name}
    c.failure = failure
    diagnostics_keep_end()
    reset_diagnostics()   // (a check's warnings: about the code, not a query — answered by none)
}

// Files as an editor has them, saved or not (mara lsp), in place of what's on
// disk: `overlays`, each one's text by its path_key. Its module and its uses
// read again from it.
serve_overlay :: proc(all_files: map[string][dynamic]^Source_File, overlays: map[string]string) {
    cwd, _ := os.get_working_directory(context.temp_allocator)
    for _, files in all_files {
        for f in files {
            path := f.path
            if !filepath.is_abs(path) { path, _ = filepath.join({cwd, path}, context.temp_allocator) }
            text, open := overlays[path_key(path)]
            if !open { continue }
            f.source = strings.clone(text)
        }
    }
}

// A path as a key: one however it's spelled — separators one way, and on
// Windows, letters' case not minded.
path_key :: proc(path: string) -> string {
    cleaned, _ := filepath.clean(path, context.temp_allocator)
    key, _ := strings.replace_all(cleaned, "\\", "/", context.temp_allocator)
    when ODIN_OS == .Windows { key = strings.to_lower(key, context.temp_allocator) }
    return key
}

// A query's answer, and whether it is one — false where `mara ask` would
// fail: a mistake in the query (that is its answer), a name not found, the
// module not checking (what's wrong with it is).
serve_answer :: proc(c: ^Serve_Check, words: []string, args: ^CLI_Args = nil, module := "") -> (answer: string, ok: bool) {
    q, err := ask_parse_query(words)
    if q.help { return ASK_USAGE + "\n", true }
    if err != "" { return strings.concatenate({err, "\n"}, context.temp_allocator), false }
    // (Pointed at a file of a module the check didn't read: checked again,
    // that module beside its own from here on — `args`, the check's.)
    if args != nil && q.at != "" && c.session.files != nil {
        if m := point_module(c.session.all_files, q.at); m != "" && m not_in c.session.files {
            heap := runtime.heap_allocator()
            also := make([dynamic]string, heap)
            append(&also, ..args.also)
            append(&also, strings.clone(m, heap))
            args.also = also[:]
            serve_check(c, args^, strings.clone(c.stamp, context.temp_allocator), keeping = c.kept != nil)
        }
    }
    // (A check with errors answers from what they don't break, and says
    // after each answer which scopes those are.)
    partial := c.session.checked != nil && c.session.checked.partial
    if c.failure != "" && !partial { return c.failure, false }
    // (What a query keeps for the next, a fun's def-use, stays with its check.)
    context.allocator = virtual.arena_allocator(&c.arena)
    s := &c.session
    // (Asked as the query's module's: one of the set, as `mara ask` there.)
    if module != "" && module in s.files { s.pkg = module } else if args != nil { s.pkg = args.pkg_name }
    in_, in_err := ask_scopes(q, s.all_files, s.files, s.pkg)
    if in_err != "" { return strings.concatenate({in_err, "\n"}, context.temp_allocator), false }
    answer, ok = ask_run(s, q, in_)
    if s.checked != nil { answer = strings.concatenate({answer, s.checked.errors_said}, context.temp_allocator) }
    return
}

// The sources a check reads, as one text: each .mara file's path, size and
// time written: the stdlib's, the project's and the folders its build names.
// Another stamp: a file changed, came or went.
serve_stamp :: proc(compiler_dir: string, search_dirs: []string = nil) -> string {
    context.allocator = context.temp_allocator
    b := strings.builder_make()
    if compiler_dir != "" {
        for dir in module_search_dirs(compiler_dir) { serve_stamp_dir(&b, dir) }
    }
    serve_stamp_dir(&b, ".")
    for dir in search_dirs { serve_stamp_dir(&b, dir) }
    return strings.to_string(b)
}

serve_stamp_dir :: proc(b: ^strings.Builder, dir: string) {
    for e in list_dir(dir) {
        if e.dir || !strings.has_suffix(e.name, ".mara") { continue }
        fmt.sbprintf(b, "%s/%s %d %d\n", dir, e.name, e.size, e.written)
    }
}

// A line's words: split at whitespace, a double-quoted stretch one word
// (`at "C:\My Code\f.mara:12"`), its quotes dropped.
ask_words :: proc(line: string) -> []string {
    words: [dynamic]string
    words.allocator = context.temp_allocator
    i := 0
    for i < len(line) {
        for i < len(line) && strings.is_space(rune(line[i])) { i += 1 }
        if i >= len(line) { break }
        if line[i] == '"' {
            end := strings.index_byte(line[i + 1:], '"')
            if end < 0 { end = len(line) - i - 1 }
            append(&words, line[i + 1:i + 1 + end])
            i += end + 2
            continue
        }
        start := i
        for i < len(line) && !strings.is_space(rune(line[i])) { i += 1 }
        append(&words, line[start:i])
    }
    return words[:]
}
