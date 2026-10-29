package mara

import "core:bufio"
import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:path/filepath"
import "core:strings"
import "core:time"

// ---------------------------------------------------------------------------
// `mara serve [module]`: ask's queries, one a line from stdin, each answered
// as `mara ask <line>` would answer it, then ASK_DONE — against the module as
// it is on disk, checked again when a .mara file changes. A window starts it
// once and talks to it through pipes; it ends when its input does.
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
}

serve :: proc(args: CLI_Args) {
    compiler := compiler_file()
    check: Serve_Check
    serve_check(&check, args, serve_stamp(args.compiler_dir))
    r: bufio.Reader
    bufio.reader_init(&r, os.to_stream(os.stdin))
    defer bufio.reader_destroy(&r)
    for {
        line, rerr := bufio.reader_read_string(&r, '\n', context.temp_allocator)
        if rerr != nil && line == "" { break }
        // (Mara.exe rebuilt: ended, the query unanswered — the window starts
        // the new one and asks it again. Nothing said: serve's stderr reaches
        // the window with its answers, a word of it an answer begun.)
        if compiler_rebuilt(compiler) { os.exit(COMPILER_REBUILT_EXIT) }
        // (A blank line is a query too: `mara ask` alone, the module map.)
        if stamp := serve_stamp(args.compiler_dir); stamp != check.stamp {
            serve_check(&check, args, stamp)
        }
        answer, ok := serve_answer(&check, ask_words(line))
        fmt.print(answer)
        fmt.println(ASK_DONE if ok else ASK_FAILED)
        free_all(context.temp_allocator)
        if rerr != nil { break }
    }
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

// The module as it is on disk now, checked in a new arena — the last check's
// freed first, whole. (The build's globals, its tokens, tree and diagnostics,
// pointed into it: emptied, they fill with this check's.)
serve_check :: proc(c: ^Serve_Check, args: CLI_Args, stamp: string, overlays: ^map[string]string = nil) {
    if c.session.checked != nil { program_code_free(&c.session.checked.code) }   // (its own memory)
    virtual.arena_destroy(&c.arena)
    c^ = {}
    delete(build_tokens)   // (the tokens and the tree are on the heap)
    tree_free(&build_tree)
    build_tokens, build_files, build_literals, build_tree = {}, {}, {}, {}
    reset_diagnostics()
    if err := virtual.arena_init_growing(&c.arena); err != nil {
        fmt.panicf("mara serve: no arena for a check (%v)", err)
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
    files := compute_use_closure(all_files, args.pkg_name)
    checked, _, failure := check_module(args, files, &perf)
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
            f.imports = extract_imports(f.source)
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
serve_answer :: proc(c: ^Serve_Check, words: []string) -> (answer: string, ok: bool) {
    q, err := ask_parse_query(words)
    if q.help { return ASK_USAGE + "\n", true }
    if err != "" { return strings.concatenate({err, "\n"}, context.temp_allocator), false }
    if c.failure != "" { return c.failure, false }
    // (What a query keeps for the next, a fun's def-use, stays with its check.)
    context.allocator = virtual.arena_allocator(&c.arena)
    s := &c.session
    in_, in_err := ask_scopes(q, s.all_files, s.files, s.pkg)
    if in_err != "" { return strings.concatenate({in_err, "\n"}, context.temp_allocator), false }
    return ask_run(s, q, in_)
}

// The sources a check reads, as one text: each .mara file's path, size and
// time written, the stdlib's and the project's. Another stamp: a file
// changed, came or went.
serve_stamp :: proc(compiler_dir: string) -> string {
    context.allocator = context.temp_allocator
    b := strings.builder_make()
    if compiler_dir != "" {
        for dir in code_search_dirs(compiler_dir) { serve_stamp_dir(&b, dir) }
    }
    serve_stamp_dir(&b, ".")
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
