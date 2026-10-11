package mara

import "core:bufio"
import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:strings"
import "core:time"

// ---------------------------------------------------------------------------
// `mara serve [module]`: ask's queries, one a line from stdin, each answered
// as `mara ask <line>` would answer it, then ASK_DONE — against the module as
// it is on disk, checked again when a .mara file changes. A window starts it
// once and talks to it through pipes; it ends when its input does.
// ---------------------------------------------------------------------------

// ASK_DONE ends each answer: a client reading them knows where one ends.
ASK_DONE :: "-- end of answer --"

// One check of the module, in an arena of its own: freed whole when a file
// changes and the next check replaces it.
Serve_Check :: struct {
    arena:   virtual.Arena,
    session: Ask_Session,   // (its program, when there is one, even one with errors)
    failure: string,   // what every answer is instead, when it didn't check
    stamp:   string,   // the sources it read (serve_stamp)
}

serve :: proc(args: CLI_Args) {
    check: Serve_Check
    serve_check(&check, args, serve_stamp(args.compiler_dir))
    r: bufio.Reader
    bufio.reader_init(&r, os.to_stream(os.stdin))
    defer bufio.reader_destroy(&r)
    for {
        line, rerr := bufio.reader_read_string(&r, '\n', context.temp_allocator)
        if rerr != nil && line == "" { break }
        // (A blank line is a query too: `mara ask` alone, the module map.)
        if stamp := serve_stamp(args.compiler_dir); stamp != check.stamp {
            serve_check(&check, args, stamp)
        }
        fmt.print(serve_answer(&check, ask_words(line)))
        fmt.println(ASK_DONE)
        free_all(context.temp_allocator)
        if rerr != nil { break }
    }
}

// The module as it is on disk now, checked in a new arena — the last check's
// freed first, whole. (The build's globals, its tokens, tree and diagnostics,
// pointed into it: emptied, they fill with this check's.)
serve_check :: proc(c: ^Serve_Check, args: CLI_Args, stamp: string) {
    if c.session.checked != nil { program_code_free(&c.session.checked.code) }   // (its own memory)
    virtual.arena_destroy(&c.arena)
    c^ = {}
    build_tokens, build_files, build_literals, build_tree = {}, {}, {}, {}
    reset_diagnostics()
    if err := virtual.arena_init_growing(&c.arena); err != nil {
        fmt.panicf("mara serve: no arena for a check (%v)", err)
    }
    context.allocator = virtual.arena_allocator(&c.arena)
    c.stamp = strings.clone(stamp)

    perf := Performance_Timer{quiet = true}
    perf_timer_begin(&perf, "discover")
    all_files := discover_all_files(args.compiler_dir, ".")
    if args.pkg_name not_in all_files {
        c.failure = module_missing(all_files, args.pkg_name)
        return
    }
    files := compute_use_closure(all_files, args.pkg_name)
    checked, _, failure := check_module(args, files, &perf)
    c.session = Ask_Session{checked, all_files, files, args.compiler_dir, args.pkg_name}
    c.failure = failure
    reset_diagnostics()   // (a check's warnings: about the code, not a query — answered by none)
}

// A query's answer — a mistake in it is its answer; when the module didn't
// check, what's wrong with it is.
serve_answer :: proc(c: ^Serve_Check, words: []string) -> string {
    q, err := ask_parse_query(words)
    if q.help { return ASK_USAGE + "\n" }
    if err != "" { return strings.concatenate({err, "\n"}, context.temp_allocator) }
    if c.failure != "" { return c.failure }
    // (What a query keeps for the next, a fun's def-use, stays with its check.)
    context.allocator = virtual.arena_allocator(&c.arena)
    s := &c.session
    in_, in_err := ask_scopes(q, s.all_files, s.files, s.pkg)
    if in_err != "" { return strings.concatenate({in_err, "\n"}, context.temp_allocator) }
    out, _ := ask_run(s, q, in_)
    return out
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
    dh, err := os.open(dir)
    if err != nil { return }
    defer os.close(dh)
    entries, _ := os.read_dir(dh, -1, context.allocator)
    for e in entries {
        if e.type == .Directory || !strings.has_suffix(e.name, ".mara") { continue }
        fmt.sbprintf(b, "%s/%s %d %d\n", dir, e.name, e.size, time.time_to_unix_nano(e.modification_time))
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
