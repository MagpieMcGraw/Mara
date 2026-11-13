package mara

import "core:fmt"
import "core:hash"
import "core:os"
import "core:path/filepath"
import "core:strings"
import "core:time"

// ---------------------------------------------------------------------------
// The window (`mara view`) as `mara ask`'s answerer. A compiler has one
// window, wherever it's asked from. It listens on one pipe name
// (view_pipe_name, given it by `mara view`); each connection sends one line
// and gets its answer, with an end line; then the window closes the connection.
// A query says where it's asked from, `-in "<folder>" <module> <query>`: the
// window's `mara serve` goes there and answers it as `mara ask <query>` would.
// "-show " before that: the window shows the query too (`mara ask -show`), and
// moves to that module. "-cursor " before it: it shows the answer as what's at
// the editor's cursor (`mara ask -cursor`), and moves too. "-raise" and where
// from: comes to the front and moves (`mara view`).
// Docs: "-docs <dir>\t<words>": words looked up in that directory's .mara
// files and the stdlib's, shown in its Docs panel and answered with what it
// found (`mara docs`). Four more fields, "\t<kind>\t<name>\t<path>\t<line>",
// are what the name at the editor's point refers to (`mara docs at`): shown
// first, the rest below. Also "-editor <program>": the editor it opens a file
// in, at a line (`mara editor`); "-colors <name>=#rrggbb ...", an editor's
// colors, for its Sublime theme (`mara colors`).
// ---------------------------------------------------------------------------

// How long `mara ask` waits for a window's next byte before it checks here
// instead. (A re-check of a big program takes seconds.)
VIEW_QUIET :: 30 * time.Second

// How a request to a window went.
View_Exchange :: enum {
    Answered,
    No_Window,   // none listens on the name
    Broken,      // one did, then stopped answering
}

// The pipe name this compiler's window listens on: a hash of the compiler's
// path (on Windows case folded: one path however it's spelled), so windows
// opened by two compilers never meet.
view_pipe_name :: proc() -> string {
    key := get_compiler_exe()
    when ODIN_OS == .Windows { key = strings.to_lower(key, context.temp_allocator) }
    return fmt.aprintf("mara-view-%016x", hash.fnv64a(transmute([]byte)key))
}

// Where a line to the window is asked from: this folder and `module`.
view_write_here :: proc(b: ^strings.Builder, module: string) {
    cwd, _ := os.get_working_directory(context.temp_allocator)
    fmt.sbprintf(b, `-in "%s" %s`, cwd, module)
}

// `mara ask`'s query asked of the window, when one is open: the answer, and
// whether it failed. ok false when no window answers — none open, or one that
// stopped answering or cut its answer off — or when no module here is the one
// asked about, which only the check here knows what to say about.
ask_via_view :: proc(args: CLI_Args) -> (answer: string, failed: bool, ok: bool) {
    if !module_is_in(".", args.pkg_name) { return }
    b := strings.builder_make(context.temp_allocator)
    if args.show { strings.write_string(&b, "-show ") }
    if args.cursor { strings.write_string(&b, "-cursor ") }
    view_write_here(&b, args.pkg_name)
    strings.write_byte(&b, ' ')
    for w, i in args.ask_words {
        if i > 0 { strings.write_byte(&b, ' ') }
        // (A word with a space in it, quoted: still one word to ask_words.)
        if strings.index_any(w, " \t") >= 0 { fmt.sbprintf(&b, `"%s"`, w) } else { strings.write_string(&b, w) }
    }
    reply, said_failed, how := view_request(view_pipe_name(), strings.to_string(b))
    if how == .Answered { return reply, said_failed, true }
    // (A window that stopped answering, or cut its answer off: said, then
    // the check here answers.)
    if how == .Broken && !args.cursor { fmt.eprintln("mara ask: the window didn't answer; checking here instead") }
    return "", false, false
}

// `mara docs <words>`: a window this compiler opened, wherever, looks them up
// in this directory's .mara files and the stdlib's; what it found printed.
// `mara docs -reload`: what its Docs panel shows looked up again (its F5).
// Exits 1 when it found nothing, or no window answers.
docs_via_view :: proc(args: CLI_Args) {
    cwd, _ := os.get_working_directory(context.temp_allocator)
    words := strings.join(args.docs_words, " ", context.temp_allocator)
    exact := ""
    if args.docs_at != "" {
        name: string
        exact, name = docs_exact(args, cwd, words)
        if words == "" { words = name }
    }
    request := strings.concatenate({"-docs ", cwd, "\t", words, exact}, context.temp_allocator)
    if words == "-reload" && exact == "" { request = "-reload" }
    answer, failed, how := view_request(view_pipe_name(), request)
    switch how {
    case .No_Window:
        fmt.eprintln("mara docs: no window is open — 'mara view' opens one")
        os.exit(1)
    case .Broken:
        fmt.eprintln("mara docs: the window didn't answer")
        os.exit(1)
    case .Answered:
        fmt.print(answer)
        if failed { os.exit(1) }
    }
}

// `mara editor <program>`: the window keeps the editor that opens a crash's
// calls. Exits 1 when no window answers.
editor_via_view :: proc(args: CLI_Args) {
    _, failed, how := view_request(view_pipe_name(), strings.concatenate({"-editor ", args.editor}, context.temp_allocator))
    switch how {
    case .No_Window:
        fmt.eprintln("mara editor: no window is open — 'mara view' opens one")
        os.exit(1)
    case .Broken:
        fmt.eprintln("mara editor: the window didn't answer")
        os.exit(1)
    case .Answered:
        if failed { os.exit(1) }
    }
}

// `mara colors <name>=#rrggbb ...`: the window keeps Sublime's colors, for its
// Sublime theme. Exits 1 when no window answers.
colors_via_view :: proc(args: CLI_Args) {
    _, failed, how := view_request(view_pipe_name(), strings.concatenate({"-colors ", args.colors}, context.temp_allocator))
    switch how {
    case .No_Window:
        fmt.eprintln("mara colors: no window is open — 'mara view' opens one")
        os.exit(1)
    case .Broken:
        fmt.eprintln("mara colors: the window didn't answer")
        os.exit(1)
    case .Answered:
        if failed { os.exit(1) }
    }
}

// What the name at `mara docs at <point>` refers to, as the docs request's
// last fields — "\t<kind>\t<name>\t<path>\t<line>", a builtin's path empty,
// a keyword's kind "keyword" — and its name. "" when nothing there refers to
// anything, or the point's token isn't the words' (the file changed since it
// was saved: the point is on something else now).
docs_exact :: proc(args: CLI_Args, cwd, words: string) -> (exact, name: string) {
    // (`mara ask at`'s first lines: "<file>:<l>:<c>  token '<t>'", then
    // "refers to: <kind> <name>  <file>:<line>".)
    lines := strings.split_lines(docs_point_answer(args), context.temp_allocator)
    if len(lines) < 2 { return }
    token := ""
    if at := strings.index(lines[0], "token '"); at >= 0 { token = strings.trim_suffix(lines[0][at + 7:], "'") }
    if words != "" && !docs_same_word(token, words) { return }
    // (A keyword refers to nothing: it's itself, shown by its entry in
    // doc/basics.mara.)
    if !strings.has_prefix(lines[1], "refers to: ") {
        if _, is_keyword := keyword_lookup(token); is_keyword || token == "defer?" {
            return fmt.tprintf("\tkeyword\t%s\t\t0", token), token
        }
        return
    }
    s := lines[1][len("refers to: "):]
    space := strings.index_byte(s, ' ')
    if space < 0 { return }
    kind := s[:space]
    s = s[space + 1:]
    loc := ""
    if gap := strings.index(s, "  "); gap >= 0 {
        loc = strings.trim_space(s[gap + 2:])
        s = s[:gap]
    }
    name = s
    if loc == "" { return fmt.tprintf("\t%s\t%s\t\t0", kind, name), name }   // (a builtin)
    colon := strings.last_index_byte(loc, ':')
    if colon < 0 { return "", name }
    path, line := loc[:colon], loc[colon + 1:]
    if !filepath.is_abs(path) { path, _ = filepath.join({cwd, path}, context.temp_allocator) }
    return fmt.tprintf("\t%s\t%s\t%s\t%s", kind, name, path, line), name
}

// `mara ask at <point>`'s answer: the window's, when one is open and there's
// a module here for it to ask about, else from a check made here. "" when it
// failed.
docs_point_answer :: proc(args: CLI_Args) -> string {
    query := []string{"at", args.docs_at}
    if module_is_in(".", args.pkg_name) {
        b := strings.builder_make(context.temp_allocator)
        view_write_here(&b, args.pkg_name)
        strings.write_byte(&b, ' ')
        strings.write_string(&b, strings.join(query, " ", context.temp_allocator))
        answer, failed, how := view_request(view_pipe_name(), strings.to_string(b))
        if how == .Answered { return "" if failed else answer }
    }
    here := args
    here.serve = true   // (a check for analysis: no code)
    check: Serve_Check
    serve_check(&check, here, serve_stamp(args.compiler_dir, args.search_dirs))
    local, ok := serve_answer(&check, query)
    return local if ok else ""
}

// Whether the point's token is the words' — one has the other in it (part
// of a name selected; a selection starting with the name), case not minded.
docs_same_word :: proc(token, words: string) -> bool {
    if token == "" { return false }
    t := strings.to_lower(token, context.temp_allocator)
    w := strings.to_lower(words, context.temp_allocator)
    first := w
    for c, i in w {
        if !(c == '_' || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) { first = w[:i]; break }
    }
    return strings.contains(w, t) || (first != "" && strings.contains(t, first))
}

// One request to the window listening on the pipe name: its answer, without
// the end line, and whether that line said it failed. Broken also when the
// reply came without an end line — cut off.
view_request :: proc(name, request: string) -> (answer: string, failed: bool, how: View_Exchange) {
    reply: string
    reply, how = view_exchange(name, request)
    if how != .Answered { return }
    // (Its last line ends it: the answer is before.)
    body := strings.trim_suffix(reply, "\n")
    at := strings.last_index_byte(body, '\n') + 1
    switch body[at:] {
    case ASK_DONE:   return body[:at], false, .Answered
    case ASK_FAILED: return body[:at], true, .Answered
    }
    return "", false, .Broken
}
