package mara

import "core:bufio"
import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strings"

// ---------------------------------------------------------------------------
// `mara ask` queries: parsed from their words, their `in` scopes classified,
// answered against the checked program — once from the command line, or, with
// `--stdin`, each line stdin sends against one check (ask_serve).
// ---------------------------------------------------------------------------

// One query, as written: its subject and its filters.
Ask_Query :: struct {
    target:  string,  // the type/fn/variable the query is about; "" = the module map
    kind:    string,  // "types" | "call" | "flow" | "" (every graph)
    dir:     string,  // "above" | "below" | "" (both directions)
    scope:   string,  // an `in <module|file|fn>`; "" = the cwd's program
    scope2:  string,  // a second `in` — the two compose (`<var> in <fn> in <module>`)
    at:      string,  // `at <file>:<line>`: a variable precisely; with a column, a point
    depth:   int,     // the hop budget; -1 = unbounded
    control: bool,    // `control`: add control dependence (post-dominators) to a flow slice
    help:    bool,    // `--help`: the usage, not a lookup
}

// A query from its words — the command line's after `ask`, or one stdin line.
// On a mistake, the query so far and what to say about it.
ask_parse_query :: proc(words: []string) -> (q: Ask_Query, err: string) {
    q.depth = -1
    // A shell-quoted whole query (`mara ask "v in fn flow below"`) arrives as
    // ONE word — split every word on whitespace so both forms parse
    // identically. The value after a standalone `at` is kept intact: a quoted
    // path may legitimately contain spaces (`at "C:\My Code\f.mara:12"`).
    rest: [dynamic]string
    rest.allocator = context.temp_allocator
    for i := 0; i < len(words); i += 1 {
        if words[i] == "at" && i + 1 < len(words) {
            append(&rest, words[i], words[i + 1])
            i += 1
            continue
        }
        for piece in strings.fields(words[i], context.temp_allocator) { append(&rest, piece) }
    }
    // An explicit help request prints usage rather than being looked up as a
    // name — `mara ask --help` must not 404 on a type called "--help".
    for w in rest {
        if is_help_flag(w) {
            q.help = true
            return
        }
    }
    // `in <scope>` — up to two, which COMPOSE: `<var> in <fn> in <module>`
    // scopes the variable to a function AND narrows the module. Each value's
    // role (module / file / fn) is classified against the discovered files
    // (ask_scopes), so the two are order-independent here.
    for {
        found := -1
        for w, i in rest { if w == "in" { found = i; break } }
        if found < 0 { break }
        if found + 1 >= len(rest) { return q, "mara ask: `in` needs a module, file, or function name" }
        switch {
        case q.scope == "":  q.scope = rest[found + 1]
        case q.scope2 == "": q.scope2 = rest[found + 1]
        case:                return q, "mara ask: at most two `in` scopes (e.g. a function and a module)"
        }
        // Excise just the `in <scope>` pair — filters may follow it.
        remove_range(&rest, found, found + 2)
    }
    // An optional `at <file>:<line>` — precise variable addressing.
    for w, i in rest {
        if w != "at" { continue }
        if i + 1 >= len(rest) { return q, "mara ask: `at` needs a <file>:<line> location" }
        q.at = rest[i + 1]
        remove_range(&rest, i, i + 2)
        break
    }
    // An optional depth — the first bare integer anywhere in the words.
    for w, i in rest {
        if d, ok := ask_parse_depth(w); ok {
            q.depth = d
            ordered_remove(&rest, i)
            break
        }
    }
    // What remains is the name plus optional filters, in any order: a kind
    // (which graph), a direction, `control`. The lone other word is the name.
    for w in rest {
        if k, ok := ask_canon_kind(w); ok {
            if q.kind != "" && q.kind != k { return q, fmt.tprintf("mara ask: conflicting kind filters ('%s' and '%s')", q.kind, k) }
            q.kind = k
            continue
        }
        if d, ok := ask_canon_dir(w); ok {
            if q.dir != "" && q.dir != d { return q, fmt.tprintf("mara ask: conflicting direction filters ('%s' and '%s')", q.dir, d) }
            q.dir = d
            continue
        }
        if w == "control" || w == "ctrl" {
            q.control = true
            continue
        }
        if q.target != "" {
            // Two name-like words. Usually one is really a mistyped filter or
            // a retired keyword (`lineage`) — say so; the bare "two names"
            // complaint misdiagnoses it. The trailing word first (the common
            // `<name> <typo>` order), then the leading one.
            if hint, ok := ask_keyword_hint(w); ok { return q, fmt.tprintf("mara ask: %s", hint) }
            if hint, ok := ask_keyword_hint(q.target); ok { return q, fmt.tprintf("mara ask: %s", hint) }
            return q, fmt.tprintf("mara ask: expected one name, got '%s' and '%s'  (see `mara ask --help`)", q.target, w)
        }
        q.target = w
    }
    // `at` already identifies the variable, so a name alongside it is
    // contradictory. (`at` with `in <fn>` or `in <file>` is too: ask_scopes.)
    if q.at != "" && q.target != "" {
        return q, fmt.tprintf("mara ask: `at` already identifies the variable — drop the name '%s'", q.target)
    }
    // A filter with no subject has nothing to act on; bare `mara ask` (no name,
    // no `at`, no filters) is the module map.
    if q.target == "" && q.at == "" && (q.kind != "" || q.dir != "") {
        return q, "mara ask: a filter needs a name — e.g. `mara ask <name> above`"
    }
    return q, ""
}

// Where a query's `in` scopes narrow its subject. None re-roots: the program
// is always the cwd's plus the stdlib it uses.
Ask_Scopes :: struct {
    module: string,   // `<name> in <module>`: that module's namespace
    file:   string,   // `in <file>`: the subject pinned to that file
    fn:     string,   // `<var> in <fn>`: resolved after the check (ask)
}

// A query's `in` scopes classified against the discovered files — a module,
// a file, else a function — and checked: at most one of each; none but a
// module with `at`; a module the program uses.
ask_scopes :: proc(q: Ask_Query, all_files, files: map[string][dynamic]^Source_File, pkg: string) -> (in_: Ask_Scopes, err: string) {
    for sc in ([2]string{q.scope, q.scope2}) {
        switch {
        case sc == "":
        case sc in all_files:
            if in_.module != "" { return in_, "mara ask: two module scopes — narrow to one module at a time" }
            in_.module = sc
        case ask_file_discovered(all_files, sc):
            if in_.file != "" { return in_, "mara ask: two file scopes — pin one file at a time" }
            in_.file = filepath.base(sc)
        case:
            if in_.fn != "" { return in_, "mara ask: two function scopes — disambiguate one with `at <file>:<line>`" }
            in_.fn = sc
        }
    }
    // `at` precisely identifies a variable, so a SECOND variable address — `in
    // <fn>` or `in <file>` — conflicts. `in <module>` only narrows where a name
    // resolves, so it still composes with `at` (redundantly).
    if q.at != "" && (in_.fn != "" || in_.file != "") {
        return in_, "mara ask: `at` already identifies the variable — use `in <module>` only to pin where it lives, not `in <fn>`/`in <file>`"
    }
    // A module on disk the cwd project doesn't use isn't part of this program.
    if in_.module != "" && in_.module not_in files {
        return in_, fmt.tprintf("mara ask: module '%s' isn't part of this program — %s (cwd) doesn't use it.", in_.module, pkg)
    }
    return in_, ""
}

// What queries are answered against: the program, checked once.
Ask_Session :: struct {
    checked:      ^Checked_Program,
    all_files:    map[string][dynamic]^Source_File,
    files:        map[string][dynamic]^Source_File,   // the use-closure: the program's
    compiler_dir: string,
    pkg:          string,                              // the cwd's module, the root
}

// A query's answer; false when its subject wasn't found (or was ambiguous).
ask_run :: proc(s: ^Ask_Session, q: Ask_Query, in_: Ask_Scopes) -> (out: string, found: bool) {
    // Bare `mara ask` — the module map (the project at a glance). `at`
    // identifies a variable without a name, so it is not the bare form.
    if q.target == "" && q.at == "" {
        return ask_module_map(s.checked, s.all_files, s.compiler_dir, s.pkg), true
    }
    // `at <file>:<line>:<col>` with no name — the position query. A point in
    // the source names exactly one node, so unlike `at <file>:<line>` (which
    // disambiguates a NAMED variable) it needs no target.
    if q.target == "" && strings.count(q.at, ":") == 2 {
        return ask_at_point(&build_tree, s.all_files, s.checked.annot, q.at)
    }
    s.checked.du.want_control = q.control   // the post-dominator pass, only when asked
    return ask(s.checked, q.target, q.kind, q.dir, in_.fn, q.at, s.pkg, in_.file, in_.module, q.depth)
}

// ASK_DONE ends each answer `mara ask --stdin` gives: a client reading them
// knows where one ends.
ASK_DONE :: "-- end of answer --"

// `mara ask --stdin`: each line stdin sends is a query, answered as `mara ask
// <line>` would answer it — a mistake in one is its answer — then ASK_DONE;
// until stdin closes. The program was checked once, before the first.
ask_serve :: proc(s: ^Ask_Session) {
    r: bufio.Reader
    bufio.reader_init(&r, os.to_stream(os.stdin))
    defer bufio.reader_destroy(&r)
    for {
        line, rerr := bufio.reader_read_string(&r, '\n', context.temp_allocator)
        if rerr != nil && line == "" { break }
        if words := ask_words(line); len(words) > 0 {
            fmt.print(ask_serve_one(s, words))
            fmt.println(ASK_DONE)
        }
        free_all(context.temp_allocator)
        if rerr != nil { break }
    }
}

@(private="file")
ask_serve_one :: proc(s: ^Ask_Session, words: []string) -> string {
    q, err := ask_parse_query(words)
    if q.help { return strings.concatenate({ASK_USAGE, "\n"}, context.temp_allocator) }
    if err != "" { return strings.concatenate({err, "\n"}, context.temp_allocator) }
    in_, in_err := ask_scopes(q, s.all_files, s.files, s.pkg)
    if in_err != "" { return strings.concatenate({in_err, "\n"}, context.temp_allocator) }
    out, _ := ask_run(s, q, in_)
    return out
}

// A line's words: split at whitespace, a double-quoted stretch one word
// (`at "C:\My Code\f.mara:12"`), its quotes dropped.
@(private="file")
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
