package mara

import "core:fmt"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// `mara ask` queries: parsed from their words, their `in` scopes classified,
// answered against the checked program — once from the command line, or each
// line `mara serve` reads (serve.odin).
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
    if q.target == "#tokens" { return ask_tokens(s, q, in_) }
    // `at <file>:<line>:<col>` with no name — the position query. A point in
    // the source names exactly one node, so unlike `at <file>:<line>` (which
    // disambiguates a NAMED variable) it needs no target.
    // `what at <file>:<line>:<col>` — the same point, to read.
    if q.kind == "what" {
        if q.target != "" || strings.count(q.at, ":") != 2 {
            return "mara ask: `what` is about a point — `mara ask what at <file>:<line>:<col>`\n", false
        }
        return ask_what_at_point(&build_tree, s.all_files, s.checked.annot, q.at)
    }
    if q.target == "" && strings.count(q.at, ":") == 2 {
        return ask_at_point(&build_tree, s.all_files, s.checked.annot, &s.checked.code, q.at)
    }
    // `[N!]T`, `^[]byte` — a shape: where it's written, what's declared of it
    // (ask_types.odin). In the program's own modules, or the one `in` names.
    if ask_is_shape(q.target) {
        modules := make(map[string]bool, allocator = context.temp_allocator)
        desc: string
        if in_.module != "" {
            modules[in_.module] = true
            desc = fmt.tprintf("module %s", in_.module)
        } else {
            for name, files in s.files {
                if len(files) > 0 && !ask_file_is_stdlib(files[0].path, s.compiler_dir) { modules[name] = true }
            }
            desc = fmt.tprintf("%s's own modules — `in <module>` for one, the stdlib's too", s.pkg)
        }
        if in_.file != "" { desc = fmt.tprintf("file %s", in_.file) }
        return ask_shape_query(s.checked, q.target, modules, desc, in_.file)
    }
    s.checked.du.want_control = q.control   // the post-dominator pass, only when asked
    return ask(s.checked, q.target, q.kind, q.dir, in_.fn, q.at, s.pkg, in_.file, in_.module, q.depth)
}

// `#tokens`: every token Mara has (TOKEN_TEXTS) and how many times each is
// written in the module here, or in the module or file `in` names. Most used
// first; the ones not used at the end.
@(private="file")
ask_tokens :: proc(s: ^Ask_Session, q: Ask_Query, in_: Ask_Scopes) -> (out: string, found: bool) {
    if q.kind != "" || q.dir != "" || q.at != "" || q.depth >= 0 || q.control {
        return "mara ask: #tokens takes only `in <module>` or `in <file>`\n", false
    }
    if in_.fn != "" { return fmt.tprintf("mara ask: #tokens counts a module or a file — '%s' is neither\n", in_.fn), false }
    // (Each text lexes as its kind: checked in the debug build.)
    when ODIN_DEBUG {
        for texts, k in TOKEN_TEXTS {
            #partial switch k { case .Number, .String, .Char, .Identifier, .Newline: continue }
            for text in texts {
                if text == "" { continue }
                l := lexer_init(text)
                got := next_token(&l)
                if got.kind != k || int(got.len) != len(text) { fmt.panicf("TOKEN_TEXTS: %q lexes as %v, not %v", text, got.kind, k) }
            }
        }
    }
    // The files: the module's, or the one file named (in any module of the program).
    module := in_.module if in_.module != "" else s.pkg
    files := make([dynamic]^Source_File, context.temp_allocator)
    for name, module_files in s.files {
        if in_.file == "" && name != module { continue }
        if in_.module != "" && name != module { continue }
        for f in module_files {
            if in_.file == "" || filepath.base(f.path) == in_.file { append(&files, f) }
        }
    }
    if in_.file != "" && len(files) != 1 {
        if len(files) == 0 { return fmt.tprintf("mara ask: no file %s in this program\n", in_.file), false }
        return fmt.tprintf("mara ask: %d files are named %s — add `in <module>` for one\n", len(files), in_.file), false
    }
    counts: [Token_Kind][2]int
    total := 0
    for f in files {
        for id in int(f.first_token) ..< int(f.end_token) {
            t := build_tokens[id]
            if t.kind == .EOF || t.kind == .Invalid { continue }
            text := f.source[t.offset:][:t.len]
            if t.kind == .Ampersand && text == "^" { t.kind = .Caret }   // (`^x`: the parser takes it as `&`'s kind)
            second := TOKEN_TEXTS[t.kind][1]
            counts[t.kind][1 if second != "" && text == second else 0] += 1
            total += 1
        }
    }
    Row :: struct { text: string, count: int }
    rows := make([dynamic]Row, context.temp_allocator)
    width := 0
    for texts, k in TOKEN_TEXTS {
        for text, i in texts {
            if text == "" { continue }
            append(&rows, Row{text, counts[k][i]})
            width = max(width, len(text))
        }
    }
    slice.stable_sort_by(rows[:], proc(a, b: Row) -> bool { return a.count > b.count })
    b := strings.builder_make(context.temp_allocator)
    where_ := fmt.tprintf("%s (module %s)", in_.file, files[0].module) if in_.file != "" else fmt.tprintf("module %s", module)
    fmt.sbprintf(&b, "Tokens in %s: %d in %d file%s\n\n", where_, total, len(files), "" if len(files) == 1 else "s")
    digits := len(fmt.tprint(rows[0].count))
    for r in rows {
        text := strings.left_justify(r.text, width, " ", context.temp_allocator)
        count := strings.right_justify(fmt.tprint(r.count), digits, " ", context.temp_allocator)
        if r.count == 0 { fmt.sbprintf(&b, "  %s  %s\n", text, count); continue }
        share := strings.right_justify(fmt.tprintf("%.1f%%", 100 * f64(r.count) / f64(total)), 6, " ", context.temp_allocator)
        fmt.sbprintf(&b, "  %s  %s  %s\n", text, count, share)
    }
    strings.write_string(&b, "\nComments aren't tokens: the lexer skips them.\n")
    return strings.to_string(b), true
}
