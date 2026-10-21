package mara

import "base:runtime"
import "core:bufio"
import "core:encoding/json"
import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// `mara lsp`: the Language Server Protocol, for editors — Sublime's LSP
// package, VS Code, any client — on stdin and stdout. A file asked about is
// checked with its module as serve checks one (serve.odin): its directory's,
// as `mara build` takes one there — where that can't tell, the one it
// declares (lsp_module) — the editor's open files as they are in the editor,
// saved or not, laid over the files on disk (serve_overlay). It answers
//   hover             what's at the point (`ask what at`), and the doc
//                     comment of what the name there refers to
//   definition        where the name at the point is declared
//   references        every name referring to the same declaration
//   document symbols  the file's definitions
//   completion        the names that can be written at the point (completion.odin)
//   code actions      a declaration being renamed: its uses renamed too, or its name put back
//   rename            a name, its declaration and every use (lsp_rename.odin)
// and publishes each check's errors and warnings, by file. A check is made
// when a request needs one and something changed — a file on disk, an edit
// in the editor — and after an edit, once the editor has nothing more to
// send. Code that doesn't parse is checked as far as it does (check_module).
// initializationOptions turn each off: {"hover": false, "definition": false,
// "references": false, "symbols": false, "completion": false, "renames":
// false, "diagnostics": false}.
// ---------------------------------------------------------------------------

Lsp :: struct {
    args:     CLI_Args,
    reader:   bufio.Reader,
    heap:     runtime.Allocator,   // what lasts from one message to the next
    overlays: map[string]string,   // an open file's text, by path_key
    open_uris: map[string]string,  // ... its URI, as the editor spells it
    edits:    int,                 // overlay changes so far
    utf8:     bool,                // positions count bytes; else UTF-16 units (LSP's default)
    hover, definition, references, symbols, completion, renames, diagnostics: bool,   // offered (initializationOptions)
    names:    Lsp_Names,           // the open files' declarations and their uses (lsp_rename.odin)
    orders:   Lsp_Orders,          // ... their structs' fields, funs' results and params, and what gives them by position (lsp_moves.odin)
    check:    Serve_Check,
    checked:  bool,                // a check made
    dir:      string,              // its module's directory
    module:   string,              // ... and the module
    stamp:    string,              // the files on disk it read (serve_stamp)
    checked_edits: int,            // the overlays' edits it read
    dirty:    bool,                // an edit since: a check to publish once the editor's quiet
    edit_path: string,             // ... the file edited
    published: map[string]bool,    // the uris last published to, errors or none
    shutdown: bool,
}

lsp :: proc(args: CLI_Args) {
    s: Lsp
    s.args = args
    s.args.serve = true   // (a check for analysis: no code)
    s.heap = runtime.heap_allocator()
    s.overlays = make(map[string]string, allocator = s.heap)
    s.published = make(map[string]bool, allocator = s.heap)
    s.open_uris = make(map[string]string, allocator = s.heap)
    s.hover, s.definition, s.references, s.symbols, s.completion, s.renames, s.diagnostics = true, true, true, true, true, true, true
    bufio.reader_init(&s.reader, os.to_stream(os.stdin))
    compiler := compiler_file()
    context.allocator = context.temp_allocator   // (each message's work, freed after it)
    for {
        body, ok := lsp_read(&s.reader)
        if !ok { break }   // (the editor's gone)
        // (Mara.exe rebuilt: ended — the editor starts the new one, which
        // is sent the open files again.)
        if compiler_rebuilt(compiler) {
            fmt.eprintln("mara lsp: Mara was rebuilt — ending, so the new one starts")
            os.exit(COMPILER_REBUILT_EXIT)
        }
        msg, err := json.parse(transmute([]byte)body, parse_integers = true)
        if err == .None { lsp_handle(&s, msg) }
        // (After edits, a check once nothing more waits: its errors published.)
        if s.dirty && bufio.reader_buffered(&s.reader) == 0 && !stdin_waiting() {
            s.dirty = false
            lsp_check(&s, s.edit_path)
        }
        free_all(context.temp_allocator)
    }
}

// --- messages ---------------------------------------------------------------

// One message's body: its headers read — Content-Length the one that counts
// — then that many bytes. False when stdin has ended.
lsp_read :: proc(r: ^bufio.Reader) -> (string, bool) {
    length := -1
    for {
        line, err := bufio.reader_read_string(r, '\n')
        if err != nil { return "", false }
        line = strings.trim_right(line, "\r\n")
        if line == "" {
            if length >= 0 { break }
            continue   // (a blank line before any header)
        }
        if colon := strings.index_byte(line, ':'); colon > 0 && strings.equal_fold(strings.trim_space(line[:colon]), "Content-Length") {
            length, _ = strconv.parse_int(strings.trim_space(line[colon + 1:]))
        }
    }
    body := make([]byte, length)
    got := 0
    for got < length {
        n, err := bufio.reader_read(r, body[got:])
        if n == 0 && err != nil { return "", false }
        got += n
    }
    return string(body), true
}

// A message sent: its header, its body.
lsp_send :: proc(body: string) {
    fmt.print(fmt.tprintf("Content-Length: %d\r\n\r\n%s", len(body), body))
}

lsp_respond :: proc(id: json.Value, result: string) {
    lsp_send(fmt.tprintf(`{{"jsonrpc":"2.0","id":%s,"result":%s}}`, json_id(id), result))
}

lsp_fail :: proc(id: json.Value, code: int, message: string) {
    lsp_send(fmt.tprintf(`{{"jsonrpc":"2.0","id":%s,"error":{{"code":%d,"message":%s}}}}`, json_id(id), code, json_str(message)))
}

lsp_notify :: proc(method, params: string) {
    lsp_send(fmt.tprintf(`{{"jsonrpc":"2.0","method":%s,"params":%s}}`, json_str(method), params))
}

// A message: a request answered, a notification heeded.
lsp_handle :: proc(s: ^Lsp, msg: json.Value) {
    method := json_text(json_at(msg, "method"))
    id := json_at(msg, "id")
    params := json_at(msg, "params")
    uri := json_text(json_at(json_at(params, "textDocument"), "uri"))
    switch method {
    case "initialize":
        lsp_initialize(s, id, params)
    case "shutdown":
        s.shutdown = true
        lsp_respond(id, "null")
    case "exit":
        os.exit(0 if s.shutdown else 1)
    case "textDocument/didOpen":
        lsp_set_overlay(s, uri, json_text(json_at(json_at(params, "textDocument"), "text")))
    case "textDocument/didChange":
        // (Each change the whole text: the last, the latest.)
        if changes, is_list := json_at(params, "contentChanges").(json.Array); is_list && len(changes) > 0 {
            lsp_set_overlay(s, uri, json_text(json_at(changes[len(changes) - 1], "text")))
        }
    case "textDocument/didClose":
        lsp_drop_overlay(s, uri)
    case "textDocument/didSave":
        lsp_edited(s, uri)   // (the file on disk: its stamp says it changed)
    case "textDocument/hover":
        lsp_respond(id, lsp_hover(s, params))
    case "textDocument/definition":
        lsp_respond(id, lsp_definition(s, params))
    case "textDocument/references":
        lsp_respond(id, lsp_references(s, params))
    case "textDocument/documentSymbol":
        lsp_respond(id, lsp_symbols(s, params))
    case "textDocument/completion":
        lsp_respond(id, lsp_completion(s, params))
    case "textDocument/codeAction":
        lsp_respond(id, lsp_code_actions(s, params))
    case "textDocument/rename":
        if result, refused := lsp_rename(s, params); refused != "" {
            lsp_fail(id, -32602, refused)
        } else {
            lsp_respond(id, result)
        }
    case:
        // (A notification not heeded is fine; a request needs an answer.)
        if id != nil && !strings.has_prefix(method, "$/") {
            lsp_fail(id, -32601, fmt.tprintf("mara lsp: no %s", method))
        }
    }
}

// What the server offers, as the client's options and capabilities let it.
lsp_initialize :: proc(s: ^Lsp, id, params: json.Value) {
    opts := json_at(params, "initializationOptions")
    s.hover       = json_bool(json_at(opts, "hover"), true)
    s.definition  = json_bool(json_at(opts, "definition"), true)
    s.references  = json_bool(json_at(opts, "references"), true)
    s.symbols     = json_bool(json_at(opts, "symbols"), true)
    s.completion  = json_bool(json_at(opts, "completion"), true)
    s.renames     = json_bool(json_at(opts, "renames"), true)
    s.diagnostics = json_bool(json_at(opts, "diagnostics"), true)
    // (UTF-8 positions, the compiler's, when the client takes them.)
    if encodings, is_list := json_at(json_at(json_at(params, "capabilities"), "general"), "positionEncodings").(json.Array); is_list {
        for e in encodings { if json_text(e) == "utf-8" { s.utf8 = true } }
    }
    lsp_respond(id, fmt.tprintf(
        `{{"capabilities":{{"positionEncoding":%s,"textDocumentSync":{{"openClose":true,"change":1,"save":{{"includeText":false}}}},` +
        `"hoverProvider":%v,"definitionProvider":%v,"referencesProvider":%v,"documentSymbolProvider":%v%s}},` +
        `"serverInfo":{{"name":"mara lsp"}}}}`,
        json_str("utf-8" if s.utf8 else "utf-16"), s.hover, s.definition, s.references, s.symbols,
        strings.concatenate({`,"completionProvider":{"triggerCharacters":["."]}` if s.completion else "",
                             `,"renameProvider":true,"codeActionProvider":{"codeActionKinds":["quickfix","refactor"]}` if s.renames else ""})))
}

// --- the editor's files -----------------------------------------------------

// A file as the editor has it now.
lsp_set_overlay :: proc(s: ^Lsp, uri, text: string) {
    key := path_key(uri_path(uri))
    if old, had := s.overlays[key]; had {
        lsp_map_edit(s, key, old, text)   // (the kept names' places moved with the edit)
        delete(old, s.heap)
        s.overlays[key] = strings.clone(text, s.heap)
    } else {
        s.overlays[strings.clone(key, s.heap)] = strings.clone(text, s.heap)
        s.open_uris[strings.clone(key, s.heap)] = strings.clone(uri, s.heap)
    }
    s.edits += 1
    lsp_edited(s, uri)
}

// A file closed in the editor: as it is on disk again.
lsp_drop_overlay :: proc(s: ^Lsp, uri: string) {
    k := path_key(uri_path(uri))
    if _, had := s.overlays[k]; had {
        key, text := delete_key(&s.overlays, k)
        delete(key, s.heap)
        delete(text, s.heap)
        ukey, u := delete_key(&s.open_uris, k)
        delete(ukey, s.heap)
        delete(u, s.heap)
        s.edits += 1
    }
    lsp_edited(s, uri)
}

// A file changed — in the editor, or saved: its module checked again once
// the editor's quiet, its errors published.
lsp_edited :: proc(s: ^Lsp, uri: string) {
    s.dirty = true
    lsp_keep(s, &s.edit_path, uri_path(uri))
}

// A string that lasts (on the heap), the one before let go.
lsp_keep :: proc(s: ^Lsp, at: ^string, value: string) {
    if at^ == value { return }
    delete(at^, s.heap)
    at^ = strings.clone(value, s.heap)
}

// --- the check --------------------------------------------------------------

// The module of the file at `path` checked (lsp_module) — unless the check
// made is of it and nothing's changed since, on disk or in the editor — its
// errors published when it's made. False when there's no program to answer
// from: no module there, or it didn't parse.
lsp_check :: proc(s: ^Lsp, path: string) -> bool {
    if path == "" { return false }
    dir := filepath.dir(path)
    module := lsp_module(s, path)
    if os.change_directory(dir) != nil { return false }
    stamp := serve_stamp(s.args.compiler_dir)
    if s.checked && path_key(dir) == path_key(s.dir) && module == s.module && stamp == s.stamp && s.edits == s.checked_edits {
        return s.check.session.checked != nil
    }
    args := s.args
    args.pkg_name = module
    serve_check(&s.check, args, stamp, &s.overlays)
    lsp_keep(s, &s.dir, dir)
    lsp_keep(s, &s.module, module)
    lsp_keep(s, &s.stamp, stamp)
    s.checked = true
    s.checked_edits = s.edits
    lsp_keep_names(s)
    lsp_keep_orders(s)
    // (The edited file's module this one: its check made.)
    if s.edit_path != "" && path_key(dir) == path_key(filepath.dir(s.edit_path)) && module == lsp_module(s, s.edit_path) { s.dirty = false }
    if s.diagnostics { lsp_publish(s) }
    return s.check.session.checked != nil
}

// The check's errors and warnings, each file's — and none, now, for a file
// that had some before.
lsp_publish :: proc(s: ^Lsp) {
    by_uri := make(map[string][dynamic]string)
    for d in s.check.diagnostics {
        file, line, col, ok := lsp_split_location(d.location)
        if !ok { continue }
        path := lsp_abs(s, file)
        uri := lsp_uri(s, path)
        // (The word there, marked: an error's place is its first character.)
        src, _ := lsp_source(s, path)
        _, text := line_at(src, line)
        c0 := clamp(col - 1, 0, len(text))
        c1 := c0
        for c1 < len(text) && is_word_byte(text[c1]) { c1 += 1 }
        if c1 == c0 { c1 = min(c0 + 1, len(text)) }
        severity := 2 if d.kind == .Warning else 1
        items := by_uri[uri]
        append(&items, fmt.tprintf(`{{"range":%s,"severity":%d,"source":"mara","message":%s}}`,
                                   lsp_range(s, text, line, c0, line, text, c1), severity, json_str(d.message)))
        by_uri[uri] = items
    }
    if s.renames { lsp_moved_diagnostics(s, &by_uri) }   // (places left in a moved order's old one: lsp_moves.odin)
    for uri, items in by_uri {
        lsp_notify("textDocument/publishDiagnostics", fmt.tprintf(`{{"uri":%s,"diagnostics":[%s]}}`, json_str(uri), strings.join(items[:], ",")))
    }
    // (None for a file that had some, and for each open file without any: an
    // editor's marks always the check's.)
    cleared := make(map[string]bool)
    for uri in s.published { if uri not_in by_uri { cleared[uri] = true } }
    for _, uri in s.open_uris { if uri not_in by_uri { cleared[uri] = true } }
    for uri in cleared {
        lsp_notify("textDocument/publishDiagnostics", fmt.tprintf(`{{"uri":%s,"diagnostics":[]}}`, json_str(uri)))
    }
    for uri in s.published { delete(uri, s.heap) }
    clear(&s.published)
    for uri in by_uri { s.published[strings.clone(uri, s.heap)] = true }
}

// --- answers ----------------------------------------------------------------

// Hover: what's at the point, as `mara ask what at` says it; then the doc
// comment of what the name there refers to.
lsp_hover :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.hover { return "null" }
    spec, ok := lsp_point(s, params)
    if !ok { return "null" }
    session := &s.check.session
    what, found := ask_what_at_point(&build_tree, session.all_files, session.checked.annot, spec)
    if !found { return "null" }
    value := strings.concatenate({"```\n", what, "```"})
    if r, _, refers := point_reference(&build_tree, session.all_files, session.checked.annot, spec); refers && r.decl != 0 {
        if doc := doc_comment_above(build_tokens[r.decl]); doc != "" { value = strings.concatenate({value, "\n\n", doc}) }
    }
    return fmt.tprintf(`{{"contents":{{"kind":"markdown","value":%s}}}}`, json_str(value))
}

// Definition: where the name at the point is declared.
lsp_definition :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.definition { return "null" }
    spec, ok := lsp_point(s, params)
    if !ok { return "null" }
    session := &s.check.session
    r, _, refers := point_reference(&build_tree, session.all_files, session.checked.annot, spec)
    if !refers || r.decl == 0 { return "null" }
    return lsp_location(s, r.decl)
}

// References: every name referring to the declaration the name at the point
// does — the declaration's own when the client asks for it.
lsp_references :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.references { return "null" }
    spec, ok := lsp_point(s, params)
    if !ok { return "null" }
    session := &s.check.session
    r, _, refers := point_reference(&build_tree, session.all_files, session.checked.annot, spec)
    if !refers || r.decl == 0 { return "[]" }
    with_declaration := json_bool(json_at(json_at(params, "context"), "includeDeclaration"), true)
    items := make([dynamic]string)
    for tok in references_to(&build_tree, session.checked.annot, r.decl) {
        if tok == r.decl && !with_declaration { continue }
        append(&items, lsp_location(s, tok))
    }
    return strings.concatenate({"[", strings.join(items[:], ","), "]"})
}

// Completion: the names that can be written at the point. The editor's text
// with a placeholder typed in there (COMPLETE_HERE) is checked, and what the
// placeholder is says which (completions_at). That check isn't of the
// editor's text: the next request checks again.
lsp_completion :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.completion { return "null" }
    path := uri_path(json_text(json_at(json_at(params, "textDocument"), "uri")))
    position := json_at(params, "position")
    line := json_int(json_at(position, "line")) + 1
    key := path_key(path)
    src, open := s.overlays[key]
    if !open {
        data, err := os.read_entire_file_from_path(path, context.allocator)
        if err != nil { return "null" }
        src = string(data)
    }
    start, text := line_at(src, line)
    col := lsp_byte_col(s, text, json_int(json_at(position, "character")))
    files := make(map[string]string)
    for k, v in s.overlays { files[k] = v }
    files[key] = strings.concatenate({src[:start + col], COMPLETE_HERE, src[start + col:]})
    dir := filepath.dir(path)
    module := lsp_module(s, path)
    if os.change_directory(dir) != nil { return "null" }
    args := s.args
    args.pkg_name = module
    resolve_completing = true   // (the resolver records what's in sight at the placeholder)
    serve_check(&s.check, args, serve_stamp(s.args.compiler_dir), &files)
    resolve_completing = false
    lsp_keep(s, &s.dir, dir)
    lsp_keep(s, &s.module, module)
    s.checked = false   // (not the editor's text: the next request checks again)
    session := &s.check.session
    file := lsp_file(s, path)
    if session.checked == nil || file == nil { return "null" }
    // (Where the placeholder starts: after what of the name is typed.)
    spec := fmt.tprintf("%s:%d:%d", filepath.base(path), line, col + 1)
    items := make([dynamic]string)
    for c in completions_at(&build_tree, session.all_files, session.checked.annot, session.checked, file.module, spec) {
        kind, rank := 6, 0
        switch c.kind {
        case .Field:    kind = 5
        case .Method:   kind = 2
        case .Variable: kind = 6
        case .Function: kind, rank = 3, 1
        case .Type:     kind, rank = 22, 1
        case .Module:   kind, rank = 9, 1
        case .Variant:  kind = 20
        case .Keyword:  kind, rank = 14, 2
        }
        append(&items, fmt.tprintf(`{{"label":%s,"kind":%d,"detail":%s,"sortText":%s}}`,
                                   json_str(c.label), kind, json_str(c.detail), json_str(fmt.tprintf("%d%s", rank, c.label))))
    }
    return strings.concatenate({`{"isIncomplete":false,"items":[`, strings.join(items[:], ","), "]}"})
}

// Document symbols: the file's definitions — funs, structs, unions, error
// sets, constants — each its name and its whole.
lsp_symbols :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.symbols { return "null" }
    path := uri_path(json_text(json_at(json_at(params, "textDocument"), "uri")))
    if !lsp_check(s, path) { return "[]" }
    file := lsp_file(s, path)
    if file == nil { return "[]" }
    t := &build_tree
    items := make([dynamic]string)
    for i in 1 ..< len(t.tag) {
        if t.tag[i] != .Define || t.first[i] < file.first_token || t.first[i] >= file.end_token { continue }
        first, last := build_tokens[t.first[i]], build_tokens[t.end[i] - 1]
        text := file.source[first.offset:last.offset + last.len]
        kind := 14   // a constant
        if colons := strings.index(text, "::"); colons >= 0 {
            what := strings.trim_left_space(text[colons + 2:])
            switch {
            case strings.has_prefix(what, "fun"):                                          kind = 12   // a function
            case strings.has_prefix(what, "struct"), strings.has_prefix(what, "class"):    kind = 23   // a struct
            case strings.has_prefix(what, "union"), strings.has_prefix(what, "enum"),
                 strings.has_prefix(what, "error"):                                        kind = 10   // an enum
            }
        }
        append(&items, fmt.tprintf(`{{"name":%s,"kind":%d,"range":%s,"selectionRange":%s}}`,
                                   json_str(token_text(first)), kind, lsp_token_range(s, first, last), lsp_token_range(s, first, first)))
    }
    return strings.concatenate({"[", strings.join(items[:], ","), "]"})
}

// The point a request is about, as `ask at` takes one — "<file>:<line>:
// <col>", its module checked; false when there's none to answer from, or
// the point is on no word (a word ending just before it counts).
lsp_point :: proc(s: ^Lsp, params: json.Value) -> (spec: string, ok: bool) {
    path := uri_path(json_text(json_at(json_at(params, "textDocument"), "uri")))
    position := json_at(params, "position")
    line := json_int(json_at(position, "line")) + 1
    if !lsp_check(s, path) { return }
    src, have := lsp_source(s, path)
    if !have { return }
    _, text := line_at(src, line)
    col := lsp_byte_col(s, text, json_int(json_at(position, "character")))
    if col >= len(text) || !is_word_byte(text[col]) && text[col] != '"' {
        if col == 0 || !is_word_byte(text[col - 1]) { return }
        col -= 1
    }
    return fmt.tprintf("%s:%d:%d", filepath.base(path), line, col + 1), true
}

// --- places -----------------------------------------------------------------

// A token's place, as a Location.
lsp_location :: proc(s: ^Lsp, id: Token_Id) -> string {
    tok := build_tokens[id]
    path := lsp_abs(s, build_files[tok.file].path)
    return fmt.tprintf(`{{"uri":%s,"range":%s}}`, json_str(lsp_uri(s, path)), lsp_token_range(s, tok, tok))
}

// A path's URI: the editor's own spelling of it when it has the file open.
lsp_uri :: proc(s: ^Lsp, path: string) -> string {
    if uri, open := s.open_uris[path_key(path)]; open { return uri }
    return path_uri(path)
}

// From the first token's start to the last's end, as a Range.
lsp_token_range :: proc(s: ^Lsp, first, last: Token) -> string {
    src := build_files[first.file].source
    l0, l1 := token_line(first), token_line(last)
    _, t0 := line_at(src, l0)
    _, t1 := line_at(src, l1)
    return lsp_range(s, t0, l0, token_col(first) - 1, l1, t1, token_col(last) - 1 + int(last.len))
}

// A range from byte c0 of line l0 (its text t0) to byte c1 of line l1, as
// the client counts.
lsp_range :: proc(s: ^Lsp, t0: string, l0, c0: int, l1: int, t1: string, c1: int) -> string {
    a, b := clamp(c0, 0, len(t0)), clamp(c1, 0, len(t1))
    return fmt.tprintf(`{{"start":{{"line":%d,"character":%d}},"end":{{"line":%d,"character":%d}}}}`,
                       l0 - 1, lsp_units(s, t0[:a]), l1 - 1, lsp_units(s, t1[:b]))
}

// How long text is as the client counts: bytes, or UTF-16 units.
lsp_units :: proc(s: ^Lsp, text: string) -> int {
    if s.utf8 { return len(text) }
    n := 0
    for r in text { n += 2 if r >= 0x10000 else 1 }
    return n
}

// The byte of a line the client's `character` is at.
lsp_byte_col :: proc(s: ^Lsp, line: string, character: int) -> int {
    if s.utf8 { return clamp(character, 0, len(line)) }
    n := 0
    for r, i in line {
        if n >= character { return i }
        n += 2 if r >= 0x10000 else 1
    }
    return len(line)
}

// Line n (from 1) of a text: where it starts, and its text without its line end.
line_at :: proc(src: string, n: int) -> (start: int, text: string) {
    line := 1
    for line < n {
        nl := strings.index_byte(src[start:], '\n')
        if nl < 0 { return len(src), "" }
        start += nl + 1
        line += 1
    }
    end := strings.index_byte(src[start:], '\n')
    text = src[start:] if end < 0 else src[start:start + end]
    return start, strings.trim_right(text, "\r")
}

// A path the check holds — relative to its module's directory, or the
// stdlib's, absolute — made absolute.
lsp_abs :: proc(s: ^Lsp, path: string) -> string {
    if filepath.is_abs(path) { return path }
    joined, _ := filepath.join({s.dir, path})
    return joined
}

// The check's file at a path; nil for none.
lsp_file :: proc(s: ^Lsp, path: string) -> ^Source_File {
    key := path_key(path)
    for f in build_files { if path_key(lsp_abs(s, f.path)) == key { return f } }
    return nil
}

// A file's text: as the check read it, else as the editor has it, else on disk.
// The module the file at `path` is checked with: its directory's, as `mara
// build` takes one there (module_here) — a folder's program, the modules it
// uses beside it, checked whole. Where that can't tell — several, none named
// as the directory — the one the file declares, as the editor has it; else
// the directory's name.
lsp_module :: proc(s: ^Lsp, path: string) -> string {
    dir := filepath.dir(path)
    name, problem := module_here("", dir)
    if problem == "" { return name }
    if text, have := lsp_editor_text(s, path); have {
        if own := extract_package_name(text); own != "" { return own }
    }
    return filepath.base(dir)
}

lsp_source :: proc(s: ^Lsp, path: string) -> (string, bool) {
    if f := lsp_file(s, path); f != nil { return f.source, true }
    if text, open := s.overlays[path_key(path)]; open { return text, true }
    data, err := os.read_entire_file_from_path(path, context.allocator)
    if err != nil { return "", false }
    return string(data), true
}

// "<file>:<line>:<col>", a diagnostic's location, apart.
lsp_split_location :: proc(location: string) -> (file: string, line, col: int, ok: bool) {
    b := strings.last_index_byte(location, ':')
    if b <= 0 { return }
    a := strings.last_index_byte(location[:b], ':')
    if a <= 0 { return }
    line, _ = strconv.parse_int(location[a + 1:b])
    col, _ = strconv.parse_int(location[b + 1:])
    return location[:a], line, col, line > 0
}

// A doc comment's line marking it as one the user wrote or approved, in
// their style: left out of what's shown (the Docs panel's DOC_MARK too).
DOC_MARK :: "#magpie"

// The doc comment above a declaration's name: the `//` lines right above its
// line, or a `/* … */` block ending on the line above (`doc_block_words`) —
// their words, a DOC_MARK line left out.
doc_comment_above :: proc(tok: Token) -> string {
    f := build_files[tok.file]
    lines := make([dynamic]string)
    n := token_line(tok) - 1
    if n >= 1 {
        if _, above := line_at(f.source, n); strings.has_suffix(strings.trim_space(above), "*/") {
            return doc_block_words(f.source, n)
        }
    }
    for ; n >= 1; n -= 1 {
        _, text := line_at(f.source, n)
        text = strings.trim_space(text)
        if !strings.has_prefix(text, "//") { break }
        if strings.trim_space(text[2:]) == DOC_MARK { continue }
        inject_at(&lines, 0, strings.trim_space(text[2:]))
    }
    for len(lines) > 0 && lines[len(lines) - 1] == "" { pop(&lines) }
    return strings.join(lines[:], "\n")
}

// A `/* … */` doc comment's words, the block ending on line `last`: from the
// line its `/*` starts (that line's own `/*` its first) — each line less the
// `/*` line's indentation, the `/*` and `*/` left out, blank first and last
// lines dropped, a DOC_MARK line too. "" when no block starting a line ends
// there.
doc_block_words :: proc(source: string, last: int) -> string {
    first := last
    for ; first >= 1; first -= 1 {
        _, text := line_at(source, first)
        if strings.has_prefix(strings.trim_left_space(text), "/*") { break }
    }
    if first < 1 { return "" }
    _, opening := line_at(source, first)
    indent := opening[:len(opening) - len(strings.trim_left_space(opening))]
    lines := make([dynamic]string, context.temp_allocator)
    for n in first ..= last {
        _, text := line_at(source, n)
        text = strings.trim_right_space(text)
        if n == first { text = strings.trim_left_space(text)[2:] } else { text = strings.trim_prefix(text, indent) }
        if n == last { text = strings.trim_right_space(strings.trim_suffix(text, "*/")) }
        if strings.trim_space(text) == DOC_MARK { continue }
        append(&lines, text)
    }
    for len(lines) > 0 && strings.trim_space(lines[0]) == "" { ordered_remove(&lines, 0) }
    for len(lines) > 0 && strings.trim_space(lines[len(lines) - 1]) == "" { pop(&lines) }
    if len(lines) > 0 { lines[0] = strings.trim_space(lines[0]) }
    return strings.join(lines[:], "\n")
}

is_word_byte :: proc(c: u8) -> bool {
    return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

// --- URIs -------------------------------------------------------------------

// A file: URI's path — "file:///C:/Code/x.mara" is C:\Code\x.mara on
// Windows — its %XX escapes decoded.
uri_path :: proc(uri: string) -> string {
    s := strings.trim_prefix(uri, "file://")
    b := strings.builder_make()
    for i := 0; i < len(s); i += 1 {
        if s[i] == '%' && i + 2 < len(s) {
            if v, ok := strconv.parse_u64_of_base(s[i + 1:i + 3], 16); ok {
                strings.write_byte(&b, u8(v))
                i += 2
                continue
            }
        }
        strings.write_byte(&b, s[i])
    }
    path := strings.to_string(b)
    when ODIN_OS == .Windows {
        if len(path) >= 3 && path[0] == '/' && path[2] == ':' { path = path[1:] }
        path, _ = strings.replace_all(path, "/", "\\")
    }
    return path
}

// A path's file: URI.
path_uri :: proc(path: string) -> string {
    p, _ := strings.replace_all(path, "\\", "/")
    b := strings.builder_make()
    strings.write_string(&b, "file://")
    if !strings.has_prefix(p, "/") { strings.write_byte(&b, '/') }
    for c in transmute([]byte)p {
        if is_word_byte(c) || strings.index_byte("-.~/:", c) >= 0 {
            strings.write_byte(&b, c)
        } else {
            fmt.sbprintf(&b, "%%%02X", c)
        }
    }
    return strings.to_string(b)
}

// --- JSON -------------------------------------------------------------------

json_at :: proc(v: json.Value, key: string) -> json.Value {
    if o, ok := v.(json.Object); ok { return o[key] }
    return nil
}

json_text :: proc(v: json.Value) -> string {
    s, _ := v.(json.String)
    return s
}

json_int :: proc(v: json.Value) -> int {
    #partial switch x in v {
    case json.Integer: return int(x)
    case json.Float:   return int(x)
    }
    return 0
}

json_bool :: proc(v: json.Value, otherwise: bool) -> bool {
    b, ok := v.(json.Boolean)
    return b if ok else otherwise
}

// A request's id, as it came: a number or a string.
json_id :: proc(v: json.Value) -> string {
    #partial switch x in v {
    case json.Integer: return fmt.tprintf("%d", x)
    case json.Float:   return fmt.tprintf("%v", x)
    case json.String:  return json_str(x)
    }
    return "null"
}

// A string as JSON: quoted, escaped — and UTF-8, as JSON must be: a byte
// that's no character's (a file's, say) is U+FFFD.
json_str :: proc(s: string) -> string {
    b := strings.builder_make()
    strings.write_byte(&b, '"')
    for r in s {
        switch r {
        case '"':  strings.write_string(&b, `\"`)
        case '\\': strings.write_string(&b, `\\`)
        case '\n': strings.write_string(&b, `\n`)
        case '\r': strings.write_string(&b, `\r`)
        case '\t': strings.write_string(&b, `\t`)
        case:
            if r < 0x20 { fmt.sbprintf(&b, `\u%04x`, int(r)) } else { strings.write_rune(&b, r) }
        }
    }
    strings.write_byte(&b, '"')
    return strings.to_string(b)
}
