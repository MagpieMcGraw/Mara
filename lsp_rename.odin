package mara

import "core:encoding/json"
import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:path/filepath"
import "core:strings"

// ---------------------------------------------------------------------------
// Renames (mara lsp). The server keeps, from the last check that parsed,
// each declaration in the editor's open files and every name referring to
// it — their places in the editor's text, kept up with each edit
// (lsp_map_edit). A declaration whose place the editor's text now spells
// another name at, while its uses still spell the old one, is being
// renamed (lsp_renamings): a code action offers to rename its uses too, or
// to put the name back — offered, never asked. `textDocument/rename`
// renames a name and every use of it outright.
// ---------------------------------------------------------------------------

// A place in a file: its path, and a byte of the editor's text of it.
Lsp_Place :: struct {
    path: string,
    at:   int,
}

// A declaration as the last check that parsed saw it: its name, its place,
// its uses'.
Lsp_Name :: struct {
    name: string,
    decl: Lsp_Place,
    uses: [dynamic]Lsp_Place,
}

// The names kept, in an arena of their own: let go whole when kept again.
Lsp_Names :: struct {
    arena: virtual.Arena,
    names: [dynamic]Lsp_Name,
}

// A kept declaration being renamed: from its old name to the one its place
// spells now, `left` of its uses still spelling the old.
Lsp_Renaming :: struct {
    index: int,     // in names
    from:  string,
    to:    string,
    left:  int,
}

// The names kept again, from the check just made — unless it didn't parse:
// what it knows of the names then may be part of them. A declaration being
// renamed keeps what was kept of it: its old name, its uses — the check
// sees neither now.
lsp_keep_names :: proc(s: ^Lsp) {
    session := &s.check.session
    if session.checked == nil { return }
    for d in s.check.diagnostics { if d.kind == .Parse_Error { return } }
    renaming := lsp_renamings(s)
    fresh: Lsp_Names
    if virtual.arena_init_growing(&fresh.arena) != nil { return }
    {
        context.allocator = virtual.arena_allocator(&fresh.arena)
        fresh.names = make([dynamic]Lsp_Name)
        for decl, uses in references_by_declaration(&build_tree, session.checked.annot) {
            tok := build_tokens[decl]
            path := lsp_abs(s, build_files[tok.file].path)
            if path_key(path) not_in s.overlays { continue }   // (the editor's open files': what it renames)
            n := Lsp_Name{name = strings.clone(token_text(tok)), decl = {strings.clone(path), int(tok.offset)}}
            for u in uses {
                ut := build_tokens[u]
                append(&n.uses, Lsp_Place{strings.clone(lsp_abs(s, build_files[ut.file].path)), int(ut.offset)})
            }
            append(&fresh.names, n)
        }
        for r in renaming {
            old := s.names.names[r.index]
            n := Lsp_Name{name = strings.clone(old.name), decl = {strings.clone(old.decl.path), old.decl.at}}
            for u in old.uses { append(&n.uses, Lsp_Place{strings.clone(u.path), u.at}) }
            append(&fresh.names, n)
        }
    }
    virtual.arena_destroy(&s.names.arena)
    s.names = fresh
}

// An edit of an open file — its text before and after: one stretch replaced,
// found by what the two share at their ends — the kept places in it moved
// with it (the names', the orders': lsp_moves.odin); a place in the
// stretch replaced, to its start.
lsp_map_edit :: proc(s: ^Lsp, key: string, before, after: string) {
    p := 0
    for p < len(before) && p < len(after) && before[p] == after[p] { p += 1 }
    tail := 0
    for tail < len(before) - p && tail < len(after) - p && before[len(before) - 1 - tail] == after[len(after) - 1 - tail] { tail += 1 }
    old_end, delta := len(before) - tail, len(after) - len(before)
    move :: proc(at, p, old_end, delta: int) -> int {
        if at < p { return at }
        if at >= old_end { return at + delta }
        return p
    }
    for &n in s.names.names {
        if path_key(n.decl.path) == key { n.decl.at = move(n.decl.at, p, old_end, delta) }
        for &u in n.uses {
            if path_key(u.path) == key { u.at = move(u.at, p, old_end, delta) }
        }
    }
    for &o in s.orders.orders {
        if path_key(o.path) == key {
            o.name_at = move(o.name_at, p, old_end, delta)
            o.span_at = move(o.span_at, p, old_end, delta)
            o.span_end = move(o.span_end, p, old_end, delta)
        }
        for &l in o.sites {
            if path_key(l.path) == key { l.at, l.end = move(l.at, p, old_end, delta), move(l.end, p, old_end, delta) }
        }
    }
}

// The kept declarations being renamed: the editor's text spells another
// name at one's place — a name, no keyword — and some of its uses still
// spell the old.
lsp_renamings :: proc(s: ^Lsp) -> []Lsp_Renaming {
    out := make([dynamic]Lsp_Renaming)
    for n, i in s.names.names {
        text, ok := lsp_editor_text(s, n.decl.path)
        if !ok { continue }
        _, word := word_around(text, n.decl.at)
        if word == "" || word == n.name || !is_name_start(word[0]) || is_keyword(word) { continue }
        left := 0
        for u in n.uses {
            if ut, have := lsp_editor_text(s, u.path); have {
                if _, w := word_around(ut, u.at); w == n.name { left += 1 }
            }
        }
        if left > 0 { append(&out, Lsp_Renaming{i, n.name, word, left}) }
    }
    return out[:]
}

// Code actions, for a declaration being renamed with its declaration or a
// use on the lines asked about, in this file: its uses renamed too, or its
// name put back. And fields, results, params being moved (lsp_moved_actions);
// at a fun's name, its body written out elsewhere called (lsp_shape_actions);
// at an if, or a fun's name, its one-statement ifs with `do` (lsp_do_actions).
lsp_code_actions :: proc(s: ^Lsp, params: json.Value) -> string {
    if !s.renames { return "[]" }
    path := uri_path(json_text(json_at(json_at(params, "textDocument"), "uri")))
    key := path_key(path)
    asked := json_at(params, "range")
    l0 := json_int(json_at(json_at(asked, "start"), "line"))
    l1 := json_int(json_at(json_at(asked, "end"), "line"))
    lsp_check(s, path)   // (the names kept up to date with what's changed)
    here, have := lsp_editor_text(s, path)
    if !have { return "[]" }
    on_lines :: proc(text: string, at, l0, l1: int) -> bool {
        line := strings.count(text[:clamp(at, 0, len(text))], "\n")
        return line >= l0 && line <= l1
    }
    actions := make([dynamic]string)
    for r in lsp_renamings(s) {
        n := s.names.names[r.index]
        on := path_key(n.decl.path) == key && on_lines(here, n.decl.at, l0, l1)
        for u in n.uses { if !on && path_key(u.path) == key && on_lines(here, u.at, l0, l1) { on = true } }
        if !on { continue }
        // Its uses that still spell the old name: the new one.
        by_uri := make(map[string][dynamic]string)
        for u in n.uses {
            text, ok := lsp_editor_text(s, u.path)
            if !ok { continue }
            start, w := word_around(text, u.at)
            if w != r.from { continue }
            uri := lsp_uri(s, u.path)
            edits := by_uri[uri]
            append(&edits, lsp_text_edit(s, text, start, start + len(w), r.to))
            by_uri[uri] = edits
        }
        title := fmt.tprintf("Rename the %d use%s of %s to %s", r.left, "" if r.left == 1 else "s", r.from, r.to)
        append(&actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","isPreferred":true,"edit":%s}}`, json_str(title), lsp_workspace_edit(by_uri)))
        // Or the declaration's name as it was.
        start, w := word_around(here, n.decl.at)
        back := make(map[string][dynamic]string)
        put_back := make([dynamic]string)
        append(&put_back, lsp_text_edit(s, here, start, start + len(w), r.from))
        back[lsp_uri(s, path)] = put_back
        append(&actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","edit":%s}}`,
                                     json_str(fmt.tprintf("Put the name back: %s", r.from)), lsp_workspace_edit(back)))
    }
    lsp_moved_actions(s, path, here, l0, l1, &actions)   // (fields, results, params moved: lsp_moves.odin)
    lsp_shape_actions(s, path, here, l0, l1, &actions)   // (a fun's body written out: shapes.odin)
    lsp_do_actions(s, path, here, l0, l1, &actions)      // (one-statement ifs written with `do`: shapes.odin)
    return strings.concatenate({"[", strings.join(actions[:], ","), "]"})
}

// Rename: the name at the point, its declaration and every use, to the new
// name; "" and why not, when there's none or the new name is no name.
lsp_rename :: proc(s: ^Lsp, params: json.Value) -> (result: string, refused: string) {
    if !s.renames { return "null", "" }
    to := json_text(json_at(params, "newName"))
    if to == "" || !is_name_start(to[0]) || is_keyword(to) { return "", fmt.tprintf("mara lsp: '%s' isn't a name", to) }
    for c in transmute([]byte)to { if !is_word_byte(c) { return "", fmt.tprintf("mara lsp: '%s' isn't a name", to) } }
    spec, ok := lsp_point(s, params)
    if !ok { return "null", "" }
    session := &s.check.session
    r, _, refers := point_reference(&build_tree, session.all_files, session.checked.annot, spec)
    if !refers || r.decl == 0 { return "", "mara lsp: nothing here to rename (a builtin's no source to rename)" }
    by_uri := make(map[string][dynamic]string)
    for id in references_to(&build_tree, session.checked.annot, r.decl) {
        tok := build_tokens[id]
        f := build_files[tok.file]
        uri := lsp_uri(s, lsp_abs(s, f.path))
        edits := by_uri[uri]
        append(&edits, lsp_text_edit(s, f.source, int(tok.offset), int(tok.offset + tok.len), to))
        by_uri[uri] = edits
    }
    return lsp_workspace_edit(by_uri), ""
}

// --- edits ------------------------------------------------------------------

// A TextEdit: bytes a to b of the text, replaced.
lsp_text_edit :: proc(s: ^Lsp, text: string, a, b: int, with: string) -> string {
    return fmt.tprintf(`{{"range":{{"start":%s,"end":%s}},"newText":%s}}`, lsp_position_at(s, text, a), lsp_position_at(s, text, b), json_str(with))
}

// A WorkspaceEdit: each file's edits.
lsp_workspace_edit :: proc(by_uri: map[string][dynamic]string) -> string {
    files := make([dynamic]string)
    for uri, edits in by_uri {
        append(&files, fmt.tprintf("%s:[%s]", json_str(uri), strings.join(edits[:], ",")))
    }
    return strings.concatenate({`{"changes":{`, strings.join(files[:], ","), "}}"})
}

// A byte of a text as a Position, as the client counts.
lsp_position_at :: proc(s: ^Lsp, text: string, at: int) -> string {
    at := clamp(at, 0, len(text))
    line := strings.count(text[:at], "\n")
    start := strings.last_index_byte(text[:at], '\n') + 1
    return fmt.tprintf(`{{"line":%d,"character":%d}}`, line, lsp_units(s, text[start:at]))
}

// The editor's text of a file: as it has it open, else as it is on disk.
lsp_editor_text :: proc(s: ^Lsp, path: string) -> (string, bool) {
    if text, open := s.overlays[path_key(path)]; open { return text, true }
    data, err := os.read_entire_file_from_path(path, context.allocator)
    if err != nil { return "", false }
    return string(data), true
}

// The name around a byte of a text: where it starts — back to its first
// letter — and it; "" when the byte is in none.
word_around :: proc(text: string, at: int) -> (start: int, word: string) {
    if at < 0 || at > len(text) { return at, "" }
    start = at
    for start > 0 && is_word_byte(text[start - 1]) { start -= 1 }
    end := at
    for end < len(text) && is_word_byte(text[end]) { end += 1 }
    return start, text[start:end]
}

is_name_start :: proc(c: u8) -> bool {
    return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

// Whether a word is one of Mara's keywords: no name.
is_keyword :: proc(word: string) -> bool {
    for kw in COMPLETION_KEYWORDS { if kw == word { return true } }
    return false
}
