package mara

import "core:fmt"
import "core:mem/virtual"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Moved fields (mara lsp). The server keeps, from the last check that
// parsed, each struct declared in the editor's open files — its fields in
// order, its body as written — and every literal of it that gives its
// fields by position: where its entries are, kept up with each edit
// (lsp_map_edit), and each one's text as written. A struct whose fields come
// back in another order — the same names — while some of those literals
// still read as written is having its fields moved: each such literal is
// said to give them in the old order (lsp_publish), and a code action puts
// them all in the new one, or the fields back (lsp_code_actions). Said even
// when the literal still checks: two fields of one type swapped would
// quietly mean another thing.
// ---------------------------------------------------------------------------

// A literal giving a kept struct's fields by position: from its first
// entry's start to its last's end, and each entry's text as written.
Lsp_Literal :: struct {
    path:    string,
    at, end: int,
    entries: []string,
}

// A struct as the last check that parsed saw it — or, while its fields are
// being moved (or one is cut, not put back yet), as it was before: its
// fields' order then, its literals then.
Lsp_Struct :: struct {
    name:     string,
    path:     string,
    name_at:  int,              // its name's place
    body_at:  int,              // its body: after its `{` ...
    body_end: int,              // ... to its `}`
    body:     string,           // ... as it was written
    fields:   []string,         // its fields, in order
    literals: [dynamic]Lsp_Literal,
    moved:    []string,         // being moved: its fields' order now; nil when not
}

// The structs kept, in an arena of their own: let go whole when kept again.
Lsp_Structs :: struct {
    arena:   virtual.Arena,
    structs: [dynamic]Lsp_Struct,
}

// The structs kept again, from the check just made — unless it didn't
// parse. A struct whose literals still read as the kept ones were written,
// its fields now in another order (being moved) or fewer or more of them
// (one cut, not put back yet), keeps what was kept of it. Its fields
// renamed or retyped in place, as many as before: what the check says.
lsp_keep_structs :: proc(s: ^Lsp) {
    session := &s.check.session
    if session.checked == nil { return }
    for d in s.check.diagnostics { if d.kind == .Parse_Error { return } }
    fresh: Lsp_Structs
    if virtual.arena_init_growing(&fresh.arena) != nil { return }
    {
        context.allocator = virtual.arena_allocator(&fresh.arena)
        fresh.structs = make([dynamic]Lsp_Struct)
        lsp_fresh_structs(s, &fresh.structs)
        for &f in fresh.structs {
            old := lsp_kept_struct(s, f.name, f.path)
            if old == nil || slice.equal(old.fields, f.fields) || lsp_as_written(s, old^) == 0 { continue }
            same_count := len(old.fields) == len(f.fields)
            if same_count && !lsp_same_names(old.fields, f.fields) { continue }
            kept := Lsp_Struct{name = f.name, path = f.path, name_at = f.name_at, body_at = f.body_at, body_end = f.body_end,
                               body = strings.clone(old.body), fields = lsp_clone_names(old.fields)}
            if same_count { kept.moved = f.fields }
            kept.literals = make([dynamic]Lsp_Literal)
            for l in old.literals {
                append(&kept.literals, Lsp_Literal{path = strings.clone(l.path), at = l.at, end = l.end, entries = lsp_clone_names(l.entries)})
            }
            f = kept
        }
    }
    virtual.arena_destroy(&s.structs.arena)
    s.structs = fresh
}

// The check's structs declared in the editor's open files, and their
// literals that give fields by position, all of them (any file's).
@(private="file")
lsp_fresh_structs :: proc(s: ^Lsp, out: ^[dynamic]Lsp_Struct) {
    a := s.check.session.checked.annot
    t := &build_tree
    index := make(map[^Type_Scope]int, allocator = context.temp_allocator)
    for key, ts in a.decls {
        if ts == nil || ts.kind != .Struct || ts.is_module || ts.is_union_variant { continue }
        _, n := annot_split(key)
        if t.tag[n] != .Struct_Def { continue }
        first := build_tokens[t.first[n]]
        file := build_files[first.file]
        path := lsp_abs(s, file.path)
        if path_key(path) not_in s.overlays { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        // (Its name: before its `::`; its body: its braces' inside.)
        name_at := int(first.offset)
        if t.first[n] >= 2 && token_text(build_tokens[t.first[n] - 2]) == name { name_at = int(build_tokens[t.first[n] - 2].offset) }
        open, close := -1, -1
        for k := t.first[n]; k < t.end[n]; k += 1 {
            tk := build_tokens[k]
            if tk.kind == .Left_Brace && open < 0 { open = int(tk.offset + tk.len) }
            if tk.kind == .Right_Brace { close = int(tk.offset) }
        }
        if open < 0 || close < open { continue }
        fields := make([]string, len(ts.fields) - first_user_field(ts))
        for f, i in ts.fields[first_user_field(ts):] { fields[i] = strings.clone(f.name) }
        append(out, Lsp_Struct{name = strings.clone(name), path = strings.clone(path), name_at = name_at,
                               body_at = open, body_end = close, body = strings.clone(file.source[open:close]),
                               fields = fields, literals = make([dynamic]Lsp_Literal)})
        index[ts] = len(out) - 1
    }
    if len(index) == 0 { return }
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)   // (a generic's instances: one literal)
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            if t.tag[n] != .Literal || seen[t.first[n]] { continue }
            ts, is_scope := distinct_base(annot_type(a, Instance_Id(i), n)).(^Type_Scope)
            if !is_scope { continue }
            at, kept := index[ts]
            if !kept { continue }
            entries := tree_list(t, t.b[n])
            if len(entries) == 0 || len(entries) != len(out[at].fields) || t.tag[entries[0]] == .Named_Entry { continue }
            seen[t.first[n]] = true
            first, last := build_tokens[t.first[entries[0]]], build_tokens[t.end[entries[len(entries) - 1]] - 1]
            src := build_files[first.file].source
            texts := make([]string, len(entries))
            for e, j in entries {
                a0, a1 := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
                texts[j] = strings.clone(src[a0.offset:a1.offset + a1.len])
            }
            append(&out[at].literals, Lsp_Literal{path = strings.clone(lsp_abs(s, build_files[first.file].path)),
                                                  at = int(first.offset), end = int(last.offset + last.len), entries = texts})
        }
    }
}

// The kept struct of a name declared in a file; nil for none.
@(private="file")
lsp_kept_struct :: proc(s: ^Lsp, name, path: string) -> ^Lsp_Struct {
    for &st in s.structs.structs {
        if st.name == name && path_key(st.path) == path_key(path) { return &st }
    }
    return nil
}

// Whether two lists of names have the same names, in any order.
@(private="file")
lsp_same_names :: proc(a, b: []string) -> bool {
    if len(a) != len(b) { return false }
    for x in a { if !slice.contains(b, x) { return false } }
    return true
}

@(private="file")
lsp_clone_names :: proc(names: []string) -> []string {
    out := make([]string, len(names))
    for n, i in names { out[i] = strings.clone(n) }
    return out
}

// How many of a struct's kept literals still read as they were written.
@(private="file")
lsp_as_written :: proc(s: ^Lsp, st: Lsp_Struct) -> int {
    n := 0
    for l in st.literals { if lsp_reads_as_written(s, l) { n += 1 } }
    return n
}

// Whether a kept literal's entries, in the editor's text now, are the ones
// it was written with, in that order.
lsp_reads_as_written :: proc(s: ^Lsp, l: Lsp_Literal) -> bool {
    text, ok := lsp_editor_text(s, l.path)
    if !ok || l.at < 0 || l.end > len(text) || l.at > l.end { return false }
    slots := lsp_entry_slots(text[l.at:l.end])
    if len(slots) != len(l.entries) { return false }
    for sl, i in slots {
        if text[l.at + sl[0]:l.at + sl[1]] != l.entries[i] { return false }
    }
    return true
}

// A literal's entries in its text (from its first's start to its last's
// end): each one's start and end, its spaces left out — parted by the
// commas and line ends not inside brackets, braces, parentheses, quotes.
lsp_entry_slots :: proc(text: string) -> [][2]int {
    out := make([dynamic][2]int)
    depth := 0
    start := 0
    add :: proc(out: ^[dynamic][2]int, text: string, a, b: int) {
        a, b := a, b
        for a < b && strings.is_space(rune(text[a])) { a += 1 }
        for b > a && strings.is_space(rune(text[b - 1])) { b -= 1 }
        if b > a { append(out, [2]int{a, b}) }
    }
    for i := 0; i < len(text); i += 1 {
        switch text[i] {
        case '(', '[', '{': depth += 1
        case ')', ']', '}': depth -= 1
        case '"', '\'':
            q := text[i]
            i += 1
            for i < len(text) && text[i] != q {
                if text[i] == '\\' { i += 1 }
                i += 1
            }
        case ',', '\n':
            if depth == 0 {
                add(&out, text, start, i)
                start = i + 1
            }
        }
    }
    add(&out, text, start, len(text))
    return out[:]
}

// A kept literal said to give its struct's fields in the old order: as
// written still, and not the same written in the new one (its entries all
// alike).
lsp_literal_moved :: proc(s: ^Lsp, st: Lsp_Struct, l: Lsp_Literal) -> bool {
    if st.moved == nil || !lsp_reads_as_written(s, l) { return false }
    for name, i in st.moved {
        j, _ := slice.linear_search(st.fields, name)
        if l.entries[j] != l.entries[i] { return true }
    }
    return false
}

// A kept literal's entries in the new order: each one's text where the
// field its value is for now is — the text between them as it is.
lsp_literal_reordered :: proc(s: ^Lsp, st: Lsp_Struct, l: Lsp_Literal, text: string) -> string {
    stretch := text[l.at:l.end]
    slots := lsp_entry_slots(stretch)
    b := strings.builder_make()
    from := 0
    for name, i in st.moved {
        j, _ := slice.linear_search(st.fields, name)
        strings.write_string(&b, stretch[from:slots[i][0]])
        strings.write_string(&b, stretch[slots[j][0]:slots[j][1]])
        from = slots[i][1]
    }
    strings.write_string(&b, stretch[from:])
    return strings.to_string(b)
}

// The fields' names, as a list for a message: "kind, file, offset, len".
lsp_field_list :: proc(names: []string) -> string {
    return strings.join(names, ", ", context.temp_allocator)
}

// The moved fields' diagnostics, each file's, added to `by_uri`: each
// literal still in the old order, and the struct (how many there are).
lsp_moved_diagnostics :: proc(s: ^Lsp, by_uri: ^map[string][dynamic]string) {
    for st in s.structs.structs {
        if st.moved == nil { continue }
        left := 0
        for l in st.literals {
            if !lsp_literal_moved(s, st, l) { continue }
            left += 1
            text, _ := lsp_editor_text(s, l.path)
            end := l.end
            if nl := strings.index_byte(text[l.at:l.end], '\n'); nl >= 0 { end = l.at + nl }   // (its first line)
            message := fmt.tprintf("%s's fields were reordered (%s), but this literal still gives them in the old order (%s)",
                                   st.name, lsp_field_list(st.moved), lsp_field_list(st.fields))
            lsp_add_diagnostic(s, by_uri, l.path, text, l.at, end, message)
        }
        if left == 0 { continue }
        text, _ := lsp_editor_text(s, st.path)
        message := fmt.tprintf("%s's fields were reordered: %d literal%s still give%s them in the old order. A code action puts them in the new one, or the fields back.",
                               st.name, left, "" if left == 1 else "s", "s" if left == 1 else "")
        lsp_add_diagnostic(s, by_uri, st.path, text, st.name_at, st.name_at + len(st.name), message)
    }
}

// An error from byte a to b of a file's text, added to its diagnostics.
@(private="file")
lsp_add_diagnostic :: proc(s: ^Lsp, by_uri: ^map[string][dynamic]string, path, text: string, a, b: int, message: string) {
    uri := lsp_uri(s, path)
    items := by_uri[uri]
    append(&items, fmt.tprintf(`{{"range":{{"start":%s,"end":%s}},"severity":1,"source":"mara","message":%s}}`,
                               lsp_position_at(s, text, a), lsp_position_at(s, text, b), json_str(message)))
    by_uri[uri] = items
}

// The moved fields' code actions for the lines asked about in a file (its
// struct's name or body there, or a literal still in the old order): its
// literals put in the new order, or its fields put back.
lsp_moved_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    key := path_key(path)
    line_of :: proc(text: string, at: int) -> int { return strings.count(text[:clamp(at, 0, len(text))], "\n") }
    for st in s.structs.structs {
        if st.moved == nil { continue }
        on := path_key(st.path) == key && line_of(here, st.name_at) <= l1 && line_of(here, st.body_end) >= l0
        left := 0
        by_uri := make(map[string][dynamic]string)
        for l in st.literals {
            if !lsp_literal_moved(s, st, l) { continue }
            left += 1
            text, _ := lsp_editor_text(s, l.path)
            if path_key(l.path) == key && line_of(here, l.at) <= l1 && line_of(here, l.end) >= l0 { on = true }
            uri := lsp_uri(s, l.path)
            edits := by_uri[uri]
            append(&edits, lsp_text_edit(s, text, l.at, l.end, lsp_literal_reordered(s, st, l, text)))
            by_uri[uri] = edits
        }
        if left == 0 || !on { continue }
        title := fmt.tprintf("Put the %d %s literal%s in the new order (%s)", left, st.name, "" if left == 1 else "s", lsp_field_list(st.moved))
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","isPreferred":true,"edit":%s}}`, json_str(title), lsp_workspace_edit(by_uri)))
        // Or its fields as they were.
        text, _ := lsp_editor_text(s, st.path)
        back := make(map[string][dynamic]string)
        put_back := make([dynamic]string)
        append(&put_back, lsp_text_edit(s, text, st.body_at, st.body_end, st.body))
        back[lsp_uri(s, st.path)] = put_back
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","edit":%s}}`,
                                    json_str(fmt.tprintf("Put %s's fields back in the old order (%s)", st.name, lsp_field_list(st.fields))), lsp_workspace_edit(back)))
    }
}
