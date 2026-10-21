package mara

import "core:fmt"
import "core:mem/virtual"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Moved fields (mara lsp). The server keeps, from each check that parsed,
// each struct declared in the editor's open files — its fields in order —
// and every literal of it that gives its fields by position: each entry's
// text, and the field that text is for. A literal is known by its entries:
// the next check's literal with the same texts, in any order, is it (in the
// order literals come) — so what it's for survives its entries moved, by a
// code action, by hand, by an undo. Its texts changed (a value edited), or
// new, it's taken as written for its struct's order then. A literal whose
// entries, as they are now, give its struct's fields in another order than
// the struct has — the same fields — is said to (lsp_publish), and a code
// action puts each in the struct's order, or the struct's fields back as
// they were when every literal last fit (lsp_code_actions). Said even when
// the literal still checks: two fields of one type swapped would quietly
// mean another thing. A field renamed in place is followed (its literals'
// texts are for it still); a field cut and not yet put back changes
// nothing known.
// ---------------------------------------------------------------------------

// A literal giving a kept struct's fields by position: where its entries
// are (the first's start to the last's end), each one's text, and the field
// each text is for — nil when not known (its entries weren't as many as
// its struct's fields).
Lsp_Literal :: struct {
    path:    string,
    at, end: int,
    texts:   []string,
    fields:  []string,
}

// A struct as the last check that saw it had it, and its body as it was
// when its literals last all fit it: what's put back.
Lsp_Struct :: struct {
    name:        string,
    path:        string,
    name_at:     int,       // its name's place
    body_at:     int,       // its body: after its `{` ...
    body_end:    int,       // ... to its `}`
    fields:      []string,  // its fields, in order
    body:        string,    // its body when its literals last all fit it ("" for never) ...
    body_fields: []string,  // ... its fields' order then
    literals:    [dynamic]Lsp_Literal,
}

// The structs kept, in an arena of their own: let go whole when kept again.
Lsp_Structs :: struct {
    arena:   virtual.Arena,
    structs: [dynamic]Lsp_Struct,
}

// The structs kept again, from the check just made — unless it didn't
// parse. Each literal keeps what was known of the one with its texts; a
// struct the check didn't see (another module's check), its file still
// open, is kept as it was.
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
            renames := lsp_field_renames(old, f.fields)
            next := 0   // (old's literals gone past, in order)
            for &l in f.literals {
                if old != nil {
                    for k in next ..< len(old.literals) {
                        ol := old.literals[k]
                        if path_key(ol.path) != path_key(l.path) || !lsp_same_texts(ol.texts, l.texts) { continue }
                        next = k + 1
                        if ol.fields != nil {
                            l.texts = lsp_clone_names(ol.texts)
                            l.fields = lsp_clone_names(ol.fields)
                            for &name in l.fields { if to, renamed := renames[name]; renamed { name = to } }
                        }
                        break
                    }
                }
                // (New, its values changed, or not known: as written for its struct's order now.)
                if l.fields == nil && len(l.texts) == len(f.fields) { l.fields = lsp_clone_names(f.fields) }
            }
            // (Its body now, what's put back, when every literal fits it.)
            fits := true
            for l in f.literals {
                order := lsp_literal_order(s, l)
                if order == nil || !slice.equal(order, f.fields) { fits = false }
            }
            if fits {
                text, _ := lsp_editor_text(s, f.path)
                if f.body_end <= len(text) { f.body = strings.clone(text[f.body_at:f.body_end]) }
                f.body_fields = lsp_clone_names(f.fields)
            } else if old != nil {
                f.body = strings.clone(old.body)
                f.body_fields = lsp_clone_names(old.body_fields)
            }
        }
        for st in s.structs.structs {
            if path_key(st.path) not_in s.overlays || lsp_find_struct(fresh.structs[:], st.name, st.path) != nil { continue }
            append(&fresh.structs, lsp_struct_clone(st))
        }
    }
    virtual.arena_destroy(&s.structs.arena)
    s.structs = fresh
}

// The check's structs declared in the editor's open files, and their
// literals that give fields by position, all of them (any file's), in the
// order they're written.
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
                               body_at = open, body_end = close, fields = fields, literals = make([dynamic]Lsp_Literal)})
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
            if len(entries) == 0 || t.tag[entries[0]] == .Named_Entry { continue }
            // (`Token{0}`: its zero, not its first field.)
            if len(entries) == 1 && len(out[at].fields) != 1 { continue }
            seen[t.first[n]] = true
            first, last := build_tokens[t.first[entries[0]]], build_tokens[t.end[entries[len(entries) - 1]] - 1]
            src := build_files[first.file].source
            texts := make([]string, len(entries))
            for e, j in entries {
                a0, a1 := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
                texts[j] = strings.clone(src[a0.offset:a1.offset + a1.len])
            }
            append(&out[at].literals, Lsp_Literal{path = strings.clone(lsp_abs(s, build_files[first.file].path)),
                                                  at = int(first.offset), end = int(last.offset + last.len), texts = texts})
        }
    }
    for &st in out {
        slice.sort_by(st.literals[:], proc(x, y: Lsp_Literal) -> bool { return x.path < y.path || x.path == y.path && x.at < y.at })
    }
}

// The fields renamed in place since the struct was kept: the same count,
// a name at a place where the other's isn't anywhere — the old's to the new.
@(private="file")
lsp_field_renames :: proc(old: ^Lsp_Struct, fields: []string) -> map[string]string {
    out := make(map[string]string, allocator = context.temp_allocator)
    if old == nil || len(old.fields) != len(fields) { return out }
    for name, i in old.fields {
        if fields[i] != name && !slice.contains(fields, name) && !slice.contains(old.fields, fields[i]) { out[name] = fields[i] }
    }
    return out
}

@(private="file")
lsp_kept_struct :: proc(s: ^Lsp, name, path: string) -> ^Lsp_Struct {
    return lsp_find_struct(s.structs.structs[:], name, path)
}

@(private="file")
lsp_find_struct :: proc(structs: []Lsp_Struct, name, path: string) -> ^Lsp_Struct {
    for &st in structs {
        if st.name == name && path_key(st.path) == path_key(path) { return &st }
    }
    return nil
}

@(private="file")
lsp_struct_clone :: proc(st: Lsp_Struct) -> Lsp_Struct {
    out := st
    out.name, out.path, out.body = strings.clone(st.name), strings.clone(st.path), strings.clone(st.body)
    out.fields, out.body_fields = lsp_clone_names(st.fields), lsp_clone_names(st.body_fields)
    out.literals = make([dynamic]Lsp_Literal)
    for l in st.literals {
        append(&out.literals, Lsp_Literal{path = strings.clone(l.path), at = l.at, end = l.end,
                                          texts = lsp_clone_names(l.texts), fields = lsp_clone_names(l.fields)})
    }
    return out
}

@(private="file")
lsp_clone_names :: proc(names: []string) -> []string {
    if names == nil { return nil }
    out := make([]string, len(names))
    for n, i in names { out[i] = strings.clone(n) }
    return out
}

// Whether two lists of names have the same names, in any order.
@(private="file")
lsp_same_names :: proc(a, b: []string) -> bool {
    if len(a) != len(b) { return false }
    for x in a { if !slice.contains(b, x) { return false } }
    return true
}

// Whether two literals' entries are the same texts, in any order.
@(private="file")
lsp_same_texts :: proc(a, b: []string) -> bool {
    if len(a) != len(b) { return false }
    used := make([]bool, len(b), context.temp_allocator)
    outer: for x in a {
        for y, j in b {
            if !used[j] && x == y {
                used[j] = true
                continue outer
            }
        }
        return false
    }
    return true
}

// The fields a kept literal's entries give, in the order its entries are
// in the editor's text now (each text's field, an alike text's taken in
// turn); nil when that's not known — its entries' texts aren't the ones
// known, or what they're for isn't.
lsp_literal_order :: proc(s: ^Lsp, l: Lsp_Literal) -> []string {
    if l.fields == nil { return nil }
    text, ok := lsp_editor_text(s, l.path)
    if !ok || l.at < 0 || l.end > len(text) || l.at > l.end { return nil }
    slots := lsp_entry_slots(text[l.at:l.end])
    if len(slots) != len(l.texts) { return nil }
    out := make([]string, len(slots), context.temp_allocator)
    used := make([]bool, len(l.texts), context.temp_allocator)
    outer: for sl, i in slots {
        here := text[l.at + sl[0]:l.at + sl[1]]
        for t, j in l.texts {
            if !used[j] && t == here {
                used[j] = true
                out[i] = l.fields[j]
                continue outer
            }
        }
        return nil
    }
    return out
}

// A literal's entries in its text (from its first's start to its last's
// end): each one's start and end, its spaces left out — parted by the
// commas and line ends not inside brackets, braces, parentheses, quotes.
lsp_entry_slots :: proc(text: string) -> [][2]int {
    out := make([dynamic][2]int, context.temp_allocator)
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

// A kept literal giving its struct's fields in another order than its
// struct has them now (the same fields): that order; nil when it doesn't.
lsp_literal_moved :: proc(s: ^Lsp, st: Lsp_Struct, l: Lsp_Literal) -> []string {
    order := lsp_literal_order(s, l)
    if order == nil || !lsp_same_names(order, st.fields) || slice.equal(order, st.fields) { return nil }
    return order
}

// A literal's entries in its struct's order: each one's text where its
// field is now — the text between them as it is.
lsp_literal_reordered :: proc(st: Lsp_Struct, l: Lsp_Literal, order: []string, text: string) -> string {
    stretch := text[l.at:l.end]
    slots := lsp_entry_slots(stretch)
    b := strings.builder_make()
    from := 0
    for name, i in st.fields {
        j, _ := slice.linear_search(order, name)
        strings.write_string(&b, stretch[from:slots[i][0]])
        strings.write_string(&b, stretch[slots[j][0]:slots[j][1]])
        from = slots[i][1]
    }
    strings.write_string(&b, stretch[from:])
    return strings.to_string(b)
}

// Fields' names as a list for a message: "kind, file, offset, len".
lsp_field_list :: proc(names: []string) -> string {
    return strings.join(names, ", ", context.temp_allocator)
}

// The moved fields' diagnostics, each file's, added to `by_uri`: each
// literal in another order than its struct's, and the struct (how many).
lsp_moved_diagnostics :: proc(s: ^Lsp, by_uri: ^map[string][dynamic]string) {
    for st in s.structs.structs {
        left := 0
        for l in st.literals {
            order := lsp_literal_moved(s, st, l)
            if order == nil { continue }
            left += 1
            text, _ := lsp_editor_text(s, l.path)
            end := l.end
            if nl := strings.index_byte(text[l.at:l.end], '\n'); nl >= 0 { end = l.at + nl }   // (its first line)
            message := fmt.tprintf("%s's fields were reordered (%s), but this literal still gives them in the old order (%s)",
                                   st.name, lsp_field_list(st.fields), lsp_field_list(order))
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

// The moved fields' code actions for the lines asked about in a file (a
// struct there, or a literal of it in another order): its literals put in
// its order, or its fields put back as they were when its literals last
// fit.
lsp_moved_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    key := path_key(path)
    line_of :: proc(text: string, at: int) -> int { return strings.count(text[:clamp(at, 0, len(text))], "\n") }
    for st in s.structs.structs {
        on := path_key(st.path) == key && line_of(here, st.name_at) <= l1 && line_of(here, st.body_end) >= l0
        left := 0
        by_uri := make(map[string][dynamic]string)
        for l in st.literals {
            order := lsp_literal_moved(s, st, l)
            if order == nil { continue }
            left += 1
            text, _ := lsp_editor_text(s, l.path)
            if path_key(l.path) == key && line_of(here, l.at) <= l1 && line_of(here, l.end) >= l0 { on = true }
            uri := lsp_uri(s, l.path)
            edits := by_uri[uri]
            append(&edits, lsp_text_edit(s, text, l.at, l.end, lsp_literal_reordered(st, l, order, text)))
            by_uri[uri] = edits
        }
        if left == 0 || !on { continue }
        title := fmt.tprintf("Put the %d %s literal%s in the new order (%s)", left, st.name, "" if left == 1 else "s", lsp_field_list(st.fields))
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","isPreferred":true,"edit":%s}}`, json_str(title), lsp_workspace_edit(by_uri)))
        // Or its fields as they were.
        if st.body == "" || slice.equal(st.body_fields, st.fields) { continue }
        text, _ := lsp_editor_text(s, st.path)
        back := make(map[string][dynamic]string)
        put_back := make([dynamic]string)
        append(&put_back, lsp_text_edit(s, text, st.body_at, st.body_end, st.body))
        back[lsp_uri(s, st.path)] = put_back
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","edit":%s}}`,
                                    json_str(fmt.tprintf("Put %s's fields back in the old order (%s)", st.name, lsp_field_list(st.body_fields))), lsp_workspace_edit(back)))
    }
}
