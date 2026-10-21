package mara

import "core:fmt"
import "core:mem/virtual"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Moved fields, results, params (mara lsp). The server keeps, from each
// check that parsed, the orders declared in the editor's open files — each
// struct's fields, each fun's results (by their types) and params — and
// every place that gives them by position: a struct's literals; a fun's
// `return a, b` and `a, b := f()`; its calls. For each, every entry's text
// and the part (field, result, param) that text is for. A place is known by
// its entries: the next check's place of the same kind with the same texts,
// in any order, is it (in the order places come) — so what it's for
// survives its entries moved, by a code action, by hand, by an undo. Its
// texts changed (a value edited), or new, it's taken as written for the
// order then. A place whose entries, as they are now, give the parts in
// another order than its order has — the same parts — is said to
// (lsp_publish), and a code action puts each in the order's, or the order
// back as it was when every place last fit (lsp_code_actions). Said even
// when the place still checks: two parts of one type swapped would quietly
// mean another thing. A part renamed in place is followed; one cut and not
// yet put back changes nothing known.
// ---------------------------------------------------------------------------

// A place giving an order's parts by position: where its entries are (the
// first's start to the last's end), each one's text, and the part each text
// is for — nil when not known (its entries weren't as many as the parts).
Lsp_Site :: struct {
    kind:    Site_Kind,
    path:    string,
    at, end: int,
    texts:   []string,
    parts:   []string,
}

// An order as the last check that saw it had it — a struct's fields, a
// fun's results or params — and as it was written when its places last all
// fit it: what's put back.
Lsp_Order :: struct {
    kind:       Order_Kind,
    name:       string,    // the struct's or fun's
    path:       string,
    name_at:    int,       // its name's place
    span_at:    int,       // what's put back: a struct's body (inside its braces), a fun's results or params ...
    span_end:   int,
    parts:      []string,  // its parts now: fields' names, results' types, params' names
    text:       string,    // the span as written when its places last all fit it ("" for never) ...
    text_parts: []string,  // ... its parts' order then
    sites:      [dynamic]Lsp_Site,
}

// The orders kept, in an arena of their own: let go whole when kept again.
Lsp_Orders :: struct {
    arena:  virtual.Arena,
    orders: [dynamic]Lsp_Order,
}

// The orders kept again, from the check just made — unless it didn't parse.
// Each place keeps what was known of the one with its texts; an order the
// check didn't see (another module's check), its file still open, is kept
// as it was.
lsp_keep_orders :: proc(s: ^Lsp) {
    session := &s.check.session
    if session.checked == nil { return }
    for d in s.check.diagnostics { if d.kind == .Parse_Error { return } }
    fresh: Lsp_Orders
    if virtual.arena_init_growing(&fresh.arena) != nil { return }
    {
        context.allocator = virtual.arena_allocator(&fresh.arena)
        fresh.orders = make([dynamic]Lsp_Order)
        lsp_fresh_orders(s, &fresh.orders)
        for &o in fresh.orders {
            old := lsp_find_order(s.orders.orders[:], o.kind, o.name, o.path)
            renames := lsp_part_renames(old, o.parts)
            next := 0   // (old's places gone past, in order)
            for &p in o.sites {
                if old != nil {
                    for k in next ..< len(old.sites) {
                        op := old.sites[k]
                        if op.kind != p.kind || path_key(op.path) != path_key(p.path) || !lsp_same_texts(op.texts, p.texts) { continue }
                        next = k + 1
                        if op.parts != nil {
                            p.texts = lsp_clone_names(op.texts)
                            p.parts = lsp_clone_names(op.parts)
                            for &name in p.parts { if to, renamed := renames[name]; renamed { name = to } }
                        }
                        break
                    }
                }
                // (New, its values changed, or not known: as written for the order now.)
                if p.parts == nil && len(p.texts) == len(o.parts) { p.parts = lsp_clone_names(o.parts) }
            }
            // (Its span now, what's put back, when every place fits it.)
            fits := true
            for p in o.sites {
                given := lsp_site_order(s, p)
                if given == nil || !slice.equal(given, o.parts) { fits = false }
            }
            if fits {
                text, _ := lsp_editor_text(s, o.path)
                if o.span_end <= len(text) { o.text = strings.clone(text[o.span_at:o.span_end]) }
                o.text_parts = lsp_clone_names(o.parts)
            } else if old != nil {
                o.text = strings.clone(old.text)
                o.text_parts = lsp_clone_names(old.text_parts)
            }
        }
        for o in s.orders.orders {
            if path_key(o.path) not_in s.overlays || lsp_find_order(fresh.orders[:], o.kind, o.name, o.path) != nil { continue }
            append(&fresh.orders, lsp_order_clone(o))
        }
    }
    virtual.arena_destroy(&s.orders.arena)
    s.orders = fresh
}

// The check's orders declared in the editor's open files (orders_of, the
// compiler's), each place's entries as their texts and where they are. (A
// method call's: not followed — its receiver isn't among its entries.)
@(private="file")
lsp_fresh_orders :: proc(s: ^Lsp, out: ^[dynamic]Lsp_Order) {
    t := &build_tree
    open := make(map[u16]bool, allocator = context.temp_allocator)
    for f, i in build_files { if path_key(lsp_abs(s, f.path)) in s.overlays { open[u16(i)] = true } }
    for o in orders_of(t, s.check.session.checked.annot, &open) {
        first := build_tokens[t.first[o.def]]
        path := lsp_abs(s, build_files[first.file].path)
        name_at := int(build_tokens[o.name_tok].offset) if o.name_tok != 0 else int(first.offset)
        // (What's put back: a struct's body, inside its braces; a fun's results or params.)
        at, end := -1, -1
        if o.kind == .Fields {
            for k := t.first[o.def]; k < t.end[o.def]; k += 1 {
                tk := build_tokens[k]
                if tk.kind == .Left_Brace && at < 0 { at = int(tk.offset + tk.len) }
                if tk.kind == .Right_Brace { end = int(tk.offset) }
            }
        } else if o.groups != nil {
            last := build_tokens[o.groups[len(o.groups) - 1].end - 1]
            at, end = int(build_tokens[o.groups[0].first].offset), int(last.offset + last.len)
        }
        if at < 0 || end < at { continue }
        lo := Lsp_Order{kind = o.kind, name = strings.clone(o.name), path = strings.clone(path), name_at = name_at,
                        span_at = at, span_end = end, parts = lsp_clone_names(o.parts), sites = make([dynamic]Lsp_Site)}
        for site in o.sites {
            if site.kind == .Method_Call || len(site.entries) == 0 { continue }
            e0, e1 := build_tokens[t.first[site.entries[0]]], build_tokens[t.end[site.entries[len(site.entries) - 1]] - 1]
            src := build_files[e0.file].source
            texts := make([]string, len(site.entries))
            for e, j in site.entries {
                a0, a1 := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
                texts[j] = strings.clone(src[a0.offset:a1.offset + a1.len])
            }
            append(&lo.sites, Lsp_Site{kind = site.kind, path = strings.clone(lsp_abs(s, build_files[e0.file].path)),
                                       at = int(e0.offset), end = int(e1.offset + e1.len), texts = texts})
        }
        slice.sort_by(lo.sites[:], proc(x, y: Lsp_Site) -> bool { return x.path < y.path || x.path == y.path && x.at < y.at })
        append(out, lo)
    }
}

// The parts renamed in place since the order was kept: the same count, a
// name at a place where the other's isn't anywhere — the old's to the new.
@(private="file")
lsp_part_renames :: proc(old: ^Lsp_Order, parts: []string) -> map[string]string {
    out := make(map[string]string, allocator = context.temp_allocator)
    if old == nil || len(old.parts) != len(parts) { return out }
    for name, i in old.parts {
        if parts[i] != name && !slice.contains(parts, name) && !slice.contains(old.parts, parts[i]) { out[name] = parts[i] }
    }
    return out
}

@(private="file")
lsp_find_order :: proc(orders: []Lsp_Order, kind: Order_Kind, name, path: string) -> ^Lsp_Order {
    for &o in orders {
        if o.kind == kind && o.name == name && path_key(o.path) == path_key(path) { return &o }
    }
    return nil
}

@(private="file")
lsp_order_clone :: proc(o: Lsp_Order) -> Lsp_Order {
    out := o
    out.name, out.path, out.text = strings.clone(o.name), strings.clone(o.path), strings.clone(o.text)
    out.parts, out.text_parts = lsp_clone_names(o.parts), lsp_clone_names(o.text_parts)
    out.sites = make([dynamic]Lsp_Site)
    for p in o.sites {
        append(&out.sites, Lsp_Site{kind = p.kind, path = strings.clone(p.path), at = p.at, end = p.end,
                                    texts = lsp_clone_names(p.texts), parts = lsp_clone_names(p.parts)})
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

// Whether two lists of names have the same names, in any order (an alike
// one as many times).
@(private="file")
lsp_same_names :: proc(a, b: []string) -> bool {
    return lsp_same_texts(a, b)
}

// Whether two lists of texts are the same texts, in any order.
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

// The parts a kept place's entries give, in the order its entries are in
// the editor's text now (each text's part, an alike text's taken in turn);
// nil when that's not known — its entries' texts aren't the ones known, or
// what they're for isn't.
lsp_site_order :: proc(s: ^Lsp, p: Lsp_Site) -> []string {
    if p.parts == nil { return nil }
    text, ok := lsp_editor_text(s, p.path)
    if !ok || p.at < 0 || p.end > len(text) || p.at > p.end { return nil }
    slots := lsp_entry_slots(text[p.at:p.end])
    if len(slots) != len(p.texts) { return nil }
    out := make([]string, len(slots), context.temp_allocator)
    used := make([]bool, len(p.texts), context.temp_allocator)
    outer: for sl, i in slots {
        here := text[p.at + sl[0]:p.at + sl[1]]
        for t, j in p.texts {
            if !used[j] && t == here {
                used[j] = true
                out[i] = p.parts[j]
                continue outer
            }
        }
        return nil
    }
    return out
}

// A place's entries in its text (from its first's start to its last's
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

// A kept place giving its order's parts in another order than its order has
// now (the same parts): that order; nil when it doesn't.
lsp_site_moved :: proc(s: ^Lsp, o: Lsp_Order, p: Lsp_Site) -> []string {
    given := lsp_site_order(s, p)
    if given == nil || !lsp_same_names(given, o.parts) || slice.equal(given, o.parts) { return nil }
    return given
}

// A place's entries in its order's order: each one's text where its part is
// now — the text between them as it is. (Alike parts, alike results'
// types: each in turn.)
lsp_site_reordered :: proc(o: Lsp_Order, p: Lsp_Site, given: []string, text: string) -> string {
    stretch := text[p.at:p.end]
    slots := lsp_entry_slots(stretch)
    used := make([]bool, len(given), context.temp_allocator)
    b := strings.builder_make()
    from := 0
    for name, i in o.parts {
        j := 0
        for k in 0 ..< len(given) {
            if !used[k] && given[k] == name {
                j = k
                break
            }
        }
        used[j] = true
        strings.write_string(&b, stretch[from:slots[i][0]])
        strings.write_string(&b, stretch[slots[j][0]:slots[j][1]])
        from = slots[i][1]
    }
    strings.write_string(&b, stretch[from:])
    return strings.to_string(b)
}

// Parts as a list for a message: "kind, file, offset, len".
lsp_part_list :: proc(names: []string) -> string {
    return strings.join(names, ", ", context.temp_allocator)
}

// What a place does with the parts, said of it: "this literal still gives
// them", "this destructure still names them", ...
@(private="file")
lsp_site_said :: proc(kind: Site_Kind) -> string {
    switch kind {
    case .Literal:     return "this literal still gives them"
    case .Return:      return "this return still gives them"
    case .Destructure: return "this destructure still names them"
    case .Call, .Method_Call: return "this call still passes them"
    }
    return ""
}

// An order's places, said: "30 literals", "1 place", "2 calls".
@(private="file")
lsp_sites_word :: proc(kind: Order_Kind, n: int) -> string {
    noun := "literal" if kind == .Fields else "call" if kind == .Params else "place"
    return fmt.tprintf("%d %s%s", n, noun, "" if n == 1 else "s")
}

// The moved parts' diagnostics, each file's, added to `by_uri`: each place
// in another order than its order's, and the order (how many).
lsp_moved_diagnostics :: proc(s: ^Lsp, by_uri: ^map[string][dynamic]string) {
    for o in s.orders.orders {
        left := 0
        for p in o.sites {
            given := lsp_site_moved(s, o, p)
            if given == nil { continue }
            left += 1
            text, _ := lsp_editor_text(s, p.path)
            end := p.end
            if nl := strings.index_byte(text[p.at:p.end], '\n'); nl >= 0 { end = p.at + nl }   // (its first line)
            message := fmt.tprintf("%s's %s were reordered (%s), but %s in the old order (%s)",
                                   o.name, order_parts_word(o.kind), lsp_part_list(o.parts), lsp_site_said(p.kind), lsp_part_list(given))
            lsp_add_diagnostic(s, by_uri, p.path, text, p.at, end, message)
        }
        if left == 0 { continue }
        text, _ := lsp_editor_text(s, o.path)
        message := fmt.tprintf("%s's %s were reordered: %s still use%s the old order. A code action puts them in the new one, or the %s back.",
                               o.name, order_parts_word(o.kind), lsp_sites_word(o.kind, left), "s" if left == 1 else "", order_parts_word(o.kind))
        lsp_add_diagnostic(s, by_uri, o.path, text, o.name_at, o.name_at + len(o.name), message)
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

// The moved parts' code actions for the lines asked about in a file (an
// order's declaration there, or a place of it in another order): its places
// put in its order, or the order put back as it was when its places last
// fit.
lsp_moved_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    key := path_key(path)
    line_of :: proc(text: string, at: int) -> int { return strings.count(text[:clamp(at, 0, len(text))], "\n") }
    for o in s.orders.orders {
        on := path_key(o.path) == key && line_of(here, o.name_at) <= l1 && line_of(here, o.span_end) >= l0
        left := 0
        by_uri := make(map[string][dynamic]string)
        for p in o.sites {
            given := lsp_site_moved(s, o, p)
            if given == nil { continue }
            left += 1
            text, _ := lsp_editor_text(s, p.path)
            if path_key(p.path) == key && line_of(here, p.at) <= l1 && line_of(here, p.end) >= l0 { on = true }
            uri := lsp_uri(s, p.path)
            edits := by_uri[uri]
            append(&edits, lsp_text_edit(s, text, p.at, p.end, lsp_site_reordered(o, p, given, text)))
            by_uri[uri] = edits
        }
        if left == 0 || !on { continue }
        title: string
        switch o.kind {
        case .Fields:  title = fmt.tprintf("Put the %d %s literal%s in the new order (%s)", left, o.name, "" if left == 1 else "s", lsp_part_list(o.parts))
        case .Results: title = fmt.tprintf("Put the %s using %s's results in the new order (%s)", lsp_sites_word(o.kind, left), o.name, lsp_part_list(o.parts))
        case .Params:  title = fmt.tprintf("Put the %d call%s of %s in the new order (%s)", left, "" if left == 1 else "s", o.name, lsp_part_list(o.parts))
        }
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","isPreferred":true,"edit":%s}}`, json_str(title), lsp_workspace_edit(by_uri)))
        // Or the order as it was.
        if o.text == "" || slice.equal(o.text_parts, o.parts) { continue }
        text, _ := lsp_editor_text(s, o.path)
        back := make(map[string][dynamic]string)
        put_back := make([dynamic]string)
        append(&put_back, lsp_text_edit(s, text, o.span_at, o.span_end, o.text))
        back[lsp_uri(s, o.path)] = put_back
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"quickfix","edit":%s}}`,
                                    json_str(fmt.tprintf("Put %s's %s back in the old order (%s)", o.name, order_parts_word(o.kind), lsp_part_list(o.text_parts))),
                                    lsp_workspace_edit(back)))
    }
}

// --- a fun's body written out (shapes.odin) -----------------------------------

// The code action at a fun's name, asked for (nothing said on its own): the
// fun called in each place its body is written out, its run of statements
// there the call.
lsp_shape_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    session := &s.check.session
    if session.checked == nil { return }
    t := &build_tree
    a := session.checked.annot
    key := path_key(path)
    for k, ts in a.decls {
        _, n := annot_split(k)
        if ts == nil || ts.kind != .Fun || t.tag[n] != .Fun_Def { continue }
        name_tok := t.first[n] - 2 if t.first[n] >= 2 else t.first[n]
        tok := build_tokens[name_tok]
        if path_key(lsp_abs(s, build_files[tok.file].path)) != key { continue }
        line := token_line(tok) - 1
        if line < l0 || line > l1 { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        matches := shape_matches(t, a, n, ts)
        if len(matches) == 0 { continue }
        by_uri := make(map[string][dynamic]string)
        for m in matches {
            file, at, end := shape_span(t, m)
            p := lsp_abs(s, build_files[file].path)
            text, _ := lsp_editor_text(s, p)
            uri := lsp_uri(s, p)
            edits := by_uri[uri]
            append(&edits, lsp_text_edit(s, text, at, end, shape_call_text(t, name, m)))
            by_uri[uri] = edits
        }
        title := fmt.tprintf("Call %s in the %d place%s its body is written out", name, len(matches), "" if len(matches) == 1 else "s")
        append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str(title), lsp_workspace_edit(by_uri)))
    }
}

// --- one-statement ifs written with `do` (shapes.odin) -----------------------

// The code actions for ifs written with `do`, asked for: at an if that can
// be, it written so — over a selection, every one starting in it — and when
// its fun has more, all of them; at a fun's name, all of its.
lsp_do_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    session := &s.check.session
    if session.checked == nil { return }
    t := &build_tree
    key := path_key(path)
    for k, ts in session.checked.annot.decls {
        _, n := annot_split(k)
        if ts == nil || ts.kind != .Fun || t.tag[n] != .Fun_Def { continue }
        first := build_tokens[t.first[n]]
        if path_key(lsp_abs(s, build_files[first.file].path)) != key { continue }
        last := build_tokens[t.end[n] - 1]
        if token_line(first) - 1 > l1 || token_line(last) - 1 < l0 { continue }
        chains := do_chains(t, n)
        if len(chains) == 0 { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        edit_of :: proc(s: ^Lsp, t: ^Tree, chains: []Tree_Id) -> string {
            by_uri := make(map[string][dynamic]string)
            for c in chains {
                file, at, end := do_span(t, c)
                p := lsp_abs(s, build_files[file].path)
                text, _ := lsp_editor_text(s, p)
                uri := lsp_uri(s, p)
                edits := by_uri[uri]
                append(&edits, lsp_text_edit(s, text, at, end, do_text(t, c)))
                by_uri[uri] = edits
            }
            return lsp_workspace_edit(by_uri)
        }
        // (The ones the lines asked about start on: at the cursor, one; a selection, all in it.)
        picked := make([dynamic]Tree_Id, context.temp_allocator)
        for c in chains {
            line := token_line(build_tokens[t.first[c]]) - 1
            if line >= l0 && line <= l1 { append(&picked, c) }
        }
        if len(picked) == 1 {
            append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str("Write this if with do"), edit_of(s, t, picked[:])))
        } else if len(picked) > 1 {
            title := fmt.tprintf("Write the %d selected ifs with do", len(picked))
            append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str(title), edit_of(s, t, picked[:])))
        }
        name_line := token_line(build_tokens[t.first[n] - 2 if t.first[n] >= 2 else t.first[n]]) - 1
        if (len(picked) > 0 && len(picked) < len(chains)) || (name_line >= l0 && name_line <= l1) {
            title := fmt.tprintf("Write %s's %d one-statement if%s with do", name, len(chains), "" if len(chains) == 1 else "s")
            append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str(title), edit_of(s, t, chains[:])))
        }
    }
}

// --- ifs joined into a chain with elif (shapes.odin) --------------------------

// The code actions for ifs joined with elif, asked for: at an if of a run
// that can be joined, its run — over a selection, the ifs of a run starting
// in it (two or more); at a fun's name, all of its runs.
lsp_elif_actions :: proc(s: ^Lsp, path, here: string, l0, l1: int, actions: ^[dynamic]string) {
    session := &s.check.session
    if session.checked == nil { return }
    t := &build_tree
    key := path_key(path)
    for k, ts in session.checked.annot.decls {
        _, n := annot_split(k)
        if ts == nil || ts.kind != .Fun || t.tag[n] != .Fun_Def { continue }
        first := build_tokens[t.first[n]]
        if path_key(lsp_abs(s, build_files[first.file].path)) != key { continue }
        if token_line(first) - 1 > l1 || token_line(build_tokens[t.end[n] - 1]) - 1 < l0 { continue }
        runs := elif_runs(t, n)
        if len(runs) == 0 { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        edit_of :: proc(s: ^Lsp, t: ^Tree, runs: [][]Tree_Id) -> string {
            by_uri := make(map[string][dynamic]string)
            for run in runs {
                for e in elif_edits(t, run) {
                    p := lsp_abs(s, build_files[e.file].path)
                    text, _ := lsp_editor_text(s, p)
                    uri := lsp_uri(s, p)
                    edits := by_uri[uri]
                    append(&edits, lsp_text_edit(s, text, e.at, e.end, e.text))
                    by_uri[uri] = edits
                }
            }
            return lsp_workspace_edit(by_uri)
        }
        line_of :: proc(t: ^Tree, n: Tree_Id) -> int { return token_line(build_tokens[t.first[n]]) - 1 }
        for run in runs {
            // (The ifs of it starting on the lines asked about.)
            lo, hi := -1, -1
            for s, i in run {
                if line_of(t, s) >= l0 && line_of(t, s) <= l1 {
                    if lo < 0 { lo = i }
                    hi = i
                }
            }
            if lo < 0 { continue }
            picked := run if lo == hi else run[lo:hi + 1]
            if len(picked) < 2 { continue }
            title := fmt.tprintf("Join these %d ifs into one chain with elif", len(picked))
            if lo != hi { title = fmt.tprintf("Join the %d selected ifs into one chain with elif", len(picked)) }
            append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str(title), edit_of(s, t, [][]Tree_Id{picked})))
        }
        name_line := token_line(build_tokens[t.first[n] - 2 if t.first[n] >= 2 else t.first[n]]) - 1
        if name_line >= l0 && name_line <= l1 {
            total := 0
            for run in runs { total += len(run) }
            title := fmt.tprintf("Join %s's %d ifs into %d chain%s with elif", name, total, len(runs), "" if len(runs) == 1 else "s")
            append(actions, fmt.tprintf(`{{"title":%s,"kind":"refactor","edit":%s}}`, json_str(title), edit_of(s, t, runs[:])))
        }
    }
}
