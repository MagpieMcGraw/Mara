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

// What an order is of.
Lsp_Order_Kind :: enum { Fields, Results, Params }

// What a place giving an order's parts is.
Lsp_Site_Kind :: enum { Literal, Return, Destructure, Call }

// A place giving an order's parts by position: where its entries are (the
// first's start to the last's end), each one's text, and the part each text
// is for — nil when not known (its entries weren't as many as the parts).
Lsp_Site :: struct {
    kind:    Lsp_Site_Kind,
    path:    string,
    at, end: int,
    texts:   []string,
    parts:   []string,
}

// An order as the last check that saw it had it — a struct's fields, a
// fun's results or params — and as it was written when its places last all
// fit it: what's put back.
Lsp_Order :: struct {
    kind:       Lsp_Order_Kind,
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

// The check's orders declared in the editor's open files — structs' fields,
// funs' results (two or more) and params (two or more) — and every place
// giving them by position (any file's), in the order they're written.
@(private="file")
lsp_fresh_orders :: proc(s: ^Lsp, out: ^[dynamic]Lsp_Order) {
    a := s.check.session.checked.annot
    t := &build_tree
    of_struct := make(map[^Type_Scope]int, allocator = context.temp_allocator)
    of_results := make(map[Tree_Id]int, allocator = context.temp_allocator)   // (by the fun's Fun_Def)
    of_params := make(map[Tree_Id]int, allocator = context.temp_allocator)
    funs := make([dynamic]Tree_Id, context.temp_allocator)   // (the open files' Fun_Defs: a return's own fun)
    for key, ts in a.decls {
        if ts == nil || ts.is_module { continue }
        _, n := annot_split(key)
        first := build_tokens[t.first[n]]
        file := build_files[first.file]
        path := lsp_abs(s, file.path)
        if path_key(path) not_in s.overlays { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        // (Its name: before its `::`.)
        name_at := int(first.offset)
        if t.first[n] >= 2 && token_text(build_tokens[t.first[n] - 2]) == name { name_at = int(build_tokens[t.first[n] - 2].offset) }
        order :: proc(kind: Lsp_Order_Kind, name, path: string, name_at, at, end: int, parts: []string) -> Lsp_Order {
            return {kind = kind, name = strings.clone(name), path = strings.clone(path), name_at = name_at,
                    span_at = at, span_end = end, parts = parts, sites = make([dynamic]Lsp_Site)}
        }
        switch {
        case ts.kind == .Struct && !ts.is_union_variant && t.tag[n] == .Struct_Def:
            // (Its body: its braces' inside.)
            open, close := -1, -1
            for k := t.first[n]; k < t.end[n]; k += 1 {
                tk := build_tokens[k]
                if tk.kind == .Left_Brace && open < 0 { open = int(tk.offset + tk.len) }
                if tk.kind == .Right_Brace { close = int(tk.offset) }
            }
            if open < 0 || close < open { continue }
            parts := make([]string, len(ts.fields) - first_user_field(ts))
            for f, i in ts.fields[first_user_field(ts):] { parts[i] = strings.clone(f.name) }
            append(out, order(.Fields, name, path, name_at, open, close, parts))
            of_struct[ts] = len(out) - 1
        case ts.kind == .Fun && t.tag[n] == .Fun_Def:
            append(&funs, n)
            r := tree_rec(t, t.a[n], 5)
            params, results := tree_list(t, r[1]), tree_list(t, r[2])
            if len(results) >= 2 && len(results) == len(ts.return_types) {
                parts := make([]string, len(results))
                for rt, i in ts.return_types { parts[i] = strings.clone(type_name(rt)) }
                at, end := lsp_nodes_span(t, results)
                append(out, order(.Results, name, path, name_at, at, end, parts))
                of_results[n] = len(out) - 1
            }
            if len(params) > 0 && len(ts.params) >= 2 {
                parts := make([]string, len(ts.params))
                for p, i in ts.params { parts[i] = strings.clone(p.name) }
                at, end := lsp_nodes_span(t, params)
                append(out, order(.Params, name, path, name_at, at, end, parts))
                of_params[n] = len(out) - 1
            }
        }
    }
    if len(out) == 0 { return }
    seen := make(map[[2]u32]bool, allocator = context.temp_allocator)   // (a generic's instances: one place)
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            site: Lsp_Site_Kind
            entries: []Tree_Id
            at := -1   // (its order)
            #partial switch t.tag[n] {
            case .Literal:
                ts, is_scope := distinct_base(annot_type(a, Instance_Id(i), n)).(^Type_Scope)
                if !is_scope { continue }
                o, kept := of_struct[ts]
                if !kept { continue }
                entries = tree_list(t, t.b[n])
                if len(entries) == 0 || t.tag[entries[0]] == .Named_Entry { continue }
                if len(entries) == 1 && len(out[o].parts) != 1 { continue }   // (`Token{0}`: its zero, not its first field)
                site, at = .Literal, o
            case .Return:
                entries = tree_list(t, t.a[n])
                if len(entries) < 2 { continue }
                fun := lsp_own_fun(t, funs[:], n)
                o, kept := of_results[fun]
                if fun == 0 || !kept { continue }
                site, at = .Return, o
            case .Decl, .Assign:
                entries = tree_list(t, t.a[n])
                values := tree_list(t, tree_rec(t, t.b[n], 2)[1]) if t.tag[n] == .Decl else tree_list(t, t.b[n])
                if len(entries) < 2 || len(values) != 1 { continue }
                call := values[0]
                for t.tag[call] == .Paren { call = Tree_Id(t.a[call]) }
                if t.tag[call] != .Call { continue }
                callee := a.callees[annot_key(Instance_Id(i), call)] or_else nil
                if callee == nil { continue }
                o, kept := of_results[callee.node]
                if !kept { continue }
                site, at = .Destructure, o
            case .Call:
                callee := a.callees[annot_key(Instance_Id(i), n)] or_else nil
                if callee == nil || callee.kind != .Fun { continue }
                o, kept := of_params[callee.node]
                if !kept { continue }
                entries = tree_list(t, t.a[n])
                if len(entries) == 0 { continue }
                site, at = .Call, o
            case:
                continue
            }
            key := [2]u32{u32(t.first[n]), u32(site)}
            if at < 0 || seen[key] { continue }
            seen[key] = true
            first, last := build_tokens[t.first[entries[0]]], build_tokens[t.end[entries[len(entries) - 1]] - 1]
            src := build_files[first.file].source
            texts := make([]string, len(entries))
            for e, j in entries {
                a0, a1 := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
                texts[j] = strings.clone(src[a0.offset:a1.offset + a1.len])
            }
            append(&out[at].sites, Lsp_Site{kind = site, path = strings.clone(lsp_abs(s, build_files[first.file].path)),
                                             at = int(first.offset), end = int(last.offset + last.len), texts = texts})
        }
    }
    for &o in out {
        slice.sort_by(o.sites[:], proc(x, y: Lsp_Site) -> bool { return x.path < y.path || x.path == y.path && x.at < y.at })
    }
}

// From the first node's start to the last's end, in its file's text.
@(private="file")
lsp_nodes_span :: proc(t: ^Tree, nodes: []Tree_Id) -> (at, end: int) {
    first, last := build_tokens[t.first[nodes[0]]], build_tokens[t.end[nodes[len(nodes) - 1]] - 1]
    return int(first.offset), int(last.offset + last.len)
}

// The fun a node is in: the innermost Fun_Def around it, of `funs`; 0 for none.
@(private="file")
lsp_own_fun :: proc(t: ^Tree, funs: []Tree_Id, n: Tree_Id) -> Tree_Id {
    best := Tree_Id(0)
    for f in funs {
        if t.first[f] <= t.first[n] && t.first[n] < t.end[f] && (best == 0 || t.first[f] > t.first[best]) { best = f }
    }
    // (Inside another fun nested in it: that one's, kept or not.)
    if best == 0 { return 0 }
    return best
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
lsp_find_order :: proc(orders: []Lsp_Order, kind: Lsp_Order_Kind, name, path: string) -> ^Lsp_Order {
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

// What an order's parts are called: "fields", "results", "params".
@(private="file")
lsp_parts_word :: proc(kind: Lsp_Order_Kind) -> string {
    switch kind {
    case .Fields:  return "fields"
    case .Results: return "results"
    case .Params:  return "params"
    }
    return ""
}

// What a place does with the parts, said of it: "this literal still gives
// them", "this destructure still names them", ...
@(private="file")
lsp_site_said :: proc(kind: Lsp_Site_Kind) -> string {
    switch kind {
    case .Literal:     return "this literal still gives them"
    case .Return:      return "this return still gives them"
    case .Destructure: return "this destructure still names them"
    case .Call:        return "this call still passes them"
    }
    return ""
}

// An order's places, said: "30 literals", "1 place", "2 calls".
@(private="file")
lsp_sites_word :: proc(kind: Lsp_Order_Kind, n: int) -> string {
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
                                   o.name, lsp_parts_word(o.kind), lsp_part_list(o.parts), lsp_site_said(p.kind), lsp_part_list(given))
            lsp_add_diagnostic(s, by_uri, p.path, text, p.at, end, message)
        }
        if left == 0 { continue }
        text, _ := lsp_editor_text(s, o.path)
        message := fmt.tprintf("%s's %s were reordered: %s still use%s the old order. A code action puts them in the new one, or the %s back.",
                               o.name, lsp_parts_word(o.kind), lsp_sites_word(o.kind, left), "s" if left == 1 else "", lsp_parts_word(o.kind))
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
                                    json_str(fmt.tprintf("Put %s's %s back in the old order (%s)", o.name, lsp_parts_word(o.kind), lsp_part_list(o.text_parts))),
                                    lsp_workspace_edit(back)))
    }
}
