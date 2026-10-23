package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Orders and their places (`mara edit`; mara lsp's moved parts). An order is
// the parts a declaration lists in turn — a struct's fields, a fun's results
// (by their types), a fun's params — and its places are where code gives
// them by position: a struct's literals; a fun's `return a, b` and `a, b :=
// f()`; its calls. orders_of: the checked program's orders, each with its
// declaration's items and its places, entry i of a place for part i.
// edit_order: an order put in another — its declaration's items moved, and
// every place's entries — as the edits to make.
// ---------------------------------------------------------------------------

Order_Kind :: enum { Fields, Results, Params }

Site_Kind :: enum { Literal, Return, Destructure, Call, Method_Call }

// One of a declaration's items as written: a group of fields or params (`a,
// b : T`), a result's type — its tokens, and the parts it declares, in turn.
Order_Group :: struct {
    first, end: Token_Id,   // [first, end)
    parts:      []string,
}

// A place giving an order's parts by position: its node, and its entries,
// entry i for part i as checked. (A method call's: its args, its receiver
// the first param's, not among them.)
Order_Site :: struct {
    kind:    Site_Kind,
    node:    Tree_Id,
    entries: []Tree_Id,
}

Order :: struct {
    kind:     Order_Kind,
    name:     string,
    def:      Tree_Id,          // its Struct_Def or Fun_Def
    name_tok: Token_Id,         // its name; 0 for none found
    parts:    []string,         // fields' names, results' types, params' names
    groups:   []Order_Group,    // its declaration's items, in order; nil when they aren't as its parts are
    sites:    [dynamic]Order_Site,
}

// The checked program's orders — every struct's fields, every fun's results
// (two or more) and params (two or more), declared in a file `files` has
// (nil: any) — and every place giving them by position, any file's.
orders_of :: proc(t: ^Tree, a: ^Annotations, files: ^map[u16]bool = nil) -> [dynamic]Order {
    out := make([dynamic]Order)
    of_struct := make(map[^Type_Scope]int, allocator = context.temp_allocator)
    of_results := make(map[Tree_Id]int, allocator = context.temp_allocator)   // (by the fun's Fun_Def)
    of_params := make(map[Tree_Id]int, allocator = context.temp_allocator)
    funs := make([dynamic]Tree_Id, context.temp_allocator)   // (every Fun_Def: a return's own fun)
    for key, ts in a.decls {
        if ts == nil || ts.is_module { continue }
        _, n := annot_split(key)
        if t.tag[n] == .Fun_Def { append(&funs, n) }
        if files != nil && build_tokens[t.first[n]].file not_in files^ { continue }
        name := ts.source_name if ts.source_name != "" else ts.name
        name_tok := Token_Id(0)   // (before its `::`)
        if t.first[n] >= 2 && token_text(build_tokens[t.first[n] - 2]) == name { name_tok = t.first[n] - 2 }
        v := scope_view(t, n)
        switch {
        case ts.kind == .Struct && !ts.is_union_variant && t.tag[n] == .Struct_Def:
            parts := make([]string, len(ts.fields) - first_user_field(ts))
            for f, i in ts.fields[first_user_field(ts):] { parts[i] = f.name }
            // (Its fields' lines: each a Decl of one or more names.)
            groups := make([dynamic]Order_Group)
            for item in v.body {
                if t.tag[item] != .Decl { continue }
                names := make([dynamic]string)
                for target in tree_list(t, t.a[item]) { append(&names, token_text(build_tokens[t.main[target]])) }
                append(&groups, Order_Group{t.first[item], t.end[item], names[:]})
            }
            append(&out, Order{kind = .Fields, name = name, def = n, name_tok = name_tok, parts = parts, groups = order_groups(groups[:], parts)})
            of_struct[ts] = len(out) - 1
        case ts.kind == .Fun && t.tag[n] == .Fun_Def:
            if len(v.returns) >= 2 && len(v.returns) == len(ts.return_types) {
                parts := make([]string, len(v.returns))
                groups := make([]Order_Group, len(v.returns))
                for r, i in v.returns {
                    parts[i] = type_name(ts.return_types[i])
                    groups[i] = {t.first[r], t.end[r], parts[i:i + 1]}
                }
                append(&out, Order{kind = .Results, name = name, def = n, name_tok = name_tok, parts = parts, groups = groups})
                of_results[n] = len(out) - 1
            }
            if len(v.params) > 0 && len(ts.params) >= 2 {
                parts := make([]string, len(ts.params))
                for p, i in ts.params { parts[i] = p.name }
                groups := make([dynamic]Order_Group)
                for g in v.params {
                    if t.tag[g] != .Param_Group { continue }
                    names := make([dynamic]string)
                    for tok in tree_token_list(t, t.a[g]) { append(&names, token_text(build_tokens[tok])) }
                    append(&groups, Order_Group{t.first[g], t.end[g], names[:]})
                }
                append(&out, Order{kind = .Params, name = name, def = n, name_tok = name_tok, parts = parts, groups = order_groups(groups[:], parts)})
                of_params[n] = len(out) - 1
            }
        }
    }
    if len(out) == 0 { return out }
    seen := make(map[[2]u32]bool, allocator = context.temp_allocator)   // (a generic's instances: one place)
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            site: Site_Kind
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
                fun := order_own_fun(t, funs[:], n)
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
            case .Call, .Method_Call:
                callee := a.callees[annot_key(Instance_Id(i), n)] or_else nil
                if callee == nil || callee.kind != .Fun { continue }
                o, kept := of_params[callee.node]
                if !kept { continue }
                if t.tag[n] == .Call {
                    entries, site = tree_list(t, t.a[n]), .Call
                } else {
                    entries, site = method_view(t, n).args, .Method_Call
                }
                if len(entries) == 0 && site == .Call { continue }
                at = o
            case:
                continue
            }
            key := [2]u32{u32(t.first[n]), u32(site)}
            if at < 0 || seen[key] { continue }
            seen[key] = true
            append(&out[at].sites, Order_Site{site, n, entries})
        }
    }
    return out
}

// A declaration's items, when the parts they declare are its parts, in
// order; else nil.
@(private="file")
order_groups :: proc(groups: []Order_Group, parts: []string) -> []Order_Group {
    k := 0
    for g in groups {
        for p in g.parts {
            if k >= len(parts) || parts[k] != p { return nil }
            k += 1
        }
    }
    if k != len(parts) { return nil }
    return groups
}

// The fun a node is in: the innermost Fun_Def around it; 0 for none.
order_own_fun :: proc(t: ^Tree, funs: []Tree_Id, n: Tree_Id) -> Tree_Id {
    best := Tree_Id(0)
    for f in funs {
        if t.first[f] <= t.first[n] && t.first[n] < t.end[f] && (best == 0 || t.first[f] > t.first[best]) { best = f }
    }
    return best
}

// What an order's parts are called: "fields", "results", "params".
order_parts_word :: proc(kind: Order_Kind) -> string {
    switch kind {
    case .Fields:  return "fields"
    case .Results: return "results"
    case .Params:  return "params"
    }
    return ""
}

// --- the edit ---------------------------------------------------------------

// An edit to make: bytes [at, end) of a file's text replaced.
Order_Edit :: struct {
    file:    u16,
    at, end: int,
    text:    string,
}

// An order put in another, `to` — every part once: its declaration's items
// moved (a group's parts move together, in their order: none split) and
// each place's entries put in the new order (a place inside another's
// entry, in it), as edits to the files as the check read them. "" and the
// edits; else what stops it, and none.
edit_order :: proc(t: ^Tree, o: Order, to: []string) -> (edits: [dynamic]Order_Edit, problem: string) {
    what := order_parts_word(o.kind)
    if !order_same(o.parts, to) {
        return nil, fmt.tprintf("%s's %s are %s: name each once, in the order wanted", o.name, what, strings.join(o.parts, ", "))
    }
    if o.groups == nil {
        return nil, fmt.tprintf("%s's %s aren't declared as its own list of them: edit it by hand", o.name, what)
    }
    // The declaration's items in the new order: each group whole, its parts
    // in theirs.
    moved := make([dynamic]int)   // (by slot: the group that goes there)
    used := make([]bool, len(o.groups))
    for k := 0; k < len(to); {
        g := -1
        for group, j in o.groups {
            if !used[j] && group.parts[0] == to[k] {
                g = j
                break
            }
        }
        if g < 0 || k + len(o.groups[g].parts) > len(to) || !slice.equal(o.groups[g].parts, to[k:k + len(o.groups[g].parts)]) {
            for group in o.groups {
                if len(group.parts) > 1 && slice.contains(group.parts, to[k]) {
                    return nil, fmt.tprintf("%s are declared together: they move together, in that order (or split them first)", strings.join(group.parts, ", "))
                }
            }
            return nil, fmt.tprintf("%s's %s can't go in that order", o.name, what)
        }
        used[g] = true
        append(&moved, g)
        k += len(o.groups[g].parts)
    }
    // Its places: as many entries as parts; a method call's when its receiver,
    // the first param, stays first.
    for s in o.sites {
        if s.kind == .Method_Call {
            if to[0] != o.parts[0] {
                return nil, fmt.tprintf("%s is called as a method (%s): its receiver is its first param, %s — that stays first", o.name, token_location(build_tokens[t.first[s.node]]), o.parts[0])
            }
            if len(s.entries) != len(o.parts) - 1 {
                return nil, fmt.tprintf("a call of %s gives fewer arguments than its params (%s): edit it by hand first", o.name, token_location(build_tokens[t.first[s.node]]))
            }
        } else if len(s.entries) != len(o.parts) {
            return nil, fmt.tprintf("a call of %s gives fewer arguments than its params (%s): edit it by hand first", o.name, token_location(build_tokens[t.first[s.node]]))
        }
    }
    edits = make([dynamic]Order_Edit)
    // The declaration's items: each slot the text of the group that goes
    // there — a field's line, its comment after it too.
    for g, slot in moved {
        if g == slot { continue }
        at, end, file := order_group_span(t, o, slot)
        from_at, from_end, _ := order_group_span(t, o, g)
        src := build_files[file].source
        append(&edits, Order_Edit{file, at, end, src[from_at:from_end]})
    }
    // Each place outside the others: its entries in the new order, the
    // places inside them too.
    for s in o.sites {
        outer := true
        for other in o.sites {
            if other.node != s.node && order_site_in(t, s, other) {
            outer = false
            break
        }
        }
        if !outer { continue }
        file, at, end := order_site_span(t, s)
        append(&edits, Order_Edit{file, at, end, order_site_text(t, o, to, s)})
    }
    return edits, ""
}

// Whether two lists have the same items, as many times each.
@(private="file")
order_same :: proc(a, b: []string) -> bool {
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

// Where a declaration's item is: its tokens — a field's, to its line's end
// (its comment there) — and its file.
@(private="file")
order_group_span :: proc(t: ^Tree, o: Order, g: int) -> (at, end: int, file: u16) {
    first, last := build_tokens[o.groups[g].first], build_tokens[o.groups[g].end - 1]
    src := build_files[first.file].source
    at, end = int(first.offset), int(last.offset + last.len)
    if o.kind == .Fields {
        for end < len(src) && src[end] != '\n' && src[end] != '\r' { end += 1 }
        for end > at && (src[end - 1] == ' ' || src[end - 1] == '\t') { end -= 1 }
    }
    return at, end, first.file
}

// Where a place's entries are: from its first's start to its last's end.
@(private="file")
order_site_span :: proc(t: ^Tree, s: Order_Site) -> (file: u16, at, end: int) {
    first, last := build_tokens[t.first[s.entries[0]]], build_tokens[t.end[s.entries[len(s.entries) - 1]] - 1]
    return first.file, int(first.offset), int(last.offset + last.len)
}

// Whether place s is inside one of other's entries.
@(private="file")
order_site_in :: proc(t: ^Tree, s, other: Order_Site) -> bool {
    if len(s.entries) == 0 || len(other.entries) == 0 { return false }
    for e in other.entries {
        if t.first[e] <= t.first[s.entries[0]] && t.end[s.entries[len(s.entries) - 1]] <= t.end[e] { return true }
    }
    return false
}

// A place's entries' text in the new order — each entry's own text, the
// places inside it put in the new order too — the text between them as it
// was. (A method call's entries: the params after its receiver.)
@(private="file")
order_site_text :: proc(t: ^Tree, o: Order, to: []string, s: Order_Site) -> string {
    parts, wanted := o.parts, to
    if s.kind == .Method_Call { parts, wanted = o.parts[1:], to[1:] }
    file, at, end := order_site_span(t, s)
    src := build_files[file].source
    b := strings.builder_make()
    used := make([]bool, len(parts), context.temp_allocator)
    pos := at
    for name, i in wanted {
        j := 0
        for k in 0 ..< len(parts) {
            if !used[k] && parts[k] == name {
                j = k
                break
            }
        }
        used[j] = true
        e := s.entries[i]
        e_at := int(build_tokens[t.first[e]].offset)
        strings.write_string(&b, src[pos:e_at])
        strings.write_string(&b, order_entry_text(t, o, to, s.entries[j]))
        pos = int(build_tokens[t.end[e] - 1].offset + build_tokens[t.end[e] - 1].len)
    }
    strings.write_string(&b, src[pos:end])
    return strings.to_string(b)
}

// An entry's text, the order's places inside it put in the new order.
@(private="file")
order_entry_text :: proc(t: ^Tree, o: Order, to: []string, e: Tree_Id) -> string {
    first, last := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
    src := build_files[first.file].source
    at, end := int(first.offset), int(last.offset + last.len)
    b := strings.builder_make()
    pos := at
    // (The outermost places inside it, in the order they're written.)
    inner := make([dynamic]Order_Site, context.temp_allocator)
    for s in o.sites {
        if len(s.entries) == 0 { continue }
        _, s_at, s_end := order_site_span(t, s)
        if s_at < at || s_end > end { continue }
        nested := false
        for other in o.sites {
            if other.node == s.node || len(other.entries) == 0 { continue }
            _, o_at, o_end := order_site_span(t, other)
            if o_at >= at && o_end <= end && order_site_in(t, s, other) {
                nested = true
                break
            }
        }
        if !nested { append(&inner, s) }
    }
    starts := make(map[Tree_Id]int, allocator = context.temp_allocator)
    for s in inner { _, starts[s.node], _ = order_site_span(t, s) }
    for i in 1 ..< len(inner) {   // (by where they start)
        for j := i; j > 0 && starts[inner[j].node] < starts[inner[j - 1].node]; j -= 1 { inner[j], inner[j - 1] = inner[j - 1], inner[j] }
    }
    for s in inner {
        _, s_at, s_end := order_site_span(t, s)
        if s_at < pos { continue }
        strings.write_string(&b, src[pos:s_at])
        strings.write_string(&b, order_site_text(t, o, to, s))
        pos = s_end
    }
    strings.write_string(&b, src[pos:end])
    return strings.to_string(b)
}

// `file:line:col` of a token.
@(private="file")
token_location :: proc(tok: Token) -> string {
    return fmt.tprintf("%s:%d:%d", build_files[tok.file].path, token_line(tok), token_col(tok))
}

// --- mara edit --------------------------------------------------------------

// `mara edit [module] <name>.<fields|results|params> <part> ...` (EDIT_USAGE):
// the order named put in the one given, in the module checked here — the
// files written. `<fun>.calls`: the fun called where its body is written out
// (shape_matches). What was done, or what stopped it (false).
edit_run :: proc(checked: ^Checked_Program, target: string, to: []string) -> (said: string, ok: bool) {
    dot := strings.last_index_byte(target, '.')
    if dot <= 0 { return fmt.tprintf("mara edit: '%s' isn't <name>.<fields|results|params|calls|do|elif>\n", target), false }
    name, kind_word := target[:dot], target[dot + 1:]
    if kind_word == "calls" { return edit_calls(checked, name) }
    if kind_word == "do" { return edit_do(checked, name) }
    if kind_word == "elif" { return edit_elif(checked, name) }
    kind: Order_Kind
    switch kind_word {
    case "fields":  kind = .Fields
    case "results": kind = .Results
    case "params":  kind = .Params
    case:           return fmt.tprintf("mara edit: '%s': what to edit is fields, results, params, calls, do or elif\n", kind_word), false
    }
    orders := orders_of(&build_tree, checked.annot)
    found := make([dynamic]Order)
    for o in orders { if o.kind == kind && o.name == name { append(&found, o) } }
    if len(found) == 0 { return fmt.tprintf("mara edit: no %s with %s named %s here\n", "struct" if kind == .Fields else "fun", kind_word, name), false }
    if len(found) > 1 {
        b := strings.builder_make()
        fmt.sbprintf(&b, "mara edit: %d named %s here — which isn't told yet:\n", len(found), name)
        for o in found { fmt.sbprintf(&b, "  %s\n", token_location(build_tokens[build_tree.first[o.def]])) }
        return strings.to_string(b), false
    }
    o := found[0]
    edits, problem := edit_order(&build_tree, o, to)
    if problem != "" { return fmt.tprintf("mara edit: %s\n", problem), false }
    if slice.equal(o.parts, to) { return fmt.tprintf("%s's %s are in that order already.\n", name, kind_word), true }
    written, failed := edit_apply(edits[:])
    if failed != "" { return failed, false }
    places := len(o.sites)
    return fmt.tprintf("%s's %s now %s: its declaration and %d place%s (%s)\n", name, kind_word, strings.join(to, ", "),
                       places, "" if places == 1 else "s", strings.join(written, ", ")), true
}

// The fun named, in the module checked: its Fun_Def and scope; else why not.
@(private="file")
edit_fun :: proc(checked: ^Checked_Program, name: string) -> (def: Tree_Id, ts: ^Type_Scope, problem: string) {
    t := &build_tree
    found := make([dynamic]Tree_Id)
    scopes := make([dynamic]^Type_Scope)
    for key, s in checked.annot.decls {
        _, n := annot_split(key)
        if s == nil || s.kind != .Fun || t.tag[n] != .Fun_Def { continue }
        if (s.source_name if s.source_name != "" else s.name) != name || slice.contains(found[:], n) { continue }
        append(&found, n)
        append(&scopes, s)
    }
    if len(found) == 0 { return 0, nil, fmt.tprintf("mara edit: no fun named %s here\n", name) }
    if len(found) > 1 {
        b := strings.builder_make()
        fmt.sbprintf(&b, "mara edit: %d funs named %s here — which isn't told yet:\n", len(found), name)
        for n in found { fmt.sbprintf(&b, "  %s\n", token_location(build_tokens[t.first[n]])) }
        return 0, nil, strings.to_string(b)
    }
    return found[0], scopes[0], ""
}

// `mara edit <fun>.calls`: the fun called in each place its body is written
// out — the run of statements there its call.
@(private="file")
edit_calls :: proc(checked: ^Checked_Program, name: string) -> (said: string, ok: bool) {
    t := &build_tree
    a := checked.annot
    def, ts, problem := edit_fun(checked, name)
    if problem != "" { return problem, false }
    matches := shape_matches(t, a, def, ts)
    if len(matches) == 0 { return fmt.tprintf("No place writes out %s's body.\n", name), true }
    edits := make([dynamic]Order_Edit)
    for m in matches {
        file, at, end := shape_span(t, m)
        append(&edits, Order_Edit{file, at, end, shape_call_text(t, name, m)})
    }
    written, failed := edit_apply(edits[:])
    if failed != "" { return failed, false }
    return fmt.tprintf("%s called in the %d place%s its body was written out (%s)\n", name, len(matches),
                       "" if len(matches) == 1 else "s", strings.join(written, ", ")), true
}

// `mara edit <fun>.do`: the fun's one-statement if chains written with `do`,
// and in its other braced chains the one-statement branches (do_edits).
@(private="file")
edit_do :: proc(checked: ^Checked_Program, name: string) -> (said: string, ok: bool) {
    t := &build_tree
    def, _, problem := edit_fun(checked, name)
    if problem != "" { return problem, false }
    found := do_edits(t, def)
    if len(found) == 0 { return fmt.tprintf("No if in %s has a branch of one statement written as a block.\n", name), true }
    edits := make([dynamic]Order_Edit)
    chains, branches := 0, 0
    for d in found {
        append(&edits, d.edit)
        if d.whole { chains += 1 } else { branches += 1 }
    }
    written, failed := edit_apply(edits[:])
    if failed != "" { return failed, false }
    parts := make([dynamic]string, context.temp_allocator)
    if chains > 0 { append(&parts, fmt.tprintf("%d if%s", chains, "" if chains == 1 else "s")) }
    if branches > 0 { append(&parts, fmt.tprintf("%d branch%s", branches, "" if branches == 1 else "es")) }
    return fmt.tprintf("%s: %s written with do (%s)\n", name, strings.join(parts[:], " and "), strings.join(written, ", ")), true
}

// `mara edit <fun>.elif`: the fun's runs of ifs, each branch leaving, joined
// into chains with elif (elif_runs).
@(private="file")
edit_elif :: proc(checked: ^Checked_Program, name: string) -> (said: string, ok: bool) {
    t := &build_tree
    def, _, problem := edit_fun(checked, name)
    if problem != "" { return problem, false }
    runs := elif_runs(t, def)
    if len(runs) == 0 { return fmt.tprintf("No ifs in %s one after another can be one chain with elif.\n", name), true }
    edits := make([dynamic]Order_Edit)
    joined := 0
    for run in runs {
        append(&edits, ..elif_edits(t, run)[:])
        joined += len(run)
    }
    written, failed := edit_apply(edits[:])
    if failed != "" { return failed, false }
    return fmt.tprintf("%s: %d ifs joined into %d chain%s with elif (%s)\n", name, joined, len(runs), "" if len(runs) == 1 else "s", strings.join(written, ", ")), true
}

// Edits made: each file's, last first, its text made again and written.
// The files written; else why not.
edit_apply :: proc(edits: []Order_Edit) -> (written: []string, problem: string) {
    by_file := make(map[u16][dynamic]Order_Edit)
    for e in edits {
        list := by_file[e.file]
        append(&list, e)
        by_file[e.file] = list
    }
    out := make([dynamic]string)
    for file, list in by_file {
        slice.sort_by(list[:], proc(x, y: Order_Edit) -> bool { return x.at > y.at })
        text := build_files[file].source
        for e in list { text = strings.concatenate({text[:e.at], e.text, text[e.end:]}) }
        path := build_files[file].path
        if err := os.write_entire_file(path, transmute([]byte)text); err != nil {
            return nil, fmt.tprintf("mara edit: %s couldn't be written: %v\n", path, err)
        }
        append(&out, path)
    }
    slice.sort(out[:])
    return out[:], ""
}
