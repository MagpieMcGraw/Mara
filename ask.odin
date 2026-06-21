package mara

// ---------------------------------------------------------------------------
// `mara ask` — static type-dependency queries (design/mara_ask.md §4.1)
//
// The first ask: a type dependency graph, read straight off the symbol table —
// no dataflow walk.
//   mara ask <Type> deps    what this type pulls in (its field/embed types,
//                           transitively; a fun's signature types)
//   mara ask <Type> users   who depends on it (who contains/embeds/takes/returns
//                           it) — the "what breaks if I change this" query
//
// The engine (`run_ask`) is a PURE function over Checked_Program returning an
// Ask_Result graph; the renderer is separate (a --json serializer is a trivial
// later add over the same graph). Output is a deterministic text adjacency dump:
// each type printed once with its direct typed edges, sorted for stable diffs —
// AI-readable, greppable, golden-testable. Stops after check_program (no codegen).
// ---------------------------------------------------------------------------

import "core:fmt"
import "core:strings"

Ask_Edge_Kind :: enum { Contains, Embeds, Takes, Returns, Base }

Ask_Node :: struct {
    label: string,   // user-facing type / fn name
    sub:   string,   // "struct" / "enum" / "union" / "distinct" / "fun"
    span:  Span,
}

Ask_Edge :: struct {
    from, to: int,
    kind:     Ask_Edge_Kind,
    via:      string,   // field / param name carrying the dependency ("" for returns / base)
    wrap:     string,   // "^" / "[]" wrapper shown on the target, "" if direct
}

Ask_Result :: struct {
    nodes:    [dynamic]Ask_Node,
    edges:    [dynamic]Ask_Edge,
    root:     int,
    index_of: map[rawptr]int,   // type identity -> node id (intern dedup)
}

// --- type → display helpers ------------------------------------------------

ask_label :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    return v.source_name if v.source_name != "" else ask_demangle(v.name, v.home_package)
    case ^Type_Enum:     return v.source_name if v.source_name != "" else ask_demangle(v.name, v.home_package)
    case ^Type_Union:    return v.source_name if v.source_name != "" else ask_demangle(v.name, v.home_package)
    case ^Type_Distinct: return v.source_name if v.source_name != "" else ask_demangle(v.name, v.home_package)
    }
    return type_flat_name(t)
}

// A flat name is `<flattened home_package>_<bare>` (the module path's dots become
// underscores in the mangle, e.g. home "mara.math" -> name "mara_math_Vec3").
// Recover the bare name for display when no source_name was recorded (cross-module
// / monomorphized types).
ask_demangle :: proc(name: string, home_package: string) -> string {
    if home_package == "" { return name }
    flat_home, _ := strings.replace_all(home_package, ".", "_")
    if strings.has_prefix(name, flat_home) {
        rest := name[len(flat_home):]
        if len(rest) > 1 && rest[0] == '_' { return rest[1:] }
    }
    return name
}

// The node's category, and whether it is a NAMED type worth a node at all
// (primitives / numerics are leaves — not type dependencies, so not interned).
ask_sub :: proc(t: Type) -> (sub: string, named: bool) {
    #partial switch v in t {
    case ^Type_Scope:    return ("fun" if v.kind == .Fun else "struct"), true
    case ^Type_Enum:     return "enum", true
    case ^Type_Union:    return "union", true
    case ^Type_Distinct: return "distinct", true
    }
    return "", false
}

ask_span :: proc(t: Type) -> Span {
    #partial switch v in t {
    case ^Type_Scope:    return v.body_span
    case ^Type_Enum:     return v.span
    case ^Type_Union:    return v.span
    case ^Type_Distinct: return v.span
    }
    return Span{}
}

// structs / unions / distinct have further type deps worth recursing into; enums
// are leaves (variants are integer constants), and funs expand only at the root.
ask_recurses :: proc(t: Type) -> bool {
    #partial switch v in t {
    case ^Type_Scope:    return v.kind == .Struct
    case ^Type_Union:    return true
    case ^Type_Distinct: return true
    }
    return false
}

// Peel ^ / [] / [N] wrappers, returning the core type and a wrapper prefix
// (outermost first) to render on the target — e.g. `[]^Mesh` -> (Mesh, "[]^").
ask_peel :: proc(t: Type) -> (core: Type, wrap: string) {
    cur := t
    parts: [dynamic]string
    peel: for {
        #partial switch v in cur {
        case ^Type_Ptr:           append(&parts, "^");    cur = v.elem
        case ^Type_Slice:         append(&parts, "[]");   cur = v.elem
        case ^Type_Fixed_Array:   append(&parts, "[]");   cur = v.elem
        case ^Type_Partial_Array: append(&parts, "[..]"); cur = v.elem
        case: break peel
        }
    }
    return cur, strings.concatenate(parts[:])
}

// --- node interning --------------------------------------------------------

ask_intern :: proc(res: ^Ask_Result, t: Type) -> (id: int, is_new: bool) {
    key := raw_type_key(t)
    if existing, ok := res.index_of[key]; ok { return existing, false }
    sub, _ := ask_sub(t)
    id = len(res.nodes)
    append(&res.nodes, Ask_Node{ label = ask_label(t), sub = sub, span = ask_span(t) })
    res.index_of[key] = id
    return id, true
}

// --- target resolution (user types the source name, tables key on flat) ----

ask_resolve :: proc(table: ^SymbolTable, target: string) -> (Type, bool) {
    for _, s in table.structs        { if s.source_name == target || s.name == target { return s, true } }
    for _, f in table.funs           { if f.source_name == target || f.name == target { return f, true } }
    for _, e in table.enums          { if e.source_name == target || e.name == target { return e, true } }
    for _, u in table.unions         { if u.source_name == target || u.name == target { return u, true } }
    for _, d in table.distinct_types { if d.source_name == target || d.name == target { return d, true } }
    return nil, false
}

// --- deps: forward type-dependency walk ------------------------------------

// Outgoing typed edges of a container type — the SINGLE source of truth shared
// by `deps` (forward) and `users` (reverse), so the two can never disagree about
// the graph. struct/ctor -> its fields; fun -> params + returns; distinct -> its
// base; union -> its variant structs. NOTE: a parameterized struct is stored as
// a `kind == .Struct` callable in `table.funs` (its constructor), with its data
// fields in `.fields` (not `.params`) — so a full reverse scan MUST route every
// container through here, or every field of a generic goes missing from `users`.
Ask_Out_Edge :: struct {
    core: Type,            // target type, wrappers already peeled (may be primitive — caller filters)
    kind: Ask_Edge_Kind,
    via:  string,          // field / param name ("" for returns / base)
    wrap: string,          // "^" / "[]" / "[..]" prefix shown on the target
}

ask_out_edges :: proc(table: ^SymbolTable, t: Type, out: ^[dynamic]Ask_Out_Edge) {
    add :: proc(out: ^[dynamic]Ask_Out_Edge, ty: Type, kind: Ask_Edge_Kind, via: string) {
        core, wrap := ask_peel(ty)
        append(out, Ask_Out_Edge{ core = core, kind = kind, via = via, wrap = wrap })
    }
    #partial switch v in t {
    case ^Type_Scope:
        if v.kind == .Struct {
            for f in v.fields { add(out, f.type_, (.Embeds if f.is_using else .Contains), f.name) }
        } else {
            for p in v.params        { add(out, p.type_, .Takes, p.name) }
            for rt in v.return_types { add(out, rt, .Returns, "") }
        }
    case ^Type_Distinct:
        add(out, v.base_type, .Base, "")
    case ^Type_Union:
        // A union depends on its variant structs (looked up via variant_structs).
        for vn in v.variants {
            sname, ok := v.variant_structs[vn]; if !ok { continue }
            st, ok2 := table.structs[sname];    if !ok2 { continue }
            append(out, Ask_Out_Edge{ core = Type(st), kind = .Contains, via = vn, wrap = "" })
        }
    }
}

ask_emit_deps :: proc(table: ^SymbolTable, res: ^Ask_Result, t: Type, from: int, worklist: ^[dynamic]Type) {
    edges: [dynamic]Ask_Out_Edge
    ask_out_edges(table, t, &edges)
    for e in edges {
        if _, named := ask_sub(e.core); !named { continue }   // skip primitive / numeric leaves
        to, _ := ask_intern(res, e.core)
        append(&res.edges, Ask_Edge{ from = from, to = to, kind = e.kind, via = e.via, wrap = e.wrap })
        if ask_recurses(e.core) { append(worklist, e.core) }
    }
}

ask_deps :: proc(table: ^SymbolTable, res: ^Ask_Result, root: Type) {
    rid, _ := ask_intern(res, root)
    res.root = rid
    worklist: [dynamic]Type
    append(&worklist, root)
    processed: map[rawptr]bool
    for len(worklist) > 0 {
        t := pop(&worklist)
        key := raw_type_key(t)
        if processed[key] { continue }
        processed[key] = true
        from, _ := ask_intern(res, t)
        ask_emit_deps(table, res, t, from, &worklist)
    }
}

// --- users: reverse — who references the target ----------------------------

// Match by the flat (package-prefixed, globally unique) NAME, not by pointer
// identity. A parameterized struct's monomorphized fields hold distinct type-
// objects that nonetheless share the canonical flat name, so a raw-pointer
// compare silently misses every usage inside a generic — the exact "what breaks
// if I change this" the query exists to answer. The forward `deps` walk is
// immune because it interns whatever object it meets and labels it by
// source_name; only this reverse compare-against-a-resolved-target needs a
// monomorphization-stable key.
ask_type_name :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    return v.name
    case ^Type_Enum:     return v.name
    case ^Type_Union:    return v.name
    case ^Type_Distinct: return v.name
    }
    return ""
}

// Scan one container's outgoing edges (via the shared model) for any that land
// on the target, recording each as a reverse edge. Dedups by container identity
// because a scope can be reachable from more than one table.
ask_scan_user :: proc(table: ^SymbolTable, res: ^Ask_Result, seen: ^map[rawptr]bool, container: Type, rid: int, tname: string) {
    // A module namespace is not a "user" of the types it declares — declaring is
    // not using. (Module structs carry no data fields, so the field scan is
    // already empty for them; this stays as the explicit invariant.)
    if sc, ok := container.(^Type_Scope); ok && sc.is_module { return }
    key := raw_type_key(container)
    if seen[key] { return }
    seen[key] = true
    edges: [dynamic]Ask_Out_Edge
    ask_out_edges(table, container, &edges)
    for e in edges {
        if ask_type_name(e.core) != tname { continue }
        uid, _ := ask_intern(res, container)
        append(&res.edges, Ask_Edge{ from = uid, to = rid, kind = e.kind, via = e.via, wrap = e.wrap })
    }
}

ask_users :: proc(table: ^SymbolTable, res: ^Ask_Result, target: Type) {
    rid, _ := ask_intern(res, target)
    res.root = rid
    tname := ask_type_name(target)
    if tname == "" { return }   // an unnamed target can't be matched by name
    // Every container kind, mirroring `deps`. Parameterized structs live in
    // `table.funs` (as `kind == .Struct` constructors), so both scope tables
    // must be walked — scanning only `table.structs` misses every generic.
    seen: map[rawptr]bool
    for _, s in table.structs        { ask_scan_user(table, res, &seen, s, rid, tname) }
    for _, s in table.funs           { ask_scan_user(table, res, &seen, s, rid, tname) }
    for _, u in table.unions         { ask_scan_user(table, res, &seen, u, rid, tname) }
    for _, d in table.distinct_types { ask_scan_user(table, res, &seen, d, rid, tname) }
}

// --- determinism: sort edges so the rendered output is golden-test stable ---
// Tables are maps (non-deterministic iteration), so edges must be sorted by a
// content key. Edge counts per query are small, so an O(n^2) selection sort with
// no closure-capture (res passed explicitly) is the simplest correct option.

ask_edge_key :: proc(res: ^Ask_Result, e: Ask_Edge) -> string {
    return fmt.tprintf("%s|%02d|%s|%s", res.nodes[e.from].label, int(e.kind), e.via, res.nodes[e.to].label)
}

ask_sort_edges :: proc(res: ^Ask_Result) {
    n := len(res.edges)
    for i in 0 ..< n {
        m := i
        for j in i + 1 ..< n {
            if ask_edge_key(res, res.edges[j]) < ask_edge_key(res, res.edges[m]) { m = j }
        }
        if m != i { res.edges[i], res.edges[m] = res.edges[m], res.edges[i] }
    }
}

// --- engine entry ----------------------------------------------------------

// The closed set of query verbs — lets the CLI accept the target and verb in
// EITHER order (`ask deps Font` or `ask Font deps`) by spotting which is a verb.
ask_is_verb :: proc(s: string) -> bool {
    return s == "deps" || s == "users"
}

run_ask :: proc(checked: ^Checked_Program, target: string, verb: string) -> (Ask_Result, bool) {
    res: Ask_Result
    res.root = -1
    root, found := ask_resolve(checked.table, target)
    if !found { return res, false }
    switch verb {
    case "deps":  ask_deps(checked.table, &res, root)
    case "users": ask_users(checked.table, &res, root)
    case:         return res, false
    }
    ask_sort_edges(&res)
    return res, true
}

// --- renderer (text adjacency dump) ----------------------------------------

ask_edge_word :: proc(k: Ask_Edge_Kind) -> string {
    #partial switch k {
    case .Contains: return "field"
    case .Embeds:   return "embed"
    case .Takes:    return "param"
    case .Returns:  return "return"
    case .Base:     return "base"
    }
    return "?"
}

ask_loc :: proc(span: Span) -> string {
    if span.file == "" { return "?" }
    return fmt.tprintf("%s:%d", span.file, span.line)
}

render_ask :: proc(res: ^Ask_Result, target: string, verb: string) -> string {
    b := strings.builder_make()

    if verb == "users" {
        root := res.nodes[res.root]
        fmt.sbprintf(&b, "ask users %s   (%d users)\n\n", target, len(res.edges))
        fmt.sbprintf(&b, "%s  %s  %s\n", root.label, root.sub, ask_loc(root.span))
        if len(res.edges) == 0 { fmt.sbprint(&b, "  (no users)\n"); return strings.to_string(b) }
        fmt.sbprint(&b, "  used by:\n")
        for e in res.edges {
            u := res.nodes[e.from]
            via := fmt.tprintf(" %s", e.via) if e.via != "" else ""
            fmt.sbprintf(&b, "    %-6s %s  (%s%s : %s%s)\n", u.sub, u.label, ask_edge_word(e.kind), via, e.wrap, target)
        }
        return strings.to_string(b)
    }

    // deps: one adjacency block per node, root first (interned at id 0).
    fmt.sbprintf(&b, "ask deps %s   (%d types, %d edges)\n", target, len(res.nodes), len(res.edges))
    for node, i in res.nodes {
        fmt.sbprintf(&b, "\n%s  %s  %s\n", node.label, node.sub, ask_loc(node.span))
        any := false
        for e in res.edges {
            if e.from != i { continue }
            any = true
            tgt := res.nodes[e.to]
            via := fmt.tprintf(" %s", e.via) if e.via != "" else ""
            fmt.sbprintf(&b, "  %s%s : %s%s\n", ask_edge_word(e.kind), via, e.wrap, tgt.label)
        }
        if !any { fmt.sbprint(&b, "  (no type dependencies)\n") }
    }
    return strings.to_string(b)
}
