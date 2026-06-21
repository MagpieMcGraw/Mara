package mara

// ---------------------------------------------------------------------------
// `mara ask` — static type-dependency queries (design/mara_ask.md §4.1)
//
// The first ask: a type dependency graph, read straight off the symbol table —
// no dataflow walk. The target may be a TYPE (struct / enum / union / distinct)
// or a FUNCTION name.
//   mara ask <Type|fn> deps    what it pulls in — a type's field/embed types
//                              (TRANSITIVE closure); a fun's parameter + return
//                              types (and through any struct among them).
//   mara ask <Type|fn> users   who depends on it — who contains / embeds / takes /
//                              returns it. DIRECT (one hop), NOT transitive. The
//                              "what breaks if I change this" query. CAVEAT: call
//                              edges are not yet modeled, so `users` on a fun does
//                              NOT list its callers (only type-level references,
//                              e.g. a `fn <name>` nominal type).
// Verbs accept singular or plural (`dep`/`deps`, `user`/`users`), in either order.
//
// The engine (`run_ask`) is a PURE function over Checked_Program returning an
// Ask_Result graph; the renderer is separate (a --json serializer is a trivial
// later add over the same graph). Output is a deterministic text adjacency dump:
// each type printed once with its direct typed edges, sorted for stable diffs —
// AI-readable, greppable, golden-testable. Stops after check_program (no codegen).
// ---------------------------------------------------------------------------

import "core:fmt"
import "core:slice"
import "core:strings"
import "core:path/filepath"

Ask_Edge_Kind :: enum { Contains, Embeds, Takes, Returns, Base }

Ask_Node :: struct {
    label: string,   // user-facing type / fn name
    sub:   string,   // "struct" / "enum" / "union" / "distinct" / "fun"
    span:  Span,
    mark:  string,   // "" for ordinary types; e.g. "synthetic" for compiler-generated ones
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

// The owning module's name (`mara.math`, `camera`, ""). The map / module-surface
// views group definitions by this.
ask_home_package :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    return v.home_package
    case ^Type_Enum:     return v.home_package
    case ^Type_Union:    return v.home_package
    case ^Type_Distinct: return v.home_package
    }
    return ""
}

// The user-written name. Empty for monomorphized instances and other synthetic
// types — the signal the module views use to list DECLARATIONS (the generic
// `Program`), not instances (`mara_core_Program` minted under whoever uses it).
ask_source_name :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    return v.source_name
    case ^Type_Enum:     return v.source_name
    case ^Type_Union:    return v.source_name
    case ^Type_Distinct: return v.source_name
    }
    return ""
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

// A marker for compiler-GENERATED types, "" for ordinary user declarations.
// Only the truly synthetic case (a union's `_Tag` discriminant enum) is flagged;
// variant structs are source-backed (a `Name = tag {…}` line) and stay unmarked.
ask_mark :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Enum: if v.is_synthetic { return "synthetic" }
    }
    return ""
}

ask_intern :: proc(res: ^Ask_Result, t: Type) -> (id: int, is_new: bool) {
    key := raw_type_key(t)
    if existing, ok := res.index_of[key]; ok { return existing, false }
    sub, _ := ask_sub(t)
    id = len(res.nodes)
    append(&res.nodes, Ask_Node{ label = ask_label(t), sub = sub, span = ask_span(t), mark = ask_mark(t) })
    res.index_of[key] = id
    return id, true
}

// --- target resolution (user types the source name, tables key on flat) ----

// One resolved definition the name could refer to.
Ask_Match :: struct {
    type_: Type,
    label: string,   // source / display name (what the user types)
    flat:  string,   // package-prefixed unique name
    sub:   string,   // "struct" / "enum" / "union" / "distinct" / "fun"
    span:  Span,
    mark:  string,   // "" for ordinary types; e.g. "synthetic" for compiler-generated ones
}

// Every definition in (optionally) the scoped file, deduped by (span, kind).
// The dedup is load-bearing, not cosmetic: a struct and its synthesized
// constructor live in two tables (`.structs` and `.funs`) but share one def
// site, and every monomorphization of a generic shares the generic's def site —
// so without it a perfectly unambiguous `Foo` would report as N "definitions".
// With it, those collapse to the one definition the user means, while two
// genuinely distinct same-named types (different files) stay separate. The KIND
// is part of the key because a union and its synthesized tag enum legitimately
// share one source span (the union decl) — span alone would shadow one with the
// other; same kind + same span is the actual "same definition" signal.
// `scope_file` (a bare filename) restricts to definitions declared in that file —
// the disambiguation lever behind `in <file>`.
Ask_Dedup_Key :: struct { span: Span, sub: string }

ask_all_definitions :: proc(table: ^SymbolTable, scope_file: string) -> [dynamic]Ask_Match {
    matches: [dynamic]Ask_Match
    seen: map[Ask_Dedup_Key]bool
    consider :: proc(matches: ^[dynamic]Ask_Match, seen: ^map[Ask_Dedup_Key]bool, t: Type, scope_file: string) {
        sp := ask_span(t)
        if scope_file != "" && filepath.base(sp.file) != scope_file { return }
        sub, _ := ask_sub(t)
        key := Ask_Dedup_Key{ span = sp, sub = sub }
        if seen[key] { return }
        seen[key] = true
        append(matches, Ask_Match{ type_ = t, label = ask_label(t), flat = ask_type_name(t), sub = sub, span = sp, mark = ask_mark(t) })
    }
    for _, s in table.structs        { consider(&matches, &seen, s, scope_file) }
    for _, f in table.funs           { consider(&matches, &seen, f, scope_file) }
    for _, e in table.enums          { consider(&matches, &seen, e, scope_file) }
    for _, u in table.unions         { consider(&matches, &seen, u, scope_file) }
    for _, d in table.distinct_types { consider(&matches, &seen, d, scope_file) }
    return matches
}

// Exact resolution: the definitions whose name the user typed verbatim.
ask_resolve_all :: proc(table: ^SymbolTable, target: string, scope_file: string) -> [dynamic]Ask_Match {
    out: [dynamic]Ask_Match
    for m in ask_all_definitions(table, scope_file) {
        if m.label == target || m.flat == target { append(&out, m) }
    }
    return out
}

// --- fuzzy fallback: "did you mean" when exact resolution finds nothing -------

ASK_FUZZY_LIMIT :: 7

// Loose match score, higher = better, 0 = not a candidate. Tiers (strongest
// first) so good matches always outrank weak ones: case-only equality, prefix,
// substring, a small edit distance for typos, then in-order subsequence for
// abbreviations. The `- len` tiebreakers prefer the shorter (more specific) name.
//
// Two deliberate choices keep "did you mean" honest:
//   * A real typo (small edit distance) outranks a loose subsequence, so
//     `Camara` surfaces `Camera` ABOVE sprawling matches like `camera_turn_walking`.
//   * The subsequence tier is ANCHORED on a shared first character. Without it a
//     short query coincidentally subsequences half the table (`idle` is in order
//     inside `file_delete`); anchoring kills that noise — a no-substring miss
//     with no close name now correctly suggests nothing.
ask_fuzzy_score :: proc(query, name: string) -> int {
    if len(query) == 0 || len(name) == 0 { return 0 }
    q := strings.to_lower(query)
    n := strings.to_lower(name)
    if q == n                           { return 1000 }
    if strings.has_prefix(n, q)         { return 900 - len(n) }
    if i := strings.index(n, q); i >= 0 { return 800 - i*2 - len(n) }
    d := ask_levenshtein(q, n)
    if 3*d <= len(q)                    { return 600 - d*120 }
    if q[0] == n[0] {
        if gaps, ok := ask_subseq_gaps(q, n); ok { return 400 - gaps*6 - len(n) }
    }
    return 0
}

// Are all of q's bytes present in n in order? Returns the count of n's bytes
// skipped between matches (a tightness penalty). q/n are lowercase ASCII.
ask_subseq_gaps :: proc(q, n: string) -> (gaps: int, ok: bool) {
    qi, last := 0, -1
    for i in 0 ..< len(n) {
        if qi >= len(q) { break }
        if n[i] == q[qi] {
            if last >= 0 { gaps += i - last - 1 }
            last = i
            qi += 1
        }
    }
    return gaps, qi == len(q)
}

// Classic two-row Levenshtein edit distance (ASCII, short strings).
ask_levenshtein :: proc(a, b: string) -> int {
    la, lb := len(a), len(b)
    if la == 0 { return lb }
    if lb == 0 { return la }
    prev := make([]int, lb + 1)
    curr := make([]int, lb + 1)
    for j in 0 ..= lb { prev[j] = j }
    for i in 1 ..= la {
        curr[0] = i
        for j in 1 ..= lb {
            cost := 0 if a[i-1] == b[j-1] else 1
            curr[j] = min(prev[j] + 1, curr[j-1] + 1, prev[j-1] + cost)
        }
        copy(prev, curr)
    }
    return prev[lb]
}

// Top-N definitions by fuzzy score against `target`, ties broken by name for
// determinism. Used only when exact resolution returns nothing.
ask_fuzzy :: proc(table: ^SymbolTable, target: string, scope_file: string, limit: int) -> [dynamic]Ask_Match {
    Scored :: struct { m: Ask_Match, score: int }
    pool: [dynamic]Scored
    for m in ask_all_definitions(table, scope_file) {
        if sc := ask_fuzzy_score(target, m.label); sc > 0 {
            append(&pool, Scored{ m = m, score = sc })
        }
    }
    out: [dynamic]Ask_Match
    n := len(pool)
    k := min(limit, n)
    for i in 0 ..< k {                       // partial selection of the top k
        best := i
        for j in i + 1 ..< n {
            if pool[j].score > pool[best].score ||
               (pool[j].score == pool[best].score && pool[j].m.label < pool[best].m.label) {
                best = j
            }
        }
        pool[i], pool[best] = pool[best], pool[i]
        append(&out, pool[i].m)
    }
    return out
}

// --- variant fallback: a variant name isn't a queryable type --------------

// A variant name (`Idle`, `DropFile`) is not a queryable type on its own, so
// exact resolution misses it — yet it's a natural thing to type after seeing
// `Stream_State` is an enum. Find its owning enum / union and point there
// instead of dropping to a noisy fuzzy guess. Reads only variant NAME lists
// (no union-layout machinery).
ask_find_variant :: proc(table: ^SymbolTable, target: string) -> (owner: string, kind: string, ok: bool) {
    for _, e in table.enums {
        if e.is_synthetic { continue }   // a union's internal `_Tag`: point at the union, not its tag enum
        if _, has := e.variants[target]; has { return ask_label(e), "enum", true }
    }
    for _, u in table.unions {
        for vn in u.variants {
            if vn == target { return ask_label(u), "union", true }
        }
    }
    return "", "", false
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
// Both natural spellings of each verb are accepted (singular/plural) and folded
// to the canonical form the engine switches on, so the doc's `user` and the
// engine's `users` can never drift apart again.
ask_canon_verb :: proc(s: string) -> (canon: string, ok: bool) {
    switch s {
    case "deps", "dep":   return "deps", true
    case "users", "user": return "users", true
    }
    return "", false
}

ask_is_verb :: proc(s: string) -> bool {
    _, ok := ask_canon_verb(s)
    return ok
}

// Compute one direction's graph for an already-resolved subject type.
ask_compute :: proc(table: ^SymbolTable, root: Type, verb: string) -> Ask_Result {
    res: Ask_Result
    res.root = -1
    switch verb {
    case "deps":  ask_deps(table, &res, root)
    case "users": ask_users(table, &res, root)
    }
    ask_sort_edges(&res)
    return res
}

// Top-level entry. Resolve `target` (optionally pinned to a `scope_file`), then
// render. `verb == ""` asks for BOTH directions. Returns the rendered text and
// whether a single subject was found — on false (not found / ambiguous) the text
// already explains why, and the caller exits non-zero.
ask :: proc(checked: ^Checked_Program, target, verb, pkg, scope_file: string) -> (out: string, ok: bool) {
    matches := ask_resolve_all(checked.table, target, scope_file)
    b := strings.builder_make()

    scope_desc := pkg if scope_file == "" else fmt.tprintf("%s, file %s", pkg, scope_file)

    if len(matches) == 0 {
        // A module name? Show its surface (declared types + funs). Checked before
        // the variant / fuzzy guesses — a module is an intentional, exact target.
        if surface, is_mod := ask_module_surface(checked, target); is_mod {
            return surface, true
        }
        // Before guessing: if the name is a known variant, say so — it's the
        // single most likely reason a real-looking name fails to resolve.
        if owner, kind, is_variant := ask_find_variant(checked.table, target); is_variant {
            fmt.sbprintf(&b, "mara ask: '%s' is a variant of %s %s — variants aren't queryable yet.\n", target, kind, owner)
            fmt.sbprintf(&b, "  (try `mara ask %s`)\n", owner)
            return strings.to_string(b), false
        }
        // No exact hit — offer the closest names rather than a bare miss.
        suggestions := ask_fuzzy(checked.table, target, scope_file, ASK_FUZZY_LIMIT)
        if len(suggestions) > 0 {
            fmt.sbprintf(&b, "mara ask: no exact match for '%s' in %s — did you mean:\n", target, scope_desc)
            for m in suggestions {
                fmt.sbprintf(&b, "    %-8s %s  %s%s\n", m.sub, m.label, ask_loc(m.span), ask_mark_suffix(m.mark))
            }
        } else {
            fmt.sbprintf(&b, "mara ask: no type or function named '%s' in %s\n", target, scope_desc)
        }
        fmt.sbprint(&b, "  (variables are not queryable yet — coming with variable support.)\n")
        return strings.to_string(b), false
    }
    if len(matches) > 1 {
        // Subject ambiguity: don't guess. List the candidates and tell the user
        // how to pick one. (For types this is rare; it becomes the norm only once
        // variables/slices land — the `in <scope>` lever is already here for it.)
        // Sort for a stable listing — `matches` arrives in (non-deterministic)
        // map-iteration order, like the edges that `ask_sort_edges` already fixes.
        slice.sort_by(matches[:], proc(a, b: Ask_Match) -> bool {
            if a.label != b.label         { return a.label < b.label }
            if a.span.file != b.span.file { return a.span.file < b.span.file }
            return a.span.line < b.span.line
        })
        fmt.sbprintf(&b, "mara ask: '%s' is ambiguous — %d definitions in %s (narrow with `in <module|file>`):\n",
                     target, len(matches), scope_desc)
        for m in matches {
            fmt.sbprintf(&b, "    %-8s %s  %s%s\n", m.sub, m.label, ask_loc(m.span), ask_mark_suffix(m.mark))
        }
        return strings.to_string(b), false
    }

    subject := matches[0]
    fmt.sbprintf(&b, "%s — %s  %s   (module %s)%s\n", subject.label, subject.sub, ask_loc(subject.span), pkg, ask_mark_suffix(subject.mark))

    if verb == "" || verb == "deps" {
        res := ask_compute(checked.table, subject.type_, "deps")
        render_ask_deps(&b, &res)
    }
    if verb == "" || verb == "users" {
        res := ask_compute(checked.table, subject.type_, "users")
        render_ask_users(&b, &res, subject.sub == "fun")
    }
    // The broad "tell me about this name" form is honest about its coverage gap;
    // the targeted deps/users forms stay terse.
    if verb == "" {
        fmt.sbprint(&b, "\n(variables: not queryable yet)\n")
    }
    return strings.to_string(b), true
}

// --- renderer (text adjacency dump) ----------------------------------------

// deps: one adjacency block per node (root first), each node with its location
// and its direct typed edges. The whole block is the TRANSITIVE closure.
render_ask_deps :: proc(b: ^strings.Builder, res: ^Ask_Result) {
    // Count TYPE nodes only — the root may be a `fun` (the subject), which is not
    // a type and must not inflate the count (a fn's own node sits at index 0).
    types := 0
    for n in res.nodes { if n.sub != "fun" { types += 1 } }
    fmt.sbprintf(b, "\ndeps   (%d types, %d edges, TRANSITIVE closure)\n", types, len(res.edges))
    for node, i in res.nodes {
        fmt.sbprintf(b, "\n  %s  %s  %s%s\n", node.label, node.sub, ask_loc(node.span), ask_mark_suffix(node.mark))
        any := false
        for e in res.edges {
            if e.from != i { continue }
            any = true
            tgt := res.nodes[e.to]
            via := fmt.tprintf(" %s", e.via) if e.via != "" else ""
            fmt.sbprintf(b, "    %s%s : %s%s\n", ask_edge_word(e.kind), via, e.wrap, tgt.label)
        }
        if !any { fmt.sbprint(b, "    (no type dependencies)\n") }
    }
}

// users: the DIRECT (one-hop) reverse references. Header separates distinct
// users from use-sites so neither count is misread.
render_ask_users :: proc(b: ^strings.Builder, res: ^Ask_Result, subject_is_fun: bool) {
    fmt.sbprintf(b, "\nusers   (%d users, %d use-sites, DIRECT one-hop)\n",
                 ask_distinct_sources(res), len(res.edges))
    // A function subject's reverse set is a known blind spot: call edges are not
    // modeled, so `(no users)` here must NOT be read as "no callers".
    if subject_is_fun {
        fmt.sbprint(b, "  note: call edges are NOT tracked yet — this lists only type-level\n")
        fmt.sbprint(b, "        references (e.g. a `fn <name>` nominal type), NOT callers.\n")
    }
    if len(res.edges) == 0 { fmt.sbprint(b, "  (no users)\n"); return }
    root_label := res.nodes[res.root].label
    for e in res.edges {
        u := res.nodes[e.from]
        via := fmt.tprintf(" %s", e.via) if e.via != "" else ""
        fmt.sbprintf(b, "  %-6s %s  (%s%s : %s%s)%s\n", u.sub, u.label, ask_edge_word(e.kind), via, e.wrap, root_label, ask_mark_suffix(u.mark))
    }
}

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

// A type's marker as a bracketed suffix (" [synthetic]"), or "" when ordinary.
ask_mark_suffix :: proc(mark: string) -> string {
    return "" if mark == "" else fmt.tprintf(" [%s]", mark)
}

// Distinct source nodes among the edges — the real "how many things use this"
// count, as opposed to len(edges), which counts use-SITES: one fn taking the
// type in two params (or returning it twice) is ONE user but several sites.
ask_distinct_sources :: proc(res: ^Ask_Result) -> int {
    seen: map[int]bool
    for e in res.edges { seen[e.from] = true }
    return len(seen)
}

// ---------------------------------------------------------------------------
// Module-level orientation: the map (`mara ask`) and the surface (`mara ask
// <Module>`). These sit ABOVE the per-name views — the drill-down is
// map -> module -> name -> deps/users, each level pointing at the next.
// ---------------------------------------------------------------------------

ask_plural :: proc(n: int, noun: string) -> string {
    return fmt.tprintf("%d %s", n, noun) if n == 1 else fmt.tprintf("%d %ss", n, noun)
}

// Does `file` belong to the stdlib? Discovery stores stdlib files with an
// absolute path under `compiler_dir` and local files relative to the cwd, so a
// prefix match (when compiler_dir is absolute) or, failing that, absoluteness
// itself classifies it. "local" is the safe default.
ask_file_is_stdlib :: proc(file, compiler_dir: string) -> bool {
    if file == "" { return false }
    if compiler_dir != "" && strings.has_prefix(file, compiler_dir) { return true }
    return filepath.is_abs(file)
}

// A type's distinct-user count — the reverse-edge in-degree, reusing the very
// graph `users` renders. The orientation signal for "which type matters here".
ask_user_count :: proc(table: ^SymbolTable, t: Type) -> int {
    res := ask_compute(table, t, "users")
    return ask_distinct_sources(&res)
}

// --- module surface: what one module declares ------------------------------

// `home_package` is the module name verbatim (`mara.math`, `camera`); the `mara.`
// prefix is an optional alias (the checker resolves `math` to `mara.math` too —
// see is_package), so both spellings match here.
ask_module_name_matches :: proc(home, query: string) -> bool {
    if home == query { return true }
    return strings.has_prefix(home, "mara.") && home[len("mara."):] == query
}

// `mara ask <Module>` — the module's own types (ranked by how many things use
// them) and funs (source order). Returns ok=false when `target` names no loaded
// module, so the caller falls through to variant / fuzzy handling.
ask_module_surface :: proc(checked: ^Checked_Program, target: string) -> (out: string, ok: bool) {
    Entry :: struct { m: Ask_Match, users: int }
    types: [dynamic]Entry
    funs:  [dynamic]Ask_Match
    canonical := target
    for m in ask_all_definitions(checked.table, "") {
        hp := ask_home_package(m.type_)
        if m.mark == "synthetic" || ask_source_name(m.type_) == "" { continue }   // skip instances/synthetic
        if !ask_module_name_matches(hp, target) { continue }
        canonical = hp
        if m.sub == "fun" { append(&funs, m) }
        else              { append(&types, Entry{ m = m, users = ask_user_count(checked.table, m.type_) }) }
    }
    if len(types) == 0 && len(funs) == 0 { return "", false }   // not a (loaded) module

    slice.sort_by(types[:], proc(a, b: Entry) -> bool {
        if a.users != b.users { return a.users > b.users }      // most-used first
        return a.m.label < b.m.label
    })
    slice.sort_by(funs[:], proc(a, b: Ask_Match) -> bool {
        if a.span.file != b.span.file { return a.span.file < b.span.file }
        return a.span.line < b.span.line
    })

    b := strings.builder_make()
    fmt.sbprintf(&b, "%s — module   (%s, %s)\n", canonical, ask_plural(len(types), "type"), ask_plural(len(funs), "fun"))
    if len(types) > 0 {
        fmt.sbprint(&b, "\n  types        (most-used first)\n")
        for e in types {
            tail := fmt.tprintf("   ·  %s", ask_plural(e.users, "user")) if e.users > 0 else ""
            fmt.sbprintf(&b, "    %-8s %s  %s%s%s\n", e.m.sub, e.m.label, ask_loc(e.m.span), ask_mark_suffix(e.m.mark), tail)
        }
    }
    if len(funs) > 0 {
        fmt.sbprint(&b, "\n  funs         (source order)\n")
        for m in funs {
            fmt.sbprintf(&b, "    %-8s %s  %s\n", m.sub, m.label, ask_loc(m.span))
        }
    }
    return strings.to_string(b), true
}

// --- module map: the project at a glance -----------------------------------

Ask_Module_Info :: struct {
    name:     string,   // source module name, e.g. "mara.core"
    types:    int,
    funs:     int,
    has_main: bool,
    stdlib:   bool,
}

// `mara ask` with no name — every loaded module with its declared-type / fun
// counts, local modules first (a stranger's entry point), stdlib after. Modules
// carrying a `main` are flagged: the cwd's entry points. The hint teaches the
// next drill-down step.
ask_module_map :: proc(checked: ^Checked_Program, programs: map[string]^Program, all_files: map[string][dynamic]^Source_File, compiler_dir, root_pkg: string) -> string {
    // One pass over the deduped definitions -> per-module (flat) counts + a
    // representative file for the local/stdlib split. Tables hold every CHECKED
    // module — local AND the stdlib modules actually pulled in — so this is the
    // authoritative module set (`programs` carries only the local ones).
    Counts :: struct { types, funs: int, file: string }
    by_home: map[string]Counts
    for m in ask_all_definitions(checked.table, "") {
        if m.mark == "synthetic" || ask_source_name(m.type_) == "" { continue }   // skip instances/synthetic
        hp := ask_home_package(m.type_)
        if hp == "" { continue }
        c := by_home[hp]
        if m.sub == "fun" { c.funs += 1 } else { c.types += 1 }
        if c.file == "" { c.file = m.span.file }
        by_home[hp] = c
    }

    // `home_package` IS the module name (`mara.math`, `camera`) — the same key
    // `all_files` and `programs` use. A home that names no discovered module is
    // an internal/synthetic package (skip it).
    infos: [dynamic]Ask_Module_Info
    for hp, c in by_home {
        if hp not_in all_files { continue }
        prog, in_programs := programs[hp]
        append(&infos, Ask_Module_Info{
            name = hp, types = c.types, funs = c.funs,
            has_main = in_programs && pkg_has_main(prog),
            stdlib   = ask_file_is_stdlib(c.file, compiler_dir),
        })
    }
    slice.sort_by(infos[:], proc(a, b: Ask_Module_Info) -> bool {
        if a.stdlib != b.stdlib { return !a.stdlib }   // local before stdlib
        return a.name < b.name
    })

    b := strings.builder_make()
    fmt.sbprintf(&b, "%s — module map   (run `mara ask <module>` to look inside one)\n", root_pkg)
    group := ""
    for info in infos {
        g := "stdlib" if info.stdlib else "your code"
        if g != group { fmt.sbprintf(&b, "\n  %s\n", g); group = g }
        main_tag := "   · main" if info.has_main else ""
        fmt.sbprintf(&b, "    %-14s %-9s · %s%s\n",
                     info.name, ask_plural(info.types, "type"), ask_plural(info.funs, "fun"), main_tag)
    }
    return strings.to_string(b)
}
