package mara

// ---------------------------------------------------------------------------
// `mara ask` — static type-dependency queries (design/mara_ask.md §4.1)
//
// The first ask: a type dependency graph, read straight off the symbol table —
// no dataflow walk. The target may be a TYPE (struct / enum / union / distinct)
// or a FUNCTION name.
//   mara ask <Type|fn> deps    what it pulls in — a type's field/embed types;
//                              a fun's parameter + return types (and through any
//                              struct among them).
//   mara ask <Type|fn> users   who depends on it — who contains / embeds / takes /
//                              returns it. The "what breaks if I change this"
//                              query. CAVEAT: call edges are not yet modeled, so
//                              `users` on a fun does NOT list its callers (only
//                              type-level references, e.g. a `fn <name>` type).
//   mara ask <Type|fn> [depth] both directions take an optional hop budget:
//                              0 = direct edges only, omitted = the full
//                              transitive closure (the default). Same knob both
//                              ways — it caps `deps` and expands `users`.
// Verbs accept singular or plural (`dep`/`deps`, `user`/`users`), in either order;
// a bare integer anywhere among the tokens is the depth.
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

// The full edge set — the default `root_filter` for `ask_deps`, i.e. follow every
// kind of outgoing edge from the root. A function's type graph narrows this to
// `{.Takes}` (above = parameter types) or `{.Returns}` (below = return types) so
// the two directions split the signature; structs keep the full set (their fields
// are Contains/Embeds and there is only one direction to walk forward).
ASK_ALL_EDGES :: bit_set[Ask_Edge_Kind]{ .Contains, .Embeds, .Takes, .Returns, .Base }

Ask_Node :: struct {
    label: string,        // user-facing type / fn name
    home_package: string, // owning module, for a qualified display name (math.Vec3)
    sub:   string,   // "struct" / "union" / "error" / "distinct" / "fun" ("enum" only for a union's synthetic tag)
    span:  Span,
    mark:  string,   // "" for ordinary types; e.g. "synthetic" for compiler-generated ones
    dist:  int,      // shortest hop distance from the query root (0 = the root itself)
    basics: [dynamic]Ask_Basic,  // basic-typed members (primitive fields / params) — shown inline, no graph node
}

// A primitive member that carries no graph node of its own — the field/param name,
// what kind of member it is, and its rendered type. Stored structured (not a
// pre-formatted line) so the tree renderer can re-indent it and drop the word.
Ask_Basic :: struct {
    via:      string,
    kind:     Ask_Edge_Kind,
    type_str: string,
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

// Module-qualified display name — `gfx.shader.compile`, or the bare name when the
// type has no home package. Used by the call-tree rows so a name read in isolation
// still says which module it lives in.
ask_qualified_label :: proc(t: Type) -> string {
    home := ask_home_package(t)
    if home == "" { return ask_label(t) }
    return fmt.tprintf("%s.%s", home, ask_label(t))
}

// The node's category, and whether it is a NAMED type worth a node at all
// (primitives / numerics are leaves — not type dependencies, so not interned).
ask_sub :: proc(t: Type) -> (sub: string, named: bool) {
    #partial switch v in t {
    case ^Type_Scope:    return ("fun" if v.kind == .Fun else "struct"), true
    case ^Type_Enum:     return ask_enum_sub(v), true
    case ^Type_Union:    return "union", true
    case ^Type_Distinct: return "distinct", true
    }
    return "", false
}

// A Type_Enum is never spelled `enum` in Mara source — there is no `enum`
// keyword. It is the lowered form of a payloadless `union { ... }` (the common
// case), an `error { ... }` set, or a data union's compiler-generated `_Tag`
// discriminant. Report the SOURCE form so `mara ask` echoes what the user wrote.
// The synthetic `_Tag` keeps the "enum" label deliberately: a data union's
// Type_Union shares its span, and ask_all_definitions dedups on (span, sub), so
// relabeling the tag "union" would collapse it onto the union and hide one.
ask_enum_sub :: proc(e: ^Type_Enum) -> string {
    if e.is_synthetic  { return "enum" }
    if e.is_error_kind { return "error" }
    return "union"
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

// An FFI function — a `fun` inside a `foreign` block. These live ONLY in
// checked.functions (never table.funs) and carry no source_name (their bare name
// is recovered from the mangled name by ask_demangle), so the enumerators add
// them explicitly and the module views keep them past the "drop the unnamed"
// instance filter.
ask_is_foreign :: proc(t: Type) -> bool {
    if ts, ok := t.(^Type_Scope); ok {
        _, is_ffi := ts.origin.(Origin_Foreign)
        return is_ffi
    }
    return false
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

// Peel ^ / [] / [N] / [..] wrappers, returning the core type and a wrapper prefix
// (outermost first) to render on the target — e.g. `[]^Mesh` -> (Mesh, "[]^"),
// `[4][4]f32` -> (f32, "[4][4]"). Fixed-array SIZES are kept so the wrapper reads
// back as source (Vec3's `[3]f32` vs Quat's `[4]f32` stay distinct — collapsing
// both to `[]f32` made them indistinguishable). Slices stay `[]` (no compile-time
// size) and partial arrays `[..]` (capacity omitted — often unspecified at decl).
ask_peel :: proc(t: Type) -> (core: Type, wrap: string) {
    cur := t
    parts: [dynamic]string
    peel: for {
        #partial switch v in cur {
        case ^Type_Ptr:           append(&parts, "^");    cur = v.elem
        case ^Type_Slice:         append(&parts, "[]");   cur = v.elem
        case ^Type_Fixed_Array:   append(&parts, fmt.tprintf("[%d]", v.size)); cur = v.elem
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
    append(&res.nodes, Ask_Node{ label = ask_label(t), home_package = ask_home_package(t), sub = sub, span = ask_span(t), mark = ask_mark(t) })
    res.index_of[key] = id
    return id, true
}

// --- target resolution (user types the source name, tables key on flat) ----

// One resolved definition the name could refer to.
Ask_Match :: struct {
    type_: Type,
    label: string,   // source / display name (what the user types)
    flat:  string,   // package-prefixed unique name
    sub:   string,   // "struct" / "union" / "error" / "distinct" / "fun" ("enum" only for a union's synthetic tag)
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

ask_all_definitions :: proc(table: ^SymbolTable, scope_file: string, funcs: map[string]^Type_Scope, scope_module := "") -> [dynamic]Ask_Match {
    matches: [dynamic]Ask_Match
    seen: map[Ask_Dedup_Key]bool
    consider :: proc(matches: ^[dynamic]Ask_Match, seen: ^map[Ask_Dedup_Key]bool, t: Type, scope_file: string, scope_module: string) {
        // A module's backing namespace is a `.Struct`-kind Type_Scope with
        // is_module set — a compiler-generated scope holding the module's defs,
        // not a data type. It has no fields, no span, and no users, yet ask_sub
        // labels it "struct" and ask_label gives it the module's own name (any
        // case — `camera`, `Pounce`). Enumerating it lets `mara ask <module>`
        // resolve to a phantom `struct ?` subject instead of the module surface.
        // Worse, which module won was map-order-dependent: every such scope shares
        // the empty-span dedup key, so only one survived per run (why `mara ask
        // Pounce` usually worked while peers flaked). Module names are served by
        // ask_module_surface / the module map; skip the namespace here so a module
        // name always resolves there, structurally (not by case) — while a
        // separately-named data type like the struct `Camera` resolves as itself.
        if ts, ok := t.(^Type_Scope); ok && ts.is_module { return }
        sp := ask_span(t)
        if scope_file != "" && filepath.base(sp.file) != scope_file { return }
        // `in <module>` narrows resolution to one module's namespace — the same
        // disambiguation lever as scope_file, one level coarser. The analysis root
        // never moves (always cwd + the stdlib it uses); this only filters which
        // definition of a name the subject resolves to.
        if scope_module != "" && ask_home_package(t) != scope_module { return }
        sub, _ := ask_sub(t)
        key := Ask_Dedup_Key{ span = sp, sub = sub }
        if seen[key] { return }
        seen[key] = true
        append(matches, Ask_Match{ type_ = t, label = ask_label(t), flat = ask_type_name(t), sub = sub, span = sp, mark = ask_mark(t) })
    }
    for _, s in table.structs        { consider(&matches, &seen, s, scope_file, scope_module) }
    for _, f in table.funs           { consider(&matches, &seen, f, scope_file, scope_module) }
    for _, e in table.enums          { consider(&matches, &seen, e, scope_file, scope_module) }
    for _, u in table.unions         { consider(&matches, &seen, u, scope_file, scope_module) }
    for _, d in table.distinct_types { consider(&matches, &seen, d, scope_file, scope_module) }
    // FFI functions are absent from table.funs — surface the foreign ones from
    // checked.functions so resolution, fuzzy, and the module views all see them.
    for _, f in funcs { if ask_is_foreign(f) { consider(&matches, &seen, f, scope_file, scope_module) } }
    return matches
}

// Exact resolution: the definitions whose name the user typed verbatim.
ask_resolve_all :: proc(table: ^SymbolTable, target: string, scope_file: string, funcs: map[string]^Type_Scope, scope_module := "") -> [dynamic]Ask_Match {
    out: [dynamic]Ask_Match
    for m in ask_all_definitions(table, scope_file, funcs, scope_module) {
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

// A leftover ask token that is neither the subject name nor a live filter. Tells
// a RETIRED keyword (give the current spelling) apart from a TYPO of a live
// filter (suggest it) apart from a genuine second name (no hint — the caller
// falls back to the plain "expected one name"). Without this, `... lineage` and
// `... flw` both misreport as a stray second name, hiding the real mistake.
ask_keyword_hint :: proc(tok: string) -> (hint: string, ok: bool) {
    switch strings.to_lower(tok) {
    case "lineage", "source", "provenance":
        return "`lineage` is retired — a variable's `flow above` IS its lineage tree. Try `mara ask <var> in <fn> flow above`, or just `<var> in <fn>` (which already shows flow).", true
    case "deps", "uses", "users", "contributors", "affects":
        return fmt.tprintf("`%s` is retired — kinds are now `types` / `call` / `flow`, each with `above` / `below`. See `mara ask --help`.", tok), true
    }
    // A typo of a live filter? Anchor on the first letter and require a small edit
    // distance relative to the token — mirroring the name-fuzzy edit tier — so
    // `flw`->`flow` and `typs`->`types` resolve, but a real short name like `cam`
    // is not dragged onto `call`.
    lower := strings.to_lower(tok)
    if len(lower) == 0 { return "", false }
    KEYWORDS := []string{"types", "call", "flow", "above", "below", "control"}
    best, best_d := "", max(int)
    for k in KEYWORDS {
        if d := ask_levenshtein(lower, k); d < best_d { best_d, best = d, k }
    }
    if best_d > 0 && lower[0] == best[0] && 3 * best_d <= len(lower) {
        return fmt.tprintf("unknown filter `%s` — did you mean `%s`? (filters: types|call|flow, above|below, control)", tok, best), true
    }
    return "", false
}

// Top-N definitions by fuzzy score against `target`, ties broken by name for
// determinism. Used only when exact resolution returns nothing.
ask_fuzzy :: proc(table: ^SymbolTable, target: string, scope_file: string, limit: int, funcs: map[string]^Type_Scope, scope_module := "") -> [dynamic]Ask_Match {
    Scored :: struct { m: Ask_Match, score: int }
    pool: [dynamic]Scored
    for m in ask_all_definitions(table, scope_file, funcs, scope_module) {
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
ask_find_variant :: proc(table: ^SymbolTable, target: string, scope_module := "") -> (owner: string, kind: string, ok: bool) {
    // When `in <module>` is active, only owners in that module count — otherwise
    // the hint points at a union in some other module, contradicting the scope.
    for _, e in table.enums {
        if e.is_synthetic { continue }   // a union's internal `_Tag`: point at the union, not its tag enum
        if scope_module != "" && e.home_package != scope_module { continue }
        if _, has := e.variants[target]; has { return ask_label(e), ask_enum_sub(e), true }
    }
    for _, u in table.unions {
        if scope_module != "" && u.home_package != scope_module { continue }
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

// Forward type-dependency BFS, bounded to `depth` hops (depth < 0 = unbounded).
// A node is EXPANDED — has its outgoing edges emitted — iff it sits within depth
// of the root; nodes exactly one hop past the budget are still interned (so they
// appear as edge targets) but never expanded, which is how depth 0 yields the
// root's direct adjacency and nothing deeper. BFS (not the old stack pop) so each
// node's recorded `dist` is its SHORTEST distance — the value the renderer gates
// on. Field/param slice order is deterministic, so intern order (hence output)
// stays stable without sorting nodes.
ask_deps :: proc(table: ^SymbolTable, res: ^Ask_Result, root: Type, depth: int, root_filter := ASK_ALL_EDGES) {
    rid, _ := ask_intern(res, root)
    res.root = rid
    res.nodes[rid].dist = 0
    processed: map[rawptr]bool
    queue: [dynamic]Type
    append(&queue, root)
    for head := 0; head < len(queue); head += 1 {
        t := queue[head]
        key := raw_type_key(t)
        if processed[key] { continue }
        processed[key] = true
        from, _ := ask_intern(res, t)
        is_root := from == rid
        d := res.nodes[from].dist
        edges: [dynamic]Ask_Out_Edge
        ask_out_edges(table, t, &edges)
        for e in edges {
            // From the root only, honor `root_filter` — a function splits its
            // Takes (params) from its Returns so above/below show distinct graphs.
            // Deeper nodes (the param/return types' own fields) always expand fully.
            if is_root && e.kind not_in root_filter { continue }
            if _, named := ask_sub(e.core); !named {
                // Primitive / numeric member — it carries no graph node, so without
                // this it vanishes entirely. Record it as an inline field line so the
                // node shows its real shape (a leaf struct like Glyph lists its
                // x,y,w,h:i32 instead of reading as empty).
                append(&res.nodes[from].basics, Ask_Basic{ via = e.via, kind = e.kind, type_str = fmt.tprintf("%s%s", e.wrap, type_name(e.core)) })
                continue
            }
            to, is_new := ask_intern(res, e.core)
            if is_new { res.nodes[to].dist = d + 1 }
            append(&res.edges, Ask_Edge{ from = from, to = to, kind = e.kind, via = e.via, wrap = e.wrap })
            // Only follow into a target that can recurse AND still fits the budget.
            if ask_recurses(e.core) && (depth < 0 || d + 1 <= depth) && !processed[raw_type_key(e.core)] {
                append(&queue, e.core)
            }
        }
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

// One reverse reference: a container that points at some type, with the edge
// detail. The reverse walk is a BFS over an index of these (keyed by the flat
// name of the type referenced) rather than a full-table rescan per hop.
Ask_Rev_Ref :: struct { container: Type, kind: Ask_Edge_Kind, via: string, wrap: string }

// flat type name -> every container that references it (one outgoing edge each).
// Built once from the SAME `ask_out_edges` model `deps` uses, so the two
// directions can't disagree about the graph. Keyed by flat name (not pointer) so
// a generic's monomorphized fields — distinct objects sharing a canonical name —
// all fold onto the one queryable type. Containers are deduped by identity: a
// parameterized struct lives in BOTH `.structs` and `.funs` (data struct + ctor),
// and counting its edges twice would double every use-site.
ask_build_reverse_index :: proc(table: ^SymbolTable, funcs: map[string]^Type_Scope) -> map[string][dynamic]Ask_Rev_Ref {
    rev: map[string][dynamic]Ask_Rev_Ref
    seen: map[rawptr]bool
    add :: proc(table: ^SymbolTable, rev: ^map[string][dynamic]Ask_Rev_Ref, seen: ^map[rawptr]bool, container: Type) {
        // Declaring a type is not "using" it — a module namespace owns no data
        // fields, so this only formalizes an already-empty scan.
        if sc, ok := container.(^Type_Scope); ok && sc.is_module { return }
        key := raw_type_key(container)
        if seen[key] { return }
        seen[key] = true
        edges: [dynamic]Ask_Out_Edge
        ask_out_edges(table, container, &edges)
        for e in edges {
            name := ask_type_name(e.core)
            if name == "" { continue }
            list := rev^[name]                                  // map values aren't addressable —
            append(&list, Ask_Rev_Ref{ container = container, kind = e.kind, via = e.via, wrap = e.wrap })
            rev^[name] = list                                   // append to a local copy, store back
        }
    }
    for _, s in table.structs        { add(table, &rev, &seen, s) }
    for _, s in table.funs           { add(table, &rev, &seen, s) }
    for _, u in table.unions         { add(table, &rev, &seen, u) }
    for _, d in table.distinct_types { add(table, &rev, &seen, d) }
    // FFI functions reference types through their params/returns (e.g. every SDL
    // fn taking a `Window`), so scan the foreign ones too or `users` misses them.
    for _, f in funcs { if ask_is_foreign(f) { add(table, &rev, &seen, f) } }
    return rev
}

// users: reverse reachability out to `depth` hops (depth < 0 = unbounded). Each
// recorded edge is container -> the closer-to-root type it references, so the
// rings read outward: a depth-1 user references the target itself; a depth-2 user
// references some depth-1 user; and so on. BFS over the reverse index gives every
// node its SHORTEST distance (the value the renderer groups on).
// `kinds` restricts which reverse-edge kinds are walked. The type-below view passes
// {.Contains, .Embeds, .Base} so it reports only structural users (structs that
// contain/embed this type) — function-signature edges (Takes/Returns) are the
// `call` kind, served separately by render_struct_calls. The default (all kinds) is
// the broad in-degree used by the module surface's "most-used" ranking.
ask_users :: proc(table: ^SymbolTable, res: ^Ask_Result, target: Type, depth: int, funcs: map[string]^Type_Scope, kinds := ASK_ALL_EDGES) {
    rid, _ := ask_intern(res, target)
    res.root = rid
    res.nodes[rid].dist = 0
    if ask_type_name(target) == "" { return }   // an unnamed target can't be matched by name
    rev := ask_build_reverse_index(table, funcs)
    processed: map[rawptr]bool
    queue: [dynamic]Type
    append(&queue, target)
    for head := 0; head < len(queue); head += 1 {
        cur := queue[head]
        ckey := raw_type_key(cur)
        if processed[ckey] { continue }
        processed[ckey] = true
        cur_id, _ := ask_intern(res, cur)
        d := res.nodes[cur_id].dist
        cname := ask_type_name(cur)
        if cname == "" { continue }
        refs := rev[cname]   // bind first: ranging a map index of an ABSENT key faults (transient lvalue)
        for ref in refs {
            if ref.kind not_in kinds { continue }
            uid, is_new := ask_intern(res, ref.container)
            if is_new { res.nodes[uid].dist = d + 1 }
            append(&res.edges, Ask_Edge{ from = uid, to = cur_id, kind = ref.kind, via = ref.via, wrap = ref.wrap })
            // Walk a user's own users only while still within the hop budget.
            if (depth < 0 || d + 1 <= depth) && !processed[raw_type_key(ref.container)] {
                append(&queue, ref.container)
            }
        }
    }
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

// mara ask takes two optional filter axes after a name — KIND (which graph) and
// DIRECTION (which way) — in any order. Each folds to a canonical spelling so the
// CLI can tell a filter token from the name. Omitting an axis widens it to both.
ask_canon_kind :: proc(s: string) -> (canon: string, ok: bool) {
    switch s {
    case "types", "type":       return "types", true
    case "call", "calls":       return "call", true      // the call graph (callees / callers)
    case "flow":                return "flow", true      // the dataflow slice (above = lineage / producer tree)
    }
    return "", false
}

ask_canon_dir :: proc(s: string) -> (canon: string, ok: bool) {
    switch s {
    case "above": return "above", true
    case "below": return "below", true
    }
    return "", false
}

// A space-joined echo of the active filters, for command-echo in error hints.
ask_filters_str :: proc(kind, dir: string) -> string {
    if kind != "" && dir != "" { return fmt.tprintf("%s %s", kind, dir) }
    if kind != "" { return kind }
    return dir
}

// Compute one direction's graph for an already-resolved subject type, bounded to
// `depth` hops (depth < 0 = unbounded / full closure).
ask_compute :: proc(table: ^SymbolTable, root: Type, verb: string, depth: int, funcs: map[string]^Type_Scope, root_filter := ASK_ALL_EDGES, users_kinds := ASK_ALL_EDGES) -> Ask_Result {
    res: Ask_Result
    res.root = -1
    switch verb {
    case "deps":  ask_deps(table, &res, root, depth, root_filter)
    case "users": ask_users(table, &res, root, depth, funcs, users_kinds)
    }
    ask_sort_edges(&res)
    return res
}

// Top-level entry. Resolve `target` (optionally pinned to a `scope_file`), then
// render the selected (kind, dir) filters — an empty axis means "both". Returns
// the rendered text and whether a single subject was found — on false (not found
// / ambiguous) the text already explains why, and the caller exits non-zero.
ask :: proc(checked: ^Checked_Program, target, kind, dir, scope, at, pkg, scope_file, scope_module: string, depth: int) -> (out: string, ok: bool) {
    // Precise variable criterion — `at <file>:<line>` identifies a variable by its
    // definition site; no name needed.
    if at != "" {
        return ask_try_at(checked, at, kind, dir, pkg, depth)
    }
    // Variable criterion — `<name> in <fn>`. A non-empty `scope` named something
    // that was not a module or file (main() consumes those), so resolve it as a
    // function and slice the local/parameter `target` inside it.
    if scope != "" {
        vout, vok, handled := ask_try_variable(checked, target, kind, dir, scope, pkg, scope_module, depth)
        if handled { return vout, vok }
        // Not a function. A struct is a named scope too, but its members are fields
        // (not sliceable) and methods (queryable by name), so point there instead.
        if tmatches := ask_resolve_all(checked.table, scope, "", checked.functions, scope_module); len(tmatches) > 0 {
            return fmt.tprintf("mara ask: '%s' is a %s, not a function — `in` scopes to a function's variables; query the %s directly with `mara ask %s`.\n", scope, tmatches[0].sub, tmatches[0].sub, scope), false
        }
        return fmt.tprintf("mara ask: '%s' is not a known module, file, or function in %s\n", scope, pkg), false
    }

    matches := ask_resolve_all(checked.table, target, scope_file, checked.functions, scope_module)
    b := strings.builder_make()

    // Describe the resolution scope for the not-found / ambiguity messages. The
    // root is always the cwd project (`pkg`); `in <module>` / `in <file>` narrow
    // within it, so name them when present.
    scope_desc := pkg
    if scope_module != "" { scope_desc = fmt.tprintf("module %s", scope_module) }
    if scope_file != ""   { scope_desc = fmt.tprintf("%s, file %s", scope_desc, scope_file) }

    if len(matches) == 0 {
        // A module name? Show its surface (declared types + funs). Checked before
        // the variant / fuzzy guesses — a module is an intentional, exact target.
        if surface, is_mod := ask_module_surface(checked, target); is_mod {
            return surface, true
        }
        // Before guessing: if the name is a known variant, say so — it's the
        // single most likely reason a real-looking name fails to resolve.
        if owner, kind, is_variant := ask_find_variant(checked.table, target, scope_module); is_variant {
            fmt.sbprintf(&b, "mara ask: '%s' is a variant of %s %s — variants aren't queryable yet.\n", target, kind, owner)
            fmt.sbprintf(&b, "  (try `mara ask %s`)\n", owner)
            return strings.to_string(b), false
        }
        // No exact hit — offer the closest names rather than a bare miss.
        suggestions := ask_fuzzy(checked.table, target, scope_file, ASK_FUZZY_LIMIT, checked.functions, scope_module)
        if len(suggestions) > 0 {
            fmt.sbprintf(&b, "mara ask: no exact match for '%s' in %s — did you mean:\n", target, scope_desc)
            for m in suggestions {
                fmt.sbprintf(&b, "    %-8s %s  %s%s\n", m.sub, m.label, ask_loc(m.span), ask_mark_suffix(m.mark))
            }
        } else {
            fmt.sbprintf(&b, "mara ask: no type or function named '%s' in %s\n", target, scope_desc)
        }
        fmt.sbprint(&b, "  (a local or parameter? address it with `<name> in <fn>` or `at <file>:<line>`.)\n")
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

    ft, is_fn := subject.type_.(^Type_Scope)
    is_fn = is_fn && ft.kind == .Fun

    // A bare query (no kind) shows the subject's NATURAL kind, not all three: a
    // function's calls, any other type's structure. (A variable's natural kind is
    // flow — that default lives in render_var_slice.) An explicit kind overrides.
    // This keeps `mara ask Foo` focused — one analysis, not a three-kind dump — and
    // mirrors how the variable view already picks flow for a bare query.
    eff_kind := kind
    if eff_kind == "" { eff_kind = "call" if is_fn else "types" }
    show_types := eff_kind == "types"
    show_call  := eff_kind == "call"
    show_flow  := eff_kind == "flow"
    show_above := dir  == "" || dir  == "above"
    show_below := dir  == "" || dir  == "below"

    // The module shown is the subject's OWN home package, not the cwd project
    // (`pkg`) — a stdlib type queried from a game dir is `mara.font`, not `Pounce`.
    home_pkg := ask_home_package(subject.type_)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&b, "%s — %s  %s   (module %s)%s\n", subject.label, subject.sub, ask_loc(subject.span), home_pkg, ask_mark_suffix(subject.mark))
    header_len := len(strings.to_string(b))

    // Flow is the "outside" view, and for both a type (every value of it) and a
    // function (every call of it) it aggregates across the whole program, so every
    // function's def-use graph must exist first (data-only, cheap). Control deps
    // (post-dominators) are the expensive step — build them only on `control`, and
    // only for the functions the slice actually touches.
    if show_flow {
        flow_analyze_all(checked)
        if checked.want_control_deps {
            if is_fn { flow_build_fn_guards(checked, ft) }
            else     { flow_build_type_guards(checked, subject.type_) }
        }
    }

    // The CALL graph (callees/callers) reads off the materialized call_graph and is
    // always available. The FLOW views (args in / results out) need call SITES, which
    // flow_analyze_all populates; with none, both flow directions are empty — say so
    // once and suppress their per-section "never called" repeats. (A function with no
    // callers can still have callees, so this gates flow only, not `call`.)
    fn_uncalled := is_fn && show_flow && len(checked.call_sites[ft]) == 0
    if fn_uncalled {
        fmt.sbprintf(&b, "\n%s has no call sites — its flow views (arguments in, results out) are empty\n", subject.label)
    }

    // ABOVE — what feeds / builds the subject.
    //   types: a struct's field types; a function's PARAMETER types.
    //   call:  a function's callees.
    //   flow:  what computes the args at a function's call sites, or what feeds a type's values.
    if show_above && show_types {
        filter := bit_set[Ask_Edge_Kind]{.Takes} if is_fn else ASK_ALL_EDGES
        res := ask_compute(checked.table, subject.type_, "deps", depth, checked.functions, filter)
        render_ask_deps(&b, &res, depth, "above")
    }
    if show_above && show_call {
        if is_fn { render_fn_callees(&b, checked, ft, depth) }
        else     { render_struct_calls(&b, checked, subject.type_, .Returns, "above") }
    }
    if show_above && show_flow {
        if is_fn { if !fn_uncalled { render_fn_flow_above(&b, checked, ft, subject.label) } }
        else     { render_type_flow_above(&b, checked, subject.type_, subject.label) }
    }

    // BELOW — what the subject feeds / who depends on it.
    //   types: structs that contain/embed this struct; a function's RETURN types.
    //   call:  a function's callers.
    //   flow:  where a function's results flow, or what a type's values feed.
    if show_below && show_types {
        if is_fn {
            res := ask_compute(checked.table, subject.type_, "deps", depth, checked.functions, {.Returns})
            render_ask_deps(&b, &res, depth, "below")
        } else {
            // Structural users only — fns that take/return this type are the `call`
            // kind (render_struct_calls below), not "structs I'm a field of".
            res := ask_compute(checked.table, subject.type_, "users", depth, checked.functions, users_kinds = {.Contains, .Embeds, .Base})
            render_ask_users(&b, &res, depth)
        }
    }
    if show_below && show_call {
        if is_fn { render_fn_users(&b, checked, ft, depth) }   // callers, from the call graph
        else     { render_struct_calls(&b, checked, subject.type_, .Takes, "below") }
    }
    if show_below && show_flow {
        if is_fn { if !fn_uncalled { render_fn_flow_below(&b, checked, ft, subject.label) } }
        else     { render_type_flow_below(&b, checked, subject.type_, subject.label, depth) }
    }

    // The chosen filters can name a graph this subject lacks (a type has no data
    // slice; a function has no type-level users). Don't return a bare header.
    if len(strings.to_string(b)) == header_len {
        reason := "matching graph"
        if show_flow && !show_types {
            reason = "flow slice"
        } else if is_fn {
            reason = "type-level users"
        }
        fmt.sbprintf(&b, "\n(nothing to show — a %s has no %s here)\n", subject.sub, reason)
    }

    return strings.to_string(b), true
}

// Variable criterion: `mara ask <name> in <fn>`. `scope` named a thing that was
// not a module or file (main() consumes those), so try it as a function and look
// for a local/parameter `target` inside it. handled=false only when `scope` is
// not a function at all, so the caller can report what a scope may be.
ask_try_variable :: proc(checked: ^Checked_Program, target, kind, dir, scope, pkg, scope_module: string, depth: int) -> (out: string, ok: bool, handled: bool) {
    // `var in fn in module` composes: the module narrows WHICH `fn` we slice into
    // when the function name is shared across modules.
    matches := ask_resolve_all(checked.table, scope, "", checked.functions, scope_module)
    fns: [dynamic]^Type_Scope
    defer delete(fns)
    for m in matches {
        if ft, isfn := m.type_.(^Type_Scope); isfn && ft.kind == .Fun { append(&fns, ft) }
    }
    if len(fns) == 0 { return "", false, false }   // not a function — let the caller report
    if len(fns) > 1 {
        return fmt.tprintf("mara ask: scope '%s' is ambiguous — %d functions share that name; address the variable with `at <file>:<line>`.\n", scope, len(fns)), false, true
    }
    ft := fns[0]
    ensure_fn_analysis(checked, ft)

    // `return` is the function's output endpoint — the inside view (what feeds the
    // return), the counterpart to slicing a parameter. `return` is a keyword, so it
    // can never collide with a local name.
    if target == "return" {
        return render_return_slice(checked, ft, scope, kind, dir, pkg), true, true
    }

    vars: [dynamic]^Var_Binding
    defer delete(vars)
    for vb in checked.var_bindings {
        if vb.fn == ft && vb.name == target { append(&vars, vb) }
    }
    if len(vars) == 0 {
        return fmt.tprintf("mara ask: no variable '%s' in function '%s' — its parameters and locals are sliceable.\n", target, scope), false, true
    }
    if len(vars) > 1 {
        // Shadowing: same name, different declarations. Don't guess — list them.
        slice.sort_by(vars[:], proc(a, b: ^Var_Binding) -> bool { return a.span.line < b.span.line })
        sb := strings.builder_make()
        fmt.sbprintf(&sb, "mara ask: '%s' names %d variables in '%s' (shadowing) — pick one with `at <file>:<line>`:\n", target, len(vars), scope)
        for vb in vars {
            knd := "param" if vb.kind == .Param else "local"
            fmt.sbprintf(&sb, "    %-6s %s\n", knd, ask_loc(vb.span))
        }
        return strings.to_string(sb), false, true
    }
    return render_var_slice(checked, vars[0], scope, kind, dir, pkg, depth), true, true
}

// Precise variable criterion: `mara ask at <file>:<line>`. A function carries no
// source range, so analyze the functions declared in that file (their def sites
// then exist) and pick the variable defined at exactly (file, line). A line that
// assigns several variables lists them; one with none reports the miss.
ask_try_at :: proc(checked: ^Checked_Program, loc, kind, dir, pkg: string, depth: int) -> (out: string, ok: bool) {
    file, line, pok := ask_parse_at(loc)
    if !pok {
        return fmt.tprintf("mara ask: `at` expects <file>:<line> (e.g. `at camera.mara:176`); got '%s'\n", loc), false
    }
    // Populate def sites by analyzing the functions declared in that file.
    for _, ft in checked.functions {
        if ft != nil && ft.kind == .Fun && filepath.base(ft.body_span.file) == file {
            ensure_fn_analysis(checked, ft)
        }
    }
    // Distinct variables with a definition at exactly (file, line).
    bindings: [dynamic]^Var_Binding
    defer delete(bindings)
    seen: map[^Var_Binding]bool
    defer delete(seen)
    for d in checked.defs {
        if d.binding == nil || seen[d.binding] { continue }
        if d.span.line == line && filepath.base(d.span.file) == file {
            seen[d.binding] = true
            append(&bindings, d.binding)
        }
    }
    if len(bindings) == 0 {
        return fmt.tprintf("mara ask: no variable defined at %s:%d — point `at` at a declaration or assignment.\n", file, line), false
    }
    if len(bindings) > 1 {
        slice.sort_by(bindings[:], proc(a, b: ^Var_Binding) -> bool { return a.name < b.name })
        sb := strings.builder_make()
        fmt.sbprintf(&sb, "mara ask: %s:%d defines %d variables — name one with `<var> in <fn>`:\n", file, line, len(bindings))
        for vb in bindings {
            knd := "param" if vb.kind == .Param else "local"
            fmt.sbprintf(&sb, "    %-6s %s\n", knd, vb.name)
        }
        return strings.to_string(sb), false
    }
    return render_var_slice(checked, bindings[0], ask_label(bindings[0].fn), kind, dir, pkg, depth), true
}

// --- renderer (text adjacency dump) ----------------------------------------

// deps: one adjacency block per EXPANDED node (root first), each with its
// location and its direct typed edges. At unbounded depth the blocks are the
// full transitive closure; at depth N the fringe (nodes one hop past the budget)
// appears only as edge targets, never as its own block — so depth 0 is exactly
// the root's direct adjacency.
// Module-qualified node name for the tree rows (math.Vec3), bare if no package.
ask_qnode :: proc(n: Ask_Node) -> string {
    if n.home_package == "" { return n.label }
    return fmt.tprintf("%s.%s", n.home_package, n.label)
}

// A member's display name: a struct field is just its name (`obj`); a param / embed
// keeps its word (`param x`, `embed shape`); an unnamed member — a return, or a
// distinct's base — is named by its word (`return`, `base`).
ask_member_name :: proc(via: string, kind: Ask_Edge_Kind) -> string {
    if via == ""         { return ask_edge_word(kind) }
    if kind == .Contains { return via }
    return fmt.tprintf("%s %s", ask_edge_word(kind), via)
}

render_ask_deps :: proc(b: ^strings.Builder, res: ^Ask_Result, depth: int, dir := "above") {
    root := &res.nodes[res.root]
    if len(res.edges) == 0 && len(root.basics) == 0 {
        fmt.sbprintf(b, "\n%s (types)   (no type dependencies)\n", dir)
        return
    }
    // Count named type nodes within the depth bound — the root may be a `fun` (the
    // subject), which is not a type and must not inflate the count; a fringe node
    // (dist > depth) is interned as a leaf label, not a counted block.
    types := 0
    for n in res.nodes {
        if depth >= 0 && n.dist > depth { continue }
        if n.sub != "fun" { types += 1 }
    }
    count := ask_plural(types, "type")
    if len(res.edges) == 0 { count = "basic types only" }   // a struct built only from primitives (Glyph)
    fmt.sbprintf(b, "\n%s (types)   (%s, %s)\n", dir, count, ask_depth_label(depth))

    // Walk the type graph as an indented tree (mirror of the call tree). A GLOBAL
    // `seen` expands each aggregate once: a struct reached twice shows "(shown
    // above)" and the walk terminates on cyclic / diamond graphs.
    seen: map[int]bool
    defer delete(seen)
    seen[res.root] = true
    ask_walk_deps(b, res, res.root, 1, &seen)
}

// Render node_id's members at `indent` — typed fields (edges) then primitive basics,
// recursing into struct / union targets. distinct / enum / primitive targets are
// LEAVES: we don't unwrap a Vec3 to its `[3]f32` base. Names are module-qualified.
ask_walk_deps :: proc(b: ^strings.Builder, res: ^Ask_Result, node_id, indent: int, seen: ^map[int]bool) {
    for e in res.edges {
        if e.from != node_id { continue }
        tgt := res.nodes[e.to]
        expandable := tgt.sub == "struct" || tgt.sub == "union"
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        fmt.sbprintf(b, "%s : %s%s", ask_member_name(e.via, e.kind), e.wrap, ask_qnode(tgt))
        if expandable && seen[e.to] { fmt.sbprint(b, "  (shown above)") }
        fmt.sbprint(b, "\n")
        if expandable && !seen[e.to] {
            seen[e.to] = true
            ask_walk_deps(b, res, e.to, indent + 1, seen)
        }
    }
    for m in res.nodes[node_id].basics {
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        fmt.sbprintf(b, "%s : %s\n", ask_member_name(m.via, m.kind), m.type_str)
    }
}

// "full closure (depth ∞)" when unbounded, else "depth N" — shared by both
// direction headers so they describe the hop budget identically.
ask_depth_label :: proc(depth: int) -> string {
    return "full closure (depth ∞)" if depth < 0 else fmt.tprintf("depth %d", depth)
}

// Deduped count of a node's neighbours in `adj` (drops self-recursion and duplicate
// call sites) — the "direct" count for a call-tree header.
ask_direct_call_count :: proc(adj: [][dynamic]int, node: int) -> int {
    local: map[int]bool
    defer delete(local)
    n := 0
    for k in adj[node] {
        if k == node || local[k] { continue }
        local[k] = true
        n += 1
    }
    return n
}

// Print one level of a call tree (node's neighbours in `adj`) in CALL ORDER — by the
// first call-site line recorded on each edge (cg.edge_line) — then recurse into each.
// `forward` selects callees (out-edges) vs callers (a reverse index); it only flips
// which end of the pair is the caller for the order lookup. A GLOBAL `seen` expands
// each function at most once — cycles (recursion) and diamonds collapse to
// "(shown above)", so the walk always terminates and a utility called everywhere
// doesn't blow up the output. `remaining` is the depth cap left (~1e9 unbounded).
ask_walk_calls :: proc(b: ^strings.Builder, cg: ^Call_Graph, adj: [][dynamic]int,
                       node, indent, remaining: int, seen: ^map[int]bool, forward: bool) {
    if remaining <= 0 { return }

    Kid :: struct { id, key: int, label: string }
    kids: [dynamic]Kid
    defer delete(kids)
    local: map[int]bool
    defer delete(local)
    for k in adj[node] {
        if k == node || local[k] { continue }   // skip self-recursion + duplicate call sites
        local[k] = true
        caller_s := cg.nodes[node] if forward else cg.nodes[k]
        callee_s := cg.nodes[k]    if forward else cg.nodes[node]
        key := cg.edge_line[Call_Edge{ from = caller_s, to = callee_s }] or_else (1 << 30)
        append(&kids, Kid{ k, key, ask_qualified_label(cg.nodes[k]) })
    }
    slice.sort_by(kids[:], proc(x, y: Kid) -> bool {
        if x.key   != y.key   { return x.key < y.key }     // call order (first call-site line)
        if x.label != y.label { return x.label < y.label }
        return x.id < y.id
    })

    for kid in kids {
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        if seen[kid.id] {
            fmt.sbprintf(b, "%s  (shown above)\n", kid.label)
            continue
        }
        seen[kid.id] = true
        sub, _ := ask_sub(cg.nodes[kid.id])
        tag := "" if sub == "fun" else fmt.tprintf("  (%s)", sub)
        fmt.sbprintf(b, "%s%s\n", kid.label, tag)
        ask_walk_calls(b, cg, adj, kid.id, indent + 1, remaining - 1, seen, forward)
    }
}

// users: the reverse references, grouped by hop distance from the subject. Header
// separates distinct users from use-sites so neither count is misread. When the
// view reaches past one hop, rows are bucketed under "N hops" subheaders and each
// names the closer-to-root type it references (not the subject), so a chain like
// Megastruct -> Camera -> Object -> Vec3 reads outward ring by ring.
// users on a FUNCTION = its callers, read off the materialized call graph
// (Checked_Program.call_graph — resolved direct calls collected during checking).
// Indirect calls through fn-typed params are not edges, so a function reached only
// that way reads as having no callers.
render_fn_users :: proc(b: ^strings.Builder, checked: ^Checked_Program, ft: ^Type_Scope, depth: int) {
    cg := &checked.call_graph
    // Reverse adjacency (callee -> its callers), built once, then walked as a tree
    // up toward the program's entry points.
    rev := make([][dynamic]int, len(cg.nodes))
    defer { for r in rev { delete(r) }; delete(rev) }
    for callees, c in cg.out_edges {
        for callee in callees { append(&rev[callee], c) }
    }

    nf, ok := cg.index_of[ft]
    direct := ask_direct_call_count(rev, nf) if ok else 0
    fmt.sbprintf(b, "\nbelow (calls)   (%s, %s)\n", ask_plural(direct, "direct caller"), ask_depth_label(depth))
    if direct == 0 {
        fmt.sbprint(b, "  (no direct callers; indirect calls via fn-typed params aren't tracked)\n")
        return
    }
    seen: map[int]bool
    defer delete(seen)
    seen[nf] = true
    budget := depth if depth >= 0 else (1 << 30)
    ask_walk_calls(b, cg, rev, nf, 1, budget, &seen, false)
}

// callees of a function — `fun call above`, the mirror of render_fn_users, read off
// the materialized call graph's out-edges (resolved direct calls + construction
// edges this function makes). A constructor edge surfaces as the built struct
// (sub "struct"); a plain call as `fun`. Indirect calls via fn-typed params aren't
// edges, so a function that only dispatches dynamically reads as calling nothing.
render_fn_callees :: proc(b: ^strings.Builder, checked: ^Checked_Program, ft: ^Type_Scope, depth: int) {
    cg := &checked.call_graph
    nf, ok := cg.index_of[ft]
    direct := ask_direct_call_count(cg.out_edges[:], nf) if ok else 0
    fmt.sbprintf(b, "\nabove (calls)   (%s, %s)\n", ask_plural(direct, "direct callee"), ask_depth_label(depth))
    if direct == 0 {
        fmt.sbprint(b, "  (calls nothing directly; indirect calls via fn-typed params aren't tracked)\n")
        return
    }
    seen: map[int]bool
    defer delete(seen)
    seen[nf] = true
    budget := depth if depth >= 0 else (1 << 30)
    ask_walk_calls(b, cg, cg.out_edges[:], nf, 1, budget, &seen, true)
}

// struct/type `call` — the functions whose SIGNATURE mentions this type, read off
// the same reverse index as `users` but filtered to the signature edge kinds:
//   below (.Takes):   functions that TAKE this type as an argument — the rich one
//                     ("who would I have to update if this type changed shape").
//   above (.Returns): functions that RETURN (hand back) a value of this type.
// A one-hop view — a function isn't itself "taken" by another, so there is nothing
// to recurse. The auto-generated constructor is construction (`T{…}`), not a
// Returns edge, so it is not listed under `above`; a true "what builds this value"
// producer query is deferred (design/mara_ask.txt, struct call above).
render_struct_calls :: proc(b: ^strings.Builder, checked: ^Checked_Program, target: Type, want: Ask_Edge_Kind, dir: string) {
    rev := ask_build_reverse_index(checked.table, checked.functions)
    name := ask_type_name(target)
    refs := rev[name]   // bind first — a map index of an absent key is a transient lvalue

    Row :: struct { label, via, wrap: string, span: Span }
    rows: [dynamic]Row
    defer delete(rows)
    seen: map[string]bool
    defer delete(seen)
    for ref in refs {
        if ref.kind != want { continue }
        cont_fn, ok := ref.container.(^Type_Scope)
        if !ok || cont_fn.kind != .Fun { continue }   // signature edges only originate in callables
        key := fmt.tprintf("%s|%s", ask_label(cont_fn), ref.via)
        if seen[key] { continue }
        seen[key] = true
        append(&rows, Row{ label = ask_label(cont_fn), via = ref.via, wrap = ref.wrap, span = ask_span(cont_fn) })
    }
    slice.sort_by(rows[:], proc(x, y: Row) -> bool {
        if x.label != y.label { return x.label < y.label }
        return x.via < y.via
    })

    word := ask_edge_word(want)   // "param" / "return"
    tlabel := ask_label(target)
    fmt.sbprintf(b, "\n%s (calls)   (%s)\n", dir, ask_plural(len(rows), "function"))
    if len(rows) == 0 {
        verb := "take it" if want == .Takes else "return it"
        fmt.sbprintf(b, "  (no functions %s)\n", verb)
        return
    }
    for r in rows {
        via := fmt.tprintf(" %s", r.via) if r.via != "" else ""
        fmt.sbprintf(b, "  fun    %-22s %s   (%s%s : %s%s)\n", r.label, ask_loc(r.span), word, via, r.wrap, tlabel)
    }
}

render_ask_users :: proc(b: ^strings.Builder, res: ^Ask_Result, depth: int) {
    fmt.sbprintf(b, "\nbelow (types)   (%s, %s, %s)\n",
                 ask_plural(ask_distinct_sources(res), "user"), ask_plural(len(res.edges), "use-site"), ask_depth_label(depth))
    if len(res.edges) == 0 { fmt.sbprint(b, "  (no users)\n"); return }

    // Flatten to self-contained rows so the sort needs no captured `res` (Odin
    // proc literals don't close over locals). Order by (hop, user, edge) — all
    // content, so the reverse scan's map-iteration order never leaks into output.
    Row :: struct {
        dist:                              int,
        sub, label, via, wrap, to, mark:   string,
        kind:                              Ask_Edge_Kind,
    }
    rows: [dynamic]Row
    max_hop := 0
    for e in res.edges {
        u := res.nodes[e.from]
        if u.dist > max_hop { max_hop = u.dist }
        append(&rows, Row{ dist = u.dist, sub = u.sub, label = u.label, via = e.via,
                           wrap = e.wrap, to = res.nodes[e.to].label, mark = u.mark, kind = e.kind })
    }
    slice.sort_by(rows[:], proc(x, y: Row) -> bool {
        if x.dist  != y.dist  { return x.dist  < y.dist  }
        if x.label != y.label { return x.label < y.label }
        if x.via   != y.via   { return x.via   < y.via   }
        return x.to < y.to
    })

    multi  := max_hop > 1                 // single-ring views stay flat, like before
    curhop := -1
    for r in rows {
        if multi && r.dist != curhop {
            curhop = r.dist
            tag := " (direct)" if r.dist == 1 else ""
            fmt.sbprintf(b, "\n  %s%s:\n", ask_plural(r.dist, "hop"), tag)
        }
        indent := "    " if multi else "  "
        via := fmt.tprintf(" %s", r.via) if r.via != "" else ""
        fmt.sbprintf(b, "%s%-6s %s  (%s%s : %s%s)%s\n",
                     indent, r.sub, r.label, ask_edge_word(r.kind), via, r.wrap, r.to, ask_mark_suffix(r.mark))
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
ask_user_count :: proc(table: ^SymbolTable, t: Type, funcs: map[string]^Type_Scope) -> int {
    res := ask_compute(table, t, "users", 0, funcs)   // DIRECT users only — the surface ranks by one-hop in-degree
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
    for m in ask_all_definitions(checked.table, "", checked.functions) {
        hp := ask_home_package(m.type_)
        if m.mark == "synthetic" || (ask_source_name(m.type_) == "" && !ask_is_foreign(m.type_)) { continue }   // skip instances/synthetic, keep FFI funs
        if !ask_module_name_matches(hp, target) { continue }
        canonical = hp
        if m.sub == "fun" { append(&funs, m) }
        else              { append(&types, Entry{ m = m, users = ask_user_count(checked.table, m.type_, checked.functions) }) }
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

// --- no analyzable module in the cwd ---------------------------------------

// `mara ask` runs against the module in the current directory (its folder name
// is the default root). When that folder names no discovered module, the generic
// build error ("no files found for module X") buries the real problem and never
// mentions the user's query. This renders ask-shaped guidance instead: name the
// miss, show the modules that ARE analyzable (local first, then stdlib — exactly
// the valid `in <module>` arguments), and teach the two ways forward — cd into a
// module's directory, or pin one inline with `in <module>`. The local/stdlib
// split classifies each module by a representative file, like the module map.
ask_no_module_here :: proc(all_files: map[string][dynamic]^Source_File, compiler_dir, cwd_name, target, query: string) -> string {
    locals: [dynamic]string
    libs:   [dynamic]string
    for name, files in all_files {
        if len(files) == 0 { continue }
        if ask_file_is_stdlib(files[0].path, compiler_dir) { append(&libs, name) }
        else                                               { append(&locals, name) }
    }
    less := proc(a, b: string) -> bool { return a < b }
    slice.sort_by(locals[:], less)
    slice.sort_by(libs[:], less)

    // Echo the user's own command in the inline-fix hint so the fix is copy-paste.
    inline_hint := "mara ask <name> in <module>"
    if target != "" {
        q := fmt.tprintf(" %s", query) if query != "" else ""
        inline_hint = fmt.tprintf("mara ask %s%s in <module>", target, q)
    }

    b := strings.builder_make()
    if len(locals) == 0 {
        // The user's third case: the directory holds no Mara module at all.
        fmt.sbprintf(&b, "mara ask: no Mara module in the current directory ('%s').\n", cwd_name)
        fmt.sbprint(&b,  "  mara ask analyzes the module in the directory you run it from —\n")
        fmt.sbprint(&b,  "  a folder whose .mara files declare a module. cd into one, or pin a\n")
        fmt.sbprint(&b,  "  module inline:\n")
    } else {
        // A module IS here, just under a name other than the folder's.
        fmt.sbprintf(&b, "mara ask: '%s' (this folder's name) is not a module here.\n", cwd_name)
        fmt.sbprint(&b,  "  Run mara ask from a module's own directory, or pin one inline:\n")
    }
    fmt.sbprintf(&b, "      %s\n", inline_hint)

    if len(locals) > 0 || len(libs) > 0 {
        fmt.sbprint(&b, "\n  modules on the search path (each valid as `in <module>`):\n")
        if len(locals) > 0 {
            fmt.sbprint(&b, "    your code\n")
            for n in locals { fmt.sbprintf(&b, "      %s\n", n) }
        }
        if len(libs) > 0 {
            fmt.sbprint(&b, "    stdlib\n")
            for n in libs { fmt.sbprintf(&b, "      %s\n", n) }
        }
    }
    return strings.to_string(b)
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
    for m in ask_all_definitions(checked.table, "", checked.functions) {
        if m.mark == "synthetic" || (ask_source_name(m.type_) == "" && !ask_is_foreign(m.type_)) { continue }   // skip instances/synthetic, keep FFI funs
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
