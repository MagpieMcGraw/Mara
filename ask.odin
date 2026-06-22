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

Ask_Node :: struct {
    label: string,   // user-facing type / fn name
    sub:   string,   // "struct" / "union" / "error" / "distinct" / "fun" ("enum" only for a union's synthetic tag)
    span:  Span,
    mark:  string,   // "" for ordinary types; e.g. "synthetic" for compiler-generated ones
    dist:  int,      // shortest hop distance from the query root (0 = the root itself)
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

ask_all_definitions :: proc(table: ^SymbolTable, scope_file: string, funcs: map[string]^Type_Scope) -> [dynamic]Ask_Match {
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
    // FFI functions are absent from table.funs — surface the foreign ones from
    // checked.functions so resolution, fuzzy, and the module views all see them.
    for _, f in funcs { if ask_is_foreign(f) { consider(&matches, &seen, f, scope_file) } }
    return matches
}

// Exact resolution: the definitions whose name the user typed verbatim.
ask_resolve_all :: proc(table: ^SymbolTable, target: string, scope_file: string, funcs: map[string]^Type_Scope) -> [dynamic]Ask_Match {
    out: [dynamic]Ask_Match
    for m in ask_all_definitions(table, scope_file, funcs) {
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
ask_fuzzy :: proc(table: ^SymbolTable, target: string, scope_file: string, limit: int, funcs: map[string]^Type_Scope) -> [dynamic]Ask_Match {
    Scored :: struct { m: Ask_Match, score: int }
    pool: [dynamic]Scored
    for m in ask_all_definitions(table, scope_file, funcs) {
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
        if _, has := e.variants[target]; has { return ask_label(e), ask_enum_sub(e), true }
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

// Forward type-dependency BFS, bounded to `depth` hops (depth < 0 = unbounded).
// A node is EXPANDED — has its outgoing edges emitted — iff it sits within depth
// of the root; nodes exactly one hop past the budget are still interned (so they
// appear as edge targets) but never expanded, which is how depth 0 yields the
// root's direct adjacency and nothing deeper. BFS (not the old stack pop) so each
// node's recorded `dist` is its SHORTEST distance — the value the renderer gates
// on. Field/param slice order is deterministic, so intern order (hence output)
// stays stable without sorting nodes.
ask_deps :: proc(table: ^SymbolTable, res: ^Ask_Result, root: Type, depth: int) {
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
        d := res.nodes[from].dist
        edges: [dynamic]Ask_Out_Edge
        ask_out_edges(table, t, &edges)
        for e in edges {
            if _, named := ask_sub(e.core); !named { continue }   // skip primitive / numeric leaves
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
ask_users :: proc(table: ^SymbolTable, res: ^Ask_Result, target: Type, depth: int, funcs: map[string]^Type_Scope) {
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
    case "types", "type": return "types", true
    case "flow":          return "flow", true
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
ask_compute :: proc(table: ^SymbolTable, root: Type, verb: string, depth: int, funcs: map[string]^Type_Scope) -> Ask_Result {
    res: Ask_Result
    res.root = -1
    switch verb {
    case "deps":  ask_deps(table, &res, root, depth)
    case "users": ask_users(table, &res, root, depth, funcs)
    }
    ask_sort_edges(&res)
    return res
}

// Top-level entry. Resolve `target` (optionally pinned to a `scope_file`), then
// render the selected (kind, dir) filters — an empty axis means "both". Returns
// the rendered text and whether a single subject was found — on false (not found
// / ambiguous) the text already explains why, and the caller exits non-zero.
ask :: proc(checked: ^Checked_Program, target, kind, dir, scope, at, pkg, scope_file: string, depth: int) -> (out: string, ok: bool) {
    // Precise variable criterion — `at <file>:<line>` identifies a variable by its
    // definition site; no name needed.
    if at != "" {
        return ask_try_at(checked, at, kind, dir, pkg)
    }
    // Variable criterion — `<name> in <fn>`. A non-empty `scope` named something
    // that was not a module or file (main() consumes those), so resolve it as a
    // function and slice the local/parameter `target` inside it.
    if scope != "" {
        vout, vok, handled := ask_try_variable(checked, target, kind, dir, scope, pkg)
        if handled { return vout, vok }
        // Not a function. A struct is a named scope too, but its members are fields
        // (not sliceable) and methods (queryable by name), so point there instead.
        if tmatches := ask_resolve_all(checked.table, scope, "", checked.functions); len(tmatches) > 0 {
            return fmt.tprintf("mara ask: '%s' is a %s, not a function — `in` scopes to a function's variables; query the %s directly with `mara ask %s`.\n", scope, tmatches[0].sub, tmatches[0].sub, scope), false
        }
        return fmt.tprintf("mara ask: '%s' is not a known module, file, or function in %s\n", scope, pkg), false
    }

    matches := ask_resolve_all(checked.table, target, scope_file, checked.functions)
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
        suggestions := ask_fuzzy(checked.table, target, scope_file, ASK_FUZZY_LIMIT, checked.functions)
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

    show_types := kind == "" || kind == "types"
    show_flow  := kind == "" || kind == "flow"
    show_above := dir  == "" || dir  == "above"
    show_below := dir  == "" || dir  == "below"

    ft, is_fn := subject.type_.(^Type_Scope)
    is_fn = is_fn && ft.kind == .Fun

    fmt.sbprintf(&b, "%s — %s  %s   (module %s)%s\n", subject.label, subject.sub, ask_loc(subject.span), pkg, ask_mark_suffix(subject.mark))
    header_len := len(strings.to_string(b))

    // ABOVE — what the subject is built from / what feeds it. Type dependencies for
    // any subject; for a function, the backward data slice of its return as well.
    if show_above && show_types {
        res := ask_compute(checked.table, subject.type_, "deps", depth, checked.functions)
        render_ask_deps(&b, &res, depth)
    }
    if show_above && show_flow && is_fn {
        fmt.sbprint(&b, render_contributors(checked, ft, subject.label))
    }

    // BELOW — what depends on the subject / what it feeds. Type users for a type;
    // for a function, its callers plus the forward data slice of its parameters.
    if show_below && show_types && !is_fn {
        res := ask_compute(checked.table, subject.type_, "users", depth, checked.functions)
        render_ask_users(&b, &res, depth)
    }
    if show_below && show_flow && is_fn {
        render_fn_users(&b, checked, ft)   // callers, from the call graph
        fmt.sbprint(&b, render_affects(checked, ft, subject.label))
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
ask_try_variable :: proc(checked: ^Checked_Program, target, kind, dir, scope, pkg: string) -> (out: string, ok: bool, handled: bool) {
    matches := ask_resolve_all(checked.table, scope, "", checked.functions)
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
    return render_var_slice(checked, vars[0], scope, kind, dir, pkg), true, true
}

// Precise variable criterion: `mara ask at <file>:<line>`. A function carries no
// source range, so analyze the functions declared in that file (their def sites
// then exist) and pick the variable defined at exactly (file, line). A line that
// assigns several variables lists them; one with none reports the miss.
ask_try_at :: proc(checked: ^Checked_Program, loc, kind, dir, pkg: string) -> (out: string, ok: bool) {
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
    return render_var_slice(checked, bindings[0], ask_label(bindings[0].fn), kind, dir, pkg), true
}

// --- renderer (text adjacency dump) ----------------------------------------

// deps: one adjacency block per EXPANDED node (root first), each with its
// location and its direct typed edges. At unbounded depth the blocks are the
// full transitive closure; at depth N the fringe (nodes one hop past the budget)
// appears only as edge targets, never as its own block — so depth 0 is exactly
// the root's direct adjacency.
render_ask_deps :: proc(b: ^strings.Builder, res: ^Ask_Result, depth: int) {
    // No edges = nothing this type/fn pulls in. Say so plainly rather than listing
    // the subject itself as a lone "1 type" with "(no type dependencies)".
    if len(res.edges) == 0 {
        fmt.sbprint(b, "\nabove (types)   (no type dependencies)\n")
        return
    }
    // Count TYPE nodes only — the root may be a `fun` (the subject), which is not
    // a type and must not inflate the count (a fn's own node sits at index 0).
    types := 0
    for n in res.nodes { if n.sub != "fun" { types += 1 } }
    fmt.sbprintf(b, "\nabove (types)   (%s, %s, %s)\n", ask_plural(types, "type"), ask_plural(len(res.edges), "edge"), ask_depth_label(depth))
    for node, i in res.nodes {
        if depth >= 0 && node.dist > depth { continue }   // fringe target — interned, not expanded
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

// "full closure (depth ∞)" when unbounded, else "depth N" — shared by both
// direction headers so they describe the hop budget identically.
ask_depth_label :: proc(depth: int) -> string {
    return "full closure (depth ∞)" if depth < 0 else fmt.tprintf("depth %d", depth)
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
render_fn_users :: proc(b: ^strings.Builder, checked: ^Checked_Program, ft: ^Type_Scope) {
    cg := &checked.call_graph
    callers: [dynamic]^Type_Scope
    defer delete(callers)
    if nf, ok := cg.index_of[ft]; ok {
        for callees, c in cg.out_edges {
            if c == nf { continue }   // a recursive self-call isn't an external user
            for callee in callees {
                if callee == nf { append(&callers, cg.nodes[c]); break }
            }
        }
    }
    slice.sort_by(callers[:], proc(a, b: ^Type_Scope) -> bool {
        la, lb := ask_label(a), ask_label(b)
        if la != lb { return la < lb }
        return a.body_span.line < b.body_span.line
    })
    fmt.sbprintf(b, "\nbelow (calls)   (%s)\n", ask_plural(len(callers), "caller"))
    if len(callers) == 0 {
        fmt.sbprint(b, "  (no direct callers; indirect calls via fn-typed params aren't tracked)\n")
        return
    }
    for c in callers {
        sub, _ := ask_sub(c)
        fmt.sbprintf(b, "  %-6s %s  %s\n", sub, ask_label(c), ask_loc(ask_span(c)))
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
