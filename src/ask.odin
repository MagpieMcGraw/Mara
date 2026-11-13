package mara

// ---------------------------------------------------------------------------
// `mara ask` — the analyzer (design/mara_ask.md): what a name is and how it
// connects, read off the checked program. A subject — a module, a type, a
// function, a variable — is shown in its natural view, or the one asked for:
//   types   a type's fields and embeds, a fun's param and result types
//           (above), and who contains or takes it (below);
//   call    a fun's callees (above) and callers (below);
//   flow    a value's slice: what feeds it (above), what it feeds (below) —
//           def-use over the program graph (defuse.odin, slice.odin,
//           lineage.odin); `control` adds the branches that decide it.
// A depth caps the levels (a tree of calls or types is one unless asked: ASK_DEPTH_OMITTED);
// `in`/`at` narrow where the subject resolves
// (ask_query.odin parses a query). Output is deterministic text, sorted for
// stable diffs — AI-readable, greppable, golden-tested (test/ask.sh). It
// runs after the check: no codegen.
// ---------------------------------------------------------------------------

import "core:fmt"
import "core:slice"
import "core:strings"
import "core:path/filepath"

// A query with no depth, and one with `all`. A tree of calls or types with none goes
// one level: the whole of one is often most of the program, and `all` is every level.
// In flow, every hop either way, but a list of what's reached stops at
// ASK_FLOW_ROWS_SHOWN unless it's `all`.
ASK_DEPTH_OMITTED :: -1
ASK_DEPTH_ALL     :: -2

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
    order:    int,        // its place among its container's members
    decl:     Token_Id,   // a field's declaration
}

Ask_Edge :: struct {
    from, to: int,
    kind:     Ask_Edge_Kind,
    via:      string,   // field / param name carrying the dependency ("" for returns / base)
    wrap:     string,   // "^" / "[]" wrapper shown on the target, "" if direct
    order:    int,      // its place among its container's members
    decl:     Token_Id, // a field's declaration
}

Ask_Result :: struct {
    nodes:    [dynamic]Ask_Node,
    edges:    [dynamic]Ask_Edge,
    root:     int,
    index_of: map[rawptr]int,   // type identity -> node id (intern dedup)
}

// --- type → display helpers ------------------------------------------------

// What a named type — a fun or a struct, an enum, a union, a distinct type —
// says of itself: its flat name, the name written, its module, where it is.
// False for any other type.
Ask_Named :: struct {
    name, source_name, home_package: string,
    span:                            Span,
}

ask_named :: proc(t: Type) -> (n: Ask_Named, ok: bool) {
    #partial switch v in t {
    case ^Type_Scope:    return {v.name, v.source_name, v.home_package, v.body_span}, true
    case ^Type_Enum:     return {v.name, v.source_name, v.home_package, v.span}, true
    case ^Type_Union:    return {v.name, v.source_name, v.home_package, v.span}, true
    case ^Type_Distinct: return {v.name, v.source_name, v.home_package, v.span}, true
    }
    return
}

ask_label :: proc(t: Type) -> string {
    n, named := ask_named(t)
    if !named { return type_flat_name(t) }
    return n.source_name if n.source_name != "" else ask_demangle(n.name, n.home_package)
}

// A name as it's written: a generic's instance, whose name is made up from it
// (`pick__i64`), under its generic's. A definition's first token is its name.
ask_written_name :: proc(t: Type) -> string {
    label := ask_label(t)
    first := ask_span(t).tok
    if first == 0 { return label }
    written := token_text(build_tokens[first])
    return written if strings.has_prefix(label, strings.concatenate({written, "__"}, context.temp_allocator)) else label
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
// still says which module it lives in, and so it can be asked about as it reads.
ask_qualified_label :: proc(t: Type) -> string {
    home := ask_home_package(t)
    if home == "" { return ask_written_name(t) }
    return fmt.tprintf("%s.%s", home, ask_written_name(t))
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
    n, _ := ask_named(t)
    return n.span
}

// The owning module's name (`mara.math`, `camera`, ""). The map / module-surface
// views group definitions by this.
ask_home_package :: proc(t: Type) -> string {
    n, _ := ask_named(t)
    return n.home_package
}

// The user-written name. Empty for monomorphized instances and other synthetic
// types — the signal the module views use to list DECLARATIONS (the generic
// `Program`), not instances (`mara_core_Program` minted under whoever uses it).
ask_source_name :: proc(t: Type) -> string {
    n, _ := ask_named(t)
    return n.source_name
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

// Peel ^ / [] / [N!] / [N] wrappers, returning the core type and a wrapper prefix
// (outermost first) to render on the target — e.g. `[]^Mesh` -> (Mesh, "[]^"),
// `[4!][4!]f32` -> (f32, "[4!][4!]"). SIZES are kept so the wrapper reads back
// as source (Vec3's `[3!]f32` vs Quat's `[4!]f32` stay distinct — collapsing
// both to `[]f32` made them indistinguishable); a list's too, `[16]`. Slices
// stay `[]` (no compile-time size).
ask_peel :: proc(t: Type) -> (core: Type, wrap: string) {
    cur := t
    parts: [dynamic]string
    peel: for {
        #partial switch v in cur {
        case ^Type_Ptr:           append(&parts, "^");    cur = v.elem
        case ^Type_Slice:         append(&parts, "[]");   cur = v.elem
        case ^Type_Fixed_Array:   append(&parts, fmt.tprintf("[%d!]", v.size)); cur = v.elem
        case ^Type_Partial_Array: append(&parts, fmt.tprintf("[%d]", v.size)); cur = v.elem
        case: break peel
        }
    }
    return cur, strings.concatenate(parts[:])
}

// --- node interning --------------------------------------------------------

// Whether a type is a union's variant's struct: part of its union, not a
// type of its module's own.
ask_is_variant :: proc(t: Type) -> bool {
    st, is_scope := t.(^Type_Scope)
    return is_scope && st.is_union_variant
}

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
    inside: string,  // the scope whose body defines it, as its name is said in full: "Pool." ("": a module's own)
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
// the disambiguation lever behind `in <file>`. A generic is found by the name it's
// written with; the instance that stands for it is the one that sorts first, so the
// answer is the same each run.
Ask_Dedup_Key :: struct { span: Span, sub: string }

// What is listed is what a scope defines itself, as the code sees it: a
// module's own definitions (`within` nil: any module's), or those in the body
// of the fun or struct `within` — never what a scope inside it defines, which
// is that scope's (`Pool.Head`, `Head in Pool`). `every`: no scope's view —
// all of them, for what counts every struct of a module.
ask_all_definitions :: proc(table: ^SymbolTable, scope_file: string, funcs: map[string]^Type_Scope, scope_module := "",
                            within: ^Type_Scope = nil, every := false) -> [dynamic]Ask_Match {
    matches: [dynamic]Ask_Match
    seen: map[Ask_Dedup_Key]int
    Where :: struct { within: ^Type_Scope, every: bool }
    at := Where{within, every}
    consider :: proc(matches: ^[dynamic]Ask_Match, seen: ^map[Ask_Dedup_Key]int, t: Type, scope_file: string, scope_module: string, at: Where) {
        // (The scope that defines it: the one asked about.)
        if owner := ask_owner_scope(t); !at.every {
            if at.within == nil && owner != nil && !owner.is_module { return }
            if at.within != nil && (owner == nil || owner.decl != at.within.decl || owner.is_module) { return }
        }
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
        if scope_file != "" && filepath.base(span_file(sp)) != scope_file { return }
        // `in <module>` narrows resolution to one module's namespace — the same
        // disambiguation lever as scope_file, one level coarser. The analysis root
        // never moves (always cwd + the stdlib it uses); this only filters which
        // definition of a name the subject resolves to.
        if scope_module != "" && ask_home_package(t) != scope_module { return }
        sub, _ := ask_sub(t)
        key := Ask_Dedup_Key{ span = sp, sub = sub }
        m := Ask_Match{ type_ = t, label = ask_written_name(t), flat = ask_type_name(t), sub = sub, span = sp, mark = ask_mark(t) }
        if at, known := seen[key]; known {
            if m.flat < matches[at].flat { matches[at] = m }
            return
        }
        seen[key] = len(matches)
        append(matches, m)
    }
    for _, f in table.funs           { consider(&matches, &seen, f, scope_file, scope_module, at) }
    for _, e in table.enums          { consider(&matches, &seen, e, scope_file, scope_module, at) }
    for _, u in table.unions         { consider(&matches, &seen, u, scope_file, scope_module, at) }
    for _, d in table.distinct_types { consider(&matches, &seen, d, scope_file, scope_module, at) }
    // FFI functions are absent from table.funs — surface the foreign ones from
    // checked.functions so resolution, fuzzy, and the module views all see them.
    // So are a generic's instances: they're how it's found.
    for _, f in funcs {
        if ask_is_foreign(f) || ask_written_name(f) != ask_label(f) { consider(&matches, &seen, f, scope_file, scope_module, at) }
    }
    for _, m in table.mono_cache { consider(&matches, &seen, m, scope_file, scope_module, at) }
    return matches
}

// The scope that defines a type or a fun: a module, or the fun or struct
// whose body has it (nil: unknown — the compiler's own).
ask_owner_scope :: proc(t: Type) -> ^Type_Scope {
    #partial switch v in t {
    case ^Type_Scope:    return v.parent_scope
    case ^Type_Enum:     return v.owner
    case ^Type_Union:    return v.tag_enum.owner if v.tag_enum != nil else nil
    case ^Type_Distinct: return v.owner
    }
    return nil
}

// Exact resolution: the definitions whose name the user typed verbatim — a
// module's own, or (`within`) those a fun's or a struct's body defines.
ask_resolve_all :: proc(table: ^SymbolTable, target: string, scope_file: string, funcs: map[string]^Type_Scope, scope_module := "",
                        within: ^Type_Scope = nil) -> [dynamic]Ask_Match {
    out: [dynamic]Ask_Match
    for m in ask_all_definitions(table, scope_file, funcs, scope_module, within) {
        if m.label == target || m.flat == target { append(&out, m) }
    }
    return out
}

// What a name with dots reaches, as code writes it: `m.Pool` — a module's
// definition; `Pool.Head`, `main.inner`, `m.Pool.Head` — one the body of the
// struct or fun before the last dot defines. Named in full, `Pool.Head`.
ask_resolve_path :: proc(checked: ^Checked_Program, target, scope_file, scope_module: string) -> [dynamic]Ask_Match {
    dot := strings.last_index_byte(target, '.')
    if dot <= 0 { return ask_resolve_all(checked.table, target, scope_file, checked.functions, scope_module) }
    owner, name := target[:dot], target[dot + 1:]
    if out := ask_resolve_all(checked.table, name, scope_file, checked.functions, owner); len(out) > 0 { return out }
    out: [dynamic]Ask_Match
    for o in ask_resolve_path(checked, owner, scope_file, scope_module) {
        ts, is_scope := o.type_.(^Type_Scope)
        if !is_scope { continue }
        for m in ask_resolve_all(checked.table, name, "", checked.functions, "", ts) {
            m := m
            m.inside = fmt.tprintf("%s%s.", o.inside, o.label)
            append(&out, m)
        }
    }
    return out
}

// The scopes whose bodies define something named `name`: each as `Scope.name`,
// for a miss to say where it is.
ask_defined_in :: proc(checked: ^Checked_Program, name: string) -> []string {
    out := make([dynamic]string, context.temp_allocator)
    for m in ask_all_definitions(checked.table, "", checked.functions, "", nil, every = true) {
        owner := ask_owner_scope(m.type_)
        if m.label != name || owner == nil || owner.is_module || m.mark == "synthetic" { continue }
        full := fmt.tprintf("%s.%s", ask_written_name(owner), name)
        if !slice.contains(out[:], full) { append(&out, full) }
    }
    slice.sort(out[:])
    return out[:]
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

// Top-N of what can be asked about, by fuzzy score against `target`, ties broken by
// name for determinism, and how many more there were. Used only when exact resolution
// returns nothing.
ask_fuzzy :: proc(checked: ^Checked_Program, target: string, scope_file: string, limit: int, scope_module := "") -> (out: [dynamic]Ask_Match, cut: int) {
    Scored :: struct { m: Ask_Match, score: int }
    pool := make([dynamic]Scored, context.temp_allocator)
    for m in ask_all_definitions(checked.table, scope_file, checked.functions, scope_module) {
        if sc := ask_fuzzy_score(target, m.label); sc > 0 {
            append(&pool, Scored{ m = m, score = sc })
        }
    }
    // (Dispatch groups and fields can be asked for by name too.)
    for tok in checked.names.dispatches {
        t := build_tokens[tok]
        f := build_files[t.file]
        if scope_module != "" && f.module != scope_module { continue }
        if scope_file != "" && filepath.base(f.path) != scope_file { continue }
        if sc := ask_fuzzy_score(target, token_text(t)); sc > 0 {
            append(&pool, Scored{ m = {label = token_text(t), sub = "dispatch", span = token_span(t)}, score = sc })
        }
    }
    seen_fields := make(map[Token_Id]bool, allocator = context.temp_allocator)
    for ts in ask_all_structs(checked.table) {
        if scope_file != "" && filepath.base(span_file(ts.body_span)) != scope_file { continue }
        if scope_module != "" && ts.home_package != scope_module { continue }
        for field in ts.fields {
            if field.decl == 0 || seen_fields[field.decl] { continue }
            sc := ask_fuzzy_score(target, field.name)
            if sc == 0 { continue }
            seen_fields[field.decl] = true
            owner := token_text(build_tokens[ts.body_span.tok]) if ts.body_span.tok != 0 else ask_label(ts)
            append(&pool, Scored{ m = {label = fmt.tprintf("%s.%s", owner, field.name), sub = "field", span = token_span(build_tokens[field.decl])}, score = sc })
        }
    }
    // (So can constants.)
    t := &build_tree
    for tok, def in checked.names.defs {
        if names_def_kind(t, Tree_Id(t.b[def])) != .Const { continue }
        tk := build_tokens[tok]
        f := build_files[tk.file]
        if scope_module != "" && f.module != scope_module { continue }
        if scope_file != "" && filepath.base(f.path) != scope_file { continue }
        if sc := ask_fuzzy_score(target, token_text(tk)); sc > 0 {
            append(&pool, Scored{ m = {label = token_text(tk), sub = "const", span = token_span(tk)}, score = sc })
        }
    }
    slice.sort_by(pool[:], proc(x, y: Scored) -> bool {
        if x.score != y.score { return x.score > y.score }
        if x.m.label != y.m.label { return x.m.label < y.m.label }
        return span_before(x.m.span, y.m.span)
    })
    for s, i in pool {
        if i == limit { break }
        append(&out, s.m)
    }
    return out, max(len(pool) - limit, 0)
}

// Suggestions as a list, saying how many didn't fit.
@(private="file")
ask_write_suggestions :: proc(b: ^strings.Builder, suggestions: []Ask_Match, cut: int) {
    for m in suggestions {
        fmt.sbprintf(b, "    %-8s %s  %s%s\n", m.sub, m.label, ask_loc(m.span), ask_mark_suffix(m.mark))
    }
    if cut > 0 { fmt.sbprintf(b, "    (and %d more)\n", cut) }
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
    wrap: string,          // "^" / "[]" / "[16]" / "[3!]" prefix shown on the target
    decl: Token_Id,        // a field's declaration
}

ask_out_edges :: proc(table: ^SymbolTable, t: Type, out: ^[dynamic]Ask_Out_Edge) {
    add :: proc(out: ^[dynamic]Ask_Out_Edge, ty: Type, kind: Ask_Edge_Kind, via: string, decl: Token_Id = 0) {
        core, wrap := ask_peel(ty)
        append(out, Ask_Out_Edge{ core = core, kind = kind, via = via, wrap = wrap, decl = decl })
    }
    #partial switch v in t {
    case ^Type_Scope:
        if v.kind == .Struct {
            for f in v.fields { add(out, f.type_, (.Embeds if f.is_using else .Contains), f.name, f.decl) }
        } else {
            for p in v.params        { add(out, p.type_, .Takes, p.name) }
            for rt in v.return_types { add(out, rt, .Returns, "") }
        }
    case ^Type_Distinct:
        add(out, v.base_type, .Base, "")
    case ^Type_Union:
        // A union depends on its variant structs.
        for vn in v.variants {
            st := v.variant_structs[vn]
            if st == nil { continue }
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
        for e, order in edges {
            // From the root only, honor `root_filter` — a function splits its
            // Takes (params) from its Returns so above/below show distinct graphs.
            // Deeper nodes (the param/return types' own fields) always expand fully.
            if is_root && e.kind not_in root_filter { continue }
            if _, named := ask_sub(e.core); !named {
                // Primitive / numeric member — it carries no graph node, so without
                // this it vanishes entirely. Record it as an inline field line so the
                // node shows its real shape (a leaf struct like Glyph lists its
                // x,y,w,h:i32 instead of reading as empty).
                append(&res.nodes[from].basics, Ask_Basic{ via = e.via, kind = e.kind, type_str = fmt.tprintf("%s%s", e.wrap, type_name(e.core)), order = order, decl = e.decl })
                continue
            }
            to, is_new := ask_intern(res, e.core)
            if is_new { res.nodes[to].dist = d + 1 }
            append(&res.edges, Ask_Edge{ from = from, to = to, kind = e.kind, via = e.via, wrap = e.wrap, order = order, decl = e.decl })
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
    n, _ := ask_named(t)
    return n.name
}

// One reverse reference: a container that points at some type, with the edge
// detail. The reverse walk is a BFS over an index of these (keyed by the flat
// name of the type referenced) rather than a full-table rescan per hop.
Ask_Rev_Ref :: struct { container: Type, kind: Ask_Edge_Kind, via: string, wrap: string }

// flat type name -> every container that references it (one outgoing edge each).
// Built once a check (the table keeps it: a question asks it, however many
// times) from the SAME `ask_out_edges` model `deps` uses, so the two
// directions can't disagree about the graph. Keyed by flat name (not pointer) so
// a generic's monomorphized fields — distinct objects sharing a canonical name —
// all fold onto the one queryable type. Containers are deduped by identity: a
// parameterized struct lives in BOTH `.structs` and `.funs` (data struct + ctor),
// and counting its edges twice would double every use-site.
ask_type_users :: proc(table: ^SymbolTable, funcs: map[string]^Type_Scope) -> map[string][dynamic]Ask_Rev_Ref {
    if table.users_made { return table.users }
    context.allocator = table.allocator
    rev: map[string][dynamic]Ask_Rev_Ref
    seen := make(map[rawptr]bool, allocator = context.temp_allocator)
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
    for _, s in table.funs           { add(table, &rev, &seen, s) }
    for _, u in table.unions         { add(table, &rev, &seen, u) }
    for _, d in table.distinct_types { add(table, &rev, &seen, d) }
    // FFI functions reference types through their params/returns (e.g. every SDL
    // fn taking a `Window`), so scan the foreign ones too or `users` misses them.
    for _, f in funcs { if ask_is_foreign(f) { add(table, &rev, &seen, f) } }
    table.users, table.users_made = rev, true
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
    rev := ask_type_users(table, funcs)
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
    case "what":                return "what", true      // what is at a point (`what at <file>:<line>:<col>`)
    case "cursor":              return "cursor", true    // what a window shows for an editor's cursor (`cursor at <file>@<byte>`)
    }
    return "", false
}

ask_canon_dir :: proc(s: string) -> (canon: string, ok: bool) {
    switch s {
    case "above", "bfor": return "above", true
    case "below", "aftr": return "below", true
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
    case "deps":  ask_deps(table, &res, root, depth, root_filter)   // (in source order)
    case "users":
        ask_users(table, &res, root, depth, funcs, users_kinds)
        ask_sort_edges(&res)
    }
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
    // (`<name> in <scope>`, the scope a struct or a fun: a definition its body
    // has — `Head in Pool` is `Pool.Head`.)
    nested: [dynamic]Ask_Match
    if scope != "" { nested = ask_resolve_path(checked, fmt.tprintf("%s.%s", scope, target), scope_file, scope_module) }
    if scope != "" && len(nested) == 0 {
        vout, vok, handled := ask_try_variable(checked, target, kind, dir, scope, pkg, scope_module, depth)
        if handled { return vout, vok }
        // Not a function. A struct's a named scope too: `x in S` is `S.x`.
        if tmatches := ask_resolve_all(checked.table, scope, "", checked.functions, scope_module); len(tmatches) > 0 {
            if tmatches[0].sub == "struct" || len(ask_variants_of(tmatches[0].type_)) > 0 {
                return ask_member(checked, scope, target, kind, dir, pkg, depth, scope_file, scope_module)
            }
            return fmt.tprintf("mara ask: '%s' is a %s, not a function — `in` scopes to a function's variables; query the %s directly with `mara ask %s`.\n", scope, tmatches[0].sub, tmatches[0].sub, scope), false
        }
        return fmt.tprintf("mara ask: '%s' is not a known module, file, or function in %s\n", scope, pkg), false
    }

    matches := nested if len(nested) > 0 else ask_resolve_all(checked.table, target, scope_file, checked.functions, scope_module)
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
        if surface, is_mod := ask_module_surface(checked, target, kind); is_mod {
            return surface, true
        }
        // A dispatch group: by name, or with its module as `logging.note`.
        dot := strings.last_index_byte(target, '.')
        group_name, group_module := target, scope_module
        if dot > 0 { group_name, group_module = target[dot + 1:], target[:dot] }
        if groups := ask_find_dispatches(checked, group_name, scope_file, group_module); len(groups) > 0 {
            return ask_dispatch_answer(checked, groups[:], group_name, kind, dir, pkg, depth)
        }
        // A name with a dot: a definition of that module, as a call tree's rows write
        // it (`scene.read_actor_look`); one a struct's or a fun's body defines
        // (`Pool.Head`, `main.inner`); or a struct's field.
        if dot > 0 {
            matches = ask_resolve_path(checked, target, scope_file, scope_module)
            if len(matches) == 0 {
                return ask_member(checked, target[:dot], target[dot + 1:], kind, dir, pkg, depth, scope_file, scope_module)
            }
        } else if answer, found, answered := ask_other_name(checked, target, kind, dir, depth, pkg, scope_file, scope_module); answered {
            return answer, found
        }
    }
    if len(matches) == 0 {
        // No exact hit — offer the closest names rather than a bare miss.
        suggestions, cut := ask_fuzzy(checked, target, scope_file, ASK_FUZZY_LIMIT, scope_module)
        if len(suggestions) > 0 {
            fmt.sbprintf(&b, "mara ask: no exact match for '%s' in %s — did you mean:\n", target, scope_desc)
            ask_write_suggestions(&b, suggestions[:], cut)
        } else {
            fmt.sbprintf(&b, "mara ask: no type or function named '%s' in %s\n", target, scope_desc)
        }
        // (One a struct's or a fun's body defines: it is that scope's.)
        if inside := ask_defined_in(checked, target); len(inside) > 0 {
            fmt.sbprintf(&b, "  (defined inside another scope: `mara ask %s`)\n", strings.join(inside, "`, `mara ask ", context.temp_allocator))
        } else {
            fmt.sbprint(&b, "  (a local or parameter? address it with `<name> in <fn>` or `at <file>:<line>`.)\n")
        }
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
            return span_before(a.span, b.span)
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
    // (A call tree is every instance's. The other views are of the instance standing
    // for the generic, with its types.)
    if eff_kind != "call" && ask_label(subject.type_) != subject.label {
        subject.mark = fmt.tprintf("generic: as %s", ask_label(subject.type_))
    }
    show_types := eff_kind == "types"
    show_call  := eff_kind == "call"
    show_flow  := eff_kind == "flow"
    show_above := dir  == "" || dir  == "above"
    show_below := dir  == "" || dir  == "below"

    // A type's natural view starts with what it is, which says what it's made of: what's
    // left to show is what uses it.
    bare_type := kind == "" && dir == "" && !is_fn
    hops := ask_type_hops(depth)
    // The module shown is the subject's OWN home package, not the cwd project
    // (`pkg`) — a stdlib type queried from a game dir is `mara.font`, not `Pounce`.
    home_pkg := ask_home_package(subject.type_)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&b, "%s%s — %s  %s   (module %s)%s\n", subject.inside, subject.label, subject.sub, ask_loc(subject.span), home_pkg, ask_mark_suffix(subject.mark))
    if kind == "" && dir == "" { ask_write_what_it_is(&b, subject) }
    header_len := len(strings.to_string(b))

    // Flow is the "outside" view, and for both a type (every value of it) and a
    // function (every call of it) it aggregates across the whole program, so every
    // function's def-use graph must exist first (data-only, cheap). Control deps
    // (post-dominators) are the expensive step: a function's are built the first
    // time a slice asks for one of its definitions' guards (du_def_guards).
    if show_flow { du_all(checked) }

    // The CALL graph (callees/callers) reads off the materialized call_graph and is
    // always available. The FLOW views (args in / results out) need call SITES, which
    // the graph records; with none, both flow directions are empty — say so
    // once and suppress their per-section "never called" repeats. (A function with no
    // callers can still have callees, so this gates flow only, not `call`.)
    fn_uncalled := false
    if is_fn && show_flow {
        sites := du_call_sites(checked, ft)
        fn_uncalled = len(sites) == 0
        delete(sites)
    }
    if fn_uncalled {
        fmt.sbprintf(&b, "\n%s has no call sites — its flow views (arguments in, results out) are empty\n", subject.label)
    }

    // ABOVE — what feeds / builds the subject.
    //   types: a struct's field types; a function's PARAMETER types.
    //   call:  a function's callees.
    //   flow:  what computes the args at a function's call sites, or what feeds a type's values.
    if show_above && show_types && !bare_type {
        filter := bit_set[Ask_Edge_Kind]{.Takes} if is_fn else ASK_ALL_EDGES
        if e, is_enum := subject.type_.(^Type_Enum); is_enum {
            render_enum_variants(&b, e)
        } else {
            render_ask_deps(&b, checked, subject.type_, hops, "above", filter)
        }
    }
    if show_above && show_call {
        if is_fn { render_fn_calls(&b, checked, ft, depth, forward = true) }
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
            render_ask_deps(&b, checked, subject.type_, hops, "below", {.Returns})
        } else {
            // Structural users only — fns that take/return this type are the `call`
            // kind (render_struct_calls below), not "structs I'm a field of".
            render_ask_users(&b, checked, subject.type_, hops, say_funs = bare_type)
        }
    }
    if bare_type { hit_write_variants(&b, &build_tree, checked.annot, ask_variants_of(subject.type_), subject.label, ask_is_error_set(subject.type_)) }
    if show_below && show_call {
        if is_fn { render_fn_calls(&b, checked, ft, depth, forward = false) }
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

// What a name asked about on its own is: a fun's signature and its doc comment; a
// type's doc comment and its declaration as written. The views under it say how it
// connects.
@(private="file")
ask_write_what_it_is :: proc(b: ^strings.Builder, subject: Ask_Match) {
    first := subject.span.tok
    if first == 0 { return }
    ts, is_scope := subject.type_.(^Type_Scope)
    is_fn := is_scope && ts.kind == .Fun
    if is_fn {
        if signature := ask_signature(first); signature != "" { fmt.sbprintf(b, "\n  %s\n", signature) }
    }
    if doc := doc_comment_above(build_tokens[first]); doc != "" {
        strings.write_byte(b, '\n')
        for line in strings.split_lines(doc, context.temp_allocator) {
            if line == "" { strings.write_byte(b, '\n') } else { fmt.sbprintf(b, "  %s\n", line) }
        }
    }
    if !is_fn {
        strings.write_byte(b, '\n')
        ask_write_declaration(b, first)
    }
}

// A definition as it's written, comments and all, from the line its name's on to the
// end of its body. A fun in its body shows its signature, its own body as `{ … }`.
@(private="file")
ask_write_declaration :: proc(b: ^strings.Builder, first: Token_Id) {
    f := build_files[build_tokens[first].file]
    Cut :: struct { from, to: int }
    cuts := make([dynamic]Cut, context.temp_allocator)
    braces, open := 0, 0
    last := first
    walk: for id := first; id < f.end_token; id += 1 {
        tok := build_tokens[id]
        #partial switch tok.kind {
        case .Left_Paren, .Left_Bracket:
            open += 1
        case .Right_Paren, .Right_Bracket:
            open -= 1
        case .Left_Brace:
            if braces > 0 {
                if close := ask_fun_body_end(f, id); close != 0 {
                    append(&cuts, Cut{int(tok.offset) + 1, int(build_tokens[close].offset)})
                    id, last = close, close
                    continue walk
                }
            }
            braces += 1
        case .Right_Brace:
            braces -= 1
            if braces == 0 {
                last = id
                break walk
            }
        case .Newline, .EOF:
            if braces == 0 && open == 0 { break walk }
            continue walk
        }
        last = id
    }
    src := f.source
    lo, hi := int(build_tokens[first].offset), int(build_tokens[last].offset)
    for lo > 0 && src[lo - 1] != '\n' { lo -= 1 }
    for hi < len(src) && src[hi] != '\n' { hi += 1 }
    text := strings.builder_make(context.temp_allocator)
    at := lo
    for c in cuts {
        strings.write_string(&text, src[at:c.from])
        strings.write_string(&text, " … ")
        at = c.to
    }
    strings.write_string(&text, src[at:hi])
    for line in strings.split_lines(strings.to_string(text), context.temp_allocator) {
        trimmed := strings.trim_right_space(line)
        spaced, _ := strings.replace_all(trimmed, "\t", "    ", context.temp_allocator)
        fmt.sbprintf(b, "  %s\n", spaced)
    }
}

// The `}` of a fun's body over lines, its `{` the token `open`; 0 for any other brace.
@(private="file")
ask_fun_body_end :: proc(f: ^Source_File, open: Token_Id) -> Token_Id {
    line := token_line(build_tokens[open])
    is_fun := false
    for id := open - 1; id >= f.first_token && token_line(build_tokens[id]) == line; id -= 1 {
        is_fun ||= build_tokens[id].kind == .Fun
    }
    if !is_fun { return 0 }
    braces := 0
    for id := open; id < f.end_token; id += 1 {
        #partial switch build_tokens[id].kind {
        case .Left_Brace:
            braces += 1
        case .Right_Brace:
            braces -= 1
            if braces == 0 { return id if token_line(build_tokens[id]) != line else 0 }
        }
    }
    return 0
}

// What follows a declaration on its line: a comment, or "".
@(private="file")
ask_line_comment :: proc(decl: Token_Id) -> string {
    if decl == 0 { return "" }
    tok := build_tokens[decl]
    f := build_files[tok.file]
    hi := int(tok.offset)
    for hi < len(f.source) && f.source[hi] != '\n' { hi += 1 }
    id := decl
    for id + 1 < f.end_token && int(build_tokens[id + 1].offset) < hi && build_tokens[id + 1].kind != .Newline { id += 1 }
    last := build_tokens[id]
    rest := strings.trim_space(f.source[int(last.offset + last.len):hi])
    return rest if strings.has_prefix(rest, "//") else ""
}

// --- variants ----------------------------------------------------------------

// A union's, an enum's or an error set's variants, in source order.
ask_variants_of :: proc(t: Type) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    #partial switch v in t {
    case ^Type_Enum:
        for _, decl in v.variant_decls { if decl != 0 { append(&out, decl) } }
    case ^Type_Union:
        for name in v.variants { if decl := variant_decl(v, name); decl != 0 { append(&out, decl) } }
    }
    slice.sort(out[:])
    return out[:]
}

ask_is_error_set :: proc(t: Type) -> bool {
    e, is_enum := t.(^Type_Enum)
    return is_enum && e.is_error_kind
}

// `types above` of a union without data, or an error set: its variants, what each's
// numbered unless it's only an error's name.
@(private="file")
render_enum_variants :: proc(b: ^strings.Builder, e: ^Type_Enum) {
    decls := ask_variants_of(e)
    fmt.sbprintf(b, "\nabove (types)   (%s)\n", ask_plural(len(decls), "variant"))
    for decl in decls {
        name := token_text(build_tokens[decl])
        strings.write_string(b, "  ")
        strings.write_string(b, name)
        if !e.is_error_kind { fmt.sbprintf(b, " = %d", e.variants[name]) }
        if comment := ask_line_comment(decl); comment != "" { fmt.sbprintf(b, "   %s", comment) }
        strings.write_byte(b, '\n')
    }
}

// A definition as written up to its body, on one line: a fun's name, params and
// results, whatever lines they're written on.
@(private="file")
ask_signature :: proc(first: Token_Id) -> string {
    f := build_files[build_tokens[first].file]
    sb := strings.builder_make(context.temp_allocator)
    open := 0   // brackets open
    after := -1   // where the token before ended
    walk: for id := first; id < f.end_token; id += 1 {
        tok := build_tokens[id]
        #partial switch tok.kind {
        case .Left_Paren, .Left_Bracket:
            open += 1
        case .Right_Paren, .Right_Bracket, .Right_Brace:
            open -= 1
        case .Left_Brace:
            if open == 0 { break walk }
            open += 1
        case .Newline, .Do, .EOF:
            if open == 0 { break walk }
            if tok.kind == .Newline { continue walk }
        }
        if after >= 0 {
            gap := f.source[after:tok.offset]
            if !strings.contains(gap, "\n") {
                strings.write_string(&sb, gap)
            } else if tok.kind != .Right_Paren && !strings.has_suffix(strings.to_string(sb), "(") {
                strings.write_byte(&sb, ' ')
            }
        }
        strings.write_string(&sb, f.source[tok.offset:][:tok.len])
        after = int(tok.offset + tok.len)
    }
    // (A comma ending a last line of params is nothing to read here.)
    joined, _ := strings.replace_all(strings.to_string(sb), ",)", ")", context.temp_allocator)
    return joined
}

// --- a field asked for by name -----------------------------------------------

// A field a name can be: one per declaration, a generic's instances declaring
// theirs once.
Ask_Field :: struct {
    owner: string,     // its struct's name, as written
    home:  string,     // its struct's module
    decl:  Token_Id,   // where it's declared
}

// Every struct of the program. A generic's are its instances, each with its own copy
// of its fields; a constructor's table holds a struct too.
@(private="file")
ask_all_structs :: proc(table: ^SymbolTable) -> [dynamic]^Type_Scope {
    out := make([dynamic]^Type_Scope, context.temp_allocator)
    seen := make(map[^Type_Scope]bool, allocator = context.temp_allocator)
    add :: proc(out: ^[dynamic]^Type_Scope, seen: ^map[^Type_Scope]bool, ts: ^Type_Scope) {
        if ts == nil || ts.kind != .Struct || ts.is_module || seen[ts] { return }
        seen[ts] = true
        append(out, ts)
    }
    for _, ts in table.funs { add(&out, &seen, ts) }
    for _, ts in table.mono_cache { add(&out, &seen, ts) }
    return out
}

// The fields called `name`, of the struct at `owner` (or of any, with none), in
// source order. The `in` scopes narrow them as they do any name.
@(private="file")
ask_find_fields :: proc(table: ^SymbolTable, name, scope_file, scope_module: string, owner: Span) -> [dynamic]Ask_Field {
    out: [dynamic]Ask_Field
    for ts in ask_all_structs(table) {
        if owner.at != 0 && ts.body_span.at != owner.at { continue }
        if owner.at == 0 {
            if scope_file != "" && filepath.base(span_file(ts.body_span)) != scope_file { continue }
            if scope_module != "" && ts.home_package != scope_module { continue }
        }
        for field in ts.fields {
            if field.name != name || field.decl == 0 { continue }
            already := false
            for f in out { already ||= f.decl == field.decl }
            if already { continue }
            written := token_text(build_tokens[ts.body_span.tok]) if ts.body_span.tok != 0 else ask_label(ts)
            append(&out, Ask_Field{owner = written, home = ts.home_package, decl = field.decl})
        }
    }
    slice.sort_by(out[:], proc(a, b: Ask_Field) -> bool { return a.decl < b.decl })
    return out
}

// The answer for fields found by name: `what at` at the declaration of the one,
// and with several, which they are. A field has no graphs to choose from.
@(private="file")
ask_field_answer :: proc(checked: ^Checked_Program, fields: []Ask_Field, name, kind, dir: string, depth: int, pkg: string) -> (out: string, ok: bool) {
    if len(fields) > 1 {
        sb := strings.builder_make()
        fmt.sbprintf(&sb, "mara ask: '%s' is a field of %d structs — name one with `<struct>.%s`:\n", name, len(fields), name)
        for f in fields {
            fmt.sbprintf(&sb, "    %s.%s  %s\n", f.owner, name, ask_loc(token_span(build_tokens[f.decl])))
        }
        return strings.to_string(sb), false
    }
    if kind != "" || dir != "" || depth != ASK_DEPTH_OMITTED {
        return fmt.tprintf("mara ask: %s.%s is a field: the answer is where it's written and read, with no types, call or flow, above or below, or depth\n", fields[0].owner, name), false
    }
    f := fields[0]
    home := f.home if f.home != "" else pkg
    title := fmt.tprintf("%s.%s — field  %s   (module %s)", f.owner, name, ask_loc(token_span(build_tokens[f.decl])), home)
    return ask_what_at_token(&build_tree, checked.annot, f.decl, title, checked)
}

// `<struct>.<member>`, or `<member> in <struct>`: the field's answer, or the fun's
// when that's what's named (`module.struct.member` narrows to that module). A miss
// says what there is.
@(private="file")
ask_member :: proc(checked: ^Checked_Program, owner_text, member, kind, dir, pkg: string, depth: int, scope_file, scope_module: string) -> (out: string, ok: bool) {
    owner, module := owner_text, scope_module
    if dot := strings.last_index_byte(owner_text, '.'); dot > 0 {
        owner, module = owner_text[dot + 1:], owner_text[:dot]
    }
    sb := strings.builder_make()
    // A union's or an error set's: its variant.
    for m in ask_resolve_all(checked.table, owner, scope_file, checked.functions, module) {
        decls := ask_variants_of(m.type_)
        if len(decls) == 0 { continue }
        for decl in decls {
            if token_text(build_tokens[decl]) != member { continue }
            return ask_variant_answer(checked, {{ask_written_name(m.type_), m.sub, ask_home_package(m.type_), decl}}, member, kind, dir, depth, pkg)
        }
        words := make([dynamic]string, context.temp_allocator)
        for decl in decls { append(&words, token_text(build_tokens[decl])) }
        fmt.sbprintf(&sb, "mara ask: %s %s has no variant '%s' — its variants: %s\n", m.sub, m.label, member, strings.join(words[:], ", ", context.temp_allocator))
        return strings.to_string(sb), false
    }
    owners: [dynamic]Ask_Match
    defer delete(owners)
    for m in ask_resolve_all(checked.table, owner, scope_file, checked.functions, module) {
        if m.sub == "struct" { append(&owners, m) }
    }
    // Through fields: `Viewer.camera.position`, the struct's what `camera` is.
    owner_span: Span
    if len(owners) == 0 {
        if ts, missing, found := ask_follow_fields(checked, owner_text, scope_file, scope_module); found {
            if missing != "" {
                fmt.sbprintf(&sb, "mara ask: %s has no field '%s'\n", ask_written_name(ts), missing)
                return strings.to_string(sb), false
            }
            owner_span = ts.body_span
            owner = ask_written_name(ts)
            append(&owners, Ask_Match{type_ = ts, label = owner, sub = "struct", span = ts.body_span})
        }
    }
    if len(owners) == 0 {
        fmt.sbprintf(&sb, "mara ask: no struct or module named '%s' in %s\n", owner_text, pkg)
        suggestions, cut := ask_fuzzy(checked, owner, scope_file, ASK_FUZZY_LIMIT, module)
        ask_write_suggestions(&sb, suggestions[:], cut)
        return strings.to_string(sb), false
    }
    if len(owners) > 1 {
        slice.sort_by(owners[:], proc(a, b: Ask_Match) -> bool { return span_before(a.span, b.span) })
        fmt.sbprintf(&sb, "mara ask: '%s' is %d structs — narrow with `in <module>`:\n", owner, len(owners))
        for m in owners { fmt.sbprintf(&sb, "    %s  %s\n", m.label, ask_loc(m.span)) }
        return strings.to_string(sb), false
    }
    owner_span = owners[0].span
    fields := ask_find_fields(checked.table, member, "", "", owner_span)
    defer delete(fields)
    if len(fields) > 0 { return ask_field_answer(checked, fields[:], member, kind, dir, depth, pkg) }
    // (Not a field: one of its funs, or nothing it has.)
    names := make([dynamic]string, context.temp_allocator)
    for ts in ask_all_structs(checked.table) {
        if ts.body_span.at != owner_span.at { continue }
        for field in ts.fields {
            if !slice.contains(names[:], field.name) { append(&names, field.name) }
        }
    }
    fmt.sbprintf(&sb, "mara ask: struct %s has no field '%s'", owner, member)
    if len(names) > 0 { fmt.sbprintf(&sb, " — its fields: %s", strings.join(names[:], ", ", context.temp_allocator)) }
    strings.write_byte(&sb, '\n')
    return strings.to_string(sb), false
}

// The struct a path of fields ends at, `Viewer.camera` or `scene.Viewer.camera`: its
// start a struct, by the words before it the module it's in. `missing`, a field the
// path names that isn't there; found false, when the path starts at no struct or goes
// through something that holds no fields.
@(private="file")
ask_follow_fields :: proc(checked: ^Checked_Program, path, scope_file, scope_module: string) -> (ts: ^Type_Scope, missing: string, found: bool) {
    parts := strings.split(path, ".", context.temp_allocator)
    for part, k in parts {
        module := scope_module if k == 0 else strings.join(parts[:k], ".", context.temp_allocator)
        for m in ask_resolve_all(checked.table, part, scope_file, checked.functions, module) {
            start, is_scope := m.type_.(^Type_Scope)
            if !is_scope || start.kind != .Struct { continue }
            cur := start
            walk: for name in parts[k + 1:] {
                for f in cur.fields {
                    if f.name != name { continue }
                    core, _ := ask_peel(f.type_)
                    next, is_struct := distinct_base(core).(^Type_Scope)
                    if !is_struct || next.kind != .Struct { return nil, "", false }
                    cur = next
                    continue walk
                }
                return cur, name, true
            }
            return cur, "", true
        }
    }
    return nil, "", false
}

// --- a variant or a constant, by name -----------------------------------------

Ask_Variant :: struct {
    owner: string,     // its type's name, as written
    sub:   string,     // what its type is: `union`, `error`
    home:  string,     // its type's module
    decl:  Token_Id,
}

// The variants called `name`, in source order; a generic's instances declare theirs
// once.
@(private="file")
ask_find_variants :: proc(table: ^SymbolTable, name, scope_file, scope_module: string) -> [dynamic]Ask_Variant {
    out: [dynamic]Ask_Variant
    add :: proc(out: ^[dynamic]Ask_Variant, t: Type, name, scope_file, scope_module: string) {
        if scope_module != "" && ask_home_package(t) != scope_module { return }
        if scope_file != "" && filepath.base(span_file(ask_span(t))) != scope_file { return }
        decl := variant_decl(t, name)
        if decl == 0 { return }
        for v in out { if v.decl == decl { return } }
        sub, _ := ask_sub(t)
        append(out, Ask_Variant{ask_written_name(t), sub, ask_home_package(t), decl})
    }
    for _, e in table.enums {
        if !e.is_synthetic { add(&out, e, name, scope_file, scope_module) }   // (a union's `_Tag`: its union's)
    }
    for _, u in table.unions { add(&out, u, name, scope_file, scope_module) }
    for _, m in table.mono_cache { add(&out, m, name, scope_file, scope_module) }
    slice.sort_by(out[:], proc(a, b: Ask_Variant) -> bool { return a.decl < b.decl })
    return out
}

// Where a variant's named. It has no graphs to choose from.
@(private="file")
ask_variant_answer :: proc(checked: ^Checked_Program, variants: []Ask_Variant, name, kind, dir: string, depth: int, pkg: string) -> (out: string, ok: bool) {
    if len(variants) > 1 {
        sb := strings.builder_make()
        fmt.sbprintf(&sb, "mara ask: '%s' is a variant of %d types — name one with `<type>.%s`:\n", name, len(variants), name)
        for v in variants { fmt.sbprintf(&sb, "    %s.%s  %s\n", v.owner, name, ask_loc(token_span(build_tokens[v.decl]))) }
        return strings.to_string(sb), false
    }
    v := variants[0]
    if kind != "" || dir != "" || depth != ASK_DEPTH_OMITTED {
        return fmt.tprintf("mara ask: %s.%s is a variant: the answer is where it's named, with no types, call or flow, above or below, or depth\n", v.owner, name), false
    }
    home := v.home if v.home != "" else pkg
    title := fmt.tprintf("%s — variant of %s %s  %s   (module %s)", name, v.sub, v.owner, ask_loc(token_span(build_tokens[v.decl])), home)
    return hit_variant_answer(&build_tree, checked.annot, v.decl, title), true
}

// A constant or a global a name can be.
@(private="file")
Ask_Value :: struct {
    word: string,     // `const`, `global`
    decl: Token_Id,
}

// The constants and globals called `name`, in source order.
@(private="file")
ask_find_values :: proc(checked: ^Checked_Program, name, scope_file, scope_module: string) -> [dynamic]Ask_Value {
    out: [dynamic]Ask_Value
    add :: proc(out: ^[dynamic]Ask_Value, word: string, tok: Token_Id, scope_file, scope_module: string) {
        f := build_files[build_tokens[tok].file]
        if scope_module != "" && f.module != scope_module { return }
        if scope_file != "" && filepath.base(f.path) != scope_file { return }
        for v in out { if v.decl == tok { return } }
        append(out, Ask_Value{word, tok})
    }
    t := &build_tree
    for tok, def in checked.names.defs {
        if token_text(build_tokens[tok]) == name && names_def_kind(t, Tree_Id(t.b[def])) == .Const { add(&out, "const", tok, scope_file, scope_module) }
    }
    slice.sort_by(out[:], proc(a, b: Ask_Value) -> bool { return a.decl < b.decl })
    return out
}

// A name that's no definition with a view of its own: a field, a variant, a constant or
// a global. One answers; several say what they are. answered false for none.
@(private="file")
ask_other_name :: proc(checked: ^Checked_Program, name, kind, dir: string, depth: int, pkg, scope_file, scope_module: string) -> (out: string, ok: bool, answered: bool) {
    fields := ask_find_fields(checked.table, name, scope_file, scope_module, {})
    variants := ask_find_variants(checked.table, name, scope_file, scope_module)
    values := ask_find_values(checked, name, scope_file, scope_module)
    defer { delete(fields); delete(variants); delete(values) }
    groups := 0
    for n in ([3]int{len(fields), len(variants), len(values)}) { groups += 1 if n > 0 else 0 }
    if groups == 0 { return "", false, false }
    if groups == 1 && len(values) <= 1 {
        if len(fields) > 0 {
            out, ok = ask_field_answer(checked, fields[:], name, kind, dir, depth, pkg)
        } else if len(variants) > 0 {
            out, ok = ask_variant_answer(checked, variants[:], name, kind, dir, depth, pkg)
        } else {
            v := values[0]
            tok := build_tokens[v.decl]
            if kind != "" || dir != "" || depth != ASK_DEPTH_OMITTED {
                return fmt.tprintf("mara ask: %s is a %s: the answer is where it's read, with no types, call or flow, above or below, or depth\n", name, v.word), false, true
            }
            title := fmt.tprintf("%s — %s  %s   (module %s)", name, v.word, ask_loc(token_span(tok)), build_files[tok.file].module)
            out, ok = ask_what_at_token(&build_tree, checked.annot, v.decl, title, checked)
        }
        return out, ok, true
    }
    sb := strings.builder_make()
    fmt.sbprintf(&sb, "mara ask: '%s' names %d things:\n", name, len(fields) + len(variants) + len(values))
    for f in fields { fmt.sbprintf(&sb, "    field    %s.%s  %s\n", f.owner, name, ask_loc(token_span(build_tokens[f.decl]))) }
    for v in variants { fmt.sbprintf(&sb, "    variant  %s.%s  %s\n", v.owner, name, ask_loc(token_span(build_tokens[v.decl]))) }
    for v in values {
        tok := build_tokens[v.decl]
        fmt.sbprintf(&sb, "    %-8s %s  %s   (`mara ask %s in %s`)\n", v.word, name, ask_loc(token_span(tok)), name, build_files[tok.file].module)
    }
    return strings.to_string(sb), false, true
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
    f := du_fn(checked, ft)

    // `return` is the function's output endpoint — the inside view (what feeds the
    // return), the counterpart to slicing a parameter. `return` is a keyword, so it
    // can never collide with a local name.
    if target == "return" {
        return render_return_slice(checked, ft, scope, kind, dir, pkg), true, true
    }

    vars: [dynamic]^Var_Binding
    defer delete(vars)
    if f != nil {
        for vb in f.vars { if vb.name == target { append(&vars, vb) } }
    }
    if len(vars) == 0 {
        return fmt.tprintf("mara ask: no variable '%s' in function '%s' — its parameters and locals are sliceable.\n", target, scope), false, true
    }
    if len(vars) > 1 {
        // Shadowing: same name, different declarations. Don't guess — list them.
        slice.sort_by(vars[:], proc(a, b: ^Var_Binding) -> bool { return span_line(a.span) < span_line(b.span) })
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
        if ft != nil && ft.kind == .Fun && filepath.base(span_file(ft.body_span)) == file {
            du_fn(checked, ft)
        }
    }
    // Distinct variables with a definition at exactly (file, line), remembering the
    // def found there — flow roots at THAT write, so `at` on a `*=` slices from the
    // modification (its above = the earlier mods + decl), not the whole variable.
    bindings: [dynamic]^Var_Binding
    defer delete(bindings)
    seen: map[^Var_Binding]bool
    defer delete(seen)
    root_of: map[^Var_Binding]^Def
    defer delete(root_of)
    for d in checked.du.defs {
        if d.binding == nil || seen[d.binding] { continue }
        if span_line(d.span) == line && filepath.base(span_file(d.span)) == file {
            seen[d.binding] = true
            append(&bindings, d.binding)
            root_of[d.binding] = d
        }
    }
    if len(bindings) == 0 {
        // (None defined there: what's written there, unless a view of a variable's asked for.)
        if kind == "" && dir == "" { return ask_what_at_line(checked, loc) }
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
    return render_var_slice(checked, bindings[0], ask_label(bindings[0].fn), kind, dir, pkg, depth, root_of[bindings[0]]), true
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

render_ask_deps :: proc(b: ^strings.Builder, checked: ^Checked_Program, subject: Type, hops: int, dir: string, filter: bit_set[Ask_Edge_Kind]) {
    res := ask_compute(checked.table, subject, "deps", ask_type_reach(hops), checked.functions, filter)
    root := &res.nodes[res.root]
    if len(res.edges) == 0 && len(root.basics) == 0 {
        fmt.sbprintf(b, "\n%s (types)   (no type dependencies)\n", dir)
        return
    }
    // The named types shown: the subject's not one of them, and one a level past the
    // last is only a name.
    types := 0
    for n, i in res.nodes {
        if i == res.root || n.sub == "fun" { continue }
        if hops < 0 || n.dist <= max(hops, 1) { types += 1 }
    }
    count := ask_plural(types, "type")
    if len(res.edges) == 0 { count = "basic types only" }   // a struct built only from primitives (Glyph)
    fmt.sbprintf(b, "\n%s (types)   (%s, %s)\n", dir, count, ask_depth_label(hops))

    // Walk the type graph as an indented tree (mirror of the call tree). A GLOBAL
    // `seen` expands each aggregate once: a struct reached twice shows "(shown
    // above)" and the walk terminates on cyclic / diamond graphs.
    if hops != 0 {
        seen: map[int]bool
        defer delete(seen)
        seen[res.root] = true
        ask_walk_deps(b, &res, res.root, 1, &seen)
    }
    // (How much further it goes.)
    if hops >= 0 {
        whole := ask_compute(checked.table, subject, "deps", -1, checked.functions, filter)
        total := 0
        for n, i in whole.nodes {
            if i != whole.root && n.sub != "fun" { total += 1 }
        }
        shown := types if hops != 0 else 0
        if total > shown { fmt.sbprintf(b, "  (%d more: add a depth, or 'all')\n", total - shown) }
    }
}

// Render node_id's members at `indent`, in source order, recursing into struct / union
// targets. distinct / enum / primitive targets are LEAVES: we don't unwrap a Vec3 to
// its `[3!]f32` base. Names are module-qualified. The first level's say what's beside
// their declarations.
ask_walk_deps :: proc(b: ^strings.Builder, res: ^Ask_Result, node_id, indent: int, seen: ^map[int]bool) {
    edges := make([dynamic]Ask_Edge, context.temp_allocator)
    for e in res.edges {
        if e.from == node_id { append(&edges, e) }
    }
    basics := res.nodes[node_id].basics[:]
    pad :: proc(b: ^strings.Builder, indent: int, decl: Token_Id) -> string {
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        comment := ask_line_comment(decl) if indent == 1 else ""
        return fmt.tprintf("   %s", comment) if comment != "" else ""
    }
    for len(edges) > 0 || len(basics) > 0 {
        if len(edges) == 0 || (len(basics) > 0 && basics[0].order < edges[0].order) {
            m := basics[0]
            basics = basics[1:]
            comment := pad(b, indent, m.decl)
            fmt.sbprintf(b, "%s : %s%s\n", ask_member_name(m.via, m.kind), m.type_str, comment)
            continue
        }
        e := edges[0]
        ordered_remove(&edges, 0)
        tgt := res.nodes[e.to]
        // (One a level past the last has nothing to show, so nothing's been shown.)
        expandable := (tgt.sub == "struct" || tgt.sub == "union") && len(tgt.basics) + ask_edges_from(res, e.to) > 0
        comment := pad(b, indent, e.decl)
        fmt.sbprintf(b, "%s : %s%s", ask_member_name(e.via, e.kind), e.wrap, ask_qnode(tgt))
        if expandable && seen[e.to] { fmt.sbprint(b, "  (shown above)") }
        fmt.sbprintf(b, "%s\n", comment)
        if expandable && !seen[e.to] {
            seen[e.to] = true
            ask_walk_deps(b, res, e.to, indent + 1, seen)
        }
    }
}

@(private="file")
ask_edges_from :: proc(res: ^Ask_Result, node: int) -> int {
    n := 0
    for e in res.edges {
        if e.from == node { n += 1 }
    }
    return n
}

// How many levels a tree of types shows: what's asked, or the direct ones. Below zero,
// every level.
@(private="file")
ask_type_hops :: proc(depth: int) -> int {
    return 1 if depth == ASK_DEPTH_OMITTED else depth
}

// ... as the walks take it: how far past the direct ones they go.
@(private="file")
ask_type_reach :: proc(hops: int) -> int {
    return max(hops - 1, 0) if hops >= 0 else -1
}

// "full closure (depth ∞)" when unbounded, else "depth N" — shared by both
// direction headers so they describe the hop budget identically.
ask_depth_label :: proc(depth: int) -> string {
    return "full closure (depth ∞)" if depth < 0 else fmt.tprintf("depth %d", depth)
}

// One function in a call tree: every instance of it, a generic's being one fun as
// written.
@(private="file")
Ask_Call_Fun :: struct {
    nodes: [dynamic]int,
    key:   Ask_Call_Key,
    order: int,      // its first call's line, for callees
    label: string,
    span:  Span,
}

// What makes two nodes one function: where it's defined. The funs the compiler makes
// for an enum (from_text, `E(n)`) all say the enum's, so they're told apart by name;
// one with no place of its own, by its node.
@(private="file")
Ask_Call_Key :: struct {
    span: Span,
    name: string,
    node: int,
}

@(private="file")
ask_call_key :: proc(cg: ^Call_Graph, node: int) -> Ask_Call_Key {
    s := cg.nodes[node]
    span := ask_span(s)
    if span.at == 0 { return {node = node} }
    if _, written := s.origin.(Origin_Source); written { return {span = span} }
    return {span = span, name = s.source_name if s.source_name != "" else s.name}
}

// A walk over a call tree.
@(private="file")
Ask_Call_Walk :: struct {
    cg:      ^Call_Graph,
    adj:     [][dynamic]int,                   // callees, or callers
    forward: bool,                             // callees
    sites:   map[Call_Edge][dynamic]Tree_Id,   // every call written (the call graph's)
    seen:    map[Ask_Call_Key]bool,
}

// The functions next to `nodes` in the tree, duplicate call sites and self-recursion
// dropped: callees in call order, callers where they're defined.
@(private="file")
ask_call_funs :: proc(w: ^Ask_Call_Walk, nodes: []int) -> [dynamic]Ask_Call_Fun {
    funs: [dynamic]Ask_Call_Fun
    at := make(map[Ask_Call_Key]int, allocator = context.temp_allocator)
    for node in nodes {
        for k in w.adj[node] {
            if slice.contains(nodes, k) { continue }
            caller, callee := w.cg.nodes[node], w.cg.nodes[k]
            if !w.forward { caller, callee = callee, caller }
            line := cg_first_line(w.cg, &build_tree, Call_Edge{from = caller, to = callee})
            key := ask_call_key(w.cg, k)
            if i, known := at[key]; known {
                f := &funs[i]
                if !slice.contains(f.nodes[:], k) { append(&f.nodes, k) }
                f.order = min(f.order, line)
                continue
            }
            at[key] = len(funs)
            f := Ask_Call_Fun{key = key, order = line, label = ask_qualified_label(w.cg.nodes[k]), span = ask_span(w.cg.nodes[k])}
            append(&f.nodes, k)
            append(&funs, f)
        }
    }
    context.user_ptr = w
    slice.sort_by(funs[:], proc(x, y: Ask_Call_Fun) -> bool {
        w := cast(^Ask_Call_Walk)context.user_ptr
        if w.forward && x.order != y.order { return x.order < y.order }
        if x.span != y.span { return span_before(x.span, y.span) }
        return x.label < y.label
    })
    return funs
}

// Print a level of a call tree and the levels under it, `remaining` deep. A row is a
// function, where it's defined. Under a first level's are its calls, each a line of its
// own: where it's written, and what's written. A function shows once: a cycle or a
// utility called everywhere says "(shown above)" after that.
@(private="file")
ask_walk_calls :: proc(w: ^Ask_Call_Walk, b: ^strings.Builder, nodes: []int, indent, remaining: int) {
    if remaining <= 0 { return }
    for fun in ask_call_funs(w, nodes) {
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        fmt.sbprintf(b, "%s  %s", ask_loc(fun.span), fun.label)
        shown := fun.key in w.seen
        if shown {
            strings.write_string(b, "  (shown above)")
        } else {
            sub, _ := ask_sub(w.cg.nodes[fun.nodes[0]])
            if sub != "fun" { fmt.sbprintf(b, "  (%s)", sub) }
        }
        strings.write_byte(b, '\n')
        if indent == 1 { ask_write_calls(w, b, nodes, fun, indent + 1) }
        if shown { continue }
        w.seen[fun.key] = true
        ask_walk_calls(w, b, fun.nodes[:], indent + 1, remaining - 1)
    }
}

// The calls between `nodes` and a function next to them: a line once. None is written
// where only a default argument makes the call.
@(private="file")
ask_write_calls :: proc(w: ^Ask_Call_Walk, b: ^strings.Builder, nodes: []int, fun: Ask_Call_Fun, indent: int) {
    toks := make([dynamic]Token_Id, context.temp_allocator)
    for node in nodes {
        for k in fun.nodes {
            caller, callee := w.cg.nodes[node], w.cg.nodes[k]
            if !w.forward { caller, callee = callee, caller }
            if sites, called := w.sites[Call_Edge{from = caller, to = callee}]; called {
                for n in sites { append(&toks, build_tree.first[n]) }
            }
        }
    }
    slice.sort(toks[:])
    last: Token
    any := false
    for id in toks {
        tok := build_tokens[id]
        if any && tok.file == last.file && token_line(tok) == token_line(last) { continue }
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        fmt.sbprintf(b, "at %s  %s\n", ask_loc(token_span(tok)), hit_source_line(tok))
        last, any = tok, true
    }
    if !any {
        for _ in 0 ..< 2 * indent { strings.write_byte(b, ' ') }
        strings.write_string(b, "(from a default argument)\n")
    }
}

// How many functions the tree reaches that `w.seen` hasn't shown.
@(private="file")
ask_calls_unshown :: proc(w: ^Ask_Call_Walk, roots: []int) -> int {
    visited := make(map[int]bool, allocator = context.temp_allocator)
    counted := make(map[Ask_Call_Key]bool, allocator = context.temp_allocator)
    stack := make([dynamic]int, context.temp_allocator)
    for r in roots { visited[r] = true; append(&stack, r) }
    more := 0
    for len(stack) > 0 {
        node := pop(&stack)
        key := ask_call_key(w.cg, node)
        if key not_in w.seen && key not_in counted {
            counted[key] = true
            more += 1
        }
        for k in w.adj[node] {
            if !visited[k] { visited[k] = true; append(&stack, k) }
        }
    }
    return more
}

// A fun's call tree: its callees (above, `forward`) or its callers (below), read off
// the call graph, which has every resolved direct call and construction; a generic's
// are every instance's. Indirect calls through fn-typed values aren't edges, so a fun
// reached only that way has no callers. It goes one level unless asked for more: all
// of one is often most of the program.
@(private="file")
render_fn_calls :: proc(b: ^strings.Builder, checked: ^Checked_Program, ft: ^Type_Scope, depth: int, forward: bool) {
    cg := &checked.call_graph
    roots := make([dynamic]int, context.temp_allocator)
    if nf, ok := cg.index_of[ft]; ok {
        key := ask_call_key(cg, nf)
        for _, i in cg.nodes {
            if ask_call_key(cg, i) == key { append(&roots, i) }
        }
    }
    render_calls_of(b, checked, roots[:], depth, forward)
}

// The call tree of the funs at some nodes of the call graph, as one.
@(private="file")
render_calls_of :: proc(b: ^strings.Builder, checked: ^Checked_Program, roots: []int, depth: int, forward: bool) {
    cg := &checked.call_graph
    hops := 1 if depth == ASK_DEPTH_OMITTED else depth
    sites := cg_sites(&checked.call_graph)
    w := Ask_Call_Walk{cg = cg, adj = cg.out_edges[:] if forward else cg.in_edges[:], forward = forward, sites = sites}
    direct := len(ask_call_funs(&w, roots))
    dir_word, row_word := "above", "direct callee"
    if !forward { dir_word, row_word = "below", "direct caller" }
    fmt.sbprintf(b, "\n%s (calls)   (%s, %s)\n", dir_word, ask_plural(direct, row_word), ask_depth_label(hops))
    if direct == 0 {
        if forward {
            fmt.sbprint(b, "  (calls nothing directly; indirect calls via fn-typed params aren't tracked)\n")
        } else {
            fmt.sbprint(b, "  (no direct callers; indirect calls via fn-typed params aren't tracked)\n")
        }
        return
    }
    for r in roots { w.seen[ask_call_key(cg, r)] = true }
    ask_walk_calls(&w, b, roots, 1, hops if hops >= 0 else (1 << 30))
    if more := ask_calls_unshown(&w, roots); more > 0 {
        fmt.sbprintf(b, "  (%d more: add a depth, or 'all')\n", more)
    }
}

// --- a dispatch group --------------------------------------------------------

// The dispatch groups called `name`, in source order, a body's too. The groups of one
// name are one to a call that sees them, so they're asked about as one.
@(private="file")
ask_find_dispatches :: proc(checked: ^Checked_Program, name, scope_file, scope_module: string) -> [dynamic]Token_Id {
    out: [dynamic]Token_Id
    for tok in checked.names.dispatches {
        t := build_tokens[tok]
        if token_text(t) != name { continue }
        f := build_files[t.file]
        if scope_module != "" && f.module != scope_module { continue }
        if scope_file != "" && filepath.base(f.path) != scope_file { continue }
        append(&out, tok)
    }
    slice.sort(out[:])
    return out
}

// What groups choose among: the declarations of their funs, a group among them by its
// own, each once.
@(private="file")
ask_dispatch_members :: proc(checked: ^Checked_Program, groups: []Token_Id) -> [dynamic]Token_Id {
    out: [dynamic]Token_Id
    visited := make(map[Token_Id]bool, allocator = context.temp_allocator)
    add :: proc(r: ^Name_Table, group: Token_Id, out: ^[dynamic]Token_Id, visited: ^map[Token_Id]bool) {
        if visited[group] { return }
        visited[group] = true
        def := r.defs[group] or_else 0
        if def == 0 { return }
        for tok in tree_token_list(&build_tree, build_tree.a[build_tree.b[def]]) {
            ref := r.token_refs[tok] or_else {}
            if ref.decl == 0 { continue }
            if r.dispatches[ref.decl] {
                add(r, ref.decl, out, visited)
            } else if !slice.contains(out[:], ref.decl) {
                append(out, ref.decl)
            }
        }
    }
    for g in groups { add(checked.names, g, &out, &visited) }
    return out
}

// A dispatch group asked about: what it chooses among (above), and every call of any
// of them, by the group's name or a member's (below), a member's own calls of another
// left out. It has no types or flow of its own: a call's are its member's.
@(private="file")
ask_dispatch_answer :: proc(checked: ^Checked_Program, groups: []Token_Id, name, kind, dir, pkg: string, depth: int) -> (out: string, ok: bool) {
    if kind != "" && kind != "call" {
        return fmt.tprintf("mara ask: '%s' is a dispatch group: %s is its members', so ask one of them. `mara ask %s` lists them.\n", name, kind, name), false
    }
    b := strings.builder_make()
    for g in groups {
        tok := build_tokens[g]
        fmt.sbprintf(&b, "%s — dispatch  %s   (module %s)\n", name, ask_loc(token_span(tok)), build_files[tok.file].module)
    }
    if kind == "" && dir == "" {
        for g in groups {
            doc := doc_comment_above(build_tokens[g])
            if doc == "" { continue }
            strings.write_byte(&b, '\n')
            for line in strings.split_lines(doc, context.temp_allocator) {
                if line == "" { strings.write_byte(&b, '\n') } else { fmt.sbprintf(&b, "  %s\n", line) }
            }
        }
    }
    members := ask_dispatch_members(checked, groups)
    defer delete(members)
    if dir != "below" {
        fmt.sbprintf(&b, "\nabove (calls)   (%s)\n", ask_plural(len(members), "member"))
        for m in members {
            tok := build_tokens[m]
            fmt.sbprintf(&b, "  %s  %s.%s\n", ask_loc(token_span(tok)), build_files[tok.file].module, token_text(tok))
            if signature := ask_signature(m); signature != "" { fmt.sbprintf(&b, "    %s\n", signature) }
        }
    }
    if dir != "above" {
        cg := &checked.call_graph
        roots := make([dynamic]int, context.temp_allocator)
        for s, i in cg.nodes {
            span := ask_span(s)
            for m in members {
                // (A foreign fun's span starts at its `fun`, not its name.)
                if span.tok == m || (ask_is_foreign(s) && span.tok <= m && m < span.end) {
                    append(&roots, i)
                    break
                }
            }
        }
        render_calls_of(&b, checked, roots[:], depth, forward = false)
    }
    return strings.to_string(b), true
}

// --- what a param's given ----------------------------------------------------

// How many of a param's calls `flow above` lists: a utility's would be most of the
// program, and `<fun> call below` has every one.
ASK_PARAM_CALLS_SHOWN :: 20

// What each call of a param's fun passes it: where the call's written, the fun it's
// in, what's written for it. The lines a call tree gives, cut to what the param gets.
ask_write_param_calls :: proc(bb: ^strings.Builder, checked: ^Checked_Program, b: ^Var_Binding) {
    cg := &checked.call_graph
    fn_name := ask_written_name(b.fn)
    Row :: struct { node: Tree_Id, caller: ^Type_Scope }
    rows := make([dynamic]Row, context.temp_allocator)
    if nf, known := cg.index_of[b.fn]; known {
        key := ask_call_key(cg, nf)
        sites := cg_sites(&checked.call_graph)
        for edge, nodes in sites {
            to, has := cg.index_of[edge.to]
            if !has || ask_call_key(cg, to) != key { continue }
            for n in nodes { append(&rows, Row{n, edge.from}) }
        }
    }
    slice.sort_by(rows[:], proc(x, y: Row) -> bool { return x.node < y.node })
    uniq := make([dynamic]Row, context.temp_allocator)
    for r in rows {
        if len(uniq) == 0 || uniq[len(uniq) - 1].node != r.node { append(&uniq, r) }
    }
    if len(uniq) == 0 {
        fmt.sbprintf(bb, "  %s   (a param: nothing calls %s directly)\n", b.name, fn_name)
        return
    }
    fmt.sbprintf(bb, "  %s   (a param: what %s of %s pass%s)\n", b.name, ask_plural(len(uniq), "call"), fn_name, "es" if len(uniq) == 1 else "")
    for r, i in uniq {
        if i == ASK_PARAM_CALLS_SHOWN {
            fmt.sbprintf(bb, "    (%d more: `mara ask %s call below` has every call)\n", len(uniq) - i, fn_name)
            break
        }
        tok := build_tokens[build_tree.first[r.node]]
        fmt.sbprintf(bb, "    %s  %s  %s\n", ask_loc(token_span(tok)), ask_written_name(r.caller), ask_call_arg_text(r.node, b.param_index, len(b.fn.params)))
    }
}

// What a call passes the param at `index` of `params`, as written: its default, if it
// passes none. A call by an operator, or that's a declaration, shows its line.
@(private="file")
ask_call_arg_text :: proc(n: Tree_Id, index, params: int) -> string {
    t := &build_tree
    args := make([dynamic]Tree_Id, context.temp_allocator)
    #partial switch t.tag[n] {
    case .Call:
        append(&args, ..tree_list(t, t.a[n]))
    case .Method_Call:
        view := method_view(t, n)
        append(&args, view.receiver)
        append(&args, ..view.args)
    case:
        return hit_source_line(build_tokens[t.first[n]])
    }
    // (More than it has params: the type params it was given first.)
    at := index + max(len(args) - params, 0)
    if at >= len(args) { return "(its default)" }
    return span_text(build_files[build_tokens[t.first[n]].file].source, tree_span(t, args[at]))
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
    rev := ask_type_users(checked.table, checked.functions)
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

// users: the reverse references, grouped by hop distance from the subject. Header
// separates distinct users from use-sites so neither count is misread. When the
// view reaches past one hop, rows are bucketed under "N hops" subheaders and each
// names the closer-to-root type it references (not the subject), so a chain like
// Megastruct -> Camera -> Object -> Vec3 reads outward ring by ring.
render_ask_users :: proc(b: ^strings.Builder, checked: ^Checked_Program, subject: Type, hops: int, say_funs: bool) {
    STRUCTURAL :: bit_set[Ask_Edge_Kind]{.Contains, .Embeds, .Base}
    result := ask_compute(checked.table, subject, "users", ask_type_reach(hops), checked.functions, users_kinds = STRUCTURAL)
    res := &result
    fmt.sbprintf(b, "\nbelow (types)   (%s, %s, %s)\n",
                 ask_plural(ask_distinct_sources(res), "user"), ask_plural(len(res.edges), "use-site"), ask_depth_label(hops))
    defer if say_funs {
        // (The funs in the count a module's view gives.)
        direct := ask_compute(checked.table, subject, "users", 0, checked.functions, users_kinds = STRUCTURAL)
        funs := ask_user_count(checked.table, subject, checked.functions) - ask_distinct_sources(&direct)
        if funs > 0 { fmt.sbprintf(b, "  (and %s taking or returning it: `mara ask %s call`)\n", ask_plural(funs, "fun"), ask_written_name(subject)) }
    }
    // (How much further it goes.)
    more := 0
    if hops >= 0 {
        whole := ask_compute(checked.table, subject, "users", -1, checked.functions, users_kinds = STRUCTURAL)
        more = ask_distinct_sources(&whole) - (ask_distinct_sources(res) if hops != 0 else 0)
    }
    defer if more > 0 { fmt.sbprintf(b, "  (%d more: add a depth, or 'all')\n", more) }
    if len(res.edges) == 0 { fmt.sbprint(b, "  (no users)\n"); return }
    if hops == 0 { return }

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
        // Bucket by where THIS reference sits, not the container's shortest path: a
        // struct that references a type N hops out is N+1 hops out THROUGH THIS edge.
        // So the same container appears in several rings — Megastruct references
        // Camera at 2 hops AND Glyph at 3 — instead of collapsing to its nearest one.
        hop := res.nodes[e.to].dist + 1
        if hop > max_hop { max_hop = hop }
        append(&rows, Row{ dist = hop, sub = u.sub, label = u.label, via = e.via,
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
    if span_file(span) == "" { return "?" }
    return fmt.tprintf("%s:%d", ask_short_path(span_file(span)), span_line(span))
}

// Where a query's run from (ask_run): what's outside it is written from there, where
// that's shorter than the whole path. What's written so still finds the file: `at`
// resolves it from here.
ask_here: string
@(private="file")
ask_here_room: [4096]u8

// Where queries are run from now on.
ask_run_from :: proc(dir: string) {
    ask_here = string(ask_here_room[:copy(ask_here_room[:], dir)])
}

@(private="file")
ask_short_path :: proc(path: string) -> string {
    if ask_here == "" || !filepath.is_abs(path) { return path }
    rel, err := filepath.rel(ask_here, path, context.temp_allocator)
    return rel if err == nil && len(rel) < len(path) else path
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
ask_is_stdlib :: proc(files: []^Source_File) -> bool {
    return len(files) > 0 && files[0].stdlib
}

// A type's distinct-user count — the reverse-edge in-degree, reusing the very
// graph `users` renders. The orientation signal for "which type matters here".
ask_user_count :: proc(table: ^SymbolTable, t: Type, funcs: map[string]^Type_Scope) -> int {
    res := ask_compute(table, t, "users", 0, funcs)   // DIRECT users only — the surface ranks by one-hop in-degree
    return ask_distinct_sources(&res)
}

// --- module surface: what one module declares ------------------------------

// `home_package` is the module name verbatim (`mara.math`, `camera`); the `mara.`
// prefix is an optional alias (the checker resolves `math` to `mara.math` too),
// so both spellings match here.
ask_module_name_matches :: proc(home, query: string) -> bool {
    if home == query { return true }
    return strings.has_prefix(home, "mara.") && home[len("mara."):] == query
}

// The shapes a module's declarations have — each fun's params, results and
// locals, each struct's fields (`mara ask <module> types`): how many of each
// are lists `[N]T`, arrays `[N!]T`, arrays by an enum `[K]T`, slices `[]T`,
// pointers `^T`, anything else; for the array shapes, the types most written.
// Generic instances aren't counted: the generic is, as written.
ASK_SHAPES :: [?]string{"[N]T", "[N!]T", "[K]T", "[]T", "^T", "other"}
ASK_SHAPE_NAMES :: [?]string{"list", "array", "by enum", "slice", "pointer", ""}
ASK_PLACES :: [?]string{"params", "results", "locals", "fields"}

ask_shape_of :: proc(t: Type) -> int {
    #partial switch v in distinct_base(t) {
    case ^Type_Partial_Array: return 0
    case ^Type_Fixed_Array:   return 2 if v.index_type != nil else 1
    case ^Type_Slice:         return 3
    case ^Type_Ptr:           return 4
    }
    return 5
}

ask_module_shapes :: proc(checked: ^Checked_Program, module: string) -> string {
    names := ASK_SHAPE_NAMES
    counts: [len(ASK_SHAPES)][len(ASK_PLACES)]int
    written: [len(ASK_SHAPES)]map[string]int
    for &w in written { w.allocator = context.temp_allocator }
    add :: proc(counts: ^[len(ASK_SHAPES)][len(ASK_PLACES)]int, written: ^[len(ASK_SHAPES)]map[string]int, t: Type, place: int) {
        if t == nil { return }
        s := ask_shape_of(t)
        counts[s][place] += 1
        if s <= 2 { written[s][type_name(t)] += 1 }
    }
    owned :: proc(ts: ^Type_Scope, module: string) -> bool {
        if ts == nil || !ask_module_name_matches(ts.home_package, module) { return false }
        return ts.source_name != "" || ask_is_foreign(ts)   // (an instance has none: its generic counts)
    }
    for _, ts in checked.functions {
        if !owned(ts, module) { continue }
        for p in ts.params { add(&counts, &written, p.type_, 0) }
        for r in ts.return_types { add(&counts, &written, r, 1) }
        if checked.annot == nil { continue }
        for v in checked.annot.vars[ts] or_else nil {
            if v.kind == .Local { add(&counts, &written, v.type_, 2) }
        }
    }
    for m in ask_all_definitions(checked.table, "", checked.functions, every = true) {
        ts, is_scope := m.type_.(^Type_Scope)
        if !is_scope || ts.kind != .Struct || !owned(ts, module) || ask_is_variant(m.type_) { continue }
        for f in ts.fields { add(&counts, &written, f.type_, 3) }
        for p in ts.params { add(&counts, &written, p.type_, 0) }
    }
    b := strings.builder_make()
    fmt.sbprint(&b, "\n  shapes       (its funs' params, results, locals; its structs' fields)\n")
    fmt.sbprintf(&b, "    %-17s", "")
    for p in ASK_PLACES { fmt.sbprintf(&b, "%8s", p) }
    fmt.sbprintf(&b, "%8s\n", "all")
    for shape, s in ASK_SHAPES {
        total := 0
        for n in counts[s] { total += n }
        fmt.sbprintf(&b, "    %-8s %-8s", shape, names[s])
        for n in counts[s] { fmt.sbprintf(&b, "%8s", fmt.tprint(n)) }
        fmt.sbprintf(&b, "%8s", fmt.tprint(total))
        if s <= 2 && len(written[s]) > 0 {
            Written :: struct { name: string, n: int }
            ws: [dynamic]Written
            ws.allocator = context.temp_allocator
            for name, n in written[s] { append(&ws, Written{name, n}) }
            slice.sort_by(ws[:], proc(a, c: Written) -> bool { return a.n > c.n if a.n != c.n else a.name < c.name })
            fmt.sbprint(&b, "   ")
            for w, i in ws {
                if i == 5 { fmt.sbprintf(&b, "  · %d more", len(ws) - 5); break }
                fmt.sbprintf(&b, "%s %s ×%d", "" if i == 0 else "  ·", w.name, w.n)
            }
        }
        fmt.sbprint(&b, "\n")
    }
    return strings.to_string(b)
}

// `mara ask <Module>` — the module's own types (ranked by how many things use
// them) and funs (source order); `types`, the shapes its declarations have too
// (ask_module_shapes). Returns ok=false when `target` names no loaded module,
// so the caller falls through to variant / fuzzy handling.
ask_module_surface :: proc(checked: ^Checked_Program, target: string, kind := "") -> (out: string, ok: bool) {
    Entry :: struct { m: Ask_Match, users: int }
    types: [dynamic]Entry
    funs:  [dynamic]Ask_Match
    canonical := target
    for m in ask_all_definitions(checked.table, "", checked.functions) {
        hp := ask_home_package(m.type_)
        if m.mark == "synthetic" || ask_source_name(m.type_) == "" { continue }   // skip instances/synthetic
        if ask_is_foreign(m.type_) { continue }   // (a foreign block's funs are its file's: the module's are the Mara funs that call them)
        if ask_is_variant(m.type_) { continue }   // (a union's variant: its union's)
        if !ask_module_name_matches(hp, target) { continue }
        canonical = hp
        if m.sub == "fun" { append(&funs, m) }
        else              { append(&types, Entry{ m = m, users = ask_user_count(checked.table, m.type_, checked.functions) }) }
    }
    if len(types) == 0 && len(funs) == 0 { return "", false }   // not a (loaded) module

    // Its constants: what its body-level definitions are that aren't funs or types.
    consts := make([dynamic]Token_Id, context.temp_allocator)
    for d in names_defs(checked.names, 0, canonical) {
        if build_tree.tag[d.node] == .Define && names_def_kind(&build_tree, Tree_Id(build_tree.b[d.node])) == .Const { append(&consts, build_tree.main[d.node]) }
    }
    slice.sort(consts[:])

    slice.sort_by(types[:], proc(a, b: Entry) -> bool {
        if a.users != b.users { return a.users > b.users }      // most-used first
        return a.m.label < b.m.label
    })
    slice.sort_by(funs[:], proc(a, b: Ask_Match) -> bool { return span_before(a.span, b.span) })

    b := strings.builder_make()
    fmt.sbprintf(&b, "%s — module   (%s, %s)\n", canonical, ask_plural(len(types), "type"), ask_plural(len(funs), "fun"))
    // (A doc comment's first line is what most say first.)
    doc_line :: proc(b: ^strings.Builder, first: Token_Id) {
        if first == 0 { return }
        doc := doc_comment_above(build_tokens[first])
        if doc == "" { return }
        if nl := strings.index_byte(doc, '\n'); nl >= 0 { doc = doc[:nl] }
        fmt.sbprintf(b, "      %s\n", doc)
    }
    if len(types) > 0 {
        fmt.sbprint(&b, "\n  types        (most-used first)\n")
        for e in types {
            tail := fmt.tprintf("   ·  %s", ask_plural(e.users, "user")) if e.users > 0 else ""
            fmt.sbprintf(&b, "    %-8s %s  %s%s%s\n", e.m.sub, e.m.label, ask_loc(e.m.span), ask_mark_suffix(e.m.mark), tail)
            doc_line(&b, e.m.span.tok)
        }
    }
    if len(consts) > 0 {
        fmt.sbprint(&b, "\n  constants    (source order)\n")
        for tok in consts {
            fmt.sbprintf(&b, "    %s  %s\n", ask_loc(token_span(build_tokens[tok])), hit_source_line(build_tokens[tok]))
        }
    }
    if len(funs) > 0 {
        fmt.sbprint(&b, "\n  funs         (source order)\n")
        for m in funs {
            fmt.sbprintf(&b, "    %s  %s\n", ask_loc(m.span), ask_signature(m.span.tok))
            doc_line(&b, m.span.tok)
        }
    }
    if kind == "types" { fmt.sbprint(&b, ask_module_shapes(checked, canonical)) }
    return strings.to_string(b), true
}

// --- no analyzable module in the cwd ---------------------------------------

// `mara ask` runs against the module in the current directory (module_at:
// the one its files declare; of several, the folder's name). When that names no
// discovered module, the generic
// build error ("no files found for module X") buries the real problem and never
// mentions the user's query. This renders ask-shaped guidance instead: name the
// miss, show the modules that ARE analyzable (local first, then stdlib — exactly
// the valid `in <module>` arguments), and teach the two ways forward — cd into a
// module's directory, or pin one inline with `in <module>`. The local/stdlib
// split classifies each module by a representative file, like the module map.
ask_no_module_here :: proc(all_files: map[string][dynamic]^Source_File, cwd_name, target, query: string) -> string {
    locals: [dynamic]string
    libs:   [dynamic]string
    for name, files in all_files {
        if len(files) == 0 { continue }
        if ask_is_stdlib(files[:]) { append(&libs, name) }
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
ask_module_map :: proc(checked: ^Checked_Program, all_files: map[string][dynamic]^Source_File, root_pkg: string) -> string {
    // One pass over the deduped definitions -> per-module (flat) counts. Tables hold
    // every CHECKED module — local AND the stdlib modules actually pulled in — so this
    // is the authoritative module set.
    Counts :: struct { types, funs: int }
    by_home: map[string]Counts
    for m in ask_all_definitions(checked.table, "", checked.functions) {
        if m.mark == "synthetic" || ask_source_name(m.type_) == "" { continue }   // skip instances/synthetic
        if ask_is_foreign(m.type_) { continue }   // (a foreign block's funs are its file's: the module's are the Mara funs that call them)
        if ask_is_variant(m.type_) { continue }   // (a union's variant: its union's)
        hp := ask_home_package(m.type_)
        if hp == "" { continue }
        c := by_home[hp]
        if m.sub == "fun" { c.funs += 1 } else { c.types += 1 }
        by_home[hp] = c
    }

    // `home_package` IS the module name (`mara.math`, `camera`) — the same key
    // `all_files` uses. A home that names no discovered module is an
    // internal/synthetic package (skip it).
    infos: [dynamic]Ask_Module_Info
    for hp, c in by_home {
        files, discovered := all_files[hp]
        if !discovered { continue }
        has_main, _ := module_entries(hp)
        append(&infos, Ask_Module_Info{
            name = hp, types = c.types, funs = c.funs,
            has_main = has_main,
            stdlib   = ask_is_stdlib(files[:]),
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
