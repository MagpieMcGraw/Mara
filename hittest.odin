package mara

import "core:fmt"
import "core:slice"
import "core:strconv"
import "core:strings"
import "core:path/filepath"

// ---------------------------------------------------------------------------
// Position → syntax node. The lookup behind `mara ask at <file>:<line>:<col>`,
// and the addressing primitive the other queries should eventually hang off:
// a name is ambiguous (a module, a struct and three locals can share one), but
// a point in the source names exactly one node.
//
// Resolve the cursor to a token index (binary search, since the token array is
// ordered by position), then take each node of the flat tree whose token
// extent [first, end) holds it — the tree is a table, so one pass, no walk —
// widest first: containment is nested, so the list reads outermost → innermost.
//
// Not listed: a type as written, and a list's part (a param group, a literal's
// named entry) — the cursor names the statement, definition or expression
// around them.
//
// An expression's type is its annotation, in each instance it is checked in
// (hit_type). What the checker types nothing — a module's name — shows none.
// The innermost name holding the point says what it refers to (hit_refers):
// its declaration's kind, name and file:line — `mara docs` shows that one
// first. `mara ask what at <point>` says the same to read (ask_what_at_point):
// a variable or a field's types along its path, where it's declared, and where
// it's written and read; of anything else that's named, what it is, its type
// and where it's declared; of what isn't, the expressions around it. A hover
// asks for what it is alone.
// ---------------------------------------------------------------------------

// Whether a node is one a cursor names.
@(private="file")
hit_listed :: proc(tag: Tree_Tag) -> bool {
    #partial switch tag {
    case .File, .Param_Group, .Generic_Param, .Union_Tag, .Union_Pad, .Union_Size:
        return false
    }
    return tag < .Type_Name || tag > .Type_Paren
}

// --- cursor → token ---------------------------------------------------------

// Index of the token at or immediately before (line, col). The array is ordered
// by position, so this is a binary search for the last token that starts at or
// before the cursor. Columns are BYTE offsets into the line — see lexer_advance;
// a caller working in characters has to convert before calling.
token_index_at :: proc(tokens: []Token, line, col: int) -> (int, bool) {
    if len(tokens) == 0 { return 0, false }
    before :: proc(t: Token, line, col: int) -> bool {
        return token_line(t) < line || (token_line(t) == line && token_col(t) <= col)
    }
    lo, hi, best := 0, len(tokens) - 1, -1
    for lo <= hi {
        mid := (lo + hi) / 2
        if before(tokens[mid], line, col) { best = mid; lo = mid + 1 } else { hi = mid - 1 }
    }
    if best < 0 { return 0, false }
    // Landing on an earlier line means the cursor sits before the first token of
    // its own line (leading indentation). Prefer that line's first token.
    if token_line(tokens[best]) != line && best + 1 < len(tokens) && token_line(tokens[best + 1]) == line {
        return best + 1, true
    }
    return best, true
}

// --- entry ------------------------------------------------------------------

// The source text a span covers, trimmed to one line for display.
@(private="file")
span_text :: proc(src: string, s: Span) -> string {
    if s.end <= s.tok { return "" }
    first, last := build_tokens[s.tok], build_tokens[s.end - 1]
    lo, hi := int(first.offset), int(last.offset + last.len)   // (a literal as written)
    if multiline := strings.contains_rune(src[lo:hi], '\n'); multiline {
        // Clip to the first line and mark the truncation.
        end := lo
        for end < len(src) && src[end] != '\n' { end += 1 }
        return strings.concatenate({strings.trim_space(src[lo:end]), " …"})
    }
    return strings.trim_space(src[lo:hi])
}

// The type the annotations give what is written at a node: in each instance
// it is checked in — outside any generic, the one; in a generic's template,
// each instance's, as they differ.
@(private="file")
hit_type :: proc(a: ^Annotations, n: Tree_Id) -> string {
    labels := make([dynamic]string, context.temp_allocator)
    for inst, i in a.instances {
        if n < inst.lo || n > inst.hi { continue }
        label := hit_label(annot_type(a, Instance_Id(i), n))
        if label != "" && !slice.contains(labels[:], label) { append(&labels, label) }
    }
    return strings.join(labels[:], ", ", context.temp_allocator)
}

// A type as `ask at` shows it: an untyped number as one (a `:=` binding's,
// the width it settled at); what has no value — a void call, `print`'s —
// none.
@(private="file")
hit_label :: proc(t: Type) -> string {
    if t == nil { return "" }
    if infer_cell_of(t) != nil { return type_name(solidify_type(t)) }
    #partial switch _ in t {
    case Type_Error, Type_Void: return ""
    case Type_Infer_Int:        return "untyped int"
    case Type_Infer_Float:      return "untyped float"
    }
    return type_name(t)
}


// What the name at a point — its token `at`, its text `name` — refers to,
// as the innermost of the nodes holding it (widest first) says: "refers to:
// <kind> <name>  <file>:<line>", its declaration's; a builtin's, which no
// source declares, without the place. Only a reference about that name: a
// node around it (a call, around a string in its arguments) refers to
// something else. "" when nothing there refers to anything.
@(private="file")
hit_refers :: proc(t: ^Tree, a: ^Annotations, hits: []Tree_Id, at: int, name: string) -> string {
    r, _, found := hit_ref(t, a, hits, at, name)
    if !found { return "" }
    if r.decl == 0 { return fmt.tprintf("refers to: %s %s\n", ref_kind_word(r.kind), name) }
    tok := build_tokens[r.decl]
    return fmt.tprintf("refers to: %s %s  %s\n", ref_kind_word(r.kind), token_text(tok), ask_loc(token_span(tok)))
}

// hit_refers's reference: the innermost about the point's name, and the node
// that makes it; found false for none.
@(private="file")
hit_ref :: proc(t: ^Tree, a: ^Annotations, hits: []Tree_Id, at: int, name: string) -> (Ref, Tree_Id, bool) {
    #reverse for n in hits {
        for inst, i in a.instances {
            if n < inst.lo || n > inst.hi || int(n - inst.lo) >= len(a.refs[i]) { continue }
            r := annot_ref(a, Instance_Id(i), n)
            if r.kind == .None { continue }
            if r.decl == 0 {
                // (A builtin: only a node its name begins — the name, a call of it.)
                if int(t.first[n]) != at { continue }
                return r, n, true
            }
            if token_text(build_tokens[r.decl]) != name { continue }
            return r, n, true
        }
    }
    // (A definition's own name refers to nothing — it's what's declared
    // there: itself, then. A param's, the same.)
    for n in hits {
        if t.tag[n] == .Define && int(t.first[n]) == at { return Ref{decl = Token_Id(at), kind = hit_define_kind(t, n)}, n, true }
    }
    if g := hit_param_group(t, at); g != 0 { return Ref{decl = Token_Id(at), kind = .Param}, g, true }
    return {}, 0, false
}

// The param group that declares a name, its token `at`; 0 for none.
@(private="file")
hit_param_group :: proc(t: ^Tree, at: int) -> Tree_Id {
    for i in 1 ..< len(t.tag) {
        if t.tag[i] != .Param_Group || int(t.first[i]) > at || at >= int(t.end[i]) { continue }
        for name in tree_token_list(t, t.a[i]) {
            if int(name) == at { return Tree_Id(i) }
        }
    }
    return 0
}

// What a definition defines, as a reference's kind: a fun, a type (a
// struct, a union, an enum, an error set), else a constant.
@(private="file")
hit_define_kind :: proc(t: ^Tree, n: Tree_Id) -> Ref_Kind {
    first, last := build_tokens[t.first[n]], build_tokens[t.end[n] - 1]
    text := build_files[first.file].source[first.offset:last.offset + last.len]
    colons := strings.index(text, "::")
    if colons < 0 { return .Const }
    what := strings.trim_left_space(text[colons + 2:])
    switch {
    case strings.has_prefix(what, "fun"): return .Fun
    case strings.has_prefix(what, "struct"), strings.has_prefix(what, "class"), strings.has_prefix(what, "union"),
         strings.has_prefix(what, "enum"), strings.has_prefix(what, "error"):
        return .Type
    }
    return .Const
}

// A reference's kind as `ask at` says it.
ref_kind_word :: proc(k: Ref_Kind) -> string {
    switch k {
    case .None:    return "nothing"
    case .Local:   return "local"
    case .Param:   return "param"
    case .Result:  return "result"
    case .Field:   return "field"
    case .Global:  return "global"
    case .Const:   return "const"
    case .Variant: return "variant"
    case .Fun:     return "fun"
    case .Type:    return "type"
    case .Module:  return "module"
    case .Builtin: return "builtin"
    }
    return "?"
}

// A point in a file, found: its file, its token (`at`, in the build's
// tokens; tok_i, in the file's), and the nodes holding it, widest first.
Hit_Point :: struct {
    src:    ^Source_File,
    want:   string,    // the file's name
    line:   int,
    col:    int,
    base:   int,       // the file's first token
    tokens: []Token,   // the file's
    tok_i:  int,
    at:     int,
    hits:   [dynamic]Tree_Id,
}

// `<file>:<line>:<col>` found: the point; else what to say instead, and
// false.
@(private="file")
hit_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File, spec: string) -> (p: Hit_Point, msg: string, ok: bool) {
    parts := strings.split(spec, ":")
    defer delete(parts)
    if len(parts) != 3 {
        return p, fmt.tprintf("mara ask: `at %s` — expected <file>:<line>:<col>\n", spec), false
    }
    line, line_ok := strconv.parse_int(parts[1])
    col,  col_ok  := strconv.parse_int(parts[2])
    if !line_ok || !col_ok || line < 1 || col < 1 {
        return p, fmt.tprintf("mara ask: `at %s` — line and column must be positive integers\n", spec), false
    }

    // (A file's name alone can be several files, in the stdlib or ours: the
    // one at that path from here if there is one, else one in this build.)
    want := filepath.base(parts[0])
    named := path_key(parts[0])
    src_file: ^Source_File
    search: for _, files in all_files {
        for f in files {
            if filepath.base(f.path) != want { continue }
            if path_key(f.path) == named {
                src_file = f
                break search
            }
            if src_file == nil || (src_file.end_token <= src_file.first_token && f.end_token > f.first_token) { src_file = f }
        }
    }
    if src_file == nil {
        return p, fmt.tprintf("mara ask: no source file named '%s'\n", parts[0]), false
    }
    if src_file.end_token <= src_file.first_token {
        return p, fmt.tprintf("mara ask: '%s' has no tokens (not part of this build?)\n", want), false
    }

    // (Token positions print from the file's first.)
    base := int(src_file.first_token)
    tokens := build_tokens[src_file.first_token:src_file.end_token]
    tok_i, found := token_index_at(tokens, line, col)
    if !found {
        return p, fmt.tprintf("mara ask: nothing at %s:%d:%d\n", want, line, col), false
    }

    // (The file's nodes holding the cursor; the widest first — an equal one,
    // the parent: made after its children.)
    at := base + tok_i
    hits := make([dynamic]Tree_Id, context.temp_allocator)
    for i in 1 ..< len(t.tag) {
        n := Tree_Id(i)
        first, end := int(t.first[n]), int(t.end[n])
        if first < base || first >= int(src_file.end_token) || !hit_listed(t.tag[n]) { continue }
        if first <= at && at < end { append(&hits, n) }
    }
    if len(hits) == 0 {
        return p, fmt.tprintf("%s:%d:%d — token '%s', but no node covers it\n",
                              want, line, col, token_text(tokens[tok_i])), false
    }
    width :: proc(t: ^Tree, n: Tree_Id) -> int { return int(t.end[n] - t.first[n]) }
    for a in 1 ..< len(hits) {
        h := hits[a]
        b := a - 1
        for b >= 0 && (width(t, hits[b]) < width(t, h) || width(t, hits[b]) == width(t, h) && hits[b] < h) {
            hits[b + 1] = hits[b]; b -= 1
        }
        hits[b + 1] = h
    }
    return Hit_Point{src_file, want, line, col, base, tokens, tok_i, at, hits}, "", true
}

// The reference the name at `<file>:<line>:<col>` makes (mara lsp): its
// declaration's token — 0 for a builtin — and kind, and the name there; ok
// false when nothing there refers to anything.
point_reference :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File, a: ^Annotations, spec: string) -> (r: Ref, name: string, ok: bool) {
    p, _, found := hit_point(t, all_files, spec)
    if !found { return }
    name = token_text(p.tokens[p.tok_i])
    r, _, ok = hit_ref(t, a, p.hits[:], p.at, name)
    return
}

// The nodes holding a point, widest first, and its token (mara lsp's
// completion); ok false when nothing's there.
point_hits :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File, spec: string) -> (hits: []Tree_Id, at: Token_Id, ok: bool) {
    p, _, found := hit_point(t, all_files, spec)
    if !found { return }
    return p.hits[:], Token_Id(p.at), true
}

// The token that is a name among the tokens of the node that refers by it: a
// field's is its last; false for neither.
@(private="file")
ref_name_token :: proc(t: ^Tree, n: Tree_Id, name: string) -> (Token_Id, bool) {
    if token_text(build_tokens[t.end[n] - 1]) == name { return t.end[n] - 1, true }
    if token_text(build_tokens[t.first[n]]) == name { return t.first[n], true }
    return 0, false
}

// Every reference in the program, by the declaration it names (its name's
// token): each the name's token where it's written, once — mara lsp keeps
// them to tell a declaration renamed from its uses (lsp.odin's names).
references_by_declaration :: proc(t: ^Tree, a: ^Annotations) -> map[Token_Id][dynamic]Token_Id {
    out := make(map[Token_Id][dynamic]Token_Id)
    seen := make(map[Token_Id]bool)
    for inst, i in a.instances {
        for r, k in a.refs[i] {
            if r.decl == 0 { continue }
            n := inst.lo + Tree_Id(k)
            tok, named := ref_name_token(t, n, token_text(build_tokens[r.decl]))
            if !named || tok == r.decl || seen[tok] { continue }
            seen[tok] = true
            uses := out[r.decl]
            append(&uses, tok)
            out[r.decl] = uses
        }
    }
    return out
}

// Every name that refers to the declaration whose name is the token `decl`,
// as its token: the declaration's own first, each once.
references_to :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id) -> []Token_Id {
    name := token_text(build_tokens[decl])
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)
    out := make([dynamic]Token_Id, context.temp_allocator)
    seen[decl] = true
    append(&out, decl)
    for inst, i in a.instances {
        for r, k in a.refs[i] {
            if r.decl != decl { continue }
            tok, named := ref_name_token(t, inst.lo + Tree_Id(k), name)
            if !named { continue }
            if !seen[tok] {
                seen[tok] = true
                append(&out, tok)
            }
        }
    }
    return out[:]
}

// Resolve `<file>:<line>:<col>` to the chain of nodes holding it, each with
// its type and what it was lowered to. Returns rendered text and whether
// anything was found.
ask_at_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File,
                     a: ^Annotations, pc: ^Program_Code, spec: string) -> (string, bool) {
    p, msg, ok := hit_point(t, all_files, spec)
    if !ok { return msg, false }
    want, line, col, base, tokens, tok_i, at, hits, src_file := p.want, p.line, p.col, p.base, p.tokens, p.tok_i, p.at, p.hits, p.src

    sb := strings.builder_make()
    fmt.sbprintf(&sb, "%s:%d:%d  token '%s'\n", want, line, col, token_text(tokens[tok_i]))
    fmt.sbprint(&sb, hit_refers(t, a, hits[:], at, token_text(tokens[tok_i])))
    fmt.sbprint(&sb, "\n")
    prev: Span
    for n in hits {
        if t.tag[n] == .Named_Entry { continue }   // (the literal's part: the literal said)
        span := tree_span(t, n)
        if span.tok == prev.tok && span.end == prev.end { continue }   // (a node and the one it wraps)
        prev = span
        ty := ""
        if t.tag[n] >= .Number {
            ty = hit_type(a, n)
            // (A `?` typed no value of its own: its call's.)
            if ty == "" && t.tag[n] == .Try { ty = hit_type(a, Tree_Id(t.a[n])) }
        }
        fmt.sbprintf(&sb, "  %-24s [%d,%d)  %s", fmt.tprint(t.tag[n]), int(span.tok) - base, int(span.end) - base,
                     span_text(src_file.source, span))
        if ty != "" { fmt.sbprintf(&sb, "   : %s", ty) }
        fmt.sbprint(&sb, "\n")
        if ops := hit_ops(pc, a, n); ops != "" { fmt.sbprintf(&sb, "      → %s\n", ops) }
    }
    return strings.to_string(sb), true
}

// What a node was lowered to (Annotations.ops): its nodes in the lowered
// program, in order — an operation's kind, else the node's (a local, a
// scope), and its name; the same one again, counted. The same in each
// instance once; else each instance's, apart.
@(private="file")
hit_ops :: proc(pc: ^Program_Code, a: ^Annotations, n: Tree_Id) -> string {
    lists := make([dynamic]string, context.temp_allocator)
    for inst, i in a.ops {
        if n < a.instances[i].lo || n > a.instances[i].hi || inst[n - a.instances[i].lo].code == 0 { continue }
        g, id := graph_ops(pc, a, annot_key(Instance_Id(i), n))
        parts := make([dynamic]string, context.temp_allocator)
        last, times := "", 0
        for ; id != NO_NODE; id = graph_ops_next(g, id) {
            what := fmt.tprint(g.op[id]) if g.kind[id] == .Op else fmt.tprint(g.kind[id])
            if name := graph_name(g, id); name != "" { what = fmt.tprintf("%s %s", what, name) }
            if what == last {
                times += 1
                parts[len(parts) - 1] = fmt.tprintf("%s ×%d", what, times)
                continue
            }
            append(&parts, what)
            last, times = what, 1
        }
        list := strings.join(parts[:], ", ", context.temp_allocator)
        if !slice.contains(lists[:], list) { append(&lists, list) }
    }
    return strings.join(lists[:], " | ", context.temp_allocator)
}

// `mara ask what at <file>:<line>:<col>`: what is at the point, to read. With
// `uses`, a variable's or a field's types along its path, where it's declared,
// and where it's written and read (hit_uses_answer). Else the name there, what
// it is and its type, and where it's declared; what's no name, the expressions
// around it, innermost first, to its statement, each with its type. (`ask at`
// lists every node, for the tree's sake.)
ask_what_at_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File,
                          a: ^Annotations, spec: string, uses := false) -> (string, bool) {
    p, msg, ok := hit_point(t, all_files, spec)
    if !ok { return msg, false }
    hits := p.hits[:]
    name := token_text(p.tokens[p.tok_i])
    inner := hits[len(hits) - 1]
    r, named_at, refers := hit_ref(t, a, hits, p.at, name)
    if uses && refers && r.decl != 0 {
        #partial switch r.kind {
        case .Local, .Param, .Result, .Field, .Global:
            return hit_uses_answer(t, a, &p, r, named_at), true
        }
    }
    // (The point's own node: the innermost, when it ends at the point — a
    // name, a field's name. Its type, the name's.)
    own := int(t.end[inner]) - 1 == p.at && t.tag[inner] >= .Number
    own_type := hit_type(a, inner) if own else ""

    sb := strings.builder_make()
    // (As written: a string with its quotes.)
    written := span_text(p.src.source, token_span(p.tokens[p.tok_i]))
    fmt.sbprint(&sb, written)
    if refers { fmt.sbprintf(&sb, " — %s", ref_kind_word(r.kind)) }
    if own_type != "" { fmt.sbprintf(&sb, " : %s", own_type) }
    fmt.sbprint(&sb, "\n")
    if refers {
        if r.decl == 0 {
            fmt.sbprint(&sb, "  built into the compiler\n")
        } else {
            fmt.sbprintf(&sb, "  declared  %s\n", ask_loc(token_span(build_tokens[r.decl])))
            // (A definition's first line: a fun's signature, a struct's params.)
            if def := hit_definition_at(t, r.decl); def != 0 {
                first := span_text(source_of(build_tokens[r.decl]), tree_span(t, def))
                first = strings.trim_suffix(strings.trim_suffix(first, " …"), " {")
                fmt.sbprintf(&sb, "  %s\n", first)
            }
        }
        return strings.to_string(sb), true
    }

    // The expressions around it, innermost first: each one line, to the
    // first spanning lines (a body, a block).
    fmt.sbprint(&sb, "\n")
    prev: Span
    shown := 0
    #reverse for n in hits {
        span := tree_span(t, n)
        if span.tok == prev.tok && span.end == prev.end { continue }   // (a node and the one it wraps)
        prev = span
        text := span_text(p.src.source, span)
        // (A node over lines shows its first, "…" after: a body, a block.)
        if strings.contains(text, "\n") || strings.has_suffix(text, "…") || t.tag[n] == .Define || t.tag[n] == .Fun_Def { break }
        if text == written { continue }   // (the name: said above)
        ty := hit_type(a, n) if t.tag[n] >= .Number else ""
        if len(text) > 100 {
            // (At a character's start: a cut mid-character isn't text.)
            cut := 100
            for cut > 0 && text[cut] & 0xC0 == 0x80 { cut -= 1 }
            text = strings.concatenate({text[:cut], "…"}, context.temp_allocator)
        }
        fmt.sbprintf(&sb, "  %s", text)
        if ty != "" { fmt.sbprintf(&sb, "   : %s", ty) }
        fmt.sbprint(&sb, "\n")
        shown += 1
        if shown == 8 { break }
    }
    return strings.to_string(sb), true
}

// What a use of a name does to what it names. A pointer taken may be either:
// what's done with it is elsewhere.
Use_Kind :: enum { Written, Pointer, Read }

// A place a name is used, or a field is written without being named: the token
// it's at, its node, and what it does there.
Hit_Use :: struct {
    tok:  Token_Id,
    node: Tree_Id,
    kind: Use_Kind,
    path: string,   // its file's
    here: bool,     // in the file the question's about
}

// A use added: `here` the file the question's about.
@(private="file")
hit_add_use :: proc(uses: ^[dynamic]Hit_Use, tok: Token_Id, n: Tree_Id, kind: Use_Kind, here: u16) {
    token := build_tokens[tok]
    append(uses, Hit_Use{tok, n, kind, span_file(token_span(token)), token.file == here})
}

// What the name at node n does to what it names: climbs from it while it's
// part of what an assignment's target, or a `&`, is about. `x.f.g = v` writes
// part of x.f. Through a pointer it doesn't (`p.g = v`: p is only read, what it
// points at is written), nor through a slice to its items; a slice's own `len`
// is the slice's.
@(private="file")
hit_use_kind :: proc(t: ^Tree, a: ^Annotations, i: Instance_Id, n: Tree_Id) -> Use_Kind {
    if t.tag[n] == .Named_Entry { return .Written }   // (`Foo{x = v}`)
    in_list :: proc(t: ^Tree, list: u32, n: Tree_Id) -> bool {
        for c in tree_list(t, list) {
            if c == n { return true }
        }
        return false
    }
    cur := n
    for {
        p := t.parent[cur]
        if p == 0 { return .Read }
        #partial switch t.tag[p] {
        case .Paren:
        case .Field, .Index, .Slice:
            if Tree_Id(t.a[p]) != cur { return .Read }
            #partial switch _ in distinct_base(annot_type(a, i, cur)) {
            case ^Type_Ptr:   return .Read
            case ^Type_Slice: if t.tag[p] != .Field { return .Read }
            }
        case .Assign, .Decl:
            return .Written if in_list(t, t.a[p], cur) else .Read
        case .Compound:
            return .Written if Tree_Id(t.a[p]) == cur else .Read
        case .Unary:
            if token_text(build_tokens[t.main[p]]) != "&" { return .Read }
            // (`&x + v` adds to x.)
            up := t.parent[p]
            if t.tag[up] == .Binary && Tree_Id(t.a[up]) == p && token_text(build_tokens[t.main[up]]) == "+" { return .Written }
            return .Pointer
        case:
            return .Read
        }
        cur = p
    }
}

// Whether a value of a type holds the field declared at `decl`, itself or in a
// struct or array it holds. (Each struct's answer kept.)
@(private="file")
hit_holds_field :: proc(ty: Type, decl: Token_Id, known: ^map[^Type_Scope]bool) -> bool {
    base := distinct_base(ty)
    #partial switch v in base {
    case ^Type_Fixed_Array:   return hit_holds_field(v.elem, decl, known)
    case ^Type_Partial_Array: return hit_holds_field(v.elem, decl, known)
    }
    ts, is_scope := base.(^Type_Scope)
    if !is_scope || ts.kind != .Struct { return false }
    if held, was := known[ts]; was { return held }
    known[ts] = false
    for f in ts.fields {
        if f.decl == decl || hit_holds_field(f.type_, decl, known) {
            known[ts] = true
            return true
        }
    }
    return false
}

// Where the field declared at `decl` is written without being named: a value
// that holds it assigned whole, a literal's entry by position.
@(private="file")
hit_field_writes :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id, uses: ^[dynamic]Hit_Use, here: u16) {
    known := make(map[^Type_Scope]bool, allocator = context.temp_allocator)
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            #partial switch t.tag[n] {
            case .Assign:
                for target in tree_list(t, t.a[n]) {
                    if hit_holds_field(annot_type(a, Instance_Id(i), target), decl, &known) {
                        hit_add_use(uses, t.first[target], target, .Written, here)
                    }
                }
            case .Literal:
                ts, is_scope := distinct_base(annot_type(a, Instance_Id(i), n)).(^Type_Scope)
                if !is_scope { continue }
                entries := tree_list(t, t.b[n])
                if len(entries) == 0 || t.tag[entries[0]] == .Named_Entry || t.tag[entries[0]] == .Broadcast { continue }
                user := ts.fields[first_user_field(&ts.sd):]
                if len(entries) == 1 && len(user) > 1 {
                    // (`Token{0}`: its zero. `Foo{f()}`: every field f's.)
                    if t.tag[entries[0]] != .Call && t.tag[entries[0]] != .Method_Call { continue }
                    for f in user {
                        if f.decl == decl { hit_add_use(uses, t.first[n], n, .Written, here) }
                    }
                    continue
                }
                for e, at in entries {
                    if at < len(user) && user[at].decl == decl { hit_add_use(uses, t.first[e], e, .Written, here) }
                }
            }
        }
    }
}

// The name of the definition holding a node, the innermost: the fun a use is
// in, the struct a field is; "" for none.
@(private="file")
hit_holder_name :: proc(t: ^Tree, n: Tree_Id) -> string {
    for c := n; c != 0; c = t.parent[c] {
        if t.tag[c] == .Define && c != n { return token_text(build_tokens[t.main[c]]) }
    }
    return ""
}

// The innermost node holding a token. (Children come before their parents, so
// the first found.)
@(private="file")
hit_node_at :: proc(t: ^Tree, tok: Token_Id) -> Tree_Id {
    for i in 1 ..< len(t.tag) {
        if t.first[i] <= tok && tok < t.end[i] { return Tree_Id(i) }
    }
    return 0
}

// The line of source a token's on, trimmed: tabs between its words one space.
@(private="file")
hit_source_line :: proc(tok: Token) -> string {
    src := source_of(tok)
    lo, hi := int(tok.offset), int(tok.offset)
    for lo > 0 && src[lo - 1] != '\n' { lo -= 1 }
    for hi < len(src) && src[hi] != '\n' { hi += 1 }
    sb := strings.builder_make(context.temp_allocator)
    tabbed := false
    for i in 0 ..< hi - lo {
        ch := src[lo + i]
        if ch != '\t' {
            if tabbed { strings.write_byte(&sb, ' ') }
            strings.write_byte(&sb, ch)
        }
        tabbed = ch == '\t'
    }
    return strings.trim_space(strings.to_string(sb))
}

// A place, as the answer lists it: `  <file>:<line>  <what it's in>`, its line
// of source under it.
@(private="file")
hit_write_place :: proc(sb: ^strings.Builder, t: ^Tree, tok: Token_Id, n: Tree_Id) {
    fmt.sbprintf(sb, "  %s", ask_loc(token_span(build_tokens[tok])))
    if holder := hit_holder_name(t, n); holder != "" { fmt.sbprintf(sb, "  %s", holder) }
    fmt.sbprintf(sb, "\n    %s\n", hit_source_line(build_tokens[tok]))
}

// The types along a path, as it's written: `game.timers.work` is
// `^State.Timers.Timer`. Each part's type is all of the part's, `b[i]` the
// item's. "" when the checker typed none of it.
@(private="file")
hit_path_types :: proc(t: ^Tree, a: ^Annotations, n: Tree_Id) -> string {
    parts := make([dynamic]string, context.temp_allocator)
    cur := n
    for {
        label := hit_type(a, cur)
        if label != "" { inject_at(&parts, 0, label) }
        c := cur
        down: for {
            #partial switch t.tag[c] {
            case .Index, .Slice, .Deref, .Paren, .Try: c = Tree_Id(t.a[c])
            case: break down
            }
        }
        if t.tag[c] != .Field { break }
        cur = Tree_Id(t.a[c])
    }
    return strings.join(parts[:], ".", context.temp_allocator)
}

// A variable's or a field's answer: the path to it as written and the types
// along it, where it's declared, then where it's written, where a pointer to it
// is taken and where it's read: the file asked about first, a line once in
// each. A field's written and read wherever a value of its struct is, in this
// module and the modules it uses.
@(private="file")
hit_uses_answer :: proc(t: ^Tree, a: ^Annotations, p: ^Hit_Point, r: Ref, named_at: Tree_Id) -> string {
    if len(t.parent) != len(t.tag) { tree_parents(t) }
    name := token_text(build_tokens[r.decl])
    here := p.tokens[p.tok_i].file
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)
    seen[r.decl] = true
    uses := make([dynamic]Hit_Use, context.temp_allocator)
    for inst, i in a.instances {
        for ref, k in a.refs[i] {
            if ref.decl != r.decl { continue }
            n := inst.lo + Tree_Id(k)
            tok, named := ref_name_token(t, n, name)
            if !named || seen[tok] { continue }
            seen[tok] = true
            hit_add_use(&uses, tok, n, hit_use_kind(t, a, Instance_Id(i), n), here)
        }
    }

    // (A declaration, a literal's entry, have no type of their own: their uses' does.)
    types := hit_path_types(t, a, named_at)
    for u in uses {
        if types != "" { break }
        types = hit_type(a, u.node)
    }
    if r.kind == .Field { hit_field_writes(t, a, r.decl, &uses, here) }
    slice.sort_by(uses[:], proc(x, y: Hit_Use) -> bool {
        if x.here != y.here { return x.here }
        if x.path != y.path { return x.path < y.path }
        return x.tok < y.tok
    })

    sb := strings.builder_make()
    fmt.sbprintf(&sb, "%s\n", span_text(p.src.source, tree_span(t, named_at)) if t.tag[named_at] == .Field else name)
    if types != "" { fmt.sbprintf(&sb, "%s\n", types) }
    fmt.sbprint(&sb, "\ndeclared\n")
    hit_write_place(&sb, t, r.decl, hit_node_at(t, r.decl))
    for kind in Use_Kind {
        rows := make([dynamic]Hit_Use, context.temp_allocator)
        last_tok: Token
        for u in uses {
            if u.kind != kind { continue }
            tok := build_tokens[u.tok]
            if len(rows) > 0 && tok.file == last_tok.file && token_line(tok) == token_line(last_tok) { continue }
            append(&rows, u)
            last_tok = tok
        }
        if kind == .Pointer && len(rows) == 0 { continue }
        word := "written" if kind == .Written else "pointer taken" if kind == .Pointer else "read"
        fmt.sbprintf(&sb, "%s %d\n", word, len(rows))
        for u in rows { hit_write_place(&sb, t, u.tok, u.node) }
    }
    return strings.to_string(sb)
}

// The Define whose name is the token `decl` — a fun's, a struct's, a
// constant's; 0 for none (a local's, a param's, a field's).
@(private="file")
hit_definition_at :: proc(t: ^Tree, decl: Token_Id) -> Tree_Id {
    for i in 1 ..< len(t.tag) {
        if t.tag[i] == .Define && t.first[i] == decl { return Tree_Id(i) }
    }
    return 0
}

// The source text of the file a token is in.
@(private="file")
source_of :: proc(tok: Token) -> string {
    return build_files[tok.file].source
}
