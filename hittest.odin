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
// what the name is, its type, where it's declared, what it's in, and the
// expressions around it, innermost first.
// ---------------------------------------------------------------------------

// Whether a node is one a cursor names.
@(private="file")
hit_listed :: proc(tag: Tree_Tag) -> bool {
    #partial switch tag {
    case .File, .Param_Group, .Generic_Param, .Union_Tag, .Union_Pad, .Union_Size, .Named_Entry:
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
    r, found := hit_ref(t, a, hits, at, name)
    if !found { return "" }
    if r.decl == 0 { return fmt.tprintf("refers to: %s %s\n", ref_kind_word(r.kind), name) }
    tok := build_tokens[r.decl]
    return fmt.tprintf("refers to: %s %s  %s\n", ref_kind_word(r.kind), token_text(tok), ask_loc(token_span(tok)))
}

// hit_refers's reference: the innermost about the point's name; found false
// for none.
@(private="file")
hit_ref :: proc(t: ^Tree, a: ^Annotations, hits: []Tree_Id, at: int, name: string) -> (Ref, bool) {
    #reverse for n in hits {
        for inst, i in a.instances {
            if n < inst.lo || n > inst.hi || int(n - inst.lo) >= len(a.refs[i]) { continue }
            r := annot_ref(a, Instance_Id(i), n)
            if r.kind == .None { continue }
            if r.decl == 0 {
                // (A builtin: only a node its name begins — the name, a call of it.)
                if int(t.first[n]) != at { continue }
                return r, true
            }
            if token_text(build_tokens[r.decl]) != name { continue }
            return r, true
        }
    }
    // (A definition's own name refers to nothing — it's what's declared
    // there: itself, then.)
    for n in hits {
        if t.tag[n] == .Define && int(t.first[n]) == at { return Ref{decl = Token_Id(at), kind = hit_define_kind(t, n)}, true }
    }
    return {}, false
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

    want := filepath.base(parts[0])
    src_file: ^Source_File
    for _, files in all_files {
        for f in files { if filepath.base(f.path) == want { src_file = f; break } }
        if src_file != nil { break }
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
    r, ok = hit_ref(t, a, p.hits[:], p.at, name)
    return
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
            n := inst.lo + Tree_Id(k)
            // (The name among its node's tokens: a field's is its last.)
            tok: Token_Id
            switch {
            case token_text(build_tokens[t.end[n] - 1]) == name: tok = t.end[n] - 1
            case token_text(build_tokens[t.first[n]]) == name:   tok = t.first[n]
            case: continue
            }
            if !seen[tok] {
                seen[tok] = true
                append(&out, tok)
            }
        }
    }
    return out[:]
}

// Resolve `<file>:<line>:<col>` to the chain of nodes holding it. Returns
// rendered text and whether anything was found.
ask_at_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File,
                     a: ^Annotations, spec: string) -> (string, bool) {
    p, msg, ok := hit_point(t, all_files, spec)
    if !ok { return msg, false }
    want, line, col, base, tokens, tok_i, at, hits, src_file := p.want, p.line, p.col, p.base, p.tokens, p.tok_i, p.at, p.hits, p.src

    sb := strings.builder_make()
    fmt.sbprintf(&sb, "%s:%d:%d  token '%s'\n", want, line, col, token_text(tokens[tok_i]))
    fmt.sbprint(&sb, hit_refers(t, a, hits[:], at, token_text(tokens[tok_i])))
    fmt.sbprint(&sb, "\n")
    prev: Span
    for n in hits {
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
    }
    return strings.to_string(sb), true
}

// `mara ask what at <file>:<line>:<col>`: what is at the point, to read —
// the name there, what it is and its type, where it's declared, the
// definition it's in; then the expressions around it, innermost first, to
// its statement, each with its type. (`ask at` lists every node, for the
// tree's sake.)
ask_what_at_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File,
                          a: ^Annotations, spec: string) -> (string, bool) {
    p, msg, ok := hit_point(t, all_files, spec)
    if !ok { return msg, false }
    hits := p.hits[:]
    name := token_text(p.tokens[p.tok_i])
    inner := hits[len(hits) - 1]
    // (The point's own node: the innermost, when it ends at the point — a
    // name, a field's name. Its type, the name's.)
    own := int(t.end[inner]) - 1 == p.at && t.tag[inner] >= .Number
    own_type := hit_type(a, inner) if own else ""

    sb := strings.builder_make()
    r, refers := hit_ref(t, a, hits, p.at, name)
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
    }
    // (The definition it's in: the innermost Define holding it.)
    #reverse for n in hits {
        if t.tag[n] != .Define || int(t.first[n]) == p.at { continue }   // (its own definition: said above)
        text := span_text(p.src.source, tree_span(t, n))
        if colons := strings.index(text, "::"); colons > 0 {
            fmt.sbprintf(&sb, "  in        %s  %s\n", strings.trim_space(text[:colons]), ask_loc(tree_span(t, n)))
        }
        break
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
        if len(text) > 100 { text = strings.concatenate({text[:100], "…"}, context.temp_allocator) }
        fmt.sbprintf(&sb, "  %s", text)
        if ty != "" { fmt.sbprintf(&sb, "   : %s", ty) }
        fmt.sbprint(&sb, "\n")
        shown += 1
        if shown == 8 { break }
    }
    return strings.to_string(sb), true
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
