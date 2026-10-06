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


// Resolve `<file>:<line>:<col>` to the chain of nodes holding it. Returns
// rendered text and whether anything was found.
ask_at_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File,
                     a: ^Annotations, spec: string) -> (string, bool) {
    parts := strings.split(spec, ":")
    defer delete(parts)
    if len(parts) != 3 {
        return fmt.tprintf("mara ask: `at %s` — expected <file>:<line>:<col>\n", spec), false
    }
    line, line_ok := strconv.parse_int(parts[1])
    col,  col_ok  := strconv.parse_int(parts[2])
    if !line_ok || !col_ok || line < 1 || col < 1 {
        return fmt.tprintf("mara ask: `at %s` — line and column must be positive integers\n", spec), false
    }

    want := filepath.base(parts[0])
    src_file: ^Source_File
    for _, files in all_files {
        for f in files { if filepath.base(f.path) == want { src_file = f; break } }
        if src_file != nil { break }
    }
    if src_file == nil {
        return fmt.tprintf("mara ask: no source file named '%s'\n", parts[0]), false
    }
    if src_file.end_token <= src_file.first_token {
        return fmt.tprintf("mara ask: '%s' has no tokens (not part of this build?)\n", want), false
    }

    // (Token positions print from the file's first.)
    base := int(src_file.first_token)
    tokens := build_tokens[src_file.first_token:src_file.end_token]
    tok_i, found := token_index_at(tokens, line, col)
    if !found {
        return fmt.tprintf("mara ask: nothing at %s:%d:%d\n", want, line, col), false
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
        return fmt.tprintf("%s:%d:%d — token '%s', but no node covers it\n",
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

    sb := strings.builder_make()
    fmt.sbprintf(&sb, "%s:%d:%d  token '%s'\n\n", want, line, col, token_text(tokens[tok_i]))
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
