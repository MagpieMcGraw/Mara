package mara

import "core:fmt"
import "core:strconv"
import "core:strings"
import "core:path/filepath"

// ---------------------------------------------------------------------------
// Position → AST node. The lookup behind `mara ask at <file>:<line>:<col>`, and
// the addressing primitive the other queries should eventually hang off: a name
// is ambiguous (a module, a struct and three locals can share one), but a point
// in the source names exactly one node.
//
// Three steps. Resolve the cursor to a token index (binary search, since the
// token array is ordered by position). Walk the AST collecting every node whose
// token extent contains that index. Sort by width — containment is nested, so
// the narrowest match is the innermost node and the list reads outermost-in.
//
// Extents come from Span.tok/tok_end, recorded by the parser (see cover_span).
// That is why this works in token indices rather than (line, col) pairs:
// containment is an integer compare, and token indices carry no text encoding.
//
// NOT walked: `Stmt_Decl.checked`, `Stmt_Multi_Return_Assign.checked` and
// `Expr_Call.desugared`. Those hold checker-synthesized replacement nodes, not
// source the user can point at — the cursor lands on the original, which is
// what it was aimed at. Some resolved information lives on the desugared node,
// so a renderer may need to follow those links even though the walk does not.
// Type_Exprs are also skipped: a separate union, and no extents on it yet.
// ---------------------------------------------------------------------------

Hit :: struct {
    label: string,   // node kind, e.g. "Expr_Binary"
    span:  Span,
    expr:  Expr,     // set for expression nodes, nil otherwise
    stmt:  Stmt,     // set for statement nodes, nil otherwise
}

@(private="file")
contains :: proc(s: Span, i: int) -> bool {
    return s.tok_end > s.tok && s.tok <= i && i < s.tok_end
}

@(private="file")
add_expr :: proc(out: ^[dynamic]Hit, label: string, e: Expr, i: int) {
    if sp := expr_span(e); sp != nil && contains(sp^, i) {
        append(out, Hit{label = label, span = sp^, expr = e})
    }
}

// --- the walk ---------------------------------------------------------------
//
// Both switches are exhaustive on purpose: a new AST variant fails to compile
// here until it is handled, rather than silently becoming a hole the cursor
// falls through. Children are visited unconditionally rather than only when the
// parent matched — a node built outside the four parse dispatch points may not
// have been widened to cover its children, and a missed node is worse than a
// few wasted comparisons on a one-shot query.

hit_expr :: proc(e: Expr, i: int, out: ^[dynamic]Hit) {
    if e == nil { return }
    switch v in e {
    case ^Expr_Number:           add_expr(out, "Expr_Number", e, i)
    case ^Expr_String:           add_expr(out, "Expr_String", e, i)
    case ^Expr_Char:             add_expr(out, "Expr_Char", e, i)
    case ^Expr_Ident:            add_expr(out, "Expr_Ident", e, i)
    case ^Expr_Bool:             add_expr(out, "Expr_Bool", e, i)
    case ^Expr_Skip_Constructor: add_expr(out, "Expr_Skip_Constructor", e, i)
    case ^Expr_Compiler_Intrinsic: add_expr(out, "Expr_Compiler_Intrinsic", e, i)
    case ^Expr_Include:          add_expr(out, "Expr_Include", e, i)
    case ^Expr_Type_Name:        add_expr(out, "Expr_Type_Name", e, i)
    case ^Expr_Self:             add_expr(out, "Expr_Self", e, i)
    case ^Expr_Size_Of:          add_expr(out, "Expr_Size_Of", e, i)   // type_expr child skipped

    case ^Expr_Unary:
        add_expr(out, "Expr_Unary", e, i)
        hit_expr(v.operand, i, out)
    case ^Expr_Binary:
        add_expr(out, "Expr_Binary", e, i)
        hit_expr(v.left, i, out); hit_expr(v.right, i, out)
    case ^Expr_Call:
        add_expr(out, "Expr_Call", e, i)
        hit_expr(v.qualifier, i, out)
        for a in v.args { hit_expr(a, i, out) }
        if v.overrides != nil { hit_expr(v.overrides, i, out) }
    case ^Expr_Array:
        add_expr(out, "Expr_Array", e, i)
        for el in v.elements { hit_expr(el, i, out) }
    case ^Expr_Index:
        add_expr(out, "Expr_Index", e, i)
        hit_expr(v.expr, i, out); hit_expr(v.index, i, out)
    case ^Expr_Slice:
        add_expr(out, "Expr_Slice", e, i)
        hit_expr(v.expr, i, out); hit_expr(v.low, i, out); hit_expr(v.high, i, out)
    case ^Expr_Struct_Literal:
        add_expr(out, "Expr_Struct_Literal", e, i)
        for f in v.fields { hit_expr(f.value, i, out) }
        hit_expr(v.broadcast_value, i, out)
        for av in v.array_values { hit_expr(av, i, out) }
    case ^Expr_Field_Access:
        add_expr(out, "Expr_Field_Access", e, i)
        hit_expr(v.expr, i, out)
    case ^Expr_Assert:
        add_expr(out, "Expr_Assert", e, i)
        hit_expr(v.cond, i, out)
    case ^Expr_Take:
        add_expr(out, "Expr_Take", e, i)
        hit_expr(v.storage, i, out); hit_expr(v.count_expr, i, out)
    case ^Expr_If:
        add_expr(out, "Expr_If", e, i)
        hit_expr(v.condition, i, out); hit_expr(v.then_expr, i, out); hit_expr(v.else_expr, i, out)
    case ^Expr_Tuple_Default:
        add_expr(out, "Expr_Tuple_Default", e, i)
        hit_expr(v.source, i, out)
    case ^Expr_Try:
        add_expr(out, "Expr_Try", e, i)
        hit_expr(v.inner, i, out)
    }
}

hit_stmt :: proc(s: Stmt, i: int, out: ^[dynamic]Hit) {
    if s == nil { return }
    label: string
    switch v in s {
    case ^Stmt_Assign:              label = "Stmt_Assign"
    case ^Stmt_Multi_Assign:        label = "Stmt_Multi_Assign"
    case ^Stmt_Multi_Return_Assign: label = "Stmt_Multi_Return_Assign"
    case ^Stmt_Decl:                label = "Stmt_Decl"
    case ^Stmt_Define:              label = "Stmt_Define"
    case Stmt_Call:                 label = "Stmt_Call"
    case ^Stmt_If:                  label = "Stmt_If"
    case ^Stmt_For:                 label = "Stmt_For"
    case ^Stmt_Scope:               label = "Stmt_Scope"
    case Stmt_Return:               label = "Stmt_Return"
    case Stmt_Break:                label = "Stmt_Break"
    case Stmt_Continue:             label = "Stmt_Continue"
    case ^Stmt_Defer:               label = "Stmt_Defer"
    case ^Stmt_Match:               label = "Stmt_Match"
    case ^Stmt_Foreign:             label = "Stmt_Foreign"
    case ^Stmt_Union_Def:           label = "Stmt_Union_Def"
    case ^Stmt_Distinct_Def:        label = "Stmt_Distinct_Def"
    case ^Stmt_Dispatch_Def:        label = "Stmt_Dispatch_Def"
    case Stmt_Overload:             label = "Stmt_Overload"
    case Stmt_Module:               label = "Stmt_Module"
    }
    sp := stmt_span(s)
    if contains(sp, i) {
        append(out, Hit{label = label, span = sp, stmt = s})
    }

    // Children. Second switch so the label pass above stays a flat table.
    #partial switch v in s {
    case ^Stmt_Assign:
        hit_expr(v.value, i, out); hit_expr(v.target, i, out); hit_expr(v.slice_cap_expr, i, out)
    case ^Stmt_Multi_Assign:
        for a in v.assigns { hit_stmt(a, i, out) }
    case ^Stmt_Multi_Return_Assign:
        for t in v.targets { hit_expr(t, i, out) }
        for e in v.values  { hit_expr(e, i, out) }
    case ^Stmt_Decl:
        for e in v.init_values { hit_expr(e, i, out) }
        hit_expr(v.slice_cap_expr, i, out)
    case ^Stmt_Define:
        hit_expr(v.value, i, out)
    case Stmt_Call:
        hit_expr(v.expr, i, out)
    case ^Stmt_If:
        hit_expr(v.condition, i, out)
        for b in v.body      { hit_stmt(b, i, out) }
        for b in v.else_body { hit_stmt(b, i, out) }
    case ^Stmt_For:
        hit_stmt(v.init, i, out); hit_stmt(v.post, i, out)
        hit_expr(v.condition, i, out)
        hit_expr(v.range_low, i, out); hit_expr(v.range_high, i, out)
        hit_expr(v.collection, i, out); hit_expr(v.collection_len, i, out)
        for b in v.body { hit_stmt(b, i, out) }
    case ^Stmt_Scope:
        for b in v.typed_params { hit_expr(b.default_value, i, out) }
        for f in v.fields       { hit_expr(f.default_value, i, out) }
        for b in v.body { hit_stmt(b, i, out) }
        for d in v.defs { hit_stmt(d, i, out) }   // may overlap body; deduped at output
    case Stmt_Return:
        for e in v.values { hit_expr(e, i, out) }
    case ^Stmt_Defer:
        for b in v.body { hit_stmt(b, i, out) }
    case ^Stmt_Match:
        hit_expr(v.subject, i, out)
        for arm in v.arms {
            hit_expr(arm.value, i, out)
            for b in arm.body { hit_stmt(b, i, out) }
        }
    case ^Stmt_Foreign:
        for d in v.decls {
            for prm in d.typed_params { hit_expr(prm.default_value, i, out) }
        }
    case ^Stmt_Union_Def:
        for variant in v.variants {
            for f in variant.fields { hit_expr(f.default_value, i, out) }
        }
    case ^Stmt_Distinct_Def:
        hit_expr(v.default_cap_expr, i, out)
    }
}

// --- cursor → token ---------------------------------------------------------

// Index of the token at or immediately before (line, col). The array is ordered
// by position, so this is a binary search for the last token that starts at or
// before the cursor. Columns are BYTE offsets into the line — see lexer_advance;
// a caller working in characters has to convert before calling.
token_index_at :: proc(tokens: []Token, line, col: int) -> (int, bool) {
    if len(tokens) == 0 { return 0, false }
    before :: proc(t: Token, line, col: int) -> bool {
        return t.line < line || (t.line == line && t.col <= col)
    }
    lo, hi, best := 0, len(tokens) - 1, -1
    for lo <= hi {
        mid := (lo + hi) / 2
        if before(tokens[mid], line, col) { best = mid; lo = mid + 1 } else { hi = mid - 1 }
    }
    if best < 0 { return 0, false }
    // Landing on an earlier line means the cursor sits before the first token of
    // its own line (leading indentation). Prefer that line's first token.
    if tokens[best].line != line && best + 1 < len(tokens) && tokens[best + 1].line == line {
        return best + 1, true
    }
    return best, true
}

// --- entry ------------------------------------------------------------------

// Byte offset of a 1-based (line, col) in `src`, or -1 when out of range.
@(private="file")
offset_of :: proc(src: string, line, col: int) -> int {
    cur, i := 1, 0
    for i < len(src) && cur < line { if src[i] == '\n' { cur += 1 }; i += 1 }
    if cur != line { return -1 }
    off := i + col - 1
    return off if off <= len(src) else -1
}

// The source text a span covers, trimmed to one line for display.
@(private="file")
span_text :: proc(src: string, tokens: []Token, s: Span) -> string {
    if s.tok_end <= s.tok || s.tok_end > len(tokens) { return "" }
    first, last := tokens[s.tok], tokens[s.tok_end - 1]
    lo := offset_of(src, first.line, first.col)
    if lo < 0 { return "" }
    hi := offset_of(src, last.line, last.col + len(last.text))
    multiline := last.line != first.line
    if multiline || hi < 0 || hi > len(src) {
        // Clip to the first line and mark the truncation.
        end := lo
        for end < len(src) && src[end] != '\n' { end += 1 }
        return strings.concatenate({strings.trim_space(src[lo:end]), " …"})
    }
    return strings.trim_space(src[lo:hi])
}

// Resolve `<file>:<line>:<col>` to the chain of AST nodes containing it.
// Returns rendered text and whether anything was found.
ask_at_point :: proc(programs: map[string]^Program,
                     all_files: map[string][dynamic]^Source_File,
                     spec: string) -> (string, bool) {
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
    if src_file.tokens == nil || len(src_file.tokens) == 0 {
        return fmt.tprintf("mara ask: '%s' has no tokens (not part of this build?)\n", want), false
    }

    tokens := src_file.tokens[:]
    tok_i, found := token_index_at(tokens, line, col)
    if !found {
        return fmt.tprintf("mara ask: nothing at %s:%d:%d\n", want, line, col), false
    }

    hits: [dynamic]Hit
    defer delete(hits)
    for _, prog in programs {
        for s in prog { if stmt_span(s).file == src_file.path { hit_stmt(s, tok_i, &hits) } }
    }
    if len(hits) == 0 {
        return fmt.tprintf("%s:%d:%d — token '%s', but no AST node covers it\n",
                           want, line, col, tokens[tok_i].text), false
    }

    // Widest first: containment is nested, so this reads outermost → innermost.
    for a in 1 ..< len(hits) {
        h := hits[a]
        b := a - 1
        for b >= 0 && (hits[b].span.tok_end - hits[b].span.tok) < (h.span.tok_end - h.span.tok) {
            hits[b + 1] = hits[b]; b -= 1
        }
        hits[b + 1] = h
    }

    sb := strings.builder_make()
    fmt.sbprintf(&sb, "%s:%d:%d  token '%s'\n\n", want, line, col, tokens[tok_i].text)
    prev := Span{tok = -1, tok_end = -1}
    for h in hits {
        if h.span.tok == prev.tok && h.span.tok_end == prev.tok_end { continue }  // defs/body overlap
        prev = h.span
        t := ""
        if h.expr != nil { t = ask_label(expr_type(h.expr)) }
        fmt.sbprintf(&sb, "  %-24s [%d,%d)  %s", h.label, h.span.tok, h.span.tok_end,
                     span_text(src_file.source, tokens, h.span))
        if t != "" { fmt.sbprintf(&sb, "   : %s", t) }
        fmt.sbprint(&sb, "\n")
    }
    return strings.to_string(sb), true
}
