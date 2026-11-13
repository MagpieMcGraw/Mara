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
// it's written and read, a field's on that value (place.odin) unless it's the
// field's declaration; of a constant, where it's read; of a variant, where it's
// made and matched; of anything else that's named, what it is, its type and
// where it's declared; of what isn't, the expressions around it. A hover asks
// for what it is alone. `what at <file>:<line>` says what each name on a line
// is, and `<name> at <file>:<line>` is `what at` at that name.
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
hit_type :: proc(a: ^Annotations, n: Tree_Id, ref_elem := false) -> string {
    labels := make([dynamic]string, context.temp_allocator)
    for inst, i in a.instances {
        if n < inst.lo || n > inst.hi { continue }
        ty := annot_type(a, Instance_Id(i), n)
        if fr, is_ref := ty.(^Type_Field); is_ref && ref_elem { ty = fr.elem }
        label := hit_label(ty)
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
        if t.tag[n] == .Define && int(t.first[n]) == at { return Ref{decl = Token_Id(at), kind = names_def_kind(t, Tree_Id(t.b[n]))}, n, true }
    }
    if g := hit_param_group(t, at); g != 0 { return Ref{decl = Token_Id(at), kind = .Param}, g, true }
    return {}, 0, false
}

// The param group that declares a name, its token `at`; 0 for none.
@(private="file")
hit_param_group :: proc(t: ^Tree, at: int) -> Tree_Id {
    lo, hi := tree_file_nodes(t, build_tokens[at].file)
    for i in lo ..= hi {
        if t.tag[i] != .Param_Group || int(t.first[i]) > at || at >= int(t.end[i]) { continue }
        for name in tree_token_list(t, t.a[i]) {
            if int(name) == at { return Tree_Id(i) }
        }
    }
    return 0
}

// A reference's kind as `ask at` says it.
ref_kind_word :: proc(k: Ref_Kind) -> string {
    switch k {
    case .None:    return "nothing"
    case .Local:   return "local"
    case .Param:   return "param"
    case .Result:  return "result"
    case .Field:   return "field"
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

// A path as a key: whatever it's written from, the same file's the same.
@(private="file")
hit_path_key :: proc(path: string) -> string {
    whole, err := filepath.abs(path, context.temp_allocator)
    return path_key(whole if err == nil else path)
}

// A file of this build by a path, or only its name: the one at that path from here if
// there is one, else the first with that name.
@(private="file")
hit_built_file :: proc(file: string) -> ^Source_File {
    want := filepath.base(file)
    named := hit_path_key(file)
    found: ^Source_File
    for f in build_files {
        if f == nil || filepath.base(f.path) != want || f.end_token <= f.first_token { continue }
        if hit_path_key(f.path) == named { return f }
        if found == nil { found = f }
    }
    return found
}

// `<file>:<line>`, or `<file>:<line>:<col>` less its column: the file and the line.
@(private="file")
hit_file_line :: proc(at: string) -> (src: ^Source_File, line: int, msg: string, ok: bool) {
    spec := at
    if ask_at_has_column(spec) { spec = spec[:strings.last_index_byte(spec, ':')] }
    colon := strings.last_index_byte(spec, ':')
    if colon <= 0 { return nil, 0, fmt.tprintf("mara ask: `at %s` — expected <file>:<line>\n", at), false }
    n, n_ok := strconv.parse_int(spec[colon + 1:])
    if !n_ok || n < 1 { return nil, 0, fmt.tprintf("mara ask: `at %s` — the line must be a positive integer\n", at), false }
    src = hit_built_file(spec[:colon])
    if src == nil { return nil, 0, fmt.tprintf("mara ask: no source file named '%s' in this build\n", spec[:colon]), false }
    return src, n, "", true
}

// The names written on a line of a file, as their tokens' ids; none past its end.
@(private="file")
hit_names_on_line :: proc(src: ^Source_File, line: int) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    tokens := build_tokens[src.first_token:src.end_token]
    i, found := token_index_at(tokens, line, 1)
    if !found { return nil }
    for ; i < len(tokens) && token_line(tokens[i]) <= line; i += 1 {
        if token_line(tokens[i]) == line && tokens[i].kind == .Identifier { append(&out, src.first_token + Token_Id(i)) }
    }
    return out[:]
}

// What a name is, as a row: its kind, its type, where it's declared.
@(private="file")
hit_name_row :: proc(sb: ^strings.Builder, t: ^Tree, a: ^Annotations, r: Ref, n: Tree_Id, name: string) {
    fmt.sbprintf(sb, "  %s — %s", name, ref_kind_word(r.kind))
    #partial switch r.kind {
    case .Local, .Param, .Result, .Field, .Const:
        if ty := hit_type(a, n) if t.tag[n] >= .Number else ""; ty != "" { fmt.sbprintf(sb, " : %s", ty) }
    }
    if r.decl != 0 { fmt.sbprintf(sb, "   declared %s", ask_loc(token_span(build_tokens[r.decl]))) }
    strings.write_byte(sb, '\n')
}

// What a name written at a token refers to, a type's as written too: hit_ref's nodes
// aren't types (hit_listed), which the name table has names for.
@(private="file")
hit_name_ref :: proc(checked: ^Checked_Program, src: ^Source_File, want: string, line: int, tok: Token_Id) -> (r: Ref, n: Tree_Id, found: bool) {
    t := &build_tree
    name := token_text(build_tokens[tok])
    if p, _, point_ok := hit_point_in(t, src, want, line, token_col(build_tokens[tok])); point_ok {
        r, n, found = hit_ref(t, checked.annot, p.hits[:], p.at, name)
        if found { return }
    }
    n = tree_node_at(t, tok)
    if n != 0 && int(n) < len(checked.names.refs) {
        r = checked.names.refs[n]
        if r.kind != .None && r.decl != 0 && token_text(build_tokens[r.decl]) == name { return r, n, true }
    }
    return {}, 0, false
}

// `mara ask what at <file>:<line>`: the line, and what each name on it is. A name on a
// line can be asked about: `mara ask <name> at <file>:<line>`.
ask_what_at_line :: proc(checked: ^Checked_Program, at: string) -> (string, bool) {
    t := &build_tree
    a := checked.annot
    src, line, msg, ok := hit_file_line(at)
    if !ok { return msg, false }
    want := filepath.base(src.path)
    names := hit_names_on_line(src, line)
    sb := strings.builder_make()
    tokens := build_tokens[src.first_token:src.end_token]
    i, found := token_index_at(tokens, line, 1)
    if !found || token_line(tokens[i]) != line {
        fmt.sbprintf(&sb, "%s:%d  (nothing's written on it)\n", want, line)
        return strings.to_string(sb), true
    }
    fmt.sbprintf(&sb, "%s  %s\n\n", ask_loc(token_span(tokens[i])), hit_source_line(tokens[i]))
    seen := make(map[string]bool, allocator = context.temp_allocator)
    for tok in names {
        name := token_text(build_tokens[tok])
        r, n, refers := hit_name_ref(checked, src, want, line, tok)
        key := fmt.tprintf("%s/%d", name, int(r.decl))
        if !refers || seen[key] { continue }
        seen[key] = true
        hit_name_row(&sb, t, a, r, n, name)
    }
    return strings.to_string(sb), true
}

// `mara ask <name> at <file>:<line>`: what `name` is there. A fun or a type: its answer
// anywhere. A variable: where it's written and read, or a view of it if one's asked for.
// Anything else: where it's named.
ask_name_at :: proc(checked: ^Checked_Program, name, at, kind, dir, pkg: string, depth: int) -> (string, bool) {
    t := &build_tree
    a := checked.annot
    src, line, msg, ok := hit_file_line(at)
    if !ok { return msg, false }
    want := filepath.base(src.path)
    names := hit_names_on_line(src, line)
    written: Token_Id
    for tok in names {
        if token_text(build_tokens[tok]) == name {
            written = tok
            break
        }
    }
    if written == 0 {
        words := make([dynamic]string, context.temp_allocator)
        for tok in names {
            word := token_text(build_tokens[tok])
            if !slice.contains(words[:], word) { append(&words, word) }
        }
        if len(words) == 0 { return fmt.tprintf("mara ask: no '%s' on %s:%d: no names are written there\n", name, want, line), false }
        return fmt.tprintf("mara ask: no '%s' on %s:%d — its names: %s\n", name, want, line, strings.join(words[:], ", ", context.temp_allocator)), false
    }
    r, _, refers := hit_name_ref(checked, src, want, line, written)
    if !refers { return fmt.tprintf("mara ask: '%s' on %s:%d refers to nothing the check knows\n", name, want, line), false }
    filtered := kind != "" || dir != "" || depth != ASK_DEPTH_OMITTED
    #partial switch r.kind {
    case .Fun, .Type:
        if r.decl != 0 {
            tok := build_tokens[r.decl]
            f := build_files[tok.file]
            return ask(checked, token_text(tok), kind, dir, "", "", pkg, filepath.base(f.path), f.module, depth)
        }
    case .Local, .Param, .Result:
        if filtered {
            for _, ft in checked.functions {
                if ft != nil && ft.kind == .Fun && span_file(ft.body_span) == src.path { du_fn(checked, ft) }
            }
            for b in checked.du.vars {
                if b.tok == r.decl { return render_var_slice(checked, b, ask_label(b.fn), kind, dir, pkg, depth), true }
            }
        }
    case:
        if filtered {
            return fmt.tprintf("mara ask: '%s' on %s:%d is a %s: the answer is where it's named, with no types, call or flow, above or below, or depth\n", name, want, line, ref_kind_word(r.kind)), false
        }
    }
    p, point_msg, point_ok := hit_point_in(t, src, want, line, token_col(build_tokens[written]))
    if !point_ok { return point_msg, false }
    return hit_what(t, a, &p, true, "")
}

// `<file>:<line>:<col>` found: the point; else what to say instead, and
// false.
@(private="file")
hit_point :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File, spec: string) -> (p: Hit_Point, msg: string, ok: bool) {
    // (From the end: a whole path's drive has a colon too.)
    col_at := strings.last_index_byte(spec, ':')
    line_at := strings.last_index_byte(spec[:max(col_at, 0)], ':')
    if col_at <= 0 || line_at <= 0 {
        return p, fmt.tprintf("mara ask: `at %s` — expected <file>:<line>:<col>\n", spec), false
    }
    file := spec[:line_at]
    line, line_ok := strconv.parse_int(spec[line_at + 1:col_at])
    col,  col_ok  := strconv.parse_int(spec[col_at + 1:])
    if !line_ok || !col_ok || line < 1 || col < 1 {
        return p, fmt.tprintf("mara ask: `at %s` — line and column must be positive integers\n", spec), false
    }

    // (A file's name alone can be several files, in the stdlib or ours: the
    // one at that path from here if there is one, else one in this build.)
    want := filepath.base(file)
    named := hit_path_key(file)
    src_file: ^Source_File
    search: for _, files in all_files {
        for f in files {
            if filepath.base(f.path) != want { continue }
            if hit_path_key(f.path) == named {
                src_file = f
                break search
            }
            if src_file == nil || (src_file.end_token <= src_file.first_token && f.end_token > f.first_token) { src_file = f }
        }
    }
    if src_file == nil {
        return p, fmt.tprintf("mara ask: no source file named '%s'\n", file), false
    }
    return hit_point_in(t, src_file, want, line, col)
}

// The point at a line and a column of a file, `want` the file's name.
@(private="file")
hit_point_in :: proc(t: ^Tree, src_file: ^Source_File, want: string, line, col: int) -> (p: Hit_Point, msg: string, ok: bool) {
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
    lo, hi := tree_file_nodes(t, build_tokens[at].file)
    for n in lo ..= hi {
        first, end := int(t.first[n]), int(t.end[n])
        if hit_listed(t.tag[n]) && first <= at && at < end { append(&hits, n) }
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
    #partial switch t.tag[n] {
    case .Arm_Dot, .Arm_Variant:   // (The variant a match's arm names; its body's last token is its body's.)
        return t.main[n], token_text(build_tokens[t.main[n]]) == name
    }
    if token_text(build_tokens[t.end[n] - 1]) == name { return t.end[n] - 1, true }
    if token_text(build_tokens[t.first[n]]) == name { return t.first[n], true }
    return 0, false
}

// How many places name a declaration, its own aside, a generic's instances once.
hit_name_count :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id) -> int {
    return len(references_to(t, a, decl)) - 1
}

// Every name that refers to the declaration whose name is the token `decl`,
// as its token: the declaration's own first, each once (a generic's body's,
// checked an instance at a time, once). What refers to it: annot_uses.
references_to :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id) -> []Token_Id {
    name := token_text(build_tokens[decl])
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)
    out := make([dynamic]Token_Id, context.temp_allocator)
    seen[decl] = true
    append(&out, decl)
    for u in annot_uses(a, decl) {
        tok, named := ref_name_token(t, u.node, name)
        if !named || seen[tok] { continue }
        seen[tok] = true
        append(&out, tok)
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
                          a: ^Annotations, spec: string, uses := false, checked: ^Checked_Program = nil) -> (string, bool) {
    p, msg, ok := hit_point(t, all_files, spec)
    if !ok { return msg, false }
    return hit_what(t, a, &p, uses, "", checked)
}

// What `what at` says at a declaration's name, with its uses. `title` is its first line.
ask_what_at_token :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id, title: string, checked: ^Checked_Program = nil) -> (string, bool) {
    tok := build_tokens[decl]
    src := build_files[tok.file]
    p, msg, ok := hit_point_in(t, src, filepath.base(src.path), token_line(tok), token_col(tok))
    if !ok { return msg, false }
    return hit_what(t, a, &p, true, title, checked)
}

@(private="file")
hit_what :: proc(t: ^Tree, a: ^Annotations, p: ^Hit_Point, uses: bool, title: string, checked: ^Checked_Program = nil) -> (string, bool) {
    hits := p.hits[:]
    name := token_text(p.tokens[p.tok_i])
    inner := hits[len(hits) - 1]
    r, named_at, refers := hit_ref(t, a, hits, p.at, name)
    if uses && refers && r.decl != 0 {
        #partial switch r.kind {
        case .Local, .Param, .Result, .Field, .Const:
            return hit_uses_answer(t, a, p, r, named_at, title, checked), true
        case .Variant:
            return hit_variant_answer(t, a, r.decl, title), true
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
    // (An operator an `overload` gives a meaning: the function it calls.)
    calls := hit_op_calls(t, a, hits, p.at) if !refers else nil
    for decl, i in calls { fmt.sbprintf(&sb, "%s%s", " — calls " if i == 0 else ", ", token_text(build_tokens[decl])) }
    if own_type != "" { fmt.sbprintf(&sb, " : %s", own_type) }
    fmt.sbprint(&sb, "\n")
    for decl in calls { hit_declared(&sb, t, decl) }
    if refers {
        if r.decl == 0 {
            fmt.sbprint(&sb, "  built into the compiler\n")
        } else {
            hit_declared(&sb, t, r.decl)
        }
        // (A type's name: what a value of it can do.)
        if checked != nil && r.kind == .Type {
            if ty, bound := checked_binding(checked, r, name); bound {
                if fs, is_scope := ty.(^Type_Scope); !is_scope || fs.kind == .Struct {
                    can_do(&sb, checked, ty, Token_Id(p.at))
                }
            }
        } else if checked != nil && r.kind == .Builtin {
            if ty, is_type := tc_primitive_named(name); is_type { can_do(&sb, checked, ty, Token_Id(p.at)) }
        }
        return strings.to_string(sb), true
    }

    // (A type's keyword, `i64`: what a value of it can do.)
    if checked != nil {
        if ty, is_type := tc_primitive_named(name); is_type { can_do(&sb, checked, ty, Token_Id(p.at)) }
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

// Where decl is declared, and its definition's first line: a fun's signature, a
// struct's params.
@(private="file")
hit_declared :: proc(sb: ^strings.Builder, t: ^Tree, decl: Token_Id) {
    fmt.sbprintf(sb, "  declared  %s\n", ask_loc(token_span(build_tokens[decl])))
    if def := tree_define_at(t, decl); def != 0 {
        first := span_text(source_of(build_tokens[decl]), tree_span(t, def))
        first = strings.trim_suffix(strings.trim_suffix(first, " …"), " {")
        fmt.sbprintf(sb, "  %s\n", first)
    }
}

// The functions the operator at token `at` calls — an `overload`'s members the
// checker picked for it, by their declarations, each once (in a generic's body
// each instance picks its own).
@(private="file")
hit_op_calls :: proc(t: ^Tree, a: ^Annotations, hits: []Tree_Id, at: int) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    #reverse for n in hits {
        op := t.main[n]
        if t.tag[n] == .Compound { op = Token_Id(tree_rec(t, t.b[n], 2)[0]) }   // (`x op= v`, kept on the statement)
        if int(op) != at { continue }
        for inst, i in a.instances {
            if n < inst.lo || n > inst.hi { continue }
            ts := a.callees[annot_key(Instance_Id(i), n)] or_else nil
            if ts != nil && ts.decl != 0 && !slice.contains(out[:], ts.decl) { append(&out, ts.decl) }
        }
        if len(out) > 0 { break }
    }
    return out[:]
}

// --- variants ------------------------------------------------------------------

// Whether a variant named at node n asks what a value is, or makes one: a match's
// arm, a comparison.
@(private="file")
hit_variant_matched :: proc(t: ^Tree, n: Tree_Id) -> bool {
    #partial switch t.tag[n] {
    case .Arm_Dot, .Arm_Variant: return true
    }
    cur := n
    for {
        p := t.parent[cur]
        #partial switch t.tag[p] {
        case .Paren:
            cur = p
            continue
        case .Arm_Value:
            return Tree_Id(t.a[p]) == cur
        case .Binary:
            op := token_text(build_tokens[t.main[p]])
            return op == "==" || op == "!="
        }
        return false
    }
}

// Every place the variants `decls` are named: made (Written) or matched (Read), each
// once, in source order.
@(private="file")
hit_variant_uses :: proc(t: ^Tree, a: ^Annotations, decls: []Token_Id) -> map[Token_Id][dynamic]Hit_Use {
    if len(t.parent) != len(t.tag) { tree_parents(t) }
    out := make(map[Token_Id][dynamic]Hit_Use, allocator = context.temp_allocator)
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)
    for decl in decls {
        for u in annot_uses(a, decl) {
            if annot_use_ref(a, u).kind != .Variant { continue }
            tok, named := ref_name_token(t, u.node, token_text(build_tokens[decl]))
            if !named || seen[tok] { continue }
            seen[tok] = true
            list := out[decl]
            list.allocator = context.temp_allocator
            hit_add_use(&list, tok, u.node, .Read if hit_variant_matched(t, u.node) else .Written, 0)
            out[decl] = list
        }
    }
    for _, list in out {
        slice.sort_by(list[:], proc(x, y: Hit_Use) -> bool {
            if x.path != y.path { return x.path < y.path }
            return x.tok < y.tok
        })
    }
    return out
}

// The uses of one kind, a line once.
@(private="file")
hit_variant_rows :: proc(uses: []Hit_Use, kind: Use_Kind) -> []Hit_Use {
    rows := make([dynamic]Hit_Use, context.temp_allocator)
    last: Token
    for u in uses {
        if u.kind != kind { continue }
        tok := build_tokens[u.tok]
        if len(rows) > 0 && tok.file == last.file && token_line(tok) == token_line(last) { continue }
        append(&rows, u)
        last = tok
    }
    return rows[:]
}

// What a variant's uses are called: an error's are how things fail.
@(private="file")
hit_variant_words :: proc(is_error: bool) -> (made, matched: string) {
    if is_error { return "fails with", "handled" }
    return "made", "matched"
}

// How many of a variant's uses a type's view lists: `mara ask <type>.<variant>` has
// every one.
HIT_VARIANT_ROWS_SHOWN :: 6

// A type's view of its variants: for each named anywhere, how many places make it and
// how many match it, and where; the ones nothing names, together.
hit_write_variants :: proc(b: ^strings.Builder, t: ^Tree, a: ^Annotations, decls: []Token_Id, owner: string, is_error: bool) {
    if len(decls) == 0 { return }
    uses := hit_variant_uses(t, a, decls)
    made_word, matched_word := hit_variant_words(is_error)
    fmt.sbprintf(b, "\nvariants (%d)\n", len(decls))
    never := make([dynamic]string, context.temp_allocator)
    for decl in decls {
        name := token_text(build_tokens[decl])
        list := uses[decl] or_else nil
        if len(list) == 0 {
            append(&never, name)
            continue
        }
        made, matched := hit_variant_rows(list[:], .Written), hit_variant_rows(list[:], .Read)
        fmt.sbprintf(b, "  %s   (%s %d, %s %d)\n", name, made_word, len(made), matched_word, len(matched))
        shown := 0
        for rows, which in ([2][]Hit_Use{made, matched}) {
            for u in rows {
                if shown < HIT_VARIANT_ROWS_SHOWN {
                    fmt.sbprintf(b, "    %s  %s  %s  %s\n", made_word if which == 0 else matched_word, ask_loc(token_span(build_tokens[u.tok])), hit_holder_name(t, u.node), hit_source_line(build_tokens[u.tok]))
                }
                shown += 1
            }
        }
        if shown > HIT_VARIANT_ROWS_SHOWN {
            fmt.sbprintf(b, "    (%d more: `mara ask %s.%s` has each)\n", shown - HIT_VARIANT_ROWS_SHOWN, owner, name)
        }
    }
    if len(never) > 0 {
        fmt.sbprintf(b, "  nothing names: %s\n", strings.join(never[:], ", ", context.temp_allocator))
    }
}

// A variant asked about: where it's made and where it's matched, every one.
hit_variant_answer :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id, title: string) -> string {
    if len(t.parent) != len(t.tag) { tree_parents(t) }
    // (Its type's definition holds it.)
    owner := ""
    is_error := false
    for c := tree_node_at(t, decl); c != 0; c = t.parent[c] {
        if t.tag[c] == .Error_Def { is_error = true }
        if t.tag[c] == .Define {
            owner = token_text(build_tokens[t.main[c]])
            break
        }
    }
    uses := hit_variant_uses(t, a, []Token_Id{decl})
    list := uses[decl] or_else nil
    sb := strings.builder_make()
    if title != "" {
        fmt.sbprintf(&sb, "%s\n", title)
    } else {
        fmt.sbprintf(&sb, "%s — variant of %s  %s\n", token_text(build_tokens[decl]), owner, ask_loc(token_span(build_tokens[decl])))
    }
    made_word, matched_word := hit_variant_words(is_error)
    for rows, which in ([2][]Hit_Use{hit_variant_rows(list[:], .Written), hit_variant_rows(list[:], .Read)}) {
        fmt.sbprintf(&sb, "\n%s %d\n", made_word if which == 0 else matched_word, len(rows))
        for u in rows { hit_write_place(&sb, t, u.tok, u.node) }
    }
    return strings.to_string(sb)
}

// What a use of a name does to what it names. A pointer taken may be either:
// what's done with it is elsewhere.
Use_Kind :: enum { Written, Pointer, Read }

// A place a name is used, or a field is written without being named: the token
// it's at, its node, and what it does there.
Hit_Use :: struct {
    tok:   Token_Id,
    node:  Tree_Id,
    kind:  Use_Kind,
    path:  string,   // its file's
    here:  bool,     // in the file the question's about
    maybe: bool,     // it can't be told whether it's on the value asked about
}

// A use added: `here` the file the question's about.
@(private="file")
hit_add_use :: proc(uses: ^[dynamic]Hit_Use, tok: Token_Id, n: Tree_Id, kind: Use_Kind, here: u16, maybe := false) {
    token := build_tokens[tok]
    append(uses, Hit_Use{tok, n, kind, span_file(token_span(token)), token.file == here, maybe})
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
            // (`&x ++ v` adds to x.)
            up := t.parent[p]
            if t.tag[up] == .Binary && Tree_Id(t.a[up]) == p && token_text(build_tokens[t.main[up]]) == "++" { return .Written }
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
// that holds it assigned whole, a literal's entry by position. Only those on
// the places asked about (none: every value of its struct).
@(private="file")
hit_field_writes :: proc(t: ^Tree, a: ^Annotations, decl: Token_Id, uses: ^[dynamic]Hit_Use, here: u16, f: ^Place_Finder, asked: []Place) {
    known := make(map[^Type_Scope]bool, allocator = context.temp_allocator)
    entry := proc(uses: ^[dynamic]Hit_Use, t: ^Tree, f: ^Place_Finder, asked: []Place, decl: Token_Id, lit, at: Tree_Id, i: Instance_Id, here: u16) {
        m := Place_Match.Yes
        if asked != nil { m = place_match(asked, place_of_entry(f, lit, decl, i)) }
        if m != .No { hit_add_use(uses, t.first[at], at, .Written, here, m == .Maybe) }
    }
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            #partial switch t.tag[n] {
            case .Assign:
                for target in tree_list(t, t.a[n]) {
                    if hit_holds_field(annot_type(a, Instance_Id(i), target), decl, &known) {
                        m := Place_Match.Yes
                        if asked != nil { m = place_holds(asked, place_of(f, target, Instance_Id(i))) }
                        if m != .No { hit_add_use(uses, t.first[target], target, .Written, here, m == .Maybe) }
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
                    for field in user {
                        if field.decl == decl { entry(uses, t, f, asked, decl, n, n, Instance_Id(i), here) }
                    }
                    continue
                }
                for e, at in entries {
                    if at < len(user) && user[at].decl == decl { entry(uses, t, f, asked, decl, n, e, Instance_Id(i), here) }
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

// The line of source a token's on, trimmed: tabs between its words one space.
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
// item's; a field reference's past the first part its field's type, so
// `Events.mouse.x` is `Events.Mouse.f32`. "" when the checker typed none of it.
@(private="file")
hit_path_types :: proc(t: ^Tree, a: ^Annotations, n: Tree_Id) -> string {
    parts := make([dynamic]string, context.temp_allocator)
    cur := n
    for {
        c := cur
        down: for {
            #partial switch t.tag[c] {
            case .Index, .Slice, .Deref, .Paren, .Try: c = Tree_Id(t.a[c])
            case: break down
            }
        }
        label := hit_type(a, cur, ref_elem = t.tag[c] == .Field)
        if label != "" { inject_at(&parts, 0, label) }
        if t.tag[c] != .Field { break }
        cur = Tree_Id(t.a[c])
    }
    return strings.join(parts[:], ".", context.temp_allocator)
}

// The places a use of a field is on: a literal's named entry's are where the
// literal goes.
@(private="file")
hit_use_places :: proc(f: ^Place_Finder, t: ^Tree, n: Tree_Id, decl: Token_Id, i: Instance_Id) -> []Place {
    if t.tag[n] == .Named_Entry { return place_of_entry(f, t.parent[n], decl, i) }
    return place_of(f, n, i)
}

// The places a field asked about at node n is on, in every instance n's checked
// in; nil for its declaration, which is about every value of its struct.
@(private="file")
hit_asked_places :: proc(f: ^Place_Finder, t: ^Tree, a: ^Annotations, n: Tree_Id, decl: Token_Id) -> []Place {
    if t.tag[n] != .Field && t.tag[n] != .Named_Entry && !(t.tag[n] == .Ident && t.main[n] != decl) { return nil }
    out := make([dynamic]Place, context.temp_allocator)
    for inst, i in a.instances {
        if n < inst.lo || n > inst.hi || annot_ref(a, Instance_Id(i), n).decl != decl { continue }
        append(&out, ..hit_use_places(f, t, n, decl, Instance_Id(i)))
    }
    return out[:] if len(out) > 0 else nil
}

// A variable's or a field's answer: the path to it as written and the types
// along it, where it's declared, then where it's written, where a pointer to it
// is taken and where it's read: the file asked about first, a line once in
// each. A field reached through a value is about that value, followed through
// locals and params (place.odin); where that can't be told, a use is listed
// apart as a maybe. A field's declaration is about every value of its struct.
@(private="file")
hit_uses_answer :: proc(t: ^Tree, a: ^Annotations, p: ^Hit_Point, r: Ref, named_at: Tree_Id, title: string, checked: ^Checked_Program = nil) -> string {
    if len(t.parent) != len(t.tag) { tree_parents(t) }
    name := token_text(build_tokens[r.decl])
    here := p.tokens[p.tok_i].file
    seen := make(map[Token_Id]bool, allocator = context.temp_allocator)
    seen[r.decl] = true
    uses := make([dynamic]Hit_Use, context.temp_allocator)
    finder: ^Place_Finder
    asked: []Place
    if r.kind == .Field {
        finder = place_finder_make(t, a)
        asked = hit_asked_places(finder, t, a, named_at, r.decl)
    }
    for u in annot_uses(a, r.decl) {
        tok, named := ref_name_token(t, u.node, name)
        if !named || seen[tok] { continue }
        m := Place_Match.Yes
        if asked != nil && int(tok) != p.at { m = place_match(asked, hit_use_places(finder, t, u.node, r.decl, u.inst)) }
        if m == .No { continue }
        seen[tok] = true
        hit_add_use(&uses, tok, u.node, hit_use_kind(t, a, u.inst, u.node), here, m == .Maybe)
    }

    // (A declaration, a literal's entry, have no type of their own: their uses' does.)
    types := hit_path_types(t, a, named_at)
    for u in uses {
        if types != "" { break }
        types = hit_type(a, u.node)
    }
    if r.kind == .Field { hit_field_writes(t, a, r.decl, &uses, here, finder, asked) }
    slice.sort_by(uses[:], proc(x, y: Hit_Use) -> bool {
        if x.here != y.here { return x.here }
        if x.path != y.path { return x.path < y.path }
        return x.tok < y.tok
    })

    sb := strings.builder_make()
    if title != "" {
        fmt.sbprintf(&sb, "%s\n", title)
    } else {
        fmt.sbprintf(&sb, "%s\n", span_text(p.src.source, tree_span(t, named_at)) if t.tag[named_at] == .Field else name)
    }
    if types != "" { fmt.sbprintf(&sb, "%s\n", types) }
    if checked != nil {
        // (What it can do: its type's, the node naming it or a use's.)
        ty := completion_type_of(a, named_at)
        for u in uses {
            if ty != nil { break }
            ty = completion_type_of(a, u.node)
        }
        can_do(&sb, checked, ty, Token_Id(p.at))
    }
    fmt.sbprint(&sb, "\ndeclared\n")
    hit_write_place(&sb, t, r.decl, tree_node_at(t, r.decl))
    for maybe in ([2]bool{false, true}) {
        for kind in Use_Kind {
            rows := make([dynamic]Hit_Use, context.temp_allocator)
            last_tok: Token
            for u in uses {
                if u.kind != kind || u.maybe != maybe { continue }
                tok := build_tokens[u.tok]
                if len(rows) > 0 && tok.file == last_tok.file && token_line(tok) == token_line(last_tok) { continue }
                append(&rows, u)
                last_tok = tok
            }
            if (maybe || kind == .Pointer || (kind == .Written && r.kind == .Const)) && len(rows) == 0 { continue }
            word := "written" if kind == .Written else "pointer taken" if kind == .Pointer else "read"
            fmt.sbprintf(&sb, "%s%s %d\n", "maybe " if maybe else "", word, len(rows))
            for u in rows { hit_write_place(&sb, t, u.tok, u.node) }
        }
    }
    return strings.to_string(sb)
}

// The source text of the file a token is in.
@(private="file")
source_of :: proc(tok: Token) -> string {
    return build_files[tok.file].source
}
