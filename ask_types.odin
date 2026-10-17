package mara

import "core:fmt"
import "core:slice"
import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// `mara ask [N!]T` — where a type of a shape is: each place one is written
// (a type in the source — a declaration's, a param's, a literal's, an
// alias's — exactly, at its `[` or `^`), and each declaration whose type has
// one (a param, result, local or field, written so or not: `name : str64` is
// a `[64]utf8`). A shape: `[N]T` a list, `[N!]T` exactly N, `[K]T` an
// enum's array (`[Kind]T` that enum's), `[]T` a view, `^T` a pointer; a size
// a number or any (a name); an element `T` any, a type's name, or a shape
// (`[N][]byte`, `^[N!]f32`). The user's code by default; `in <module>` one
// module, the stdlib's too; `in <file>` one file.
// ---------------------------------------------------------------------------

Ask_Shape_Kind :: enum u8 { Any, Named, List, Fixed, By_Enum, Slice, Pointer }

Ask_Shape :: struct {
    kind: Ask_Shape_Kind,
    size: int,       // a list's or array's: -1, any
    name: string,    // Named: the type's name; By_Enum: the enum's ("": any)
    elem: ^Ask_Shape,
}

// Whether a query's subject is a shape, not a name.
ask_is_shape :: proc(s: string) -> bool {
    return len(s) > 0 && (s[0] == '[' || s[0] == '^')
}

// A shape from its text, all of it; else why it isn't one.
ask_parse_shape :: proc(s: string) -> (sh: ^Ask_Shape, err: string) {
    rest: string
    sh, rest, err = ask_shape_part(s)
    if err == "" && rest != "" { err = fmt.tprintf("'%s' after the shape", rest) }
    return
}

@(private="file")
ask_shape_part :: proc(s: string) -> (sh: ^Ask_Shape, rest: string, err: string) {
    sh = new(Ask_Shape, context.temp_allocator)
    sh.size = -1
    if s == "" { return sh, "", "an element's type is missing (`T`: any)" }
    if s[0] == '^' {
        sh.kind = .Pointer
        sh.elem, rest, err = ask_shape_part(s[1:])
        return
    }
    if s[0] == '[' {
        close := strings.index_byte(s, ']')
        if close < 0 { return sh, "", "a `[` with no `]`" }
        inner := s[1:close]
        switch {
        case inner == "" || inner[0] == ':':
            sh.kind = .Slice
        case strings.has_prefix(inner, ".."):
            return sh, "", "a list is written `[N]T` now, no `..`"
        case strings.has_suffix(inner, "!"):
            sh.kind = .Fixed
            sh.size = ask_shape_size(inner[:len(inner) - 1])
        case inner == "K":
            sh.kind = .By_Enum
        case len(inner) > 1 && inner[0] >= 'A' && inner[0] <= 'Z' && ask_shape_size(inner) < 0 && strings.to_upper(inner, context.temp_allocator) != inner:
            sh.kind = .By_Enum   // (`[Kind]T`: an enum's name — a constant's is written in capitals, `[MAX]T`: any size)
            sh.name = inner
        case:
            sh.kind = .List
            sh.size = ask_shape_size(inner)
        }
        sh.elem, rest, err = ask_shape_part(s[close + 1:])
        return
    }
    if s[0] == 'T' && (len(s) == 1 || !is_ident_byte(s[1])) {
        sh.kind = .Any
        return sh, s[1:], ""
    }
    end := 0
    for end < len(s) && (is_ident_byte(s[end]) || s[end] == '.') { end += 1 }
    if end == 0 { return sh, "", fmt.tprintf("'%s' isn't a type", s) }
    sh.kind = .Named
    sh.name = s[:end]
    return sh, s[end:], ""
}

@(private="file")
is_ident_byte :: proc(c: byte) -> bool {
    return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

// A size as a number; -1, any (a name: `N`, `MAX`).
@(private="file")
ask_shape_size :: proc(s: string) -> int {
    if n, ok := strconv.parse_int(s); ok && n >= 0 { return n }
    return -1
}

// --- matching a checked type -----------------------------------------------

// Whether a type is of the shape (through the names it has: an alias, a
// distinct type, both their own name and what they name).
ask_shape_matches :: proc(sh: ^Ask_Shape, t: Type) -> bool {
    if t == nil { return false }
    #partial switch sh.kind {
    case .Any:   return true
    case .Named: return ask_type_named(t, sh.name)
    }
    #partial switch v in distinct_base(t) {
    case ^Type_Partial_Array:
        return sh.kind == .List && (sh.size < 0 || sh.size == v.size) && ask_shape_matches(sh.elem, v.elem)
    case ^Type_Fixed_Array:
        if v.index_type != nil {
            return sh.kind == .By_Enum && (sh.name == "" || ask_type_named(v.index_type, sh.name)) && ask_shape_matches(sh.elem, v.elem)
        }
        return sh.kind == .Fixed && (sh.size < 0 || sh.size == v.size) && ask_shape_matches(sh.elem, v.elem)
    case ^Type_Slice:
        return sh.kind == .Slice && ask_shape_matches(sh.elem, v.elem)
    case ^Type_Ptr:
        return sh.kind == .Pointer && ask_shape_matches(sh.elem, v.elem)
    }
    return false
}

// Whether a type is of the shape, or a part of it is: an element, a pointee.
ask_shape_within :: proc(sh: ^Ask_Shape, t: Type) -> bool {
    if ask_shape_matches(sh, t) { return true }
    #partial switch v in distinct_base(t) {
    case ^Type_Partial_Array: return ask_shape_within(sh, v.elem)
    case ^Type_Fixed_Array:   return ask_shape_within(sh, v.elem)
    case ^Type_Slice:         return ask_shape_within(sh, v.elem)
    case ^Type_Ptr:           return ask_shape_within(sh, v.elem)
    }
    return false
}

// Whether a type goes by a name: its own, or, an alias or a distinct type,
// what it names'.
@(private="file")
ask_type_named :: proc(t: Type, name: string) -> bool {
    cur := t
    for cur != nil {
        if type_name(cur) == name || ask_source_name(cur) == name { return true }
        d, is_named := cur.(^Type_Distinct)
        if !is_named { return false }
        cur = d.base_type
    }
    return false
}

// --- matching a type as written ----------------------------------------------

// Whether a type node, as written, is of the shape: a list `[N]T` (unless N
// names an enum: `[Kind]T`), `[N!]T`, `[N I]T` (by I), `[]T`, `^T`; a size
// written as a number compared, any other only by `N`; an element by its
// text.
ask_shape_written :: proc(sh: ^Ask_Shape, rs: ^Resolver, n: Tree_Id) -> bool {
    t := &build_tree
    if n == 0 { return false }
    #partial switch sh.kind {
    case .Any:   return true
    case .Named: return ask_node_text(n) == sh.name
    }
    #partial switch t.tag[n] {
    case .Type_Pointer:
        return sh.kind == .Pointer && ask_shape_written(sh.elem, rs, Tree_Id(t.a[n]))
    case .Type_Slice:
        return sh.kind == .Slice && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
    case .Type_Partial:
        size := Tree_Id(t.a[n])
        if ask_size_names_enum(rs, size) {
            return sh.kind == .By_Enum && (sh.name == "" || ask_node_text(size) == sh.name) && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
        }
        return sh.kind == .List && ask_written_size(sh, size) && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
    case .Type_Array:
        r := tree_rec(t, t.a[n], 3)
        if r[1] != 0 {
            return sh.kind == .By_Enum && (sh.name == "" || ask_node_text(Tree_Id(r[1])) == sh.name) && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
        }
        if ask_size_names_enum(rs, Tree_Id(r[0])) {
            return sh.kind == .By_Enum && (sh.name == "" || ask_node_text(Tree_Id(r[0])) == sh.name) && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
        }
        return sh.kind == .Fixed && ask_written_size(sh, Tree_Id(r[0])) && ask_shape_written(sh.elem, rs, Tree_Id(t.b[n]))
    }
    return false
}

// Whether a size as written fits the shape's: any; else a number, the same.
@(private="file")
ask_written_size :: proc(sh: ^Ask_Shape, size: Tree_Id) -> bool {
    if sh.size < 0 { return true }
    if size == 0 || build_tree.tag[size] != .Number { return false }
    v, ok := strconv.parse_int(token_text(build_tokens[build_tree.main[size]]))
    return ok && v == sh.size
}

// Whether a size is a name that names an enum (`[Kind]T`) — a type's name,
// not a generic's size param (`$N`, written in a size: `[$N]T`).
@(private="file")
ask_size_names_enum :: proc(rs: ^Resolver, size: Tree_Id) -> bool {
    if rs == nil || size == 0 || build_tree.tag[size] != .Ident || int(size) >= len(rs.refs) { return false }
    ref := rs.refs[size]
    if ref.kind != .Type || ref.decl == 0 { return false }
    d := ref.decl
    if d > 0 && build_tokens[d - 1].kind == .Dollar {
        #partial switch build_tokens[d + 1].kind {
        case .Right_Bracket, .Bang: return false
        }
    }
    return true
}

// A node's source text, as written — each run of spaces one space.
ask_node_text :: proc(n: Tree_Id) -> string {
    t := &build_tree
    first, end := t.first[n], t.end[n]
    if end <= first { return "" }
    f := build_files[build_tokens[first].file]
    last := build_tokens[end - 1]
    lo, hi := int(build_tokens[first].offset), int(last.offset + last.len)
    if lo < 0 || hi > len(f.source) || lo >= hi { return "" }
    b := strings.builder_make(context.temp_allocator)
    space := false
    for c in transmute([]byte)f.source[lo:hi] {
        if c == ' ' || c == '\t' || c == '\r' || c == '\n' { space = true; continue }
        if space && strings.builder_len(b) > 0 { strings.write_byte(&b, ' ') }
        space = false
        strings.write_byte(&b, c)
    }
    return strings.to_string(b)
}

// The source line a token is on, trimmed.
@(private="file")
ask_line_of :: proc(tok: Token_Id) -> string {
    f := build_files[build_tokens[tok].file]
    at := int(build_tokens[tok].offset)
    lo, hi := at, at
    for lo > 0 && f.source[lo - 1] != '\n' { lo -= 1 }
    for hi < len(f.source) && f.source[hi] != '\n' && f.source[hi] != '\r' { hi += 1 }
    line := strings.trim_space(f.source[lo:hi])
    if len(line) > 72 { line = strings.concatenate({line[:69], "…"}, context.temp_allocator) }
    return line
}

// --- the query ---------------------------------------------------------------

Ask_Shape_Hit :: struct {
    span: Span,
    what: string,   // written: the type as written; declared: "name : type"
    note: string,   // written: its line; declared: what it is, and of what
}

// `mara ask <shape>`: where the shape is written, then what's declared of it,
// in `modules` (and `file`, when given), each in source order.
ask_shape_query :: proc(checked: ^Checked_Program, query: string, modules: map[string]bool, scope_desc, file: string) -> (out: string, ok: bool) {
    sh, err := ask_parse_shape(query)
    if err != "" {
        return fmt.tprintf("mara ask: '%s' isn't a shape: %s — e.g. `[N]T` a list, `[N!]T` exactly N, `[K]T` an enum's array, `[]T`, `^T`, `[64]utf8`\n", query, err), false
    }
    in_scope :: proc(span: Span, home: string, modules: map[string]bool, file: string) -> bool {
        if home not_in modules { return false }
        return file == "" || strings.has_suffix(span_file(span), file)
    }
    t := &build_tree
    written: [dynamic]Ask_Shape_Hit
    written.allocator = context.temp_allocator
    for i in 1 ..< len(t.tag) {
        n := Tree_Id(i)
        #partial switch t.tag[n] {
        case .Type_Partial, .Type_Array, .Type_Slice, .Type_Pointer:
        case:
            continue
        }
        span := Span{at = t.first[n], tok = t.first[n], end = t.end[n]}
        if span.at == 0 || !in_scope(span, build_files[build_tokens[span.at].file].module, modules, file) { continue }
        if !ask_shape_written(sh, checked.rs, n) { continue }
        append(&written, Ask_Shape_Hit{span = span, what = ask_node_text(n), note = ask_line_of(span.at)})
    }
    declared: [dynamic]Ask_Shape_Hit
    declared.allocator = context.temp_allocator
    add :: proc(out: ^[dynamic]Ask_Shape_Hit, sh: ^Ask_Shape, span: Span, name: string, t: Type, what: string) {
        if !ask_shape_within(sh, t) { return }
        append(out, Ask_Shape_Hit{span = span, what = fmt.tprintf("%s : %s", name, type_name(t)) if name != "" else type_name(t), note = what})
    }
    owned :: proc(ts: ^Type_Scope) -> bool {
        return ts != nil && (ts.source_name != "" || ask_is_foreign(ts))   // (an instance has none: its generic is written)
    }
    for _, ts in checked.functions {
        if !owned(ts) { continue }
        fspan := ask_span(ts)
        if !in_scope(fspan, ts.home_package, modules, file) { continue }
        fname := ts.source_name if ts.source_name != "" else ask_demangle(ts.name, ts.home_package)
        for p in ts.params {
            add(&declared, sh, Span{at = p.decl} if p.decl != 0 else fspan, p.name, p.type_, fmt.tprintf("param of %s", fname))
        }
        for r in ts.return_types { add(&declared, sh, fspan, "", r, fmt.tprintf("result of %s", fname)) }
        if checked.annot == nil { continue }
        for v in checked.annot.vars[ts] or_else nil {
            if v.kind != .Local || v.tok == 0 { continue }
            add(&declared, sh, Span{at = v.tok}, token_text(build_tokens[v.tok]), v.type_, fmt.tprintf("local in %s", fname))
        }
    }
    for m in ask_all_definitions(checked.table, "", checked.functions) {
        ts, is_scope := m.type_.(^Type_Scope)
        if !is_scope || ts.kind != .Struct || !owned(ts) || ask_is_variant(m.type_) { continue }
        if !in_scope(ask_span(ts), ts.home_package, modules, file) { continue }
        for f in ts.fields {
            add(&declared, sh, Span{at = f.decl} if f.decl != 0 else ask_span(ts), f.name, f.type_, fmt.tprintf("field of %s", ts.source_name))
        }
    }
    by_place :: proc(a, b: Ask_Shape_Hit) -> bool { return span_before(a.span, b.span) }
    slice.sort_by(written[:], by_place)
    slice.sort_by(declared[:], by_place)

    b := strings.builder_make()
    fmt.sbprintf(&b, "%s — %d written, %d declared   (%s)\n", query, len(written), len(declared), scope_desc)
    loc :: proc(s: Span) -> string { return fmt.tprintf("%s:%d:%d", span_file(s), span_line(s), span_col(s)) }
    if len(written) > 0 {
        fmt.sbprint(&b, "\n  written      (each type of the shape in the source, at its first character)\n")
        for h in written { fmt.sbprintf(&b, "    %-34s %-20s %s\n", loc(h.span), h.what, h.note) }
    }
    if len(declared) > 0 {
        fmt.sbprint(&b, "\n  declared     (each param, result, local, field whose type has one — written so or not)\n")
        for h in declared { fmt.sbprintf(&b, "    %-34s %-36s %s\n", loc(h.span), h.what, h.note) }
    }
    return strings.to_string(b), true
}
