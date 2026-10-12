package mara

import "core:strings"

// ---------------------------------------------------------------------------
// Completion (mara lsp): the names that can be written at a point. The
// editor's text has a placeholder name typed in at the point — COMPLETE_HERE,
// after whatever of the name is typed already — so it parses, and the check
// of that text says what the placeholder is. A field's name, after `x.`:
// x's type's members — a struct's fields and methods, a module's names, a
// union's or an enum's variants, a slice's len and cap. Else a name: the
// variables its fun declares before it, its params, then the names its fun's
// enclosing scopes define — its struct's, its file's, its module's — and
// what the modules used there export, and the keywords.
// ---------------------------------------------------------------------------

COMPLETE_HERE :: "mara_complete_here"

Completion_Kind :: enum {
    Field,
    Method,
    Function,
    Variable,
    Type,
    Module,
    Variant,
    Keyword,
}

Completion :: struct {
    label:  string,
    kind:   Completion_Kind,
    detail: string,   // its type; a fun's signature
}

COMPLETION_KEYWORDS :: [?]string{
    "fun", "struct", "union", "enum", "error", "distinct", "use", "include", "module",
    "if", "elif", "else", "for", "in", "match", "do", "return", "break", "continue", "defer",
    "and", "or", "not", "void", "true", "false",
}

// What can be written where the placeholder is, in a check of the text with
// it typed in: `spec`, its place, <file>:<line>:<col>.
completions_at :: proc(t: ^Tree, all_files: map[string][dynamic]^Source_File, a: ^Annotations,
                       checked: ^Checked_Program, module: string, spec: string) -> []Completion {
    hits, at, ok := point_hits(t, all_files, spec)
    if !ok || len(hits) == 0 { return nil }
    c := Completions{seen = make(map[string]bool, allocator = context.temp_allocator)}
    c.out.allocator = context.temp_allocator
    inner := hits[len(hits) - 1]

    // `x.|`: x's type's members.
    if t.tag[inner] == .Field && Token_Id(t.b[inner]) == at {
        completion_members(&c, completion_type_of(a, Tree_Id(t.a[inner])))
        return c.out[:]
    }

    // A name: its fun's variables before it, its params; then what its
    // scopes, out to its module's, define and use.
    scope := completion_scope(a, inner)
    if scope != nil {
        // (Bound first: ranging over a missing key straight from the map faults.)
        vars, _ := a.vars[scope]
        for v in vars {
            if v.tok != 0 && v.tok < at { completion_add(&c, token_text(build_tokens[v.tok]), .Variable, type_name(v.type_)) }
        }
        for p in scope.params { completion_add(&c, p.name, .Variable, type_name(p.type_)) }
    }
    s := scope
    if s == nil { s = completion_module_scope(checked, module) }
    // (A block's names are its locals, said already — but its uses, a file's,
    // count: names resolve through every scope's, as scope_includes_lookup.)
    for ; s != nil; s = s.parent_scope {
        if s.kind != .Block { completion_scope_names(&c, s) }
        for inc in s.includes {
            if inc != nil { completion_scope_names(&c, sd_type_scope(inc), exports_only = true) }
        }
    }
    for kw in COMPLETION_KEYWORDS { completion_add(&c, kw, .Keyword, "") }
    return c.out[:]
}

Completions :: struct {
    out:  [dynamic]Completion,
    seen: map[string]bool,
}

// A name added, once: none of the compiler's own (`__tag`), not the placeholder.
completion_add :: proc(c: ^Completions, label: string, kind: Completion_Kind, detail: string) {
    if label == "" || label in c.seen || strings.has_prefix(label, "__") || strings.contains(label, COMPLETE_HERE) { return }
    c.seen[label] = true
    append(&c.out, Completion{label, kind, detail})
}

// A type's members, through pointers and distinct types to what has some.
completion_members :: proc(c: ^Completions, typ: Type) {
    t := typ
    for {
        #partial switch v in t {
        case ^Type_Ptr:      t = v.elem; continue
        case ^Type_Distinct: t = v.base_type; continue
        }
        break
    }
    #partial switch v in t {
    case ^Type_Scope:
        for f in v.fields { completion_add(c, f.name, .Field, type_name(f.type_)) }
        completion_scope_names(c, v, methods = !v.is_module)
    case ^Type_Union:
        for name in v.variants { completion_add(c, name, .Variant, "") }
    case ^Type_Enum:
        for name in v.variants { completion_add(c, name, .Variant, "") }
    case ^Type_Slice:
        completion_add(c, "len", .Field, "i64")
        completion_add(c, "cap", .Field, "i64")
    case ^Type_Partial_Array:
        completion_add(c, "len", .Field, "i64")
        completion_add(c, "cap", .Field, "i64")
    case ^Type_Fixed_Array:
        completion_add(c, "len", .Field, "i64")
    }
}

// The funs and types a scope defines (`methods`: as a struct's, called on
// a value of it) — a module's exports alone when `exports_only`.
completion_scope_names :: proc(c: ^Completions, s: ^Type_Scope, methods := false, exports_only := false) {
    if s == nil { return }
    if !exports_only {
        for name, fn in s.functions {
            // (A fun's own name only: not the flat one a nested fun's filed under too.)
            if fn == nil || fn.source_name != "" && name != fn.source_name { continue }
            kind := Completion_Kind.Method if methods else .Function
            if fn.kind != .Fun { kind = .Type }   // (a struct's constructor: the struct)
            completion_add(c, name, kind, completion_signature(fn))
        }
    }
    for name, ty in s.types {
        // (A nested fun's or struct's flat name, filed here too: not its own.)
        if fs, is_scope := ty.(^Type_Scope); is_scope && !fs.is_module && fs.source_name != "" && name != fs.source_name { continue }
        kind := Completion_Kind.Type
        #partial switch v in ty {
        case ^Type_Scope:
            if v.is_module { kind = .Module } else if v.kind == .Fun { kind = .Function }
        }
        detail := type_name(ty)
        if fs, is_scope := ty.(^Type_Scope); is_scope && kind == .Function { detail = completion_signature(fs) }
        completion_add(c, name, kind, detail)
    }
}

// A fun as its signature reads: fun(a: T, b: U) -> R.
completion_signature :: proc(fn: ^Type_Scope) -> string {
    if fn == nil { return "" }
    if fn.kind != .Fun { return type_name(fn) }
    b := strings.builder_make()
    strings.write_string(&b, "fun(")
    for p, i in fn.params {
        if i > 0 { strings.write_string(&b, ", ") }
        if p.name != "" {
            strings.write_string(&b, p.name)
            strings.write_string(&b, ": ")
        }
        strings.write_string(&b, type_name(p.type_))
    }
    strings.write_string(&b, ")")
    for r, i in fn.return_types {
        strings.write_string(&b, " -> " if i == 0 else ", ")
        strings.write_string(&b, type_name(r))
    }
    return strings.to_string(b)
}

// A node's type, in the first instance it's checked in that types it.
completion_type_of :: proc(a: ^Annotations, n: Tree_Id) -> Type {
    for inst, i in a.instances {
        if n < inst.lo || n > inst.hi { continue }
        if t := annot_type(a, Instance_Id(i), n); t != nil { return t }
    }
    return nil
}

// The fun or struct a node is written in: the innermost body checked that
// holds it.
completion_scope :: proc(a: ^Annotations, n: Tree_Id) -> ^Type_Scope {
    best: ^Type_Scope
    best_width := max(int)
    for b in a.bodies {
        if b.scope == nil || n < b.lo || n > b.hi { continue }
        if w := int(b.hi - b.lo); w < best_width {
            best, best_width = b.scope, w
        }
    }
    return best
}

// A module's own scope, for a name written outside any fun: one of its
// funs' — its scopes out to the module's.
completion_module_scope :: proc(checked: ^Checked_Program, module: string) -> ^Type_Scope {
    if checked == nil { return nil }
    flat, _ := strings.replace_all(module, ".", "_", context.temp_allocator)
    for _, fn in checked.functions {
        if fn == nil || fn.home_package != flat { continue }
        for s := fn.parent_scope; s != nil; s = s.parent_scope {
            if s.is_module { return s }
        }
    }
    return nil
}
