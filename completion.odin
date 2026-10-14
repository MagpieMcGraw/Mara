package mara

import "core:strings"

// ---------------------------------------------------------------------------
// Completion (mara lsp): the names that can be written at a point. The
// editor's text has a placeholder name typed in at the point — COMPLETE_HERE,
// after whatever of the name is typed already — so it parses, and the check
// of that text says what the placeholder is. A field's name, after `x.`:
// x's type's members — a struct's fields and methods, a module's names, a
// union's or an enum's variants, a slice's len and cap. Else a name: what the
// resolver had in sight at the placeholder (resolve_completing) — the
// variables declared before it, the params, what the scopes out to the
// module define and use — and the keywords.
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
        completion_members(&c, checked, completion_type_of(a, Tree_Id(t.a[inner])))
        return c.out[:]
    }

    // A name: what's in sight where it's written.
    if checked != nil && checked.rs != nil {
        for seen in checked.rs.in_sight { completion_named(&c, checked, seen.name, seen.ref) }
    }
    for kw in COMPLETION_KEYWORDS { completion_add(&c, kw, .Keyword, "") }
    return c.out[:]
}

// A name in sight, by what it refers to: its kind, its type (a fun's
// signature).
completion_named :: proc(c: ^Completions, checked: ^Checked_Program, name: string, ref: Ref) {
    t, _ := checked_binding(checked, ref, name)
    kind := Completion_Kind.Type
    #partial switch ref.kind {
    case .Local, .Param, .Result, .Field, .Global, .Const: kind = .Variable
    case .Fun:     kind = .Function
    case .Module:  kind = .Module
    case .Variant: kind = .Variant
    }
    fs, is_scope := t.(^Type_Scope)
    if is_scope && fs.is_module { kind = .Module }
    if is_scope && kind == .Function && fs.kind != .Fun { kind = .Type }   // (a struct's constructor: the struct)
    detail := ""
    if t != nil { detail = completion_signature(fs) if is_scope && kind == .Function else type_name(t) }
    completion_add(c, name, kind, detail)
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
completion_members :: proc(c: ^Completions, checked: ^Checked_Program, typ: Type) {
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
        if v.is_module {
            // (A module's names: its definitions, the resolver's.)
            if checked != nil && checked.rs != nil {
                for name, ref in resolve_module_defs(checked.rs, v.name) { completion_named(c, checked, name, ref) }
            }
            break
        }
        for f in v.fields { completion_add(c, f.name, .Field, type_name(f.type_)) }
        completion_scope_names(c, v, methods = true)
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

// The funs and types a struct defines (`methods`: as its, called on a value
// of it).
completion_scope_names :: proc(c: ^Completions, s: ^Type_Scope, methods := false) {
    if s == nil { return }
    {
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

