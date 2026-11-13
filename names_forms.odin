package mara

import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Every form a name is written in, answered from the table (names_find): a
// name by itself, a call's, a qualified name's parts, a member, a type
// written, `Self`, a field reference's type, a name written as a token; why
// one means nothing; what a declaration runs into.
// ---------------------------------------------------------------------------

// What node n's name refers to, as written (Ref{}: nothing — why: names_miss).
// `base`: it qualifies another (`pkg.f()`), where a module's own name names
// the module.
names_ref :: proc(r: ^Resolver, n: Tree_Id, base := false) -> Ref {
    t := r.t
    #partial switch t.tag[n] {
    case .Ident:
        ref, ok, miss := names_find(r, rs_text(t.main[n]), t.main[n])
        if ok { return ref }
        if base && miss.hidden == "" && len(miss.owners) == 0 {
            if own, is_own := names_own_module(r, rs_text(t.main[n]), t.main[n]); is_own { return own }
        }
    case .Call:
        name := rs_text(t.main[n])
        if rs_builtin_call(name) { return {kind = .Builtin} }
        ref, _ := names_lookup(r, name, t.main[n])
        return ref
    case .Method_Call:
        mv := method_view(t, n)
        if ref, ok := names_member(r, mv.receiver, rs_text(mv.name)); ok { return ref }
    case .Field:
        q := Tree_Id(t.a[n])
        field := rs_text(Token_Id(t.b[n]))
        if ref, ok := names_member(r, q, field); ok { return ref }
        // (A module's, a struct's, a fun's enum's variant, by its name alone.)
        if t.tag[q] == .Ident || t.tag[q] == .Field {
            qref := names_base_ref(r, q)
            if rs_names_def(qref) {
                if _, has := names_members(r, qref); has {
                    if sp := rs_space_of(r, qref); sp != nil { if ref, found := sp.variants[field]; found { return ref } }
                }
            }
        }
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        if len(parts) == 0 { return {} }   // (a type missing where one was due: the parser said so)
        name := rs_text(parts[0])
        if len(parts) == 1 {
            if name == "Self" { ref, _ := names_self(r, parts[0]); return ref }
            if _, primitive := tc_primitive_named(name); primitive { return {kind = .Builtin} }
            ref, _ := names_lookup(r, name, parts[0])
            return ref
        }
        ref, _ := names_parts(r, parts)
        return ref
    case .Type_Keyword:
        return {kind = .Builtin}
    case .Type_Dollar:
        // (`$T` again: the first's — what declared it.)
        tok := Token_Id(t.a[n])
        ref, _ := names_lookup(r, rs_text(tok), tok)
        return ref
    case .Type_Of:
        ref, _ := names_parts(r, tree_token_list(t, t.a[n]))
        return ref
    case .Type_Generic:
        ref, _ := names_lookup(r, rs_text(t.main[n]), t.main[n])
        return ref
    }
    return {}
}

// Why node n's name means nothing: a local of a fun around, past its
// boundary; the scopes that each have it.
names_miss :: proc(r: ^Resolver, n: Tree_Id) -> Rs_Miss {
    t := r.t
    #partial switch t.tag[n] {
    case .Ident, .Type_Generic:
        _, ok, miss := names_find(r, rs_text(t.main[n]), t.main[n])
        if !ok { return miss }
    case .Call:
        name := rs_text(t.main[n])
        if rs_builtin_call(name) { return {} }
        _, ok, miss := names_find(r, name, t.main[n])
        if !ok { return miss }
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        if len(parts) == 0 { return {} }
        name := rs_text(parts[0])
        if len(parts) == 1 && (name == "Self" || tc_is_primitive_name(name)) { return {} }
        _, ok, miss := names_find(r, name, parts[0])
        if !ok { return miss }
    }
    return {}
}

@(private="file")
tc_is_primitive_name :: proc(name: string) -> bool {
    _, primitive := tc_primitive_named(name)
    return primitive
}

// A qualified name's base's ref: filled already (names_fill, in node order —
// a base before what it qualifies), else found.
@(private="file")
names_base_ref :: proc(r: ^Resolver, q: Tree_Id) -> Ref {
    if ref := r.refs[q]; ref.kind != .None { return ref }
    return names_ref(r, q, base = true)
}

// What a qualified name's base (a module, a type, a fun, by its name) has by
// `name`.
@(private="file")
names_member :: proc(r: ^Resolver, q: Tree_Id, name: string) -> (Ref, bool) {
    t := r.t
    if t.tag[q] != .Ident && t.tag[q] != .Field { return {}, false }
    qref := names_base_ref(r, q)
    if !rs_names_def(qref) { return {}, false }
    m, ok := names_members(r, qref)
    if !ok { return {}, false }
    ref, found := m[name]
    return ref, found
}

// A qualified name's parts (`a.b.c`): the first in sight — a module's own name
// as itself, when nothing in sight has it — each next one a member.
names_parts :: proc(r: ^Resolver, parts: []Token_Id) -> (ref: Ref, ok: bool) {
    if len(parts) == 0 { return }
    miss: Rs_Miss
    ref, ok, miss = names_find(r, rs_text(parts[0]), parts[0])
    if !ok && len(parts) > 1 && len(miss.owners) == 0 { ref, ok = names_own_module(r, rs_text(parts[0]), parts[0]) }
    for part in parts[1:] {
        if !ok { break }
        m, has := names_members(r, ref)
        if !has { return {}, false }
        ref, ok = m[rs_text(part)]
    }
    return
}

// A name written as a token (a dispatch's member, an `overload`'s fun, a
// method's name, `~Shape`, a qualified name's first part): what it refers to
// where it's written.
names_token_ref :: proc(r: ^Resolver, tok: Token_Id) -> Ref {
    name := rs_text(tok)
    ref, ok, miss := names_find(r, name, tok)
    if ok { return ref }
    // (A qualified name's first: its module's own name.)
    if int(tok) + 1 < len(build_tokens) && build_tokens[tok + 1].kind == .Dot && len(miss.owners) == 0 {
        if own, is_own := names_own_module(r, name, tok); is_own { return own }
    }
    return {}
}

// Why a name written as a token means nothing.
names_token_miss :: proc(r: ^Resolver, tok: Token_Id) -> Rs_Miss {
    _, ok, miss := names_find(r, rs_text(tok), tok)
    if ok { return {} }
    return miss
}

// A module's own name where `at` is, inside it (`pkg.helper()` in pkg).
names_own_module :: proc(r: ^Resolver, name: string, at: Token_Id) -> (Ref, bool) {
    for s := names_record_at(r, at); s != nil; s = s.parent {
        if s.kind != .Module { continue }
        if s.own == 0 || name != rs_text(s.own) { return {}, false }
        r.named[s.own] = s
        return {s.own, .Module}, true
    }
    return {}, false
}

// `Self` where `at` is: the innermost fun or struct whose body it's in (in a
// signature, the one around it).
names_self :: proc(r: ^Resolver, at: Token_Id) -> (Ref, bool) {
    for s := names_record_at(r, at); s != nil; s = s.parent {
        if (s.kind == .Fun || s.kind == .Struct) && s.decl != 0 && at >= s.body_lo {
            return {s.decl, .Variant if s.variant else .Type}, true
        }
    }
    return {}, false
}

// What a qualified name reaches in a definition (`A.B`, `m.f`, `Color.Red`):
// a module's definitions; a struct's own (its body's); a fun's nested ones; a
// union's or an error set's variants; a distinct type's or an alias's, its
// base's.
names_members :: proc(r: ^Resolver, ref: Ref) -> (map[string]Ref, bool) {
    if sp := rs_space_of(r, ref); sp != nil { return sp.defs, true }
    if ref.kind == .Module || ref.decl == 0 { return nil, false }
    if m, made := r.members[ref.decl]; made { return m, true }
    if _, ok := r.defs[ref.decl]; !ok { return nil, false }
    t := r.t
    value := Tree_Id(t.b[r.defs[r.alias_of[ref.decl] or_else ref.decl]])
    m := make(map[string]Ref)
    #partial switch t.tag[value] {
    case .Union_Def:
        for vr in tree_list(t, t.b[value]) { m[rs_text(t.main[vr])] = {t.main[vr], .Variant} }
    case .Error_Def:
        for tok in tree_token_list(t, t.a[value]) { m[rs_text(tok)] = {tok, .Variant} }
    case .Distinct_Def, .Alias_Def:
        base := Tree_Id(t.a[value])
        if t.tag[base] != .Type_Name { return nil, false }
        bref := r.refs[base] if r.refs[base].kind != .None else names_ref(r, base)
        if bref.kind == .None || bref.decl == ref.decl { return nil, false }
        return names_members(r, bref)
    case:
        return nil, false
    }
    r.members[ref.decl] = m
    return m, true
}

// A field reference's type written as a value (`for f in Binds.Combos`) or a
// type (`Event_State.Mouse`): what owns the field, the field's type, where in
// the name's parts it starts.
names_field_type :: proc(r: ^Resolver, n: Tree_Id) -> (Rs_Field_Type, bool) {
    t := r.t
    #partial switch t.tag[n] {
    case .Field:
        q := Tree_Id(t.a[n])
        field := rs_text(Token_Id(t.b[n]))
        if t.tag[q] != .Ident && t.tag[q] != .Field { return {}, false }
        qref := names_base_ref(r, q)
        if !rs_names_def(qref) { return {}, false }
        m, ok := names_members(r, qref)
        if !ok { return {}, false }
        if _, found := m[field]; found { return {}, false }
        if sp := rs_space_of(r, qref); sp != nil { if _, found := sp.variants[field]; found { return {}, false } }
        if qref.kind != .Type { return {}, false }
        if elem, has := names_lookup(r, field, Token_Id(t.b[n])); has && elem.kind == .Type { return {qref, elem, 0}, true }
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        if len(parts) < 2 { return {}, false }
        if _, ok := names_parts(r, parts); ok { return {}, false }
        for split in 1 ..< len(parts) {
            owner, has := names_parts(r, parts[:split])
            if !has || owner.kind != .Type { continue }
            elem: Ref
            found := false
            if tc_is_primitive_name(rs_text(parts[split])) && split == len(parts) - 1 {
                elem, found = {kind = .Builtin}, true
            } else {
                elem, found = names_parts(r, parts[split:])
                found = found && elem.kind == .Type
            }
            if found { return {owner, elem, split}, true }
        }
    }
    return {}, false
}

// What declaring a variable runs into where it's declared (rs_clash's): a
// name its level has already (a param's, said apart); one around it it would
// hide (before: what declares it); a constant, a fun, a type or a module of
// its name in sight. A param or a named result: a fun, a type or a module it
// would hide.
names_clash :: proc(r: ^Resolver, v: Name_Var, body: ^Scope) -> (c: Rs_Clash) {
    name := v.name
    at := v.ref.decl
    if name == "_" { return }
    found, ok, miss := names_find(r, name, at)
    if v.ref.kind == .Param || v.ref.kind == .Result {
        if ok {
            #partial switch found.kind { case .Fun, .Type, .Module: c.hides = found }
        }
        return
    }
    // (Nothing of its name in sight: it runs into nothing.)
    if !ok && len(miss.owners) == 0 { return }
    // (The nearest thing of its name in sight: a variable of its body, or a
    // definition — whichever came in sight later.)
    near: ^Name_Var
    for &x in body.vars {
        if x.slot == v.slot && x.ref.decl != at && x.from <= at && (x.to == 0 || at < x.to) && (near == nil || x.from > near.from) { near = &x }
    }
    def: Ref
    def_sc: ^Scope
    for s := names_record_at(r, at); s != nil && def_sc == nil; s = s.parent {
        if x, has := s.declared[name]; has { def, def_sc = x, s; break }
        if x, has := s.defs[name]; has {
            def, def_sc = x, s
            if def.kind == .Const && r.type_names[def.decl] { def.kind = .Type }
            if len(s.dups[name]) > 0 { def = {} }   // (defined there twice: the name means neither)
            break
        }
        if x, has := s.params[name]; has { def, def_sc = x, s; break }
        if s.kind == .Module && (name == "std" || name == "void") { def, def_sc = {kind = .Builtin}, s; break }
    }
    use_var := near != nil && (def_sc == nil || near.from > def_sc.text_lo)
    if use_var || def_sc != nil {
        outermost := !use_var && (def_sc.kind == .Module || def_sc.kind == .File && def.kind != .Module)
        if !outermost {
            level := near.level if use_var else def_sc.level
            kind := near.ref.kind if use_var else def.kind
            if level == v.level && (v.level_kind == .Block || use_var || kind == .Const) {
                c.taken, c.param = true, kind == .Param
                return
            }
            c.before, c.shadows = near.ref.decl if use_var else def.decl, true
        }
    }
    ref := found if ok else miss.first
    #partial switch ref.kind {
    case .Const:              c.constant = true
    case .Fun, .Type, .Module: c.hides = ref
    }
    return
}

// What every name written means, from the records the walk made: each
// node's, why one means nothing, a field reference's type, each name written
// as a token, each declaration's clash — the tables the checker and the tools
// read. (A declaration's own name the walk gave already.) mara lsp's
// completion: the names in sight where its placeholder is.
names_fill :: proc(r: ^Resolver) {
    t := r.t
    // (A name that qualifies another: a module's own name may name it.)
    base := make([]bool, len(t.tag), context.temp_allocator)
    for n in 1 ..< len(t.tag) {
        #partial switch t.tag[n] {
        case .Field:       base[Tree_Id(t.a[n])] = true
        case .Method_Call: base[method_view(t, Tree_Id(n)).receiver] = true
        }
    }
    token :: proc(r: ^Resolver, tok: Token_Id, plain: bool) {
        if tok == 0 { return }
        if ref := names_token_ref(r, tok); ref.kind != .None {
            r.token_refs[tok] = ref
        } else if plain {
            if m := names_token_miss(r, tok); m.hidden != "" || len(m.owners) > 0 { r.token_misses[tok] = m }
        }
    }
    for n in 1 ..< len(t.tag) {
        nid := Tree_Id(n)
        if resolve_completing && !r.captured && t.main[nid] != 0 && strings.contains(rs_text(t.main[nid]), COMPLETE_HERE) { names_capture(r, t.main[nid]) }
        #partial switch t.tag[nid] {
        case .Ident, .Call, .Method_Call, .Field, .Type_Name, .Type_Keyword, .Type_Dollar, .Type_Of, .Type_Generic:
            if r.refs[nid].kind != .None { continue }
            ref := names_ref(r, nid, base[nid])
            r.refs[nid] = ref
            if ref.kind == .None {
                #partial switch t.tag[nid] {
                case .Ident, .Call, .Type_Name, .Type_Generic:
                    if m := names_miss(r, nid); m.hidden != "" || len(m.owners) > 0 { r.misses[nid] = m }
                }
            }
            #partial switch t.tag[nid] {
            case .Field, .Type_Name:
                if ft, ok := names_field_type(r, nid); ok { r.field_types[nid] = ft }
            }
            #partial switch t.tag[nid] {
            case .Type_Name:
                if parts := tree_token_list(t, t.a[nid]); len(parts) > 1 { token(r, parts[0], false) }
            case .Type_Of:
                if parts := tree_token_list(t, t.a[nid]); len(parts) > 0 { token(r, parts[0], false) }
            case .Method_Call:
                if ref.kind == .None { token(r, method_view(t, nid).name, true) }
            }
        case .Dispatch_Def:
            for tok in tree_token_list(t, t.a[nid]) { token(r, tok, true) }   // (its members)
        case .Overload:
            token(r, Token_Id(t.b[nid]), true)   // (the dispatch's or the fun's name)
        case .Type_Tilde:
            token(r, Token_Id(t.a[nid]), true)   // (`~Shape`: the shape)
        }
    }
    // (What each declaration runs into.)
    for sc in r.records {
        for v in sc.vars {
            if !v.clashes { continue }
            c := names_clash(r, v, sc)
            keep := c.hides.kind != .None if v.ref.kind != .Local else c.taken || c.before != 0 || c.constant || c.hides.kind != .None
            if keep { r.clashes[v.ref.decl] = c }
        }
    }
}

// mara lsp's completion: the names in sight at `at` — each name's nearest,
// then what the scopes out from there use.
names_capture :: proc(r: ^Resolver, at: Token_Id) {
    r.captured = true
    here := names_record_at(r, at)
    if here == nil { return }
    seen := make(map[string]bool, context.temp_allocator)
    if body := names_body_of(here); body != nil {
        vars := make([dynamic]Name_Var, context.temp_allocator)
        for x in body.vars { if x.from <= at && (x.to == 0 || at < x.to) { append(&vars, x) } }
        slice.sort_by(vars[:], proc(a, b: Name_Var) -> bool { return a.from > b.from })
        for x in vars {
            if x.name in seen { continue }
            seen[x.name] = true
            append(&r.in_sight, Rs_Seen{x.name, x.ref})
        }
    }
    for s := here; s != nil; s = s.parent {
        for name, ref in s.declared { if name not_in seen { seen[name] = true; append(&r.in_sight, Rs_Seen{name, ref}) } }
        for name, ref in s.defs { if name not_in seen { seen[name] = true; append(&r.in_sight, Rs_Seen{name, ref}) } }
        for name, ref in s.params { if name not_in seen { seen[name] = true; append(&r.in_sight, Rs_Seen{name, ref}) } }
        if s.kind == .Module {
            for b in ([]string{"std", "void"}) { if b not_in seen { seen[b] = true; append(&r.in_sight, Rs_Seen{b, {kind = .Builtin}}) } }
        }
    }
    for s := here; s != nil; s = s.parent {
        for u in s.uses {
            for name, ref in u.defs { if name not_in seen { seen[name] = true; append(&r.in_sight, Rs_Seen{name, ref}) } }
        }
    }
}
