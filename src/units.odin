package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// units.odin — a check that found errors: which definitions they break.
//
// A definition — a fun, a struct, a constant, a type — is a unit. Its head
// is what the rest of the program sees of it: a fun's params and results
// (all of a fun with a `~S` param); anything else, all of it. A fun's body is its own: nothing outside reads
// it. So an error breaks the definition it's written in — its head, or a
// fun's body — and a broken head breaks what names it, heads and bodies
// alike, and on from those. A broken body breaks nothing else — but what is
// defined in it, or in a broken struct, or in a file with an error in a
// statement of the module's own, goes with it: its code has nowhere to be
// placed. What isn't broken checked as it would have alone: it is lowered
// and answered from as ever (a tool's check — a build stops at any error).

Units :: struct {
    def:     []Token_Id,   // by token: the innermost definition it's written in, by its name's token (0: none — a module's own statement)
    in_body: []bool,       // ... and whether in that definition's body, a fun's
    head:    map[Token_Id]bool,   // the definitions whose head is broken: an error in it, or it names one
    body:    map[Token_Id]bool,   // the funs whose body is: an error in it, or it names a broken head
    outer:   map[Token_Id]Token_Id,   // each definition written in another's: that one
    loose:   map[u16]bool,        // the files with an error in a statement of the module's own
    via:     map[Token_Id]Token_Id,   // each definition broken by naming a broken head: that one
    met:     map[Token_Id]bool,       // the calls given the head they need (by the call's name's token)
}

// The definition an error at a token is in (0: none — a statement of its
// file's own, as the parser read it: one it took out of a definition can be
// within that definition's tokens).
units_home :: proc(u: ^Units, t: ^Tree, tok: Token_Id) -> Token_Id {
    for s in tree_list(t, t.a[t.files[build_tokens[tok].file]]) {
        if t.tag[s] != .Define && tok >= t.first[s] && tok < t.end[s] { return 0 }
    }
    return u.def[tok]
}

// The units a check's errors break — `errors`, the tokens they're at.
units_find :: proc(k: ^TC, errors: []Token_Id) -> ^Units {
    t := k.t
    u := new(Units)
    u.def = make([]Token_Id, len(build_tokens))
    u.in_body = make([]bool, len(build_tokens))
    // (A definition's nodes come before its own: the outer ones first, each
    // inner one over its part. A tree the parser read past an error into
    // can hold two definitions of one name's tokens: one is never the
    // other's outer — a chain that came back to its start would be walked
    // for ever: units_within.)
    #reverse for tag, i in t.tag {
        if tag != .Define { continue }
        s := Tree_Id(i)
        decl := t.main[s]
        if owner := u.def[t.first[s]]; owner != 0 && !units_within(u, owner, decl) { u.outer[decl] = owner }
        for tok in t.first[s] ..< t.end[s] { u.def[tok], u.in_body[tok] = decl, false }
        value := Tree_Id(t.b[s])
        if value == 0 || t.tag[value] != .Fun_Def { continue }
        // (A fun with a `~S` param: what its body uses of S is what a call
        // of it is checked against — its body is its head's.)
        if len(tc_tildes(k, value)) > 0 { continue }
        if body := scope_view(t, value).body; len(body) > 0 {
            for tok in t.first[body[0]] ..< t.end[body[len(body) - 1]] { u.in_body[tok] = true }
        }
    }
    // What names each definition: who, and whether from a body.
    User :: struct { def: Token_Id, in_body: bool }
    users := make(map[Token_Id][dynamic]User, context.temp_allocator)
    note :: proc(u: ^Units, users: ^map[Token_Id][dynamic]User, at, decl: Token_Id) {
        if decl == 0 || int(decl) >= len(u.def) || u.met[at] { return }
        target, user := u.def[decl], u.def[at]
        if target == 0 || user == 0 || target == user { return }
        if target not_in users { users[target] = make([dynamic]User, context.temp_allocator) }
        append(&users[target], User{user, u.in_body[at]})
    }
    // (A call checked against what it needs — requires.odin — names no head it depends on.)
    for sid, ts in k.annot.callees {
        if ts == nil { continue }
        if _, needed := ts.origin.(Origin_Required); needed {
            _, n := annot_split(sid)
            u.met[t.main[n]] = true
        }
    }
    // (As the name table found each name, as the checker settled it — a
    // field, a method — and each call's fun.)
    for r, n in k.names.refs { if r.decl != 0 { note(u, &users, t.main[n], r.decl) } }
    for tok, r in k.names.token_refs { note(u, &users, tok, r.decl) }
    a := k.annot
    for inst, i in a.instances {
        for r, at in a.refs[i] { if r.decl != 0 { note(u, &users, t.main[inst.lo + Tree_Id(at)], r.decl) } }
    }
    for sid, ts in a.callees {
        if _, n := annot_split(sid); ts != nil { note(u, &users, t.main[n], ts.decl) }
    }
    // The errors' own, then on from each broken head.
    broken := make([dynamic]Token_Id, context.temp_allocator)
    own := make(map[Token_Id]bool, context.temp_allocator)   // (those with an error of their own)
    for tok in errors {
        if tok == 0 || int(tok) >= len(u.def) { continue }
        d := units_home(u, t, tok)
        own[d] = true
        switch {
        case d == 0:          u.loose[build_tokens[tok].file] = true
        case u.in_body[tok]:  u.body[d] = true
        case !u.head[d]:      u.head[d] = true; append(&broken, d)
        }
    }
    for i := 0; i < len(broken); i += 1 {
        named := users[broken[i]] or_else nil   // (bound first: a loop over a map's missing entry crashes)
        for x in named {
            // (Of several it names, the first by place: the same one every check.)
            if !own[x.def] {
                if first, has := u.via[x.def]; !has || units_before(broken[i], first) { u.via[x.def] = broken[i] }
            }
            if x.in_body { u.body[x.def] = true; continue }
            if !u.head[x.def] { u.head[x.def] = true; append(&broken, x.def) }
        }
    }
    return u
}

// Whether definition `d` is `from` or one `from` is written in. Every walk
// out through u.outer stops after as many steps as it has entries: one that
// came back to its start would go round for ever.
@(private="file")
units_within :: proc(u: ^Units, from, d: Token_Id) -> bool {
    o := from
    for _ in 0 ..= len(u.outer) {
        if o == 0 { return false }
        if o == d { return true }
        o = u.outer[o] or_else 0
    }
    return false
}

// Whether the code written at a token is broken: its file's own statements,
// its definition, or one that definition is written in.
@(private="file")
units_broken_at :: proc(u: ^Units, tok: Token_Id) -> bool {
    if u.loose[build_tokens[tok].file] { return true }
    d := u.def[tok]
    for _ in 0 ..= len(u.outer) {
        if d == 0 { break }
        if u.head[d] || u.body[d] { return true }
        d = u.outer[d] or_else 0
    }
    return false
}

// Whether a scope's code is broken (u nil: nothing is).
units_broken :: proc(u: ^Units, t: ^Tree, sc: ^TC_Scope) -> bool {
    if u == nil || sc.node == 0 || t.tag[sc.node] == .Module_Scope { return false }
    return units_broken_at(u, t.first[sc.node])
}

// ... a constant's.
units_broken_const :: proc(u: ^Units, t: ^Tree, kc: ^TC_Const) -> bool {
    return u != nil && units_broken_at(u, t.main[kc.def])
}

// Whether a token comes before another as the report lists them: by its
// file's path, then its place in it; one at no token last.
@(private="file")
units_before :: proc(a, b: Token_Id) -> bool {
    if a == 0 || b == 0 { return a != 0 && b == 0 }
    fa, fb := build_tokens[a].file, build_tokens[b].file
    if fa != fb { return build_files[fa].path < build_files[fb].path }
    return a < b
}

// A definition's name, with those it's written in: `main.step`.
@(private="file")
units_name :: proc(u: ^Units, d: Token_Id) -> string {
    name := token_text(build_tokens[d])
    o := u.outer[d] or_else 0
    for _ in 0 ..= len(u.outer) {   // (units_within)
        if o == 0 { break }
        name = strings.concatenate({token_text(build_tokens[o]), ".", name}, context.temp_allocator)
        o = u.outer[o] or_else 0
    }
    return name
}

// What a tool's check says after an answer when it has errors: the scopes
// with errors that no answer comes from, each with its errors (three of
// them); the scopes left out with them, each using one whose head is
// broken; and the errors in scopes that answer all the same — found once
// they were lowered: a missing return, an escape.
units_report :: proc(k: ^TC, errors: []Diagnostic) -> string {
    t := k.t
    u := k.units
    if u == nil { u = units_find(k, nil) }   // (only lowering found errors: nothing is left out)
    Group :: struct { home: Token_Id, file: u16, out: bool, errors: [dynamic]Diagnostic }
    groups := make([dynamic]Group, context.temp_allocator)
    // (By file and place, whatever order the files were read in or the errors found.)
    errors := slice.clone(errors, context.temp_allocator)
    slice.stable_sort_by(errors, proc(x, y: Diagnostic) -> bool { return units_before(x.at, y.at) })
    for d in errors {
        home, file, out := Token_Id(0), u16(0), true
        if d.at != 0 {
            home, file = units_home(u, t, d.at), build_tokens[d.at].file
            out = k.units != nil && units_broken_at(u, d.at)
        }
        at := -1
        for g, i in groups { if g.home == home && g.file == file && g.out == out { at = i } }
        if at < 0 {
            at = len(groups)
            append(&groups, Group{home, file, out, make([dynamic]Diagnostic, context.temp_allocator)})
        }
        append(&groups[at].errors, d)
    }
    place :: proc(d: Token_Id) -> string { return ask_loc(Span{at = d, tok = d, end = d + 1}) }
    said :: proc(b: ^strings.Builder, u: ^Units, groups: []Group, out: bool, title: string) {
        first := true
        for g in groups {
            if g.out != out { continue }
            if first { strings.write_string(b, title); first = false }
            switch {
            case g.home != 0:           fmt.sbprintf(b, "  %s  %s\n", units_name(u, g.home), place(g.home))
            case len(g.errors) > 0 && g.errors[0].at != 0:
                fmt.sbprintf(b, "  %s, outside any definition: nothing in its file answers\n", ask_loc(Span{at = g.errors[0].at, tok = g.errors[0].at, end = g.errors[0].at + 1}))
            case:                       strings.write_string(b, "  the program\n")
            }
            for d, i in g.errors {
                if i == 3 { fmt.sbprintf(b, "    (and %d more)\n", len(g.errors) - 3); break }
                fmt.sbprintf(b, "    %s\n", diagnostic_line(d))
            }
        }
    }
    b := strings.builder_make()
    said(&b, u, groups[:], true, "\nscopes with errors — no answers from them:\n")
    with := make([dynamic]Token_Id, context.temp_allocator)
    for d in u.via { append(&with, d) }
    slice.sort_by(with[:], units_before)
    if len(with) > 0 { strings.write_string(&b, "left out with them — each uses one:\n") }
    for d in with { fmt.sbprintf(&b, "  %s  %s   (uses %s)\n", units_name(u, d), place(d), units_name(u, u.via[d])) }
    said(&b, u, groups[:], false, "\nerrors in scopes that answer all the same:\n")
    // (What calls need that nothing defines yet: requires.odin.)
    // (Each call's own need: two callers that need a name two ways are both listed.)
    needs :: proc(b: ^strings.Builder, k: ^TC, defined: bool, title: string) {
        first := true
        said := make(map[string]bool, context.temp_allocator)   // (two calls on a line that need the same: once)
        // (By file and place, whatever order the calls were checked in.)
        required := slice.clone(k.required[:], context.temp_allocator)
        slice.stable_sort_by(required, proc(x, y: Required) -> bool { return units_before(x.at.at, y.at.at) })
        for r in required {
            if (r.ft.origin.(Origin_Required).of != nil) != defined { continue }
            line := fmt.tprintf("  %s   %s", required_text(r.name, r.ft), ask_loc(r.at))
            if r.by != nil && r.by.source_name != "" { line = fmt.tprintf("%s, in %s", line, r.by.source_name) }
            if said[line] { continue }
            said[line] = true
            if first { strings.write_string(b, title); first = false }
            strings.write_string(b, line)
            strings.write_byte(b, '\n')
        }
    }
    needs(&b, k, false, "\nnot defined yet — needed as:\n")
    needs(&b, k, true, "\ncalled before its head checks — as:\n")
    return strings.to_string(b)
}
