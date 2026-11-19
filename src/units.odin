package mara

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
}

// The units a check's errors break — `errors`, the tokens they're at.
units_find :: proc(k: ^TC, errors: []Token_Id) -> ^Units {
    t := k.t
    u := new(Units)
    u.def = make([]Token_Id, len(build_tokens))
    u.in_body = make([]bool, len(build_tokens))
    // (A definition's nodes come before its own: the outer ones first, each
    // inner one over its part.)
    #reverse for tag, i in t.tag {
        if tag != .Define { continue }
        s := Tree_Id(i)
        decl := t.main[s]
        if owner := u.def[t.first[s]]; owner != 0 { u.outer[decl] = owner }
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
        if decl == 0 || int(decl) >= len(u.def) { return }
        target, user := u.def[decl], u.def[at]
        if target == 0 || user == 0 || target == user { return }
        if target not_in users { users[target] = make([dynamic]User, context.temp_allocator) }
        append(&users[target], User{user, u.in_body[at]})
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
    for tok in errors {
        if tok == 0 || int(tok) >= len(u.def) { continue }
        d := u.def[tok]
        // (In a statement of its file's own, as the parser read it — one it
        // took for a definition's can be within that definition's tokens.)
        file := build_tokens[tok].file
        for s in tree_list(t, t.a[t.files[file]]) {
            if t.tag[s] != .Define && tok >= t.first[s] && tok < t.end[s] { d = 0 }
        }
        switch {
        case d == 0:          u.loose[file] = true
        case u.in_body[tok]:  u.body[d] = true
        case !u.head[d]:      u.head[d] = true; append(&broken, d)
        }
    }
    for i := 0; i < len(broken); i += 1 {
        named := users[broken[i]] or_else nil   // (bound first: a loop over a map's missing entry crashes)
        for x in named {
            if x.in_body { u.body[x.def] = true; continue }
            if !u.head[x.def] { u.head[x.def] = true; append(&broken, x.def) }
        }
    }
    return u
}

// Whether the code written at a token is broken: its file's own statements,
// its definition, or one that definition is written in.
@(private="file")
units_broken_at :: proc(u: ^Units, tok: Token_Id) -> bool {
    if u.loose[build_tokens[tok].file] { return true }
    for d := u.def[tok]; d != 0; d = u.outer[d] or_else 0 {
        if u.head[d] || u.body[d] { return true }
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
