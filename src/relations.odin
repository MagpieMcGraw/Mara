package mara

// ---------------------------------------------------------------------------
// The program's relations, the other way round.
//
// The checker records what each node means one way: what a name refers to
// (Annotations.refs), what a call calls (Annotations.callees). What a pass or
// a tool asks is often the other way: what refers to this declaration, what
// calls this fun. Each such question has one answer here, found from the
// checker's record the first time it is asked and kept with the check (mara
// serve's and mara lsp's checks stay between questions). A tool builds no
// index of its own: it asks.
// ---------------------------------------------------------------------------

// A name that refers to a declaration: its node, in the instance it was
// checked in.
Use :: struct {
    inst: Instance_Id,
    node: Tree_Id,
}

// Every name that refers to what the token `decl` declares — a.refs, the
// other way round — in the order checked: an instance at a time, each one's
// nodes in order. (A generic's body is checked once an instance: a name in it
// is there once for each.)
annot_uses :: proc(a: ^Annotations, decl: Token_Id) -> []Use {
    if a.uses_first == nil { annot_uses_build(a) }
    if decl == 0 || int(decl) + 1 >= len(a.uses_first) { return nil }
    return a.uses[a.uses_first[decl]:a.uses_first[decl + 1]]
}

// What a use refers to, as checked there.
annot_use_ref :: proc(a: ^Annotations, u: Use) -> Ref {
    return a.refs[u.inst][u.node - a.instances[u.inst].lo]
}

// The uses, grouped by declaration: where each declaration's begin (by its
// token; one past the last, the end), then the uses themselves.
@(private="file")
annot_uses_build :: proc(a: ^Annotations) {
    first := make([]u32, len(build_tokens) + 2, a.allocator)
    total := 0
    for refs in a.refs {
        for r in refs {
            if r.decl == 0 { continue }
            first[r.decl + 1] += 1
            total += 1
        }
    }
    for i in 1 ..< len(first) { first[i] += first[i - 1] }
    uses := make([]Use, total, a.allocator)
    next := make([]u32, len(first), context.temp_allocator)
    copy(next, first)
    for inst, i in a.instances {
        for r, k in a.refs[i] {
            if r.decl == 0 { continue }
            uses[next[r.decl]] = {Instance_Id(i), inst.lo + Tree_Id(k)}
            next[r.decl] += 1
        }
    }
    a.uses_first, a.uses = first, uses
}
