package mara

import "core:slice"

// ---------------------------------------------------------------------------
// What a name means at a point of the text, asked of the scopes' records —
// what each defines and uses, the scope around it — and of the variables the
// checker binds as it goes: each in sight from where it's declared to its
// block's end, in its fun's, struct's or file's body alone.
//
// The records are made by the resolver's walk over the statements; what each
// name written means is filled in from them once it's done (names_fill).
// ---------------------------------------------------------------------------

// A variable as the checker binds it: in sight from `from` up to before `to`
// (0: its block isn't closed yet).
Name_Var :: struct {
    name:     string,
    ref:      Ref,
    from, to: Token_Id,
    level:    int,             // the level it's declared at (Rs_Level.id), and its kind
    level_kind: Rs_Scope_Kind,
    clashes:  bool,            // what it runs into is said where it's declared (names_clash): a `:=`'s, a loop's, a param's, a result's
    slot:     i32,             // its name's number (Resolver.slots): what's compared
}

// A variable bound in a block not closed yet: its body's record, its place.
Names_Open :: struct {
    sc: ^Scope,
    at: int,
}

// The innermost record whose text holds `at` (nil: none).
names_record_at :: proc(r: ^Resolver, at: Token_Id) -> ^Scope {
    if !r.records_sorted {
        keep := make([dynamic]^Scope, 0, len(r.records), r.allocator)
        for sc in r.records { if sc.text_hi > sc.text_lo { append(&keep, sc) } }
        slice.sort_by(keep[:], proc(a, b: ^Scope) -> bool { return a.text_lo < b.text_lo || a.text_lo == b.text_lo && a.text_hi > b.text_hi })
        r.records = keep
        r.record_lo = make([]Token_Id, len(keep), r.allocator)
        for sc, i in keep { r.record_lo[i] = sc.text_lo }
        r.records_sorted = true
    }
    // (The last to start at or before it — where the last ask's did, when it's
    // still that one; else searched — then the scopes around it.)
    los := r.record_lo
    i := r.record_last
    if !(i < len(los) && los[i] <= at && (i + 1 == len(los) || los[i + 1] > at)) {
        lo, hi := 0, len(los)
        for lo < hi {
            mid := (lo + hi) / 2
            if los[mid] <= at { lo = mid + 1 } else { hi = mid }
        }
        if lo == 0 { return nil }
        i = lo - 1
        r.record_last = i
    }
    for sc := r.records[i]; sc != nil && sc.text_hi != 0; sc = sc.parent {
        if at >= sc.text_lo && at < sc.text_hi { return sc }
    }
    return nil
}

// The body whose variables are in sight in a scope: its fun's, its struct's,
// its file's.
names_body_of :: proc(sc: ^Scope) -> ^Scope {
    for s := sc; s != nil; s = s.parent {
        #partial switch s.kind { case .Fun, .Struct, .File: return s }
    }
    return nil
}

// --- the answer -----------------------------------------------------------------------

// Something a name could mean where it's asked: what it refers to, the scope
// whose it is (a use's: the scope it brings), where it came in sight (later:
// nearer), whether a block's record has it, which scope out from here's uses
// bring it (0: the nearest's that bring any).
Names_Seen :: struct {
    ref:   Ref,
    sc:    ^Scope,
    use:   ^Scope,
    at:    Token_Id,
    block: bool,
    level: int,
}

// Whose a scope's names are: the fun's or the struct's it's in, else its
// module's.
names_owner :: proc(sc: ^Scope) -> string {
    for s := sc; s != nil; s = s.parent {
        #partial switch s.kind { case .Fun, .Struct, .File, .Module: return s.name }
    }
    return ""
}

@(private="file")
names_seen_owner :: proc(x: Names_Seen) -> string {
    return x.use.name if x.use != nil else names_owner(x.sc)
}

// The nearest variable named by `slot` in sight at `at` in a body (nil: none).
names_nearest_var :: proc(body: ^Scope, slot: i32, at: Token_Id) -> ^Name_Var {
    if body == nil || slot < 0 { return nil }
    v: ^Name_Var
    for &x in body.vars {
        if x.slot == slot && x.from <= at && (x.to == 0 || at < x.to) && (v == nil || x.from > v.from) { v = &x }
    }
    return v
}

// A local of a fun or a struct around the body, of a name in sight at `at`
// past its boundary: whose it is, and where it came in sight.
@(private="file")
names_outer :: proc(body: ^Scope, slot: i32, at: Token_Id) -> (string, ^Name_Var) {
    if body == nil { return "", nil }
    for s := names_body_of(body.parent); s != nil; s = names_body_of(s.parent) {
        if v := names_nearest_var(s, slot, at); v != nil { return names_owner(s), v }
    }
    return "", nil
}

// What a scope defines of a name and what its uses bring (`level`: how many
// scopes nearer bring some): into defs and used. The level after it.
@(private="file")
names_gather :: proc(r: ^Resolver, s: ^Scope, name: string, defs, used: ^[dynamic]Names_Seen, level: int) -> int {
    block := s.kind == .Block
    if x, has := s.declared[name]; has { append(defs, Names_Seen{ref = x, sc = s, at = s.text_lo, block = block}) }
    if x, has := s.defs[name]; has {
        x := x
        if x.kind == .Const && r.type_names[x.decl] { x.kind = .Type }
        append(defs, Names_Seen{ref = x, sc = s, at = s.text_lo, block = block})
        // (Defined there more than once: each.)
        if len(s.dups) > 0 {
            earlier := s.dups[name]   // (bound first: a loop over a map's entry is unsafe in Odin)
            for d in earlier {
                d := d
                if d.kind == .Const && r.type_names[d.decl] { d.kind = .Type }
                append(defs, Names_Seen{ref = d, sc = s, at = s.text_lo, block = block})
            }
        }
    }
    if x, has := s.params[name]; has { append(defs, Names_Seen{ref = x, sc = s, at = s.text_lo, block = block}) }
    if s.kind == .Module && (name == "std" || name == "void") { append(defs, Names_Seen{ref = {kind = .Builtin}, sc = s}) }
    any := false
    for u in s.uses {
        if x, has := u.defs[name]; has {
            append(used, Names_Seen{ref = x, sc = s, use = u, at = s.text_lo, block = block, level = level})
            any = true
        }
    }
    return level + 1 if any else level
}

// What a file's scope and its module's see of a name, as a scope inside it
// gathers it (levels from the file's), kept.
Names_Key :: struct {
    sc:   ^Scope,
    slot: i32,
}
Names_Memo :: struct {
    defs, used: []Names_Seen,
}

@(private="file")
names_memo :: proc(r: ^Resolver, sc: ^Scope, name: string, slot: i32) -> Names_Memo {
    key := Names_Key{sc, slot}
    if slot >= 0 { if m, ok := r.sight_memo[key]; ok { return m } }
    defs := make([dynamic]Names_Seen, 0, 2, r.allocator)
    used := make([dynamic]Names_Seen, 0, 2, r.allocator)
    level := 0
    for s := sc; s != nil; s = s.parent { level = names_gather(r, s, name, &defs, &used, level) }
    m := Names_Memo{defs[:], used[:]}
    if slot >= 0 { r.sight_memo[key] = m }
    return m
}

// What `name` means where `at` is: a variable in sight, else what the scopes
// out from there define or bring by a use. Two things of one name in sight are
// neither (nothing hides anything) — but a variable declared beside what's in
// sight already is itself from there on (that it hides it is said where it's
// declared). Nothing: why — a local of a fun around, past its boundary; the
// scopes that each have it.
names_find :: proc(r: ^Resolver, name: string, at: Token_Id) -> (ref: Ref, ok: bool, miss: Rs_Miss) {
    here := names_record_at(r, at)
    if here == nil { return }
    body := names_body_of(here)
    slot := r.slots[name] or_else -1   // (none: nothing anywhere is named so)
    v := names_nearest_var(body, slot, at)
    defs := &r.seen_defs   // (defined out from here, nearest first)
    used := &r.seen_used   // (brought by uses, nearest first)
    clear(defs)
    clear(used)
    if v != nil {
        // (A variable in sight: it's the name, unless a block entered after it
        // defines or brings the name too — the blocks out to its body alone.)
        level := 0
        for s := here; s != nil && s != body; s = s.parent {
            if s.kind == .Block && s.text_lo > v.from { level = names_gather(r, s, name, defs, used, level) }
        }
        for x in defs { if !rs_shares(r, v.ref, x.ref) { return {}, false, names_conflict_all(r, here, body, name, slot, at) } }
        for x in used { if !rs_shares(r, v.ref, x.ref) { return {}, false, names_conflict_all(r, here, body, name, slot, at) } }
        return v.ref, true, {}
    }
    level := 0
    for s := here; s != nil; s = s.parent {
        // (A file's scope and its module's: the same for every name asked in
        // the file, found once.)
        if s.kind == .File || s.kind == .Module {
            m := names_memo(r, s, name, slot)
            append(defs, ..m.defs)
            for x in m.used {
                x := x
                x.level += level
                append(used, x)
            }
            break
        }
        level = names_gather(r, s, name, defs, used, level)
    }
    // (A conflict is met where the later of the two came in sight: a local of
    // a fun around, past its boundary, is said only if it came after.)
    past :: proc(r: ^Resolver, body: ^Scope, name: string, slot: i32, at, met: Token_Id) -> Rs_Miss {
        miss := names_conflict(r, body, slot, at, false)
        if hidden, outer := names_outer(body, slot, at); outer != nil && outer.from > met { miss.hidden = hidden }
        return miss
    }
    if len(defs) > 0 {
        first := defs[0]
        for x in defs[1:] { if !rs_shares(r, first.ref, x.ref) { return {}, false, past(r, body, name, slot, at, max(first.at, x.at)) } }
        for x in used { if !rs_shares(r, first.ref, x.ref) { return {}, false, past(r, body, name, slot, at, max(first.at, x.at)) } }
        return first.ref, true, {}
    }
    if len(used) == 0 {
        miss.hidden, _ = names_outer(body, slot, at)
        return
    }
    first := used[0]
    for x in used { if x.level > 0 && !rs_shares(r, first.ref, x.ref) { return {}, false, past(r, body, name, slot, at, max(first.at, x.at)) } }
    // (The nearest scope's uses: one thing of the name, else none — dispatch
    // groups the checker's to choose among.)
    groups := true
    unlike := 0
    for x, i in used {
        if x.level > 0 { break }
        one := false
        for d in used[:i] { one = one || rs_same(r, d.ref, x.ref) }
        if one { continue }
        unlike += 1
        groups = groups && x.ref.kind == .Fun && r.dispatches[x.ref.decl]
    }
    if unlike == 1 { return first.ref, true, {} }
    miss.hidden, _ = names_outer(body, slot, at)
    if !groups {
        owners := make([dynamic]string)
        for x, i in used {
            if x.level > 0 { break }
            one := false
            for d in used[:i] { one = one || rs_same(r, d.ref, x.ref) }
            if one { continue }
            if miss.first.kind == .None { miss.first = x.ref }
            if !slice.contains(owners[:], x.use.name) { append(&owners, x.use.name) }
        }
        miss.owners = owners[:]
    }
    return
}

// A variable's conflict: everything of the name in sight, gathered whole
// first (names_find stopped at the variable's body).
@(private="file")
names_conflict_all :: proc(r: ^Resolver, here, body: ^Scope, name: string, slot: i32, at: Token_Id) -> Rs_Miss {
    defs := &r.seen_defs
    used := &r.seen_used
    clear(defs)
    clear(used)
    level := 0
    for s := here; s != nil; s = s.parent { level = names_gather(r, s, name, defs, used, level) }
    return names_conflict(r, body, slot, at, true)
}

// Two things of a name in sight: what each is, whose — nearest first, each once
// (from the scratch names_find left: what's defined and brought).
@(private="file")
names_conflict :: proc(r: ^Resolver, body: ^Scope, slot: i32, at: Token_Id, with_vars: bool) -> (miss: Rs_Miss) {
    owners := make([dynamic]string)
    add :: proc(miss: ^Rs_Miss, owners: ^[dynamic]string, owner: string, ref: Ref) {
        if miss.first.kind == .None { miss.first = ref }
        if owner != "" && !slice.contains(owners[:], owner) { append(owners, owner) }
    }
    seen := make([dynamic]Names_Seen, context.temp_allocator)
    if with_vars && body != nil {
        for x in body.vars {
            if x.slot == slot && x.from <= at && (x.to == 0 || at < x.to) { append(&seen, Names_Seen{ref = x.ref, sc = body, at = x.from}) }
        }
    }
    append(&seen, ..r.seen_defs[:])
    slice.stable_sort_by(seen[:], proc(a, b: Names_Seen) -> bool { return a.at > b.at })
    for x in seen { add(&miss, &owners, names_seen_owner(x), x.ref) }
    for x in r.seen_used { add(&miss, &owners, names_seen_owner(x), x.ref) }
    miss.owners = owners[:]
    return
}

// What `name` means where `at` is (names_find, without why not).
names_lookup :: proc(r: ^Resolver, name: string, at: Token_Id) -> (Ref, bool) {
    ref, ok, _ := names_find(r, name, at)
    return ref, ok
}

