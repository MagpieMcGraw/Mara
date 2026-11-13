package mara

import "core:fmt"
import "core:os"
import "core:slice"

// ---------------------------------------------------------------------------
// What a name means at a point of the text, asked of the scopes' records —
// what each defines and uses, the scope around it — and of the variables the
// checker binds as it goes: each in sight from where it's declared to its
// block's end, in its fun's, struct's or file's body alone.
//
// Stage 1: the records are the resolver's, and nothing reads the answers but
// MARA_NAMES=check, which compares them with the resolver's for every name
// checked.
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
}

// A variable bound in a block not closed yet: its body's record, its place.
Names_Open :: struct {
    sc: ^Scope,
    at: int,
}

// (MARA_NAMES=check: the variables kept, the answers compared.)
names_checking: bool

// The innermost record whose text holds `at` (nil: none).
names_record_at :: proc(r: ^Resolver, at: Token_Id) -> ^Scope {
    if !r.records_sorted {
        keep := make([dynamic]^Scope, 0, len(r.records), r.allocator)
        for sc in r.records { if sc.text_hi > sc.text_lo { append(&keep, sc) } }
        slice.sort_by(keep[:], proc(a, b: ^Scope) -> bool { return a.text_lo < b.text_lo || a.text_lo == b.text_lo && a.text_hi > b.text_hi })
        r.records = keep
        r.records_sorted = true
    }
    // (The last to start at or before it — else a scope around that one.)
    lo, hi := 0, len(r.records)
    for lo < hi {
        mid := (lo + hi) / 2
        if r.records[mid].text_lo <= at { lo = mid + 1 } else { hi = mid }
    }
    if lo == 0 { return nil }
    for sc := r.records[lo - 1]; sc != nil && sc.text_hi != 0; sc = sc.parent {
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

// Something a name could mean where it's asked: what it refers to, whose it
// is (the fun's or the struct's it's in, else the module's; a use's, the
// scope it brings), where it came in sight (later: nearer).
@(private="file")
Names_Seen :: struct {
    ref:   Ref,
    owner: string,
    at:    Token_Id,
    block: bool,     // defined or brought in a block's record
}

// Whose a scope's names are: the fun's or the struct's it's in, else its
// module's.
names_owner :: proc(sc: ^Scope) -> string {
    for s := sc; s != nil; s = s.parent {
        #partial switch s.kind { case .Fun, .Struct, .File, .Module: return s.name }
    }
    return ""
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
    // (Its body's variables in sight, nearest first.)
    vars := make([dynamic]^Name_Var, context.temp_allocator)
    if body != nil {
        for &x in body.vars {
            if x.name == name && x.from <= at && (x.to == 0 || at < x.to) { append(&vars, &x) }
        }
        slice.sort_by(vars[:], proc(a, b: ^Name_Var) -> bool { return a.from > b.from })
    }
    defs := make([dynamic]Names_Seen, context.temp_allocator)    // defined out from here, nearest first
    used := make([dynamic]Names_Seen, context.temp_allocator)    // brought by uses ...
    used_level := make([dynamic]int, context.temp_allocator)     // ... and which scope out from here's
    level := 0
    for s := here; s != nil; s = s.parent {
        owner := names_owner(s)
        block := s.kind == .Block
        if x, has := s.declared[name]; has { append(&defs, Names_Seen{x, owner, s.text_lo, block}) }
        if x, has := s.defs[name]; has {
            x := x
            if x.kind == .Const && r.type_names[x.decl] { x.kind = .Type }
            append(&defs, Names_Seen{x, owner, s.text_lo, block})
            // (Defined there more than once: each.)
            earlier := s.dups[name]   // (bound first: a loop over a map's entry is unsafe in Odin)
            for d in earlier {
                d := d
                if d.kind == .Const && r.type_names[d.decl] { d.kind = .Type }
                append(&defs, Names_Seen{d, owner, s.text_lo, block})
            }
        }
        if x, has := s.params[name]; has { append(&defs, Names_Seen{x, owner, s.text_lo, block}) }
        if s.kind == .Module && (name == "std" || name == "void") { append(&defs, Names_Seen{Ref{kind = .Builtin}, owner, 0, false}) }
        any := false
        for u in s.uses {
            if x, has := u.defs[name]; has {
                append(&used, Names_Seen{x, u.name, s.text_lo, block})
                append(&used_level, level)
                any = true
            }
        }
        if any { level += 1 }
    }
    // (A local of a fun or a struct around: out of sight past its boundary.)
    outer: ^Name_Var
    if body != nil {
        for s := names_body_of(body.parent); s != nil && outer == nil; s = names_body_of(s.parent) {
            for &x in s.vars {
                if x.name == name && x.from <= at && (x.to == 0 || at < x.to) && (outer == nil || x.from > outer.from) { outer = &x }
            }
            if outer != nil { miss.hidden = names_owner(s) }
        }
    }
    // (Two things in sight: what each is, whose — nearest first, each once.)
    conflict :: proc(r: ^Resolver, miss: ^Rs_Miss, vars: []^Name_Var, body: ^Scope, defs, used: []Names_Seen) {
        owners := make([dynamic]string)
        add :: proc(miss: ^Rs_Miss, owners: ^[dynamic]string, owner: string, ref: Ref) {
            if miss.first.kind == .None { miss.first = ref }
            if owner != "" && !slice.contains(owners[:], owner) { append(owners, owner) }
        }
        seen := make([dynamic]Names_Seen, context.temp_allocator)
        for v in vars { append(&seen, Names_Seen{v.ref, names_owner(body), v.from, false}) }
        append(&seen, ..defs)
        slice.stable_sort_by(seen[:], proc(a, b: Names_Seen) -> bool { return a.at > b.at })
        for x in seen { add(miss, &owners, x.owner, x.ref) }
        for x in used { add(miss, &owners, x.owner, x.ref) }
        miss.owners = owners[:]
    }
    if len(vars) > 0 {
        v := vars[0]
        // (Defined or brought in a block entered after it: the two conflict.)
        for x in defs { if x.block && x.at > v.from && !rs_shares(r, v.ref, x.ref) { miss.hidden = ""; conflict(r, &miss, vars[:], body, defs[:], used[:]); return } }
        for x in used { if x.block && x.at > v.from && !rs_shares(r, v.ref, x.ref) { miss.hidden = ""; conflict(r, &miss, vars[:], body, defs[:], used[:]); return } }
        return v.ref, true, {}
    }
    // (A conflict is met where the later of the two came in sight: a local of
    // a fun around, past its boundary, is said only if it came after.)
    past :: proc(miss: ^Rs_Miss, outer: ^Name_Var, at: Token_Id) { if outer == nil || outer.from <= at { miss.hidden = "" } }
    if len(defs) > 0 {
        first := defs[0]
        for x in defs[1:] { if !rs_shares(r, first.ref, x.ref) { past(&miss, outer, max(first.at, x.at)); conflict(r, &miss, nil, body, defs[:], used[:]); return } }
        for x in used { if !rs_shares(r, first.ref, x.ref) { past(&miss, outer, max(first.at, x.at)); conflict(r, &miss, nil, body, defs[:], used[:]); return } }
        return first.ref, true, {}
    }
    if len(used) == 0 { return }
    first := used[0].ref
    for x, i in used { if used_level[i] > 0 && !rs_shares(r, first, x.ref) { past(&miss, outer, max(used[0].at, x.at)); conflict(r, &miss, nil, body, nil, used[:]); return } }
    // (The nearest scope's uses: one thing of the name, else none — dispatch
    // groups the checker's to choose among.)
    groups := true
    unlike := make([dynamic]Names_Seen, context.temp_allocator)
    for x, i in used {
        if used_level[i] > 0 { break }
        one := false
        for d in unlike { one = one || rs_same(r, d.ref, x.ref) }
        if one { continue }
        append(&unlike, x)
        groups = groups && x.ref.kind == .Fun && r.dispatches[x.ref.decl]
    }
    if len(unlike) == 1 { return first, true, {} }
    if !groups {
        owners := make([dynamic]string)
        for d in unlike { if !slice.contains(owners[:], d.owner) { append(&owners, d.owner) } }
        miss.owners, miss.first = owners[:], unlike[0].ref
    }
    return
}

// What `name` means where `at` is (names_find, without why not).
names_lookup :: proc(r: ^Resolver, name: string, at: Token_Id) -> (Ref, bool) {
    ref, ok, _ := names_find(r, name, at)
    return ref, ok
}

// --- the check ----------------------------------------------------------------------

// MARA_NAMES=check: each name the resolver's walk reached, asked of the table
// — what it refers to, why it means nothing, a field reference's type — and
// each name written as a token, each declaration's clash, against what the
// resolver found. One line a disagreement (the first few), then counts by what.
names_check :: proc(k: ^TC) {
    if !names_checking { return }
    r := k.rs
    t := k.t
    y := Names_Tally{by = make(map[string]int, allocator = context.temp_allocator)}
    // (A name that qualifies another: a module's own name may name it.)
    base := make([]bool, len(t.tag), context.temp_allocator)
    for n in 1 ..< len(t.tag) {
        #partial switch t.tag[n] {
        case .Field:       base[Tree_Id(t.a[n])] = true
        case .Method_Call: base[method_view(t, Tree_Id(n)).receiver] = true
        }
    }
    for n in 1 ..< len(t.tag) {
        nid := Tree_Id(n)
        if !r.visited[nid] { continue }   // (a dead `#if` arm's)
        at := t.main[nid] if t.main[nid] != 0 else t.first[nid]
        #partial switch t.tag[nid] {
        case .Ident, .Call, .Method_Call, .Field, .Type_Name, .Type_Keyword, .Type_Dollar, .Type_Of, .Type_Generic:
            want := r.refs[nid]
            if t.tag[nid] == .Ident && want.decl == t.main[nid] { continue }   // (a declaration's own name: no use)
            names_tally(&y, fmt.tprint(t.tag[nid]), at, tc_text(t.main[nid]), want == names_ref(r, nid, base[nid]), want, names_ref(r, nid, base[nid]))
            #partial switch t.tag[nid] {
            case .Ident, .Call, .Type_Name, .Type_Generic:
                if want.kind == .None {
                    wm := r.misses[nid] or_else Rs_Miss{}
                    gm := names_miss(r, nid)
                    names_tally(&y, fmt.tprintf("%v miss", t.tag[nid]), at, tc_text(t.main[nid]), names_miss_same(wm, gm), wm.first, gm.first, wm, gm)
                }
            }
            #partial switch t.tag[nid] {
            case .Field, .Type_Name:
                wf, wok := r.field_types[nid]
                gf, gok := names_field_type(r, nid)
                names_tally(&y, fmt.tprintf("%v field type", t.tag[nid]), at, tc_text(t.main[nid]), wok == gok && wf == gf, wf.elem, gf.elem)
            }
        }
    }
    for tok, want in r.token_refs {
        names_tally(&y, "token", tok, tc_text(tok), want == names_token_ref(r, tok), want, names_token_ref(r, tok))
    }
    for tok, want in r.token_misses {
        got := names_token_miss(r, tok)
        names_tally(&y, "token miss", tok, tc_text(tok), names_miss_same(want, got), want.first, got.first, want, got)
    }
    for sc in names_vars_of(r) {
        for v in sc.vars {
            if !v.clashes { continue }
            want := r.clashes[v.ref.decl] or_else Rs_Clash{}
            got := names_clash(r, v, sc)
            // (A `:=`'s is kept only when it runs into something.)
            if v.ref.kind == .Local && !(got.taken || got.before != 0 || got.constant || got.hides.kind != .None) { got = {} }
            if v.ref.kind != .Local && got.hides.kind == .None { got = {} }
            names_tally(&y, fmt.tprintf("%v clash", v.ref.kind), v.ref.decl, v.name, want == got, want.hides, got.hides, clash = [2]Rs_Clash{want, got})
        }
    }
    fmt.printfln("names: %d agree, %d differ", y.agree, y.differ)
    keys := make([dynamic]string, context.temp_allocator)
    for key in y.by { append(&keys, key) }
    slice.sort(keys[:])
    for key in keys { fmt.printfln("names: differ %s: %d", key, y.by[key]) }
}

@(private="file")
Names_Tally :: struct {
    agree, differ: int,
    by: map[string]int,
}

@(private="file")
names_tally :: proc(y: ^Names_Tally, what: string, at: Token_Id, name: string, same: bool, want, got: Ref, wm: Rs_Miss = {}, gm: Rs_Miss = {}, clash: [2]Rs_Clash = {}) {
    if same { y.agree += 1; return }
    y.differ += 1
    y.by[what] += 1
    if y.differ > 60 { return }
    sp := Span{at = at, tok = at, end = at + 1}
    fmt.printfln("names: %s:%d: %s `%s`: resolver %v %s, names %v %s", span_file(sp), span_line(sp), what, name,
                 want.kind, names_where(want.decl), got.kind, names_where(got.decl))
    if wm.hidden != "" || gm.hidden != "" || len(wm.owners) + len(gm.owners) > 0 {
        fmt.printfln("names:     miss: resolver hidden %q owners %v, names hidden %q owners %v", wm.hidden, wm.owners, gm.hidden, gm.owners)
    }
    if clash[0] != clash[1] { fmt.printfln("names:     clash: resolver %v, names %v", clash[0], clash[1]) }
}

@(private="file")
names_miss_same :: proc(a, b: Rs_Miss) -> bool {
    return a.hidden == b.hidden && a.first == b.first && slice.equal(a.owners, b.owners)
}

// Whether a token is some module's own name as it names itself (rs_own_module's).
@(private="file")
resolve_module_own_any :: proc(r: ^Resolver, tok: Token_Id) -> Token_Id {
    for _, m in r.modules { if m.own == tok { return tok } }
    return 0
}

@(private="file")
names_builtin_call :: proc(name: string) -> bool {
    switch name {
    case "print", "crash", "int", "uint", "print_cstr", "print_int", "print_float", "len", "cap", "slice_from_ptr", "cstring",
         "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "f16", "f32", "f64", "utf8", "bool":
        return true
    }
    return false
}

@(private="file")
names_where :: proc(tok: Token_Id) -> string {
    if tok == 0 { return "-" }
    sp := token_span(build_tokens[tok])
    return fmt.tprintf("%s:%d", span_file(sp), span_line(sp))
}

// (MARA_NAMES read once a check.)
names_check_begin :: proc() {
    names_checking = os.get_env("MARA_NAMES", context.temp_allocator) == "check"
}

