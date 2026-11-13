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

// --- the checker's side -----------------------------------------------------------------

names_enter :: proc(k: ^TC) {
    if !names_checking { return }
    append(&k.names_levels, len(k.names_open))
}

// A block closed at `end`: its variables are out of sight from there.
names_leave :: proc(k: ^TC, end: Token_Id) {
    if !names_checking { return }
    mark := pop(&k.names_levels)
    for o in k.names_open[mark:] { o.sc.vars[o.at].to = end }
    resize(&k.names_open, mark)
}

// A variable bound (tc_bind): in sight from k.names_from, else past the
// statement that declares it. (An instance binds it again: kept once.)
names_bind :: proc(k: ^TC, name: string, ref: Ref) {
    if !names_checking || ref.decl == 0 || name == "_" { return }
    body := names_body_of(names_record_at(k.rs, ref.decl))
    if body == nil { return }
    at, seen := body.var_at[ref.decl]
    if !seen {
        from := k.names_from
        if from == 0 { from = k.t.end[k.names_stmt] if k.names_stmt != 0 else ref.decl + 1 }
        append(&body.vars, Name_Var{name, ref, from, 0})
        at = len(body.vars) - 1
        body.var_at[ref.decl] = at
    }
    append(&k.names_open, Names_Open{body, at})
}

// A body checked: its names compared (names_check).
names_body_checked :: proc(k: ^TC, node: Tree_Id) {
    if !names_checking || node == 0 || k.t.first[node] == 0 { return }
    if body := names_body_of(names_record_at(k.rs, k.t.first[node])); body != nil { body.checked = true }
}

// --- the answer -----------------------------------------------------------------------

// What `name` means where `at` is: a variable in sight, else what the scopes
// out from there define or bring by a use. Two things of one name in sight are
// neither (nothing hides anything) — but a variable declared beside what's in
// sight already is itself from there on (that it hides it is said where it's
// declared).
names_lookup :: proc(r: ^Resolver, name: string, at: Token_Id) -> (Ref, bool) {
    here := names_record_at(r, at)
    if here == nil { return {}, false }
    // (The innermost variable in sight.)
    v: ^Name_Var
    if body := names_body_of(here); body != nil {
        for &x in body.vars {
            if x.name == name && x.from <= at && (x.to == 0 || at < x.to) && (v == nil || x.from > v.from) { v = &x }
        }
    }
    defined := make([dynamic]Ref, context.temp_allocator)   // what the scopes out from here define, innermost first
    def_lo := Token_Id(0)                                    // ... where the innermost of them starts
    used_levels := 0
    first_used: [dynamic]Ref                                 // the innermost scope's uses' that have it
    first_used = make([dynamic]Ref, context.temp_allocator)
    others := make([dynamic]Ref, context.temp_allocator)     // the outer scopes' uses'
    for s := here; s != nil; s = s.parent {
        one :: proc(r: ^Resolver, s: ^Scope, ref: Ref, defined: ^[dynamic]Ref, def_lo: ^Token_Id, v: ^Name_Var) -> bool {
            ref := ref
            if ref.kind == .Const && r.type_names[ref.decl] { ref.kind = .Type }
            // (Defined in a block entered after the variable: they conflict.)
            if v != nil {
                return !(s.kind == .Block && s.text_lo > v.from && !rs_shares(r, v.ref, ref))
            }
            if len(defined) == 0 { def_lo^ = s.text_lo }
            append(defined, ref)
            return true
        }
        if ref, ok := s.params[name]; ok { if !one(r, s, ref, &defined, &def_lo, v) { return {}, false } }
        if ref, ok := s.declared[name]; ok { if !one(r, s, ref, &defined, &def_lo, v) { return {}, false } }
        if ref, ok := s.defs[name]; ok { if !one(r, s, ref, &defined, &def_lo, v) { return {}, false } }
        level := false
        for u in s.uses {
            ref, ok := u.defs[name]
            if !ok { continue }
            if v != nil {
                if s.kind == .Block && s.text_lo > v.from && !rs_shares(r, v.ref, ref) { return {}, false }
                continue
            }
            if used_levels == 0 { append(&first_used, ref) } else { append(&others, ref) }
            level = true
        }
        if level { used_levels += 1 }
        if s.kind == .Module && (name == "std" || name == "void") && v == nil { append(&defined, Ref{kind = .Builtin}) }
    }
    if v != nil { return v.ref, true }
    // (Two of one name in sight: neither — unless they're one, or dispatch
    // groups, which join.)
    if len(defined) > 0 {
        first := defined[0]
        for x in defined[1:] { if !rs_shares(r, first, x) { return {}, false } }
        for x in first_used { if !rs_shares(r, first, x) { return {}, false } }
        for x in others { if !rs_shares(r, first, x) { return {}, false } }
        return first, true
    }
    if len(first_used) == 0 { return {}, false }
    first := first_used[0]
    for x in others { if !rs_shares(r, first, x) { return {}, false } }
    // (The innermost scope's uses: one thing of the name, else none.)
    for x in first_used[1:] { if !rs_same(r, first, x) { return {}, false } }
    return first, true
}

// --- the check (stage 1) -------------------------------------------------------------

// MARA_NAMES=check: what each name checked means, asked as above, against
// what the resolver found it to — one line a disagreement (the first few),
// then counts.
names_check :: proc(k: ^TC) {
    if !names_checking || k.c.errors > 0 { return }
    r := k.rs
    t := k.t
    agree, differ := 0, 0
    differ_by := make(map[string]int, allocator = context.temp_allocator)
    compare :: proc(r: ^Resolver, what: string, at: Token_Id, name: string, want: Ref, agree, differ: ^int, by: ^map[string]int) {
        sc := names_record_at(r, at)
        body := names_body_of(sc)
        if body == nil || !body.checked { return }
        got, _ := names_lookup(r, name, at)
        if got == want { agree^ += 1; return }
        differ^ += 1
        key := fmt.tprintf("%s: resolver %v, names %v", what, want.kind, got.kind)
        by[key] += 1
        if differ^ <= 40 {
            sp := Span{at = at, tok = at, end = at + 1}
            fmt.printfln("names: %s:%d: %s `%s`: resolver %v %s, names %v %s", span_file(sp), span_line(sp), what, name,
                         want.kind, names_where(want.decl), got.kind, names_where(got.decl))
        }
    }
    for n in 1 ..< len(t.tag) {
        nid := Tree_Id(n)
        if !r.visited[nid] { continue }   // (a dead `#if` arm's)
        #partial switch t.tag[nid] {
        case .Ident:
            if r.refs[nid].decl == t.main[nid] { continue }   // (a declaration's own name: no use)
            if r.refs[nid].kind == .Module && r.refs[nid].decl == resolve_module_own_any(r, r.refs[nid].decl) { continue }   // (a module's own name inside itself)
            compare(r, "Ident", t.main[nid], tc_text(t.main[nid]), r.refs[nid], &agree, &differ, &differ_by)
        case .Call:
            name := tc_text(t.main[nid])
            if names_builtin_call(name) { continue }
            compare(r, "Call", t.main[nid], name, r.refs[nid], &agree, &differ, &differ_by)
        case .Type_Name:
            parts := tree_token_list(t, t.a[nid])
            if len(parts) != 1 { continue }
            name := tc_text(parts[0])
            if name == "Self" { continue }
            if _, primitive := tc_primitive_named(name); primitive { continue }
            compare(r, "Type_Name", parts[0], name, r.refs[nid], &agree, &differ, &differ_by)
        case .Type_Generic:
            compare(r, "Type_Generic", t.main[nid], tc_text(t.main[nid]), r.refs[nid], &agree, &differ, &differ_by)
        case .Type_Dollar:
            tok := Token_Id(t.a[nid])
            compare(r, "Type_Dollar", tok, tc_text(tok), r.refs[nid], &agree, &differ, &differ_by)
        }
    }
    for tok, want in r.token_refs {
        if want.kind == .Module && want.decl == resolve_module_own_any(r, want.decl) { continue }
        compare(r, "token", tok, tc_text(tok), want, &agree, &differ, &differ_by)
    }
    fmt.printfln("names: %d agree, %d differ", agree, differ)
    keys := make([dynamic]string, context.temp_allocator)
    for key in differ_by { append(&keys, key) }
    slice.sort(keys[:])
    for key in keys { fmt.printfln("names: differ %s: %d", key, differ_by[key]) }
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

// Where a block's names are in sight from: its first statement (else `none`).
names_from_body :: proc(k: ^TC, body: []Tree_Id, none: Token_Id = 0) -> Token_Id {
    if len(body) > 0 { return k.t.first[body[0]] }
    return none
}
