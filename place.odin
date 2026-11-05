package mara

import "core:slice"

// ---------------------------------------------------------------------------
// Which value a field's use is on, for `mara ask what at` (hittest.odin).
//
// A place is a variable and the fields down from it. `game.timers.work`, in a
// fun whose `game` param is given `&game` by game_run, is game_run's local
// `game`, then timers, then work. `timer.work` is the same place when the local
// `timer` was given `&game.timers`.
//
// A value is its own variable. A local holding a pointer or a slice is followed
// to what it's given, and a param to what its calls pass. Order isn't looked at:
// a variable given two things may be either, and a use on it counts for both.
//
// What can't be followed makes a place loose: a pointer or slice held in a field,
// or returned by a call, and the params of a fun used as a value. A loose place
// may be another value of its type too, so a use on one is only a maybe.
// ---------------------------------------------------------------------------

Place :: struct {
    root:   Token_Id,     // the variable's declaration, a fresh value's first token, PLACE_EVERY, or 0 for none known
    fields: []Token_Id,   // the fields down from it, by their declarations
    loose:  bool,
}

// The root of a place in a struct's own body and what it passes on as `#self`:
// it runs for every value of the struct.
PLACE_EVERY :: max(Token_Id)

// What a variable was given: a node in an instance; 0 for what can't be followed.
Place_Given :: struct {
    node: Tree_Id,
    inst: Instance_Id,
}

Place_Finder :: struct {
    t:     ^Tree,
    a:     ^Annotations,
    given: map[Token_Id][dynamic]Place_Given,
    memo:  map[Token_Id][]Place,
    busy:  map[Token_Id]bool,
}

Place_Match :: enum { No, Maybe, Yes }

PLACE_MOST :: 64   // more places than this for one variable, and it's treated as unknown

@(private="file")
place_one :: proc(root: Token_Id, fields: []Token_Id = nil, loose := false) -> []Place {
    out := make([]Place, 1, context.temp_allocator)
    out[0] = Place{root, fields, loose}
    return out
}

@(private="file")
place_unknown :: proc() -> []Place {
    return place_one(0, nil, true)
}

// A node's reference and type in an instance; none for a node outside it.
@(private="file")
place_ref :: proc(f: ^Place_Finder, n: Tree_Id, i: Instance_Id) -> Ref {
    inst := f.a.instances[i]
    if n < inst.lo || n > inst.hi { return {} }
    return annot_ref(f.a, i, n)
}

@(private="file")
place_type :: proc(f: ^Place_Finder, n: Tree_Id, i: Instance_Id) -> Type {
    inst := f.a.instances[i]
    if n < inst.lo || n > inst.hi { return nil }
    return annot_type(f.a, i, n)
}

// Whether a value of this type refers to storage kept somewhere else.
@(private="file")
place_refers :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice: return true
    }
    return false
}

@(private="file")
place_give :: proc(f: ^Place_Finder, tok: Token_Id, g: Place_Given) {
    list := f.given[tok]
    append(&list, g)
    f.given[tok] = list
}

// What a declaration's or an assignment's targets are given. A variable that
// holds a value stays its own place: only pointers and slices are followed.
@(private="file")
place_give_values :: proc(f: ^Place_Finder, targets, values: []Tree_Id, i: Instance_Id) {
    if len(values) == 0 { return }
    for target, j in targets {
        if f.t.tag[target] != .Ident { continue }
        r := place_ref(f, target, i)
        #partial switch r.kind {
        case .Local, .Param, .Result:
        case: continue
        }
        if len(values) == len(targets) {
            if place_refers(place_type(f, values[j], i)) { place_give(f, r.decl, {values[j], i}) }
        } else if place_refers(place_type(f, target, i)) {
            place_give(f, r.decl, {0, i})   // (one of a call's results)
        }
    }
}

// What every variable in the program is given.
place_finder_make :: proc(t: ^Tree, a: ^Annotations) -> ^Place_Finder {
    f := new(Place_Finder, context.temp_allocator)
    f.t, f.a = t, a
    f.given = make(map[Token_Id][dynamic]Place_Given, allocator = context.temp_allocator)
    f.memo = make(map[Token_Id][]Place, allocator = context.temp_allocator)
    f.busy = make(map[Token_Id]bool, allocator = context.temp_allocator)

    // Each param: what each of its calls passes. A param left to its default, in
    // a call, is given nothing to follow.
    for key, ts in a.callees {
        if ts == nil { continue }
        i, _ := annot_split(key)
        args, known := a.args[key]
        for p, k in ts.params {
            if p.decl == 0 { continue }
            if !known || k >= len(args) {
                place_give(f, p.decl, {0, i})
            } else if args[k].kind == .Written || args[k].kind == .Receiver {
                place_give(f, p.decl, {args[k].node, i})
            }
        }
    }

    // A fun used as a value is called from who knows where.
    taken := make(map[Token_Id]bool, allocator = context.temp_allocator)
    for inst, i in a.instances {
        for r, k in a.refs[i] {
            n := inst.lo + Tree_Id(k)
            if r.kind == .Fun && r.decl != 0 && (t.tag[n] == .Ident || t.tag[n] == .Field) { taken[r.decl] = true }
        }
    }
    for _, ts in a.decls {
        if ts == nil || !taken[ts.decl] { continue }
        for p in ts.params {
            if p.decl != 0 { place_give(f, p.decl, {}) }
        }
    }

    // Each local holding a pointer or a slice, and each loop's element.
    for inst, i in a.instances {
        for k in 0 ..< len(a.types[i]) {
            n := inst.lo + Tree_Id(k)
            #partial switch t.tag[n] {
            case .Decl:
                v := decl_view(t, n)
                place_give_values(f, v.targets, v.values, Instance_Id(i))
            case .Assign:
                place_give_values(f, tree_list(t, t.a[n]), tree_list(t, t.b[n]), Instance_Id(i))
            case .For_Each:
                v := for_view(t, n)
                if v.elem != 0 && v.collection != 0 { place_give(f, v.elem, {v.collection, Instance_Id(i)}) }
            }
        }
    }
    return f
}

// The places a variable may be.
@(private="file")
place_of_var :: proc(f: ^Place_Finder, tok: Token_Id) -> []Place {
    if known, done := f.memo[tok]; done { return known }
    if f.busy[tok] { return nil }   // (a recursive call passing it on: what else it's given says)
    given, has := f.given[tok]
    if !has {
        own := place_one(tok)
        f.memo[tok] = own
        return own
    }
    f.busy[tok] = true
    out := make([dynamic]Place, context.temp_allocator)
    for g in given {
        from := place_unknown() if g.node == 0 else place_of(f, g.node, g.inst)
        for p in from {
            if !place_listed(out[:], p) { append(&out, p) }
        }
    }
    delete_key(&f.busy, tok)
    result := out[:]
    if len(result) == 0 || len(result) > PLACE_MOST { result = place_unknown() }
    f.memo[tok] = result
    return result
}

@(private="file")
place_listed :: proc(list: []Place, p: Place) -> bool {
    for q in list {
        if q.root == p.root && q.loose == p.loose && slice.equal(q.fields, p.fields) { return true }
    }
    return false
}

// `base`, each with more fields down from it.
@(private="file")
place_down :: proc(base: []Place, more: ..Token_Id) -> []Place {
    out := make([]Place, len(base), context.temp_allocator)
    for p, k in base {
        fields := make([]Token_Id, len(p.fields) + len(more), context.temp_allocator)
        copy(fields, p.fields)
        copy(fields[len(p.fields):], more)
        out[k] = Place{p.root, fields, p.loose}
    }
    return out
}

// What's inside a node: its place. A pointer or slice kept in a field, or got any
// other way but a variable, goes somewhere that can't be followed.
@(private="file")
place_inside :: proc(f: ^Place_Finder, n: Tree_Id, i: Instance_Id) -> []Place {
    base := place_of(f, n, i)
    inner := n
    for f.t.tag[inner] == .Paren { inner = Tree_Id(f.t.a[inner]) }
    if f.t.tag[inner] == .Ident || f.t.tag[inner] == .Self || !place_refers(place_type(f, n, i)) { return base }
    out := make([]Place, len(base), context.temp_allocator)
    for p, k in base { out[k] = Place{p.root, p.fields, true} }
    return out
}

// The places an expression may be.
place_of :: proc(f: ^Place_Finder, n: Tree_Id, i: Instance_Id) -> []Place {
    t := f.t
    #partial switch t.tag[n] {
    case .Paren:
        return place_of(f, Tree_Id(t.a[n]), i)
    case .Deref, .Index, .Slice:
        return place_inside(f, Tree_Id(t.a[n]), i)
    case .Unary:
        if token_text(build_tokens[t.main[n]]) == "&" { return place_of(f, Tree_Id(t.a[n]), i) }
    case .Self:
        return place_one(PLACE_EVERY)
    case .Ident:
        r := place_ref(f, n, i)
        #partial switch r.kind {
        case .Local, .Param, .Result: return place_of_var(f, r.decl)
        case .Global:                 return place_one(r.decl)
        case .Field:                  return place_down(place_one(PLACE_EVERY), r.decl)
        }
    case .Field:
        r := place_ref(f, n, i)
        operand := Tree_Id(t.a[n])
        #partial switch r.kind {
        case .Global:  return place_one(r.decl)   // (a module's variable, by the module's name)
        case .Builtin: return place_inside(f, operand, i)   // (`.len`, a swizzle: a part of it)
        case .Field:
            base := place_inside(f, operand, i)
            // (A field reached through a `using` is down that field too.)
            owner := distinct_base(place_type(f, operand, i))
            if pt, is_ptr := owner.(^Type_Ptr); is_ptr { owner = distinct_base(pt.elem) }
            if sd := as_scope_body(owner); sd != nil {
                if path, through := struct_using_path(sd, token_text(build_tokens[Token_Id(t.b[n])])); through {
                    for step in path { base = place_down(base, step.decl) }
                }
            }
            return place_down(base, r.decl)
        }
    }
    // Anything else: a value made here is its own, a pointer from who knows where isn't.
    if place_refers(place_type(f, n, i)) { return place_unknown() }
    return place_one(t.first[n])
}

// Where a literal's values go: the place it's written to.
place_of_literal :: proc(f: ^Place_Finder, n: Tree_Id, i: Instance_Id) -> []Place {
    t := f.t
    // (`v{x = 1}` writes into the variable it names.)
    if f.a.overrides[annot_key(i, n)] && t.a[n] != 0 {
        if r := place_ref(f, Tree_Id(t.a[n]), i); r.decl != 0 { return place_of_var(f, r.decl) }
    }
    p := t.parent[n]
    #partial switch t.tag[p] {
    case .Paren:
        return place_of_literal(f, p, i)
    case .Call:
        if Tree_Id(t.b[p]) == n { return place_of_literal(f, p, i) }   // (`Foo() {x = 1}`)
    case .Named_Entry:
        if r := place_ref(f, p, i); r.decl != 0 { return place_down(place_of_literal(f, t.parent[p], i), r.decl) }
    case .Decl:
        v := decl_view(t, p)
        for value, k in v.values {
            if value == n && k < len(v.targets) { return place_of(f, v.targets[k], i) }
        }
    case .Assign:
        values := tree_list(t, t.b[p])
        targets := tree_list(t, t.a[p])
        for value, k in values {
            if value == n && k < len(targets) { return place_of(f, targets[k], i) }
        }
    case .Return:
        return place_unknown()   // (it goes wherever the call's result does)
    }
    return place_one(t.first[n])
}

// The places a literal's field is written to, the literal at node `lit`.
place_of_entry :: proc(f: ^Place_Finder, lit: Tree_Id, decl: Token_Id, i: Instance_Id) -> []Place {
    return place_down(place_of_literal(f, lit, i), decl)
}

// Whether `part`, a run of fields, ends `whole`.
@(private="file")
place_ends :: proc(whole, part: []Token_Id) -> bool {
    return len(part) <= len(whole) && slice.equal(whole[len(whole) - len(part):], part)
}

// Whether a use on these places is on what was asked about.
place_match :: proc(asked, used: []Place) -> Place_Match {
    best := Place_Match.No
    for a in asked {
        for u in used {
            if a.root == PLACE_EVERY && place_ends(u.fields, a.fields) { return .Yes }
            if u.root == PLACE_EVERY && place_ends(a.fields, u.fields) { return .Yes }
            if a.root != 0 && a.root == u.root && slice.equal(a.fields, u.fields) { return .Yes }
            if a.loose || u.loose { best = .Maybe }
        }
    }
    return best
}

// Whether assigning to `target` writes what was asked about, as a whole value
// that holds it: `game^ = State()` writes game.timers.work.seconds.
place_holds :: proc(asked, target: []Place) -> Place_Match {
    best := Place_Match.No
    for a in asked {
        for u in target {
            if a.root == PLACE_EVERY || u.root == PLACE_EVERY {
                // (Any run of the fields: a constructor's `work = Timer()`.)
                for start in 0 ..= len(a.fields) {
                    if len(u.fields) <= len(a.fields) - start && slice.equal(a.fields[start:][:len(u.fields)], u.fields) { return .Yes }
                }
            } else if a.root != 0 && a.root == u.root && len(u.fields) <= len(a.fields) && slice.equal(a.fields[:len(u.fields)], u.fields) {
                return .Yes
            }
            if a.loose || u.loose { best = .Maybe }
        }
    }
    return best
}
