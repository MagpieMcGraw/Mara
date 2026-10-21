package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// A fun's body found written out (`mara edit <fun>.calls`; mara lsp's code
// action at a fun). The fun's body is a pattern: its params are holes, each
// matching any expression (the same one each time it's used); its locals
// match the place's locals. A run of statements somewhere else with the
// body's shape is a place a call could go — `return f(args)` for a body
// ending in a return of what the run's return gives, `f(args)` for one
// giving nothing. The body's first statements declaring locals (`here :=
// file.pos`) may be left out of the run when a local of the place's fun
// holds the same value there: declared as that value (`here := file.pos`
// earlier), and nothing it's made of written between — no assignment to it,
// no address taken of it, no call that could write through it (shape_writes:
// the callee's body looked at, the calls it makes too).
// ---------------------------------------------------------------------------

// A place the fun's body is written out: its statements (a run of one
// statement list), what each param is there, and whether the call returns
// what the run did.
Shape_Match :: struct {
    stmts:   []Tree_Id,
    args:    []Tree_Id,   // by param
    returns: bool,
}

@(private="file")
Shape_Env :: struct {
    t:         ^Tree,
    a:         ^Annotations,
    hi, si:    Instance_Id,           // the fun's instance, the place's
    params:    map[Token_Id]int,      // the fun's params' declaring tokens: which
    locals:    map[Token_Id]bool,     // the fun's locals' declaring tokens
    holes:     []Tree_Id,             // by param: what it is at the place (0: not yet)
    bound:     map[Token_Id]Token_Id, // a local of the fun's: the place's local it is
}

// The places in the fun's module where the fun's body (`def`, its Fun_Def;
// `ts`, its scope) is written out, the fun's own body left out.
shape_matches :: proc(t: ^Tree, a: ^Annotations, def: Tree_Id, ts: ^Type_Scope) -> [dynamic]Shape_Match {
    out := make([dynamic]Shape_Match)
    if ts == nil || len(ts.params) == 0 || ts.calling_conv == .C { return out }
    body := scope_view(t, def).body
    if len(body) == 0 { return out }
    // (Giving results: its body ends in a return, the call returns them.)
    returns := len(ts.return_types) > 0
    if returns && t.tag[body[len(body) - 1]] != .Return { return out }
    hi, found := shape_instance(a, ts)
    if !found { return out }
    params := make(map[Token_Id]int, allocator = context.temp_allocator)
    for p, i in ts.params { params[p.decl] = i }
    locals := make(map[Token_Id]bool, allocator = context.temp_allocator)
    lo, _ := shape_nodes(t, def)
    for n := lo; n <= def; n += 1 {
        if t.tag[n] == .Decl {
            for target in tree_list(t, t.a[n]) { if t.tag[target] == .Ident { locals[t.main[target]] = true } }
        }
    }
    // (Its first statements declaring one local each: may be left out of a place.)
    leading := 0
    for leading < len(body) - 1 && t.tag[body[leading]] == .Decl && len(tree_list(t, t.a[body[leading]])) == 1 { leading += 1 }
    for key, site_ts in a.decls {
        si, n := annot_split(key)
        if site_ts == nil || site_ts.kind != .Fun || t.tag[n] != .Fun_Def || n == def || site_ts.home_package != ts.home_package { continue }
        lists := make([dynamic][]Tree_Id, context.temp_allocator)
        shape_lists(t, scope_view(t, n).body, &lists)
        for list in lists {
            for i := 0; i < len(list); {
                matched := false
                for absorb := 0; absorb <= leading && !matched; absorb += 1 {
                    want := body[absorb:]
                    if i + len(want) > len(list) { continue }
                    env := Shape_Env{t = t, a = a, hi = hi, si = si, params = params, locals = locals,
                                     holes = make([]Tree_Id, len(ts.params), context.temp_allocator),
                                     bound = make(map[Token_Id]Token_Id, allocator = context.temp_allocator)}
                    ok := true
                    for w, j in want { if !shape_same(&env, w, list[i + j]) { ok = false; break } }
                    if !ok { continue }
                    for h in env.holes { if h == 0 { ok = false } }   // (a param the run never gave: no call to write)
                    run := list[i:i + len(want)]
                    if ok && !shape_absorbed(&env, body[:absorb], n, run) { ok = false }
                    if ok && !returns && !shape_locals_kept(&env, n, run) { ok = false }
                    if !ok { continue }
                    append(&out, Shape_Match{stmts = slice.clone(run), args = slice.clone(env.holes), returns = returns})
                    i += len(want)
                    matched = true
                }
                if !matched { i += 1 }
            }
        }
    }
    return out
}

// A fun's instance: a generic's, the one checking its body; any other's,
// the program's own (instance 0).
@(private="file")
shape_instance :: proc(a: ^Annotations, ts: ^Type_Scope) -> (Instance_Id, bool) {
    for inst, i in a.instances { if inst.scope == ts { return Instance_Id(i), true } }
    if len(a.instances) > 0 && ts.node >= a.instances[0].lo && ts.node <= a.instances[0].hi { return 0, true }
    return 0, false
}

// A node's own nodes: made as it was parsed, one after another, it last —
// from the first back from it still inside its tokens, to it.
@(private="file")
shape_nodes :: proc(t: ^Tree, n: Tree_Id) -> (lo, hi: Tree_Id) {
    lo = n
    for lo > 1 && t.first[lo - 1] >= t.first[n] && t.end[lo - 1] <= t.end[n] { lo -= 1 }
    return lo, n
}

// A body's statement lists, it and every one in it: if's, loops', with's,
// defer's, a match's arms'. (A fun defined in it: its own.)
@(private="file")
shape_lists :: proc(t: ^Tree, list: []Tree_Id, out: ^[dynamic][]Tree_Id) {
    if len(list) == 0 { return }
    append(out, list)
    for s in list {
        #partial switch t.tag[s] {
        case .If, .Elif:
            v := if_view(t, s)
            shape_lists(t, v.then, out)
            shape_lists(t, v.else_, out)
        case .For_Range, .For_Each, .For_C, .For_Cond:
            shape_lists(t, for_view(t, s).body, out)
        case .With:
            shape_lists(t, tree_list(t, t.b[s]), out)
        case .Defer:
            shape_lists(t, tree_list(t, t.a[s]), out)
        case .Match:
            for arm in tree_list(t, t.b[s]) {
                shape_lists(t, tree_list(t, t.b[arm]) if t.tag[arm] == .Arm_Value else tree_list(t, t.a[arm]), out)
            }
        }
    }
}

// Whether the place's node s has the fun's node h's shape: the same kind,
// the same words, the same parts — a param of the fun's anything (the same
// each time), a local of the fun's the place's local it's bound to, any
// other name the same one.
@(private="file")
shape_same :: proc(env: ^Shape_Env, h, s: Tree_Id) -> bool {
    t := env.t
    if h == 0 || s == 0 { return h == s }
    if t.tag[h] == .Ident {
        r := annot_ref(env.a, env.hi, h)
        if p, is_param := env.params[r.decl]; is_param && r.decl != 0 {
            if env.holes[p] == 0 {
                env.holes[p] = s
                return true
            }
            return shape_alike(env, env.holes[p], s)
        }
        if t.tag[s] != .Ident { return false }
        sr := annot_ref(env.a, env.si, s)
        // (A declaring name has no ref of its own: its token is its declaration.)
        hd, sd := r.decl, sr.decl
        if hd == 0 { hd = t.main[h] }
        if sd == 0 { sd = t.main[s] }
        if env.locals[hd] {
            // (Declared by the run itself: a Decl's target, bound when it's met.)
            if to, bound := env.bound[hd]; bound { return to == sd }
            env.bound[hd] = sd
            return true
        }
        return r.decl == sr.decl && token_text(build_tokens[t.main[h]]) == token_text(build_tokens[t.main[s]])
    }
    if t.tag[h] != t.tag[s] { return false }
    // (Its word — an operator, a literal's value, a keyword; a declaration's
    // or assignment's, its first name: its targets are compared.)
    if t.tag[h] != .Decl && t.tag[h] != .Assign && token_text(build_tokens[t.main[h]]) != token_text(build_tokens[t.main[s]]) { return false }
    if t.tag[h] == .Call || t.tag[h] == .Method_Call {
        hr, sr := annot_ref(env.a, env.hi, h), annot_ref(env.a, env.si, s)
        if hr.decl != sr.decl { return false }
    }
    shape := tree_shapes[t.tag[h]]
    return shape_field(env, shape.a, t.a[h], t.a[s], shape) && shape_field(env, shape.b, t.b[h], t.b[s], shape)
}

// A node's field, as its shape has it, alike in both.
@(private="file")
shape_field :: proc(env: ^Shape_Env, kind: Tree_Field, x, y: u32, shape: Tree_Shape) -> bool {
    t := env.t
    switch kind {
    case .None:
        return true
    case .Node:
        return shape_same(env, Tree_Id(x), Tree_Id(y))
    case .List:
        xs, ys := tree_list(t, x), tree_list(t, y)
        if len(xs) != len(ys) { return false }
        for e, i in xs { if !shape_same(env, e, ys[i]) { return false } }
        return true
    case .Token:
        if (x == 0) != (y == 0) { return false }
        return x == 0 || token_text(build_tokens[Token_Id(x)]) == token_text(build_tokens[Token_Id(y)])
    case .Tokens:
        xs, ys := tree_token_list(t, x), tree_token_list(t, y)
        if len(xs) != len(ys) { return false }
        for e, i in xs { if token_text(build_tokens[e]) != token_text(build_tokens[ys[i]]) { return false } }
        return true
    case .Rec:
        n := 0
        for n < len(shape.rec) && shape.rec[n] != .None { n += 1 }
        xs, ys := tree_rec(t, x, n), tree_rec(t, y, n)
        rec := shape.rec
        for i in 0 ..< n {
            if !shape_field(env, rec[i], xs[i], ys[i], Tree_Shape{rec = rec}) { return false }
        }
        return true
    }
    return false
}

// Whether two of the place's expressions are alike: the same shape, names
// the same ones.
@(private="file")
shape_alike :: proc(env: ^Shape_Env, x, y: Tree_Id) -> bool {
    t := env.t
    if x == 0 || y == 0 { return x == y }
    if t.tag[x] != t.tag[y] || token_text(build_tokens[t.main[x]]) != token_text(build_tokens[t.main[y]]) { return false }
    if t.tag[x] == .Ident { return annot_ref(env.a, env.si, x).decl == annot_ref(env.a, env.si, y).decl }
    // (The same as the fun's own comparing, the place on both sides: its own
    // instance for the "fun" side, no holes.)
    inner := Shape_Env{t = t, a = env.a, hi = env.si, si = env.si,
                       params = make(map[Token_Id]int, allocator = context.temp_allocator),
                       locals = make(map[Token_Id]bool, allocator = context.temp_allocator),
                       bound = make(map[Token_Id]Token_Id, allocator = context.temp_allocator)}
    return shape_same(&inner, x, y)
}

// The fun's first statements left out of the run (`absorbed`), each `x :=
// v`: x bound to a local of the place's fun declared as v (as the run's
// holes make it) before the run, nothing it's made of written between.
@(private="file")
shape_absorbed :: proc(env: ^Shape_Env, absorbed: []Tree_Id, fun: Tree_Id, run: []Tree_Id) -> bool {
    t := env.t
    for d in absorbed {
        target := tree_list(t, t.a[d])[0]
        local, bound := env.bound[t.main[target]]
        if !bound || local == 0 { return false }
        values := tree_list(t, tree_rec(t, t.b[d], 2)[1])
        if len(values) != 1 { return false }
        // The place's declaration of that local, in its fun: `local := value`.
        decl := shape_decl_of(t, env.a, env.si, fun, local)
        if decl == 0 || t.first[decl] >= t.first[run[0]] { return false }
        site_values := tree_list(t, tree_rec(t, t.b[decl], 2)[1])
        if len(site_values) != 1 || !shape_same(env, values[0], site_values[0]) { return false }
        // What it's made of: the place's locals and params (anything else, no).
        roots := make(map[Token_Id]bool, allocator = context.temp_allocator)
        roots[local] = true
        if !shape_roots(t, env.a, env.si, site_values[0], &roots) { return false }
        // Nothing of it written on the way from its declaration to the run
        // (shape_unchanged).
        if !shape_unchanged(env, scope_view(t, fun).body, decl, run[0], &roots) { return false }
    }
    return true
}

// The Decl in a fun declaring the local whose token is `tok`; 0 for none.
@(private="file")
shape_decl_of :: proc(t: ^Tree, a: ^Annotations, i: Instance_Id, fun: Tree_Id, tok: Token_Id) -> Tree_Id {
    lo, _ := shape_nodes(t, fun)
    for n := lo; n <= fun; n += 1 {
        if t.tag[n] != .Decl { continue }
        targets := tree_list(t, t.a[n])
        if len(targets) == 1 && t.main[targets[0]] == tok { return n }
    }
    return 0
}

// The locals and params an expression reads, added to roots; false when it
// reads anything else that could change (a global).
@(private="file")
shape_roots :: proc(t: ^Tree, a: ^Annotations, i: Instance_Id, e: Tree_Id, roots: ^map[Token_Id]bool) -> bool {
    lo, _ := shape_nodes(t, e)
    for n := lo; n <= e; n += 1 {
        if t.tag[n] != .Ident { continue }
        r := annot_ref(a, i, n)
        #partial switch r.kind {
        case .Local, .Param: roots[r.decl] = true
        case .Global:        return false
        }
    }
    return true
}

// A statement list and the place in it of the statement a node is in, from
// a fun's body down to the list the node is a statement of.
@(private="file")
Shape_Step :: struct {
    list:  []Tree_Id,
    index: int,
}

// Whether nothing on the way from statement `decl` to statement `at` (in
// one fun's body) could write what `roots` names. The way: decl's list
// after it — a statement there whose branch ends in a return, break or
// continue reaching nothing past it — then down each statement holding
// `at`: an if's condition, its branch `at` is in alone; a loop around `at`
// all of it (its next round comes round); the statements before `at` in
// its list. decl not in a list on the way: it doesn't come before `at` on
// every way there — no.
@(private="file")
shape_unchanged :: proc(env: ^Shape_Env, body: []Tree_Id, decl, at: Tree_Id, roots: ^map[Token_Id]bool) -> bool {
    t := env.t
    chain := make([dynamic]Shape_Step, context.temp_allocator)
    if !shape_chain(t, body, at, &chain) { return false }
    level := -1
    from := 0
    for step, k in chain {
        for s, i in step.list[:step.index] {
            if s == decl {
                level, from = k, i + 1
            }
        }
    }
    if level < 0 { return false }
    seen := make(map[^Type_Scope]bool, allocator = context.temp_allocator)
    for k in level ..< len(chain) {
        step := chain[k]
        first := from if k == level else 0
        for s in step.list[first:step.index] {
            if shape_reaching_writes(env, s, roots, &seen) { return false }
        }
        if k == len(chain) - 1 { break }
        // (The statement holding `at`: what of it runs before `at` does.)
        holder := step.list[step.index]
        #partial switch t.tag[holder] {
        case .If, .Elif:
            if shape_subtree_writes(env, Tree_Id(t.a[holder]), roots, &seen) { return false }
        case .For_Range, .For_Each, .For_C, .For_Cond:
            if shape_subtree_writes(env, holder, roots, &seen) { return false }
        case .Match, .With:
            if shape_subtree_writes(env, Tree_Id(t.a[holder]), roots, &seen) { return false }
        }
    }
    return true
}

// The way down from a list to the statement `at` (shape_unchanged): each
// list and the place of the statement holding it. False when it isn't there.
@(private="file")
shape_chain :: proc(t: ^Tree, list: []Tree_Id, at: Tree_Id, out: ^[dynamic]Shape_Step) -> bool {
    for s, i in list {
        if s == at {
            append(out, Shape_Step{list, i})
            return true
        }
        if t.first[at] < t.first[s] || t.first[at] >= t.end[s] { continue }
        append(out, Shape_Step{list, i})
        inner := make([dynamic][]Tree_Id, context.temp_allocator)
        #partial switch t.tag[s] {
        case .If, .Elif:
            v := if_view(t, s)
            append(&inner, v.then, v.else_)
        case .For_Range, .For_Each, .For_C, .For_Cond:
            append(&inner, for_view(t, s).body)
        case .With:
            append(&inner, tree_list(t, t.b[s]))
        case .Defer:
            append(&inner, tree_list(t, t.a[s]))
        case .Match:
            for arm in tree_list(t, t.b[s]) {
                append(&inner, tree_list(t, t.b[arm]) if t.tag[arm] == .Arm_Value else tree_list(t, t.a[arm]))
            }
        }
        for l in inner { if shape_chain(t, l, at, out) { return true } }
        pop(out)
        return false
    }
    return false
}

// Whether a statement could write what `roots` names in what of it reaches
// the statement after it: an if's condition, and a branch of it only when
// that branch can end without a return, break or continue. (A defer's runs
// later.)
@(private="file")
shape_reaching_writes :: proc(env: ^Shape_Env, s: Tree_Id, roots: ^map[Token_Id]bool, seen: ^map[^Type_Scope]bool) -> bool {
    t := env.t
    #partial switch t.tag[s] {
    case .Defer:
        return false
    case .If, .Elif:
        v := if_view(t, s)
        if shape_subtree_writes(env, v.cond, roots, seen) { return true }
        for branch in ([2][]Tree_Id{v.then, v.else_}) {
            if len(branch) == 0 || !shape_falls_through(t, branch) { continue }
            for b in branch { if shape_reaching_writes(env, b, roots, seen) { return true } }
        }
        return false
    }
    return shape_subtree_writes(env, s, roots, seen)
}

// Whether a statement list can end without a return, break or continue: its
// last statement can (an if, when any branch can — one without an else, it
// can).
@(private="file")
shape_falls_through :: proc(t: ^Tree, list: []Tree_Id) -> bool {
    if len(list) == 0 { return true }
    last := list[len(list) - 1]
    #partial switch t.tag[last] {
    case .Return, .Break: return false
    case .If, .Elif:
        v := if_view(t, last)
        return len(v.else_) == 0 || shape_falls_through(t, v.then) || shape_falls_through(t, v.else_)
    }
    if build_tokens[t.main[last]].kind == .Continue { return false }
    return true
}

// Whether anything in a node (any of its nodes, in the place's instance)
// could write what `roots` names (shape_writes).
@(private="file")
shape_subtree_writes :: proc(env: ^Shape_Env, n: Tree_Id, roots: ^map[Token_Id]bool, seen: ^map[^Type_Scope]bool) -> bool {
    t := env.t
    if n == 0 { return false }
    lo, _ := shape_nodes(t, n)
    for m := lo; m <= n; m += 1 {
        if shape_writes(t, env.a, env.si, m, roots, seen) { return true }
    }
    return false
}

// Whether node n writes what `roots` names (shape_writes_between).
@(private="file")
shape_writes :: proc(t: ^Tree, a: ^Annotations, i: Instance_Id, n: Tree_Id, roots: ^map[Token_Id]bool, seen: ^map[^Type_Scope]bool) -> bool {
    root :: proc(t: ^Tree, a: ^Annotations, i: Instance_Id, e: Tree_Id, roots: ^map[Token_Id]bool) -> bool {
        e := e
        for {
            #partial switch t.tag[e] {
            case .Paren, .Field, .Index, .Deref, .Slice: e = Tree_Id(t.a[e])
            case .Ident: return roots[annot_ref(a, i, e).decl]
            case: return false
            }
        }
    }
    #partial switch t.tag[n] {
    case .Assign:
        for target in tree_list(t, t.a[n]) { if root(t, a, i, target, roots) { return true } }
    case .Compound:
        if root(t, a, i, Tree_Id(t.a[n]), roots) { return true }
    case .Unary:
        if build_tokens[t.main[n]].kind == .Ampersand && root(t, a, i, Tree_Id(t.a[n]), roots) { return true }
    case .Call, .Method_Call:
        args := tree_list(t, t.a[n]) if t.tag[n] == .Call else method_view(t, n).args
        callee := a.callees[annot_key(i, n)] or_else nil
        shift := 0
        if t.tag[n] == .Method_Call {
            if root(t, a, i, method_view(t, n).receiver, roots) {
                if callee == nil || shape_writes_param(t, a, callee, 0, seen) { return true }
            }
            shift = 1
        }
        for arg, j in args {
            if !root(t, a, i, arg, roots) { continue }
            if callee == nil { continue }   // (a builtin's: it reads what it's given; `&x` is the address taken)
            if shape_writes_param(t, a, callee, j + shift, seen) { return true }
        }
    }
    return false
}

// Whether a fun could write through its param p: assigns to it or through
// it, takes its address, or passes it to a call that could. (A fun without
// a body here — foreign — could.)
@(private="file")
shape_writes_param :: proc(t: ^Tree, a: ^Annotations, callee: ^Type_Scope, p: int, seen: ^map[^Type_Scope]bool) -> bool {
    if callee.kind != .Fun { return false }   // (a constructor: its params are values given)
    if callee.calling_conv == .C || callee.node == 0 || p >= len(callee.params) { return true }
    if seen[callee] { return false }   // (recursion: as far as it's seen)
    seen[callee] = true
    i, found := shape_instance(a, callee)
    if !found { return true }
    roots := make(map[Token_Id]bool, allocator = context.temp_allocator)
    roots[callee.params[p].decl] = true
    lo, _ := shape_nodes(t, callee.node)
    for n := lo; n <= callee.node; n += 1 {
        if shape_writes(t, a, i, n, &roots, seen) { return true }
    }
    return false
}

// A run that gives nothing back: the locals it declares not read after it.
@(private="file")
shape_locals_kept :: proc(env: ^Shape_Env, fun: Tree_Id, run: []Tree_Id) -> bool {
    t := env.t
    declared := make(map[Token_Id]bool, allocator = context.temp_allocator)
    for _, local in env.bound { declared[local] = true }
    after := t.end[run[len(run) - 1]]
    lo, _ := shape_nodes(t, fun)
    for n := lo; n <= fun; n += 1 {
        if t.tag[n] == .Ident && t.first[n] >= after && declared[annot_ref(env.a, env.si, n).decl] { return false }
    }
    return true
}

// A match's call, as written in place of its run: `return f(args)` or
// `f(args)`, each arg as the place wrote it.
shape_call_text :: proc(t: ^Tree, name: string, m: Shape_Match) -> string {
    args := make([dynamic]string, context.temp_allocator)
    for e in m.args {
        first, last := build_tokens[t.first[e]], build_tokens[t.end[e] - 1]
        append(&args, build_files[first.file].source[first.offset:last.offset + last.len])
    }
    call := fmt.tprintf("%s(%s)", name, strings.join(args[:], ", "))
    return strings.concatenate({"return ", call}) if m.returns else call
}

// Where a match's run is: its first statement's start to its last's end.
shape_span :: proc(t: ^Tree, m: Shape_Match) -> (file: u16, at, end: int) {
    first, last := build_tokens[t.first[m.stmts[0]]], build_tokens[t.end[m.stmts[len(m.stmts) - 1]] - 1]
    return first.file, int(first.offset), int(last.offset + last.len)
}
