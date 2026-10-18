package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Lowering (design/annotated_tree.md, stage 2): the program graph made from
// the flat tree and what the checker found about it (annot.odin), once the
// check is done — the checker only checks.
//
// Each code is lowered on its own (lw_code), in the instance it was checked
// in (its event in TC.events: its salt, so tc_node_type and the rest read
// that instance's annotations) — when the middle end asks for it
// (middle_program), or where the program writes it (lower_place). A body's statements and expressions are built in
// the order the checker checked them, through the one builder, each value's
// type the one annotated on its node.
//
// While it runs, the builder is k.gb, and its state is k.lower; the helpers
// that take a value to its use (lw_store, lw_value_as, lw_built, …) are in
// lower_build.odin. What lowering can't build stops the build, saying so
// (lw_fail).
// ---------------------------------------------------------------------------

// The lowering's own state: the body being built.
Lower :: struct {
    ts:         ^Type_Scope,                // the fun or struct whose code is being built (nil: a constant's)
    recv:       struct { node: Tree_Id, t: Type, r: Built },   // the call being built's receiver, built
    byte_addrs: map[Syntax_Id][2]Node_Id,   // each `&bytes[i]` built: its address, its element
    span_read:  Built_Span_Read,            // the span of bytes last built to be read as its destination's type
    parallel:   ^[dynamic]LW_Held,          // assigned together (`a, b = b, a`): each store, held
    compound:   struct { target: Tree_Id, place: Operand },   // a compound assignment's target, its place built
}

lower_begin :: proc(k: ^TC) -> (^Graph_Program, LW_Codes) {
    p := graph_program_new(k.checked, tc_module_graph_decls(k))
    lw_const_index(k)
    // What each module statement was settled as; each code's event — where
    // it was checked: a body's by its fun or struct (and the statement that
    // declares it), a constant's by its declaration.
    n := len(k.events)
    codes := LW_Codes{done = make([]bool, n), code = make([]^Program_Graph, n), folded = make([]bool, n), analysed = make([]bool, n)}
    for e, i in k.events {
        tc_salt_set(k, e.salt)
        switch e.kind {
        case .Module_Stmt:
            graph_module_stmt(p, e.sid)
        case .Body:
            codes.bodies[e.sc.ts] = i
        case .Const:
            codes.consts[tc_sid(k, e.kc.def)] = i
        }
    }
    return p, codes
}

// A lowering's own view of the checker (TC): a copy of it, with a builder of
// its own (lw_code builds through it). What lowering changes as it goes —
// the instance, the module, the type params bound, the body's state — is the
// copy's; the rest — the tree, the annotations, the tables — every lowering
// shares, and only reads (a debug build checks: lw_shared_sizes).
lw_worker :: proc(k: ^TC, p: ^Graph_Program) -> ^TC {
    w := new(TC)
    w^ = k^
    w.gb = graph_builder_new(p)
    w.lowering = true
    w.lower = {}
    w.field_default = {}
    return w
}

// How much each table lowerings share holds — the checker's, the
// annotations', the symbol table's. A lowering that added to one would have
// written what another lowering reads: the sizes, taken before and after,
// and a lowering's view's after, are all the same.
lw_shared_sizes :: proc(k: ^TC) -> [dynamic]int {
    s := make([dynamic]int, context.temp_allocator)
    append(&s, len(k.addressed_calls), len(k.modules), len(k.events), len(k.const_by_decl), len(k.scopes), len(k.scope_of),
        len(k.checked_modules), len(k.in_progress), len(k.templates), len(k.consts), len(k.scope_consts),
        len(k.instances), len(k.instance_order), len(k.vars), len(k.struct_instances), len(k.variant_scopes),
        len(k.exposed))
    a := k.annot
    append(&s, len(a.instances), len(a.types), len(a.refs), len(a.callees), len(a.args), len(a.forms), len(a.overrides),
        len(a.receivers), len(a.call_names), len(a.size_of), len(a.dot_bases), len(a.vars), len(a.bodies),
        len(a.type_table.types))
    append(&s, len(k.checked.functions), len(k.table.funs), len(k.table.structs))
    return s
}

// Each code put in place where the program writes it — lowered there, if it
// wasn't yet — and one no statement places lowered all the same, as it was
// checked.
lower_place :: proc(k: ^TC, codes: ^LW_Codes) {
    b := k.gb
    for ms in b.prog.module_list {
        if !ms.settled && ms.d.settles { graph_fatal(ms.d.span, "the checker settled no declaration here") }
        lw_place_decl(k, codes, ms.d)
    }
    for e, i in k.events { if e.kind != .Module_Stmt { lw_code(k, codes, i) } }
}

// Each code's event (TC.events): where it was checked, and whether it is
// lowered yet.
LW_Codes :: struct {
    bodies: map[^Type_Scope]int,    // a fun's or a struct's body's
    consts: map[Syntax_Id]int,      // a constant's, by its declaration
    // By event, each written by the lowering that lowers it alone: whether
    // it's lowered, its code (nil: it failed, or isn't one), whether the code
    // is analysed (middle.odin).
    done:     []bool,
    code:     []^Program_Graph,
    folded:   []bool,
    analysed: []bool,
}

// One code lowered, on its own: from the tree and the annotations, in the
// instance it was checked in — no code needs another's. (Once.)
lw_code :: proc(k: ^TC, codes: ^LW_Codes, i: int) {
    if codes.done[i] { return }
    codes.done[i] = true
    e := k.events[i]
    tc_salt_set(k, e.salt)
    k.pkg = e.pkg
    #partial switch e.kind {
    case .Const:          codes.code[i] = lw_const(k, e.kc)
    case .Body:           codes.code[i] = lw_body(k, e.sc)
    }
}

// The code a statement outside any body defines — a module's, a body's
// definition: a constant's, or a fun's or struct's, each of its instances —
// lowered and put in place (Program_Code.codes, the program's written order:
// each module's statements in turn, a code's body's definitions after it).
// (What runs nothing — a variable, which no function sees, an import, a
// type, a dispatch group, a foreign fun, a constant nothing uses — is no
// code.)
lw_place_decl :: proc(k: ^TC, codes: ^LW_Codes, d: Graph_Decl) {
    b := k.gb
    if i, is_const := codes.consts[d.id]; is_const { lw_code(k, codes, i) }
    if c, built := b.prog.consts[d.id]; built {
        graph_place(b.prog, c)
        return
    }
    #partial switch d.form {
    case .Scope:
        // (Each scope the checker made of it — one; a generic's, each
        // instance's — lowered and put in place.)
        list := lw_decl_scopes(k, d)
        if len(list) == 0 {
            if d.generic { return }   // a generic nothing instantiates: syntax only
            graph_fatal(d.span, "'%s' reached the graph unchecked", d.name)
        }
        for ts in list { lw_place_scope(k, codes, ts, d.name, d.span, .Synthetic if d.generic else .Explicit) }
    case .Code:
        graph_fatal(d.span, "code outside a body reached the graph")
    }
}

// The scopes a definition is — one; a generic's, each instance's (by name:
// ids stable) — as the checker recorded them by its node (Annotations.decls).
lw_decl_scopes :: proc(k: ^TC, d: Graph_Decl) -> []^Type_Scope {
    a := k.annot
    out := make([dynamic]^Type_Scope, context.temp_allocator)
    if ts := a.decls[d.node] or_else nil; ts != nil { append(&out, ts) }   // (a generic's too: the compiler's Program, one scope)
    if !d.generic { return out[:] }
    _, n := annot_split(d.node)
    for _, i in a.instances {   // (its body as each instance checked it: a generic's, a generic union's variant's)
        ts := a.decls[annot_key(Instance_Id(i), n)] or_else nil
        if ts != nil && !ts.is_module && !slice.contains(out[:], ts) { append(&out, ts) }
    }
    slice.sort_by(out[:], proc(x, y: ^Type_Scope) -> bool { return ask_type_name(x) < ask_type_name(y) })
    return out[:]
}

// A fun's or struct's code (a clean check checked every one), lowered and
// put in place; then its body's definitions'.
lw_place_scope :: proc(k: ^TC, codes: ^LW_Codes, ts: ^Type_Scope, name: string, span: Span, written: Written) {
    b := k.gb
    if i, checked := codes.bodies[ts]; checked { lw_code(k, codes, i) }
    c, built := b.prog.bodies[ts]
    if !built { graph_fatal(span, "the checker built no graph of '%s'", graph_scope_name(ts, name, written)) }
    graph_place_scope(b.prog, c, ts, name, written)
    for d in c.defs { lw_place_decl(k, codes, d) }
}

// The declaration of the variable a name refers to: in the code being built,
// by the token its annotation says declares it (graph_local).
lw_local :: proc(k: ^TC, n: Tree_Id) -> Node_Id {
    if d := graph_local(k.gb, tc_ref(k, n).decl); d != NO_NODE { return d }
    lw_fail(k, n, "a name no code here declares")
}

lw_unsupported :: proc(k: ^TC, n: Tree_Id, what: string) -> ! {
    graph_fatal(tree_span(k.t, n), "lower: %s is not supported yet (%v)", what, k.t.tag[n])
}

// What lowering can't build: the build stops, saying why.
lw_fail :: proc(k: ^TC, n: Tree_Id, reason: string) -> ! {
    graph_fatal(tree_span(k.t, n), "lower: %s", reason)
}

// --- constants and bodies -------------------------------------------------------

// A constant's value, built into its declaration (tc_check_const).
lw_const :: proc(k: ^TC, kc: ^TC_Const) -> ^Program_Graph {
    b := k.gb
    span := tree_span(k.t, kc.def)
    lowering := b.at
    b.at = tc_sid(k, kc.def)
    defer b.at = lowering
    f := graph_const_begin(b, tc_graph_decl(k, kc.def))
    ann: Type = Type_Any{}
    if kc.ann != 0 { ann = tc_node_type(k, kc.ann) }
    saved := k.lower
    k.lower = {}
    defer k.lower = saved
    at := graph_dest_var(f.root, nil if is_untyped(ann) else ann)
    r := lw_expr(k, kc.value, .Into, dest = at, temp_span = span)
    lw_store(k, kc.value, tc_node_type(k, kc.value), r, graph_dest_var(f.root, kc.t), span, settle = true)
    return graph_const_end(b, f, kc.t)
}

// A use of a constant: its value (a table's global, read; asked its place, the
// global itself).
lw_const_use :: proc(k: ^TC, kc: ^TC_Const, n: Tree_Id, t: Type, want: Build_Want, w: Written) -> Built {
    b := k.gb
    if want == .None { return {} }
    span := tree_span(k.t, n)
    named := Graph_Named{value = kc.sid}
    if graph_aggregate(t) {
        g := graph_const_global(b, w, span, t, kc.name, named)
        if want == .Value { return {v = graph_read(b, g, t, span), ok = true} }
        return {v = g, place = true, ok = true}
    }
    if want == .Place { return {} }
    return {v = graph_named_const(b, w, span, t, kc.name, named, untyped = tc_open(kc.t)), ok = true}
}

// A fun's or a struct's body (tc_scope_body): its code, statement by
// statement — a struct's top block's declarations its fields.
lw_body :: proc(k: ^TC, sc: ^TC_Scope) -> ^Program_Graph {
    b := k.gb
    t := k.t
    ts := sc.ts
    v := scope_view(t, sc.node)
    span := tree_span(t, sc.def)
    is_struct := ts.kind == .Struct
    saved := k.lower
    k.lower = {ts = ts}
    defer k.lower = saved
    at := b.at
    b.at = tc_sid(k, sc.node)   // (its node: an instance's own — its definition is the template's)
    defer b.at = at
    returned := lw_returned_local(k, ts, v.body) if b.arena && v.intrinsic == 0 else 0
    holds := v.intrinsic == 0 && !is_struct && lw_scope_arena(k, v.body, returned)
    f := graph_body_begin(b, ts, span, v.intrinsic != 0, .Synthetic if sc.synthetic else .Explicit, returned, holds)
    if v.intrinsic == 0 { lw_scope(k, v.body, ts if is_struct else nil, top = true) }
    return graph_body_end(b, f)
}

// --- the arena ------------------------------------------------------------------
// Where the program has a scope arena, a local whose value is big lives on
// it (routes_to_arena): its space taken where it is declared, the arena
// marked where its scope begins and reset at each exit. Which scopes mark it
// is read off their declarations' types before they are built. (A big
// temporary is the fun's, from its entry: storage_big_temps.)

// The local every `return` of a fun with one result returns as it is: what
// its code builds in its caller's slot, not on the arena (the token that
// declares it). 0 when one returns anything else, or there are none.
lw_returned_local :: proc(k: ^TC, ts: ^Type_Scope, body: []Tree_Id) -> Token_Id {
    if ts == nil || ts.kind != .Fun || len(ts.return_types) != 1 { return 0 }
    r := LW_Returns{want = ts.return_types[0]}
    lw_scan_returns(k, body, &r)
    return 0 if r.other else r.tok
}

@(private="file")
LW_Returns :: struct {
    want:  Type,
    tok:   Token_Id,
    other: bool,
}

// Each `return` in the statements lowering builds (lw_scope's, and each
// nested block's).
@(private="file")
lw_scan_returns :: proc(k: ^TC, stmts: []Tree_Id, r: ^LW_Returns) {
    t := k.t
    for s in tc_live(k, stmts) {
        #partial switch t.tag[s] {
        case .Return:
            values := tree_list(t, t.a[s])
            tok := lw_return_local(k, values[0], r.want) if len(values) == 1 else 0
            if tok == 0 || r.tok != 0 && tok != r.tok { r.other = true } else { r.tok = tok }
        case .If, .Elif:
            v := if_view(t, s)
            lw_scan_returns(k, v.then, r)
            lw_scan_returns(k, v.else_, r)
        case .For_Range, .For_Each, .For_C, .For_Cond:
            lw_scan_returns(k, for_view(t, s).body, r)
        case .With:
            lw_scan_returns(k, tree_list(t, t.b[s]), r)
        case .Match:
            for arm in tree_list(t, t.b[s]) { lw_scan_returns(k, lw_arm_body(k, arm), r) }
        }
    }
}

// A match arm's statements.
lw_arm_body :: proc(k: ^TC, arm: Tree_Id) -> []Tree_Id {
    t := k.t
    return tree_list(t, t.b[arm]) if t.tag[arm] == .Arm_Value else tree_list(t, t.a[arm])
}

// The local `return v` returns as it is — read, with no view taken of it or
// widening (lw_return, lw_value_as): its token; else 0.
@(private="file")
lw_return_local :: proc(k: ^TC, val: Tree_Id, want: Type) -> Token_Id {
    e := tc_unparen(k, val)
    if k.t.tag[e] != .Ident { return 0 }
    ref := tc_ref(k, e)
    if ref.kind != .Local { return 0 }
    vt := tc_node_type(k, val)
    if lw_names_fun(k, e, vt) { return 0 }   // (a fun's name: its global, lw_ident)
    if view_kind(want, vt) != .None { return 0 }
    if _, _, num := numeric_info(graph_settled(vt)); num && !(is_infer(vt) && infer_cell_of(vt) == nil) && graph_widens(graph_settled(vt), want) { return 0 }
    return ref.decl
}

// Whether a local declared in these statements, a block's own, lives on the
// arena (lw_decl_arena); `returned` (lw_returned_local) doesn't.
lw_scope_arena :: proc(k: ^TC, stmts: []Tree_Id, returned: Token_Id) -> bool {
    if !k.gb.arena { return false }
    t := k.t
    for s in tc_live(k, stmts) {
        if t.tag[s] != .Decl { continue }
        v := decl_view(t, s)
        if len(v.targets) > 1 && len(v.values) == 1 {
            // (A destructure's: a big result's local, on the arena.)
            if lw_destructure_arena(k, v.targets, v.values[0], returned) { return true }
            continue
        }
        for tg, i in v.targets {
            // (Of no type a big one is — its own, its annotation's — it has
            // no local on the arena: most, decided without the rest.)
            if !routes_to_arena(tc_node_type(k, tg)) && (v.type_ == 0 || !routes_to_arena(tc_node_type(k, v.type_))) { continue }
            if tc_name(k, tg) == "_" { continue }   // (no local)
            lt, takes := lw_decl_type(k, tg, v.values[i] if i < len(v.values) else 0, v.type_)
            if takes && lt != nil && routes_to_arena(lt) && k.t.main[tg] != returned { return true }
        }
    }
    return false
}

// Whether `a, b := f()` (or `f()?`) declares a local on the arena: a name
// for a big result — but the local every return returns (its caller's slot).
lw_destructure_arena :: proc(k: ^TC, targets: []Tree_Id, value: Tree_Id, returned: Token_Id) -> bool {
    v := tc_unparen(k, value)
    returns := tc_call_returns(k, v)
    if k.t.tag[v] == .Try {
        rets := tc_call_returns(k, tc_unparen(k, Tree_Id(k.t.a[v])))
        if len(rets) > 0 { returns = rets[:len(rets) - 1] }
    }
    for tg, i in targets {
        if i >= len(returns) || k.t.tag[tg] != .Ident || tc_name(k, tg) == "_" || k.t.main[tg] == returned { continue }
        if routes_to_arena(returns[i]) { return true }
    }
    return false
}

// A big value with nowhere to go — an argument, a dropped result — built in
// a temporary of its own, which lives on the arena (storage_big_temps); its
// read (held false: not one, built nothing).
lw_big_held :: proc(k: ^TC, n: Tree_Id, t: Type, w: Written, span: Span) -> (Built, bool) {
    if t == nil || !lw_placeless(k, tc_unparen(k, n)) || !routes_to_arena(t) || !graph_aggregate(t) { return {}, false }
    b := k.gb
    slot := graph_slot(b, "temp", t, span)
    d := graph_dest_var(slot, t)
    r := lw_expr(k, n, .Into, w, dest = d)
    lw_store(k, n, t, r, d, span)
    return {v = graph_read(b, graph_var(b, slot, t, span), t, span), ok = true}, true
}

// Whether an expression's value is made, not read from a place: a call's
// result, a literal, an array, a union's variant, an `if` expression's.
lw_placeless :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[n] {
    case .Call, .Method_Call, .Literal, .Array, .Dot_Ident, .If_Expr, .Broadcast: return true
    case .Field: return tc_ref(k, n).kind == .Variant
    }
    return false
}

// One name's declaration in a body (lw_decl_one): the type its local takes,
// and whether its space can be on the arena (graph_build_decl: a `let`
// binds memory it takes; a bare declaration of no type declares none).
@(private="file")
lw_decl_type :: proc(k: ^TC, target, value, ann_node: Tree_Id) -> (Type, bool) {
    t := k.t
    ann: Type = Type_Any{}
    if ann_node != 0 { ann = tc_node_type(k, ann_node) }
    form, _, _ := tc_decl_form(k, value, ann_node, ann)
    switch form {
    case .Void, .Shape: return ann, true
    case .Take:         return tc_node_type(k, target), tc_text(t.main[tc_unparen(k, value)]) != "let"
    case .Bare:
        _, is_error := ann.(Type_Error)
        return ann, !is_error
    case .Value:
    }
    return tc_node_type(k, target), true
}

// A block's statements (tc_scope).
lw_scope :: proc(k: ^TC, stmts: []Tree_Id, fields_of: ^Type_Scope = nil, top := false) {
    t := k.t
    b := k.gb
    stmts := tc_live(k, stmts)
    for s in stmts {
        if t.tag[s] == .Define {
            if top { graph_build_def(b, tc_graph_decl(k, s)) }
            continue
        }
        span := tree_span(t, s)
        at := lw_at(k, s)
        graph_build_body_stmt(b, span)
        if t.tag[s] == .Using && fields_of != nil {
            lw_decl(k, Tree_Id(t.a[s]), fields_of)
        } else if t.tag[s] == .Decl && fields_of != nil {
            lw_decl(k, s, fields_of)
        } else {
            lw_stmt(k, s)
        }
        b.at = at
    }
}

// The tree node whose operations are built from here (Graph_Builder.at, each
// node's syntax): n, in the instance being lowered. The one it was is
// returned, to be put back.
lw_at :: proc(k: ^TC, n: Tree_Id) -> Syntax_Id {
    at := k.gb.at
    k.gb.at = tc_sid(k, n)
    return at
}

// A default lowered where a call leaves it off: what it's built of is the
// call's (Graph_Builder.pin) — a tree node's nodes in one code. What to put
// back once it's built.
lw_pin :: proc(k: ^TC) -> Syntax_Id {
    pin := k.gb.pin
    if pin == 0 { k.gb.pin = k.gb.at }
    return pin
}

lw_stmt :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    at := lw_at(k, s)
    defer k.gb.at = at
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        if lw_override(k, e) { return }
        // (A big result dropped: built in a temporary of its own, on the arena.)
        if _, held := lw_big_held(k, e, tc_node_type(k, e), .Explicit, tree_span(t, s)); held { return }
        lw_expr(k, e, .Value)
    case .Decl:
        lw_decl(k, s)
    case .Assign:
        lw_assign(k, s)
    case .Return:
        lw_return(k, s)
    case .If, .Elif:
        lw_if(k, s)
    case .For_Range, .For_Each, .For_C, .For_Cond:
        lw_for(k, s)
    case .Compound:
        lw_compound(k, s)
    case .Defer:
        body := tree_list(t, t.a[s])
        gd := graph_build_defer(k.gb, span, lw_scope_arena(k, body, k.gb.body.returned), tree_defer_on_failure(t, s))
        lw_scope(k, body)
        graph_build_defer_end(k.gb, gd)
    case .With:
        lw_with(k, s)
    case .Allocator:
        // (main's: its entry made the arena.)
    case .Match:
        lw_match(k, s)
    case .Break, .Continue:
        graph_build_loop_exit(k.gb, span, is_break = t.tag[s] == .Break)
    case:
        lw_unsupported(k, s, "this statement")
    }
}


// --- declarations ---------------------------------------------------------------

lw_decl :: proc(k: ^TC, s: Tree_Id, fields_of: ^Type_Scope = nil) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    v := decl_view(t, s)
    if len(v.targets) > 1 && len(v.values) == 1 {
        if fields_of != nil {
            names := make([]string, len(v.targets), context.temp_allocator)
            toks := make([]Token_Id, len(v.targets), context.temp_allocator)
            for tg, i in v.targets { names[i], toks[i] = tc_name(k, tg), t.main[tg] }
            graph_build_fields(b, names, toks, span)
        }
        lw_destructure(k, s, v.targets, v.values[0], true)
        return
    }
    if len(v.targets) > 1 && fields_of != nil {
        names := make([]string, len(v.targets), context.temp_allocator)
        toks := make([]Token_Id, len(v.targets), context.temp_allocator)
        for tg, i in v.targets { names[i], toks[i] = tc_name(k, tg), t.main[tg] }
        graph_build_fields(b, names, toks, span)
    }
    for tg, i in v.targets {
        lw_decl_one(k, s, tg, v.values[i] if i < len(v.values) else 0, v.type_, fields_of)
    }
}

// One name's declaration (tc_decl_one): its local, its value built into it,
// then stored at its type.
lw_decl_one :: proc(k: ^TC, s, target, value, ann_node: Tree_Id, fields_of: ^Type_Scope) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    name := tc_name(k, target)
    if name == "_" {
        // (`_ := v`: nothing declared — v built for its own sake, as `_ = v`;
        // a big one in a temporary of its own, on the arena.)
        if value == 0 { return }   // (`_ : T`: nothing at all)
        if _, held := lw_big_held(k, value, tc_node_type(k, value), .Explicit, span); held { return }
        lw_expr(k, value, .Value)
        return
    }
    ann: Type = Type_Any{}
    if ann_node != 0 { ann = tc_node_type(k, ann_node) }
    form, _, bindings := tc_decl_form(k, value, ann_node, ann)
    #partial switch form {
    case .Void:
        lw_decl_void(k, s, target, value, name, ann, fields_of)
        return
    case .Take:
        lw_decl_take(k, s, target, value, name, ann, fields_of)
        return
    case .Shape:
        lw_decl_shape(k, s, target, name, ann, bindings, fields_of)
        return
    case .Bare:
        lw_decl_bare(k, target, name, ann, span, lw_field_decl(k, fields_of, name, target, span))
        return
    }
    decl := lw_field_decl(k, fields_of, name, target, span)
    if decl == NO_NODE { decl = graph_build_decl(b, name, k.t.main[target], span, tc_node_type(k, target)) }
    vt := tc_node_type(k, value)
    final := tc_node_type(k, target)
    // (A partial array: zero first where its value fills a prefix of it —
    // text, a slice's elements, bytes read into it.)
    prefixed := is_partial_array(ann)
    #partial switch t.tag[value] {
    case .String, .Ident, .Field:
        if is_untyped(ann) { prefixed = true }
    }
    // (A text constant's name fills it as its text does: `s := GREETING`.)
    named_text := t.tag[tc_unparen(k, value)] != .String && lw_const_named(k, value) && is_partial_array(vt)
    fills := lw_fills_prefix(k, value, final) || named_text && is_partial_array(final)
    m, _ := tc_byte_node(k, value)
    reads := is_partial_array(final) && tc_byte_flow(k, final, value, vt) == .Read && (t.tag[m] == .Index || t.tag[m] == .Slice)
    zero := prefixed && (fills || reads)
    if zero { graph_build_zero_var(b, decl, final, span) }
    saved_field := k.field_default
    k.field_default = {}
    if fields_of != nil {
        sc := k.scopes[k.scope_of[fields_of]]
        k.field_default = {value = tc_unparen(k, value), name = name, t = ann, span = tree_span(t, sc.def)}
    }
    r := lw_expr(k, value, .Into, dest = graph_dest_var(decl, nil if is_untyped(ann) else ann, tc_sid(k, target)), temp_span = span)
    k.field_default = saved_field
    if !is_any(ann) { lw_byte_view_address(k, ann, value) }
    graph_build_typed(b, decl, final)
    wrote, zeroed := lw_store(k, value, vt, r, graph_dest_var(decl, final, tc_sid(k, target)), span, settle = true)
    if prefixed && (zeroed || wrote && fills) != zero { lw_fail(k, s, "a partial array zeroed first, or not, other than lowering found") }
    if zeroed && !prefixed { lw_fail(k, s, "a new partial array read from bytes") }
}

// `x : T` (tc_decl_bare): its zero — unset until written, no constructor run.
lw_decl_bare :: proc(k: ^TC, target: Tree_Id, name: string, ann: Type, span: Span, field: Node_Id) {
    b := k.gb
    if _, is_error := ann.(Type_Error); is_error { return }
    decl := field
    if decl == NO_NODE {
        decl = graph_build_decl(b, name, k.t.main[target], span, ann)
        graph_build_typed(b, decl, ann)
    } else if b.g.type_[decl] == 0 {
        graph_build_typed(b, decl, ann)
    }
    at := lw_at(k, target)
    defer b.at = at
    graph_build_bare(b, decl, ann, tree_span(k.t, target))
}

// A construction's arguments (tc_ctor_args): its params' defaults.
lw_ctor_args :: proc(k: ^TC, ts: ^Type_Scope, span: Span) -> []Operand {
    args := make([]Operand, len(ts.params), context.temp_allocator)
    for p, i in ts.params {
        if p.default_node == 0 { continue }
        args[i] = lw_default(k, p.default_node, p.type_, span, {sig = ts, param = i})
    }
    return args
}

// A default, built where what leaves it off runs it (tc_default).
lw_default :: proc(k: ^TC, def: Tree_Id, t: Type, span: Span, w: Graph_Widen) -> Operand {
    pin := lw_pin(k)
    defer k.gb.pin = pin
    use, at := lw_use_type(k, def, t, span)
    r := lw_expr(k, def, .Either, .Implied, dest = use, temp_span = at)
    return lw_value_as(k, def, tc_node_type(k, def), r, t, span, w)
}

// --- assignments ------------------------------------------------------------

lw_assign :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) > 1 && len(values) == 1 {
        lw_destructure(k, s, targets, values[0], false)
        return
    }
    if len(targets) > 1 && len(targets) == len(values) {
        lw_parallel_assign(k, s, targets, values)
        return
    }
    lw_assign_one(k, s, targets[0], values[0])
}

// One target's assignment (tc_assign_one).
lw_assign_one :: proc(k: ^TC, s, target, value: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    #partial switch t.tag[target] {
    case .Field:
        lw_field_assign(k, s, target, value)
        return
    case .Deref:
        lw_deref_assign(k, s, target, value)
        return
    case .Index:
        lw_index_assign(k, s, target, value)
        return
    case .Slice:
        lw_slice_assign(k, s, target, value)
        return
    }
    name := tc_name(k, target)
    if name == "_" {
        // (A big value dropped: built in a temporary of its own, on the arena.)
        if _, held := lw_big_held(k, value, tc_node_type(k, value), .Explicit, span); held { return }
        lw_expr(k, value, .Value)
        return
    }
    existing := tc_node_type(k, target)
    if tc_is_void(k, value) {
        graph_build_void_assign(b, name, lw_local(k, target), distinct_base(existing), span, tree_span(t, value))
        return
    }
    vt: Type = distinct_base(existing) if !is_untyped(existing) else nil
    r := lw_expr(k, value, .Into, dest = graph_dest_var(lw_local(k, target), vt, tc_sid(k, target)), temp = true, temp_span = span)
    lw_byte_view_address(k, existing, value)
    lw_store(k, value, tc_node_type(k, value), r, lw_parallel_hold(k, graph_dest_var(lw_local(k, target), distinct_base(existing), tc_sid(k, target)), span), span)
}

// `x op= v` (tc_compound): `x = x op v`, at the `op=`.
lw_compound :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    target := Tree_Id(t.a[s])
    r := tree_rec(t, t.b[s], 2)
    op_tok, value := Token_Id(r[0]), Tree_Id(r[1])
    #partial switch t.tag[target] {
    case .Field:
        lw_field_assign(k, s, target, value, op_tok)
        return
    case .Deref:
        lw_deref_assign(k, s, target, value, op_tok)
        return
    case .Index:
        lw_index_assign(k, s, target, value, op_tok)
        return
    }
    existing := tc_node_type(k, target)
    fr := lw_compound_value(k, s, op_tok, target, value, .Into)
    lw_store(k, 0, tc_node_type(k, s), fr, graph_dest_var(lw_local(k, target), distinct_base(existing), tc_sid(k, target)), span)
}

// A compound assignment's operation (tc_compound_value).
lw_compound_value :: proc(k: ^TC, s: Tree_Id, op_tok: Token_Id, target, value: Tree_Id, want: Build_Want) -> Built {
    op, _ := compound_assign_op(build_tokens[op_tok].kind)
    r := lw_binary_op(k, s, op, token_span(build_tokens[op_tok]), target, value, want, .Explicit, tc_node_type(k, s))
    if !r.ok { lw_fail(k, s, "a compound assignment's operation") }
    return r
}

// --- control flow -------------------------------------------------------------

// `return a, b` (tc_return): each value at its result's type.
lw_return :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    values := tree_list(t, t.a[s])
    rts := k.lower.ts.return_types[:] if k.lower.ts != nil else nil
    // (`return f()`, f's several results (tc_return): each of its outputs.)
    if len(values) == 1 {
        if returns := tc_call_returns(k, values[0]); len(returns) > 1 {
            r := lw_expr(k, values[0], .Value)
            graph_build_return_outputs(b, r.v, len(returns), span)
            return
        }
    }
    vals := make([dynamic]Operand, 0, len(values), context.temp_allocator)
    for val, i in values {
        want := rts[i]
        text, slot := false, NO_NODE
        vt := tc_node_type(k, val)
        // (Text — a literal, or a text constant's — in a zeroed temporary;
        // an array's value its result views, in a temporary.)
        named_text := false
        if is_partial_array(want) {
            named_text = t.tag[tc_unparen(k, val)] != .String && lw_const_named(k, val) && is_partial_array(vt)
            if t.tag[tc_unparen(k, val)] == .String || named_text {
                text, slot = true, graph_slot(b, "temp", want, span)
                graph_build_zero_var(b, slot, want, span)
            }
        }
        use, at := lw_use_type(k, val, want, span)
        held := NO_NODE
        if _, from_array := distinct_base(vt).(^Type_Fixed_Array); from_array && is_slice_type(want) && !lw_either_place(k, val, at) {
            held = graph_slot(b, "temp", vt, span)
        }
        r := lw_expr(k, val, .Either, dest = use, temp_span = at)
        if is_partial_array(want) && !text == built_is_text_constant(b, r) { lw_fail(k, val, "a text constant, or not one, other than lowering found") }
        if !text {
            append(&vals, lw_value_as(k, val, vt, r, want, span, {to = want}, held))
        } else {
            lw_store(k, val, vt, r, graph_dest_var(slot, want), span)
            append(&vals, graph_read(b, graph_var(b, slot, want, span), want, span))
        }
        lw_byte_view_address(k, want, val)
    }
    graph_build_return(b, vals[:], span)
}

// A condition's value, its node n's (is_condition_type): a bool's own; an
// error's, whether it failed — not Ok, as bool(e) has it.
lw_truth :: proc(k: ^TC, n: Tree_Id, v: Operand) -> Operand {
    if !is_err_type(tc_node_type(k, n)) { return v }
    return graph_op_value(k.gb, .Cast, .Implied, tree_span(k.t, n), Type_Bool{}, "bool", v)
}

// `if c {…} else {…}` (tc_if).
lw_if :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    v := if_view(t, s)
    cond := lw_expr(k, v.cond, .Value)
    fi := graph_build_if(b, lw_truth(k, v.cond, cond.v), span, len(v.else_) > 0, lw_scope_arena(k, v.then, b.body.returned))
    lw_scope(k, v.then)
    graph_build_else(b, &fi, span, lw_scope_arena(k, v.else_, b.body.returned))
    if len(v.else_) > 0 { lw_scope(k, v.else_) }
    graph_build_if_end(b, &fi)
}

// `with &a {…}` (tc_with): a block of its own that sets the arena slot to a
// — arena_swap, the one it held kept — and puts that back by a defer of its
// own at every way out; inside it the body's block, so the body's arena
// marks and resets are a's, done before the slot is put back.
lw_with :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    swap := tc_arena_swap(k.table)
    if swap == nil { lw_fail(k, s, "a `with` with no arena_swap") }
    pt := fn_primary_return(swap)
    p := Tree_Id(t.a[s])
    body := tree_list(t, t.b[s])
    outer := graph_build_block_open(b, "with", span, false)
    r := lw_expr(k, p, .Value)
    // (A pointer to the arena, as arena_swap takes any: its address alone.)
    arg := graph_op_value(b, .Cast, .Synthetic, span, pt, "", r.v)
    was := Operand{graph_call_op(b, .Call, .Synthetic, span, swap, pt, arg), 0}
    slot := graph_slot(b, "with", nil, span)
    graph_build_write_at(b, graph_var(b, slot, nil, span), was, span)
    graph_build_typed(b, slot, pt)
    gd := graph_build_defer(b, span, false, false)
    back := graph_read(b, graph_var(b, slot, pt, span), pt, span)
    graph_call_op(b, .Call, .Synthetic, span, swap, pt, back)
    graph_build_defer_end(b, gd)
    inner := graph_build_block_open(b, "with body", span, lw_scope_arena(k, body, b.body.returned))
    lw_scope(k, body)
    graph_build_block_close(b, inner)
    graph_build_block_close(b, outer)
}

// A loop (tc_for): its block, its variables, then its runs.
lw_for :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    v := for_view(t, s)
    tag := t.tag[s]
    // (A loop variable named `_` is none: the loop counts, or walks, for no one.)
    named :: proc(tok: Token_Id) -> Token_Id { return tok if tok != 0 && tc_text(tok) != "_" else 0 }
    var_tok, elem_tok, index_tok := named(v.var), named(v.elem), named(v.index)
    fl := graph_build_for(b, {span = span, var_name = tc_text(var_tok) if var_tok != 0 else "",
                            elem_name = tc_text(elem_tok) if elem_tok != 0 else "",
                            index_name = tc_text(index_tok) if index_tok != 0 else "",
                            var_tok = var_tok, elem_tok = elem_tok, index_tok = index_tok,
                            is_range = tag == .For_Range, has_cond = v.cond != 0, has_step = v.post != 0,
                            end_literal = v.hi != 0 && t.tag[tc_unparen(k, v.hi)] == .Number,
                            body_arena = lw_scope_arena(k, v.body, b.body.returned)})
    defer graph_build_for_end(b, &fl)
    walk: LW_Walk   // (a plain place collection's: what the loop's runs walk)
    #partial switch tag {
    case .For_Each:
        ct: Type
        coll := NO_VALUE
        if !lw_pure_place(k, v.collection) {
            ct = lw_loop_items(k, &fl, v.collection)
        } else {
            // (A plain place: viewed once, where the loop begins; else built
            // where each run walks it.)
            ct = tc_node_type(k, v.collection)
            if graph_loop_view_of(ct) != nil {
                coll = lw_expr(k, v.collection, .Place).v
            } else {
                walk = {k, v.collection}
                fl.walk, fl.walk_data = lw_walk_place, &walk
            }
        }
        elem := loop_elem_through(ct)
        if elem == nil { elem = Type_Error{} }
        if v.type_ != 0 { elem = tc_node_type(k, v.type_) }
        graph_build_for_collection(b, &fl, coll, ct, tc_is_self(k, v.collection), distinct_base(elem))
        lw_scope(k, v.body)
    case .For_Range:
        // (Its counter's type: as written, else its bounds'.)
        lt, ht := tc_node_type(k, v.lo), tc_node_type(k, v.hi)
        ct := distinct_base(range_counter(lt, ht, tc_node_type(k, v.type_) if v.type_ != 0 else nil))
        graph_build_range_counter(b, &fl)
        lo := lw_expr(k, v.lo, .Value)
        fl.lo = graph_build_range_bound(b, lo.v, lt, ct, span)
        hi := lw_expr(k, v.hi, .Value)
        fl.high = hi.v
        fl.hi = graph_build_range_bound(b, hi.v, ht, ct, span)
        graph_build_range(b, &fl, ct)
        lw_scope(k, v.body)
    case:
        if v.init != 0 { lw_stmt(k, v.init) }
        graph_build_for_runs(b, &fl)
        cond := lw_expr(k, v.cond, .Value)
        graph_build_for_cond(b, &fl, lw_truth(k, v.cond, cond.v))
        lw_scope(k, v.body)
        if v.post != 0 {   // (its step, after its body: where it runs)
            graph_build_for_step(b, &fl)
            lw_stmt(k, v.post)
        }
    }
}

// A plain place, built again where a loop's run walks it (Graph_For.walk).
LW_Walk :: struct {
    k: ^TC,
    n: Tree_Id,
}

lw_walk_place :: proc(data: rawptr, span: Span) -> Operand {
    walk := (^LW_Walk)(data)
    return lw_expr(walk.k, walk.n, .Place).v
}

// A loop's collection that is no plain place: held in the
// loop's own local, or viewed.
lw_loop_items :: proc(k: ^TC, fl: ^Graph_For, e: Tree_Id) -> Type {
    b := k.gb
    graph_build_items(b, fl)
    tag := k.t.tag[tc_unparen(k, e)]
    #partial switch tag {
    case .Array, .Literal:
        t := solidify_type(lw_store_into(k, e, graph_dest_var(fl.coll_slot, nil), fl.span))
        if graph_loop_view_of(t) != nil { lw_fail(k, e, "a literal loop over its view") }
        graph_build_typed(b, fl.coll_slot, t)
        return t
    }
    t := tc_node_type(k, e)
    view := graph_loop_view_of(t)
    // (A value viewed: held in a temporary made before it — zero first when
    // it fills a prefix of a partial array.)
    held := NO_NODE
    if view != nil && !lw_either_place(k, e) {
        held = graph_slot(b, "temp", t, fl.span)
        if lw_fills_prefix(k, e, t) { graph_build_zero_var(b, held, t, fl.span) }
    }
    r := lw_expr(k, e, .Either)
    if view != nil {
        if r.place != (held == NO_NODE) { lw_fail(k, e, "a loop's collection, a place or not, other than lowering found") }
        graph_build_items_view(b, fl, held, r.v, r.place, t, view, tc_is_self(k, e))
    } else {
        graph_build_typed(b, fl.coll_slot, t)
        lw_store(k, e, t, r, graph_dest_var(fl.coll_slot, t), fl.span)
    }
    return t
}

// A value built into a destination, then stored there.
lw_store_into :: proc(k: ^TC, e: Tree_Id, d: Dest, span: Span, settle := false) -> Type {
    r := lw_expr(k, e, .Into, dest = d, temp_span = span)
    t := tc_node_type(k, e)
    lw_store(k, e, t, r, d, span, settle)
    return t
}

// --- expressions ----------------------------------------------------------------

// An expression built as its use asks (tc_check): its value, its place, either,
// or into a destination.
lw_expr :: proc(k: ^TC, n: Tree_Id, want := Build_Want.Value, w := Written.Explicit,
                dest := Dest{}, temp := false, temp_span := Span{}) -> Built {
    if n == 0 { return {} }
    b := k.gb
    at := lw_at(k, n)
    defer b.at = at
    // (A compound assignment's target, read in its operation: through the
    // place already built.)
    if n == k.lower.compound.target {
        t := tc_node_type(k, n)
        span := tree_span(k.t, n)
        if want == .Value { return {v = graph_read(b, k.lower.compound.place, t, span), ok = true} }
        return {v = k.lower.compound.place, place = true, ok = true}
    }
    if want == .Place && lw_holds(k, n) {
        p := lw_hold(k, n, temp_span if temp_span != {} else tree_span(k.t, n))
        return {v = p, place = true, ok = p != NO_VALUE}
    }
    r := lw_expr_impl(k, n, want, w, dest, temp, temp_span)
    if !r.ok { lw_fail(k, n, fmt.tprintf("a %v lowering builds nothing for", k.t.tag[n])) }
    return r
}

lw_expr_impl :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span) -> Built {
    t := k.t
    b := k.gb
    span := tree_span(t, n)
    ty := tc_node_type(k, n)
    #partial switch t.tag[n] {
    case .Number:
        return lw_number(k, n, span, false, want, w)
    case .String:
        text := token_text(build_tokens[t.main[n]])
        g := graph_text(b, graph_op_value(b, .Global, w, span, ty), Const_Value{text = text, is_text = true})
        return {v = g, place = want == .Place, ok = true}
    case .Char:
        text := token_text(build_tokens[t.main[n]])
        if want == .Place { return {} }
        return {v = graph_const(b, w, span, Type_Utf8{}, "", Const_Value{int = i128(text[0]) if len(text) > 0 else 0}), ok = true}
    case .True, .False:
        if want == .Place { return {} }
        return {v = graph_const(b, w, span, Type_Bool{}, "", Const_Value{int = 1 if t.tag[n] == .True else 0}), ok = true}
    case .Paren, .Big_Endian:
        return lw_expr(k, Tree_Id(t.a[n]), want, w, dest, temp, temp_span)
    case .Ident, .Type_Name:
        return lw_ident(k, n, want, w, dest, temp, temp_span)
    case .Unary:
        if m := Tree_Id(t.a[n]); build_tokens[t.main[n]].kind == .Ampersand && t.tag[m] == .Method_Call {
            lw_at(k, m)   // (the call's; the `&`, its receiver's address)
            return lw_call(k, m, want, w, dest, temp, temp_span, addressed = n)
        }
        return lw_unary(k, n, want, w)
    case .Deref:
        r := lw_expr(k, Tree_Id(t.a[n]), .Place, w, temp_span = span)
        p := graph_op_value(b, .Deref, .Explicit, span, ty, "", r.v)
        if want == .Value { return {v = graph_read(b, p, ty, span), ok = true} }
        return {v = p, place = true, ok = true}
    case .Binary:
        if given := k.annot.args[tc_sid(k, n)] or_else nil; len(given) == 2 && given[0].kind == .Built_Into {
            return lw_join_in_place(k, n, tc_callee(k, n), want, w, dest, temp, span)
        }
        return lw_binary_op(k, n, build_tokens[t.main[n]].kind, span, Tree_Id(t.a[n]), Tree_Id(t.b[n]), want, w, ty)
    case .Call, .Method_Call:
        return lw_call(k, n, want, w, dest, temp, temp_span)
    case .Assert:
        return lw_assert(k, n, want, w)
    case .If_Expr:
        return lw_if_expr(k, n, want, w)
    case .Dot_Ident:
        if tc_sid(k, n) in k.annot.dot_bases { return lw_field(k, n, want, w, dest, temp, temp_span) }
        return lw_variant_of(k, ty, tc_text(Token_Id(t.a[n])), span, want, w, dest, temp, temp_span)
    case .Field:
        return lw_field(k, n, want, w, dest, temp, temp_span)
    case .Literal, .Broadcast:
        return lw_literal(k, n, want, w, dest, temp, temp_span)
    case .Self:
        return lw_self(k, n, want, w)
    case .Index:
        return lw_index(k, n, want)
    case .Slice:
        return lw_slice(k, n, want, w, dest)
    case .Array:
        return lw_array_literal(k, n, want, w, dest, temp, temp_span)
    case .Take:
        return lw_take(k, n, want, w)
    case .In_Range:
        return lw_in_range(k, n, want, w)
    case .Size_Of:
        return lw_size_of(k, n, want, w)
    case .Hash_Name:
        return lw_hash_name(k, n, want, w, span)
    case .Try:
        if want == .Place { return {} }
        r := lw_expr(k, Tree_Id(t.a[n]), .Value, w)
        if !r.ok { return {} }
        return {v = graph_try_after(b, span, r.v), ok = true}
    }
    lw_unsupported(k, n, "this expression")
}

// A number (tc_number), negated: `-3` (reported at the `-`).
lw_number :: proc(k: ^TC, n: Tree_Id, span: Span, negate: bool, want: Build_Want, w: Written) -> Built {
    text := token_text(build_tokens[k.t.main[n]])
    f, i, _ := parse_number_text(text)
    is_float := strings.index_byte(text, '.') >= 0
    if negate { f, i = -f, -i }
    if want == .Place { return {} }
    t := tc_node_type(k, n)   // (its width, its use's: tc_settle)
    if t == nil { lw_fail(k, n, "a number the checker never typed") }
    return {v = graph_const(k.gb, w, span, t, "", Const_Value{int = i, float = f, is_float = is_float}, untyped = true), ok = true}
}

// Whether a name of type `t` names a fun — a fun's, a struct's constructor's
// — and so its global (lw_ident): what it refers to says, a variable that
// holds one doesn't.
lw_names_fun :: proc(k: ^TC, n: Tree_Id, t: Type) -> bool {
    ts, is_scope := t.(^Type_Scope)
    if !is_scope || ts.is_module { return false }
    #partial switch tc_ref(k, n).kind {
    case .Fun:  return true
    case .Type: return ts.kind == .Fun || len(ts.params) > 0
    }
    return false
}

// A name (tc_ident): a variant, a constant, `void`, a fun's name as a value,
// else a variable — its place, or read.
lw_ident :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span) -> Built {
    b := k.gb
    name := tc_name(k, n)
    span := tree_span(k.t, n)
    t := tc_node_type(k, n)
    ref := tc_ref(k, n)
    switch {
    case ref.kind == .Variant:
        return lw_variant_of(k, t, name, span, want, w, dest, temp, temp_span)
    case ref.kind == .Const:
        return lw_const_use(k, lw_const_of(k, n, ref.decl), n, t, want, w)
    case name == "void":
        if want == .Place { return {} }
        return {v = graph_const(b, w, span, t, "void", nil), ok = true}
    case ref.kind == .Type && tc_sid(k, n) in k.annot.known:
        // (A generic's size param: the size it was bound to.)
        if want == .Place { return {} }
        kv := k.annot.known[tc_sid(k, n)]
        return {v = graph_const(b, w, span, t, name, Const_Value{int = kv.value}, untyped = true), ok = true}
    }
    if ts, is_scope := t.(^Type_Scope); is_scope && !ts.is_module {
        if lw_names_fun(k, n, t) {
            if want == .Place { return {} }
            return {v = graph_op_value(b, .Global, w, span, t, name), ok = true}
        }
    }
    // (A module's or a type's name is no value: what a field reads through
    // it is built, lw_field.)
    if ref.kind == .Module || ref.kind == .Type { return {} }
    place := graph_var(b, lw_local(k, n), t, span)
    if want == .Value { return {v = graph_read(b, place, t, span), ok = true} }
    return {v = place, place = true, ok = true}
}

// A variant's value, by its name: an enum's, or a union's tag.
lw_variant_value :: proc(t: Type, name: string) -> int {
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:  return v.variants[name]
    case ^Type_Union: return v.tag_map[name]
    }
    return 0
}

// Each constant by its instance and the token that declares it
// (TC.const_by_decl): made before any code is lowered, which only reads it.
lw_const_index :: proc(k: ^TC) {
    for _, kc in k.consts { k.const_by_decl[lw_const_key(u64(kc.sid) >> 32, k.t.main[kc.def])] = kc }
    for _, list in k.scope_consts { for _, kc in list { k.const_by_decl[lw_const_key(u64(kc.sid) >> 32, k.t.main[kc.def])] = kc } }
}

@(private="file")
lw_const_key :: proc(salt: u64, decl: Token_Id) -> u64 { return salt << 32 | u64(decl) }

// The constant a declaring token names.
// (A body's constant in a generic's instance is that instance's own: the
// use's instance first, then the tree's.)
lw_const_of :: proc(k: ^TC, use: Tree_Id, decl: Token_Id) -> ^TC_Const {
    kc := k.const_by_decl[lw_const_key(u64(tc_instance(k, use)), decl)] or_else nil
    if kc == nil { kc = k.const_by_decl[lw_const_key(0, decl)] or_else nil }
    if kc == nil { graph_fatal(Span{at = decl}, "lower: no constant is declared here") }
    return kc
}

// Its place, when it has none: a temporary made first — zero first where
// its value fills a prefix of it — the value stored in it.
lw_hold :: proc(k: ^TC, n: Tree_Id, span: Span) -> Operand {
    b := k.gb
    t := tc_node_type(k, n)
    slot := graph_slot(b, "temp", nil, span)
    if lw_fills_prefix(k, n, t) { graph_build_zero_var(b, slot, t, span) }
    d := graph_dest_var(slot, nil)
    r := lw_expr(k, n, .Into, dest = d, temp_span = span)
    lw_store(k, n, t, r, d, span)
    graph_build_typed(b, slot, t)
    return graph_var(b, slot, t, span)
}

// `(x + a) + b`, a join onto a join (tc_note_join_in_place): built where it
// goes — a fresh destination, else a temporary (`x = y + "-" + x` would
// read x after its first part overwrote it: an assignment's is `temp`) —
// the left join's result there first (a join onto a join itself: there in
// place too), then b appended into it by `add`, the call the checker chose,
// as `&it + b` would: a chain builds one list, x copied once, no list per
// `+`.
lw_join_in_place :: proc(k: ^TC, n: Tree_Id, add: ^Type_Scope, want: Build_Want, w: Written, dest: Dest, temp: bool, span: Span) -> Built {
    b := k.gb
    t := k.t
    jt := tc_node_type(k, n)
    left, right := Tree_Id(t.a[n]), Tree_Id(t.b[n])
    into := want == .Into && !temp
    target := dest
    slot := NO_NODE
    if !into {
        slot = graph_slot(b, "join", nil, span)
        target = graph_dest_var(slot, nil)
    }
    r := lw_expr(k, left, .Into, w, dest = target)
    at := graph_dest_place(b, target, span)
    if !r.into { graph_build_write_at(b, at, lw_value(k, r, left, tc_node_type(k, left)), span) }
    addr := graph_op_value(b, .Address, w, span, type_ptr(jt), "", at)
    rr := lw_expr(k, right, .Either, w)
    a0 := graph_build_as(b, addr, false, type_ptr(jt), span, span, {sig = add, param = 0})
    a1 := graph_build_as(b, rr.v, rr.place, tc_node_type(k, right), tree_span(t, right), span, {sig = add, param = 1})
    graph_call_op(b, .Call, w, span, add, fn_primary_return(add), a0, a1)
    if into { return {ok = true, into = true} }
    graph_build_typed(b, slot, jt)
    p := graph_var(b, slot, jt, span)
    if want == .Value { return {v = graph_read(b, p, jt, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// A unary operation (tc_unary); `of`: the operand in place of its own.
lw_unary :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, of := Tree_Id(0)) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    op := build_tokens[tr.main[n]].kind
    operand := of if of != 0 else Tree_Id(tr.a[n])
    if op == .Minus && tr.tag[operand] == .Number { return lw_number(k, operand, span, true, want, w) }
    if want == .Place { lw_fail(k, n, "a unary's place") }
    either := op == .Minus
    ask: Build_Want = .Place if op == .Ampersand else .Either if either else .Value
    r := lw_expr(k, operand, ask, w, temp_span = span)
    ot := tc_node_type(k, operand)
    // (Its type as tc_unary makes it — `&x.f()`'s node is annotated with the
    // call's.)
    t: Type
    #partial switch op {
    case .Not:       t = Type_Bool{}
    case .Ampersand: t = new_clone(Type_Ptr{elem = ot})
    case:            t = ot
    }
    if callee := tc_callee(k, n); callee != nil && of == 0 {
        // (`overload -`: a function of the one operand.)
        ret := fn_primary_return(callee)
        arg: Operand
        if len(callee.params) > 0 {
            pt := callee.params[0].type_
            arg = lw_value_as(k, operand, ot, r, pt, span, {to = pt})
        } else {
            arg = lw_value(k, r, operand, ot)
        }
        kind: Op_Kind = .Construct if callee.kind == .Struct else .Call
        return {v = {graph_call_op(b, kind, w, span, callee, ret, arg), 0}, ok = true}
    }
    if op == .Ampersand {
        a := graph_op_value(b, .Address, w, span, t, "", r.v)
        if tc_byte_index(k, operand) { k.lower.byte_addrs[tc_sid(k, n)] = {a.op, r.v.op} }
        return {v = a, ok = true}
    }
    v := r.v
    if either { v = lw_value(k, r, operand, ot) }
    if op == .Not { v = lw_truth(k, operand, v) }
    return {v = graph_op_value(b, .Unary, w, span, t, graph_token_text(op), v), ok = true}
}

// `left op right` (tc_binary_op): each side at the type the operation works
// in; `and` / `or` short-circuit. `at`: its node (a Binary, a compound
// assignment); `t`: its type.
lw_binary_op :: proc(k: ^TC, at: Tree_Id, tok: Token_Kind, span: Span, left, right: Tree_Id,
                     want: Build_Want, w: Written, t: Type, in_range: ^TC_In_Range = nil) -> Built {
    tr := k.t
    b := k.gb
    op := tok
    #partial switch tok {   // (wrapping: the operation's, its word the token's)
    case .Wrap_Plus:  op = .Plus
    case .Wrap_Minus: op = .Minus
    case .Wrap_Star:  op = .Star
    }
    if want == .Place { lw_fail(k, at, "a binary's place") }
    sides: [2]Operand
    types: [2]Type
    arrays: [2]bool
    and_or := op == .And || op == .Or
    // (Each side at the type it is taken at: an overload's param, else the
    // operation's working type.)
    callee: ^Type_Scope
    if at != 0 { callee = tc_callee(k, at) }
    work := Graph_Work{op, t, tc_node_type(k, left), tc_node_type(k, right)}
    sa: Graph_And
    if and_or { sa = graph_build_and(b, op == .And, w, span) }
    for side, i in ([2]Tree_Id{left, right}) {
        if and_or {
            // (A side: its expression; an `in`'s, its comparison.)
            r: Built
            switch {
            case in_range == nil: r = lw_expr(k, side, .Value, w)
            case i == 0:          r = lw_binary_op(k, 0, .Greater_Equal, in_range.span, in_range.value, in_range.lo, .Value, w, Type_Bool{})
            case:                 r = lw_binary_op(k, 0, .Less, in_range.span, in_range.value, in_range.hi, .Value, w, Type_Bool{})
            }
            types[i] = tc_node_type(k, side)
            sides[i] = r.v if in_range != nil else lw_truth(k, side, r.v)
            if i == 0 { graph_build_and_left(b, &sa, sides[i]) }
            continue
        }
        if callee != nil && i < len(callee.params) {
            if v, made := lw_text_as_list(k, side, callee.params[i].type_, span, w); made {
                types[i] = callee.params[i].type_
                sides[i] = v
                continue
            }
        }
        r := lw_expr(k, side, .Either, w)
        st := tc_node_type(k, side)
        types[i] = st
        if tr.tag[tc_unparen(k, side)] == .Array { lw_fail(k, side, "an array literal as an operand") }
        _, is_array := distinct_base(st).(^Type_Fixed_Array)
        arrays[i] = is_array && !r.place
        as := Graph_Widen{work = work, binary = true}
        if callee != nil { as = {sig = callee, param = i} if i < len(callee.params) else {} }
        at := lw_at(k, side)   // (its read and its widening: the side's)
        sides[i] = graph_build_as(b, r.v, r.place, st, tree_span(tr, side), span, as)
        b.at = at
    }
    if callee != nil {
        ret := fn_primary_return(callee)
        kind: Op_Kind = .Construct if callee.kind == .Struct else .Call
        return {v = {graph_call_op(b, kind, w, span, callee, ret, sides[0], sides[1]), 0}, ok = true}
    }
    if and_or { return {v = graph_build_and_end(b, &sa, sides[1]), ok = true} }
    kind: Op_Kind = .Compare if is_comparison_op(op) else .Arith
    return {v = graph_op_value(b, kind, w, span, t, graph_token_text(tok), sides[0], sides[1]), ok = true}
}

// `assert(c)` (tc_assert). With `-no assert`, behind `if false`: the
// analyses still see what its condition reads, and it never runs.
lw_assert :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    t := k.t
    span := tree_span(t, n)
    cond := Tree_Id(t.a[n])
    if want != .Value { lw_fail(k, n, "an assert's place") }
    off: Graph_If
    if k.no_assert {
        never := graph_const(k.gb, .Synthetic, span, Type_Bool{}, "", Const_Value{int = 0})
        off = graph_build_if(k.gb, never, span, false, false)
    }
    defer if k.no_assert {
        graph_build_else(k.gb, &off, span, false)
        graph_build_if_end(k.gb, &off)
    }
    r := lw_expr(k, cond, .Value, w)
    lo, hi := int(t.first[cond]), int(t.end[cond])
    sides: Maybe([2]string)
    // (A comparison, written bare: each side's text, either side of its operator.)
    if t.tag[cond] == .Binary && is_comparison_op(build_tokens[t.main[cond]].kind) {
        at := int(t.main[cond])
        sides = [2]string{
            "" if tc_is_literal(k, Tree_Id(t.a[cond])) else token_range_text(lo, at),
            "" if tc_is_literal(k, Tree_Id(t.b[cond])) else token_range_text(at + 1, hi),
        }
    }
    graph_assert(k.gb, span, token_range_text(lo, hi), lw_truth(k, cond, r.v), w, sides)
    return {v = NO_VALUE, ok = true}
}

// `if c do a else b` as a value (tc_if_expr): its local, the condition,
// each branch written to the local at the if's type, then the local.
lw_if_expr :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    cond_n := Tree_Id(tr.a[n])
    then_n, else_n := tree_pair(tr, n)
    slot := graph_slot(b, "if", nil, span)
    cond := lw_expr(k, cond_n, .Value, w)
    gi := graph_build_if_expr(b, lw_truth(k, cond_n, cond.v), w, span)
    types: [2]Type
    t := tc_node_type(k, n)
    for branch, i in ([2]Tree_Id{then_n, else_n}) {
        if i == 1 { graph_build_if_expr_else(b, &gi) }
        // (Zero first where it fills a prefix of a partial array.)
        if lw_may_fill_prefix(k, branch) && lw_fills_prefix(k, branch, t) {
            graph_build_zero_var(b, slot, t, span)
        }
        r := lw_expr(k, branch, .Into, dest = graph_dest_var(slot, nil))
        types[i] = tc_node_type(k, branch)
        if r.into { continue }
        if lw_builds_into(k, branch) || tc_byte_index(k, branch) { lw_fail(k, branch, "an if's branch built in place, or of bytes") }
        val := graph_build_widen(b, lw_value(k, r, branch, types[i]), span, {to = t})
        graph_build_write_at(b, graph_var(b, slot, nil, span), val, span)
    }
    graph_build_if_expr_end(b, &gi)
    for bt in types {
        if view_kind(t, bt) != .None { lw_fail(k, n, "an if's branch viewed") }
    }
    lt := t
    if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array && is_infer(fa.elem) { lt = solidify_type(t) }   // (one of open elements no use typed: the default's)
    graph_build_typed(b, slot, lt)
    p := graph_var(b, slot, lt, span)
    if want == .Value { return {v = graph_read(b, p, lt, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// --- calls --------------------------------------------------------------------

// A call (tc_call); asked for its place, stored in a temporary made first.
lw_call :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span, addressed := Tree_Id(0)) -> Built {
    b := k.gb
    if want != .Place { return lw_call_impl(k, n, want, w, dest, temp, temp_span, addressed) }
    at := temp_span if temp_span != {} else tree_span(k.t, n)
    slot := graph_slot(b, "temp", nil, at)
    r := lw_call_impl(k, n, .Into, w, graph_dest_var(slot, nil), temp, at, addressed)
    if !r.ok { lw_fail(k, n, "a call's place") }
    t := tc_node_type(k, n)
    if !r.into { graph_build_write_at(b, graph_var(b, slot, nil, at), r.v, at) }
    graph_build_typed(b, slot, t)
    return {v = graph_var(b, slot, t, at), place = true, ok = true}
}

lw_call_impl :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, dest: Dest, temp: bool, temp_span: Span, addressed := Tree_Id(0)) -> Built {
    if k.t.tag[n] == .Method_Call { return lw_method_call(k, n, want, w, dest, temp, temp_span, addressed) }
    saved := k.lower.recv
    k.lower.recv = {}
    defer k.lower.recv = saved
    return lw_call_core(k, n, tc_name(k, n), tree_list(k.t, k.t.a[n]), want, w, dest, temp, temp_span)
}

// A call of what its annotation says it calls (tc_call_core): a builtin, a
// fun, a struct's constructor, a fun's value; its arguments as its params
// receive them.
lw_call_core :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, want: Build_Want, w: Written,
                     dest: Dest, temp: bool, temp_span: Span) -> Built {
    tr := k.t
    b := k.gb
    span := tree_span(tr, n)
    form, has_form := k.annot.forms[tc_sid(k, n)]
    if !has_form { lw_fail(k, n, "a call of no form annotated") }
    switch form {
    case .Builtin:
        return lw_builtin(k, n, name, args, want, w)
    case .Conversion:
        // (`Id(x)`, Id a distinct type: x, seen as Id.)
        if want == .Place { lw_fail(k, n, "a conversion's place") }
        to := tc_node_type(k, n)
        if pa, is_pa := distinct_base(to).(^Type_Partial_Array); is_pa && len(args) == 1 {
            from := distinct_base(tc_node_type(k, args[0]))
            _, from_pa := from.(^Type_Partial_Array)
            if from_pa || is_slice_type(from) { return lw_into_partial(k, args[0], to, pa, want, w, span) }
        }
        r := lw_expr(k, args[0], .Value, w)
        return {v = graph_op_value(b, .Cast, w, span, tc_node_type(k, n), name, r.v), ok = true}
    case .Fun, .Value, .Dispatch, .Generic:   // (a dispatch's member, a generic's instance: a fun called)
    }
    if want == .Place { lw_fail(k, n, "a call's place") }
    ft := tc_callee(k, n)
    indirect := form == .Value
    is_struct := ft.kind == .Struct
    overrides := Tree_Id(tr.b[n]) if tr.tag[n] == .Call else method_view(tr, n).overrides
    dest := dest
    into_temp := false
    if is_struct && want == .Into && temp {
        dest = graph_build_temp(b, temp_span, build_temp_type(dest))
        into_temp = true
    }
    view_slot := NO_NODE
    if !is_struct && !indirect && want == .Into {
        if ret := fn_primary_return(ft); ret != nil && is_slice_type(graph_dest_type(b, dest)) {
            if _, from_array := distinct_base(ret).(^Type_Fixed_Array); from_array { view_slot = graph_slot(b, "temp", ret, temp_span) }
        }
    }
    ops := make([dynamic]Operand, 0, len(args), context.temp_allocator)
    given := k.annot.args[tc_sid(k, n)] or_else nil
    for arg, i in given {
        a := arg.node
        pin := lw_pin(k) if arg.kind == .Default || arg.kind == .Call_Site else k.gb.pin   // (a default: lowered here, the call's)
        defer k.gb.pin = pin
        pt := ft.params[i].type_
        use, use_at := lw_use_type(k, a, pt, span)
        if arg.kind == .Written {
            if v, made := lw_text_as_list(k, a, pt, span, w); made {
                append(&ops, v)
                continue
            }
        }
        if arg.kind == .Receiver {
            if !k.lower.recv.r.ok { lw_fail(k, a, "a receiver taken as an argument, never built") }
            append(&ops, lw_value_as(k, a, k.lower.recv.t, k.lower.recv.r, pt, span, {sig = ft, param = i}))
        } else {
            at := tc_node_type(k, a)
            #partial switch arg.kind {
            case .Call_Site:
                at = lw_hash_name_type(k, a)
            case .Default:
                if arg.slot >= 0 {
                    if returns := tc_call_returns(k, a); len(returns) > 1 { at = returns[arg.slot] }
                }
            }
            // (An array's value its param views: held in a temporary. A
            // call site's name and a shared default's output are values.)
            held := NO_NODE
            if _, from_array := distinct_base(at).(^Type_Fixed_Array); from_array && is_slice_type(pt) {
                place := arg.kind != .Call_Site && !(arg.kind == .Default && arg.slot >= 0) && lw_either_place(k, a, use_at)
                if !place { held = graph_slot(b, "temp", at, span) }
            }
            r: Built
            switch arg.kind {
            case .Call_Site:
                // (`#caller_name`: the call site's — at the `_`, else the call.)
                r = lw_hash_name(k, a, .Either, w, tree_span(tr, args[i]) if i < len(args) else span)
            case .Default:
                if arg.slot >= 0 {
                    r = lw_tuple_default(k, a, int(arg.slot), .Implied)
                } else {
                    r = lw_expr(k, a, .Either, .Implied, dest = use, temp_span = use_at)
                }
            case .Built_Into:
                lw_fail(k, a, "a join's left side built into a call (lw_join_in_place's)")
            case .Written, .Receiver:
                held_big := false
                if held == NO_NODE { r, held_big = lw_big_held(k, a, at, w, span) }
                if !held_big { r = lw_expr(k, a, .Either, w, dest = use, temp_span = use_at) }
            }
            append(&ops, lw_value_as(k, a, at, r, pt, span, {sig = ft, param = i}, held))
        }
        lw_byte_view_address(k, pt, a)
    }
    // (A union's variant built by its params: built as the union, tc_variant_call.)
    if ut, is_union := distinct_base(tc_node_type(k, n)).(^Type_Union); is_union && is_struct {
        return lw_variant_call(k, n, ut, ft, ops[:], want, w, dest, into_temp, temp_span, overrides, made = into_temp)
    }
    if is_struct {
        if into_temp {
            return lw_construct(k, n, ft, ops[:], .Into, w, dest, true, temp_span, made = true, overrides = overrides)
        }
        return lw_construct(k, n, ft, ops[:], want, w, dest, false, temp_span, overrides = overrides)
    }
    ret := fn_primary_return(ft)
    if indirect { return {v = graph_build_indirect(b, name, lw_local(k, n), ft, ret, ops[:], w, span), ok = true} }
    call := Operand{graph_call_op(b, .Call, w, span, ft, ret, ..ops[:]), 0}
    if view_slot != NO_NODE {
        graph_build_write_at(b, graph_var(b, view_slot, ret, temp_span), call, temp_span)
        return {v = graph_var(b, view_slot, ret, temp_span), place = true, ok = true}
    }
    return {v = call, ok = true}
}

// Text written in place — a literal, a text constant's — taken by value as a
// list (a param's, an operator's side: `"abc" + "de"`): in a zeroed
// temporary of that list's type, written in, as a return's is — the list's
// room, not the text's own bytes'. false: not text, or not to a list.
lw_text_as_list :: proc(k: ^TC, e: Tree_Id, to: Type, span: Span, w: Written) -> (Operand, bool) {
    b := k.gb
    t := k.t
    if !is_partial_array(to) { return {}, false }
    et := tc_node_type(k, e)
    literal := t.tag[tc_unparen(k, e)] == .String
    if !literal && !(lw_const_named(k, e) && is_partial_array(et)) { return {}, false }
    slot := graph_slot(b, "temp", to, span)
    graph_build_zero_var(b, slot, to, span)
    r := lw_expr(k, e, .Either, w)
    lw_store(k, e, et, r, graph_dest_var(slot, to), span)
    return graph_read(b, graph_var(b, slot, to, span), to, span), true
}

// `Path(view)`: a partial array made of a slice's items (or a smaller
// partial array's) — as many as fit, as `p = view` writes them — a fresh
// one, to add to (`Path(dir) + "/" + name`).
lw_into_partial :: proc(k: ^TC, arg: Tree_Id, to: Type, pa: ^Type_Partial_Array, want: Build_Want, w: Written, span: Span) -> Built {
    b := k.gb
    slot := graph_slot(b, "made", nil, span)
    graph_build_typed(b, slot, to)
    graph_build_zero_var(b, slot, to, span)
    r := lw_expr(k, arg, .Either, w)
    v := graph_build_as(b, r.v, r.place, tc_node_type(k, arg), tree_span(k.t, arg), span, {to = type_slice(pa.elem)})
    graph_build_write_at(b, graph_var(b, slot, to, span), v, span)
    p := graph_var(b, slot, to, span)
    if want == .Value { return {v = graph_read(b, p, to, span), ok = true} }
    return {v = p, place = true, ok = true}
}

// A builtin (tc_builtin): print, crash, a cast.
lw_builtin :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, want: Build_Want, w: Written) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    vals := make([dynamic]Operand, 0, len(args), context.temp_allocator)
    each :: proc(k: ^TC, args: []Tree_Id, w: Written, span: Span, vals: ^[dynamic]Operand) {
        for a in args {
            r := lw_arg(k, a, .Value, w, temp_span = span)
            append(vals, r.v)
        }
    }
    switch name {
    case "print", "crash":
        each(k, args, w, span, &vals)
        graph_op(b, .Print if name == "print" else .Crash, w, span, nil, name, ..vals[:])
        return {v = NO_VALUE, ok = true}
    }
    target, is_cast := cast_result_type(name)
    if !is_cast { return lw_builtin_more(k, n, name, args, want, w) }
    each(k, args, w, span, &vals)
    if want == .Place { lw_fail(k, n, "a builtin's place") }
    return {v = graph_op_value(b, .Cast, w, span, target, name, ..vals[:]), ok = true}
}

// An argument (tc_arg) — or the receiver, as built.
lw_arg :: proc(k: ^TC, a: Tree_Id, want: Build_Want, w: Written, temp_span := Span{}) -> Built {
    if a != 0 && a == k.lower.recv.node {
        r := k.lower.recv.r
        if want == .Value && r.place { r = {v = lw_value(k, r, a, k.lower.recv.t), ok = true} }
        return r
    }
    return lw_expr(k, a, want, w, temp_span = temp_span)
}
