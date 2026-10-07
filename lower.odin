package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Lowering (design/annotated_tree.md, stage 2): the program graph made from
// the flat tree and what the checker found about it (annot.odin), once the
// check is done — the checker only checks.
//
// It replays what the checker checked, in the order it did (TC.events): each
// module's statements settled, each constant, each body — in the instance it
// was checked in (its salt, so tc_node_type and the rest read that
// instance's annotations). A body's statements and expressions are built in
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

lower_program :: proc(k: ^TC) -> ^Graph_Builder {
    b := graph_builder_new(k.checked, tc_module_graph_decls(k))
    k.gb = b
    k.lowering = true
    defer k.lowering = false
    saved_salt, saved_pkg, saved_subst := TC_Salt{k.salt, k.salt_lo, k.salt_hi}, k.pkg, k.subst
    defer {
        tc_instance_end(k, saved_salt)
        k.pkg, k.subst = saved_pkg, saved_subst
    }
    for e in k.events {
        tc_instance_end(k, e.salt)
        k.pkg, k.subst = e.pkg, e.subst
        switch e.kind {
        case .Module_Stmt:    graph_module_stmt(b, e.sid, e.declared)
        case .Const:          lw_const(k, e.kc)
        case .Body:           lw_body(k, e.sc)
        case .Program_Struct: lw_program_struct(k)
        }
    }
    return b
}

// The declaration of the variable a name refers to: in the code being built,
// by the token its annotation says declares it (graph_local); else one of
// the compiler's own globals (graph_global).
lw_local :: proc(k: ^TC, n: Tree_Id) -> Node_Id {
    if d := graph_local(k.gb, tc_ref(k, n).decl); d != NO_NODE { return d }
    if d := graph_global(k.gb, tc_name(k, n)); d != NO_NODE { return d }
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
lw_const :: proc(k: ^TC, kc: ^TC_Const) {
    b := k.gb
    if tc_sid(k, kc.def) in b.consts { return }
    span := tree_span(k.t, kc.def)
    f := graph_const_begin(b, tc_graph_decl(k, kc.def))
    ann: Type = Type_Any{}
    if kc.ann != 0 { ann = tc_node_type(k, kc.ann) }
    saved := k.lower
    k.lower = {}
    defer k.lower = saved
    at := graph_dest_var(kc.name, f.root, nil if is_untyped(ann) else ann)
    r := lw_expr(k, kc.value, .Into, dest = at, temp_span = span)
    lw_store(k, kc.value, tc_node_type(k, kc.value), r, graph_dest_var(kc.name, f.root, kc.t), span, settle = true)
    graph_const_end(b, f, kc.t)
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
    return {v = graph_named_const(b, w, span, t, kc.name, named), ok = true}
}

// A fun's or a struct's body (tc_scope_body): its code, statement by
// statement — a struct's top block's declarations its fields.
lw_body :: proc(k: ^TC, sc: ^TC_Scope) {
    b := k.gb
    t := k.t
    ts := sc.ts
    v := scope_view(t, sc.node)
    span := tree_span(t, sc.def)
    is_struct := ts.kind == .Struct
    saved := k.lower
    k.lower = {ts = ts}
    defer k.lower = saved
    f := graph_body_begin(b, ts, tc_sid(k, sc.def), span, v.intrinsic != 0, .Synthetic if sc.synthetic else .Explicit)
    if v.intrinsic == 0 { lw_scope(k, v.body, ts if is_struct else nil, top = true) }
    graph_body_end(b, f)
}

// The program's struct (the compiler's): built from mara.core's declaration
// of it — its fields, each a declaration, and no code (nothing constructs
// it: main's entry sets up its storage).
lw_program_struct :: proc(k: ^TC) {
    pt := k.table.funs["Program"] or_else nil
    if pt == nil || pt.body_span == {} { return }
    t := k.t
    for _, tmpl in k.templates {
        span := tree_span(t, tmpl.def)
        if span != pt.body_span { continue }
        v := scope_view(t, tmpl.node)
        f := graph_body_begin(k.gb, pt, tc_sid(k, tmpl.def), span, v.intrinsic != 0, .Synthetic)
        b := k.gb
        for s in v.body {
            if t.tag[s] != .Decl {
                graph_body_fail(b, f, "the program's struct declares no field")
                break
            }
            ss := tree_span(t, s)
            graph_build_body_stmt(b, ss, true)
            saved := graph_build_stmt(b, tc_sid(k, s), ss, tc_stmt_kind(k, s), fresh = true)
            for target in decl_view(t, s).targets { graph_build_program_field(b, tc_name(k, target), t.main[target], ss) }
            graph_build_stmt_end(b, saved)
        }
        graph_body_end(b, f)
        return
    }
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
        graph_build_body_stmt(b, span, true)
        saved := graph_build_stmt(b, tc_sid(k, s), span, tc_stmt_kind(k, s), fresh = true)
        if t.tag[s] == .Using && fields_of != nil {
            lw_decl(k, Tree_Id(t.a[s]), fields_of)
        } else if t.tag[s] == .Decl && fields_of != nil {
            lw_decl(k, s, fields_of)
        } else {
            lw_stmt(k, s)
        }
        graph_build_stmt_end(b, saved)
    }
}

lw_stmt :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        if lw_override(k, e) { return }
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
        gd := graph_build_defer(k.gb, span)
        lw_scope(k, tree_list(t, t.a[s]))
        graph_build_defer_end(k.gb, gd)
    case .Match:
        lw_match(k, s)
    case .Break, .Continue:
        graph_build_loop_exit(k.gb, span, is_break = t.tag[s] == .Break)
    case:
        lw_unsupported(k, s, "this statement")
    }
}

// A statement that is its own entry in the graph's statements (a loop's
// init, its step).
lw_stmt_entry :: proc(k: ^TC, s: Tree_Id) {
    saved := graph_build_stmt(k.gb, tc_sid(k, s), tree_span(k.t, s), tc_stmt_kind(k, s))
    lw_stmt(k, s)
    graph_build_stmt_end(k.gb, saved)
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
            graph_build_fields(b, names, toks, span, {tc_sid(k, s)}, {tree_span(t, v.values[0])}, true)
        }
        lw_destructure(k, s, v.targets, v.values[0], true, fields_of)
        return
    }
    if len(v.targets) > 1 && fields_of != nil {
        names := make([]string, len(v.targets), context.temp_allocator)
        ids := make([]Syntax_Id, len(v.targets), context.temp_allocator)
        toks := make([]Token_Id, len(v.targets), context.temp_allocator)
        inits := make([]Span, len(v.values), context.temp_allocator)
        for tg, i in v.targets { names[i], ids[i], toks[i] = tc_name(k, tg), tc_sid(k, tg), t.main[tg] }
        for val, i in v.values { inits[i] = tree_span(t, val) }
        graph_build_fields(b, names, toks, span, ids, inits, false)
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
    ann: Type = Type_Any{}
    if ann_node != 0 { ann = tc_node_type(k, ann_node) }
    if value != 0 && tc_is_void(k, value) && !tc_is_pointer(ann) {
        lw_decl_void(k, s, target, value, name, ann, fields_of)
        return
    }
    if value != 0 && t.tag[tc_unparen(k, value)] == .Take {
        lw_decl_take(k, s, target, value, name, ann, fields_of)
        return
    }
    cap_n := Tree_Id(0)
    if ann_node != 0 && t.tag[ann_node] == .Type_Slice {
        cap_n = Tree_Id(t.a[ann_node])
        if cap_n == 0 { cap_n = tc_count_arg(k, Tree_Id(t.b[ann_node])) }
    }
    if value == 0 {
        if bindings := tc_shape_bindings(k, ann_node); len(bindings) > 0 {
            lw_decl_shape(k, s, target, name, ann, bindings, fields_of)
            return
        }
        lw_decl_bare(k, target, name, ann, span, lw_field_decl(k, fields_of, name, target, 0, span), cap_n)
        return
    }
    decl := lw_field_decl(k, fields_of, name, target, value, span)
    if decl == NO_NODE { decl = graph_build_decl(b, name, k.t.main[target], span) }
    prefix: [2]Node_Id
    prefixed := false
    #partial switch t.tag[value] {
    case .String, .Ident, .Field:
        if is_untyped(ann) { prefix, prefixed = graph_build_prefix(b, name, decl, span), true }
    }
    if !prefixed && is_partial_array(ann) { prefix, prefixed = graph_build_prefix(b, name, decl, span), true }
    saved_field := k.field_default
    k.field_default = {}
    if fields_of != nil {
        sc := k.scopes[k.scope_of[fields_of]]
        k.field_default = {value = tc_unparen(k, value), name = name, t = ann, span = tree_span(t, sc.def)}
    }
    r := lw_expr(k, value, .Into, dest = graph_dest_var(name, decl, nil if is_untyped(ann) else ann), temp_span = span)
    k.field_default = saved_field
    vt := tc_node_type(k, value)
    final := tc_node_type(k, target)
    if !is_any(ann) { lw_byte_view_address(k, ann, value) }
    graph_build_typed(b, decl, final)
    wrote, zeroed := lw_store(k, value, vt, r, graph_dest_var(name, decl, final), span, settle = true)
    if prefixed {
        fills := is_partial_array(final) && (t.tag[value] == .String || is_slice_type(vt))
        graph_build_prefix_end(b, prefix, zeroed || wrote && fills, final)
    }
    if zeroed && !prefixed { lw_fail(k, s, "a new partial array read from bytes") }
    if va, is_array := distinct_base(vt).(^Type_Fixed_Array); is_array && is_infer(va.elem) && fields_of == nil {
        graph_build_retype_literal(b, int(decl), b.nodes, final)
    }
}

// `x : T` (tc_decl_bare): its zero, or its construction.
lw_decl_bare :: proc(k: ^TC, target: Tree_Id, name: string, ann: Type, span: Span, field: Node_Id, cap_n: Tree_Id) {
    b := k.gb
    if _, is_error := ann.(Type_Error); is_error { return }
    if cap_n != 0 {
        lw_decl_sized(k, name, k.t.main[target], ann, span, field, cap_n)
        return
    }
    st := tc_bare_struct(ann)
    decl := field
    if decl == NO_NODE {
        decl = graph_build_decl(b, name, k.t.main[target], span)
        graph_build_typed(b, decl, ann)
    } else if b.g.type_[decl] == nil {
        graph_build_typed(b, decl, ann)
    }
    args: []Operand
    if st != nil && constructs_bare(st) { args = lw_ctor_args(k, st, span) }
    graph_build_bare(b, decl, ann, nil, args, span)
}

// `s : [:n]T` (tc_decl_bare): its local, then n of T for it.
lw_decl_sized :: proc(k: ^TC, name: string, tok: Token_Id, ann: Type, span: Span, field: Node_Id, cap_n: Tree_Id) {
    b := k.gb
    decl := field
    if decl == NO_NODE { decl = graph_build_decl(b, name, tok, span) }
    r := lw_expr(k, cap_n, .Value)
    if field != NO_NODE {
        graph_build_bare(b, decl, b.g.type_[decl], nil, nil, span)
        return
    }
    graph_build_typed(b, decl, ann)
    graph_build_bare(b, decl, ann, r.v, nil, span)
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
        lw_expr(k, value, .Value)
        return
    }
    if name == "this_program" { return }   // (its arena: set up by main's entry, nothing built here)
    existing := tc_node_type(k, target)
    if tc_is_void(k, value) {
        graph_build_void_assign(b, name, lw_local(k, target), distinct_base(existing), span, tree_span(t, value))
        return
    }
    vt: Type = distinct_base(existing) if !is_untyped(existing) else nil
    r := lw_expr(k, value, .Into, dest = graph_dest_var(name, lw_local(k, target), vt), temp = true, temp_span = span)
    lw_byte_view_address(k, existing, value)
    lw_store(k, value, tc_node_type(k, value), r, lw_parallel_hold(k, graph_dest_var(name, lw_local(k, target), distinct_base(existing)), span), span)
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
    name := tc_name(k, target)
    existing := tc_node_type(k, target)
    fr := lw_compound_value(k, s, op_tok, target, value, .Into)
    lw_store(k, 0, tc_node_type(k, s), fr, graph_dest_var(name, lw_local(k, target), distinct_base(existing)), span)
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
    vals := make([dynamic]Operand, 0, len(values), context.temp_allocator)
    for val, i in values {
        want := rts[i]
        text, slot := false, NO_NODE
        vt := tc_node_type(k, val)
        // (Text — a literal, or a text constant's — in a zeroed temporary;
        // an array's value its result views, in a temporary.)
        text_held: Graph_Held
        if is_partial_array(want) {
            if t.tag[tc_unparen(k, val)] == .String {
                text, slot = true, graph_slot(b, "temp", want, span)
                graph_build_zero_var(b, slot, want, span)
            } else {
                text_held = graph_build_hold(b, want, span, zero = true)
            }
        }
        use, at := lw_use_type(k, val, want, span)
        held := NO_NODE
        if _, from_array := distinct_base(vt).(^Type_Fixed_Array); from_array && is_slice_type(want) {
            held = graph_build_hold(b, vt, span).slot
        }
        r := lw_expr(k, val, .Either, dest = use, temp_span = at)
        if text_held.to > 0 {
            if built_is_text_constant(b, r) {
                text, slot = true, text_held.slot
            } else {
                graph_build_unhold(b, text_held)
            }
        }
        if !text {
            append(&vals, lw_value_as(k, val, vt, r, want, span, {to = want}, held))
        } else {
            lw_store(k, val, vt, r, graph_dest_var("temp", slot, want), span)
            append(&vals, graph_read(b, graph_var(b, "temp", slot, want, span), want, span))
        }
        lw_byte_view_address(k, want, val)
    }
    graph_build_return(b, vals[:], span)
}

// `if c {…} else {…}` (tc_if).
lw_if :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    v := if_view(t, s)
    cond := lw_expr(k, v.cond, .Value)
    fi := graph_build_if(b, cond.v, span, len(v.else_) > 0)
    lw_scope(k, v.then)
    graph_build_else(b, &fi, span)
    if len(v.else_) > 0 { lw_scope(k, v.else_) }
    graph_build_if_end(b, &fi)
}

// A loop (tc_for): its block, its variables, then its runs.
lw_for :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    b := k.gb
    span := tree_span(t, s)
    v := for_view(t, s)
    tag := t.tag[s]
    fl := graph_build_for(b, {span = span, var_name = tc_text(v.var) if v.var != 0 else "",
                            elem_name = tc_text(v.elem) if v.elem != 0 else "",
                            index_name = tc_text(v.index) if v.index != 0 else "",
                            var_tok = v.var, elem_tok = v.elem, index_tok = v.index,
                            is_range = tag == .For_Range, has_cond = v.cond != 0, has_step = v.post != 0,
                            end_literal = v.hi != 0 && t.tag[tc_unparen(k, v.hi)] == .Number})
    defer graph_build_for_end(b, &fl)
    #partial switch tag {
    case .For_Each:
        ct: Type
        coll := NO_VALUE
        if !lw_pure_place(k, v.collection) {
            ct = lw_loop_items(k, &fl, v.collection)
        } else {
            r := lw_expr(k, v.collection, .Place)
            ct, coll = tc_node_type(k, v.collection), r.v
        }
        elem: Type = Type_Error{}
        #partial switch c in ct {
        case ^Type_Fixed_Array:   elem = c.elem
        case ^Type_Slice:         elem = c.elem
        case ^Type_Partial_Array: elem = c.elem
        }
        if v.type_ != 0 { elem = tc_node_type(k, v.type_) }
        graph_build_for_collection(b, &fl, coll, ct, tc_is_self(k, v.collection), distinct_base(elem))
        lw_scope(k, v.body)
    case .For_Range:
        bounds := [2]int{-1, -1}
        graph_build_range_counter(b, &fl)
        lo := lw_expr(k, v.lo, .Value)
        lt := tc_node_type(k, v.lo)
        bounds[0] = len(b.body.checks)
        fl.lo = graph_build_range_bound(b, lo.v, lt, span)
        hi := lw_expr(k, v.hi, .Value)
        ht := tc_node_type(k, v.hi)
        fl.high = hi.v
        bounds[1] = len(b.body.checks)
        fl.hi = graph_build_range_bound(b, hi.v, ht, span)
        it: Type
        if v.type_ != 0 {
            it = tc_node_type(k, v.type_)
        } else {
            it = try_promote_numeric(lt, ht)
            if _, is_error := it.(Type_Error); is_error || is_infer(it) { it = slice_header_width_type }
        }
        graph_build_range(b, &fl, bounds, distinct_base(it))
        lw_scope(k, v.body)
    case:
        if v.init != 0 { lw_stmt_entry(k, v.init) }
        graph_build_for_runs(b, &fl)
        cond := lw_expr(k, v.cond, .Value)
        graph_build_for_cond(b, &fl, cond.v)
        lw_scope(k, v.body)
        if v.post != 0 {   // (its step, after its body: where it runs)
            graph_build_for_step(b, &fl)
            lw_stmt_entry(k, v.post)
        }
    }
}

// A loop's collection that is no plain place: held in the
// loop's own local, or viewed.
lw_loop_items :: proc(k: ^TC, fl: ^Graph_For, e: Tree_Id) -> Type {
    b := k.gb
    graph_build_items(b, fl)
    tag := k.t.tag[tc_unparen(k, e)]
    #partial switch tag {
    case .Array, .Literal:
        from := b.nodes
        t := solidify_type(lw_store_into(k, e, graph_dest_var("items", fl.coll_slot, nil), fl.span))
        if graph_loop_view_of(t) != nil { lw_fail(k, e, "a literal loop over its view") }
        graph_build_retype_literal(b, from, b.nodes, t)
        graph_build_typed(b, fl.coll_slot, t)
        return t
    }
    t := tc_node_type(k, e)
    view := graph_loop_view_of(t)
    // (A value viewed: held in a temporary made before it — zero first when
    // it fills a prefix of a partial array.)
    held: Graph_Held
    if view != nil {
        fills := is_partial_array(t) && (tag == .String || is_slice_type(t))
        held = graph_build_hold(b, t, fl.span, zero = fills)
    }
    r := lw_expr(k, e, .Either)
    if view != nil {
        graph_build_items_view(b, fl, held, r.v, r.place, t, view, tc_is_self(k, e))
    } else {
        graph_build_typed(b, fl.coll_slot, t)
        lw_store(k, e, t, r, graph_dest_var("items", fl.coll_slot, t), fl.span)
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
            return lw_call(k, m, want, w, dest, temp, temp_span, addressed = n)
        }
        return lw_unary(k, n, want, w)
    case .Deref:
        r := lw_expr(k, Tree_Id(t.a[n]), .Place, w, temp_span = span)
        p := graph_op_value(b, .Deref, .Explicit, span, ty, "", r.v)
        if want == .Value { return {v = graph_read(b, p, ty, span), ok = true} }
        return {v = p, place = true, ok = true}
    case .Binary:
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
        return lw_index(k, n, want, w)
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
    t: Type = Type_Infer_Float{} if is_float else Type_Infer_Int{}
    if want == .Place { return {} }
    return {v = graph_const(k.gb, w, span, t, "", Const_Value{int = i, float = f, is_float = is_float}), ok = true}
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
        return {v = graph_op_value(b, .Const, w, span, t, "void"), ok = true}
    }
    if ts, is_scope := t.(^Type_Scope); is_scope && !ts.is_module {
        declared := name in k.c.declared_funs && (ts.kind == .Fun || len(ts.params) > 0)
        if declared || ref.kind == .Fun && ts.kind == .Fun {
            if want == .Place { return {} }
            return {v = graph_op_value(b, .Global, w, span, t, name), ok = true}
        }
    }
    // (A module's or a type's name is no value: what a field reads through
    // it is built, lw_field.)
    if ref.kind == .Module || ref.kind == .Type { return {} }
    place := graph_var(b, name, lw_local(k, n), t, span)
    if want == .Value { return {v = graph_read(b, place, t, span), ok = true} }
    return {v = place, place = true, ok = true}
}

// A variant's value, by its name: an enum's, or a union's tag.
lw_variant_value :: proc(t: Type, name: string) -> int {
    #partial switch v in t {
    case ^Type_Enum:  return v.variants[name]
    case ^Type_Union: return v.tag_map[name]
    }
    return 0
}

// The constant a declaring token names.
// (A body's constant in a generic's instance is that instance's own: the
// use's instance first, then the tree's.)
lw_const_of :: proc(k: ^TC, use: Tree_Id, decl: Token_Id) -> ^TC_Const {
    key :: proc(salt: u64, decl: Token_Id) -> u64 { return salt << 32 | u64(decl) }
    if k.const_by_decl == nil {
        for _, kc in k.consts { k.const_by_decl[key(u64(kc.sid) >> 32, k.t.main[kc.def])] = kc }
        for _, list in k.scope_consts { for _, kc in list { k.const_by_decl[key(u64(kc.sid) >> 32, k.t.main[kc.def])] = kc } }
    }
    kc := k.const_by_decl[key(u64(tc_instance(k, use)), decl)] or_else nil
    if kc == nil { kc = k.const_by_decl[key(0, decl)] or_else nil }
    if kc == nil { graph_fatal(Span{at = decl}, "lower: no constant is declared here") }
    return kc
}

// Its place, when it has none: a temporary made first, the value
// stored in it.
lw_hold :: proc(k: ^TC, n: Tree_Id, span: Span) -> Operand {
    b := k.gb
    slot := graph_slot(b, "temp", nil, span)
    prefix := graph_build_prefix(b, "temp", slot, span)
    d := graph_dest_var("temp", slot, nil)
    r := lw_expr(k, n, .Into, dest = d, temp_span = span)
    t := tc_node_type(k, n)
    lw_store(k, n, t, r, d, span)
    graph_build_prefix_end(b, prefix, is_partial_array(t) && (k.t.tag[n] == .String || is_slice_type(t)), t)
    graph_build_typed(b, slot, t)
    return graph_var(b, "temp", slot, t, span)
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
    wrapping := op == .Wrap_Minus
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
    word := "-%" if wrapping else graph_token_text(.Minus if op == .Minus else op)
    return {v = graph_op_value(b, .Unary, w, span, t, word, v), ok = true}
}

// `left op right` (tc_binary_op): each side at the type the operation works
// in; `and` / `or` short-circuit. `at`: its node (a Binary, a compound
// assignment); `t`: its type.
lw_binary_op :: proc(k: ^TC, at: Tree_Id, tok: Token_Kind, span: Span, left, right: Tree_Id,
                     want: Build_Want, w: Written, t: Type, in_range: ^TC_In_Range = nil) -> Built {
    tr := k.t
    b := k.gb
    op := tok
    wrapping := false
    #partial switch tok {
    case .Wrap_Plus:  op, wrapping = .Plus, true
    case .Wrap_Minus: op, wrapping = .Minus, true
    case .Wrap_Star:  op, wrapping = .Star, true
    }
    if want == .Place { lw_fail(k, at, "a binary's place") }
    sides: [2]Operand
    widen := [2]int{-1, -1}
    types: [2]Type
    arrays: [2]bool
    and_or := op == .And || op == .Or
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
            sides[i] = r.v
            if i == 0 { graph_build_and_left(b, &sa, r.v) }
            continue
        }
        r := lw_expr(k, side, .Either, w)
        st := tc_node_type(k, side)
        types[i] = st
        if tr.tag[tc_unparen(k, side)] == .Array { lw_fail(k, side, "an array literal as an operand") }
        _, is_array := distinct_base(st).(^Type_Fixed_Array)
        arrays[i] = is_array && !r.place
        sides[i], widen[i] = graph_build_as(b, r.v, r.place, st, tree_span(tr, side), span, {})
    }
    lt, rt := types[0], types[1]
    if callee := tc_callee(k, at); at != 0 && callee != nil {
        ret := fn_primary_return(callee)
        for wi, i in widen {
            if wi >= 0 && i < len(callee.params) { b.body.widens[wi].sig, b.body.widens[wi].param = callee, i }
        }
        kind: Op_Kind = .Construct if callee.kind == .Struct else .Call
        return {v = {graph_call_op(b, kind, w, span, callee, ret, sides[0], sides[1]), 0}, ok = true}
    }
    if and_or { return {v = graph_build_and_end(b, &sa, sides[1]), ok = true} }
    work := Graph_Work{op, t, lt, rt}
    for wi in widen {
        if wi >= 0 { b.body.widens[wi].work, b.body.widens[wi].binary, b.body.widens[wi].views = work, true, false }
    }
    kind: Op_Kind = .Compare if is_comparison_op(op) else .Arith
    word := graph_token_text(op)
    if wrapping { word = strings.concatenate({word, "%"}) }
    return {v = graph_op_value(b, kind, w, span, t, word, sides[0], sides[1]), ok = true}
}

// `assert(c)` (tc_assert).
lw_assert :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    t := k.t
    span := tree_span(t, n)
    cond := Tree_Id(t.a[n])
    if want != .Value { lw_fail(k, n, "an assert's place") }
    r := lw_expr(k, cond, .Value, w)
    lo, hi := int(t.first[cond]), int(t.end[cond])
    sides: Maybe([2]string)
    if bin := tc_unparen(k, cond); t.tag[bin] == .Binary && is_comparison_op(build_tokens[t.main[bin]].kind) {
        op := build_tokens[t.main[bin]].kind
        at, depth := -1, 0
        for i in lo ..< hi {
            #partial switch build_tokens[i].kind {
            case .Left_Paren, .Left_Bracket, .Left_Brace:    depth += 1
            case .Right_Paren, .Right_Bracket, .Right_Brace: depth -= 1
            case op: if depth == 0 { at = i }
            }
        }
        if at > lo && at < hi - 1 {
            sides = [2]string{
                "" if tc_is_literal(k, Tree_Id(t.a[bin])) else token_range_text(lo, at),
                "" if tc_is_literal(k, Tree_Id(t.b[bin])) else token_range_text(at + 1, hi),
            }
        }
    }
    graph_assert(k.gb, span, token_range_text(lo, hi), r.v, w, sides)
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
    gi := graph_build_if_expr(b, cond.v, w, span)
    types: [2]Type
    widen := [2]int{-1, -1}
    prefix: [2][2]Node_Id
    for branch, i in ([2]Tree_Id{then_n, else_n}) {
        if i == 1 { graph_build_if_expr_else(b, &gi) }
        if lw_may_fill_prefix(k, branch) { prefix[i] = graph_build_prefix(b, "if", slot, span) }
        r := lw_expr(k, branch, .Into, dest = graph_dest_var("if", slot, nil))
        types[i] = tc_node_type(k, branch)
        if r.into { continue }
        if lw_builds_into(k, branch) || tc_byte_index(k, branch) { lw_fail(k, branch, "an if's branch built in place, or of bytes") }
        count := len(b.body.widens)
        val := graph_build_widen(b, lw_value(k, r, branch, types[i]), span, {pending = true})
        if len(b.body.widens) > count { widen[i] = count }
        graph_build_write_at(b, graph_var(b, "if", slot, nil, span), val, span)
    }
    graph_build_if_expr_end(b, &gi)
    t := tc_node_type(k, n)
    for bt, i in types {
        if build_views(t, bt) { lw_fail(k, n, "an if's branch viewed") }
        if prefix[i] != {} {
            branch := then_n if i == 0 else else_n
            fills := is_partial_array(t) && (tr.tag[tc_unparen(k, branch)] == .String || is_slice_type(bt))
            graph_build_prefix_end(b, prefix[i], fills, t)
        }
    }
    for wi in widen { if wi >= 0 { b.body.widens[wi].to = t } }
    lt := t
    if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array && is_infer(fa.elem) {
        lt = solidify_type(t)
        graph_build_retype_literal(b, int(slot), b.nodes, lt)
    }
    graph_build_typed(b, slot, lt)
    p := graph_var(b, "if", slot, lt, span)
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
    r := lw_call_impl(k, n, .Into, w, graph_dest_var("temp", slot, nil), temp, at, addressed)
    if !r.ok { lw_fail(k, n, "a call's place") }
    t := tc_node_type(k, n)
    if !r.into { graph_build_write_at(b, graph_var(b, "temp", slot, nil, at), r.v, at) }
    graph_build_typed(b, slot, t)
    return {v = graph_var(b, "temp", slot, t, at), place = true, ok = true}
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
        r := lw_expr(k, args[0], .Value, w)
        return {v = graph_op_value(b, .Cast, w, span, tc_node_type(k, n), name, r.v), ok = true}
    case .Dispatch:
        return lw_dispatch_call(k, n, args, want, w)
    case .Generic:
        return lw_generic_call(k, n, args, want, w)
    case .Fun, .Value:
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
        pt := ft.params[i].type_
        use, use_at := lw_use_type(k, a, pt, span)
        if arg.kind == .Receiver {
            append(&ops, lw_value_as(k, a, k.lower.recv.t, k.lower.recv.r, pt, span, {sig = ft, param = i}))
        } else {
            at := tc_node_type(k, a)
            #partial switch arg.kind {
            case .Call_Site:
                at = lw_hash_name_type(k, a)
            case .Default:
                if arg.slot >= 0 {
                    if returns := tc_call_returns(k, a, nil); len(returns) > 1 { at = returns[arg.slot] }
                }
            }
            // (An array's value its param views: held in a temporary.)
            held := NO_NODE
            if _, from_array := distinct_base(at).(^Type_Fixed_Array); from_array && is_slice_type(pt) {
                held = graph_build_hold(b, at, span).slot
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
            case .Written, .Receiver:
                r = lw_expr(k, a, .Either, w, dest = use, temp_span = use_at)
            }
            append(&ops, lw_value_as(k, a, at, r, pt, span, {sig = ft, param = i}, held))
        }
        lw_byte_view_address(k, pt, a)
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
        graph_build_write_at(b, graph_var(b, "temp", view_slot, ret, temp_span), call, temp_span)
        return {v = graph_var(b, "temp", view_slot, ret, temp_span), place = true, ok = true}
    }
    return {v = call, ok = true}
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
