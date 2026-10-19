package mara

import "core:strings"

// Lowering the rest of the statements and expressions: match, the builtins
// past print and the casts, `void` declarations, size_of, `in` a range,
// the compiler's names, a default taken from a group's one value, a
// generic's call, the shape shortcut.

// `match x { … }` (tc_match): the subject — a plain place, walked where it is
// needed; else held in a local made first — then the switch on its tag (a
// value arm's value built before it), then each arm's block.
lw_match :: proc(k: ^TC, s: Tree_Id) {
    tr := k.t
    b := k.gb
    span := tree_span(tr, s)
    subj := Tree_Id(tr.a[s])
    arms := tree_list(tr, tr.b[s])
    if subj == 0 { return }
    slot := NO_NODE
    subject := NO_VALUE
    st := tc_node_type(k, subj)
    if !lw_pure_place(k, subj) {
        slot = graph_slot(b, "subject", nil, span)
        st = lw_store_into(k, subj, graph_dest_var(slot, nil), span)
        graph_build_typed(b, slot, st)
    } else {
        subject = lw_expr(k, subj, .Place).v
    }
    ut, is_union := distinct_base(st).(^Type_Union)
    et, is_enum := distinct_base(st).(^Type_Enum)
    gm := graph_build_match_begin(b, span, len(arms), slot, subject, st, tr.tag[tc_unparen(k, subj)] == .Self)
    for arm, i in arms {
        tag := tr.tag[arm]
        if tag == .Arm_Else { continue }
        if gm.is_union || tag != .Arm_Value {
            graph_build_match_tag(b, gm, span, i)
            continue
        }
        value := Tree_Id(tr.a[arm])
        if tr.tag[value] == .Ident && is_enum && tc_name(k, value) in et.variants {
            graph_build_match_tag(b, gm, span, i)
            continue
        }
        graph_build_match_value(b, gm, lw_expr(k, value).v)
    }
    graph_build_match_switch(b, gm, span)
    defer graph_build_match_end(b, gm)
    for arm, i in arms {
        a := tc_match_arm(k, subj, arm, et, ut)
        tag := tr.tag[arm]
        // (A variant arm binds a union's payload; an enum's variants carry
        // none — `Red` alone on an enum is its tag, as `.Red` is.)
        ra := Graph_Arm{variant = a.variant, bound = a.bound, bound_tok = a.bound_tok,
                        is_else = tag == .Arm_Else, is_union = tag == .Arm_Variant && is_union}
        // (Its tag, and a union's payload.)
        if a.variant != "" {
            switch {
            case is_enum:  ra.tag = et.variants[a.variant]
            case is_union: ra.tag, ra.payload = ut.tag_map[a.variant], lw_variant_struct(ut, a.variant)
            }
        }
        ra.arena = lw_scope_arena(k, a.body, b.body.returned)
        blk := graph_build_arm(b, gm, ra, i)
        // (A binding of a subject in place: its uses that need it, checked.)
        checked: []Tree_Id
        if ra.is_union && a.bound != "" && slot == NO_NODE {
            checked = lw_bind_checks(k, subj, a.body, a.bound_tok, {union_t = st, variant = a.variant, tag = ra.tag})
        }
        lw_scope(k, a.body)
        for u in checked { delete_key(&k.lower.bind_checks, u) }
        graph_build_arm_end(b, gm, blk)
    }
}

// A match arm's binding is its subject's payload, in place (graph_build_arm),
// so an arm that may give the subject another variant has each use of the
// binding after such a change — or in a loop of the arm's with one — check
// the subject's tag first (lw_bind_check), stopping when it's another's.
// What may change it: a write into it, its address taken, a method called
// on it; and where code elsewhere can reach it — through a pointer or a
// slice, a param's (passed by its address), the receiver's field, a local
// whose address is taken in the fun or that is itself a view (a `let`'s, a
// binding) — any call, any write but to a local's own variable. Arms that
// change nothing check nothing. (A subject held in a slot of its own is a
// copy no one else sees: lw_match asks for none.)
LW_Bind_Check :: struct {
    union_t: Type,
    variant: string,
    tag:     int,
}

lw_bind_checks :: proc(k: ^TC, subj: Tree_Id, body: []Tree_Id, bound: Token_Id, check: LW_Bind_Check) -> []Tree_Id {
    Walk :: struct {
        k:               ^TC,
        root, bound:     Token_Id,
        shared:          bool,
        changes, loops:  [dynamic]Span,
        uses:            [dynamic]Tree_Id,
    }
    change :: proc(w: ^Walk, n: Tree_Id) { append(&w.changes, tree_span(w.k.t, n)) }
    write :: proc(w: ^Walk, target, at: Tree_Id) {
        r, through := lw_place_root(w.k, target)
        switch {
        case r == w.bound && !through:                  // (the payload's own fields: not its tag)
        case r != 0 && r == w.root:                     change(w, at)
        case w.shared && (through || r == 0):           change(w, at)
        }
    }
    walk :: proc(w: ^Walk, n: Tree_Id) {
        t := w.k.t
        #partial switch t.tag[n] {
        case .Fun_Def, .Struct_Def:
            return   // (a nested definition's body runs when it's called)
        case .Ident:
            if r := tc_ref(w.k, n); r.kind == .Local && r.decl == w.bound { append(&w.uses, n) }
        case .For_Range, .For_Each, .For_C, .For_Cond:
            append(&w.loops, tree_span(t, n))
        case .Assign:
            for tg in tree_list(t, t.a[n]) { write(w, tg, n) }
        case .Compound:
            write(w, Tree_Id(t.a[n]), n)
        case .Unary:
            if build_tokens[t.main[n]].kind == .Ampersand {
                if r, _ := lw_place_root(w.k, Tree_Id(t.a[n])); r != 0 && r == w.root { change(w, n) }
            }
        case .Call, .Method_Call:
            form := w.k.annot.forms[tc_sid(w.k, n)] or_else .Fun
            if form == .Builtin || form == .Conversion { break }
            if w.shared { change(w, n); break }
            if t.tag[n] == .Method_Call {
                if r, _ := lw_place_root(w.k, method_view(t, n).receiver); r != 0 && r == w.root { change(w, n) }
            }
        }
        kids := make([dynamic]Tree_Id, context.temp_allocator)
        tree_children(t, n, &kids)
        for c in kids { walk(w, c) }
    }
    root, shared := lw_place_root(k, subj)
    if root != 0 && !shared {
        facts := lw_fun_facts(k)
        shared = root in facts.addressed || root in facts.views
    }
    w := Walk{k = k, root = root, bound = bound, shared = shared}
    w.changes = make([dynamic]Span, context.temp_allocator)
    w.loops = make([dynamic]Span, context.temp_allocator)
    w.uses = make([dynamic]Tree_Id, context.temp_allocator)
    for s in body { walk(&w, s) }
    if len(w.changes) == 0 { return nil }
    checked := make([dynamic]Tree_Id, context.temp_allocator)
    for u in w.uses {
        at := tree_span(k.t, u).at
        needs := false
        for c in w.changes {
            if c.at < at { needs = true; break }
            for l in w.loops {
                if l.at <= c.at && c.at <= l.end && l.at <= at && at <= l.end { needs = true; break }
            }
            if needs { break }
        }
        if needs {
            k.lower.bind_checks[u] = check
            append(&checked, u)
        }
    }
    return checked[:]
}

// A place's root variable — the token that declares it (0: none, a call's
// result, the receiver) — and whether it is reached through memory others
// can reach too: a pointer, a slice, a param's (passed by its address), a
// field's of the receiver.
lw_place_root :: proc(k: ^TC, n: Tree_Id) -> (root: Token_Id, through: bool) {
    t := k.t
    n := tc_unparen(k, n)
    #partial switch t.tag[n] {
    case .Ident:
        r := tc_ref(k, n)
        return r.decl, r.kind != .Local
    case .Deref:
        r, _ := lw_place_root(k, Tree_Id(t.a[n]))
        return r, true
    case .Field, .Index, .Slice:
        base := Tree_Id(t.a[n])
        r, through := lw_place_root(k, base)
        #partial switch _ in distinct_base(tc_node_type(k, base)) {
        case ^Type_Ptr, ^Type_Slice: through = true
        }
        return r, through
    }
    return 0, true
}

// What a fun's body does to its locals, for lw_bind_checks: each whose
// address it takes (`&x`, `&x.f`, `&x[i]` — an append's too), each that is
// itself a view of other memory (a `let`'s, a match arm's binding).
LW_Fun_Facts :: struct {
    addressed: map[Token_Id]bool,
    views:     map[Token_Id]bool,
}

lw_fun_facts :: proc(k: ^TC) -> ^LW_Fun_Facts {
    if k.lower.facts != nil { return k.lower.facts }
    f := new(LW_Fun_Facts, context.temp_allocator)
    f.addressed = make(map[Token_Id]bool, context.temp_allocator)
    f.views = make(map[Token_Id]bool, context.temp_allocator)
    walk :: proc(k: ^TC, f: ^LW_Fun_Facts, n: Tree_Id) {
        t := k.t
        #partial switch t.tag[n] {
        case .Unary:
            if build_tokens[t.main[n]].kind == .Ampersand {
                if r, _ := lw_place_root(k, Tree_Id(t.a[n])); r != 0 { f.addressed[r] = true }
            }
        case .Method_Call:   // (a method taking ^Self: the receiver's address)
            if r, _ := lw_place_root(k, method_view(t, n).receiver); r != 0 { f.addressed[r] = true }
        case .Arm_Variant:
            if tok := Token_Id(t.b[n]); tok != 0 { f.views[tok] = true }
        case .Decl:
            v := decl_view(t, n)
            if len(v.values) == 1 && t.tag[tc_unparen(k, v.values[0])] == .Take {
                for tg in v.targets { if t.tag[tg] == .Ident { f.views[t.main[tg]] = true } }
            }
        }
        kids := make([dynamic]Tree_Id, context.temp_allocator)
        tree_children(t, n, &kids)
        for c in kids { walk(k, f, c) }
    }
    if k.lower.node != 0 {
        for s in scope_view(k.t, k.lower.node).body { walk(k, f, s) }
    }
    k.lower.facts = f
    return f
}

// A binding's use that checks its subject's tag first: the union it views
// — a check of its tag against the arm's (graph: a Variant of the binding,
// with the tag) — then the payload again.
lw_bind_check :: proc(k: ^TC, place: Operand, t: Type, name: string, bc: LW_Bind_Check, span: Span) -> Operand {
    b := k.gb
    tag := graph_const(b, .Implied, span, graph_tag_type(bc.union_t), bc.variant, Const_Value{int = i128(bc.tag)})
    whole := graph_op_value(b, .Variant, .Implied, span, bc.union_t, bc.variant, place, tag)
    return graph_op_value(b, .Variant, .Implied, span, t, name, whole)
}

lw_variant_struct :: proc(ut: ^Type_Union, name: string) -> Type {
    if vs := ut.variant_structs[name]; vs != nil { return vs }
    return nil
}

// The rest of the builtins (tc_builtin_more): print_cstr / print_int /
// print_float, len and cap (a fixed array's, its size), slice_from_ptr,
// cstring.
lw_builtin_more :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, want: Build_Want, w: Written) -> Built {
    b := k.gb
    span := tree_span(k.t, n)
    switch name {
    case "print_cstr", "print_int", "print_float":
        r := lw_arg(k, args[0], .Value, w, temp_span = span)
        if want == .Place { lw_fail(k, n, "a builtin's place") }
        graph_op(b, .Print, w, span, nil, name, r.v)
        return {v = NO_VALUE, ok = true}
    case "len", "cap":
        t := slice_header_width_type
        at := lw_arg_type(k, args[0])
        if want == .Place { lw_fail(k, n, "a builtin's place") }
        if fa, fixed := distinct_base(graph_pointee(at)).(^Type_Fixed_Array); fixed {   // (its size: nothing of it built)
            return {v = graph_const(b, w, span, t, name, Const_Value{int = i128(fa.size)}), ok = true}
        }
        r := lw_arg(k, args[0], .Place, w, temp_span = span)
        if !r.place { lw_fail(k, n, "the length of a value") }
        base := r.v
        if pt, is_ptr := distinct_base(at).(^Type_Ptr); is_ptr && !tc_is_self(k, args[0]) { base = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", base) }
        field := graph_op_value(b, .Field, w, span, t, name, base)
        return {v = graph_read(b, field, t, span), ok = true}
    case "slice_from_ptr":
        pr := lw_arg(k, args[0], .Value, w, temp_span = span)
        sr := lw_arg(k, args[1], .Value, w, temp_span = span)
        if want == .Place { lw_fail(k, n, "a builtin's place") }
        return {v = graph_op_value(b, .Slice, w, span, tc_node_type(k, n), name, pr.v, sr.v), ok = true}
    case "cstring":
        r := lw_arg(k, args[0], .Value, w, temp_span = span)
        if want == .Place { lw_fail(k, n, "a builtin's place") }
        return {v = graph_op_value(b, .Cast, w, span, Type_CString{}, name, r.v), ok = true}
    }
    lw_unsupported(k, n, "this builtin")
}

// An argument's type: the receiver's, as built; else its own.
lw_arg_type :: proc(k: ^TC, a: Tree_Id) -> Type {
    if a != 0 && a == k.lower.recv.node { return k.lower.recv.t }
    return tc_node_type(k, a)
}

// `x : T = void` (tc_decl_void): declared uninitialized — a field's, its
// void written.
lw_decl_void :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, fields_of: ^Type_Scope) {
    b := k.gb
    span := tree_span(k.t, s)
    decl := lw_field_decl(k, fields_of, name, target, span)
    if decl == NO_NODE { decl = graph_build_decl(b, name, k.t.main[target], span, ann) }
    graph_build_typed(b, decl, ann)
    if fields_of != nil {
        val := graph_build_void(b, ann, tree_span(k.t, value))
        graph_build_write_at(b, graph_var(b, decl, ann, span), val, span)
        return
    }
    graph_build_void_decl(b, decl, ann, span, span)
}

// `size_of(T)` (tc_size_of): T's size, a constant.
lw_size_of :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    if want == .Place { return {} }
    t := k.annot.size_of[tc_sid(k, n)]
    return {v = graph_const(k.gb, w, tree_span(k.t, n), tc_node_type(k, n), "size_of", graph_size_of(t), untyped = true), ok = true}
}

// `x in lo..hi` (tc_in_range): `x >= lo and x < hi`; `not in`, its negation.
lw_in_range :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written) -> Built {
    tr := k.t
    span := tree_span(tr, n)
    lo, hi := tree_pair(tr, n)
    if hi == 0 { return lw_in_items(k, n, lo, want, w) }
    rng := TC_In_Range{value = Tree_Id(tr.a[n]), lo = lo, hi = hi, span = span}
    if build_tokens[tr.main[n]].kind != .Not { return lw_binary_op(k, 0, .And, span, 0, 0, want, w, Type_Bool{}, &rng) }
    if want == .Place { lw_fail(k, n, "a unary's place") }
    r := lw_binary_op(k, 0, .And, span, 0, 0, .Value, w, Type_Bool{}, &rng)
    return {v = graph_op_value(k.gb, .Unary, w, span, Type_Bool{}, graph_token_text(.Not), r.v), ok = true}
}

// `x in xs` (tc_in_items): the overload's call with xs — through a pointer,
// what it points at; a value with no place (an array literal), held first —
// then x (text to a list: its own, lw_text_as_list); `not in`, negated.
// x is built first, as written.
lw_in_items :: proc(k: ^TC, n, coll: Tree_Id, want: Build_Want, w: Written) -> Built {
    b := k.gb
    tr := k.t
    span := tree_span(tr, n)
    if want == .Place { lw_fail(k, n, "an `in`'s place") }
    callee := tc_callee(k, n)
    if callee == nil || len(callee.params) != 2 { lw_fail(k, n, "an `in` with no overload to call") }
    value := Tree_Id(tr.a[n])
    a1, made := lw_text_as_list(k, value, callee.params[1].type_, span, w)
    if !made {
        rv := lw_expr(k, value, .Either, w)
        a1 = graph_build_as(b, rv.v, rv.place, tc_node_type(k, value), tree_span(tr, value), span, {sig = callee, param = 1})
    }
    ct := tc_node_type(k, coll)
    cv: Operand
    place := true
    switch {
    case lw_pure_place(k, coll):
        cv = lw_expr(k, coll, .Place, w).v
    case is_slice_type(ct) || is_ptr_type(ct):
        r := lw_expr(k, coll, .Either, w)
        cv, place = r.v, r.place
        if is_ptr_type(ct) && !place { cv, place = lw_hold(k, coll, span), true }
    case:
        cv = lw_hold(k, coll, span)
    }
    if pt, is_ptr := distinct_base(ct).(^Type_Ptr); is_ptr {
        cv = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", cv)   // (through the pointer, what it points at)
        ct = pt.elem
    }
    a0 := lw_value_as(k, coll, ct, Built{v = cv, place = place, ok = true}, callee.params[0].type_, span, {sig = callee, param = 0})
    call := Operand{graph_call_op(b, .Call, w, span, callee, fn_primary_return(callee), a0, a1), 0}
    if build_tokens[tr.main[n]].kind == .Not { call = graph_op_value(b, .Unary, w, span, Type_Bool{}, graph_token_text(.Not), call) }
    return {v = call, ok = true}
}

// Whether a type is a pointer.
is_ptr_type :: proc(t: Type) -> bool {
    _, is_ptr := distinct_base(t).(^Type_Ptr)
    return is_ptr
}

// `#caller_name`, `#caller_span` (tc_hash_name): an atom — the enclosing
// fun's name, where it is (a default's: the call's, `span`), by its place in
// the program's table; `#web` and the targets: a bool.
lw_hash_name :: proc(k: ^TC, n: Tree_Id, want: Build_Want, w: Written, span: Span) -> Built {
    b := k.gb
    name := tc_text(Token_Id(k.t.a[n]))
    if want == .Place { return {} }
    flag: bool
    switch name {
    case "caller_name", "caller_span":
        text := lw_enclosing_fn_name(k) if name == "caller_name" else span_location(span)
        id := checked_atom(k.checked, text)
        return {v = graph_const(b, w, span, Type_Atom{}, name, Const_Value{int = i128(id)}), ok = true}
    case "web":     flag = k.c.target_web
    case "native":  flag = !k.c.target_web
    case "windows": flag = k.c.target_os == .Windows
    case "linux":   flag = k.c.target_os == .Linux
    case "mac":     flag = k.c.target_os == .Mac
    case "profile_memory": flag = k.c.profile_memory
    case:
        lw_unsupported(k, n, "this compiler name")
    }
    return {v = graph_const(b, w, span, Type_Bool{}, "", Const_Value{int = 1 if flag else 0}), ok = true}
}

// The fun whose code is being built's name (enclosing_fn_name): `main` at
// a module's level.
lw_enclosing_fn_name :: proc(k: ^TC) -> string {
    if s := k.lower.ts; s != nil { return s.source_name if s.source_name != "" else s.name }
    return "main"
}

// A param's default that is one of its group's one value's results
// (tc_tuple_default): the call built at the first slot, once, each other its
// output.
lw_tuple_default :: proc(k: ^TC, src: Tree_Id, slot: int, w: Written) -> Built {
    b := k.gb
    returns := tc_call_returns(k, src)
    multi := len(returns) > 1
    if slot > 0 && multi {
        op, made := graph_build_tuple_get(b, tc_sid(k, src))
        if !made { lw_fail(k, src, "a default's slot before its call") }
        return {v = {op, i32(slot)}, ok = true}
    }
    r := lw_expr(k, src, .Value, w)
    if multi && slot == 0 { graph_build_tuple_set(b, tc_sid(k, src), r.v.op) }
    return r
}

// A declaration by the shape shortcut (tc_decl_shape): its local (a struct's
// field), then its literal built into it.
lw_decl_shape :: proc(k: ^TC, s, target: Tree_Id, name: string, ann: Type, bindings: []TC_Binding, fields_of: ^Type_Scope) {
    b := k.gb
    span := tree_span(k.t, s)
    decl := lw_field_decl(k, fields_of, name, target, span)
    if decl == NO_NODE { decl = graph_build_decl(b, name, k.t.main[target], span, ann) }
    // (Its construction is the name's, as the checker annotates it.)
    at := lw_at(k, target)
    defer b.at = at
    r := lw_shape_literal(k, s, ann, bindings, .Into, graph_dest_var(decl, ann, tc_sid(k, target)))
    graph_build_typed(b, decl, ann)
    lw_store(k, 0, ann, r, graph_dest_var(decl, ann, tc_sid(k, target)), span, settle = true)
}

// `{inner = Box(5)}` of the shape shortcut (tc_shape_literal).
lw_shape_literal :: proc(k: ^TC, s: Tree_Id, t: Type, bindings: []TC_Binding, want: Build_Want, dest: Dest) -> Built {
    span := tree_span(k.t, s)
    ts := t.(^Type_Scope)
    sd := &ts.sd
    // (A bare declaration's: no constructor run — its other fields unset.)
    gl := graph_build_literal(k.gb, span, "", false, t, dest)
    if gl == nil { lw_fail(k, s, "a literal the graph builds no way") }
    for bd in bindings {
        idx, has := sd.field_map[bd.field]
        if !has { continue }
        lw_literal_field(k, bd.call, sd.fields[idx], 0, bd.field, span, gl)
    }
    return lw_built(k, want, false, false, dest, t, span, false)
}
