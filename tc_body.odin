package mara

import "core:fmt"
import "core:mem/virtual"
import "core:slice"
import "core:strings"

// Bodies, checked statement by statement in the order they run. A struct's
// is its constructor, a fun's body like any other: once it is checked, the
// struct takes what its top block declared as its layout (tc_layout). A
// module's is its files' statements: checked the same, though nothing calls
// it — no code is built of it. (The graph is lowered from them once checking
// is done: lower.odin, which replays each body where TC.events says it was
// checked.)

tc_scope_body :: proc(k: ^TC, sc: ^TC_Scope) {
    t := k.t
    ts := sc.ts
    v := scope_view(t, sc.node) if sc.node != 0 else Scope_View{}
    span := tree_span(t, sc.def)
    ts.sig_state = .In_Progress
    hint := k.hint
    defer k.hint = hint
    outer, outer_vars, outer_defer, outer_loops := k.body, k.vars, k.in_defer, k.loops
    k.body, k.vars, k.in_defer, k.loops = ts, {}, false, 0
    defer {
        if len(k.vars) > 0 { k.annot.vars[ts] = k.vars }
        k.body, k.vars, k.in_defer, k.loops = outer, outer_vars, outer_defer, outer_loops
    }
    if sc.node != 0 { append(&k.annot.bodies, Annot_Body{ts, tc_instance(k, sc.node), tree_lo(k.t, sc.node), sc.node}) }
    tc_register_defs(k, sc)
    // (Its params and named results — locals: its variables, an intrinsic's
    // too, though no code of its reads them. Bound before its constants: a
    // constant may be written with a param that is one, a struct's size.)
    for p in ts.params { tc_bind(k, p.name, p.type_, {p.decl, .Param}) }
    tc_check_local_consts(k, sc)
    // (An intrinsic's body is the compiler's: its signature, the LLVM
    // intrinsic's shape.)
    if v.intrinsic != 0 { check_llvm_intrinsic_signature(k.c, ts, tc_intrinsic_name(k, v.intrinsic), span) }
    if sc.node != 0 {
        k.annot.decls[tc_sid(k, sc.node)] = ts
        tc_event(k, {kind = .Body, sc = sc})   // (lowered from here: after its constants)
    }
    for name, i in ts.return_binding_names { tc_bind(k, name, ts.return_types[i], {ts.return_binding_decls[i], .Result}) }
    if v.intrinsic == 0 {
        tc_type_params_bind(k, sc.subst)   // (an instance's: its type params, checked whenever its body is)
        for stmts in tc_scope_stmts(k, sc) { tc_scope(k, stmts) }
    }
    // (A struct: what its top block declared, its layout. A module is no
    // value: it has none.)
    if ts.kind == .Struct && !ts.is_module { tc_layout(k, sc) }
    ts.sig_state = .Resolved
    // (A default param's width the body left open: settled.)
    solidify_param_defaults(k.c, ts)
    // (Its definitions' bodies, after its own: a struct's methods read its
    // layout.)
    tc_check_defs(k, sc)
    // (Its foreign funs, for the emitter.)
    for s in sc.foreigns { tc_extract_foreign(k, s, ts.name) }
}

// A struct's layout: what its constructor's top block declared, in order —
// each name a field of the type its declaration found (`_` names none; one
// that failed, none). They were its constructor's locals while it was
// checked: taken, they are the struct's fields — no longer among its body's
// variables, and named as fields from here on (what a tool says of one).
// `using f: T` marks its field: T's own fields are reached as the struct's.
tc_layout :: proc(k: ^TC, sc: ^TC_Scope) {
    t := k.t
    ts := sc.ts
    body := scope_view(t, sc.node).body
    tc_early_self(k, body)
    for s in tc_live(k, body) {
        d, using_ := s, false
        if t.tag[s] == .Using { d, using_ = Tree_Id(t.a[s]), true }
        if t.tag[d] != .Decl { continue }
        v := decl_view(t, d)
        // (Several names from one call: each its slot of the call's results.)
        several := len(v.targets) > 1 && len(v.values) == 1 && tc_call_returns(k, v.values[0]) != nil
        for tg, i in v.targets {
            if t.tag[tg] != .Ident { continue }
            name := tc_name(k, tg)
            if name == "_" || name in ts.field_map { continue }
            ft, bound := tc_bound(k, t.main[tg])
            if !bound || ft == nil { continue }
            if _, failed := ft.(Type_Error); failed { continue }
            value: Tree_Id
            if len(v.values) == 1 { value = v.values[0] } else if i < len(v.values) { value = v.values[i] }
            // (`x : T = void`: no default — the field starts unset.)
            if value != 0 && tc_is_void(k, value) && !tc_is_pointer(ft) && !void_is_value(ft) { value = 0 }
            // (A width its uses left open: settled, as a local's is.)
            append(&ts.fields, Struct_Type_Field{name = name, decl = t.main[tg], type_ = solidify_type(ft), default_node = value,
                                                 default_slot = i if several else nil, is_using = using_})
            build_field_map(&ts.sd)
            tc_set_ref(k, tg, {t.main[tg], .Field})
            for vd, at in k.vars {
                if vd.tok == t.main[tg] { ordered_remove(&k.vars, at); break }
            }
            if !using_ { continue }
            f := ts.fields[len(ts.fields) - 1]
            if _, is_array := f.type_.(^Type_Fixed_Array); is_array { continue }
            sd := as_scope_body(f.type_)
            if sd != nil { tc_struct_ensure(k, sd_type_scope(sd)) }   // (its fields known)
            if sd == nil || len(sd.fields) == 0 { tc_error(k, tree_span(t, sc.def), TYPE_USING_FIELD_STRUCT_FIXED_ARRAY, f.name) }
        }
    }
}

// A block's statements: each checked whole before the next.
tc_scope :: proc(k: ^TC, stmts: []Tree_Id) {
    t := k.t
    stmts := tc_live(k, stmts)   // (`#if`: its live arm's, in its place)
    // (Its declarations, for the stack's size guard at its end.)
    saved := k.decls
    decls := make([dynamic]TC_Decl_Note, virtual.arena_allocator(k.blocks))   // (scratch: the check's)
    k.decls = &decls
    defer {
        tc_storage_sizes(k, decls[:])
        k.decls = saved
    }
    for s in stmts {
        if t.tag[s] == .Define || t.tag[s] == .Foreign {
            // (A body's definitions, its blocks' too, are registered and checked
            // with it: tc_body_defs.)
            continue
        }
        tc_stmt(k, s)
    }
}

tc_stmt :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    k.hint = nil   // (What the last statement was checked as is nothing to this one.)
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        e := Tree_Id(t.a[s])
        if t.tag[e] == .Import { return }   // (`use m`: checked before its module — tc_check_uses)
        if tc_override(k, e) { return }
        k.several_ok = tc_unparen(k, e)   // (what it drops: said below)
        rt := tc_check(k, e)
        k.several_ok = 0
        // A call's value, dropped: `_ = f()` says so.
        if tc_is_call(k, e) && rt != nil {
            _, is_void := rt.(Type_Void)
            _, is_error := rt.(Type_Error)
            if !is_void && !is_error { tc_error(k, span, TYPE_DISCARDED_RETURN, tc_call_name(k, e)) }
        } else if op := tc_unparen(k, e); (t.tag[op] == .Binary || t.tag[op] == .Unary) && rt != nil {
            tc_dropped_value(k, op, rt, span)
        } else if name := tc_diag_name(k, op); t.tag[op] == .Ident && rt != nil && tc_type_source_name(rt) == name {
            // (A type's name alone: there's nothing to run.)
            tc_error(k, span, TYPE_TYPE_NOT_VALUE, name)
        } else if _, failed := rt.(Type_Error); rt != nil && !failed && tc_only_reads(k, op) {
            // (A value read and dropped: `if c do done` meant `done = true`.)
            check_warning(k.c, span, WARN_LINE_DOES_NOTHING, tc_written(k, op), tc_written(k, op))
        }
    case .Decl:
        tc_decl(k, s)
    case .Using:
        // (`using f: T`: f's declaration. What `using` says is its layout's:
        // tc_layout.)
        if d := Tree_Id(t.a[s]); t.tag[d] == .Decl { tc_decl(k, d) } else { tc_unsupported(k, s, "this `using`") }
    case .Assign:
        tc_assign(k, s)
    case .Return:
        tc_return(k, s)
    case .If, .Elif:
        tc_if(k, s)
    case .For_Range, .For_Each, .For_C, .For_Cond:
        tc_for(k, s)
    case .Compound:
        tc_compound(k, s)
    case .Defer:
        // (Its block leaves only by its end: no `?`, `return`, or loop exit
        // to a loop around it.)
        if tree_defer_on_failure(t, s) { tc_defer_on_failure(k, s) }
        in_defer, loops := k.in_defer, k.loops
        k.in_defer, k.loops = true, 0
        tc_scope(k, tree_list(t, t.a[s]))
        k.in_defer, k.loops = in_defer, loops
    case .Allocator:
        tc_allocator(k, s)
    case .Overload:
        tc_validate(k, s)   // (its group: one in sight)
    case .Module:
        // (`module m`: the module that includes this file — its first line.)
        if first := tree_list(t, t.a[t.files[build_tokens[t.first[s]].file]]); first[0] != s { tc_error(k, span, TYPE_MODULE_AT_TOP) }
    case .Match:
        tc_match(k, s)
    case .Break, .Continue:
        if k.loops == 0 {
            word := "break" if t.tag[s] == .Break else "continue"
            tc_error(k, span, TYPE_LOOP_EXIT_IN_DEFER if k.in_defer else TYPE_LOOP_EXIT_OUTSIDE_LOOP, word)
        }
    case:
        tc_unsupported(k, s, "this statement")
    }
}


// An expression that only reads — a name, a field, an item, a literal — with
// no call at its top (an overloaded index is one): alone on a line, nothing.
tc_only_reads :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[n] {
    case .Number, .String, .Char, .True, .False, .Ident, .Dot_Ident, .Deref, .Field, .In_Range, .Literal, .Array, .Size_Of, .Self:
        return true
    case .Index, .Slice:
        return tc_callee(k, n) == nil
    }
    return false
}

// An operator's value on a line of its own, `clean ++ c`: an error, as a
// call's dropped value is — unless its left side is a pointer, `&clean ++ c`:
// what the pointer is to is what an overload's function was called to change.
tc_dropped_value :: proc(k: ^TC, n: Tree_Id, rt: Type, span: Span) {
    _, is_void := rt.(Type_Void)
    _, is_error := rt.(Type_Error)
    if is_void || is_error { return }
    t := k.t
    if t.tag[n] == .Binary && tc_callee(k, n) != nil {
        left := Tree_Id(t.a[n])
        if _, through := distinct_base(tc_node_type(k, left)).(^Type_Ptr); through { return }
        // (A chain's, `a ++ b ++ c`: the one it starts from.)
        first := tc_unparen(k, left)
        for t.tag[first] == .Binary { first = tc_unparen(k, Tree_Id(t.a[first])) }
        tc_error(k, span, TYPE_DROPPED_OPERATOR_VALUE, tc_written(k, n), tc_written(k, first), tc_written(k, n))
        return
    }
    tc_error(k, span, TYPE_DROPPED_VALUE, tc_written(k, n))
}

// `defer?`: only where a failure ends the code — a function that returns an
// err, as `?` needs — and not in a defer's block, which ends no function.
tc_defer_on_failure :: proc(k: ^TC, s: Tree_Id) {
    span := tree_span(k.t, s)
    if rts := tc_results(k); len(rts) == 0 || !is_err_type(rts[len(rts) - 1]) {
        tc_error(k, span, TYPE_DEFER_ERR_OUTSIDE_ERR_FUNCTION)
    } else if k.in_defer {
        tc_error(k, span, TYPE_DEFER_ERR_IN_DEFER)
    }
}

// `x := v`, `x : T = v`, `x : T`: its type the annotation's, else the
// value's.
tc_decl :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    v := decl_view(t, s)
    if len(v.targets) > 1 && len(v.values) == 1 {
        // (Several from one value: its results — bare names declared, places
        // stored.)
        tc_destructure(k, s, v.targets, v.values[0], true, v.type_)
        return
    }
    for tg in v.targets {
        if t.tag[tg] != .Ident {
            tc_unsupported(k, s, "a declaration of no name")
            return
        }
    }
    if len(v.values) > 0 && len(v.values) != len(v.targets) {
        tc_unsupported(k, s, "this declaration")
        return
    }
    for tg, i in v.targets {
        tc_decl_one(k, s, tg, v.values[i] if i < len(v.values) else 0, v.type_)
    }
}

// One name's declaration.
tc_decl_one :: proc(k: ^TC, s, target, value, ann_node: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    name := tc_name(k, target)
    if name == "_" {
        // (`_ := v` names nothing — no variable, no field: v checked for its
        // own sake, as `_ = v` does.)
        k.hint = tc_type(k, ann_node, span) if ann_node != 0 else nil
        if value != 0 { tc_check(k, value) }
        return
    }
    ref := tc_decl_ref(k, target)
    tc_set_ref(k, target, ref)
    ann: Type = Type_Any{}
    if ann_node != 0 { ann = tc_type(k, ann_node, span) }
    if !tc_declarable(k, ref, name, span) {
        tc_bound_set(k, ref.decl, Type_Error{})   // (its uses aren't reported again)
        return
    }
    if ann_node != 0 && ck_decl_fits(k, ann, value) {   // (the lean core's: ck.odin)
        ck_decl(k, s, target, value, name, ann, ref)
        return
    }
    form, cap_n, bindings := tc_decl_form(k, value, ann_node, ann)
    if cap_n != 0 {
        // (`s : [:n]T`: a slice views storage that exists — it would be
        // storage of its own.)
        if sl, is_slice := ann.(^Type_Slice); is_slice {
            e := type_name(sl.elem)
            tc_error(k, span, TYPE_SLICE_SIZED_DECLARATION, name, e)
        }
        tc_set_type(k, target, ann)
        tc_bind(k, name, ann, ref)
        return
    }
    if form == .Void {
        tc_decl_void(k, s, target, value, name, ann)
        return
    }
    #partial switch form {
    case .Take:
        tc_decl_take(k, s, target, value, name, ann)
        return
    case .Shape:
        tc_decl_shape(k, s, target, name, ann, bindings)
        return
    case .Bare:
        tc_decl_bare(k, target, name, ref, ann, span)
        return
    }
    k.hint = ann
    errors_before := k.c.errors
    // (One name for a call's several results: said below. A `?`'s, by it.)
    if tc_is_call(k, tc_unparen(k, value)) { k.several_ok = tc_unparen(k, value) }
    vt := tc_check(k, value)
    k.several_ok = 0
    if is_any(ann) && !tc_is_value(k, value, vt, span) {
        tc_bind(k, name, Type_Error{}, ref)
        return
    }
    tc_no_literal_slice(k, vt if is_untyped(ann) else ann, value, span)
    tc_check_big_endian(k, value, span)
    if returns := tc_call_returns(k, value); len(returns) > 1 {
        // (One name for several results: `a, b := f()` takes them.)
        tc_error(k, span, TYPE_MULTI_RETURN_ASSIGN_LEFT_SIDE, 1, len(returns))
        tc_bind(k, name, Type_Error{}, ref)
        return
    }
    final: Type
    if !is_any(ann) {
        // (Bytes read as the annotation's type: no conversion to check.)
        flow := tc_check_byte_flow(k, ann, value, vt, span)
        if flow == .Read { tc_span_read_size(k, value, ann, tc_is_distinct(ann), span) }
        fa, to_array := distinct_base(ann).(^Type_Fixed_Array)
        // (A distinct type: matched by name — unless the value is a literal
        // not of it, matched by its shape.)
        #partial switch t.tag[tc_unparen(k, value)] {
        case .Array, .Literal, .Broadcast:
            if tc_is_distinct(ann) && types_equal(ann, vt) { to_array = false }
        case:
            if tc_is_distinct(ann) { to_array = false }
        }
        if to_array && flow == .None {
            // (A fixed array: its elements', and room for them.)
            tc_array_assign(k, span, name, fa, vt, value)
        } else if flow == .None && !coerce_deferred(k.c, vt, ann, span) && types_incompatible(ann, vt) {
            tc_assign_error(k, span, vt, name, ann, value)
        }
        tc_value_at(k, value, vt, ann, span)
        final = ann
    } else if existing, shadowed := tc_declared_before(k, ref); shadowed {
        // (Reported as a shadow: checked as the write it reads as.)
        tc_check_write(k, value, vt, existing, name, span)
        return
    } else if is_infer(vt) {
        // Its width is the one its uses give it (unify_infer_concrete): all the same.
        cell := new(Infer_Cell)
        cell.name, cell.span = name, span
        if src := infer_cell_of(vt); src != nil { unify_infer_cells(k.c, cell, src, span) }
        if _, is_float := vt.(Type_Infer_Float); is_float {
            final = Type_Infer_Float{cell = cell}
        } else {
            final = Type_Infer_Int{cell = cell}
        }
    } else {
        final = solidify_type(vt)
        // (`x := [a, b, c]` whose len its fun sets: a list, as `x : [3]T = …` is.)
        if fa, is_fixed := final.(^Type_Fixed_Array); is_fixed && fa.index_type == nil && tc_literal_grows(k, ref.decl, value) {
            final = type_partial_array(fa.size, fa.elem)
            tc_value_at(k, value, vt, final, span)
        }
        if is_untyped(final) && k.c.errors == errors_before {
            check_warning(k.c, span, TYPE_VARIABLE_CONCRETE_TYPE_TYPE_CHECKING, name)
        }
        if is_cstring(final) { tc_error(k, span, TYPE_CSTRING_FOREIGN_ONLY) }
    }
    tc_bind(k, name, final, ref)
    tc_set_type(k, target, final)   // (the name declared: its type)
    tc_settle(k, value, final)
    tc_note_decl(k, name, final, span, k.t.tag[tc_unparen(k, value)] == .Take)
}

// Whether `x := [a, b, …]` (decl: x; value: the literal) is a list: its fun
// sets x's len or appends to it — `x.len = n`, `x.len -= 1`, `&x ++ v` —
// which only a list does. (By the resolver's refs: uses not checked yet.)
tc_literal_grows :: proc(k: ^TC, decl: Token_Id, value: Tree_Id) -> bool {
    tr := k.t
    if tr.tag[tc_unparen(k, value)] != .Array || k.body == nil { return false }
    i, ok := k.scope_of[k.body]
    if !ok { return false }
    names_x :: proc(k: ^TC, n: Tree_Id, decl: Token_Id) -> bool {
        n := tc_unparen(k, n)
        return k.t.tag[n] == .Ident && k.rs.refs[n].decl == decl
    }
    len_of_x :: proc(k: ^TC, n: Tree_Id, decl: Token_Id) -> bool {
        n := tc_unparen(k, n)
        return k.t.tag[n] == .Field && tc_text(Token_Id(k.t.b[n])) == "len" && names_x(k, Tree_Id(k.t.a[n]), decl)
    }
    hi := k.scopes[i].node
    for n in tree_lo(tr, hi) ..= hi {
        #partial switch tr.tag[n] {
        case .Assign:
            for tg in tree_list(tr, tr.a[n]) { if len_of_x(k, tg, decl) { return true } }
        case .Compound:
            if len_of_x(k, Tree_Id(tr.a[n]), decl) { return true }
        case .Binary:
            l := tc_unparen(k, Tree_Id(tr.a[n]))
            if tc_text(tr.main[n]) == "++" && tr.tag[l] == .Unary && tc_text(tr.main[l]) == "&" && names_x(k, Tree_Id(tr.a[l]), decl) { return true }
        }
    }
    return false
}

// What a declaration is, as written — the checker and lowering each read it
// here: `x : T = void`, T no pointer (uninitialized: a pointer's void is its
// null, a value, a field reference's too: void_is_value); `x := take(…)`; `x : T` with no value, by a shape's
// `bindings` or bare; or one of a value. `cap_n`: `[:n]T`'s count, n — on a
// declaration, an error (a slice has no storage of its own).
Decl_Form :: enum u8 { Value, Void, Take, Shape, Bare }

tc_decl_form :: proc(k: ^TC, value, ann_node: Tree_Id, ann: Type) -> (form: Decl_Form, cap_n: Tree_Id, bindings: []TC_Binding) {
    t := k.t
    if ann_node != 0 && t.tag[ann_node] == .Type_Slice {
        cap_n = Tree_Id(t.a[ann_node])
    }
    switch {
    case value != 0 && tc_is_void(k, value) && !tc_is_pointer(ann) && !void_is_value(ann): form = .Void
    case value != 0 && t.tag[tc_unparen(k, value)] == .Take:         form = .Take
    case value == 0:
        bindings = tc_shape_bindings(k, ann_node)
        form = .Shape if len(bindings) > 0 else .Bare
    }
    return
}

// What a declaration's name declares: its own token, a local.
tc_decl_ref :: proc(k: ^TC, target: Tree_Id) -> Ref {
    return {k.t.main[target], .Local}
}

// Whether a name can be declared here (tok: the token that declares it):
// not in this scope already, and no constant's, fun's, type's or module's
// in sight (it would hide that one) — the resolver's. (Shadowing
// an enclosing local is reported, and declares.) A param's name is taken
// too: params and what the body declares are one name space, so a field or
// a local named as a param would be ambiguous.
tc_declarable :: proc(k: ^TC, ref: Ref, name: string, span: Span) -> bool {
    c := k.rs.clashes[ref.decl] or_else {}
    if c.taken {
        if c.param && k.body != nil {
            tc_error(k, span, TYPE_DECLARATION_NAMES_PARAM, name, scope_display_name(k.body), "variable")
        } else {
            tc_error(k, span, TYPE_VARIABLE_ALREADY_DECLARED_SCOPE, name)
        }
        return false
    }
    // (A fun's, a type's, a module's name: said as that, not as a shadow.)
    if c.hides.kind != .None {
        word := "fun" if c.hides.kind == .Fun else "type" if c.hides.kind == .Type else "module"
        at := c.hides.decl
        tc_error(k, span, TYPE_VARIABLE_HIDES_DEFINITION, name, word, name, span_loc(Span{at = at, tok = at, end = at + 1}))
        return false
    }
    if c.shadows { tc_error(k, span, TYPE_VARIABLE_SHADOWS_ENCLOSING_BINDING, name) }
    if c.constant {
        tc_error(k, span, TYPE_VARIABLE_SHADOWS_CONSTANT_OUTER_SCOPE, name)
        return false
    }
    return true
}

// A name the resolver found nothing for, said so: an enclosing scope's local,
// that is the rule it broke; else msg.
tc_unresolved :: proc(k: ^TC, miss: Rs_Miss, span: Span, name: string, msg: string) {
    if miss.hidden != "" {
        tc_error(k, span, TYPE_LOCAL_OF_ENCLOSING_SCOPE, name, miss.hidden)
        return
    }
    // (What there was before #allocator and main's args: what's there now.)
    if name == "this_program" || name == "Program" {
        tc_error(k, span, TYPE_THIS_PROGRAM_GONE, name)
        return
    }
    if tc_behind_use(k, span, name) { return }
    tc_error(k, span, msg, name)
}

// A name a use keeps behind its module's name (`s :: use mara.string`, for
// `trimmed`), said so. Whether it is one.
tc_behind_use :: proc(k: ^TC, span: Span, name: string) -> bool {
    alias, module := resolve_named_use_of(k.rs, span.at, name) or_return
    tc_error(k, span, TYPE_NAME_BEHIND_USE, name, alias, module, alias, name)
    return true
}

// `x : T`: its zero, unset until written — a struct's constructor doesn't
// run (`x := T()` runs it); flow.odin's definite assignment finds a read
// before a write.
tc_decl_bare :: proc(k: ^TC, target: Tree_Id, name: string, ref: Ref, ann: Type, span: Span) {
    tc_set_type(k, target, ann)
    defer tc_bind(k, name, ann, ref)
    tc_note_decl(k, name, ann, span, false)
    if _, is_error := ann.(Type_Error); is_error { return }
    if (ref.kind == .Local || ref.kind == .Field) && is_partial_array(ann) { k.lists[ref.decl] += {.Fresh} }
    if is_any(ann) { tc_error(k, span, TYPE_DECLARATION_WITHOUT_INITIALIZER_REQUIRES_TYPE) }
}


// A name already declared where a declaration (tok) would declare it, below
// the module — the resolver's: what it means.
tc_declared_before :: proc(k: ^TC, ref: Ref) -> (Type, bool) {
    c := k.rs.clashes[ref.decl] or_else {}
    if c.before == 0 { return nil, false }
    return tc_bound(k, c.before)
}

// A value written to a variable of type `existing`: checked against it.
tc_check_write :: proc(k: ^TC, value: Tree_Id, vt, existing: Type, name: string, span: Span) {
    tc_no_literal_slice(k, existing, value, span)
    if tc_check_byte_flow(k, existing, value, vt, span) != .None { return }
    if !coerce_deferred(k.c, vt, existing, span) && !coerce_deferred(k.c, existing, vt, span) &&
       types_incompatible(existing, vt) {
        tc_assign_error(k, span, vt, name, existing, value)
    }
    tc_value_at(k, value, vt, existing, span)
}

is_slice_type :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Slice)
    return ok
}

// `x = v`: the value at the variable's type.
tc_assign :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    targets := tree_list(t, t.a[s])
    values := tree_list(t, t.b[s])
    if len(targets) > 1 && len(values) == 1 {
        tc_destructure(k, s, targets, values[0], false, 0)
        return
    }
    if len(targets) > 1 && len(targets) == len(values) {
        for tg, i in targets { tc_assign_one(k, s, tg, values[i]) }
        return
    }
    if len(targets) != 1 || len(values) != 1 {
        tc_unsupported(k, s, "this assignment")
        return
    }
    // (`_ = f()`: all its results dropped, on purpose.)
    if t.tag[targets[0]] == .Ident && tc_name(k, targets[0]) == "_" { k.several_ok = tc_unparen(k, values[0]) }
    tc_assign_one(k, s, targets[0], values[0])
    k.several_ok = 0
}

// One target's assignment (a broadcast's copies are each one).
tc_assign_one :: proc(k: ^TC, s, target, value: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[target] {
    case .Field: tc_field_assign(k, s, target, value)
    case .Index: tc_index_assign(k, s, target, value)
    case .Slice: tc_slice_assign(k, s, target, value)
    case .Deref: tc_deref_assign(k, s, target, value)
    }
    #partial switch t.tag[target] {
    case .Field, .Index, .Slice, .Deref:
        // (Into a constant: its storage is read-only.)
        if cname, is_const := tc_write_root_const(k, target); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
        return
    case .Ident:
    case:
        tc_unsupported(k, target, "this assignment target")
        return
    }
    name := tc_name(k, target)
    if name == "_" {
        // A discard: the value checked for its own sake.
        k.hint = nil
        tc_check(k, value)
        return
    }
    existing, ref, ok := tc_name_write(k, target, name, span)
    if !ok { return }
    if tc_is_void(k, value) {
        // (`x = void` de-initializes: the void value written, unchecked.)
        tc_check(k, value)
        return
    }
    if !tc_is_variable(ref) {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    vt := tc_check(k, value)
    // (A pointer given what it points at: written through with `^` — a local
    // can point elsewhere, so `=` doesn't guess. A param can't: `out = v`.)
    if p, is_ptr := distinct_base(existing).(^Type_Ptr); is_ptr && types_incompatible(existing, vt) && !types_incompatible(p.elem, vt) {
        tc_error(k, span, TYPE_ASSIGN_POINTER_LOCAL, name, type_name(existing), name, tc_written(k, value))
        return
    }
    tc_check_write(k, value, vt, existing, name, span)
}

// A write to a bare name, checked: the name is declared, no constant, and no
// param the fun can't write. Its type and what it refers to; ok false when
// it can't be written (reported).
tc_name_write :: proc(k: ^TC, target: Tree_Id, name: string, span: Span) -> (existing: Type, ref: Ref, ok: bool) {
    ref = k.rs.refs[target]
    found: bool
    existing, found = tc_ref_type(k, ref, name)
    if found {
        tc_set_ref(k, target, ref)
        tc_set_type(k, target, existing)   // (the name written: its type)
        tc_list_use(k, ref.decl, existing, false, false, span)
    }
    if ref.kind == .Const {
        tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, name)
        return nil, {}, false
    }
    if !found {
        tc_unresolved(k, k.rs.misses[target] or_else {}, span, name, TYPE_ASSIGN_UNDECLARED_VARIABLE)
        tc_bind(k, name, Type_Error{}, {})
        tc_bound_set(k, k.t.main[target], Type_Error{})   // (what the resolver declared it as: its uses aren't reported again)
        return nil, {}, false
    }
    // (No param can be written: one passed by address is the caller's value,
    // any other is held as its argument.)
    if ref.kind == .Param {
        if is_immutable_param_type(existing) { tc_error(k, span, TYPE_CANNOT_ASSIGN_IMMUTABLE_PARAMETER, name) } else { tc_error(k, span, TYPE_CANNOT_ASSIGN_PARAMETER, name, name) }
    }
    return existing, ref, true
}

// Whether a name refers to a variable: a body's, a param, a named result, a
// struct's field (in its body), a module's.
tc_is_variable :: proc(ref: Ref) -> bool {
    #partial switch ref.kind {
    case .Local, .Param, .Result, .Field: return true
    }
    return false
}

// `return a, b`: each value at its result's type (trailing errs implied `.Ok`).
tc_return :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    if k.in_defer {
        tc_error(k, span, TYPE_RETURN_IN_DEFER)
        return
    }
    values := tree_list(t, t.a[s])
    rts := tc_results(k)
    expected, supplied := len(rts), len(values)
    trailing_errs := 0
    for i := expected - 1; i >= 0 && is_err_type(rts[i]); i -= 1 { trailing_errs += 1 }
    least := expected - trailing_errs
    // (`return f()`, f's several results: each returned, in turn — as many
    // as `return a, b` could give, the errs left out Ok — each at its
    // result's type. lw_return. The call checked first, as the first result
    // would be: a method's results are known once it's found.)
    lone: Type   // (a lone call's type, checked here: the loop below takes it)
    if supplied == 1 && expected > 0 {
        if call := tc_unparen(k, values[0]); tc_is_call(k, call) {
            k.hint = rts[0]
            k.several_ok = call
            lone = tc_check(k, values[0])
            k.several_ok = 0
            if returns := tc_call_returns(k, values[0]); len(returns) > 1 {
                if len(returns) > expected || len(returns) < least {
                    tc_error(k, span, TYPE_RETURN_SEVERAL_COUNT, len(returns), expected, tc_call_name(k, call))
                    return
                }
                for rt, i in returns {
                    want := rts[i]
                    if tc_array_returned_as_slice(k, 0, rt, want, span) { continue }
                    if !is_any(rt) && !is_any(want) && !coerce_deferred(k.c, rt, want, span) && !types_equal(want, rt) {
                        tc_error(k, span, TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED, i + 1, type_name(rt), type_name(want))
                    }
                }
                return
            }
        }
    }
    switch {
    case expected == 0 && supplied > 0:
        // (What it gives back named: the `-> T` its fun is missing.)
        k.hint = nil
        names := make([]string, supplied, context.temp_allocator)
        for val, i in values { names[i] = type_name(solidify_type(tc_check(k, val))) }
        what := strings.join(names, ", ", context.temp_allocator)
        tc_error(k, span, TYPE_RETURN_FROM_NO_RESULT, what, what)
        return
    case expected == 1 && supplied > 1:
        tc_error(k, span, TYPE_RETURN_SEVERAL_FOR_ONE, supplied, type_name(rts[0]))
        return
    case expected == 1 && supplied == 0 && least > 0, expected > 1 && (supplied > expected || supplied < least):
        tc_error(k, span, TYPE_RETURN_VALUE_COUNT_MATCH_EXPECTED, supplied, expected)
        return
    }
    for val, i in values {
        want := rts[i]
        k.hint = want
        vt := lone if i == 0 && lone != nil else tc_check(k, val)
        // (An err passed on by hand, `return 0, e`: its trace's next site.)
        if _, to_err := distinct_base(want).(Type_Err); to_err {
            if _, of_err := distinct_base(vt).(Type_Err); of_err { tc_note_err_pass(k, val, returned = true) }
        }
        if tc_array_returned_as_slice(k, val, vt, want, span) { continue }
        if !is_any(vt) && !is_any(want) && !coerce_deferred(k.c, vt, want, span) &&
           !types_equal(want, vt) {
            if expected > 1 {
                tc_error(k, span, TYPE_RETURN_VALUE_TYPE_MATCH_EXPECTED, i + 1, type_name(vt), type_name(want))
            } else {
                tc_error(k, span, TYPE_RETURN_TYPE_MATCH_EXPECTED, type_name(vt), type_name(want))
            }
        }
        tc_value_at(k, val, vt, want, span)
    }
}

// An array — fixed, partial — returned where a slice is given back: an
// error, said so (true). Elsewhere an array passes as a slice, a view of it;
// given back, the view would outlive the array, the fun's own. A text
// literal too (the user's call): a fun giving text back says how much room
// it gives, `-> str64`, the literal copied into the caller's. `val` 0: a
// call's results forwarded, `return f()`.
tc_array_returned_as_slice :: proc(k: ^TC, val: Tree_Id, vt, want: Type, span: Span) -> bool {
    if _, to_slice := distinct_base(want).(^Type_Slice); !to_slice { return false }
    #partial switch _ in distinct_base(vt) {
    case ^Type_Fixed_Array, ^Type_Partial_Array:
    case:
        return false
    }
    if val != 0 && tc_text_literal(k, val) {
        tc_error(k, span, TYPE_RETURN_TEXT_AS_SLICE, type_name(want))
        return true
    }
    what := type_name(vt) if val == 0 else tc_source_desc(k, val, vt)
    tc_error(k, span, TYPE_RETURN_ARRAY_AS_SLICE, what, type_name(want), type_name(vt))
    return true
}

// `if c {…} elif d {…} else {…}`: the condition a bool or an error
// (is_condition_type), then each block (an elif, the else block's one
// statement).
tc_if :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    v := if_view(t, s)
    if v.hash != 0 {
        // (One whose condition is known is folded away: tc_live.)
        tc_error(k, tree_span(t, v.cond), TYPE_CONDITION_COMPTIME_KNOWN_BOOLEAN)
        return
    }
    ct := tc_check(k, v.cond)
    if !is_condition_type(ct) { tc_not_condition(k, span, ct, TYPE_CONDITION_BOOL_2, type_name(ct)) }
    tc_scope(k, v.then)
    if len(v.else_) > 0 { tc_scope(k, v.else_) }
}

// --- loops ------------------------------------------------------------------

// `for i in lo..hi`, `for e, i in c`, `for init; cond; step`, `for cond`: its
// variables bound in its block, then its body.
// How a run of a loop's body can end: leaving the loop (a `break`, a
// `return`), going round again (a `continue`), or reaching the body's end
// (going round again too).
Loop_End :: enum u8 { Exit, Loop, Fall }

// The ways a loop body's statements, run in order, can end its run: each
// statement's, while one can fall through to the next.
tc_body_ends :: proc(k: ^TC, stmts: []Tree_Id) -> bit_set[Loop_End] {
    ends := bit_set[Loop_End]{.Fall}
    for s in stmts {
        if .Fall not_in ends { break }
        ends = ends - {.Fall} + tc_stmt_ends(k, s)
    }
    return ends
}

// One statement's: a `break` or `return` leaves; a `continue` goes round; an
// `if`'s, its branches' (no `else`: falls too); any other falls — or goes
// round, when a `continue` of this loop is somewhere in it.
tc_stmt_ends :: proc(k: ^TC, s: Tree_Id) -> bit_set[Loop_End] {
    t := k.t
    #partial switch t.tag[s] {
    case .Break, .Return: return {.Exit}
    case .Continue:       return {.Loop}
    case .If:
        v := if_view(t, s)
        if v.hash == 0 {
            ends := tc_body_ends(k, v.then)
            return ends + (tc_body_ends(k, v.else_) if len(v.else_) > 0 else {.Fall})
        }
    }
    return {.Fall, .Loop} if tc_has_continue(k, s) else {.Fall}
}

// Whether a `continue` of the loop a statement is in is somewhere in it (not
// in a loop of its own, nor a fun defined there).
tc_has_continue :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := k.t
    #partial switch t.tag[n] {
    case .Continue: return true
    case .For_Each, .For_Range, .For_C, .For_Cond, .Fun_Def, .Struct_Def: return false
    }
    kids := make([dynamic]Tree_Id, context.temp_allocator)
    tree_children(t, n, &kids)
    for c in kids { if tc_has_continue(k, c) { return true } }
    return false
}

// What a loop over a collection of type `ct` walks: its elements' type — an
// array's, a slice's, a partial array's (nil: no collection).
loop_elem :: proc(ct: Type) -> Type {
    #partial switch c in distinct_base(ct) {
    case ^Type_Fixed_Array:   return c.elem
    case ^Type_Slice:         return c.elem
    case ^Type_Partial_Array: return c.elem
    }
    return nil
}

// ... or through a pointer to one, `for f in files` (files: ^[]T): its
// items' — one level, as indexing and fields see through it.
loop_elem_through :: proc(ct: Type) -> Type {
    if e := loop_elem(ct); e != nil { return e }
    if pt, is_ptr := distinct_base(ct).(^Type_Ptr); is_ptr { return loop_elem(pt.elem) }
    return nil
}

// A range's counter: of the type written (nil: none), else its bounds' — at
// the header's width when they disagree or have none.
range_counter :: proc(lt, ht, written: Type) -> Type {
    if written != nil { return written }
    it := try_promote_numeric(lt, ht)
    if _, is_error := it.(Type_Error); is_error || is_infer(it) { return slice_header_width_type }
    return it
}

tc_for :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    v := for_view(t, s)
    k.loops += 1
    defer k.loops -= 1
    // (A loop whose every run ends in its `break` or a `return` runs once at
    // most: said so, a warning — a statement one-lined out of its block
    // (`if a do x = 1; break`) is the usual why.)
    defer if tc_body_ends(k, v.body) == {.Exit} { emit_diagnostic_once(.Warning, span, WARN_LOOP_NEVER_LOOPS) }
    #partial switch t.tag[s] {
    case .For_Each:
        // (A type looped over: its values — tc_loop_over_type.)
        if ft, is_field_type := tc_looped_field_type(k, tc_unparen(k, v.collection), span); is_field_type {
            tc_set_type(k, tc_unparen(k, v.collection), ft)
            tc_loop_over_type(k, v, ft, span)
            return
        }
        // (A call of several results: a loop over the call — tc_for_call.)
        call := tc_unparen(k, v.collection)
        if tc_is_call(k, call) { k.several_ok = call }
        k.list_ok = call   // (looped over: no change to it)
        ct := tc_check(k, v.collection)
        k.several_ok = 0
        tc_list_looped(k, call, ct)
        if loops_over_type(k, v.collection) {
            tc_loop_over_type(k, v, ct, span)
            return
        }
        if returns := tc_call_returns(k, v.collection); len(returns) > 1 {
            if v.by_ref != 0 { tc_error(k, span, TYPE_REF_LOOP_OVER_CALL) }
            tc_for_call(k, s, v, ct, returns)
            return
        }
        if names := loop_names(v); len(names) > 2 { tc_error(k, span, TYPE_LOOP_ITEM_NAMES, len(names)) }
        // (A literal looped over is held at its own type, settled.)
        #partial switch k.t.tag[tc_unparen(k, v.collection)] {
        case .Array, .Literal: ct = solidify_type(ct)
        }
        tc_settle(k, v.collection, ct)
        elem := loop_elem_through(ct)
        if elem == nil {
            elem = Type_Error{}
            _, is_error := ct.(Type_Error)
            if is_error {
            } else if tc_is_call(k, call) {
                // (A call of one result: what a loop over a call needs said.)
                tc_error(k, span, TYPE_CANNOT_LOOP_OVER_CALL, tc_call_name(k, call), type_name(ct), type_name(ct))
            } else if st, is_scope := ct.(^Type_Scope); is_scope {
                tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE, scope_display_name(st))
            } else {
                tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_TYPE, type_name(ct))
            }
        }
        if v.type_ != 0 { elem = tc_type(k, v.type_, span) }
        if v.by_ref != 0 { elem = tc_ref_loop(k, v, ct, elem, span) }
        // (An item too big for the stack — a 1 KB struct — would be copied
        // into the loop's name each round, and no loop name lives on the
        // arena: taken where it is instead, `for &item in xs`.)
        if v.by_ref == 0 && v.elem != 0 && tc_text(v.elem) != "_" && elem != nil && routes_to_arena(elem) {
            name := tc_text(v.elem)
            tc_error(k, span, TYPE_LOOP_ITEM_TOO_BIG, name, type_name(elem), type_size(elem), name, tc_written(k, v.collection))
        }
        // (A loop variable named `_` is none: nothing the body can name.)
        tc_loop_name(k, v.elem)
        tc_loop_name(k, v.index)
        if v.elem != 0 && tc_text(v.elem) != "_" { tc_bind(k, tc_text(v.elem), elem, {v.elem, .Local}) }
        if v.index != 0 && tc_text(v.index) != "_" { tc_bind(k, tc_text(v.index), slice_header_width_type, {v.index, .Local}) }
        tc_scope(k, v.body)
    case .For_Range:
        lt := tc_check(k, v.lo)
        ht := tc_check(k, v.hi)
        it := range_counter(lt, ht, tc_type(k, v.type_, span) if v.type_ != 0 else nil)
        tc_settle(k, v.lo, it)
        tc_settle(k, v.hi, it)
        if !is_numeric(lt) && !is_infer(lt) && !is_any(lt) { tc_error(k, span, TYPE_RANGE_LOWER_BOUND_NUMERIC, type_name(lt)) }
        if !is_numeric(ht) && !is_infer(ht) && !is_any(ht) { tc_error(k, span, TYPE_RANGE_UPPER_BOUND_NUMERIC, type_name(ht)) }
        // (A range counts up: known bounds that count down are an error.)
        lc, lc_ok := tc_comptime_int(k, v.lo)
        hc, hc_ok := tc_comptime_int(k, v.hi)
        if lc_ok && hc_ok && lc > hc { tc_error(k, span, TYPE_DESCENDING_RANGE, lc, tc_text(v.dots), hc, lc, hc) }
        tc_loop_name(k, v.var)
        if tc_text(v.var) != "_" { tc_bind(k, tc_text(v.var), it, {v.var, .Local}) }
        tc_scope(k, v.body)
    case:
        if v.init != 0 { tc_stmt(k, v.init) }
        ct := tc_check(k, v.cond)
        if !is_condition_type(ct) { tc_not_condition(k, span, ct, TYPE_CONDITION_BOOL, type_name(ct)) }
        // (`for true in xs`: no name before `in`, so a test of xs's items, looped
        // on — a loop over them was meant. Wrapped, `for (… in xs)`, it's meant.)
        if t.tag[s] == .For_Cond && t.tag[v.cond] == .In_Range && tc_text(t.main[v.cond]) == "in" {
            emit_diagnostic_once(.Warning, tree_span(t, v.cond), WARN_LOOP_ON_IN_TEST, tc_written(k, v.cond), tc_written(k, Tree_Id(t.a[v.cond])))
        }
        if v.post != 0 { tc_stmt(k, v.post) }
        tc_scope(k, v.body)
    }
}

// The most values `for v in T` takes: each is written into the loop's table
// where it begins.
TYPE_LOOP_MOST :: 4096

// A loop's collection that is a field reference's type — `S.bool`, as the
// parser reads it; `Binds.Combos`, its field's type a name (the resolver's:
// a type in sight, no member of Binds) — and that type.
tc_looped_field_type :: proc(k: ^TC, n: Tree_Id, span: Span) -> (Type, bool) {
    t := k.t
    if t.tag[n] == .Type_Field { return tc_type(k, n, span), true }
    ft, named := k.rs.field_types[n]
    if !named || t.tag[n] != .Field { return nil, false }
    owner, _ := tc_ref_type(k, ft.owner, tc_written(k, Tree_Id(t.a[n])))
    elem, _ := tc_ref_type(k, ft.elem, tc_text(Token_Id(t.b[n])))
    return tc_field_type_of(k, owner, elem, span), true
}

// Whether a loop's collection is a type (`for v in Mode`, `for f in S.bool`):
// its values are looped over (type_loop_values).
loops_over_type :: proc(k: ^TC, n: Tree_Id) -> bool {
    n := tc_unparen(k, n)
    if k.t.tag[n] == .Type_Field { return true }
    if _, named := k.rs.field_types[n]; named && k.t.tag[n] == .Field { return true }
    return (k.t.tag[n] == .Ident || k.t.tag[n] == .Field) && tc_ref(k, n).kind == .Type
}

// A type's values, as `for v in T` takes them: an enum's, in the order its
// variants are declared, a value two names share once; a union's, its tags
// (its `Name_Tag`'s); a field reference type's, each field of that type its
// struct holds, in the struct's order. ok false for another type; whole false
// when there are more than TYPE_LOOP_MOST.
type_loop_values :: proc(t: Type) -> (elem: Type, values: []i128, ok, whole: bool) {
    out := make([dynamic]i128, context.temp_allocator)
    by_enum :: proc(out: ^[dynamic]i128, et: ^Type_Enum) {
        Variant :: struct { name: string, value: int, decl: Token_Id }
        vs := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
        for name, value in et.variants { append(&vs, Variant{name, value, et.variant_decls[name]}) }
        slice.sort_by(vs[:], proc(a, b: Variant) -> bool {
            if a.decl != b.decl { return a.decl < b.decl }
            if a.value != b.value { return a.value < b.value }
            return a.name < b.name
        })
        for v in vs { if !slice.contains(out[:], i128(v.value)) { append(out, i128(v.value)) } }
    }
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:
        by_enum(&out, v)
        return t, out[:], true, len(out) <= TYPE_LOOP_MOST
    case ^Type_Union:
        by_enum(&out, v.tag_enum)
        return v.tag_enum, out[:], true, len(out) <= TYPE_LOOP_MOST
    case ^Type_Field:
        paths, all := field_ref_paths(v.owner, v.elem, 2 * TYPE_LOOP_MOST)
        for p in paths { if !slice.contains(out[:], i128(p.value)) { append(&out, i128(p.value)) } }
        return t, out[:], true, all && len(out) <= TYPE_LOOP_MOST
    }
    return nil, nil, false, false
}

// `for v in T`, T a type: one of its values a round (type_loop_values), and
// `for v, i in T` counts them from 0. They're no place: `for &v` is an error.
tc_loop_over_type :: proc(k: ^TC, v: For_View, t: Type, span: Span) {
    elem, values, ok, whole := type_loop_values(t)
    if _, is_error := t.(Type_Error); is_error {
        elem = Type_Error{}
    } else if !ok {
        elem = Type_Error{}
        if st, is_scope := t.(^Type_Scope); is_scope {
            tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_STRUCT_TYPE, scope_display_name(st))
        } else {
            tc_error(k, span, TYPE_CANNOT_ITERATE_OVER_TYPE, type_name(t))
        }
    } else if !whole {
        tc_error(k, span, TYPE_LOOP_OVER_TYPE_TOO_MANY, type_name(t), TYPE_LOOP_MOST)
    }
    _ = values
    if v.by_ref != 0 { tc_error(k, span, TYPE_LOOP_OVER_TYPE_REF, tc_text(v.elem), type_name(t)) }
    if names := loop_names(v); len(names) > 2 { tc_error(k, span, TYPE_LOOP_ITEM_NAMES, len(names)) }
    if v.type_ != 0 { tc_error(k, span, TYPE_LOOP_OVER_TYPE_TYPED, type_name(elem)) }
    tc_loop_name(k, v.elem)
    tc_loop_name(k, v.index)
    if v.elem != 0 && tc_text(v.elem) != "_" { tc_bind(k, tc_text(v.elem), elem, {v.elem, .Local}) }
    if v.index != 0 && tc_text(v.index) != "_" { tc_bind(k, tc_text(v.index), slice_header_width_type, {v.index, .Local}) }
    tc_scope(k, v.body)
}

// A loop's name, said wrong as a declaration's would be (tc_declarable):
// an enclosing loop's name, `for i` inside `for value, i`, hides it — the
// inner loop ran the outer's own counter (sooblivion). It's bound all the
// same.
tc_loop_name :: proc(k: ^TC, tok: Token_Id) {
    if tok == 0 || tc_text(tok) == "_" { return }
    _ = tc_declarable(k, {tok, .Local}, tc_text(tok), Span{at = tok, tok = tok, end = tok + 1})
}

// `for &item in xs`: the loop's name a pointer to each item where it is
// (`item.x += 1`, `item^ = v` write the collection). Its items must be
// somewhere it can write: not an immutable param's, not a constant's, not
// a value made for the loop and kept nowhere (a call's list, a literal) —
// a view or a pointer, whatever gives it, is somewhere.
@(private="file")
tc_ref_loop :: proc(k: ^TC, v: For_View, ct: Type, elem: Type, span: Span) -> Type {
    name := tc_text(v.elem)
    coll := tc_written(k, v.collection)
    if pname, immutable := tc_write_root_param(k, v.collection); immutable {
        tc_error(k, span, TYPE_REF_LOOP_IMMUTABLE_PARAMETER, name, pname, name, coll)
    } else if cname, is_const := tc_write_root_const(k, v.collection); is_const {
        tc_error(k, span, TYPE_REF_LOOP_CONSTANT, name, cname, name, coll)
    } else {
        base := distinct_base(ct)
        _, is_ptr := base.(^Type_Ptr)
        #partial switch k.t.tag[tc_access_root(k, v.collection)] {
        case .Ident, .Deref:
        case:
            if !is_ptr && !is_slice_type(base) { tc_error(k, span, TYPE_REF_LOOP_NO_PLACE, name) }
        }
    }
    return type_ptr(elem)
}

// `for x in f()`, `for x, i in f()`, `for a, b in g()`: the call gives one
// bool, anywhere among its results, and is called each round while it's
// true; its other results are the round's values, in order (loop_call_shape).
// A name for each value, and one more after them that counts the rounds,
// from 0. (`ct`: the call's type as checked.)
tc_for_call :: proc(k: ^TC, s: Tree_Id, v: For_View, ct: Type, returns: []Type) {
    span := tree_span(k.t, s)
    names := loop_names(v)
    flag, values, shaped := loop_call_shape(returns)
    call := tc_call_name(k, tc_unparen(k, v.collection))
    bad := false
    if _, is_error := ct.(Type_Error); is_error {
        bad = true
    } else if !shaped {
        results := make([]string, len(returns), context.temp_allocator)
        for r, i in returns { results[i] = type_name(r) }
        tc_error(k, span, TYPE_LOOP_CALL_RESULTS, call, strings.join(results, ", ", context.temp_allocator))
        bad = true
    } else if len(names) != len(values) && len(names) != len(values) + 1 {
        tc_error(k, span, TYPE_LOOP_CALL_NAMES, call, len(values), "" if len(values) == 1 else "s", len(names))
        bad = true
    } else if v.type_ != 0 {
        if len(values) != 1 {
            tc_error(k, span, TYPE_LOOP_CALL_WRITTEN_TYPES)
        } else if written := tc_type(k, v.type_, span); !types_equal(written, solidify_type(returns[values[0]])) {
            tc_error(k, span, TYPE_LOOP_CALL_WRITTEN_TYPE, type_name(solidify_type(returns[values[0]])), type_name(written))
        }
    }
    _ = flag
    for tok, i in names {
        if tc_text(tok) == "_" { continue }
        t: Type = slice_header_width_type   // (one after the values: the round)
        if bad { t = Type_Error{} } else if i < len(values) { t = solidify_type(returns[values[i]]) }
        tc_loop_name(k, tok)
        tc_bind(k, tc_text(tok), t, {tok, .Local})
    }
    tc_scope(k, v.body)
}

// A for-each's names, in order: its first, its index, the rest.
loop_names :: proc(v: For_View) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    if v.elem != 0 { append(&out, v.elem) }
    if v.index != 0 { append(&out, v.index) }
    append(&out, ..v.more)
    return out[:]
}

// A loop over a call, by its results: which one is its bool, the flag (false:
// done), and its values — the others, in order. ok false when it gives no
// bool, or more than one, or nothing else.
loop_call_shape :: proc(returns: []Type) -> (flag: int, values: []int, ok: bool) {
    flag = -1
    out := make([dynamic]int, context.temp_allocator)
    for r, i in returns {
        if _, is_bool := distinct_base(r).(Type_Bool); is_bool {
            if flag >= 0 { return -1, nil, false }
            flag = i
        } else {
            append(&out, i)
        }
    }
    return flag, out[:], flag >= 0 && len(out) > 0
}

// `x op= v`: `x = x op v`, the operation at the `op=`.
tc_compound :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    target := Tree_Id(t.a[s])
    r := tree_rec(t, t.b[s], 2)
    op_tok, value := Token_Id(r[0]), Tree_Id(r[1])
    #partial switch t.tag[target] {
    case .Field, .Index, .Deref:
        #partial switch t.tag[target] {
        case .Field: tc_field_assign(k, s, target, value, op_tok)
        case .Index: tc_index_assign(k, s, target, value, op_tok)
        case .Deref: tc_deref_assign(k, s, target, value, op_tok)
        }
        if cname, is_const := tc_write_root_const(k, target); is_const { tc_error(k, span, TYPE_CANNOT_WRITE_CONSTANT, cname) }
        return
    case .Ident:
    case:
        tc_unsupported(k, target, "this compound assignment's target")
        return
    }
    name := tc_name(k, target)
    existing, ref, ok := tc_name_write(k, target, name, span)
    if !ok { return }
    if !tc_is_variable(ref) {
        tc_unsupported(k, s, "an assignment to a field or module name")
        return
    }
    k.hint = existing if !is_untyped(existing) else nil
    vt := tc_compound_value(k, s, op_tok, target, value)
    if !coerce_deferred(k.c, vt, existing, span) && !coerce_deferred(k.c, existing, vt, span) &&
       types_incompatible(existing, vt) {
        tc_assign_error(k, span, vt, name, existing, target, value)
    }
}

// A compound assignment's operation: its target op its value — its type,
// kept on its statement.
tc_compound_value :: proc(k: ^TC, s: Tree_Id, op_tok: Token_Id, target, value: Tree_Id) -> Type {
    op, _ := compound_assign_op(build_tokens[op_tok].kind)
    t := tc_binary_op(k, s, op, token_span(build_tokens[op_tok]), target, value)
    tc_set_type(k, s, t)
    return t
}

// A slice bound to a string literal or to a constant: a writable view of
// read-only storage (a write through it would fault).
tc_no_literal_slice :: proc(k: ^TC, target: Type, value: Tree_Id, span: Span) {
    if value == 0 || !is_slice_type(target) { return }
    if k.t.tag[tc_unparen(k, value)] == .String {
        tc_error(k, span, TYPE_SLICE_CANNOT_BIND_STRING_LITERAL)
    } else if name, is_const := tc_write_root_const(k, value); is_const {
        tc_error(k, span, TYPE_SLICE_CANNOT_BIND_CONSTANT, name, name)
    }
}

// A value declared as a fixed array: its elements' type, and no more of
// them than it holds (a shorter one leaves the rest zero; text counts its
// bytes, not its tier). A literal's items are made as the array's; any
// other value's are copied as they are, so they're laid out alike
// (item_layout_mismatch: a `[2!][64]utf8` is no `[2!][]utf8`).
tc_array_assign :: proc(k: ^TC, span: Span, name: string, fa: ^Type_Fixed_Array, vt: Type, value: Tree_Id) {
    #partial switch k.t.tag[tc_unparen(k, value)] {
    case .Array, .Literal, .Broadcast, .String:
    case:
        if v, is_buffer := vt.(^Type_Fixed_Array); is_buffer && item_layout_mismatch(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
            return
        }
        if v, is_buffer := vt.(^Type_Partial_Array); is_buffer && item_layout_mismatch(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
            return
        }
    }
    #partial switch v in vt {
    case ^Type_Fixed_Array:
        if types_incompatible(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
        } else if v.size > 0 && v.size > fa.size {
            tc_error(k, span, TYPE_ARRAY_ELEMENTS_CAPACITY, v.size, name, fa.size)
        }
    case ^Type_Partial_Array:
        size := v.size
        if m := tc_unparen(k, value); k.t.tag[m] == .String { size = len(tc_text(k.t.main[m])) }
        if types_incompatible(fa, v) {   // (a list, not text: types_compatible's)
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
        } else if types_incompatible(fa.elem, v.elem) {
            tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa))
        } else if size > 0 && size > fa.size {
            tc_error(k, span, TYPE_ARRAY_ELEMENTS_CAPACITY, size, name, fa.size)
        }
    case:
        if !is_any(vt) { tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(fa)) }
    }
}

// `p^ = v`: what p points at, at its type.
tc_deref_assign :: proc(k: ^TC, s, target, value: Tree_Id, op_tok: Token_Id = 0) {
    tr := k.t
    span := tree_span(tr, s)
    diag := value if op_tok == 0 else 0
    of := Tree_Id(tr.a[target])
    pt := tc_check(k, of)
    // (A `^` no one wrote — `next(&l) = v`, `out = v`: tp_through.)
    unwritten := tr.b[target] == 0
    _, gives_ptr := distinct_base(pt).(^Type_Ptr)
    if !unwritten || gives_ptr || is_any(pt) {
        // (What it points at types the value, as a field's type does: `p^ = {0}`.)
        k.hint = nil
        if p, is_ptr := distinct_base(pt).(^Type_Ptr); is_ptr { k.hint = p.elem }
        vt := tc_store_at(k, value, op_tok, target, s)
        if p, is_ptr := distinct_base(pt).(^Type_Ptr); is_ptr {
            tc_set_type(k, target, p.elem)
            if types_incompatible(p.elem, vt) {
                if unwritten && tr.tag[of] == .Ident && !types_incompatible(pt, vt) {
                    name := tc_name(k, of)
                    tc_error(k, span, TYPE_PARAM_POINTS_ELSEWHERE, name, name, type_name(p.elem), type_name(vt))
                } else {
                    tc_error(k, span, TYPE_CANNOT_ASSIGN_THROUGH_POINTER, type_name(vt), type_name(p.elem))
                }
            }
            tc_value_at(k, diag, vt, p.elem, span)
        } else if !is_any(pt) {
            tc_error(k, span, TYPE_CANNOT_DEREFERENCE_ASSIGN_NON_POINTER, type_name(pt))
        }
        return
    }
    // (A call giving no pointer, written to: a value gone after the line.)
    tc_check(k, value)
    tc_error(k, span, TYPE_ASSIGN_TO_RESULT)
}

// A block's statements with each `#if` whose condition is known replaced by
// its live arm's (an elif in its chain is an ordinary if).
tc_live :: proc(k: ^TC, stmts: []Tree_Id) -> []Tree_Id {
    t := k.t
    folds := false
    for s in stmts {
        if t.tag[s] == .If && if_view(t, s).hash != 0 || t.tag[s] == .Expose { folds = true; break }
    }
    if !folds { return stmts }
    out := make([dynamic]Tree_Id, 0, len(stmts), context.temp_allocator)
    for s in stmts {
        // (`#expose`: the definition it marks — a DLL's entry.)
        if t.tag[s] == .Expose {
            inner := Tree_Id(t.a[s])
            k.exposed[inner] = true
            append(&out, inner)
            continue
        }
        if t.tag[s] != .If || if_view(t, s).hash == 0 {
            append(&out, s)
            continue
        }
        v := if_view(t, s)
        live, known := tc_comptime_bool(k, v.cond)
        if !known {
            append(&out, s)   // (left for the check to report)
            continue
        }
        append(&out, ..tc_live(k, v.then if live else v.else_))
    }
    return out[:]
}

// A condition known when the program is compiled: a bool, the target (#web,
// #native, #windows, #linux, #mac), `not` of one.
tc_comptime_bool :: proc(k: ^TC, n: Tree_Id) -> (bool, bool) {
    t := k.t
    m := tc_unparen(k, n)
    #partial switch t.tag[m] {
    case .True:  return true, true
    case .False: return false, true
    case .Hash_Name:
        switch tc_text(Token_Id(t.a[m])) {
        case "web":     return k.c.target_web, true
        case "native":  return !k.c.target_web, true
        case "windows": return k.c.target_os == .Windows, true
        case "linux":   return k.c.target_os == .Linux, true
        case "mac":     return k.c.target_os == .Mac, true
        case "profile_memory": return k.c.profile_memory, true
        }
    case .Unary:
        if build_tokens[t.main[m]].kind == .Not {
            v, ok := tc_comptime_bool(k, Tree_Id(t.a[m]))
            if ok { return !v, true }
        }
    }
    return false, false
}

// `void`, written as a value.
tc_is_void :: proc(k: ^TC, n: Tree_Id) -> bool {
    return k.t.tag[n] == .Ident && tc_name(k, n) == "void"
}

tc_is_pointer :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(^Type_Ptr)
    return ok
}

// `x : T = void`: declared uninitialized (no construction, no stores) —
// the value where it is written void. Unannotated, there is no type.
tc_decl_void :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type) {
    span := tree_span(k.t, s)
    ref := tc_decl_ref(k, target)
    if is_any(ann) {
        if _, shadowed := tc_declared_before(k, ref); !shadowed {
            tc_error(k, span, TYPE_VOID_INIT_REQUIRES_EXPLICIT, name, name)
            tc_bind(k, name, Type_Error{}, ref)
        }
        return
    }
    tc_bind(k, name, ann, ref)
    tc_set_type(k, target, ann)
    tc_note_decl(k, name, ann, span, false)
}

// A declaration of a block, for its size guard.
TC_Decl_Note :: struct {
    name: string,
    t:    Type,
    span: Span,
    take: bool,   // (a take binds memory it takes: no storage of its own)
}

tc_note_decl :: proc(k: ^TC, name: string, t: Type, span: Span, take: bool) {
    if k.decls != nil { append(k.decls, TC_Decl_Note{name, distinct_base(t), span, take}) }
}

// A value too big for the stack, with no scope arena to hold it: an error
// Analysis alone runs no code.
tc_storage_sizes :: proc(k: ^TC, decls: []TC_Decl_Note) {
    if k.c.analysis_only || k.table.has_scope_allocator || k.table.context_expected_at_runtime { return }
    for d in decls {
        if !d.take && routes_to_arena(d.t) {
            tc_error(k, d.span, TYPE_VALUE_TOO_LARGE_STACK_BYTES, d.name, type_size(d.t))
        }
    }
}

// `match x { .A {…}  B b {…}  v {…}  else {…} }`: the subject a union, an
// enum or an err; each arm's variant one it has (a union's payload bound
// where an arm names it); every variant covered, unless an else says
// otherwise.
tc_match :: proc(k: ^TC, s: Tree_Id) {
    tr := k.t
    span := tree_span(tr, s)
    subj := Tree_Id(tr.a[s])
    arms := tree_list(tr, tr.b[s])
    if subj == 0 { return }
    st := tc_check(k, subj)
    // (A named union — `type U`, `distinct U` — matched as U is.)
    sb := distinct_base(st)
    ut, is_union := sb.(^Type_Union)
    et, is_enum := sb.(^Type_Enum)
    _, is_err := sb.(Type_Err)
    if !is_union && !is_enum && !is_err {
        tc_error(k, span, TYPE_MATCH_REQUIRES_UNION, type_name(st))
        return
    }
    has_else := false
    for arm in arms { if tr.tag[arm] == .Arm_Else { has_else = true } }
    if is_err && !has_else { tc_error(k, span, TYPE_MATCH_ERR_REQUIRES_ELSE) }
    for arm, i in arms {
        if tr.tag[arm] == .Arm_Else && i != len(arms) - 1 { tc_error(k, span, TYPE_LAST_ARM_MATCH) }
    }
    covered := make(map[string]bool, context.temp_allocator)
    for arm in arms {
        a := tc_match_arm(k, subj, arm, et, ut)
        name := a.variant
        tc_match_arm_ref(k, arm, a, st)
        #partial switch tr.tag[arm] {
        case .Arm_Dot:
            switch {
            case is_enum:
                if name not_in et.variants { tc_error(k, span, TYPE_ENUM_VARIANT, type_name(et), name) }
            case is_union:
                if name not_in ut.tag_map { tc_error(k, span, TYPE_UNION_VARIANT, type_name(ut), name) }
            case:
                tc_error(k, span, TYPE_DOT_SHORTHAND_ONLY_USED_MATCHING, name)
            }
        case .Arm_Variant:
            if is_union && name not_in ut.tag_map { tc_error(k, span, TYPE_VARIANT_UNION, name, type_name(ut)) }
            // (An err's: an error set's variant, by kind — one set's, else
            // said which: `Parse_Error.Lost`.)
            if is_err && name != "Ok" {
                if _, sets := err_variant_named(k.table, name); len(sets) == 0 {
                    tc_error(k, span, TYPE_ERR_ARM_NO_VARIANT, name)
                } else if len(sets) > 1 {
                    tc_error(k, span, TYPE_ERR_ARM_AMBIGUOUS, name, strings.join(sets, " and ", context.temp_allocator), sets[0], name)
                }
            }
            if is_union {
                if vs := ut.variant_structs[name]; vs != nil && a.bound != "" {
                    // (A rebound subject: its meaning back after the arm.)
                    was, had := tc_bound(k, a.bound_tok)
                    defer tc_bound_restore(k, a.bound_tok, was, had)
                    tc_bind(k, a.bound, vs, {a.bound_tok, .Local})
                    tc_scope(k, a.body)
                    if name != "" { covered[name] = true }
                    continue
                }
            }
        case .Arm_Value:
            if name == "" {
                tc_check(k, a.value)
                if tr.tag[a.value] == .Field { covered[tc_text(Token_Id(tr.b[a.value]))] = true }
            }
        }
        if name != "" { covered[name] = true }
        tc_scope(k, a.body)
    }
    // (Every variant covered, unless an else says otherwise.)
    if has_else || !(is_enum || is_union) { return }
    if is_enum {
        for name in et.variants {
            if name not_in covered { tc_error(k, span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, type_name(et), name) }
        }
    } else {
        for name in ut.variants {
            if name not_in covered { tc_error(k, span, TYPE_MATCH_MISSING_VARIANT_ADD_ARM, type_name(ut), name) }
        }
    }
}

// What a match's arm names, as a name elsewhere says it: its variant. An `err`'s, by
// kind: the variant of the one set that has it (more's an error, said by the arm).
tc_match_arm_ref :: proc(k: ^TC, arm: Tree_Id, a: Match_Arm, subject: Type) {
    if a.variant == "" { return }
    decl := variant_decl(subject, a.variant)
    if _, is_err := distinct_base(subject).(Type_Err); is_err {
        for _, e in k.table.enums {
            if !e.is_error_kind { continue }
            if d := e.variant_decls[a.variant] or_else 0; d != 0 {
                decl = d
                break
            }
        }
    }
    if decl == 0 { return }
    // (A value arm's value is the name; the others' is the arm's own.)
    tc_set_ref(k, a.value if k.t.tag[arm] == .Arm_Value else arm, {decl, .Variant})
}

// A match arm, as written against a subject of enum `et` or union `ut` (nil:
// neither) — the checker and lowering each read it here: the variant it names
// ("": none — an else, a value no variant is), its body, a value arm's value,
// and the name its payload is bound to with the token declaring it (a variant
// arm's own; with none, a bare subject's name sees the payload).
Match_Arm :: struct {
    variant:   string,
    body:      []Tree_Id,
    value:     Tree_Id,
    bound:     string,
    bound_tok: Token_Id,
}

tc_match_arm :: proc(k: ^TC, subj, arm: Tree_Id, et: ^Type_Enum, ut: ^Type_Union) -> (a: Match_Arm) {
    t := k.t
    #partial switch t.tag[arm] {
    case .Arm_Dot:
        a.variant, a.body = tc_text(t.main[arm]), tree_list(t, t.a[arm])
    case .Arm_Variant:
        a.variant, a.body = tc_text(t.main[arm]), tree_list(t, t.a[arm])
        if bt := Token_Id(t.b[arm]); bt != 0 {
            a.bound, a.bound_tok = tc_text(bt), bt
        } else if su := tc_unparen(k, subj); t.tag[su] == .Ident {
            a.bound, a.bound_tok = tc_name(k, su), t.main[su]
        }
    case .Arm_Else:
        a.body = tree_list(t, t.a[arm])
    case .Arm_Value:
        a.value, a.body = Tree_Id(t.a[arm]), tree_list(t, t.b[arm])
        if t.tag[a.value] == .Ident {
            name := tc_name(k, a.value)
            if et != nil && name in et.variants || ut != nil && name in ut.tag_map { a.variant = name }
        }
    }
    return
}

// A struct's field initializer handing `#self` to anything — a call, an
// expression — while field declarations follow it: what it reads may not be
// written yet: a warning.
tc_early_self :: proc(k: ^TC, body: []Tree_Id) {
    t := k.t
    stmts := tc_live(k, body)
    decl_after := make([]bool, len(stmts), context.temp_allocator)
    seen := false
    for i := len(stmts) - 1; i >= 0; i -= 1 {
        decl_after[i] = seen
        if t.tag[stmts[i]] == .Decl || t.tag[stmts[i]] == .Using { seen = true }
    }
    for s, i in stmts {
        if t.tag[s] != .Decl || !decl_after[i] { continue }
        v := decl_view(t, s)
        for value in v.values {
            if name, found := tc_self_call(k, value); found {
                check_warning(k.c, tree_span(t, s), TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS, name)
                break
            }
            if tc_has_self(k, value) {
                names := make([dynamic]string, context.temp_allocator)
                for tg in v.targets { append(&names, tc_name(k, tg)) }
                check_warning(k.c, tree_span(t, s), TYPE_MOVE_BELOW_ALL_DECLARATIONS_CLASS, strings.join(names[:], ", ", context.temp_allocator))
                break
            }
        }
    }
}

// The call an expression hands `#self` to, by name — the innermost.
tc_self_call :: proc(k: ^TC, n: Tree_Id) -> (string, bool) {
    if n == 0 { return "", false }
    t := k.t
    #partial switch t.tag[n] {
    case .Call, .Method_Call:
        args := tree_list(t, t.a[n]) if t.tag[n] == .Call else method_view(t, n).args
        for a in args {
            if name, found := tc_self_call(k, a); found { return name, true }
        }
        for a in args {
            if tc_is_self(k, a) { return tc_call_name(k, n), true }
        }
    case .Binary:
        if name, found := tc_self_call(k, Tree_Id(t.a[n])); found { return name, true }
        return tc_self_call(k, Tree_Id(t.b[n]))
    case .Unary, .Deref, .Paren, .Field, .Broadcast, .Take:
        sub := Tree_Id(t.b[n]) if t.tag[n] == .Take else Tree_Id(t.a[n])
        return tc_self_call(k, sub)
    case .Index:
        if name, found := tc_self_call(k, Tree_Id(t.a[n])); found { return name, true }
        return tc_self_call(k, Tree_Id(t.b[n]))
    case .Slice:
        lo, hi := tree_pair(t, n)
        for p in ([3]Tree_Id{Tree_Id(t.a[n]), lo, hi}) {
            if name, found := tc_self_call(k, p); found { return name, true }
        }
    case .Literal:
        for e in tree_list(t, t.b[n]) {
            if name, found := tc_self_call(k, Tree_Id(t.a[e]) if t.tag[e] == .Named_Entry else e); found { return name, true }
        }
    case .Array:
        for e in tree_list(t, t.a[n]) {
            if name, found := tc_self_call(k, e); found { return name, true }
        }
    case .If_Expr:
        then_, else_ := tree_pair(t, n)
        if name, found := tc_self_call(k, then_); found { return name, true }
        return tc_self_call(k, else_)
    }
    return "", false
}

// Whether `#self` is anywhere in an expression.
tc_has_self :: proc(k: ^TC, n: Tree_Id) -> bool {
    if n == 0 { return false }
    t := k.t
    #partial switch t.tag[n] {
    case .Self: return true
    case .Call, .Method_Call:
        args := tree_list(t, t.a[n]) if t.tag[n] == .Call else method_view(t, n).args
        for a in args { if tc_has_self(k, a) { return true } }
    case .Binary, .Index:
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, Tree_Id(t.b[n]))
    case .Unary, .Deref, .Paren, .Field, .Broadcast:
        return tc_has_self(k, Tree_Id(t.a[n]))
    case .Take:
        return tc_has_self(k, Tree_Id(t.b[n]))
    case .Slice:
        lo, hi := tree_pair(t, n)
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, lo) || tc_has_self(k, hi)
    case .Literal:
        for e in tree_list(t, t.b[n]) {
            if tc_has_self(k, Tree_Id(t.a[e]) if t.tag[e] == .Named_Entry else e) { return true }
        }
    case .Array:
        for e in tree_list(t, t.a[n]) { if tc_has_self(k, e) { return true } }
    case .If_Expr:
        then_, else_ := tree_pair(t, n)
        return tc_has_self(k, Tree_Id(t.a[n])) || tc_has_self(k, then_) || tc_has_self(k, else_)
    }
    return false
}

// The shape shortcut: `h : Holder(Box(5))`, a shape's argument a
// constructor's call, means `h : Holder(Box) = {inner = Box(5)}` — each field
// of the shape's type given that call. Its bindings (none: no shortcut).
TC_Binding :: struct {
    field: string,
    call:  Tree_Id,
}

tc_shape_bindings :: proc(k: ^TC, ann: Tree_Id) -> []TC_Binding {
    t := k.t
    if ann == 0 || t.tag[ann] != .Type_Generic { return nil }
    tmpl, is_template := tc_template(k, k.rs.refs[ann])
    if !is_template || t.tag[tmpl.node] != .Struct_Def { return nil }
    gps, _ := tc_struct_generics(k, tmpl.node)
    out := make([dynamic]TC_Binding, context.temp_allocator)
    for a, i in tree_list(t, t.a[ann]) {
        if i >= len(gps) || gps[i].shape == 0 { continue }
        call := tc_unparen(k, a)
        if !tc_is_call(k, call) { continue }
        for s in scope_view(t, tmpl.node).body {
            if t.tag[s] != .Decl { continue }
            v := decl_view(t, s)
            if v.type_ == 0 || t.tag[v.type_] != .Type_Name || k.rs.refs[v.type_].decl != gps[i].decl { continue }
            for tg in v.targets { append(&out, TC_Binding{tc_name(k, tg), call}) }
        }
    }
    return out[:]
}

// A declaration by the shape shortcut: its struct's literal, each field the
// shape's call.
tc_decl_shape :: proc(k: ^TC, s, target: Tree_Id, name: string, ann: Type, bindings: []TC_Binding) {
    span := tree_span(k.t, s)
    ref := tc_decl_ref(k, target)
    // (Its literal built from the shape: no constructor run, as a bare
    // declaration runs none.)
    k.hint = ann
    tc_shape_literal(k, s, ann, bindings)
    tc_bind(k, name, ann, ref)
    tc_set_type(k, target, ann)
    tc_note_decl(k, name, ann, span, false)
}

// `{inner = Box(5)}` of the shape shortcut, at its type.
tc_shape_literal :: proc(k: ^TC, s: Tree_Id, t: Type, bindings: []TC_Binding) {
    span := tree_span(k.t, s)
    ts, is_scope := t.(^Type_Scope)
    if !is_scope || ts.kind != .Struct {
        tc_unsupported(k, s, "a shape's shortcut of no struct")
        return
    }
    tc_struct_ensure(k, ts)
    sd := &ts.sd
    tc_ctor_args(k, ts, span)
    for bd in bindings {
        idx, has := sd.field_map[bd.field]
        if !has { continue }
        tc_literal_field(k, bd.call, sd.fields[idx], 0, bd.field, span)
    }
}

