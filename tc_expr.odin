package mara

import "core:fmt"
import "core:strings"

// Expressions, checked and built in the order they run: each returns its type
// and what it built (tc_expr). `want` is what its use asks of it — its value,
// its place, either, or to be built into `dest`.

tc_expr :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want := Fuse_Want.Value, w := Written.Explicit,
                dest := Dest{}, temp := false, temp_span := Span{}) -> (Type, Fused) {
    if n == 0 { return Type_Error{}, {} }
    b := tc_building(k)
    ask := want if b != nil else .None
    t, r := tc_expr_impl(k, n, env, ask, w, dest, temp, temp_span)
    tc_set_type(k, n, t)
    if ask != .None && !r.ok { tc_fail(k, fmt.aprintf("%v", k.t.tag[n])) }
    return t, r
}

// Check without building.
tc_check :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    t, _ := tc_expr(k, n, env, .None)
    return t
}

tc_expr_impl :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                     dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    t := k.t
    span := tree_span(t, n)
    b := tc_building(k)
    #partial switch t.tag[n] {
    case .Number:
        return tc_number(k, n, span, false, want, w)
    case .String:
        text := token_text(build_tokens[t.main[n]])
        pa := new(Type_Partial_Array)
        pa.size = string_literal_cap(len(text))
        pa.elem = Type_Utf8{}
        if want == .None { return pa, {} }
        g := graph_text(b, graph_op_value(b, .Global, w, span, pa), Const_Value{text = text, is_text = true})
        return pa, {v = g, place = want == .Place, ok = true}
    case .Char:
        text := token_text(build_tokens[t.main[n]])
        if want == .None { return Type_Utf8{}, {} }
        if want == .Place { return Type_Utf8{}, {} }
        v := graph_const(b, w, span, Type_Utf8{}, "", Const_Value{int = i128(text[0]) if len(text) > 0 else 0})
        return Type_Utf8{}, {v = v, ok = true}
    case .True, .False:
        if want == .None || want == .Place { return Type_Bool{}, {} }
        v := graph_const(b, w, span, Type_Bool{}, "", Const_Value{int = 1 if t.tag[n] == .True else 0})
        return Type_Bool{}, {v = v, ok = true}
    case .Paren:
        return tc_expr(k, Tree_Id(t.a[n]), env, want, w, dest, temp, temp_span)
    case .Ident:
        return tc_ident(k, n, env, want, w)
    case .Unary:
        return tc_unary(k, n, env, want, w)
    case .Deref:
        return tc_deref(k, n, env, want, w)
    case .Binary:
        return tc_binary(k, n, env, want, w)
    case .Call:
        return tc_call(k, n, env, want, w, dest, temp, temp_span)
    }
    tc_unsupported(k, n, "this expression")
    return Type_Error{}, {}
}

// A number, its value from its token (negated: `-3`, reported at the `-`).
tc_number :: proc(k: ^TC, n: Tree_Id, span: Span, negate: bool, want: Fuse_Want, w: Written) -> (Type, Fused) {
    text := token_text(build_tokens[k.t.main[n]])
    f, i, _ := parse_number_text(text)
    is_float := strings.index_byte(text, '.') >= 0
    if negate { f, i = -f, -i }
    t: Type = Type_Infer_Float{} if is_float else Type_Infer_Int{}
    if want == .None || want == .Place { return t, {} }
    b := tc_building(k)
    v := graph_const(b, w, span, t, "", Const_Value{int = i, float = f, is_float = is_float})
    return t, {v = v, ok = true}
}

tc_ident :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    name := tc_name(k, n)
    span := tree_span(k.t, n)
    k.hint = nil
    t, loc_scope, ok := type_env_locate(env, name)
    if !ok {
        tc_error(k, span, TYPE_UNDEFINED_IDENTIFIER, name)
        return Type_Error{}, {}
    }
    _ = loc_scope
    b := tc_building(k)
    if name == "void" {
        if want == .None || want == .Place { return t, {} }
        return t, {v = graph_op_value(b, .Const, w, span, t, "void"), ok = true}
    }
    if _, is_scope := t.(^Type_Scope); is_scope {
        tc_unsupported(k, n, "a function or type as a value")
        return t, {}
    }
    if want == .None { return t, {} }
    place := graph_var(b, name, NO_NODE, t, span)
    if want == .Value { return t, {v = graph_read(b, place, t, span), ok = true} }
    return t, {v = place, place = true, ok = true}
}

tc_unary :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    op := build_tokens[tr.main[n]].kind
    operand := Tree_Id(tr.a[n])
    if op == .Minus && tr.tag[operand] == .Number {
        t, r := tc_number(k, operand, span, true, want, w)
        tc_set_type(k, operand, t)
        return t, r
    }
    if want == .Place { tc_fail(k, "a unary's place") }
    wrapping := op == .Wrap_Minus
    either := op == .Minus
    ask: Fuse_Want = .Place if op == .Ampersand else .Either if either else .Value
    if want == .None || want == .Place { ask = .None }
    ot, r := tc_expr(k, operand, env, ask, w, temp_span = span)
    t: Type
    #partial switch op {
    case .Minus, .Wrap_Minus:
        t = ot
        if wrapping {
            if !is_wrap_operand(ot) {
                tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER_UNARY, type_name(ot))
                return Type_Error{}, {}
            }
        } else if !is_numeric(ot) {
            tc_error(k, span, TYPE_CANNOT_NEGATE, type_name(ot))
        } else if _, kind, k_ok := numeric_info(ot); k_ok && kind == .Unsigned {
            tc_error(k, span, TYPE_CANNOT_NEGATE_UNSIGNED, type_name(ot))
        }
    case .Not:
        if _, is_bool := ot.(Type_Bool); !is_bool && !is_any(ot) { tc_error(k, span, TYPE_CANNOT_APPLY, type_name(ot)) }
        t = Type_Bool{}
    case .Tilde:
        if !is_integer(ot) && !is_any(ot) { tc_error(k, span, TYPE_CANNOT_APPLY_REQUIRES_INTEGER_TYPE, type_name(ot)) }
        t = ot
    case .Ampersand:
        if tr.tag[operand] == .String { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL) }
        pt := new(Type_Ptr)
        pt.elem = ot
        t = pt
    case:
        tc_unsupported(k, n, "this unary operator")
        return Type_Error{}, {}
    }
    b := tc_building(k)
    if want == .None || want == .Place || b == nil { return t, {} }
    if op == .Ampersand {
        return t, {v = graph_op_value(b, .Address, w, span, t, "", r.v), ok = true}
    }
    v := r.v
    if either { v = tc_value(k, r, operand, ot) }
    word := "-%" if wrapping else graph_token_text(.Minus if op == .Minus else op)
    return t, {v = graph_op_value(b, .Unary, w, span, t, word, v), ok = true}
}

tc_deref :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    span := tree_span(k.t, n)
    ask := Fuse_Want.Place if want != .None else .None
    ot, r := tc_expr(k, Tree_Id(k.t.a[n]), env, ask, w, temp_span = span)
    t: Type = Type_Error{}
    if p, ok := ot.(^Type_Ptr); ok {
        t = p.elem
    } else if !is_any(ot) {
        tc_error(k, span, TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE, type_name(ot))
    }
    b := tc_building(k)
    if want == .None || b == nil { return t, {} }
    p := graph_op_value(b, .Deref, .Explicit, span, t, "", r.v)
    if want == .Value { return t, {v = graph_read(b, p, t, span), ok = true} }
    return t, {v = p, place = true, ok = true}
}

// A built expression's value: a place is read, right after it.
tc_value :: proc(k: ^TC, r: Fused, n: Tree_Id, t: Type) -> Operand {
    b := tc_building(k)
    if b == nil || !r.place { return r.v }
    return graph_read(b, r.v, t, tree_span(k.t, n))
}

// A binary operation: each side at the type the operation works in; `and` /
// `or` short-circuit.
tc_binary :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    tok := build_tokens[tr.main[n]].kind
    op := tok
    wrapping := false
    #partial switch tok {
    case .Wrap_Plus:  op, wrapping = .Plus, true
    case .Wrap_Minus: op, wrapping = .Minus, true
    case .Wrap_Star:  op, wrapping = .Star, true
    }
    b := tc_building(k)
    build := want != .None && b != nil
    if want == .Place {
        tc_fail(k, "a binary's place")
        build = false
    }
    left, right := Tree_Id(tr.a[n]), Tree_Id(tr.b[n])
    hint := k.hint
    sides: [2]Operand
    widen := [2]int{-1, -1}
    types: [2]Type
    and_or := op == .And || op == .Or
    sa: Graph_And
    if build && and_or { sa = graph_fuse_and(b, op == .And, w, span) }
    for side, i in ([2]Tree_Id{left, right}) {
        k.hint = hint
        if !build {
            types[i] = tc_check(k, side, env)
            continue
        }
        if and_or {
            st, r := tc_expr(k, side, env, .Value, w)
            types[i] = st
            if b = tc_building(k); b == nil { build = false; continue }
            sides[i] = r.v
            if i == 0 { graph_fuse_and_left(b, &sa, r.v) }
            continue
        }
        st, r := tc_expr(k, side, env, .Either, w)
        types[i] = st
        if b = tc_building(k); b == nil { build = false; continue }
        sides[i], widen[i] = graph_fuse_as(b, r.v, r.place, st, tree_span(tr, side), span, {})
    }
    lt, rt := types[0], types[1]
    t: Type = Type_Error{}
    if wrapping && (!is_wrap_operand(lt) || !is_wrap_operand(rt)) {
        tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER, op_str(op), type_name(lt), type_name(rt))
        return Type_Error{}, {}
    }
    #partial switch op {
    case .And, .Or:
        word := "and" if op == .And else "or"
        if _, ok := lt.(Type_Bool); !ok && !is_any(lt) { tc_error(k, span, TYPE_LEFT_OPERAND_BOOL, word, type_name(lt)) }
        if _, ok := rt.(Type_Bool); !ok && !is_any(rt) { tc_error(k, span, TYPE_RIGHT_OPERAND_BOOL, word, type_name(rt)) }
        t = Type_Bool{}
    case .Equal_Equal, .Not_Equal:
        if !is_any(lt) && !is_any(rt) {
            if is_composite(lt) || is_composite(rt) {
                tc_error(k, span, TYPE_CANNOT_COMPARE_USING, type_name(lt), type_name(rt), "==" if op == .Equal_Equal else "!=")
            }
            if is_numeric(lt) && is_numeric(rt) { promote_numeric(k.c, lt, rt, span) }
        }
        t = Type_Bool{}
    case .Less, .Less_Equal, .Greater, .Greater_Equal:
        if !is_numeric(lt) { tc_error(k, span, TYPE_LEFT_OPERAND_COMPARISON_NUMERIC, type_name(lt)) }
        if !is_numeric(rt) { tc_error(k, span, TYPE_RIGHT_OPERAND_COMPARISON_NUMERIC, type_name(rt)) }
        if is_numeric(lt) && is_numeric(rt) { promote_numeric(k.c, lt, rt, span) }
        t = Type_Bool{}
    case .Plus:
        if !is_numeric(lt) || !is_numeric(rt) {
            tc_error(k, span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT, type_name(lt), type_name(rt))
            return Type_Error{}, {}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case .Minus, .Star, .Slash, .Modulo:
        if !is_numeric(lt) || !is_numeric(rt) {
            sym := "-" if op == .Minus else "*" if op == .Star else "/" if op == .Slash else "%%"
            tc_error(k, span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2, sym, type_name(lt), type_name(rt))
            return Type_Error{}, {}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(lt) && !is_any(lt) {
            tc_error(k, span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(lt))
            return Type_Error{}, {}
        }
        if !is_integer(rt) && !is_any(rt) {
            tc_error(k, span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(rt))
            return Type_Error{}, {}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case:
        tc_unsupported(k, n, "this operator")
        return Type_Error{}, {}
    }
    if !build { return t, {} }
    if b = tc_building(k); b == nil { return t, {} }
    if and_or {
        if _, is_bool := t.(Type_Bool); !is_bool {
            tc_fail(k, "and / or of no bool")
            return t, {}
        }
        return t, {v = graph_fuse_and_end(b, &sa, sides[1]), ok = true}
    }
    work := Graph_Work{op, t, lt, rt}
    for wi in widen {
        if wi >= 0 { b.fuse.widens[wi].work, b.fuse.widens[wi].binary, b.fuse.widens[wi].views = work, true, false }
    }
    kind: Op_Kind = .Compare if is_comparison_op(op) else .Arith
    word := graph_token_text(op)
    if wrapping { word = strings.concatenate({word, "%"}) }
    return t, {v = graph_op_value(b, kind, w, span, t, word, sides[0], sides[1]), ok = true}
}

// --- calls --------------------------------------------------------------------

// A call being built: its operands, each at its param's type (a builtin's as
// they are).
TC_Call :: struct {
    ops:  [dynamic]Operand,
    args: [dynamic]Fused,
    types: [dynamic]Type,
}

tc_call :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    name := tc_name(k, n)
    args := tree_list(tr, tr.a[n])
    if tr.b[n] != 0 { tc_unsupported(k, n, "an override block") }
    build := want != .None && tc_building(k) != nil
    if want == .Place {
        tc_unsupported(k, n, "a call's place")
        build = false
    }
    switch name {
    case "print", "crash":
        fc: TC_Call
        defer { delete(fc.args); delete(fc.types) }
        for a in args {
            at, r := tc_expr(k, a, env, .Value if build else .None, w, temp_span = span)
            append(&fc.args, r)
            append(&fc.types, at)
        }
        if build {
            if b := tc_building(k); b != nil {
                vals := make([]Operand, len(fc.args), context.temp_allocator)
                for r, i in fc.args { vals[i] = r.v }
                graph_op(b, .Crash if name == "crash" else .Print, w, span, nil, name, ..vals)
                return nil, {v = NO_VALUE, ok = true}
            }
        }
        return nil, {}
    }
    ft_raw, found := type_env_get(env, name)
    if !found {
        tc_error(k, span, TYPE_UNDEFINED_FUNCTION, name)
        for a in args { tc_check(k, a, env) }
        return Type_Error{}, {}
    }
    ft, is_fun := ft_raw.(^Type_Scope)
    if !is_fun || ft.kind != .Fun {
        tc_unsupported(k, n, "a call to no fun")
        return Type_Error{}, {}
    }
    if len(args) != len(ft.params) {
        qualified := name
        if ft.home_package != "" { qualified = strings.concatenate({ft.home_package, ".", name}) }
        tc_error(k, span, TYPE_EXPECTS_ARGS, qualified, len(ft.params), fn_params_desc(ft), len(args))
        for a in args { tc_check(k, a, env) }
        return fn_primary_return(ft), {}
    }
    ops := make([dynamic]Operand, 0, len(args), context.temp_allocator)
    for a, i in args {
        pt := ft.params[i].type_
        k.hint = pt
        at: Type
        if build {
            r: Fused
            at, r = tc_expr(k, a, env, .Either, w)
            if b := tc_building(k); b != nil {
                append(&ops, graph_fuse_widen(b, tc_value(k, r, a, at), span, {sig = ft, param = i}))
            }
        } else {
            at = tc_check(k, a, env)
        }
        if !coerce_deferred(k.c, at, pt, span) && types_incompatible(pt, at) && !value_preserving_widen(at, pt) {
            tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, "", name, ft.params[i].name, type_name(pt), type_name(at))
        }
        if is_infer(at) { tc_literal_overflow(k, a, pt, span) }
    }
    ret := fn_primary_return(ft)
    if !build { return ret, {} }
    b := tc_building(k)
    if b == nil { return ret, {} }
    return ret, {v = {graph_call_op(b, .Call, w, span, ft, ret, ..ops[:]), 0}, ok = true}
}

// A literal that doesn't fit the type it is used at (check_literal_overflow's).
tc_literal_overflow :: proc(k: ^TC, n: Tree_Id, target: Type, span: Span) {
    tr := k.t
    neg := false
    num := n
    if tr.tag[n] == .Unary && build_tokens[tr.main[n]].kind == .Minus && tr.tag[tr.a[n]] == .Number {
        neg, num = true, Tree_Id(tr.a[n])
    }
    if tr.tag[num] != .Number { return }
    text := token_text(build_tokens[tr.main[num]])
    f, i, _ := parse_number_text(text)
    if neg { f, i = -f, -i }
    check_value_range(k.c, f, i, target, span)
}
