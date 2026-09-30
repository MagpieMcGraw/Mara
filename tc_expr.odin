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
    // A compound assignment's target, read in its operation: through the
    // place already built.
    if ask != .None && n == k.compound.target && n != 0 {
        t := tc_check(k, n, env)
        span := tree_span(k.t, n)
        if ask == .Value { return t, {v = graph_read(b, k.compound.place, t, span), ok = true} }
        return t, {v = k.compound.place, place = true, ok = true}
    }
    // What has no place of its own, asked for one: held in a temporary.
    if ask == .Place && tc_holds(k, n) {
        t, p := tc_hold(k, n, env, temp_span if temp_span != {} else tree_span(k.t, n))
        tc_set_type(k, n, t)
        return t, {v = p, place = true, ok = p != NO_VALUE}
    }
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
    case .Assert:
        return tc_assert(k, n, env, want, w)
    case .Field:
        return tc_field(k, n, env, want, w)
    case .Literal:
        return tc_literal(k, n, env, want, w, dest, temp, temp_span)
    case .Index:
        return tc_index(k, n, env, want, w)
    case .Array:
        return tc_array_literal(k, n, env, want, w, dest, temp, temp_span)
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
        // (A type named as a value: said so.)
        flat := resolve_type_name(k.c, name, "", env)
        if flat in k.table.funs || flat in k.table.enums || flat in k.table.unions {
            tc_error(k, span, TYPE_TYPE_VALUE_DID_MEAN, name, name)
        } else {
            report_unresolved(k.c, span, env, name, TYPE_UNDEFINED_IDENTIFIER)
        }
        return Type_Error{}, {}
    }
    b := tc_building(k)
    if name == "void" {
        if want == .None || want == .Place { return t, {} }
        return t, {v = graph_op_value(b, .Const, w, span, t, "void"), ok = true}
    }
    // (A local is found in no scope: what a scope holds is a fun, a type, a
    // constant — a function sees no module's variables.)
    if loc_scope != nil {
        tc_unsupported(k, n, "a name that is no local")
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
    return tc_binary_op(k, build_tokens[tr.main[n]].kind, tree_span(tr, n), Tree_Id(tr.a[n]), Tree_Id(tr.b[n]), env, want, w)
}

// `left op right`, where `span` is: a Binary's, or a compound assignment's
// (`x += v` is `x = x + v`, at the `+=`).
tc_binary_op :: proc(k: ^TC, tok: Token_Kind, span: Span, left, right: Tree_Id, env: ^Type_Scope,
                     want: Fuse_Want, w: Written) -> (Type, Fused) {
    tr := k.t
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
        tc_error(k, span, "tc: the operator %v is not supported yet", tok)
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

// A call; asked for its place, stored in a temporary made first (built there,
// a construction) at the use's span.
tc_call :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    b := tc_building(k)
    if b == nil || want != .Place { return tc_call_impl(k, n, env, want, w, dest, temp, temp_span) }
    at := temp_span if temp_span != {} else tree_span(k.t, n)
    slot := graph_slot(b, "temp", nil, at)
    t, r := tc_call_impl(k, n, env, .Into, w, graph_dest_var("temp", slot, nil), temp, at)
    if b = tc_building(k); b == nil { return t, {} }
    if !r.ok {
        tc_fail(k, "a call's place")
        return t, {}
    }
    if !r.into { graph_fuse_write_at(b, graph_var(b, "temp", slot, nil, at), r.v, at) }
    graph_fuse_typed(b, slot, t)
    return t, {v = graph_var(b, "temp", slot, t, at), place = true, ok = true}
}

tc_call_impl :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written,
                     dest: Dest, temp: bool, temp_span: Span) -> (Type, Fused) {
    tr := k.t
    span := tree_span(tr, n)
    name := tc_name(k, n)
    args := tree_list(tr, tr.a[n])
    build := want != .None && tc_building(k) != nil
    // (A call of several results, as one argument: its extras would be lost.)
    for a in args {
        if returns := tc_call_returns(k, a, env); len(returns) > 1 {
            tc_error(k, tree_span(tr, tc_unparen(k, a)), TYPE_MULTI_RETURN_AS_ARG, len(returns))
        }
    }
    if want == .Place {
        tc_fail(k, "a call's place")
        build = false
    }
    if t, r, is_builtin := tc_builtin(k, n, name, args, env, want if build else .None, w); is_builtin { return t, r }
    ft_raw, found := type_env_get(env, name)
    if !found {
        tc_error(k, span, TYPE_UNDEFINED_FUNCTION, name)
        for a in args { tc_check(k, a, env) }
        return Type_Error{}, {}
    }
    ft, is_scope := ft_raw.(^Type_Scope)
    if !is_scope || ft.is_module || ft.node == 0 {
        tc_unsupported(k, n, "a call of this")
        return Type_Error{}, {}
    }
    if tr.b[n] != 0 { tc_unsupported(k, n, "an override block") }
    is_struct := ft.kind == .Struct
    k.callees[n] = ft
    if is_struct { tc_struct_ensure(k, ft) }
    // (Built into storage that holds a value: a temporary made first.)
    dest := dest
    into_temp := false
    if b := tc_building(k); build && b != nil && is_struct && want == .Into && temp {
        dest = graph_fuse_temp(b, temp_span, fuse_temp_type(dest))
        into_temp = true
    }
    ops := make([dynamic]Operand, 0, len(args), context.temp_allocator)
    if len(args) < count_required_params(ft) || len(args) > len(ft.params) {
        qualified := name
        if ft.home_package != "" { qualified = strings.concatenate({ft.home_package, ".", name}) }
        tc_error(k, span, TYPE_EXPECTS_ARGS, qualified, len(ft.params), fn_params_desc(ft), len(args))
    } else if len(args) < len(ft.params) {
        tc_unsupported(k, n, "a call leaving params to their defaults")
        return Type_Error{}, {}
    }
    for a, i in args {
        if len(args) > len(ft.params) || len(args) < count_required_params(ft) { break }
        pt := ft.params[i].type_
        k.hint = pt
        at: Type
        if b := tc_building(k); build && b != nil {
            // (A temporary its value may need, before it: an array's a slice
            // param views.)
            use, use_at := tc_use_type(k, a, pt, span)
            held: Graph_Later
            if is_slice_type(pt) { held = graph_fuse_later(b) }
            r: Fused
            at, r = tc_expr(k, a, env, .Either, w, dest = use, temp_span = use_at)
            if tc_building(k) != nil { append(&ops, tc_value_as(k, a, at, r, pt, span, {sig = ft, param = i}, &held)) }
        } else {
            at = tc_check(k, a, env)
        }
        if !coerce_deferred(k.c, at, pt, span) && types_incompatible(pt, at) && !value_preserving_widen(at, pt) {
            clause := ""
            if an := tc_diag_name(k, a); an != "" { clause = fmt.tprintf(" ('%s')", an) }
            tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, clause, name, ft.params[i].name, type_name(pt), type_name(at))
        }
        if is_infer(at) { tc_literal_overflow(k, a, pt, span) }
    }
    if is_struct {
        if !build || tc_building(k) == nil { return ft, {} }
        if into_temp {
            return ft, tc_construct(k, n, ft, ops[:], .Into, w, dest, true, temp_span, made = true)
        }
        return ft, tc_construct(k, n, ft, ops[:], want, w, dest, false, temp_span)
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
    num := tc_unparen(k, n)
    if tr.tag[num] == .Unary && build_tokens[tr.main[num]].kind == .Minus && tr.tag[tc_unparen(k, Tree_Id(tr.a[num]))] == .Number {
        neg, num = true, tc_unparen(k, Tree_Id(tr.a[num]))
    }
    if tr.tag[num] != .Number { return }
    text := token_text(build_tokens[tr.main[num]])
    f, i, _ := parse_number_text(text)
    if neg { f, i = -f, -i }
    check_value_range(k.c, f, i, target, span)
}

// `assert(c)`: the condition's value, then the assert — with the
// condition's text, and a comparison's sides' (a literal's left out: its
// text is its value).
tc_assert :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, want: Fuse_Want, w: Written) -> (Type, Fused) {
    t := k.t
    span := tree_span(t, n)
    cond := Tree_Id(t.a[n])
    if want != .None && want != .Value { tc_fail(k, "an assert's place") }
    ct, r := tc_expr(k, cond, env, .Value if want == .Value else .None, w)
    if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL, type_name(ct)) }
    b := tc_building(k)
    if b == nil || want != .Value { return Type_Void{}, {} }
    lo, hi := int(t.first[cond]), int(t.end[cond])
    sides: Maybe([2]string)
    if bin := tc_unparen(k, cond); t.tag[bin] == .Binary && is_comparison_op(build_tokens[t.main[bin]].kind) {
        // (Split at the last operator of its kind outside any brackets.)
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
    graph_assert(b, span, token_range_text(lo, hi), r.v, w, sides)
    return Type_Void{}, {v = NO_VALUE, ok = true}
}

// An expression without the parens around it.
tc_unparen :: proc(k: ^TC, n: Tree_Id) -> Tree_Id {
    n := n
    for k.t.tag[n] == .Paren { n = Tree_Id(k.t.a[n]) }
    return n
}

// Whether an expression's text states its value: a number, a bool, a char,
// a negated number.
tc_is_literal :: proc(k: ^TC, n: Tree_Id) -> bool {
    n := tc_unparen(k, n)
    #partial switch k.t.tag[n] {
    case .Number, .True, .False, .Char: return true
    case .Unary:
        return build_tokens[k.t.main[n]].kind == .Minus && k.t.tag[tc_unparen(k, Tree_Id(k.t.a[n]))] == .Number
    }
    return false
}

// An expression with no place of its own: an operation's value, a `?`'s, a
// slice, an assert, a take. (A deref names one.)
tc_holds :: proc(k: ^TC, n: Tree_Id) -> bool {
    #partial switch k.t.tag[n] {
    case .Binary, .Unary, .Try, .Slice, .Assert, .Take: return true
    }
    return false
}

// Its place, when it has none: a temporary made first, the value stored in
// it (built there, what builds in place), its variable the place.
tc_hold :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, span: Span) -> (Type, Operand) {
    b := tc_building(k)
    if b == nil { return tc_check(k, n, env), NO_VALUE }
    slot := graph_slot(b, "temp", nil, span)
    // (Text, or a slice's elements, filling a new partial array: zero first.)
    prefix := graph_fuse_prefix(b, "temp", slot, span)
    d := graph_dest_var("temp", slot, nil)
    t, r := tc_expr(k, n, env, .Into, dest = d, temp_span = span)
    tc_store(k, n, t, r, d, span)
    if b = tc_building(k); b == nil { return t, NO_VALUE }
    graph_fuse_prefix_end(b, prefix, is_partial_array(t) && (k.t.tag[n] == .String || is_slice_type(t)), t)
    graph_fuse_typed(b, slot, t)
    return t, graph_var(b, "temp", slot, t, span)
}

// A builtin: print, crash, a cast. Its args are built as they are, as values.
tc_builtin :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, env: ^Type_Scope,
                   want: Fuse_Want, w: Written) -> (Type, Fused, bool) {
    span := tree_span(k.t, n)
    ask := Fuse_Want.Value if want != .None else .None
    vals := make([dynamic]Operand, 0, len(args), context.temp_allocator)
    types := make([dynamic]Type, 0, len(args), context.temp_allocator)
    each :: proc(k: ^TC, args: []Tree_Id, env: ^Type_Scope, ask: Fuse_Want, w: Written, span: Span,
                 vals: ^[dynamic]Operand, types: ^[dynamic]Type) {
        for a in args {
            t, r := tc_expr(k, a, env, ask, w, temp_span = span)
            append(vals, r.v)
            append(types, t)
        }
    }
    switch name {
    case "print":
        each(k, args, env, ask, w, span, &vals, &types)
        tc_print_format(k, args, span)
        return Type_Error{}, tc_builtin_op(k, .Print, name, vals[:], want, w, span), true
    case "crash":
        if len(args) > 1 {
            tc_error(k, span, TYPE_CRASH_EXPECTS_ARGUMENTS, len(args))
        } else {
            each(k, args, env, ask, w, span, &vals, &types)
        }
        return Type_Error{}, tc_builtin_op(k, .Crash, name, vals[:], want, w, span), true
    case "int", "uint":
        if len(args) != 1 {
            tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
            return Type_Error{}, {}, true
        }
        each(k, args, env, ask, w, span, &vals, &types)
        tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64 if name == "int" else TYPE_TYPE_UINT_RESERVED_USE_U64)
        return Type_Error{}, {}, true
    }
    target, is_cast := cast_result_type(name)
    if !is_cast { return nil, {}, false }
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        return Type_Error{}, {}, true
    }
    each(k, args, env, ask, w, span, &vals, &types)
    // (One that changes nothing is said to.)
    if cast_target_same_as_operand(types[0], target) {
        operand := tc_diag_name(k, args[0])
        if operand == "" { operand = "the operand" }
        check_warning(k.c, span, WARN_REDUNDANT_CAST, name, operand, name)
    }
    b := tc_building(k)
    if want == .None || b == nil { return target, {}, true }
    if want == .Place {
        tc_fail(k, "a builtin's place")
        return target, {}, true
    }
    return target, {v = graph_op_value(b, .Cast, w, span, target, name, ..vals[:]), ok = true}, true
}

tc_builtin_op :: proc(k: ^TC, op: Op_Kind, name: string, vals: []Operand, want: Fuse_Want, w: Written, span: Span) -> Fused {
    b := tc_building(k)
    if want == .None || b == nil { return {} }
    if want == .Place {
        tc_fail(k, "a builtin's place")
        return {}
    }
    graph_op(b, op, w, span, nil, name, ..vals)
    return {v = NO_VALUE, ok = true}
}

// print's format: its `%`s, one per value after it.
tc_print_format :: proc(k: ^TC, args: []Tree_Id, span: Span) {
    if len(args) == 0 || k.t.tag[args[0]] != .String { return }
    text := tc_text(k.t.main[args[0]])
    count := 0
    for i := 0; i < len(text); i += 1 {
        if text[i] != '%' { continue }
        if i + 1 < len(text) && text[i + 1] == '%' {
            i += 1
            continue
        }
        count += 1
    }
    if count > 0 && count != len(args) - 1 {
        tc_error(k, span, TYPE_PRINT_FORMAT_STRING_PLACEHOLDER_VALUE, count, len(args) - 1)
    }
}

// What a call returns, every value (a constructor's: itself, and an err if it
// can fail); nil for what is no call.
tc_call_returns :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> []Type {
    m := tc_unparen(k, n)
    if k.t.tag[m] != .Call { return nil }
    callee := k.callees[m] or_else nil
    if callee == nil && env != nil {
        // (Not checked yet: the fun its name names.)
        if t, ok := type_env_get(env, tc_name(k, m)); ok { callee, _ = t.(^Type_Scope) }
    }
    if callee == nil { return nil }
    if list, is_ctor := constructor_effective_returns(callee); is_ctor { return list }
    if callee.kind == .Fun { return callee.return_types[:] }
    return nil
}

// What a use that takes a value at a type asks of it: an array literal is
// built at that type (a short one's other slots zero); a literal a slice
// views, in a temporary placed at the use's span — an array's at the slice's
// element type.
tc_use_type :: proc(k: ^TC, n: Tree_Id, t: Type, span: Span) -> (Dest, Span) {
    if t == nil { return {}, {} }
    e := tc_unparen(k, n)
    tag := k.t.tag[e]
    if sl, to_slice := distinct_base(t).(^Type_Slice); to_slice {
        #partial switch tag {
        case .Array:
            count := len(tree_list(k.t, k.t.a[e]))
            return {type_ = new_clone(Type_Fixed_Array{size = count, elem = sl.elem})}, span
        case .Literal:
            return {}, span
        }
        return {}, {}
    }
    if tag == .Array && graph_aggregate(t) { return {type_ = t}, {} }
    if _, to_array := distinct_base(t).(^Type_Fixed_Array); to_array && tag == .Slice { return {type_ = t}, {} }
    return {}, {}
}

// An argument or a returned value at the type its use takes: a view where
// one is taken (a partial array's header, an array's slice — its value held
// in a temporary reserved before it, `held`), else its value, widened.
tc_value_as :: proc(k: ^TC, e: Tree_Id, t: Type, r: Fused, to: Type, span: Span, w: Graph_Widen,
                    held: ^Graph_Later = nil) -> Operand {
    b := tc_building(k)
    if b == nil { return NO_VALUE }
    if to != nil {
        _, to_slice := distinct_base(to).(^Type_Slice)
        _, from_array := distinct_base(t).(^Type_Fixed_Array)
        is_literal := k.t.tag[tc_unparen(k, e)] == .Array
        if _, at := tc_use_type(k, e, to, span); at != {} && !from_array {
            tc_fail(k, "a literal placed at its use, of no array")
            return NO_VALUE
        }
        _, to_ptr := distinct_base(to).(^Type_Ptr)
        _, from_ptr := distinct_base(t).(^Type_Ptr)
        if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(t) {
            return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), tc_value(k, r, e, t))
        }
        if to_slice && from_array {
            if r.place { return graph_op_value(b, .Slice, .Implied, span, to, "", r.v) }
            if held == nil || !held.reserved {
                tc_fail(k, "a slice of an array value")
                return NO_VALUE
            }
            graph_fuse_later_begin(b, held)
            slot := graph_slot(b, "temp", t, span)
            if !graph_fuse_later_end(b, held) { tc_fail(k, "an array's value across runs") }
            graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", slot, t, span), r.v)
            return graph_op_value(b, .Slice, .Implied, span, to, "", graph_var(b, "temp", slot, t, span))
        }
        _, to_array := distinct_base(to).(^Type_Fixed_Array)
        if u := tc_unparen(k, e); to_array && (k.t.tag[u] == .Slice || k.t.tag[u] == .Index && is_byte_buffer(tc_node_type(k, Tree_Id(k.t.a[u])))) {
            tc_unsupported(k, e, "bytes taken as an array")
            return NO_VALUE
        }
        if is_literal && graph_aggregate(to) && r.v.op != NO_NODE && b.g.type_[r.v.op] == to { return r.v }
        if is_literal && graph_aggregate(to) {
            tc_fail(k, "bytes or a literal at its use's type")
            return NO_VALUE
        }
    }
    return graph_fuse_widen(b, tc_value(k, r, e, t), span, w)
}
