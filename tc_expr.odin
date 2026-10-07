package mara

import "core:fmt"
import "core:strings"

// Expressions, checked: each its type, kept on its node (tc_check), with
// what it names, what it calls and what each call's params receive
// (annot.odin). The graph is lowered from them once checking is done
// (lower.odin).

// An expression checked: its type, annotated.
tc_check :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    if n == 0 { return Type_Error{} }
    assert(!k.lowering, "the checker's tc_check, called while lowering")
    t := tc_expr_impl(k, n, env)
    tc_set_type(k, n, t)
    return t
}

// An expression checked, used at `t` (tc_settle).
tc_check_at :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, t: Type) -> Type {
    r := tc_check(k, n, env)
    tc_settle(k, n, t)
    return r
}

tc_expr_impl :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    t := k.t
    span := tree_span(t, n)
    #partial switch t.tag[n] {
    case .Number:
        return tc_number(k, n)
    case .String:
        text := token_text(build_tokens[t.main[n]])
        pa := new(Type_Partial_Array)
        pa.size = string_literal_cap(len(text))
        pa.elem = Type_Utf8{}
        return pa
    case .Char:
        return Type_Utf8{}
    case .True, .False:
        return Type_Bool{}
    case .Paren:
        return tc_check(k, Tree_Id(t.a[n]), env)
    case .Big_Endian:
        // (A read of bytes, big-endian: as the read; where it is viewed, the flag.)
        return tc_check(k, Tree_Id(t.a[n]), env)
    case .Ident:
        return tc_ident(k, n, env)
    case .Unary:
        // (`&x.f()`: f's receiver addressed — `f(&x)`.)
        if m := Tree_Id(k.t.a[n]); build_tokens[k.t.main[n]].kind == .Ampersand && k.t.tag[m] == .Method_Call {
            return tc_call(k, m, env, addressed = n)
        }
        return tc_unary(k, n, env)
    case .Deref:
        return tc_deref(k, n, env)
    case .Binary:
        return tc_binary(k, n, env)
    case .In_Range:
        return tc_in_range(k, n, env)
    case .Call, .Method_Call:
        return tc_call(k, n, env)
    case .Assert:
        return tc_assert(k, n, env)
    case .Take:
        return tc_take(k, n, env)
    case .Type_Name:
        // (A count written where a type's argument goes — `[]T(n)`'s n: the name.)
        return tc_ident(k, n, env)
    case .Hash_Name:
        return tc_hash_name(k, n, env)
    case .Self:
        return tc_self(k, n, env)
    case .Size_Of:
        return tc_size_of(k, n, env)
    case .If_Expr:
        return tc_if_expr(k, n, env)
    case .Try:
        return tc_try(k, n, env)
    case .Dot_Ident:
        if tc_sid(k, n) in k.annot.dot_bases { return tc_field(k, n, env) }
        name := tc_text(Token_Id(k.t.a[n]))
        hint := k.hint
        k.hint = nil
        et, _, found := tc_variant_ident(k, name, hint, env, true, span)
        if !found {
            tc_error(k, span, TYPE_VISIBLE_ENUM_UNION_VARIANT, name)
            return Type_Error{}
        }
        if et == nil { return Type_Error{} }
        tc_set_ref(k, n, {variant_decl(et, name), .Variant})
        tc_variant_of(k, et, name, span)
        return et
    case .Field:
        return tc_field(k, n, env)
    case .Literal, .Broadcast:   // (`all v`: `{all v}`)
        return tc_literal(k, n, env)
    case .Index:
        return tc_index(k, n, env)
    case .Slice:
        return tc_slice(k, n, env)
    case .Array:
        return tc_array_literal(k, n, env)
    }
    tc_unsupported(k, n, "this expression")
    return Type_Error{}
}

// A number: untyped, its width its use's.
tc_number :: proc(k: ^TC, n: Tree_Id) -> Type {
    return Type_Infer_Float{} if strings.index_byte(token_text(build_tokens[k.t.main[n]]), '.') >= 0 else Type_Infer_Int{}
}

// What a use takes a value at, where the value's width is the use's to
// decide (tc_open_node): a number, a constant's name, `void`, an operation
// of such, an array literal of such, an if of such — typed `t`, and what it
// is made of with it. (`t` a binding's open width: as the binding settles,
// graph_settled.)
tc_settle :: proc(k: ^TC, n: Tree_Id, t: Type) {
    if n == 0 || t == nil || tc_open(t) || !tc_open_node(k, n) { return }
    tc_set_type(k, n, t)
    tr := k.t
    #partial switch tr.tag[n] {
    case .Paren:
        tc_settle(k, Tree_Id(tr.a[n]), t)
    case .Unary:
        #partial switch build_tokens[tr.main[n]].kind {
        case .Minus, .Wrap_Minus, .Tilde: tc_settle(k, Tree_Id(tr.a[n]), t)
        }
    case .Binary:
        #partial switch build_tokens[tr.main[n]].kind {
        case .Plus, .Minus, .Star, .Slash, .Modulo, .Wrap_Plus, .Wrap_Minus, .Wrap_Star,
             .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
            tc_settle(k, Tree_Id(tr.a[n]), t)
            tc_settle(k, Tree_Id(tr.b[n]), t)
        }
    case .Array:
        if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array {
            for e in tree_list(tr, tr.a[n]) { tc_settle(k, e, fa.elem) }
        }
    case .If_Expr:
        then_n, else_n := tree_pair(tr, n)
        tc_settle(k, then_n, t)
        tc_settle(k, else_n, t)
    }
}

// A width no use has decided yet (no binding's).
tc_open :: proc(t: Type) -> bool {
    return is_infer(t) && infer_cell_of(t) == nil
}

// Whether a node's type is its use's to decide: a number's, a constant's,
// an operation's of such (an open width), an untyped `void`, an array
// literal's of open elements, an if's of either.
tc_open_node :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := tc_node_type(k, n)
    #partial switch k.t.tag[n] {
    case .Number, .Paren, .Unary, .Binary, .Size_Of, .Field, .Dot_Ident:
        return tc_open(t)
    case .Ident:
        return tc_open(t) || is_any(t) && tc_name(k, n) == "void"
    case .Array, .If_Expr:
        if fa, is_array := t.(^Type_Fixed_Array); is_array { return tc_open(fa.elem) }
        return k.t.tag[n] == .If_Expr && tc_open(t)
    }
    return false
}

tc_ident :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    name := tc_name(k, n)
    span := tree_span(k.t, n)
    hint := k.hint
    k.hint = nil
    // (A variant of the enum expected, first.)
    if hint != nil {
        if et, _, found := tc_variant_ident(k, name, hint, env, false, span); found {
            if et == nil { return Type_Error{} }
            tc_set_ref(k, n, {variant_decl(et, name), .Variant})
            tc_variant_of(k, et, name, span)
            return et
        }
    }
    // (A constant: the one a scope around it declares — it shadows a
    // module's — else its own module's, or one it uses' — two is ambiguous.)
    t, loc_scope, ok := scope_find(env, name)
    kc := tc_local_const(k, env, loc_scope, name) if ok else nil
    if kc == nil {
        unambiguous: bool
        kc, unambiguous = tc_const_ref(k, env, name, span)
        if !unambiguous { return Type_Error{} }
    }
    if kc != nil {
        tc_set_ref(k, n, {k.t.main[kc.def], .Const})
    } else if ok {
        tc_set_ref(k, n, scope_find_ref(env, name))
    }
    if !ok && kc != nil {
        // (Not bound here yet: its value's type — unless it is the value
        // being checked.)
        if kc.visiting || kc.state == .In_Progress {
            tc_error(k, span, TYPE_CONSTANT_DEFINED_ITSELF, name)
            return Type_Error{}
        }
        kc.visiting = true
        ct := tc_check(k, kc.value, env)
        kc.visiting = false
        return ct
    }
    if !ok {
        // (A type named as a value: said so.)
        flat := resolve_type_name(k.pkg, name, "", env)
        if flat in k.table.funs || flat in k.table.enums || flat in k.table.unions {
            tc_error(k, span, TYPE_TYPE_VALUE_DID_MEAN, name, name)
        } else {
            report_unresolved(k.c, span, env, name, TYPE_UNDEFINED_IDENTIFIER)
        }
        return Type_Error{}
    }
    return t
}

// (`of`: the operand in place of its own — a method call's receiver, where
// the `&` is written around the call.)
tc_unary :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, of := Tree_Id(0)) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    op := build_tokens[tr.main[n]].kind
    operand := of if of != 0 else Tree_Id(tr.a[n])
    if op == .Minus && tr.tag[operand] == .Number {
        t := tc_number(k, operand)
        tc_set_type(k, operand, t)
        return t
    }
    wrapping := op == .Wrap_Minus
    ot := tc_check(k, operand, env)
    t: Type
    #partial switch op {
    case .Minus, .Wrap_Minus:
        t = ot
        if wrapping {
            if !is_wrap_operand(ot) {
                tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER_UNARY, type_name(ot))
                return Type_Error{}
            }
        } else if !is_numeric(ot) {
            // (`overload -`: a function of the one operand, when one fits.)
            if callee := tc_unary_overload(k, ot, env); callee != nil {
                tc_set_callee(k, n, callee)
                tc_set_args(k, n, {{operand, .Written, -1}})
                tc_settle(k, operand, callee.params[0].type_)
                return fn_primary_return(callee)
            }
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
        // (An address of an immutable param's storage, of a constant's: what
        // it would let be written can't be.)
        if pname, immutable := tc_write_root_param(k, operand, env); immutable {
            tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_IMMUTABLE_PARAMETER, pname)
        }
        if cname, is_const := tc_write_root_const(k, operand); is_const { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_CONSTANT, cname) }
        if tr.tag[operand] == .String { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL) }
        // (A part of a value — an if's, a literal's — is no storage; a
        // slice builds a header with nowhere to point.)
        #partial switch tr.tag[tc_access_root(k, operand)] {
        case .If_Expr, .Array, .Literal: tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_EXPRESSION)
        }
        if tr.tag[tc_unparen(k, operand)] == .Slice { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_SLICE_TEMP) }
        pt := new(Type_Ptr)
        pt.elem = ot
        t = pt
    case:
        tc_unsupported(k, n, "this unary operator")
        return Type_Error{}
    }
    return t
}

tc_deref :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    span := tree_span(k.t, n)
    ot := tc_check(k, Tree_Id(k.t.a[n]), env)
    if p, ok := ot.(^Type_Ptr); ok { return p.elem }
    if !is_any(ot) { tc_error(k, span, TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE, type_name(ot)) }
    return Type_Error{}
}

// A binary operation: each side at the type the operation works in; `and` /
// `or` short-circuit.
tc_binary :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    return tc_binary_op(k, n, build_tokens[tr.main[n]].kind, tree_span(tr, n), Tree_Id(tr.a[n]), Tree_Id(tr.b[n]), env)
}

// `x in lo..hi`: `x >= lo and x < hi` — `not in`, its negation — x walked
// twice, each part at the `in`.
TC_In_Range :: struct {
    value, lo, hi: Tree_Id,
    span:          Span,
}

tc_in_range :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    lo, hi := tree_pair(tr, n)
    rng := TC_In_Range{value = Tree_Id(tr.a[n]), lo = lo, hi = hi, span = span}
    if build_tokens[tr.main[n]].kind != .Not { return tc_binary_op(k, 0, .And, span, 0, 0, env, &rng) }
    ot := tc_binary_op(k, 0, .And, span, 0, 0, env, &rng)
    if _, is_bool := ot.(Type_Bool); !is_bool && !is_any(ot) { tc_error(k, span, TYPE_CANNOT_APPLY, type_name(ot)) }
    return Type_Bool{}
}

// `left op right`, where `span` is: a Binary's, or a compound assignment's
// (`x += v` is `x = x op v`, at the `+=`). `at`: its node, where an operator
// through `overload` is annotated as the call it is.
tc_binary_op :: proc(k: ^TC, at: Tree_Id, tok: Token_Kind, span: Span, left, right: Tree_Id, env: ^Type_Scope,
                     in_range: ^TC_In_Range = nil) -> Type {
    // (A side: its expression; an `in`'s, its comparison.)
    side_of :: proc(k: ^TC, rng: ^TC_In_Range, i: int, side: Tree_Id, env: ^Type_Scope) -> Type {
        if rng == nil { return tc_check(k, side, env) }
        if i == 0 { return tc_binary_op(k, 0, .Greater_Equal, rng.span, rng.value, rng.lo, env) }
        return tc_binary_op(k, 0, .Less, rng.span, rng.value, rng.hi, env)
    }
    tr := k.t
    op := tok
    wrapping := false
    #partial switch tok {
    case .Wrap_Plus:  op, wrapping = .Plus, true
    case .Wrap_Minus: op, wrapping = .Minus, true
    case .Wrap_Star:  op, wrapping = .Star, true
    }
    hint := k.hint
    types: [2]Type
    for side, i in ([2]Tree_Id{left, right}) {
        k.hint = hint
        types[i] = side_of(k, in_range, i, side, env)
    }
    lt, rt := types[0], types[1]
    and_or := op == .And || op == .Or
    t: Type = Type_Error{}
    if wrapping && (!is_wrap_operand(lt) || !is_wrap_operand(rt)) {
        tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER, op_str(op), type_name(lt), type_name(rt))
        return Type_Error{}
    }
    // (An operand no number: an `overload`'s function, when one fits.)
    if !and_or && (!is_numeric(lt) || !is_numeric(rt)) {
        if callee, found := tc_operator_overload(k, op, lt, rt, env, span); found {
            tc_set_callee(k, at, callee)
            tc_set_args(k, at, {{left, .Written, -1}, {right, .Written, -1}})
            tc_settle(k, left, callee.params[0].type_)
            tc_settle(k, right, callee.params[1].type_)
            return fn_primary_return(callee)
        }
    }
    #partial switch op {
    case .And, .Or:
        word := "and" if op == .And else "or"
        if _, ok := lt.(Type_Bool); !ok && !is_any(lt) {
            tc_error(k, span, TYPE_LEFT_OPERAND_BOOL, word, type_name(lt))
            // (`x and y == 0` is `x and (y == 0)`: show the form meant.)
            if r := tc_unparen(k, right); in_range == nil && tr.tag[r] == .Binary && is_numeric(lt) {
                if cmp := build_tokens[tr.main[r]].kind; is_comparison_op(cmp) {
                    rhs := tc_written(k, Tree_Id(tr.b[r]))
                    meant := fmt.tprintf("%s %s %s %s %s %s %s", tc_written(k, left), op_str(cmp), rhs,
                                         word, tc_written(k, Tree_Id(tr.a[r])), op_str(cmp), rhs)
                    check_warning(k.c, span, TYPE_DID_MEAN_EACH_OPERAND_NEEDS, meant, word)
                }
            }
        }
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
            return Type_Error{}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case .Minus, .Star, .Slash, .Modulo:
        if !is_numeric(lt) || !is_numeric(rt) {
            sym := "-" if op == .Minus else "*" if op == .Star else "/" if op == .Slash else "%%"
            tc_error(k, span, TYPE_MISMATCHED_TYPES_DID_FORGET_IMPORT_2, sym, type_name(lt), type_name(rt))
            return Type_Error{}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(lt) && !is_any(lt) {
            tc_error(k, span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(lt))
            return Type_Error{}
        }
        if !is_integer(rt) && !is_any(rt) {
            tc_error(k, span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(rt))
            return Type_Error{}
        }
        t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
    case:
        tc_error(k, span, "tc: the operator %v is not supported yet", tok)
        return Type_Error{}
    }
    // (Each side at the type the operation takes it at: a comparison's, the
    // other side's; an arithmetic one's, its own.)
    if is_comparison_op(op) {
        tc_settle(k, left, rt)
        tc_settle(k, right, lt)
    } else if !and_or {
        tc_settle(k, left, t)
        tc_settle(k, right, t)
    }
    return t
}

// --- calls --------------------------------------------------------------------

tc_call :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope, addressed := Tree_Id(0)) -> Type {
    if k.t.tag[n] == .Method_Call { return tc_method_call(k, n, env, addressed) }
    saved := k.recv
    k.recv = {}
    defer k.recv = saved
    return tc_call_core(k, n, tc_name(k, n), tree_list(k.t, k.t.a[n]), env)
}

// A call of `name` on `args` — or, resolved by its qualifier (a method, a
// module's fun: `qual`; a module's dispatch: `qual_dispatch`), of that.
tc_call_core :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, env: ^Type_Scope,
                     qual: ^Type_Scope = nil, qual_dispatch: []string = nil) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    // (A call of several results, as one argument: its extras would be lost —
    // a method call's, checked before its receiver.)
    for a in args {
        if tr.tag[n] == .Method_Call { break }
        if returns := tc_call_returns(k, a, env); len(returns) > 1 {
            tc_error(k, tree_span(tr, tc_unparen(k, a)), TYPE_MULTI_RETURN_AS_ARG, len(returns))
        }
    }
    if len(qual_dispatch) > 0 {
        members := make([dynamic]string, context.temp_allocator)
        append(&members, ..qual_dispatch)
        return tc_dispatch_call(k, n, name, members, args, env)
    }
    if qual == nil {
        if t, is_builtin := tc_builtin(k, n, name, args, env); is_builtin {
            tc_set_ref(k, n, {kind = .Builtin})
            k.annot.forms[tc_sid(k, n)] = .Builtin
            return t
        }
        if members, is_dispatch := find_dispatch(k.c, env, name); is_dispatch {
            return tc_dispatch_call(k, n, name, members, args, env)
        }
        if tmpl, is_template := k.templates[name]; is_template {
            return tc_generic_call(k, n, name, tmpl, args, env)
        }
    }
    ft_raw, found := scope_lookup(env, name)
    if qual != nil { ft_raw, found = qual, true }
    if !found {
        tc_error(k, span, TYPE_UNDEFINED_FUNCTION, name)
        for a in args { tc_check(k, a, env) }
        return Type_Error{}
    }
    if dt, is_distinct := ft_raw.(^Type_Distinct); is_distinct {
        tc_set_ref(k, n, {type_decl(dt), .Type})
        k.annot.forms[tc_sid(k, n)] = .Conversion
        return tc_distinct_conversion(k, n, name, dt, args, env)
    }
    ft, is_scope := ft_raw.(^Type_Scope)
    // (A fun written in the program, or a foreign one; else a fun's value — a
    // name no declared fun has, holding one — called through it.)
    indirect := is_scope && qual == nil && ft.kind == .Fun && name not_in k.c.declared_funs && (ft.name == "" || ft.name not_in k.c.declared_funs)
    if !is_scope {
        tc_error(k, span, TYPE_FUNCTION, name)
        return Type_Error{}
    }
    // (A fun two modules it uses have: ambiguous.)
    if qual == nil && name in k.c.declared_funs && ft.name != "" {
        if owners := fn_ambiguous_owners(env, name); owners != nil {
            tc_error(k, span, TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED, name, strings.join(owners[:], ", ", context.temp_allocator), owners[0], name)
            return Type_Error{}
        }
    }
    if ft.is_module || !indirect && ft.node == 0 && ft.calling_conv != .C {
        tc_unsupported(k, n, "a call of this")
        return Type_Error{}
    }
    is_struct := ft.kind == .Struct
    // (`Foo(args) {f = v}`: its fields written once it is constructed.)
    overrides := Tree_Id(tr.b[n]) if tr.tag[n] == .Call else method_view(tr, n).overrides
    if overrides != 0 && !is_struct { tc_error(k, span, TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID, name) }
    tc_set_callee(k, n, ft)
    tc_set_ref(k, n, scope_find_ref(env, name) if indirect else Ref{ft.decl, .Type if is_struct else .Fun})
    k.annot.forms[tc_sid(k, n)] = .Value if indirect else .Fun
    if is_struct { tc_struct_ensure(k, ft) }
    if len(args) < count_required_params(ft) || len(args) > len(ft.params) {
        qualified := name
        if ft.home_package != "" { qualified = strings.concatenate({ft.home_package, ".", name}) }
        tc_error(k, span, TYPE_EXPECTS_ARGS, qualified, len(ft.params), fn_params_desc(ft), len(args))
    }
    // (The params it leaves off: their defaults, each checked in its fun's
    // defining scope, run at the call.)
    items := make([dynamic]TC_Arg, 0, len(ft.params), context.temp_allocator)
    if len(args) >= count_required_params(ft) && len(args) <= len(ft.params) {
        // (A param's default: run at the call, checked in its fun's scope;
        // `#caller_name`, the call site's, written there.)
        default_arg :: proc(k: ^TC, p: Struct_Type_Field, ft: ^Type_Scope, env: ^Type_Scope, at: Span) -> TC_Arg {
            if k.t.tag[p.default_node] == .Hash_Name { return TC_Arg{p.default_node, env, at, nil} }
            return TC_Arg{p.default_node, callee_def_scope(ft), {}, p.default_slot}
        }
        for a, i in args {
            // (`_`: its param's default — said so when it has none.)
            if tr.tag[a] == .Ident && tc_name(k, a) == "_" && i < len(ft.params) {
                if ft.params[i].default_node == 0 {
                    tc_error(k, span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER, i + 1, name, ft.params[i].name)
                } else {
                    append(&items, default_arg(k, ft.params[i], ft, env, tree_span(tr, a)))
                    continue
                }
            }
            append(&items, TC_Arg{a, env, {}, nil})
        }
        for i := len(args); i < len(ft.params); i += 1 { append(&items, default_arg(k, ft.params[i], ft, env, span)) }
        // (What each param receives, kept.)
        received := make([]Arg, len(items), context.temp_allocator)
        for item, i in items {
            switch {
            case item.node == k.recv.node && item.node != 0: received[i] = {item.node, .Receiver, -1}
            case item.at != {}:                                received[i] = {item.node, .Call_Site, -1}
            case item.node == ft.params[i].default_node:       received[i] = {item.node, .Default, i32(item.slot.? or_else -1)}
            case:                                              received[i] = {item.node, .Written, -1}
            }
        }
        tc_set_args(k, n, received)
    }
    for item, i in items {
        a, a_env := item.node, item.env
        pt := ft.params[i].type_
        k.hint = pt
        at: Type
        if item.at != {} {
            at = tc_hash_name(k, a, a_env)
        } else if slot, is_slot := item.slot.?; is_slot {
            at = tc_tuple_default(k, a, slot, a_env, span)
        } else {
            at = k.recv.t if a == k.recv.node else tc_check(k, a, a_env)
        }
        // (Bytes read as an array param: `buf[off]`, `buf[lo:hi]` — its size
        // the param's.)
        reinterpret := false
        if _, to_array := pt.(^Type_Fixed_Array); to_array {
            if m, _ := tc_byte_node(k, a); tc_byte_index(k, a) || k.t.tag[m] == .Slice && is_byte_buffer(at) {
                reinterpret = tc_check_byte_flow(k, pt, a, at, span) == .Read
            }
        }
        if !reinterpret && !coerce_deferred(k.c, at, pt, span) && types_incompatible(pt, at) && !value_preserving_widen(at, pt) {
            clause := ""
            if an := tc_diag_name(k, a); an != "" { clause = fmt.tprintf(" ('%s')", an) }
            tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, clause, name, ft.params[i].name, type_name(pt), type_name(at))
        }
        // (A runtime string into a `cstring` param: `cstring(s)`, written —
        // the copy and the terminator seen. A literal, or a constant one,
        // passes free: rodata carries the \0.)
        if is_cstring(pt) && !is_cstring(at) && !tc_text_literal(k, a) {
            tc_error(k, span, TYPE_CSTRING_ARG_EXPLICIT)
        }
        tc_value_at(k, a, at, pt, span)
    }
    if is_struct {
        if overrides != 0 { tc_literal_fields(k, overrides, tree_list(tr, tr.b[overrides]), &ft.sd, env) }
        return ft
    }
    return fn_primary_return(ft)
}

// A literal that doesn't fit the type it is used at.
// A value at the type its use takes it at, `t`: one of no width of its own
// settled to it (tc_settle), a literal's range checked.
tc_value_at :: proc(k: ^TC, n: Tree_Id, vt, t: Type, span: Span) {
    if is_infer(vt) { tc_literal_overflow(k, n, t, span) }
    tc_settle(k, n, t)
}

tc_literal_overflow :: proc(k: ^TC, n: Tree_Id, target: Type, span: Span) {
    if f, i, lit := tc_literal_value(k, n); lit {
        check_value_range(k.c, f, i, target, span)
        return
    }
    // (A constant's name: its value's.)
    if u := tc_unparen(k, n); k.t.tag[u] == .Ident {
        if kc, ok := k.consts[tc_name(k, u)]; ok { tc_literal_overflow(k, kc.value, target, span) }
    }
}

// A number as written, or negated: its value.
tc_literal_value :: proc(k: ^TC, n: Tree_Id) -> (f64, i128, bool) {
    tr := k.t
    neg := false
    num := tc_unparen(k, n)
    if tr.tag[num] == .Unary && build_tokens[tr.main[num]].kind == .Minus && tr.tag[tc_unparen(k, Tree_Id(tr.a[num]))] == .Number {
        neg, num = true, tc_unparen(k, Tree_Id(tr.a[num]))
    }
    if tr.tag[num] != .Number { return 0, 0, false }
    f, i, _ := parse_number_text(token_text(build_tokens[tr.main[num]]))
    if neg { f, i = -f, -i }
    return f, i, true
}

// `assert(c)`: its condition a bool.
tc_assert :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    span := tree_span(k.t, n)
    ct := tc_check(k, Tree_Id(k.t.a[n]), env)
    if _, ok := ct.(Type_Bool); !ok && !is_any(ct) { tc_error(k, span, TYPE_CONDITION_BOOL, type_name(ct)) }
    return Type_Void{}
}

// `#self`: the address of what a constructor builds (Self, its place) —
// only a constructor's frame has one.
tc_self :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    f := enclosing_callable_scope(env)
    if f == nil || f.kind != .Struct {
        tc_error(k, tree_span(k.t, n), TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT)
        return Type_Error{}
    }
    return new_clone(Type_Ptr{elem = f})
}

// Whether an expression is `#self`: what is reached through it is Self's
// own, no pointer's.
tc_is_self :: proc(k: ^TC, n: Tree_Id) -> bool {
    return k.t.tag[tc_unparen(k, n)] == .Self
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
    if tc_ref(k, n).kind == .Variant { return true }   // (a variant's name states its value)
    #partial switch k.t.tag[n] {
    case .Number, .True, .False, .Char: return true
    case .Unary:
        return build_tokens[k.t.main[n]].kind == .Minus && k.t.tag[tc_unparen(k, Tree_Id(k.t.a[n]))] == .Number
    }
    return false
}

// A builtin: print, crash, a cast — its args checked as values.
tc_builtin :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, env: ^Type_Scope) -> (Type, bool) {
    span := tree_span(k.t, n)
    types := make([dynamic]Type, 0, len(args), context.temp_allocator)
    each :: proc(k: ^TC, args: []Tree_Id, env: ^Type_Scope, types: ^[dynamic]Type) {
        for a in args { append(types, tc_arg(k, a, env)) }
    }
    switch name {
    case "print":
        each(k, args, env, &types)
        for a, i in args { tc_is_value(k, a, types[i], tree_span(k.t, a), printed = true) }
        tc_print_format(k, args, span)
        return Type_Error{}, true
    case "crash":
        if len(args) > 1 {
            tc_error(k, span, TYPE_CRASH_EXPECTS_ARGUMENTS, len(args))
        } else {
            each(k, args, env, &types)
        }
        return Type_Error{}, true
    case "int", "uint":
        if len(args) != 1 {
            tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
            return Type_Error{}, true
        }
        each(k, args, env, &types)
        tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64 if name == "int" else TYPE_TYPE_UINT_RESERVED_USE_U64)
        return Type_Error{}, true
    }
    target, is_cast := cast_result_type(name)
    if !is_cast { return tc_builtin_more(k, n, name, args, env) }
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        return Type_Error{}, true
    }
    each(k, args, env, &types)
    // (One that changes nothing is said to.)
    if cast_target_same_as_operand(types[0], target) {
        operand := tc_diag_name(k, args[0])
        if operand == "" { operand = "the operand" }
        check_warning(k.c, span, WARN_REDUNDANT_CAST, name, operand, name)
    }
    return target, true
}

// Whether `n`, checked as `t`, is a value where one goes with no type to
// meet it (a `:=`, print's arguments) — said when it is none: a type's
// name, a module's, a call that returns nothing; a fun, when printed.
tc_is_value :: proc(k: ^TC, n: Tree_Id, t: Type, span: Span, printed := false) -> bool {
    m := tc_unparen(k, n)
    name := tc_diag_name(k, m)
    ts, is_scope := t.(^Type_Scope)
    if is_scope && ts.is_module {
        tc_error(k, span, TYPE_MODULE_NOT_VALUE, name)
        return false
    }
    // (A type's own name: no local can share it — tc_declarable.)
    if k.t.tag[m] == .Ident && tc_type_source_name(t) == name {
        if printed { tc_error(k, span, TYPE_TYPE_NOT_VALUE, name) } else { tc_error(k, span, TYPE_TYPE_VALUE_DID_MEAN, name, name) }
        return false
    }
    if _, is_void := t.(Type_Void); tc_is_call(k, m) && (t == nil || is_void) {
        tc_error(k, span, TYPE_CALL_NO_VALUE, name)
        return false
    }
    if printed && is_scope && ts.kind == .Fun {
        tc_error(k, span, TYPE_PRINT_FUN, name)
        return false
    }
    return true
}

// The name a type is written by: a struct's, an enum's, a union's, a
// distinct type's; "" for any other.
tc_type_source_name :: proc(t: Type) -> string {
    #partial switch v in t {
    case ^Type_Scope:    if v.kind == .Struct && !v.is_module { return v.source_name }
    case ^Type_Enum:     return v.source_name
    case ^Type_Union:    return v.source_name
    case ^Type_Distinct: return v.source_name
    }
    return ""
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
    if !tc_is_call(k, m) { return nil }
    callee := tc_callee(k, m)
    if callee == nil && env != nil {
        // (Not checked yet: the fun its name names.)
        if t, ok := scope_lookup(env, tc_call_name(k, m)); ok { callee, _ = t.(^Type_Scope) }
    }
    if callee == nil { return nil }
    if list, is_ctor := constructor_effective_returns(callee); is_ctor { return list }
    if callee.kind == .Fun { return callee.return_types[:] }
    return nil
}

// An argument as checked: its expression, where its names resolve — a
// default's: its fun's defining scope, or (`#caller_name`) the call site,
// `at`; a default one of a group's one value: its slot.
TC_Arg :: struct {
    node: Tree_Id,
    env:  ^Type_Scope,
    at:   Span,
    slot: Maybe(int),
}

// A param's default that is a slot of its group's one value (`x, y :=
// f()`): f's result there; a value no call of several results, a
// broadcast: the value's.
tc_tuple_default :: proc(k: ^TC, src: Tree_Id, slot: int, env: ^Type_Scope, span: Span) -> Type {
    st := tc_check(k, src, env)
    if _, is_err := st.(Type_Error); is_err { return Type_Error{} }
    if returns := tc_call_returns(k, src, env); len(returns) > 1 {
        if slot >= len(returns) {
            tc_error(k, span, TYPE_TUPLE_DESTRUCTURE_INDEX_OUT_RANGE, slot, len(returns))
            return Type_Error{}
        }
        return returns[slot]
    }
    return st
}

// `#caller_name`, `#caller_span`: text; `#web` and the targets: a bool.
tc_hash_name :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    switch tc_text(Token_Id(k.t.a[n])) {
    case "caller_name", "caller_span":
        return new_clone(Type_Ptr{elem = Type_Byte{}})
    case "web", "native", "windows", "linux", "mac":
        return Type_Bool{}
    }
    tc_unsupported(k, n, "this compiler name")
    return Type_Error{}
}

// A construction's arguments: its constructor's params' defaults, each
// checked where its fun is defined.
tc_ctor_args :: proc(k: ^TC, ts: ^Type_Scope, span: Span) {
    for p in ts.params {
        if p.default_node == 0 { continue }
        tc_default(k, p.default_node, p.type_, ts)
    }
}

// A default, checked in its owner's defining scope, at the type it defaults.
tc_default :: proc(k: ^TC, def: Tree_Id, t: Type, owner: ^Type_Scope) {
    saved := k.hint
    k.hint = t
    defer k.hint = saved
    tc_check_at(k, def, callee_def_scope(owner), t)
}

// The rest of the builtins: print_cstr / print_int / print_float (as print),
// len and cap (of a place — a fixed array's, its size), slice_from_ptr,
// cstring.
tc_builtin_more :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, env: ^Type_Scope) -> (Type, bool) {
    span := tree_span(k.t, n)
    switch name {
    case "print_cstr", "print_int", "print_float":
        msg := TYPE_PRINT_CSTR_EXPECTS_ARGUMENT_BYTE
        if name == "print_int" { msg = TYPE_PRINT_INT_EXPECTS_ARGUMENT_INT }
        if name == "print_float" { msg = TYPE_PRINT_FLOAT_EXPECTS_ARGUMENT_FLOAT }
        if len(args) != 1 {
            tc_error(k, span, msg, len(args))
            return Type_Error{}, true
        }
        tc_arg(k, args[0], env)
        return Type_Error{}, true
    case "len", "cap":
        t := slice_header_width_type
        if len(args) != 1 {
            tc_error(k, span, TYPE_LEN_EXPECTS_ARGUMENT if name == "len" else TYPE_CAP_EXPECTS_ARGUMENT, len(args))
            return t, true
        }
        at := tc_arg(k, args[0], env)
        if !is_array_type(at) && !is_any(at) {
            tc_error(k, span, TYPE_LEN_REQUIRES_ARRAY_SLICE if name == "len" else TYPE_CAP_REQUIRES_ARRAY_SLICE, type_name(at))
        }
        return t, true
    case "slice_from_ptr":
        t := new_clone(Type_Slice{elem = Type_Byte{}})
        if len(args) != 2 {
            tc_error(k, span, TYPE_SLICE_PTR_EXPECTS_ARGUMENTS_PTR, len(args))
            return t, true
        }
        pt := tc_arg(k, args[0], env)
        if _, is_ptr := pt.(^Type_Ptr); !is_ptr && !is_any(pt) {
            tc_error(k, span, TYPE_SLICE_PTR_FIRST_ARGUMENT_POINTER, type_name(pt))
        }
        st := tc_arg(k, args[1], env)
        tc_settle(k, args[1], slice_header_width_type)
        if !is_numeric(st) && !is_any(st) {
            tc_error(k, span, TYPE_SLICE_PTR_SECOND_ARGUMENT_NUMERIC, type_name(st))
        } else if !coerces_to_slice_width(st) {
            tc_error(k, span, TYPE_SLICE_PTR_SECOND_ARGUMENT_WIDTH, type_name(slice_header_width_type), type_name(st))
        }
        if k.pkg != "os" && k.pkg != "mara.os" {
            if _, known := tc_comptime_int(k, args[1], nil); !known {
                tc_error(k, span, TYPE_SLICE_PTR_OUTSIDE_OS_MODULE +
                    "(literal, '::' constant, or comptime arithmetic). Runtime-derived lengths " +
                    "are restricted because they're the classic source of OOB-access bugs at C boundaries.")
            }
        }
        return t, true
    case "cstring":
        if len(args) != 1 {
            tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
            return Type_CString{}, true
        }
        at := tc_arg(k, args[0], env)
        elem: Type
        #partial switch v in distinct_base(at) {
        case ^Type_Partial_Array: elem = v.elem
        case ^Type_Slice:         elem = v.elem
        case ^Type_Fixed_Array:   elem = v.elem
        }
        elem_ok := false
        #partial switch _ in elem {
        case Type_Utf8, Type_Byte: elem_ok = true
        }
        if !elem_ok && !is_any(at) { tc_error(k, span, TYPE_CSTRING_CTOR_ARGUMENT, type_name(at)) }
        return Type_CString{}, true
    }
    return nil, false
}

// `size_of(T)`: T's size, a constant (untyped: the width its use takes).
tc_size_of :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    span := tree_span(k.t, n)
    t := tc_type(k, Tree_Id(k.t.a[n]), env, span)
    if _, is_error := t.(Type_Error); is_error { tc_error(k, span, TYPE_SIZE_UNKNOWN_TYPE) }
    tc_ensure_layout(k, t)
    k.annot.size_of[tc_sid(k, n)] = t
    return Type_Infer_Int{}
}

// A type's layout known: each struct in it checked (its fields found).
tc_ensure_layout :: proc(k: ^TC, t: Type) {
    #partial switch v in t {
    case ^Type_Scope:
        if v.kind != .Struct { return }
        tc_struct_ensure(k, v)
        for f in v.sd.fields { tc_ensure_layout(k, f.type_) }
    case ^Type_Fixed_Array:   tc_ensure_layout(k, v.elem)
    case ^Type_Partial_Array: tc_ensure_layout(k, v.elem)
    case ^Type_Distinct:      tc_ensure_layout(k, v.base_type)
    case ^Type_Union:
        for _, st in v.variant_structs { tc_ensure_layout(k, st) }
    }
}

// `Id(x)`, Id a distinct type: x at its base type, seen as Id (a
// conversion: its bits as they are).
tc_distinct_conversion :: proc(k: ^TC, n: Tree_Id, name: string, dt: ^Type_Distinct, args: []Tree_Id, env: ^Type_Scope) -> Type {
    span := tree_span(k.t, n)
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        return Type_Error{}
    }
    saved := k.hint
    k.hint = dt.base_type
    at := tc_check(k, args[0], env)
    k.hint = saved
    if !is_any(at) && !is_infer(at) && types_incompatible(dt.base_type, at) {
        tc_error(k, span, TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE, name, type_name(at), type_name(dt.base_type))
    }
    return dt
}

// `f()?`: the call, its err returned when it is one — its value the call's
// first, or none when it returns only its err.
tc_try :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    span := tree_span(k.t, n)
    inner := Tree_Id(k.t.a[n])
    tc_check(k, inner, env)
    if !tc_is_call(k, tc_unparen(k, inner)) {
        tc_error(k, span, TYPE_TRY_OPERAND_MUST_BE_CALL)
        return Type_Error{}
    }
    rets := tc_call_returns(k, inner, env)
    if len(rets) == 0 || !is_err_type(rets[len(rets) - 1]) {
        tc_error(k, span, TYPE_TRY_REQUIRES_ERR_RETURN)
        return Type_Error{}
    }
    rts := enclosing_return_types(env)
    if len(rts) == 0 || !is_err_type(rts[len(rts) - 1]) {
        tc_error(k, span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
        return Type_Error{}
    }
    if len(rets) == 1 { return Type_Void{} }
    return rets[0]
}

// `if c do a else b` as a value: its condition a bool, its type its
// branches' (an untyped one takes the other's).
tc_if_expr :: proc(k: ^TC, n: Tree_Id, env: ^Type_Scope) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    then_n, else_n := tree_pair(tr, n)
    ct := tc_check(k, Tree_Id(tr.a[n]), env)
    if !is_any(ct) {
        if _, is_bool := ct.(Type_Bool); !is_bool { tc_error(k, span, TYPE_EXPRESSION_CONDITION_BOOL, type_name(ct)) }
    }
    types: [2]Type
    for branch, i in ([2]Tree_Id{then_n, else_n}) { types[i] = tc_check(k, branch, env) }
    t := types[0]
    switch {
    case is_untyped(types[0]) || is_infer(types[0]): t = types[1]
    case is_untyped(types[1]) || is_infer(types[1]):
    case types_incompatible(types[0], types[1]):
        tc_error(k, span, TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS, type_name(types[0]), type_name(types[1]))
    }
    // (Each branch written to its local, at its type.)
    tc_settle(k, then_n, t)
    tc_settle(k, else_n, t)
    return t
}

// The expression an access path (`x.f[i].g`) is rooted at.
tc_access_root :: proc(k: ^TC, n: Tree_Id) -> Tree_Id {
    cur := tc_unparen(k, n)
    for {
        #partial switch k.t.tag[cur] {
        case .Field, .Index: cur = tc_unparen(k, Tree_Id(k.t.a[cur]))
        case: return cur
        }
    }
}

// A call's receiver, checked where its method was found (tc_method_call):
// the first argument, not checked again.
TC_Recv :: struct {
    node: Tree_Id,
    t:    Type,
}

// An argument, checked — or the receiver, as checked.
tc_arg :: proc(k: ^TC, a: Tree_Id, env: ^Type_Scope) -> Type {
    if a != 0 && a == k.recv.node { return k.recv.t }
    return tc_check(k, a, env)
}
