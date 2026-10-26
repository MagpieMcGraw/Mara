package mara

import "core:fmt"
import "core:strings"
import "core:slice"

// Expressions, checked: each its type, kept on its node (tc_check), with
// what it names, what it calls and what each call's params receive
// (annot.odin). The graph is lowered from them once checking is done
// (lower.odin).

// An expression checked: its type, annotated.
tc_check :: proc(k: ^TC, n: Tree_Id) -> Type {
    if n == 0 { return Type_Error{} }
    assert(!k.lowering, "the checker's tc_check, called while lowering")
    hint := k.hint
    t := tc_expr_impl(k, n)
    tc_set_type(k, n, t)
    tc_note_err_site(k, n, t, hint)
    return t
}

// An error's variant where an err is made of it — where an err goes: a
// return's, an err param's, `e : err = Lost` (k.hint) — noted with where
// it is, an atom ("errors.mara:12:20 in digit"), for lowering to put in
// the err's high 32 bits (lw_err_site): `e.where()` gives it back, and `?`
// passes it on as it is. Ok is no failure: none, its err 0.
tc_note_err_site :: proc(k: ^TC, n: Tree_Id, t: Type, hint: Type) {
    if _, to_err := distinct_base(hint).(Type_Err); !to_err { return }
    et, is_enum := distinct_base(t).(^Type_Enum)
    if !is_enum || !et.is_error_kind { return }
    tr := k.t
    name: string
    #partial switch tr.tag[n] {
    case .Ident:     name = tc_name(k, n)
    case .Dot_Ident: name = tc_text(Token_Id(tr.a[n]))
    case .Field:     name = tc_text(Token_Id(tr.b[n]))
    case:            return
    }
    if value, has := et.variants[name]; !has || value == 0 { return }
    k.annot.err_sites[tc_sid(k, n)] = checked_atom(k.checked, tc_err_place(k, n)) + 1
}

// Where an err is passed on — a `?` (n the `?`), a `return …, e` of one
// made before (n the value; `returned`) — noted as an atom, for lowering to
// add to its trace (lw_err_pass). Apart: `return f()?` is both a `?` and a
// value, one that isn't the err.
tc_note_err_pass :: proc(k: ^TC, n: Tree_Id, returned := false) {
    site := checked_atom(k.checked, tc_err_place(k, n)) + 1
    if returned { k.annot.err_returns[tc_sid(k, n)] = site } else { k.annot.err_passes[tc_sid(k, n)] = site }
}

// A place in an err's trace: "lexer.mara:12:37 in digit".
tc_err_place :: proc(k: ^TC, n: Tree_Id) -> string {
    place := span_location(tree_span(k.t, n))
    return fmt.tprintf("%s in %s", place, scope_display_name(k.body)) if k.body != nil else place
}

// An expression checked, used at `t` (tc_settle).
tc_check_at :: proc(k: ^TC, n: Tree_Id, t: Type) -> Type {
    r := tc_check(k, n)
    tc_settle(k, n, t)
    return r
}

tc_expr_impl :: proc(k: ^TC, n: Tree_Id) -> Type {
    t := k.t
    span := tree_span(t, n)
    #partial switch t.tag[n] {
    case .Number:
        return tc_number(k, n)
    case .String:
        text := token_text(build_tokens[t.main[n]])
        return type_text_list(len(text), Type_Utf8{})
    case .Char:
        return Type_Utf8{}
    case .True, .False:
        return Type_Bool{}
    case .Paren:
        return tc_check(k, Tree_Id(t.a[n]))
    case .Big_Endian:
        // (A read of bytes, big-endian: as the read; where it is viewed, the flag.)
        return tc_check(k, Tree_Id(t.a[n]))
    case .Ident:
        return tc_ident(k, n)
    case .Unary:
        // (`&x.f()`: f's receiver addressed — `f(&x)`.)
        if m := Tree_Id(k.t.a[n]); build_tokens[k.t.main[n]].kind == .Ampersand && k.t.tag[m] == .Method_Call {
            return tc_call(k, m, addressed = n)
        }
        return tc_unary(k, n)
    case .Deref:
        return tc_deref(k, n)
    case .Binary:
        return tc_binary(k, n)
    case .In_Range:
        return tc_in_range(k, n)
    case .Call, .Method_Call:
        return tc_call(k, n)
    case .Assert:
        return tc_assert(k, n)
    case .Take:
        return tc_take(k, n)
    case .Type_Name:
        // (A name written where a type's argument goes, standing for a value.)
        return tc_ident(k, n)
    case .Hash_Name:
        return tc_hash_name(k, n)
    case .Self:
        return tc_self(k, n)
    case .Size_Of:
        return tc_size_of(k, n)
    case .If_Expr:
        return tc_if_expr(k, n)
    case .Try:
        return tc_try(k, n)
    case .Dot_Ident:
        if tc_sid(k, n) in k.annot.dot_bases { return tc_field(k, n) }
        name := tc_text(Token_Id(k.t.a[n]))
        hint := k.hint
        k.hint = nil
        et, _, found := tc_variant_ident(k, name, hint, true, span)
        if !found {
            tc_error(k, span, TYPE_VISIBLE_ENUM_UNION_VARIANT, name)
            return Type_Error{}
        }
        if et == nil { return Type_Error{} }
        tc_set_ref(k, n, {variant_decl(et, name), .Variant})
        tc_variant_built(k, n, et, name)
        return et
    case .Field:
        return tc_field(k, n)
    case .Literal, .Broadcast:   // (`all v`: `{all v}`)
        return tc_literal(k, n)
    case .Index:
        return tc_index(k, n)
    case .Slice:
        return tc_slice(k, n)
    case .Array:
        return tc_array_literal(k, n)
    }
    tc_unsupported(k, n, "this expression")
    return Type_Error{}
}

// A number: untyped, its width its use's.
tc_number :: proc(k: ^TC, n: Tree_Id) -> Type {
    return Type_Infer_Float{} if number_text_is_float(token_text(build_tokens[k.t.main[n]])) else Type_Infer_Int{}
}

// What a use takes a value at, where the value's width is the use's to
// decide (tc_open_node): a number, a constant's name, `void`, an operation
// of such, an array literal of such (or a slice of one), an if of such —
// typed `t`, and what it is made of with it. (`t` a binding's open width: as the binding settles,
// graph_settled.)
tc_settle :: proc(k: ^TC, n: Tree_Id, t: Type) {
    if n == 0 || t == nil || tc_open(t) || !tc_open_node(k, n) { return }
    tr := k.t
    t := t
    // (An array literal a slice takes — `f([1, 2, 3])`, `a[0:2] = [9, 9]` —
    // is an array the slice views: of its elements, as many as it has.)
    if tr.tag[n] == .Array {
        if sl, to_slice := distinct_base(t).(^Type_Slice); to_slice {
            t = type_fixed_array(len(tree_list(tr, tr.a[n])), sl.elem)
        }
    }
    tc_set_type(k, n, t)
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
        } else if pa, is_list := distinct_base(t).(^Type_Partial_Array); is_list {
            // (Into a list, `[8]u8 = [1, 2, 3]`: its items at the list's
            // element type, as a fixed array's are.)
            for e in tree_list(tr, tr.a[n]) { tc_settle(k, e, pa.elem) }
        }
    case .Slice:
        tc_settle(k, Tree_Id(tr.a[n]), t)   // (`[1, 2, 3][:]`: the array it views, of the slice's elements)
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

// An element type no use has decided yet: a width's, or an array's of
// such (`[[1, 2], [3, 4]]`, its items' arrays of open numbers).
tc_open_elems :: proc(t: Type) -> bool {
    if fa, is_array := t.(^Type_Fixed_Array); is_array { return tc_open_elems(fa.elem) }
    return tc_open(t)
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
        if fa, is_array := t.(^Type_Fixed_Array); is_array { return tc_open_elems(fa.elem) }
        return k.t.tag[n] == .If_Expr && tc_open(t)
    case .Slice:
        sl, is_slice := t.(^Type_Slice)
        return is_slice && tc_open(sl.elem) && tc_open_node(k, Tree_Id(k.t.a[n]))
    }
    return false
}

tc_ident :: proc(k: ^TC, n: Tree_Id) -> Type {
    name := tc_name(k, n)
    span := tree_span(k.t, n)
    hint := k.hint
    k.hint = nil
    // (A variant of the enum expected, first.)
    if hint != nil {
        if et, _, found := tc_variant_ident(k, name, hint, false, span); found {
            if et == nil { return Type_Error{} }
            tc_set_ref(k, n, {variant_decl(et, name), .Variant})
            tc_variant_built(k, n, et, name)
            return et
        }
    }
    // (What it refers to — the resolver's — and what that means now: a
    // constant not checked yet is checked here, by its use.)
    ref := k.rs.refs[n]
    t, ok := tc_ref_type(k, ref, name)
    kc := k.const_at[ref.decl] if ref.kind == .Const else nil
    if ref.kind == .None || kc != nil && !kc.local {
        // (A module's constant two modules have — its own and one it uses,
        // or two it uses — is ambiguous: said so.)
        if !tc_const_unambiguous(k, n, name, span) { return Type_Error{} }
    }
    if ok || kc != nil { tc_set_ref(k, n, ref) }
    // (A generic's size param, `[$N]T`, as a value: the size it was bound
    // to, a constant — untyped, the width its use takes.)
    if ci, is_size := t.(Type_Const_Int); ok && is_size {
        k.annot.known[tc_sid(k, n)] = {i128(ci.value), Type_Infer_Int{}}
        return Type_Infer_Int{}
    }
    if !ok && kc != nil {
        // (Not bound here yet: its value's type — unless it is the value
        // being checked.)
        if kc.visiting || kc.state == .In_Progress {
            tc_error(k, span, TYPE_CONSTANT_DEFINED_ITSELF, name)
            return Type_Error{}
        }
        kc.visiting = true
        ct := tc_check(k, kc.value)
        kc.visiting = false
        return ct
    }
    // (A completion's placeholder: the type its place takes, for the
    // variants of it — completions_at.)
    if !ok && k.annot.complete_hint == nil && strings.contains(name, COMPLETE_HERE) { k.annot.complete_hint = hint }
    if !ok && ref.kind == .None {
        // (A variant's name by itself, naming nothing else: the one enum in
        // sight with that variant — `mode := help`.)
        if et, _, found := tc_variant_ident(k, name, nil, true, span, bare = true); found {
            if et == nil { return Type_Error{} }   // (two enums have it: said so)
            tc_set_ref(k, n, {variant_decl(et, name), .Variant})
            tc_variant_built(k, n, et, name)
            return et
        }
    }
    if !ok {
        // (A type named as a value: said so.)
        if _, is_template := tc_template(k, ref); ref.kind == .Type && !is_template {
            tc_error(k, span, TYPE_TYPE_VALUE_DID_MEAN, name, name)
        } else {
            tc_unresolved(k, k.rs.misses[n] or_else {}, span, name, TYPE_UNDEFINED_IDENTIFIER)
        }
        return Type_Error{}
    }
    return t
}

// (`of`: the operand in place of its own — a method call's receiver, where
// the `&` is written around the call.)
tc_unary :: proc(k: ^TC, n: Tree_Id, of := Tree_Id(0)) -> Type {
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
    ot := tc_check(k, operand)
    t: Type
    #partial switch op {
    case .Minus, .Wrap_Minus:
        t = ot
        if wrapping {
            if !is_wrap_operand(ot) {
                tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER_UNARY, type_name(ot))
                return Type_Error{}
            }
        } else if own, is_own := own_number(ot); is_own {
            // (A type of its own over a number negates as its base does.)
            if _, kind, _ := numeric_info(distinct_base(own)); kind == .Unsigned {
                tc_error(k, span, TYPE_CANNOT_NEGATE_UNSIGNED, type_name(ot))
            }
        } else if !is_numeric(ot) {
            // (`overload -`: a function of the one operand, when one fits.)
            if callee := tc_unary_overload(k, ot, tr.main[n]); callee != nil {
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
        if !is_condition_type(ot) { tc_not_condition(k, span, ot, TYPE_CANNOT_APPLY, type_name(ot)) }
        t = Type_Bool{}
    case .Tilde:
        if !is_integer(distinct_base(ot)) && !is_any(ot) && !is_utf8_type(ot) { tc_error(k, span, TYPE_CANNOT_APPLY_REQUIRES_INTEGER_TYPE, type_name(ot)) }
        t = ot
    case .Ampersand:
        // (A param that is a pointer, its address taken: the pointer itself
        // meant — `files + name` with `files: ^[]Path`. Said so, and nothing
        // more of it: an append on `^^[]Path` would only say that again.)
        if p := tc_unparen(k, operand); tr.tag[p] == .Ident && k.rs.refs[p].kind == .Param {
            if _, is_ptr := distinct_base(ot).(^Type_Ptr); is_ptr {
                name := tc_name(k, p)
                tc_error(k, span, TYPE_ADDRESS_OF_POINTER_PARAMETER, name, type_name(ot), name, name)
                return Type_Error{}
            }
        }
        // (An address of an immutable param's storage, of a constant's: what
        // it would let be written can't be.)
        if pname, immutable := tc_write_root_param(k, operand); immutable {
            tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_IMMUTABLE_PARAMETER, pname)
        } else if p := tc_unparen(k, operand); tr.tag[p] == .Ident && k.rs.refs[p].kind == .Param {
            // (A param held as its argument has no storage to point at.)
            tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_PARAMETER, tc_name(k, p), tc_name(k, p))
        }
        if cname, is_const := tc_write_root_const(k, operand); is_const { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_CONSTANT, cname) }
        if tr.tag[operand] == .String { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_STRING_LITERAL) }
        // (A part of a value — an if's, a literal's — is no storage; a
        // slice builds a header with nowhere to point.)
        #partial switch tr.tag[tc_access_root(k, operand)] {
        case .If_Expr, .Array, .Literal: tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_EXPRESSION)
        }
        if tr.tag[tc_unparen(k, operand)] == .Slice { tc_error(k, span, TYPE_CANNOT_TAKE_ADDRESS_SLICE_TEMP) }
        t = type_ptr(ot)
    case:
        tc_unsupported(k, n, "this unary operator")
        return Type_Error{}
    }
    return t
}

tc_deref :: proc(k: ^TC, n: Tree_Id) -> Type {
    span := tree_span(k.t, n)
    ot := tc_check(k, Tree_Id(k.t.a[n]))
    if p, ok := distinct_base(ot).(^Type_Ptr); ok { return p.elem }   // (through a type of its own, another name, too)
    // (A `^` no one wrote, under a target: `f().n = v`, f giving no pointer.)
    if k.t.b[n] == 0 && !is_any(ot) {
        tc_error(k, span, TYPE_ASSIGN_TO_RESULT)
        return Type_Error{}
    }
    if !is_any(ot) { tc_error(k, span, TYPE_CANNOT_DEREFERENCE_NON_POINTER_TYPE, type_name(ot)) }
    return Type_Error{}
}

// A binary operation: each side at the type the operation works in; `and` /
// `or` short-circuit.
tc_binary :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    return tc_binary_op(k, n, build_tokens[tr.main[n]].kind, tree_span(tr, n), Tree_Id(tr.a[n]), Tree_Id(tr.b[n]))
}

// `x in lo..hi`: `x >= lo and x < hi` — `not in`, its negation — x walked
// twice, each part at the `in`.
TC_In_Range :: struct {
    value, lo, hi: Tree_Id,
    span:          Span,
    includes_end:  bool,   // written `..`: x <= hi; `:`: x < hi
}

// `(x + a) + b`, `+` a join both times (mara.core's join, join_item): the
// left one's result is a temporary nothing else sees, so b is appended into
// it in place — the call is the add `&it + b` would make, the left built
// into its result (Built_Into: lw_join_in_place). A chain then builds one
// list, copying x once.
tc_note_join_in_place :: proc(k: ^TC, at, left, right: Tree_Id, callee: ^Type_Scope, lt, rt: Type, span: Span) {
    if at == 0 || !is_core_join(callee) { return }
    l := tc_unparen(k, left)
    if k.t.tag[l] != .Binary { return }
    // (The left a join, or a join onto a join, in place itself.)
    given := k.annot.args[tc_sid(k, l)] or_else nil
    in_place := len(given) == 2 && given[0].kind == .Built_Into
    if lc := tc_callee(k, l); !in_place && (lc == nil || !is_core_join(lc)) { return }
    if add, ok := tc_operator_overload(k, .Plus, type_ptr(lt), rt, span); ok && !is_core_join(add) {
        tc_set_callee(k, at, add)
        tc_set_args(k, at, {{left, .Built_Into, -1}, {right, .Written, -1}})
    }
}

// Whether a fun is one of mara.core's appends, `&list + x`: they give
// nothing back.
is_core_append :: proc(f: ^Type_Scope) -> bool {
    if f == nil || f.home_package != "mara.core" { return false }
    switch f.source_name if f.source_name != "" else f.name {
    case "utf8_add", "utf8_add_item", "slice_add", "slice_add_item": return true
    }
    // (A generic one's instance: by its name, as is_core_join.)
    return strings.has_prefix(f.name, "mara_core_slice_add__") || strings.has_prefix(f.name, "mara_core_slice_add_item__")
}

// Whether a fun is an instance of mara.core's join or join_item.
is_core_join :: proc(f: ^Type_Scope) -> bool {
    if f == nil || f.home_package != "mara.core" { return false }
    return strings.has_prefix(f.name, "mara_core_join__") || strings.has_prefix(f.name, "mara_core_join_item__")
}

tc_in_range :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    lo, hi := tree_pair(tr, n)
    if hi == 0 { return tc_in_items(k, n, Tree_Id(tr.a[n]), lo, span) }
    rng := TC_In_Range{value = Tree_Id(tr.a[n]), lo = lo, hi = hi, span = span, includes_end = range_includes_end(tr, n)}
    if build_tokens[tr.main[n]].kind != .Not { return tc_binary_op(k, 0, .And, span, 0, 0, &rng) }
    ot := tc_binary_op(k, 0, .And, span, 0, 0, &rng)
    if _, is_bool := ot.(Type_Bool); !is_bool && !is_any(ot) { tc_error(k, span, TYPE_CANNOT_APPLY, type_name(ot)) }
    return Type_Bool{}
}

// `x in xs` (no `..`): whether some item of xs is x — the `overload in`
// (mara.core's includes), called with xs, then x; `not in`, its negation
// (lw_in_items). Through one pointer, as `for` sees: `x in files`, files a
// `^[]T`.
tc_in_items :: proc(k: ^TC, n, value, coll: Tree_Id, span: Span) -> Type {
    vt := tc_check(k, value)
    ct := tc_check(k, coll)
    seen := ct
    if pt, is_ptr := distinct_base(ct).(^Type_Ptr); is_ptr && loop_elem(pt.elem) != nil { seen = pt.elem }
    if is_any(vt) || is_any(seen) { return Type_Bool{} }   // (said so already)
    // (Said at the `in`, not in includes: an item `==` can't compare with x.)
    if elem := loop_elem(seen); elem != nil && !tc_can_equal(k, elem, vt, span) {
        tc_error(k, span, TYPE_IN_ITEM_TYPE, type_name(solidify_type(vt)), type_name(solidify_type(elem)))
        return Type_Error{}
    }
    callee, found := tc_operator_overload(k, .In, seen, vt, span)
    if !found {
        tc_error(k, span, TYPE_IN_NEEDS_ITEMS, type_name(solidify_type(ct)))
        return Type_Error{}
    }
    tc_set_callee(k, n, callee)
    tc_set_args(k, n, {{coll, .Written, -1}, {value, .Written, -1}})
    tc_settle(k, coll, callee.params[0].type_)
    tc_settle(k, value, callee.params[1].type_)
    return Type_Bool{}
}

// Whether `a == b` compares an a with a b: numbers (or characters) both, one
// comparable type, or an `overload ==` that takes them (text).
tc_can_equal :: proc(k: ^TC, a, b: Type, span: Span) -> bool {
    if (is_numeric(a) || is_infer(a)) && (is_numeric(b) || is_infer(b)) { return true }
    if is_byte_or_utf8(a) && is_byte_or_utf8(b) { return true }
    if types_equal(distinct_base(a), distinct_base(b)) && is_comparable(a) { return true }
    _, found := tc_operator_overload(k, .Equal_Equal, a, b, span)
    return found
}

is_utf8_type :: proc(t: Type) -> bool {
    _, ok := distinct_base(t).(Type_Utf8)
    return ok
}

// A byte of memory, raw or text: byte, utf8.
is_byte_or_utf8 :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(t) {
    case Type_Byte, Type_Utf8: return true
    }
    return false
}

// A comparison with a byte or utf8 on a side (utf8 is bytes for now — no
// codepoint type yet — and orders as bytes do, unsigned). A number written
// beside one is a byte's value, settled to it; otherwise the other side is
// the same type.
tc_byte_compare :: proc(k: ^TC, span: Span, op: Token_Kind, sides: [2]Tree_Id, types: [2]Type) {
    u := types[0] if is_byte_or_utf8(types[0]) else types[1]
    for t, i in types {
        if is_any(t) { continue }
        if lit, is_int := t.(Type_Infer_Int); is_int && lit.cell == nil {
            if v, known := tc_comptime_int(k, sides[i]); known && (v < 0 || v > 255) {
                tc_error(k, span, TYPE_CONSTANT_OVERFLOWS_RANGE_2, v, type_name(u), 255)
            }
            tc_settle(k, sides[i], u)
        } else if !types_equal(t, u) || !types_equal(u, t) {
            tc_error(k, span, TYPE_CANNOT_COMPARE_USING, type_name(solidify_type(types[0])), type_name(solidify_type(types[1])), op_str(op))
            return
        }
    }
}

// `left op right`, where `span` is: a Binary's, or a compound assignment's
// (`x += v` is `x = x op v`, at the `+=`). `at`: its node, where an operator
// through `overload` is annotated as the call it is.
tc_binary_op :: proc(k: ^TC, at: Tree_Id, tok: Token_Kind, span: Span, left, right: Tree_Id,
                     in_range: ^TC_In_Range = nil) -> Type {
    // (A side: its expression; an `in`'s, its comparison.)
    side_of :: proc(k: ^TC, rng: ^TC_In_Range, i: int, side: Tree_Id) -> Type {
        if rng == nil { return tc_check(k, side) }
        if i == 0 { return tc_binary_op(k, 0, .Greater_Equal, rng.span, rng.value, rng.lo) }
        return tc_binary_op(k, 0, .Less_Equal if rng.includes_end else .Less, rng.span, rng.value, rng.hi)
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
    sides := [2]Tree_Id{left, right}
    // (`x == .B`, `.B != x`: the shorthand's enum or union the other side's —
    // a union's tag's, a value's — that side checked first. So too a name
    // naming nothing, a variant's by itself: `x == B`.)
    shorthand := -1
    if in_range == nil && (op == .Equal_Equal || op == .Not_Equal) {
        for side, i in sides {
            if s := tc_unparen(k, side); tr.tag[s] == .Dot_Ident && tc_sid(k, s) not_in k.annot.dot_bases { shorthand = i }
            if s := tc_unparen(k, side); tr.tag[s] == .Ident && k.rs.refs[s].kind == .None { shorthand = i }
        }
    }
    order := [2]int{1, 0} if shorthand == 0 else [2]int{0, 1}
    for i in order {
        k.hint = hint
        if i == shorthand { k.hint = types[1 - i] }
        types[i] = side_of(k, in_range, i, sides[i])
    }
    lt, rt := types[0], types[1]
    // (A side that failed is said so already: the operation fails with it, no
    // error of its own — `(view + "/") + name` matching an append.)
    _, l_failed := lt.(Type_Error)
    _, r_failed := rt.(Type_Error)
    if l_failed || r_failed { return Type_Error{} }
    and_or := op == .And || op == .Or
    t: Type = Type_Error{}
    // (A type of its own over a number takes its base's operators: tc_own_op.)
    _, l_own := own_number(lt)
    _, r_own := own_number(rt)
    if !and_or && (l_own || r_own) {
        return tc_own_op(k, op, wrapping, span, left, right, lt, rt)
    }
    // (utf8 takes arithmetic and bitwise operators as u8 does: tc_utf8_op —
    // with a number or utf8 on the other side; `&buf + ch` is an append.)
    scalar :: proc(t: Type) -> bool { return is_utf8_type(t) || is_numeric(t) || is_any(t) }
    if !and_or && !is_comparison_op(op) && in_range == nil && (is_utf8_type(lt) || is_utf8_type(rt)) && scalar(lt) && scalar(rt) {
        return tc_utf8_op(k, op, span, left, right, lt, rt)
    }
    if wrapping && (!is_wrap_operand(lt) || !is_wrap_operand(rt)) {
        tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER, op_str(op), type_name(lt), type_name(rt))
        return Type_Error{}
    }
    // (An operand no number: an `overload`'s function, when one fits.)
    if !and_or && (!is_numeric(lt) || !is_numeric(rt)) {
        if callee, found := tc_operator_overload(k, op, lt, rt, span); found {
            tc_set_callee(k, at, callee)
            tc_set_args(k, at, {{left, .Written, -1}, {right, .Written, -1}})
            tc_settle(k, left, callee.params[0].type_)
            tc_settle(k, right, callee.params[1].type_)
            tc_note_join_in_place(k, at, left, right, callee, lt, rt, span)
            return fn_primary_return(callee)
        }
    }
    // (A byte is memory, not a number: arithmetic and bitwise operators
    // take its value converted, `u8(b) + 1`. Comparisons take it as it is.)
    if !and_or && !is_comparison_op(op) && in_range == nil {
        for side, i in ([2]Tree_Id{left, right}) {
            if _, is_byte := distinct_base(lt if i == 0 else rt).(Type_Byte); is_byte {
                written := tc_written(k, side)
                tc_error(k, span, TYPE_BYTE_NOT_NUMBER, written, op_str(op), written)
                return Type_Error{}
            }
        }
    }
    #partial switch op {
    case .And, .Or:
        word := "and" if op == .And else "or"
        if !is_condition_type(lt) {
            tc_not_condition(k, span, lt, TYPE_LEFT_OPERAND_BOOL, word, type_name(lt))
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
        if !is_condition_type(rt) { tc_not_condition(k, span, rt, TYPE_RIGHT_OPERAND_BOOL, word, type_name(rt)) }
        t = Type_Bool{}
    case .Equal_Equal, .Not_Equal:
        // (Two of one type: numbers at one width, as arithmetic takes them;
        // anything else the same type — no conversion.)
        if is_byte_or_utf8(lt) || is_byte_or_utf8(rt) {
            tc_byte_compare(k, span, op, sides, types)
        } else if !is_any(lt) && !is_any(rt) {
            if !is_comparable(lt) || !is_comparable(rt) {
                tc_error(k, span, TYPE_CANNOT_COMPARE_USING, type_name(lt), type_name(rt), op_str(op))
            } else if is_numeric(lt) && is_numeric(rt) {
                promote_numeric(k.c, lt, rt, span)
            } else if !types_equal(lt, rt) || !types_equal(rt, lt) {
                tc_error(k, span, TYPE_CANNOT_COMPARE_USING, type_name(solidify_type(lt)), type_name(solidify_type(rt)), op_str(op))
            }
        }
        t = Type_Bool{}
    case .Less, .Less_Equal, .Greater, .Greater_Equal:
        if is_utf8_type(lt) || is_utf8_type(rt) {
            tc_byte_compare(k, span, op, sides, types)
        } else {
            if !is_numeric(lt) { tc_error(k, span, TYPE_LEFT_OPERAND_COMPARISON_NUMERIC, type_name(lt)) }
            if !is_numeric(rt) { tc_error(k, span, TYPE_RIGHT_OPERAND_COMPARISON_NUMERIC, type_name(rt)) }
            if is_numeric(lt) && is_numeric(rt) { promote_numeric(k.c, lt, rt, span) }
        }
        t = Type_Bool{}
    case .Plus:
        if !is_numeric(lt) || !is_numeric(rt) {
            // (`&buf + x` on a fixed array: no overload is missing — it can't grow.)
            if hint := tc_partial_hint(k, left, lt); hint != "" {
                tc_error(k, span, TYPE_APPEND_TO_FIXED_ARRAY, type_name(lt), type_name(rt), hint)
                return Type_Error{}
            }
            // (`&list + a + b`: the left an append, which gives nothing back.)
            if l := tc_unparen(k, left); tr.tag[l] == .Binary && is_core_append(tc_callee(k, l)) {
                target, item := Tree_Id(tr.a[l]), Tree_Id(tr.b[l])
                if is_numeric(rt) && is_numeric(tc_node_type(k, item)) {
                    tc_error(k, span, TYPE_APPEND_CHAIN_SUM, tc_written(k, l), tc_written(k, right),
                             tc_written(k, target), tc_written(k, item), tc_written(k, right))
                } else {
                    tc_error(k, span, TYPE_APPEND_CHAIN, tc_written(k, l), tc_written(k, right))
                }
                return Type_Error{}
            }
            // (A view joined: it has no room to make the new one of.)
            if is_slice_type(lt) {
                tc_error(k, span, TYPE_JOIN_VIEW, type_name(lt))
                return Type_Error{}
            }
            // (`&p + x`, p a pointer to a list already: p itself meant.)
            if pt, is_ptr := distinct_base(lt).(^Type_Ptr); is_ptr {
                if inner, to_ptr := distinct_base(pt.elem).(^Type_Ptr); to_ptr && loop_elem(inner.elem) != nil {
                    target := tc_written(k, tc_unparen(k, left))
                    name := target[1:] if strings.has_prefix(target, "&") else target
                    tc_error(k, span, TYPE_APPEND_POINTER_TO_POINTER, target, type_name(lt), name, type_name(pt.elem), name, tc_written(k, right))
                    return Type_Error{}
                }
            }
            // (A view onto a list of lists: an item takes it, not the list.)
            if pt, is_ptr := distinct_base(lt).(^Type_Ptr); is_ptr {
                if items := loop_elem(pt.elem); items != nil && arg_incompatible(items, rt) && !types_incompatible(items, rt) {
                    target, item := tc_written(k, tc_unparen(k, left)), tc_written(k, right)
                    list := target[1:] if strings.has_prefix(target, "&") else fmt.tprintf("%s^", target)
                    tc_error(k, span, TYPE_APPEND_VIEW_TO_LISTS, target, item, type_name(items), list, item, target, item)
                    return Type_Error{}
                }
            }
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
        // (A known count past the value's bits, or negative: said so now.)
        if op == .Shift_Left || op == .Shift_Right {
            bits := 64
            if nt, is_num := unwrap_alias(t).(Type_Numeric); is_num { bits = int(nt.bits) }
            if count, known := tc_comptime_int(k, right); known && (count < 0 || count >= i64(bits)) {
                tc_error(k, span, TYPE_SHIFT_COUNT_CONST, count, bits - 1, type_name(t))
            }
        }
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

// An operation on a type of its own over a number (`Count :: i32`), as on its
// base (tc_binary_op): the other side the same type, or a literal, which
// takes it. The result that type, a comparison's bool. A plain number beside
// it is converted first, as with any two types: `c + Count(n)`, `i32(c) + n`.
@(private="file")
tc_own_op :: proc(k: ^TC, op: Token_Kind, wrapping: bool, span: Span, left, right: Tree_Id, lt, rt: Type) -> Type {
    own, l_own := own_number(lt)
    if !l_own { own, _ = own_number(rt) }
    base := distinct_base(own)
    for side in ([2]Type{lt, rt}) {
        if is_any(side) || (types_equal(own, side) && types_equal(side, own)) { continue }
        tc_error(k, span, TYPE_OWN_NUMBER_OPERAND, op_str(op), type_name(solidify_type(lt)), type_name(solidify_type(rt)),
                 type_name(own), type_name(own), type_name(own), type_name(base))
        return Type_Error{}
    }
    if wrapping && !is_wrap_operand(own) {
        tc_error(k, span, TYPE_WRAPPING_REQUIRES_INTEGER, op_str(op), type_name(lt), type_name(rt))
        return Type_Error{}
    }
    t: Type = own
    #partial switch op {
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
        t = Type_Bool{}
    case .Plus, .Minus, .Star, .Slash, .Modulo:
    case .Ampersand, .Pipe, .Tilde, .Shift_Left, .Shift_Right:
        if !is_integer(base) {
            tc_error(k, span, TYPE_BITWISE_OPERATORS_REQUIRE_INTEGER_OPERANDS, type_name(own))
            return Type_Error{}
        }
        // (A known shift count past its bits, or negative: said so now.)
        if nt, is_num := base.(Type_Numeric); is_num && (op == .Shift_Left || op == .Shift_Right) {
            if count, known := tc_comptime_int(k, right); known && (count < 0 || count >= i64(nt.bits)) {
                tc_error(k, span, TYPE_SHIFT_COUNT_CONST, count, nt.bits - 1, type_name(own))
            }
        }
    case:
        tc_error(k, span, "tc: the operator %v is not supported yet", op)
        return Type_Error{}
    }
    tc_settle(k, left, own)
    tc_settle(k, right, own)
    return t
}

// An arithmetic or bitwise operation on utf8 (tc_binary_op), as on u8: the
// other side utf8 too, or an integer literal, which takes utf8's width; the
// result utf8. Any other integer is converted first, as anywhere (no
// widening): `c - '0'` is utf8, `i64(c - '0')` a number.
@(private="file")
tc_utf8_op :: proc(k: ^TC, op: Token_Kind, span: Span, left, right: Tree_Id, lt, rt: Type) -> Type {
    for side in ([2]Type{lt, rt}) {
        _, float_lit := resolve_infer(side).(Type_Infer_Float)
        if is_utf8_type(side) || is_any(side) || (is_infer(resolve_infer(side)) && !float_lit) { continue }
        tc_error(k, span, TYPE_UTF8_OPERAND, op_str(op), type_name(lt), type_name(rt))
        return Type_Error{}
    }
    t := lt if is_utf8_type(lt) else rt
    if !is_utf8_type(lt) || !is_utf8_type(rt) { t = promote_numeric(k.c, lt, rt, span) }
    // (A known shift count past its 8 bits, or negative: said so now.)
    if op == .Shift_Left || op == .Shift_Right {
        if count, known := tc_comptime_int(k, right); known && (count < 0 || count >= 8) {
            tc_error(k, span, TYPE_SHIFT_COUNT_CONST, count, 7, type_name(t))
        }
    }
    tc_settle(k, left, t)
    tc_settle(k, right, t)
    return t
}

// --- calls --------------------------------------------------------------------

tc_call :: proc(k: ^TC, n: Tree_Id, addressed := Tree_Id(0)) -> Type {
    several := tc_takes_several(k, n)
    t: Type
    if k.t.tag[n] == .Method_Call {
        t = tc_method_call(k, n, addressed)
    } else {
        saved := k.recv
        k.recv = {}
        defer k.recv = saved
        t = tc_call_core(k, n, tc_name(k, n), tree_list(k.t, k.t.a[n]))
    }
    if !several { tc_one_value(k, n, len(tc_call_returns(k, n))) }
    // (`E.from_text(s)` gives E's variant written `= 0` when s names none: E
    // must have one.)
    if callee := tc_callee(k, n); callee != nil {
        if ft, from_text := callee.origin.(Origin_From_Text); from_text && ft.enum_.zero_name == "" {
            tc_error(k, tree_span(k.t, n), TYPE_FROM_TEXT_NEEDS_ZERO, callee.name, type_name(fn_result(callee, 0)))
        }
    }
    return t
}

// Whether n is where several results go — a destructure's value, `?`'s
// call, a statement's call (its own check says what's dropped) — as its
// checker said just before checking it (k.several_ok); asked once, at n's
// check's start.
tc_takes_several :: proc(k: ^TC, n: Tree_Id) -> bool {
    ok := k.several_ok == n
    k.several_ok = 0
    return ok
}

// A call's (or a `?`'s) values, `count`, where one value goes: more than one
// is an error — the others would be lost.
tc_one_value :: proc(k: ^TC, n: Tree_Id, count: int) {
    if count <= 1 { return }
    example := fmt.tprintf("%s(…)", tc_call_name(k, n))
    if k.t.tag[n] == .Try { example = fmt.tprintf("%s(…)?", tc_call_name(k, tc_unparen(k, Tree_Id(k.t.a[n])))) }
    tc_error(k, tree_span(k.t, n), TYPE_MULTI_RETURN_AS_ONE, count, example)
}

// What a call's name refers to: a call's own; a method call's, its method
// not found on the receiver — `x.f(a)`, the fun `f(x, a)` — its name's.
tc_callee_ref :: proc(k: ^TC, n: Tree_Id) -> Ref {
    if k.t.tag[n] == .Method_Call { return k.rs.token_refs[method_view(k.t, n).name] or_else {} }
    return k.rs.refs[n]
}

// A call of `name` on `args` — or, resolved by its qualifier (a method, a
// module's fun: `qual`; a module's dispatch: `qual_dispatch`), of that.
tc_call_core :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id,
                     qual: ^Type_Scope = nil, qual_dispatch: []TC_Member = nil) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    if len(qual_dispatch) > 0 { return tc_dispatch_call(k, n, name, qual_dispatch, args) }
    if qual == nil {
        if t, is_builtin := tc_builtin(k, n, name, args); is_builtin {
            tc_set_ref(k, n, {kind = .Builtin})
            k.annot.forms[tc_sid(k, n)] = .Builtin
            return t
        }
        if groups := resolve_dispatches(k.rs, tr.main[n], name); len(groups) > 0 {
            return tc_dispatch_call(k, n, name, tc_dispatch_members(k, groups), args)
        }
        if tmpl, is_template := tc_template(k, tc_callee_ref(k, n)); is_template && tr.tag[tmpl.node] != .Union_Def {
            return tc_generic_call(k, n, name, tmpl, args)
        }
    }
    ref := tc_callee_ref(k, n)
    ft_raw, found := tc_ref_type(k, ref, name)
    if qual != nil { ft_raw, found = qual, true }
    if !found {
        // (A union's variant built by its params: `Rect(5)` where a Shape goes.)
        if ut, _ := tc_variant_union(k, name); ut != nil { return tc_variant_call(k, n, ut, name, args) }
        // (A fun two modules it uses have: ambiguous.)
        if qual == nil && ref.kind == .None {
            if owners := resolve_fun_owners(k.rs, tr.main[n], name); owners != nil {
                tc_error(k, span, TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED, name, strings.join(owners[:], ", ", context.temp_allocator), owners[0], name)
                for a in args { tc_check(k, a) }
                return Type_Error{}
            }
        }
        if owner := resolve_foreign_owner(k.rs, tr.main[n], name); owner != "" {
            tc_error(k, span, TYPE_FOREIGN_FUN_PRIVATE, name, owner)
        } else {
            tc_error(k, span, TYPE_UNDEFINED_FUNCTION, name)
        }
        for a in args { tc_check(k, a) }
        return Type_Error{}
    }
    if dt, is_distinct := ft_raw.(^Type_Distinct); is_distinct {
        tc_set_ref(k, n, {type_decl(dt), .Type})
        k.annot.forms[tc_sid(k, n)] = .Conversion
        return tc_distinct_conversion(k, n, name, dt, args)
    }
    if et, is_enum := ft_raw.(^Type_Enum); is_enum && !et.is_error_kind && !et.is_synthetic {
        return tc_enum_number(k, n, name, et, args)
    }
    ft, is_scope := ft_raw.(^Type_Scope)
    // (A fun written in the program, or a foreign one; else a fun's value — a
    // name no declared fun has, holding one — called through it.)
    indirect := is_scope && qual == nil && ft.kind == .Fun && tc_is_variable(ref) && ft.decl == 0
    if !is_scope {
        tc_error(k, span, TYPE_FUNCTION, name)
        return Type_Error{}
    }
    // (A fun two modules it uses have: ambiguous.)
    if qual == nil && ft.name != "" {
        if owners := resolve_fun_owners(k.rs, tr.main[n], name); owners != nil {
            tc_error(k, span, TYPE_FUNCTION_AMBIGUOUS_DEFINED_USE_QUALIFIED, name, strings.join(owners[:], ", ", context.temp_allocator), owners[0], name)
            return Type_Error{}
        }
    }
    // (No source, and called: a foreign fun, an enum's from_text.)
    _, from_text := ft.origin.(Origin_From_Text)
    _, variant_text := ft.origin.(Origin_Variant_Text)
    _, err_runtime := ft.origin.(Origin_Err_Runtime)
    if ft.is_module || !indirect && ft.node == 0 && ft.calling_conv != .C && !from_text && !variant_text && !err_runtime {
        tc_unsupported(k, n, "a call of this")
        return Type_Error{}
    }
    is_struct := ft.kind == .Struct
    // (`Foo(args) {f = v}`: its fields written once it is constructed.)
    overrides := Tree_Id(tr.b[n]) if tr.tag[n] == .Call else method_view(tr, n).overrides
    if overrides != 0 && !is_struct { tc_error(k, span, TYPE_FIELD_OVERRIDE_BLOCK_ONLY_VALID, name) }
    tc_set_callee(k, n, ft)
    tc_set_ref(k, n, ref if indirect else Ref{ft.decl, .Type if is_struct else .Fun})
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
        default_arg :: proc(k: ^TC, p: Struct_Type_Field, ft: ^Type_Scope, at: Span) -> TC_Arg {
            if k.t.tag[p.default_node] == .Hash_Name { return TC_Arg{p.default_node, at, nil} }
            return TC_Arg{p.default_node, {}, p.default_slot}
        }
        for a, i in args {
            // (`_`: its param's default — said so when it has none.)
            if tr.tag[a] == .Ident && tc_name(k, a) == "_" && i < len(ft.params) {
                if ft.params[i].default_node == 0 {
                    tc_error(k, span, TYPE_ARGUMENT_REQUIRES_DEFAULT_VALUE_PARAMETER, i + 1, name, ft.params[i].name)
                } else {
                    append(&items, default_arg(k, ft.params[i], ft, tree_span(tr, a)))
                    continue
                }
            }
            append(&items, TC_Arg{a, {}, nil})
        }
        for i := len(args); i < len(ft.params); i += 1 { append(&items, default_arg(k, ft.params[i], ft, span)) }
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
        a := item.node
        pt := ft.params[i].type_
        k.hint = pt
        at: Type
        if item.at != {} {
            at = tc_hash_name(k, a)
        } else if slot, is_slot := item.slot.?; is_slot {
            at = tc_tuple_default(k, a, slot, span)
        } else {
            at = k.recv.t if a == k.recv.node else tc_check(k, a)
        }
        // (Bytes read as an array param: `buf[off]`, `buf[lo:hi]` — its size
        // the param's.)
        reinterpret := false
        if _, to_array := pt.(^Type_Fixed_Array); to_array {
            if m, _ := tc_byte_node(k, a); tc_byte_index(k, a) || k.t.tag[m] == .Slice && is_byte_buffer(at) {
                reinterpret = tc_check_byte_flow(k, pt, a, at, span) == .Read
            }
        }
        // (A method's receiver of a distinct struct — `distinct P` — is a P
        // to it: the struct's methods are its too.)
        own := a == k.recv.node && a != 0 && tc_own_receiver(at, pt)
        if !reinterpret && !own && !coerce_deferred(k.c, at, pt, span) && arg_incompatible(pt, at) {
            clause := ""
            if an := tc_diag_name(k, a); an != "" { clause = fmt.tprintf(" ('%s')", an) }
            tc_error(k, span, TYPE_ARGUMENT_EXPECTED, i + 1, clause, name, ft.params[i].name, type_name(pt), type_name(at), tc_partial_hint(k, a, at, pt))
        }
        // (A runtime string into a `cstring` param: `cstring(s)`, written —
        // the copy and the terminator seen. A literal, or a constant one,
        // passes free: rodata carries the \0. `void`, a null: a C function's
        // none.)
        if is_cstring(pt) && !is_cstring(at) && !tc_text_literal(k, a) && !tc_void_arg(k, a) {
            tc_error(k, span, TYPE_CSTRING_ARG_EXPLICIT)
        }
        tc_value_at(k, a, at, pt, span)
    }
    if is_struct {
        if overrides != 0 { tc_literal_fields(k, overrides, tree_list(tr, tr.b[overrides]), &ft.sd) }
        return ft
    }
    return fn_primary_return(ft)
}

// A literal that doesn't fit the type it is used at.
// A value at the type its use takes it at, `t`: one of no width of its own
// settled to it (tc_settle), a literal's range checked.
tc_value_at :: proc(k: ^TC, n: Tree_Id, vt, t: Type, span: Span) {
    tc_flow_use(k, vt, t, span)
    if is_infer(vt) { tc_literal_overflow(k, n, t, span) }
    // (A fixed array into a list, `ints : [2]i64 = [1, 2, 3]`: its items
    // must fit in the list's room, known now.)
    if pa, to_list := distinct_base(t).(^Type_Partial_Array); to_list && pa.text == 0 {
        if fa, from_fixed := distinct_base(vt).(^Type_Fixed_Array); from_fixed && fa.size > pa.size {
            tc_error(k, span, TYPE_ARRAY_PAST_LIST_ROOM, fa.size, type_name(t), pa.size)
        }
    }
    tc_settle(k, n, t)
}

// Every flow is a use of a binding of no written width (unify_infer_concrete):
// its value into a width, a width written into it, a pointer to it where one
// to a width goes — wherever the check that let it through didn't count it
// already (an array literal's element, say).
tc_flow_use :: proc(k: ^TC, vt, t: Type, span: Span) {
    if coerce_deferred_pointee(k.c, vt, t, span) { return }
    if infer_cell_of(vt) != nil {
        _ = coerce_deferred(k.c, vt, t, span)
    } else if infer_cell_of(t) != nil && !is_infer(resolve_infer(vt)) {
        _ = coerce_deferred(k.c, t, vt, span)
    }
}

tc_literal_overflow :: proc(k: ^TC, n: Tree_Id, target: Type, span: Span) {
    if f, i, lit := tc_literal_value(k, n); lit {
        check_value_range(k.c, f, i, target, span)
        return
    }
    // (A constant's name: its value's.)
    if u := tc_unparen(k, n); k.t.tag[u] == .Ident {
        if kc := tc_const_named(k, u); kc != nil { tc_literal_overflow(k, kc.value, target, span) }
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

// `assert(c)`: its condition a bool or an error (is_condition_type).
tc_assert :: proc(k: ^TC, n: Tree_Id) -> Type {
    span := tree_span(k.t, n)
    ct := tc_check(k, Tree_Id(k.t.a[n]))
    if !is_condition_type(ct) { tc_not_condition(k, span, ct, TYPE_CONDITION_BOOL, type_name(ct)) }
    return Type_Void{}
}

// `#self`: the address of what a constructor builds (Self, its place) —
// only a constructor's frame has one.
tc_self :: proc(k: ^TC, n: Tree_Id) -> Type {
    f := k.body
    if f == nil || f.kind != .Struct {
        tc_error(k, tree_span(k.t, n), TYPE_SELF_ONLY_LEGAL_INSIDE_STRUCT)
        return Type_Error{}
    }
    return type_ptr(f)
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
tc_builtin :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id) -> (Type, bool) {
    span := tree_span(k.t, n)
    types := make([dynamic]Type, 0, len(args), context.temp_allocator)
    each :: proc(k: ^TC, args: []Tree_Id, types: ^[dynamic]Type) {
        for a in args { append(types, tc_arg(k, a)) }
    }
    switch name {
    case "print":
        each(k, args, &types)
        for a, i in args { tc_is_value(k, a, types[i], tree_span(k.t, a), printed = true) }
        // (Untyped numbers printed at their default width, an operation of
        // them all at one: `print(1.5 / 2)` an f64 division — each left to
        // its own, 2 was an i64 and the division had no width.)
        for a, i in args { tc_settle_untyped(k, a, types[i], nil) }
        tc_print_format(k, args, span)
        return Type_Error{}, true
    case "crash":
        if len(args) > 1 {
            tc_error(k, span, TYPE_CRASH_EXPECTS_ARGUMENTS, len(args))
        } else {
            each(k, args, &types)
        }
        return Type_Error{}, true
    case "int", "uint":
        if len(args) != 1 {
            tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
            return Type_Error{}, true
        }
        each(k, args, &types)
        tc_error(k, span, TYPE_TYPE_INT_RESERVED_USE_I64 if name == "int" else TYPE_TYPE_UINT_RESERVED_USE_U64)
        return Type_Error{}, true
    }
    target, is_cast := cast_result_type(name)
    if !is_cast { return tc_builtin_more(k, n, name, args) }
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        return Type_Error{}, true
    }
    each(k, args, &types)
    tc_settle_untyped(k, args[0], types[0], target)
    // (A known float made an int it doesn't fit: said so now.)
    if nt, to_int := target.(Type_Numeric); to_int && nt.kind != .Float && nt.bits > 0 {
        _, from_kind, from_num := numeric_info(types[0])
        _, from_f64 := distinct_base(resolve_infer(types[0])).(Type_F64)
        _, from_open := resolve_infer(types[0]).(Type_Infer_Float)
        if from_f64 || from_open || from_num && from_kind == .Float {
            if x, known := tc_comptime_float(k, args[0]); known && !float_fits_int(x, int(nt.bits), nt.kind == .Unsigned) {
                tc_error(k, span, TYPE_FLOAT_DOESNT_FIT_CONST, x, name)
            }
        }
    }
    // (One that changes nothing is said to.)
    if cast_target_same_as_operand(types[0], target) {
        operand := tc_diag_name(k, args[0])
        if operand == "" { operand = "the operand" }
        check_warning(k.c, span, WARN_REDUNDANT_CAST, name, operand, name)
    }
    return target, true
}

// An untyped number (or an operation of them), checked as `t`, given its
// width where nothing else gives one — print's arguments, a cast's: the
// cast's own type when it's of the number's kind (`u64(0xFFFF…)`,
// `f32(1.5 / 2)`), else the number's default (`f32(3 / 2)` divides ints).
// A variable of no width written is its uses' to decide: left as it is.
tc_settle_untyped :: proc(k: ^TC, n: Tree_Id, t: Type, target: Type) {
    if !is_infer(t) || infer_cell_of(t) != nil { return }
    at := solidify_type(t)
    _, open_float := resolve_infer(t).(Type_Infer_Float)
    #partial switch v in target {
    case Type_Numeric: if (v.kind == .Float) == open_float { at = target }
    case Type_F64:     if open_float { at = target }
    }
    tc_settle(k, n, at)
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
tc_call_returns :: proc(k: ^TC, n: Tree_Id) -> []Type {
    m := tc_unparen(k, n)
    if !tc_is_call(k, m) { return nil }
    callee := tc_callee(k, m)
    if callee == nil {
        // (Not checked yet: the fun its name names — or an enum's from_text.)
        if t, ok := tc_ref_type(k, tc_callee_ref(k, m), tc_call_name(k, m)); ok { callee, _ = t.(^Type_Scope) }
        if callee == nil { callee = tc_from_text_call(k, m) }
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
    at:   Span,
    slot: Maybe(int),
}

// A param's default that is a slot of its group's one value (`x, y :=
// f()`): f's result there; a value no call of several results, a
// broadcast: the value's.
tc_tuple_default :: proc(k: ^TC, src: Tree_Id, slot: int, span: Span) -> Type {
    k.several_ok = tc_unparen(k, src)   // (each slot its result)
    st := tc_check(k, src)
    k.several_ok = 0
    if _, is_err := st.(Type_Error); is_err { return Type_Error{} }
    if returns := tc_call_returns(k, src); len(returns) > 1 {
        if slot >= len(returns) {
            tc_error(k, span, TYPE_TUPLE_DESTRUCTURE_INDEX_OUT_RANGE, slot, len(returns))
            return Type_Error{}
        }
        return returns[slot]
    }
    return st
}

// `#caller_name`, `#caller_span`: text; `#web`, the targets and
// `#profile_memory` (a `-profile memory` build): a bool.
tc_hash_name :: proc(k: ^TC, n: Tree_Id) -> Type {
    switch tc_text(Token_Id(k.t.a[n])) {
    case "caller_name", "caller_span":
        return Type_Atom{}
    case "web", "native", "windows", "linux", "mac", "profile_memory":
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
    tc_check_at(k, def, t)
}

// The rest of the builtins: print_cstr / print_int / print_float (as print),
// len and cap (of a place — a fixed array's, its size), slice_from_ptr,
// cstring.
tc_builtin_more :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id) -> (Type, bool) {
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
        tc_arg(k, args[0])
        return Type_Error{}, true
    case "len", "cap":
        t := slice_header_width_type
        if len(args) != 1 {
            tc_error(k, span, TYPE_LEN_EXPECTS_ARGUMENT if name == "len" else TYPE_CAP_EXPECTS_ARGUMENT, len(args))
            return t, true
        }
        at := tc_arg(k, args[0])
        if !is_array_type(at) && !is_any(at) {
            tc_error(k, span, TYPE_LEN_REQUIRES_ARRAY_SLICE if name == "len" else TYPE_CAP_REQUIRES_ARRAY_SLICE, type_name(at))
        }
        return t, true
    case "slice_from_ptr":
        t := type_slice(Type_Byte{})
        if len(args) != 2 {
            tc_error(k, span, TYPE_SLICE_PTR_EXPECTS_ARGUMENTS_PTR, len(args))
            return t, true
        }
        pt := tc_arg(k, args[0])
        if _, is_ptr := pt.(^Type_Ptr); !is_ptr && !is_any(pt) {
            tc_error(k, span, TYPE_SLICE_PTR_FIRST_ARGUMENT_POINTER, type_name(pt))
        }
        st := tc_arg(k, args[1])
        tc_settle(k, args[1], slice_header_width_type)
        if !is_numeric(st) && !is_any(st) {
            tc_error(k, span, TYPE_SLICE_PTR_SECOND_ARGUMENT_NUMERIC, type_name(st))
        } else if !coerces_to_slice_width(st) {
            tc_error(k, span, TYPE_SLICE_PTR_SECOND_ARGUMENT_WIDTH, type_name(slice_header_width_type), type_name(st))
        }
        if k.pkg != "os" && k.pkg != "mara.os" {
            if _, known := tc_comptime_int(k, args[1]); !known {
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
        at := tc_arg(k, args[0])
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
tc_size_of :: proc(k: ^TC, n: Tree_Id) -> Type {
    span := tree_span(k.t, n)
    t := tc_type(k, Tree_Id(k.t.a[n]), span)
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
tc_distinct_conversion :: proc(k: ^TC, n: Tree_Id, name: string, dt: ^Type_Distinct, args: []Tree_Id) -> Type {
    span := tree_span(k.t, n)
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        return Type_Error{}
    }
    saved := k.hint
    k.hint = dt.base_type
    at := tc_check(k, args[0])
    k.hint = saved
    // (A pointer to a binding of no written width, its width the base's
    // pointee: `IntPtr(&n)`, as `p : ^i64 = &n`.)
    if coerce_deferred_pointee(k.c, at, dt.base_type, span) { at = dt.base_type }
    // (A list of another room, made one of this: the copy asked for.)
    if from, to := distinct_base(at), distinct_base(dt.base_type); tc_list_resized(from, to) { return dt }
    // (A number of any width, as its base's conversion takes one: `Count(i)`.)
    if _, own := own_number(dt); own && is_numeric(distinct_base(at)) { return dt }
    if !is_any(at) && !is_infer(at) && types_incompatible(dt.base_type, at) {
        tc_error(k, span, TYPE_CANNOT_CONSTRUCT_UNDERLYING_TYPE, name, type_name(at), type_name(dt.base_type))
    }
    return dt
}

// `E(n)`, E an enum: the variant whose value the integer n is
// (`GL_Tex_Param(0x813D)`). A constant that's no variant's value is an
// error here; a number known only when it runs is checked there, the
// program stopped when it's none (llvm_from_number).
tc_enum_number :: proc(k: ^TC, n: Tree_Id, name: string, et: ^Type_Enum, args: []Tree_Id) -> Type {
    span := tree_span(k.t, n)
    tc_set_ref(k, n, {type_decl(et), .Type})   // (the call names its enum: `Mode(3)`, `gl.GL_Tex_Param(n)`)
    if len(args) != 1 {
        tc_error(k, span, TYPE_EXPECTS_ARGUMENT_3, name, len(args))
        for a in args { tc_check(k, a) }
        return Type_Error{}
    }
    saved := k.hint
    k.hint = nil
    at := tc_check(k, args[0])
    k.hint = saved
    if _, failed := at.(Type_Error); failed { return Type_Error{} }
    _, from_enum := distinct_base(at).(^Type_Enum)
    if from_enum || !is_integer(distinct_base(at)) && !is_any(at) {
        tc_error(k, span, TYPE_ENUM_NUMBER_INTEGER, name, type_name(solidify_type(at)))
        return Type_Error{}
    }
    if v, known := tc_comptime_int(k, args[0]); known && !enum_has_value(et, v) {
        tc_error(k, span, TYPE_ENUM_NO_SUCH_VALUE, v, name, enum_variants_text(et))
    }
    // (Its fun takes it at its own type: a literal, or a name of no width
    // written, at i64 — that use deciding it, as an argument's does.)
    pt := solidify_type(at)
    tc_value_at(k, args[0], at, pt, span)
    k.annot.forms[tc_sid(k, n)] = .Fun   // (its fun's, made here)
    tc_set_callee(k, n, tc_from_number_fun(et, et, pt))
    tc_set_args(k, n, {{args[0], .Written, -1}})
    return et
}

// Whether a variant of the enum has the value v.
enum_has_value :: proc(et: ^Type_Enum, v: i64) -> bool {
    for _, value in et.variants { if i64(value) == v { return true } }
    return false
}

// An enum's variants as an error lists them, by value: `Off = 0, Slow = 3`
// (the first 8, then how many more).
enum_variants_text :: proc(et: ^Type_Enum) -> string {
    Variant :: struct { name: string, value: int }
    vs := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
    for name, value in et.variants { append(&vs, Variant{name, value}) }
    slice.sort_by(vs[:], proc(a, b: Variant) -> bool { return a.value < b.value || a.value == b.value && a.name < b.name })
    b := strings.builder_make(context.temp_allocator)
    for v, i in vs {
        if i == 8 {
            fmt.sbprintf(&b, ", and %d more", len(vs) - 8)
            break
        }
        fmt.sbprintf(&b, "%s%s = %d", ", " if i > 0 else "", v.name, v.value)
    }
    return strings.to_string(b)
}

// Whether `from` is a list of another room than the list `to`, of elements
// it takes: what only an explicit conversion makes one of the other.
tc_list_resized :: proc(from, to: Type) -> bool {
    fa, from_list := from.(^Type_Partial_Array)
    ta, to_list := to.(^Type_Partial_Array)
    return from_list && to_list && fa.size != ta.size && buffer_elem_compatible(ta.elem, fa.elem)
}

// `f()?`: the call, its err returned when it is one — its value the call's
// first, or none when it returns only its err.
tc_try :: proc(k: ^TC, n: Tree_Id) -> Type {
    several := tc_takes_several(k, n)
    span := tree_span(k.t, n)
    inner := Tree_Id(k.t.a[n])
    k.several_ok = tc_unparen(k, inner)   // (its err is `?`'s; the rest, its)
    tc_check(k, inner)
    k.several_ok = 0
    if !tc_is_call(k, tc_unparen(k, inner)) {
        tc_error(k, span, TYPE_TRY_OPERAND_MUST_BE_CALL)
        return Type_Error{}
    }
    rets := tc_call_returns(k, inner)
    if len(rets) == 0 || !is_err_type(rets[len(rets) - 1]) {
        tc_error(k, span, TYPE_TRY_REQUIRES_ERR_RETURN)
        return Type_Error{}
    }
    tc_note_err_pass(k, n)   // (where it passes a failure on: its trace's next site)
    if rts := tc_results(k); k.in_defer {
        tc_error(k, span, TYPE_TRY_IN_DEFER)   // (its value still typed: no errors after it)
    } else if len(rts) == 0 || !is_err_type(rts[len(rts) - 1]) {
        tc_error(k, span, TYPE_TRY_OUTSIDE_ERR_FUNCTION)
        return Type_Error{}
    }
    if len(rets) == 1 { return Type_Void{} }
    if !several { tc_one_value(k, n, len(rets) - 1) }
    return rets[0]
}

// `if c do a else b` as a value: its condition a bool or an error
// (is_condition_type), its type its branches' (an untyped one takes the
// other's).
tc_if_expr :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    span := tree_span(tr, n)
    then_n, else_n := tree_pair(tr, n)
    ct := tc_check(k, Tree_Id(tr.a[n]))
    if !is_condition_type(ct) { tc_not_condition(k, span, ct, TYPE_EXPRESSION_CONDITION_BOOL, type_name(ct)) }
    types: [2]Type
    for branch, i in ([2]Tree_Id{then_n, else_n}) { types[i] = tc_check(k, branch) }
    t := types[0]
    switch {
    case is_untyped(types[0]) || is_infer(types[0]): t = types[1]
    case is_untyped(types[1]) || is_infer(types[1]):
    case types_incompatible(types[0], types[1]):
        tc_error(k, span, TYPE_EXPRESSION_BRANCHES_INCOMPATIBLE_TYPES_VS, type_name(types[0]), type_name(types[1]))
    }
    // (Neither branch of a width: a binding's carries its own — its width
    // the expression's, as an operation's is; two bindings', one width. A
    // binding's value in a branch: a use of it at the expression's type.)
    if is_infer(types[0]) && is_infer(types[1]) {
        c0, c1 := infer_cell_of(types[0]), infer_cell_of(types[1])
        if c0 != nil && c1 != nil { unify_infer_cells(k.c, c0, c1, span) }
        if c0 != nil { t = types[0] } else if c1 != nil { t = types[1] }
    }
    for bt in types { tc_flow_use(k, bt, t, span) }
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
tc_arg :: proc(k: ^TC, a: Tree_Id) -> Type {
    if a != 0 && a == k.recv.node { return k.recv.t }
    return tc_check(k, a)
}
