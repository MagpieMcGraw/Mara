package mara

// The checker's lean core, as the rewrite grows it (memory: the checker
// rewrite): what's commonest checked without the general path's questions,
// none of which can apply to it — the same annotations, the same errors.
//
// So far: a declaration `v : T = e`, T a number's type or bool, e of
// numbers, names of such, parens, `-`, arithmetic and comparisons
// (ck_core).

// What a core expression is: a number's (an open width's too), a bool's;
// none: no core expression.
@(private="file")
Ck_Kind :: enum u8 { None, Number, Bool }

// A type the core takes: a number's — a width's, f64 — or bool; no
// distinct one, no open binding's.
@(private="file")
ck_kind_of :: proc(t: Type) -> Ck_Kind {
    #partial switch v in t {
    case Type_Numeric, Type_F64:   return .Number
    case Type_Bool:                return .Bool
    case Type_Infer_Int:           return .Number if v.cell == nil else .None
    case Type_Infer_Float:         return .Number if v.cell == nil else .None
    }
    return .None
}

// Whether an expression is the core's: what it is, every part of it the
// core's too — a number, a name of a variable of a core type, a paren, a
// `-` of a number, arithmetic of numbers, a comparison of numbers, an
// `and` / `or` of bools. (Decided before anything is checked: the core
// never meets what it can't do.)
@(private="file")
ck_core :: proc(k: ^TC, n: Tree_Id) -> Ck_Kind {
    tr := k.t
    #partial switch tr.tag[n] {
    case .Number:
        return .Number
    case .Paren:
        return ck_core(k, Tree_Id(tr.a[n]))
    case .Ident:
        ref := k.rs.refs[n]
        #partial switch ref.kind {
        case .Local, .Param, .Result:
        case: return .None
        }
        t, ok := tc_bound(k, ref.decl)
        if !ok { return .None }
        return ck_kind_of(t)
    case .Unary:
        if build_tokens[tr.main[n]].kind != .Minus { return .None }
        return .Number if ck_core(k, Tree_Id(tr.a[n])) == .Number else .None
    case .Binary:
        l, r := ck_core(k, Tree_Id(tr.a[n])), ck_core(k, Tree_Id(tr.b[n]))
        #partial switch build_tokens[tr.main[n]].kind {
        case .Plus, .Minus, .Star, .Slash, .Modulo:
            return .Number if l == .Number && r == .Number else .None
        case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
            return .Bool if l == .Number && r == .Number else .None
        case .And, .Or:
            return .Bool if l == .Bool && r == .Bool else .None
        }
    }
    return .None
}

// A core expression checked (ck_core said it is one): as tc_check does,
// the hint (TC.hint) taken as it takes it.
@(private="file")
ck_expr :: proc(k: ^TC, n: Tree_Id) -> Type {
    tr := k.t
    t: Type
    #partial switch tr.tag[n] {
    case .Number:
        t = tc_number(k, n)
    case .Paren:
        t = ck_expr(k, Tree_Id(tr.a[n]))
    case .Ident:
        // (A local's, a param's, a result's: bound — no variant a core hint
        // has; the hint taken.)
        ref := k.rs.refs[n]
        t, _ = tc_bound(k, ref.decl)
        tc_set_ref(k, n, ref)
        k.hint = nil
    case .Unary:
        operand := Tree_Id(tr.a[n])
        if tr.tag[operand] == .Number {
            t = tc_number(k, operand)
            tc_set_type(k, operand, t)
        } else {
            t = ck_expr(k, operand)
            if _, kind, ok := numeric_info(t); ok && kind == .Unsigned { tc_error(k, tree_span(tr, n), TYPE_CANNOT_NEGATE_UNSIGNED, type_name(t)) }
        }
    case .Binary:
        hint := k.hint
        k.hint = hint
        lt := ck_expr(k, Tree_Id(tr.a[n]))
        k.hint = hint
        rt := ck_expr(k, Tree_Id(tr.b[n]))
        op := build_tokens[tr.main[n]].kind
        span := tree_span(tr, n)
        // (Each side then at the type the operation takes it at: a
        // comparison's, the other side's; an arithmetic one's, its own.)
        #partial switch op {
        case .Plus, .Minus, .Star, .Slash, .Modulo:
            t = coerce_infer_to_hint(k.c, promote_numeric(k.c, lt, rt, span), hint, span)
            tc_settle(k, Tree_Id(tr.a[n]), t)
            tc_settle(k, Tree_Id(tr.b[n]), t)
        case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal:
            promote_numeric(k.c, lt, rt, span)
            t = Type_Bool{}
            tc_settle(k, Tree_Id(tr.a[n]), rt)
            tc_settle(k, Tree_Id(tr.b[n]), lt)
        case .And, .Or:
            t = Type_Bool{}
        }
    }
    tc_set_type(k, n, t)
    return t
}

// Whether a declaration's the core's: of a core type, a core value.
ck_decl_fits :: proc(k: ^TC, ann: Type, value: Tree_Id) -> bool {
    if value == 0 { return false }
    a := ck_kind_of(ann)
    if a == .None || is_infer(ann) { return false }
    return ck_core(k, value) == a
}

// `v : T = e`, the core's (ck_decl_fits): as tc_decl_one checks it — what
// tc_decl_form, a field's default, bytes, a slice, a big-endian read, a
// call's results, an array would ask, none of them can be.
ck_decl :: proc(k: ^TC, s, target, value: Tree_Id, name: string, ann: Type, ref: Ref) {
    span := tree_span(k.t, s)
    k.hint = ann
    vt := ck_expr(k, value)
    if !coerce_deferred(k.c, vt, ann, span) && types_incompatible(ann, vt) {
        tc_assign_error(k, span, vt, name, ann, value)
    }
    tc_value_at(k, value, vt, ann, span)
    tc_bind(k, name, ann, ref)
    tc_set_type(k, target, ann)   // (the name declared: its type)
    tc_settle(k, value, ann)
    tc_note_decl(k, name, ann, span, false)
}
