package mara

import "core:fmt"
import "core:strings"

// What the checker's diagnostics say about the source: a name for an
// expression, the operands a mismatch traces to. (Parens are seen through.)

// "a.b[i]", "f()", or "" when the expression has no nameable form.
tc_diag_name :: proc(k: ^TC, n: Tree_Id) -> string {
    t := k.t
    #partial switch t.tag[n] {
    case .Paren:
        return tc_diag_name(k, Tree_Id(t.a[n]))
    case .Ident:
        return tc_name(k, n)
    case .Field:
        base := tc_diag_name(k, Tree_Id(t.a[n]))
        field := tc_text(Token_Id(t.b[n]))
        if base == "" { return field }
        return fmt.tprintf("%s.%s", base, field)
    case .Index:
        base := tc_diag_name(k, Tree_Id(t.a[n]))
        if base == "" { return "" }
        idx := tc_diag_name(k, Tree_Id(t.b[n]))
        if idx == "" { return base }
        return fmt.tprintf("%s[%s]", base, idx)
    case .Call, .Method_Call:
        return fmt.tprintf("%s()", tc_call_name(k, n))
    }
    return ""
}

// A fixed array's address where a buffer that keeps a len goes — `&buf` of a
// `[N!]T` into a `^[]T` (or `^[M]T`) param, `&buf + x`: the fix, a partial
// array of the same room, as the error's last clause ("" when it's not
// that). `want` nil: any buffer (an append's).
tc_partial_hint :: proc(k: ^TC, n: Tree_Id, got: Type, want: Type = nil) -> string {
    gp, g_ptr := got.(^Type_Ptr)
    if !g_ptr { return "" }
    fa, g_fixed := distinct_base(gp.elem).(^Type_Fixed_Array)
    if !g_fixed { return "" }
    if want != nil {
        wp, w_ptr := want.(^Type_Ptr)
        if !w_ptr { return "" }
        elem: Type
        #partial switch w in distinct_base(wp.elem) {
        case ^Type_Slice:         elem = w.elem
        case ^Type_Partial_Array: elem = w.elem
        case:                     return ""
        }
        if types_incompatible(elem, fa.elem) { return "" }
    }
    // (Its name, seen through the `&`.)
    m := tc_unparen(k, n)
    if k.t.tag[m] == .Unary && build_tokens[k.t.main[m]].kind == .Ampersand { m = Tree_Id(k.t.a[m]) }
    name := tc_diag_name(k, m)
    what := fmt.tprintf("`%s`", name) if name != "" else "it"
    return fmt.tprintf(" — %s is a fixed array, with no len to move: declare it a list, `[%d]%s`", what, fa.size, type_name(fa.elem))
}

// An array where a buffer of items laid out otherwise goes (text kept as
// lists where slices go, `[2!][64]utf8` for a `[][]utf8`; rows of another
// size): what its items are and what the param's are, as the error's last
// clause ("" when it's not that).
tc_items_hint :: proc(got, want: Type) -> string {
    // (A buffer's item type, and its count when it's a fixed array.)
    items :: proc(t: Type) -> (Type, int) {
        #partial switch v in distinct_base(resolve_infer(t)) {
        case ^Type_Slice:         return v.elem, -1
        case ^Type_Partial_Array: return v.elem, -1
        case ^Type_Fixed_Array:   return v.elem, v.size
        }
        return nil, -1
    }
    kind :: proc(t: Type) -> string {
        #partial switch v in distinct_base(resolve_infer(t)) {
        case ^Type_Slice:         return "slices"
        case ^Type_Partial_Array: return "lists"
        case ^Type_Fixed_Array:   return fmt.tprintf("fixed arrays of %d", v.size)
        case Type_Atom:           return "atoms"
        case Type_CString:        return "cstrings"
        }
        return type_name(t)
    }
    g, n := items(got)
    w, _ := items(want)
    if g == nil || w == nil || !item_layout_mismatch(w, g) { return "" }
    if _, to_views := distinct_base(w).(^Type_Slice); to_views && n >= 0 {
        return fmt.tprintf(" — its items are %s, and a %s holds %s: make it an array of them, `[%d!]%s%s`", kind(g), type_name(want), kind(w), n, type_name(w), "{...}")
    }
    return fmt.tprintf(" — its items are %s, and a %s holds %s", kind(g), type_name(want), kind(w))
}

// An expression as written: "y == 0".
tc_written :: proc(k: ^TC, n: Tree_Id) -> string {
    return token_range_text(int(k.t.first[n]), int(k.t.end[n]))
}

// Whether `n` is a string literal, or a constant naming one.
// Whether an argument is `void` as written: a null, for a C function.
tc_void_arg :: proc(k: ^TC, n: Tree_Id) -> bool {
    m := tc_unparen(k, n)
    return k.t.tag[m] == .Ident && tc_name(k, m) == "void"
}

tc_text_literal :: proc(k: ^TC, n: Tree_Id) -> bool {
    m := tc_unparen(k, n)
    if k.t.tag[m] == .String { return true }
    if k.t.tag[m] != .Ident { return false }
    kc := tc_const_named(k, m)
    return kc != nil && k.t.tag[kc.value] == .String
}

// "p.x (i64), q (i64)": the named operands of `n` too wide for `target`.
tc_wide_clause :: proc(k: ^TC, target: Type, roots: ..Tree_Id) -> string {
    srcs: [dynamic]string
    defer delete(srcs)
    collect :: proc(k: ^TC, n: Tree_Id, target: Type, out: ^[dynamic]string) {
        t := k.t
        #partial switch t.tag[n] {
        case .Paren, .Unary:
            collect(k, Tree_Id(t.a[n]), target, out)
            return
        case .Binary:
            collect(k, Tree_Id(t.a[n]), target, out)
            collect(k, Tree_Id(t.b[n]), target, out)
            return
        }
        nt := tc_node_type(k, n)
        if nt == nil || !is_numeric(nt) || is_infer(nt) { return }
        if !types_incompatible(target, nt) { return }
        name := tc_diag_name(k, n)
        if name == "" { return }
        entry := fmt.tprintf("%s (%s)", name, type_name(nt))
        for s in out^ { if s == entry { return } }
        append(out, entry)
    }
    for n in roots { collect(k, n, target, &srcs) }
    if len(srcs) == 0 { return "" }
    return strings.join(srcs[:], ", ")
}

// "cannot assign X to variable 'v' of type Y" (— from the wide operands).
tc_assign_error :: proc(k: ^TC, span: Span, vt: Type, name: string, target: Type, values: ..Tree_Id) {
    if clause := tc_wide_clause(k, target, ..values); clause != "" {
        tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE_FROM, type_name(vt), name, type_name(target), clause)
        return
    }
    tc_error(k, span, TYPE_CANNOT_ASSIGN_VARIABLE_TYPE, type_name(vt), name, type_name(target))
}
