package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Lineage — `mara ask <var> in <fn> lineage` (a.k.a. provenance / data lineage).
//
// "What is this value built from?" — the backward dual of the forward call-
// following view. Rooted at one variable, it walks the def-use graph BACKWARD and
// prints a TREE: each producing statement is a node, a producing CALL is labelled
// by name, and every input it consumed (ALL call arguments, not just the ones the
// return data-depends on) becomes a child to recurse into. So a glyph's position
// reads as:  glyph ⟵ pack_rect() ⟵ outline ⟵ parse_glyph() ⟵ ttf ⟵ TTF() ⟵ file.
//
// This differs from the `flow above` slice, which is a FLAT set crossing calls by
// summary; lineage is a chain that FOLLOWS the producing calls. It stays in the
// rooted function — a call is a labelled rung whose inputs are the caller's args,
// which are themselves local (so the pipeline is intra-procedural). Parameters and
// other call-free external inputs are the leaves. Each binding is expanded once
// (a shared/looping producer shows fully the first time, then "(shown above)").
// ---------------------------------------------------------------------------

// `mara ask <var> in <fn> lineage` / `at <file>:<line> lineage`. Builds its own
// header, so render_var_slice hands the whole query off here.
render_lineage :: proc(checked: ^Checked_Program, b: ^Var_Binding, fn_label, pkg: string, depth: int) -> string {
    ensure_fn_analysis(checked, b.fn)
    bb := strings.builder_make()
    knd := "param" if b.kind == .Param else "local"
    home_pkg := ask_home_package(b.fn)
    if home_pkg == "" { home_pkg = pkg }
    fmt.sbprintf(&bb, "%s — %s in %s  %s   (module %s)\n", b.name, knd, fn_label, ask_loc(b.span), home_pkg)
    fmt.sbprint(&bb, "\nlineage — what builds this value, following every input into the calls that produce it\n\n")

    // The producing defs of the root (a write/decl with a value). A bare parameter
    // has only its entry def (value nil) — an external input with no local origin.
    producing: [dynamic]^Def
    defer delete(producing)
    for d in checked.defs {
        if d.binding == b && d.value != nil { append(&producing, d) }
    }
    if len(producing) == 0 {
        fmt.sbprintf(&bb, "  %s   (a %s — external input; nothing in %s builds it)\n", b.name, knd, fn_label)
        return strings.to_string(bb)
    }
    slice.sort_by(producing[:], lineage_def_less)

    budget := depth if depth >= 0 else (1 << 30)
    seen: map[^Def]bool
    defer delete(seen)
    for d in producing {
        lineage_node(checked, &bb, d, budget, 0, &seen)
    }
    return strings.to_string(bb)
}

// One node of the tree: `binding ⟵ producer   loc`, then its inputs indented below.
lineage_node :: proc(checked: ^Checked_Program, bb: ^strings.Builder, d: ^Def, budget, indent: int, seen: ^map[^Def]bool) {
    name := d.binding.name if d.binding != nil else "?"
    lineage_pad(bb, indent)

    // A parameter / entry def is a leaf — the value enters from outside the function.
    if d.kind == .Param || d.value == nil {
        fmt.sbprintf(bb, "%s   (param / external input)   %s\n", name, ask_loc(d.span))
        return
    }
    if d in seen^ {
        fmt.sbprintf(bb, "%s   (shown above)\n", name)
        return
    }
    seen^[d] = true

    label, is_call := lineage_call_label(d.value)
    if is_call {
        fmt.sbprintf(bb, "%s  ⟵ %s()   %s\n", name, label, ask_loc(d.span))
    } else {
        fmt.sbprintf(bb, "%s   %s\n", name, ask_loc(d.span))
    }
    if budget == 0 { return }

    // Recurse into every input the producer consumed — all call arguments included,
    // unfiltered (the point of lineage: what was fed in, not just what the result
    // mathematically derives from). Dedup the child defs for a stable, finite tree.
    idents: [dynamic]^Expr_Ident
    defer delete(idents)
    lineage_all_idents(d.value, &idents)

    child_seen: map[^Def]bool
    defer delete(child_seen)
    for u in idents {
        rdefs := checked.reaching[u]   // bind before ranging (transient map-index lvalue)
        for d2 in rdefs {
            if child_seen[d2] { continue }
            child_seen[d2] = true
            lineage_node(checked, bb, d2, budget - 1, indent + 1, seen)
        }
    }
}

// Source order (by span), so the root's producing writes read top-to-bottom.
@(private="file")
lineage_def_less :: proc(a, b: ^Def) -> bool {
    if a.span.file != b.span.file { return a.span.file < b.span.file }
    if a.span.line != b.span.line { return a.span.line < b.span.line }
    return a.span.col < b.span.col
}

@(private="file")
lineage_pad :: proc(bb: ^strings.Builder, indent: int) {
    for _ in 0 ..< indent { fmt.sbprint(bb, "    ") }
}

// The producing call's display name, or ok=false when the value isn't a call.
// A numeric/built-in CAST (`i32(px)`) is spelled like a call but produces nothing
// — it's a no-op rung, so report it as a non-call and let the operand show through.
@(private="file")
lineage_call_label :: proc(value: Expr) -> (name: string, ok: bool) {
    call: ^Expr_Call
    #partial switch v in value {
    case ^Expr_Call:          call = v
    case ^Expr_Tuple_Default: if c, c_ok := v.source.(^Expr_Call); c_ok { call = c }
    }
    if call == nil { return "", false }
    if _, is_cast := cast_result_type(call.name); is_cast { return "", false }
    if rf, rf_ok := call.resolved_func.?; rf_ok && rf.callee != nil { return ask_label(rf.callee), true }
    return call.name, true
}

// Every variable use in an expression — ALL of them, including every call argument
// (unlike slice_collect, which return_deps-filters call args). A tuple-default
// destructure (`a, b := f()`) routes through its source call.
@(private="file")
lineage_all_idents :: proc(e: Expr, out: ^[dynamic]^Expr_Ident) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:        append(out, v)
    case ^Expr_Call:
        for a in v.args { lineage_all_idents(a, out) }
        if v.overrides != nil { lineage_all_idents(v.overrides, out) }   // typed ptr: a nil one wraps to a non-nil union
    case ^Expr_Unary:        lineage_all_idents(v.operand, out)
    case ^Expr_Binary:       lineage_all_idents(v.left, out); lineage_all_idents(v.right, out)
    case ^Expr_Index:        lineage_all_idents(v.expr, out); lineage_all_idents(v.index, out)
    case ^Expr_Slice:        lineage_all_idents(v.expr, out); lineage_all_idents(v.low, out); lineage_all_idents(v.high, out)
    case ^Expr_Field_Access: lineage_all_idents(v.expr, out)
    case ^Expr_Struct_Literal:
        for f in v.fields { lineage_all_idents(f.value, out) }
        for a in v.array_values { lineage_all_idents(a, out) }
        lineage_all_idents(v.broadcast_value, out)
    case ^Expr_Take:         lineage_all_idents(v.storage, out); lineage_all_idents(v.count_expr, out)
    case ^Expr_Try:          lineage_all_idents(v.inner, out)
    case ^Expr_If:           lineage_all_idents(v.condition, out); lineage_all_idents(v.then_expr, out); lineage_all_idents(v.else_expr, out)
    case ^Expr_Array:        for el in v.elements { lineage_all_idents(el, out) }
    case ^Expr_Tuple_Default: lineage_all_idents(v.source, out)
    }
}
