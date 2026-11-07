package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Lineage — `mara ask <var> in <fn> flow above` (provenance / data lineage).
//
// "What is this value built from?" — the backward dual of the forward call-
// following view. Rooted at one variable, it walks the def-use (defuse.odin)
// BACKWARD and prints a TREE: each producing statement is a node, a producing
// CALL is labelled by name, and every input it consumed (ALL call arguments, not
// just the ones the return data-depends on) becomes a child to recurse into. So
// a glyph's position reads as:
// glyph ⟵ pack_rect() ⟵ outline ⟵ parse_glyph() ⟵ ttf ⟵ TTF() ⟵ file.
//
// This differs from the backward slice, which is a FLAT set crossing calls by
// summary; lineage is a chain that FOLLOWS the producing calls. It stays in the
// rooted function — a call is a labelled rung whose inputs are the caller's args,
// which are themselves local (so the pipeline is intra-procedural). Parameters and
// other call-free external inputs are the leaves. Each definition is expanded
// once (a shared/looping producer shows fully the first time, then "(shown
// above)").
// ---------------------------------------------------------------------------

// `flow above` for a variable: the lineage / producer tree. Writes into the
// caller's builder, under the variable header render_var_slice already printed.
// "What builds this value", following every input into the calls that produce it.
// Each row is a variable, the line that gives it its value, as written: a call that
// reads no variable is seen there.
render_lineage_body :: proc(checked: ^Checked_Program, bb: ^strings.Builder, b: ^Var_Binding, depth: int, root_def: ^Def) {
    fn_label := ask_label(b.fn)
    fmt.sbprint(bb, "\nabove (flow) — what builds this value, following every input into the calls that produce it\n\n")

    // Flow roots at ONE point in the variable's timeline — its declaration by
    // default, or the write addressed with `at <file>:<line>`. `above` shows what
    // SUPPLIES that point: the back-walk from the root's inputs. A variable's own
    // later modifications are forward evolution (they belong to `below`), not
    // suppliers — so a literal decl like `speed: f32 = 500` has nothing above it.
    root := root_def
    if root == nil { root = var_root_def(checked, b) }

    // The root's direct inputs. A value-less decl (`x: T`, zero-init) or a bare
    // parameter has none; a value from literals or a call of nothing reads no
    // variable. Either way, no variable supplies it — say so and stop.
    inputs: [dynamic]^Def
    defer delete(inputs)
    if root != nil && root.valued {
        uses: [dynamic]Du_Use
        defer delete(uses)
        du_def_uses(checked, root, false, &uses)
        seen_in: map[^Def]bool
        defer delete(seen_in)
        for u in uses {
            for d2 in du_reach(u) { if !seen_in[d2] { seen_in[d2] = true; append(&inputs, d2) } }
        }
    }
    // Rooted at the declaration by default: if the variable is written again later,
    // the declaration isn't the whole story — say so, and list those writes.
    later: [dynamic]^Def
    defer delete(later)
    if root_def == nil && root != nil {
        defs := var_defs(checked, b)
        defer delete(defs)
        for d in defs { if d != root { append(&later, d) } }
        slice.sort_by(later[:], def_less)
    }
    if b.kind == .Param && (root == nil || root.kind == .Param) {
        ask_write_param_calls(bb, checked, b)
    } else {
        lineage_row(bb, b.name, root.span if root != nil else b.span, 1)
        switch {
        case len(inputs) > 0:
            slice.sort_by(inputs[:], def_less)
            // (Depth 1 is what it reads, as a call tree's is what it calls.)
            if depth == 0 {
                fmt.sbprintf(bb, "    (%d more: add a depth, or 'all')\n", len(inputs))
                break
            }
            budget := depth - 1 if depth > 0 else (1 << 30)
            seen: map[^Def]bool
            defer delete(seen)
            for d in inputs { lineage_node(checked, bb, d, budget, 2, &seen) }
        case root == nil || !root.valued:
            fmt.sbprintf(bb, "    (declared without a value%s)\n", ": written again below" if len(later) > 0 else "")
        case:
            fmt.sbprintf(bb, "    (no variable of %s feeds it)\n", fn_label)
        }
    }
    if len(later) > 0 { render_later_writes(checked, bb, b, later[:]) }
}

// A row of the tree: the variable, where it gets its value, and what's written there.
@(private="file")
lineage_row :: proc(bb: ^strings.Builder, name: string, span: Span, indent: int) {
    lineage_pad(bb, indent)
    fmt.sbprintf(bb, "%s  %s  %s\n", name, ask_loc(span), hit_source_line(build_tokens[span.tok]))
}

// The writes after a variable's declaration, each as written — so a
// declaration-rooted `above` can't pass for the variable's whole history.
@(private="file")
render_later_writes :: proc(checked: ^Checked_Program, bb: ^strings.Builder, b: ^Var_Binding, later: []^Def) {
    fmt.sbprintf(bb, "\n  %s is written again — trace a write with `mara ask at <file>:<line> flow above`:\n", b.name)
    for d in later { fmt.sbprintf(bb, "    %s  %s\n", ask_loc(d.span), hit_source_line(build_tokens[d.span.tok])) }
}

// One node of the tree, then its inputs indented below.
lineage_node :: proc(checked: ^Checked_Program, bb: ^strings.Builder, d: ^Def, budget, indent: int, seen: ^map[^Def]bool) {
    name := d.binding.name if d.binding != nil else "?"

    // A parameter's entry is a leaf — the value enters from outside the function.
    if d.kind == .Param {
        lineage_pad(bb, indent)
        fmt.sbprintf(bb, "%s  %s  (a param)\n", name, ask_loc(d.span))
        return
    }
    if d in seen^ {
        lineage_pad(bb, indent)
        fmt.sbprintf(bb, "%s  (shown above)\n", name)
        return
    }
    seen^[d] = true
    lineage_row(bb, name, d.span, indent)
    if !d.valued || budget == 0 { return }

    // Recurse into every input the producer consumed — all call arguments included,
    // unfiltered (the point of lineage: what was fed in, not just what the result
    // mathematically derives from). Dedup the child defs for a stable, finite tree.
    uses: [dynamic]Du_Use
    defer delete(uses)
    du_def_uses(checked, d, false, &uses)

    // Per use, its reaching defs in source order (the set has no order).
    child_seen: map[^Def]bool
    defer delete(child_seen)
    kids: [dynamic]^Def
    defer delete(kids)
    for u in uses {
        clear(&kids)
        for d2 in du_reach(u) {
            if child_seen[d2] { continue }
            child_seen[d2] = true
            append(&kids, d2)
        }
        slice.sort_by(kids[:], def_less)
        for d2 in kids { lineage_node(checked, bb, d2, budget - 1, indent + 1, seen) }
    }
}

@(private="file")
lineage_pad :: proc(bb: ^strings.Builder, indent: int) {
    for _ in 0 ..< indent { fmt.sbprint(bb, "  ") }
}
