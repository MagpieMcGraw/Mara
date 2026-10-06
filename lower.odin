package mara

// ---------------------------------------------------------------------------
// Lowering (design/annotated_tree.md, stage 2): the program graph made from
// the flat tree and what the checker found about it (annot.odin), once the
// check is done — the checker only checks.
// ---------------------------------------------------------------------------

lower_program :: proc(k: ^TC) -> ^Graph_Builder {
    b := graph_builder_new(k.checked, tc_module_graph_decls(k))
    return b
}
