package mara

// ---------------------------------------------------------------------------
// LLVM IR from the program graph (design/graph_retrofit.md, phase 3).
//
// A fun's code is its runs: each becomes a block, and each operation in it
// lowers as the operations table in design/program_graph.md says. The worker
// loop asks llvm_function for every fun; it emits the fun when it handles every
// operation in it and declines otherwise, and the syntax-tree emitter
// (codegen_fn.odin) does the rest — until it does nothing and is deleted.
// ---------------------------------------------------------------------------

// Emit a fun from the graph. False, having emitted nothing, when some part of
// it isn't handled yet.
llvm_function :: proc(g: ^Codegen, cf: ^Type_Scope) -> bool {
    return false
}
