package mara

import "core:fmt"
import "core:os"

// flow.odin — post-check intraprocedural flow analysis.
//
// This pass walks each function body over the DURABLE graph (ft.body — the exact
// statements codegen emits) AFTER checking, to re-derive the correctness
// analyses that today run INLINE on the during-check Type_Env traversal:
// definite assignment (no read-before-init of a pointer/slice), must-use-err,
// and all-paths-return. Lifting them here is "step 3" of the Type_Env teardown:
// once the point-sensitive flow state is computed by a self-contained post-check
// pass over the scope graph, Type_Env sheds it and shrinks to (eventually
// disappears as) the lookup mirror that the durable graph already replaced.
//
// Why a post-check pass and not an env relocation: the flow state is genuinely
// point-sensitive (it forks at branches, merges at joins), so it can't live on
// the durable Type_Scope. A pass that OWNS its own transient frame and walks the
// graph in control-flow order is the clean home — and it composes with the
// interprocedural call-graph summaries (purity, fallibility) that already live
// post-check (see callgraph.odin / project_call_graph).
//
// SKELETON (this commit): the traversal scaffold ONLY. It visits every source
// function and recurses the control-flow tree (if/for/defer/match bodies — the
// .Block scopes), but performs NO analysis and raises NO diagnostics. The inline
// checker is still the sole authority. MARA_DUMP_FLOW=1 dumps coverage stats so
// the walk can be confirmed exhaustive over the constructs the real analysis
// will care about (decls, branch joins) before any of it is ported in. Inert —
// no behavior change.

Flow_Stats :: struct {
    functions:  int, // source functions walked
    statements: int, // statements visited (all nesting levels)
    decls:      int, // Stmt_Decl — what definite-assignment tracks
    branches:   int, // if / match — the merge points
    max_depth:  int, // deepest control-flow nesting reached
}

// Entry point — called post-check (after build_call_graph), inert for now.
flow_analyze_program :: proc(checked: ^Checked_Program) {
    stats: Flow_Stats
    for _, ft in checked.functions {
        if ft == nil { continue }
        // Source bodies only: intrinsics/foreigns have no Mara statements to walk.
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        if len(ft.body) == 0 { continue }
        stats.functions += 1
        flow_walk_stmts(&stats, ft.body[:], 1)
    }
    flow_dump_stats(stats)
}

// Recurse the control-flow tree, counting coverage. Descends if/for/defer/match
// bodies (the .Block scopes) but NOT a nested Stmt_Scope — a nested fun/struct is
// a separate function with its own checked.functions entry and its own flow, so
// it is walked on its own, not inlined here.
flow_walk_stmts :: proc(stats: ^Flow_Stats, stmts: []Stmt, depth: int) {
    if depth > stats.max_depth { stats.max_depth = depth }
    for s in stmts {
        stats.statements += 1
        #partial switch v in s {
        case ^Stmt_Decl:
            stats.decls += 1
        case ^Stmt_If:
            stats.branches += 1
            flow_walk_stmts(stats, v.body[:], depth + 1)
            flow_walk_stmts(stats, v.else_body[:], depth + 1)
        case ^Stmt_For:
            flow_walk_stmts(stats, v.body[:], depth + 1)
        case ^Stmt_Defer:
            flow_walk_stmts(stats, v.body[:], depth + 1)
        case ^Stmt_Match:
            stats.branches += 1
            for arm in v.arms {
                flow_walk_stmts(stats, arm.body[:], depth + 1)
            }
        }
    }
}

flow_dump_stats :: proc(stats: Flow_Stats) {
    buf: [8]byte
    if os.get_env_buf(buf[:], "MARA_DUMP_FLOW") != "1" { return }
    fmt.eprintf(
        "[flow] %d source funcs, %d stmts, %d decls, %d branches, max depth %d\n",
        stats.functions, stats.statements, stats.decls, stats.branches, stats.max_depth,
    )
}
