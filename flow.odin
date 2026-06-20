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
// STATUS: the traversal scaffold visits every source function and recurses the
// control-flow tree (if/for/defer/match bodies — the .Block scopes), not nested
// Stmt_Scope (separate functions). It OWNS its first analysis: all-paths-return
// (the inline check at check_scope_body has been removed; this pass raises
// TYPE_FUNCTION_MISSING_RETURN_ALL_CODE). Still to port: must-use-err, then
// definite-assignment (branch-merge). MARA_DUMP_FLOW=1 dumps coverage + what was
// flagged.

Flow_Stats :: struct {
    functions:  int, // source functions walked
    statements: int, // statements visited (all nesting levels)
    decls:      int, // Stmt_Decl — what definite-assignment tracks
    branches:   int, // if / match — the merge points
    max_depth:  int, // deepest control-flow nesting reached

    // Functions flagged for "missing return on all code paths" — the first
    // analysis this pass OWNS (emitted below, not just collected).
    missing_return: [dynamic]string,

    // Names flagged for unused-err (validation mode — collected, not yet emitted;
    // the inline check_unused_locals is still authoritative). Confirms agreement:
    // a program that compiles must collect 0, an unused-err fixture must collect it.
    unused_err: [dynamic]string,
}

// Entry point — called post-check (after build_call_graph). Walks every source
// function and raises the intraprocedural diagnostics it owns. Takes the Checker
// purely as the error sink (check_error); the analysis itself reads only the
// durable Checked_Program.
flow_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program) {
    stats: Flow_Stats
    for _, ft in checked.functions {
        if ft == nil { continue }
        // Source bodies only: intrinsics/foreigns have no Mara statements to walk.
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        if len(ft.body) == 0 { continue }
        stats.functions += 1
        flow_walk_stmts(&stats, ft.body[:], 1)
        if flow_missing_return(ft) {
            name := ft.source_name if ft.source_name != "" else ft.name
            // Same message + span the inline check used (ft.body_span == s.span).
            check_error(c, ft.body_span, TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, name)
            append(&stats.missing_return, name)
        }
        flow_check_unused(ft, &stats.unused_err)
    }
    flow_dump_stats(stats)
}

// All-paths-return analysis, recomputed over the durable scope (ft.return_types
// + ft.body) — a faithful copy of the inline check (check_scope_body ~8778):
// a non-void function whose first return isn't `any` and whose returns aren't
// all-err must return on every path. always_returns / is_any / all_err_returns
// are the same shared helpers the inline site uses, so this is the SAME verdict,
// just relocated to the post-check pass.
flow_missing_return :: proc(ft: ^Type_Scope) -> bool {
    if len(ft.return_types) == 0 { return false }       // void
    if is_any(ft.return_types[0]) { return false }      // unresolved generic return
    if all_err_returns(ft.return_types) { return false } // all-err can fall off (.Ok fill)
    return !always_returns(ft.body)
}

// --- must-use-err ---------------------------------------------------------
// An err-typed local that is declared but never read — not checked, not
// propagated with `?` (which leaves no binding), not discarded with `_` — is an
// error. This reproduces the inline check_unused_locals/flag_unused_local over
// the durable body: a per-block scope close over that block's own err-decls,
// with a read ANYWHERE in the block or a descendant clearing it. Shadowing is
// respected via the frame stack (a read binds the nearest enclosing decl).
//
// VALIDATION MODE: flagged names are collected into `out`, NOT emitted — the
// inline check is still authoritative. Green programs must collect nothing
// (they compile), and an unused-err fixture must show up.

Flow_Err_Local :: struct {
    span: Span,
    read: bool,
}

// One lexical block's err-typed locals (name -> declared/read). Empty for the
// vast majority of blocks, so the map is allocated lazily on first err-decl.
Flow_Frame :: struct {
    errs: map[string]Flow_Err_Local,
}

flow_check_unused :: proc(ft: ^Type_Scope, out: ^[dynamic]string) {
    stack: [dynamic]^Flow_Frame
    defer delete(stack)
    flow_unused_block(&stack, ft.body[:], out)
}

// Walk one block: push a frame, process its statements (recording err-decls and
// marking reads on the stack), then at close flag every err-decl left unread.
flow_unused_block :: proc(stack: ^[dynamic]^Flow_Frame, stmts: []Stmt, out: ^[dynamic]string) {
    frame: Flow_Frame
    append(stack, &frame)
    for s in stmts { flow_unused_stmt(stack, s, out) }
    for name, loc in frame.errs {
        if !loc.read { append(out, name) }
    }
    delete(frame.errs)
    pop(stack)
}

flow_unused_stmt :: proc(stack: ^[dynamic]^Flow_Frame, s: Stmt, out: ^[dynamic]string) {
    #partial switch v in s {
    case ^Stmt_Decl:
        for e in v.init_values { flow_expr_reads(stack, e) }
        flow_expr_reads(stack, v.slice_cap_expr)
        // The desugared `.checked` carries the per-name resolved types; the span
        // stays the Stmt_Decl's, matching the inline flag_unused_local location.
        for inner in v.checked {
            #partial switch a in inner {
            case ^Stmt_Assign:
                if a.is_decl { flow_record_err_decl(stack, a.name, a.var_type, v.span) }
            case ^Stmt_Multi_Return_Assign:
                if a.is_decl {
                    for n, i in a.names {
                        if i < len(a.var_types) { flow_record_err_decl(stack, n, a.var_types[i], v.span) }
                    }
                }
            }
        }
    case ^Stmt_Assign:
        flow_expr_reads(stack, v.value)
        flow_expr_reads(stack, v.target)
        if v.is_decl { flow_record_err_decl(stack, v.name, v.var_type, v.span) }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { flow_unused_stmt(stack, a, out) }
    case ^Stmt_Multi_Return_Assign:
        for e in v.values { flow_expr_reads(stack, e) }
        for e in v.targets { flow_expr_reads(stack, e) }
    case Stmt_Call:
        flow_expr_reads(stack, v.expr)
    case Stmt_Return:
        for e in v.values { flow_expr_reads(stack, e) }
    case ^Stmt_If:
        flow_expr_reads(stack, v.condition)
        flow_unused_block(stack, v.body[:], out)
        flow_unused_block(stack, v.else_body[:], out)
    case ^Stmt_For:
        if v.init != nil { flow_unused_stmt(stack, v.init, out) }
        flow_expr_reads(stack, v.condition)
        flow_expr_reads(stack, v.range_low)
        flow_expr_reads(stack, v.range_high)
        flow_expr_reads(stack, v.collection)
        flow_expr_reads(stack, v.collection_len)
        flow_unused_block(stack, v.body[:], out)
        if v.post != nil { flow_unused_stmt(stack, v.post, out) }
    case ^Stmt_Match:
        flow_expr_reads(stack, v.subject)
        for arm in v.arms {
            flow_expr_reads(stack, arm.value)
            flow_unused_block(stack, arm.body[:], out)
        }
    case ^Stmt_Defer:
        flow_unused_block(stack, v.body[:], out)
    }
}

// Record an err-typed declared name into the innermost frame. Skips `_` and
// non-err types — exactly what flag_unused_local actions today.
flow_record_err_decl :: proc(stack: ^[dynamic]^Flow_Frame, name: string, t: Type, span: Span) {
    if name == "_" || name == "" { return }
    if !is_err_type(t) { return }
    top := stack[len(stack) - 1]
    if top.errs == nil { top.errs = make(map[string]Flow_Err_Local) }
    top.errs[name] = Flow_Err_Local{span = span, read = false}
}

// Mark a name read in the NEAREST enclosing frame that declared it as an err —
// the shadowing-correct equivalent of the inline read flag reaching the binding's
// declaring env via the chain.
flow_mark_read :: proc(stack: ^[dynamic]^Flow_Frame, name: string) {
    #reverse for frame in stack^ {
        if loc, ok := frame.errs[name]; ok {
            loc.read = true
            frame.errs[name] = loc
            return
        }
    }
}

// Recursively mark every identifier read in an expression. A bare Expr_Ident is
// the read; everything else just recurses into sub-expressions. Leaves
// (literals, Self, size_of, type names) contain no local reads. Call names are
// NOT reads — the inline checker marks reads at Expr_Ident sites only, and a
// call's callee is a name string, not an ident.
flow_expr_reads :: proc(stack: ^[dynamic]^Flow_Frame, e: Expr) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:
        flow_mark_read(stack, v.name)
    case ^Expr_Unary:
        flow_expr_reads(stack, v.operand)
    case ^Expr_Binary:
        flow_expr_reads(stack, v.left)
        flow_expr_reads(stack, v.right)
    case ^Expr_Call:
        flow_expr_reads(stack, v.qualifier)
        for a in v.args { flow_expr_reads(stack, a) }
        if v.overrides != nil {
            for f in v.overrides.fields { flow_expr_reads(stack, f.value) }
        }
    case ^Expr_Index:
        flow_expr_reads(stack, v.expr)
        flow_expr_reads(stack, v.index)
    case ^Expr_Slice:
        flow_expr_reads(stack, v.expr)
        flow_expr_reads(stack, v.low)
        flow_expr_reads(stack, v.high)
    case ^Expr_Field_Access:
        flow_expr_reads(stack, v.expr)
    case ^Expr_Array:
        for el in v.elements { flow_expr_reads(stack, el) }
    case ^Expr_Struct_Literal:
        for f in v.fields { flow_expr_reads(stack, f.value) }
    case ^Expr_Try:
        flow_expr_reads(stack, v.inner)
    case ^Expr_If:
        flow_expr_reads(stack, v.condition)
        flow_expr_reads(stack, v.then_expr)
        flow_expr_reads(stack, v.else_expr)
    case ^Expr_Assert:
        flow_expr_reads(stack, v.cond)
    case ^Expr_Take:
        flow_expr_reads(stack, v.storage)
        flow_expr_reads(stack, v.count_expr)
    }
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
    fmt.eprintf("[flow] missing-return flagged: %d %v\n",
        len(stats.missing_return), stats.missing_return)
    fmt.eprintf("[flow] unused-err flagged: %d %v\n",
        len(stats.unused_err), stats.unused_err)
}
