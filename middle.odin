package mara

import "core:os"
import "core:slice"
import "core:strconv"

// middle.odin — the middle end, a code at a time. Each code is lowered on
// its own (lw_code), then folded and analysed while what it calls is
// analysed already: callees first, a recursive group of funs together (the
// call graph's strongly connected components, bottom-up — it's made from the
// annotations, before any code). Constants and structs' codes are lowered
// first: folding a constant's value runs them. What the analyses find is kept
// and reported once every code is (middle_report), in the order the
// program-wide passes reported it.
//
// The work is a worker's at a time (Middle_Worker): a lowering of its own
// (lw_worker), its own state for each analysis. What workers share they only
// read, or add to under the program's lock (Graph_Program.lock): the codes
// built, the constants' tables.

Middle :: struct {
    on:      bool,
    prog:    ^Graph_Program,     // the codes lowered
    workers: [dynamic]^Middle_Worker,
    escape:  [dynamic][dynamic]Esc_Diag,   // each thread's escape diagnostics
}

// One worker of the middle end: its lowering and what its analyses keep.
Middle_Worker :: struct {
    k:     ^TC,
    flow:  Flow_Pass,
    reach: Reach_Pass,
    fold:  Folder,
}

// Every code lowered and analysed, then put in place in written order.
middle_program :: proc(k: ^TC, c: ^Checker, checked: ^Checked_Program, fns: []^Type_Scope) -> Middle {
    mid := Middle{on = true}
    saved_salt, saved_pkg, saved_subst := TC_Salt{k.salt, k.salt_lo, k.salt_hi}, k.pkg, k.subst
    defer {
        tc_instance_end(k, saved_salt)
        k.pkg, k.subst = saved_pkg, saved_subst
    }
    p, codes := lower_begin(k)
    shared := lw_shared_sizes(k) if ODIN_DEBUG else nil
    mid.prog = p
    pc := &p.pc
    pc.lock = &p.lock
    g_infer_frozen = true
    defer g_infer_frozen = false
    // The workers: one. (A debug build can deal codes out to several in
    // turn, MARA_LOWER_WORKERS — what one builds next to another's.)
    n := 1
    when ODIN_DEBUG {
        if s := os.get_env("MARA_LOWER_WORKERS", context.temp_allocator); s != "" { n = max(1, strconv.parse_int(s) or_else 1) }
    }
    for _ in 0 ..< n {
        mw := new(Middle_Worker)
        mw^ = {k = lw_worker(k, p), flow = flow_pass_make(fns), fold = graph_fold_begin(pc, checked)}
        append(&mid.workers, mw)
    }
    escape_begin(c, pc)
    escape_thread_begin(pc)
    turn := 0
    next :: proc(mid: ^Middle, turn: ^int) -> ^Middle_Worker {
        mw := mid.workers[turn^ % len(mid.workers)]
        turn^ += 1
        return mw
    }

    // Constants, and the structs a constant's value may construct.
    for e, i in k.events {
        mw := next(&mid, &turn)
        #partial switch e.kind {
        case .Const, .Program_Struct: lw_code(mw.k, &codes, i)
        case .Body:                   if e.sc.ts.kind == .Struct { lw_code(mw.k, &codes, i) }
        }
    }
    // Each component's funs, then the component's escape analysis, then each
    // one's own.
    cg := c.cg
    for scc in cg.sccs { middle_scc(next(&mid, &turn), &codes, cg, scc[:]) }
    // What no call graph node is: the constants, a struct nothing constructs
    // or calls, the program's struct — in the order checked.
    for e, i in k.events {
        if e.kind == .Module_Stmt { continue }
        mw := next(&mid, &turn)
        lw_code(mw.k, &codes, i)
        middle_analyse(mw, &codes, i)
    }
    append(&mid.escape, escape_thread_end())
    pc.lock = nil
    lower_place(mid.workers[0].k, &codes)
    folders := make([dynamic]^Folder, context.temp_allocator)
    for mw in mid.workers { append(&folders, &mw.fold) }
    graph_fold_end(folders[:])
    when ODIN_DEBUG {
        after := lw_shared_sizes(k)
        for mw in mid.workers {
            worker := lw_shared_sizes(mw.k)
            if !slice.equal(shared[:], after[:]) || !slice.equal(shared[:], worker[:]) {
                graph_fatal({}, "lowering added to what lowerings share: %v, then %v (its view: %v)", shared[:], after[:], worker[:])
            }
        }
    }
    return mid
}

// A component of the call graph: its funs lowered, its escape analysis run,
// each fun analysed — a worker's, once its callees' are done.
middle_scc :: proc(mw: ^Middle_Worker, codes: ^LW_Codes, cg: ^Call_Graph, scc: []int) {
    for node in scc {
        if i, checked := codes.bodies[cg.nodes[node]]; checked { lw_code(mw.k, codes, i) }
    }
    escape_scc(cg, scc)
    for node in scc {
        if i, checked := codes.bodies[cg.nodes[node]]; checked { middle_analyse(mw, codes, i) }
    }
}

// An event's code analysed, once: folded where it uses constants, then its
// flow and what its calls reach.
middle_analyse :: proc(mw: ^Middle_Worker, codes: ^LW_Codes, i: int) {
    if codes.analysed[i] { return }
    codes.analysed[i] = true
    g := codes.code[i]
    if g == nil { return }
    b := mw.k.gb
    when ODIN_DEBUG {   // (what it calls is built — else what a call reaches would be guessed at)
        for id := Node_Id(0); id <= g.end; id += 1 {
            if g.kind[id] != .Op || (g.op[id] != .Call && g.op[id] != .Construct) { continue }
            callee := graph_called(g, id)
            if callee == nil || graph_fun_code(&b.prog.pc, callee) != nil { continue }
            if j, checked := codes.bodies[callee]; checked && !codes.done[j] {
                graph_fatal(g.origin[id], "'%s' analysed before '%s', which it calls, is built", graph_name(g, 0), callee.name)
            }
        }
    }
    graph_fold_code(&mw.fold, b, g)
    flow_code(&mw.flow, g)
    if g.kind[0] != .Const { reach_code(&mw.reach, &b.prog.pc, g) }
}

// What the middle end found, reported: flow's, escape's, what calls reach —
// every worker's.
middle_report :: proc(c: ^Checker, checked: ^Checked_Program, mid: ^Middle, fns: []^Type_Scope, void_defaults: map[Span]bool) {
    flows := make([dynamic]^Flow_Pass, context.temp_allocator)
    reaches := make([dynamic]^Reach_Pass, context.temp_allocator)
    for mw in mid.workers {
        append(&flows, &mw.flow)
        append(&reaches, &mw.reach)
    }
    flow_report(c, checked, flows[:], fns, void_defaults)
    for fp in flows { flow_pass_free(fp) }
    escape_report(c, mid.escape[:])
    reach_report(c, reaches[:])
}

// The workers let go of: their lowerings' builders and views.
middle_free :: proc(mid: ^Middle) {
    for mw in mid.workers {
        graph_builder_free(mw.k.gb)
        free(mw.k)
        free(mw)
    }
    delete(mid.workers)
}
