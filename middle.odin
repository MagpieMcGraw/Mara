package mara

import "core:mem/virtual"
import "core:os"
import "core:slice"
import "core:strconv"
import "core:sync"
import "core:thread"
import "core:time"

// middle.odin — the middle end, a code at a time. Each code is lowered on
// its own (lw_code), then folded and analysed while what it calls is
// analysed already: callees first, a recursive group of funs together (the
// call graph's strongly connected components, bottom-up — it's made from the
// annotations, before any code). Constants and structs' codes are lowered
// first: folding a constant's value runs them. What the analyses find is kept
// and reported once every code is (middle_report), in the order the
// program-wide passes reported it. Every code is kept: the lowered program,
// put in place in written order, is what codegen, ask and serve read.
//
// The work is shared out to workers, each a thread (Middle_Worker): a
// lowering of its own (lw_worker), its own state for each analysis, its own
// memory (its builder's store). What workers share they only read, or add to
// under the program's lock (Graph_Program.lock): the codes built, the
// constants' tables. Constants and structs are any worker's; a component of
// the call graph is a worker's once every component it calls is done; what's
// left, any worker's.

Middle :: struct {
    on:      bool,
    prog:    ^Graph_Program,     // the codes lowered
    workers: [dynamic]^Middle_Worker,
    escape:  [dynamic][dynamic]Esc_Diag,   // each worker's escape diagnostics
    analysed: time.Duration,               // the analyses' time, every worker's: told apart from lowering's in the build's timings
}

// One worker of the middle end: its lowering and what its analyses keep.
Middle_Worker :: struct {
    k:     ^TC,
    flow:  Flow_Pass,
    reach: Reach_Pass,
    fold:  Folder,
    analysed: time.Duration,   // its analyses' time (Middle.analysed)
}

// Every code lowered and analysed, then put in place in written order.
middle_program :: proc(k: ^TC, c: ^Checker, checked: ^Checked_Program, fns: []^Type_Scope) -> Middle {
    mid := Middle{on = true}
    saved_salt, saved_pkg, saved_subst := TC_Salt{salt = k.salt, lo = k.salt_lo, hi = k.salt_hi}, k.pkg, k.subst
    defer {
        tc_salt_set(k, saved_salt)
        k.pkg, k.subst = saved_pkg, saved_subst
    }
    p, codes := lower_begin(k)
    shared := lw_shared_sizes(k) if ODIN_DEBUG else nil
    mid.prog = p
    pc := &p.pc
    pc.lock = &p.lock
    g_infer_frozen = true
    defer g_infer_frozen = false
    // The workers: one — a build is sequential, its time the work's
    // (MARA_LOWER_WORKERS: a thread each, as many as it says).
    n := 1
    if s := os.get_env("MARA_LOWER_WORKERS", context.temp_allocator); s != "" { n = max(1, strconv.parse_int(s) or_else 1) }
    for _ in 0 ..< n {
        mw := new(Middle_Worker)
        mw^ = {k = lw_worker(k, p), flow = flow_pass_make(fns), fold = graph_fold_begin(pc, checked)}
        append(&mid.workers, mw)
    }
    resize(&mid.escape, n)
    escape_begin(c, pc)
    run := Middle_Run{mid = &mid, codes = &codes, cg = c.cg}

    // Constants, and the structs a constant's value may construct.
    for e, i in k.events {
        #partial switch e.kind {
        case .Const, .Program_Struct: append(&run.list, i)
        case .Body:                   if e.sc.ts.kind == .Struct { append(&run.list, i) }
        }
    }
    middle_threads(&run, proc(run: ^Middle_Run, mw: ^Middle_Worker) {
        for i in middle_take(run) { lw_code(mw.k, run.codes, i) }
    })
    // ... folded now, before any fun is lowered: what folding a constant
    // runs — a struct's code — is done changing before it's read.
    folding := time.tick_now()
    for g, i in codes.code {
        if g == nil || codes.folded[i] { continue }
        graph_fold_code(&mid.workers[0].fold, mid.workers[0].k.gb, g)
        codes.folded[i] = true
    }
    mid.analysed += time.tick_since(folding)
    // Each component's funs, then the component's escape analysis, then each
    // one's own — once the components it calls are done.
    middle_components(&run)
    middle_threads(&run, proc(run: ^Middle_Run, mw: ^Middle_Worker) {
        for s in middle_ready(run) {
            middle_scc(mw, run.codes, run.cg, run.cg.sccs[s][:])
            middle_done(run, s)
        }
    })
    // What no call graph node is: the constants, a struct nothing constructs
    // or calls, the program's struct.
    clear(&run.list)
    run.next = 0
    for e, i in k.events { if e.kind != .Module_Stmt { append(&run.list, i) } }
    middle_threads(&run, proc(run: ^Middle_Run, mw: ^Middle_Worker) {
        for i in middle_take(run) {
            lw_code(mw.k, run.codes, i)
            middle_analyse(mw, run.codes, i)
        }
    })
    pc.lock = nil
    lower_place(mid.workers[0].k, &codes)
    folders := make([dynamic]^Folder, context.temp_allocator)
    for mw in mid.workers { append(&folders, &mw.fold) }
    ending := time.tick_now()
    graph_fold_end(folders[:])
    mid.analysed += time.tick_since(ending)
    for mw in mid.workers { mid.analysed += mw.analysed }
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

// The work the workers share out, and where it's at.
Middle_Run :: struct {
    mid:     ^Middle,
    codes:   ^LW_Codes,
    cg:      ^Call_Graph,
    lock:    sync.Mutex,
    // Events, any worker's: the next one to take.
    list:    [dynamic]int,
    next:    int,
    // The call graph's components: each one's callees' left to be done; who
    // calls each; those ready, with none left; how many aren't done.
    waits:   []int,
    callers: [][dynamic]int,
    ready:   [dynamic]int,
    left:    int,
    changed: sync.Cond,   // (one done: more may be ready, or none left)
}

// Each worker's thread runs `work`, its memory its own (its builder's
// store); then each is joined. One worker — the default — works on the
// calling thread: no thread to start.
middle_threads :: proc(run: ^Middle_Run, work: proc(run: ^Middle_Run, mw: ^Middle_Worker)) {
    jobs := make([]Middle_Job, len(run.mid.workers), context.temp_allocator)
    for mw, i in run.mid.workers { jobs[i] = {run, mw, work, i} }
    if len(jobs) == 1 {
        middle_job(&jobs[0])
        return
    }
    threads := make([]^thread.Thread, len(run.mid.workers), context.temp_allocator)
    for _, i in run.mid.workers {
        threads[i] = thread.create(proc(t: ^thread.Thread) { middle_job((^Middle_Job)(t.data)) })
        threads[i].data = &jobs[i]
        thread.start(threads[i])
    }
    for t in threads {
        thread.join(t)
        thread.destroy(t)
    }
}

// The events left, a worker's turn at a time: the next one it takes.
middle_take :: proc(run: ^Middle_Run) -> (i: int, ok: bool) {
    sync.mutex_lock(&run.lock)
    defer sync.mutex_unlock(&run.lock)
    if run.next >= len(run.list) { return }
    i, ok = run.list[run.next], true
    run.next += 1
    return
}

// The call graph's components, each with the components it calls to wait
// for (bottom-up: none, first).
middle_components :: proc(run: ^Middle_Run) {
    cg := run.cg
    run.waits = make([]int, len(cg.sccs))
    run.callers = make([][dynamic]int, len(cg.sccs))
    for scc, s in cg.sccs {
        for node in scc {
            for to in cg.out_edges[node] {
                callee := cg.scc_of[to]
                if callee == s || slice.contains(run.callers[callee][:], s) { continue }
                append(&run.callers[callee], s)
                run.waits[s] += 1
            }
        }
    }
    run.left = len(cg.sccs)
    for w, s in run.waits { if w == 0 { append(&run.ready, s) } }
}

// The next component ready — waiting for one, while any is left.
middle_ready :: proc(run: ^Middle_Run) -> (s: int, ok: bool) {
    sync.mutex_lock(&run.lock)
    defer sync.mutex_unlock(&run.lock)
    for len(run.ready) == 0 && run.left > 0 { sync.cond_wait(&run.changed, &run.lock) }
    if len(run.ready) == 0 { return }
    return pop(&run.ready), true
}

// A component done: the components calling it wait for one less.
middle_done :: proc(run: ^Middle_Run, s: int) {
    sync.mutex_lock(&run.lock)
    defer sync.mutex_unlock(&run.lock)
    run.left -= 1
    for caller in run.callers[s] {
        run.waits[caller] -= 1
        if run.waits[caller] == 0 { append(&run.ready, caller) }
    }
    sync.cond_broadcast(&run.changed)
}

Middle_Job :: struct { run: ^Middle_Run, mw: ^Middle_Worker, work: proc(run: ^Middle_Run, mw: ^Middle_Worker), index: int }

// A worker's work, in its memory (its builder's store), with its own escape
// state.
middle_job :: proc(job: ^Middle_Job) {
    in_store := virtual.arena_allocator(job.mw.k.gb.store.arena)
    context.allocator = in_store
    context.temp_allocator = in_store
    escape_thread_begin(&job.run.mid.prog.pc)
    job.work(job.run, job.mw)
    esc := escape_thread_end()
    append(&job.run.mid.escape[job.index], ..esc[:])
}

// A component of the call graph: its funs lowered, its escape analysis run,
// each fun analysed — a worker's, once its callees' are done.
middle_scc :: proc(mw: ^Middle_Worker, codes: ^LW_Codes, cg: ^Call_Graph, scc: []int) {
    members := make([dynamic]^Type_Scope, 0, len(scc), context.temp_allocator)
    for node in scc {
        if i, checked := codes.bodies[cg.nodes[node]]; checked { lw_code(mw.k, codes, i) }
        if cg.nodes[node] != nil { append(&members, cg.nodes[node]) }   // (nil: a constant's value's calls, run at no fun's)
    }
    analysing := time.tick_now()
    reach_scc(&mw.k.gb.prog.pc, &mw.reach, members[:])
    escape_scc(cg, scc)
    mw.analysed += time.tick_since(analysing)
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
    analysing := time.tick_now()
    defer mw.analysed += time.tick_since(analysing)
    when ODIN_DEBUG {   // (what it calls is built — else what a call reaches would be guessed at)
        for id := Node_Id(0); id <= g.end; id += 1 {
            if g.kind[id] != .Op || (g.op[id] != .Call && g.op[id] != .Construct) { continue }
            callee := graph_called(g, id)
            if callee == nil || graph_fun_code(&b.prog.pc, callee) != nil { continue }
            if j, checked := codes.bodies[callee]; checked && !codes.done[j] {
                graph_fatal(graph_origin(g, id), "'%s' analysed before '%s', which it calls, is built", graph_name(g, 0), callee.name)
            }
        }
    }
    if !codes.folded[i] {
        graph_fold_code(&mw.fold, b, g)
        codes.folded[i] = true
    }
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
        graph_builder_free(mw.k.gb, virtual.arena_allocator(mw.k.gb.store.arena))
        free(mw.k)
        free(mw)
    }
    delete(mid.workers)
}
