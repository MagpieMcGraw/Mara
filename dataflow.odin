package mara

import "core:fmt"

// Forward dataflow over a fun's runs (graph_code_runs: its code's, then its
// defer blocks'): each run's entry state is joined from every way into it —
// the run before it (a `then` edge) and, for a defer block's first run, each
// run-defer that runs it, at that point — and a loop goes round to its
// fixpoint. The analyses on it (definite assignment, reaching definitions,
// escape) differ in their state and in what an operation does to it.

Run_Flow :: struct($S: typeid) {
    g:        ^Program_Graph,
    runs:     []i32,
    run_at:   map[i32]int,       // a run → its place in runs
    slots:    int,               // a state's length
    in_state: [][]S,             // each run's entry state, once entered
    entered:  []bool,
    queued:   []bool,
    todo:     [dynamic]int,
    copy:     proc(dst, src: []S),
    join:     proc(dst, src: []S) -> bool,   // dst joined with src: whether it grew
}

run_flow_make :: proc(g: ^Program_Graph, runs: []i32, slots: int,
                      copy: proc(dst, src: []$S), join: proc(dst, src: []S) -> bool) -> (f: Run_Flow(S)) {
    f.g, f.runs, f.slots, f.copy, f.join = g, runs, slots, copy, join
    for r, i in runs { f.run_at[r] = i }
    f.in_state = make([][]S, len(runs))
    f.entered = make([]bool, len(runs))
    f.queued = make([]bool, len(runs))
    return
}

run_flow_free :: proc(f: ^Run_Flow($S)) {
    for s in f.in_state { delete(s) }
    delete(f.in_state)
    delete(f.entered)
    delete(f.queued)
    delete(f.todo)
    delete(f.run_at)
}

// Run ri goes again (a value it reads grew).
run_flow_queue :: proc(f: ^Run_Flow($S), ri: int) {
    if f.queued[ri] { return }
    f.queued[ri] = true
    append(&f.todo, ri)
}

// Run ri is entered with `state`: joined into its entry state, and queued
// when that grew (or it is entered first).
run_flow_enter :: proc(f: ^Run_Flow($S), ri: int, state: []S) {
    if !f.entered[ri] {
        f.entered[ri] = true
        f.in_state[ri] = make([]S, f.slots)
        f.copy(f.in_state[ri], state)
        run_flow_queue(f, ri)
        return
    }
    if f.join(f.in_state[ri], state) { run_flow_queue(f, ri) }
}

// The run a `then` edge (or a defer block's entry) lands in, by its place in
// runs; ok false for one outside them.
run_flow_at :: proc(f: ^Run_Flow($S), to: Node_Id) -> (int, bool) {
    return f.run_at[f.g.run_starts[to]]
}

// The fixpoint, from `entry` (the first run's state): `step` runs each
// operation on the state — a run-defer once the defer block it runs is
// entered with the state there.
run_flow_solve :: proc(f: ^Run_Flow($S), entry: []S, data: $D, step: proc(data: D, ri: int, op: Node_Id, state: []S)) {
    if len(f.runs) == 0 { return }
    g := f.g
    run_flow_enter(f, 0, entry)
    state := make([]S, f.slots)
    defer delete(state)
    visits := 0
    for len(f.todo) > 0 {
        ri := pop(&f.todo)
        f.queued[ri] = false
        visits += 1
        if visits > 10_000_000 { fmt.panicf("dataflow over %d runs did not converge", len(f.runs)) }
        f.copy(state, f.in_state[ri])
        ops := graph_run(g, int(f.runs[ri]))
        for op in ops {
            if g.op[op] == .Run_Defer {
                for in_ in graph_out(g, g.defer_of[op]) {
                    if di, ok := run_flow_at(f, in_.to); ok { run_flow_enter(f, di, state) }
                }
            }
            step(data, ri, op, state)
        }
        for e in graph_out(g, ops[len(ops) - 1]) {
            if si, ok := run_flow_at(f, e.to); ok { run_flow_enter(f, si, state) }
        }
    }
}

// The bit-set state of the analyses that track facts per variable: a join is
// a union.
bits_copy :: proc(dst, src: []u64) { copy(dst, src) }

bits_union :: proc(dst, src: []u64) -> (grew: bool) {
    for w, i in src {
        if dst[i] | w != dst[i] { dst[i] |= w; grew = true }
    }
    return
}

bits_set :: proc(b: []u64, i: int) { b[i / 64] |= 1 << uint(i % 64) }

bits_clear :: proc(b: []u64, i: int) { b[i / 64] &~= 1 << uint(i % 64) }

bits_has :: proc(b: []u64, i: int) -> bool { return b[i / 64] & (1 << uint(i % 64)) != 0 }

bits_clear_mask :: proc(b, mask: []u64) { for m, i in mask { b[i] &~= m } }
