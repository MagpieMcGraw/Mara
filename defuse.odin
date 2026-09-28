package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Def-use over the program graph: what `mara ask`'s flow views slice
// (design/graph_retrofit.md, phase 2).
//
// A variable is a fun's param, local or named result: a declaration node of
// its own code (a nested fun's are its own). A synthetic local (a loop's end,
// an if-expression's value, a temp) is part of the code that reads it: seen
// through, never a variable.
//
// A definition is one statement's writes to one variable, or a param's entry.
// Its kind is its statement's (`x := v` a declaration, `x.f = v` a write), its
// line the statement's, and what it reads the operands of its writes. A call
// contributes only the arguments its result is computed from (the call
// graph's return-dependency summary) unless every input is asked for.
//
// Reaching definitions are dataflow over the runs: a whole write replaces the
// variable's definitions, a partial one adds to them, a join unions its
// incoming states, and a loop iterates to its fixpoint. A defer's block sees
// the state at each exit that runs it; what it writes stays inside it.
//
// Control dependence is post-dominance over the runs of a fun's code: a
// statement is guarded by the if, loop or match whose branch decides whether
// it runs, early returns included. A `?` is no branch here, as in the text.
// ---------------------------------------------------------------------------

Binding_Kind :: enum { Local, Param }

// A variable of a fun, as the flow views name it.
Var_Binding :: struct {
    node:        Node_Id,
    name:        string,
    fn:          ^Type_Scope,
    kind:        Binding_Kind,
    span:        Span,
    param_index: int,     // its position when a param; -1 otherwise
    type_:       Type,
}

Def_Kind :: enum { Param, Decl, Assign, Loop_Var, Destructure, Complex }

// One definition. A synthetic local's have no binding: they are seen through.
Def :: struct {
    binding: ^Var_Binding,
    var:     Node_Id,
    kind:    Def_Kind,
    stmt:    i32,                // in the graph's stmts; -1 for a param's entry
    span:    Span,
    writes:  [dynamic]Node_Id,   // the operations it takes its value from
    valued:  bool,               // some write carries a value (not a bare zero or construction)
    run:     i32,                // the run of its first write, for its guards; -1 for a param
    at_entry: bool,              // defined from the fun's entry: a param, a declaration that stores nothing
    guards:  []Guard,
    order:   int,                // creation order: source order among defs sharing a span
}

// Source order, total: defs that share a span (a fun's params, `a, b := f()`)
// fall back to creation order, which follows the source within a statement.
def_less :: proc(a, b: ^Def) -> bool {
    if a.span.file != b.span.file { return a.span.file < b.span.file }
    if a.span.line != b.span.line { return a.span.line < b.span.line }
    if a.span.col != b.span.col { return a.span.col < b.span.col }
    return a.order < b.order
}

// A statement that decides whether another runs: an if, a loop, a match.
Guard_Kind :: enum { If, For, Match }
Guard :: struct {
    kind:  Guard_Kind,
    span:  Span,
    conds: []Operand,   // what it branches on
}

// One call of a fun: the call operation and the fun it runs in.
Fn_Call_Site :: struct {
    caller: ^Type_Scope,
    op:     Node_Id,
}

// One fun's analysis.
Du_Fn :: struct {
    ft:      ^Type_Scope,
    node:    Node_Id,
    vars:    [dynamic]^Var_Binding,
    defs:    [dynamic]^Def,        // its variables' and synthetic locals' definitions
    runs:    [dynamic]i32,         // its code's runs, then its defer blocks'
    main:    int,                  // how many of `runs` are its code's own
    returns: [dynamic]Node_Id,     // its explicit returns
    ret_run: map[Node_Id]i32,
    calls:   [dynamic]Node_Id,     // its calls, constructions and prints
    guards:  map[i32][dynamic]Guard,  // a run → the statements guarding it (on `control`)
    guarded: bool,
}

Def_Use :: struct {
    fns:          map[^Type_Scope]^Du_Fn,
    bindings:     map[Node_Id]^Var_Binding,
    vars:         [dynamic]^Var_Binding,   // every analyzed variable
    defs:         [dynamic]^Def,           // every analyzed variable's definitions
    reaching:     map[Node_Id][]^Def,      // a use (a var operation) → the definitions that may reach it
    starts:       map[Node_Id]i32,         // each run's first operation → the run
    want_control: bool,                    // `control`: guards too (post-dominators)
    order:        int,
}

// --- analysis ---------------------------------------------------------------

// A fun's def-use, built the first time it is asked for (with its guards,
// on `control`).
du_fn :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> ^Du_Fn {
    du := &checked.du
    if ft == nil || ft.kind != .Fun { return nil }
    f, done := du.fns[ft]
    if !done {
        f = new(Du_Fn)
        f.ft = ft
        du.fns[ft] = f
        du_build(checked, f)
        du_dump(checked, f)
    }
    if du.want_control && !f.guarded { du_guards(checked, f) }
    return f
}

// Every fun's def-use: the whole-program views (a type's values, a fun's
// call sites) seed across functions. Data only: guards are built on demand
// for the functions a slice touches.
du_all :: proc(checked: ^Checked_Program) {
    want := checked.du.want_control
    checked.du.want_control = false
    defer checked.du.want_control = want
    for _, ft in checked.functions { du_fn(checked, ft) }
}

@(private="file")
du_build :: proc(checked: ^Checked_Program, f: ^Du_Fn) {
    du := &checked.du
    g := &checked.graph
    node, ok := g.scope_node[f.ft]
    if !ok { return }   // a template: only its instances have code
    f.node = node
    if len(du.starts) == 0 { du.starts = graph_run_starts(g) }

    // Its variables, and the synthetic locals seen through: its own subtree,
    // less the subtrees of what it defines.
    tracked: map[Node_Id]int
    defer delete(tracked)
    params := 0
    for id := node + 1; id <= g.last[node]; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct, .Union, .Enum:
            id = g.last[id]
        case .Param:
            du_bind(checked, f, id, .Param, params)
            params += 1
            tracked[id] = len(tracked)
        case .Result:
            if g.written[id] == .Explicit { du_bind(checked, f, id, .Local, -1); tracked[id] = len(tracked) }
        case .Local:
            if g.written[id] == .Explicit { du_bind(checked, f, id, .Local, -1) }
            tracked[id] = len(tracked)
        }
    }

    // Its runs: its code's, then each defer block's, entered by a run defer.
    seen: map[i32]bool
    defer delete(seen)
    du_collect_runs(g, du.starts, node, &f.runs, &seen)
    f.main = len(f.runs)
    for i := 0; i < len(f.runs); i += 1 {
        for op in graph_run(g, int(f.runs[i])) {
            if g.op[op] != .Run_Defer { continue }
            for e in graph_out(g, op) {
                if e.kind == .Runs { du_collect_runs(g, du.starts, e.to, &f.runs, &seen) }
            }
        }
    }

    // Views: a synthetic local set to a slice of a variable (`dst[lo:] = src`
    // writes through one). What is written through it writes that variable.
    views: map[Node_Id]Node_Id
    defer delete(views)
    for r in f.runs {
        for op in graph_run(g, int(r)) {
            if g.op[op] != .Write { continue }
            t, whole, ok := du_written(g, op)
            if !ok || !whole || t not_in tracked || t in du.bindings { continue }
            val := graph_operands(g, op)[1].op
            if val == NO_NODE || g.op[val] != .Slice { continue }
            if v, vok := du_place_root(g, graph_operands(g, val)[0].op); vok && v in du.bindings {
                views[t] = v
            }
        }
    }

    // Its definitions: a param's entry, then each statement's writes.
    def_of: map[[2]i32]^Def   // (variable, statement) → its definition
    defer delete(def_of)
    for b in f.vars {
        if b.kind == .Param { du_def(checked, f, &def_of, b.node, -1, g.origin[b.node]) }
    }
    for r, ri in f.runs {
        for op in graph_run(g, int(r)) {
            #partial switch g.op[op] {
            case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Variant:
                v, _, is_def := du_target(g, views, op)
                if !is_def || v not_in tracked { break }
                s := g.stmt[op]
                d := du_def(checked, f, &def_of, v, s, g.stmts[s].span if s >= 0 else g.origin[op])
                if d.run < 0 { d.run = r }
                if !du_is_step(g, op) {
                    append(&d.writes, op)
                    if du_write_valued(g, op) { d.valued = true }
                }
            case .Return:
                if ri < f.main && g.written[op] == .Explicit {
                    append(&f.returns, op)
                    f.ret_run[op] = r
                }
            }
            #partial switch g.op[op] {
            case .Call, .Construct, .Print, .Crash: append(&f.calls, op)
            }
        }
    }
    // A declaration that stores nothing (`x : T = void`) still defines its
    // variable where it is written, as from the fun's entry: a later whole
    // write replaces it.
    for b in f.vars {
        if b.kind != .Local || g.kind[b.node] != .Local { continue }
        if _, ok := def_of[[2]i32{i32(b.node), g.stmt[b.node]}]; ok { continue }
        d := du_def(checked, f, &def_of, b.node, g.stmt[b.node], g.stmts[g.stmt[b.node]].span)
        d.valued = true   // `void`, as written
        d.at_entry = true
    }
    for d in f.defs { du_classify(g, views, d) }

    // Reaching definitions: states are bit sets over the fun's definitions.
    words := (len(f.defs) + 63) / 64
    kill := make([][]u64, len(tracked))   // each variable's definitions
    defer { for k in kill { delete(k) }; delete(kill) }
    for &k in kill { k = make([]u64, words) }
    for d, i in f.defs { bits_set(kill[tracked[d.var]], i) }
    index_of: map[^Def]int
    defer delete(index_of)
    for d, i in f.defs { index_of[d] = i }

    run_at: map[i32]int   // a run → its position in f.runs
    defer delete(run_at)
    for r, i in f.runs { run_at[r] = i }
    in_state := make([][]u64, len(f.runs))
    defer { for s in in_state { delete(s) }; delete(in_state) }
    for &s in in_state { s = make([]u64, words) }
    entered := make([]bool, len(f.runs))
    defer delete(entered)

    // The entry: every param defined.
    todo: [dynamic]int
    defer delete(todo)
    if len(f.runs) > 0 {
        for d, i in f.defs { if d.kind == .Param || d.at_entry { bits_set(in_state[0], i) } }
        entered[0] = true
        append(&todo, 0)
    }
    state := make([]u64, words)
    defer delete(state)
    Transfer :: struct {
        g: ^Program_Graph, f: ^Du_Fn, def_of: ^map[[2]i32]^Def, tracked: ^map[Node_Id]int,
        kill: [][]u64, index_of: ^map[^Def]int, views: ^map[Node_Id]Node_Id,
    }
    t := Transfer{g, f, &def_of, &tracked, kill, &index_of, &views}
    apply :: proc(t: ^Transfer, op: Node_Id, state: []u64) {
        v, whole, is_def := du_target(t.g, t.views^, op)
        if !is_def { return }
        k, tracked := t.tracked[v]
        if !tracked { return }
        d := t.def_of[[2]i32{i32(v), t.g.stmt[op]}]
        if whole { bits_clear_mask(state, t.kill[k]) }
        bits_set(state, t.index_of[d])
    }
    merge_into :: proc(dst, src: []u64) -> bool {
        changed := false
        for w, i in src {
            if dst[i] | w != dst[i] { dst[i] |= w; changed = true }
        }
        return changed
    }
    for len(todo) > 0 {
        ri := pop(&todo)
        copy(state, in_state[ri])
        ops := graph_run(g, int(f.runs[ri]))
        for op in ops {
            apply(&t, op, state)
            if g.op[op] == .Run_Defer {
                for e in graph_out(g, op) {
                    if e.kind != .Runs { continue }
                    for e2 in graph_out(g, e.to) {
                        if e2.kind != .Then { continue }
                        if di, ok := run_at[du.starts[e2.to]]; ok {
                            if merge_into(in_state[di], state) || !entered[di] { entered[di] = true; append(&todo, di) }
                        }
                    }
                }
            }
        }
        for e in graph_out(g, ops[len(ops) - 1]) {
            if e.kind != .Then { continue }
            si, ok := run_at[du.starts[e.to]]
            if !ok { continue }
            if merge_into(in_state[si], state) || !entered[si] { entered[si] = true; append(&todo, si) }
        }
    }

    // The uses, against the fixpoint: every var operation naming a tracked
    // declaration, less a whole write's own destination.
    dest: map[Node_Id]bool
    defer delete(dest)
    for r in f.runs {
        for op in graph_run(g, int(r)) {
            #partial switch g.op[op] {
            case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Arena_Alloc:
                ops := graph_operands(g, op)
                if len(ops) > 0 && g.op[ops[0].op] == .Var && g.kind[ops[0].op] == .Op { dest[ops[0].op] = true }
            }
        }
    }
    for r, ri in f.runs {
        copy(state, in_state[ri])
        for op in graph_run(g, int(r)) {
            du_uses_in(g, du, f, op, state, tracked, kill, dest)
            apply(&t, op, state)
        }
    }
}

// A var operation is a use of the variable it names, unless it is where a
// whole write lands: what reaches it is that variable's definitions in the
// state just before it (a run lists operations in the order they run).
@(private="file")
du_uses_in :: proc(g: ^Program_Graph, du: ^Def_Use, f: ^Du_Fn, op: Node_Id, state: []u64,
                   tracked: map[Node_Id]int, kill: [][]u64, dest: map[Node_Id]bool) {
    if g.op[op] != .Var || op in dest { return }
    k, ok := tracked[g.refers[op]]
    if !ok { return }
    reach: [dynamic]^Def
    for d, i in f.defs {
        if bits_has(kill[k], i) && bits_has(state, i) { append(&reach, d) }
    }
    if len(reach) > 0 { du.reaching[op] = reach[:] } else { delete(reach) }
}

// The runs a scope's code reaches from its entry (a Then edge from the scope).
@(private="file")
du_collect_runs :: proc(g: ^Program_Graph, starts: map[Node_Id]i32, scope: Node_Id, out: ^[dynamic]i32, seen: ^map[i32]bool) {
    todo: [dynamic]i32
    defer delete(todo)
    for e in graph_out(g, scope) { if e.kind == .Then { append(&todo, starts[e.to]) } }
    for len(todo) > 0 {
        r := pop(&todo)
        if r in seen^ { continue }
        seen^[r] = true
        append(out, r)
        ops := graph_run(g, int(r))
        // Depth-first in edge order keeps a run's successors after it.
        for i := len(graph_out(g, ops[len(ops) - 1])) - 1; i >= 0; i -= 1 {
            e := graph_out(g, ops[len(ops) - 1])[i]
            if e.kind == .Then { append(&todo, starts[e.to]) }
        }
    }
}


// --- helpers ------------------------------------------------------------------

@(private="file")
bits_set :: proc(b: []u64, i: int) { b[i / 64] |= 1 << uint(i % 64) }

@(private="file")
bits_has :: proc(b: []u64, i: int) -> bool { return b[i / 64] & (1 << uint(i % 64)) != 0 }

@(private="file")
bits_clear_mask :: proc(b, mask: []u64) { for m, i in mask { b[i] &~= m } }

// --- variables and definitions ---------------------------------------------

@(private="file")
du_bind :: proc(checked: ^Checked_Program, f: ^Du_Fn, id: Node_Id, kind: Binding_Kind, param_index: int) {
    g := &checked.graph
    b := new(Var_Binding)
    b^ = Var_Binding{
        node = id, name = g.name[id], fn = f.ft, kind = kind, span = g.origin[id],
        param_index = param_index, type_ = g.type_[id],
    }
    append(&f.vars, b)
    append(&checked.du.vars, b)
    checked.du.bindings[id] = b
}

// The definition of variable `v` at statement `stmt`, made the first time.
@(private="file")
du_def :: proc(checked: ^Checked_Program, f: ^Du_Fn, def_of: ^map[[2]i32]^Def, v: Node_Id, stmt: i32, span: Span) -> ^Def {
    key := [2]i32{i32(v), stmt}
    if d, ok := def_of[key]; ok { return d }
    du := &checked.du
    d := new(Def)
    d^ = Def{binding = du.bindings[v], var = v, stmt = stmt, span = span, run = -1, order = du.order}
    d.kind = .Param if d.binding != nil && d.binding.kind == .Param && stmt < 0 else .Assign
    du.order += 1
    def_of[key] = d
    append(&f.defs, d)
    if d.binding != nil { append(&du.defs, d) }
    return d
}

// What an operation writes: the variable its destination is rooted at, and
// whether it replaces all of it. A match arm's binding is defined by the
// payload's place it names.
@(private="file")
du_written :: proc(g: ^Program_Graph, op: Node_Id) -> (v: Node_Id, whole: bool, ok: bool) {
    #partial switch g.op[op] {
    case .Variant:
        if g.refers[op] == NO_NODE { return }
        return g.refers[op], true, true
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
        ops := graph_operands(g, op)
        if len(ops) == 0 || !du_is_place(g, ops[0].op) { return }
        p := ops[0].op
        whole = true
        for {
            #partial switch g.op[p] {
            case .Var:
                if g.refers[p] == NO_NODE { return }
                return g.refers[p], whole, true
            case .Field, .Index, .Deref, .Swizzle, .Variant, .Slice:
                whole = false
                p = graph_operands(g, p)[0].op
                if p == NO_NODE || g.kind[p] != .Op { return }
            case:
                return
            }
        }
    }
    return
}

// What an operation writes, through a view: a write into a synthetic local
// holding a slice of a variable writes part of that variable (all but the
// write that sets the view).
@(private="file")
du_target :: proc(g: ^Program_Graph, views: map[Node_Id]Node_Id, op: Node_Id) -> (v: Node_Id, whole: bool, ok: bool) {
    v, whole, ok = du_written(g, op)
    if !ok { return }
    if target, is_view := views[v]; is_view {
        sets_view := g.op[op] == .Write && g.op[graph_operands(g, op)[1].op] == .Slice
        if !sets_view { return target, false, true }
    }
    return
}

// The variable a place is rooted at, through fields, elements and derefs.
@(private="file")
du_place_root :: proc(g: ^Program_Graph, op: Node_Id) -> (Node_Id, bool) {
    p := op
    for p != NO_NODE && g.kind[p] == .Op {
        #partial switch g.op[p] {
        case .Var:
            return g.refers[p], g.refers[p] != NO_NODE
        case .Field, .Index, .Deref, .Swizzle, .Variant, .Slice:
            p = graph_operands(g, p)[0].op
        case:
            return NO_NODE, false
        }
    }
    return NO_NODE, false
}

@(private="file")
du_is_place :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    if op == NO_NODE || g.kind[op] != .Op { return false }
    #partial switch g.op[op] {
    case .Var, .Field, .Index, .Deref, .Swizzle, .Variant, .Slice, .Global: return true
    }
    return false
}

// A loop's step (`i = i + 1`, synthetic): it redefines the loop's variable
// from itself, and gives it no value of its own.
@(private="file")
du_is_step :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    if g.op[op] != .Write || g.written[op] != .Synthetic { return false }
    val := graph_operands(g, op)[1].op
    return val != NO_NODE && g.op[val] == .Arith && g.written[val] == .Synthetic
}

// Whether a write gives its variable a value: a bare declaration's zero or
// construction does not, nor an index's synthetic start.
@(private="file")
du_write_valued :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    #partial switch g.op[op] {
    case .Write, .Fill:
        val := graph_operands(g, op)[1].op
        return val != NO_NODE && !(g.op[val] == .Const && g.written[val] == .Synthetic)
    case .Construct, .Zero:
        return g.written[op] != .Synthetic
    }
    return true   // a byte read, a match binding
}

// A definition's kind: its statement's, with a match arm's binding a
// destructure and an assignment that writes only part of a value a write.
@(private="file")
du_classify :: proc(g: ^Program_Graph, views: map[Node_Id]Node_Id, d: ^Def) {
    if d.binding == nil || d.stmt < 0 { return }
    whole := false
    for op in d.writes {
        if g.op[op] == .Variant { d.kind = .Destructure; return }
        if _, w, _ := du_target(g, views, op); w { whole = true }
    }
    kind := g.stmts[d.stmt].kind if d.stmt >= 0 else Stmt_Kind.Other
    switch kind {
    case .Decl:        d.kind = .Decl
    case .Destructure: d.kind = .Destructure
    case .Loop:        d.kind = .Loop_Var
    case .Write:       d.kind = .Complex
    case .Assign, .If, .Match, .Other:
        d.kind = .Assign if whole else .Complex
    }
}

// --- what a value reads -------------------------------------------------------

// A walk over the operations that compute a value, collecting the variable
// uses it reads. Filtered, a call contributes only the arguments its result
// is computed from; unfiltered, every argument (what was fed in).
Du_Walk :: struct {
    checked:  ^Checked_Program,
    filtered: bool,
    out:      ^[dynamic]Node_Id,
    seen:     map[^Def]bool,   // synthetic locals' definitions already seen through
}

// The variable uses a value reads.
du_value_uses :: proc(checked: ^Checked_Program, o: Operand, filtered: bool, out: ^[dynamic]Node_Id) {
    w := Du_Walk{checked = checked, filtered = filtered, out = out}
    defer delete(w.seen)
    du_walk_value(&w, o)
}

// The variable uses a definition's value reads.
du_def_uses :: proc(checked: ^Checked_Program, d: ^Def, filtered: bool, out: ^[dynamic]Node_Id) {
    w := Du_Walk{checked = checked, filtered = filtered, out = out}
    defer delete(w.seen)
    for op in d.writes { du_walk_write(&w, op) }
}

@(private="file")
du_walk_write :: proc(w: ^Du_Walk, op: Node_Id) {
    g := &w.checked.graph
    ops := graph_operands(g, op)
    #partial switch g.op[op] {
    case .Write, .Fill:  du_walk_value(w, ops[1])
    case .Byte_Read:     for o in ops[1:] { du_walk_value(w, o) }
    case .Construct:     du_walk_call(w, op)
    case .Variant:       du_walk_value(w, ops[0])
    }
}

@(private="file")
du_walk_value :: proc(w: ^Du_Walk, o: Operand) {
    if o.op == NO_NODE { return }
    g := &w.checked.graph
    ops := graph_operands(g, o.op)
    #partial switch g.op[o.op] {
    case .Var:
        du_walk_use(w, o.op)
    case .Read, .Address, .Field, .Deref, .Swizzle, .Variant:
        du_walk_value(w, ops[0])
    case .Index:
        du_walk_value(w, ops[0])
        // A loop's element read is the collection's data; its position is not.
        if g.written[o.op] != .Synthetic { du_walk_value(w, ops[1]) }
    case .Call, .Construct:
        du_walk_call(w, o.op)
    case .Arith, .Compare, .Unary, .Cast, .Slice, .Carve:
        for x in ops { du_walk_value(w, x) }
    }
}

// A call's arguments: all of them, or those its result is computed from.
@(private="file")
du_walk_call :: proc(w: ^Du_Walk, op: Node_Id) {
    g := &w.checked.graph
    args := du_call_args(g, op)
    callee := du_callee(g, op)
    if w.filtered && callee != nil && callee.ast != nil {
        cg := &w.checked.call_graph
        if n, ok := cg.index_of[callee]; ok && n < len(cg.return_deps) {
            for i in cg.return_deps[n] { if i >= 0 && i < len(args) { du_walk_value(w, args[i]) } }
            return
        }
    }
    for a in args { du_walk_value(w, a) }
}

// A var operation: a variable's use, or a synthetic local seen through to
// the values written into it.
@(private="file")
du_walk_use :: proc(w: ^Du_Walk, op: Node_Id) {
    du := &w.checked.du
    g := &w.checked.graph
    if g.refers[op] in du.bindings {
        append(w.out, op)
        return
    }
    for d in du.reaching[op] {
        if d.binding != nil || d in w.seen { continue }
        w.seen[d] = true
        for wr in d.writes { du_walk_write(w, wr) }
    }
}

// The fun or struct a call or construct operation runs; nil through a
// function value.
du_callee :: proc(g: ^Program_Graph, op: Node_Id) -> ^Type_Scope {
    for e in graph_out(g, op) {
        if e.kind == .Calls { return g.type_[e.to].(^Type_Scope) }
    }
    return nil
}

// A call's arguments, as its callee's params take them: less where a
// construction builds, less the function value a call goes through.
du_call_args :: proc(g: ^Program_Graph, op: Node_Id) -> []Operand {
    args := graph_operands(g, op)
    if g.op[op] == .Construct {
        if len(args) > 0 && du_is_place(g, args[0].op) { args = args[1:] }
    } else if g.op[op] == .Call && du_callee(g, op) == nil && len(args) > 0 {
        args = args[1:]
    }
    return args
}

// The call a definition takes its value from, by the callee's label: `x :=
// f(y)`, `x := Foo(y)`, `a, b := f()`. A literal's construction is written as
// braces, a bare `x : Foo` writes none, and a cast is no call.
du_call_label :: proc(checked: ^Checked_Program, d: ^Def) -> (name: string, ok: bool) {
    g := &checked.graph
    if len(d.writes) == 0 { return "", false }
    op := d.writes[0]
    #partial switch g.op[op] {
    case .Write:
        op = graph_operands(g, op)[1].op
        if op == NO_NODE || g.op[op] != .Call { return "", false }
    case .Construct:
        // Braces, or a bare declaration's implicit construction: no call written.
        if strings.has_suffix(g.name[op], "{}") || g.written[op] == .Synthetic { return "", false }
        if du_callee(g, op) == nil { return "", false }   // a union variant: no function runs
    case:
        return "", false
    }
    if callee := du_callee(g, op); callee != nil { return ask_label(callee), true }
    return g.name[op], true
}

// Where a fun is called: every call operation that runs it.
du_call_sites :: proc(checked: ^Checked_Program, F: ^Type_Scope) -> [dynamic]Fn_Call_Site {
    g := &checked.graph
    sites: [dynamic]Fn_Call_Site
    node, ok := g.scope_node[F]
    if !ok { return sites }
    for ei in graph_in(g, node) {
        e := g.edges[ei]
        if e.kind != .Calls { continue }
        append(&sites, Fn_Call_Site{caller = graph_caller(g, e.from), op = e.from})
    }
    return sites
}

// --- guards ---------------------------------------------------------------------

// Control dependence over the runs of a fun's code (not its defer blocks):
// run y is guarded by run x's branch when one of x's successors leads only
// through y to the exit and x does not. A branch counts as a guard when its
// statement is an if, a loop or a match; a `?`'s return is no path of its own.
@(private="file")
du_guards :: proc(checked: ^Checked_Program, f: ^Du_Fn) {
    f.guarded = true
    g := &checked.graph
    du := &checked.du
    n := f.main
    if n == 0 { return }
    exit := n
    at: map[i32]int
    defer delete(at)
    for i in 0 ..< n { at[f.runs[i]] = i }
    succ := make([][dynamic]int, n + 1)
    defer { for s in succ { delete(s) }; delete(succ) }
    for i in 0 ..< n {
        ops := graph_run(g, int(f.runs[i]))
        last := ops[len(ops) - 1]
        if g.op[last] == .Return { append(&succ[i], exit); continue }
        for e in graph_out(g, last) {
            if e.kind != .Then { continue }
            j, ok := at[du.starts[e.to]]
            if !ok { continue }
            if g.op[last] == .Branch && g.written[last] == .Implied {
                // A `?`: only the path that goes on.
                t := graph_run(g, int(f.runs[j]))
                if tl := t[len(t) - 1]; g.op[tl] == .Return && g.written[tl] == .Implied { continue }
            }
            if !slice.contains(succ[i][:], j) { append(&succ[i], j) }
        }
    }

    // Post-dominators: pd[i] = {i} ∪ ⋂ pd[successors], iterated.
    words := (n + 1 + 63) / 64
    pd := make([][]u64, n + 1)
    defer { for s in pd { delete(s) }; delete(pd) }
    for i in 0 ..= n {
        pd[i] = make([]u64, words)
        if i == exit { bits_set(pd[i], i) } else { for j in 0 ..= n { bits_set(pd[i], j) } }
    }
    next := make([]u64, words)
    defer delete(next)
    for changed := true; changed; {
        changed = false
        for i in 0 ..< n {
            for &w in next { w = 0 }
            if len(succ[i]) > 0 {
                copy(next, pd[succ[i][0]])
                for s in succ[i][1:] { for w, k in pd[s] { next[k] &= w } }
            }
            bits_set(next, i)
            if !slice.equal(next, pd[i]) { copy(pd[i], next); changed = true }
        }
    }

    // Each branch x and successor a: every run that post-dominates a but not x.
    for x in 0 ..< n {
        if len(succ[x]) < 2 { continue }
        ops := graph_run(g, int(f.runs[x]))
        last := ops[len(ops) - 1]
        if g.stmt[last] < 0 { continue }
        st := g.stmts[g.stmt[last]]
        kind: Guard_Kind
        #partial switch st.kind {
        case .If:    kind = .If
        case .Loop:  kind = .For
        case .Match: kind = .Match
        case:        continue
        }
        guard := Guard{kind = kind, span = st.span, conds = graph_operands(g, last)}
        for a in succ[x] {
            if a == exit { continue }
            for y in 0 ..< n {
                if !bits_has(pd[a], y) || bits_has(pd[x], y) { continue }
                list := f.guards[f.runs[y]]
                dup := false
                for gd in list { if gd.span == guard.span { dup = true; break } }
                if !dup { append(&list, guard); f.guards[f.runs[y]] = list }
            }
        }
    }
    for d in f.defs { if d.run >= 0 { d.guards = f.guards[d.run][:] } }
}

// The guards of a fun's explicit return.
du_return_guards :: proc(f: ^Du_Fn, ret: Node_Id) -> []Guard {
    return f.guards[f.ret_run[ret]][:]
}

// --- diagnostics ------------------------------------------------------------------

// MARA_DUMP_USEDEF=1: each fun's variables, definitions and what reaches each use.
@(private="file")
du_dump :: proc(checked: ^Checked_Program, f: ^Du_Fn) {
    buf: [8]u8
    if os.get_env_buf(buf[:], "MARA_DUMP_USEDEF") == "" { return }
    g := &checked.graph
    fmt.eprintf("--- def-use: %s (%d vars, %d defs, %d runs) ---\n", f.ft.name, len(f.vars), len(f.defs), len(f.runs))
    for d in f.defs {
        name := d.binding.name if d.binding != nil else fmt.tprintf("(%s)", g.name[d.var])
        fmt.eprintf("  def %-11v %-18s %s  writes %v\n", d.kind, name, span_loc(d.span), d.writes[:])
    }
    for r in f.runs {
        for op in graph_run(g, int(r)) {
            if reach, ok := checked.du.reaching[op]; ok {
                fmt.eprintf("  use %-18s %s <-", g.name[op], span_loc(g.origin[op]))
                for d in reach { fmt.eprintf(" %v@%s", d.kind, span_loc(d.span)) }
                fmt.eprintln()
            }
        }
    }
}
