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

Binding_Kind :: enum { Local, Param, Result }

// A variable of a fun, as the flow views name it: one its body binds
// (Annotations.vars) — the token that declares it, its name and type.
Var_Binding :: struct {
    tok:         Token_Id,
    name:        string,
    fn:          ^Type_Scope,
    kind:        Binding_Kind,
    span:        Span,    // its token's
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
    fn:      ^Du_Fn,             // the fun it is in
    order:   int,                // creation order: source order among defs sharing a span
}

// Source order, total: defs that share a span (a fun's params, `a, b := f()`)
// fall back to creation order, which follows the source within a statement.
def_less :: proc(a, b: ^Def) -> bool {
    if span_before(a.span, b.span) { return true }
    if span_before(b.span, a.span) { return false }
    return a.order < b.order
}

// A statement that decides whether another runs: an if, a loop, a match.
Guard_Kind :: enum { If, For, Match }
Guard :: struct {
    kind:  Guard_Kind,
    span:  Span,
    conds: []Operand,   // what it branches on
}

// One call of a fun: the call operation, the fun it runs in and that fun's
// code.
Fn_Call_Site :: struct {
    caller: ^Type_Scope,
    op:     Node_Id,
    g:      ^Program_Graph,
}

// One fun's analysis.
Du_Fn :: struct {
    ft:       ^Type_Scope,
    g:        ^Program_Graph,       // its code (nil: it has none — a foreign fun)
    node:     Node_Id,
    vars:     [dynamic]^Var_Binding,
    bindings: map[Node_Id]^Var_Binding,   // a variable's declaration in its code → the variable
    defs:     [dynamic]^Def,        // its variables' and synthetic locals' definitions
    reaching: map[Node_Id][]^Def,   // a use (a var operation) → the definitions that may reach it
    runs:     [dynamic]i32,         // its code's runs, then its defer blocks'
    main:     int,                  // how many of `runs` are its code's own
    returns:  [dynamic]Node_Id,     // its explicit returns
    ret_run:  map[Node_Id]i32,
    calls:    [dynamic]Node_Id,     // its calls, constructions and prints
    guards:   map[i32][dynamic]Guard,  // a run → the statements guarding it (du_def_guards)
    guarded:  bool,                 // guards computed
}

// A use of a variable: a var operation, in a fun's code.
Du_Use :: struct {
    fn: ^Du_Fn,
    op: Node_Id,
}

Def_Use :: struct {
    fns:          map[^Type_Scope]^Du_Fn,
    vars:         [dynamic]^Var_Binding,   // every analyzed variable
    defs:         [dynamic]^Def,           // every analyzed variable's definitions

    want_control: bool,                    // `control`: guards too (post-dominators)
    order:        int,
}

// --- analysis ---------------------------------------------------------------

// A fun's def-use, built the first time it is asked for.
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
    return f
}

// The statements guarding a definition (control dependence), computed for
// its fun the first time any of its are asked for. A param's: none.
du_def_guards :: proc(checked: ^Checked_Program, d: ^Def) -> []Guard {
    if d.run < 0 || d.fn == nil { return nil }
    if !d.fn.guarded { du_guards(checked, d.fn) }
    return d.fn.guards[d.run][:]
}

// Every fun's def-use: the whole-program views (a type's values, a fun's
// call sites) seed across functions. Data only: guards are built on demand
// for the functions a slice touches.
du_all :: proc(checked: ^Checked_Program) {
    for _, ft in checked.functions { du_fn(checked, ft) }
}

@(private="file")
du_build :: proc(checked: ^Checked_Program, f: ^Du_Fn) {
    du := &checked.du
    g := checked.code.funs[f.ft] or_else nil

    // Its variables: the ones its body binds (Annotations.vars).
    annotated, _ := checked.annot.vars[f.ft]
    of_var := make([]^Var_Binding, len(annotated))
    defer delete(of_var)
    params := 0
    for v, i in annotated {
        kind, index := Binding_Kind.Local, -1
        #partial switch v.kind {
        case .Param:
            kind, index = .Param, params
            params += 1
        case .Result:
            kind = .Result
        }
        of_var[i] = du_bind(checked, f, v, kind, index)
    }

    // (A fun with no code — a foreign one: each param defined on entry, and
    // nothing more.)
    node := Node_Id(0)   // (its code's root)
    if g == nil {
        for b in f.vars {
            if b.kind != .Param { continue }
            d := new(Def)
            d^ = Def{binding = b, var = NO_NODE, kind = .Param, stmt = -1, span = b.span, run = -1, fn = f, order = du.order}
            du.order += 1
            append(&f.defs, d)
            append(&du.defs, d)
        }
        return
    }
    f.g, f.node = g, node

    // The declarations its code names (its own, not a nested fun's): each a
    // variable's, found by the token that declares it, or a synthetic local
    // seen through — a loop's end, an if-expression's value, a temporary. (An
    // unnamed result is neither.)
    tracked: map[Node_Id]int
    defer delete(tracked)
    decl_of: map[^Var_Binding]Node_Id
    defer delete(decl_of)
    for id := node + 1; id <= g.last[node]; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = g.last[id]
        case .Param, .Local, .Result:
            if g.written[id] == .Explicit {
                i := annot_var(checked.annot, f.ft, g.decl_tok[id], g.type_[id])
                if i < 0 { graph_fatal(g.origin[id], "def-use: '%s' is none of %s's variables", g.name[id], f.ft.name) }
                f.bindings[id] = of_var[i]
                decl_of[of_var[i]] = id
            } else if g.kind[id] == .Result {
                continue
            }
            tracked[id] = len(tracked)
        }
    }

    // Its runs: its code's, then each defer block's, entered by a run defer.
    f.main = graph_code_runs(g, node, &f.runs)

    // Its definitions: a param's entry, then each statement's writes.
    def_of: map[[2]i32]^Def   // (variable, statement) → its definition
    defer delete(def_of)
    for b in f.vars {
        if b.kind == .Param { du_def(checked, f, &def_of, decl_of[b], -1, b.span) }
    }
    for r, ri in f.runs {
        for op in graph_run(g, int(r)) {
            #partial switch g.op[op] {
            case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Variant:
                v, _, is_def := du_written(g, op)
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
    for d in f.defs { du_classify(g, d) }

    // Reaching definitions: states are bit sets over the fun's definitions.
    words := (len(f.defs) + 63) / 64
    kill := make([][]u64, len(tracked))   // each variable's definitions
    defer { for k in kill { delete(k) }; delete(kill) }
    for &k in kill { k = make([]u64, words) }
    for d, i in f.defs { bits_set(kill[tracked[d.var]], i) }
    index_of: map[^Def]int
    defer delete(index_of)
    for d, i in f.defs { index_of[d] = i }

    Transfer :: struct {
        g: ^Program_Graph, f: ^Du_Fn, def_of: ^map[[2]i32]^Def, tracked: ^map[Node_Id]int,
        kill: [][]u64, index_of: ^map[^Def]int,
    }
    t := Transfer{g, f, &def_of, &tracked, kill, &index_of}
    apply :: proc(t: ^Transfer, ri: int, op: Node_Id, state: []u64) {
        v, whole, is_def := du_written(t.g, op)
        if !is_def { return }
        k, tracked := t.tracked[v]
        if !tracked { return }
        d := t.def_of[[2]i32{i32(v), t.g.stmt[op]}]
        if whole { bits_clear_mask(state, t.kill[k]) }
        bits_set(state, t.index_of[d])
    }
    // The entry: every param defined.
    fl := run_flow_make(g, f.runs[:], words, bits_copy, bits_union)
    defer run_flow_free(&fl)
    state := make([]u64, words)
    defer delete(state)
    for d, i in f.defs { if d.kind == .Param { bits_set(state, i) } }
    run_flow_solve(&fl, state, &t, apply)

    // The uses, against the fixpoint: every var operation naming a tracked
    // declaration, less a whole write's own destination.
    dest: map[Node_Id]bool
    defer delete(dest)
    for r in f.runs {
        for op in graph_run(g, int(r)) {
            if d := graph_whole_write_dest(g, op); d != NO_NODE { dest[d] = true }
        }
    }
    for r, ri in f.runs {
        if fl.entered[ri] { copy(state, fl.in_state[ri]) } else { slice.zero(state) }
        for op in graph_run(g, int(r)) {
            du_uses_in(g, f, op, state, tracked, kill, dest)
            apply(&t, ri, op, state)
        }
    }
}

// A var operation is a use of the variable it names, unless it is where a
// whole write lands: what reaches it is that variable's definitions in the
// state just before it (a run lists operations in the order they run).
@(private="file")
du_uses_in :: proc(g: ^Program_Graph, f: ^Du_Fn, op: Node_Id, state: []u64,
                   tracked: map[Node_Id]int, kill: [][]u64, dest: map[Node_Id]bool) {
    if g.op[op] != .Var || op in dest { return }
    k, ok := tracked[g.refers[op]]
    if !ok { return }
    reach: [dynamic]^Def
    for d, i in f.defs {
        if bits_has(kill[k], i) && bits_has(state, i) { append(&reach, d) }
    }
    if len(reach) > 0 { f.reaching[op] = reach[:] } else { delete(reach) }
}

// --- variables and definitions ---------------------------------------------

@(private="file")
du_bind :: proc(checked: ^Checked_Program, f: ^Du_Fn, v: Var_Decl, kind: Binding_Kind, param_index: int) -> ^Var_Binding {
    tok := build_tokens[v.tok]
    b := new(Var_Binding)
    b^ = Var_Binding{
        tok = v.tok, name = token_text(tok), fn = f.ft, kind = kind, span = token_span(tok),
        param_index = param_index, type_ = solidify_type(v.type_),
    }
    append(&f.vars, b)
    append(&checked.du.vars, b)
    return b
}

// The definition of variable `v` at statement `stmt`, made the first time.
@(private="file")
du_def :: proc(checked: ^Checked_Program, f: ^Du_Fn, def_of: ^map[[2]i32]^Def, v: Node_Id, stmt: i32, span: Span) -> ^Def {
    key := [2]i32{i32(v), stmt}
    if d, ok := def_of[key]; ok { return d }
    du := &checked.du
    d := new(Def)
    d^ = Def{binding = f.bindings[v], var = v, stmt = stmt, span = span, run = -1, fn = f, order = du.order}
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
            case .Field, .Index, .View, .Deref, .Swizzle, .Variant, .Slice:
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

@(private="file")
du_is_place :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    if op == NO_NODE || g.kind[op] != .Op { return false }
    #partial switch g.op[op] {
    case .Var, .Field, .Index, .View, .Deref, .Swizzle, .Variant, .Slice, .Global: return true
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
du_classify :: proc(g: ^Program_Graph, d: ^Def) {
    if d.binding == nil || d.stmt < 0 { return }
    whole := false
    for op in d.writes {
        if g.op[op] == .Variant { d.kind = .Destructure; return }
        if _, w, _ := du_written(g, op); w { whole = true }
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

// A walk over the operations that compute a value, in a fun's code,
// collecting the variable uses it reads. Filtered, a call contributes only
// the arguments its result is computed from; unfiltered, every argument
// (what was fed in).
Du_Walk :: struct {
    checked:  ^Checked_Program,
    f:        ^Du_Fn,
    filtered: bool,
    out:      ^[dynamic]Du_Use,
    seen:     map[^Def]bool,   // synthetic locals' definitions already seen through
}

// The variable uses a value in f's code reads. (A fun with no def-use — a
// struct's constructor: none.)
du_value_uses :: proc(checked: ^Checked_Program, f: ^Du_Fn, o: Operand, filtered: bool, out: ^[dynamic]Du_Use) {
    if f == nil || f.g == nil { return }
    w := Du_Walk{checked = checked, f = f, filtered = filtered, out = out}
    defer delete(w.seen)
    du_walk_value(&w, o)
}

// The variable uses a definition's value reads.
du_def_uses :: proc(checked: ^Checked_Program, d: ^Def, filtered: bool, out: ^[dynamic]Du_Use) {
    if d.fn == nil || d.fn.g == nil { return }
    w := Du_Walk{checked = checked, f = d.fn, filtered = filtered, out = out}
    defer delete(w.seen)
    for op in d.writes { du_walk_write(&w, op) }
}

@(private="file")
du_walk_write :: proc(w: ^Du_Walk, op: Node_Id) {
    g := w.f.g
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
    g := w.f.g
    ops := graph_operands(g, o.op)
    #partial switch g.op[o.op] {
    case .Var:
        du_walk_use(w, o.op)
    case .Read, .Address, .Field, .Deref, .Swizzle, .Variant:
        du_walk_value(w, ops[0])
    case .Index, .View:
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
    g := w.f.g
    args := du_call_args(g, op)
    callee := graph_called(g, op)
    if w.filtered && callee != nil && scope_is_written(callee) {
        cg := &w.checked.call_graph
        if !cg.deps_ready { cg_compute_return_deps(cg, w.checked) }
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
    f := w.f
    if f.g.refers[op] in f.bindings {
        append(w.out, Du_Use{f, op})
        return
    }
    reach, _ := f.reaching[op]
    for d in reach {
        if d.binding != nil || d in w.seen { continue }
        w.seen[d] = true
        for wr in d.writes { du_walk_write(w, wr) }
    }
}


// A call's arguments, as its callee's params take them: less where a
// construction builds, less the function value a call goes through.
du_call_args :: proc(g: ^Program_Graph, op: Node_Id) -> []Operand {
    args := graph_operands(g, op)
    if g.op[op] == .Construct {
        if len(args) > 0 && du_is_place(g, args[0].op) { args = args[1:] }
    } else if g.op[op] == .Call && graph_called(g, op) == nil && len(args) > 0 {
        args = args[1:]
    }
    return args
}

// The call a definition takes its value from, by the callee's label: `x :=
// f(y)`, `x := Foo(y)`, `a, b := f()`. A literal's construction is written as
// braces, a bare `x : Foo` writes none, and a cast is no call.
du_call_label :: proc(checked: ^Checked_Program, d: ^Def) -> (name: string, ok: bool) {
    if d.fn == nil || d.fn.g == nil { return "", false }
    g := d.fn.g
    if len(d.writes) == 0 { return "", false }
    op := d.writes[0]
    if g.op[op] == .Write {
        op = graph_operands(g, op)[1].op
        if op == NO_NODE { return "", false }
        op = du_built_in_temp(g, op)
        if g.op[op] != .Call && g.op[op] != .Construct { return "", false }
    }
    #partial switch g.op[op] {
    case .Call:
    case .Construct:
        // Braces, or a bare declaration's implicit construction: no call written.
        if strings.has_suffix(g.name[op], "{}") || g.written[op] == .Synthetic { return "", false }
        if graph_called(g, op) == nil { return "", false }   // a union variant: no function runs
    case:
        return "", false
    }
    if callee := graph_called(g, op); callee != nil { return ask_label(callee), true }
    return g.name[op], true
}

// A value read out of a temporary it was built in whole — a construction
// assigned to storage that already holds a value — is that
// construction; any other value is itself.
du_built_in_temp :: proc(g: ^Program_Graph, v: Node_Id) -> Node_Id {
    if g.op[v] != .Read { return v }
    place := graph_operands(g, v)[0].op
    if place == NO_NODE || g.op[place] != .Var { return v }
    t := g.refers[place]
    if t == NO_NODE || g.kind[t] != .Local || g.written[t] != .Synthetic { return v }
    for id := t + 1; id < v; id += 1 {
        if g.kind[id] != .Op || g.op[id] != .Construct { continue }
        dest := graph_operands(g, id)[0].op
        if dest != NO_NODE && g.op[dest] == .Var && g.refers[dest] == t { return id }
    }
    return v
}

// Where a fun is called: every call operation that runs it, in the code of
// each function the call graph says calls it (a fun's, or a struct's
// constructor's).
du_call_sites :: proc(checked: ^Checked_Program, F: ^Type_Scope) -> [dynamic]Fn_Call_Site {
    cg := &checked.call_graph
    sites: [dynamic]Fn_Call_Site
    to, ok := cg.index_of[F]
    if !ok { return sites }
    for callees, from in cg.out_edges {
        if !slice.contains(callees[:], to) { continue }
        caller := cg.nodes[from]
        g := checked.code.funs[caller] or_else nil
        if g == nil { continue }
        calls: []Node_Id
        if f := du_fn(checked, caller); f != nil {
            calls = f.calls[:]
        } else {
            calls = du_code_calls(g)
        }
        for op in calls {
            if graph_called(g, op) == F { append(&sites, Fn_Call_Site{caller = caller, op = op, g = g}) }
        }
    }
    return sites
}

// The calls and constructions a struct's constructor runs, in its code's
// runs.
@(private="file")
du_code_calls :: proc(g: ^Program_Graph) -> []Node_Id {
    runs := make([dynamic]i32, context.temp_allocator)
    graph_code_runs(g, 0, &runs)
    calls := make([dynamic]Node_Id, context.temp_allocator)
    for r in runs {
        for op in graph_run(g, int(r)) {
            #partial switch g.op[op] {
            case .Call, .Construct: append(&calls, op)
            }
        }
    }
    return calls[:]
}

// --- guards ---------------------------------------------------------------------

// Control dependence over the runs of a fun's code (not its defer blocks):
// run y is guarded by run x's branch when one of x's successors leads only
// through y to the exit and x does not. A branch counts as a guard when its
// statement is an if, a loop or a match; a `?`'s return is no path of its own.
du_guards :: proc(checked: ^Checked_Program, f: ^Du_Fn) {
    f.guarded = true
    g := f.g
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
            j, ok := at[g.run_starts[e.to]]
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
    g := f.g
    if g == nil { return }
    fmt.eprintf("--- def-use: %s (%d vars, %d defs, %d runs) ---\n", f.ft.name, len(f.vars), len(f.defs), len(f.runs))
    for d in f.defs {
        name := d.binding.name if d.binding != nil else fmt.tprintf("(%s)", g.name[d.var])
        fmt.eprintf("  def %-11v %-18s %s  writes %v\n", d.kind, name, span_loc(d.span), d.writes[:])
    }
    for r in f.runs {
        for op in graph_run(g, int(r)) {
            if reach, ok := f.reaching[op]; ok {
                fmt.eprintf("  use %-18s %s <-", g.name[op], span_loc(g.origin[op]))
                for d in reach { fmt.eprintf(" %v@%s", d.kind, span_loc(d.span)) }
                fmt.eprintln()
            }
        }
    }
}
