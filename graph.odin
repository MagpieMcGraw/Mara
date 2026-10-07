package mara

import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The program's code (design/annotated_tree.md, stage 4): what the analyses
// and the emitter read. Lowering builds it from the annotated tree once the
// check is clean (lower.odin, through Graph_Builder and the graph_build_*
// procs); put together (build_program_graph), it is each fun's, struct's
// constructor's and constant's code, a graph of its own (Program_Code).
//
// A code's nodes are its scopes — its own and its blocks — the variables they
// declare, and operations (the set in design/program_graph.md § Operations).
// Each fact is a column indexed by Node_Id, the code's own from 0: its root,
// then everything in it, depth-first in written order, so a scope's subtree
// is one run of ids: [id, last[id]]. (Built, the codes share one graph, in
// pieces as each is lowered; graph_canonicalize puts them in order, laying
// out each code in a graph of its own.)
//
// Execution order is kept apart from the tree: every function's operations
// are cut into runs, each ending in a jump, branch, switch or return, and a
// Then edge joins a run's last operation to the first of each run that can
// come next. An operation's operands are other operations' outputs, produced
// earlier in its run (or in a run only it follows); a value that crosses a
// join goes through a synthetic local.
//
// A generic's instances are nodes (they are what runs); the template is only
// syntax. Every instance points at the template as its origin.
// ---------------------------------------------------------------------------

Node_Id :: distinct i32
NO_NODE :: Node_Id(-1)

Node_Kind :: enum u8 {
    // Scopes
    Module, Struct, Fun, Block,
    // Names declared in a scope
    Field, Param, Result, Local, Const,
    // An operation; which one is in the `op` column
    Op,
}

Op_Kind :: enum u8 {
    // Places
    Var, Global, Field, Index, View, Deref, Variant, Swizzle, Slice,
    // Memory
    Read, Write, Address, Zero, Construct, Fill, Carve, Byte_Read, Arena_Alloc,
    // Values
    Const, Arith, Compare, Unary, Cast,
    // Calls
    Call, Print, Assert, Crash,
    // Ending a run
    Jump, Branch, Switch, Return,
    // Implicit work at a scope's exits
    Run_Defer, Arena_Mark, Arena_Reset,
}

// How a node or edge is written (design/program_graph.md, Identity and editing).
Written :: enum u8 { Explicit, Implied, Synthetic }

// A `then`: a run's last operation, or a scope for its entry → a run's first
// operation. (What a call runs and what a run-defer runs are columns:
// Program_Graph.callee, .defer_of.)
Edge :: struct {
    from:    Node_Id,
    to:      Node_Id,
    written: Written,
}

// An operation's input: another operation's output. A call has one output per
// return value; everything else has at most one.
Operand :: struct {
    op:  Node_Id,
    out: i32,
}

NO_VALUE :: Operand{op = NO_NODE}

// A node no drop replaced (Graph_Builder.repl).
@(private="file")
KEPT :: Operand{op = Node_Id(-2)}

// A statement code is lowered from: where it is written and what it does to
// the variables it writes, which is how an analysis reports a write.
Graph_Stmt :: struct {
    span: Span,
    kind: Stmt_Kind,
}

Stmt_Kind :: enum u8 {
    Other,
    Decl,         // declares a variable: `x := v`, `x : T = v`, `x : T`
    Assign,       // `x = v`, `x += v`
    Write,        // writes part of one: `x.f = v`, `a[i] = v`, `p^ = v`
    Destructure,  // `a, b := f()`
    Loop, If, Match,
}

Program_Graph :: struct {
    kind:    [dynamic]Node_Kind,
    op:      [dynamic]Op_Kind,  // for operations
    written: [dynamic]Written,
    parent:  [dynamic]Node_Id,
    last:    [dynamic]Node_Id,  // the subtree's last id
    name:    [dynamic]string,
    type_:   [dynamic]Type,     // has type; nil when the node has none
    origin:  [dynamic]Span,     // where it is written, or what caused a synthetic node
    refers:  [dynamic]Node_Id,  // a var or variant operation → the declaration it names
    callee:  [dynamic]^Type_Scope,      // a call or construct operation → the fun or struct it runs (nil through a fun's value)
    defer_of: map[Node_Id]Node_Id,      // a run-defer operation → the defer block it runs
    stmt:    [dynamic]i32,      // an operation → the statement it comes from (in `stmts`), or -1
    decl_tok: [dynamic]Token_Id,      // a variable's declaration — a param, a named result, a local — → the token that declares it (0: none)

    // A node's operands are operands[operand_first[id] : operand_first[id+1]].
    operands:      [dynamic]Operand,
    operand_first: [dynamic]i32,

    // Run r is run_ops[run_first[r] : run_first[r+1]], in the order it runs;
    // run_starts is each run by its first operation (where a Then edge lands).
    run_ops:    [dynamic]Node_Id,
    run_first:  [dynamic]i32,
    run_starts: map[Node_Id]i32,

    // The Then edges, sorted by `from`: a node's are
    // edges[out_first[id] : out_first[id+1]].
    edges:     [dynamic]Edge,
    out_first: [dynamic]i32,

    // Each checked fun and struct's node: the bridge while analyses still key
    // on scopes.
    scope_node: map[^Type_Scope]Node_Id,

    // The statements code is lowered from, for analyses that report a statement
    // (a definition's line, a guarding branch): each one's origin and kind.
    stmts: [dynamic]Graph_Stmt,

    // Statements right after a return, break or continue: the first of each
    // stretch.
    unreachable: [dynamic]Span,
    settled:     [dynamic]Node_Id,   // literals whose type is their use's (a `:=` width adopted, an operand's): for the range check

    // A constant operation's value, where code needs one: a literal, an enum
    // variant, a named scalar constant, a fixed array's length. `void` and a
    // constant not evaluated here have none.
    consts: map[Node_Id]Const_Value,

    // An assert on a comparison: each side's source text, which its failure
    // reports beside the side's value — "" for a side whose text states its
    // value (a literal, a variant).
    assert_sides: map[Node_Id][2]string,

    // A constant, by its value's node (Graph_Named.value; 0: none): an
    // operation that names one — its value at the use, a table's global —
    // and each one's code.
    constant:   [dynamic]Syntax_Id,
    const_code: map[Syntax_Id]Node_Id,

    // A fun that consumes a param into its result → which param, by its
    // place among the fun's (graph_find_consumes).
    consumes: map[Node_Id]int,
}

// A constant's value: an integer (bools and chars too), or a float.
Const_Value :: struct {
    int:      i128,
    float:    f64,
    is_float: bool,
    text:     string,   // a string constant's, when is_text
    is_text:  bool,
}

graph_out :: proc(g: ^Program_Graph, id: Node_Id) -> []Edge {
    return g.edges[g.out_first[id]:g.out_first[id + 1]]
}

graph_operands :: proc(g: ^Program_Graph, id: Node_Id) -> []Operand {
    return g.operands[g.operand_first[id]:g.operand_first[id + 1]]
}

// Where a whole write lands — `e = f()` writes e, reading nothing — its
// destination's var operation; NO_NODE for any other operation.
graph_whole_write_dest :: proc(g: ^Program_Graph, op: Node_Id) -> Node_Id {
    #partial switch g.op[op] {
    case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Arena_Alloc:
        ops := graph_operands(g, op)
        if len(ops) > 0 && ops[0].op != NO_NODE && g.kind[ops[0].op] == .Op && g.op[ops[0].op] == .Var { return ops[0].op }
    }
    return NO_NODE
}

// The fun or struct a call or construction runs; nil through a function value.
graph_called :: proc(g: ^Program_Graph, op: Node_Id) -> ^Type_Scope {
    return g.callee[op]
}

// The signature a call runs by: its callee's, or — through a function value,
// its first operand — that value's type.
graph_signature :: proc(g: ^Program_Graph, op: Node_Id) -> ^Type_Scope {
    if callee := graph_called(g, op); callee != nil { return callee }
    ops := graph_operands(g, op)
    if g.op[op] != .Call || len(ops) == 0 || ops[0].op == NO_NODE { return nil }
    ft, is_fn := distinct_base(g.type_[ops[0].op]).(^Type_Scope)
    return ft if is_fn && ft.kind == .Fun else nil
}

graph_run :: proc(g: ^Program_Graph, r: int) -> []Node_Id {
    return g.run_ops[g.run_first[r]:g.run_first[r + 1]]
}

// Each run by its first operation (g.run_starts), once the runs are final.
@(private="file")
graph_index_runs :: proc(g: ^Program_Graph) {
    g.run_starts = make(map[Node_Id]i32, len(g.run_first))
    for r in 0 ..< len(g.run_first) - 1 {
        if ops := graph_run(g, r); len(ops) > 0 { g.run_starts[ops[0]] = i32(r) }
    }
}

// Whether a fun or struct's code can reach its end without a return: the
// synthetic return that ends its body, in a run its entry reaches.
graph_falls_off :: proc(g: ^Program_Graph, scope: Node_Id) -> bool {
    starts := g.run_starts
    seen: map[i32]bool
    defer delete(seen)
    todo: [dynamic]i32
    defer delete(todo)
    for e in graph_out(g, scope) { append(&todo, starts[e.to]) }
    for len(todo) > 0 {
        r := pop(&todo)
        if r in seen { continue }
        seen[r] = true
        ops := graph_run(g, int(r))
        last := ops[len(ops) - 1]
        if g.op[last] == .Return && g.written[last] == .Synthetic { return true }
        for e in graph_out(g, last) { append(&todo, starts[e.to]) }
    }
    return false
}

// A fun's (or struct's) code as runs: those its entry reaches, then those of
// each defer block a run defer in them runs. Returns how many are its own
// code's; each list keeps a run's successors after it.
graph_code_runs :: proc(g: ^Program_Graph, scope: Node_Id, out: ^[dynamic]i32) -> (own: int) {
    starts := g.run_starts
    seen: map[i32]bool
    defer delete(seen)
    reach :: proc(g: ^Program_Graph, starts: map[Node_Id]i32, scope: Node_Id, out: ^[dynamic]i32, seen: ^map[i32]bool) {
        todo: [dynamic]i32
        defer delete(todo)
        for e in graph_out(g, scope) { append(&todo, starts[e.to]) }
        for len(todo) > 0 {
            r := pop(&todo)
            if r in seen^ { continue }
            seen^[r] = true
            append(out, r)
            ops := graph_run(g, int(r))
            // Depth-first in edge order keeps a run's successors after it.
            next := graph_out(g, ops[len(ops) - 1])
            for i := len(next) - 1; i >= 0; i -= 1 {
                append(&todo, starts[next[i].to])
            }
        }
    }
    reach(g, starts, scope, out, &seen)
    own = len(out)
    for i := 0; i < len(out); i += 1 {
        for op in graph_run(g, int(out[i])) {
            if g.op[op] != .Run_Defer { continue }
            reach(g, starts, g.defer_of[op], out, &seen)
        }
    }
    return
}

graph_is_terminator :: proc(k: Op_Kind) -> bool {
    #partial switch k {
    case .Jump, .Branch, .Switch, .Return: return true
    }
    return false
}

// --- builder ----------------------------------------------------------------

Graph_Builder :: struct {
    g:       ^Program_Graph,
    checked: ^Checked_Program,
    stmt:    i32,     // the statement being lowered (in g.stmts), or -1
    // Checked types by the span of the statement declaring them. A generic's
    // instances share their template's span, so one span can hold several.
    by_span: map[Span][dynamic]Type,
    arena:      bool,    // the program has a scope arena: big values live on it
    runs:       [dynamic]^Run,   // every run made, freed at the end
    nodes:      int,             // how many nodes exist; the columns run ahead
    code:       Code,
    // Refers-to: each declaration made in the code being built — a fun's, a
    // struct's, a constant's; its defers' are its own — by the token that
    // declares it (graph_declare, graph_local).
    locals:     map[Token_Id]Node_Id,
    self:       Node_Id,         // what `Self` names in a struct's code
    program:    Node_Id,         // the synthetic scope of the compiler's globals (this_program)
    // Each module's statements, where each goes (graph_modules): built as the
    // checker settles them (graph_module_stmt), or — a scope, a type — when
    // the graph is put together.
    module_stmts: map[Syntax_Id]int,
    module_list:  [dynamic]Graph_Module_Stmt,
    def_segs:     map[Syntax_Id]int,   // a body's constants, built as settled: each one's segment
    const_segs:   map[Syntax_Id]int,               // each constant's code, by its statement (graph_const_begin)
    // Every name the checker's table has a constant under, by its value's id
    // (a module's constant is there under its flat name and its bare one):
    // what its table is named (graph_table_names).
    constant_names: map[string]Syntax_Id,
    // Segments: a scope's contents built on their own, at any time, then put
    // where the scope is (graph_canonicalize).
    segs:    [dynamic]Graph_Segment,
    seg:     int,
    // The bodies the checker built as it checked them, by their scope, each a
    // segment: the builder puts them in place. The body being built; the
    // first the checker couldn't build (an internal error, reported once the
    // check is found clean).
    body_segs: map[^Type_Scope]int,
    scope_of: map[Syntax_Id]^Type_Scope,   // each scope statement's, as the checker built it
    bodies:   [dynamic]^Graph_Body,
    body:     ^Graph_Body,
    failure:  struct { name, reason: string, span: Span },
    // Operations made before whether they are needed was known, found not
    // to be: each is left out, and what it stood for used in its place —
    // by node, once the graph is put together (repl; KEPT where it is not),
    // listed until then.
    repl:     []Operand,
    drops:    [dynamic][2]Operand,
}

// What one build made: the nodes, closed runs, statements and unreachable
// spans it added — in pieces, when another build ran in the middle of it —
// and the segments that go inside it, where each goes.
@(private="file")
Graph_Segment :: struct {
    pieces:  [dynamic]Graph_Piece,
    anchors: [dynamic]Graph_Anchor,
    root:    Node_Id,   // a scope's: its node, placed by its anchor
    placed:  bool,      // an anchor puts it somewhere
    // A body's definitions: each one's code put after it when the body is
    // placed (graph_body_place).
    defs:    [dynamic]Graph_Decl,
}

// A stretch of one segment's items: [from, to) of each.
@(private="file")
Graph_Piece :: struct {
    nodes, runs, stmts, unreach: [2]int,
}

// Where segment `seg` goes in the one it is anchored in: before the items
// that segment made after these counts.
@(private="file")
Graph_Anchor :: struct {
    seg:                          int,
    nodes, runs, stmts, unreach:  int,
}

// The statement column of what a scope's segment makes outside its own
// statements (its node, params, results, implied return), until its anchor
// says which statement that is.
@(private="file")
STMT_ANCHOR :: i32(-2)

// A declaration made in the code being built, by the token that declares it:
// what a name its token declares refers to there. (A union match's arms that
// rebind their subject declare one token each in turn: the arm being built's.)
@(private="file")
graph_declare :: proc(b: ^Graph_Builder, d: Node_Id, tok: Token_Id) {
    if tok == 0 { return }
    b.g.decl_tok[d] = tok
    b.locals[tok] = d
}

// The declaration in the code being built of the variable a name refers to,
// by the token its annotation says declares it; none when no code here
// declares it.
graph_local :: proc(b: ^Graph_Builder, tok: Token_Id) -> Node_Id {
    return b.locals[tok] or_else NO_NODE
}

// The compiler's own global a name is — `this_program`, `context` — when it
// is one (graph_modules: the program's scope, then its two).
graph_global :: proc(b: ^Graph_Builder, name: string) -> Node_Id {
    switch name {
    case "this_program": return b.program + 1
    case "context":      return b.program + 2
    }
    return NO_NODE
}

// The code being built's declarations, saved and emptied for another's.
@(private="file")
graph_locals_enter :: proc(b: ^Graph_Builder) -> (saved: map[Token_Id]Node_Id) {
    saved, b.locals = b.locals, {}
    return
}

@(private="file")
graph_locals_leave :: proc(b: ^Graph_Builder, saved: map[Token_Id]Node_Id) {
    delete(b.locals)
    b.locals = saved
}


// The code being built: a fun's body, a struct's field initializers, a defer's
// block. Saved and restored around a nested definition.
@(private="file")
Code :: struct {
    active: bool,
    block:  Node_Id,              // where new operations sit in the tree
    run:    ^Run,                 // the run being filled; nil after a jump or return
    scopes: [dynamic]Code_Scope,  // open scopes, outermost first
    loops:  [dynamic]Loop,
    tuples: map[Syntax_Id]Node_Id,   // a default's shared source call → its operation
    constructed: Node_Id,         // the last construction's operation (its outputs past Self: a fallible one's err)
}

@(private="file")
Run :: struct {
    ops:     [dynamic]Node_Id,
    waiting: [dynamic]i32,       // the `then` edges (by index) whose target is this run's first operation, once it has one
}

@(private="file")
Code_Scope :: struct {
    block:  Node_Id,
    defers: [dynamic]Node_Id,   // defer blocks registered so far, in order
    tentative: int,             // its arena mark and resets, decided later (b.body.marks); -1: none
}

@(private="file")
Loop :: struct {
    cont, done: ^Run,
    scope:      int,   // index of the loop body's scope in Code.scopes
}

// What a plain declaration becomes where it is written, and the struct whose
// fields it declares (their types come from the checked struct).
@(private="file")
Decl_Site :: struct {
    kind:  Node_Kind,    // .Field, .Local or .Const
    owner: ^Type_Scope,  // the struct, for .Field
}

// The builder, made before checking: the checker builds each body as it
// checks it (graph_body_begin), and build_program_graph puts them in place.
graph_builder_new :: proc(checked: ^Checked_Program, modules: map[string][]Graph_Decl) -> ^Graph_Builder {
    b := new(Graph_Builder)
    b.g = new(Program_Graph)
    b.checked = checked
    b.stmt = -1
    b.arena = checked.table.has_scope_allocator || checked.table.context_expected_at_runtime
    append(&b.segs, Graph_Segment{root = NO_NODE})   // the program's own: its modules' declarations
    graph_piece_begin(b, 0)
    graph_modules(b, modules)
    return b
}

// A module's statement, and where it goes: before what its module made after
// it (an anchor in the program's segment).
Graph_Module_Stmt :: struct {
    d:        Graph_Decl,
    module:   Node_Id,
    anchor:   int,
    built:    bool,
    declared: Graph_Declared,
}

// What a statement declares, as the checker settled it: each name's type,
// in the order it names them, and what it does (tc_stmt_kind's: a
// broadcast's statement is its copies').
Graph_Declared :: struct {
    types: []Type,
    kind:  Stmt_Kind,
    set:   bool,
}

// The program's modules, before anything is checked: the compiler's globals
// (typed once checked), then a place for each module's statements, the
// modules in name order, each's in written order: where the code each
// defines goes.
@(private="file")
graph_modules :: proc(b: ^Graph_Builder, programs: map[string][]Graph_Decl) {
    b.program = graph_node(b, .Module, .Synthetic, NO_NODE, "program", nil, {})
    for name in ([]string{"this_program", "context"}) {
        graph_node(b, .Field, .Synthetic, b.program, name, nil, {})
    }
    graph_close(b, b.program)
    modules := make([dynamic]string, 0, len(programs), context.temp_allocator)
    for name in programs { append(&modules, name) }
    slice.sort(modules[:])
    for name in modules {
        for d in programs[name] {
            b.module_stmts[d.id] = len(b.module_list)
            append(&b.module_list, Graph_Module_Stmt{d = d, module = NO_NODE, anchor = graph_anchor_here(b)})
        }
    }
}

// A module's statement the checker has settled — a constant, a variable, a
// destructure: its declarations, in a segment of their own, put where the
// statement is. (Once: a statement is settled by the first pass over it.)
graph_module_stmt :: proc(b: ^Graph_Builder, id: Syntax_Id, declared: Graph_Declared) {
    i, is_module := b.module_stmts[id]
    if !is_module || b.module_list[i].built { return }
    b.module_list[i].declared = declared
    if b.module_list[i].d.settles { graph_module_build(b, &b.module_list[i]) }
}

// (What the builder is in the middle of — a body the checker is building —
// is no module's: its code and its names are left as they are.)
@(private="file")
graph_module_build :: proc(b: ^Graph_Builder, ms: ^Graph_Module_Stmt) {
    ms.built = true
    si, saved := graph_segment_enter(b)
    code, locals := b.code, graph_locals_enter(b)
    b.code = {}
    graph_decl_stmt(b, ms.d, ms.module, {kind = .Field}, ms.declared)
    b.code = code
    graph_locals_leave(b, locals)
    graph_segment_leave(b, saved)
    b.segs[0].anchors[ms.anchor].seg = si
}

graph_builder_free :: proc(b: ^Graph_Builder) {
    for _, list in b.by_span { delete(list) }
    delete(b.by_span)
    for r in b.runs {
        delete(r.ops)
        delete(r.waiting)
        free(r)
    }
    delete(b.runs)
    delete(b.locals)
    delete(b.constant_names)
    delete(b.const_segs)
    for s in b.segs {
        delete(s.pieces)
        delete(s.anchors)
        delete(s.defs)
    }
    delete(b.segs)
    delete(b.body_segs)
    delete(b.scope_of)
    for f in b.bodies { graph_body_free(f) }
    delete(b.bodies)
    delete(b.repl)
    delete(b.drops)
    free(b.g)
    free(b)
}

build_program_graph :: proc(b: ^Graph_Builder) -> Program_Code {
    defer graph_builder_free(b)
    if f := b.failure; f.reason != "" { graph_fatal(f.span, "the checker built no graph of '%s': %s", f.name, f.reason) }
    g, checked := b.g, b.checked
    graph_index(b)

    // The compiler's own globals, which code names but never declares.
    for name, i in ([]string{"this_program", "context"}) {
        if root := checked.table.root_env; root != nil { g.type_[int(b.program) + 1 + i], _ = scope_defines(root, name) }
    }
    // The modules' statements left: their scopes and types — each placed
    // from what the checker made of it (its bodies built, its instances
    // known). One the checker settles and didn't is an error.
    for &ms in b.module_list {
        if ms.built { continue }
        if ms.d.settles { graph_fatal(ms.d.span, "the checker settled no declaration here") }
        graph_module_build(b, &ms)
    }
    graph_piece_end(b, 0)
    for _, si in b.const_segs {
        root := b.segs[si].root
        if !b.segs[si].placed { graph_fatal(b.g.origin[root], "the constant '%s' was built but never placed", b.g.name[root]) }
    }
    // What was dropped, by node: those listed while checking, then settling's.
    if len(b.bodies) > 0 || len(b.drops) > 0 {
        b.repl = make([]Operand, b.nodes)
        slice.fill(b.repl, KEPT)
        for d in b.drops { b.repl[d[0].op] = d[1] }
    }
    for f in b.bodies { graph_body_settle(b, f) }
    // (Each call named for its callee, an instance's now known.)
    for callee, op in g.callee[:b.nodes] {
        if callee == nil { continue }
        braces := strings.has_suffix(g.name[op], "{}")   // a literal's construction, as written
        g.name[op] = graph_call_name(callee)
        if braces { g.name[op] = strings.concatenate({g.name[op], "{}"}) }
    }
    graph_resize(g, b.nodes)
    append(&g.operand_first, i32(len(g.operands)))
    append(&g.run_first, i32(len(g.run_ops)))
    pc := graph_canonicalize(b)
    for c in pc.codes {
        graph_settle_literals(c)
        graph_find_consumes(c)
        if k, consumes := c.consumes[0]; consumes { pc.consumes[c.type_[0].(^Type_Scope)] = k }
        graph_index_edges(c)
        graph_index_runs(c)
    }
    graph_fold_uses(&pc, checked)
    graph_table_names(b, &pc)
    when ODIN_DEBUG {
        graph_check_coverage(b, &pc)
        for c in pc.codes {
            graph_check_runs(c)
            graph_check_refers(c)
        }
    }
    graph_dump(&pc)
    return pc
}

// --- the program's code ---------------------------------------------------------

// The program's code, once lowered (design/annotated_tree.md, stage 4): each
// fun's, each struct's constructor's and each constant's, a graph of its own —
// its ids its own, from 0: its node, then everything in it — and what the
// program has once: the constants' tables, the funs that consume a param, the
// statements nothing reaches.
Program_Code :: struct {
    codes:       [dynamic]^Program_Graph,          // each, in written order
    funs:        map[^Type_Scope]^Program_Graph,   // a fun's, a struct's constructor's
    consts:      map[Syntax_Id]^Program_Graph,     // a constant's, by its value's node
    tables:      map[Syntax_Id]^Fold,              // each table's value, by its constant (graph_fold_uses)
    table_names: map[Syntax_Id]string,             // ... its symbol's name
    fold_errors: [dynamic]Fold_Error,              // the uses of constants with no value
    consumes:    map[^Type_Scope]int,              // a fun that consumes a param into its result → which
    unreachable: [dynamic]Span,                    // statements right after a return, break or continue
    arena:       ^virtual.Arena,                   // where the codes are (they last as long as the program)
}

// Leave node id out of the graph, `with` standing for it where it is used.
graph_drop :: proc(b: ^Graph_Builder, id: Node_Id, with: Operand) {
    if b.repl != nil {
        b.repl[id] = with
    } else {
        append(&b.drops, [2]Operand{{id, 0}, with})
    }
}

@(private="file")
graph_dropped :: proc(b: ^Graph_Builder, id: Node_Id) -> bool {
    return b.repl != nil && b.repl[id] != KEPT
}

// The builder's counts of each item, as they stand now.
@(private="file")
graph_counts :: proc(b: ^Graph_Builder) -> [4]int {
    return {b.nodes, len(b.g.run_first), len(b.g.stmts), len(b.g.unreachable)}
}

// Segment si's next piece starts, or its last ends, where the counts stand.
@(private="file")
graph_piece_begin :: proc(b: ^Graph_Builder, si: int) {
    c := graph_counts(b)
    append(&b.segs[si].pieces, Graph_Piece{nodes = {c[0], -1}, runs = {c[1], -1}, stmts = {c[2], -1}, unreach = {c[3], -1}})
}

@(private="file")
graph_piece_end :: proc(b: ^Graph_Builder, si: int) {
    p := &b.segs[si].pieces[len(b.segs[si].pieces) - 1]
    c := graph_counts(b)
    p.nodes[1], p.runs[1], p.stmts[1], p.unreach[1] = c[0], c[1], c[2], c[3]
}

// A new segment, built from here until graph_segment_leave: what the current
// one makes after it is another piece of that one.
@(private="file")
graph_segment_enter :: proc(b: ^Graph_Builder) -> (si, saved: int) {
    si, saved = len(b.segs), b.seg
    append(&b.segs, Graph_Segment{root = NO_NODE})
    graph_piece_end(b, saved)
    b.seg = si
    graph_piece_begin(b, si)
    return
}

@(private="file")
graph_segment_leave :: proc(b: ^Graph_Builder, saved: int) {
    graph_piece_end(b, b.seg)
    b.seg = saved
    graph_piece_begin(b, saved)
}

// Where a segment goes: here, in the one being built.
@(private="file")
graph_anchor_here :: proc(b: ^Graph_Builder, seg := -1) -> int {
    c := graph_counts(b)
    s := &b.segs[b.seg]
    append(&s.anchors, Graph_Anchor{seg = seg, nodes = c[0], runs = c[1], stmts = c[2], unreach = c[3]})
    if seg >= 0 { b.segs[seg].placed = true }
    return len(s.anchors) - 1
}


// Put a scope's segment where its anchor is: its node's parent and name
// (an instance's is its mangled name, known once checking is done), and the
// statement it and the rest made outside the scope's own statements are in.
@(private="file")
graph_segment_place :: proc(b: ^Graph_Builder, si: int, parent: Node_Id, stmt: i32, name: string) {
    s := b.segs[si]
    b.g.parent[s.root] = parent
    b.g.name[s.root] = name
    for p in s.pieces {
        for i in p.nodes[0] ..< p.nodes[1] {
            if b.g.stmt[i] == STMT_ANCHOR { b.g.stmt[i] = stmt }
        }
    }
}

// Put every segment where its scope is: the nodes in the order one build in
// written order makes them — each scope's contents right after its node — and
// the runs, statements and unreachable spans where they would have come; every
// id that names one of them renumbered. (Bodies are built as the checker
// checks them, out of written order.)
@(private="file")
graph_canonicalize :: proc(b: ^Graph_Builder) -> Program_Code {
    g := b.g
    n := b.nodes
    // Each segment's items in order, a nested segment's where its anchor says.
    Item :: enum { Node, Run, Stmt, Unreach }
    walk :: proc(b: ^Graph_Builder, si: int, item: Item, out: ^[dynamic]int) {
        s := b.segs[si]
        at :: proc(a: Graph_Anchor, item: Item) -> int {
            switch item {
            case .Node:    return a.nodes
            case .Run:     return a.runs
            case .Stmt:    return a.stmts
            case .Unreach: return a.unreach
            }
            return 0
        }
        k := 0
        for p in s.pieces {
            r: [2]int
            switch item {
            case .Node:    r = p.nodes
            case .Run:     r = p.runs
            case .Stmt:    r = p.stmts
            case .Unreach: r = p.unreach
            }
            for i in r[0] ..< r[1] {
                // What was anchored before this item was made goes before it.
                for k < len(s.anchors) && at(s.anchors[k], item) <= i {
                    if s.anchors[k].seg >= 0 { walk(b, s.anchors[k].seg, item, out) }
                    k += 1
                }
                if item == .Node && graph_dropped(b, Node_Id(i)) { continue }
                append(out, i)
            }
        }
        for ; k < len(s.anchors); k += 1 {
            if s.anchors[k].seg >= 0 { walk(b, s.anchors[k].seg, item, out) }
        }
    }
    order: [Item][dynamic]int
    defer for o in order { delete(o) }
    for item in Item { walk(b, 0, item, &order[item]) }
    nodes, runs, stmts, unreach := order[.Node][:], order[.Run][:], order[.Stmt][:], order[.Unreach][:]
    // What no anchor reaches is left out. What a dropped operation stood for
    // is used in its place.
    new_id := make([]Node_Id, n)
    defer delete(new_id)
    slice.fill(new_id, NO_NODE)
    for old, i in nodes { new_id[old] = Node_Id(i) }
    re :: proc(new_id: []Node_Id, id: Node_Id) -> Node_Id {
        if id == NO_NODE { return id }
        assert(new_id[id] != NO_NODE, "a node refers to one left out")
        return new_id[id]
    }
    ro :: proc(b: ^Graph_Builder, new_id: []Node_Id, o: Operand) -> Operand {
        o := o
        for (o.op != NO_NODE && graph_dropped(b, o.op)) { o = b.repl[o.op] }
        return Operand{re(new_id, o.op), o.out}
    }
    kept :: proc(new_id: []Node_Id, id: Node_Id) -> bool { return id != NO_NODE && new_id[id] != NO_NODE }
    new_stmt := make([]i32, len(g.stmts))
    defer delete(new_stmt)
    slice.fill(new_stmt, -1)
    for old, i in stmts { new_stmt[old] = i32(i) }

    pc: Program_Code
    pc.arena = new(virtual.Arena)
    if err := virtual.arena_init_growing(pc.arena); err != nil { graph_fatal({}, "no memory for the program's code") }
    context.allocator = virtual.arena_allocator(pc.arena)
    for old in unreach { append(&pc.unreachable, g.unreachable[old]) }

    // Each code: a node with no parent, and the nodes after it up to the
    // next — in written order, a scope's subtree is one stretch. (The
    // compiler's globals' scope is none: what names one of its globals has
    // a node of its own for it.)
    code_of := make([]i32, len(nodes), context.temp_allocator)   // each node's code (-1: none), by its place in written order
    lo_of := make([dynamic]int, context.temp_allocator)          // each code's first node, by its place
    const_of := make(map[Node_Id]Syntax_Id, len(g.const_code), context.temp_allocator)
    for v, d in g.const_code { const_of[d] = v }
    ts_of := make(map[Node_Id]^Type_Scope, len(g.scope_node), context.temp_allocator)
    for ts, d in g.scope_node { ts_of[d] = ts }
    for old, i in nodes {
        if g.parent[old] == NO_NODE {
            #partial switch g.kind[old] {
            case .Module:   // (the compiler's own globals)
            case .Fun, .Struct, .Const:
                append(&pc.codes, new(Program_Graph))
                append(&lo_of, i)
            case:
                graph_fatal(g.origin[old], "a %v '%s' is no code", g.kind[old], g.name[old])
            }
            code_of[i] = -1 if g.kind[old] == .Module else i32(len(pc.codes) - 1)
            continue
        }
        if i == 0 { graph_fatal(g.origin[old], "'%s' is in no code", g.name[old]) }
        code_of[i] = code_of[i - 1]
    }
    // (Where a node is: its code and its id there.)
    Place :: struct { code: i32, id: Node_Id }
    place :: proc(code_of: []i32, lo_of: []int, new_id: []Node_Id, old: Node_Id) -> Place {
        i := new_id[old]
        c := code_of[i]
        return {c, i - Node_Id(lo_of[c]) if c >= 0 else NO_NODE}
    }
    used := make([dynamic]i32, context.temp_allocator)
    stmt_at := make([]i32, len(stmts), context.temp_allocator)   // a statement's id in the code being laid out (-1: none yet)
    slice.fill(stmt_at, -1)
    for c, ci in pc.codes {
        lo := lo_of[ci]
        hi := (lo_of[ci + 1] if ci + 1 < len(lo_of) else len(nodes)) - 1
        // (Those before the next code's: the compiler's globals' scope, when it
        // comes after, is no node of this one.)
        for hi > lo && code_of[hi] != i32(ci) { hi -= 1 }
        count := hi - lo + 1
        // What it names outside it: a node each, past its own.
        outside: map[Node_Id]Node_Id   // (rare: made once one is)
        outer := make([dynamic]Node_Id, context.temp_allocator)
        graph_resize(c, count)
        clear(&used)   // (its statements, by their place in written order: each its id here in stmt_at)
        for i in lo ..= hi {
            old := nodes[i]
            assert(g.stmt[old] != STMT_ANCHOR, "a segment's node was never placed")
            if s := g.stmt[old]; s >= 0 && stmt_at[new_stmt[s]] < 0 {
                stmt_at[new_stmt[s]] = 0
                append(&used, new_stmt[s])
            }
        }
        slice.sort(used[:])
        reserve(&c.stmts, len(used))
        for s in used {
            stmt_at[s] = i32(len(c.stmts))
            append(&c.stmts, g.stmts[stmts[s]])
        }
        defer for s in used { stmt_at[s] = -1 }
        for i in lo ..= hi {
            old, at := nodes[i], i - lo
            c.kind[at], c.op[at], c.written[at] = g.kind[old], g.op[old], g.written[old]
            c.name[at], c.type_[at], c.origin[at] = g.name[old], g.type_[old], g.origin[old]
            c.callee[at], c.decl_tok[at], c.constant[at] = g.callee[old], g.decl_tok[old], g.constant[old]
            c.parent[at] = NO_NODE if g.parent[old] == NO_NODE else re(new_id, g.parent[old]) - Node_Id(lo)
            c.last[at] = Node_Id(at)
            r := g.refers[old]
            if r == NO_NODE {
                c.refers[at] = NO_NODE
            } else if nr := re(new_id, r); int(nr) >= lo && int(nr) <= hi {
                c.refers[at] = nr - Node_Id(lo)
            } else {   // (one outside it)
                if r not_in outside {
                    outside[r] = Node_Id(count + len(outer))
                    append(&outer, r)
                }
                c.refers[at] = outside[r]
            }
            s := g.stmt[old]
            c.stmt[at] = -1 if s < 0 else stmt_at[new_stmt[s]]
            assert(s < 0 || c.stmt[at] >= 0, "a node is in a statement left out")
            c.operand_first[at] = i32(len(c.operands))
            for o in g.operands[g.operand_first[old]:g.operand_first[old + 1]] {
                no := ro(b, new_id, o)
                if no.op != NO_NODE {
                    if int(no.op) < lo || int(no.op) > hi { graph_fatal(g.origin[old], "an operand of '%s' is in another code", g.name[old]) }
                    no.op -= Node_Id(lo)
                }
                append(&c.operands, no)
            }
        }
        // A subtree is one run of ids: each node's last is its last descendant's.
        for at := count - 1; at >= 0; at -= 1 {
            if p := c.parent[at]; p != NO_NODE && c.last[at] > c.last[p] { c.last[p] = c.last[at] }
        }
        if len(outer) > 0 { graph_resize(c, count + len(outer)) }
        for r, k in outer {
            at := count + k
            c.kind[at], c.op[at], c.written[at] = g.kind[r], g.op[r], g.written[r]
            c.name[at], c.type_[at], c.origin[at] = g.name[r], g.type_[r], g.origin[r]
            c.parent[at], c.last[at], c.refers[at], c.stmt[at] = NO_NODE, Node_Id(at), NO_NODE, -1
            c.operand_first[at] = i32(len(c.operands))
        }
        append(&c.operand_first, i32(len(c.operands)))
        delete(outside)
        root := Node_Id(nodes[lo])
        if g.kind[root] == .Const { pc.consts[const_of[root]] = c } else { pc.funs[ts_of[root]] = c }
    }
    // A run's operations in the order they are placed (a segment built
    // after what follows it in its run goes before it), in its code. What
    // entered the operation that began it — dropped, or placed after another
    // — enters the first placed (none, when there is none).
    next_kept := make(map[Node_Id]Node_Id, context.temp_allocator)
    placed := make([dynamic]Node_Id, context.temp_allocator)
    for old in runs {
        ops := g.run_ops[g.run_first[old]:g.run_first[old + 1]]
        clear(&placed)
        for op in ops {
            if !graph_dropped(b, op) { append(&placed, re(new_id, op)) }
        }
        if !slice.is_sorted(placed[:]) { slice.sort(placed[:]) }
        first := Node_Id(nodes[placed[0]]) if len(placed) > 0 else NO_NODE
        for op in ops {   // (its leading dropped ones, and the first kept)
            if op != first { next_kept[op] = first }
            if !graph_dropped(b, op) { break }
        }
        if len(placed) == 0 { continue }
        ci := code_of[placed[0]]
        c, lo := pc.codes[ci], Node_Id(lo_of[ci])
        append(&c.run_first, i32(len(c.run_ops)))
        for op in placed { append(&c.run_ops, op - lo) }
    }
    for c in pc.codes { append(&c.run_first, i32(len(c.run_ops))) }
    // (A `then` into a run that never got an operation leads nowhere.)
    for e in g.edges {
        if !kept(new_id, e.from) { continue }
        to, written := e.to, e.written
        if to != NO_NODE && (graph_dropped(b, to) || to in next_kept) {
            to = next_kept[to] or_else NO_NODE
            if to != NO_NODE { written = g.written[to] }
        }
        if to == NO_NODE { continue }
        from, into := place(code_of[:], lo_of[:], new_id, e.from), place(code_of[:], lo_of[:], new_id, to)
        if from.code != into.code { graph_fatal(g.origin[e.from], "a then from '%s' into another code", g.name[e.from]) }
        append(&pc.codes[from.code].edges, Edge{from = from.id, to = into.id, written = written})
    }
    // What only some nodes have, each to its code: counted, each code's
    // reserved, then put.
    Side :: enum { Consts, Sides, Defer }
    counts := make([][Side]i32, len(pc.codes), context.temp_allocator)
    count :: proc(counts: [][Side]i32, code_of: []i32, new_id: []Node_Id, old: Node_Id, s: Side) {
        if old == NO_NODE || new_id[old] == NO_NODE { return }
        if c := code_of[new_id[old]]; c >= 0 { counts[c][s] += 1 }
    }
    for id in g.consts { count(counts, code_of, new_id, id, .Consts) }
    for id in g.assert_sides { count(counts, code_of, new_id, id, .Sides) }
    for id in g.defer_of { count(counts, code_of, new_id, id, .Defer) }
    for c, i in pc.codes {
        n := counts[i]
        if n[.Consts] > 0 { reserve(&c.consts, int(n[.Consts])) }
        if n[.Sides] > 0 { reserve(&c.assert_sides, int(n[.Sides])) }
        if n[.Defer] > 0 { reserve(&c.defer_of, int(n[.Defer])) }
    }
    for id in g.settled {
        if !kept(new_id, id) { continue }
        p := place(code_of[:], lo_of[:], new_id, id)
        append(&pc.codes[p.code].settled, p.id)
    }
    for c in pc.codes { slice.sort(c.settled[:]) }
    for id, v in g.consts { if kept(new_id, id) { p := place(code_of[:], lo_of[:], new_id, id); if p.code >= 0 { pc.codes[p.code].consts[p.id] = v } } }
    for id, s in g.assert_sides { if kept(new_id, id) { p := place(code_of[:], lo_of[:], new_id, id); if p.code >= 0 { pc.codes[p.code].assert_sides[p.id] = s } } }
    for op, d in g.defer_of {
        if !kept(new_id, op) { continue }
        p := place(code_of[:], lo_of[:], new_id, op)
        pc.codes[p.code].defer_of[p.id] = place(code_of[:], lo_of[:], new_id, d).id
    }
    graph_free_columns(g)
    return pc
}

// The storage of a graph's columns and tables, before it is replaced.
@(private="file")
graph_free_columns :: proc(g: ^Program_Graph) {
    delete(g.kind); delete(g.op); delete(g.written); delete(g.parent); delete(g.last)
    delete(g.name); delete(g.type_); delete(g.origin); delete(g.refers); delete(g.stmt)
    delete(g.operands); delete(g.operand_first); delete(g.run_ops); delete(g.run_first)
    delete(g.edges); delete(g.out_first)
    delete(g.scope_node); delete(g.stmts); delete(g.unreachable); delete(g.settled)
    delete(g.consts); delete(g.assert_sides); delete(g.consumes); delete(g.decl_tok)
    delete(g.callee); delete(g.defer_of); delete(g.constant); delete(g.const_code)
}

// A type with its `:=` bindings' deferred widths settled — the one each
// adopted, else the default, i64 or f64. (A literal's own, with no binding,
// takes the type its use gives it — except behind a pointer, which no use
// types.)
graph_settled :: proc(t: Type, pointee := false) -> Type {
    #partial switch v in t {
    case Type_Infer_Int:
        if v.cell == nil && !pointee { return t }
        r := resolve_infer(t)
        return Type_Numeric{.Signed, 64} if is_infer(r) else r
    case Type_Infer_Float:
        if v.cell == nil && !pointee { return t }
        r := resolve_infer(t)
        return Type_F64{} if is_infer(r) else r
    case ^Type_Ptr:
        if is_infer(v.elem) { return new_clone(Type_Ptr{elem = graph_settled(v.elem, pointee = true)}) }
    }
    return t
}

// A new node. The columns grow in chunks and are written by index: ten
// appends per node cost twice as much, and most nodes are operations.
@(private="file")
graph_node :: proc(b: ^Graph_Builder, kind: Node_Kind, written: Written, parent: Node_Id,
                   name: string, t: Type, origin: Span) -> Node_Id {
    g := b.g
    i := b.nodes
    if i >= len(g.kind) { graph_resize(g, max(2 * len(g.kind), 1 << 16)) }
    id := Node_Id(i)
    g.kind[i] = kind
    g.op[i] = .Var
    g.written[i] = written
    g.parent[i] = parent
    g.last[i] = id
    g.name[i] = name
    g.type_[i] = t if b.body != nil else graph_settled(t)   // (a body's settle with it)
    g.origin[i] = origin
    g.refers[i] = NO_NODE
    g.callee[i] = nil
    g.stmt[i] = b.stmt
    g.decl_tok[i] = 0
    g.constant[i] = 0
    g.operand_first[i] = i32(len(g.operands))
    b.nodes += 1
    return id
}

// Every per-node column to `n` entries.
@(private="file")
graph_resize :: proc(g: ^Program_Graph, n: int) {
    resize(&g.kind, n)
    resize(&g.op, n)
    resize(&g.written, n)
    resize(&g.parent, n)
    resize(&g.last, n)
    resize(&g.name, n)
    resize(&g.type_, n)
    resize(&g.origin, n)
    resize(&g.refers, n)
    resize(&g.callee, n)
    resize(&g.stmt, n)
    resize(&g.decl_tok, n)
    resize(&g.constant, n)
    resize(&g.operand_first, n)
}

// End a scope: its subtree is everything added since it.
@(private="file")
graph_close :: proc(b: ^Graph_Builder, id: Node_Id) {
    b.g.last[id] = Node_Id(b.nodes - 1)
}

graph_fatal :: proc(span: Span, format: string, args: ..any) -> ! {
    loc := span_location(span) if span_file(span) != "" else ""
    emit_diagnostic(.Graph_Error, loc, format, ..args)
    flush_diagnostics()
    os.exit(1)
}

// The pointer behind a checked scope or type, for identity.
@(private="file")
graph_type_ptr :: proc(t: Type) -> rawptr {
    #partial switch v in t {
    case ^Type_Scope:    return v
    case ^Type_Union:    return v
    case ^Type_Enum:     return v
    case ^Type_Distinct: return v
    }
    return nil
}

@(private="file")
graph_index :: proc(b: ^Graph_Builder) {
    add :: proc(b: ^Graph_Builder, span: Span, t: Type) {
        if span == {} { return }
        if span not_in b.by_span { b.by_span[span] = {} }
        list := &b.by_span[span]
        for x in list { if graph_type_ptr(x) == graph_type_ptr(t) { return } }
        append(list, t)
    }
    t := b.checked.table
    for _, st in t.structs          { add(b, st.body_span, st) }
    for _, ft in t.funs             { add(b, ft.body_span, ft) }
    for _, ft in b.checked.functions { add(b, ft.body_span, ft) }
    for _, u in t.unions            { add(b, u.span, u) }
    for _, e in t.enums             { add(b, e.span, e) }
    for _, d in t.distinct_types    { add(b, d.span, d) }
    // The tables are maps; order a span's instances by name so ids are stable.
    for _, list in b.by_span {
        slice.sort_by(list[:], proc(x, y: Type) -> bool { return ask_type_name(x) < ask_type_name(y) })
    }
}

// --- statements ---------------------------------------------------------------

// What the builder keys a statement or an expression by: its node in the
// tree, salted in a generic's instance (tc_sid). 0 is none.
Syntax_Id :: distinct u64

// What a statement outside any body declares — a module's, a body's
// definition — as the checker reads it, for the builder
// to build where it goes (graph_decl_stmt).
Graph_Decl :: struct {
    id:      Syntax_Id,
    span:    Span,
    kind:    Stmt_Kind,          // what it does, as the statements table has it
    form:    Graph_Decl_Form,
    settles: bool,               // a variable's or a constant's: built as the checker settles it
    name:    string,             // what it names: an import, a constant, a scope, a type
    names:   []string,           // .Names: each name, "" where it declares none (a store, `_`)
    value:   Syntax_Id,            // .Const: its value (0: none), which its uses find it by
    generic: bool,               // .Scope, .Union: a generic's, built for each instance
    parts:   []Graph_Decl_Part,  // .Foreign: its funs; .Union: an enum's variants
}

Graph_Decl_Part :: struct {
    name: string,
    span: Span,
}

Graph_Decl_Form :: enum u8 {
    None,       // declares nothing: a call, a return, a rule, a header
    Names,
    Import,
    Const,
    Scope,      // a fun or a struct
    Foreign,
    Union,      // or an enum
    Type,       // a distinct type or an alias
    Dispatch,
    Code,       // code outside a body: an error
}

// A statement outside any body — a module's, a body's definition: the code
// it defines, a fun's or a struct's or a constant's, put here. (Each is
// lowered on its own, lower.odin.)
@(private="file")
graph_decl_stmt :: proc(b: ^Graph_Builder, d: Graph_Decl, parent: Node_Id, site: Decl_Site, declared: Graph_Declared = {}) {
    // (A constant the checker built: put here.)
    if si, built := b.const_segs[d.id]; built {
        b.g.parent[b.segs[si].root] = parent
        graph_anchor_here(b, si)
        return
    }
    // (What runs nothing — a module's variable, which no function sees, an
    // import, a type, a dispatch group, a foreign fun, a constant nothing
    // uses — is no code: nothing here.)
    #partial switch d.form {
    case .Scope:
        saved_stmt := b.stmt
        b.stmt = i32(len(b.g.stmts))
        append(&b.g.stmts, Graph_Stmt{span = d.span, kind = declared.kind if declared.set else d.kind})
        defer b.stmt = saved_stmt
        graph_scope_def(b, d, parent)
    case .Code:
        graph_fatal(d.span, "code outside a body reached the graph")
    }
}

// A plain declaration, as a field of the owning struct or a local / constant.
@(private="file")
graph_decl :: proc(b: ^Graph_Builder, site: Decl_Site, parent: Node_Id, name: string, t: Type, span: Span, tok := Token_Id(0)) -> Node_Id {
    t := t
    if site.kind == .Field && site.owner != nil {
        // Signatures resolve on demand, so a struct nothing uses has no typed
        // fields yet: the field exists, its type is unknown.
        if i, ok := site.owner.field_map[name]; ok {
            t = site.owner.fields[i].type_
        } else if site.owner.sig_state == .Resolved {
            graph_fatal(span, "field '%s' is missing from struct '%s'", name, site.owner.name)
        }
    }
    d := graph_node(b, site.kind, .Explicit, parent, name, t, span)
    graph_declare(b, d, tok)
    return d
}


// `void`: the uninitialized value (a pointer's null), as written.
@(private="file")
graph_void :: proc(b: ^Graph_Builder, t: Type, span: Span) -> Operand {
    return graph_op_value(b, .Const, .Explicit, span, t, "void")
}

// The struct a bare declaration constructs, or zero for anything else. An
// array of structs is zeroed, then each element constructed. A struct that
// can't be built bare stays zero: an array's elements (the checker warns), a
// `~T` slot's field (the shape shortcut fills it; the checker rejects others).
// (Its constructor runs on `args`: its params' defaults, the checker's —
// an array's elements', each on the same ones.)
@(private="file")
graph_construct_bare :: proc(b: ^Graph_Builder, dest: Operand, t: Type, args: []Operand, span: Span) {
    ops := make([dynamic]Operand, 0, 1 + len(args), context.temp_allocator)
    append(&ops, dest)
    append(&ops, ..args)
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        if v.kind == .Struct && !v.is_module && constructs_bare(v) {
            graph_call_op(b, .Construct, .Synthetic, span, v, t, ..ops[:])
            return
        }
    case ^Type_Fixed_Array:
        graph_op(b, .Zero, .Synthetic, span, t, "", dest)
        if st := graph_elem_struct(v.elem); st != nil && constructs_bare(st) { graph_call_op(b, .Construct, .Synthetic, span, st, v.elem, ..ops[:]) }
        return
    case ^Type_Partial_Array:
        graph_op(b, .Zero, .Synthetic, span, t, "", dest)
        if st := graph_elem_struct(v.elem); st != nil && constructs_bare(st) { graph_call_op(b, .Construct, .Synthetic, span, st, v.elem, ..ops[:]) }
        return
    }
    graph_op(b, .Zero, .Synthetic, span, t, "", dest)
}

// The struct an array's elements construct, through nested arrays.
graph_elem_struct :: proc(t: Type) -> ^Type_Scope {
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        if v.kind == .Struct && !v.is_module { return v }
    case ^Type_Fixed_Array:   return graph_elem_struct(v.elem)
    case ^Type_Partial_Array: return graph_elem_struct(v.elem)
    }
    return nil
}


// --- control flow -----------------------------------------------------------

// A value at the type its use takes: a narrower number widens, implied —
// sign- or zero-extended by its own signedness, or f32 to f64 — wherever the
// checker lets a narrower value in (an operation's operands, a store, an
// argument, a return, an index). A literal already has its use's type.
@(private="file")
graph_widen :: proc(b: ^Graph_Builder, v: Operand, to: Type, span: Span) -> Operand {
    if v.op == NO_NODE || v.out != 0 || !graph_widens(b.g.type_[v.op], to) { return v }
    return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), v)
}

// Whether a value of type `from` widens to `to`: both numbers of one kind,
// `to` the wider.
@(private="file")
graph_widens :: proc(from, to: Type) -> bool {
    if from == nil || to == nil || is_infer(from) || is_infer(to) { return false }
    fb, fk, fok := numeric_info(from)
    tb, tk, tok := numeric_info(to)
    return fok && tok && tb > fb && (fk == .Float) == (tk == .Float)
}

// A slice, or a pointer to one.
graph_header_of :: proc(t: Type) -> bool {
    t := t
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { t = pt.elem }
    _, is_slice := distinct_base(t).(^Type_Slice)
    return is_slice
}

// A partial array, or a pointer to one.
graph_partial_of :: proc(t: Type) -> bool {
    t := t
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { t = pt.elem }
    _, is_partial := distinct_base(t).(^Type_Partial_Array)
    return is_partial
}


// A binary operation: its operator, its type and its sides'.
Graph_Work :: struct {
    op:        Token_Kind,
    t, lt, rt: Type,
}

graph_work :: proc(w: Graph_Work) -> Type {
    if !is_comparison_op(w.op) && w.t != nil && !is_infer(w.t) && !is_any(w.t) { return w.t }
    if w.lt == nil || w.rt == nil || is_infer(w.lt) || is_infer(w.rt) { return nil }
    if t, ok := common_numeric_type(distinct_base(w.lt), distinct_base(w.rt)); ok { return t }
    return nil
}

// The result types of the fun whose code is being built.
@(private="file")
graph_result_types :: proc(b: ^Graph_Builder) -> []Type {
    if ts := graph_code_scope(b); ts != nil { return ts.return_types[:] }
    return nil
}

// The fun or struct whose code is being built.
@(private="file")
graph_code_scope :: proc(b: ^Graph_Builder) -> ^Type_Scope {
    for p := b.code.block; p != NO_NODE; p = b.g.parent[p] {
        #partial switch b.g.kind[p] {
        case .Fun, .Struct:
            ts, _ := b.g.type_[p].(^Type_Scope)
            return ts
        }
    }
    return nil
}

// The results after `vals` — each a trailing err a return may leave out —
// as an implied `Ok`, the err that is none. (Code falling off the end of
// results that aren't errs is the missing-return check's to report: it
// stops there.)
@(private="file")
graph_implied_oks :: proc(b: ^Graph_Builder, vals: ^[dynamic]Operand, rts: []Type, span: Span) {
    for i := len(vals); i < len(rts) && is_err_type(rts[i]); i += 1 {
        append(vals, graph_const(b, .Implied, span, rts[i], "Ok", Const_Value{}))
    }
}


// A collection's place each time the loop needs it.
@(private="file")
graph_coll_place :: proc(b: ^Graph_Builder, fl: ^Graph_For, span: Span) -> Operand {
    if slot := fl.coll_slot; slot != NO_NODE { return graph_var(b, b.g.name[slot], slot, b.g.type_[slot], span) }
    return graph_base_of(b, graph_place_again(b, fl.coll, span), fl.coll_t, span, fl.coll_self)
}

graph_loop_view_of :: proc(t: Type) -> Type {
    t := t
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { t = pt.elem }
    #partial switch v in distinct_base(t) {
    case ^Type_Slice:
        return v
    case ^Type_Partial_Array:
        view := new(Type_Slice)
        view.elem = v.elem
        return view
    }
    return nil
}

// A collection's length: known for a fixed array, its header's `len` otherwise.
@(private="file")
graph_len :: proc(b: ^Graph_Builder, place: Operand, t: Type, span: Span) -> Operand {
    t := t
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { t = pt.elem }
    if fa, fixed := distinct_base(t).(^Type_Fixed_Array); fixed {
        return graph_const(b, .Synthetic, span, slice_header_width_type, "len", Const_Value{int = i128(fa.size)})
    }
    len_place := graph_op_value(b, .Field, .Synthetic, span, slice_header_width_type, "len", place)
    return graph_read(b, len_place, slice_header_width_type, span)
}

// `break` / `continue`: leave the scopes down to the loop body, then jump.
@(private="file")
graph_loop_exit :: proc(b: ^Graph_Builder, span: Span, is_break: bool) {
    if len(b.code.loops) == 0 { graph_fatal(span, "a loop exit outside any loop") }
    l := b.code.loops[len(b.code.loops) - 1]
    graph_exit_scopes(b, l.scope, span)
    graph_jump(b, l.done if is_break else l.cont, .Explicit, span)
}

// Enter a scope: an arena mark when it holds a big value. (A struct's
// declarations are its fields: in Self, not on the arena.) Nor main's body:
// its scope ends with the program, which made the arena in its setup.
@(private="file")
graph_scope_open :: proc(b: ^Graph_Builder, block: Node_Id, span: Span) {
    // The checker opens a scope before its declarations are typed: its mark,
    // and the reset at each of its exits, are made and decided when the
    // graph is put together (graph_body_settle).
    if b.arena && b.g.kind[block] != .Struct {
        append(&b.body.marks, Graph_Arena{mark = graph_op(b, .Arena_Mark, .Synthetic, span), block = block})
        append(&b.code.scopes, Code_Scope{block = block, tentative = len(b.body.marks) - 1})
        return
    }
    append(&b.code.scopes, Code_Scope{block = block, tentative = -1})
}

// Leave a scope at its end: its defers and reset, if the end is reached.
@(private="file")
graph_scope_close :: proc(b: ^Graph_Builder, span: Span) {
    if graph_reachable(b) { graph_exit_scopes(b, len(b.code.scopes) - 1, span) }
    s := pop(&b.code.scopes)
    delete(s.defers)
}

// What leaving scopes[from:] runs, innermost first: each scope's defers, the
// last registered first, then its arena reset.
@(private="file")
graph_exit_scopes :: proc(b: ^Graph_Builder, from: int, span: Span) {
    for i := len(b.code.scopes) - 1; i >= from; i -= 1 {
        s := &b.code.scopes[i]
        for j := len(s.defers) - 1; j >= 0; j -= 1 {
            op := graph_op(b, .Run_Defer, .Synthetic, span)
            b.g.defer_of[op] = s.defers[j]
        }
        if s.tentative >= 0 { append(&b.body.marks[s.tentative].resets, graph_op(b, .Arena_Reset, .Synthetic, span)) }
    }
}

// --- code and runs --------------------------------------------------------

// Start the code of a fun, a struct's initializers or a defer's block: a fresh
// run, entered from `owner`. Returns the enclosing code, for graph_code_end.
@(private="file")
graph_code_begin :: proc(b: ^Graph_Builder, owner: Node_Id) -> Code {
    saved := b.code
    b.code = Code{active = true, block = owner}
    entry := graph_run_new(b)
    graph_then(b, owner, entry, .Synthetic)
    b.code.run = entry
    return saved
}


@(private="file")
graph_code_finish :: proc(b: ^Graph_Builder, span: Span) {
    if graph_reachable(b) {
        // Falling off the end returns `Ok` for each err result (the checker
        // allows it for those alone).
        vals := make([dynamic]Operand, 0, 2, context.temp_allocator)
        graph_implied_oks(b, &vals, graph_result_types(b), span)
        graph_exit_scopes(b, 0, span)
        graph_op(b, .Return, .Synthetic, span, nil, "", ..vals[:])
        graph_run_close(b)
    }
    for len(b.code.scopes) > 0 {
        s := pop(&b.code.scopes)
        delete(s.defers)
    }
}

@(private="file")
graph_code_end :: proc(b: ^Graph_Builder, saved: Code) {
    delete(b.code.scopes)
    delete(b.code.loops)
    delete(b.code.tuples)
    b.code = saved
}

@(private="file")
graph_run_new :: proc(b: ^Graph_Builder) -> ^Run {
    r := new(Run)
    append(&b.runs, r)
    return r
}

// `from`'s next operation is the first of `to`, now or once it has one.
@(private="file")
graph_then :: proc(b: ^Graph_Builder, from: Node_Id, to: ^Run, written: Written) {
    if len(to.ops) > 0 {
        append(&b.g.edges, Edge{from = from, to = to.ops[0], written = written})
    } else {
        // Its place among the edges now — a branch's targets keep their order
        // (yes, then no) — and its target once the run has an operation.
        append(&to.waiting, i32(len(b.g.edges)))
        append(&b.g.edges, Edge{from = from, to = NO_NODE, written = written})
    }
}

// Whether the run being filled can be reached: a run nothing enters and
// nothing is in yet is the dead end after a return.
@(private="file")
graph_reachable :: proc(b: ^Graph_Builder) -> bool {
    r := b.code.run
    return r != nil && (len(r.ops) > 0 || len(r.waiting) > 0)
}

// Append an operation to the run being filled. Code after a return or jump
// goes in a run nothing enters.
@(private="file")
graph_emit :: proc(b: ^Graph_Builder, id: Node_Id) {
    if b.code.run == nil { b.code.run = graph_run_new(b) }
    r := b.code.run
    if len(r.ops) == 0 {
        for w in r.waiting {
            b.g.edges[w].to = id
            b.g.edges[w].written = b.g.written[id]
        }
        clear(&r.waiting)
    }
    append(&r.ops, id)
}

// The run is complete: store its operations.
@(private="file")
graph_run_close :: proc(b: ^Graph_Builder) {
    r := b.code.run
    append(&b.g.run_first, i32(len(b.g.run_ops)))
    append(&b.g.run_ops, ..r.ops[:])
    b.code.run = nil
}

@(private="file")
graph_jump :: proc(b: ^Graph_Builder, to: ^Run, w: Written, span: Span) {
    op := graph_op(b, .Jump, w, span)
    graph_then(b, op, to, w)
    graph_run_close(b)
}

@(private="file")
graph_branch :: proc(b: ^Graph_Builder, cond: Operand, yes, no: ^Run, w: Written, span: Span) {
    op := graph_op(b, .Branch, w, span, nil, "", cond)
    graph_then(b, op, yes, w)
    graph_then(b, op, no, w)
    graph_run_close(b)
}

@(private="file")
graph_switch :: proc(b: ^Graph_Builder, operands: []Operand, arms: []^Run, span: Span) {
    op := graph_op(b, .Switch, .Explicit, span, nil, "", ..operands)
    for r in arms { graph_then(b, op, r, .Explicit) }
    graph_run_close(b)
}

// --- operations -----------------------------------------------------------

graph_op :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, t: Type = nil, name := "", operands: ..Operand) -> Node_Id {
    id := graph_node(b, .Op, w, b.code.block, name, t, span)
    b.g.op[id] = kind
    append(&b.g.operands, ..operands)
    graph_emit(b, id)
    return id
}

graph_op_value :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, t: Type = nil, name := "", operands: ..Operand) -> Operand {
    return Operand{graph_op(b, kind, w, span, t, name, ..operands), 0}
}

// A variable's place: `decl`, its declaration (graph_local, graph_global).
graph_var :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, t: Type, span: Span) -> Operand {
    if decl == NO_NODE { graph_fatal(span, "the variable '%s' has no declaration", name) }
    // (As written as its declaration — a temporary's synthetic; the
    // compiler's own globals, synthetic, written by name.)
    w := b.g.written[decl] if b.g.parent[decl] != b.program else .Explicit
    op := graph_op(b, .Var, w, span, t, name)
    b.g.refers[op] = decl
    return Operand{op, 0}
}

// Where a value is stored, as a recipe: the place's operations are emitted
// where the store happens, after the value — which may have crossed runs on
// the way (an `if` expression, `and`, `?`). An assignment's target is worked
// out before its value, so its place arrives computed (.At).
Dest :: struct {
    kind:   Dest_Kind,
    at:     Operand,   // .At: the place, already computed
    decl:   Node_Id,   // .Var: its declaration, when known here
    name:   string,    // .Var: the variable; .Field: the field; .Variant: the variant
    index:  int,       // .Index
    type_:  Type,
    parent: ^Dest,     // .Field, .Index, .Variant: the value they are part of
}

Dest_Kind :: enum u8 { Var, At, Field, Index, Variant }

graph_dest_var :: proc(name: string, decl: Node_Id, t: Type) -> Dest {
    return Dest{kind = .Var, name = name, decl = decl, type_ = t}
}

// Emit a destination's place in the current run.
graph_dest_place :: proc(b: ^Graph_Builder, d: Dest, span: Span) -> Operand {
    switch d.kind {
    case .Var:   return graph_var(b, d.name, d.decl, d.type_, span)
    case .At:    return d.at
    case .Field: return graph_op_value(b, .Field, .Explicit, span, d.type_, d.name, graph_dest_place(b, d.parent^, span))
    case .Index: return graph_op_value(b, .Index, .Explicit, span, d.type_, "", graph_dest_place(b, d.parent^, span), graph_const_index(b, d.index, span))
    case .Variant: return graph_op_value(b, .Variant, .Implied, span, d.type_, d.name, graph_dest_place(b, d.parent^, span))
    }
    return NO_VALUE
}

graph_read :: proc(b: ^Graph_Builder, place: Operand, t: Type, span: Span) -> Operand {
    return graph_op_value(b, .Read, b.g.written[place.op], span, t, "", place)
}

// A synthetic local of the current block, for a value that outlives a run.
// (Storage no use types — an if-expression's of a bare literal — settles
// with its body's: an unsettled width takes the default, as behind a
// pointer.)
graph_slot :: proc(b: ^Graph_Builder, name: string, t: Type, span: Span) -> Node_Id {
    id := graph_node(b, .Local, .Synthetic, b.code.block, name, t, span)
    append(&b.body.slots, id)
    return id
}

// A plain place walked once more (another run): the operations that name it
// — a variable, a constant table, a field, an element at a constant or at a
// variable's value, what a pointer points at, bytes seen as a type — copied.
// (Its base's dereference, at the walk's span: graph_base_of.)
graph_place_again :: proc(b: ^Graph_Builder, p: Operand, span: Span) -> Operand {
    if p.op == NO_NODE { return p }
    g := b.g
    id := p.op
    #partial switch g.op[id] {
    case .Var, .Global, .Const, .Field, .Swizzle, .Index, .Deref, .View, .Read, .Cast:
    case:
        graph_fatal(g.origin[id], "a place walked again holds a %v", g.op[id])
    }
    src := graph_built_operands(b, id)
    ops := make([]Operand, len(src), context.temp_allocator)
    for o, k in src { ops[k] = graph_place_again(b, o, span) }
    n := graph_op_value(b, g.op[id], g.written[id], g.origin[id], g.type_[id], g.name[id], ..ops)
    g.refers[n.op] = g.refers[id]
    if c, ok := g.consts[id]; ok { g.consts[n.op] = c }
    if g.op[id] == .Const { graph_const_settles(b, n.op, g.type_[id]) }
    g.constant[n.op] = g.constant[id]
    // (A widening decided when the graph is put together: this one too, alike.)
    if f := b.body; f != nil && g.op[id] == .Cast {
        for w in f.widens {
            if w.id != id { continue }
            twin := w
            twin.id, twin.v = n.op, ops[0]
            append(&f.widens, twin)
            break
        }
    }
    return Operand{n.op, p.out}
}

// A plain place left out, its operations built for walking it again (a
// place used only in the runs where it's walked: graph_place_again).
graph_drop_place :: proc(b: ^Graph_Builder, p: Operand) {
    if p.op == NO_NODE { return }
    for o in graph_built_operands(b, p.op) { graph_drop_place(b, o) }
    graph_drop(b, p.op, NO_VALUE)
}

// A plain place's base, from its place: through a
// pointer, what it points at.
graph_base_of :: proc(b: ^Graph_Builder, p: Operand, t: Type, span: Span, is_self := false) -> Operand {
    if is_self { return p }   // (through `#self` is Self)
    if pt, ok := distinct_base(t).(^Type_Ptr); ok {
        return graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)
    }
    return p
}

graph_pointee :: proc(t: Type) -> Type {
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { return pt.elem }
    return t
}

graph_aggregate :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        return v.kind == .Struct
    case ^Type_Fixed_Array, ^Type_Partial_Array, ^Type_Union:
        return true
    }
    return false
}


// The type a destination holds: an existing place's own (a target's type as
// the checker records it can be the whole variable's: `a[i] = x`).
graph_dest_type :: proc(b: ^Graph_Builder, d: Dest) -> Type {
    if d.kind == .At && d.at.op != NO_NODE {
        if t := b.g.type_[d.at.op]; t != nil { return t }
    }
    return d.type_
}

// The call's results, each written to its field.
graph_spread_results :: proc(b: ^Graph_Builder, span: Span, sd: ^Scope_Body, parent: ^Dest, callee: ^Type_Scope, c: Operand) {
    for rt, i in callee.return_types {
        if i >= len(sd.fields) { break }
        f := sd.fields[i]
        val := Operand{c.op, i32(i)}
        _, to_slice := distinct_base(f.type_).(^Type_Slice)
        if _, from_array := distinct_base(rt).(^Type_Fixed_Array); to_slice && from_array {
            slot := graph_slot(b, "temp", rt, span)
            graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", slot, rt, span), val)
            val = graph_op_value(b, .Slice, .Implied, span, f.type_, "", graph_var(b, "temp", slot, rt, span))
        }
        field := graph_dest_place(b, Dest{kind = .Field, name = f.name, type_ = f.type_, parent = parent}, span)
        graph_op(b, .Write, .Explicit, span, nil, "", field, val)
    }
}

// A union's variant `name` as a struct: its tag first, then its fields; nil
// when t is no union with that variant.
graph_variant_struct :: proc(b: ^Graph_Builder, t: Type, name: string) -> ^Type_Scope {
    ut, is_union := distinct_base(t).(^Type_Union)
    if !is_union || name == "" { return nil }
    return ut.variant_structs[name]
}

// An array's element type.
graph_elem_type :: proc(t: Type) -> Type {
    #partial switch v in distinct_base(t) {
    case ^Type_Fixed_Array:   return v.elem
    case ^Type_Partial_Array: return v.elem
    case ^Type_Slice:         return v.elem
    }
    return nil
}

// `?` after its call is built: a branch on the call's err — its failure
// returns the err — then the call's value, where it didn't fail.
graph_try_after :: proc(b: ^Graph_Builder, span: Span, inner: Operand) -> Operand {
    outs := graph_outputs_op(b, inner, span)
    n := graph_outputs(b, outs)
    if n == 0 { graph_fatal(span, "`?` on a call with no err output") }
    err := Operand{outs, i32(n - 1)}
    fail, ok := graph_run_new(b), graph_run_new(b)
    failed := graph_op_value(b, .Cast, .Implied, span, Type_Bool{}, "bool", err)   // an error: nonzero
    graph_branch(b, failed, fail, ok, .Implied, span)
    b.code.run = fail
    // It returns the err, and each other result's zero value (implied).
    rts := graph_result_types(b)
    vals := make([dynamic]Operand, 0, len(rts), context.temp_allocator)
    for i in 0 ..< len(rts) - 1 { append(&vals, graph_const(b, .Implied, span, rts[i], "zero", Const_Value{})) }
    append(&vals, err)
    graph_exit_scopes(b, 0, span)
    graph_op(b, .Return, .Implied, span, nil, "", ..vals[:])
    graph_run_close(b)
    b.code.run = ok
    if n == 1 { return NO_VALUE }   // err only
    return inner
}

// The operation whose outputs a call's value `v` is the first of: the call; a
// fallible construction's, its construct (the value is the built place, read).
@(private="file")
graph_outputs_op :: proc(b: ^Graph_Builder, v: Operand, span: Span) -> Node_Id {
    if v.op != NO_NODE && b.g.op[v.op] == .Call { return v.op }
    if v.op != NO_NODE && b.g.op[v.op] == .Read && b.code.constructed != NO_NODE { return b.code.constructed }
    graph_fatal(span, "a call's outputs, built as no call")
}

// How many outputs a call has: its callee's return list (a fallible
// constructor's includes the struct itself); through a function value, its
// signature's.
@(private="file")
graph_outputs :: proc(b: ^Graph_Builder, op: Node_Id) -> int {
    callee := b.g.callee[op]
    if callee == nil && b.g.op[op] == .Call {
        ops := graph_built_operands(b, op)
        if len(ops) > 0 && ops[0].op != NO_NODE {
            if ft, is_fn := distinct_base(b.g.type_[ops[0].op]).(^Type_Scope); is_fn && ft.kind == .Fun { callee = ft }
        }
    }
    if callee == nil { return 0 }
    if list, is_ctor := constructor_effective_returns(callee); is_ctor { return len(list) }
    return len(callee.return_types)
}

// A call or construct operation, with a Calls edge to what it runs.
graph_call_op :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, callee: ^Type_Scope, t: Type, operands: ..Operand) -> Node_Id {
    op := graph_op(b, kind, w, span, t, graph_call_name(callee), ..operands)
    b.g.callee[op] = callee
    return op
}

@(private="file")
graph_call_name :: proc(callee: ^Type_Scope) -> string {
    return callee.source_name if callee.source_name != "" else ask_demangle(callee.name, callee.home_package)
}

// An element's position, as a constant.
@(private="file")
graph_const_index :: proc(b: ^Graph_Builder, i: int, span: Span) -> Operand {
    return graph_const(b, .Synthetic, span, slice_header_width_type, fmt.aprintf("%d", i), Const_Value{int = i128(i)})
}

// A constant whose width is its use's: settled with its body's.
@(private="file")
graph_const_settles :: proc(b: ^Graph_Builder, id: Node_Id, t: Type) {
    if !is_infer(t) { return }
    if b.body == nil { graph_fatal(b.g.origin[id], "a constant of open width outside any body") }
    append(&b.body.consts, id)   // its width is known when its body's are
}

// A constant operation, with its value when it has one.
graph_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, value: Maybe(Const_Value)) -> Operand {
    o := graph_op_value(b, .Const, w, span, t, name)
    if v, ok := value.?; ok {
        b.g.consts[o.op] = v
        graph_const_settles(b, o.op, t)
    }
    return o
}

// The value a name resolved to stands for, when the resolution holds it: an
// enum variant's, an array's length. (A named constant's is its code's:
// graph_fold_uses.)
//
// What a name that stands for a constant is, as the builder builds it: a
// declared constant's value (its id — the code its uses are folded from), or
// a value already known (an enum's variant, a length).
Graph_Named :: struct {
    value: Syntax_Id,
    known: Maybe(Const_Value),
}

// A named register-value constant where it's used: its declaration's
// value, computed at the use's width once the graph is put together
// (graph_fold_uses). An enum's variant, a length: its value.
graph_named_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, n: Graph_Named) -> Operand {
    if n.value == 0 { return graph_const(b, w, span, t, name, n.known) }
    o := graph_op_value(b, .Const, w, span, t, name)
    b.g.constant[o.op] = n.value
    graph_const_settles(b, o.op, t)
    return o
}

// A string constant's global carries its text in the constants table.
graph_text :: proc(b: ^Graph_Builder, global: Operand, value: Maybe(Const_Value)) -> Operand {
    if c, ok := value.?; ok && c.is_text { b.g.consts[global.op] = c }
    return global
}

// A named constant held in memory: text, or a table — which names its
// declaration (once every one is built: a use can come first).
graph_const_global :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, n: Graph_Named) -> Operand {
    o := graph_op_value(b, .Global, w, span, t, name)
    if n.value != 0 { b.g.constant[o.op] = n.value }
    return o
}

// A type's size in bytes.
graph_size_of :: proc(t: Type) -> Maybe(Const_Value) {
    if t == nil { return nil }
    return Const_Value{int = i128(type_size(t))}
}


graph_token_text :: proc(op: Token_Kind) -> string {
    #partial switch op {
    case .Plus:          return "+"
    case .Minus:         return "-"
    case .Star:          return "*"
    case .Slash:         return "/"
    case .Modulo:        return "%"
    case .Wrap_Plus:     return "+%"
    case .Wrap_Minus:    return "-%"
    case .Wrap_Star:     return "*%"
    case .Equal_Equal:   return "=="
    case .Not_Equal:     return "!="
    case .Less:          return "<"
    case .Less_Equal:    return "<="
    case .Greater:       return ">"
    case .Greater_Equal: return ">="
    case .Ampersand:     return "&"
    case .Pipe:          return "|"
    case .Tilde:         return "~"
    case .Shift_Left:    return "<<"
    case .Shift_Right:   return ">>"
    case .Not:           return "not"
    }
    return "?"
}

// A literal's type is what its use takes: the checker leaves one whose width
// its context decides (`n + 1`, `x : u8 = 7`) as infer_int or infer_float.
// An operation comes after its operands, so walking back from the last one
// types each use before its operands. What no use decides takes the default.
@(private="file")
graph_settle_literals :: proc(g: ^Program_Graph) {
    for i := len(g.kind) - 1; i >= 0; i -= 1 {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        for o, k in graph_operands(g, id) {
            // A literal of no type yet — a number, or an untyped `void` (its
            // use's pointer: `p == void`, an argument) — takes its use's.
            if o.op == NO_NODE || o.out != 0 { continue }
            untyped_void := g.op[o.op] == .Const && g.name[o.op] == "void" && is_any(g.type_[o.op])
            if !is_infer(g.type_[o.op]) && !untyped_void { continue }
            if t := graph_literal_use(g, id, k); t != nil && !is_infer(t) {
                g.type_[o.op] = t
                if g.op[o.op] == .Const && (o.op in g.consts || g.constant[o.op] != 0) { append(&g.settled, o.op) }
            }
        }
        if is_infer(g.type_[id]) { g.type_[id] = solidify_type(g.type_[id]) }
    }
}

// The type an operation takes its k-th operand at, when that decides a
// literal's; nil when it doesn't.
@(private="file")
graph_literal_use :: proc(g: ^Program_Graph, id: Node_Id, k: int) -> Type {
    ops := graph_operands(g, id)
    #partial switch g.op[id] {
    case .Arith, .Unary:
        return g.type_[id]
    case .Compare:
        if other := ops[1 - k].op; other != NO_NODE && !is_infer(g.type_[other]) { return g.type_[other] }
    case .Write:
        if k > 0 { return g.type_[ops[0].op] }
    case .Fill:
        if k > 0 { return graph_elem_type(g.type_[ops[0].op]) }
    case .Call:
        if c := g.callee[id]; c != nil {
            if k < len(c.params) { return c.params[k].type_ }
        } else if k > 0 && ops[0].op != NO_NODE {
            // (Through a function value, its first operand: its signature's.)
            ft, is_fn := distinct_base(g.type_[ops[0].op]).(^Type_Scope)
            if is_fn && ft.kind == .Fun && k - 1 < len(ft.params) { return ft.params[k - 1].type_ }
        }
    case .Construct:   // its first operand is where it builds
        if c := g.callee[id]; c != nil && k >= 1 && k - 1 < len(c.params) { return c.params[k - 1].type_ }
    case .Return:
        fun := graph_code_owner(g, id)
        if fun == NO_NODE { return nil }
        ts, is_scope := g.type_[fun].(^Type_Scope)
        if !is_scope { return nil }
        rts := ts.return_types[:]
        if k < len(rts) { return rts[k] }   // (an operand for each result)
    case .Index, .View, .Slice, .Zero, .Carve:
        if k > 0 { return slice_header_width_type }
    case .Byte_Read:
        if k > 1 { return slice_header_width_type }
    case .Switch:
        if k > 0 { return g.type_[ops[0].op] }
    case .Branch, .Assert:
        return Type_Bool{}
    }
    return nil
}

// Each table's name: its constant's longest in the checker's table (a
// module's is there under its flat name and its bare one), the first of
// those alike.
@(private="file")
graph_table_names :: proc(b: ^Graph_Builder, pc: ^Program_Code) {
    for key, v in b.constant_names {
        if v not_in pc.tables { continue }
        if name, named := pc.table_names[v]; named && (len(name) > len(key) || len(name) == len(key) && name < key) { continue }
        pc.table_names[v] = key
    }
}

// A place as the source writes it: `o.inner.p`, `a[i]`. A temporary, or a
// place reached through an explicit dereference, has no name.
graph_place_name :: proc(g: ^Program_Graph, p: Operand) -> string {
    if p.op == NO_NODE { return "" }
    ops := graph_operands(g, p.op)
    #partial switch g.op[p.op] {
    case .Var:
        if g.written[p.op] == .Synthetic { return "" }
        return g.name[p.op]
    case .Field, .Swizzle:
        base := graph_place_name(g, ops[0])
        if base == "" { return g.name[p.op] }
        return fmt.tprintf("%s.%s", base, g.name[p.op])
    case .Deref:
        if g.written[p.op] == .Implied { return graph_place_name(g, ops[0]) }
    case .View:
        return graph_place_name(g, ops[0])   // the bytes it views
    case .Index:
        base := graph_place_name(g, ops[0])
        if base == "" { return "" }
        i := ops[1].op
        if i != NO_NODE && g.op[i] == .Cast && g.written[i] == .Implied { i = graph_operands(g, i)[0].op }
        idx := ""
        if i != NO_NODE && g.op[i] == .Read { idx = graph_place_name(g, graph_operands(g, i)[0]) }
        if idx == "" { return base }
        return fmt.tprintf("%s[%s]", base, idx)
    }
    return ""
}

// The fun or struct whose code an operation is in.
@(private="file")
graph_code_owner :: proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    for p := g.parent[id]; p != NO_NODE; p = g.parent[p] {
        #partial switch g.kind[p] {
        case .Fun, .Struct: return p
        }
    }
    return NO_NODE
}

// Each fun that consumes a param into its result: its result is built in
// its caller's slot — a struct, a fixed or partial array — and is a local
// every return returns, declared as a copy of the param (`r := pk`) of the
// result's type, the param's one mention. It reads pk only while making that
// copy, so a caller doing `x = f(x, …)` can hand it x as both pk and the
// result slot: the copy is then onto itself (skipped at runtime), and every
// write to r lands in x — no temporary, no copy back. The functional update:
// `push :: fun(pa: [..N]T, x: T) -> [..N]T { r := pa; r[r.len] = x;
// r.len += 1; return r }`, `state = update(state)`.
@(private="file")
graph_find_consumes :: proc(g: ^Program_Graph) {
    returned: map[Node_Id]Node_Id   // a fun → the local its returns return (NO_NODE: not one)
    mention:  map[Node_Id]Node_Id   // a param → its one variable operation (NO_NODE: several)
    defer { delete(returned); delete(mention) }
    for i in 0 ..< len(g.kind) {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        #partial switch g.op[id] {
        case .Var:
            if p := g.refers[id]; p != NO_NODE && g.kind[p] == .Param {
                mention[p] = NO_NODE if p in mention else id
            }
        case .Return:
            if g.written[id] != .Explicit { continue }
            fun := graph_code_owner(g, id)
            local := NO_NODE
            if ops := graph_operands(g, id); len(ops) == 1 && ops[0].op != NO_NODE && g.op[ops[0].op] == .Read {
                place := graph_operands(g, ops[0].op)[0].op
                if g.op[place] == .Var && g.refers[place] != NO_NODE && g.kind[g.refers[place]] == .Local { local = g.refers[place] }
            }
            if fun in returned && returned[fun] != local { local = NO_NODE }
            returned[fun] = local
        }
    }
    for fun, local in returned {
        if local == NO_NODE { continue }
        ft, is_scope := g.type_[fun].(^Type_Scope)
        if !is_scope || ft.kind != .Fun || len(ft.cg_returns) != 1 { continue }
        ret := distinct_base(ft.cg_returns[0])
        by_slot := as_struct_body(ret) != nil
        #partial switch _ in ret {
        case ^Type_Fixed_Array, ^Type_Partial_Array: by_slot = true
        }
        if !by_slot { continue }
        // (Its params come first among its contents.)
        for p := fun + 1; p <= g.last[fun] && g.kind[p] == .Param; p += 1 {
            v, once := mention[p]
            if !once || v == NO_NODE { continue }
            read := graph_user(g, v, g.last[fun])
            if read == NO_NODE || g.op[read] != .Read { continue }
            w := graph_user(g, read, g.last[fun])
            if w == NO_NODE || g.op[w] != .Write || g.stmt[w] < 0 || g.stmts[g.stmt[w]].kind != .Decl { continue }
            if ops := graph_operands(g, w); ops[1].op != read || g.op[ops[0].op] != .Var || g.refers[ops[0].op] != local { continue }
            for cp, k in ft.cg_params {
                if cp.name == g.name[p] && types_equal(distinct_base(cp.type_), ret) { g.consumes[fun] = k }
            }
            break
        }
    }
}

// The param a fun consumes into its result (graph_find_consumes), if any.
graph_consumed :: proc(pc: ^Program_Code, ft: ^Type_Scope) -> Maybe(int) {
    if k, consumes := pc.consumes[ft]; consumes { return k }
    return nil
}

// The first operation after op, up to `last`, that takes op's output.
@(private="file")
graph_user :: proc(g: ^Program_Graph, op, last: Node_Id) -> Node_Id {
    for id := op + 1; id <= last; id += 1 {
        if g.kind[id] != .Op { continue }
        for o in graph_operands(g, id) { if o.op == op { return id } }
    }
    return NO_NODE
}

// Sort the edge table by `from` and index it (a counting sort: one pass).
@(private="file")
graph_index_edges :: proc(g: ^Program_Graph) {
    n := len(g.kind)
    resize(&g.out_first, n + 1)
    slice.zero(g.out_first[:])
    for e in g.edges { g.out_first[e.from + 1] += 1 }
    for i in 1 ..= n { g.out_first[i] += g.out_first[i - 1] }
    sorted := make([dynamic]Edge, len(g.edges))
    next := slice.clone(g.out_first[:n], context.temp_allocator)
    for e in g.edges {
        sorted[next[e.from]] = e
        next[e.from] += 1
    }
    delete(g.edges)
    g.edges = sorted
}

// --- scopes -------------------------------------------------------------------


// A fun or struct: its node, for each type it was checked as (a generic's
// instances), its body put in place.
@(private="file")
graph_scope_def :: proc(b: ^Graph_Builder, d: Graph_Decl, parent: Node_Id) {
    // (One scope, the checker's for this statement — a generic fun's
    // instance's own copy of a nested fun, say, which shares its span.)
    if ts, built := b.scope_of[d.id]; built && !d.generic {
        graph_scope_node(b, ts, d.name, d.span, parent, .Explicit)
        return
    }
    list, ok := b.by_span[d.span]
    if !ok {
        if d.generic { return }   // a generic nothing instantiates: syntax only
        graph_fatal(d.span, "'%s' reached the graph unchecked", d.name)
    }
    for t in list {
        ts, is_scope := t.(^Type_Scope)
        if !is_scope || ts.is_module { continue }
        graph_scope_node(b, ts, d.name, d.span, parent, .Synthetic if d.generic else .Explicit)
    }
}

// A fun or struct: its params and results, then its code — a fun's body, a
// struct's field initializers — in a scope of its own.
@(private="file")
graph_scope_node :: proc(b: ^Graph_Builder, ts: ^Type_Scope, name: string, span: Span, parent: Node_Id, written: Written) {
    // Built by the checker: put in place. (The graph is built from a clean
    // check: every body was.)
    si, built := b.body_segs[ts]
    if !built { graph_fatal(span, "the checker built no graph of '%s'", graph_scope_name(ts, name, written)) }
    graph_body_place(b, si, parent, graph_scope_name(ts, name, written))
}

// A fun's or struct's node. (One in a segment of its own is named where it
// is placed.)
@(private="file")
graph_scope_root :: proc(b: ^Graph_Builder, ts: ^Type_Scope, span: Span, parent: Node_Id, written: Written, name := "") -> Node_Id {
    kind: Node_Kind = .Fun if ts.kind == .Fun else .Struct
    n := graph_node(b, kind, written, parent, name, ts, span)
    b.g.scope_node[ts] = n
    return n
}

// A scope's name: as written, or an instance's, from its mangled one.
@(private="file")
graph_scope_name :: proc(ts: ^Type_Scope, name: string, written: Written) -> string {
    return name if written == .Explicit else ask_demangle(ts.name, ts.home_package)
}

// --- bodies the checker builds ------------------------------------------------

// A fun's body the checker builds as it checks it (design/graph_retrofit.md,
// phase 4): its scope's node and contents, in a segment of their own, put in
// place when the builder meets the scope. The checker finishes bodies out of
// order — a nested definition's before its parent's code, a generic's
// instance at its first call — and each is placed where it goes.
//
// Where the checker can't build something, the body fails: its segment is
// dropped, and the builder stops where it meets the scope, saying why
// (graph_scope_node).
Graph_Body :: struct {
    seg, outer: int,
    stmt:       i32,           // the enclosing build's statement, as it was
    ts:         ^Type_Scope,
    root:       Node_Id,
    contents:   Graph_Contents,
    outer_body: ^Graph_Body,
    // Each statement's entry, made the first time the checker meets it (it
    // meets one in each of its passes).
    stmts:      map[Syntax_Id]i32,
    // Types are settled when the graph is put together: a `:=` binding's width is the one it
    // adopts from a later use, a param's default's once its fun is checked.
    // Synthetic locals settle as behind a pointer; constants whose width a
    // binding settles are listed in g.settled; a widening is kept or dropped.
    slots:      [dynamic]Node_Id,
    consts:     [dynamic]Node_Id,
    widens:     [dynamic]Graph_Widen,
    checks:     [dynamic]Graph_Check,
    marks:      [dynamic]Graph_Arena,
    allocs:     [dynamic]Graph_Alloc,
    returns:    [dynamic]Node_Id,        // its returns: what the local every one returns is
    // A struct's: each field declaration's lowered assignment, and its field.
    fields:     map[Syntax_Id]Node_Id,
    field_inits: map[Syntax_Id]Span,   // (where its initializer is written)
    field_outs: map[Syntax_Id][]Node_Id,   // fields from one call's outputs: their destructure's declarations
    const_decl: Graph_Decl,              // a constant's: its statement
    failed:     string,
}

// A scope's arena mark and the resets at its exits, made where the builder
// makes them, kept when its declarations turn out to hold a value on the
// arena (graph_scope_open).
Graph_Arena :: struct {
    mark:   Node_Id,
    resets: [dynamic]Node_Id,
    block:  Node_Id,
}

// A local's space on the arena, made before its value: kept
// when its type turns out to route there.
Graph_Alloc :: struct {
    decl, var, alloc: Node_Id,
}

// A number widened to the type its use takes (graph_widen), decided when the
// graph is put together. It widens to `to` — settled, for a declaration's
// (as its node is); or to the param `param` of `sig`; or to a binary
// operation's working type.
Graph_Widen :: struct {
    id:        Node_Id,
    v:         Operand,
    to:        Type,
    settle_to: bool,
    sig:       ^Type_Scope,
    param:     int,
    work:      Graph_Work,
    binary:    bool,
    // A value at a param's type chosen after it is built (for
    // a dispatch's or an operator's argument): a view may be taken — its
    // place seen as a slice (slice; read left out), or a partial array's
    // header as one (the cast) — else it widens. t is its type; read and
    // slice are a place's.
    views:     bool,
    t:         Type,
    read:      Node_Id,
    slice:     Node_Id,
    pending:   bool,   // `to` is set once known (an if expression's type)
}

// Start building a fun's body as the checker checks it: `id` its statement's,
// `span` its; an intrinsic's has no code of its own.
graph_body_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, id: Syntax_Id, span: Span, intrinsic: bool, written: Written) -> ^Graph_Body {
    b.scope_of[id] = ts
    f := new(Graph_Body)
    f.ts, f.outer_body = ts, b.body
    b.body = f
    f.seg, f.outer = graph_segment_enter(b)
    f.stmt, b.stmt = b.stmt, STMT_ANCHOR
    f.root = graph_scope_root(b, ts, span, NO_NODE, written)
    b.segs[f.seg].root = f.root
    f.contents = graph_contents_begin(b, ts, span, intrinsic, f.root)
    return f
}

// What the checker couldn't build: the rest of the body is checked without
// building, and its segment dropped. A clean check's graph is never built
// then: the first such body is reported instead.
graph_body_fail :: proc(b: ^Graph_Builder, f: ^Graph_Body, reason: string) {
    if f.failed != "" { return }
    f.failed = reason
    if b.failure.reason == "" {
        b.failure = {f.ts.name if f.ts != nil && f.ts.name != "" else b.g.name[f.root], reason, b.g.origin[f.root]}
    }
}

// The body is checked: finish it, settle its types and keep it for the
// builder to put in place — or, if it failed, drop it.
graph_body_end :: proc(b: ^Graph_Builder, f: ^Graph_Body) {
    graph_contents_end(b, f.contents, finish = f.failed == "")
    ok := f.failed == ""   // (its end can find what it can't build: a scope's values on the arena)
    b.stmt = f.stmt
    graph_segment_leave(b, f.outer)
    b.body = f.outer_body
    delete(f.stmts)
    delete(f.fields)
    delete(f.field_inits)
    for _, ids in f.field_outs { delete(ids) }
    delete(f.field_outs)
    if ok {
        b.body_segs[f.ts] = f.seg
        append(&b.bodies, f)   // settled when the graph is put together
        return
    }
    graph_body_free(f)
}

@(private="file")
graph_body_free :: proc(f: ^Graph_Body) {
    delete(f.slots)
    delete(f.consts)
    delete(f.widens)
    delete(f.checks)

    for m in f.marks { delete(m.resets) }
    delete(f.marks)
    delete(f.allocs)
    delete(f.returns)
    free(f)
}

// A value at a param's type known only later: a place is
// read, cast (a header's view, a widening), and seen as a slice — whichever
// its param takes kept; a value, cast. Its index in the body's list, to name
// the param once it is known.
graph_build_as :: proc(b: ^Graph_Builder, v: Operand, place: bool, t: Type, read_span, span: Span, w: Graph_Widen) -> (Operand, int) {
    w := w
    w.views, w.t, w.read, w.slice = true, t, NO_NODE, NO_NODE
    val := v
    if place {
        val = graph_read(b, v, t, read_span)   // (at the expression, as a value is read)
        w.read = val.op
    }
    // A cast only where one can be taken — a number's widening, a partial
    // array's header — and a slice only of a fixed array's place.
    _, _, num := numeric_info(graph_settled(t))
    if !num && !graph_partial_of(t) || is_infer(t) && infer_cell_of(t) == nil { return val, -1 }
    w.id, w.v = graph_op(b, .Cast, .Implied, span, nil, "", val), val
    if _, from_array := distinct_base(t).(^Type_Fixed_Array); place && from_array { w.slice = graph_op(b, .Slice, .Implied, span, nil, "", v) }
    append(&b.body.widens, w)
    return {w.id, 0}, len(b.body.widens) - 1
}

// A number at the type its use takes, as graph_widen: an operation made
// here, kept or dropped when the graph is put together.
graph_build_widen :: proc(b: ^Graph_Builder, v: Operand, span: Span, w: Graph_Widen) -> Operand {
    if v.op == NO_NODE || v.out != 0 { return v }
    // What is no number, or a literal's own (no binding types it), never widens.
    from := b.g.type_[v.op]
    if _, _, num := numeric_info(graph_settled(from)); !num { return v }
    if is_infer(from) && infer_cell_of(from) == nil { return v }
    // Where no width is still open, decided now.
    if !w.binary && !w.pending && !graph_open_width(from) {
        to := w.to
        if w.sig != nil { to = w.sig.params[w.param].type_ if w.param < len(w.sig.params) else nil }
        if !graph_open_width(to) && !(w.sig != nil && graph_param_open(w.sig, w.param)) {
            if w.settle_to { to = graph_settled(to) }
            if !graph_widens(graph_settled(from), to) { return v }
            return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), v)
        }
    }
    f := b.body
    w := w
    w.id, w.v, w.read, w.slice = graph_op(b, .Cast, .Implied, span, nil, "", v), v, NO_NODE, NO_NODE
    append(&f.widens, w)
    return {w.id, 0}
}

// Whether a type's width is a `:=` binding's still open (it adopts a later
// use's).
@(private="file")
graph_open_width :: proc(t: Type) -> bool {
    #partial switch v in t {
    case Type_Infer_Int:   return v.cell != nil && is_infer(t)
    case Type_Infer_Float: return v.cell != nil && is_infer(t)
    case ^Type_Ptr:        return graph_open_width(v.elem)
    }
    return false
}

// Whether a callee's param may still change type: one with a default whose
// width its body settles (solidify_param_defaults) and hasn't yet.
@(private="file")
graph_param_open :: proc(sig: ^Type_Scope, param: int) -> bool {
    if param < 0 || param >= len(sig.params) { return false }
    p := sig.params[param]
    return field_has_default(p) && is_infer(p.type_)
}

// A block of code: opened before its statements are
// checked, closed after.
Graph_Block :: struct {
    n, outer: Node_Id,
    span:     Span,
}

graph_build_block_open :: proc(b: ^Graph_Builder, label: string, span: Span) -> Graph_Block {
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, span)
    return k
}

graph_build_block_close :: proc(b: ^Graph_Builder, k: Graph_Block) {
    graph_scope_close(b, k.span)
    b.code.block = k.outer
    graph_close(b, k.n)
}

// An `if`: its branch on the condition, then each block between
// its checks.
Graph_If :: struct {
    then_r, else_r, join: ^Run,
    block:                Graph_Block,
    has_else:             bool,
    span:                 Span,
}

graph_build_if :: proc(b: ^Graph_Builder, cond: Operand, span: Span, has_else: bool) -> Graph_If {
    fi := Graph_If{has_else = has_else, span = span}
    fi.then_r, fi.join = graph_run_new(b), graph_run_new(b)
    fi.else_r = graph_run_new(b) if fi.has_else else fi.join
    graph_branch(b, cond, fi.then_r, fi.else_r, .Explicit, span)
    b.code.run = fi.then_r
    fi.block = graph_build_block_open(b, "if", span)
    return fi
}

graph_build_else :: proc(b: ^Graph_Builder, fi: ^Graph_If, span: Span) {
    graph_build_block_close(b, fi.block)
    if graph_reachable(b) { graph_jump(b, fi.join, .Synthetic, fi.span) }
    if fi.has_else {
        b.code.run = fi.else_r
        fi.block = graph_build_block_open(b, "else", span)
    }
}

graph_build_if_end :: proc(b: ^Graph_Builder, fi: ^Graph_If) {
    if fi.has_else {
        graph_build_block_close(b, fi.block)
        if graph_reachable(b) { graph_jump(b, fi.join, .Synthetic, fi.span) }
    }
    b.code.run = fi.join
}

// A return, its values built: an implied `Ok` for each
// trailing err left out, the scopes left, the return.
graph_build_return :: proc(b: ^Graph_Builder, vals: []Operand, span: Span) {
    rts := graph_result_types(b)
    all := make([dynamic]Operand, 0, len(rts), context.temp_allocator)
    append(&all, ..vals)
    graph_implied_oks(b, &all, rts, span)
    graph_exit_scopes(b, 0, span)
    append(&b.body.returns, graph_op(b, .Return, .Explicit, span, nil, "", ..all[:]))
    graph_run_close(b)
}

// A struct's field declaration: its fields,
// typed as the struct's; each name's assignment (`lowered`, the checker's
// lowering of it; `inits`, the values as written) stores into its own and
// is this statement's.
// A struct's field declaration: each name a field; `lowered`, the checker's
// statements that write them — one per name (`inits`, where each one's
// initializer is written), or one destructure writing them all from one call
// (`a, b := f()`: each output to its field).
graph_build_fields :: proc(b: ^Graph_Builder, names: []string, toks: []Token_Id, span: Span, lowered: []Syntax_Id, inits: []Span, destructure: bool) {
    f := b.body
    ids := make([]Node_Id, len(names))
    for name, i in names {
        d := graph_decl(b, {kind = .Field, owner = f.ts}, b.code.block, name, nil, span, toks[i])
        ids[i] = d
        if i < len(lowered) {
            key := lowered[i]
            f.fields[key] = d
            f.stmts[key] = b.stmt
            if i < len(inits) { f.field_inits[key] = inits[i] }
        }
    }
    if len(names) > 1 && len(lowered) == 1 && destructure {
        f.field_outs[lowered[0]] = ids
        return
    }
    delete(ids)
}

// A field of the program's struct (the compiler's: nothing constructs it).
graph_build_program_field :: proc(b: ^Graph_Builder, name: string, tok: Token_Id, span: Span) {
    graph_decl(b, {kind = .Field, owner = b.body.ts}, b.code.block, name, nil, span, tok)
}

// The program's struct (main's entry sets up its
// storage, nothing constructs it): each field mara.core declares for it,
// typed as the struct's, a statement of its own; no code.


// A local's declaration (graph_decl), before its value: typed once it is
// checked (graph_build_typed).
graph_build_decl :: proc(b: ^Graph_Builder, name: string, tok: Token_Id, span: Span, bound := false) -> Node_Id {
    d := graph_decl(b, {kind = .Local}, b.code.block, name, nil, span, tok)
    // A big value lives on the arena: its space, taken before
    // its value — kept once its type says so. (A `let` binds memory it takes.)
    if b.arena && !bound {
        v := graph_var(b, name, d, nil, span)
        a := graph_op(b, .Arena_Alloc, .Synthetic, span, nil, "", v)
        append(&b.body.allocs, Graph_Alloc{decl = d, var = v.op, alloc = a})
    }
    return d
}

graph_build_typed :: proc(b: ^Graph_Builder, d: Node_Id, t: Type) {
    b.g.type_[d] = t
    // Its variable's operations made before that was known (where a value
    // was built into it), typed as it is.
    for i in int(d) + 1 ..< b.nodes {
        if b.g.kind[i] == .Op && b.g.op[i] == .Var && b.g.refers[i] == d && b.g.type_[i] == nil { b.g.type_[i] = t }
    }
}

// `x : T = void` and `x = void`: the value left
// uninitialized — `void` where it is written, `at`.
graph_build_void_decl :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span, at: Span) {
    val := graph_void(b, t, at)
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, b.g.name[decl], decl, t, span), val)
}

graph_build_void_assign :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, t: Type, span, at: Span) {
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, name, decl, t, span), graph_void(b, t, at))
}

// Where the build stands, to leave out what is built after it: a field
// access's base, built before the access is found to name no member (a
// variant, a constant, a module's function) — the builder never builds it.
Graph_Mark :: struct {
    nodes: int,
    run:   ^Run,
    ops:   int,
}

graph_build_mark :: proc(b: ^Graph_Builder) -> Graph_Mark {
    return {b.nodes, b.code.run, len(b.code.run.ops) if b.code.run != nil else 0}
}

graph_build_drop_since :: proc(b: ^Graph_Builder, m: Graph_Mark) {
    if b.nodes == m.nodes { return }
    r := b.code.run
    if r == nil || r != m.run && m.run != nil {
        graph_body_fail(b, b.body, "a field access's base crossed runs")
        return
    }
    for i in m.nodes ..< b.nodes { graph_drop(b, Node_Id(i), NO_VALUE) }
    if m.run == nil {
        b.code.run = nil   // (the run the base began: code after a jump)
        return
    }
    // The then-edges its first operation took wait for the next again.
    if m.ops == 0 && len(r.ops) > 0 {
        for &e, k in b.g.edges {
            if e.to == r.ops[0] {
                e.to = NO_NODE
                append(&r.waiting, i32(k))
            }
        }
    }
    resize(&r.ops, m.ops)
}

// An assert of its condition's value, its text as written; a comparison's
// sides as written, for its failure's message ("" for a side whose text
// states its value).
graph_assert :: proc(b: ^Graph_Builder, span: Span, text: string, cond: Operand, w: Written, sides: Maybe([2]string)) {
    a := graph_op(b, .Assert, w, span, nil, text, cond)
    if s, compared := sides.?; compared { b.g.assert_sides[a] = s }
}

// `a and b`, `a or b`: the result through a synthetic
// local, the right side in a run of its own — begun before the left side,
// branched on after it, joined after the right.
Graph_And :: struct {
    slot:      Node_Id,
    word:      string,
    rhs, join: ^Run,
    and:       bool,
    w:         Written,
    span:      Span,
}

graph_build_and :: proc(b: ^Graph_Builder, is_and: bool, w: Written, span: Span) -> Graph_And {
    word := "and" if is_and else "or"
    return {slot = graph_slot(b, word, Type_Bool{}, span), word = word, and = is_and, w = w, span = span}
}

graph_build_and_left :: proc(b: ^Graph_Builder, sa: ^Graph_And, l: Operand) {
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), l)
    sa.rhs, sa.join = graph_run_new(b), graph_run_new(b)
    if sa.and {
        graph_branch(b, l, sa.rhs, sa.join, sa.w, sa.span)
    } else {
        graph_branch(b, l, sa.join, sa.rhs, sa.w, sa.span)
    }
    b.code.run = sa.rhs
}

graph_build_and_end :: proc(b: ^Graph_Builder, sa: ^Graph_And, r: Operand) -> Operand {
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), r)
    graph_jump(b, sa.join, .Synthetic, sa.span)
    b.code.run = sa.join
    return graph_read(b, graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), Type_Bool{}, sa.span)
}

// A bare declaration's value: its type's construction, or zero;
// a sized slice's zero takes its capacity.
graph_build_bare :: proc(b: ^Graph_Builder, d: Node_Id, t: Type, cap: Maybe(Operand), args: []Operand, span: Span) {
    if c, has := cap.?; has {
        n := graph_build_widen(b, c, span, {to = slice_header_width_type})
        graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, b.g.name[d], d, t, span), n)
        return
    }
    graph_construct_bare(b, graph_var(b, b.g.name[d], d, t, span), t, args, span)
}

// A new partial array's zero, made before the value it may be a prefix of:
// kept, typed, when it is.
graph_build_prefix :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, span: Span) -> [2]Node_Id {
    v := graph_var(b, name, decl, nil, span)
    return {v.op, graph_op(b, .Zero, .Synthetic, span, nil, "", v)}
}

graph_build_prefix_end :: proc(b: ^Graph_Builder, p: [2]Node_Id, keep: bool, t: Type) {
    for id in p {
        if keep { b.g.type_[id] = t } else { graph_drop(b, id, NO_VALUE) }
    }
}

// A call through a function value: the arguments, then the
// value, read, then the call.
graph_build_indirect :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, fn_value: Type, t: Type, args: []Operand, w: Written, span: Span) -> Operand {
    ops := make([dynamic]Operand, 0, len(args) + 1, context.temp_allocator)
    append(&ops, graph_read(b, graph_var(b, name, decl, fn_value, span), fn_value, span))
    append(&ops, ..args)
    return graph_op_value(b, .Call, w, span, t, name, ..ops[:])
}

// Bytes indexed, seen as another type once the use of them says which: the
// element's place, built, is that view — the same operands, the bytes at the
// index.
graph_build_view :: proc(b: ^Graph_Builder, place: Operand, t: Type, big: bool, span: Span) {
    id := place.op
    b.g.op[id], b.g.type_[id], b.g.origin[id] = .View, t, span
    b.g.name[id] = "#big_endian" if big else ""
    // (Its base's implied dereference and its offset's widening are the
    // view's, where it is.)
    for o, k in graph_built_operands(b, id) {
        if o.op == NO_NODE || b.g.written[o.op] != .Implied { continue }
        if k == 0 && b.g.op[o.op] == .Deref || k == 1 && b.g.op[o.op] == .Cast { b.g.origin[o.op] = span }
    }
}

// Bytes read by a byte read: of the element built, its
// buffer's place (its dereference at the read) and its index as it was
// before it was widened; the element's operation left out.
graph_build_byte_operands :: proc(b: ^Graph_Builder, place: Operand, span: Span) -> (Operand, Operand) {
    id := place.op
    ops := graph_built_operands(b, id)
    buf, off := ops[0], ops[1]
    if off.op != NO_NODE && b.g.op[off.op] == .Cast && b.g.written[off.op] == .Implied {
        raw := b.g.operands[b.g.operand_first[off.op]]
        graph_drop(b, off.op, raw)
        off = raw
    }
    graph_drop(b, id, NO_VALUE)
    if buf.op != NO_NODE && b.g.op[buf.op] == .Deref && b.g.written[buf.op] == .Implied { b.g.origin[buf.op] = span }
    return buf, off
}

// A span of bytes read: of the slice built, its bytes' place
// (its dereference at the read) and its bounds; the slice left out.
graph_build_span_operands :: proc(b: ^Graph_Builder, slice: Operand, span: Span) -> (buf, lo, hi: Operand) {
    id := slice.op
    ops := graph_built_operands(b, id)
    buf, lo, hi = ops[0], ops[1], ops[2]
    graph_drop(b, id, NO_VALUE)
    if buf.op != NO_NODE && b.g.op[buf.op] == .Deref && b.g.written[buf.op] == .Implied { b.g.origin[buf.op] = span }
    return
}

// A span of bytes seen as a `t` at its start: of the slice
// built, its bytes' place and its start, at the header's width (0 when it
// has none); the view.
graph_build_span_view :: proc(b: ^Graph_Builder, slice: Operand, t: Type, big: bool, span: Span) -> Operand {
    buf, lo, _ := graph_build_span_operands(b, slice, span)
    at: Operand
    if lo != NO_VALUE {
        at = graph_build_widen(b, lo, span, {to = slice_header_width_type})
    } else {
        at = graph_const(b, .Synthetic, span, slice_header_width_type, "0", Const_Value{})
    }
    return graph_op_value(b, .View, .Explicit, span, t, "#big_endian" if big else "", buf, at)
}

// A temporary what comes next may need, made before it — zeroed first where
// it fills a partial array: kept if it is used, else left out
// (graph_build_unhold). Whether it is needed is known once what it holds is
// built, and it goes before that.
Graph_Held :: struct {
    slot: Node_Id,
    to:   int,       // its nodes: slot ..< to (none made: 0)
}

graph_build_hold :: proc(b: ^Graph_Builder, t: Type, span: Span, zero := false) -> Graph_Held {
    h := Graph_Held{slot = graph_slot(b, "temp", t, span)}
    if zero { graph_build_zero_var(b, h.slot, t, span) }
    h.to = b.nodes
    return h
}

graph_build_unhold :: proc(b: ^Graph_Builder, h: Graph_Held) {
    for i in int(h.slot) ..< h.to { graph_drop(b, Node_Id(i), NO_VALUE) }
}

// `bytes[lo:hi] = v`: its target is a view of the bytes at lo —
// their place, lo at the header's width, the view — where v is no array;
// else the slice (lo, hi, their place, the slice). Which is known once v is
// checked: both are built before it, in one line — a view's place, lo, hi,
// a slice's place, the slice, the view — and one's parts left out.
Graph_Span_Target :: struct {
    view_place: [2]int,   // (node ranges)
    hi:         [2]int,
    place:      [2]int,
    lo:         Operand,
    widened:    bool,     // lo, by a cast of its own
    run:        ^Run,
    branched:   bool,     // hi did (a `?`: what follows it is in its runs)
    vplace:     Operand,
    slice, zero, view: Node_Id,
    bytes:      Operand,  // the bytes' place, the checker's (built from node `from` on)
    bytes_t:    Type,
    bytes_self: bool,
}

// The view's place, first: the bytes' place as the checker built it (from
// node `from` on).
graph_build_span_target :: proc(b: ^Graph_Builder, bytes: Operand, t: Type, is_self: bool, from: int, span: Span) -> Graph_Span_Target {
    st := Graph_Span_Target{lo = NO_VALUE, zero = NO_NODE, bytes = bytes, bytes_t = t, bytes_self = is_self}
    st.view_place.x = from
    st.vplace = graph_base_of(b, bytes, t, span, is_self)
    st.view_place.y = b.nodes
    return st
}

// lo built: at the header's width (a slice's, at it); hi next.
graph_build_span_target_hi :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, lo: Operand, slice_span: Span) {
    if lo != NO_VALUE {
        st.lo = graph_build_widen(b, lo, slice_span, {to = slice_header_width_type})
        st.widened = st.lo.op != lo.op
    }
    st.run = b.code.run
    st.hi.x = b.nodes
}

// hi built: the slice's place, the slice, then the view (of no type yet).
graph_build_span_target_ops :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, hi: Operand, t: Type, big: bool, slice_span, span: Span) {
    st.hi.y = b.nodes
    st.branched = b.code.run != st.run
    st.place.x = b.nodes
    p := graph_base_of(b, graph_place_again(b, st.bytes, slice_span), st.bytes_t, slice_span, st.bytes_self)
    st.place.y = b.nodes
    st.slice = graph_op(b, .Slice, .Explicit, slice_span, t, "", p, st.lo, hi)
    at := st.lo
    if at == NO_VALUE {
        at = graph_const(b, .Synthetic, span, slice_header_width_type, "0", Const_Value{})
        st.zero = at.op
    }
    st.view = graph_op(b, .View, .Explicit, span, nil, "#big_endian" if big else "", st.vplace, at)
}

// v checked: the target — the view, as `view`; the slice, when nil. False
// when a view's hi branched.
graph_build_span_target_end :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, view: Type, span: Span) -> (Operand, bool) {
    drop :: proc(b: ^Graph_Builder, r: [2]int) {
        for i in r.x ..< r.y { graph_drop(b, Node_Id(i), NO_VALUE) }
    }
    if view == nil {
        drop(b, st.view_place)
        if st.zero != NO_NODE { graph_drop(b, st.zero, NO_VALUE) }
        graph_drop(b, st.view, NO_VALUE)
        return {st.slice, 0}, true
    }
    drop(b, st.hi)
    drop(b, st.place)
    graph_drop(b, st.slice, NO_VALUE)
    b.g.type_[st.view] = view
    if st.widened { b.g.origin[st.lo.op] = span }   // (lo's widening, at the view)
    return {st.view, 0}, !st.branched
}

// Bytes taken as an array: their view, copied into a
// temporary, read.
graph_build_view_temp :: proc(b: ^Graph_Builder, view: Operand, t: Type, span: Span) -> Operand {
    slot := graph_slot(b, "temp", t, span)
    graph_op(b, .Write, .Implied, span, nil, "", graph_var(b, "temp", slot, t, span), graph_read(b, view, t, span))
    return graph_read(b, graph_var(b, "temp", slot, t, span), t, span)
}

// A take: the count, then the storage, the checker's — `&x`
// as its address (of type t), else a place — then the carve. It carves from
// the storage's header: `&s` is s's, a `^[]byte` what it points at; or,
// positional (`&bytes[i]`), the view of the bytes there as what's taken.
graph_build_carve :: proc(b: ^Graph_Builder, span: Span, keyword: string, taken: Type, storage: Operand, t: Type, addressed, is_self: bool, count: Operand, w: Written) -> Operand {
    from := storage
    if addressed {
        if storage.op == NO_NODE || b.g.op[storage.op] != .Address { graph_fatal(span, "a take's `&` built as no address") }
        from = graph_built_operands(b, storage.op)[0]
        graph_drop(b, storage.op, NO_VALUE)
        if b.g.op[from.op] == .Index && is_byte_buffer(b.g.type_[graph_built_operands(b, from.op)[0].op]) {
            graph_build_view(b, from, taken, false, span)
        }
    } else {
        from = graph_base_of(b, storage, t, span, is_self)
    }
    return graph_op_value(b, .Carve, w, span, taken, keyword, from, count)
}

// A plain place the checker built where it was checked, walked where it's
// needed (a slice's, after its bounds): its operations copied there, its
// first building left out.
graph_build_base_place :: proc(b: ^Graph_Builder, p: Operand, t: Type, is_self: bool, span: Span) -> Operand {
    again := graph_place_again(b, p, span)
    graph_drop_place(b, p)
    return graph_base_of(b, again, t, span, is_self)
}

// A destructure of a call's outputs: the names it
// declares made before the call (typed once checked), then each output
// written to its name, or to its target's place, in turn. Its names as
// written; `stores`, which are lvalues, stored to rather than declared.
Graph_Destructure :: struct {
    on:     bool,
    names:  []string,
    stores: []bool,
    span:   Span,
    decls:  []Node_Id,   // each name's declaration ...
    writes: bool,        // ... the variables' it writes (`a, b = f()`), not ones it declares
    call:   Operand,
    place:  Operand,   // the target of the output being written
}

graph_build_destructure :: proc(b: ^Graph_Builder, id: Syntax_Id, span: Span, names: []string, toks: []Token_Id, stores: []bool, is_decl: bool) -> Graph_Destructure {
    mr := Graph_Destructure{on = true, names = names, stores = stores, span = span, writes = !is_decl}
    // (A struct's fields from one call: declared as its fields.)
    if ids, of_fields := b.body.field_outs[id]; of_fields {
        mr.decls = ids
        return mr
    }
    // (Each name's declaration: made here, or — written — the variable's.)
    mr.decls = make([]Node_Id, len(names), context.temp_allocator)
    for name, i in names {
        mr.decls[i] = NO_NODE
        if name == "" || name == "_" || stores[i] { continue }
        mr.decls[i] = graph_decl(b, {kind = .Local}, b.code.block, name, nil, span, toks[i]) if is_decl else graph_local(b, toks[i])
    }
    return mr
}

// (`t`: the name's type, the checker's.)
graph_build_destructure_write :: proc(b: ^Graph_Builder, mr: ^Graph_Destructure, i: int, t: Type) {
    name, target := mr.names[i], mr.stores[i]
    if name == "_" || name == "" && !target { return }
    val := mr.call
    if i > 0 { val = {graph_outputs_op(b, mr.call, mr.span), i32(i)} }
    dest := mr.place
    if !target {
        if mr.decls[i] != NO_NODE && !mr.writes { graph_build_typed(b, mr.decls[i], t) }
        dest = graph_var(b, name, mr.decls[i], t, mr.span)
    }
    graph_op(b, .Write, .Explicit, mr.span, nil, "", dest, val)
}

// A match, its subject checked: the switch on its tag — each
// arm's tag a constant filled in when the arm is (graph_build_arm) — then,
// per arm, its block; the code after it joins.
Graph_Match :: struct {
    slot:     Node_Id,
    subject:  Operand,   // else its place, the checker's: walked again where needed
    t:        Type,      // its type
    is_self:  bool,
    is_union: bool,
    ops:      [dynamic]Operand,
    tags:     []Node_Id,
    arms:     []^Run,
    join:     ^Run,
    span:     Span,
}

graph_build_match_begin :: proc(b: ^Graph_Builder, span: Span, arms: int, slot: Node_Id, subject: Operand, t: Type, is_self: bool) -> ^Graph_Match {
    gm := new(Graph_Match, context.temp_allocator)
    gm.slot, gm.span = slot, span
    gm.subject, gm.t, gm.is_self = subject, t, is_self
    _, gm.is_union = distinct_base(t).(^Type_Union)
    gm.ops = make([dynamic]Operand, 0, arms + 1, context.temp_allocator)
    if gm.is_union {
        append(&gm.ops, graph_build_subject(b, span, gm, first = true))
    } else {
        append(&gm.ops, graph_read(b, graph_build_subject(b, span, gm, first = true), t, span))
    }
    gm.tags = make([]Node_Id, arms, context.temp_allocator)
    gm.arms = make([]^Run, arms, context.temp_allocator)
    for i in 0 ..< arms {
        gm.arms[i] = graph_run_new(b)
        gm.tags[i] = NO_NODE
    }
    return gm
}

// An arm's tag: a union's variant's, an enum's — a constant filled in when
// the arm is resolved (graph_build_arm).
graph_build_match_tag :: proc(b: ^Graph_Builder, gm: ^Graph_Match, span: Span, i: int) {
    t := graph_tag_type(gm.t) if gm.is_union else gm.t
    tag := graph_const(b, .Implied, span, t, "", Const_Value{})
    gm.tags[i] = tag.op
    append(&gm.ops, tag)
}

// A value's arm: its value.
graph_build_match_value :: proc(b: ^Graph_Builder, gm: ^Graph_Match, val: Operand) {
    append(&gm.ops, val)
}

graph_build_match_switch :: proc(b: ^Graph_Builder, gm: ^Graph_Match, span: Span) {
    graph_switch(b, gm.ops[:], gm.arms, span)
    gm.join = graph_run_new(b)
}

@(private="file")
graph_build_subject :: proc(b: ^Graph_Builder, span: Span, gm: ^Graph_Match, first := false) -> Operand {
    if gm.slot != NO_NODE { return graph_var(b, "subject", gm.slot, b.g.type_[gm.slot], span) }
    p := gm.subject if first else graph_place_again(b, gm.subject, span)
    return graph_base_of(b, p, gm.t, span, gm.is_self)
}


// An arm as the checker resolved it: the variant it matches and its tag,
// and — a union's arm that binds its payload — the name and the variant's
// struct; whether it is the else arm, a union's arm.
Graph_Arm :: struct {
    variant:  string,
    tag:      int,
    bound:    string,
    bound_tok: Token_Id,
    payload:  Type,
    is_else:  bool,
    is_union: bool,
}

// An arm, resolved: its tag, its run and block, and — a union's arm that
// binds its payload — the binding, the payload's place.
graph_build_arm :: proc(b: ^Graph_Builder, gm: ^Graph_Match, ga: Graph_Arm, i: int) -> Graph_Block {
    if id := gm.tags[i]; id != NO_NODE {
        b.g.name[id] = ga.variant
        b.g.consts[id] = Const_Value{int = i128(ga.tag)}
    }
    span := gm.span
    b.code.run = gm.arms[i]
    label := "else" if ga.is_else else fmt.aprintf("arm %s", ga.variant)
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, span)
    if ga.is_union && ga.bound != "" {
        if ga.payload == nil { graph_fatal(span, "match arm '%s' has no resolved variant", ga.variant) }
        bound := graph_node(b, .Local, .Explicit, k.n, ga.bound, ga.payload, span)
        // The binding is the payload's place, not a copy.
        payload := graph_op(b, .Variant, .Explicit, span, ga.payload, ga.bound, graph_build_subject(b, span, gm))
        b.g.refers[payload] = bound
        graph_declare(b, bound, ga.bound_tok)   // after the subject's place: it may reuse the name
    }
    return k
}

graph_build_arm_end :: proc(b: ^Graph_Builder, gm: ^Graph_Match, k: Graph_Block) {
    graph_build_block_close(b, k)
    if graph_reachable(b) { graph_jump(b, gm.join, .Synthetic, k.span) }
}

graph_build_match_end :: proc(b: ^Graph_Builder, gm: ^Graph_Match) {
    b.code.run = gm.join
}

// A defer's block: its code of its own — a run entered from
// the block, ending in a return — built as its statements are checked, then
// registered with the scope it is in (Run_Defer runs it at every exit).
Graph_Defer :: struct {
    d:     Node_Id,
    saved: Code,
    span:  Span,
}

graph_build_defer :: proc(b: ^Graph_Builder, span: Span) -> Graph_Defer {
    gd := Graph_Defer{d = graph_node(b, .Block, .Explicit, b.code.block, "defer", nil, span), span = span}
    gd.saved = graph_code_begin(b, gd.d)
    graph_scope_open(b, gd.d, span)
    return gd
}

graph_build_defer_end :: proc(b: ^Graph_Builder, gd: Graph_Defer) {
    graph_code_finish(b, gd.span)
    graph_code_end(b, gd.saved)
    append(&b.code.scopes[len(b.code.scopes) - 1].defers, gd.d)
    graph_close(b, gd.d)
}

// An `if` expression's runs: the branch on its condition,
// each branch's run, and the join.
Graph_If_Expr :: struct {
    yes, no, join: ^Run,
    span:          Span,
}

graph_build_if_expr :: proc(b: ^Graph_Builder, cond: Operand, w: Written, span: Span) -> Graph_If_Expr {
    gi := Graph_If_Expr{yes = graph_run_new(b), no = graph_run_new(b), join = graph_run_new(b), span = span}
    graph_branch(b, cond, gi.yes, gi.no, w, span)
    b.code.run = gi.yes
    return gi
}

graph_build_if_expr_else :: proc(b: ^Graph_Builder, gi: ^Graph_If_Expr) {
    graph_jump(b, gi.join, .Synthetic, gi.span)
    b.code.run = gi.no
}

graph_build_if_expr_end :: proc(b: ^Graph_Builder, gi: ^Graph_If_Expr) {
    graph_jump(b, gi.join, .Synthetic, gi.span)
    b.code.run = gi.join
}

// The kind of the statement being built, once its check says (a
// destructure found a broadcast is its copies').
graph_build_stmt_kind :: proc(b: ^Graph_Builder, kind: Stmt_Kind) {
    b.g.stmts[b.stmt].kind = kind
}

// A broadcast literal built into d: its value at the element
// type, then the fill.
graph_build_fill :: proc(b: ^Graph_Builder, span: Span, t: Type, d: Dest, val: Operand) {
    x := graph_build_widen(b, val, span, {to = graph_elem_type(t)})
    graph_op(b, .Fill, .Explicit, span, t, "", graph_dest_place(b, d, span), x)
}

// `void` written: the uninitialized value (graph_void).
graph_build_void :: proc(b: ^Graph_Builder, t: Type, span: Span) -> Operand {
    return graph_void(b, t, span)
}

// An override block written into a variable's struct: each field's value
// into its field.
graph_build_override :: proc(b: ^Graph_Builder, d: Dest, sd: ^Scope_Body) -> ^Graph_Literal {
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent, gl.sd = d, d, sd
    return gl
}

// The call the slots of a default share (Code.tuples): made at the first.
graph_build_tuple_set :: proc(b: ^Graph_Builder, key: Syntax_Id, op: Node_Id) {
    b.code.tuples[key] = op
}

graph_build_tuple_get :: proc(b: ^Graph_Builder, key: Syntax_Id) -> (Node_Id, bool) {
    op, ok := b.code.tuples[key]
    return op, ok
}

// A value written to a place already built.
graph_build_write_at :: proc(b: ^Graph_Builder, place, v: Operand, span: Span) {
    graph_op(b, .Write, .Explicit, span, nil, "", place, v)
}

// A loop as written, as the builder needs it: its counter's name (a range's),
// its element's and index's ("" for none), and which parts it has.
Graph_Loop :: struct {
    span:        Span,
    var_name:    string,
    elem_name:   string,
    index_name:  string,
    var_tok, elem_tok, index_tok: Token_Id,   // (the tokens that declare them)
    is_range:    bool,
    has_cond:    bool,   // `for cond {}`, a C-style loop
    has_step:    bool,   // a C-style loop's
    end_literal: bool,   // a range whose end is a literal
}

// A loop, built around its checks: its block, the loop's
// variables, then its runs — the check, the body, the step — and the code
// after it.
Graph_For :: struct {
    using loop:              Graph_Loop,
    f, outer:                Node_Id,
    counter:                 Node_Id,
    end_slot, coll_slot:     Node_Id,
    elem:                    Node_Id,
    lo, hi:                  Operand,
    high:                    Operand,   // a range's end as the checker built it (a literal's: walked again)
    coll:                    Operand,   // a plain place collection's place, the checker's
    coll_t:                  Type,
    coll_self:               bool,
    elem_t:                  Type,      // a collection loop's element's
    check, body, post, done: ^Run,
    body_block:              Node_Id,
    has_post:                bool,
    stepped:                 bool,  // past its body: in its step (graph_build_for_step)
}

graph_build_for :: proc(b: ^Graph_Builder, loop: Graph_Loop) -> Graph_For {
    fl := Graph_For{loop = loop, counter = NO_NODE, end_slot = NO_NODE, coll_slot = NO_NODE, elem = NO_NODE}
    fl.f = graph_node(b, .Block, .Explicit, b.code.block, "for", nil, fl.span)
    fl.outer = b.code.block
    b.code.block = fl.f
    return fl
}

// A range's counter, before its bounds (typed once they are checked).
graph_build_range_counter :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    fl.counter = graph_node(b, .Local, .Explicit, fl.f, fl.var_name, nil, fl.span)
    graph_declare(b, fl.counter, fl.var_tok)
}

// A range's bound at the counter's type: cast when its
// own differs — decided when the graph is put together.
graph_build_range_bound :: proc(b: ^Graph_Builder, v: Operand, t: Type, span: Span) -> Operand {
    id := graph_op(b, .Cast, .Synthetic, span, nil, "", v)
    append(&b.body.checks, Graph_Check{kind = .Bound, ids = {id, NO_NODE}, v = v, t = t})
    return {id, 0}
}

// The range's bounds checked: the counter typed, the end held (a literal's
// is itself), the check that the range counts up — kept when a bound is no
// constant — and the counter's first value; then the check run.
graph_build_range :: proc(b: ^Graph_Builder, fl: ^Graph_For, bounds: [2]int, ct: Type) {
    b.g.type_[fl.counter] = ct
    for k in bounds { if k >= 0 { b.body.checks[k].ct = ct } }
    if !fl.end_literal {
        fl.end_slot = graph_slot(b, "end", ct, fl.span)
        graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, "end", fl.end_slot, ct, fl.span), fl.hi)
    }
    up := graph_op_value(b, .Compare, .Synthetic, fl.span, Type_Bool{}, "<=", fl.lo, fl.hi)
    assert := graph_op(b, .Assert, .Synthetic, fl.span, nil, "range", up)
    append(&b.body.checks, Graph_Check{kind = .Ascends, ids = {up.op, assert}, lo = fl.lo, hi = fl.hi})
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, fl.var_name, fl.counter, ct, fl.span), fl.lo)
    graph_build_for_runs(b, fl)
}

// A collection loop, the collection checked (a plain place, `place` of type
// `t`: walked where the loop needs it): a slice's elements as they are when
// the loop begins, the element and the index; then the check run.
graph_build_for_collection :: proc(b: ^Graph_Builder, fl: ^Graph_For, place: Operand, t: Type, is_self: bool, elem_t: Type) {
    fl.coll, fl.coll_t, fl.coll_self, fl.elem_t = place, t, is_self, elem_t
    if fl.coll_slot == NO_NODE {
        if view := graph_loop_view_of(t); view != nil {
            fl.coll_slot = graph_slot(b, "items", view, fl.span)
            val := graph_op_value(b, .Slice, .Implied, fl.span, view, "", graph_base_of(b, place, t, fl.span, is_self))
            graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, "items", fl.coll_slot, view, fl.span), val)
        } else {
            graph_drop_place(b, place)   // (walked in each run: graph_coll_place)
        }
    }
    if fl.elem_name != "" {
        fl.elem = graph_node(b, .Local, .Explicit, fl.f, fl.elem_name, elem_t, fl.span)
        graph_declare(b, fl.elem, fl.elem_tok)
    }
    index_t := Type(slice_header_width_type)
    if fl.index_name != "" {
        fl.counter = graph_node(b, .Local, .Explicit, fl.f, fl.index_name, index_t, fl.span)
        graph_declare(b, fl.counter, fl.index_tok)
    } else {
        fl.counter = graph_slot(b, "index", index_t, fl.span)
    }
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, b.g.name[fl.counter], fl.counter, index_t, fl.span),
             graph_const(b, .Synthetic, fl.span, index_t, "0", Const_Value{}))
    graph_build_for_runs(b, fl)
}

// A collection that is no plain place: held in a local made
// before it — its place's view, when it has a header, else itself — which
// the loop walks. Its local first (typed once it is checked).
graph_build_items :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    fl.coll_slot = graph_slot(b, "items", nil, fl.span)
}

// Checked, `t` its type: its view, or it, written to the local. A value is
// held in the temporary made before it (`held`), else that is left out.
graph_build_items_view :: proc(b: ^Graph_Builder, fl: ^Graph_For, held: Graph_Held, place: Operand, is_place: bool, t, view: Type, is_self: bool) {
    span := fl.span
    p := place
    if !is_place {
        graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", held.slot, t, span), place)
        p = graph_var(b, "temp", held.slot, t, span)
    } else {
        graph_build_unhold(b, held)
    }
    if pt, ok := distinct_base(t).(^Type_Ptr); ok && !is_self {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)   // (through a pointer, what it points at)
    }
    val := graph_op_value(b, .Slice, .Implied, span, view, "", p)
    graph_build_typed(b, fl.coll_slot, view)
    graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, "items", fl.coll_slot, view, span), val)
}

// The loop's runs, into the check: a counter against its bound; else the
// condition, checked next (graph_build_for_cond); else none (`for {}`).
graph_build_for_runs :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    fl.check, fl.body, fl.post, fl.done = graph_run_new(b), graph_run_new(b), graph_run_new(b), graph_run_new(b)
    fl.has_post = fl.has_step || fl.counter != NO_NODE
    graph_jump(b, fl.check, .Synthetic, fl.span)
    b.code.run = fl.check
    span := fl.span
    if fl.counter != NO_NODE {
        ct := b.g.type_[fl.counter]
        cur := graph_read(b, graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), ct, span)
        bound: Operand
        if fl.is_range {
            if fl.end_slot != NO_NODE {
                bound = graph_read(b, graph_var(b, "end", fl.end_slot, b.g.type_[fl.end_slot], span), b.g.type_[fl.end_slot], span)
            } else {
                bound = graph_place_again(b, fl.high, span)   // (a literal)
            }
        } else {
            bound = graph_len(b, graph_coll_place(b, fl, span), fl.coll_t, span)
        }
        cmp := graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, "<", cur, bound)
        graph_branch(b, cmp, fl.body, fl.done, .Synthetic, span)
        graph_build_for_body(b, fl)
    } else if !fl.has_cond {
        graph_jump(b, fl.body, .Synthetic, span)   // `for {}`: until a break
        graph_build_for_body(b, fl)
    }
}

// A condition loop's condition, built in its check run.
graph_build_for_cond :: proc(b: ^Graph_Builder, fl: ^Graph_For, cond: Operand) {
    graph_branch(b, cond, fl.body, fl.done, .Explicit, fl.span)
    graph_build_for_body(b, fl)
}

// The body's run and block, its statements checked next: an element's
// loop reads the element first.
@(private="file")
graph_build_for_body :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    span := fl.span
    b.code.run = fl.body
    append(&b.code.loops, Loop{cont = fl.post if fl.has_post else fl.check, done = fl.done, scope = len(b.code.scopes)})
    fl.body_block = graph_node(b, .Block, .Explicit, fl.f, "body", nil, span)
    b.code.block = fl.body_block
    graph_scope_open(b, fl.body_block, span)
    if fl.elem != NO_NODE {
        ct := b.g.type_[fl.counter]
        at := graph_read(b, graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), ct, span)
        at = graph_widen(b, at, slice_header_width_type, span)
        et := fl.elem_t
        slot := graph_op_value(b, .Index, .Synthetic, span, et, "", graph_coll_place(b, fl, span), at)
        graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, fl.elem_name, fl.elem, et, span),
                 graph_read(b, slot, et, span))
    }
}

// After the body: its scope's end, then the step's run — a C-style loop's
// step is built next, into it (graph_build_for_end runs this first when the
// loop has none).
graph_build_for_step :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    span := fl.span
    graph_scope_close(b, span)
    graph_close(b, fl.body_block)
    b.code.block = fl.f
    pop(&b.code.loops)
    cont := fl.post if fl.has_post else fl.check
    if graph_reachable(b) { graph_jump(b, cont, .Synthetic, span) }
    if fl.has_post { b.code.run = fl.post }
    fl.stepped = true
}

// The step's run's end, and the code after the loop.
graph_build_for_end :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    if !fl.stepped { graph_build_for_step(b, fl) }
    span := fl.span
    if fl.has_post {
        if fl.counter != NO_NODE {
            ct := b.g.type_[fl.counter]
            cur := graph_read(b, graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), ct, span)
            next := graph_op_value(b, .Arith, .Synthetic, span, ct, "+%", cur, graph_const(b, .Synthetic, span, ct, "1", Const_Value{int = 1}))
            graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), next)
        }
        graph_jump(b, fl.check, .Synthetic, span)
    }
    graph_close(b, fl.f)
    b.code.run = fl.done
    b.code.block = fl.outer
}

// `break`, `continue` (graph_loop_exit).
graph_build_loop_exit :: proc(b: ^Graph_Builder, span: Span, is_break: bool) {
    graph_loop_exit(b, span, is_break)
}

// A range's bound cast or its check that it counts up, decided when the
// graph is put together.
Graph_Check :: struct {
    kind:   enum u8 { Bound, Ascends },
    ids:    [2]Node_Id,   // the cast; the compare and the assert
    v:      Operand,      // the bound's value
    t, ct:  Type,         // its type, the counter's
    lo, hi: Operand,      // the bounds, as the check reads them
}

// A struct literal built into d, before its fields are
// checked: its construction — zero for `Foo{0}`, else its constructor on
// its params' defaults (a union's variant: its tag, then the field defaults
// the literal doesn't give) — and where its fields are. Nil when t is no
// aggregate the literal builds.
Graph_Literal :: struct {
    d, parent: Dest,
    sd:        ^Scope_Body,
    skip:      int,
    variant:   ^Type_Scope,   // a variant's struct: its field defaults (the checker's, into parent)
}

// A literal's construction at d: a struct's constructor run on `args` (its
// params' defaults, the checker's); a union's variant zeroed and tagged; an
// array zeroed.
graph_build_literal :: proc(b: ^Graph_Builder, span: Span, name: string, zero_init: bool, t: Type, d: Dest, args: []Operand = nil) -> ^Graph_Literal {
    ts, is_scope := t.(^Type_Scope)
    if is_scope && ts.kind == .Struct && !ts.is_module && zero_init {
        graph_op(b, .Zero, .Explicit, span, t, "{0}", graph_dest_place(b, d, span))
    } else if is_scope && ts.kind == .Struct && !ts.is_module {
        if len(args) != len(ts.params) { graph_fatal(span, "'%s' built without its arguments", ts.name) }
        ops := make([dynamic]Operand, 0, 1 + len(args), context.temp_allocator)
        append(&ops, graph_dest_place(b, d, span))
        append(&ops, ..args)
        op := graph_call_op(b, .Construct, .Explicit, span, ts, t, ..ops[:])
        b.g.name[op] = strings.concatenate({b.g.name[op], "{}"})   // as written: braces, no call
    } else if graph_aggregate(t) {
        _, is_union := distinct_base(t).(^Type_Union)
        graph_op(b, .Construct if is_union else .Zero, .Explicit, span, t, name, graph_dest_place(b, d, span))
    } else {
        return nil
    }
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent = d, d
    gl.sd = as_scope_body(distinct_base(t))
    if is_scope && ts.is_union_variant { gl.variant = ts }
    // A union's variant: its fields are the variant struct's, past the tag.
    if st := graph_variant_struct(b, t, name); st != nil {
        gl.sd = as_scope_body(st)
        gl.parent = Dest{kind = .Variant, name = name, type_ = st, parent = &gl.d}
        gl.variant = st
        for f in gl.sd.fields { if strings.has_prefix(f.name, "__") { gl.skip += 1 } }
    }
    return gl
}

// Where an array literal's element goes (array values).
graph_build_literal_elem :: proc(gl: ^Graph_Literal, i: int, elem_t: Type) -> Dest {
    return Dest{kind = .Index, index = i, type_ = elem_t, parent = &gl.parent}
}

// Where the literal's field goes: named, or its position's.
// `Foo{call()}`, the call built: each field its
// result. False when it resolved to no function.
graph_build_spread :: proc(b: ^Graph_Builder, gl: ^Graph_Literal, span: Span, c: Operand) -> bool {
    callee := b.g.callee[c.op] if c.op != NO_NODE else nil
    if callee == nil || gl.sd == nil { return false }
    graph_spread_results(b, span, gl.sd, &gl.parent, callee, c)
    return true
}

graph_build_literal_field :: proc(gl: ^Graph_Literal, name: string, i: int) -> Dest {
    name := name
    if name == "" && gl.sd != nil && gl.skip + i < len(gl.sd.fields) { name = gl.sd.fields[gl.skip + i].name }
    t: Type
    if gl.sd != nil {
        if fi, ok := gl.sd.field_map[name]; ok { t = gl.sd.fields[fi].type_ }
    }
    return Dest{kind = .Field, name = name, type_ = t, parent = &gl.parent}
}

// An array literal built into d: zero at the destination's
// type — a short literal leaves the rest zero — or, with none known yet, the
// literal's (typed once its first element is), then each element into its
// slot.
Graph_Array :: struct {
    d:      Dest,
    zero:   Node_Id,
    elem_t: Type,
}

graph_build_array :: proc(b: ^Graph_Builder, span: Span, d: Dest) -> ^Graph_Array {
    ga := new(Graph_Array, context.temp_allocator)
    ga.d = d
    t := d.type_ if d.type_ != nil && !is_infer(d.type_) else nil
    ga.zero = graph_op(b, .Zero, .Explicit, span, t, "", graph_dest_place(b, d, span))
    if t != nil { ga.elem_t = graph_elem_type(t) }
    return ga
}

// Element i's slot; the literal's own type, from its first element, when the
// destination gave none.
graph_build_array_elem :: proc(b: ^Graph_Builder, ga: ^Graph_Array, i: int, first: Type, lit_t: Type) -> Dest {
    if ga.elem_t == nil {
        ga.elem_t = first
        b.g.type_[ga.zero] = lit_t
    }
    return Dest{kind = .Index, index = i, type_ = ga.elem_t, parent = &ga.d}
}

// A variant built at d (a bare variant): its construction, then
// its field defaults.
graph_build_variant :: proc(b: ^Graph_Builder, t: Type, name: string, d: Dest, span: Span) -> ^Type_Scope {
    graph_op(b, .Construct, .Explicit, span, t, name, graph_dest_place(b, d, span))
    return graph_variant_struct(b, t, name)
}

// A field default a construction writes (a variant
// has no constructor to run them), into the struct at d.
graph_build_field_default :: proc(b: ^Graph_Builder, d: Dest, name: string, t: Type, v: Operand, span: Span) {
    vd := d
    fd := Dest{kind = .Field, name = name, type_ = t, parent = &vd}
    graph_op(b, .Write, .Implied, span, nil, "", graph_dest_place(b, fd, span), v)
}

// An array literal built before the type its use takes it at was known (a
// dispatch's argument, the function chosen after): its nodes, from `from`,
// retyped — an array of untyped elements (its own, its temporary's) as that
// one, an untyped element's slot as that one's element.
graph_build_retype_literal :: proc(b: ^Graph_Builder, from, to: int, new: Type) {
    new_elem := graph_elem_type(new)
    for i in from ..< to {
        t := b.g.type_[i]
        if t == nil { continue }
        if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array && is_infer(fa.elem) {
            b.g.type_[i] = new
        } else if b.g.kind[i] == .Op && b.g.op[i] == .Index && is_infer(t) {
            b.g.type_[i] = new_elem
        }
    }
}

// An aggregate built where no destination was given: a synthetic local,
// made before it, typed once it is.
graph_build_temp :: proc(b: ^Graph_Builder, span: Span, t: Type = nil) -> Dest {
    return graph_dest_var("temp", graph_slot(b, "temp", t, span), t)
}

graph_build_temp_end :: proc(b: ^Graph_Builder, d: Dest, t: Type, span: Span) -> Operand {
    b.g.type_[d.decl] = t
    graph_build_typed(b, d.decl, t)
    return graph_var(b, "temp", d.decl, t, span)
}

// A construction's operation into d: its place, the
// arguments, then its overrides' writes (graph_build_literal_field over the
// overrides, with gl.parent = d).
graph_build_construct :: proc(b: ^Graph_Builder, callee: ^Type_Scope, t: Type, d: Dest, args: []Operand, w: Written, span: Span) -> ^Graph_Literal {
    ops := make([dynamic]Operand, 0, len(args) + 1, context.temp_allocator)
    append(&ops, graph_dest_place(b, d, span))
    append(&ops, ..args)
    b.code.constructed = graph_call_op(b, .Construct, w, span, callee, t, ..ops[:])
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent = d, d
    gl.sd = as_scope_body(distinct_base(t))
    return gl
}

// A bare declaration of a value no constructor builds: zero.
graph_build_zero_var :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span: Span) {
    graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, b.g.name[decl], decl, t, span))
}

// A body's types, now that its widths are known.
// A node's operands while the graph is being built: they end where the next
// node's begin — or, the newest, now.
graph_built_operands :: proc(b: ^Graph_Builder, id: Node_Id) -> []Operand {
    end := int(b.g.operand_first[id + 1]) if int(id) + 1 < b.nodes else len(b.g.operands)
    return b.g.operands[b.g.operand_first[id]:end]
}

// The local every one of a fun's returns returns, read whole — built in its
// caller's slot, not on the arena; none when one returns something else, or
// the fun has several results.
@(private="file")
graph_build_returned :: proc(b: ^Graph_Builder, f: ^Graph_Body) -> Node_Id {
    g := b.g
    if f.ts == nil || f.ts.kind != .Fun || len(f.ts.return_types) != 1 { return NO_NODE }
    returned := NO_NODE
    for r in f.returns {
        if graph_dropped(b, r) { continue }
        ops := graph_built_operands(b, r)
        if len(ops) != 1 || ops[0].op == NO_NODE || g.op[ops[0].op] != .Read { return NO_NODE }
        place := graph_built_operands(b, ops[0].op)[0].op
        if g.op[place] != .Var || g.refers[place] == NO_NODE { return NO_NODE }
        local := g.refers[place]
        if g.kind[local] != .Local || returned != NO_NODE && local != returned { return NO_NODE }
        returned = local
    }
    return returned
}

@(private="file")
graph_body_settle :: proc(b: ^Graph_Builder, f: ^Graph_Body) {
    g := b.g
    for w in f.widens {
        to := w.to
        if w.binary {
            to = graph_work(w.work)
        } else if w.sig != nil {
            to = w.sig.params[w.param].type_ if w.param < len(w.sig.params) else nil
        }
        if w.settle_to { to = graph_settled(to) }
        if w.views {
            _, to_ptr := distinct_base(to).(^Type_Ptr)
            _, from_ptr := distinct_base(w.t).(^Type_Ptr)
            _, to_slice := distinct_base(to).(^Type_Slice)
            _, from_array := distinct_base(w.t).(^Type_Fixed_Array)
            if to != nil && to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(w.t) {
                g.type_[w.id], g.name[w.id] = to, type_name(to)   // its header, as one
                if w.slice != NO_NODE { graph_drop(b, w.slice, NO_VALUE) }
                continue
            }
            if w.slice != NO_NODE {
                if to != nil && to_slice && from_array {
                    g.type_[w.slice] = to   // its place, as a slice
                    graph_drop(b, w.read, {w.slice, 0})
                    graph_drop(b, w.id, {w.read, 0})
                    continue
                }
            }
        }
        if w.slice != NO_NODE { graph_drop(b, w.slice, NO_VALUE) }   // (no view taken)
        if graph_widens(graph_settled(g.type_[w.v.op]), to) {
            g.type_[w.id], g.name[w.id] = to, type_name(to)
        } else {
            graph_drop(b, w.id, w.v)
        }
    }
    for id in f.consts {
        if is_infer(g.type_[id]) && !is_infer(graph_settled(g.type_[id])) { append(&g.settled, id) }
    }
    // A big local's space on the arena, taken before its value — but the
    // local every return returns: it is built in the caller's slot.
    returned := graph_build_returned(b, f)
    holds: map[Node_Id]bool   // the scopes holding one
    defer delete(holds)
    for a in f.allocs {
        t := g.type_[a.decl]
        if t != nil && routes_to_arena(t) && a.decl != returned {
            g.type_[a.var], g.type_[a.alloc] = t, t
            holds[g.parent[a.decl]] = true
            continue
        }
        graph_drop(b, a.var, NO_VALUE); graph_drop(b, a.alloc, NO_VALUE)
    }
    // A scope holding values on the arena (graph_scope_open): its mark and
    // resets, where the builder makes them; else none. Main's own body sets
    // the arena up and leaves it with the program.
    main, _ := b.checked.functions["main"]
    for m in f.marks {
        if holds[m.block] && (main == nil || g.type_[m.block] != Type(main)) { continue }
        graph_drop(b, m.mark, NO_VALUE)
        for r in m.resets { graph_drop(b, r, NO_VALUE) }
    }

    // A range's bounds cast to the counter's type where theirs differs; the
    // check that it counts up where a bound is no constant.
    resolve :: proc(b: ^Graph_Builder, o: Operand) -> Operand {
        o := o
        for (o.op != NO_NODE && graph_dropped(b, o.op)) { o = b.repl[o.op] }
        return o
    }
    for k in f.checks {
        if k.kind != .Bound { continue }
        if k.t != nil && !is_infer(k.t) && !types_equal(k.t, k.ct) {
            g.type_[k.ids[0]], g.name[k.ids[0]] = k.ct, type_name(k.ct)
        } else {
            graph_drop(b, k.ids[0], k.v)
        }
    }
    for k in f.checks {
        if k.kind != .Ascends { continue }
        lo, hi := resolve(b, k.lo).op, resolve(b, k.hi).op
        if lo != NO_NODE && hi != NO_NODE && g.op[lo] == .Const && g.op[hi] == .Const {
            graph_drop(b, k.ids[0], NO_VALUE); graph_drop(b, k.ids[1], NO_VALUE)
        }
    }
    k := 0   // (its synthetic locals, in the order they were made)
    for p in b.segs[f.seg].pieces {
        for i in p.nodes[0] ..< p.nodes[1] {
            for k < len(f.slots) && int(f.slots[k]) < i { k += 1 }
            g.type_[i] = graph_settled(g.type_[i], pointee = k < len(f.slots) && int(f.slots[k]) == i)
        }
    }
    // Params by their scope's types: a default's width is settled once its
    // body is checked (solidify_param_defaults).
    if f.ts != nil {
        for p, k in f.ts.params { g.type_[f.root + 1 + Node_Id(k)] = graph_settled(p.type_) }
    }
}

// The statement the checker is on: its entry, the
// first time. A statement the checker meets only once is `fresh` (a body's
// own statements).
graph_build_stmt :: proc(b: ^Graph_Builder, id: Syntax_Id, span: Span, kind: Stmt_Kind, fresh := false) -> (saved: i32) {
    f := b.body
    saved = b.stmt
    if !fresh {
        if at, seen := f.stmts[id]; seen {
            b.stmt = at
            return
        }
    }
    b.stmt = i32(len(b.g.stmts))
    append(&b.g.stmts, Graph_Stmt{span = span, kind = kind})
    f.stmts[id] = b.stmt
    return
}

graph_build_stmt_end :: proc(b: ^Graph_Builder, saved: i32) {
    b.stmt = saved
}

// A statement of the body's code, before it is checked — code, not a
// definition (`runs_code`): one right after a return, break or continue is
// unreachable (graph.unreachable).
graph_build_body_stmt :: proc(b: ^Graph_Builder, span: Span, runs_code: bool) {
    if b.code.active && b.code.run == nil && runs_code {
        append(&b.g.unreachable, span)
    }
}

// A definition in a body, where it is written: built by the builder,
// from here, when the body is placed.
graph_build_def :: proc(b: ^Graph_Builder, d: Graph_Decl) {
    seg := &b.segs[b.seg]
    append(&seg.defs, d)
}

// Put a body where its scope is, then the code each of its definitions
// defines — a fun's, a struct's, a constant's: a code of its own, after it.
@(private="file")
graph_body_place :: proc(b: ^Graph_Builder, si: int, parent: Node_Id, name: string) {
    graph_anchor_here(b, si)
    graph_segment_place(b, si, parent, b.stmt, name)
    defs := b.segs[si].defs[:]   // (placing them grows b.segs)
    for d in defs {
        // (A constant: built as the checker settled it.)
        if early, settled := b.def_segs[d.id]; settled {
            graph_anchor_here(b, early)
            continue
        }
        sub, saved := graph_segment_enter(b)
        graph_decl_stmt(b, d, NO_NODE, {kind = .Local})
        graph_segment_leave(b, saved)
        graph_anchor_here(b, sub)
    }
}

// A body's definition the checker settles — a constant: its code, put in a
// segment of its own after the body when the body is placed.
graph_build_def_settled :: proc(b: ^Graph_Builder, d: Graph_Decl) {
    si, saved := graph_segment_enter(b)
    code, locals := b.code, graph_locals_enter(b)
    b.code = {}
    graph_decl_stmt(b, d, NO_NODE, {kind = .Local})
    b.code = code
    graph_locals_leave(b, locals)
    graph_segment_leave(b, saved)
    b.def_segs[d.id] = si
}

// --- constants ------------------------------------------------------------
// A constant is its declaration and the code that computes its value — run
// when the program is compiled, never when it runs. The checker builds it as
// it checks the value, in a segment of its own, as it builds a body; it is
// put where it is written once the checker settles the declaration
// (graph_decl_stmt).

// A constant's code, before its value is checked: its declaration (typed
// once the value is) and a run entered from it.
graph_const_begin :: proc(b: ^Graph_Builder, d: Graph_Decl) -> ^Graph_Body {
    f := new(Graph_Body)
    f.outer_body = b.body
    f.const_decl = d
    b.body = f
    f.seg, f.outer = graph_segment_enter(b)
    f.stmt, b.stmt = b.stmt, i32(len(b.g.stmts))
    append(&b.g.stmts, Graph_Stmt{span = d.span, kind = d.kind})
    f.root = graph_node(b, .Const, .Explicit, NO_NODE, d.name, nil, d.span)
    b.segs[f.seg].root = f.root
    b.g.const_code[d.value] = f.root
    f.contents = Graph_Contents{locals = graph_locals_enter(b), self = b.self, n = f.root, span = d.span}
    b.self = NO_NODE
    f.contents.code = graph_code_begin(b, f.root)
    return f
}

// Its value checked, of type t: its code ends, and it waits to be put where
// it is written. One not built is left out (graph_body_fail).
graph_const_end :: proc(b: ^Graph_Builder, f: ^Graph_Body, t: Type) {
    d := f.const_decl
    if f.failed == "" { graph_build_typed(b, f.root, t) }
    graph_contents_end(b, f.contents, finish = f.failed == "")
    b.stmt = f.stmt
    graph_segment_leave(b, f.outer)
    b.body = f.outer_body
    delete(f.stmts)
    delete(f.fields)
    delete(f.field_inits)
    delete(f.field_outs)
    if f.failed == "" {
        b.const_segs[d.id] = f.seg
        append(&b.bodies, f)   // settled when the graph is put together
        return
    }
    delete_key(&b.g.const_code, d.value)
    graph_body_free(f)
}


// What a scope's contents change in the builder, until they end.
@(private="file")
Graph_Contents :: struct {
    locals:      map[Token_Id]Node_Id,   // the outer code's declarations
    self:        Node_Id,
    code:        Code,
    n:           Node_Id,
    span:        Span,
    intrinsic:   bool,
}

// A scope's contents up to its statements: a fresh set of names, its params
// and results, and its code's start.
@(private="file")
graph_contents_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, span: Span, intrinsic: bool, n: Node_Id) -> Graph_Contents {
    kind := b.g.kind[n]
    gc := Graph_Contents{locals = graph_locals_enter(b), self = b.self, n = n, span = span, intrinsic = intrinsic}
    b.self = n if kind == .Struct else NO_NODE
    for p in ts.params {
        d := graph_node(b, .Param, .Explicit, n, p.name, p.type_, span)
        graph_declare(b, d, p.decl)
    }
    graph_results(b, ts, n, span)
    // An intrinsic's body is generated at each call: no code of its own.
    if intrinsic { return gc }
    gc.code = graph_code_begin(b, n)
    graph_scope_open(b, n, span)
    return gc
}

// A scope's contents after its statements: its code's end (unless it is
// being dropped), and the names as they were.
@(private="file")
graph_contents_end :: proc(b: ^Graph_Builder, gc: Graph_Contents, finish := true) {
    if !gc.intrinsic {
        if finish { graph_code_finish(b, gc.span) }
        graph_code_end(b, gc.code)
    }
    graph_close(b, gc.n)
    graph_locals_leave(b, gc.locals)
    b.self = gc.self
}


// A function's results: named ones by name, else `result` (or `result1`, … when several).
@(private="file")
graph_results :: proc(b: ^Graph_Builder, ts: ^Type_Scope, parent: Node_Id, span: Span) {
    for rt, i in ts.return_types {
        name := "result"
        if i < len(ts.return_binding_names) {
            name = ts.return_binding_names[i]
        } else if len(ts.return_types) > 1 {
            name = fmt.aprintf("result%d", i + 1)
        }
        named := i < len(ts.return_binding_names)
        r := graph_node(b, .Result, .Explicit if named else .Synthetic, parent, name, rt, span)
        if named {   // a named result is a local
            graph_declare(b, r, ts.return_binding_decls[i])
        }
    }
}

// A union's tag type: the one it declares (`union(tag u32)`), else i64.
@(private="file")
graph_tag_type :: proc(t: Type) -> Type {
    ut, _ := distinct_base(t).(^Type_Union)
    switch ut.tag_type if ut != nil else "" {
    case "u8":  return Type_Numeric{.Unsigned, 8}
    case "u16": return Type_Numeric{.Unsigned, 16}
    case "u32": return Type_Numeric{.Unsigned, 32}
    case "u64": return Type_Numeric{.Unsigned, 64}
    case "i8":  return Type_Numeric{.Signed, 8}
    case "i16": return Type_Numeric{.Signed, 16}
    case "i32": return Type_Numeric{.Signed, 32}
    }
    return Type_Numeric{.Signed, 64}
}

// --- checks -------------------------------------------------------------------

// Every checked fun and struct with code is exactly one node.
@(private="file")
graph_check_coverage :: proc(b: ^Graph_Builder, pc: ^Program_Code) {
    count: map[rawptr]int
    defer delete(count)
    for c in pc.codes {
        if c.kind[0] == .Fun || c.kind[0] == .Struct { count[graph_type_ptr(c.type_[0])] += 1 }
    }
    bad := 0
    check :: proc(count: ^map[rawptr]int, bad: ^int, t: Type, span: Span) {
        if n := count[graph_type_ptr(t)]; n != 1 {
            loc := span_location(span)
            emit_diagnostic(.Graph_Error, loc, "'%s' is %d nodes of the graph, not 1", ask_type_name(t), n)
            bad^ += 1
        }
    }
    // (Code: a fun's, a struct's constructor's. A foreign fun, a type, a
    // union's variant has none.)
    t := b.checked.table
    for _, ft in b.checked.functions {
        if _, is_foreign := ft.origin.(Origin_Foreign); !ft.is_module && !is_foreign { check(&count, &bad, ft, ft.body_span) }
    }
    variants := make(map[^Type_Scope]bool, context.temp_allocator)
    for _, u in t.unions { for _, st in u.variant_structs { variants[st] = true } }
    for _, st in t.structs { if !st.is_module && st not_in variants { check(&count, &bad, st, st.body_span) } }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// Refers-to is complete: every var operation names a declaration.
@(private="file")
graph_check_refers :: proc(g: ^Program_Graph) {
    bad := 0
    for k, id in g.kind {
        if k == .Op && g.op[id] == .Var && g.refers[id] == NO_NODE {
            o := g.origin[id]
            emit_diagnostic(.Graph_Error, span_location(o), "'%s' names no declaration", g.name[id])
            bad += 1
        }
    }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// The fun or struct an operation runs in: its nearest callable ancestor.
graph_caller :: proc(g: ^Program_Graph, id: Node_Id) -> ^Type_Scope {
    if n := graph_code_owner(g, id); n != NO_NODE { return g.type_[n].(^Type_Scope) }
    return nil
}

// The runs are well formed: every operation is in exactly one run; a run
// ends in its only terminator; Then edges land on the first operation of a
// run; and an operand dominates its use: earlier in the same run, or in a run
// every path to the use passes through.
@(private="file")
graph_check_runs :: proc(g: ^Program_Graph) {
    n_runs := len(g.run_first) - 1
    run_of := make([]i32, len(g.kind))
    pos := make([]i32, len(g.kind))
    defer delete(run_of)
    defer delete(pos)
    slice.fill(run_of, -1)
    bad := 0
    report :: proc(g: ^Program_Graph, bad: ^int, id: Node_Id, format: string, args: ..any) {
        o := g.origin[id]
        emit_diagnostic(.Graph_Error, span_location(o), format, ..args)
        bad^ += 1
    }
    for r in 0 ..< n_runs {
        ops := graph_run(g, r)
        for id, i in ops {
            if run_of[id] != -1 { report(g, &bad, id, "operation %d is in two runs", id) }
            run_of[id] = i32(r)
            pos[id] = i32(i)
            last := i == len(ops) - 1
            if graph_is_terminator(g.op[id]) != last {
                report(g, &bad, id, "run %d %s", r, "ends without a terminator" if last else "has a terminator before its end")
            }
        }
    }
    for k, id in g.kind {
        if k == .Op && run_of[id] == -1 { report(g, &bad, Node_Id(id), "operation %d is in no run", id) }
    }
    // The runs' control-flow graph, and each run's immediate dominator. A run
    // entered from a scope (a fun's, a struct's, a defer's first run) or from
    // nothing (code after a return) roots its own tree.
    succ := make([][dynamic]i32, n_runs)
    pred := make([][dynamic]i32, n_runs)
    is_entry := make([]bool, n_runs)
    defer {
        for s in succ { delete(s) }
        for p in pred { delete(p) }
        delete(succ); delete(pred); delete(is_entry)
    }
    for e in g.edges {
        r := run_of[e.to]
        if r == -1 || pos[e.to] != 0 { report(g, &bad, e.to, "a then edge lands inside a run"); continue }
        if g.kind[e.from] != .Op { is_entry[r] = true; continue }
        append(&succ[run_of[e.from]], r)
        append(&pred[r], run_of[e.from])
    }
    idom := graph_dominators(n_runs, succ, pred, is_entry)
    defer delete(idom)
    for id in 0 ..< len(g.kind) {
        if g.kind[id] != .Op { continue }
        for o in graph_operands(g, Node_Id(id)) {
            if o.op == NO_NODE { continue }
            if g.kind[o.op] != .Op { report(g, &bad, Node_Id(id), "operand %d is no operation", o.op); continue }
            r, def := run_of[id], run_of[o.op]
            ok := def == r && pos[o.op] < pos[id]
            for walk := r; !ok && idom[walk] != -1 && int(idom[walk]) < n_runs; {
                walk = idom[walk]
                ok = walk == def
            }
            if !ok { report(g, &bad, Node_Id(id), "operation %d uses %d, which does not dominate it", id, o.op) }
        }
    }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// Immediate dominators over a graph of runs (Cooper, Harvey and Kennedy's
// iterative algorithm). Every root — an entry, or a run nothing enters — hangs
// under one virtual root, index n, so that a run two roots reach (a join that
// code after a return also jumps to) still gets an answer: the virtual root.
// idom[n] is n; a run no root reaches has -1.
@(private="file")
graph_dominators :: proc(n: int, succ, pred: [][dynamic]i32, is_entry: []bool) -> []i32 {
    top := i32(n)
    idom := make([]i32, n + 1)
    slice.fill(idom, -1)
    idom[top] = top
    order := make([]i32, n + 1)    // reverse postorder position
    defer delete(order)
    slice.fill(order, -1)
    order[top] = 0
    Frame :: struct { run, next: i32 }
    stack: [dynamic]Frame
    defer delete(stack)
    post := make([dynamic]i32, 0, n)
    defer delete(post)
    visited := make([]bool, n)
    defer delete(visited)
    is_root := make([]bool, n)
    defer delete(is_root)
    for root in 0 ..< n {
        if !(is_entry[root] || len(pred[root]) == 0) { continue }
        is_root[root] = true
        if visited[root] { continue }
        visited[root] = true
        append(&stack, Frame{i32(root), 0})
        for len(stack) > 0 {
            f := &stack[len(stack) - 1]
            if int(f.next) < len(succ[f.run]) {
                s := succ[f.run][f.next]
                f.next += 1
                if !visited[s] {
                    visited[s] = true
                    append(&stack, Frame{s, 0})
                }
            } else {
                append(&post, f.run)
                pop(&stack)
            }
        }
    }
    rpo := make([dynamic]i32, 0, n)
    defer delete(rpo)
    #reverse for r in post {
        append(&rpo, r)
        order[r] = i32(len(rpo))   // after the virtual root's 0
    }
    intersect :: proc(idom, order: []i32, a, b: i32) -> i32 {
        a, b := a, b
        for a != b {
            for order[a] > order[b] { a = idom[a] }
            for order[b] > order[a] { b = idom[b] }
        }
        return a
    }
    for changed := true; changed; {
        changed = false
        for r in rpo {
            // A root's predecessors include the virtual root.
            new_idom: i32 = top if is_root[r] else -1
            for p in pred[r] {
                if idom[p] == -1 { continue }
                new_idom = p if new_idom == -1 else intersect(idom, order, p, new_idom)
            }
            if new_idom != idom[r] {
                idom[r] = new_idom
                changed = true
            }
        }
    }
    return idom
}

// --- dump -------------------------------------------------------------------

// MARA_GRAPH=all prints the whole graph; MARA_GRAPH=<name> prints the subtree
// of every node with that name, and the runs of each fun in it.
@(private="file")
graph_dump :: proc(pc: ^Program_Code) {
    want := os.get_env("MARA_GRAPH", context.temp_allocator)
    if want == "" { return }
    for c in pc.codes {
        fmt.printfln("code %v %s", c.kind[0], c.name[0])
        if want == "full" { graph_dump_full(pc, c) } else { graph_dump_code(c, want) }
    }
    for s in pc.unreachable { fmt.printfln("u @%s:%d:%d", filepath.base(span_file(s)), span_line(s), span_col(s)) }
}

@(private="file")
graph_dump_code :: proc(g: ^Program_Graph, want: string) {
    fmt.printf("graph: %d nodes, %d runs\n", len(g.kind), len(g.run_first) - 1)
    run_of := make([]i32, len(g.kind), context.temp_allocator)
    slice.fill(run_of, -1)
    for r in 0 ..< len(g.run_first) - 1 { for id in graph_run(g, r) { run_of[id] = i32(r) } }
    for id in 0 ..< len(g.kind) {
        if want != "all" && g.name[id] != want { continue }
        if want == "all" && g.parent[id] != NO_NODE { continue }   // roots print their subtrees
        base := graph_depth(g, Node_Id(id))
        for n in id ..= int(g.last[id]) {
            graph_dump_node(g, Node_Id(n), graph_depth(g, Node_Id(n)) - base)
        }
        if want == "all" { continue }
        // The runs whose operations are in this subtree, in order.
        for r in 0 ..< len(g.run_first) - 1 {
            ops := graph_run(g, r)
            if len(ops) == 0 || int(ops[0]) < id || int(ops[0]) > int(g.last[id]) { continue }
            sb := strings.builder_make(context.temp_allocator)
            fmt.sbprintf(&sb, "  run %d:", r)
            for op in ops { fmt.sbprintf(&sb, " %d", op) }
            for e in graph_out(g, ops[len(ops) - 1]) {
                fmt.sbprintf(&sb, "  → run %d", run_of[e.to])
            }
            fmt.println(strings.to_string(sb))
        }
    }
}

@(private="file")
graph_depth :: proc(g: ^Program_Graph, id: Node_Id) -> int {
    d := 0
    for p := g.parent[id]; p != NO_NODE; p = g.parent[p] { d += 1 }
    return d
}

// MARA_GRAPH=full: every column of every node, then the edges, runs, statements
// and tables, one fact a line in id order — two builds of one program compare
// line by line (a type is its name; a constant's value expression its span).
@(private="file")
graph_dump_full :: proc(pc: ^Program_Code, g: ^Program_Graph) {
    span :: proc(s: Span) -> string {
        return fmt.tprintf("%s:%d:%d", filepath.base(span_file(s)), span_line(s), span_col(s)) if span_file(s) != "" else "-"
    }
    calls := 0
    for c in g.callee { if c != nil { calls += 1 } }
    fmt.printf("graph: %d nodes, %d runs, %d edges\n", len(g.kind), len(g.run_first) - 1, len(g.edges) + calls + len(g.defer_of))
    for id in 0 ..< len(g.kind) {
        b := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&b, "n %d %v %v %v p%d l%d %q", id, g.kind[id], g.op[id], g.written[id],
            g.parent[id], g.last[id], g.name[id])
        if t := g.type_[id]; t != nil { fmt.sbprintf(&b, " t=%s", type_name(t)) }
        fmt.sbprintf(&b, " @%s r%d s%d", span(g.origin[id]), g.refers[id], g.stmt[id])
        if ops := graph_operands(g, Node_Id(id)); len(ops) > 0 {
            strings.write_string(&b, " (")
            for o, i in ops { fmt.sbprintf(&b, "%s%d.%d", ", " if i > 0 else "", o.op, o.out) }
            strings.write_string(&b, ")")
        }
        if c, ok := g.consts[Node_Id(id)]; ok { fmt.sbprintf(&b, " const=%v", c) }
        if c := g.constant[id]; c != 0 {   // (by its code's name: a value's node isn't the same from one build to the next)
            code, built := pc.consts[c]
            fmt.sbprintf(&b, " constant=%s", code.name[0] if built else "?")
        }
        if s, ok := g.assert_sides[Node_Id(id)]; ok { fmt.sbprintf(&b, " sides=%q|%q", s[0], s[1]) }
        if k, ok := g.consumes[Node_Id(id)]; ok { fmt.sbprintf(&b, " consumes=%d", k) }
        fmt.println(strings.to_string(b))
    }
    // (Each operation's: its thens, or what it calls, or the defer it runs.)
    for id in 0 ..< len(g.kind) {
        for e in graph_out(g, Node_Id(id)) { fmt.printfln("e %d -> %d Then %v", e.from, e.to, e.written) }
        if callee := graph_called(g, Node_Id(id)); callee != nil { fmt.printfln("e %d -> %s Calls %v", id, callee.name, g.written[id]) }
        if d, runs := g.defer_of[Node_Id(id)]; runs { fmt.printfln("e %d -> %d Runs Synthetic", id, d) }
    }
    for r in 0 ..< len(g.run_first) - 1 {
        b := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&b, "r %d:", r)
        for op in graph_run(g, r) { fmt.sbprintf(&b, " %d", op) }
        fmt.println(strings.to_string(b))
    }
    for s, i in g.stmts { fmt.printfln("s %d %v @%s", i, s.kind, span(s.span)) }
    for id in g.settled { fmt.printfln("settled %d", id) }
}

@(private="file")
graph_dump_node :: proc(g: ^Program_Graph, id: Node_Id, indent: int) {
    b := strings.builder_make(context.temp_allocator)
    for _ in 0 ..< indent { strings.write_string(&b, "  ") }
    if g.kind[id] == .Op {
        fmt.sbprintf(&b, "%d %s", id, graph_op_word(g.op[id]))
        if g.name[id] != "" { fmt.sbprintf(&b, " %s", g.name[id]) }
        ops := graph_operands(g, id)
        if len(ops) > 0 {
            strings.write_string(&b, "(")
            for o, i in ops {
                if i > 0 { strings.write_string(&b, ", ") }
                if o.op == NO_NODE { strings.write_string(&b, "_") }
                else if o.out > 0  { fmt.sbprintf(&b, "%d.%d", o.op, o.out) }
                else               { fmt.sbprintf(&b, "%d", o.op) }
            }
            strings.write_string(&b, ")")
        }
        if r := g.refers[id]; r != NO_NODE { fmt.sbprintf(&b, " = %d", r) }
        if t := g.type_[id]; t != nil { fmt.sbprintf(&b, " : %s", type_name(t)) }
        if callee := graph_called(g, id); callee != nil { fmt.sbprintf(&b, " → %s", callee.name) }
        if d, runs := g.defer_of[id]; runs { fmt.sbprintf(&b, " → %d", d) }
    } else {
        fmt.sbprintf(&b, "%d %s %s", id, graph_kind_word(g.kind[id]), g.name[id])
        if t := g.type_[id]; t != nil {
            #partial switch g.kind[id] {
            case .Field, .Param, .Result, .Local, .Const:
                fmt.sbprintf(&b, " : %s", type_name(t))
            }
        }
    }
    if o := g.origin[id]; span_file(o) != "" { fmt.sbprintf(&b, "   %s:%d", filepath.base(span_file(o)), span_line(o)) }
    if g.written[id] == .Synthetic { strings.write_string(&b, "   (synthetic)") }
    else if g.written[id] == .Implied { strings.write_string(&b, "   (implied)") }
    fmt.println(strings.to_string(b))
}

graph_kind_word :: proc(k: Node_Kind) -> string {
    switch k {
    case .Module:   return "module"
    case .Struct:   return "struct"
    case .Fun:      return "fun"
    case .Block:    return "block"
    case .Field:    return "field"
    case .Param:    return "param"
    case .Result:   return "result"
    case .Local:    return "local"
    case .Const:    return "const"
    case .Op:       return "op"
    }
    return "?"
}

graph_op_word :: proc(k: Op_Kind) -> string {
    switch k {
    case .Var:         return "var"
    case .Global:      return "global"
    case .Field:       return "field"
    case .Index:       return "index"
    case .View:        return "view"
    case .Deref:       return "deref"
    case .Variant:     return "variant"
    case .Swizzle:     return "swizzle"
    case .Slice:       return "slice"
    case .Read:        return "read"
    case .Write:       return "write"
    case .Address:     return "address"
    case .Zero:        return "zero"
    case .Construct:   return "construct"
    case .Fill:        return "fill"
    case .Carve:       return "carve"
    case .Byte_Read:   return "byte read"
    case .Arena_Alloc: return "arena alloc"
    case .Const:       return "const"
    case .Arith:       return "arith"
    case .Compare:     return "compare"
    case .Unary:       return "unary"
    case .Cast:        return "cast"
    case .Call:        return "call"
    case .Print:       return "print"
    case .Assert:      return "assert"
    case .Crash:       return "crash"
    case .Jump:        return "jump"
    case .Branch:      return "branch"
    case .Switch:      return "switch"
    case .Return:      return "return"
    case .Run_Defer:   return "run defer"
    case .Arena_Mark:  return "arena mark"
    case .Arena_Reset: return "arena reset"
    }
    return "?"
}
