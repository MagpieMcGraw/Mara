package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The program graph (design/program_graph.md): the program's shape, built from
// the checked syntax tree at the end of a clean check. The analyses after it
// move onto it one by one (design/graph_retrofit.md, phase 2).
//
// Nodes are scopes, the names they declare, and operations (the set in
// design/program_graph.md § Operations). Each fact is a column indexed by
// Node_Id. Ids are handed out depth-first in written order, so a scope's
// subtree is one run of ids: [id, last[id]].
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
    Module, Struct, Union, Enum, Fun, Block,
    // Names declared in a scope
    Field, Param, Result, Local, Const, Import, Variant, Type_Def, Dispatch,
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

Edge_Kind :: enum u8 {
    Calls,  // a call or construct operation → the fun or struct it runs
    Runs,   // a run-defer operation → the defer block it runs
    Then,   // a run's last operation, or a scope for its entry → a run's first operation
    Flows,  // a declaration → one its value moves into (the index of the operations' flows)
}

Edge :: struct {
    from:    Node_Id,
    to:      Node_Id,
    kind:    Edge_Kind,
    written: Written,
    site:    Node_Id,   // the operation where it happens: for a flow, the write, call or return
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
    stmt:    [dynamic]i32,      // an operation → the statement it comes from (in `stmts`), or -1

    // A node's operands are operands[operand_first[id] : operand_first[id+1]].
    operands:      [dynamic]Operand,
    operand_first: [dynamic]i32,

    // Run r is run_ops[run_first[r] : run_first[r+1]], in the order it runs.
    run_ops:   [dynamic]Node_Id,
    run_first: [dynamic]i32,

    // One edge table, sorted by `from`. A node's outgoing edges are
    // edges[out_first[id] : out_first[id+1]]; its incoming ones are the edge
    // numbers in_edges[in_first[id] : in_first[id+1]].
    edges:     [dynamic]Edge,
    out_first: [dynamic]i32,
    in_edges:  [dynamic]i32,
    in_first:  [dynamic]i32,

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

    // A constant's value as written, by its declaration: resolved before
    // the graph, it has no operations; a table's bytes are built from it.
    const_values: map[Node_Id]Expr,
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

graph_in :: proc(g: ^Program_Graph, id: Node_Id) -> []i32 {
    return g.in_edges[g.in_first[id]:g.in_first[id + 1]]
}

graph_operands :: proc(g: ^Program_Graph, id: Node_Id) -> []Operand {
    return g.operands[g.operand_first[id]:g.operand_first[id + 1]]
}

graph_run :: proc(g: ^Program_Graph, r: int) -> []Node_Id {
    return g.run_ops[g.run_first[r]:g.run_first[r + 1]]
}

// Each run's first operation → the run: where a Then edge lands.
graph_run_starts :: proc(g: ^Program_Graph) -> map[Node_Id]i32 {
    starts := make(map[Node_Id]i32, len(g.run_first))
    for r in 0 ..< len(g.run_first) - 1 {
        if ops := graph_run(g, r); len(ops) > 0 { starts[ops[0]] = i32(r) }
    }
    return starts
}

// Whether a fun or struct's code can reach its end without a return: the
// synthetic return that ends its body, in a run its entry reaches.
graph_falls_off :: proc(g: ^Program_Graph, starts: map[Node_Id]i32, scope: Node_Id) -> bool {
    seen: map[i32]bool
    defer delete(seen)
    todo: [dynamic]i32
    defer delete(todo)
    for e in graph_out(g, scope) { if e.kind == .Then { append(&todo, starts[e.to]) } }
    for len(todo) > 0 {
        r := pop(&todo)
        if r in seen { continue }
        seen[r] = true
        ops := graph_run(g, int(r))
        last := ops[len(ops) - 1]
        if g.op[last] == .Return && g.written[last] == .Synthetic { return true }
        for e in graph_out(g, last) { if e.kind == .Then { append(&todo, starts[e.to]) } }
    }
    return false
}

// A fun's (or struct's) code as runs: those its entry reaches, then those of
// each defer block a run defer in them runs. Returns how many are its own
// code's; each list keeps a run's successors after it.
graph_code_runs :: proc(g: ^Program_Graph, starts: map[Node_Id]i32, scope: Node_Id, out: ^[dynamic]i32) -> (own: int) {
    seen: map[i32]bool
    defer delete(seen)
    reach :: proc(g: ^Program_Graph, starts: map[Node_Id]i32, scope: Node_Id, out: ^[dynamic]i32, seen: ^map[i32]bool) {
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
            next := graph_out(g, ops[len(ops) - 1])
            for i := len(next) - 1; i >= 0; i -= 1 {
                if next[i].kind == .Then { append(&todo, starts[next[i].to]) }
            }
        }
    }
    reach(g, starts, scope, out, &seen)
    own = len(out)
    for i := 0; i < len(out); i += 1 {
        for op in graph_run(g, int(out[i])) {
            if g.op[op] != .Run_Defer { continue }
            for e in graph_out(g, op) { if e.kind == .Runs { reach(g, starts, e.to, out, &seen) } }
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
    // The calls waiting for their callee's node: a call can come before its
    // callee in written order.
    calls:      [dynamic]Pending_Call,
    arena:      bool,    // the program has a scope arena: big values live on it
    runs:       [dynamic]^Run,   // every run made, freed at the end
    nodes:      int,             // how many nodes exist; the columns run ahead
    code:       Code,
    // Refers-to: the names in scope, innermost last. A fun's lookups stop at
    // fn_base (a nested fun sees none of its outer fun's locals); a defer's
    // block shares its fun's. frames holds where each open scope's names start.
    names:      [dynamic]Name_Binding,
    frames:     [dynamic]int,
    fn_base:    int,
    self:       Node_Id,         // what `Self` names in a struct's code
    program:    Node_Id,         // the synthetic scope of the compiler's globals (this_program)
    // Each module's statements, where each goes (graph_modules): built as the
    // checker settles them (graph_module_stmt), or — a scope, a type — when
    // the graph is put together.
    module_stmts: map[rawptr]int,
    module_list:  [dynamic]Graph_Module_Stmt,
    def_segs:     map[rawptr]Graph_Def_Built,   // a body's constants, built as settled
    // A compound assignment's target (its expression, by identity) and the
    // place already computed for it: its read reuses the place.
    compound:   Graph_Compound,
    // Each constant's declaration, by its value's identity, and the table
    // globals waiting to name theirs.
    const_decls: map[rawptr]Node_Id,
    tables:      [dynamic]Graph_Table,
    // Segments: a scope's contents built on their own, at any time, then put
    // where the scope is (graph_canonicalize).
    segs:    [dynamic]Graph_Segment,
    seg:     int,
    // The bodies the checker built as it checked them, by their scope, each a
    // segment: the builder puts them in place. Why one it began failed; the
    // body being built; MARA_FUSE=log.
    fused:    map[^Type_Scope]int,
    failed:   map[^Type_Scope]string,
    fuses:    [dynamic]^Graph_Fuse,
    fuse:     ^Graph_Fuse,
    fuse_log: bool,
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
    // A fused body's definitions: each built by the builder, at its anchor,
    // when the body is placed.
    defs:    [dynamic]Graph_Def,
}

@(private="file")
Graph_Def :: struct {
    s:      Stmt,
    parent: Node_Id,
    anchor: int,
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

Graph_Compound :: struct { key: rawptr, place: Operand }

@(private="file")
Graph_Table :: struct {
    global: Node_Id,
    value:  rawptr,
}

@(private="file")
Name_Binding :: struct {
    name: string,
    decl: Node_Id,
}

@(private="file")
graph_bind :: proc(b: ^Graph_Builder, name: string, decl: Node_Id) {
    if name == "" || name == "_" { return }
    append(&b.names, Name_Binding{name, decl})
}

// The declaration a name refers to here: the innermost binding of it in the
// current fun.
@(private="file")
graph_lookup :: proc(b: ^Graph_Builder, name: string) -> Node_Id {
    for i := len(b.names) - 1; i >= b.fn_base; i -= 1 {
        if b.names[i].name == name { return b.names[i].decl }
    }
    return NO_NODE
}

@(private="file")
graph_frame_push :: proc(b: ^Graph_Builder) {
    append(&b.frames, len(b.names))
}

@(private="file")
graph_frame_pop :: proc(b: ^Graph_Builder) {
    resize(&b.names, pop(&b.frames))
}

@(private="file")
Pending_Call :: struct {
    op:     Node_Id,
    callee: ^Type_Scope,
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
    nrvo:   string,               // the local built in the caller's return slot
    tuples: map[rawptr]Node_Id,   // a default's shared source call → its operation
    constructed: Node_Id,         // the last construction's operation (its outputs past Self: a fallible one's err)
    managed: bool,                // Program's: main sets up its storage, its fields build no code
}

@(private="file")
Run :: struct {
    ops:     [dynamic]Node_Id,
    waiting: [dynamic]i32,       // the `then` edges (by index) whose target is this run's first operation, once it has one
    early:   bool,               // (fused) built before what enters it: an edge into it is its first operation's
}

@(private="file")
Code_Scope :: struct {
    block:  Node_Id,
    defers: [dynamic]Node_Id,   // defer blocks registered so far, in order
    mark:   bool,               // arena mark at entry, reset at every exit
    tentative: int,             // a fused body's: its mark and resets, decided later (b.fuse.marks); -1
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
// checks it (graph_fuse_begin), and build_program_graph puts them in place.
graph_builder_new :: proc(checked: ^Checked_Program, programs: map[string]^Program) -> ^Graph_Builder {
    b := new(Graph_Builder)
    b.g = new(Program_Graph)
    b.checked = checked
    b.stmt = -1
    b.arena = checked.table.has_scope_allocator || checked.table.context_expected_at_runtime
    // MARA_FUSE=log: why the checker didn't build a body (one checked with
    // errors), and how many it built.
    b.fuse_log = os.get_env("MARA_FUSE", context.temp_allocator) == "log"
    append(&b.segs, Graph_Segment{root = NO_NODE})   // the program's own: its modules' declarations
    graph_piece_begin(b, 0)
    graph_modules(b, programs)
    return b
}

// A module's statement, and where it goes: before what its module made after
// it (an anchor in the program's segment).
Graph_Module_Stmt :: struct {
    s:      Stmt,
    module: Node_Id,
    anchor: int,
    built:  bool,
}

// The program's modules, before anything is checked: the compiler's globals
// (typed once checked), then each module's node, in name order, and a place
// for each of its statements, in written order. (One that declares nothing:
// its entry, here.)
@(private="file")
graph_modules :: proc(b: ^Graph_Builder, programs: map[string]^Program) {
    b.program = graph_node(b, .Module, .Synthetic, NO_NODE, "program", nil, {})
    for name in ([]string{"this_program", "context"}) {
        graph_node(b, .Field, .Synthetic, b.program, name, nil, {})
    }
    graph_close(b, b.program)
    modules := make([dynamic]string, 0, len(programs), context.temp_allocator)
    for name in programs { append(&modules, name) }
    slice.sort(modules[:])
    for name in modules {
        m := graph_node(b, .Module, .Explicit, NO_NODE, name, nil, {})
        // A module is a scope like a struct: its variables are its fields, which
        // no function sees (a function sees only its arguments).
        for s in programs[name]^ {
            key := stmt_key(s)
            if key == nil {
                graph_decl_stmt(b, s, m, {kind = .Field})
                continue
            }
            b.module_stmts[key] = len(b.module_list)
            append(&b.module_list, Graph_Module_Stmt{s = s, module = m, anchor = graph_anchor_here(b)})
        }
        graph_close(b, m)
    }
}

// A module's statement the checker has settled — a constant, a variable, a
// destructure: its declarations, in a segment of their own, put where the
// statement is. (Once: a statement is settled by the first pass over it.)
graph_module_stmt :: proc(b: ^Graph_Builder, s: Stmt) {
    i, is_module := b.module_stmts[stmt_key(s)]
    if !is_module || b.module_list[i].built { return }
    #partial switch _ in s {
    case ^Stmt_Define, ^Stmt_Assign, ^Stmt_Decl, ^Stmt_Multi_Assign, ^Stmt_Multi_Return_Assign:
        graph_module_build(b, &b.module_list[i])
    }
}

// (What the builder is in the middle of — a body the checker is building —
// is no module's: its code and its names are left as they are.)
@(private="file")
graph_module_build :: proc(b: ^Graph_Builder, ms: ^Graph_Module_Stmt) {
    ms.built = true
    si, saved := graph_segment_enter(b)
    code, names, base := b.code, len(b.names), b.fn_base
    b.code, b.fn_base = {}, names
    graph_decl_stmt(b, ms.s, ms.module, {kind = .Field})
    b.code, b.fn_base = code, base
    resize(&b.names, names)
    graph_segment_leave(b, saved)
    b.segs[0].anchors[ms.anchor].seg = si
}

graph_builder_free :: proc(b: ^Graph_Builder) {
    for _, list in b.by_span { delete(list) }
    delete(b.by_span)
    delete(b.calls)
    for r in b.runs {
        delete(r.ops)
        delete(r.waiting)
        free(r)
    }
    delete(b.runs)
    delete(b.names)
    delete(b.frames)
    delete(b.const_decls)
    delete(b.tables)
    for s in b.segs {
        delete(s.pieces)
        delete(s.anchors)
        delete(s.defs)
    }
    delete(b.segs)
    delete(b.fused)
    delete(b.failed)
    for f in b.fuses { graph_fuse_free(f) }
    delete(b.fuses)
    delete(b.repl)
    delete(b.drops)
    free(b.g)
    free(b)
}

build_program_graph :: proc(b: ^Graph_Builder, programs: map[string]^Program) -> Program_Graph {
    defer graph_builder_free(b)
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
        #partial switch _ in ms.s {
        case ^Stmt_Define, ^Stmt_Assign, ^Stmt_Decl, ^Stmt_Multi_Assign, ^Stmt_Multi_Return_Assign:
            graph_fatal(stmt_span(ms.s), "the checker settled no declaration here")
        }
        graph_module_build(b, &ms)
    }
    graph_piece_end(b, 0)
    // What was dropped, by node: those listed while checking, then settling's.
    if len(b.fuses) > 0 || len(b.drops) > 0 {
        b.repl = make([]Operand, b.nodes)
        slice.fill(b.repl, KEPT)
        for d in b.drops { b.repl[d[0].op] = d[1] }
    }
    for f in b.fuses { graph_fuse_settle(b, f) }
    if b.fuse_log { fmt.eprintfln("fuse: %d bodies built as they were checked", len(b.fused)) }
    graph_resize(g, b.nodes)
    append(&g.operand_first, i32(len(g.operands)))
    append(&g.run_first, i32(len(g.run_ops)))
    if len(b.segs) > 1 { graph_canonicalize(b) }
    graph_link_calls(b)
    graph_settle_literals(b)
    graph_resolve_defs(b)
    graph_link_flows(b)
    // A `then` into a run that never got an operation leads nowhere.
    kept := 0
    for e in g.edges { if e.to != NO_NODE { g.edges[kept] = e; kept += 1 } }
    resize(&g.edges, kept)
    graph_index_edges(g)
    when ODIN_DEBUG {
        graph_check_coverage(b)
        graph_check_runs(b)
        graph_check_refers(b)
    }
    graph_dump(g)
    return g^
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
// id that names one of them renumbered. (A build in written order is already
// canonical; this is for contents built out of order.)
@(private="file")
graph_canonicalize :: proc(b: ^Graph_Builder) {
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
    // What no anchor reaches is left out: a body the checker began and the
    // builder built. What a dropped operation stood for is used in its place.
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

    // The nodes' columns, and their operands.
    ng: Program_Graph
    graph_resize(&ng, len(nodes))
    for old, i in nodes {
        ng.kind[i], ng.op[i], ng.written[i] = g.kind[old], g.op[old], g.written[old]
        ng.parent[i] = re(new_id, g.parent[old])
        ng.last[i] = Node_Id(i)
        ng.name[i], ng.type_[i], ng.origin[i] = g.name[old], g.type_[old], g.origin[old]
        ng.refers[i] = re(new_id, g.refers[old])
        assert(g.stmt[old] != STMT_ANCHOR, "a segment's node was never placed")
        ng.stmt[i] = g.stmt[old] if g.stmt[old] < 0 else new_stmt[g.stmt[old]]
        assert(g.stmt[old] < 0 || ng.stmt[i] >= 0, "a node is in a statement left out")
        ng.operand_first[i] = i32(len(ng.operands))
        for o in g.operands[g.operand_first[old]:g.operand_first[old + 1]] {
            append(&ng.operands, ro(b, new_id, o))
        }
    }
    append(&ng.operand_first, i32(len(ng.operands)))
    // A subtree is one run of ids: each node's last is its last descendant's.
    for i := len(nodes) - 1; i >= 0; i -= 1 {
        if p := ng.parent[i]; p != NO_NODE && ng.last[i] > ng.last[p] { ng.last[p] = ng.last[i] }
    }
    // A run's operations in the order they are placed (a segment built
    // after what follows it in its run goes before it). What entered the
    // operation that began it — dropped, or placed after another — enters
    // the first placed (none, when there is none).
    next_kept := make(map[Node_Id]Node_Id, context.temp_allocator)
    for old in runs {
        append(&ng.run_first, i32(len(ng.run_ops)))
        start := len(ng.run_ops)
        ops := g.run_ops[g.run_first[old]:g.run_first[old + 1]]
        for op in ops {
            if !graph_dropped(b, op) { append(&ng.run_ops, re(new_id, op)) }
        }
        placed := ng.run_ops[start:]
        if !slice.is_sorted(placed) { slice.sort(placed) }
        first := Node_Id(nodes[placed[0]]) if len(placed) > 0 else NO_NODE
        for op in ops {   // (its leading dropped ones, and the first kept)
            if op != first { next_kept[op] = first }
            if !graph_dropped(b, op) { break }
        }
    }
    append(&ng.run_first, i32(len(ng.run_ops)))
    for e in g.edges {
        if !kept(new_id, e.from) { continue }
        to, written := e.to, e.written
        if to != NO_NODE && (graph_dropped(b, to) || to in next_kept) {
            to = next_kept[to] or_else NO_NODE
            if to != NO_NODE { written = g.written[to] }
        }
        append(&ng.edges, Edge{from = re(new_id, e.from), to = re(new_id, to), kind = e.kind, written = written, site = re(new_id, e.site)})
    }
    for old in stmts { append(&ng.stmts, g.stmts[old]) }
    for old in unreach { append(&ng.unreachable, g.unreachable[old]) }
    for id in g.settled { if kept(new_id, id) { append(&ng.settled, new_id[id]) } }
    slice.sort(ng.settled[:])
    for ts, id in g.scope_node { if kept(new_id, id) { ng.scope_node[ts] = new_id[id] } }
    for id, c in g.consts { if kept(new_id, id) { ng.consts[new_id[id]] = c } }
    for id, s in g.assert_sides { if kept(new_id, id) { ng.assert_sides[new_id[id]] = s } }
    for id, e in g.const_values { if kept(new_id, id) { ng.const_values[new_id[id]] = e } }

    // What the builder still holds by id.
    calls := 0
    for c in b.calls {
        if kept(new_id, c.op) { b.calls[calls] = {new_id[c.op], c.callee}; calls += 1 }
    }
    resize(&b.calls, calls)
    tables := 0
    for t in b.tables {
        if kept(new_id, t.global) { b.tables[tables] = {new_id[t.global], t.value}; tables += 1 }
    }
    resize(&b.tables, tables)
    gone := make([dynamic]rawptr, context.temp_allocator)
    for k, id in b.const_decls {
        if kept(new_id, id) { b.const_decls[k] = new_id[id] } else { append(&gone, k) }
    }
    for k in gone { delete_key(&b.const_decls, k) }
    b.program = new_id[b.program]
    b.nodes = len(nodes)
    graph_free_columns(g)
    g^ = ng
}

// The storage of a graph's columns and tables, before it is replaced.
@(private="file")
graph_free_columns :: proc(g: ^Program_Graph) {
    delete(g.kind); delete(g.op); delete(g.written); delete(g.parent); delete(g.last)
    delete(g.name); delete(g.type_); delete(g.origin); delete(g.refers); delete(g.stmt)
    delete(g.operands); delete(g.operand_first); delete(g.run_ops); delete(g.run_first)
    delete(g.edges); delete(g.out_first); delete(g.in_edges); delete(g.in_first)
    delete(g.scope_node); delete(g.stmts); delete(g.unreachable); delete(g.settled)
    delete(g.consts); delete(g.assert_sides); delete(g.const_values)
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
    g.type_[i] = t if b.fuse != nil else graph_settled(t)   // (a fused body's settle with it)
    g.origin[i] = origin
    g.refers[i] = NO_NODE
    g.stmt[i] = b.stmt
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
    resize(&g.stmt, n)
    resize(&g.operand_first, n)
}

// End a scope: its subtree is everything added since it.
@(private="file")
graph_close :: proc(b: ^Graph_Builder, id: Node_Id) {
    b.g.last[id] = Node_Id(b.nodes - 1)
}

@(private="file")
graph_fatal :: proc(span: Span, format: string, args: ..any) -> ! {
    loc := format_location(span.file, span.line, span.col) if span.file != "" else ""
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

// A statement outside any body — a module's, a body's definition: its
// declarations, and no code. (A body's code is the checker's, built as it is
// checked.)
@(private="file")
graph_decl_stmt :: proc(b: ^Graph_Builder, s: Stmt, parent: Node_Id, site: Decl_Site) {
    saved_stmt := b.stmt
    b.stmt = i32(len(b.g.stmts))
    append(&b.g.stmts, Graph_Stmt{span = stmt_span(s), kind = graph_stmt_kind(s)})
    defer b.stmt = saved_stmt
    #partial switch v in s {
    case ^Stmt_Decl:
        if site.kind == .Field {
            for name in v.names { graph_decl(b, site, parent, name, nil, v.span) }
        } else if len(v.checked) > 0 {
            for inner in v.checked { graph_decl_stmt(b, inner, parent, site) }
        } else {
            graph_fatal(v.span, "declaration of '%s' reached the graph unchecked", v.names[0])
        }
    case ^Stmt_Assign:
        t := v.env_type if v.env_type != nil else v.var_type
        if _, is_import := v.value.(^Expr_Include); is_import {
            graph_node(b, .Import, .Explicit, parent, v.name, t, v.span)
        } else if v.is_decl && v.target == nil {
            graph_decl(b, site, parent, v.name, t, v.span)
        }
        // (`this_program = Program(…)` names the program's arena, set up at
        // main's entry: it runs nothing here.)
    case ^Stmt_Multi_Assign:
        for a in v.assigns { graph_decl_stmt(b, a, parent, site) }
    case ^Stmt_Multi_Return_Assign:
        if len(v.checked) > 0 {
            for inner in v.checked { graph_decl_stmt(b, inner, parent, site) }
            break
        }
        for name, i in v.names {
            if !v.is_decl || name == "" || name == "_" { continue }
            if i < len(v.targets) && v.targets[i] != nil { continue }   // an lvalue stores
            t: Type = v.var_types[i] if i < len(v.var_types) else nil
            graph_decl(b, site, parent, name, t, v.span)
        }
    case ^Stmt_Define:
        // A constant's value is resolved before the graph: no operations.
        t := v.env_type if v.env_type != nil else v.var_type
        kind: Node_Kind = .Const
        if _, is_import := v.value.(^Expr_Include); is_import { kind = .Import }   // `core :: include mara.core`
        d := graph_node(b, kind, .Explicit, parent, v.name, t, v.span)
        if kind == .Const && v.value != nil {
            b.const_decls[expr_identity(v.value)] = d
            b.g.const_values[d] = v.value
        }
    case Stmt_Call, Stmt_Return, Stmt_Break, Stmt_Continue, Stmt_Overload, Stmt_Module:
        // Code outside a body runs nothing here; rules and headers declare
        // nothing.
    case ^Stmt_Scope:
        if v.kind == .Block {
            n := graph_node(b, .Block, .Explicit, parent, "block", nil, v.span)
            for st in v.body { graph_decl_stmt(b, st, n, {kind = .Local}) }
            graph_close(b, n)
            break
        }
        graph_scope_def(b, v, parent)
    case ^Stmt_Foreign:
        for &f in v.decls { graph_foreign(b, &f, parent) }
    case ^Stmt_Union_Def:
        graph_union(b, v, parent)
    case ^Stmt_Distinct_Def:
        d := graph_one(b, v.span, v.name)
        graph_node(b, .Type_Def, .Explicit, parent, v.name, d, v.span)
    case ^Stmt_Dispatch_Def:
        graph_node(b, .Dispatch, .Explicit, parent, v.name, nil, v.span)
    case:
        graph_fatal(stmt_span(s), "code outside a body reached the graph")
    }
}


// What a statement does to the variables it writes (Stmt_Kind).
graph_stmt_kind :: proc(s: Stmt) -> Stmt_Kind {
    #partial switch v in s {
    case ^Stmt_Assign:
        if _, is_import := v.value.(^Expr_Include); is_import { return .Other }
        if v.target != nil { return .Write }
        if v.is_decl { return .Decl }
        if v.name == "_" || v.name == "this_program" { return .Other }
        return .Assign
    case ^Stmt_Multi_Return_Assign:
        return .Destructure if len(v.checked) == 0 else .Other
    case ^Stmt_Decl:  return .Decl   // (a local's is its checked assignments; a field's, itself)
    case ^Stmt_For:   return .Loop
    case ^Stmt_If:    return .If
    case ^Stmt_Match: return .Match
    }
    return .Other
}


// Whether a statement is code, not a definition.
@(private="file")
graph_runs_code :: proc(s: Stmt) -> bool {
    #partial switch v in s {
    case ^Stmt_Scope:
        return v.kind == .Block
    case ^Stmt_Define, ^Stmt_Union_Def, ^Stmt_Distinct_Def, ^Stmt_Dispatch_Def,
         Stmt_Overload, Stmt_Module, ^Stmt_Foreign:
        return false
    }
    return true
}

// A plain declaration, as a field of the owning struct or a local / constant.
@(private="file")
graph_decl :: proc(b: ^Graph_Builder, site: Decl_Site, parent: Node_Id, name: string, t: Type, span: Span) -> Node_Id {
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
    if site.kind != .Const { graph_bind(b, name, d) }
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
@(private="file")
graph_construct_bare :: proc(b: ^Graph_Builder, dest: Operand, t: Type, span: Span) {
    #partial switch v in distinct_base(t) {
    case ^Type_Scope:
        if v.kind == .Struct && !v.is_module && constructs_bare(v) {
            graph_call_op(b, .Construct, .Synthetic, span, v, t, ..graph_default_args(b, dest, v, span))
            return
        }
    case ^Type_Fixed_Array:
        graph_op(b, .Zero, .Synthetic, span, t, "", dest)
        if st := graph_elem_struct(v.elem); st != nil && constructs_bare(st) { graph_call_op(b, .Construct, .Synthetic, span, st, v.elem, dest) }
        return
    case ^Type_Partial_Array:
        graph_op(b, .Zero, .Synthetic, span, t, "", dest)
        if st := graph_elem_struct(v.elem); st != nil && constructs_bare(st) { graph_call_op(b, .Construct, .Synthetic, span, st, v.elem, dest) }
        return
    }
    graph_op(b, .Zero, .Synthetic, span, t, "", dest)
}

// A construction written without arguments — a bare declaration, a literal —
// runs its constructor on its params' defaults (the checker lets none be
// built so without one): its operands, the place it builds in first.
@(private="file")
graph_default_args :: proc(b: ^Graph_Builder, dest: Operand, callee: ^Type_Scope, span: Span) -> []Operand {
    ops := make([]Operand, 1 + len(callee.params), context.temp_allocator)
    ops[0] = dest
    for p, i in callee.params {
        if p.default_value == nil { graph_fatal(span, "'%s' built without its argument '%s'", callee.name, p.name) }
        ops[i + 1] = graph_default_value(b, p.default_value, p.type_, span)
    }
    return ops
}

// The struct an array's elements construct, through nested arrays.
@(private="file")
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

// An index at the header width: a narrower number widens; an enum's value, its
// tag, is taken as a number.
@(private="file")
graph_index_value :: proc(b: ^Graph_Builder, e: Expr, span: Span) -> Operand {
    at := graph_leaf(b, e)
    if _, is_enum := distinct_base(expr_type(e)).(^Type_Enum); is_enum {
        return graph_op_value(b, .Cast, .Implied, span, slice_header_width_type, type_name(slice_header_width_type), at)
    }
    return graph_widen(b, at, slice_header_width_type, span)
}



// A slice, or a pointer to one.
graph_header_of :: proc(t: Type) -> bool {
    t := t
    if pt, ok := distinct_base(t).(^Type_Ptr); ok { t = pt.elem }
    _, is_slice := distinct_base(t).(^Type_Slice)
    return is_slice
}



// What a take carves from: the storage's header — `&s` is s's, a `^[]byte`
// what it points at — or, positional (`&bytes[i]`), the view of the bytes
// there as what's taken.
@(private="file")
graph_carve_storage :: proc(b: ^Graph_Builder, v: ^Expr_Take) -> Operand {
    if u, is_addr := v.storage.(^Expr_Unary); is_addr && u.op == .Ampersand {
        if ix, is_ix := u.operand.(^Expr_Index); is_ix && is_byte_buffer(expr_type(ix.expr)) {
            return graph_plain_view(b, ix, v.type_, v.span)
        }
        return graph_plain_place(b, u.operand, v.span)
    }
    return graph_plain_base(b, v.storage, v.span)
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
graph_coll_place :: proc(b: ^Graph_Builder, coll: Expr, slot: Node_Id, span: Span) -> Operand {
    if slot != NO_NODE { return graph_var(b, b.g.name[slot], slot, b.g.type_[slot], span) }
    return graph_plain_base(b, coll, span)
}

// The view a collection loop walks, when the collection has a header — a
// slice or a partial array, or a pointer to one: a slice of the same elements.
@(private="file")
graph_loop_view :: proc(coll: Expr) -> Type {
    return graph_loop_view_of(expr_type(coll))
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
graph_scope_open :: proc(b: ^Graph_Builder, block: Node_Id, body: []Stmt, span: Span) {
    graph_frame_push(b)
    // The checker opens a scope before its declarations are typed: its mark,
    // and the reset at each of its exits, are made and decided when the
    // graph is put together (main's body is no fused one's until then).
    if f := b.fuse; f != nil && b.arena && b.g.kind[block] != .Struct {
        m := Graph_Arena{mark = graph_op(b, .Arena_Mark, .Synthetic, span), block = block, body = body, nrvo = b.code.nrvo}
        append(&f.marks, m)
        append(&b.code.scopes, Code_Scope{block = block, tentative = len(f.marks) - 1})
        return
    }
    main, _ := b.checked.functions["main"]
    mark := b.arena && b.g.kind[block] != .Struct && (main == nil || b.g.type_[block] != Type(main)) && graph_has_big_values(b, body, b.code.nrvo)
    append(&b.code.scopes, Code_Scope{block = block, mark = mark, tentative = -1})
    if mark { graph_op(b, .Arena_Mark, .Synthetic, span) }
}

// Leave a scope at its end: its defers and reset, if the end is reached.
@(private="file")
graph_scope_close :: proc(b: ^Graph_Builder, span: Span) {
    if graph_reachable(b) { graph_exit_scopes(b, len(b.code.scopes) - 1, span) }
    s := pop(&b.code.scopes)
    delete(s.defers)
    graph_frame_pop(b)
}

// What leaving scopes[from:] runs, innermost first: each scope's defers, the
// last registered first, then its arena reset.
@(private="file")
graph_exit_scopes :: proc(b: ^Graph_Builder, from: int, span: Span) {
    for i := len(b.code.scopes) - 1; i >= from; i -= 1 {
        s := &b.code.scopes[i]
        for j := len(s.defers) - 1; j >= 0; j -= 1 {
            op := graph_op(b, .Run_Defer, .Synthetic, span)
            append(&b.g.edges, Edge{from = op, to = s.defers[j], kind = .Runs, written = .Synthetic, site = op})
        }
        if s.mark { graph_op(b, .Arena_Reset, .Synthetic, span) }
        if s.tentative >= 0 { append(&b.fuse.marks[s.tentative].resets, graph_op(b, .Arena_Reset, .Synthetic, span)) }
    }
}

// Whether a scope's own declarations include one that lives on the arena
// (routes_to_arena, less the local built in the caller's return slot).
@(private="file")
graph_has_big_values :: proc(b: ^Graph_Builder, body: []Stmt, nrvo: string) -> bool {
    big :: proc(a: ^Stmt_Assign, nrvo: string) -> bool {
        return a.is_decl && a.var_type != nil && a.name != nrvo && routes_to_arena(a.var_type)
    }
    for s in body {
        #partial switch v in s {
        case ^Stmt_Assign: if big(v, nrvo) { return true }
        case ^Stmt_Decl:
            for inner in v.checked {
                if a, ok := inner.(^Stmt_Assign); ok && big(a, nrvo) { return true }
            }
        }
    }
    return false
}

// --- code and runs --------------------------------------------------------

// Start the code of a fun, a struct's initializers or a defer's block: a fresh
// run, entered from `owner`. Returns the enclosing code, for graph_code_end.
@(private="file")
graph_code_begin :: proc(b: ^Graph_Builder, owner: Node_Id, nrvo: string) -> Code {
    saved := b.code
    b.code = Code{active = true, block = owner, nrvo = nrvo}
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
        w := b.g.written[to.ops[0]] if to.early else written   // (as when its operation came after)
        append(&b.g.edges, Edge{from = from, to = to.ops[0], kind = .Then, written = w, site = from})
    } else {
        // Its place among the edges now — a branch's targets keep their order
        // (yes, then no) — and its target once the run has an operation.
        append(&to.waiting, i32(len(b.g.edges)))
        append(&b.g.edges, Edge{from = from, to = NO_NODE, kind = .Then, written = written, site = from})
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

// A variable's place; `decl` is its declaration when known here (the rest are
// resolved with refers-to, next step).
graph_var :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, t: Type, span: Span) -> Operand {
    decl := decl
    if decl == NO_NODE { decl = graph_lookup(b, name) }
    op := graph_op(b, .Var, .Explicit if decl == NO_NODE else b.g.written[decl], span, t, name)
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
graph_slot :: proc(b: ^Graph_Builder, name: string, t: Type, span: Span) -> Node_Id {
    // Storage no use types (an if-expression's of a bare literal): an
    // unsettled width takes the default, as behind a pointer.
    if f := b.fuse; f != nil {
        id := graph_node(b, .Local, .Synthetic, b.code.block, name, t, span)
        append(&f.slots, id)
        return id
    }
    return graph_node(b, .Local, .Synthetic, b.code.block, name, graph_settled(t, pointee = true), span)
}

// An expression that names a place without running anything: walking it again
// gives the same place.
graph_pure_place :: proc(e: Expr) -> bool {
    #partial switch v in e {
    case ^Expr_Ident:        return v.lowered == nil || graph_pure_place(v.lowered)
    case ^Expr_Self:         return true
    case ^Expr_Field_Access: return graph_pure_place(v.expr)
    case ^Expr_Unary:        return v.op == .Caret && graph_pure_place(v.operand)
    case ^Expr_Index:
        #partial switch i in v.index {
        case ^Expr_Number, ^Expr_Ident: return graph_pure_place(v.expr)
        }
    }
    return false
}

// A leaf's value, from its check (fuse_leaf): a literal, text, an intrinsic,
// `#self`, a name, a constant or variant field. Anything else the checker
// builds as it checks it.
graph_leaf :: proc(b: ^Graph_Builder, e: Expr, w := Written.Explicit) -> Operand {
    #partial switch v in e {
    case ^Expr_Number:            return graph_const(b, w, v.span, v.type_, "", Const_Value{int = v.int_value, float = v.value, is_float = v.is_float})
    case ^Expr_Char:              return graph_const(b, w, v.span, v.type_, "", Const_Value{int = i128(v.value)})
    case ^Expr_Bool:              return graph_const(b, w, v.span, v.type_, "", Const_Value{int = 1 if v.value else 0})
    case ^Expr_Size_Of:           return graph_const(b, w, v.span, v.type_, "size_of", graph_size_of(v.resolved_type, b.checked))
    case ^Expr_Compiler_Intrinsic:
        // The caller's name or place is text; a target flag, a bool.
        if v.kind == .Caller_Name || v.kind == .Caller_Span {
            return graph_text(b, graph_op_value(b, .Global, w, v.span, v.type_), Const_Value{text = v.resolved_value, is_text = true})
        }
        return graph_const(b, w, v.span, v.type_, v.resolved_value, Const_Value{int = 1 if v.bool_value else 0})
    case ^Expr_String:            return graph_text(b, graph_op_value(b, .Global, w, v.span, v.type_), Const_Value{text = v.value, is_text = true})
    case ^Expr_Ident:
        if v.lowered != nil { return graph_leaf(b, v.lowered, w) }
        if is_void_literal(e) { return graph_op_value(b, .Const, w, v.span, v.type_, "void") }   // an uninitialized value, a null pointer
        if v.resolved != nil { return graph_leaf_resolved(b, v.resolved, v.name, v.type_, v.span, w) }
        return graph_read(b, graph_plain_place(b, e, v.span), v.type_, v.span)
    case ^Expr_Self:
        // `#self` points at the value under construction: Self's address.
        return graph_op_value(b, .Address, w, v.span, v.type_, "", graph_plain_place(b, e, v.span))
    case ^Expr_Field_Access:
        if v.resolved != nil && !graph_is_member(v.resolved) { return graph_leaf_resolved(b, v.resolved, v.field, v.type_, v.span, w) }
    }
    graph_fatal(expr_span(e)^, "the checker built no value here")
}

// A name resolved to no variable: a constant, a variant, a function.
@(private="file")
graph_leaf_resolved :: proc(b: ^Graph_Builder, r: Resolved_Name, name: string, t: Type, span: Span, w: Written) -> Operand {
    #partial switch _ in r {
    case Resolved_Enum_Variant, Resolved_Constant:
        if graph_aggregate(t) { return graph_read(b, graph_const_global(b, w, span, t, name, r), t, span) }
        return graph_named_const(b, w, span, t, name, r)
    case Resolved_Func:
        return graph_op_value(b, .Global, w, span, t, name)   // a function as a value
    case Resolved_Union_Variant:
        // Built in a temporary made first, read.
        slot := graph_slot(b, "temp", t, span)
        graph_fuse_variant(b, t, name, graph_dest_var("temp", slot, t), span)
        return graph_read(b, graph_var(b, "temp", slot, t, span), t, span)
    }
    graph_fatal(span, "'%s' resolved to no value", name)
}

// A plain place (graph_pure_place), from its check: a variable, a constant
// table, Self, text, a field, an element at a name or a number, what a
// pointer points at.
graph_plain_place :: proc(b: ^Graph_Builder, e: Expr, span: Span) -> Operand {
    if b.compound.key != nil && graph_expr_key(e) == b.compound.key { return b.compound.place }
    #partial switch v in e {
    case ^Expr_Ident:
        if v.lowered != nil { return graph_plain_place(b, v.lowered, span) }
        if v.resolved == nil { return graph_var(b, v.name, NO_NODE, v.type_, v.span) }
        if _, is_const := v.resolved.(Resolved_Constant); is_const && graph_aggregate(v.type_) {
            return graph_const_global(b, .Explicit, v.span, v.type_, v.name, v.resolved)   // a constant table
        }
    case ^Expr_Self:
        return graph_var(b, "Self", b.self, graph_pointee(v.type_), v.span)   // Self itself
    case ^Expr_String:
        return graph_text(b, graph_op_value(b, .Global, .Explicit, v.span, v.type_), Const_Value{text = v.value, is_text = true})
    case ^Expr_Field_Access:
        if v.resolved == nil || graph_is_member(v.resolved) {
            base := graph_plain_base(b, v.expr, v.span)
            base_t := graph_pointee(expr_type(v.expr))
            if _, is_array := distinct_base(base_t).(^Type_Fixed_Array); is_array {
                return graph_op_value(b, .Swizzle, .Explicit, v.span, v.type_, v.field, base)
            }
            return graph_op_value(b, .Field, .Explicit, v.span, v.type_, v.field, base)
        }
        if _, is_const := v.resolved.(Resolved_Constant); is_const && graph_aggregate(v.type_) {
            return graph_const_global(b, .Explicit, v.span, v.type_, v.field, v.resolved)   // a module's constant table
        }
    case ^Expr_Index:
        // Bytes indexed as another type (a byte read at an argument): a view.
        if _, of_byte := distinct_base(v.type_).(Type_Byte); !of_byte && v.type_ != nil && !is_infer(v.type_) && is_byte_buffer(expr_type(v.expr)) {
            return graph_plain_view(b, v, v.type_, v.span)
        }
        base := graph_plain_base(b, v.expr, v.span)
        return graph_op_value(b, .Index, .Explicit, v.span, v.type_, "", base, graph_index_value(b, v.index, v.span))
    case ^Expr_Unary:
        if v.op == .Caret {
            return graph_op_value(b, .Deref, .Explicit, v.span, v.type_, "", graph_plain_place(b, v.operand, v.span))
        }
    }
    graph_fatal(expr_span(e)^, "the checker built no place here")
}

// A plain place's base: through a pointer, what it points at (one level of
// automatic dereference).
graph_plain_base :: proc(b: ^Graph_Builder, e: Expr, span: Span) -> Operand {
    p := graph_plain_place(b, e, span)
    if _, is_self := e.(^Expr_Self); is_self { return p }   // through `#self` is Self
    if pt, ok := distinct_base(expr_type(e)).(^Type_Ptr); ok {
        return graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)
    }
    return p
}

// Bytes at a plain index seen as a `t` (graph_view_place).
@(private="file")
graph_plain_view :: proc(b: ^Graph_Builder, ix: ^Expr_Index, t: Type, span: Span) -> Operand {
    base := graph_plain_base(b, ix.expr, span)
    at := graph_widen(b, graph_leaf(b, ix.index), slice_header_width_type, span)
    return graph_op_value(b, .View, .Explicit, span, t, "#big_endian" if ix.is_big_endian else "", base, at)
}



// A tag or padding access names part of the value (a place); variants,
// constants and functions don't.
graph_is_member :: proc(r: Resolved_Name) -> bool {
    #partial switch _ in r {
    case Resolved_Union_Tag, Resolved_Union_Pad: return true
    }
    return false
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







// The call's results, each written to its field (graph_spread_writes).
graph_spread_results :: proc(b: ^Graph_Builder, v: ^Expr_Struct_Literal, sd: ^Scope_Body, parent: ^Dest, callee: ^Type_Scope, c: Operand) {
    for rt, i in callee.return_types {
        if i >= len(sd.fields) { break }
        f := sd.fields[i]
        val := Operand{c.op, i32(i)}
        _, to_slice := distinct_base(f.type_).(^Type_Slice)
        if _, from_array := distinct_base(rt).(^Type_Fixed_Array); to_slice && from_array {
            slot := graph_slot(b, "temp", rt, v.span)
            graph_op(b, .Write, .Explicit, v.span, nil, "", graph_var(b, "temp", slot, rt, v.span), val)
            val = graph_op_value(b, .Slice, .Implied, v.span, f.type_, "", graph_var(b, "temp", slot, rt, v.span))
        }
        field := graph_dest_place(b, Dest{kind = .Field, name = f.name, type_ = f.type_, parent = parent}, v.span)
        graph_op(b, .Write, .Explicit, v.span, nil, "", field, val)
    }
}

// A union's variant `name` as a struct: its tag first, then its fields; nil
// when t is no union with that variant.
@(private="file")
graph_variant_struct :: proc(b: ^Graph_Builder, t: Type, name: string) -> ^Type_Scope {
    ut, is_union := distinct_base(t).(^Type_Union)
    if !is_union || name == "" { return nil }
    sname, has := ut.variant_structs[name]
    if !has { return nil }
    return b.checked.table.structs[sname] or_else nil
}

// A variant built at d: after its construct (zero and its tag), each field
// default the literal doesn't give — a variant has no constructor to run them.
@(private="file")
graph_variant_defaults :: proc(b: ^Graph_Builder, t: Type, variant: string, lit: ^Expr_Struct_Literal, d: Dest, span: Span) {
    st := graph_variant_struct(b, t, variant)
    if st == nil { return }
    dd := d
    graph_field_defaults(b, st, lit, Dest{kind = .Variant, name = variant, type_ = st, parent = &dd}, span)
}

// Each field default of variant struct st a literal doesn't give, written at
// the struct's place d.
@(private="file")
graph_field_defaults :: proc(b: ^Graph_Builder, st: ^Type_Scope, lit: ^Expr_Struct_Literal, d: Dest, span: Span) {
    sd := as_scope_body(st)
    vd := d
    skip := 0
    for f in sd.fields { if strings.has_prefix(f.name, "__") { skip += 1 } }
    for f, i in sd.fields {
        if f.default_value == nil { continue }
        given := false
        if lit != nil {
            for lf, j in lit.fields {
                if lf.name == f.name || (lf.name == "" && skip + j == i) { given = true }
            }
        }
        if given { continue }
        val := graph_default_value(b, f.default_value, f.type_, span)
        fd := Dest{kind = .Field, name = f.name, type_ = f.type_, parent = &vd}
        graph_op(b, .Write, .Implied, span, nil, "", graph_dest_place(b, fd, span), val)
    }
}

// A default — a variant's field's, a constructor param's — where it's used:
// it isn't checked where it's declared, so a constant one is written at the
// type it defaults; else it is a leaf (text, a name), at that type.
@(private="file")
graph_default_value :: proc(b: ^Graph_Builder, e: Expr, t: Type, span: Span) -> Operand {
    c, folds := graph_literal_value(e).?
    if dt := expr_type(e); folds && !c.is_text && (dt == nil || is_infer(dt)) {
        return graph_const(b, .Implied, span, t, "", c)
    }
    return graph_widen(b, graph_leaf(b, e, .Implied), t, span)
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
graph_try_after :: proc(b: ^Graph_Builder, v: ^Expr_Try, inner: Operand) -> Operand {
    n := graph_outputs(b, v.inner)
    if n == 0 { graph_fatal(v.span, "`?` on a call with no err output") }
    err := Operand{graph_outputs_op(b, v.inner, inner), i32(n - 1)}
    fail, ok := graph_run_new(b), graph_run_new(b)
    failed := graph_op_value(b, .Cast, .Implied, v.span, Type_Bool{}, "bool", err)   // an error: nonzero
    graph_branch(b, failed, fail, ok, .Implied, v.span)
    b.code.run = fail
    // It returns the err, and each other result's zero value (implied).
    rts := graph_result_types(b)
    vals := make([dynamic]Operand, 0, len(rts), context.temp_allocator)
    for i in 0 ..< len(rts) - 1 { append(&vals, graph_const(b, .Implied, v.span, rts[i], "zero", Const_Value{})) }
    append(&vals, err)
    graph_exit_scopes(b, 0, v.span)
    graph_op(b, .Return, .Implied, v.span, nil, "", ..vals[:])
    graph_run_close(b)
    b.code.run = ok
    if n == 1 { return NO_VALUE }   // err only
    return inner
}

// The operation whose outputs a call's value `v` is the first of: the call; a
// fallible construction's, its construct (the value is the built place, read).
@(private="file")
graph_outputs_op :: proc(b: ^Graph_Builder, e: Expr, v: Operand) -> Node_Id {
    if call, is_call := e.(^Expr_Call); is_call {
        if rf, ok := call.resolved_func.?; ok {
            if callee := graph_callee(b, rf); callee != nil && callee.kind == .Struct { return b.code.constructed }
        }
    }
    return v.op
}

// How many outputs a call has: its callee's return list (a fallible
// constructor's includes the struct itself).
@(private="file")
graph_outputs :: proc(b: ^Graph_Builder, e: Expr) -> int {
    call, ok := e.(^Expr_Call)
    if !ok { return 0 }
    rf, resolved := call.resolved_func.?
    if !resolved { return 0 }
    callee := graph_callee(b, rf)
    if callee == nil { return 0 }
    if list, is_ctor := constructor_effective_returns(callee); is_ctor { return len(list) }
    return len(callee.return_types)
}



// The fun or struct a resolved call runs. Casts and distinct conversions
// resolve to none: they are no call.
graph_callee :: proc(b: ^Graph_Builder, rf: Resolved_Func) -> ^Type_Scope {
    if rf.callee != nil || rf.name == "" { return rf.callee }
    // Resolved by name only (qualified, UFCS, dispatch): look the name up.
    if ft, ok := b.checked.table.funs[rf.name]; ok    { return ft }
    if st, ok := b.checked.table.structs[rf.name]; ok { return st }
    return nil
}

// A call or construct operation, with a Calls edge to what it runs.
graph_call_op :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, callee: ^Type_Scope, t: Type, operands: ..Operand) -> Node_Id {
    op := graph_op(b, kind, w, span, t, graph_call_name(callee), ..operands)
    append(&b.calls, Pending_Call{op = op, callee = callee})
    // (An instance's name is known once checking is done.)
    if f := b.fuse; f != nil { append(&f.calls, Pending_Call{op = op, callee = callee}) }
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

// A constant operation, with its value when it has one.
graph_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, value: Maybe(Const_Value)) -> Operand {
    o := graph_op_value(b, .Const, w, span, t, name)
    if v, ok := value.?; ok {
        b.g.consts[o.op] = v
        if is_infer(t) {
            if f := b.fuse; f != nil {
                append(&f.consts, o.op)   // its width is known when its body's are
            } else if !is_infer(b.g.type_[o.op]) {
                append(&b.g.settled, o.op)   // a width its `:=` adopted
            }
        }
    }
    return o
}

// The value a name resolved to a constant stands for: an enum variant's, or a
// named constant's when it is a literal (or names one). Others have none here.
@(private="file")
graph_const_value :: proc(r: Resolved_Name, checked: ^Checked_Program = nil) -> Maybe(Const_Value) {
    #partial switch v in r {
    case Resolved_Enum_Variant:
        return Const_Value{int = i128(v.value)}
    case Resolved_Constant:
        if v.value_expr == nil { return Const_Value{int = i128(v.int_value)} }
        return graph_literal_value(v.value_expr, checked)
    }
    return nil
}

// Whether a value written into a partial array fills only a prefix of it: a
// string constant, or a slice.
graph_fills_prefix :: proc(value: Expr) -> bool {
    if _, is_slice := distinct_base(expr_type(value)).(^Type_Slice); is_slice { return true }
    #partial switch v in value {
    case ^Expr_String:       return true
    case ^Expr_Ident:
        if c, ok := graph_const_value(v.resolved).?; ok { return c.is_text }
    case ^Expr_Field_Access:
        if c, ok := graph_const_value(v.resolved).?; ok { return c.is_text }
    }
    return false
}

// A named register-value constant where it's used: its value. One computed
// from floats (`TWO_PI :: PI * 2`) is computed at the precision of the type
// it's used at; one the graph can't fold (a union's size) is its
// expression's operations, run here.
@(private="file")
graph_named_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, r: Resolved_Name) -> Operand {
    value := graph_const_value(r, b.checked)
    rc, is_const := r.(Resolved_Constant)
    if !is_const || value != nil || rc.value_expr == nil { return graph_const(b, w, span, t, name, value) }
    if ir := llvm_type_from_checker(t); ir == "double" || ir == "float" {
        if x, folds := graph_fold_float(rc.value_expr, ir == "float"); folds {
            return graph_const(b, w, span, t, name, Const_Value{float = x, is_float = true})
        }
    }
    graph_fatal(span, "the constant '%s' has no value the graph can evaluate", name)
}

// A constant float expression's value, each step rounded to single precision
// when it's used as one — as its arithmetic would be done there. (Rounding a
// double result to single is the single result: a double holds more than
// twice the digits.)
@(private="file")
graph_fold_float :: proc(e: Expr, single: bool) -> (x: f64, ok: bool) {
    at :: proc(x: f64, single: bool) -> f64 { return f64(f32(x)) if single else x }
    #partial switch v in e {
    case ^Expr_Number:
        return at(v.value if v.is_float else f64(v.int_value), single), true
    case ^Expr_Unary:
        if v.op != .Minus { return 0, false }
        n := graph_fold_float(v.operand, single) or_return
        return -n, true
    case ^Expr_Binary:
        if _, overloaded := v.overload_fn.?; overloaded { return 0, false }
        l := graph_fold_float(v.left, single) or_return
        r := graph_fold_float(v.right, single) or_return
        #partial switch v.op {
        case .Plus:  return at(l + r, single), true
        case .Minus: return at(l - r, single), true
        case .Star:  return at(l * r, single), true
        case .Slash: if r != 0 { return at(l / r, single), true }
        }
    case ^Expr_Ident:
        if rc, ok := v.resolved.(Resolved_Constant); ok && rc.value_expr != nil { return graph_fold_float(rc.value_expr, single) }
    case ^Expr_Field_Access:
        if rc, ok := v.resolved.(Resolved_Constant); ok && rc.value_expr != nil { return graph_fold_float(rc.value_expr, single) }
    }
    return 0, false
}

// A string constant's global carries its text in the constants table.
@(private="file")
graph_text :: proc(b: ^Graph_Builder, global: Operand, value: Maybe(Const_Value)) -> Operand {
    if c, ok := value.?; ok && c.is_text { b.g.consts[global.op] = c }
    return global
}

// A named constant held in memory: text, or a table — which names its
// declaration (once every one is built: a use can come first).
@(private="file")
graph_const_global :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, r: Resolved_Name) -> Operand {
    o := graph_text(b, graph_op_value(b, .Global, w, span, t, name), graph_const_value(r))
    if rc, ok := r.(Resolved_Constant); ok && rc.value_expr != nil {
        append(&b.tables, Graph_Table{o.op, expr_identity(rc.value_expr)})
    }
    return o
}

// A constant expression's value, as the graph folds constants — for what's
// computed before any code runs (the program arena's size) or in no code of
// its own (an array element's constructor defaults).
graph_constant :: proc(e: Expr) -> Maybe(Const_Value) {
    return graph_literal_value(e)
}

@(private="file")
graph_literal_value :: proc(e: Expr, checked: ^Checked_Program = nil) -> Maybe(Const_Value) {
    #partial switch v in e {
    case ^Expr_Number: return Const_Value{int = v.int_value, float = v.value, is_float = v.is_float}
    case ^Expr_Char:   return Const_Value{int = i128(v.value)}
    case ^Expr_Bool:   return Const_Value{int = 1 if v.value else 0}
    case ^Expr_String: return Const_Value{text = v.value, is_text = true}
    case ^Expr_Unary:
        if v.op != .Minus { return nil }
        x, ok := graph_literal_value(v.operand, checked).?
        if !ok { return nil }
        return Const_Value{int = -x.int, float = -x.float, is_float = x.is_float}
    case ^Expr_Ident:          return graph_const_value(v.resolved, checked)
    case ^Expr_Field_Access:   return graph_const_value(v.resolved, checked)
    case ^Expr_Size_Of:        return graph_size_of(v.resolved_type, checked)   // (a union's, laid out)
    case ^Expr_Binary:
        // Integer arithmetic of constants (`KB :: 1 << 10`): its value.
        if _, overloaded := v.overload_fn.?; overloaded { return nil }
        l, lok := graph_literal_value(v.left, checked).?
        r, rok := graph_literal_value(v.right, checked).?
        if !lok || !rok || l.is_float || r.is_float || l.is_text || r.is_text { return nil }
        x: i128
        #partial switch v.op {
        case .Plus:      x = l.int + r.int
        case .Minus:     x = l.int - r.int
        case .Star:      x = l.int * r.int
        case .Ampersand: x = l.int & r.int
        case .Pipe:      x = l.int | r.int
        case .Tilde:     x = l.int ~ r.int
        case .Slash:     if r.int == 0 { return nil }; x = l.int / r.int   // (truncating, as the code's)
        case .Modulo:    if r.int == 0 { return nil }; x = l.int % r.int
        case .Shift_Left, .Shift_Right:
            if r.int < 0 || r.int > 63 { return nil }
            x = l.int << uint(r.int) if v.op == .Shift_Left else l.int >> uint(r.int)
        case:            return nil
        }
        if x < -(i128(1) << 63) || x >= i128(1) << 64 { return nil }
        return Const_Value{int = x}
    case ^Expr_Call:
        // A conversion of a constant: its value, when the type holds it.
        args := call_args(v)
        if len(args) != 1 || !graph_converts(v) { return nil }
        x, ok := graph_literal_value(args[0], checked).?
        if !ok { return nil }
        return graph_fits(x, v.type_)
    }
    return nil
}

// A type's size in bytes, by Mara's layout (a union's by its variants', which
// the program's structs give).
@(private="file")
graph_size_of :: proc(t: Type, checked: ^Checked_Program = nil) -> Maybe(Const_Value) {
    if t == nil { return nil }
    if _, is_union := distinct_base(t).(^Type_Union); is_union {
        if checked == nil { return nil }
        return Const_Value{int = i128(elem_byte_size(llvm_type_from_checker(t), checked))}
    }
    return Const_Value{int = i128(checker_type_byte_size(t))}
}

// Whether a call converts its argument: a numeric cast, or to a distinct type.
@(private="file")
graph_converts :: proc(v: ^Expr_Call) -> bool {
    name := call_name(v)
    if _, is_cast := cast_result_type(name); is_cast { return true }
    rf, resolved := v.resolved_func.?
    d, is_distinct := v.type_.(^Type_Distinct)
    return resolved && rf.callee == nil && is_distinct && (d.source_name == name || d.name == name)
}

// Constant x as a value of type t, when t holds it exactly.
@(private="file")
graph_fits :: proc(x: Const_Value, t: Type) -> Maybe(Const_Value) {
    #partial switch n in distinct_base(t) {
    case Type_Numeric:
        if n.kind == .Float { return Const_Value{float = x.float if x.is_float else f64(x.int), is_float = true} }
        if x.is_float { return nil }
        lo, hi: i128 = 0, (i128(1) << uint(n.bits)) - 1
        if n.kind == .Signed { lo, hi = -(i128(1) << uint(n.bits - 1)), (i128(1) << uint(n.bits - 1)) - 1 }
        if x.int < lo || x.int > hi { return nil }
        return x
    case Type_F64:
        return Const_Value{float = x.float if x.is_float else f64(x.int), is_float = true}
    }
    return nil
}


// An assignment target's identity: its node.
@(private="file")
graph_expr_key :: proc(e: Expr) -> rawptr {
    #partial switch v in e {
    case ^Expr_Field_Access: return v
    case ^Expr_Index:        return v
    case ^Expr_Unary:        return v
    }
    return nil
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
    case .Not, .Bang:    return "not"
    }
    return "?"
}

// A literal's type is what its use takes: the checker leaves one whose width
// its context decides (`n + 1`, `x : u8 = 7`) as infer_int or infer_float.
// An operation comes after its operands, so walking back from the last one
// types each use before its operands. What no use decides takes the default.
@(private="file")
graph_settle_literals :: proc(b: ^Graph_Builder) {
    g := b.g
    callee: map[Node_Id]^Type_Scope
    defer delete(callee)
    for c in b.calls { callee[c.op] = c.callee }
    for i := b.nodes - 1; i >= 0; i -= 1 {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        for o, k in graph_operands(g, id) {
            // A literal of no type yet — a number, or an untyped `void` (its
            // use's pointer: `p == void`, an argument) — takes its use's.
            if o.op == NO_NODE || o.out != 0 { continue }
            untyped_void := g.op[o.op] == .Const && g.name[o.op] == "void" && is_any(g.type_[o.op])
            if !is_infer(g.type_[o.op]) && !untyped_void { continue }
            if t := graph_literal_use(g, callee, id, k); t != nil && !is_infer(t) {
                g.type_[o.op] = t
                if g.op[o.op] == .Const && o.op in g.consts { append(&g.settled, o.op) }
            }
        }
        if is_infer(g.type_[id]) { g.type_[id] = solidify_type(g.type_[id]) }
    }
}

// The type an operation takes its k-th operand at, when that decides a
// literal's; nil when it doesn't.
@(private="file")
graph_literal_use :: proc(g: ^Program_Graph, callee: map[Node_Id]^Type_Scope, id: Node_Id, k: int) -> Type {
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
        if c, ok := callee[id]; ok && k < len(c.params) { return c.params[k].type_ }
    case .Construct:   // its first operand is where it builds
        if c, ok := callee[id]; ok && k >= 1 && k - 1 < len(c.params) { return c.params[k - 1].type_ }
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

// Every call's edge, once all the funs and structs have nodes.
@(private="file")
graph_link_calls :: proc(b: ^Graph_Builder) {
    for c in b.calls {
        to, ok := b.g.scope_node[c.callee]
        if !ok { graph_fatal(b.g.origin[c.op], "'%s' calls '%s', which has no node", b.g.name[c.op], c.callee.name) }
        append(&b.g.edges, Edge{from = c.op, to = to, kind = .Calls, written = b.g.written[c.op], site = c.op})
    }
}

// A name no local binds names a definition: a constant, a function, a type.
// Definitions are visible wherever their scope is, before or after the line
// that writes them, so these resolve once every scope is built: the
// definition of that name in the nearest enclosing scope. A module's
// variables are locals, not definitions: no function sees them.
@(private="file")
graph_resolve_defs :: proc(b: ^Graph_Builder) {
    g := b.g
    Key :: struct { scope: Node_Id, name: string }
    defs: map[Key]Node_Id
    defer delete(defs)
    for k, id in g.kind {
        p := g.parent[id]
        if p == NO_NODE { continue }
        #partial switch k {
        case .Const, .Import, .Fun, .Struct, .Union, .Enum, .Type_Def, .Dispatch:
            if g.kind[p] == .Union { continue }   // a variant's struct is named through its union
        case .Field:
            if p != b.program { continue }        // the compiler's own this_program, context
        case:
            continue
        }
        key := Key{p, g.name[id]}
        if key not_in defs { defs[key] = Node_Id(id) }
    }
    for k, id in g.kind {
        if k != .Op || g.op[id] != .Var || g.refers[id] != NO_NODE { continue }
        for p := g.parent[id]; p != NO_NODE; p = g.parent[p] {
            if d, ok := defs[Key{p, g.name[id]}]; ok {
                g.refers[id] = d
                break
            }
        }
        if g.refers[id] == NO_NODE {
            if d, ok := defs[Key{b.program, g.name[id]}]; ok { g.refers[id] = d }
        }
    }
    // A constant table's global names the declaration of its value.
    for t in b.tables {
        if d, ok := b.const_decls[t.value]; ok { g.refers[t.global] = d }
    }
}

// The flow index: a Flows edge from each declaration a value is read from to
// the declaration it moves into, at the operation that moves it — a write
// (or fill, byte read), a call's arguments into its callee's params, a return
// into its fun's results, a match arm's binding. Field-insensitive: `p.x = v`
// flows into p.
@(private="file")
graph_link_flows :: proc(b: ^Graph_Builder) {
    g := b.g
    // Each fun's and struct's params and results, in order, and each call's callee.
    params, results: map[Node_Id][dynamic]Node_Id
    callee: map[Node_Id]Node_Id
    defer {
        for _, l in params { delete(l) }
        for _, l in results { delete(l) }
        delete(params)
        delete(results)
        delete(callee)
    }
    for k, id in g.kind {
        if k != .Param && k != .Result { continue }
        list := &params if k == .Param else &results
        p := g.parent[id]
        if p not_in list { list[p] = {} }
        append(&list[p], Node_Id(id))
    }
    for c in b.calls { callee[c.op] = b.g.scope_node[c.callee] }

    srcs: [dynamic]Node_Id
    defer delete(srcs)
    flow :: proc(g: ^Program_Graph, srcs: []Node_Id, to: Node_Id, site: Node_Id) {
        if to == NO_NODE { return }
        for s in srcs { append(&g.edges, Edge{from = s, to = to, kind = .Flows, written = g.written[site], site = site}) }
    }
    for id in 0 ..< b.nodes {
        if g.kind[id] != .Op { continue }
        op := Node_Id(id)
        ops := graph_operands(g, op)
        #partial switch g.op[id] {
        case .Write, .Fill, .Byte_Read:
            clear(&srcs)
            for o in ops[1:] { graph_sources(g, callee, results, o, &srcs) }
            flow(g, srcs[:], graph_root(g, ops[0]), op)
        case .Call, .Construct:
            to, ok := callee[op]
            if !ok { continue }
            ps := params[to]
            args := ops[1:] if g.op[id] == .Construct else ops   // a construction's first operand is its destination
            for a, i in args {
                if i >= len(ps) { break }
                clear(&srcs)
                graph_sources(g, callee, results, a, &srcs)
                flow(g, srcs[:], ps[i], op)
            }
        case .Return:
            fun := graph_code_owner(g, op)
            rs := results[fun]
            for o, i in ops {   // (an operand for each result)
                if i >= len(rs) { break }
                clear(&srcs)
                graph_sources(g, callee, results, o, &srcs)
                flow(g, srcs[:], rs[i], op)
            }
        case .Variant:
            if bound := g.refers[id]; bound != NO_NODE {
                clear(&srcs)
                if s := graph_root(g, ops[0]); s != NO_NODE { append(&srcs, s) }
                flow(g, srcs[:], bound, op)
            }
        }
    }
}

// The declarations a value is read from: each variable in it (a place's own
// operands included, so `a[i]` reads a and i), and a call's result for a
// call's output. Constants and globals name no declaration.
@(private="file")
graph_sources :: proc(g: ^Program_Graph, callee: map[Node_Id]Node_Id, results: map[Node_Id][dynamic]Node_Id,
                      o: Operand, out: ^[dynamic]Node_Id) {
    if o.op == NO_NODE { return }
    #partial switch g.op[o.op] {
    case .Var:
        if r := g.refers[o.op]; r != NO_NODE && !slice.contains(out[:], r) { append(out, r) }
    case .Call, .Construct:
        // A call's value is its callee's result; its arguments flow into the
        // callee's params, not into this value. (A construction's outputs are
        // Self, then its declared results.)
        k := int(o.out)
        if g.op[o.op] == .Construct { k -= 1 }
        if c, ok := callee[o.op]; ok && k >= 0 {
            if rs, has := results[c]; has && k < len(rs) && !slice.contains(out[:], rs[k]) {
                append(out, rs[k])
            }
        }
    case .Const, .Global:
    case:
        for x in graph_operands(g, o.op) { graph_sources(g, callee, results, x, out) }
    }
}

// The declaration a place belongs to: its variable, through fields,
// elements and one pointer (field-insensitive).
@(private="file")
graph_root :: proc(g: ^Program_Graph, p: Operand) -> Node_Id {
    for id := p.op; id != NO_NODE; {
        #partial switch g.op[id] {
        case .Var:
            return g.refers[id]
        case .Field, .Index, .View, .Swizzle, .Variant, .Slice, .Deref:
            id = graph_operands(g, id)[0].op
        case:
            return NO_NODE
        }
    }
    return NO_NODE
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

// Sort the edge table by `from` and index both directions (counting sorts:
// one pass each).
@(private="file")
graph_index_edges :: proc(g: ^Program_Graph) {
    n := len(g.kind)
    resize(&g.out_first, n + 1)
    resize(&g.in_first, n + 1)
    slice.zero(g.out_first[:])
    slice.zero(g.in_first[:])
    for e in g.edges {
        g.out_first[e.from + 1] += 1
        g.in_first[e.to + 1] += 1
    }
    for i in 1 ..= n {
        g.out_first[i] += g.out_first[i - 1]
        g.in_first[i] += g.in_first[i - 1]
    }
    sorted := make([dynamic]Edge, len(g.edges))
    next := slice.clone(g.out_first[:n], context.temp_allocator)
    for e in g.edges {
        sorted[next[e.from]] = e
        next[e.from] += 1
    }
    delete(g.edges)
    g.edges = sorted
    resize(&g.in_edges, len(g.edges))
    next_in := slice.clone(g.in_first[:n], context.temp_allocator)
    for e, i in g.edges {
        g.in_edges[next_in[e.to]] = i32(i)
        next_in[e.to] += 1
    }
}

// --- scopes -------------------------------------------------------------------

// The one checked type a non-generic declaration resolved to.
@(private="file")
graph_one :: proc(b: ^Graph_Builder, span: Span, name: string) -> Type {
    list, ok := b.by_span[span]
    if !ok || len(list) != 1 {
        graph_fatal(span, "'%s' should have one checked type, has %d", name, len(list) if ok else 0)
    }
    return list[0]
}


// A fun or struct: its node, for each type it was checked as (a generic's
// instances), its body put in place.
@(private="file")
graph_scope_def :: proc(b: ^Graph_Builder, s: ^Stmt_Scope, parent: Node_Id) {
    generic := len(s.generic_params) > 0
    list, ok := b.by_span[s.span]
    if !ok {
        if generic { return }   // a generic nothing instantiates: syntax only
        graph_fatal(s.span, "'%s' reached the graph unchecked", scope_name(s))
    }
    for t in list {
        ts, is_scope := t.(^Type_Scope)
        if !is_scope || ts.is_module { continue }
        graph_scope_node(b, ts, s, parent, .Synthetic if generic else .Explicit)
    }
}

// A fun or struct: its params and results, then its code — a fun's body, a
// struct's field initializers — in a scope of its own.
@(private="file")
graph_scope_node :: proc(b: ^Graph_Builder, ts: ^Type_Scope, s: ^Stmt_Scope, parent: Node_Id, written: Written) {
    // Built by the checker: put in place. (The graph is built from a clean
    // check: every body was.)
    si, fused := b.fused[ts]
    if !fused {
        why, began := b.failed[ts]
        graph_fatal(s.span, "the checker built no graph of '%s'%s", graph_scope_name(ts, s, written), fmt.tprintf(": %s", why) if began else "")
    }
    graph_fuse_place(b, si, parent, graph_scope_name(ts, s, written))
}

// A fun's or struct's node. (One in a segment of its own is named where it
// is placed.)
@(private="file")
graph_scope_root :: proc(b: ^Graph_Builder, ts: ^Type_Scope, s: ^Stmt_Scope, parent: Node_Id, written: Written, name := "") -> Node_Id {
    kind: Node_Kind = .Fun if ts.kind == .Fun else .Struct
    n := graph_node(b, kind, written, parent, name, ts, s.span)
    b.g.scope_node[ts] = n
    return n
}

// A scope's name: as written, or an instance's, from its mangled one.
@(private="file")
graph_scope_name :: proc(ts: ^Type_Scope, s: ^Stmt_Scope, written: Written) -> string {
    return s.name if written == .Explicit else ask_demangle(ts.name, ts.home_package)
}

// --- bodies the checker builds ------------------------------------------------

// A fun's body the checker builds as it checks it (design/graph_retrofit.md,
// phase 4): its scope's node and contents, in a segment of their own, put in
// place when the builder meets the scope. The checker finishes bodies out of
// order — a nested definition's before its parent's code, a generic's
// instance at its first call — and each is placed where it goes.
//
// Where the checker can't build something yet, the body is the builder's, as
// it was: built from the annotations, and this segment left out.
Graph_Fuse :: struct {
    seg, outer: int,
    stmt:       i32,           // the enclosing build's statement, as it was
    ts:         ^Type_Scope,
    root:       Node_Id,
    contents:   Graph_Contents,
    compound:   Graph_Compound,
    outer_fuse: ^Graph_Fuse,
    // Each statement's entry, made the first time the checker meets it (it
    // meets one in each of its passes).
    stmts:      map[rawptr]i32,
    // Types are settled when the graph is put together, as the builder types
    // what it builds after checking: a `:=` binding's width is the one it
    // adopts from a later use, a param's default's once its fun is checked.
    // Synthetic locals settle as behind a pointer; constants whose width a
    // binding settles are listed in g.settled; a widening is kept or dropped.
    slots:      [dynamic]Node_Id,
    consts:     [dynamic]Node_Id,
    widens:     [dynamic]Graph_Widen,
    checks:     [dynamic]Graph_Check,
    marks:      [dynamic]Graph_Arena,
    allocs:     [dynamic]Graph_Alloc,
    calls:      [dynamic]Pending_Call,   // named by their callees when the graph is put together
    steps:      [dynamic]int,            // its loops' steps' segments
    // A struct's: each field declaration's lowered assignment, and its field.
    fields:     map[rawptr]Node_Id,
    field_inits: map[rawptr]Expr,   // (its initializer as written)
    field_outs: map[rawptr][]Node_Id,   // fields from one call's outputs: their destructure's declarations
    failed:     string,
}

// A scope's arena mark and the resets at its exits, made where the builder
// makes them, kept when its declarations turn out to hold a value on the
// arena (graph_scope_open).
Graph_Arena :: struct {
    mark:   Node_Id,
    resets: [dynamic]Node_Id,
    block:  Node_Id,
    body:   []Stmt,
    nrvo:   string,
}

// A local's space on the arena (graph_init), made before its value: kept
// when its type turns out to route there.
Graph_Alloc :: struct {
    decl, var, alloc: Node_Id,
    nrvo:             string,
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
    // A value at a param's type chosen after it is built (graph_value_as, for
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

// Start building a fun's body as the checker checks it. `body` is the body
// checked (an instance's own copy).
graph_fuse_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, s: ^Stmt_Scope, body: []Stmt, written: Written) -> ^Graph_Fuse {
    f := new(Graph_Fuse)
    f.ts, f.outer_fuse, f.compound = ts, b.fuse, b.compound
    b.fuse, b.compound = f, {}
    f.seg, f.outer = graph_segment_enter(b)
    f.stmt, b.stmt = b.stmt, STMT_ANCHOR
    f.root = graph_scope_root(b, ts, s, NO_NODE, written)
    b.segs[f.seg].root = f.root
    f.contents = graph_contents_begin(b, ts, s, f.root, body)
    return f
}

// Leave what the checker couldn't build to the builder: the rest of the body
// is checked without building, and its segment is dropped.
graph_fuse_fail :: proc(b: ^Graph_Builder, f: ^Graph_Fuse, reason: string) {
    if f.failed == "" { f.failed = reason }
}

// The body is checked: finish it, settle its types and keep it for the
// builder to put in place — or, if it failed, drop it.
graph_fuse_end :: proc(b: ^Graph_Builder, f: ^Graph_Fuse) {
    graph_contents_end(b, f.contents, finish = f.failed == "")
    ok := f.failed == ""   // (its end can find what it can't build: a scope's values on the arena)
    b.stmt = f.stmt
    graph_segment_leave(b, f.outer)
    b.fuse, b.compound = f.outer_fuse, f.compound
    delete(f.stmts)
    delete(f.fields)
    delete(f.field_inits)
    for _, ids in f.field_outs { delete(ids) }
    delete(f.field_outs)
    if ok {
        b.fused[f.ts] = f.seg
        append(&b.fuses, f)   // settled when the graph is put together
        return
    }
    if b.fuse_log {
        fmt.eprintfln("fuse no: %s: %s", f.ts.name if f.ts.name != "" else b.g.name[f.root], f.failed)
    }
    b.failed[f.ts] = f.failed
    graph_fuse_free(f)
}

@(private="file")
graph_fuse_free :: proc(f: ^Graph_Fuse) {
    delete(f.slots)
    delete(f.consts)
    delete(f.widens)
    delete(f.checks)
    delete(f.calls)
    delete(f.steps)
    for m in f.marks { delete(m.resets) }
    delete(f.marks)
    delete(f.allocs)
    free(f)
}

// A value at a param's type known only later (graph_value_as): a place is
// read, cast (a header's view, a widening), and seen as a slice — whichever
// its param takes kept; a value, cast. Its index in the body's list, to name
// the param once it is known.
graph_fuse_as :: proc(b: ^Graph_Builder, v: Operand, place: bool, t: Type, read_span, span: Span, w: Graph_Widen) -> (Operand, int) {
    w := w
    w.views, w.t, w.read, w.slice = true, t, NO_NODE, NO_NODE
    val := v
    if place {
        val = graph_read(b, v, t, read_span)   // (at the expression, as graph_value reads it)
        w.read = val.op
    }
    // A cast only where one can be taken — a number's widening, a partial
    // array's header — and a slice only of a fixed array's place.
    _, _, num := numeric_info(graph_settled(t))
    if !num && !graph_partial_of(t) || is_infer(t) && infer_cell_of(t) == nil { return val, -1 }
    w.id, w.v = graph_op(b, .Cast, .Implied, span, nil, "", val), val
    if _, from_array := distinct_base(t).(^Type_Fixed_Array); place && from_array { w.slice = graph_op(b, .Slice, .Implied, span, nil, "", v) }
    append(&b.fuse.widens, w)
    return {w.id, 0}, len(b.fuse.widens) - 1
}

// A number at the type its use takes, as graph_widen: an operation made
// here, kept or dropped when the graph is put together.
graph_fuse_widen :: proc(b: ^Graph_Builder, v: Operand, span: Span, w: Graph_Widen) -> Operand {
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
    f := b.fuse
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
    return p.default_value != nil && is_infer(p.type_)
}

// A block of code (graph_code_block): opened before its statements are
// checked, closed after.
Graph_Block :: struct {
    n, outer: Node_Id,
    span:     Span,
}

graph_fuse_block_open :: proc(b: ^Graph_Builder, label: string, body: []Stmt, span: Span) -> Graph_Block {
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, body, span)
    return k
}

graph_fuse_block_close :: proc(b: ^Graph_Builder, k: Graph_Block) {
    graph_scope_close(b, k.span)
    b.code.block = k.outer
    graph_close(b, k.n)
}

// An `if` (graph_if): its branch on the condition, then each block between
// its checks.
Graph_If :: struct {
    then_r, else_r, join: ^Run,
    block:                Graph_Block,
    has_else:             bool,
    span:                 Span,
}

graph_fuse_if :: proc(b: ^Graph_Builder, cond: Operand, v: ^Stmt_If) -> Graph_If {
    fi := Graph_If{has_else = len(v.else_body) > 0, span = v.span}
    fi.then_r, fi.join = graph_run_new(b), graph_run_new(b)
    fi.else_r = graph_run_new(b) if fi.has_else else fi.join
    graph_branch(b, cond, fi.then_r, fi.else_r, .Explicit, v.span)
    b.code.run = fi.then_r
    fi.block = graph_fuse_block_open(b, "if", v.body[:], v.span)
    return fi
}

graph_fuse_else :: proc(b: ^Graph_Builder, fi: ^Graph_If, v: ^Stmt_If) {
    graph_fuse_block_close(b, fi.block)
    if graph_reachable(b) { graph_jump(b, fi.join, .Synthetic, fi.span) }
    if fi.has_else {
        b.code.run = fi.else_r
        fi.block = graph_fuse_block_open(b, "else", v.else_body[:], v.span)
    }
}

graph_fuse_if_end :: proc(b: ^Graph_Builder, fi: ^Graph_If) {
    if fi.has_else {
        graph_fuse_block_close(b, fi.block)
        if graph_reachable(b) { graph_jump(b, fi.join, .Synthetic, fi.span) }
    }
    b.code.run = fi.join
}

// A return (graph_return_stmt), its values built: an implied `Ok` for each
// trailing err left out, the scopes left, the return.
graph_fuse_return :: proc(b: ^Graph_Builder, vals: []Operand, span: Span) {
    rts := graph_result_types(b)
    all := make([dynamic]Operand, 0, len(rts), context.temp_allocator)
    append(&all, ..vals)
    graph_implied_oks(b, &all, rts, span)
    graph_exit_scopes(b, 0, span)
    graph_op(b, .Return, .Explicit, span, nil, "", ..all[:])
    graph_run_close(b)
}

// A struct's field declaration (graph_stmt at its field site): its fields,
// typed as the struct's; each name's lowered assignment stores into its own
// and is this statement's.
graph_fuse_fields :: proc(b: ^Graph_Builder, v: ^Stmt_Decl) {
    f := b.fuse
    ids := make([]Node_Id, len(v.names))
    for name, i in v.names {
        d := graph_decl(b, {kind = .Field, owner = f.ts}, b.code.block, name, nil, v.span)
        ids[i] = d
        if i < len(v.checked) {
            key := stmt_key(v.checked[i])
            f.fields[key] = d
            f.stmts[key] = b.stmt
            if inits := decl_init(v); i < len(inits) { f.field_inits[key] = inits[i] }
        }
    }
    // (Several from one call — `a, b := f()`, lowered to its destructure:
    // each output written to its field, graph_init_many.)
    if len(v.names) > 1 && len(v.checked) == 1 {
        if _, is_mr := v.checked[0].(^Stmt_Multi_Return_Assign); is_mr {
            f.field_outs[stmt_key(v.checked[0])] = ids
            return
        }
    }
    delete(ids)
}

// The program's struct (fuse_program_struct: main's entry sets up its
// storage, nothing constructs it): each field mara.core declares for it,
// typed as the struct's, a statement of its own; no code.
graph_fuse_program_fields :: proc(b: ^Graph_Builder, body: []Stmt) {
    f := b.fuse
    for s in body {
        v, is_decl := s.(^Stmt_Decl)
        if !is_decl {
            graph_fuse_fail(b, f, "the program's struct declares no field")
            return
        }
        graph_fuse_body_stmt(b, s)
        saved := graph_fuse_stmt(b, s, fresh = true)
        for name in v.names { graph_decl(b, {kind = .Field, owner = f.ts}, b.code.block, name, nil, v.span) }
        graph_fuse_stmt_end(b, saved)
    }
}

// A local's declaration (graph_decl), before its value: typed once it is
// checked (graph_fuse_typed).
graph_fuse_decl :: proc(b: ^Graph_Builder, name: string, span: Span, bound := false) -> Node_Id {
    d := graph_decl(b, {kind = .Local}, b.code.block, name, nil, span)
    // A big value lives on the arena (graph_init): its space, taken before
    // its value — kept once its type says so. (A `let` binds memory it takes.)
    if b.arena && !bound {
        v := graph_var(b, name, d, nil, span)
        a := graph_op(b, .Arena_Alloc, .Synthetic, span, nil, "", v)
        append(&b.fuse.allocs, Graph_Alloc{decl = d, var = v.op, alloc = a, nrvo = b.code.nrvo})
    }
    return d
}

graph_fuse_typed :: proc(b: ^Graph_Builder, d: Node_Id, t: Type) {
    b.g.type_[d] = t
    // Its variable's operations made before that was known (where a value
    // was built into it), typed as it is.
    for i in int(d) + 1 ..< b.nodes {
        if b.g.kind[i] == .Op && b.g.op[i] == .Var && b.g.refers[i] == d && b.g.type_[i] == nil { b.g.type_[i] = t }
    }
}

// `x : T = void` (graph_init) and `x = void` (graph_stmt): the value left
// uninitialized.
graph_fuse_void_decl :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span: Span) {
    val := graph_void(b, t, span)
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, b.g.name[decl], decl, t, span), val)
}

graph_fuse_void_assign :: proc(b: ^Graph_Builder, name: string, t: Type, span: Span) {
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, name, NO_NODE, t, span), graph_void(b, t, span))
}

// Where the build stands, to leave out what is built after it: a field
// access's base, built before the access is found to name no member (a
// variant, a constant, a module's function) — the builder never builds it.
Graph_Mark :: struct {
    nodes: int,
    run:   ^Run,
    ops:   int,
}

graph_fuse_mark :: proc(b: ^Graph_Builder) -> Graph_Mark {
    return {b.nodes, b.code.run, len(b.code.run.ops) if b.code.run != nil else 0}
}

graph_fuse_drop_since :: proc(b: ^Graph_Builder, m: Graph_Mark) {
    if b.nodes == m.nodes { return }
    r := b.code.run
    if r == nil || r != m.run && m.run != nil {
        graph_fuse_fail(b, b.fuse, "a field access's base crossed runs")
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
            if e.kind == .Then && e.to == r.ops[0] {
                e.to = NO_NODE
                append(&r.waiting, i32(k))
            }
        }
    }
    resize(&r.ops, m.ops)
}

// An assert of its condition's value; a comparison's sides as written, for
// its failure's message.
graph_assert :: proc(b: ^Graph_Builder, v: ^Expr_Assert, cond: Operand, w: Written) {
    a := graph_op(b, .Assert, w, v.span, nil, v.cond_text, cond)
    if bin, is_bin := v.cond.(^Expr_Binary); is_bin && is_comparison_op(bin.op) && v.lhs_text != "" && v.rhs_text != "" {
        b.g.assert_sides[a] = {
            "" if assert_side_is_literal(bin.left) else v.lhs_text,
            "" if assert_side_is_literal(bin.right) else v.rhs_text,
        }
    }
}

// `a and b`, `a or b` (graph_short_circuit): the result through a synthetic
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

graph_fuse_and :: proc(b: ^Graph_Builder, is_and: bool, w: Written, span: Span) -> Graph_And {
    word := "and" if is_and else "or"
    return {slot = graph_slot(b, word, Type_Bool{}, span), word = word, and = is_and, w = w, span = span}
}

graph_fuse_and_left :: proc(b: ^Graph_Builder, sa: ^Graph_And, l: Operand) {
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), l)
    sa.rhs, sa.join = graph_run_new(b), graph_run_new(b)
    if sa.and {
        graph_branch(b, l, sa.rhs, sa.join, sa.w, sa.span)
    } else {
        graph_branch(b, l, sa.join, sa.rhs, sa.w, sa.span)
    }
    b.code.run = sa.rhs
}

graph_fuse_and_end :: proc(b: ^Graph_Builder, sa: ^Graph_And, r: Operand) -> Operand {
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), r)
    graph_jump(b, sa.join, .Synthetic, sa.span)
    b.code.run = sa.join
    return graph_read(b, graph_var(b, sa.word, sa.slot, Type_Bool{}, sa.span), Type_Bool{}, sa.span)
}

// A bare declaration's value (graph_init): its type's construction, or zero;
// a sized slice's zero takes its capacity.
graph_fuse_bare :: proc(b: ^Graph_Builder, d: Node_Id, t: Type, cap: Maybe(Operand), span: Span) {
    if c, has := cap.?; has {
        n := graph_fuse_widen(b, c, span, {to = slice_header_width_type})
        graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, b.g.name[d], d, t, span), n)
        return
    }
    graph_construct_bare(b, graph_var(b, b.g.name[d], d, t, span), t, span)
}

// A new partial array's zero, made before the value it may be a prefix of:
// kept, typed, when it is.
graph_fuse_prefix :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, span: Span) -> [2]Node_Id {
    v := graph_var(b, name, decl, nil, span)
    return {v.op, graph_op(b, .Zero, .Synthetic, span, nil, "", v)}
}

graph_fuse_prefix_end :: proc(b: ^Graph_Builder, p: [2]Node_Id, keep: bool, t: Type) {
    for id in p {
        if keep { b.g.type_[id] = t } else { graph_drop(b, id, NO_VALUE) }
    }
}

// A call through a function value (graph_call's): the arguments, then the
// value, read, then the call.
graph_fuse_indirect :: proc(b: ^Graph_Builder, name: string, fn_value: Type, t: Type, args: []Operand, w: Written, span: Span) -> Operand {
    ops := make([dynamic]Operand, 0, len(args) + 1, context.temp_allocator)
    append(&ops, graph_read(b, graph_var(b, name, NO_NODE, fn_value, span), fn_value, span))
    append(&ops, ..args)
    return graph_op_value(b, .Call, w, span, t, name, ..ops[:])
}

// Bytes indexed, seen as another type once the use of them says which
// (graph_view_place): the element's place, built, is that view — the same
// operands, the bytes at the index.
graph_fuse_view :: proc(b: ^Graph_Builder, place: Operand, t: Type, big: bool, span: Span) {
    id := place.op
    b.g.op[id], b.g.type_[id], b.g.origin[id] = .View, t, span
    b.g.name[id] = "#big_endian" if big else ""
    // (Its base's implied dereference and its offset's widening are the
    // view's, where it is.)
    // (Its operands end where the next node's begin — or, the newest, now.)
    end := int(b.g.operand_first[id + 1]) if int(id) + 1 < b.nodes else len(b.g.operands)
    ops := b.g.operands[b.g.operand_first[id]:end]
    for o, k in ops {
        if o.op == NO_NODE || b.g.written[o.op] != .Implied { continue }
        if k == 0 && b.g.op[o.op] == .Deref || k == 1 && b.g.op[o.op] == .Cast { b.g.origin[o.op] = span }
    }
}

// Bytes read by a byte read (graph_store): of the element built, its
// buffer's place (its dereference at the read) and its index as it was
// before it was widened; the element's operation left out.
graph_fuse_byte_operands :: proc(b: ^Graph_Builder, place: Operand, span: Span) -> (Operand, Operand) {
    id := place.op
    end := int(b.g.operand_first[id + 1]) if int(id) + 1 < b.nodes else len(b.g.operands)
    ops := b.g.operands[b.g.operand_first[id]:end]
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

// A span of bytes read (graph_store): of the slice built, its bytes' place
// (its dereference at the read) and its bounds; the slice left out.
graph_fuse_span_operands :: proc(b: ^Graph_Builder, slice: Operand, span: Span) -> (buf, lo, hi: Operand) {
    id := slice.op
    end := int(b.g.operand_first[id + 1]) if int(id) + 1 < b.nodes else len(b.g.operands)
    ops := b.g.operands[b.g.operand_first[id]:end]
    buf, lo, hi = ops[0], ops[1], ops[2]
    graph_drop(b, id, NO_VALUE)
    if buf.op != NO_NODE && b.g.op[buf.op] == .Deref && b.g.written[buf.op] == .Implied { b.g.origin[buf.op] = span }
    return
}

// A span of bytes seen as a `t` at its start (graph_view_at): of the slice
// built, its bytes' place and its start, at the header's width (0 when it
// has none); the view.
graph_fuse_span_view :: proc(b: ^Graph_Builder, slice: Operand, t: Type, big: bool, span: Span) -> Operand {
    buf, lo, _ := graph_fuse_span_operands(b, slice, span)
    at: Operand
    if lo != NO_VALUE {
        at = graph_fuse_widen(b, lo, span, {to = slice_header_width_type})
    } else {
        at = graph_const(b, .Synthetic, span, slice_header_width_type, "0", Const_Value{})
    }
    return graph_op_value(b, .View, .Explicit, span, t, "#big_endian" if big else "", buf, at)
}

// What is built after what follows it, where it goes (a dispatch's default
// for `_`, known once the function is chosen): a place for it, then it, in
// a segment of its own there. Its operations join the run the place is in:
// false when that is no longer the run.
Graph_Later :: struct {
    seg, anchor:  int,
    si, saved:    int,
    run:          ^Run,
    same:         bool,
    reserved:     bool,
}

// What is built before what it follows (checked first, built after): in a
// segment of its own, put in place later — at the anchor it is placed at.
// False when the run it was built in is no longer the run.
Graph_Early :: struct {
    seg, si, saved: int,
    run:            ^Run,
}

graph_fuse_early_begin :: proc(b: ^Graph_Builder) -> Graph_Early {
    e := Graph_Early{seg = b.seg, run = b.code.run}
    e.si, e.saved = graph_segment_enter(b)
    return e
}

graph_fuse_early_end :: proc(b: ^Graph_Builder, e: ^Graph_Early) {
    graph_segment_leave(b, e.saved)
}

graph_fuse_early_place :: proc(b: ^Graph_Builder, e: ^Graph_Early) -> bool {
    if b.seg != e.seg { return false }
    graph_anchor_here(b, e.si)
    return b.code.run == e.run
}

graph_fuse_later :: proc(b: ^Graph_Builder) -> Graph_Later {
    return {seg = b.seg, anchor = graph_anchor_here(b), run = b.code.run, reserved = true}
}

graph_fuse_later_begin :: proc(b: ^Graph_Builder, l: ^Graph_Later) {
    l.same = b.code.run == l.run
    l.si, l.saved = graph_segment_enter(b)
}

graph_fuse_later_end :: proc(b: ^Graph_Builder, l: ^Graph_Later) -> bool {
    graph_segment_leave(b, l.saved)
    b.segs[l.seg].anchors[l.anchor].seg = l.si
    return l.same && b.code.run == l.run
}

// `bytes[lo:hi] = v` (graph_stmt): its target is a view of the bytes at lo —
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
}

// The view's place, first.
graph_fuse_span_target :: proc(b: ^Graph_Builder, bytes: Expr, span: Span) -> Graph_Span_Target {
    st := Graph_Span_Target{lo = NO_VALUE, zero = NO_NODE}
    st.view_place.x = b.nodes
    st.vplace = graph_plain_base(b, bytes, span)
    st.view_place.y = b.nodes
    return st
}

// lo built: at the header's width (a slice's, at it); hi next.
graph_fuse_span_target_hi :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, lo: Operand, slice_span: Span) {
    if lo != NO_VALUE {
        st.lo = graph_fuse_widen(b, lo, slice_span, {to = slice_header_width_type})
        st.widened = st.lo.op != lo.op
    }
    st.run = b.code.run
    st.hi.x = b.nodes
}

// hi built: the slice's place, the slice, then the view (of no type yet).
graph_fuse_span_target_ops :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, hi: Operand, bytes: Expr, t: Type, big: bool, slice_span, span: Span) {
    st.hi.y = b.nodes
    st.branched = b.code.run != st.run
    st.place.x = b.nodes
    p := graph_plain_base(b, bytes, slice_span)
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
graph_fuse_span_target_end :: proc(b: ^Graph_Builder, st: ^Graph_Span_Target, view: Type, span: Span) -> (Operand, bool) {
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

// Bytes taken as an array (graph_value_as): their view, copied into a
// temporary, read.
graph_fuse_view_temp :: proc(b: ^Graph_Builder, view: Operand, t: Type, span: Span) -> Operand {
    slot := graph_slot(b, "temp", t, span)
    graph_op(b, .Write, .Implied, span, nil, "", graph_var(b, "temp", slot, t, span), graph_read(b, view, t, span))
    return graph_read(b, graph_var(b, "temp", slot, t, span), t, span)
}

// A take (graph_value's): the count, built; the storage it carves from,
// built here; the carve.
graph_fuse_carve :: proc(b: ^Graph_Builder, v: ^Expr_Take, count: Operand, w: Written) -> Operand {
    return graph_op_value(b, .Carve, w, v.span, v.type_, v.keyword, graph_carve_storage(b, v), count)
}

// A plain place the checker checked without building (a loop's collection,
// a slice's): built where it is walked, from its check.
graph_fuse_base_place :: proc(b: ^Graph_Builder, e: Expr, span: Span) -> Operand {
    return graph_plain_base(b, e, span)
}

// A destructure of a call's outputs (graph_destructure): the names it
// declares made before the call (typed once checked), then each output
// written to its name, or to its target's place, in turn.
Graph_Destructure :: struct {
    on:    bool,
    decls: []Node_Id,
    call:  Operand,
    place: Operand,   // the target of the output being written
}

graph_fuse_destructure :: proc(b: ^Graph_Builder, v: ^Stmt_Multi_Return_Assign) -> Graph_Destructure {
    // (A struct's fields from one call: declared as its fields.)
    if ids, of_fields := b.fuse.field_outs[rawptr(v)]; of_fields {
        return Graph_Destructure{on = true, decls = ids}
    }
    mr := Graph_Destructure{on = true, decls = make([]Node_Id, len(v.names), context.temp_allocator)}
    for name, i in v.names {
        mr.decls[i] = NO_NODE
        if !v.is_decl || name == "" || name == "_" { continue }
        if i < len(v.targets) && v.targets[i] != nil { continue }   // an lvalue stores
        mr.decls[i] = graph_decl(b, {kind = .Local}, b.code.block, name, nil, v.span)
    }
    return mr
}

graph_fuse_destructure_write :: proc(b: ^Graph_Builder, mr: ^Graph_Destructure, v: ^Stmt_Multi_Return_Assign, i: int) {
    name := v.names[i]
    target := i < len(v.targets) && v.targets[i] != nil
    if name == "_" || name == "" && !target { return }
    val := mr.call
    if i > 0 { val = {graph_outputs_op(b, v.values[0], mr.call), i32(i)} }
    dest := mr.place
    if !target {
        t: Type = v.var_types[i] if i < len(v.var_types) else nil
        if mr.decls[i] != NO_NODE { graph_fuse_typed(b, mr.decls[i], t) }
        dest = graph_var(b, name, mr.decls[i], t, v.span)
    }
    graph_op(b, .Write, .Explicit, v.span, nil, "", dest, val)
}

// A match (graph_match), its subject checked: the switch on its tag — each
// arm's tag a constant filled in when the arm is (graph_fuse_arm) — then,
// per arm, its block; the code after it joins.
Graph_Match :: struct {
    slot:     Node_Id,
    is_union: bool,
    ops:      [dynamic]Operand,
    tags:     []Node_Id,
    arms:     []^Run,
    join:     ^Run,
    span:     Span,
}

graph_fuse_match_begin :: proc(b: ^Graph_Builder, v: ^Stmt_Match, slot: Node_Id) -> ^Graph_Match {
    gm := new(Graph_Match, context.temp_allocator)
    gm.slot, gm.span = slot, v.span
    _, gm.is_union = distinct_base(expr_type(v.subject)).(^Type_Union)
    gm.ops = make([dynamic]Operand, 0, len(v.arms) + 1, context.temp_allocator)
    if gm.is_union {
        append(&gm.ops, graph_fuse_subject(b, v, gm))
    } else {
        append(&gm.ops, graph_read(b, graph_fuse_subject(b, v, gm), expr_type(v.subject), v.span))
    }
    gm.tags = make([]Node_Id, len(v.arms), context.temp_allocator)
    gm.arms = make([]^Run, len(v.arms), context.temp_allocator)
    for &arm, i in v.arms {
        gm.arms[i] = graph_run_new(b)
        gm.tags[i] = NO_NODE
    }
    return gm
}

// An arm's tag: a union's variant's, an enum's — a constant filled in when
// the arm is resolved (graph_fuse_arm).
graph_fuse_match_tag :: proc(b: ^Graph_Builder, gm: ^Graph_Match, v: ^Stmt_Match, i: int) {
    t := graph_tag_type(expr_type(v.subject)) if gm.is_union else expr_type(v.subject)
    tag := graph_const(b, .Implied, v.span, t, "", Const_Value{})
    gm.tags[i] = tag.op
    append(&gm.ops, tag)
}

// A value's arm: its value.
graph_fuse_match_value :: proc(b: ^Graph_Builder, gm: ^Graph_Match, val: Operand) {
    append(&gm.ops, val)
}

graph_fuse_match_switch :: proc(b: ^Graph_Builder, gm: ^Graph_Match, v: ^Stmt_Match) {
    graph_switch(b, gm.ops[:], gm.arms, v.span)
    gm.join = graph_run_new(b)
}

@(private="file")
graph_fuse_subject :: proc(b: ^Graph_Builder, v: ^Stmt_Match, gm: ^Graph_Match) -> Operand {
    if gm.slot != NO_NODE { return graph_var(b, "subject", gm.slot, b.g.type_[gm.slot], v.span) }
    return graph_plain_base(b, v.subject, v.span)
}

// An arm, resolved: its tag, its run and block, and — a union's arm that
// binds its payload — the binding, the payload's place.
graph_fuse_arm :: proc(b: ^Graph_Builder, gm: ^Graph_Match, v: ^Stmt_Match, arm: ^Match_Arm, i: int) -> Graph_Block {
    if id := gm.tags[i]; id != NO_NODE {
        b.g.name[id] = arm.variant
        b.g.consts[id] = Const_Value{int = i128(arm.resolved_tag)}
    }
    span := gm.span
    b.code.run = gm.arms[i]
    label := "else" if arm.is_else else fmt.aprintf("arm %s", arm.variant)
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, arm.body[:], span)
    if arm.is_union_arm && arm.bound_name != "" {
        t := graph_arm_type(b, arm, span)
        bound := graph_node(b, .Local, .Explicit, k.n, arm.bound_name, t, span)
        // The binding is the payload's place, not a copy.
        payload := graph_op(b, .Variant, .Explicit, span, t, arm.bound_name, graph_fuse_subject(b, v, gm))
        b.g.refers[payload] = bound
        graph_bind(b, arm.bound_name, bound)   // after the subject's place: it may reuse the name
    }
    return k
}

graph_fuse_arm_end :: proc(b: ^Graph_Builder, gm: ^Graph_Match, k: Graph_Block) {
    graph_fuse_block_close(b, k)
    if graph_reachable(b) { graph_jump(b, gm.join, .Synthetic, k.span) }
}

graph_fuse_match_end :: proc(b: ^Graph_Builder, gm: ^Graph_Match) {
    b.code.run = gm.join
}

// A defer's block (graph_defer): its code of its own — a run entered from
// the block, ending in a return — built as its statements are checked, then
// registered with the scope it is in (Run_Defer runs it at every exit).
Graph_Defer :: struct {
    d:     Node_Id,
    saved: Code,
    span:  Span,
}

graph_fuse_defer :: proc(b: ^Graph_Builder, v: ^Stmt_Defer) -> Graph_Defer {
    gd := Graph_Defer{d = graph_node(b, .Block, .Explicit, b.code.block, "defer", nil, v.span), span = v.span}
    gd.saved = graph_code_begin(b, gd.d, "")
    graph_scope_open(b, gd.d, v.body[:], v.span)
    return gd
}

graph_fuse_defer_end :: proc(b: ^Graph_Builder, gd: Graph_Defer) {
    graph_code_finish(b, gd.span)
    graph_code_end(b, gd.saved)
    append(&b.code.scopes[len(b.code.scopes) - 1].defers, gd.d)
    graph_close(b, gd.d)
}

// An `if` expression's runs (graph_if_place): the branch on its condition,
// each branch's run, and the join.
Graph_If_Expr :: struct {
    yes, no, join: ^Run,
    span:          Span,
}

graph_fuse_if_expr :: proc(b: ^Graph_Builder, cond: Operand, w: Written, span: Span) -> Graph_If_Expr {
    gi := Graph_If_Expr{yes = graph_run_new(b), no = graph_run_new(b), join = graph_run_new(b), span = span}
    graph_branch(b, cond, gi.yes, gi.no, w, span)
    b.code.run = gi.yes
    return gi
}

graph_fuse_if_expr_else :: proc(b: ^Graph_Builder, gi: ^Graph_If_Expr) {
    graph_jump(b, gi.join, .Synthetic, gi.span)
    b.code.run = gi.no
}

graph_fuse_if_expr_end :: proc(b: ^Graph_Builder, gi: ^Graph_If_Expr) {
    graph_jump(b, gi.join, .Synthetic, gi.span)
    b.code.run = gi.join
}

// The kind of the statement being built, once its check says (a
// destructure found a broadcast is its copies').
graph_fuse_stmt_kind :: proc(b: ^Graph_Builder, kind: Stmt_Kind) {
    b.g.stmts[b.stmt].kind = kind
}

// A broadcast literal built into d (graph_into): its value at the element
// type, then the fill.
graph_fuse_fill :: proc(b: ^Graph_Builder, v: ^Expr_Struct_Literal, t: Type, d: Dest, val: Operand) {
    x := graph_fuse_widen(b, val, v.span, {to = graph_elem_type(t)})
    graph_op(b, .Fill, .Explicit, v.span, t, "", graph_dest_place(b, d, v.span), x)
}

// `void` written: the uninitialized value (graph_void).
graph_fuse_void :: proc(b: ^Graph_Builder, t: Type, span: Span) -> Operand {
    return graph_void(b, t, span)
}

// An override block written into a variable's struct (graph_literal_writes
// at the variable): each field's value into its field.
graph_fuse_override :: proc(b: ^Graph_Builder, d: Dest, sd: ^Scope_Body) -> ^Graph_Literal {
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent, gl.sd = d, d, sd
    return gl
}

// The call the slots of a default share (Code.tuples): made at the first.
graph_fuse_tuple_set :: proc(b: ^Graph_Builder, key: rawptr, op: Node_Id) {
    b.code.tuples[key] = op
}

graph_fuse_tuple_get :: proc(b: ^Graph_Builder, key: rawptr) -> (Node_Id, bool) {
    op, ok := b.code.tuples[key]
    return op, ok
}

// A value written to a place already built.
graph_fuse_write_at :: proc(b: ^Graph_Builder, place, v: Operand, span: Span) {
    graph_op(b, .Write, .Explicit, span, nil, "", place, v)
}

// A loop (graph_for), built around its checks: its block, the loop's
// variables, then its runs — the check, the body, the step — and the code
// after it.
Graph_For :: struct {
    f, outer:                Node_Id,
    counter:                 Node_Id,
    end_slot, coll_slot:     Node_Id,
    elem:                    Node_Id,
    lo, hi:                  Operand,
    check, body, post, done: ^Run,
    body_block:              Node_Id,
    has_post:                bool,
    span:                    Span,
    step:                    int,   // the step's segment, built before the body; -1
}

graph_fuse_for :: proc(b: ^Graph_Builder, v: ^Stmt_For) -> Graph_For {
    fl := Graph_For{span = v.span, counter = NO_NODE, end_slot = NO_NODE, coll_slot = NO_NODE, elem = NO_NODE, step = -1}
    fl.f = graph_node(b, .Block, .Explicit, b.code.block, "for", nil, v.span)
    fl.outer = b.code.block
    b.code.block = fl.f
    graph_frame_push(b)   // the loop's variables, before its body's scope
    return fl
}

// A range's counter, before its bounds (typed once they are checked).
graph_fuse_range_counter :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For) {
    fl.counter = graph_node(b, .Local, .Explicit, fl.f, v.loop_var, nil, fl.span)
    graph_bind(b, v.loop_var, fl.counter)
}

// A range's bound at the counter's type (graph_range_bound): cast when its
// own differs — decided when the graph is put together.
graph_fuse_range_bound :: proc(b: ^Graph_Builder, v: Operand, t: Type, span: Span) -> Operand {
    id := graph_op(b, .Cast, .Synthetic, span, nil, "", v)
    append(&b.fuse.checks, Graph_Check{kind = .Bound, ids = {id, NO_NODE}, v = v, t = t})
    return {id, 0}
}

// The range's bounds checked: the counter typed, the end held (a literal's
// is itself), the check that the range counts up — kept when a bound is no
// constant — and the counter's first value; then the check run.
graph_fuse_range :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For, bounds: [2]int) {
    ct := v.var_type
    b.g.type_[fl.counter] = ct
    for k in bounds { if k >= 0 { b.fuse.checks[k].ct = ct } }
    if _, is_lit := v.range_high.(^Expr_Number); !is_lit {
        fl.end_slot = graph_slot(b, "end", ct, fl.span)
        graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, "end", fl.end_slot, ct, fl.span), fl.hi)
    }
    up := graph_op_value(b, .Compare, .Synthetic, fl.span, Type_Bool{}, "<=", fl.lo, fl.hi)
    assert := graph_op(b, .Assert, .Synthetic, fl.span, nil, "range", up)
    append(&b.fuse.checks, Graph_Check{kind = .Ascends, ids = {up.op, assert}, lo = fl.lo, hi = fl.hi})
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, v.loop_var, fl.counter, ct, fl.span), fl.lo)
    graph_fuse_for_runs(b, fl, v)
}

// A collection loop, the collection checked (a plain place: walked where the
// loop needs it): a slice's elements as they are when the loop begins, the
// element and the index; then the check run.
graph_fuse_for_collection :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For) {
    if view := graph_loop_view(v.collection); view != nil && fl.coll_slot == NO_NODE {
        fl.coll_slot = graph_slot(b, "items", view, fl.span)
        val := graph_op_value(b, .Slice, .Implied, fl.span, view, "", graph_plain_base(b, v.collection, fl.span))
        graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, "items", fl.coll_slot, view, fl.span), val)
    }
    if v.elem_var != "" {
        fl.elem = graph_node(b, .Local, .Explicit, fl.f, v.elem_var, v.elem_type_, fl.span)
        graph_bind(b, v.elem_var, fl.elem)
    }
    index_t := Type(slice_header_width_type)
    if v.index_var != "" {
        fl.counter = graph_node(b, .Local, .Explicit, fl.f, v.index_var, index_t, fl.span)
        graph_bind(b, v.index_var, fl.counter)
    } else {
        fl.counter = graph_slot(b, "index", index_t, fl.span)
    }
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, b.g.name[fl.counter], fl.counter, index_t, fl.span),
             graph_const(b, .Synthetic, fl.span, index_t, "0", Const_Value{}))
    graph_fuse_for_runs(b, fl, v)
}

// A collection that is no plain place (graph_for's): held in a local made
// before it — its place's view, when it has a header, else itself — which
// the loop walks. Its local first (typed once it is checked); a temporary its
// value may need, reserved before it (graph_fuse_later).
Graph_Items :: struct {
    temp: Graph_Later,
}

graph_fuse_items :: proc(b: ^Graph_Builder, fl: ^Graph_For) -> Graph_Items {
    fl.coll_slot = graph_slot(b, "items", nil, fl.span)
    return {temp = graph_fuse_later(b)}
}

// Checked, `t` its type: its view, or it, written to the local.
graph_fuse_items_view :: proc(b: ^Graph_Builder, fl: ^Graph_For, gi: ^Graph_Items, place: Operand, is_place: bool, t, view: Type, is_self, fills: bool) {
    span := fl.span
    p := place
    if !is_place {
        // A value: held in a temporary made before it (graph_place's) —
        // zero first when it fills a prefix of a partial array.
        graph_fuse_later_begin(b, &gi.temp)
        slot := graph_slot(b, "temp", t, span)
        if fills { graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, "temp", slot, t, span)) }
        if !graph_fuse_later_end(b, &gi.temp) { graph_fuse_fail(b, b.fuse, "a loop's collection across runs") }
        graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, "temp", slot, t, span), place)
        p = graph_var(b, "temp", slot, t, span)
    }
    if pt, ok := distinct_base(t).(^Type_Ptr); ok && !is_self {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)   // (through a pointer, what it points at)
    }
    val := graph_op_value(b, .Slice, .Implied, span, view, "", p)
    graph_fuse_typed(b, fl.coll_slot, view)
    graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, "items", fl.coll_slot, view, span), val)
}

// The loop's runs, into the check: a counter against its bound; else the
// condition, checked next (graph_fuse_for_cond); else none (`for {}`).
graph_fuse_for_runs :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For) {
    fl.check, fl.body, fl.post, fl.done = graph_run_new(b), graph_run_new(b), graph_run_new(b), graph_run_new(b)
    fl.has_post = v.post != nil || fl.counter != NO_NODE
    graph_jump(b, fl.check, .Synthetic, fl.span)
    b.code.run = fl.check
    span := fl.span
    if fl.counter != NO_NODE {
        ct := b.g.type_[fl.counter]
        cur := graph_read(b, graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), ct, span)
        bound: Operand
        if v.is_range {
            if fl.end_slot != NO_NODE {
                bound = graph_read(b, graph_var(b, "end", fl.end_slot, b.g.type_[fl.end_slot], span), b.g.type_[fl.end_slot], span)
            } else {
                bound = graph_leaf(b, v.range_high)
            }
        } else {
            bound = graph_len(b, graph_coll_place(b, v.collection, fl.coll_slot, span), expr_type(v.collection), span)
        }
        cmp := graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, "<", cur, bound)
        graph_branch(b, cmp, fl.body, fl.done, .Synthetic, span)
        graph_fuse_for_body(b, fl, v)
    } else if v.condition == nil {
        graph_jump(b, fl.body, .Synthetic, span)   // `for {}`: until a break
        graph_fuse_for_body(b, fl, v)
    }
}

// A condition loop's condition, built in its check run.
graph_fuse_for_cond :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For, cond: Operand) {
    graph_branch(b, cond, fl.body, fl.done, .Explicit, fl.span)
    graph_fuse_for_body(b, fl, v)
}

// The body's run and block, its statements checked next: an element's
// loop reads the element first.
@(private="file")
graph_fuse_for_body :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For) {
    span := fl.span
    b.code.run = fl.body
    append(&b.code.loops, Loop{cont = fl.post if fl.has_post else fl.check, done = fl.done, scope = len(b.code.scopes)})
    fl.body_block = graph_node(b, .Block, .Explicit, fl.f, "body", nil, span)
    b.code.block = fl.body_block
    graph_scope_open(b, fl.body_block, v.body[:], span)
    if fl.elem != NO_NODE {
        ct := b.g.type_[fl.counter]
        at := graph_read(b, graph_var(b, b.g.name[fl.counter], fl.counter, ct, span), ct, span)
        at = graph_widen(b, at, slice_header_width_type, span)
        slot := graph_op_value(b, .Index, .Synthetic, span, v.elem_type_, "", graph_coll_place(b, v.collection, fl.coll_slot, span), at)
        graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, v.elem_var, fl.elem, v.elem_type_, span),
                 graph_read(b, slot, v.elem_type_, span))
    }
}

// After the body: its scope's end, the step, and the code after the loop.
graph_fuse_for_end :: proc(b: ^Graph_Builder, fl: ^Graph_For, v: ^Stmt_For) {
    span := fl.span
    graph_scope_close(b, span)
    graph_close(b, fl.body_block)
    b.code.block = fl.f
    pop(&b.code.loops)
    cont := fl.post if fl.has_post else fl.check
    if graph_reachable(b) { graph_jump(b, cont, .Synthetic, span) }
    if fl.has_post {
        b.code.run = fl.post
        if fl.step >= 0 { graph_anchor_here(b, fl.step) }   // (the step, where it runs)
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
    graph_frame_pop(b)
}

// A C-style loop's step, checked before its body: built then, into the
// step's run, in a segment of its own anchored after the body.
Graph_Step :: struct {
    saved:      int,
    run:        ^Run,
    block:      Node_Id,
}

graph_fuse_step :: proc(b: ^Graph_Builder, fl: ^Graph_For) -> Graph_Step {
    st := Graph_Step{run = b.code.run, block = b.code.block}
    fl.step, st.saved = graph_segment_enter(b)
    append(&b.fuse.steps, fl.step)   // (settled with its body)
    b.code.run, b.code.block = fl.post, fl.f
    fl.post.early = true
    return st
}

graph_fuse_step_end :: proc(b: ^Graph_Builder, fl: ^Graph_For, st: Graph_Step) {
    b.code.run, b.code.block = st.run, st.block
    graph_segment_leave(b, st.saved)
}

// `break`, `continue` (graph_loop_exit).
graph_fuse_loop_exit :: proc(b: ^Graph_Builder, span: Span, is_break: bool) {
    graph_loop_exit(b, span, is_break)
}

// A range's bound cast or its check that it counts up, decided when the
// graph is put together (graph_range_bound, graph_for).
Graph_Check :: struct {
    kind:   enum u8 { Bound, Ascends },
    ids:    [2]Node_Id,   // the cast; the compare and the assert
    v:      Operand,      // the bound's value
    t, ct:  Type,         // its type, the counter's
    lo, hi: Operand,      // the bounds, as the check reads them
}

// A struct literal built into d (graph_into), before its fields are
// checked: its construction — zero for `Foo{0}`, else its constructor on
// its params' defaults (a union's variant: its tag, then the field defaults
// the literal doesn't give) — and where its fields are. Nil when t is no
// aggregate the literal builds.
Graph_Literal :: struct {
    d, parent: Dest,
    sd:        ^Scope_Body,
    skip:      int,
}

graph_fuse_literal :: proc(b: ^Graph_Builder, v: ^Expr_Struct_Literal, t: Type, d: Dest) -> ^Graph_Literal {
    span := v.span
    ts, is_scope := t.(^Type_Scope)
    if is_scope && ts.kind == .Struct && !ts.is_module && v.zero_init {
        graph_op(b, .Zero, .Explicit, span, t, "{0}", graph_dest_place(b, d, span))
    } else if is_scope && ts.kind == .Struct && !ts.is_module {
        ops := graph_default_args(b, graph_dest_place(b, d, span), ts, span)
        op := graph_call_op(b, .Construct, .Explicit, span, ts, t, ..ops)
        b.g.name[op] = strings.concatenate({b.g.name[op], "{}"})   // as written: braces, no call
        if ts.is_union_variant { graph_field_defaults(b, ts, v, d, span) }
    } else if graph_aggregate(t) {
        _, is_union := distinct_base(t).(^Type_Union)
        graph_op(b, .Construct if is_union else .Zero, .Explicit, span, t, v.name, graph_dest_place(b, d, span))
        if is_union { graph_variant_defaults(b, t, v.name, v, d, span) }
    } else {
        return nil
    }
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent = d, d
    gl.sd = as_scope_body(distinct_base(t))
    // A union's variant: its fields are the variant struct's, past the tag.
    if st := graph_variant_struct(b, t, v.name); st != nil {
        gl.sd = as_scope_body(st)
        gl.parent = Dest{kind = .Variant, name = v.name, type_ = st, parent = &gl.d}
        for f in gl.sd.fields { if strings.has_prefix(f.name, "__") { gl.skip += 1 } }
    }
    return gl
}

// Where an array literal's element goes (graph_literal_writes, array values).
graph_fuse_literal_elem :: proc(gl: ^Graph_Literal, i: int, elem_t: Type) -> Dest {
    return Dest{kind = .Index, index = i, type_ = elem_t, parent = &gl.parent}
}

// Where the literal's field goes: named, or its position's (graph_literal_writes).
// `Foo{call()}` (graph_spread_writes), the call built: each field its
// result. False when it resolved to no function.
graph_fuse_spread :: proc(b: ^Graph_Builder, gl: ^Graph_Literal, v: ^Expr_Struct_Literal, call: ^Expr_Call, c: Operand) -> bool {
    callee: ^Type_Scope
    if rf, resolved := call.resolved_func.?; resolved { callee = graph_callee(b, rf) }
    if callee == nil || gl.sd == nil { return false }
    graph_spread_results(b, v, gl.sd, &gl.parent, callee, c)
    return true
}

graph_fuse_literal_field :: proc(gl: ^Graph_Literal, name: string, i: int) -> Dest {
    name := name
    if name == "" && gl.sd != nil && gl.skip + i < len(gl.sd.fields) { name = gl.sd.fields[gl.skip + i].name }
    t: Type
    if gl.sd != nil {
        if fi, ok := gl.sd.field_map[name]; ok { t = gl.sd.fields[fi].type_ }
    }
    return Dest{kind = .Field, name = name, type_ = t, parent = &gl.parent}
}

// An array literal built into d (graph_into): zero at the destination's
// type — a short literal leaves the rest zero — or, with none known yet, the
// literal's (typed once its first element is), then each element into its
// slot.
Graph_Array :: struct {
    d:      Dest,
    zero:   Node_Id,
    elem_t: Type,
}

graph_fuse_array :: proc(b: ^Graph_Builder, v: ^Expr_Array, d: Dest) -> ^Graph_Array {
    ga := new(Graph_Array, context.temp_allocator)
    ga.d = d
    t := d.type_ if d.type_ != nil && !is_infer(d.type_) else nil
    ga.zero = graph_op(b, .Zero, .Explicit, v.span, t, "", graph_dest_place(b, d, v.span))
    if t != nil { ga.elem_t = graph_elem_type(t) }
    return ga
}

// Element i's slot; the literal's own type, from its first element, when the
// destination gave none.
graph_fuse_array_elem :: proc(b: ^Graph_Builder, ga: ^Graph_Array, i: int, first: Type, lit_t: Type) -> Dest {
    if ga.elem_t == nil {
        ga.elem_t = first
        b.g.type_[ga.zero] = lit_t
    }
    return Dest{kind = .Index, index = i, type_ = ga.elem_t, parent = &ga.d}
}

// A variant built at d (graph_into, a bare variant): its construction, then
// its field defaults.
graph_fuse_variant :: proc(b: ^Graph_Builder, t: Type, name: string, d: Dest, span: Span) {
    graph_op(b, .Construct, .Explicit, span, t, name, graph_dest_place(b, d, span))
    graph_variant_defaults(b, t, name, nil, d, span)
}

// An aggregate built where no destination was given: a synthetic local,
// made before it (graph_temp_place), typed once it is.
graph_fuse_temp :: proc(b: ^Graph_Builder, span: Span, t: Type = nil) -> Dest {
    return graph_dest_var("temp", graph_slot(b, "temp", t, span), t)
}

graph_fuse_temp_end :: proc(b: ^Graph_Builder, d: Dest, t: Type, span: Span) -> Operand {
    b.g.type_[d.decl] = t
    graph_fuse_typed(b, d.decl, t)
    return graph_var(b, "temp", d.decl, t, span)
}

// A construction's operation into d (graph_call's): its place, the
// arguments, then its overrides' writes (graph_fuse_literal_field over the
// overrides, with gl.parent = d).
graph_fuse_construct :: proc(b: ^Graph_Builder, callee: ^Type_Scope, t: Type, d: Dest, args: []Operand, w: Written, span: Span) -> ^Graph_Literal {
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
graph_fuse_zero_var :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span: Span) {
    graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, b.g.name[decl], decl, t, span))
}

// A fused body's types, now that its widths are known: as the builder types
// what it builds after checking.
@(private="file")
graph_fuse_settle :: proc(b: ^Graph_Builder, f: ^Graph_Fuse) {
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
    // A scope holding values on the arena (graph_scope_open): its mark and
    // resets, where the builder makes them; else none. Main's own body sets
    // the arena up and leaves it with the program.
    main, _ := b.checked.functions["main"]
    for m in f.marks {
        keep := (main == nil || g.type_[m.block] != Type(main)) && graph_has_big_values(b, m.body, m.nrvo)
        if keep { continue }
        graph_drop(b, m.mark, NO_VALUE)
        for r in m.resets { graph_drop(b, r, NO_VALUE) }
    }
    // A big local's space on the arena, taken before its value.
    for a in f.allocs {
        t := g.type_[a.decl]
        if t != nil && routes_to_arena(t) && g.name[a.decl] != a.nrvo {
            g.type_[a.var], g.type_[a.alloc] = t, t
            continue
        }
        graph_drop(b, a.var, NO_VALUE); graph_drop(b, a.alloc, NO_VALUE)
    }
    for pc in f.calls {
        braces := strings.has_suffix(g.name[pc.op], "{}")   // a literal's construction, as written
        g.name[pc.op] = graph_call_name(pc.callee)
        if braces { g.name[pc.op] = strings.concatenate({g.name[pc.op], "{}"}) }
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
        if resolve(b, k.lo).op in g.consts && resolve(b, k.hi).op in g.consts {
            graph_drop(b, k.ids[0], NO_VALUE); graph_drop(b, k.ids[1], NO_VALUE)
        }
    }
    segs := make([dynamic]int, 0, 1 + len(f.steps), context.temp_allocator)
    append(&segs, f.seg)
    append(&segs, ..f.steps[:])
    for si in segs {
        k := 0   // (its synthetic locals, in the order they were made)
        for p in b.segs[si].pieces {
            for i in p.nodes[0] ..< p.nodes[1] {
                for k < len(f.slots) && int(f.slots[k]) < i { k += 1 }
                g.type_[i] = graph_settled(g.type_[i], pointee = k < len(f.slots) && int(f.slots[k]) == i)
            }
        }
    }
    // Params by their scope's types: a default's width is settled once its
    // body is checked (solidify_param_defaults).
    for p, k in f.ts.params { g.type_[f.root + 1 + Node_Id(k)] = graph_settled(p.type_) }
}

// The statement the checker is on, as graph_stmt enters one: its entry, the
// first time. A statement the checker meets only once is `fresh` (a body's
// own statements, some of them values without an identity).
graph_fuse_stmt :: proc(b: ^Graph_Builder, s: Stmt, fresh := false) -> (saved: i32) {
    f := b.fuse
    saved = b.stmt
    key := stmt_key(s)
    if !fresh {
        if key == nil { return }   // (only a body's own statements are values)
        if at, seen := f.stmts[key]; seen {
            b.stmt = at
            return
        }
    }
    b.stmt = i32(len(b.g.stmts))
    append(&b.g.stmts, Graph_Stmt{span = stmt_span(s), kind = graph_stmt_kind(s)})
    if key != nil { f.stmts[key] = b.stmt }
    return
}

graph_fuse_stmt_end :: proc(b: ^Graph_Builder, saved: i32) {
    b.stmt = saved
}

// A statement of the body's code, before it is checked: one right after a
// return, break or continue is unreachable, as graph_body_stmt records.
graph_fuse_body_stmt :: proc(b: ^Graph_Builder, s: Stmt) {
    if b.code.active && b.code.run == nil && graph_runs_code(s) {
        append(&b.g.unreachable, stmt_span(s))
    }
}

// A definition in a fused body, where it is written: built by the builder,
// from here, when the body is placed.
graph_fuse_def :: proc(b: ^Graph_Builder, s: Stmt) {
    seg := &b.segs[b.seg]
    append(&seg.defs, Graph_Def{s = s, parent = b.code.block, anchor = graph_anchor_here(b)})
}

// Put a fused body where its scope is, and build its definitions where each
// is written.
@(private="file")
graph_fuse_place :: proc(b: ^Graph_Builder, si: int, parent: Node_Id, name: string) {
    graph_anchor_here(b, si)
    graph_segment_place(b, si, parent, b.stmt, name)
    defs := b.segs[si].defs[:]   // (placing them grows b.segs)
    for d in defs {
        // (A constant: built as the checker settled it.)
        if early, settled := b.def_segs[stmt_key(d.s)]; settled {
            if early.parent != d.parent { graph_fatal(stmt_span(d.s), "a definition built in another block") }
            b.segs[si].anchors[d.anchor].seg = early.seg
            continue
        }
        sub, saved := graph_segment_enter(b)
        b.segs[si].anchors[d.anchor].seg = sub
        graph_decl_stmt(b, d.s, d.parent, {kind = .Local})
        graph_segment_leave(b, saved)
    }
}

// A body's definition the checker settles — a constant: its declaration,
// built once its declarations pass has, in the block it is written in, in a
// segment of its own put where it is when the body is placed.
Graph_Def_Built :: struct {
    seg:    int,
    parent: Node_Id,
}

graph_fuse_def_settled :: proc(b: ^Graph_Builder, s: Stmt) {
    if _, is_const := s.(^Stmt_Define); !is_const { return }
    parent := b.code.block
    si, saved := graph_segment_enter(b)
    code, names, base := b.code, len(b.names), b.fn_base
    b.code, b.fn_base = {}, names
    graph_decl_stmt(b, s, parent, {kind = .Local})
    b.code, b.fn_base = code, base
    resize(&b.names, names)
    graph_segment_leave(b, saved)
    b.def_segs[stmt_key(s)] = {si, parent}
}

// A statement's identity, for the pointer variants.
stmt_key :: proc(s: Stmt) -> rawptr {
    #partial switch v in s {
    case ^Stmt_Assign:              return v
    case ^Stmt_Multi_Assign:        return v
    case ^Stmt_Multi_Return_Assign: return v
    case ^Stmt_Decl:                return v
    case ^Stmt_Define:              return v
    case ^Stmt_If:                  return v
    case ^Stmt_For:                 return v
    case ^Stmt_Scope:               return v
    case ^Stmt_Defer:               return v
    case ^Stmt_Match:               return v
    case ^Stmt_Foreign:             return v
    case ^Stmt_Union_Def:           return v
    case ^Stmt_Distinct_Def:        return v
    case ^Stmt_Dispatch_Def:        return v
    }
    return nil
}


// What a scope's contents change in the builder, until they end.
@(private="file")
Graph_Contents :: struct {
    base, names: int,
    self:        Node_Id,
    code:        Code,
    n:           Node_Id,
    span:        Span,
    intrinsic:   bool,
}

// A scope's contents up to its statements: a fresh set of names, its params
// and results, and its code's start.
@(private="file")
graph_contents_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, s: ^Stmt_Scope, n: Node_Id, body: []Stmt) -> Graph_Contents {
    kind := b.g.kind[n]
    gc := Graph_Contents{base = b.fn_base, names = len(b.names), self = b.self, n = n, span = s.span, intrinsic = s.is_intrinsic}
    b.fn_base = gc.names
    b.self = n if kind == .Struct else NO_NODE
    for p in ts.params { graph_bind(b, p.name, graph_node(b, .Param, .Explicit, n, p.name, p.type_, s.span)) }
    graph_results(b, ts, n, s.span)
    // An intrinsic's body is generated at each call: no code of its own.
    if s.is_intrinsic { return gc }
    gc.code = graph_code_begin(b, n, graph_nrvo(ts, body) if kind == .Fun else "")
    // The program's struct is the compiler's: main's entry sets up its
    // storage (`this_program = Program(…)` names the arena), and nothing
    // constructs it.
    b.code.managed = kind == .Struct && ts == (b.checked.table.funs["Program"] or_else nil)
    graph_scope_open(b, n, body, s.span)
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
    resize(&b.names, gc.names)
    b.fn_base, b.self = gc.base, gc.self
}

// The local a fun builds in its caller's return slot: the one every return
// names, when the fun returns one aggregate (find_nrvo_candidate, as codegen).
@(private="file")
graph_nrvo :: proc(ts: ^Type_Scope, body: []Stmt) -> string {
    if len(ts.return_types) != 1 { return "" }
    single := distinct_base(ts.return_types[0])
    aggregate := as_struct_body(single) != nil
    #partial switch _ in single {
    case ^Type_Fixed_Array, ^Type_Slice: aggregate = true
    }
    if _, pa := distinct_base(single).(^Type_Partial_Array); pa { aggregate = true }
    return find_nrvo_candidate(body) if aggregate else ""
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
        if named { graph_bind(b, name, r) }   // a named result is a local
    }
}

@(private="file")
graph_foreign :: proc(b: ^Graph_Builder, f: ^Foreign_Fun, parent: Node_Id) {
    ts, ok := graph_one(b, f.span, f.name).(^Type_Scope)
    if !ok { graph_fatal(f.span, "foreign '%s' is not a function", f.name) }
    n := graph_node(b, .Fun, .Explicit, parent, f.name, ts, f.span)
    b.g.scope_node[ts] = n
    for p in ts.params { graph_node(b, .Param, .Explicit, n, p.name, p.type_, f.span) }
    graph_results(b, ts, n, f.span)
    graph_close(b, n)
}

// A union holds its variants, each a struct; an enum holds its variant names.
@(private="file")
graph_union :: proc(b: ^Graph_Builder, v: ^Stmt_Union_Def, parent: Node_Id) {
    generic := len(v.generic_params) > 0
    written: Written = .Synthetic if generic else .Explicit
    found := false
    for t in b.by_span[v.span] {
        #partial switch u in t {
        case ^Type_Union:
            found = true
            name := v.name if !generic else ask_demangle(u.name, u.home_package)
            n := graph_node(b, .Union, written, parent, name, u, v.span)
            for variant in u.variants {
                st, st_ok := b.checked.table.structs[u.variant_structs[variant]]
                if !st_ok { graph_fatal(v.span, "variant '%s' of '%s' has no struct", variant, v.name) }
                vn := graph_node(b, .Struct, .Explicit, n, variant, st, st.body_span)
                b.g.scope_node[st] = vn
                for f in st.fields {
                    fw: Written = .Synthetic if strings.has_prefix(f.name, "__") else .Explicit   // the tag, its padding
                    graph_node(b, .Field, fw, vn, f.name, f.type_, st.body_span)
                }
                graph_close(b, vn)
            }
            graph_close(b, n)
        case ^Type_Enum:
            if u.is_synthetic { continue }   // a union's tag enum
            found = true
            n := graph_node(b, .Enum, written, parent, v.name, u, v.span)
            for variant in v.variants { graph_node(b, .Variant, .Explicit, n, variant.name, u, variant.span) }
            graph_close(b, n)
        }
    }
    if !found && !generic { graph_fatal(v.span, "'%s' reached the graph unchecked", v.name) }
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

// A union arm's payload: the variant struct the checker resolved.
@(private="file")
graph_arm_type :: proc(b: ^Graph_Builder, arm: ^Match_Arm, span: Span) -> Type {
    if st, ok := b.checked.table.structs[arm.resolved_struct]; ok { return st }
    if ft, ok := b.checked.table.funs[arm.resolved_struct]; ok    { return ft }
    graph_fatal(span, "match arm '%s' has no resolved variant", arm.variant)
}

// --- checks -------------------------------------------------------------------

// Every checked scope and type the program declares is exactly one node.
@(private="file")
graph_check_coverage :: proc(b: ^Graph_Builder) {
    count: map[rawptr]int
    defer delete(count)
    for t, id in b.g.type_ {
        #partial switch b.g.kind[id] {
        case .Fun, .Struct, .Union, .Enum, .Type_Def: count[graph_type_ptr(t)] += 1
        }
    }
    bad := 0
    check :: proc(count: ^map[rawptr]int, bad: ^int, t: Type, span: Span) {
        if n := count[graph_type_ptr(t)]; n != 1 {
            loc := format_location(span.file, span.line, span.col)
            emit_diagnostic(.Graph_Error, loc, "'%s' is %d nodes of the graph, not 1", ask_type_name(t), n)
            bad^ += 1
        }
    }
    t := b.checked.table
    for _, ft in b.checked.functions { if !ft.is_module { check(&count, &bad, ft, ft.body_span) } }
    for _, st in t.structs           { if !st.is_module { check(&count, &bad, st, st.body_span) } }
    for _, u in t.unions             { check(&count, &bad, u, u.span) }
    for _, e in t.enums              { if !e.is_synthetic { check(&count, &bad, e, e.span) } }
    for _, d in t.distinct_types     { check(&count, &bad, d, d.span) }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// Refers-to is complete: every var operation names a declaration.
@(private="file")
graph_check_refers :: proc(b: ^Graph_Builder) {
    g := b.g
    bad := 0
    for k, id in g.kind {
        if k == .Op && g.op[id] == .Var && g.refers[id] == NO_NODE {
            o := g.origin[id]
            emit_diagnostic(.Graph_Error, format_location(o.file, o.line, o.col), "'%s' names no declaration", g.name[id])
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
    for p := g.parent[id]; p != NO_NODE; p = g.parent[p] {
        #partial switch g.kind[p] {
        case .Fun, .Struct: return g.type_[p].(^Type_Scope)
        }
    }
    return nil
}

// The runs are well formed: every operation is in exactly one run; a run
// ends in its only terminator; Then edges land on the first operation of a
// run; and an operand dominates its use: earlier in the same run, or in a run
// every path to the use passes through.
@(private="file")
graph_check_runs :: proc(b: ^Graph_Builder) {
    g := b.g
    n_runs := len(g.run_first) - 1
    run_of := make([]i32, len(g.kind))
    pos := make([]i32, len(g.kind))
    defer delete(run_of)
    defer delete(pos)
    slice.fill(run_of, -1)
    bad := 0
    report :: proc(g: ^Program_Graph, bad: ^int, id: Node_Id, format: string, args: ..any) {
        o := g.origin[id]
        emit_diagnostic(.Graph_Error, format_location(o.file, o.line, o.col), format, ..args)
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
        if e.kind != .Then { continue }
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
graph_dump :: proc(g: ^Program_Graph) {
    want := os.get_env("MARA_GRAPH", context.temp_allocator)
    if want == "" { return }
    if want == "full" {
        graph_dump_full(g)
        return
    }
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
                if e.kind == .Then { fmt.sbprintf(&sb, "  → run %d", run_of[e.to]) }
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
graph_dump_full :: proc(g: ^Program_Graph) {
    span :: proc(s: Span) -> string {
        return fmt.tprintf("%s:%d:%d", filepath.base(s.file), s.line, s.col) if s.file != "" else "-"
    }
    fmt.printf("graph: %d nodes, %d runs, %d edges\n", len(g.kind), len(g.run_first) - 1, len(g.edges))
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
        if s, ok := g.assert_sides[Node_Id(id)]; ok { fmt.sbprintf(&b, " sides=%q|%q", s[0], s[1]) }
        if e, ok := g.const_values[Node_Id(id)]; ok { fmt.sbprintf(&b, " value@%s", span(expr_span(e)^)) }
        fmt.println(strings.to_string(b))
    }
    for e in g.edges { fmt.printfln("e %d -> %d %v %v site%d", e.from, e.to, e.kind, e.written, e.site) }
    for r in 0 ..< len(g.run_first) - 1 {
        b := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&b, "r %d:", r)
        for op in graph_run(g, r) { fmt.sbprintf(&b, " %d", op) }
        fmt.println(strings.to_string(b))
    }
    for s, i in g.stmts { fmt.printfln("s %d %v @%s", i, s.kind, span(s.span)) }
    for s in g.unreachable { fmt.printfln("u @%s", span(s)) }
    for id in g.settled { fmt.printfln("settled %d", id) }
    names := make([dynamic]string, 0, len(g.scope_node), context.temp_allocator)
    for ts, id in g.scope_node { append(&names, fmt.tprintf("scope %s %d", ts.name, id)) }
    slice.sort(names[:])
    for n in names { fmt.println(n) }
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
        for e in graph_out(g, id) {
            if e.kind != .Then { fmt.sbprintf(&b, " → %d", e.to) }
        }
    } else {
        fmt.sbprintf(&b, "%d %s %s", id, graph_kind_word(g.kind[id]), g.name[id])
        if t := g.type_[id]; t != nil {
            #partial switch g.kind[id] {
            case .Field, .Param, .Result, .Local, .Const, .Import, .Type_Def:
                fmt.sbprintf(&b, " : %s", type_name(t))
            }
        }
        // Where its value flows: to a declaration, at an operation.
        for e in graph_out(g, id) {
            if e.kind == .Flows { fmt.sbprintf(&b, "  ⇒ %d@%d", e.to, e.site) }
        }
    }
    if o := g.origin[id]; o.file != "" { fmt.sbprintf(&b, "   %s:%d", filepath.base(o.file), o.line) }
    if g.written[id] == .Synthetic { strings.write_string(&b, "   (synthetic)") }
    else if g.written[id] == .Implied { strings.write_string(&b, "   (implied)") }
    fmt.println(strings.to_string(b))
}

graph_kind_word :: proc(k: Node_Kind) -> string {
    switch k {
    case .Module:   return "module"
    case .Struct:   return "struct"
    case .Union:    return "union"
    case .Enum:     return "enum"
    case .Fun:      return "fun"
    case .Block:    return "block"
    case .Field:    return "field"
    case .Param:    return "param"
    case .Result:   return "result"
    case .Local:    return "local"
    case .Const:    return "const"
    case .Import:   return "import"
    case .Variant:  return "variant"
    case .Type_Def: return "type"
    case .Dispatch: return "dispatch"
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
