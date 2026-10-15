package mara

import "core:sync"

import "core:fmt"
import "core:mem"
import "core:mem/virtual"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The program's code (design/annotated_tree.md, stage 4): what the analyses
// and the emitter read. Lowering builds it from the annotated tree once the
// check is clean (lower.odin, through Graph_Builder and the graph_build_*
// procs): each fun's, struct's constructor's and constant's code, a graph of
// its own, built one at a time and put in written order (Program_Code).
//
// A code's nodes are its scopes — its own and its blocks — the variables they
// declare, and operations (the set in design/program_graph.md § Operations).
// Each fact is a column indexed by Node_Id, the code's own from 0: its root,
// then everything in it, depth-first in written order, so a scope's subtree
// is one run of ids: [id, last[id]]. Lowering builds a code's nodes in that
// order, each one it decides it needs from the annotations before it builds
// it: nothing built is left out.
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

// A statement code is lowered from: where it is written and what it does to
// the variables it writes, which is how an analysis reports a write.
Graph_Stmt :: struct {
    node: Tree_Id,   // (graph_stmt's: the tree's statement, or the target of one of several)
    span: Span,
    kind: Stmt_Kind,
}

// An operation's statement, the tree's: the one around its tree node
// (tree_stmt) — or, of the several lowering makes of one (`a, b = c, d`,
// `x, y := v`), its target's (Program_Graph.sub): the statement's span, the
// target's kind.
graph_stmt :: proc(g: ^Program_Graph, id: Node_Id) -> Graph_Stmt {
    t := &build_tree
    if target, of := g.sub[id]; of {
        s := tree_stmt(t, target)
        kind := Stmt_Kind.Decl if t.tag[s] == .Decl && t.tag[target] == .Ident else tree_assign_kind(t, target)
        return {node = target, span = tree_span(t, s), kind = kind}
    }
    _, n := annot_split(g.syntax[id])
    s := tree_stmt(t, n)
    if s == 0 { return {} }
    return {node = s, span = tree_span(t, s), kind = tree_stmt_kind(t, s)}
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
    // A subtree is one run of ids, [id, its last] (graph_last): the code's,
    // [0, end]; a block's, by it (a node not here: itself).
    end:     Node_Id,
    last:    map[Node_Id]Node_Id,
    name:    [dynamic]Name_Id,  // (its text: graph_name)
    names:   ^[dynamic]string,  // (its tables' names, a node's by its Name_Id)
    tables:  ^Graph_Tables,     // (its builder's: names, types and values, by id)
    type_:   [dynamic]Type_Id,  // has type; none when the node has none (its type: graph_type)
    types:   ^[dynamic]Type,    // (the program's types, a node's by its Type_Id)
    origins: map[Node_Id]Span,  // where a node is written, where that isn't its tree node's (graph_origin)
    binds:   map[Node_Id]Node_Id,   // a variant operation that binds a match arm's payload → the binding (graph_refers)
    // What a call or construction runs is its tree node's annotated callee
    // (graph_called) — but where lowering says otherwise: a call through a
    // fun's value, none; one written in a default a call leaves off, its own.
    callee:    map[Node_Id]^Type_Scope,
    annotated: ^map[Syntax_Id]^Type_Scope,   // (the annotations' callees: Annotations.callees)
    defer_of: map[Node_Id]Node_Id,      // a run-defer operation → the defer block it runs
    decl_tok: [dynamic]Token_Id,      // a variable's declaration — a param, a named result, a local — → the token that declares it (0: none)
    syntax:  [dynamic]Syntax_Id,      // the tree node it was lowered from, in its instance (0: none) — what's written that made it
    // One of the statements lowering makes of one — `a, b = c, d`, `x, y :=
    // v`: each target its own — an operation's target (graph_stmt).
    sub:     map[Node_Id]Tree_Id,

    // A node's operands are operands[operand_first[id] : operand_first[id+1]].
    operands:      [dynamic]Operand,
    operand_first: [dynamic]i32,
    // A variable where it's used: no node, a leaf — an operand's, its id
    // LEAF past leaves[0]'s (graph_var). A constant likewise, its id CONST
    // past consts[0]'s (graph_const).
    leaves: [dynamic]Graph_Leaf,
    consts: [dynamic]Graph_Const,
    // A variable's value read where it's used, as its leaf is (graph_read):
    // no node, an operation of its run, its id READ past reads[0]'s — the
    // leaf it reads.
    reads:  [dynamic]Operand,

    // Run r is run_ops[run_first[r] : run_first[r+1]], in the order it runs;
    // run_heads, each run by its first operation (where a Then edge lands),
    // sorted by it (graph_run_starting).
    run_ops:    [dynamic]Node_Id,
    run_first:  [dynamic]i32,
    run_heads:  []Run_Head,
    // The runs its entry reaches, then its defer blocks' (graph_code_runs),
    // worked out once it's built; how many are its own code's.
    code_runs:  []i32,
    code_own:   int,

    // The Then edges, sorted by `from` (a node's in the order they were
    // made): a node's, graph_out's.
    edges:     [dynamic]Edge,

    // Statements right after a return, break or continue: the first of each
    // stretch.
    unreachable: [dynamic]Span,
    settled:     [dynamic]Node_Id,   // literals whose type is their use's (a `:=` width adopted, an operand's): for the range check

    // A string constant's global: its text (a constant's value is its
    // leaf's, Graph_Const). (Read with graph_value.)
    texts:  map[Node_Id]Const_Id,
    values: ^[dynamic]Const_Value,   // (the program's values, a node's by its Const_Id)

    // An assert on a comparison: each side's source text, which its failure
    // reports beside the side's value — "" for a side whose text states its
    // value (a literal, a variant).
    assert_sides: map[Node_Id][2]string,

    // A constant, by its value's node (Graph_Named.value; 0: none): an
    // operation that names one — its value at the use, a table's global.
    constant: map[Node_Id]Syntax_Id,

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

// A node's value, as the program's values hold it (Program_Code.values):
// each one once, by its index; 0, none.
Const_Id :: distinct u32

// A constant's value (a leaf's), a global's text, if it has one.
graph_value :: proc(g: ^Program_Graph, id: Node_Id) -> (Const_Value, bool) {
    v := g.consts[id - CONST].value if id >= CONST && id < LEAF else g.texts[id] or_else 0
    if v == 0 { return {}, false }
    return g.values[v], true
}

// A node's value given: its code's tables' id for it, made the first time
// they have it (Graph_Tables.value_ids) — a small integer's, kept at hand.
graph_set_value :: proc(g: ^Program_Graph, id: Node_Id, c: Const_Value) {
    b := g.tables
    // (A small integer's float none, or itself: `1` is read as either.)
    small := !c.is_float && !c.is_text && c.int >= 0 && c.int < len(b.value_small[0])
    as := 0 if transmute(u64)c.float == 0 else 1
    if c.float != 0 && c.float != f64(c.int) { small = false }
    if id < CONST {
        if id not_in g.texts { g.texts[id] = 0 }
    }
    at := &g.consts[id - CONST].value if id >= CONST && id < LEAF else &g.texts[id]
    if small && b.value_small[as][c.int] != 0 {
        at^ = b.value_small[as][c.int]
        return
    }
    // (A float by its bits: -0.0 is not 0.0.)
    key := Const_Key{c.int, transmute(u64)c.float, c.is_float, c.is_text, c.text}
    v, seen := b.value_ids[key]
    if !seen {
        v = Const_Id(len(b.values))
        append(&b.values, c)
        b.value_ids[key] = v
    }
    if small { b.value_small[as][c.int] = v }
    at^ = v
}

@(private="file")
Const_Key :: struct { int: i128, float: u64, is_float, is_text: bool, text: string }

graph_out :: proc(g: ^Program_Graph, id: Node_Id) -> []Edge {
    if id >= CONST { return nil }   // (a leaf, a read: none)
    edges := g.edges[:]
    lo, hi := 0, len(edges)
    for lo < hi {
        mid := (lo + hi) / 2
        if edges[mid].from < id { lo = mid + 1 } else { hi = mid }
    }
    end := lo
    for end < len(edges) && edges[end].from == id { end += 1 }
    return edges[lo:end]
}

// A run's first operation, and the run (graph_run_starting).
Run_Head :: struct {
    op:  Node_Id,
    run: i32,
}

// The run whose first operation `op` is — where a Then edge to it lands —
// by its place among the code's runs (0: none).
graph_run_starting :: proc(g: ^Program_Graph, op: Node_Id) -> i32 {
    heads := g.run_heads
    lo, hi := 0, len(heads)
    for lo < hi {
        mid := (lo + hi) / 2
        if heads[mid].op < op { lo = mid + 1 } else { hi = mid }
    }
    return heads[lo].run if lo < len(heads) && heads[lo].op == op else 0
}

graph_operands :: proc(g: ^Program_Graph, id: Node_Id) -> []Operand {
    if id >= READ { return g.reads[id - READ:][:1] }   // (a read: its leaf)
    if id >= CONST { return nil }   // (a leaf: none)
    return g.operands[g.operand_first[id]:g.operand_first[id + 1]]
}

// Where a whole write lands — `e = f()` writes e, reading nothing — its
// destination's leaf; NO_NODE for any other operation.
graph_whole_write_dest :: proc(g: ^Program_Graph, op: Node_Id) -> Node_Id {
    #partial switch graph_op_of(g, op) {
    case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Arena_Alloc:
        ops := graph_operands(g, op)
        if len(ops) > 0 && graph_is_leaf(ops[0].op) { return ops[0].op }
    }
    return NO_NODE
}


// A node's name, as the program's names hold it (Program_Code.names): each
// one once, by its index.
Name_Id :: distinct u32

// The text of a node's name; a leaf's, its declaration's (a struct's code's
// own, `Self`).
graph_name :: proc(g: ^Program_Graph, id: Node_Id) -> string {
    if id >= READ { return "" }
    if id >= CONST && id < LEAF { return g.names[g.consts[id - CONST].name] }
    if id >= LEAF {
        d := g.leaves[id - LEAF].decl
        if d < 0 { return graph_outside_name(int(-3 - d)) }
        if d == 0 && g.kind[0] == .Struct { return "Self" }
        return g.names[g.name[d]]
    }
    return g.names[g.name[id]]
}

// A name's id, made the first time the program names it. (One at an address
// it was seen at before is found there, unhashed.)
@(private="file")
graph_intern :: proc(b: ^Graph_Builder, s: string) -> Name_Id {
    return graph_intern_in(b.tables, s)
}

@(private="file")
graph_intern_in :: proc(b: ^Graph_Tables, s: string) -> Name_Id {
    if len(s) == 0 { return 0 }
    names := &b.names
    slot := &b.name_cache[(uintptr(raw_data(s)) >> 3 ~ uintptr(len(s))) & (len(b.name_cache) - 1)]
    if slot.data == raw_data(s) && slot.len == len(s) && names[slot.id] == s { return slot.id }
    id, found := b.name_ids[s]
    if !found {
        id = Name_Id(len(names))
        append(names, s)
        b.name_ids[s] = id
    }
    slot^ = {raw_data(s), len(s), id}
    return id
}

// A node's type; a leaf's, its own as it was made, else its declaration's.
graph_type :: proc(g: ^Program_Graph, id: Node_Id) -> Type {
    id := id
    if id >= READ { id = g.reads[id - READ].op }   // (a read's: its leaf's)
    if id >= CONST && id < LEAF { return g.types[g.consts[id - CONST].type_] }
    if id >= LEAF {
        l := g.leaves[id - LEAF]
        if l.type_ != 0 || l.decl < 0 { return g.types[l.type_] }
        return g.types[g.type_[l.decl]]
    }
    return g.types[g.type_[id]]
}

// A variable named where it's used — `x` in `x + 1`, `x = v`, `x.f` — is
// no operation, but a leaf: the operand that names it, its id LEAF and
// past. Its declaration; its type, as it was made (0: its declaration's,
// as that is); the tree node it's written as.
Graph_Leaf :: struct {
    decl:   Node_Id,
    type_:  Type_Id,
    syntax: Syntax_Id,
}

LEAF :: Node_Id(1 << 30)

// A constant where it's used — `42`, `true`, `.Ok`, a named constant's value
// at its use, `void` — is a leaf too: its id CONST and past (below LEAF's).
// Its value (none: not computed here — graph_fold_code's, a named
// constant's), its type, its name (as written; `void`; `zero`), how it's
// written, the tree node it's written as.
Graph_Const :: struct {
    value:   Const_Id,
    type_:   Type_Id,
    name:    Name_Id,
    written: Written,
    syntax:  Syntax_Id,
}

CONST :: Node_Id(1 << 29)

// Whether an operand is a constant's leaf (graph_const).
graph_is_const :: #force_inline proc(id: Node_Id) -> bool {
    return id >= CONST && id < LEAF
}

// A variable's value read where it's used — `x` in `x + 1` — is no node
// either: a read, an operation of its run with no columns, its id READ and
// past (above the leaves'): the leaf it reads (Program_Graph.reads), its
// type, its tree node and how it's written that leaf's.
READ :: Node_Id(3 << 29)

// Whether an operand is a variable, used: a leaf (graph_var).
graph_is_leaf :: #force_inline proc(id: Node_Id) -> bool {
    return id >= LEAF && id < READ
}

// An operation's index among a code's operations and reads, one space: a
// node's its id, a read's past every node's (graph_ix_count) — for what an
// analysis keeps by operation.
graph_ix :: #force_inline proc(g: ^Program_Graph, id: Node_Id) -> int {
    return len(g.kind) + int(id - READ) if id >= READ else int(id)
}
graph_ix_count :: proc(g: ^Program_Graph) -> int {
    return len(g.kind) + len(g.reads)
}

// Whether an operation is a variable's read (graph_read).
graph_is_read :: #force_inline proc(id: Node_Id) -> bool {
    return id >= READ
}

// The declaration of the variable a leaf is (NO_NODE: no leaf).
graph_leaf_decl :: #force_inline proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    return g.leaves[id - LEAF].decl if id >= LEAF && id < READ else NO_NODE
}

// What an operand is, an operation or a leaf: a leaf an operation of kind
// var, which refers to its declaration; a read, one of kind read.
graph_kind_of :: #force_inline proc(g: ^Program_Graph, id: Node_Id) -> Node_Kind {
    return .Op if id >= CONST else g.kind[id]
}
graph_op_of :: #force_inline proc(g: ^Program_Graph, id: Node_Id) -> Op_Kind {
    return .Read if id >= READ else .Var if id >= LEAF else .Const if id >= CONST else g.op[id]
}
graph_refers :: #force_inline proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    if id >= READ { return NO_NODE }
    return g.leaves[id - LEAF].decl if id >= LEAF else NO_NODE if id >= CONST else g.binds[id] or_else NO_NODE
}

// How a node is written; a leaf as its declaration is — but the compiler's
// own globals, as their names are written (graph_place_outside's: past the
// code's own, no parent).
graph_written :: proc(g: ^Program_Graph, id: Node_Id) -> Written {
    id := id
    if id >= READ { id = g.reads[id - READ].op }   // (a read's: its leaf's)
    if id >= CONST && id < LEAF { return g.consts[id - CONST].written }
    if id < LEAF { return g.written[id] }
    d := g.leaves[id - LEAF].decl
    if d < 0 || g.kind[d] == .Field && g.parent[d] == NO_NODE { return .Explicit }
    return g.written[d]
}

// The tree node a node or a leaf was lowered from.
graph_syntax :: proc(g: ^Program_Graph, id: Node_Id) -> Syntax_Id {
    id := id
    if id >= READ { id = g.reads[id - READ].op }   // (a read's: its leaf's)
    if id >= CONST && id < LEAF { return g.consts[id - CONST].syntax }
    return g.leaves[id - LEAF].syntax if id >= LEAF else g.syntax[id]
}

// The leaves' ids.
graph_leaf_ids :: proc(g: ^Program_Graph) -> (lo, hi: Node_Id) {
    return LEAF, LEAF + Node_Id(len(g.leaves))
}

// The last id of a node's subtree.
graph_last :: proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    if id == 0 { return g.end }
    return g.last[id] or_else id
}

// The fun or struct a call or construction runs, as the checker annotated
// its tree node — unless lowering says otherwise (Program_Graph.callee);
// nil through a function value.
graph_called :: proc(g: ^Program_Graph, op: Node_Id) -> ^Type_Scope {
    if graph_kind_of(g, op) != .Op || (graph_op_of(g, op) != .Call && graph_op_of(g, op) != .Construct) { return nil }
    if len(g.callee) > 0 {
        if callee, own := g.callee[op]; own { return callee }
    }
    return g.annotated^[g.syntax[op]] or_else nil
}

// What a call runs, kept only where its tree node's annotation doesn't say so.
graph_set_callee :: proc(g: ^Program_Graph, op: Node_Id, callee: ^Type_Scope) {
    if callee == (g.annotated^[g.syntax[op]] or_else nil) {
        if len(g.callee) > 0 { delete_key(&g.callee, op) }
        return
    }
    g.callee[op] = callee
}

// The signature a call runs by: its callee's, or — through a function value,
// its first operand — that value's type.
graph_signature :: proc(g: ^Program_Graph, op: Node_Id) -> ^Type_Scope {
    if callee := graph_called(g, op); callee != nil { return callee }
    ops := graph_operands(g, op)
    if graph_op_of(g, op) != .Call || len(ops) == 0 || ops[0].op == NO_NODE { return nil }
    ft, is_fn := distinct_base(graph_type(g, ops[0].op)).(^Type_Scope)
    return ft if is_fn && ft.kind == .Fun else nil
}

graph_run :: proc(g: ^Program_Graph, r: int) -> []Node_Id {
    return g.run_ops[g.run_first[r]:g.run_first[r + 1]]
}

// Each run by its first operation (g.run_heads), once the runs are final.
@(private="file")
graph_index_runs :: proc(g: ^Program_Graph) {
    heads := make([dynamic]Run_Head, 0, len(g.run_first))
    for r in 0 ..< len(g.run_first) - 1 {
        if ops := graph_run(g, r); len(ops) > 0 { append(&heads, Run_Head{ops[0], i32(r)}) }
    }
    for i in 1 ..< len(heads) {   // (by insertion: a code has few, mostly in order)
        for j := i; j > 0 && heads[j - 1].op > heads[j].op; j -= 1 { heads[j - 1], heads[j] = heads[j], heads[j - 1] }
    }
    g.run_heads = heads[:]
}

// Whether a fun or struct's code can reach its end without a return: the
// synthetic return that ends its body, in a run its entry reaches.
graph_falls_off :: proc(g: ^Program_Graph, scope: Node_Id) -> bool {
    seen: map[i32]bool
    defer delete(seen)
    todo: [dynamic]i32
    defer delete(todo)
    for e in graph_out(g, scope) { append(&todo, graph_run_starting(g, e.to)) }
    for len(todo) > 0 {
        r := pop(&todo)
        if r in seen { continue }
        seen[r] = true
        ops := graph_run(g, int(r))
        last := ops[len(ops) - 1]
        if graph_op_of(g, last) == .Return && graph_written(g, last) == .Synthetic { return true }
        for e in graph_out(g, last) { append(&todo, graph_run_starting(g, e.to)) }
    }
    return false
}

// A fun's (or struct's) code as runs: those its entry reaches, then those of
// each defer block a run defer in them runs. Returns how many are its own
// code's; each list keeps a run's successors after it.
graph_code_runs :: proc(g: ^Program_Graph, scope: Node_Id, out: ^[dynamic]i32) -> (own: int) {
    if scope == 0 && g.code_runs != nil {   // (the code's own: worked out when it was built, graph_code_close)
        prior := len(out)
        append(out, ..g.code_runs)
        return prior + g.code_own
    }
    // (Which runs are listed, by run: a code has few, so here unless many.)
    few: [256]bool
    n := len(g.run_first) - 1
    seen := few[:n] if n <= len(few) else make([]bool, n)
    defer if n > len(few) { delete(seen) }
    todo := make([dynamic]i32, 0, 16)
    defer delete(todo)
    reach :: proc(g: ^Program_Graph, scope: Node_Id, out: ^[dynamic]i32, seen: []bool, todo: ^[dynamic]i32) {
        for e in graph_out(g, scope) { append(todo, graph_run_starting(g, e.to)) }
        for len(todo) > 0 {
            r := pop(todo)
            if seen[r] { continue }
            seen[r] = true
            append(out, r)
            ops := graph_run(g, int(r))
            // Depth-first in edge order keeps a run's successors after it.
            next := graph_out(g, ops[len(ops) - 1])
            for i := len(next) - 1; i >= 0; i -= 1 {
                append(todo, graph_run_starting(g, next[i].to))
            }
        }
    }
    reach(g, scope, out, seen, &todo)
    own = len(out)
    if len(g.defer_of) == 0 { return }   // (no run defers: no defer blocks)
    for i := 0; i < len(out); i += 1 {
        for op in graph_run(g, int(out[i])) {
            if graph_op_of(g, op) != .Run_Defer { continue }
            reach(g, g.defer_of[op], out, seen, &todo)
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

// Lowering builds one code at a time — a fun's, a struct's constructor's, a
// constant's (graph_body_begin … graph_body_end, graph_const_begin …
// graph_const_end): its nodes in the order they end up in, where they stay
// (graph_code_new: its columns in their regions). Once built, a code is
// finished (graph_code_close); once every code is, each is put in written
// order (graph_place_codes).
Graph_Builder :: struct {
    prog:    ^Graph_Program,  // the program's: what every code built goes into
    g:       ^Program_Graph,  // the code being built
    checked: ^Checked_Program,
    at:      Syntax_Id,   // the tree node being lowered: each node made is its (Program_Graph.syntax)
    pin:     Syntax_Id,   // ... unless a default a call leaves off is: then the call's (lw_pin)
    sub:     Tree_Id,     // the target whose statement is being lowered, of several made of one (Program_Graph.sub)
    // The last node's tree node, and its span (graph_tree_span): what the
    // next node's origin is most likely to be — nodes come a tree node's
    // several at a time.
    span_of: Syntax_Id,
    span_is: Span,
    arena:      bool,    // the program has a scope arena: big values live on it
    runs:       [dynamic]^Run,   // every run the code being built made, kept for the next once it is done
    run_pool:   [dynamic]^Run,   // (those kept: graph_run_new)
    body_pool:  [dynamic]^Graph_Body,   // (bodies done, kept for the next: graph_body_new)
    nodes:      int,             // how many nodes the code being built has; the columns run ahead
    leaves:     int,             // ... and leaves (graph_leaf_new)
    consts:     int,             // ... and constants (graph_const_new)
    reads:      int,             // ... and reads (graph_read)
    code:       Code,
    // Refers-to: each declaration made in the code being built — a fun's, a
    // struct's, a constant's; its defers' are its own — by the token that
    // declares it (graph_declare, graph_local).
    locals:     map[Token_Id]Node_Id,
    // The compiler's own globals — this_program, context: their types, and
    // whether the code being built names one (graph_global).
    globals:       [2]Type,
    outside_named: bool,
    self:       Node_Id,         // what `Self` names in a struct's code
    main:       ^Type_Scope,     // main (its body marks no arena: graph_scope_open)
    // The body being built.
    body:     ^Graph_Body,
    // What the codes it builds are made in, its own: their columns, and the
    // names, types and values they hold by id — one builder's never
    // another's.
    store:      Graph_Store,
    tables:     ^Graph_Tables,
    type_table: ^Type_Table,   // (its tables' types)
}

// The names, types and values a builder's codes hold by id — each code
// points at its builder's (Program_Graph.tables; and .names, .types, .values
// for reading) — and what finds the id of one, made the first time a code
// has it (graph_intern, type_id, graph_set_value).
Graph_Tables :: struct {
    names:       [dynamic]string,
    name_ids:    map[string]Name_Id,
    name_cache:  [1024]struct { data: [^]u8, len: int, id: Name_Id },
    types:       Type_Table,
    values:      [dynamic]Const_Value,
    value_ids:   map[Const_Key]Const_Id,
    value_small: [2][256]Const_Id,
}

// The program's lowering: what every code built goes into, whichever builder
// built it.
Graph_Program :: struct {
    checked: ^Checked_Program,
    // Each module's statements, in written order: where the code each
    // defines goes (lower_place).
    module_stmts: map[Syntax_Id]int,
    module_list:  [dynamic]Graph_Module_Stmt,
    // Every name the checker's table has a constant under, by its value's id
    // (a module's constant is there under its flat name and its bare one):
    // what its table is named (graph_table_names).
    constant_names: map[string]Syntax_Id,
    // The codes built, waiting to be put in place: each fun's and
    // struct's by its scope, each constant's by its statement.
    bodies:   map[^Type_Scope]^Built_Code,
    consts:   map[Syntax_Id]^Built_Code,
    // The first body the checker couldn't build (an internal error, reported
    // once the check is found clean).
    failure:  struct { name, reason: string, span: Span },
    pc:       Program_Code,   // the codes, as each is built
    // What builders on several threads add here, and look up in pc while
    // they do (pc.lock), is added and looked up under it.
    lock:     sync.Mutex,
    allocator: mem.Allocator,   // what it's made with (the codes built are kept with it)
    region_size: uint,          // what each builder's regions reserve (graph_region_size)
}

// Where a builder's codes are made: an arena (their graphs, the tables they
// hold by id) and a region per column.
Graph_Store :: struct {
    arena:   ^virtual.Arena,
    regions: ^[Graph_Column]Graph_Region,
}

// A code built, waiting to be put in place; a body's definitions go after
// it.
@(private="file")
Built_Code :: struct {
    g:      ^Program_Graph,
    b:      ^Graph_Builder,   // the builder it was built by (its names: graph_place_scope)
    defs:   [dynamic]Graph_Decl,
    value:  Syntax_Id,   // a constant's: its value's node (Program_Code.consts' key)
    placed: bool,
}

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
// is one: as the code being built names it, its placeholder (OUTSIDE), made
// a node of its own past the code's once the code is built
// (graph_place_outside).
graph_global :: proc(b: ^Graph_Builder, name: string) -> Node_Id {
    switch name {
    case "this_program": b.outside_named = true; return OUTSIDE[0]
    case "context":      b.outside_named = true; return OUTSIDE[1]
    }
    return NO_NODE
}

@(private="file")
OUTSIDE :: [2]Node_Id{-3, -4}
@(private="file")
graph_outside_name :: proc(k: int) -> string { return "this_program" if k == 0 else "context" }

// Whether a declaration is one of the compiler's globals, as the code being
// built names them.
@(private="file")
graph_is_outside :: proc(b: ^Graph_Builder, d: Node_Id) -> bool {
    return d == OUTSIDE[0] || d == OUTSIDE[1]
}


// The code being built: a fun's body, a struct's field initializers, a defer's
// block. Saved and restored around a defer's.
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
    defers: [dynamic]Scope_Defer,   // defer blocks registered so far, in order
    // A local of its own lives on the arena (lowering says so, when it opens
    // the scope: graph_build_decl checks), so it marks the arena where it
    // begins and resets it at each exit (`arena`; not main's body).
    holds:  bool,
    arena:  bool,
    held:   int,                // (how many of its locals do)
}

// A defer registered with its scope: its block, and whether only a return
// that fails runs it (`defer?`).
@(private="file")
Scope_Defer :: struct {
    block:      Node_Id,
    on_failure: bool,
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

// The program's lowering, made once the program is checked (lower_begin).
graph_program_new :: proc(checked: ^Checked_Program, modules: map[string][]Graph_Decl) -> ^Graph_Program {
    p := new(Graph_Program)
    p.checked = checked
    graph_modules(p, modules)
    // What builders on other threads add to, made here: it grows with this
    // thread's allocator (Graph_Program.allocator), which only one thread uses
    // at a time — under the lock while they run, this one waiting for them.
    p.allocator = context.allocator
    p.region_size = graph_region_size()
    p.bodies = make(map[^Type_Scope]^Built_Code)
    p.consts = make(map[Syntax_Id]^Built_Code)
    p.pc.funs = make(map[^Type_Scope]^Program_Graph)
    p.pc.consts = make(map[Syntax_Id]^Program_Graph)
    p.pc.consumes = make(map[^Type_Scope]int)
    p.pc.tables = make(map[Syntax_Id]^Fold)
    p.pc.summaries = make(map[^Type_Scope]^Fun_Summary)
    return p
}

// A builder for the program's codes, with storage and tables of its own.
graph_builder_new :: proc(p: ^Graph_Program) -> ^Graph_Builder {
    checked := p.checked
    b := new(Graph_Builder)
    b.prog = p
    b.checked = checked
    b.arena = checked.table.has_scope_allocator || checked.table.context_expected_at_runtime
    b.main = checked.functions["main"] or_else nil
    for name, i in ([]string{"this_program", "context"}) {
        b.globals[i] = checked.table.builtins[name] or_else nil
    }
    b.store.arena = new(virtual.Arena)
    if err := virtual.arena_init_growing(b.store.arena); err != nil { graph_fatal({}, "no memory for the program's code") }
    in_store := virtual.arena_allocator(b.store.arena)
    b.store.regions = new([Graph_Column]Graph_Region, in_store)
    for &r in b.store.regions { r.want = p.region_size }
    b.tables = new(Graph_Tables, in_store)
    r := b.store.regions
    b.tables.names = make([dynamic]string, graph_region_allocator(&r[.Names]))
    append(&b.tables.names, "")   // (Name_Id 0: none)
    b.tables.types.types = make([dynamic]Type, graph_region_allocator(&r[.Types]))
    append(&b.tables.types.types, nil)   // (Type_Id 0: none)
    b.tables.values = make([dynamic]Const_Value, graph_region_allocator(&r[.Values]))
    append(&b.tables.values, Const_Value{})   // (Const_Id 0: none)
    b.type_table = &b.tables.types
    append(&p.pc.stores, b.store)
    return b
}

// A module's statement, and whether the checker has settled it (a constant, a
// variable: once, by the first pass over it).
Graph_Module_Stmt :: struct {
    d:       Graph_Decl,
    settled: bool,
}

// The program's modules' statements: the modules in name order, each's in
// written order — where the code each defines goes.
@(private="file")
graph_modules :: proc(b: ^Graph_Program, programs: map[string][]Graph_Decl) {
    modules := make([dynamic]string, 0, len(programs), context.temp_allocator)
    for name in programs { append(&modules, name) }
    slice.sort(modules[:])
    for name in modules {
        for d in programs[name] {
            b.module_stmts[d.id] = len(b.module_list)
            append(&b.module_list, Graph_Module_Stmt{d = d})
        }
    }
}

// A module's statement the checker has met: settled, if it's one it settles.
graph_module_stmt :: proc(b: ^Graph_Program, id: Syntax_Id) {
    i, is_module := b.module_stmts[id]
    if !is_module || b.module_list[i].settled { return }
    if b.module_list[i].d.settles { b.module_list[i].settled = true }
}

// A builder done with (its codes, and what they hold, stay: Program_Code.stores).
// (`made_in`: what its runs and bodies were made with — a worker's, its
// store's arena.)
graph_builder_free :: proc(b: ^Graph_Builder, made_in := context.allocator) {
    delete(b.runs)
    for r in b.run_pool {
        delete(r.ops)
        delete(r.waiting)
        free(r, made_in)
    }
    delete(b.run_pool)
    for f in b.body_pool { graph_body_drop(f, made_in) }
    delete(b.body_pool)
    delete(b.locals)
    // (What finds an id is done with — the codes read the tables' entries.)
    delete(b.tables.name_ids)
    delete(b.tables.value_ids)
    delete(b.tables.types.slots)
    free(b)
}

// The program's lowering done with, its codes kept (build_program_graph).
@(private="file")
graph_program_free :: proc(p: ^Graph_Program) {
    delete(p.constant_names)
    delete(p.module_stmts)
    delete(p.module_list)
    for _, c in p.bodies { delete(c.defs); free(c) }
    delete(p.bodies)
    for _, c in p.consts { free(c) }
    delete(p.consts)
    free(p)
}

// Every code lowered, each finished as it was: put in written order, and
// what reads across codes — the constants' values at their uses — worked out.
build_program_graph :: proc(b: ^Graph_Program) -> Program_Code {
    defer graph_program_free(b)
    if f := b.failure; f.reason != "" { graph_fatal(f.span, "the checker built no graph of '%s': %s", f.name, f.reason) }
    checked := b.checked
    for _, c in b.consts {
        if !c.placed { graph_fatal(graph_origin(c.g, 0), "the constant '%s' was built but never placed", graph_name(c.g, 0)) }
    }
    pc := b.pc
    pc.lock = nil
    graph_table_names(b, &pc)
    when ODIN_DEBUG {
        graph_index_ops(&pc, checked.annot)   // (else made when first asked: graph_ops)
        graph_check_coverage(b, &pc)
        for c in pc.codes {
            graph_check_runs(c)
            graph_check_refers(c)
            for s, id in c.syntax[:c.end + 1] {   // (each node found by its tree node)
                if s == 0 { continue }
                g, first := graph_ops(&pc, checked.annot, s)
                if g != c || first > Node_Id(id) || c.syntax[first] != s { graph_fatal(graph_origin(c, Node_Id(id)), "'%s' isn't found by its tree node", graph_name(c, Node_Id(id))) }
            }
        }
    }
    graph_dump(&pc)
    return pc
}


// --- storage --------------------------------------------------------------------
// Each code is built where it stays: a column of every code's — its nodes'
// kinds, their types, its operands, its runs — in a region of address space
// of its own (Graph_Region), reserved once and committed as it fills. Codes
// are built one at a time, so the code being built's column is always its
// region's newest allocation: it grows in place, and once the code is done
// it is trimmed to its length (graph_trim), the next code's beginning where
// it ends. Nothing is copied.

Graph_Column :: enum u8 {
    Kind, Op, Written, Parent, Name, Type, Decl_Tok, Syntax,
    Operand_First, Operands, Leaves, Consts, Reads, Run_Ops, Run_First, Edges, Unreachable, Settled,
    // A builder's tables (Graph_Tables): each a region of its own, so what's
    // in one never moves — a code another builder built is read, on another
    // thread, while its builder adds to them.
    Names, Types, Values,
}

Graph_Region :: struct {
    base:       [^]byte,
    reserved:   uint,
    committed:  uint,
    last, used: uint,   // its newest allocation: [last, used)
    want:       uint,   // what to reserve, once it's first used (graph_region_size)
}

// What a column's region reserves: more than one builder can put in it —
// no code has more nodes, operands, runs or statements than its tokens
// three times over, none takes over 16 bytes, so 64 a token is room for
// the whole program's (a builder builds part of it). Reserving costs with
// the size (Windows): what builders don't need, they don't take.
graph_region_size :: proc() -> uint {
    return clamp(mem.align_forward_uint(uint(len(build_tokens)) * 64, GRAPH_REGION_COMMIT), uint(64) << 20, GRAPH_REGION_RESERVE)
}

@(private="file")
GRAPH_REGION_RESERVE :: uint(64) << 30   // (the most a column's region reserves)
@(private="file")
GRAPH_REGION_COMMIT :: uint(1) << 20     // (committed so much at a time)

@(private="file")
graph_region_allocator :: proc(r: ^Graph_Region) -> mem.Allocator {
    return {procedure = graph_region_proc, data = r}
}

// A region's allocations: the newest one grows and shrinks in place, and a
// new one begins where it ends. (Only the newest can change: one that isn't
// is an internal error.)
@(private="file")
graph_region_proc :: proc(data: rawptr, mode: mem.Allocator_Mode, size, alignment: int,
                          old_memory: rawptr, old_size: int, loc := #caller_location) -> (memory: []byte, err: mem.Allocator_Error) {
    r := (^Graph_Region)(data)
    // (Its newest allocation to end at `end`, committed — zero past `from`
    // when asked.)
    end_at :: proc(r: ^Graph_Region, end, from: uint, zero: bool) -> mem.Allocator_Error {
        if end > r.reserved { return .Out_Of_Memory }
        if end > r.committed {
            to := min(mem.align_forward_uint(end, GRAPH_REGION_COMMIT), r.reserved)
            virtual.commit(r.base[r.committed:], to - r.committed) or_return
            r.committed = to
        }
        if zero && end > from { mem.zero(r.base[from:], int(end - from)) }
        r.used = end
        return nil
    }
    switch mode {
    case .Alloc, .Alloc_Non_Zeroed:
        if r.base == nil {
            space := virtual.reserve(r.want if r.want != 0 else GRAPH_REGION_RESERVE) or_return
            r.base, r.reserved = raw_data(space), uint(len(space))
        }
        start := mem.align_forward_uint(r.used, uint(alignment))
        end_at(r, start + uint(size), start, mode == .Alloc) or_return
        r.last = start
        return r.base[start:][:size], nil
    case .Resize, .Resize_Non_Zeroed:
        if old_memory == nil {
            return graph_region_proc(data, .Alloc if mode == .Resize else .Alloc_Non_Zeroed, size, alignment, nil, 0, loc)
        }
        start := uint(uintptr(old_memory) - uintptr(r.base))
        if start != r.last || start + uint(old_size) != r.used { graph_fatal({}, "a code's column resized when it is no longer its region's newest") }
        end_at(r, start + uint(size), start + uint(old_size), mode == .Resize) or_return
        return r.base[start:][:size], nil
    case .Free:
        // (The newest given back; one before it stays where it is.)
        if old_memory != nil && uint(uintptr(old_memory) - uintptr(r.base)) == r.last { r.used = r.last }
        return nil, nil
    case .Query_Features:
        if set := (^mem.Allocator_Mode_Set)(old_memory); set != nil {
            set^ = {.Alloc, .Alloc_Non_Zeroed, .Resize, .Resize_Non_Zeroed, .Free, .Query_Features}
        }
        return nil, nil
    case .Free_All, .Query_Info:
        return nil, .Mode_Not_Implemented
    }
    return nil, nil
}

// A new code's graph: each column empty, in its region.
@(private="file")
graph_code_new :: proc(b: ^Graph_Builder) -> ^Program_Graph {
    g := new(Program_Graph, virtual.arena_allocator(b.store.arena))
    r := b.store.regions
    at :: proc(r: ^[Graph_Column]Graph_Region, c: Graph_Column) -> mem.Allocator { return graph_region_allocator(&r[c]) }
    g.kind = make([dynamic]Node_Kind, at(r, .Kind))
    g.op = make([dynamic]Op_Kind, at(r, .Op))
    g.written = make([dynamic]Written, at(r, .Written))
    g.parent = make([dynamic]Node_Id, at(r, .Parent))
    g.name = make([dynamic]Name_Id, at(r, .Name))
    g.tables = b.tables
    g.names = &b.tables.names
    g.types = &b.tables.types.types
    g.type_ = make([dynamic]Type_Id, at(r, .Type))
    g.decl_tok = make([dynamic]Token_Id, at(r, .Decl_Tok))
    g.syntax = make([dynamic]Syntax_Id, at(r, .Syntax))
    g.annotated = &b.checked.annot.callees
    g.values = &b.tables.values
    g.operand_first = make([dynamic]i32, at(r, .Operand_First))
    g.operands = make([dynamic]Operand, at(r, .Operands))
    g.leaves = make([dynamic]Graph_Leaf, at(r, .Leaves))
    g.consts = make([dynamic]Graph_Const, at(r, .Consts))
    g.reads = make([dynamic]Operand, at(r, .Reads))
    g.run_ops = make([dynamic]Node_Id, at(r, .Run_Ops))
    g.run_first = make([dynamic]i32, at(r, .Run_First))
    g.edges = make([dynamic]Edge, at(r, .Edges))
    g.unreachable = make([dynamic]Span, at(r, .Unreachable))
    g.settled = make([dynamic]Node_Id, at(r, .Settled))
    return g
}

// A code's columns trimmed: each node column to `n`, operand_first to `n`
// and its end (none, for none), the rest to their lengths — what each was
// built past given back to its region.
@(private="file")
graph_trim :: proc(g: ^Program_Graph, n: int) {
    trim :: proc(col: ^[dynamic]$T, n: int) {
        resize(col, n)
        if cap(col) > n { shrink(col) }
    }
    trim(&g.kind, n); trim(&g.op, n); trim(&g.written, n); trim(&g.parent, n)
    trim(&g.name, n); trim(&g.type_, n)
    trim(&g.decl_tok, n); trim(&g.syntax, n)
    trim(&g.operand_first, n + 1 if n > 0 else 0)
    trim(&g.operands, len(g.operands) if n > 0 else 0)
    trim(&g.leaves, len(g.leaves) if n > 0 else 0)
    trim(&g.consts, len(g.consts) if n > 0 else 0)
    trim(&g.reads, len(g.reads) if n > 0 else 0)
    trim(&g.run_ops, len(g.run_ops) if n > 0 else 0)
    trim(&g.run_first, len(g.run_first) if n > 0 else 0)
    trim(&g.edges, len(g.edges) if n > 0 else 0)
    trim(&g.unreachable, len(g.unreachable) if n > 0 else 0)
    trim(&g.settled, len(g.settled) if n > 0 else 0)
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
    tables:      map[Syntax_Id]^Fold,              // each table's value, by its constant (graph_fold_code)
    table_names: map[Syntax_Id]string,             // ... its symbol's name
    fold_errors: [dynamic]Fold_Error,              // the uses of constants with no value
    consumes:    map[^Type_Scope]int,              // a fun that consumes a param into its result → which
    unreachable: [dynamic]Span,                    // statements right after a return, break or continue
    stores:      [dynamic]Graph_Store,             // where the codes are, each builder's (they last as long as the program)
    summaries:   map[^Type_Scope]^Fun_Summary,     // what each fun reaches through its params, worked out once its code is built (reach_scc)
    lock:        ^sync.Mutex,                      // while codes are built on several threads: funs, consts and tables are read and written under it
}

// A fun's or struct's code, built (nil: none, or not yet).
graph_fun_code :: proc(pc: ^Program_Code, ts: ^Type_Scope) -> ^Program_Graph {
    if pc.lock != nil { sync.mutex_lock(pc.lock) }
    g := pc.funs[ts] or_else nil
    if pc.lock != nil { sync.mutex_unlock(pc.lock) }
    return g
}

// What a fun reaches, worked out (nil: not yet — reach_summary works it out).
graph_fun_summary :: proc(pc: ^Program_Code, ts: ^Type_Scope) -> ^Fun_Summary {
    if pc.lock != nil { sync.mutex_lock(pc.lock) }
    s := pc.summaries[ts] or_else nil
    if pc.lock != nil { sync.mutex_unlock(pc.lock) }
    return s
}

// A constant's code, by its value's node, built (nil: none, or not yet).
graph_const_code :: proc(pc: ^Program_Code, value: Syntax_Id) -> ^Program_Graph {
    if pc.lock != nil { sync.mutex_lock(pc.lock) }
    g := pc.consts[value] or_else nil
    if pc.lock != nil { sync.mutex_unlock(pc.lock) }
    return g
}

// A program's code let go of: its columns' regions, then its arena. (A
// build's goes with its process; `mara serve` checks again, and again.)
program_code_free :: proc(pc: ^Program_Code) {
    for s in pc.stores {
        if s.regions != nil {
            for &r in s.regions {
                if r.base != nil { virtual.release(r.base, r.reserved) }
            }
        }
        virtual.arena_destroy(s.arena)
    }
    delete(pc.stores)
    pc^ = {}
}
// --- one code at a time ---------------------------------------------------------

// A code begins: the builder's graph emptied for it. (Lowering builds one
// code at a time: one begun inside another is an error.)
@(private="file")
graph_code_open :: proc(b: ^Graph_Builder) {
    if f := b.body; f != nil { graph_fatal(graph_origin(b.g, f.root), "a code begun while '%s' is being built", graph_name(b.g, f.root)) }
    b.g = graph_code_new(b)
    b.nodes = 0
    b.leaves = 0
    b.consts = 0
    b.reads = 0
    b.outside_named = false
}

// The code built: the compiler's globals it names past its own nodes, its
// columns trimmed where they are. Nil when it failed (graph_body_fail): it
// is left out.
@(private="file")
graph_code_close :: proc(b: ^Graph_Builder, f: ^Graph_Body) -> ^Program_Graph {
    defer {   // (its runs kept for the next code's, emptied)
        for r in b.runs {
            clear(&r.ops)
            clear(&r.waiting)
            append(&b.run_pool, r)
        }
        clear(&b.runs)
    }
    g := b.g
    if f.failed != "" {
        graph_trim(g, 0)
        return nil
    }
    g.end = g.last[0] or_else 0   // (the root's subtree: graph_last)
    delete_key(&g.last, 0)
    if b.outside_named { graph_place_outside(b) }
    resize(&g.leaves, b.leaves)
    resize(&g.consts, b.consts)
    resize(&g.reads, b.reads)
    if b.nodes >= len(g.kind) { graph_resize(g, b.nodes + 1) }
    g.operand_first[b.nodes] = i32(len(g.operands))
    append(&g.run_first, i32(len(g.run_ops)))
    for e in g.edges {
        if e.to == NO_NODE { graph_fatal(graph_origin(g, e.from), "a then from '%s' into a run that never had an operation", graph_name(g, e.from)) }
    }
    when ODIN_DEBUG { graph_check_built(b) }
    graph_trim(g, b.nodes)
    graph_find_consumes(g)
    graph_index_edges(g)
    graph_index_runs(g)
    {
        runs := make([dynamic]i32, 0, len(g.run_first))
        g.code_own = graph_code_runs(g, 0, &runs)
        g.code_runs = runs[:]
    }
    return g
}

// The compiler's globals the code names — this_program, context: a node
// each, in the order it first does, past its own (the root's subtree
// closed), each name's placeholder (OUTSIDE) made the node.
@(private="file")
graph_place_outside :: proc(b: ^Graph_Builder) {
    g := b.g
    made := [2]Node_Id{NO_NODE, NO_NODE}
    for &l in g.leaves[:b.leaves] {
        k: int
        switch l.decl {
        case OUTSIDE[0]: k = 0
        case OUTSIDE[1]: k = 1
        case:            continue
        }
        if made[k] == NO_NODE {
            made[k] = graph_node(b, .Field, .Synthetic, NO_NODE, graph_outside_name(k), b.globals[k], {})
        }
        l.decl = made[k]
    }
}

// (What the code is as built: each node's type settled — but an untyped
// constant's own — each run's operations in the order they were made.)
@(private="file")
graph_check_built :: proc(b: ^Graph_Builder) {
    g := b.g
    for i in 0 ..< b.nodes {
        if !graph_is_settled(graph_type(g, Node_Id(i))) && g.kind[i] != .Const {
            graph_fatal(graph_origin(g, Node_Id(i)), "'%s' typed %s, unsettled", graph_name(g, Node_Id(i)), type_name(graph_type(g, Node_Id(i))))
        }
    }
    for r in 0 ..< len(g.run_first) - 1 {
        last := Node_Id(-1)   // (its operations, but its reads: no node)
        for op in g.run_ops[g.run_first[r]:g.run_first[r + 1]] {
            if graph_is_read(op) { continue }
            if op < last { graph_fatal({}, "a run whose operations are out of order") }
            last = op
        }
    }
}

// A fun's or struct's code, built: named — an instance by its mangled name —
// then put in place (lw_place_decl walks the program in written order; its
// body's definitions' codes go after it).
graph_place_scope :: proc(p: ^Graph_Program, c: ^Built_Code, ts: ^Type_Scope, name: string, written: Written) {
    c.g.name[0] = graph_intern_in(c.g.tables, graph_scope_name(ts, name, written))
    graph_place(p, c)
}

// A code put in place: next in Program_Code.codes, the program's written
// order. (Found by its fun or struct, or its constant's value, from when it
// was built: graph_code_found.)
graph_place :: proc(b: ^Graph_Program, c: ^Built_Code) {
    g := c.g
    if c.placed { graph_fatal(graph_origin(g, 0), "'%s' is put in place twice", graph_name(g, 0)) }
    c.placed = true
    pc := &b.pc
    append(&pc.codes, g)
    append(&pc.unreachable, ..g.unreachable[:])
}

// A code built: found from here by its fun or struct (and which param its
// result consumes), or by its constant's value — what reads across codes
// (folding, the analyses' summaries) needs no more than that it was built.
@(private="file")
graph_code_found :: proc(b: ^Graph_Builder, g: ^Program_Graph, value: Syntax_Id) {
    sync.mutex_lock(&b.prog.lock)
    defer sync.mutex_unlock(&b.prog.lock)
    pc := &b.prog.pc
    if g.kind[0] == .Const {
        pc.consts[value] = g
        return
    }
    ts := graph_type(g, 0).(^Type_Scope)
    pc.funs[ts] = g
    if k, consumes := g.consumes[0]; consumes { pc.consumes[ts] = k }
}

// A type with its widths settled: a `:=` binding's, the one it adopted;
// one no use decided (the checker settles the rest: tc_settle), the
// default, i64 or f64.
graph_settled :: proc(t: Type) -> Type {
    #partial switch v in t {
    case Type_Infer_Int:
        r := resolve_infer(t)
        return Type_Numeric{.Signed, 64} if is_infer(r) else r
    case Type_Infer_Float:
        r := resolve_infer(t)
        return Type_F64{} if is_infer(r) else r
    case ^Type_Ptr:
        if is_infer(v.elem) { return new_clone(Type_Ptr{elem = graph_settled(v.elem)}) }
    }
    return t
}

// Whether a type is as graph_settled leaves it.
graph_is_settled :: proc(t: Type) -> bool {
    #partial switch v in t {
    case Type_Infer_Int, Type_Infer_Float: return false
    case ^Type_Ptr:                        return !is_infer(v.elem)
    }
    return true
}

// A new node. The columns grow in chunks and are written by index: ten
// appends per node cost twice as much, and most nodes are operations.
@(private="file")
graph_node :: proc(b: ^Graph_Builder, kind: Node_Kind, written: Written, parent: Node_Id,
                   name: string, t: Type, origin: Span) -> Node_Id {
    g := b.g
    i := b.nodes
    if i >= len(g.kind) { graph_resize(g, max(2 * len(g.kind), 64)) }
    id := Node_Id(i)
    g.kind[i] = kind
    g.op[i] = .Var
    g.written[i] = written
    g.parent[i] = parent
    g.name[i] = graph_intern(b, name)
    g.type_[i] = 0 if t == nil else type_id(b.type_table, graph_settled(t))
    g.decl_tok[i] = 0
    s := b.pin if b.pin != 0 else b.at
    g.syntax[i] = s
    if s != b.span_of { b.span_of, b.span_is = s, graph_tree_span(s) }
    if origin != b.span_is { g.origins[id] = origin }   // (where its tree node isn't: graph_set_origin)
    if b.sub != 0 { g.sub[id] = b.sub }
    g.operand_first[i] = i32(len(g.operands))
    b.nodes += 1
    return id
}

// A new leaf. Its column grows in chunks and is written by index, as the
// nodes' do (graph_node).
@(private="file")
graph_leaf_new :: proc(b: ^Graph_Builder, l: Graph_Leaf) -> Node_Id {
    g := b.g
    k := b.leaves
    if k >= len(g.leaves) { non_zero_resize(&g.leaves, max(2 * len(g.leaves), 64)) }
    g.leaves[k] = l
    b.leaves = k + 1
    return LEAF + Node_Id(k)
}

// A new constant, as a leaf is made (graph_leaf_new).
@(private="file")
graph_const_new :: proc(b: ^Graph_Builder, c: Graph_Const) -> Node_Id {
    g := b.g
    k := b.consts
    if k >= len(g.consts) { non_zero_resize(&g.consts, max(2 * len(g.consts), 64)) }
    g.consts[k] = c
    b.consts = k + 1
    return CONST + Node_Id(k)
}

// Every per-node column to `n` entries (each written as its node is made:
// none zeroed).
@(private="file")
graph_resize :: proc(g: ^Program_Graph, n: int) {
    non_zero_resize(&g.kind, n)
    non_zero_resize(&g.op, n)
    non_zero_resize(&g.written, n)
    non_zero_resize(&g.parent, n)
    non_zero_resize(&g.name, n)
    non_zero_resize(&g.type_, n)
    non_zero_resize(&g.decl_tok, n)
    non_zero_resize(&g.syntax, n)
    non_zero_resize(&g.operand_first, n)
}

// End a scope: its subtree is everything added since it.
@(private="file")
graph_close :: proc(b: ^Graph_Builder, id: Node_Id) {
    if end := Node_Id(b.nodes - 1); end != id { b.g.last[id] = end } else { delete_key(&b.g.last, id) }
}

graph_fatal :: proc(span: Span, format: string, args: ..any) -> ! {
    loc := span_location(span) if span_file(span) != "" else ""
    emit_diagnostic(.Graph_Error, loc, format, ..args)
    flush_diagnostics()
    os.exit(1)
}

// --- statements ---------------------------------------------------------------

// What the builder keys a statement or an expression by: its node in the
// tree, salted in a generic's instance (tc_sid). 0 is none.
Syntax_Id :: distinct u64

// --- the tree's ids ---------------------------------------------------------------
// Every node of the lowered program is a tree node's, in its instance
// (Program_Graph.syntax): the node lowered to make it — or, for a default a
// call leaves off, the call (Graph_Builder.pin). A tree node's nodes are all
// in one code, so a node's id in the tree's terms is its tree node and its
// rank among that node's: the lowered program and the annotations share ids,
// and each tree node's first node is a column beside its annotations
// (Annotations.ops). Its statement is the tree's too (graph_stmt).

// Where a node is written (what a diagnostic about it points at): its tree
// node's span — a definition's own nodes (the fun or struct, its params,
// what ends it), the definition's — or, where lowering says otherwise, its
// own (Program_Graph.origins: a compound assignment's operator, a widening
// at its use, a default's text where a call leaves it off).
graph_origin :: proc(g: ^Program_Graph, id: Node_Id) -> Span {
    if len(g.origins) > 0 {
        if sp, own := g.origins[id]; own { return sp }
    }
    return graph_tree_span(graph_syntax(g, id))
}

// A node's span, as its tree node says (graph_origin).
graph_tree_span :: proc(s: Syntax_Id) -> Span {
    t := &build_tree
    _, n := annot_split(s)
    #partial switch t.tag[n] {
    case .Fun_Def, .Struct_Def: return tree_span(t, tree_stmt(t, n))   // (the definition's)
    }
    return tree_span(t, n)
}

// Where a node is written, kept only where its tree node doesn't say so.
graph_set_origin :: proc(g: ^Program_Graph, id: Node_Id, sp: Span) {
    if sp == graph_tree_span(g.syntax[id]) {
        if len(g.origins) > 0 { delete_key(&g.origins, id) }
        return
    }
    g.origins[id] = sp
}

// Where a tree node was lowered to: its code (Program_Code.codes[code - 1];
// 0: nothing was) and the first of its nodes there.
Op_At :: struct {
    code:  i32,
    first: Node_Id,
}

// Each tree node's first node, beside the annotations — checking that every
// node has its tree node, in its code's instance, and one code each.
graph_index_ops :: proc(pc: ^Program_Code, a: ^Annotations) {
    a.ops = make([dynamic][]Op_At, len(a.instances))
    for inst, i in a.instances { a.ops[i] = make([]Op_At, int(inst.hi - inst.lo) + 1) }
    for g, ci in pc.codes {
        code := i32(ci) + 1
        root, _ := annot_split(g.syntax[0])
        #reverse for s, id in g.syntax[:g.end + 1] {   // (the lowest id last: a node's first)
            if s == 0 { graph_fatal(graph_origin(g, Node_Id(id)), "'%s' in '%s' was lowered from no tree node", graph_name(g, Node_Id(id)), graph_name(g, 0)) }
            i, n := annot_split(s)
            if i != root { graph_fatal(graph_origin(g, Node_Id(id)), "'%s' in '%s' was lowered from another instance's tree node", graph_name(g, Node_Id(id)), graph_name(g, 0)) }
            at := &a.ops[i][n - a.instances[i].lo]
            if at.code != 0 && at.code != code {
                graph_fatal(graph_origin(g, Node_Id(id)), "a tree node lowered into '%s' and '%s'", graph_name(pc.codes[at.code - 1], 0), graph_name(g, 0))
            }
            at^ = {code, Node_Id(id)}
        }
    }
}

// A tree node's first node in the lowered program, and its code (nil,
// NO_NODE: none); graph_ops_next gives the rest, in order.
graph_ops :: proc(pc: ^Program_Code, a: ^Annotations, s: Syntax_Id) -> (^Program_Graph, Node_Id) {
    if a.ops == nil { graph_index_ops(pc, a) }   // (what asks it — mara ask, mara lsp — once)
    i, n := annot_split(s)
    if int(i) >= len(a.ops) || n < a.instances[i].lo || n > a.instances[i].hi { return nil, NO_NODE }
    at := a.ops[i][n - a.instances[i].lo]
    if at.code == 0 { return nil, NO_NODE }
    return pc.codes[at.code - 1], at.first
}

// The next node of the same tree node's (NO_NODE: it was the last).
graph_ops_next :: proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    for next := id + 1; next <= g.end; next += 1 {
        if g.syntax[next] == g.syntax[id] { return next }
    }
    return NO_NODE
}

// What a statement outside any body declares — a module's, a body's
// definition — as the checker reads it, for the builder
// to put the code it defines where it goes (graph_place_decl).
Graph_Decl :: struct {
    id:      Syntax_Id,
    span:    Span,
    form:    Graph_Decl_Form,
    settles: bool,               // a variable's or a constant's: built as the checker settles it
    name:    string,             // what it names: a constant, a scope
    value:   Syntax_Id,          // a constant's value (0: none), which its uses find it by
    generic: bool,               // .Scope: a generic's, built for each instance
    node:    Syntax_Id,          // .Scope: its definition's node (a Fun_Def, a Struct_Def; a variant's body): what its scope is found by (Annotations.decls)
}

Graph_Decl_Form :: enum u8 {
    None,       // a constant (its code is found by its id), a type, a call, a rule
    Scope,      // a fun or a struct
    Code,       // code outside a body: an error
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
    return graph_const(b, .Explicit, span, t, "void", nil)
}

// A bare declaration's value: its zero — a struct's, an array's, its
// partial arrays' headers stamped (the zero op's) — and nothing more. Its
// type's constructor doesn't run: `x : T` is unset until written (flow.odin's
// definite assignment); `x := T()` constructs.
@(private="file")
graph_construct_bare :: proc(b: ^Graph_Builder, dest: Operand, t: Type, span: Span) {
    graph_op(b, .Zero, .Synthetic, span, t, "", dest)
}

// --- control flow -----------------------------------------------------------

// A value at the type its use takes: a narrower number widens, implied —
// sign- or zero-extended by its own signedness, or f32 to f64 — wherever the
// checker lets a narrower value in (an operation's operands, a store, an
// argument, a return, an index). A literal already has its use's type.
@(private="file")
graph_widen :: proc(b: ^Graph_Builder, v: Operand, to: Type, span: Span) -> Operand {
    if v.op == NO_NODE || v.out != 0 || !graph_widens(graph_type(b.g, v.op), to) { return v }
    return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), v)
}

// Whether a value of type `from` widens to `to`: both numbers of one kind,
// `to` the wider.
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

// How a use of a `from` as a `to` views it: a partial array (or a pointer to
// one) as a slice's header — a cast; a fixed array as a slice — of its
// place; or it doesn't.
View_Kind :: enum u8 { None, Header, Slice }

view_kind :: proc(to, from: Type) -> View_Kind {
    if to == nil || from == nil { return .None }
    _, to_ptr := distinct_base(to).(^Type_Ptr)
    _, from_ptr := distinct_base(from).(^Type_Ptr)
    if to_ptr == from_ptr && graph_header_of(to) && graph_partial_of(from) { return .Header }
    _, to_slice := distinct_base(to).(^Type_Slice)
    _, from_array := distinct_base(from).(^Type_Fixed_Array)
    return .Slice if to_slice && from_array else .None
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
        #partial switch graph_kind_of(b.g, p) {
        case .Fun, .Struct:
            ts, _ := graph_type(b.g, p).(^Type_Scope)
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
    if slot := fl.coll_slot; slot != NO_NODE { return graph_var(b, slot, graph_type(b.g, slot), span) }
    return graph_base_of(b, fl.walk(fl.walk_data, span), fl.coll_t, span, fl.coll_self)
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
    graph_exit_scopes(b, l.scope, span, failing = false)
    graph_jump(b, l.done if is_break else l.cont, .Explicit, span)
}

// Enter a scope: an arena mark when a local of its own lives on the arena
// (`holds`, as lowering finds it). (A struct's declarations are its fields:
// in Self, not on the arena.) Nor main's body: its scope ends with the
// program, which made the arena in its setup.
@(private="file")
graph_scope_open :: proc(b: ^Graph_Builder, block: Node_Id, span: Span, holds: bool) {
    s := Code_Scope{block = block, holds = holds && b.arena && graph_kind_of(b.g, block) != .Struct}
    s.arena = s.holds && (b.main == nil || graph_type(b.g, block) != Type(b.main))
    if s.arena { graph_op(b, .Arena_Mark, .Synthetic, span) }
    append(&b.code.scopes, s)
}

// Leave a scope at its end: its defers and reset, if the end is reached.
@(private="file")
graph_scope_close :: proc(b: ^Graph_Builder, span: Span) {
    if graph_reachable(b) { graph_exit_scopes(b, len(b.code.scopes) - 1, span, failing = false) }
    graph_scope_pop(b)
}

// (A scope said to hold a local on the arena that held none: lowering's
// reading of its declarations is wrong — the mark it made is no one's.)
@(private="file")
graph_scope_pop :: proc(b: ^Graph_Builder) {
    s := pop(&b.code.scopes)
    if s.holds && s.held == 0 { graph_fatal(graph_origin(b.g, s.block), "a scope said to hold a local on the arena holds none") }
    delete(s.defers)
}

// What leaving scopes[from:] runs, innermost first: each scope's defers, the
// last registered first — a `defer?`'s only when the code returns a failure
// (`failing`) — then its arena reset.
@(private="file")
graph_exit_scopes :: proc(b: ^Graph_Builder, from: int, span: Span, failing: bool) {
    for i := len(b.code.scopes) - 1; i >= from; i -= 1 {
        s := &b.code.scopes[i]
        for j := len(s.defers) - 1; j >= 0; j -= 1 {
            if s.defers[j].on_failure && !failing { continue }
            op := graph_op(b, .Run_Defer, .Synthetic, span)
            b.g.defer_of[op] = s.defers[j].block
        }
        if s.arena { graph_op(b, .Arena_Reset, .Synthetic, span) }
    }
}

// Whether a scope open has a `defer?`: a return leaving it runs it or not by
// the err it returns.
@(private="file")
graph_defers_on_failure :: proc(b: ^Graph_Builder) -> bool {
    for s in b.code.scopes {
        for d in s.defers { if d.on_failure { return true } }
    }
    return false
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
        graph_exit_scopes(b, 0, span, failing = false)
        graph_op(b, .Return, .Synthetic, span, nil, "", ..vals[:])
        graph_run_close(b)
    }
    for len(b.code.scopes) > 0 {
        graph_scope_pop(b)
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
    r := pop(&b.run_pool) if len(b.run_pool) > 0 else new(Run)
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
            b.g.edges[w].written = graph_written(b.g, id)
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
    id := graph_op_made(b, kind, w, span, t, name, operands)
    if kind == .Call || kind == .Construct { graph_set_callee(b.g, id, nil) }   // (made as no call of something: through a fun's value)
    return id
}

@(private="file")
graph_op_made :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, t: Type, name: string, operands: []Operand) -> Node_Id {
    id := graph_node(b, .Op, w, b.code.block, name, t, span)
    b.g.op[id] = kind
    append(&b.g.operands, ..operands)
    graph_emit(b, id)
    return id
}

graph_op_value :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, t: Type = nil, name := "", operands: ..Operand) -> Operand {
    return Operand{graph_op(b, kind, w, span, t, name, ..operands), 0}
}

// A variable's place, a leaf: `decl`, its declaration (graph_local,
// graph_global) — named as it is.
graph_var :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span: Span) -> Operand {
    if decl == NO_NODE { graph_fatal(span, "a variable with no declaration") }
    g := b.g
    s := b.pin if b.pin != 0 else b.at
    id := graph_leaf_new(b, {decl = decl, type_ = 0 if t == nil else type_id(b.type_table, graph_settled(t)), syntax = s})
    if s != b.span_of { b.span_of, b.span_is = s, graph_tree_span(s) }
    if span != b.span_is { g.origins[id] = span }   // (where its tree node isn't: graph_set_origin)
    return Operand{id, 0}
}

// Where a value is stored, as a recipe: the place's operations are emitted
// where the store happens, after the value — which may have crossed runs on
// the way (an `if` expression, `and`, `?`). An assignment's target is worked
// out before its value, so its place arrives computed (.At).
Dest :: struct {
    kind:   Dest_Kind,
    at:     Operand,   // .At: the place, already computed
    decl:   Node_Id,   // .Var: its declaration, when known here
    name:   string,    // .Field: the field; .Variant: the variant
    syntax: Syntax_Id, // .Var: the name it's written as, its leaf's tree node (0: none — a temporary's)
    index:  int,       // .Index
    type_:  Type,
    parent: ^Dest,     // .Field, .Index, .Variant: the value they are part of
}

Dest_Kind :: enum u8 { Var, At, Field, Index, Variant }

graph_dest_var :: proc(decl: Node_Id, t: Type, syntax := Syntax_Id(0)) -> Dest {
    return Dest{kind = .Var, decl = decl, type_ = t, syntax = syntax}
}

// Emit a destination's place in the current run.
graph_dest_place :: proc(b: ^Graph_Builder, d: Dest, span: Span) -> Operand {
    switch d.kind {
    case .Var:
        at := b.at
        if d.syntax == 0 { return graph_var(b, d.decl, d.type_, span) }
        b.at = d.syntax   // (the name's, written where it is: what's built into it is the value's)
        defer b.at = at
        _, name := annot_split(d.syntax)
        return graph_var(b, d.decl, d.type_, tree_span(&build_tree, name))
    case .At:    return d.at
    case .Field: return graph_op_value(b, .Field, .Explicit, span, d.type_, d.name, graph_dest_place(b, d.parent^, span))
    case .Index: return graph_op_value(b, .Index, .Explicit, span, d.type_, "", graph_dest_place(b, d.parent^, span), graph_const_index(b, d.index, span))
    case .Variant: return graph_op_value(b, .Variant, .Implied, span, d.type_, d.name, graph_dest_place(b, d.parent^, span))
    }
    return NO_VALUE
}

graph_read :: proc(b: ^Graph_Builder, place: Operand, t: Type, span: Span) -> Operand {
    // (A leaf's read as the leaf is — its type, its tree node, where it's
    // written: a read, no node.)
    g := b.g
    if graph_is_leaf(place.op) && t != nil {
        l := g.leaves[place.op - LEAF]
        s := b.pin if b.pin != 0 else b.at
        if l.type_ != 0 && l.syntax == s && l.type_ == type_id(b.type_table, graph_settled(t)) && (len(g.origins) == 0 || place.op not_in g.origins) {
            if s != b.span_of { b.span_of, b.span_is = s, graph_tree_span(s) }
            if span == b.span_is {
                k := b.reads
                if k >= len(g.reads) { non_zero_resize(&g.reads, max(2 * len(g.reads), 64)) }
                g.reads[k] = place
                b.reads = k + 1
                graph_emit(b, READ + Node_Id(k))
                return Operand{READ + Node_Id(k), 0}
            }
        }
    }
    return graph_op_value(b, .Read, graph_written(g, place.op), span, t, "", place)
}

// A synthetic local of the current block, for a value that outlives a run.
graph_slot :: proc(b: ^Graph_Builder, name: string, t: Type, span: Span) -> Node_Id {
    return graph_node(b, .Local, .Synthetic, b.code.block, name, t, span)
}

// A node's type, given after it is made: settled as it is when it is made
// (graph_node).
graph_retype :: proc(b: ^Graph_Builder, id: Node_Id, t: Type) {
    b.g.type_[id] = type_id(b.type_table, graph_settled(t))
}

// A plain place walked once more (another run): the operations that name it
// — a variable, a constant table, a field, an element at a constant or at a
// variable's value, what a pointer points at, bytes seen as a type — copied.
// (Its base's dereference, at the walk's span: graph_base_of.)
graph_place_again :: proc(b: ^Graph_Builder, p: Operand, span: Span) -> Operand {
    if p.op == NO_NODE { return p }
    g := b.g
    id := p.op
    if id >= READ {   // (a read of its own, of its leaf again)
        r := g.reads[id - READ]
        return graph_read(b, graph_place_again(b, r, span), graph_type(g, r.op), graph_origin(g, r.op))
    }
    if id >= LEAF {   // (a use of its own)
        n := graph_leaf_new(b, g.leaves[id - LEAF])
        if sp, own := g.origins[id]; own { g.origins[n] = sp }
        return Operand{n, p.out}
    }
    if id >= CONST {
        n := graph_const_new(b, g.consts[id - CONST])
        if sp, own := g.origins[id]; own { g.origins[n] = sp }
        if slice.contains(g.settled[:], id) { append(&g.settled, n) }   // (graph_const_settles)
        if c, named := g.constant[id]; named { g.constant[n] = c }
        return Operand{n, p.out}
    }
    #partial switch g.op[id] {
    case .Var, .Global, .Const, .Field, .Swizzle, .Index, .Deref, .View, .Read, .Cast:
    case:
        graph_fatal(graph_origin(g, id), "a place walked again holds a %v", g.op[id])
    }
    src := graph_built_operands(b, id)
    ops := make([]Operand, len(src), context.temp_allocator)
    for o, k in src { ops[k] = graph_place_again(b, o, span) }
    n := graph_op_value(b, g.op[id], g.written[id], graph_origin(g, id), graph_type(g, id), graph_name(g, id), ..ops)
    if r, binds := g.binds[id]; binds { g.binds[n.op] = r }
    if v, has := g.texts[id]; has { g.texts[n.op] = v }
    g.syntax[n.op] = g.syntax[id]   // (walked again: the same node's)
    graph_set_origin(g, n.op, graph_origin(g, id))
    if g.op[id] == .Const && slice.contains(g.settled[:], id) { append(&g.settled, n.op) }   // (graph_const_settles)
    if c, named := g.constant[id]; named { g.constant[n.op] = c }
    return Operand{n.op, p.out}
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
        if t := graph_type(b.g, d.at.op); t != nil { return t }
    }
    return d.type_
}

// The call's results, each written to its field.
graph_spread_results :: proc(b: ^Graph_Builder, span: Span, sd: ^Scope_Body, parent: ^Dest, callee: ^Type_Scope, c: Operand) {
    for rt, i in callee.return_types {
        if i >= len(sd.fields) { break }
        f := sd.fields[i]
        val := Operand{c.op, i32(i)}
        if view_kind(f.type_, rt) == .Slice {
            slot := graph_slot(b, "temp", rt, span)
            graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, slot, rt, span), val)
            val = graph_op_value(b, .Slice, .Implied, span, f.type_, "", graph_var(b, slot, rt, span))
        }
        field := graph_dest_place(b, Dest{kind = .Field, name = f.name, type_ = f.type_, parent = parent}, span)
        graph_op(b, .Write, .Explicit, span, nil, "", field, val)
    }
}

// A union's variant `name` as a struct: its tag first, then its fields; nil
// when t is no union with that variant.
graph_variant_struct :: proc(t: Type, name: string) -> ^Type_Scope {
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
    graph_exit_scopes(b, 0, span, failing = true)
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
    if v.op != NO_NODE && graph_op_of(b.g, v.op) == .Call { return v.op }
    if v.op != NO_NODE && graph_op_of(b.g, v.op) == .Read && b.code.constructed != NO_NODE { return b.code.constructed }
    graph_fatal(span, "a call's outputs, built as no call")
}

// How many outputs a call has: its callee's return list (a fallible
// constructor's includes the struct itself); through a function value, its
// signature's.
@(private="file")
graph_outputs :: proc(b: ^Graph_Builder, op: Node_Id) -> int {
    callee := graph_called(b.g, op)
    if callee == nil && b.g.op[op] == .Call {
        ops := graph_built_operands(b, op)
        if len(ops) > 0 && ops[0].op != NO_NODE {
            if ft, is_fn := distinct_base(graph_type(b.g, ops[0].op)).(^Type_Scope); is_fn && ft.kind == .Fun { callee = ft }
        }
    }
    if callee == nil { return 0 }
    if list, is_ctor := constructor_effective_returns(callee); is_ctor { return len(list) }
    return len(callee.return_types)
}

// A call or construct operation, with a Calls edge to what it runs.
graph_call_op :: proc(b: ^Graph_Builder, kind: Op_Kind, w: Written, span: Span, callee: ^Type_Scope, t: Type, operands: ..Operand) -> Node_Id {
    op := graph_op_made(b, kind, w, span, t, graph_call_name(callee), operands)
    graph_set_callee(b.g, op, callee)
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

// A constant whose width is its use's (a number, an untyped constant's
// name, size_of), `t` as the checker settled it: listed once a use or a
// binding did (g.settled: for the range check) — one none did takes the
// default, unchecked.
@(private="file")
graph_const_settles :: proc(b: ^Graph_Builder, id: Node_Id, t: Type) {
    if b.body == nil { graph_fatal(graph_origin(b.g, id), "a constant of open width outside any body") }
    if is_infer(t) && infer_cell_of(t) == nil { return }
    append(&b.g.settled, id)
}

// A constant, a leaf (Graph_Const), with its value when it has one.
graph_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, value: Maybe(Const_Value), untyped := false) -> Operand {
    g := b.g
    s := b.pin if b.pin != 0 else b.at
    id := graph_const_new(b, {type_ = 0 if t == nil else type_id(b.type_table, graph_settled(t)), name = graph_intern(b, name), written = w, syntax = s})
    if s != b.span_of { b.span_of, b.span_is = s, graph_tree_span(s) }
    if span != b.span_is { g.origins[id] = span }   // (where its tree node isn't: graph_set_origin)
    if v, ok := value.?; ok {
        graph_set_value(g, id, v)
        if untyped { graph_const_settles(b, id, t) }
    }
    return Operand{id, 0}
}

// The value a name resolved to stands for, when the resolution holds it: an
// enum variant's, an array's length. (A named constant's is its code's:
// graph_fold_code.)
//
// What a name that stands for a constant is, as the builder builds it: a
// declared constant's value (its id — the code its uses are folded from), or
// a value already known (an enum's variant, a length).
Graph_Named :: struct {
    value: Syntax_Id,
    known: Maybe(Const_Value),
}

// A named register-value constant where it's used: its declaration's
// value, computed at the use's width once every code is built
// (graph_fold_code). An enum's variant, a length: its value.
graph_named_const :: proc(b: ^Graph_Builder, w: Written, span: Span, t: Type, name: string, n: Graph_Named, untyped := false) -> Operand {
    if n.value == 0 { return graph_const(b, w, span, t, name, n.known, untyped) }
    o := graph_const(b, w, span, t, name, nil)
    b.g.constant[o.op] = n.value
    if untyped { graph_const_settles(b, o.op, t) }
    return o
}

// A string constant's global carries its text in the constants table.
graph_text :: proc(b: ^Graph_Builder, global: Operand, value: Maybe(Const_Value)) -> Operand {
    if c, ok := value.?; ok && c.is_text { graph_set_value(b.g, global.op, c) }
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

// Each table's name: its constant's symbol (the checker's: a module's flat
// name, a body's owner-named).
@(private="file")
graph_table_names :: proc(b: ^Graph_Program, pc: ^Program_Code) {
    for key, v in b.constant_names {
        if v in pc.tables { pc.table_names[v] = key }
    }
}

// A place as the source writes it: `o.inner.p`, `a[i]`. A temporary, or a
// place reached through an explicit dereference, has no name.
graph_place_name :: proc(g: ^Program_Graph, p: Operand) -> string {
    if p.op == NO_NODE { return "" }
    if graph_is_leaf(p.op) { return "" if graph_written(g, p.op) == .Synthetic else graph_name(g, p.op) }
    ops := graph_operands(g, p.op)
    #partial switch graph_op_of(g, p.op) {
    case .Field, .Swizzle:
        base := graph_place_name(g, ops[0])
        if base == "" { return graph_name(g, p.op) }
        return fmt.tprintf("%s.%s", base, graph_name(g, p.op))
    case .Deref:
        if graph_written(g, p.op) == .Implied { return graph_place_name(g, ops[0]) }
    case .View:
        return graph_place_name(g, ops[0])   // the bytes it views
    case .Index:
        base := graph_place_name(g, ops[0])
        if base == "" { return "" }
        i := ops[1].op
        if i != NO_NODE && graph_op_of(g, i) == .Cast && graph_written(g, i) == .Implied { i = graph_operands(g, i)[0].op }
        idx := ""
        if i != NO_NODE && graph_op_of(g, i) == .Read { idx = graph_place_name(g, graph_operands(g, i)[0]) }
        if idx == "" { return base }
        return fmt.tprintf("%s[%s]", base, idx)
    }
    return ""
}

// The fun or struct whose code an operation is in.
@(private="file")
graph_code_owner :: proc(g: ^Program_Graph, id: Node_Id) -> Node_Id {
    for p := g.parent[id]; p != NO_NODE; p = g.parent[p] {
        #partial switch graph_kind_of(g, p) {
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
    mention:  map[Node_Id]Node_Id   // a param → its one leaf (NO_NODE: several)
    defer { delete(returned); delete(mention) }
    for l, i in g.leaves {
        if p := l.decl; p >= 0 && graph_kind_of(g, p) == .Param { mention[p] = NO_NODE if p in mention else LEAF + Node_Id(i) }
    }
    for i in 0 ..< len(g.kind) {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        #partial switch g.op[id] {
        case .Return:
            if g.written[id] != .Explicit { continue }
            fun := graph_code_owner(g, id)
            local := NO_NODE
            if ops := graph_operands(g, id); len(ops) == 1 && ops[0].op != NO_NODE && graph_op_of(g, ops[0].op) == .Read {
                if d := graph_leaf_decl(g, graph_operands(g, ops[0].op)[0].op); d >= 0 && graph_kind_of(g, d) == .Local { local = d }
            }
            if fun in returned && returned[fun] != local { local = NO_NODE }
            returned[fun] = local
        }
    }
    for fun, local in returned {
        if local == NO_NODE { continue }
        ft, is_scope := graph_type(g, fun).(^Type_Scope)
        if !is_scope || ft.kind != .Fun || fn_result_count(ft) != 1 { continue }
        ret := distinct_base(fn_result(ft, 0))
        by_slot := as_struct_body(ret) != nil
        #partial switch _ in ret {
        case ^Type_Fixed_Array, ^Type_Partial_Array: by_slot = true
        }
        if !by_slot { continue }
        // (Its params come first among its contents.)
        fun_end := graph_last(g, fun)
        for p := fun + 1; p <= fun_end && graph_kind_of(g, p) == .Param; p += 1 {
            v, once := mention[p]
            if !once || v == NO_NODE { continue }
            read := graph_user(g, v, fun_end)
            if read == NO_NODE || graph_op_of(g, read) != .Read { continue }
            w := graph_user(g, read, fun_end)
            if w == NO_NODE || graph_op_of(g, w) != .Write || graph_stmt(g, w).kind != .Decl { continue }
            if ops := graph_operands(g, w); ops[1].op != read || graph_leaf_decl(g, ops[0].op) != local { continue }
            for cp, k in ft.params {
                if cp.name == graph_name(g, p) && types_equal(distinct_base(cp.type_), ret) { g.consumes[fun] = k }
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

// The first operation after op (a leaf, a read: any), up to `last`, that
// takes op's output — a leaf's, its read's, if it's read.
@(private="file")
graph_user :: proc(g: ^Program_Graph, op, last: Node_Id) -> Node_Id {
    if graph_is_leaf(op) {
        for r, j in g.reads { if r.op == op { return READ + Node_Id(j) } }
    }
    for id := op + 1 if op < LEAF else 0; id <= last; id += 1 {
        if g.kind[id] != .Op { continue }
        for o in graph_operands(g, id) { if o.op == op { return id } }
    }
    return NO_NODE
}

// Sort the edge table by `from` and index it (a counting sort: one pass).
@(private="file")
graph_index_edges :: proc(g: ^Program_Graph) {
    // (By insertion, which keeps a node's in order: a code has few, mostly
    // in order already.)
    e := g.edges[:]
    for i in 1 ..< len(e) {
        for j := i; j > 0 && e[j - 1].from > e[j].from; j -= 1 { e[j - 1], e[j] = e[j], e[j - 1] }
    }
}

// --- scopes -------------------------------------------------------------------


// A fun's or struct's node: its code's root. (Named where it is put in
// place: graph_place_scope.)
@(private="file")
graph_scope_root :: proc(b: ^Graph_Builder, ts: ^Type_Scope, span: Span, written: Written) -> Node_Id {
    kind: Node_Kind = .Fun if ts.kind == .Fun else .Struct
    return graph_node(b, kind, written, NO_NODE, "", ts, span)
}

// A scope's name: as written, or an instance's, from its mangled one.
graph_scope_name :: proc(ts: ^Type_Scope, name: string, written: Written) -> string {
    return name if written == .Explicit else ask_demangle(ts.name, ts.home_package)
}

// --- bodies -------------------------------------------------------------------

// A fun's or struct's body, lowered (lower.odin): its scope's node and
// contents, a code of its own, finished once it is built, and put
// in place once every code is (graph_place_codes).
//
// Where lowering can't build something, the body fails: it is left out, and
// the build stops, saying why (build_program_graph).
Graph_Body :: struct {
    ts:         ^Type_Scope,
    root:       Node_Id,
    contents:   Graph_Contents,
    defs:       [dynamic]Graph_Decl,   // its definitions (a fun, a struct, a constant): each one's code goes after it
    // Whether each local that could live on the arena does, by its type
    // when declared (graph_build_decl); the local every return returns.
    arena_types: map[Node_Id]bool,
    returned:   Token_Id,
    const_decl: Graph_Decl,              // a constant's: its statement
    failed:     string,
}


// Where a number is widened to the type its use takes (graph_build_widen):
// to `to` — settled, for a declaration's (as its node is); or to the param
// `param` of `sig`; or to a binary operation's working type.
Graph_Widen :: struct {
    to:        Type,
    settle_to: bool,
    sig:       ^Type_Scope,
    param:     int,
    work:      Graph_Work,
    binary:    bool,
}

// The type a widening takes its value to.
@(private="file")
graph_widen_to :: proc(w: Graph_Widen) -> Type {
    to := w.to
    if w.binary {
        to = graph_work(w.work)
    } else if w.sig != nil {
        to = w.sig.params[w.param].type_ if w.param < len(w.sig.params) else nil
    }
    if w.settle_to { to = graph_settled(to) }
    return to
}

// A fun's or struct's body begins: `id` its statement's, `span` its; an
// intrinsic's has no code of its own. Its root's statement is its
// definition's, made where it is put in place (graph_place_scope). As
// lowering finds them: the local every return returns (its token), and
// whether a local of the body's own lives on the arena.
graph_body_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, span: Span, intrinsic: bool, written: Written,
                         returned := Token_Id(0), holds := false) -> ^Graph_Body {
    graph_code_open(b)
    f := graph_body_new(b)
    f.ts = ts
    b.body = f
    f.root = graph_scope_root(b, ts, span, written)
    f.returned = returned
    f.contents = graph_contents_begin(b, ts, span, intrinsic, f.root, holds)
    return f
}

// What lowering couldn't build: the rest of the body is built for nothing,
// and it is left out. A clean check's graph is never built then: the first
// such body is reported instead.
graph_body_fail :: proc(b: ^Graph_Builder, f: ^Graph_Body, reason: string) {
    if f.failed != "" { return }
    f.failed = reason
    sync.mutex_lock(&b.prog.lock)
    defer sync.mutex_unlock(&b.prog.lock)
    if b.prog.failure.reason == "" {
        b.prog.failure = {f.ts.name if f.ts != nil && f.ts.name != "" else graph_name(b.g, f.root), reason, graph_origin(b.g, f.root)}
    }
}

// The body is built: finished, to be put in place —
// or, if it failed, left out.
graph_body_end :: proc(b: ^Graph_Builder, f: ^Graph_Body) -> ^Program_Graph {
    graph_contents_end(b, f.contents, finish = f.failed == "")
    b.body = nil
    // (Its end can find what it can't build: a scope's values on the arena.)
    c := graph_code_close(b, f)
    if c != nil {
        sync.mutex_lock(&b.prog.lock)
        b.prog.bodies[f.ts] = new_clone(Built_Code{g = c, b = b, defs = f.defs}, b.prog.allocator)
        sync.mutex_unlock(&b.prog.lock)
        f.defs = nil
        graph_code_found(b, c, 0)
    }
    graph_body_free(b, f)
    return c
}

@(private="file")
graph_body_new :: proc(b: ^Graph_Builder) -> ^Graph_Body {
    return pop(&b.body_pool) if len(b.body_pool) > 0 else new(Graph_Body)
}

// A body done: kept for the next, its maps emptied (its definitions went
// with its code, if it was built).
@(private="file")
graph_body_free :: proc(b: ^Graph_Builder, f: ^Graph_Body) {
    delete(f.defs)
    kept := Graph_Body{arena_types = f.arena_types}
    graph_map_reuse(&kept.arena_types)
    f^ = kept
    append(&b.body_pool, f)
}

@(private="file")
graph_body_drop :: proc(f: ^Graph_Body, made_in := context.allocator) {
    delete(f.arena_types)
    free(f, made_in)
}

// A map emptied for its next use — or, grown big, given back: emptying
// one goes over all it holds room for, and the next is most likely small.
@(private="file")
graph_map_reuse :: proc(m: ^$M/map[$K]$V) {
    if cap(m^) > 256 {
        delete(m^)
        m^ = nil
    } else {
        clear(m)
    }
}

// A value at the type a callee's param — or, `w.binary`, a binary
// operation's working type — takes (an overloaded operator's, a dispatch's
// or a generic's argument; an operation's side), `t` its own: an array's
// place seen as a slice, a partial array's header as one, or a number
// widened; else the value (a place, read).
graph_build_as :: proc(b: ^Graph_Builder, v: Operand, place: bool, t: Type, read_span, span: Span, w: Graph_Widen) -> Operand {
    read :: proc(b: ^Graph_Builder, v: Operand, place: bool, t: Type, span: Span) -> Operand {
        return graph_read(b, v, t, span) if place else v   // (at the expression, as a value is read)
    }
    // A cast only where one can be taken — a number's widening, a partial
    // array's header — and a slice only of a fixed array's place.
    _, _, num := numeric_info(graph_settled(t))
    if !num && !graph_partial_of(t) || is_infer(t) && infer_cell_of(t) == nil { return read(b, v, place, t, read_span) }
    to := graph_widen_to(w)
    if !w.binary {
        #partial switch view_kind(to, t) {
        case .Header: return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), read(b, v, place, t, read_span))
        case .Slice:  if place { return graph_op_value(b, .Slice, .Implied, span, to, "", v) }
        }
    }
    val := read(b, v, place, t, read_span)
    if val.op == NO_NODE || !graph_widens(graph_settled(graph_type(b.g, val.op)), to) { return val }
    return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), val)
}

// A number at the type its use takes, as graph_widen: `w` says which.
graph_build_widen :: proc(b: ^Graph_Builder, v: Operand, span: Span, w: Graph_Widen) -> Operand {
    if v.op == NO_NODE || v.out != 0 { return v }
    // What is no number never widens.
    from := graph_type(b.g, v.op)
    if _, _, num := numeric_info(from); !num { return v }
    to := graph_widen_to(w)
    if !graph_widens(from, to) { return v }
    return graph_op_value(b, .Cast, .Implied, span, to, type_name(to), v)
}

// A block of code: opened before its statements are
// checked, closed after.
Graph_Block :: struct {
    n, outer: Node_Id,
    span:     Span,
}

graph_build_block_open :: proc(b: ^Graph_Builder, label: string, span: Span, holds: bool) -> Graph_Block {
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, span, holds)
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

graph_build_if :: proc(b: ^Graph_Builder, cond: Operand, span: Span, has_else, holds: bool) -> Graph_If {
    fi := Graph_If{has_else = has_else, span = span}
    fi.then_r, fi.join = graph_run_new(b), graph_run_new(b)
    fi.else_r = graph_run_new(b) if fi.has_else else fi.join
    graph_branch(b, cond, fi.then_r, fi.else_r, .Explicit, span)
    b.code.run = fi.then_r
    fi.block = graph_build_block_open(b, "if", span, holds)
    return fi
}

graph_build_else :: proc(b: ^Graph_Builder, fi: ^Graph_If, span: Span, holds: bool) {
    graph_build_block_close(b, fi.block)
    if graph_reachable(b) { graph_jump(b, fi.join, .Synthetic, fi.span) }
    if fi.has_else {
        b.code.run = fi.else_r
        fi.block = graph_build_block_open(b, "else", span, holds)
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
// trailing err left out, the scopes left, the return. A `defer?` it leaves
// runs when it fails: as its err's value says when that's a constant (`Ok`,
// `Not_A_Digit`), else by a branch on the err — a run where it failed and one
// where it didn't, each leaving the scopes and returning.
graph_build_return :: proc(b: ^Graph_Builder, vals: []Operand, span: Span) {
    rts := graph_result_types(b)
    all := make([dynamic]Operand, 0, len(rts), context.temp_allocator)
    append(&all, ..vals)
    graph_implied_oks(b, &all, rts, span)
    leave :: proc(b: ^Graph_Builder, all: []Operand, span: Span, failing: bool) {
        graph_exit_scopes(b, 0, span, failing = failing)
        graph_op(b, .Return, .Explicit, span, nil, "", ..all)
        graph_run_close(b)
    }
    has_err := len(rts) > 0 && len(all) == len(rts) && is_err_type(rts[len(rts) - 1])
    if !has_err || !graph_defers_on_failure(b) {
        leave(b, all[:], span, failing = false)
        return
    }
    err := all[len(all) - 1]
    if graph_is_const(err.op) {
        if v, known := graph_value(b.g, err.op); known {
            leave(b, all[:], span, failing = v.int != 0)
            return
        }
    }
    fail, ok := graph_run_new(b), graph_run_new(b)
    failed := graph_op_value(b, .Cast, .Implied, span, Type_Bool{}, "bool", err)   // an error: nonzero
    graph_branch(b, failed, fail, ok, .Implied, span)
    b.code.run = fail
    leave(b, all[:], span, failing = true)
    b.code.run = ok
    leave(b, all[:], span, failing = false)
}

// `return f()`: each of the call's `count` outputs — its value, `v`, first —
// returned (graph_build_return).
graph_build_return_outputs :: proc(b: ^Graph_Builder, v: Operand, count: int, span: Span) {
    outs := make([dynamic]Operand, 0, count, context.temp_allocator)
    append(&outs, v)
    if count > 1 {
        op := graph_outputs_op(b, v, span)
        for i in 1 ..< count { append(&outs, Operand{op, i32(i)}) }
    }
    graph_build_return(b, outs[:], span)
}

// A struct's field declaration: its fields,
// typed as the struct's; each name's assignment (`lowered`, the checker's
// lowering of it; `inits`, the values as written) stores into its own and
// is this statement's.
// A struct's field declaration: each name a field, found by its token as a
// local is (graph_local). (`_` names nothing: no field — its output, its
// value, dropped.)
graph_build_fields :: proc(b: ^Graph_Builder, names: []string, toks: []Token_Id, span: Span) {
    for name, i in names {
        if name != "_" { graph_decl(b, {kind = .Field, owner = b.body.ts}, b.code.block, name, nil, span, toks[i]) }
    }
}

// A field of the program's struct (the compiler's: nothing constructs it).
graph_build_program_field :: proc(b: ^Graph_Builder, name: string, tok: Token_Id, span: Span) {
    graph_decl(b, {kind = .Field, owner = b.body.ts}, b.code.block, name, nil, span, tok)
}

// The program's struct (main's entry sets up its
// storage, nothing constructs it): each field mara.core declares for it,
// typed as the struct's, a statement of its own; no code.


// A local's declaration (graph_decl), before its value: typed once it is
// built (graph_build_typed) as `t`, the type lowering knows it takes. A big
// value lives on the arena: its space, taken before its value — but the
// local every return returns, which is built in its caller's slot. (A `let`
// binds memory it takes.)
graph_build_decl :: proc(b: ^Graph_Builder, name: string, tok: Token_Id, span: Span, t: Type, bound := false) -> Node_Id {
    d := graph_decl(b, {kind = .Local}, b.code.block, name, nil, span, tok)
    if !b.arena || bound { return d }
    routes := t != nil && routes_to_arena(t)
    b.body.arena_types[d] = routes   // (checked against the type it is given: graph_code_close)
    if !routes || b.body.returned != 0 && tok == b.body.returned { return d }
    graph_op(b, .Arena_Alloc, .Synthetic, span, t, "", graph_var(b, d, t, span))
    if n := len(b.code.scopes); n > 0 && b.code.scopes[n - 1].block == b.code.block {
        s := &b.code.scopes[n - 1]
        if !s.holds { graph_fatal(span, "'%s' lives on the arena in a scope said to hold no local there", name) }
        s.held += 1
    }
    return d
}

graph_build_typed :: proc(b: ^Graph_Builder, d: Node_Id, t: Type) {
    graph_retype(b, d, t)
    // (A local that could live on the arena: as lowering said when it
    // declared it, graph_build_decl.)
    if routes, decided := b.body.arena_types[d]; decided && routes != (t != nil && routes_to_arena(t)) {
        graph_fatal(graph_origin(b.g, d), "'%s' is typed otherwise than it was declared", graph_name(b.g, d))
    }
    // (Its uses made before that was known — where a value was built into
    // it — typed as it is: a leaf of no type is its declaration's.)
}

// `x : T = void` and `x = void`: the value left
// uninitialized — `void` where it is written, `at`.
graph_build_void_decl :: proc(b: ^Graph_Builder, decl: Node_Id, t: Type, span, at: Span) {
    val := graph_void(b, t, at)
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, decl, t, span), val)
}

graph_build_void_assign :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, t: Type, span, at: Span) {
    graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, decl, t, span), graph_void(b, t, at))
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
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.slot, Type_Bool{}, sa.span), l)
    sa.rhs, sa.join = graph_run_new(b), graph_run_new(b)
    if sa.and {
        graph_branch(b, l, sa.rhs, sa.join, sa.w, sa.span)
    } else {
        graph_branch(b, l, sa.join, sa.rhs, sa.w, sa.span)
    }
    b.code.run = sa.rhs
}

graph_build_and_end :: proc(b: ^Graph_Builder, sa: ^Graph_And, r: Operand) -> Operand {
    graph_op(b, .Write, .Synthetic, sa.span, nil, "", graph_var(b, sa.slot, Type_Bool{}, sa.span), r)
    graph_jump(b, sa.join, .Synthetic, sa.span)
    b.code.run = sa.join
    return graph_read(b, graph_var(b, sa.slot, Type_Bool{}, sa.span), Type_Bool{}, sa.span)
}

// A bare declaration's value: its zero (graph_construct_bare).
graph_build_bare :: proc(b: ^Graph_Builder, d: Node_Id, t: Type, span: Span) {
    graph_construct_bare(b, graph_var(b, d, t, span), t, span)
}

// A call through a function value: the arguments, then the
// value, read, then the call.
graph_build_indirect :: proc(b: ^Graph_Builder, name: string, decl: Node_Id, fn_value: Type, t: Type, args: []Operand, w: Written, span: Span) -> Operand {
    ops := make([dynamic]Operand, 0, len(args) + 1, context.temp_allocator)
    append(&ops, graph_read(b, graph_var(b, decl, fn_value, span), fn_value, span))
    append(&ops, ..args)
    return graph_op_value(b, .Call, w, span, t, name, ..ops[:])
}

// Bytes indexed, seen as another type once the use of them says which: the
// element's place, built, is that view — the same operands, the bytes at the
// index.
graph_build_view :: proc(b: ^Graph_Builder, place: Operand, t: Type, big: bool, span: Span) {
    id := place.op
    b.g.op[id] = .View
    graph_set_origin(b.g, id, span)
    graph_retype(b, id, t)
    b.g.name[id] = graph_intern(b, "#big_endian" if big else "")
    // (Its base's implied dereference and its offset's widening are the
    // view's, where it is.)
    for o, k in graph_built_operands(b, id) {
        if o.op == NO_NODE || graph_written(b.g, o.op) != .Implied { continue }
        if k == 0 && graph_op_of(b.g, o.op) == .Deref || k == 1 && graph_op_of(b.g, o.op) == .Cast { graph_set_origin(b.g, o.op, span) }
    }
}

// Take back the operation just built — its operands are what is wanted (an
// element of bytes, a span of them, read as another type): the code's
// newest node, and its run's last operation.
@(private="file")
graph_unbuild :: proc(b: ^Graph_Builder, id: Node_Id) {
    g := b.g
    r := b.code.run
    if int(id) != b.nodes - 1 || g.kind[id] != .Op || r == nil || len(r.ops) == 0 || r.ops[len(r.ops) - 1] != id {
        graph_fatal(graph_origin(g, id), "a %v taken apart after more was built", g.op[id])
    }
    if len(r.ops) == 1 {   // (the thens its run's first operation took wait for the next again)
        for &e, k in g.edges {
            if e.to == id {
                e.to = NO_NODE
                append(&r.waiting, i32(k))
            }
        }
    }
    pop(&r.ops)
    resize(&g.operands, int(g.operand_first[id]))
    delete_key(&g.texts, id)
    delete_key(&g.origins, id)   // (its id the next node's: graph_node)
    delete_key(&g.sub, id)
    b.nodes -= 1
}

// Bytes read by a byte read: of the element just built, its buffer's place
// (its dereference at the read) and its index as it was before it was
// widened; the element taken back.
graph_build_byte_operands :: proc(b: ^Graph_Builder, place: Operand, span: Span) -> (Operand, Operand) {
    id := place.op
    ops := graph_built_operands(b, id)
    buf, off := ops[0], ops[1]
    graph_unbuild(b, id)
    if off.op != NO_NODE && graph_op_of(b.g, off.op) == .Cast && graph_written(b.g, off.op) == .Implied {
        raw := b.g.operands[b.g.operand_first[off.op]]
        graph_unbuild(b, off.op)
        off = raw
    }
    if buf.op != NO_NODE && graph_op_of(b.g, buf.op) == .Deref && graph_written(b.g, buf.op) == .Implied { graph_set_origin(b.g, buf.op, span) }
    return buf, off
}

// A span of bytes read: of the slice just built, its bytes' place (its
// dereference at the read) and its bounds; the slice taken back.
graph_build_span_operands :: proc(b: ^Graph_Builder, slice: Operand, span: Span) -> (buf, lo, hi: Operand) {
    id := slice.op
    ops := graph_built_operands(b, id)
    buf, lo, hi = ops[0], ops[1], ops[2]
    graph_unbuild(b, id)
    if buf.op != NO_NODE && graph_op_of(b.g, buf.op) == .Deref && graph_written(b.g, buf.op) == .Implied { graph_set_origin(b.g, buf.op, span) }
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

// Bytes taken as an array: their view, copied into a
// temporary, read.
graph_build_view_temp :: proc(b: ^Graph_Builder, view: Operand, t: Type, span: Span) -> Operand {
    slot := graph_slot(b, "temp", t, span)
    graph_op(b, .Write, .Implied, span, nil, "", graph_var(b, slot, t, span), graph_read(b, view, t, span))
    return graph_read(b, graph_var(b, slot, t, span), t, span)
}

// A take: the count, then the storage — `&x`, x's place; else a place, of
// type t — then the carve. It carves from the storage's header: `&s` is
// s's, a `^[]byte` what it points at; or, positional (`&bytes[i]`), the view
// of the bytes there as what's taken.
graph_build_carve :: proc(b: ^Graph_Builder, span: Span, keyword: string, taken: Type, storage: Operand, t: Type, addressed, is_self: bool, count: Operand, w: Written) -> Operand {
    from := storage
    if addressed {
        if from.op != NO_NODE && graph_op_of(b.g, from.op) == .Index && is_byte_buffer(graph_type(b.g, graph_built_operands(b, from.op)[0].op)) {
            graph_build_view(b, from, taken, false, span)
        }
    } else {
        from = graph_base_of(b, storage, t, span, is_self)
    }
    return graph_op_value(b, .Carve, w, span, taken, keyword, from, count)
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

graph_build_destructure :: proc(b: ^Graph_Builder, span: Span, names: []string, toks: []Token_Id, stores: []bool, is_decl: bool, types: []Type) -> Graph_Destructure {
    mr := Graph_Destructure{on = true, names = names, stores = stores, span = span, writes = !is_decl}
    // (Each name's declaration: made here — a big one's space on the arena,
    // taken before the call writes it (graph_build_decl) — or, written, or a
    // struct's field declared already (graph_build_fields), the variable's.)
    mr.decls = make([]Node_Id, len(names), context.temp_allocator)
    for name, i in names {
        mr.decls[i] = NO_NODE
        if name == "" || name == "_" || stores[i] { continue }
        d := graph_local(b, toks[i])
        if is_decl && (d == NO_NODE || b.g.kind[d] != .Field) { d = graph_build_decl(b, name, toks[i], span, types[i]) }
        mr.decls[i] = d
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
        dest = graph_var(b, mr.decls[i], t, mr.span)
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
    if gm.slot != NO_NODE { return graph_var(b, gm.slot, graph_type(b.g, gm.slot), span) }
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
    arena:    bool,   // a local of its own lives on the arena (graph_scope_open)
}

// An arm, resolved: its tag, its run and block, and — a union's arm that
// binds its payload — the binding, the payload's place.
graph_build_arm :: proc(b: ^Graph_Builder, gm: ^Graph_Match, ga: Graph_Arm, i: int) -> Graph_Block {
    if id := gm.tags[i]; id != NO_NODE {
        b.g.consts[id - CONST].name = graph_intern(b, ga.variant)
        graph_set_value(b.g, id, Const_Value{int = i128(ga.tag)})
    }
    span := gm.span
    b.code.run = gm.arms[i]
    label := "else" if ga.is_else else fmt.aprintf("arm %s", ga.variant)
    k := Graph_Block{n = graph_node(b, .Block, .Explicit, b.code.block, label, nil, span), outer = b.code.block, span = span}
    b.code.block = k.n
    graph_scope_open(b, k.n, span, ga.arena)
    if ga.is_union && ga.bound != "" {
        if ga.payload == nil { graph_fatal(span, "match arm '%s' has no resolved variant", ga.variant) }
        bound := graph_node(b, .Local, .Explicit, k.n, ga.bound, ga.payload, span)
        // The binding is the payload's place, not a copy.
        payload := graph_op(b, .Variant, .Explicit, span, ga.payload, ga.bound, graph_build_subject(b, span, gm))
        b.g.binds[payload] = bound
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
// registered with the scope it is in (Run_Defer runs it at every exit; a
// `defer?`'s, at a return that fails).
Graph_Defer :: struct {
    d:          Node_Id,
    saved:      Code,
    span:       Span,
    on_failure: bool,   // `defer?`: run only by a return that fails
}

graph_build_defer :: proc(b: ^Graph_Builder, span: Span, holds: bool, on_failure: bool) -> Graph_Defer {
    gd := Graph_Defer{d = graph_node(b, .Block, .Explicit, b.code.block, "defer", nil, span), span = span, on_failure = on_failure}
    gd.saved = graph_code_begin(b, gd.d)
    graph_scope_open(b, gd.d, span, holds)
    return gd
}

graph_build_defer_end :: proc(b: ^Graph_Builder, gd: Graph_Defer) {
    graph_code_finish(b, gd.span)
    graph_code_end(b, gd.saved)
    append(&b.code.scopes[len(b.code.scopes) - 1].defers, Scope_Defer{gd.d, gd.on_failure})
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
    body_arena:  bool,   // a local of its body's lives on the arena (graph_scope_open)
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
    // A plain place collection: walked where the loop needs it — built there
    // by lowering (`walk`) — unless it is viewed once, where the loop begins.
    walk:                    proc(data: rawptr, span: Span) -> Operand,
    walk_data:               rawptr,
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

// A range's counter, before its bounds (typed once they are checked): the
// loop's own when no variable is named (`for _ in`).
graph_build_range_counter :: proc(b: ^Graph_Builder, fl: ^Graph_For) {
    if fl.var_name == "" {
        fl.counter = graph_slot(b, "counter", nil, fl.span)
        return
    }
    fl.counter = graph_node(b, .Local, .Explicit, fl.f, fl.var_name, nil, fl.span)
    graph_declare(b, fl.counter, fl.var_tok)
}

// A range's bound at the counter's type, `ct`: cast when its own differs.
graph_build_range_bound :: proc(b: ^Graph_Builder, v: Operand, t, ct: Type, span: Span) -> Operand {
    if t == nil || is_infer(t) || types_equal(t, ct) { return v }
    return graph_op_value(b, .Cast, .Synthetic, span, ct, type_name(ct), v)
}

// The range's bounds built: the counter typed, the end held (a literal's is
// itself), and the counter's first value; then the check run. An end below
// the start, worked out as the program runs, is a range with nothing in it:
// the check (counter < end) runs it zero times. (Both bounds constant, the
// checker said so already: a countdown written as a range.)
graph_build_range :: proc(b: ^Graph_Builder, fl: ^Graph_For, ct: Type) {
    graph_retype(b, fl.counter, ct)
    if !fl.end_literal {
        fl.end_slot = graph_slot(b, "end", ct, fl.span)
        graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, fl.end_slot, ct, fl.span), fl.hi)
    }
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, fl.counter, ct, fl.span), fl.lo)
    graph_build_for_runs(b, fl)
}

// A collection loop, the collection of type `t` checked: a slice's elements
// as they are when the loop begins (`place`, a plain place, viewed once),
// else a plain place walked where the loop needs it (fl.walk); the element
// and the index; then the check run.
graph_build_for_collection :: proc(b: ^Graph_Builder, fl: ^Graph_For, place: Operand, t: Type, is_self: bool, elem_t: Type) {
    fl.coll_t, fl.coll_self, fl.elem_t = t, is_self, elem_t
    if fl.coll_slot == NO_NODE {
        if view := graph_loop_view_of(t); view != nil {
            fl.coll_slot = graph_slot(b, "items", view, fl.span)
            val := graph_op_value(b, .Slice, .Implied, fl.span, view, "", graph_base_of(b, place, t, fl.span, is_self))
            graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, fl.coll_slot, view, fl.span), val)
        } else if fl.walk == nil {
            graph_fatal(fl.span, "a loop's collection walked by no one")
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
    graph_op(b, .Write, .Synthetic, fl.span, nil, "", graph_var(b, fl.counter, index_t, fl.span),
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
// held in the temporary made before it (`held`).
graph_build_items_view :: proc(b: ^Graph_Builder, fl: ^Graph_For, held: Node_Id, place: Operand, is_place: bool, t, view: Type, is_self: bool) {
    span := fl.span
    p := place
    if !is_place {
        graph_op(b, .Write, .Explicit, span, nil, "", graph_var(b, held, t, span), place)
        p = graph_var(b, held, t, span)
    }
    if pt, ok := distinct_base(t).(^Type_Ptr); ok && !is_self {
        p = graph_op_value(b, .Deref, .Implied, span, pt.elem, "", p)   // (through a pointer, what it points at)
    }
    val := graph_op_value(b, .Slice, .Implied, span, view, "", p)
    graph_build_typed(b, fl.coll_slot, view)
    graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, fl.coll_slot, view, span), val)
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
        ct := graph_type(b.g, fl.counter)
        cur := graph_read(b, graph_var(b, fl.counter, ct, span), ct, span)
        bound: Operand
        if fl.is_range {
            if fl.end_slot != NO_NODE {
                bound = graph_read(b, graph_var(b, fl.end_slot, graph_type(b.g, fl.end_slot), span), graph_type(b.g, fl.end_slot), span)
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
    graph_scope_open(b, fl.body_block, span, fl.body_arena)
    if fl.elem != NO_NODE {
        ct := graph_type(b.g, fl.counter)
        at := graph_read(b, graph_var(b, fl.counter, ct, span), ct, span)
        at = graph_widen(b, at, slice_header_width_type, span)
        et := fl.elem_t
        slot := graph_op_value(b, .Index, .Synthetic, span, et, "", graph_coll_place(b, fl, span), at)
        graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, fl.elem, et, span),
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
            ct := graph_type(b.g, fl.counter)
            cur := graph_read(b, graph_var(b, fl.counter, ct, span), ct, span)
            next := graph_op_value(b, .Arith, .Synthetic, span, ct, "+%", cur, graph_const(b, .Synthetic, span, ct, "1", Const_Value{int = 1}))
            graph_op(b, .Write, .Synthetic, span, nil, "", graph_var(b, fl.counter, ct, span), next)
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

// A struct literal built into d, before its fields are
// checked: its construction — zero for `Foo{0}`, else its constructor on
// its params' defaults (a union's variant: its tag, then the field defaults
// the literal doesn't give) — and where its fields are. Nil when t is no
// aggregate the literal builds.
Graph_Literal :: struct {
    d, parent: Dest,
    sd:        ^Scope_Body,
    skip:      int,
}

// A literal's construction at d: a struct's constructor run on `args` (its
// params' defaults, the checker's); a union's variant zeroed and tagged; an
// array zeroed.
graph_build_literal :: proc(b: ^Graph_Builder, span: Span, name: string, zero_init: bool, t: Type, d: Dest, args: []Operand = nil) -> ^Graph_Literal {
    ts, is_scope := distinct_base(t).(^Type_Scope)   // (a named struct's: its base's constructor)
    if is_scope && ts.kind == .Struct && !ts.is_module && zero_init {
        graph_op(b, .Zero, .Explicit, span, t, "{0}", graph_dest_place(b, d, span))
    } else if is_scope && ts.kind == .Struct && !ts.is_module {
        if len(args) != len(ts.params) { graph_fatal(span, "'%s' built without its arguments", ts.name) }
        ops := make([dynamic]Operand, 0, 1 + len(args), context.temp_allocator)
        append(&ops, graph_dest_place(b, d, span))
        append(&ops, ..args)
        op := graph_call_op(b, .Construct, .Explicit, span, ts, t, ..ops[:])
        b.g.name[op] = graph_intern(b, strings.concatenate({graph_name(b.g, op), "{}"}))   // as written: braces, no call
    } else if graph_aggregate(t) {
        if _, is_union := distinct_base(t).(^Type_Union); is_union {
            graph_build_variant(b, t, name, d, span, args)
        } else {
            graph_op(b, .Zero, .Explicit, span, t, name, graph_dest_place(b, d, span))
        }
    } else {
        return nil
    }
    gl := new(Graph_Literal, context.temp_allocator)
    gl.d, gl.parent = d, d
    gl.sd = as_scope_body(distinct_base(t))
    // A union's variant: its fields are the variant struct's, past the tag.
    if st := graph_variant_struct(t, name); st != nil {
        gl.sd = as_scope_body(st)
        gl.parent = Dest{kind = .Variant, name = name, type_ = st, parent = &gl.d}
        gl.skip = first_user_field(gl.sd)
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
    callee := graph_called(b.g, c.op) if c.op != NO_NODE else nil
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
        graph_retype(b, ga.zero, lit_t)
    }
    return Dest{kind = .Index, index = i, type_ = ga.elem_t, parent = &ga.d}
}

// A variant built at d: the union zeroed, its tag written, then — its
// struct's body the constructor, run on `args` — its fields' defaults.
graph_build_variant :: proc(b: ^Graph_Builder, t: Type, name: string, d: Dest, span: Span, args: []Operand = nil) -> ^Type_Scope {
    ops := make([dynamic]Operand, 0, 1 + len(args), context.temp_allocator)
    append(&ops, graph_dest_place(b, d, span))
    append(&ops, ..args)
    op := graph_op_made(b, .Construct, .Explicit, span, t, name, ops[:])
    st := graph_variant_struct(t, name)
    graph_set_callee(b.g, op, st if st != nil && st.node != 0 else nil)   // (its body: its constructor)
    return st
}

// An aggregate built where no destination was given: a synthetic local,
// made before it, typed once it is.
graph_build_temp :: proc(b: ^Graph_Builder, span: Span, t: Type = nil) -> Dest {
    return graph_dest_var(graph_slot(b, "temp", t, span), t)
}

graph_build_temp_end :: proc(b: ^Graph_Builder, d: Dest, t: Type, span: Span) -> Operand {
    graph_retype(b, d.decl, t)
    graph_build_typed(b, d.decl, t)
    return graph_var(b, d.decl, t, span)
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
    graph_op(b, .Zero, .Synthetic, span, t, "", graph_var(b, decl, t, span))
}

// A body's types, now that its widths are known.
// A node's operands while the graph is being built: they end where the next
// node's begin — or, the newest, now.
graph_built_operands :: proc(b: ^Graph_Builder, id: Node_Id) -> []Operand {
    if id >= READ { return b.g.reads[id - READ:][:1] }   // (a read: its leaf)
    if id >= CONST { return nil }   // (a leaf: none)
    end := int(b.g.operand_first[id + 1]) if int(id) + 1 < b.nodes else len(b.g.operands)
    return b.g.operands[b.g.operand_first[id]:end]
}


// A statement of the body's code (not a definition), before it is lowered:
// one right after a return, break or continue is unreachable
// (graph.unreachable).
graph_build_body_stmt :: proc(b: ^Graph_Builder, span: Span) {
    if b.code.active && b.code.run == nil {
        append(&b.g.unreachable, span)
    }
}

// A definition in a body, where it is written — a fun, a struct, a constant:
// its code goes after the body's (graph_place_scope).
graph_build_def :: proc(b: ^Graph_Builder, d: Graph_Decl) {
    append(&b.body.defs, d)
}

// --- constants ------------------------------------------------------------
// A constant is its declaration and the code that computes its value — run
// when the program is compiled, never when it runs. Lowering builds it as a
// code of its own; it is put where it is written (graph_place_decl).

// A constant's code, before its value is built: its declaration (typed
// once the value is) and a run entered from it.
graph_const_begin :: proc(b: ^Graph_Builder, d: Graph_Decl) -> ^Graph_Body {
    graph_code_open(b)
    f := graph_body_new(b)
    f.const_decl = d
    b.body = f
    f.root = graph_node(b, .Const, .Explicit, NO_NODE, d.name, nil, d.span)
    f.contents = Graph_Contents{n = f.root, span = d.span}
    b.self = NO_NODE
    f.contents.code = graph_code_begin(b, f.root)
    return f
}

// Its value built, of type t: its code ends, finished, to be put
// where it is written. One not built is left out (graph_body_fail).
graph_const_end :: proc(b: ^Graph_Builder, f: ^Graph_Body, t: Type) -> ^Program_Graph {
    d := f.const_decl
    if f.failed == "" {
        graph_build_typed(b, f.root, t)
        b.g.type_[f.root] = type_id(b.type_table, t)   // (an untyped one's own: each use's width, graph_fold_code)
    }
    graph_contents_end(b, f.contents, finish = f.failed == "")
    b.body = nil
    c := graph_code_close(b, f)
    if c != nil {
        sync.mutex_lock(&b.prog.lock)
        b.prog.consts[d.id] = new_clone(Built_Code{g = c, b = b, value = d.value}, b.prog.allocator)
        sync.mutex_unlock(&b.prog.lock)
        graph_code_found(b, c, d.value)
    }
    graph_body_free(b, f)
    return c
}


// What a scope's contents change in the builder, until they end.
@(private="file")
Graph_Contents :: struct {
    code:        Code,
    n:           Node_Id,
    span:        Span,
    intrinsic:   bool,
}

// A scope's contents up to its statements: its params and results, and its
// code's start.
@(private="file")
graph_contents_begin :: proc(b: ^Graph_Builder, ts: ^Type_Scope, span: Span, intrinsic: bool, n: Node_Id, holds: bool) -> Graph_Contents {
    kind := b.g.kind[n]
    gc := Graph_Contents{n = n, span = span, intrinsic = intrinsic}
    b.self = n if kind == .Struct else NO_NODE
    for p in ts.params {
        d := graph_node(b, .Param, .Explicit, n, p.name, p.type_, span)
        graph_declare(b, d, p.decl)
    }
    graph_results(b, ts, n, span)
    // An intrinsic's body is generated at each call: no code of its own.
    if intrinsic { return gc }
    gc.code = graph_code_begin(b, n)
    graph_scope_open(b, n, span, holds)
    return gc
}

// A scope's contents after its statements: its code's end (unless it is
// being dropped), and its declarations forgotten.
@(private="file")
graph_contents_end :: proc(b: ^Graph_Builder, gc: Graph_Contents, finish := true) {
    if !gc.intrinsic {
        if finish { graph_code_finish(b, gc.span) }
        graph_code_end(b, gc.code)
    }
    graph_close(b, gc.n)
    graph_map_reuse(&b.locals)   // (its declarations: the next code's are its own)
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
graph_check_coverage :: proc(b: ^Graph_Program, pc: ^Program_Code) {
    count: map[^Type_Scope]int
    defer delete(count)
    for c in pc.codes {
        if c.kind[0] == .Fun || c.kind[0] == .Struct { count[graph_type(c, 0).(^Type_Scope)] += 1 }
    }
    bad := 0
    check :: proc(count: ^map[^Type_Scope]int, bad: ^int, t: ^Type_Scope, span: Span) {
        if n := count[t]; n != 1 {
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

// Refers-to is complete: every variable's leaf names a declaration of the
// code's (the compiler's own globals' placed in it).
@(private="file")
graph_check_refers :: proc(g: ^Program_Graph) {
    bad := 0
    for l, i in g.leaves {
        if l.decl < 0 || int(l.decl) >= len(g.kind) || g.kind[l.decl] == .Op {
            o := graph_origin(g, LEAF + Node_Id(i))
            emit_diagnostic(.Graph_Error, span_location(o), "'%s' names no declaration", graph_name(g, LEAF + Node_Id(i)))
            bad += 1
        }
    }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// The runs are well formed: every operation is in exactly one run; a run
// ends in its only terminator; Then edges land on the first operation of a
// run; and an operand dominates its use: earlier in the same run, or in a run
// every path to the use passes through.
@(private="file")
graph_check_runs :: proc(g: ^Program_Graph) {
    n_runs := len(g.run_first) - 1
    run_of := make([]i32, graph_ix_count(g))
    pos := make([]i32, graph_ix_count(g))
    defer delete(run_of)
    defer delete(pos)
    slice.fill(run_of, -1)
    bad := 0
    report :: proc(g: ^Program_Graph, bad: ^int, id: Node_Id, format: string, args: ..any) {
        o := graph_origin(g, id)
        emit_diagnostic(.Graph_Error, span_location(o), format, ..args)
        bad^ += 1
    }
    for r in 0 ..< n_runs {
        ops := graph_run(g, r)
        for id, i in ops {
            if run_of[graph_ix(g, id)] != -1 { report(g, &bad, id, "operation %d is in two runs", id) }
            run_of[graph_ix(g, id)] = i32(r)
            pos[graph_ix(g, id)] = i32(i)
            last := i == len(ops) - 1
            if graph_is_terminator(graph_op_of(g, id)) != last {
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
        r := run_of[graph_ix(g, e.to)]
        if r == -1 || pos[graph_ix(g, e.to)] != 0 { report(g, &bad, e.to, "a then edge lands inside a run"); continue }
        if graph_kind_of(g, e.from) != .Op { is_entry[r] = true; continue }
        append(&succ[run_of[graph_ix(g, e.from)]], r)
        append(&pred[r], run_of[graph_ix(g, e.from)])
    }
    idom := graph_dominators(n_runs, succ, pred, is_entry)
    defer delete(idom)
    for id in 0 ..< len(g.kind) {
        if g.kind[id] != .Op { continue }
        for o in graph_operands(g, Node_Id(id)) {
            if o.op == NO_NODE { continue }
            if o.op >= CONST { continue }   // (a leaf: no operation)
            if graph_kind_of(g, o.op) != .Op { report(g, &bad, Node_Id(id), "operand %d is no operation", o.op); continue }
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

// MARA_GRAPH=full prints every code (graph_dump_full), then the statements
// nothing reaches: what test/graphdiff.sh compares.
@(private="file")
graph_dump :: proc(pc: ^Program_Code) {
    if os.get_env("MARA_GRAPH", context.temp_allocator) != "full" { return }
    for c in pc.codes {
        fmt.printfln("code %v %s", c.kind[0], graph_name(c, 0))
        graph_dump_full(pc, c)
    }
    for s in pc.unreachable { fmt.printfln("u @%s:%d:%d", filepath.base(span_file(s)), span_line(s), span_col(s)) }
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
    for id in 0 ..< len(g.kind) { if graph_called(g, Node_Id(id)) != nil { calls += 1 } }
    fmt.printf("graph: %d nodes, %d runs, %d edges\n", len(g.kind), len(g.run_first) - 1, len(g.edges) + calls + len(g.defer_of))
    for id in 0 ..< len(g.kind) {
        b := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&b, "n %d %v %v %v p%d l%d %q", id, g.kind[id], g.op[id], g.written[id],
            g.parent[id], graph_last(g, Node_Id(id)), graph_name(g, Node_Id(id)))
        if t := graph_type(g, Node_Id(id)); t != nil { fmt.sbprintf(&b, " t=%s", type_name(t)) }
        fmt.sbprintf(&b, " @%s r%d s%d", span(graph_origin(g, Node_Id(id))), graph_refers(g, Node_Id(id)), graph_stmt(g, Node_Id(id)).node)
        if ops := graph_operands(g, Node_Id(id)); len(ops) > 0 {
            strings.write_string(&b, " (")
            for o, i in ops {
                switch {
                case o.op >= READ:  fmt.sbprintf(&b, "%sr%d", ", " if i > 0 else "", o.op - READ)
                case o.op >= LEAF:  fmt.sbprintf(&b, "%sv%d", ", " if i > 0 else "", o.op - LEAF)
                case o.op >= CONST: fmt.sbprintf(&b, "%sc%d", ", " if i > 0 else "", o.op - CONST)
                case:               fmt.sbprintf(&b, "%s%d.%d", ", " if i > 0 else "", o.op, o.out)
                }
            }
            strings.write_string(&b, ")")
        }
        if c, ok := graph_value(g, Node_Id(id)); ok { fmt.sbprintf(&b, " const=%v", c) }
        if c := g.constant[Node_Id(id)]; c != 0 {   // (by its code's name: a value's node isn't the same from one build to the next)
            code, built := pc.consts[c]
            fmt.sbprintf(&b, " constant=%s", graph_name(code, 0) if built else "?")
        }
        if s, ok := g.assert_sides[Node_Id(id)]; ok { fmt.sbprintf(&b, " sides=%q|%q", s[0], s[1]) }
        if k, ok := g.consumes[Node_Id(id)]; ok { fmt.sbprintf(&b, " consumes=%d", k) }
        fmt.println(strings.to_string(b))
    }
    // (Each constant: its name, type, value, where it's written; each leaf:
    // its variable, its type, where it's written.)
    for c, k in g.consts {
        id := CONST + Node_Id(k)
        line := fmt.tprintf("c %d %q %v t=%s @%s", k, graph_name(g, id), c.written, type_name(graph_type(g, id)), span(graph_origin(g, id)))
        if v, ok := graph_value(g, id); ok { line = fmt.tprintf("%s const=%v", line, v) }
        if n := g.constant[id]; n != 0 {
            code, built := pc.consts[n]
            line = fmt.tprintf("%s constant=%s", line, graph_name(code, 0) if built else "?")
        }
        fmt.println(line)
    }
    for l, k in g.leaves {
        id := LEAF + Node_Id(k)
        fmt.printfln("v %d -> %d %v t=%s @%s", k, l.decl, graph_written(g, id), type_name(graph_type(g, id)), span(graph_origin(g, id)))
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
    for id in g.settled { fmt.printfln("settled %d", id) }
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
