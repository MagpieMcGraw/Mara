# Mara program graph

2026-09-27 · snapshot of the living doc: https://claude.ai/code/artifact/c1effed0-e3f1-4639-8105-c32451abd07d

## Purpose

The program graph is a complete description of a Mara program: everything that exists, everything that happens, and in what order. It is rebuilt from the text on every compile and it is the compiler's IR. Beyond compiling, it serves three uses:

- **`mara ask`**: see what anything is connected to, at any zoom level, in both directions.
- **Editing through the graph**: change a connection and have the change written back into the text.
- **Position-independent compilation**: point the cursor at code and see its LLVM IR or assembly, live.

Today that description is scattered: annotations and lowered forms on the syntax tree (`type_`, `lowered_args`, `.checked`), plus separate pieces with their own node types and keys — the call graph (`callgraph.odin`), use-def (`usedef.odin`), type dependencies (`ask.odin`) and flow slices (`slice.odin`, `lineage.odin`). The program graph gathers them into one structure with one shape.

## Two structures

```
source text + tokens      what you wrote; comments are the gaps between tokens
        │
        ▼
syntax tree               the text's shape: where each thing is written
        │                   ▲ every graph node points back to its origin here
        ▼
program graph (the IR)    the program's shape: what exists and what happens,
        │                 in order, with every connection
        ├──► views                  mara ask: the graph zoomed out
        └──► LLVM IR / assembly     the graph translated

edits made through a view become text patches; both structures are rebuilt
```

Mara has two structures. The syntax tree keeps the text's shape, so it knows where each thing is written. The program graph has the program's shape: everything that exists and everything that happens, in order. The program graph is the IR: walking it from `main` is running the program.

Every graph node points back to the syntax it came from. Nodes the text never spells out — a loop's counter, a default argument at a call, a generic function's copy for one type — point to the text that caused them.

Everything else is computed from the graph and never edited: `mara ask` views (the graph zoomed out), LLVM IR (the graph translated), and indexes such as reverse edges or the call graph's summaries. Indexes are rebuilt on every build, like the index of a book; they are never a second description of the program. An edit never changes a structure in memory: it becomes a text patch, and both are rebuilt.

## Nodes

Nodes come in three kinds:

- **Scopes**: module, struct, function, block.
- **Names declared in a scope**: field, parameter, local, constant, a function's result.
- **Operations**: the things that happen — a call, an add, a comparison, a store. They live inside functions and blocks, in order.

Some nodes are **synthetic**: the program has them but the text never spells them out. A loop's counter, a default argument at each call, and one copy of a generic function per type it is used with are all synthetic; each points to the text that caused it.

The running example for the rest of this doc:

```
module shop

Item :: struct {
	price: i64
}

total :: fun(items: []Item) -> i64 {
	sum := 0
	for it in items {
		sum += it.price
	}
	return sum
}

main :: fun() {
	cart : [3]Item
	t := total(cart[:])
	print(t)
}
```

Because everything is a scope, modules, structs, functions and blocks are one kind of node. They differ in one property: how many copies of their names exist when the program runs.

| Scope | Copies of what it declares | In the example |
| --- | --- | --- |
| Module | one | anything `shop` declares |
| Struct | one per value | `price`, once per `Item` |
| Function | one set per call | `sum`, once per call of `total` |
| Block | one per run of the block | `it`, once per loop iteration |

That is the fun/struct unification and split in one line: the same kind of node, differing in when copies are made. The graph stores one node per written declaration, not per run-time copy, so a flow into `Item.price` means every Item's price unless a query says which one (see Queries).

## Connections

Six kinds of connection, each found by a different stage of the compiler. The containment tree is the backbone; the other connections cut across it. The picture shows the graph zoomed out to named things.

```
shop (module)
├── Item (struct)
│   └── price : i64
├── total (fun)
│   ├── items : []Item
│   ├── sum : i64
│   ├── for (block)
│   │   └── it : Item
│   └── result : i64
└── main (fun)
    ├── cart : [3]Item
    └── t : i64

has type:  items → Item    cart → Item    it → Item    price → i64
calls:     main → total    main → print
flows:     cart → items → it → sum → result → t
```

Refers-to isn't shown: it joins every use of a name to its declaration, so it is everywhere.

Zoomed in, `total` is operations joined by **then** — what happens next. Inside a straight run, order is just list order; a branch has two `then` edges, a loop has one pointing back:

```
total
  start:  sum = 0,  i = 0                            then → check
  check:  i < items.len ?          yes: then → body     no: then → done
  body:   it = items[i]
          sum = sum + it.price
          i = i + 1                                  then → check
  done:   return sum
```

Walking start → check → body → check → … → done is running `total`; following a call operation into another function's graph is running the call. The counter `i` is synthetic: the loop needs it, the text never wrote it.

| Connection | Meaning | Found by | Used for |
| --- | --- | --- | --- |
| contains | a scope holds a declaration, an operation or another scope | the parser: how the text is nested | the zoom level (module, struct, fun, var) |
| refers to | a use of a name → its declaration | name resolution (the scope stack) | underlies everything |
| has type | a declaration or operation → its type | the type checker | `mara ask` type |
| calls | a call operation → the function it calls | building the graph, where hidden calls become explicit | `mara ask` call |
| flows | a value moves from one place to another | building the graph, where defaults and method receivers become explicit | `mara ask` flow |
| then | an operation → the one that runs next | building the graph, where loops and branches become explicit | execution order; code generation walks it |

## Storage

Every node is a numbered id, and each kind of connection is stored by its shape: one number per node when there is exactly one, an edge table when there are many. Everything is plain numbers, so the graph can be saved, sent to an editor, or compared with the previous build's.

**The tree: a parent column, numbered depth-first.** Each node stores its one parent. Nodes are numbered in the order they are written, so a scope's whole subtree is one run of ids.

| id | node | parent |
| --- | --- | --- |
| 0 | shop | – |
| 1 | Item | 0 |
| 2 | price | 1 |
| 3 | total | 0 |
| 4 | items | 3 |
| 5 | sum | 3 |
| 6 | for | 3 |
| 7 | it | 6 |
| 8 | result | 3 |
| 9 | main | 0 |
| 10 | cart | 9 |
| 11 | t | 9 |

`total` is id 3 and its subtree is ids 3 to 8, so "is `it` inside `total`?" is 3 ≤ 7 ≤ 8: two integer comparisons.

**One-per-node facts: a column indexed by id.** A declaration has exactly one type; a use of a name refers to exactly one declaration. Each is an array with one slot per node: `has_type[4] = []Item`, and the `sum` in `return sum` has `refers_to = 5`. The reverse direction (every use of `sum`, everything of type `Item`) is built once per build by inverting the column.

**Many-to-many (calls, flows): one edge table.** Each connection is a record:

```
Edge :: struct {
	from:    Node_Id
	to:      Node_Id
	kind:    Edge_Kind   // Calls or Flows
	site:    Node_Id     // where it is written: the call, the argument
	written: Written     // Explicit, Implied or Synthetic
}
```

| kind | from → to | site | written |
| --- | --- | --- | --- |
| Calls | main → total | `total(cart[:])` | Explicit |
| Calls | main → print | `print(t)` | Explicit |
| Flows | cart → items | `cart[:]`, argument to parameter | Explicit |
| Flows | items → it | `for it in items` | Explicit |
| Flows | it → sum | `sum += it.price` | Explicit |
| Flows | sum → result | `return sum` | Explicit |
| Flows | result → t | `t := total(…)` | Explicit |

The table is sorted by `from`, with two indexes beside it: *outgoing* (for each node, where its run of edges starts) and *incoming* (edge numbers sorted by `to`). A node's list of connections is its slice of the table, one slice per direction.

Why not an array stored on each node: it would need two arrays per node (one per direction), copy each edge's data onto both ends, and mean thousands of small allocations rebuilt on every keystroke. One table built in a single pass is simpler and faster.

**Operations: in order, in runs.** Each function's operations are stored in execution order, cut into straight runs (`start`, `check`, `body`, `done` above). A run stores its `then` edges: one, or two after a branch. An operation lists its inputs directly, which are its incoming flows at the finest zoom. The named-level flow edges in the table above are those chains zoomed out, kept as an index.

## Queries

Every `mara ask` question is one rule: pick a kind of connection, a direction and a scope; the answer is the connections of that kind that cross the scope's boundary in that direction. Because a scope's subtree is one run of ids, "crosses the boundary" is one end inside the range and the other outside.

- **Above** = what the thing depends on; **below** = what depends on it. For calls and types that follows the edge (a caller depends on its callee, a declaration on its type); for flows it runs against the edge (a value depends on where it came from).
- **Depth** limits how many steps to follow. **`in <scope>`** keeps only edges with both ends inside that scope's range.
- **Zoom** is a view, not a structure. Zoomed out, operations merge into the named things they read and write and `then` edges are hidden; results roll up to a chosen scope level (the module / struct / fun / var rows of the ask matrix). Zoomed all the way in, the same rule walks operations and `then` edges.

| Query | Walk | Answer in the example |
| --- | --- | --- |
| `main call above` | call edges leaving ids 9–11 | `total`, `print` |
| `total call below` | call edges entering ids 3–8 | `main` |
| `t flow above` | flow edges into `t`, repeatedly | `result` ← `sum` ← `it` ← `items` ← `cart` |
| `Item type below` | has-type edges into `Item` | `items`, `it`, `cart`; rolled up: `total`, `main` |
| `shop call above` | call edges leaving the module's range | `print` (another module) |

**Per-copy questions.** The graph holds one node per written declaration, so `Item.price` stands for every Item's price. A precise question such as "does this cart's price reach `t`?" is answered by the query following an access path (`cart[i].price`) through the declaration graph. The summaries stay context-free and the query supplies the particular copy; this is the anchored walk from `design/mara_ask.md` §3.

## Identity and editing

**Stable identity.** Ids are renumbered on every build, so across builds a node is known by its path through the tree: `shop.total.sum`. A block has no name and takes its position instead: `shop.total.for#1.it`. The path survives any edit that doesn't rename or move the node, which makes two builds' graphs comparable.

**How each edge is written.** Every edge records its site and one of three kinds:

| Written | Meaning | Example | To change it |
| --- | --- | --- | --- |
| Explicit | the edge is a range of source | `total(cart[:])` is the call `main → total` | rewrite that range |
| Implied | the edge comes from another construct | a default argument's flow into its parameter; a method call's receiver | write it out explicitly first, then rewrite |
| Synthetic | the compiler introduced it; no text | the constructor call a bare `x : Item` makes | not editable directly |

**The edit loop.** The graph is never edited in memory; edits go to the text.

1. Query the graph and decide the change, for example moving a call or narrowing a parameter.
2. Turn the change into text patches over the affected edges' sites. Comments and formatting outside those ranges stay exactly as written.
3. Rebuild every layer from the patched text.
4. Compare the old and new graphs by stable path. A pure refactor (rename, move) must produce an empty difference; a reshape must produce exactly the intended one.

First target: parameter narrowing from `design/mara_ask.md` §10. `camera_turn_walking` reads only `input.mouse`, so its parameter becomes `^Mouse` and every call passes `input.mouse`. The graph difference should show the parameter's has-type edge moving from `Input` to `Mouse` and each call's flow narrowing from `input` to `input.mouse`, and nothing else.

## Open questions

1. **Access paths as nodes?** Store only declarations (`Item.price`) and let queries follow paths, or also store paths (`cart.price`) as nodes. Declarations keep the graph small; stored paths make per-copy questions cheap.
2. **Generics.** One node for a generic function's template, one per instance, or both linked. The instances are what runs; the template is what is written and edited.
3. **The graph's operations.** Decided: the graph is the IR, built from the syntax tree by lowering. Next to design: which operations it has (call, load, store, compare, branch and so on), how code generation expands each into LLVM IR, and which zoomed-out views are worth keeping as indexes.
4. **Partial results while code is broken.** Today one type error anywhere aborts the build. A live graph needs a broken function confined to itself, with the rest of the program still producing its graph.
5. **Position-independent compilation.** Two tiers: show the matching slice of a whole-program compile (needs every LLVM instruction tagged with its origin), and compile a fragment on its own (its above-set becomes parameters and external declarations).
