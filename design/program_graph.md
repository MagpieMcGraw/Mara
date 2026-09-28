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

**One-per-node facts: a column indexed by id.** A declaration has exactly one type; a use of a name refers to exactly one declaration. Each is an array with one slot per node: `has_type[4] = []Item`, and the `sum` in `return sum` has `refers_to = 5`. The reverse direction (every use of `sum`, everything of type `Item`) is built once per build by inverting the column. An operation also records the statement it was lowered from (a statements table: its origin and kind), which is how an analysis reports a line and what a write is: a declaration, an assignment, a destructure.

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

## Operations

Operations are at Mara's level: one for each thing the language does, whether the text writes it or the language does it for you. Each kind has one fixed LLVM template, so code generation is transcription and never looks at an operation's surroundings. That gives the test for the set: if an operation's LLVM can't be written from the operation and its types alone, the missing context must be an operation too. So implicit work is in the graph — defers at every exit, zero-init, construction, arena resets — built once and seen by every analysis, instead of each consumer deriving it again.

- An operation takes other operations' outputs as inputs and has zero or one output; a call has one per return value.
- Variables are slots. Operations reach one through a **place**: `var`, then `field`, `index` or `deref` steps; `read` and `write` go through a place. LLVM turns slots into registers, so the graph is never in SSA form.
- Structs, arrays and unions are built in place: `construct`, `fill`, and calls that return them write straight into a destination place. That is return-value optimization by construction.
- Control flow is runs joined by `then`, and four operations end a run. A value that depends on a branch (`a and b`, an `if` expression) goes through a synthetic slot, so there is no merge operation. An operand dominates its use: it comes earlier in the same run, or in a run every path to the use passes through.
- Checks that only stop the program — bounds, overflow, division by zero — are part of their operation's template, not operations.
- An operation the text doesn't write carries the Implied or Synthetic mark (see Identity and editing) and points at the syntax that caused it.

About thirty kinds in all.

**Places**

| Operation | Written as | LLVM |
| --- | --- | --- |
| `var` | `x` | the variable's slot; no instruction |
| `global` | `COLORS` (a constant table), `"hi"` | `@name`, `@.str.<hash>` |
| `field` | `p.x` | `getelementptr` to the field |
| `index` | `a[i]` | bounds check and `getelementptr`; a slice loads its pointer first |
| `view` | bytes at an offset seen as a `T`: `x : T = bytes[off]`, `bytes[off] = x`, `&bytes[off]` taken as a `^T`; `#big_endian` | check `off + size_of(T) <= cap`, then `getelementptr` to the byte; what goes through it is `align 1`, and a big-endian view's integers are swapped |
| `deref` | `p^`; implied in `p.x` when `p: ^T` | `load ptr` |
| `variant` | the bound payload in a `match` arm | `getelementptr` past the tag |
| `swizzle` | `v.xy` | element addresses or `shufflevector` |
| `slice` | `a[lo:hi]`, `slice_from_ptr(p, n)`; written to, `a[lo:hi] = b` | a slice header: pointer, length, capacity; written to, b's elements copied in from lo — as many as b has when hi is open — with lo and hi checked against the capacity |

**Memory**

| Operation | Written as | LLVM |
| --- | --- | --- |
| `read` | a place used as a value | `load`, or the address itself for a struct |
| `write` | `x = v`, `p.x += 1`; `x = void` writes the `void` constant | `store`, or `memcpy` for a struct; `void` stores nothing, or a pointer's null |
| `address` | `&x` | the place itself; no instruction |
| `zero` | synthetic, from `x : T`; `Foo{0}`; `s : []T(n)` takes `n` | `store zeroinitializer` or `memset`; for `n`, storage for n elements and the slice header over it |
| `construct` | `Foo(a)`, `Foo{…}`; synthetic from `x : Foo` | `memset`, then a call to Foo's init into the place |
| `fill` | `{all x}` | a store per slot, a loop when large |
| `carve` | `let(T, mem)`, `slice([:n]T, mem)`; positional, `let(T, &bytes[i])` | align the cursor, `getelementptr`, bump `mem.len`; positional, the view of the bytes there |
| `byte read` | a partial array filled from bytes (`pa = bytes[off]`, `pa = bytes[lo:hi]`), a value from a span (`x : T = bytes[lo:hi]`); `#big_endian` | checks, `memcpy`, `bswap`; a fill sets `len` |
| `arena alloc` | synthetic, for a local too big for the stack | `call arena_alloc` |

**Values**

| Operation | Written as | LLVM |
| --- | --- | --- |
| `const` | `42`, `2.5`, `true`, `'a'`, `.Ok`, `size_of(T)` | an immediate |
| `arith` | `+ - * / %`, shifts, bit operations | `add`, `fadd` and so on, with overflow and division-by-zero traps |
| `compare` | `== != < <= > >=` | `icmp`, `fcmp` |
| `unary` | `-x`, `not x` | `sub 0`, `xor` |
| `cast` | `f32(x)`, `Meters(x)` | `sext`, `trunc`, `sitofp` and so on, or nothing |

**Calls**

| Operation | Written as | LLVM |
| --- | --- | --- |
| `call` | `f(a)`, `a.f()`, a dispatch or generic call, `a + b` through `overload`, `op(x)` through a function value, a foreign function | `call`: direct, through a pointer, or with the C ABI; struct and multiple returns go into destination places |
| `print` | `print(a, b)` | one operation; a formatting call per argument, chosen by its type |
| `assert` | `assert(c)` | a branch to a failure that prints the source text |
| `crash` | `crash(msg)` | print, then `exit` |

**Ending a run**

| Operation | Written as | LLVM |
| --- | --- | --- |
| `jump` | the end of a block, `break`, `continue`, a loop's back edge | `br label` |
| `branch` | `if`, `elif`, a loop's condition, `and` / `or`, `if` expressions, `?` | `br i1` |
| `switch` | `match` | load the tag, `switch` |
| `return` | `return a, b`; implied by `?` on an error | store the return slots, `ret` |
| `run defer` | synthetic, at every exit of a scope, once per defer registered so far, the last first | the defer's block, emitted inline |
| `arena mark`, `arena reset` | synthetic, at entry to and every exit of a scope holding big values | `call` |

**Braces are a block of writes.** `{…}` after a value runs its writes against that value, as a scope body runs against its scope. The forms differ only in the step before the writes:

| Form | First | Then |
| --- | --- | --- |
| `Foo{a = 1}` | `construct` Foo into the destination | `write` `.a = 1` |
| `{1, 2, 3}` | `zero` the destination | `write` slots 0, 1 and 2 |
| `v{a = 1}`, in place | nothing: the destination is `v` | `write` `.a = 1` |
| `y := v{a = 1}`, a copy | `write` `y = v` | `write` `.a = 1` |

This is today's meaning: a field's default runs, then the override replaces it. The copy form is rejected today because variables and types share one namespace; that is language work, and the graph already has its shape.

**Not operations.** A loop is runs and a back edge: `for i in 0..n` adds a synthetic counter with its compare and add, and `for it in items` a synthetic index and `it = items[i]`. `defer { … }` stores its block on the scope, and `run defer` executes it, so a defer is stored once however many exits the scope has. The block's code is a fun's in miniature: a run entered from the block, ending in a `return` back to the `run defer`. `break` and `continue` are jumps. Constants and `#if` are resolved before the graph is built.

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

1. **Access paths as nodes?** Decided: declarations only. At the finest zoom an access path is already a chain of place operations (`var cart`, `index i`, `field price`; see Operations), so per-copy questions follow those chains.
2. **Generics.** Decided: one node per instance, since the instances are what runs and what code generation needs; the template is syntax only, and every instance points at it as its origin.
3. **Partial results while code is broken.** Today one type error anywhere aborts the build. A live graph needs a broken function confined to itself, with the rest of the program still producing its graph.
4. **Position-independent compilation.** Two tiers: show the matching slice of a whole-program compile (needs every LLVM instruction tagged with its origin), and compile a fragment on its own (its above-set becomes parameters and external declarations).
