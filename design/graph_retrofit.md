# Program graph retrofit

2026-09-27 · plan for moving Mara1 to the design in `design/program_graph.md`: two structures, the
syntax tree (the text's shape) and the program graph (the program's shape, which is the IR).

The retrofit is staged, not a rewrite: every phase ships on its own with the suite green, Pounce
building, and a check that proves what changed. That is the lesson of Mara3.

## What exists today

Most of the program graph already exists, scattered and keyed six different ways (node pointers,
spans, name strings, rawptr):

| Piece | Where | Becomes |
| --- | --- | --- |
| Call graph: int ids, SCCs, bottom-up summaries, purity, return deps | `callgraph.odin` | an index over Calls edges |
| Declarations, defs, reaching definitions, call sites | `usedef.odin` | declaration nodes, refers-to, operation inputs |
| Statement-level blocks and jumps | `cfg.odin` | runs and `then` edges |
| Type edges (contains / takes / returns) | `ask.odin` | has-type and contains edges |
| Token extents | `hittest.odin`, `Span.tok` | origins |
| Escape summaries | `escape.odin` | per-function summaries on the graph |

About a dozen walkers re-derive the same sugar from the AST and already disagree (loop-variable
sources, which calls count, operator calls, tuple defaults).

The big job is codegen: about 60–75% of its 17.9k lines is lowering decided from the AST's shape
(default construction, field defaults, defers re-emitted at every exit, arena mark/reset, bounds
checks, `?` branches, loop counters, match dispatch, `print`). "The graph is the IR" means that
knowledge moves into graph building.

## Phases

| Phase | What | Touches | Proof |
| --- | --- | --- | --- |
| 0 | Cleanup and pre-existing bugs (below); per-function temp numbering in codegen | small edits | suite + IR differential |
| 1 | Build the graph beside the pipeline, as a pass after checking: declarations with ids, refers-to, has-type, calls per site, operations in runs joined by `then`. Nothing consumes it yet. | new files | suite + graph dumps |
| 2 | Analyses onto the graph: call graph becomes an index; `cfg.odin`, `usedef.odin` dissolve; flow, slice/lineage, `mara ask`; definite assignment and escape last | analysis files | IR identical; recorded `mara ask` outputs identical |
| 3 | Codegen from the graph, one function at a time (the switch is the per-module worker loop); graph building absorbs codegen's implicit operations | codegen | normalized IR diff + runtime differential |
| 4 | The checker builds the graph directly; annotations, `lowered_*`, accessors and the shape check are deleted | checker | suite + IR diff |
| 5 | Flat syntax tree: integer ids, token ranges, slim tokens | parser, checker | shape parity, then IR diff |

Phases 3 and 4 run on their own branch with no parallel compiler work. The compiler runs over 50k
lines while old and new codegen coexist; the end state should be smaller than today.

Before phase 1: design the graph's operations on paper (the op set, how each is written in text,
what each becomes in LLVM).

The IR differential is `test/irdiff.sh`: it builds every fixture with a main, the multifile
fixtures, Pounce and `design/all` with `Mara_base_tmp.exe` (the baseline) and `Mara.exe`, and
requires identical IR and build output. `-n` compares modulo naming instead (`test/irnorm.pl`
renames locals and labels by first use and replaces string globals by their contents), which is
the check for phase 3.

## Phase 0 checklist

- [x] Dead fields: `Expr_Call.desugared` (read, never written), `Stmt_For.collection_len` (read,
      never written), `Stmt_For.collection_type` (written, never read), `Stmt_Assign.checked`
      (unused), `Stmt_Scope.fields` (never written by the parser)
- [x] `?` early return skips defers and arena resets (`codegen_expr.odin` ~1955,
      `codegen_stmt.odin` ~938)
- [x] Allocas are de-duplicated by name, blind to type: same-named locals in sibling scopes share
      one slot (`codegen.odin` ~1283, ~1441). Now a named local takes `name.2` when the type
      differs (`emit_local_alloca`), and reusing a name at another type is a hard error. Found
      alongside: loops never dropped their bindings, so a local declared again after a loop skipped
      its zero-init, and runtime-sized or arena-backed locals defined one IR name twice
      (`test/sibling_locals.mara`)
- [x] `populate_cg_signature` runs lazily inside the parallel codegen workers — a possible race
      (`codegen.odin` ~1185). Structural fn types now fill it where they resolve; a signature
      reaching codegen without it is a hard error (`test/fn_type_values.mara`)
- [x] Operator-overload calls are never recorded as call-graph edges (purity, escape and
      `mara ask` miss them). Both overload resolutions now record the edge
      (`test/operator_calls.mara`; its `mara ask` edges go in the goldens)
- [x] `take([]T(n), …)` rewrites a source `Type_Slice_Expr` in place; no fixture covers it. Now
      lowered into `Expr_Take.lowered_type` / `lowered_count` (read through `take_type` /
      `take_count`). The rewrite also broke generics: instances share the type expression, so the
      second lost its count (`test/slice_count_carve.mara`)
- [x] `clone_expr` shares a `{all x}` literal's `array_values` buffer between clones. It shared
      `broadcast_value` too, so generic instances annotated one node; and a re-checked clone of a
      generic call kept only its instance name, which no lookup resolved (`{all ident(p)}` failed
      in codegen). Fixed both (`test/broadcast_clones.mara`)
- [x] Codegen numbers labels and strings module-wide; restart per function so IR compares per
      function. Labels restart per function; string globals are named by a hash of their contents
      (`@.str.<16 hex>`), so no name depends on what was emitted before it
- [x] `mara ask` output: record goldens before phase 2 (none exist today). `test/ask.sh` runs
      `test/ask_queries.txt` (32 queries over Pounce and `test/operator_calls.mara`, the whole
      argument matrix) against `test/ask_expected.txt`; `-u` re-records. Recording them found
      output following map order (defs sharing a span, lineage children); now sorted totally
- [x] Found: nested broadcast `g : [2][3]i64 = {all {all x}}` fails to type-check (the inner
      literal is checked against the outer's types). An anonymous broadcast value now takes the
      element type as its hint (`test/nested_broadcast.mara`)
- [x] Found: a fn-type parameter followed by another parameter doesn't parse — in
      `fun(op: fun(i64) -> i64, x: i64)` the return list swallows `, x`. An unwrapped return list
      now ends at a named group, and a fn type's returns are positional only
      (`test/fn_type_values.mara`)

Later, not phase 0: `mara ask` refuses to run with any type error anywhere (partial results are a
phase 2–4 concern).

## Phase 1 checklist

The graph is built in `graph.odin` after checking (the `graph` stage of the perf timer).
`MARA_GRAPH=<name>` prints the subtree of every node with that name, `MARA_GRAPH=all` the whole
graph. Debug builds check that every checked scope and type is exactly one node, that the calls
agree with `callgraph.odin` and that the runs are well formed; with `MARA_GRAPH_CHECK=1` (the
suite sets it) they also check refers-to against `usedef.odin`.

- [x] Storage and declarations: modules, structs, unions, enums, funs and blocks, with their
      fields, params, results, locals, constants, imports, variants, type definitions and dispatch
      groups; contains (the parent column, depth-first) and has type. A generic's instances are
      nodes, the template is syntax only. test_1M: 720k nodes, 378 ms (3.4% of type check), peak
      memory +0.1 GB
- [x] Calls: one edge per call site, checked against `callgraph.odin` on every build. `call` and
      `construct` operations (the first operations) each carry a Calls edge; the edge table has
      outgoing and incoming indexes. The check found the call graph missing real calls, now
      recorded by the checker: a bare `x : Foo` (and arrays of structs) constructs Foo, an
      anonymous `h : Foo = {…}` constructs Foo, and a generic struct instance's bare fields
      construct theirs. Struct instances now carry their template's span. Calls in a default
      argument run in the caller but the checker checks a default once in the callee's scope, so
      those are Implied edges the check skips; phase 2 closes that gap. test_1M: 775k nodes,
      585 ms with both debug checks (5.4% of type check)
- [x] Operations in runs joined by `then`: every expression and statement lowered to the
      operation set (design/program_graph.md § Operations, plus `slice`), with their operands.
      Runs are a list apart from the tree; a Then edge joins a run's terminator to each next run's
      first operation. Synthetic operations: zero or construct for bare declarations, arena alloc
      / mark / reset, a `run defer` per registered defer at every exit (end of scope, `return`,
      `break`, `continue`, `?`), loop counters, and locals for values that outlive a run (`and` /
      `or`, `if` expressions, a range's end, a collection or match subject that is no plain place).
      A store's destination is emitted after its value. Debug builds check the runs: each ends in
      its only terminator, and every operand dominates its use. test_1M: 5.7M nodes, 113k runs;
      2.0 s in the debug build with the checks (18% of type check), 0.97 s optimized (17%, about
      codegen's cost); peak memory 6.3 → 7.0 GB. Worth a profiling pass before phase 2
- [x] Refers-to: each `var` operation → the declaration it names, checked against `usedef.odin`
      (every one of test_1M's 894k uses agrees). Locals resolve through a scope stack as the walk
      goes; definitions (constants, functions, types) by the nearest enclosing scope once all
      are built, since they can be used before they are written; the compiler's own
      `this_program` and `context` are fields of a synthetic `program` scope. The flow index: a
      Flows edge per declaration a value is read from, at each write, call argument, return and
      match binding (field-insensitive). test_1M: graph 2.6 s in the debug build

Phase 1 is complete: the graph is built on every compile and checked, and nothing reads it yet.

Left for phase 3, where codegen reads the graph: a `const` operation carries no value yet; calls
produce values, and passing a destination to a call that returns an aggregate (sret, NRVO) is
codegen's; the graph's arena rule is `routes_to_arena` (≥ 1024 bytes), while codegen's
`scope_has_big_values` tests structs with `> 1024` and bumps partial arrays without a scope mark;
the checker types a collection loop's index as `i32` against `i64` lengths.

Found after: a function could name its module's variables. The checker registered them as
constants, so a read inlined the initial value and a write made a hidden local. A module is a
scope and its variables are its locals, which no function sees (a function sees the outside world
only through its arguments): now a checker error (`test/module_locals_neg.mara`), and the graph
resolves no name to them.

## Phase 2 checklist

The analyses move onto the graph one at a time, each proven by the suite, the IR differential and
the `mara ask` goldens; a change in output is listed with its cause. The analyses run only on a
program that checked clean, since the graph is built from checked types.

- [x] The graph is built at the end of checking, before the analyses that read it: its own `graph`
      phase in the perf timer, then `analysis` (Pounce: type check 25 ms, graph 11 ms, analysis
      31 ms)
- [x] The call graph is an index over Calls edges (`build_call_graph`): the checker's call
      recording is deleted (`record_*_edge`, `call_edges`, `effectful_callers`), and so is the
      graph's calls check, which compared the two. Proven first by building both and comparing
      nodes, edges, lines and effects on every fixture: the only difference was call-order lines
      for constructions. Now every call and construct site gives its line (a construction sorted
      last before), and a default argument's calls count in the caller that runs them (no line);
      no purity verdict changed on any fixture or Pounce, and the `mara ask` goldens are the same.
      Printing is the `print` operation, so a user fun named `print_…` no longer counts as one.
      The call graph, return deps and escape now run only on a clean check (no fixture's
      diagnostics changed)
- [x] All-paths-return from the runs (`graph_falls_off`): a fun falls off when a run its entry
      reaches ends in the synthetic return that closes its body. Compared with the CFG's verdict
      on every function of every fixture first: they agreed. Writing fixtures for more shapes
      found the CFG counted dead code after a `return` as falling off, so a non-void fun ending
      in dead code was a "missing return", and dead code anywhere else went on to invalid IR (a
      pre-existing crash: codegen wrote it after the terminator). Now a statement right after a
      `return`, `break` or `continue` is an error, "unreachable code" (the builder records the
      first of each stretch; definitions after a return are no code). Dead code after an `if` or
      `match` whose every branch returns compiles, as it did in a void fun; in a non-void fun it
      was a misleading "missing return" (`test/retshapes.mara`, `test/retmiss_shapes.mara`,
      `test/unreachable_neg.mara`). The CFGs are now built on demand, for `mara ask`'s control
      dependence only
- [ ] Control dependence from the runs, then `cfg.odin` goes (with slicing)
- [ ] Reaching definitions over the runs replace `usedef.odin`
- [ ] Must-use `err` onto the graph
- [ ] Slicing, lineage and `mara ask` read the graph
- [ ] The return-dependency summary from the graph
- [ ] Definite assignment onto the graph
- [ ] Escape onto the graph

## Baselines

Recorded at 3c9bbc5, before any change, with the debug compiler (`odin build . -debug`). Peak memory
is the `mara` process only (clang runs separately).

| Program | Lines | Peak memory | Total | Lex | Parse | Type check | Codegen | Clang |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Pounce | 3.3k + stdlib | 54 MB | 0.43 s | 12 ms | 9 ms | 68 ms | 38 ms | 300 ms |
| `test_1M` | 1.0M | 6.2 GB | 19.9 s | 1.8 s | 1.7 s | 10.8 s | 2.5 s | 3.1 s |

About 6 KB of compiler memory per source line; type checking is half the wall time.
