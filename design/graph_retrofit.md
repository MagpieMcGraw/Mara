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
- [x] Slicing, lineage and `mara ask` read the graph: `defuse.odin` replaces `usedef.odin` and
      `cfg.odin`. Every operation records the statement it was lowered from (the `stmts` table
      and `stmt` column: its span and kind), so a definition is one statement's writes to one
      variable, of its statement's kind. Reaching definitions are dataflow over the runs to a
      fixpoint (the old walk patched loops by letting every def in a loop reach every use in
      it); a defer's block sees the state at each exit. Control dependence is post-dominance
      over the runs. Synthetic locals are seen through; a synthetic local set to a slice of a
      variable is a view, and writing through it writes the variable. The refers-to check
      against `usedef.odin` is gone (`MARA_GRAPH_CHECK`); every var operation naming a
      declaration is still checked in debug builds.

      Proven by a differential: every Pounce function's flow views and every variable's flow,
      call and type views (7,824 queries), and the same with `control` over the ask fixtures,
      `test.mara` and `design/all` (~4,000), old compiler against new, each difference traced.
      `askflow` (the interprocedural hops) is identical. The changes, all deliberate:
      operator calls are calls (landings, supplying calls, call sites: `v2_add flow` said "no
      call sites" while its callers listed `sum`); a variable's type is its declared type
      (`d: f32 = 0.99` was f64, a bare `x : T` had none, a match binding was its union); a
      cast, `len` or `slice_from_ptr` is no call (they counted as "calls not followed"); loops
      are precise (a def from a previous iteration no longer reaches past a redeclaration or a
      write on every path); calls under `?`, inside `assert` and in default arguments are seen;
      field destructures (`a.x, a.y = f()`), field broadcasts and in-place overrides
      (`p{ x = 1 }`) are writes; a loop's guard branches on its variable; code after an
      always-returning body is dead. A bare declaration's implicit construction and a braces
      literal are no supplying call, as before. test_1M: graph 2.57 → 2.68 s, peak memory 4.39 →
      4.46 GB (the statement column); the post-check analyses take 4.7 s there, as long as type
      checking
- [x] Must-use `err` onto the graph: one pass over the whole graph. An err local declared by a
      statement is read where a var operation names it, except where a whole write lands
      (`e = f()`); refers-to has resolved shadowing, so the old per-block scope stack is gone.
      Diagnostics identical to the old walk on every shape tried, spans included
      (`test/erruse_shapes_neg.mara`: destructured, declared, typed, written again, a sibling
      block, a loop body, and a read only in a defer)
- [x] The return-dependency summary from the graph (`du_return_deps`): a backward slice from a
      fun's returns and named results, keeping the params it reaches, and following the
      branches that decide the result (control dependence) as well as its data; the call graph
      still folds it bottom-up. The checker's ~370-line AST walk is gone, and so is the summary
      from the compile path: only `mara ask` reads it, so it is built the first time a slice
      crosses a call. `MARA_DUMP_RETURN_DEPS=1` prints it. Differences from the old walk, each
      traced: a data struct's construction is computed from its arguments (the old rule looked
      the struct up by name and found none, so every set was empty); writes into a param's
      memory count (`verts[v] = vert` puts `scratch`'s bytes in the result); `?`, match
      bindings and named results are seen; and a result decided by branches depends on what
      they test: `starts_with`, `find_byte`, a call's `err` read `[]` before. Data alone lost
      `find`'s haystack (the old walk kept it by counting a loop's bound as its variable's data),
      which is what settled it. Goldens unchanged; the ask corpus changed in 111 Pounce and 47
      fixture queries, all through these summaries (`pack_rect`'s slot now traces to the
      glyph's size). test_1M: the analysis phase 4.8 → 3.5 s
- [x] Definite assignment onto the graph: forward dataflow over each fun's runs of what may be
      unset (locals that are pointers, slices or `void` scalars, and a struct local's pointer and
      slice fields), unioned at joins; out-parameters (`init(&h)`) set what they are handed; an
      alias is a pointer every write of which is `&x`. Two graph changes it needed: a `void`
      store is a write of the `void` constant (it wrote nothing, so neither this check nor
      def-use could see `x : T = void`; def-use's special case for it is gone), and a sized
      slice's `zero` takes its capacity (`s : []T(n)` looked exactly like an unset `s : []T`,
      and codegen will need it). The nine fixtures report identically. Differences, all
      deliberate: a defer's reads see the state at exit, not at the `defer` (a pointer set
      after the `defer` was a false error); a field written through an alias is set (another
      false error); a value unset on a loop's back edge is caught (`p = void` at the end of a
      body, read at its start); and a struct built from braces has only the fields it is given
      even when its type is inferred (`n := Node{val = 1}` then `n.next`) — the old walk
      tracked fields only for annotated declarations (`test/init_shapes.mara`)
- [x] Escape onto the graph: `escape.odin` walks each fun's (and struct's) code as runs. An
      operation's roots come from its operands' — a place's are the storage it names, a read's
      what that storage holds, an address's the place — and what each variable holds is
      dataflow over the runs: a whole write replaces it, a partial one adds, joins union, loops
      iterate to their fixpoint, and a defer's block starts from every exit that runs it and
      joins back in there. A variable's depth is the blocks between it and its fun, so a for
      loop's body became a block of its own (its locals live one iteration, the loop's
      variables all of them). Summaries as before, bottom-up; a fun outside recursion reports in
      its one walk. The syntax-tree bridges escape needed are gone (`stmt_to_node`,
      `lookup_callee_scope`, `struct_lit_field_type`). Two changes under it: `dst[lo:hi] = src`
      is a write into the slice operation (the elements it views) instead of into a synthetic
      local holding the slice, so def-use's view special case is gone too; and assignment
      targets carry their types (field, element, pointee, swizzle, slice). Untyped, the graph's
      places hid a local array decaying into `h.s = arr`, and made a byte copy look like it
      could store pointers (`utf8_add`, `init` in Pounce). Diagnostics are identical on every
      fixture, the 17 escape negatives included, but for two deliberate changes: a pointer set
      to a local inside a branch and set back before the return is no longer an error (the old
      walk joined every write made in a nested block); and a runtime-sized slice (`s : [:n]T`)
      views storage that dies with it, so returning it is now an error — it was a
      use-after-free both walks missed: the next call reused the storage
      (`test/esc_sized_slice_neg.mara`). New fixtures for what the graph
      handles itself: defers, `let` views, match bindings, slice copies, decay into fields and
      elements, recursion (`test/esc_*_neg.mara`, `test/esc_flow_ok.mara`). Escape's
      diagnostics are sorted by position, and flow's no longer follow a map's order (they
      changed from run to run). `MARA_DUMP_ESC=1` prints the summaries. test_1M: the analysis
      phase 5.7 → 5.0 s (escape 1.7 s of it), peak memory unchanged; Pounce's `mara ask`
      corpus (7,824 queries) is identical

Phase 2 is complete: every analysis reads the program graph (flow's `void` checks, which were
never on the plan, still walk the syntax tree).

Left for phase 3, found here: the graph lowers `x := let(T, s)` as a write of a carve into `x`,
while `x` has no storage of its own (escape treats it as a view); and codegen gave a
runtime-sized slice no storage when it was the local a fun builds in its caller's return slot
(its `cap()` read 0) — returning such a slice is now an escape error, so no program reaches it.

## Baselines

Recorded at 3c9bbc5, before any change, with the debug compiler (`odin build . -debug`). Peak memory
is the `mara` process only (clang runs separately).

| Program | Lines | Peak memory | Total | Lex | Parse | Type check | Codegen | Clang |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Pounce | 3.3k + stdlib | 54 MB | 0.43 s | 12 ms | 9 ms | 68 ms | 38 ms | 300 ms |
| `test_1M` | 1.0M | 6.2 GB | 19.9 s | 1.8 s | 1.7 s | 10.8 s | 2.5 s | 3.1 s |

About 6 KB of compiler memory per source line; type checking is half the wall time.
