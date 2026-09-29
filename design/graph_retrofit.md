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

## Phase 3 checklist

On the `graph-codegen` branch. Codegen moves onto the graph one function at a time: `llvm.odin`
emits a function from the graph when it handles every operation in it, and the syntax-tree
emitter does the rest, until it does nothing and is deleted.

The new emitter lowers each operation cleanly, as the operations table in
`design/program_graph.md` says; it does not copy the old emitter's habits. The proof (decided
2026-09-28) is two checks, run on every step:

- **IR, modulo naming and harmless habits.** `test/irdiff.sh -n` also normalizes away what
  can't change behavior — an unreachable block, a store overwritten before anything reads it,
  and each further rule justified once where it is added. What differs after that is traced,
  as in phase 2.
- **Runtime differential.** Every fixture built by both emitters runs, and its output and exit
  code match (runtime errors included).

What the program does moves into the graph (a range loop's `lo <= hi` check, the order a write
evaluates its destination and value); how instructions are chosen stays in the emitter.

- [x] The harness: `llvm.odin`, the per-function switch in the worker loop (`MARA_GRAPH_CG=0`
      forces the old emitter), the normalizer's first rules (unreachable blocks, a store the
      next instruction overwrites), and the runtime differential, `test/irdiff.sh -r`: 169
      programs, output deterministic run to run
- [x] Scalars: locals, checked arithmetic and division, compares, casts, `if`, loops, `break`
      and `continue`, scalar calls and returns. The graph now says what the old emitter
      decided on its own: a constant carries its value (`consts`); a literal has the type its
      use takes (the checker leaves infer_int / infer_float); a narrower number widens by an
      implied cast right after it (operands, stores, arguments, returns); a range loop
      evaluates both bounds and checks `lo <= hi` before its counter's first write; its step is
      a wrapping add (it can't overflow); `-%x` keeps its `%`. Three old-emitter changes to the
      graph's shape, proved against `main` (`irdiff.sh -o`: IR changed only there, every
      program runs the same): a range check tests `lo <= hi` and branches to its ok block
      first; `and` / `or` store the left side once it is computed, not a constant before it;
      a scalar `if` expression goes through a slot like them (the phi stays for aggregates).
      Allocas come in the order code first needs them, as before; a synthetic scalar written
      once before every read (a range's end) is that value. Normalizer: string constants
      nothing references. Coverage: 4 of Pounce's 243 funs, 17 of `test.mara`'s 251, every one
      identical modulo naming; `mara ask` goldens and the Pounce corpus unchanged
- [x] Pointers and structs: address, deref, fields, struct params and locals, constructions,
      copies, results built in the caller's slot (sret, NRVO), constructors. An assignment
      now works out its target's place before its value, and a compound `t op= x` reads
      through that place — the old emitter's order (the value came first in the graph); only
      which runtime error fires first could tell. A struct is handled by its address: a read
      yields it, a write copies (`memcpy`), a param is the caller's. A construction zeroes its
      storage and runs the constructor on it; a constructor runs on zeroed storage, so it
      neither zeroes nor constructs its fields' zero again. A struct-returning call builds
      its result where the value goes when the old emitter's rule says that is safe (a
      declaration or temporary; this fun's own slot for a returned call; an existing place
      when no argument passes the callee storage), else in a temporary, copied in. The local
      every return returns is the result slot, and so is a temporary whose one read is a
      return. Found, by the graph emitter's one rule (a construction zeroes its storage, then
      runs the constructor): the old emitter ran constructors on storage it hadn't zeroed —
      the NRVO local (it lives in the caller's slot, so `a = half(1)` kept a's old fields),
      a returned `Vec()`, a constructor with params called into an existing value, and one
      built in a temporary (never zeroed: garbage) (`test/nrvo_zero.mara`,
      `test/ctor_zero.mara`). The old emitter now zeroes on every one, and no longer zeroes a
      new local whose value is a struct-returning call or construction (it writes all of
      it); an overloaded operator returning a struct is built where it goes, like the call
      it is. The graph had `#self` as a read of Self, typed as a
      pointer (the emitter loaded a pointer out of the struct's first field); it is Self's
      address, and reaching through it is Self. Normalizer: `inbounds`, unused
      getelementptrs and chains of them, a memset repeated or overwritten by a same-size
      memcpy, an alloca only ever stored into (the old constructor wrote a pointer field's
      null into a local of its own instead of the field). Still declined
      (later steps): a bare construction whose constructor has default arguments, the
      in-place update `x = f(x)`, `using` fields, structs holding partial arrays or a sized
      slice's backing
- [x] Arrays: a fixed array is handled by its address like a struct (params, locals, fields,
      results in the caller's slot, NRVO); a zero is a memset; a literal zeroes, then writes
      its elements; `{all x}` writes the one value into every element (nothing to zero); an
      array of structs runs each element's constructor on its zeroed storage; an index is a
      bounds check — none for a constant in range, none for a loop's own element — then its
      address; a one-letter swizzle is its element. The graph now says: an index widens to
      the header width by an implied cast; an array literal returned or passed is built at
      the type its use takes (it had the literal's own, `[2]infer_int`); a collection loop
      counts at the header width (its `i32` counter was compared with an `i64` length); a
      broadcast's value has the element's type, and is evaluated once (the old emitter
      evaluated the checker's clone of it per slot: `{all f()}` called f N times); a literal
      or construction assigned to storage that already holds a value is built whole in a
      temporary, then written — it may read what it replaces (`p = P{x = p.y}`, or through
      a param: `fill(&cs, cs[0].pos)`), which building in place zeroes first. The emitter
      builds such a temporary in place when nothing read from its first write on can be
      that storage: the old emitter's type-based rule (`storage_read_hits`), on graph
      places; `mara ask` still names the construction as what supplies the storage
      (`du_built_in_temp`). Language (decided 2026-09-28): the index of `for x, i in xs` is `i64`, like a
      length — it was `i32`, and the old emitter loaded it as an `i32` out of the `i64`
      counter's slot (`code/font.mara` held one in an `i32`). Old emitter, to the graph's
      shape: an array copy (`b := a`, `b = a`, a returned local) is one memcpy, not an
      element loop; a literal always zeroes first, a broadcast never; a new local given an
      array-returning call isn't zeroed first (every array-returning fun writes all of its
      result: a returned literal now zeroes the slot); a constructor's array field isn't
      zeroed again; an array-valued overloaded operator is built where it goes, like the
      call it is. Found: a loop over an array field had no bound (invalid IR;
      `test/array_field_loop.mara`), and a fallible constructor's Self slot was never
      zeroed (garbage in its bare fields; `test/fallible_ctor_zero.mara`). A bounds failure
      names the place as written (`o.cells`, `grid[i]`; the old emitter said `array` for
      anything but a bare name). Normalizer: a constant index's width, where a single-use
      getelementptr is computed, a chain folded even when its base has other uses, a
      memset overwritten by a memcpy after only address arithmetic, the order of the entry
      block's allocas, the bounds failure's name. `MARA_GRAPH_CG=log` also says where each
      declined fun stopped. Still declined: swizzles of several letters, constant tables, a
      broadcast of aggregates, arrays on the arena
- [x] Slices: a slice's header, `{len, cap, ptr}`, is an aggregate handled by its address
      (params, locals, fields, results); `.len` and `.cap` are its fields, and a write to
      `.len` checks `0 <= len <= cap`; an element is the header's pointer, the index checked
      against `cap` (one old path checked `len`; it now checks `cap` like the rest);
      `a[lo:hi]` of an array or a slice is a new header, `len = cap = hi - lo` (no bounds
      checks, as before). The graph now says: a fixed array where a slice is taken (an
      argument, a store, a field) is an implied `slice` of its place — of a temporary for a
      literal; a collection loop over a slice walks a view of it taken as the loop begins
      (the old emitter read the header once, the graph read the place each time), which the
      emitter holds as the header's values (no storage); a store widens its value to its
      place's type (for `a[i] = x` it took the whole array's, so a narrower `x` wasn't
      widened). An index is evaluated before the slice header it indexes is read, and a
      slice's bounds before its source's header: the old emitter read the header first (it
      now doesn't). A constructor's field declaration is fresh (the old emitter took it
      as existing storage). (The result slot was taken as fresh too — wrong: step 6.) Byte
      views — an address of bytes taken as a `^T`, another type's value written into bytes
      — are declined (below). Normalizer: a constant's width change, a store overwritten
      after address arithmetic, a getelementptr copied to each of its uses, the order of
      string constants
- [x] Partial arrays: `[..N]T` is an aggregate, a slice header over its own inline
      elements, so `len`, `cap`, indexing, slicing and loops are a slice's; its zero is its
      elements zeroed and its header stamped (`ptr` at them, `len` 0, `cap` N); a copy of
      anything holding one (the array itself, a struct, an array of either) re-points each
      at the copy's own elements; a constructor stamps its partial-array fields on entry;
      byte arrays are 16-aligned. The graph now says: a partial array (or a pointer to one)
      where a slice (or a pointer to one) is taken is an implied cast — its header is a
      slice's, no instruction; a collection loop over one walks a view, like a slice; and
      `Foo{0}` is a `zero`, not a construction (the language skips the constructor there:
      the graph ran it, so defaults would have applied). A struct's zero stamps the partial
      arrays in it. Old emitter, to the graph's shape: only a named result re-stamps the
      result slot's partial arrays on entry (every struct-returning fun did; anything else
      builds the result by a construction or a copy); a struct declaration no longer
      re-stamps its partial-array fields afterwards — that covered `{0}`, which now stamps
      them itself
- [x] Bytes and carves: a new place, `view` (decided 2026-09-28): bytes at an offset seen as
      a `T` — read (`x : T = bytes[off]`, and at an argument), written (every index write
      into a byte buffer, and `bytes[lo:hi] = v` for a non-array `v`, at `lo`) and addressed
      (`&bytes[off]` as a `^T`) — checked `off + size_of(T) <= cap`, `align 1` through it,
      `#big_endian` its flag (a struct read swaps as it's copied). The checker now stamps
      the viewed type on `&bytes[off]`, and for byte partial arrays too (they got a one-byte
      index check). `byte read` stays for fills: a partial array from bytes (a new one is
      zeroed first) and a value from a span. `take`: its storage is the header's place
      (`&s` is s, a `^[]byte` what it points at); positional `let(T, &bytes[i])` is the view
      there; a declared `let` local is the carved memory (never the result slot — the first
      try put it there, so its writes missed the storage). A sized slice `s : []T(n)`:
      zeroed storage (runtime-sized for a runtime n) and the header over it.
      `dst[lo:hi] = src` is a write through a slice that reads the slice's bounds, not its
      header: an open hi runs for src's length (as a value, `a[lo:]` runs to a's len).
      `slice_from_ptr(p, n)` is a header over p. Old emitter, to the graph's shape: offsets
      and bounds before the buffers they index (views, fills, span reads, element copies)
      and a take's count before its storage's header; every byte-view failure says "view"
      (it said read, write, view or let); a bare slice header zeroes with one memset; a new
      partial array filled from bytes is a zero value first. Normalizer: an alloca's order
      also for types naming other types. Still declined: positional `slice([:n]T,
      &bytes[i])`, a sized slice from bytes or from a string (the graph drops its count),
      a slice's elements into a partial array, big (arena) storage
- [x] Strings, `print`, `assert`, `crash`: a string constant is a global whose text the
      constants table holds — its value is its bytes' address; as a slice it is a header
      over them (`len` its length, `cap` one more: the terminating 0); into a partial array
      its bytes are copied (with the 0 when there's room) and `len` set. `print` is one
      operation over values already computed (decided 2026-09-28: every argument is
      evaluated before anything prints — a call that prints does so first); each prints by
      its type, spaced, or into the `%` places of a first operand that is text with them.
      `assert` branches to its failure, which names the source text and, for a comparison,
      each side's value: the graph records the sides' texts (`assert_sides`, "" for a side
      whose text states its value). `crash` prints where and its message, and exits; what
      follows is a dead block. `#caller_name` / `#caller_span` are text; `#windows` and the
      other target flags are bool constants. A constant table's global names its
      declaration (`refers`), whose value as written the graph keeps (`const_values`): the
      emitter builds the read-only table from it, as before. Old emitter, to the graph's
      shape: print evaluates every argument first (it interleaved evaluating and printing),
      and a text argument's address is taken as it's evaluated; the failure blocks of
      `assert` and `crash` and the raw printers (`print_int`, …) are shared with the new
      emitter. Printing opened most of `test.mara` to the graph (154 funs), which turned up:
      an index into text is a byte of it, bounded like its slice (the first try read a
      header out of the string's bytes); `[..N]T{}` assigned to a partial array is its zero
      value, elements zeroed too — the old emitter reset only a field's header (growing
      `len` again showed stale elements) and didn't compile it into a local
      (`test/pa_literal_zero.mara`); a span read's failures name the span read, not its
      statement (the graph had the statement's place); a fixed array of partial arrays —
      a local, a constructor's field — stamps every element's header (the graph emitter
      stamped only a bare one: cap 0; `test/pa_array_stamp.mara`); a literal reading only
      values held in registers (scalar params) is built where it goes. Found, a miscompile
      in both emitters: the result slot is no fresher than any place — the local every
      return returns lives there, so `x = f(x)` built f's result over the x f was still
      reading (`f(%sret, %sret)`; the old emitter did it for slices, since step 5a;
      `test/result_slot_alias.mara`). Old emitter, to the graph's shape: a collection
      loop's named index is a local like any other, sharing its name's slot; text or a
      slice written into a constructed value's partial-array field doesn't stamp its header
      again (every construction and zero already has); an aggregate `if` expression is a
      temporary each arm writes, like a scalar one (it picked the arm's address with a
      phi), and the new emitter keeps that temporary out of the result slot — only
      fixtures use one. Then constants: `size_of(T)` carries its value, by Mara's layout
      (`checker_type_byte_size`; a union's: step 7), and so does a named constant whose
      value converts a constant (`u32(0x68636143)`, `File_Id(0)`) when the type holds it
      exactly. Found, a miscompile in both emitters: the checker left a name of a constant
      declared in a struct's or fun's scope unresolved, and the emitters looked it up by
      bare name in the global constants table — a module constant of that name won
      (shadowing never worked), and so did another module's: Pounce's
      `Arena_Debug.alloc` reserved cache.mara's `HEADER_SIZE` (16 bytes) for its 32-byte
      header. The checker now resolves such a name to its own declaration's value; the
      graph emitter had given a fun body's constant an uninitialized slot, and now
      declines a var naming a constant (`test/scope_constants.mara`). Normalizer: a float constant's width change (`fptrunc double 0.5 to
      float`), like an integer's.
      Still declined: `-no assert` (the graph keeps an assert's condition, which
      the old emitter never evaluated), a crash message computed at runtime, `cstring(s)`
      (only ever a foreign call's argument: with those, step 9)
- [x] Unions and `match`: tags, variants, niche layouts. A union is an aggregate handled
      by its address; a `variant` place is the union's own address (each variant's
      struct, its tag first, overlays the union from its start; a niche union's Some
      variant is its storage outright), and a match arm's binding is that place, not a
      copy. A variant's construct zeroes the whole union — its bytes past the variant
      too, so a union's bytes are always its value's — then writes its tag (a niche
      union: None is null, Some the pointer its literal writes next). The graph now
      says: a variant literal's fields are written through its `variant` place (they
      were fields of the union, untyped), and a variant has no constructor, so its field
      defaults are implied writes at each construction (a constant one at its field's
      type: variant defaults aren't checked where declared); a union switch carries each
      arm's tag as an implied constant operand, the `else` arm being the target past
      them. Decided (2026-09-29): a match covers every variant, so a subject holding
      another tag is corrupt memory, and it fails: `__mara_match_fail` ("match on an
      invalid tag N" at the match), in both emitters (it skipped every arm). Unions keep
      the old emitter's ABI for now: params by address, results returned as an IR value
      (a slot like the other aggregates: decided at the switch-over). Old emitter, to the
      graph's shape: a value match tests every arm before any arm's body; a variant
      literal zeroes the whole union wherever it's built (only a temporary did); a
      niche Some writes its pointer through the variant's struct; reading a scalar param
      reads no storage (it built `m = Some{value = q}` in a temporary for q, a pointer).
      Normalizer: a memset of no more than the one just before it zeroed at the same
      address (the same `getelementptr` text is the same address), and the address
      arithmetic only it used. Also: a match is a union's by its subject's type (a dot
      arm, `.None`, binds no variant; an enum's dot arm gets its value as an implied
      constant, as a union arm gets its tag); a union's `.tag` reads as a match reads it (a niche
      union's: its pointer's nullness), `.pad` at the tag's end; an array indexed by an
      enum takes its value as a number, an implied cast; a constant's integer
      arithmetic folds (`KB :: 1 << 10`; normalizer: integer arithmetic of constants is
      its result). Pounce: 130 of 233 funs from the graph (`event_process`, the SDL
      event union, among them); what's left is arena storage (step 8), `err` values,
      foreign and multi-return calls (step 9)
- [x] Scope work: defers, the arena's mark, reset and big locals; `main` and the program's
      setup; `#expose`. A `run defer` emits the defer's block where the scope is left: a
      copy at each exit, as though written there, its labels fresh, its entry going on in
      the current block and its `return` falling through to what follows (a block whose
      entry is a loop's head: later). A scope holding a big value marks the arena on entry
      and resets it at each exit; a big local's storage is its `arena alloc`, bumped from
      the program's arena (no alloca). `main` is the program's setup — the program global,
      its arena, `args` — shared by both emitters (`emit_main_prologue`), then its body from
      the graph; falling off its end or a bare `return` is `ret i64 0`. `#expose`:
      `dllexport`, and the host's program (the first param) stored into `@__mara_program`
      first thing. Found: a branch's `then` edges came out of order when a target run had
      no operation yet (an `or`'s yes and no swapped) — an edge now takes its place when
      made and its target later, and one into a run that never gets an operation is
      dropped; the wrapping operators were plain `+ - *` in the graph (the parser keeps a
      flag): now `+% -% *%`; the deferred `:=` widths are settled on every node
      (`graph_settled`: the width a binding adopted, else i64 or f64), and the old
      emitter's arithmetic takes the settled width too; a call builds its result in a
      field or a constant index of a variable, computed ahead of its turn. Both emitters,
      to one rule: a struct's declarations are its fields, in Self, so its constructor
      never marks the arena (the old emitter marked it for a big field), nor does main's
      body (its scope ends with the program, which made the arena); `routes_to_arena` is
      the one test for a big local (the old emitter's structs went at `> 1024`, and a big
      partial array was bumped and never reset); a variant's construct stamps its partial
      arrays' headers (cap 0 before); a failure names the place as written (`grid[i]`,
      `o.cells`; the old emitter said `array`: a message change). `&` of a field or element
      of a ternary or a literal, or of a slice expression, is a checker error (it was the
      old emitter's). Old emitter bugs: a union declared bare was left uninitialized (now
      zeroed), `= void` on one copied from a null pointer (a crash), and a constructor's
      union field was rebound to a fresh local (`test/union_decl.mara`); a collection
      loop's copy of a byte partial array is aligned like every other; an aggregate `if`
      arm is built in the temporary, not copied. `test/dll_smoke` had rotted (`^Context`,
      renamed `^Program`, and nothing built it): a `.shared` marker builds a fixture
      directory as a DLL in `run.sh` and `irdiff.sh`. Normalizer: a load nothing uses; a
      slot stored once, with a constant, before each of its loads (its block dominates
      theirs) is that constant — the new emitter holds such a value, e.g. a loop's index
      when a `break` ends every pass; a store the next overwrites is found by address text,
      computed up front. Still declined: `= void` on an aggregate, a big temporary (a
      call's result on the arena), a defer block entered at a loop's head. Found after,
      memory-safety holes in both emitters' byte bounds, now one rule
      (`emit_byte_span_outside`: n elements of a size at offset off lie within cap when
      off <= cap and n <= (cap - off) / size, unsigned — a negative offset or count is
      outside, and nothing multiplies or adds before the check): a partial array filled
      from bytes never checked its source (a `[..4096]u16` from a 16-byte buffer copied
      8 KB past it; `test/byte_fill_bounds.mara`); a typed byte view took `off + size >
      cap`, which let `bytes[-1]` read and write the 4 bytes before the buffer
      (`test/byte_view_negative.mara`); a carve took `cursor + n * size > cap`, signed, so
      a negative n moved the cursor back under a live carve and a huge one's product
      wrapped small (`test/byte_carve_count.mara`; its message now says what was asked).
      And the big-variable decline didn't skip nested funs (Pounce's TTF declined for
      `loca_correct_format`'s big local)
- [x] Calls: foreign ABI, function values, default and tuple-default arguments, multi-return,
      `?`, fallible constructors. Done so far — several results, `err`, `?` and fallible
      constructors: a fun with several results takes a slot for each (`%sret.<i>`) and a
      return writes them; a call gives each result a temporary its uses read (a register
      value loaded in the call's run is kept, since that run dominates every use), an
      aggregate a declaration takes written straight into its storage; a fallible
      constructor builds Self in `%sret.0`, its err in the slots after. `err` is a register
      value (i32, set << 16 | tag); an error set's constant is one. The graph now gives a
      return an operand for each result: an omitted trailing err is an implied `Ok` (also
      when code falls off the end of err-only results), and `?`'s return is each other
      result's zero, then the err — the one-operand return was read as `?`'s, so `return 7`
      in a `-> i64, err` fun typed the 7 as the err and linked its flow to the err result
      (graph, flow edges and escape). `?` branches on an implied `bool(err)`. Decided
      (2026-09-29): a defer that changes a local a return returns is an error
      (`flow_check_defer_writes`) — the emitters disagreed on whether the caller saw the
      change — so a return may take its values, run its defers, then write its slots, the
      graph's order, which the old emitter now follows (it stored as it evaluated). Found:
      `bool(e)` truncated to one bit — an error of an even tag, `bool(Probe.Second)`, read
      false, in both emitters (`test/err_bool.mara`); a struct literal spreading a call,
      `Mesh_Data{primitive_quad()}`, wrote only the call's first result, into the first
      field — Pounce's meshes would have lost their indices (`test/spread_literal.mara`); a
      union returned by value is re-anchored where it's stored (its partial arrays pointed
      into the callee's frame). Old emitter, to the graph's shape: the one copy primitive
      for a struct result (it copied field by field); a fresh declaration claims a call's
      result slot, a struct too, and `_` binds nothing (it was a variable named `_`); an
      expression target's place before the value read into it; `?` inside a fallible
      constructor leaves Self alone, as its returns do; a string-array literal stamps all its
      elements' headers after the zero, then writes each (it stamped and zeroed each again),
      and one built in place isn't re-anchored; a struct declared as a copy of a place isn't
      zeroed first; a fixed array stored as a slice (the array, or `a[:]`) has its header
      written at the destination, no temporary; a byte partial array's result temporary is
      aligned like every other. Normalizer: nothing new. Then the functional update: a fun
      that consumes a param (`r := pk` first, r returned) skips that opening copy when its
      caller passes pk's storage as the result slot, and `x = f(x, …)` does so when x is
      the consumed argument (spelled the same) and nothing else f is handed can reach x
      (`llvm_updates_in_place`, the old emitter's rule); otherwise a temporary. An
      operator's operands go to its `overload` at the param types, as a call's arguments
      do (the graph passed `&s` in `&s + c` as a `^[..N]utf8` where `^[]utf8` is taken).
      Found: text is only its bytes, whatever its type says — returned from a `-> str64`
      fun, both emitters copied a whole partial array's worth from it (reading past it;
      the result held its neighbours), and handed to a `str64` param the graph's emitter
      passed the bytes' address as the partial array: now a returned text is built into
      the slot (zeroed, then the text, as a declaration), a text argument gets a header
      over its bytes, as the old emitter's (`test/text_partial_array.mara`). Old emitter,
      to the graph's shape: a fresh slot given a whole partial array from a place copies it
      (it stamped and zeroed the slot first). Then foreign calls and intrinsics: an
      intrinsic (a fun whose body names `@llvm.*`) is that call, its arguments at the param
      types (a fixed array loaded, by value); a foreign function follows the platform's C
      ABI (abi.odin's classification, shared with the old emitter): a register value as
      itself (text for a cstring its bytes' address), an aggregate in registers loaded in
      8-byte parts, a bigger one `byval`, the result returned (an aggregate one put back
      together in a temporary) or in a hidden `sret` slot. Found: a literal whose type is
      its use's — the width a `:=` adopts — was never range-checked: font.mara's
      `first_on_curve := -1`, a "none" sentinel, adopted a u16 index's width and was 65535
      (the graph's emitter, following the type, never took the no-on-curve path; the old
      emitter compared it signed by accident). The graph records each literal it settles
      (`settled`) and flow checks it fits (`flow_check_literal_ranges`, the checker's
      `check_value_range`; `test/settled_literal_range_neg.mara`); font.mara's sentinel is
      `n_points`. The old emitter widened an index by a `:=` variable's unsettled type:
      signed, where the settled u16 is not (from 32768 on). Then function values: a
      function-typed value is a register value (a pointer); a function named as a value is
      its symbol; a call through a value is the direct call's lowering by the value's type,
      calling the pointer. And the update in place reuses the destination's place: a
      write's place is computed before its value, so the consumed argument's place — the
      same operations — takes its values rather than being computed again (one bounds
      check, one pointer load, as the old emitter; a pointer's field `ph.f` included). Last,
      named results, where the old emitter kept them — with several results a struct or
      fixed array in its caller slot, a register value a local zeroed at entry; a single
      struct result the result slot, its partial arrays stamped at entry — and arguments:
      bytes where a fixed array is taken (`read_u16be(bytes[0])`, a `[2]byte`) are that
      many bytes seen as the array, copied into a temporary (the graph passed one byte); a
      C pointer param takes any pointer (`const void *data` is `^byte`); a call through a
      function value types its arguments by the value's signature; a tuple default whose
      source is one value is a broadcast, each slot the value again (the graph took output
      1 of a constant). Pounce: 210 of 238 funs from the graph. What's left isn't calls —
      `= void` on an aggregate, some broadcast fills, writes, casts and views, a big
      temporary on the arena: the switch-over's
- [x] Switch over: every function from the graph; the syntax-tree emitter deleted
      Declines first, down to none. `void`: a pointer null, a declared scalar zero, a
      reassigned one keeps its bytes, a declared partial array its header; an untyped
      `void` takes its use's pointer type. `cstring(s)`: text is its bytes, a slice or
      partial array checked to hold its terminating 0. A broadcast `{all x}` fills a fixed
      array, or a partial array's cap. Destructuring a fallible construction takes its err
      from the construction (the graph read output 1 of the built value). A construction
      overridden in an annotated declaration (`c : P = P(){ x = 7 }`) has its fields
      typed (the checker typed the override block on the unannotated path only). Text
      into a fixed utf8 array: zeroed, then its bytes (`emit_text_into_array`, shared).
      Match bindings are their scrutinee's payload when a literal asks whether it may be
      built in place: `s = Two{a = one.m}` in `s`'s arm `One one` zeroed s before reading
      one.m (`test/literal_self_reference.mara` caught it). Found, construction without
      arguments: `P{}` is `P(){}`, but a literal skipped the constructor's arguments —
      a param with a default wasn't passed it, one without wasn't an error, a fallible
      constructor's err slot wasn't passed at all (each ran on whatever the registers
      held; a crash). Now a literal needs what a call would: every param defaulted
      (`TYPE_EXPECTS_ARGS`, got 0) and a constructor that can't fail
      (`TYPE_LITERAL_CAN_FAIL`); a bare declaration or field of a fallible one is an error
      too (`TYPE_BARE_CAN_FAIL`), and the defaults are passed (`graph_default_args`). An
      array's elements that can't be built bare stay zero, as the checker's warning says
      (both emitters called the constructor with zeroed arguments); a `~T` slot's field
      the shape shortcut fills. The checker reports one error once per place, and the
      bare-declaration errors point at the declaration (they gave the enclosing scope's
      line). Text copied into a fixed array stops at its length (its terminating zero
      landed a byte past an array it filled). Old emitter, to the graph's shape: a fresh
      `t := f()?` claims the call's result slot (a construction's is its temporary,
      copied in without zeroing t first); a fallible construction destructured into an
      existing struct is built in it when its callee is handed none of the caller's
      storage, as a single-result one is. Then: a distinct struct is its base's; the
      in-place override `p{ x = 10 }` is typed as p (and not checked as a construction);
      `this_program` is where `@__mara_program` points, reached through a pointer. A named
      constant computed from floats (`TWO_PI :: PI * 2`) is folded at the precision of
      the type it's used at; one the graph can't fold is its expression's operations
      where it's used, as the old emitter's (normalizer: float arithmetic of two
      constants is its result, like integer arithmetic). `size_of` of a union is by its
      variants'. A slot no use types (an if-expression of bare literals) takes the
      default width; an aggregate if-expression's slot is its place (`(if c do a else
      b).x` reads the slot, no copy). Swizzles of several components: read, gathered
      into a temporary; written, scattered element by element — never a place to build
      a value in (the graph's emitter built a literal "in place" at `v.yz`: the wrong
      elements). Found: the old emitter wrote an array literal into components one by
      one, reading what it had just written (`v.xy = [v.y, v.x]` gave two copies of
      v.y); now built whole first, as the graph does. Old emitter, to the graph's
      shape: a struct declared from an if-expression isn't zeroed first. Then the last
      declines: slice bounds at the header width (`buf[a:b]`, u32 each); a distinct
      conversion of an aggregate is its bytes where they are; a union's variant struct
      built as a struct of its own (zero, tag, defaults); a struct with no init function
      only zeroed (a generic instance a shape shortcut fills); Program's constructor is
      the compiler's — main sets its storage up — so its fields build no code; falling
      off the end of a shape's bodiless method returns its slot as is, or a register's
      zero; a slice's `.ptr` is a header field; a C function as a value is its link
      symbol; a struct result's temporary is on the stack (as the old emitter's); a big
      literal built in place needs no arena temporary; a `let` over bytes holding
      partial arrays is the memory, and a copy out of a view is raw bytes (its headers
      come with them, and what fills them next restamps them); a number from a byte
      span is the bytes at its start, a struct or array field from one a sized read; a
      positional `slice([:n]T, &bytes[i])` checks and takes n at the offset; a pointer
      converts to a number (and `bool` of one is its not being null); a declared local
      struct `= void` is zero, a constructor's field left as Self's zero. Found: the
      checker never typed a C-style loop's step (`k += 1`: it went unchecked), and a
      field's declaration had no statement kind (not fresh for a call's result). Found
      in the graph's emitter: a big `let`-bound local was given arena storage and read
      from there, not from the bytes (`test/let_big_view.mara`; Pounce's game memory).
      Old emitter, to the graph's shape: a struct or array field read from a byte span
      is a sized read, as a declaration's (it read the field's size at lo, whatever
      hi was). Every function of the fixtures and Pounce now comes from the graph:
      Pounce's IR is the old emitter's, modulo naming, in every unit. Then the switch:
      the graph's emitter is the only one — what it can't lower is a codegen error at
      the operation it stopped at, `MARA_GRAPH_CG` is gone (design/all.mara's single
      named scalar result, `-> named : i64`, was the last function to lower). The
      syntax-tree emitter is deleted: everything in codegen*.odin nothing outside it
      reaches, about 11,200 lines (codegen*.odin: 17.3k lines → 6.1k; what's left is
      the module's types, constants, runtime helpers, main's setup and the emission
      helpers the graph's emitter calls). Two last reaches into the syntax tree cut: an
      array element's constructor defaults are constants (folded, as the graph folds
      them; another is an error), and the program arena's size is a constant folded at
      compile time (`Arena_Debug(16 * MB)`: it multiplied at run time, overflow-checked;
      the checker now checks the arena's arguments, whose names never resolved).
      Gate: IR byte-identical to the switch's (b5c6e17) in every program but the seven
      whose arena size is an expression (only @main's arena setup differs); runs
      identical (187); suite 187 pass; ask goldens and the corpus match; test_1M builds
      and runs the same. `test/irdiff.sh` compares two compilers only (its emitter modes
      are gone).

## Phase 4 checklist

The checker builds the graph as it checks, so nothing re-reads the syntax tree for what the
checker found. Today it can't: one body is checked in two passes (declarations and
reassignments, then control flow, calls, returns and stores through places), work happens out of
order (a module on `use`, a generic instance at its first call, another struct's signature on
demand), and some nodes are checked twice (a default argument at every call, an annotated
literal as a value and again as what the declaration holds). Operations must come in the order
they run, once each. So the checker's walk changes first, while the graph stays byte-for-byte the
same; then the building moves into it.

The proof, each step: the graph is the same — `MARA_GRAPH=full` dumps every column, edge, run and
table, and the corpus's dumps match the baseline's (`test/graphdiff.sh`) — and so is the IR
(`test/irdiff.sh -r`); the suite, the ask goldens and the corpus. Where a step changes what an
erroneous program reports, the negative fixtures say so.

- [x] Tooling: `MARA_GRAPH=full`; `test/graphdiff.sh` (the corpus's full dumps, baseline against
      working)
- [ ] Each node checked once: a default argument in its callee's scope, once (every call takes the
      result); an annotated literal once; a struct's `::` constants once; a `Module.X` default once
- [x] One ordered walk per body: a function's or struct's code, and every block, checked
      statement by statement in the order it runs (the two passes merged); a local visible from
      its declaration on
      A body's definitions are still hoisted — registered and checked before its code, so code
      can name one written after it; a block's (an if's, a loop's, an arm's) are split off the
      same way. Then each statement goes through both passes before the next. Found: a local used
      before its declaration passed the checker (the declarations pass had bound it) and failed
      in the graph (`'x' names no declaration`); it is `undefined identifier 'x'` now
      (`test/use_before_decl_neg.mara`). Graph identical in all 274 programs (diagnostics come
      in the walk's order: graphdiff sorts them, as irdiff does), IR byte-identical, runs
      identical (187), suite, ask goldens and the corpus.
- [ ] Segments: one fun's or struct's graph built on its own and placed afterwards in the
      canonical order (the checker finishes bodies out of order); the checker builds each body's
      graph when it finishes checking it
- [ ] Fusion: the walk builds operations as it checks — an expression gives its operand beside
      its type, a store builds into its destination — construct by construct, the builder's case
      deleted as each moves; a body the checker can't build yet is built by the builder, from the
      annotations, as phase 3 did per function
- [ ] The builder deleted: module-level declarations and constants from the checker too
- [ ] The last readers of annotations: `void` into a pointer checked where the store is checked;
      the returned local and the consumed param as graph queries; constant tables from values the
      checker evaluated; hit testing from origins
- [ ] Annotations, `lowered_*`, their accessors and `ast_shape.odin` deleted

## Baselines

Recorded at 3c9bbc5, before any change, with the debug compiler (`odin build . -debug`). Peak memory
is the `mara` process only (clang runs separately).

| Program | Lines | Peak memory | Total | Lex | Parse | Type check | Codegen | Clang |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Pounce | 3.3k + stdlib | 54 MB | 0.43 s | 12 ms | 9 ms | 68 ms | 38 ms | 300 ms |
| `test_1M` | 1.0M | 6.2 GB | 19.9 s | 1.8 s | 1.7 s | 10.8 s | 2.5 s | 3.1 s |

About 6 KB of compiler memory per source line; type checking is half the wall time.
