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
- [ ] Found: nested broadcast `g : [2][3]i64 = {all {all x}}` fails to type-check (the inner
      literal is checked against the outer's types)
- [ ] Found: a fn-type parameter followed by another parameter doesn't parse — in
      `fun(op: fun(i64) -> i64, x: i64)` the return list swallows `, x`

Later, not phase 0: `mara ask` refuses to run with any type error anywhere (partial results are a
phase 2–4 concern).

## Baselines

Recorded at 3c9bbc5, before any change, with the debug compiler (`odin build . -debug`). Peak memory
is the `mara` process only (clang runs separately).

| Program | Lines | Peak memory | Total | Lex | Parse | Type check | Codegen | Clang |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Pounce | 3.3k + stdlib | 54 MB | 0.43 s | 12 ms | 9 ms | 68 ms | 38 ms | 300 ms |
| `test_1M` | 1.0M | 6.2 GB | 19.9 s | 1.8 s | 1.7 s | 10.8 s | 2.5 s | 3.1 s |

About 6 KB of compiler memory per source line; type checking is half the wall time.
