# `mara ask` — static data-flow & dependency queries

**Status:** design only. Not scheduled, not started. Captured while the idea was fresh
(grew out of hand-slicing `draw_state_render`'s inputs in Pounce).

A small query command over a checked program: "what feeds this function?", "what
contributes to this value?", "what depends on this struct?". The motivating session
traced everything that flows into `gfx.draw_state_render` by hand and it fell out
cleanly — including two **dangling reads** (`DrawState.texture` and
`batch.instance_count` are consumed and asserted but never produced). The point of
this doc is that the analysis is cheap to build *here specifically*, because the
language already guarantees the property that makes it hard everywhere else.

---

## 1. Why this is tractable in Mara (and not in C)

The whole feature rests on one invariant: **a function's read/write footprint is a
subset of what's reachable from its parameters.** No mutable globals means the only
roots into memory are (a) params and (b) locals the function allocates — and locals
can't escape (returning a local-backed slice/pointer is already a hard error). So:

- The **call graph *is* the dataflow graph.** Data only moves between functions as
  explicit arguments and returns. There is no off-graph channel (a global) that a
  value could arrive through.
- "This field has no producer" is a **decidable, local fact.** If nothing in the
  reachable call tree writes it, it is its zero-init — full stop. That is exactly why
  the two dangling edges in `draw_state_render` are *visible as missing edges* rather
  than hidden behind a may-alias fixpoint.

The compiler already encodes this invariant:
- `Type_Env.scope_depth` — module scope is depth 0; the escape check is
  `depth >= env.scope_depth`. Module-level bindings outlive everything.
- `Binding.provenance` — defaults to `PROV_GLOBAL` (immutable root), distinct from
  param/local provenance. Top-level names are constants, never producers.

So the queries below are graph reachability over edges the checker can already see —
not interprocedural points-to.

---

## 2. We have already built 80% of this

The checker contains a **backward interprocedural slice** today: escape analysis.
Look at `eval_expr_arg_set` (type_checker.odin, ~4808):

```odin
// Given an expr, returns the set of fn_scope parameter indices whose data flows into it.
eval_expr_arg_set :: proc(c, e, fn_scope, tracking) -> [dynamic]int {
    Expr_Ident          -> param index if it names a param, else the tracking map
    Expr_Take / Slice   -> recurse into the storage/source expr
    Expr_Struct_Literal -> union over ref-carrying fields (deep)
    Expr_Call           -> lookup_callee_scope(call); for each index in
                           fun_return_arg_set(callee), recurse into call.args[ci]
}
```

That `Expr_Call` case is the crux: it resolves the callee
(`lookup_callee_scope`, ~4919 — mirrors dispatch order: resolved name → source name →
`resolved_func` name → stripped monomorph suffix), asks which of the callee's args
flow to its return (`fun_return_arg_set`, cached on the `SymbolTable`, cycles return
`-1`), and **recurses through the matching argument expressions**. That is a
return→arg backward walk across the call graph. `mara ask` generalizes the same walk
to more questions and finer granularity.

Reusable parts already in place:

| Need | Existing handle |
| --- | --- |
| Post-check IR to query (no re-walk) | `Checked_Program` — `functions: map[string]Checked_Scope`, `function_order`, `constant_values`, `table` |
| Name → function AST | `SymbolTable.fun_asts` (`map[string]^Stmt_Scope`) |
| Call → callee resolution (incl. dispatch/UFCS) | `lookup_callee_scope`, `Expr_Call.resolved_func: Maybe(Resolved_Func)`, `find_dispatch` / `dispatch_groups` |
| Operator → function resolution | `Expr_Binary.overload_fn` / `Expr_Unary.overload_fn` (`Maybe(Resolved_Func)`) — already resolved on the node |
| Return → arg dataflow | `fun_return_arg_set` (+ `arg_set_freeze`) |
| Params / fields / returns of a fn | `Stmt_Scope.typed_params`, `.fields`, `.return_types`; `Checked_Scope.params` |
| Field/index/deref write sites | `Stmt_Assign.target` (complex LHS) + `Expr_Field_Access` / `Expr_Index` |
| Intra-proc points-to | `Type_Env.aliases` (`it = &root` → `aliases[it]="root"`) |
| Foreign / intrinsic leaves | `Checked_Scope.origin` (`Source` / `Foreign` / `Intrinsic`) |
| Source locations (for the LSP) | `Span` on every AST node |
| "Is this name ever read?" | `Binding.read` (already tracked for must-use-err / unused-locals) |

---

## 3. One engine, two front-ends

**Design rule: the analysis is a pure function over `Checked_Program`, returning a
result graph. The CLI prints it; the eventual LSP serializes it. No analysis logic in
the printer.** This is the same separation the codebase already keeps ("codegen does
no analysis").

```odin
Ask_Node_Kind :: enum { Function, Field, Param, Const, File, Foreign, Opaque }

Ask_Node :: struct {
    kind:  Ask_Node_Kind,
    label: string,        // "draw_state_create", "DrawState.texture", "instanced_text.glsl"
    span:  Span,          // for LSP jump-to / inline; zero for synthesized leaves
    flags: bit_set[Ask_Flag],   // .Dangling (read, never produced), .Opaque (indirect call), ...
}

Ask_Edge :: struct { from, to: int, kind: enum { Produces, Consumes, Calls, Returns } }

Ask_Result :: struct { nodes: [dynamic]Ask_Node, edges: [dynamic]Ask_Edge, root: int }

run_ask :: proc(checked: ^Checked_Program, q: Ask_Query) -> Ask_Result { ... }
```

Renderers over `Ask_Result`: text tree (default), `--dot` (Graphviz; this is the
graph the user wants to *see*), `--json` (tooling + LSP transport).

---

## 4. Query surface

```
mara ask <fn> inputs                 # producer/consumer set of fn's reachable input surface
mara ask <fn>.<param> contributors   # backward slice toward sources (generalized escape walk)
mara ask <Type> deps                 # struct dependency graph
mara ask <Type>.<field> writers      # every site that assigns this field, program-wide
mara ask <var> in <fn> assignments    # every assignment to a specific local
```

Flags: `--dot`, `--json`, `--depth N` (cap transitive walk), `--module <m>` (scope the
search). All read-only; all stop after type-checking (see §6).

`inputs` is the headline. `<fn> deps` for structs is nearly free (read
`SymbolTable.structs`, edges = field types). `contributors` is literally
`eval_expr_arg_set` lifted out of escape analysis and run to a printed result.

---

## 5. Algorithm — `inputs` (the draw_state_render case)

1. **Resolve** the target in `checked.functions`; get its `ast: ^Stmt_Scope` and
   `typed_params`.
2. **Seed** the consumed set: walk the body for `Expr_Field_Access` / `Expr_Index`
   rooted at a param (or a local aliased to one — track `vao_info := state.vao_state`
   via the same idea as `Type_Env.aliases`). These are the fields the function *reads*.
   For `draw_state_render(state)` that yields `state.shader`, `.texture`,
   `.command_buffer`, `.vao_state`(→ `vao`, `meshes`, `mesh_count`), `batch.instances`,
   `batch.instance_count`, etc.
3. **Find producers.** Collect the function's call sites (scan `function_order` bodies
   for `Expr_Call` resolving to it via `lookup_callee_scope`). Each call gives the real
   argument (`&game.draw_state_text`). From the aggregate's construction + every
   function handed `&agg`, gather field-writes (`Stmt_Assign.target` = field access on
   the aggregate) and the calls that perform them. Recurse through those producers'
   inputs (shader ← `draw_state_create` ← `make_program` ← file; instances ←
   `append_one` ← playa + camera; …). Edges via `lookup_callee_scope`; return flow via
   `fun_return_arg_set`.
4. **Classify leaves:** `read_entire_file` arg → `File` node; module-level `::` →
   `Const` (look up `constant_values`); `origin == .Foreign` → `Foreign`; a root param
   with no further producer → `Param`.
5. **Dangling = read set ∖ written set.** Fields consumed (step 2) with no producer
   (step 3) get `.Dangling`. This is the check that surfaces `texture` (atlas built in
   `asset.init`, never assigned to the draw state) and `instance_count` (`append_one`
   bumps `instances.len`, never `instance_count`).
6. **Over-approximation markers** (honesty, not silent drops):
   - `lookup_callee_scope` returns nil → indirect / fn-typed-param call → emit an
     `Opaque` node. Nominal `fn <name>` types narrow the candidate set; a later pass can
     resolve an opaque node to "all functions of that nominal fn type."
   - Call resolves to a dispatch group → fan to all candidates (`find_dispatch`).
7. **Termination:** visited-set keyed on `(function, direction)`. `fun_return_arg_set`
   already caches and breaks cycles (`-1`); the field walk needs its own visited set.

`contributors` is the same walk seeded from a single value instead of a whole param
surface — i.e. `eval_expr_arg_set` with the result kept as a graph rather than collapsed
to an index set.

---

## 6. CLI integration

`parse_args` (main.odin) currently hard-requires `positional[1] == "build"`. Add an
`ask` subcommand that reuses the front half of the pipeline and **skips codegen**:

```
discover_all_files → compute_use_closure → lex_target_files → parse_target_files
→ check_program        (STOP — no generate_program, no clang, no link)
→ run_ask(checked, query) → render
```

New file `ask.odin` holds the query parser, `run_ask`, and the renderers. Because it
stops after `check_program`, `mara ask` costs parse + check only — no LLVM, no clang —
so it's fast enough to run interactively and, later, on every keystroke in the LSP.

---

## 7. The LSP front-end

The CLI (§6) and the LSP are the two front-ends over the one `run_ask` engine (§3).
The LSP is where the analysis actually earns its keep — a gutter annotation that updates
as you type beats a CLI command you have to remember to run.

**Design target**, in priority order: (1) *instant* — answers feel synchronous, never a
spinner; (2) *zero divergence* — the editor shows exactly what the compiler thinks,
because it asks the same compiler; (3) *no dependencies* — one binary, no node_modules,
no separate process tree. None of these are aspirational; they fall out of the
architecture below. (Informal bar: lean and fast enough that someone who actively
dislikes language servers would leave it on.)

**Why the server can be naive.** Mainstream LSPs are complex because their host compilers
are too slow to run per-keystroke — rust-analyzer's salsa / lazy-query machinery exists
largely to avoid re-running rustc. Mara has no such problem. A full build is ~300ms
*including codegen and clang*; the server needs neither — it stops at `check_program`
(§6), so its per-edit cost is lex + parse + check, a fraction of a build. The first cut
re-checks the whole package on every change (debounced ~150ms after the last keystroke)
and stays imperceptible. The incremental cleverness others are forced into, Mara can skip.

**The server is the compiler, not a model of it.** rust-analyzer reimplements much of
rustc's semantics — a permanent source of "the IDE says one thing, the build says
another." clangd avoids that by reusing clang; Mara does the same by construction. Every
response is read off the one `Checked_Program` that also drives codegen, so the editor
can never disagree with `mara build`. Hover, goto-def, find-refs, and diagnostics are not
new analysis — they are serializations of data the checker already produced.

**Transport.** A `mara lsp` subcommand speaks JSON-RPC over stdio: a Content-Length
framing loop plus `core:encoding/json` (already in the Odin stdlib — no third-party code,
still one binary). `TextDocumentSyncKind.Full` (whole-document sync); range-incremental
sync buys nothing while re-checks are this cheap. State is a single warm
`Checked_Program`, rebuilt on debounced `didChange`.

**MVP surface** — every capability is a thin read over data the checker already holds:

| LSP method | Backed by |
| --- | --- |
| `publishDiagnostics` | existing located diagnostics (`diagnostics.odin`) — span → range, near format-only |
| `textDocument/hover` | `Expr.type_` is filled on every node; position → AST node → type |
| `textDocument/definition` | name resolution already resolves to decls (`fun_asts`, `Expr_Ident.resolved`, `Span`) |
| `textDocument/references` | same resolution — semantic, not grep |
| `textDocument/documentHighlight` | `DocumentHighlightKind.{Read,Write}` from `Binding.read` / `Stmt_Assign.target` |
| `textDocument/semanticTokens` | parser/checker know keyword vs type vs fn vs param per token — compiler-accurate highlighting, an upgrade on the Sublime regex grammar |

**Diagnostics are table stakes — be quietly excellent, don't try to impress with them.**
The protocol piece is standard and the data already exists, so the only win available is
latency + parity: instant, and byte-identical to `mara build`. Lag or divergence there
would un-impress; presence alone won't wow. Nail it and move on.

**Where `ask` plugs in — the differentiator.** The same `run_ask` is surfaced three ways:
- a custom request `mara/ask` returning `Ask_Result` JSON (the full graph, for a tree/panel view);
- **code lenses** above each `fun` — "inputs" / "contributors" — that expand the relevant slice on click;
- **inline diagnostics** off the cheap sub-queries: "read, never written ⚠" and "N writers"
  in the gutter. These run on the warm `Checked_Program` like any other diagnostic, and
  would have flagged `DrawState.texture` / `instance_count` *as the code was typed*.

Every `Ask_Node` carries a `Span`, so all three get jump-to and inline decoration for free.

**Explicitly deferred (the long tail).** Completion done *well* is a genuine sub-project
(ranking, context, partial-parse recovery); rename, formatting, and workspace-symbols are
real work too. None of them are what makes the server notable, and none are blocked by the
core — they get added once the core is in daily use. Listed here so their absence in v1
reads as a decision, not an oversight.

**Incrementality (future).** The "function is an island" property means an edit only
invalidates its function's callers and callees, not the whole program — the same invariant
behind parallel per-module codegen. If debounced full re-check ever stops feeling instant
on a large project, that's the upgrade path. The first cut does not need it.

---

## 8. Honest limits

- **Field granularity is new.** The escape machinery is *parameter-index* granular;
  collecting per-field writes (`Stmt_Assign.target`) is additional but mechanical.
- **Operator overloading is a non-issue.** A resolved overload sits on the node
  (`Expr_Binary.overload_fn` / `Expr_Unary.overload_fn`); the slice treats it as an
  ordinary already-resolved call and recurses into the operands as its arguments. A
  primitive op (`i64 + i64`) isn't a call — just union the operand provenances. No
  special handling, and no need to consult the overload *set* at a concrete site (that
  only matters forward, "who could call this overload", or at unresolved generic sites).
- **Aliasing degrades precision in tiers; only byte type-punning actually breaks it.**
  (1) *Resolved* — direct field writes, resolved calls/overloads — exact.
  (2) *Typed* pointer/index aliasing — two `^DrawState`, or `arr[i]`/`arr[j]` at runtime
  indices — keeps the field/element *type*; only *which instance/index* is uncertain, so
  the answer stays sound and field-precise (the writer set, reported not guessed; follows
  `Type_Env.aliases`). (3) *Byte type-punning at a runtime offset* —
  `head: Head = #big_endian bytes[off]` next to `bytes[other] = …` — loses the type *and*
  the location, so a read can't be tied to a specific write. This is the one real
  soundness hole. Even here Mara bounds it: only writers of *that* buffer reachable
  through the params it is passed to qualify (no global feeds it from offscreen), and
  reinterpret sites are syntactically marked (`Expr_Index.is_big_endian` + the sized-read
  forms), so the tool enumerates exactly where it dropped to "region of `bytes`" instead
  of answering wrong.
- **Byte-backed slices stay in tiers 1–2.** The dominant byte-buffer use — backing for a
  typed `[]T` view (strings, asset blobs, font tables read through slices) — restores
  type and per-access structure. The analysis tracks the *slice* as the unit (slices are
  already first-class in the escape machinery via `Provenance` / `local_slice_backed`),
  treats the buffer as a leaf source, and reads through the slice are ordinary typed
  accesses. Raw reinterpret-at-computed-offset is the rare exception, not the rule.
- **Indirect calls** are opaque nodes until fn-type resolution lands. Nominal fn types
  make that tractable (bounded candidate set), unlike C function pointers.
- **Const folding of leaves:** module-level `::` values are leaves, not chased into.

None of these block the headline `inputs` / `deps` / `contributors` queries; they bound
precision at the edges, and each degradation is surfaced in the output.

---

## 9. Validation

`gfx.draw_state_render` in Pounce is the golden fixture. `mara ask draw_state_render
inputs` must report the consumed fields, their producer chains (shader ← file; vao ←
`primitives_init`; instances ← `append_one` ← playa + camera), and flag `texture` and
`instance_count` as `.Dangling`. Add `mara ask Visual deps` and a `contributors` case as
secondary fixtures. Diff the rendered tree against a checked-in golden, same as the
existing `test/` fixtures.

**Why this fixture, specifically — there's already a hand-rolled version in the tree.**
`draw_state_assert_ready` asserts that every field the draw consumes is non-zero, i.e.
*was produced* (0 = zero-init = no producer ran). That is this exact dangling-edge check,
done by hand, at runtime, with 0 as the "unwritten" sentinel. It's the strongest evidence
the feature earns its place: the need was sharp enough to hand-roll. The tool improves on
it three ways — it *generates* the consumed-field list instead of asking you to maintain
it, it checks the list *completely* (a forgotten `assert` is a silent gap; a derived list
can't forget), and it runs at *compile time*. What stays in the runtime assert is only its
genuinely dynamic residue (per-frame data, value sanity). Honest boundary: static "a
producer exists" is weaker than runtime "it ran and wrote a sane value" — so the assert
and the analysis are the dynamic and static halves of the same question, the same split as
slicing vs. a debugger.

---

## 10. Field-read footprint & param narrowing

Track not just *that* a function reads a struct parameter, but *which fields* of it — the
read-set / field-footprint. Two payoffs:

- **Sharper slices.** `inputs`/`contributors` report the exact consumed field set
  (`state.shader`, `state.vao_state.instance_vbo`, …) rather than "depends on `state`."
  The positive form of §8's "field granularity is new."
- **A refactor falls out: param narrowing.** If every read on a param `s: ^Big` lies under
  one sub-field — only `s.sub.*` is ever touched — then `s` could be `^Sub`; a parameter
  with an *empty* read-set is dead. This is exactly the camera cleanup, derived
  automatically: `camera_turn_walking` read only the mouse fields of the per-frame input →
  narrow to `^Mouse`; `zrel`/`loop_time` had empty read-sets → drop them. The diagnosis we
  did by eye is this analysis's printout. It's a *suggestion*, not a mandate — a human may
  keep the wider type by convention (e.g. "keyboard-users take the whole `^Event_State`"
  even though the body only reads `.keyboard`).

Mechanism: extend §5 step 2 (which already collects `Expr_Field_Access` rooted at a param)
from a boolean "is this field read" into an accumulated *set of access paths*. The
per-function footprint is a summary, like `fun_return_arg_set`, computed over the call
graph — a struct passed onward inherits the callee's footprint. Same precision caveats as
§8 (the aliasing tiers; the byte-punning hole, where the footprint collapses to "the
buffer"). Surfaces as `mara ask <fn> reads`, and as a lint: "param `s: ^Big` reads only
`.sub` → narrow to `^Sub`."
