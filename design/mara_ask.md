# `mara ask` — static data-flow & dependency queries

**Status:** substrate built; first version chosen. The "definitional summaries built
once" layer (§3) that this feature presumes now exists for real — §12's materialized
call graph shipped during the Type_Env teardown (callgraph.odin: skeleton, SCCs, the
`cg_bottom_up` summary framework, purity, return-arg-sets). The first `mara ask` to
build (decided 2026-06-21) is the **type dependency graph** — `<Type> deps`, §4:
who-contains-what / who-embeds-what / who-calls-what over the symbol table. It's the
right first cut because it's almost entirely *structural* (struct field + embed edges,
function-signature type edges) — it reads `SymbolTable.structs`/`.funs` directly and
barely touches the dataflow walk, so it ships value without the field-granular
machinery `inputs` (§5) still needs. (Grew out of hand-slicing `draw_state_render`'s
inputs in Pounce.)

> **Doc currency.** Most of this doc predates the Type_Env teardown. The *concepts* all
> hold and the substrate is stronger now, but several named handles moved. §1/§2/§12 are
> corrected inline; the later dataflow sections (§5/§7/§8/§10/§11) still use the old names
> because those queries aren't built yet — read them through this table:
>
> | doc says | now |
> | --- | --- |
> | `Checked_Scope` | folded into `^Type_Scope` (its `.params`/`.return_types`/`.origin`) |
> | `Type_Env` | deleted — the checker threads `^Type_Scope` directly |
> | `Type_Env.aliases` | flow.odin's `g_flow_alias` (`it = &root` redirect); rebuild a local map for the ask walk |
> | `Type_Env.scope_depth` | escape.odin's `enclosing_fun_depth` |
> | `Binding.provenance` | escape.odin frame-stack `get/set_provenance` (default `PROV_GLOBAL`) |
> | `Binding.read` | flow.odin's `flow_expr_reads` (read-tracking moved to the flow pass) |
> | `fun_return_arg_set` "SymbolTable cache, `-1` cycles" | query over `Checked_Program.call_graph.return_args` (SCC fixpoint) |
>
> The call graph in §12 is no longer "future" — it's built.

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

The compiler already encodes this invariant — now in the post-check escape pass
(escape.odin), which re-derives it over the durable scope graph rather than on a
transient env:
- **frame depth** — `enclosing_fun_depth` counts enclosing `.Fun` scopes; the escape
  check rejects a value living at our frame depth or deeper. Module-level bindings
  (depth 0) outlive everything. (Was `Type_Env.scope_depth`.)
- **provenance** — defaults to `PROV_GLOBAL` (immutable root), distinct from
  param/local provenance; tracked on the pass's block-scoped frame stack
  (`get_provenance`/`set_provenance`). Top-level names are constants, never producers.
  (Was `Binding.provenance`.)

So the queries below are graph reachability over edges the checker can already see —
not interprocedural points-to.

---

## 2. We have already built 80% of this

(Now more than 80%: §12's materialized call graph + bottom-up summary framework
shipped too — see that section. The backward slice below predates it and still
stands.)

The checker contains a **backward interprocedural slice** today: escape analysis.
Look at `eval_expr_arg_set` (type_checker.odin, ~5049):

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
(`lookup_callee_scope`, ~5163 — mirrors dispatch order: resolved name → source name →
`resolved_func` name → stripped monomorph suffix), asks which of the callee's args
flow to its return (`fun_return_arg_set`, ~4832 — now a query over the materialized
`Checked_Program.call_graph.return_args`; the old `-1` cycle hack is gone, replaced by
the SCC fixpoint in `cg_bottom_up`), and **recurses through the matching argument
expressions**. That is a return→arg backward walk across the call graph. `mara ask`
generalizes the same walk to more questions and finer granularity.

Reusable parts already in place:

| Need | Existing handle |
| --- | --- |
| Post-check IR to query (no re-walk) | `Checked_Program` — `functions: map[string]^Type_Scope`, `function_order`, `call_graph: Call_Graph`, `constant_values`, `table` |
| Name → function AST | `SymbolTable.fun_asts` (`map[string]^Stmt_Scope`) |
| Call → callee resolution (incl. dispatch/UFCS) | `lookup_callee_scope`, `Expr_Call.resolved_func: Maybe(Resolved_Func)`, `find_dispatch` / `dispatch_groups` |
| Operator → function resolution | `Expr_Binary.overload_fn` / `Expr_Unary.overload_fn` (`Maybe(Resolved_Func)`) — already resolved on the node |
| Return → arg dataflow | `fun_return_arg_set` → `Checked_Program.call_graph.return_args` (computed by `cg_compute_return_args` over `cg_bottom_up`) |
| Params / fields / returns of a fn | `Stmt_Scope.typed_params`, `.fields`, `.return_types`; on the checked side `^Type_Scope.params` / `.fields` / `.return_types` (Checked_Scope folded into Type_Scope) |
| Field/index/deref write sites | `Stmt_Assign.target` (complex LHS) + `Expr_Field_Access` / `Expr_Index` |
| Intra-proc points-to | flow.odin's `g_flow_alias` (`it = &root` redirect, same idea as the old `Type_Env.aliases`; rebuild a local map for the ask walk) |
| Foreign / intrinsic leaves | `^Type_Scope.origin` (`Origin_Source` / `Origin_Foreign` / `Origin_Intrinsic`) |
| Source locations (for the LSP) | `Span` on every AST node |
| "Is this name ever read?" | flow.odin's read-walker `flow_expr_reads` (the analysis moved to the post-check flow pass; `Binding.read` is gone) |

---

## 3. One engine, two front-ends

**Design rule: the analysis is a pure function over `Checked_Program`, returning a
result graph. The CLI prints it; the eventual LSP serializes it. No analysis logic in
the printer.** This is the same separation the codebase already keeps ("codegen does
no analysis").

```odin
Ask_Node_Kind :: enum { Function, Type, Field, Param, Const, File, Foreign, Opaque }
// `Type` (struct/enum/union/distinct) is the v1 node — §4.1. The rest are for the
// dataflow queries (`inputs`/`contributors`).

Ask_Node :: struct {
    kind:  Ask_Node_Kind,
    label: string,        // "draw_state_create", "DrawState", "DrawState.texture", "instanced_text.glsl"
    span:  Span,          // for LSP jump-to / inline; zero for synthesized leaves
    flags: bit_set[Ask_Flag],   // .Dangling (read, never produced), .Opaque (indirect call), ...
}

// Contains/Embeds/Takes/Returns/Calls are the structural v1 edges (§4.1);
// Produces/Consumes are the dataflow edges (§5).
Ask_Edge :: struct { from, to: int, kind: enum { Contains, Embeds, Takes, Returns, Calls, Produces, Consumes } }

Ask_Result :: struct { nodes: [dynamic]Ask_Node, edges: [dynamic]Ask_Edge, root: int }

run_ask :: proc(checked: ^Checked_Program, q: Ask_Query) -> Ask_Result { ... }
```

Renderers over `Ask_Result`: text tree (default), `--dot` (Graphviz; this is the
graph the user wants to *see*), `--json` (tooling + LSP transport).

**The engine itself is two layers, and only the first is whole-program.** `run_ask` reads
as if it recomputes from `Checked_Program` per call; in practice it splits:

- **Definitional summaries — built once, context-insensitive.** Call graph, struct/type
  graph (struct → field types), the read- and write-footprint summaries (function ×
  param-path → paths read / written, transitively), `fun_return_arg_set`. None mention a
  concrete object — they are keyed on *formal* params and type names, cached on the
  `SymbolTable` and frozen after the check, exactly as `fun_return_arg_set` already is.
  This is "in general, who writes `DrawState.texture`" — the substrate behind
  `<Type>.<field> writers`.
- **The anchored walk — per query, context-sensitive, lazy.** A query seeds a concrete
  point — a function, a value, or (§5) a *call site* — binds formals to the actual objects
  there, and walks the summaries *projected onto that instance*. This is the only part that
  runs per mouse-point, and it is cheap: a reachability traversal of built summaries, not a
  recomputation.

The relation is a function to its stack frame: the summary graph is the reusable shape, the
anchored walk is that shape instantiated with concrete values, on demand, one invocation at
a time.

**This is also what makes context sensitivity affordable** — the axis that makes precise
interprocedural analysis costly elsewhere. The expensive version computes a
context-sensitive result for *every* call site eagerly (the all-contexts product).
`mara ask` never pays it: summaries are context-*insensitive* and built once, and exactly
*one* context — the call you asked about — is instantiated, lazily, on demand. You don't
enumerate every possible stack frame ahead of time; you instantiate the one you're standing
in. The point-at-the-call UX is not just ergonomics, it is the cost model.

---

## 4. Query surface

```
mara ask                             # BUILT: module map — every loaded module (local first, then stdlib); main-bearing ones flagged
mara ask <Module>                    # BUILT: module surface — that module's declared types (ranked by user-count) + funs (source order)
mara ask <fn> inputs                 # producer/consumer set of fn's reachable input surface
mara ask <fn>.<param> contributors   # backward slice toward sources (generalized escape walk)
mara ask <Type> deps                 # v1: type dependency graph — what this type pulls in (§4.1)
mara ask <Type> users                # v1: reverse — who contains/embeds/takes/returns this type (§4.1)
mara ask <Type>.<field> writers      # every site that assigns this field, program-wide
mara ask <var> in <fn> assignments    # every assignment to a specific local
mara ask <var> in <fn> readers         # every read of a local/store, counting the loop back-edge (§11)
mara ask <fn> scratch                   # loop-carried scratch buffers missing a per-iteration reset (§11)
mara ask at <file>:<line> inputs        # 'inputs' anchored on the concrete call there — the actual object's fill chain (§5; LSP: point at the call)
```

Flags: `--dot`, `--json`, `--depth N` (cap transitive walk), `--module <m>` (scope the
search). All read-only; all stop after type-checking (see §6).

`inputs` is the headline *eventually*. `contributors` is literally `eval_expr_arg_set`
lifted out of escape analysis and run to a printed result. But the **first version to
build** is `deps` — see §4.1.

The no-name **map** and `<Module>` **surface** are the orientation layer above the
per-name queries — the drill-down is `mara ask` → `mara ask <Module>` → `mara ask
<Name> deps|users`. Both read the same symbol table: a module is matched by
`home_package` (the `mara.` alias accepted), surface types rank by reverse-edge user
count, and only declarations are listed (monomorphized instances filtered out).

---

## 4.1 First version: the type dependency graph (`deps` / `users`)

**Chosen first cut (2026-06-21).** Of the query surface, the type dependency graph is the
one that ships real value with the least new machinery: it is almost entirely
*structural*. Where `inputs` (§5) needs field-granular read/write footprints that don't
exist yet, `deps` reads what the symbol table already holds — struct layouts and function
signatures — and emits a graph. It barely touches the dataflow walk, and the one
cross-function edge it wants (who calls what) is now free from the materialized call graph
(§12). It is also broadly useful on its own ("what does this type pull in", "who embeds
`DrawState`", "who takes a `^Camera`") and exercises the whole §3/§6 spine — query parse →
`run_ask` → `Ask_Result` → text/`--dot` renderers, stopping after `check_program` — on a
low-risk query before the harder `inputs` walk.

**Nodes.** Types (`.Struct` data scopes, enums, unions, distinct) and functions. Reuse §3's
`Ask_Node`; add a `Type` node kind to `Ask_Node_Kind` (the enum has `Function` but no type
node yet). `label` = the type/fn name, `span` from the `^Type_Scope` / `^Stmt_Scope`.

**Edges — all read directly off declarations, no analysis pass:**

| Edge | Source |
| --- | --- |
| struct **contains** type | `^Type_Scope.fields[].type_` (a field whose type is/embeds another scope/enum/union) — `SymbolTable.structs` |
| struct **embeds** type | the `using` field(s) on a struct — the "who embeds what" the language already distinguishes from a plain field |
| fn **takes** type | `^Type_Scope.params[].type_` (unwrap `^T` / `[]T` / `[N]T` to the underlying named type) |
| fn **returns** type | `^Type_Scope.return_types[]` |
| fn **calls** fn | `Checked_Program.call_graph` out-edges — already materialized; *optional* in v1, the type edges alone are useful |

Unwrapping pointer/slice/array wrappers to the underlying named type is the only real
walk; it's the same `distinct_base`/element-unwrap the codegen layout already does.

**Two directions, and the reverse is the prize.** `mara ask <Type> deps` = forward (what
`Visual` pulls in: its field types, transitively). `mara ask <Type> users` = reverse (who
contains/embeds/takes/returns `Visual`) — the "what breaks if I change this struct" query,
which is the one people actually reach for. Both are the same edge set walked in opposite
directions; build the edge set once, traverse either way. `--depth N` caps the transitive
walk; `--dot` is the headline output (this graph is meant to be *seen*).

**What v1 deliberately omits** (all present in later queries, none needed here): field-level
read/write footprints, the dangling check (§5), the anchored/per-call walk (§5), provenance
(§10), flow sensitivity (§11). v1 is pure declaration-structure + the call edges.

**Validation.** `mara ask Visual deps` and a `<core type> users` case as golden fixtures
(§9 style — diff the rendered tree against a checked-in golden). A cheap honesty check: the
type graph's strongly-connected components are mutually-recursive type groups, which must
already be the ones codegen forward-declares — a free cross-check against existing behavior.

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

**Seeding from a concrete call (the anchored walk).** Steps 1–7 seed on a function
*definition* — `draw_state_render`'s param surface, call-site-agnostic. The form you reach
for while debugging seeds on a *call*: point at the `Expr_Call` in `game_draw`, bind its
formal `state` to the actual argument's access path (`game.draw_state_text`, via the arg
expr / `Type_Env.aliases`), and run the same walk with the read/write sets resolved to that
object. Now the dangling check names the missing producer for *this* `draw_state_text`, not
"some `DrawState`."

Honest about the anchored walk:
- It seeds object *identity*, but the producer search is still whole-program-from-the-object,
  not a subtree under the call. The atlas that fills `.texture` was likely written by an
  `asset_init(&game)` that ran *earlier in `game_draw`* — a sibling of the call you pointed
  at — so the walk reaches sideways and upward, bounded only by where the object flows
  (no-globals keeps that bounded).
- A runtime-selected object (`batches[i]`) degrades identity to "element of `batches`" —
  §8 tier 2: field/type kept, index lost. Sound, reported not guessed.

What it *gains* over the definitional form: along a concrete traced path it can ask the
§9/§11 ordering question — does a writer *dominate* this call — not just "does one exist."
Existence is the definitional query's ceiling; the anchored frame gives "did it run before
here." The CLI must name the site (`at <file>:<line>`); in the LSP it is cursor →
`Expr_Call` → walk, which is where this query lives.

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

---

## 11. Loop-carried scratch — the `nodes.len = 0` check

Everything above is **flow-insensitive reachability**: §5's dangling check is set difference
(`read ∖ written`) — it cares *whether* a write exists anywhere in the reachable tree, never
*when*. That blind spot has a sharp failure mode, and this section is the sibling analysis that
closes it. It is the one **flow-sensitive** query in the doc: it has to look at the single edge the
others ignore — the loop **back-edge** (the jump from the bottom of a loop body back to the top).

**The case that motivated it.** [font.mara:155](../code/font.mara:155), `nodes.len = 0`, was once
deleted as dead code and silently broke multi-contour glyphs. It is load-bearing, and nothing in §5
would have protected it: `nodes.len` is both read and written, so it is never "dangling."

**The buffer's life, in plain terms.** `nodes : [..1024]Node` is created *once*, at
[font.mara:136](../code/font.mara:136), before the contour loop at [139](../code/font.mara:139).
Call each turn of that loop a *lap*. Every lap does three things in order: **empty** it
(`nodes.len = 0`, line 155), **fill** it (the `&nodes + Node{…}` appends, 171–209), **drain** it (the
pen walk reads `nodes[0]` and loops `0..nodes.len`, 212–251). One buffer, reused every lap.

**Why deleting the reset looked safe — and is the whole trap.** On the first lap the buffer is empty
for free: Mara zero-inits everything, so `len` starts at 0 with no help. The reset writes the value
the buffer already holds — locally a no-op. The cost only lands from the *second lap on*, where the
back-edge carries the previous contour's nodes back in: `nodes[0]` is then the wrong start point and
the `0..nodes.len` walk reads stale entries. One-contour glyphs pass; multi-contour glyphs (`B`, `8`,
`o`) break. This is the **reuse-dual of §9's `draw_state_assert_ready`**: both ask "is the storage in
the state the consumer assumes?" — there, never produced; here, produced once but destroyed by the
back-edge. Zero-init makes the first pass correct for free, which is exactly what hides the missing
producer on every later pass.

**The read of `.len` is hidden.** Grepping for `nodes.len` reads turns up nothing in the loop body —
but every `&nodes + x` is a read-modify-write of `.len` (read len → store at `nodes[len]` → bump
len). The append *is* the len read. The analysis must model the append (an `Expr_Binary`, `&S + x`)
as touching `S.len`, or it sees a write with no reader and concludes backwards.

**The real question: accumulator or resetting scratch?** A buffer reused in a loop is one of two
things, and only the second needs a reset:
- **Accumulator / tally** — collects across laps; its value *after* the loop is the point. `edges`
  and `contour_start` in this same function are accumulators.
- **Resetting scratch** — filled and consumed within one lap, then thrown away. `nodes` is scratch.

Two signals separate them, and the flag requires **both**:

1. **Read shape — whole-buffer drain from a fixed origin.** Scratch is read back over its *entire*
   current contents from index 0 each lap: `nodes[0]` *and* the `0..nodes.len` walk. An accumulator
   read per-lap is read through a **moving window**, not from 0 — the second loop at
   [font.mara:258](../code/font.mara:258) reads each contour's edges as the span
   `[contour_start[ci], contour_start[ci+1])` (the fencepost scheme spelled out in the comment at
   [126](../code/font.mara:126)), a window that slides per contour. Fixed `0` says "the front is
   *this lap's* start"; a sliding `lo..hi` says "a slice of a growing whole."
2. **Lifetime — dead after the loop.** Scratch has no reader once the loop ends (`Binding.read`
   shows no use past the loop body), so the per-lap drain is its *only* consumer: build-and-discard.
   An accumulator is read after the loop, or one of its fixed slots is.

**The rule.** Storage `S` whose declaration sits in a scope *outside* a `Stmt_For` `L` (compare the
decl's `scope_depth` to `L`'s body), where inside `L.body`: `S` is appended to (`&S + …`, so the
write-anchor is `len`), is drained whole `0..S.len` from a fixed origin, and is **not** read after
`L` — *and* nothing fully kills `S` at the top of `L.body` (a `Stmt_Assign` of `S.len = 0`, or a full
overwrite) → **flag**:

> `nodes` is filled and fully drained each iteration but never reset; from the second iteration on it
> reads on top of the previous iteration's contents. Add `nodes.len = 0` at the top of the loop, or
> move the declaration inside the loop.

The fix message is honest about the trade it names. Hoisting `nodes` out of the loop is a hand
optimization — it avoids re-zeroing 1024 `Node`s every contour. The reset is the *correctness
obligation that the optimization incurs*. Moving the declaration inside the loop also fixes it (fresh
zero-init each lap) at exactly the cost the hoist was avoiding. The tool states both; the human picks.

One framing makes the whole thing click: the reads are pinned to `0` and cannot drift. The writes
anchor at `len`, which *should* be 0 at lap start. `nodes.len = 0` is what keeps the **write-anchor
pinned to the read-anchor**. Delete it and the write-anchor floats up lap by lap while the read-anchor
stays at 0 — they desync, and the drain reads from 0 straight into the previous lap's leftovers.

**Two surfaces** (the §3 one-engine rule still holds — both read the same result):
- **The lint.** Fires on the broken code as an ordinary diagnostic, no diff awareness needed: it
  flags the *absence* of a reset given the scratch shape, so it catches the bug however it arose
  (deleted, or never written). Queryable as `mara ask <fn> scratch`; in the LSP, a gutter warning on
  the loop.
- **"What reads this store?"** The dual of `<Type>.<field> writers`, made back-edge-aware. Select
  `nodes.len = 0` and it names the reads of `nodes.len`/`nodes[…]` it governs this iteration — the
  appends (171–209) and the drain (212, 215) — and notes that, because `&nodes +` accumulates rather
  than overwrites, those reads inherit this store's effect on every later iteration through the
  back-edge. That answers the exact question behind the deletion — "does this line do anything?" —
  where reading top-to-bottom answers wrong: the store's whole job is to stop the *previous*
  iteration's `len` from reaching those reads. A store with no such reads reports "dead — safe to
  remove." Queryable as `mara ask <var> in <fn> readers`; in the LSP, a hover / inlay.

**False positives.** A literal-`0` read *alone* is not enough — this is correct and must not be reset:

```
seen : [..256]i32
for x in stream {
    &seen + x              // append, len grows every lap
    if x == seen[0] { … }  // literal-0 read every lap, no reset
}
```

`seen[0]` is "the first value we ever saw" — a persistent slot, not a per-lap start. The two-signal
rule spares it: `seen` is *poked* at one fixed slot, not **drained `0..len` as a unit**, and it
outlives the loop. The same combination spares `edges`/`contour_start` (moving window *and* read
after). The honest residue: a buffer that genuinely fills-and-fully-drains-from-0 each lap, is dead
after the loop, yet is *meant* to reprocess prior laps' data plus the new — survives both filters and
would false-positive. That is a "redo everything plus new, each lap" loop: rare, and arguably its own
smell. Not zero false positives, but you have to go looking for one.

**Limits.**
- **Flow sensitivity is new.** The rest of the doc is reachability; this needs the back-edge and the
  top-of-body kill. v1 is intra-procedural (decl, loop, appends, reads, reset all in one function —
  the common case). A reset performed by a *helper* the loop calls is an interprocedural extension,
  the same summary shape as §10's footprint.
- **`.len` is the clean cursor.** Partial arrays make "the reset" syntactically obvious
  (`S.len = 0`) and the append a recognizable len read-modify-write. A buffer that tracks its count
  in a *separate* variable and index-writes (`buf[count] = …; count += 1`) needs that count variable
  identified as the cursor first — harder, out of scope for v1.

**Validation.** The [font.mara:139](../code/font.mara:139) contour loop is the golden fixture, and it
is self-checking: with `nodes.len = 0` removed, `nodes` must flag; `edges` and `contour_start` —
accumulators in the *same loop* — must stay silent. That same-loop contrast is the false-positive
test baked into the fixture. Diff the rendered diagnostic against a checked-in golden, as elsewhere
in `test/`.

---

## 12. The materialized call graph as shared substrate — BUILT

**Status: BUILT (callgraph.odin), 2026-06-20/21.** It landed during the Type_Env
teardown, ahead of `mara ask`, because several analyses wanted it at once. A
post-`check_program` artifact on `Checked_Program.call_graph`: nodes = callable scopes,
edges = resolved calls + construction edges, Tarjan SCCs, reachability-from-`main`, and
— the real prize — the `cg_bottom_up` summary framework (visit SCCs callees-first,
iterate each to a fixpoint). Two summaries ride it today: **purity** (`cg_compute_purity`
+ `MARA_DUMP_PURITY`) and **return-arg-sets** (`cg_compute_return_args` →
`call_graph.return_args`, which `fun_return_arg_set` now queries — the `-1` hack retired,
and *more precise* for recursion than the lazy version it replaced). The rest of this
section is the original vision; it reads as "future" but the skeleton + framework are now
real, so the remaining items are summaries to add, not infrastructure to invent.

**Why it was scattered re-derivations before.** The checker walked a call graph
constantly without materializing one: `fun_return_arg_set` followed callees through
`lookup_callee_scope` and hand-rolled cycle detection (that `-1` return *was* an ad-hoc SCC
check). Codegen re-derives the same edges from callee resolution + `function_order` for its
emission order and parallel scheduling. Materializing it once sits upstream of all of them —
the consolidation the codebase already favors (function-is-island).

**The skeleton is not the prize — the summary framework is.** Every interprocedural summary
in this doc — arg-sets, the read/write footprints (§5, §10), provenance — is the *same*
bottom-up-over-SCCs pass with a different lattice. Build the skeleton once (nodes =
`function_order`; edges = resolved calls + dispatch fan + operator-overload edges, all already
on the nodes as `resolved_func` / `overload_fn` / `dispatch_groups`) and the summaries become a
*framework* over it instead of N bespoke walks each with its own cycle guard.
`fun_return_arg_set`'s `-1` hack becomes "the SCC this node is in," computed once and shared.

**What it unlocks beyond `ask`** — each is a propagation over the same edges (✓ = already
built on `cg_bottom_up`; the rest are summaries still to add):

- **Static stack bounds — the scope allocator made analyzable.** Frame sizes are known at
  check time; graph + SCCs give worst-case stack depth per entry point, flag recursion (a
  cycle = unbounded = must arena/heap, not stack), and could drive stack-vs-arena placement
  statically. This is the *static* form of the overflow already hit and fixed by the
  big-tuple-slot arena bump — and it fits the TigerStyle bar: bounded, provable resources.
- **Interprocedural provenance — ✓ partially.** Provenance is here *intra*-procedurally (the
  escape pass's frame stack + the local-slice-backed check). The graph lifts it *across*
  calls; the return→arg half is already done — escape's `fun_return_arg_set` is now the
  `call_graph.return_args` summary, so a returned slice's backing is traced to the param it
  came from interprocedurally and *exactly* (the SCC fixpoint catches recursive laundering the
  old lazy guard missed). The full "backing originated at buffer X two frames up" form is
  `contributors`, still to surface.
- **Reachability / dead-function elimination — ✓.** `cg_compute_reachability` marks what's
  reachable from `main`; the rest is a warning or DCE (no consumer acts on it yet).
- **Purity / effect propagation — ✓.** `cg_compute_purity`: does a function transitively touch
  foreign / I/O? If not, it is a const-eval candidate. Comptime-evaluability *is* a call-graph
  property; ties into the existing `#if` / `constant_values` machinery (no const-eval consumer
  acts on it yet — the verdict is computed and dumpable, not yet used).
- **Fallibility propagation** — transitive "can this error," for the `?` / must-use-err
  system; would flag a `-> err` function whose body can't actually fail.
- **Parallel codegen scheduling** — the SCC DAG *is* the dependency structure parallel
  per-module codegen already leans on implicitly.

**One honest seam.** The graph is only as sharp as callee resolution: indirect / fn-typed-param
calls are opaque edges (§6, §8), bounded by nominal fn types. Carry two edge flavors on the one
graph — resolved/monomorphized (dataflow, DCE, stack bounds) and the dispatch-set (forward "who
could call this overload," and the opaque cases). Both are already on the nodes; the graph just
collects them.

**Where it sits.** A post-`check_program` artifact on `Checked_Program`, materializing the
edges that `function_order` + `lookup_callee_scope` already imply. Small addition, large
leverage — it is what turns §3's "summaries built once" from a per-analysis cache into a shared
framework, and the natural home for the stack-bound and provenance analyses that are out of
scope for the first `ask` cut.
