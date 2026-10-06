# The annotated tree

Decided with the user (2026-10-06): what the checker finds about each node is kept, per
instance, beside the flat tree, and becomes the program's description. The program graph
stops being a stored structure of its own; every connection it has is still there, read off
the tree and its annotations. This doc is the plan; its checklist is at the end.

## Why

The program graph (design/program_graph.md) is two things in one structure:

- **What the program means**: containment, declarations, refers-to, has-type, calls. For code
  that isn't generic this is the tree again, in a second id space, joined to it by origins
  (`Syntax_Id` ↔ `Node_Id`).
- **What it does, in order**: operations in runs joined by `then`. This is lowering: what
  codegen and the flow analyses read.

The checker builds both as it checks: it emits operations in execution order while it works
out types. That is what keeps its findings from lasting (`types` is overwritten by each
generic instance and dropped once the body is built), what keeps it from checking bodies in
parallel or putting one off until what it needs is known, and why it builds tentatively and
takes the operations back (`graph_build_mark` / `graph_build_drop_since`).

With the checker only annotating:

- `mara ask`, hittest and an editor read the tree and its annotations: one id space, the node
  the origin of everything said about it.
- Lowering is a pass of its own over the annotated tree. Whether a function's operations are
  stored beside the tree or made by a walker as they are needed is decided later, by which is
  simpler or faster.
- The checker can check bodies in parallel: each unit's annotations are its own, and the
  connections that cross units (callers, a type's users, flows through calls) are indexes
  made by inverting them afterwards.

## Every connection, from the tree

| Connection | Where it comes from |
| --- | --- |
| contains | the tree; a generic's instances are its template's range, once per instance |
| refers to | a name's annotation: the token that declares it |
| has type | a node's annotation |
| calls | a call's annotation: the fun or struct it runs — written calls and implicit ones (a construction, an operator through `overload`) |
| flows | def-use over the operations: a name's declaration, the statements that write it, across a call the arguments as the callee receives them |
| then | the operations, made from the annotated tree |

The proof that nothing is lost is stage 2's: the program graph, made from the tree and its
annotations alone, is the one the checker built (`test/graphdiff.sh`).

## Stages

1. **Annotations that last.** Per instance, for every node the checker checks: its type, the
   declaration a name refers to, a call's callee — implicit calls included — and the arguments
   as a callee receives them. Kept on the Checked_Program. The checker reads its own findings
   there. Gate: IR and graph identical; the annotations complete and agreeing with the graph.
2. **Lowering out of the checker.** A pass over the annotated tree builds the graph's
   operations, one function at a time, after checking. The checker loses its builder calls,
   its two modes (building or not) and the tentative builds. Gate: `graphdiff.sh` and
   `irdiff.sh` identical.
3. **The readers onto the tree.** `mara ask`, hittest and def-use read the annotations. Gate:
   `ask.sh`'s goldens.
4. **What's left of the graph.** Its scopes and declarations go (refers-to names a token, a
   variable is its declaration); the operations stay per function, stored or walked. Gate:
   `irdiff.sh` identical.

## Stage 1

- **Instances.** A node's identity is the builder's already (`tc_sid`): instance 0 is the tree
  as written; each generic fun's or struct's instance, numbered as it is made, is its
  template's node range checked again with its type params bound. The template itself is
  syntax only: instance 0 says nothing about its range.
- **The store.** `Annotations` on the Checked_Program: an instance table (its range, its scope)
  and columns per instance — instance 0's over the whole tree, an instance's over its
  template's range. A lookup is a node and the instance it is read in; a node outside the
  instance's range is instance 0's.
- **Refers-to.** A name is declared by a token: a local's, a param's, a field's, a constant's,
  a fun's or a type's name where it is written. A binding carries its token; a use records it
  and what kind of name it is. Names no source declares (`void`, `this_program`, the builtin
  types) are builtins: a kind, no token.
- **Calls.** Every call a node makes: a written call, a method's, a dispatch's or a generic's
  instance, a construction (`x : Item`, `Item{…}`, `Item(…)`), an operator through `overload`.
  A call through a function value has none (the honest seam, as in the call graph).
- **Arguments.** For each call, what each param receives: a written argument, the receiver, or
  the param's default (implied, its cause the call).
- **The proof.** `MARA_ANNOT=dump` prints the annotations; `MARA_ANNOT=check` checks that
  they are complete (each expression the checker checks has a type in each instance it is
  checked in, each name a declaration or a builtin, each call a callee or a function value)
  and that they agree with the graph (each operation's declaration is its name's, each Calls
  edge its call's callee). `test/annotcheck.sh` runs the check over the corpus.

## Stage 3

The readers are `mara ask` (`ask.odin`, `slice.odin`, `lineage.odin`), `ask at` (`hittest.odin`),
def-use (`defuse.odin`) and the call graph they share (`callgraph.odin`). What a flow view
computes stays def-use over the operations (the table above): reaching definitions over a
function's runs, a value's reads walked through its operations. What changes is where the
readers get what the program *means* — which variables a function has, their names, types and
places, which function calls which and where, an expression's type. Today that is the graph's
declaration and scope nodes and its Calls edges, which stage 4 removes. After stage 3 it is the
tree and its annotations, and the readers touch the operations only for flow.

- **`ask at`.** An expression's type is its annotation, in each instance it is checked in (a
  generic's template: each instance's). An untyped number shows as one; a call with no value
  (void, or `print`'s) shows none.
- **Variables are their declarations.** The checker records each variable a body binds — a
  param, a named result, a local, a loop's, a match arm's binding, a `let` — under the fun or
  struct it is bound in, in the order bound: its token, its kind, its type
  (`Annotations.vars`). The graph's declarations name the token that declares them, so an
  operation's variable is a token. The check: each function's variables are the graph's
  written declarations in its code, the same names and types.
- **Def-use's variables from the annotations.** A function's variables are its annotated ones;
  a definition or a use finds its variable through its declaration's token. The operations
  still say which synthetic locals are seen through.
- **The call graph from the annotations.** An edge for each annotated callee, from the
  function the call is in — a default argument's calls from each function whose call takes
  the default (`Annotations.args`). A call's line is its node's. A function calls the outside
  world when it calls a foreign one or prints. The check: the same graph as the one read off
  the Calls edges. A function's call sites are its callers' call operations that run it.
- Gate for each: `ask.sh`'s goldens, any change explained here; `annotcheck.sh`; `irdiff.sh`.

## Stage 4

What stays of the graph is what codegen and the flow analyses read: each function's
operations. They stay stored, as lowering builds them, since that is simpler than a walker
that would lower a function again for each reader and faster than doing so. The rest goes:

- **The end.** Each function's code — a fun's, or a struct's constructor's — and each
  constant's (what folding reads) is its own: its operations (kind, how written, type,
  where, name, operands, statement), its runs and the Then edges between them, its locals,
  its statements and its defer blocks. Ids are each code's own, from 0. A local is a
  variable's token (a param, a named result, a local) or a synthetic one (a temporary, a
  loop's end). A variable operation names its local, a global operation its constant or
  fun, a call its callee. There is no scope tree, no program-level declaration, no Calls or
  Runs edge, and no segment or canonicalization: lowering builds one code at a time.
- **The steps**, each gated by `irdiff.sh` identical, the goldens and `annotcheck.sh`:
  1. Calls and Runs edges become columns: a call's callee, a run-defer's block.
     `graphdiff.sh` identical too (the dump says the same).
  2. Names by their tokens. Lowering finds a variable's declaration by the token its name
     refers to; the builder's own name stack goes.
  3. No program-level declarations. Modules, types, variants, dispatch groups, imports
     and struct fields stop being nodes; constants are found by their token. What read
     them reads the checker's (its Type_Scopes, the annotations).
  4. A code per function. First the codes become independent inside the one graph: a
     constant's use names the constant (by its value's node), and a body's definitions
     are codes of their own. Then the graph, once built, splits into each function's and
     constant's code (`Program_Code`), ids its own from 0; the only declarations a code
     names from outside it, the compiler's globals, get nodes of their own past its
     root's. Codegen and the analyses read one code at a time; def-use's uses are a
     function and an operation. The builder still builds the codes in one graph, its
     segments and canonicalization ordering them; building one code at a time comes
     after.
  5. Locals. A code's params, results, locals and blocks stop being nodes: its locals
     table, its defer blocks. *Not done* — see the checklist: they are that table
     already, stored in the code's own columns.

## Checklist

- [x] 1. Annotations that last (2026-10-06)
  - [x] The store and the instance table; types per instance, kept; `MARA_ANNOT=dump`
        (65f1f5b). `annot.odin`. A type node keeps the type it resolved to.
  - [x] The checker's other per-node findings in the store, per instance (5d2f9ad): callees,
        call names, `size_of`, dot bases, by node and instance (`annot_key`, which `tc_sid`
        now is); constants and variants became refs' kinds.
  - [x] Refers-to (6df8853). A binding carries the token that declares its name
        (`scope_bind`'s ref); named types, funs, fields and variants know their own
        (`Scope_Body.decl`, a field's `decl`, `Type_Enum.variant_decls`). A `Ref` is that
        token and the name's kind.
  - [x] Implicit calls (3e8bebd): an operator through `overload` (on its Binary or Unary,
        or the compound assignment), a struct literal's construction (on the Literal), a
        bare or shape declaration's (on the name it declares).
  - [x] Arguments as received (7ca34e4): `Annotations.args`, per call, in param order.
  - [x] `MARA_ANNOT=check` and `test/annotcheck.sh`. Complete (every name the checker types
        names something) and agreeing with the graph both ways: every variable operation
        refers to its name's declaration, every call and construction the graph makes is
        its node's annotated callee and every annotated callee is a call the graph makes,
        every argument is computed from the node its annotation names. Corpus: the 211
        programs that compile, 0 problems — 49837 names, 28576 variables, 2834 calls, 3832
        arguments. Reversing the arguments on purpose is caught (541 problems in Pounce).
  - What stage 1 found, for stage 2:
    - The builder's own name resolution (`graph_bind` / `graph_lookup`) agrees with the
      checker's refers-to on the whole corpus: lowering can read the refs.
    - A loop's variables are declared by tokens in its header, not nodes: the loop's own
      writes of them have no node to annotate (the check counts them apart, 1571); what
      reads them is annotated.
    - A number is typed `infer_int` / `infer_float` with no cell: the width it is built at
      is its use's, decided where the builder takes it at a type (`settled`). Lowering
      needs each value's use type — a conversion annotation, added with the lowering that
      reads it.
    - `print`'s call is typed `<error>` (the checker's "no value"), not void. Kept for
      parity.
    - Not yet annotated, added in stage 2 as the lowering needs each (graphdiff proves
      them): defers run at each exit, arena mark and reset, where a value is built (into
      its destination, or a temporary), implied conversions (a widen, an array viewed as a
      slice), `?`'s branch.
- [x] 2. Lowering out of the checker (2026-10-06)
  - [x] The checker's findings are the same without a builder (e8857c8): checked with no
        builder, every annotation is the one it makes while building.
  - [x] Lowering, form by form (ccba42e, f53fd1c, 2d1f2e8, 3e017ef). `lower*.odin` replay
        what the checker checked, in its order (`TC.events`: each module statement settled,
        each constant, each body, each in its instance) and build each body from the tree
        and its annotations, through the one builder, in the order the checker built it.
        Every program in the corpus lowered to the checker's graph.
  - [x] The switch (3185241): the graph is lowered after checking, always.
  - [x] The checker only checks: its builder calls, its two modes and its tentative builds
        are gone. `tc_check` is its one entry for an expression, and returns a type. The
        build helpers it shared are lowering's (`lower_build.odin`: `lw_store`,
        `lw_value_as`, …), and so is the state they kept (`TC.lower`). The checker went from
        8645 lines to 6594; lowering is 2645.
  - Gates: the IR is identical (323 builds, and test_1M's 106 modules and its run). The
    annotations are identical to the pre-switch compiler's (342 programs) and agree with the
    graph (`annotcheck.sh`). Ask's goldens match. The graph is identical except for one
    explained difference: the program struct's `scope_allocator` field. The checker built it
    before the arena was known, so it was typed `any`; lowered after the check, it is the
    arena's type (16 programs; IR identical).
  - Time (test_1M): checking alone is 5.2 s (8.6 s when it built the graph as it went), and
    lowering takes 4.7 s. Total build time is unchanged (29.4 s). Lowering is slower than the
    building it replaced; stage 4 changes what it builds.
  - What stage 2 found, for stages 3 and 4:
    - Lowering needed three more annotations: how a call is made (`Annotations.forms`), a
      literal statement that writes into the variable it names (`overrides`), and a method
      call whose receiver is built as a value first (`receivers`). It also needed the
      checker's order (`TC.events`).
    - What stage 1 expected to annotate needed no annotation: defers at each exit, arena
      marks, where a value is built, and widening at a use's type. The builder decides them
      from the annotated types, as it did for the checker.
- [x] 3. The readers onto the tree (2026-10-06)
  - [x] `ask at` (657fb64): an expression's type is its annotation, in each instance it is
        checked in, named as the compiler names types. Before, it was the first operation
        built at the expression's span that held a value, named only when it was a struct,
        enum, union or distinct type. So most expressions showed none; now each does. The
        goldens' one change: `verts[0]`'s index shows `untyped int`. `test/askat.mara` and
        four queries cover primitives, a generic's template and a field.
  - [x] Variables are their declarations (1f6b77c): `Annotations.vars`, recorded through
        `tc_bind`. The graph's declarations name their token (`Program_Graph.decl_tok`).
        The check agrees on 8006 declarations, 9138 once foreign params are counted
        (4824842).
  - [x] Def-use's variables from the annotations (4824842): a binding per annotated
        variable — its token, name, type and place the checker's — and a code's declaration
        finds its variable by its token. The goldens are unchanged.
  - [x] The call graph from the annotations (38983cb), and a function's call sites through
        it. Compared with the one read off the Calls edges before switching: the same
        functions, edges, first lines, purity and call sites in all 257 programs that build
        one.
  - Gates: the goldens (40 queries; one change, explained above), `annotcheck.sh`,
    `annotref` (343 programs identical), `irdiff.sh` (324 builds, and test_1M) and
    `graphdiff.sh` identical.
  - Time (test_1M): the build is ~3% slower. Lowering's declaration tokens cost about
    0.3 s, which goes when stage 4 removes the graph's declarations. Building the call
    graph's lookup tables costs about 0.2 s.
  - What stage 3 found, for stage 4:
    - Readers now touch the graph only for the operations: a function's runs, the locals
      its code names (the synthetic ones are seen through), statements and their kinds, a
      call operation's callee and arguments. These are what stage 4 keeps per function. A
      function's code is still found by `scope_node`, and a variable operation's local by
      `refers` → `decl_tok`.
    - A union match's arms that rebind their subject all declare it with the subject's
      token, each at its own payload type. One token, several variables: a variable is a
      token and a type.
    - A variable a destructure or a loop's element declares at a distinct type is that
      type in the annotations; the graph holds its base type.
    - The call graph feeds escape analysis, so it is the compiler's as much as `ask`'s.
- [x] 4. What's left of the graph (2026-10-07)
  - [x] Calls and Runs edges are columns (d538f78): a call's callee is the fun or struct
        itself, a run-defer's block a node of its code. An edge is a Then edge; the
        incoming-edge index goes.
  - [x] Names by their tokens (1ca94f9, 0794c20): lowering says which declaration each
        name refers to, by the token its annotation names; the builder keeps only the
        declarations of the code being built, by token. Its name stack goes, and so does
        resolving what no code declares by its text: that was the compiler's
        `this_program` and `context`, which lowering now names, and module and type names
        a field access reads through, which it no longer builds.
  - [x] No program-level declarations (052fcfa): modules, imports, type definitions,
        dispatch groups, unions, enums and their variants, foreign funs and module
        variables stop being nodes. What stays at the program level is code: each fun's,
        each struct's constructor's, each constant's.
  - [x] A code per function (8054ac9, 86ceef0, 037407e, 936241c). A constant's use names
        the constant (by its value's node), not its declaration; a body's definitions are
        codes of their own, after it. `Program_Code` holds each fun's, struct's
        constructor's and constant's code, ids its own from 0; the compiler's two globals
        get nodes past a code's root. What the program has once — tables, fold errors,
        which funs consume a param, unreachable statements — is `Program_Code`'s.
        Codegen, escape analysis, the flow checks, folding, def-use, the slices and the
        annotation check read one code at a time; a def-use use is a function and an
        operation (`Du_Use`). Canonicalization lays each code out in a graph of its own
        as it renumbers.
  - [x] A node's callee, declaring token and constant are columns (1680011), copied with
        the rest of it as its code is laid out.
  - [ ] 5. Locals as a table of their own — decided against. A code's params, results,
        locals and blocks are already the code's own rows: a local is named by its token
        (`decl_tok`; a synthetic one has none), nothing resolves a name through them, and
        no code holds another's. Moving them to a table apart from the operations stores
        the same columns in a second id space, which codegen's values, def-use's bindings
        and escape analysis's places would all have to cross (some 30 sites read a
        declaration as a node, besides every value kept by node), for no speed.
        The blocks stay in any case: escape analysis reads a value's lifetime off how many
        blocks are around it, so a function's blocks nest — that much of a scope tree is
        the function's.
  - Gates at every commit: `irdiff.sh` identical (324 builds, and test_1M's 106 modules and
    its run), the goldens (40 queries, unchanged), `annotcheck.sh` (8006 declarations) and
    `run.sh`. `graphdiff.sh` identical at steps 1 and 2; after that it differs only by
    what each step removed or renamed, as each commit explains.
  - Time (test_1M): within ~1% of before the codes split (graph 4.6 s against 4.1 s, lower
    4.3 s against 4.6 s). Splitting cost up to 1.7 s at first; laying each code out
    directly and making the per-node maps columns took it back. graph.odin is 4204 lines
    (4277 before the stage).
  - What stage 4 found, for what comes after:
    - The builder still builds every code into one graph in the checker's order, a
      body's definitions and its constants built in the middle of it, and segments and
      canonicalization put each code together. Building one code at a time — what the
      end state above asks — removes both; it changes the order nodes are built in, so
      `graphdiff.sh` stops being a gate for it and `irdiff.sh` carries it alone.
    - A graph dump of a constant's use printed `constant=?` from the split until the
      columns change: the dump looked up a table only the builder had.
