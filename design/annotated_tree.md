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
annotations alone, is the one the checker builds today (`test/graphdiff.sh`).

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
- [ ] 2. Lowering out of the checker
- [ ] 3. The readers onto the tree
- [ ] 4. What's left of the graph
