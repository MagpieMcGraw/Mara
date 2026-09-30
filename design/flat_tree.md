# The flat syntax tree and the checker rewritten on it

Decided with the user (2026-09-30): the syntax tree goes Zig-style — every node the same shape
in a few flat arrays, lists and larger payloads in one side array — and the type checker is
rewritten on it rather than converted. This doc is the plan; its checklist is at the end.

## Why

Cache locality is the smallest part. The rest:

- **Identity is the index.** A node's id is its place in the table: no `new_expr` discipline,
  no `expr_id` / `stmt_id` / `expr_span` switches, no "made without an id" failure.
- **One shape, so generic operations are one proc each.** Children, extents, a dump, a diff, a
  copy, a hash. hittest's per-kind walk, the parse dump and the clones collapse.
- **Nothing to write through.** The tree is built once and only read — the rule phase 4 reached
  by deleting fields is the tree's natural state.
- **It serializes.** No pointers: a module's tree can be written and read back (caching,
  position-independent compilation).
- **Generics without clones.** Zig analyzes one body once per instantiation and keeps the
  results per instance. Mara clones the body per instance today (`clone_expr`/`clone_stmt`,
  fresh ids, and the bugs that came with them: nested funs in generic funs, methods on generic
  structs). With a flat tree an instance is its template's body and its bindings; what the
  checker finds about a node is kept per body it checks.

What it costs: code about one kind of node reads through a decoder (`v.left` becomes a view's
field), and a child is a bare id — distinct id types keep an expression from passing for a
type. The checker's 16k lines touch every such read, which is why the checker is rewritten on
the new tree, not converted.

## The tree

One tree for the build, like the token table: every file's nodes in it, a node's id its index.

```odin
Node_Id  :: distinct u32   // 0 is no node: an absent optional child
Node_Tag :: enum u8 { ... } // one per syntactic form

Tree :: struct {
    tag:   [dynamic]Node_Tag,
    main:  [dynamic]Token_Id,   // the report point (a binary's operator, a call's name)
    first: [dynamic]Token_Id,   // the extent: first token ...
    end:   [dynamic]Token_Id,   // ... and one past the last
    a, b:  [dynamic]u32,        // per tag: a child, a token, a list, a small value
    extra: [dynamic]u32,        // lists and the records of nodes with more than two fields
    files: [dynamic]Node_Id,    // each file's root (its statements)
}
```

- **A list** is an index into `extra` holding its count, then its ids. A node with one list
  keeps it in `a` or `b`; one with more keeps a record in `extra` (its lists, its optional
  children, its tokens), which its view decodes.
- **Names are tokens.** An identifier, a field, a fun's name is a token id; its text is
  `token_text`. The tree holds no strings.
- **Literals are tokens.** A number's value is parsed from its token when asked, a string's is
  the lexer's decoded value.
- **Views** decode a node into a plain struct, one proc per form (`fun_view(t, id)` →
  `{name, generic_params, params, returns, body, directives}`), lists as `[]Node_Id` slices into
  `extra`. Code about a form reads its view; code about any node reads the columns.
- **Types are nodes** in the same table, with their own tags (`[N]T`, `^T`, `[]T`, `[..N]T`,
  `Name(args)`, `fun(...) -> ...`).
- **Source-faithful.** The parser desugars nothing: `x += 1` is a compound assignment, `x := 1`
  a declaration, `-3` a negation of `3`, a scope's definitions stay where they are written,
  `#if` stays a node, a destructure's defaults are not synthesized. What the old parser lowered
  the new checker reads as written.
- **A body is a range.** Nodes are appended as they are parsed (a parent reserved before its
  children), so a fun's subtree is a contiguous range of ids — which is what lets the checker
  keep what it finds about a body in arrays over that range, one per instance.

## The checker on it

The new checker produces what the old one does: the symbol table, the `Type_Scope`s and other
types, the program graph (built as it checks, through the same builder calls), the diagnostics.
It keeps the type representation and replaces the checking.

- What it finds about a node — its type, what a name resolved to, a call's callee — lives in
  arrays over the body being checked, made per instance and dropped once the body is built
  into the graph. Nothing is cloned.
- It walks the source forms directly, so the old lowerings (`Decl_Lowered`, `Call_Lowered`, the
  broadcast copies, the dot-refs) are not rebuilt; each form is checked as written.
- Its budget is its own: the old checker grew in layers (two passes, registration pre-passes,
  lowered forms) that the new one has no reason to repeat.

## The proof

- **The tree**: it loses nothing. For every file of the corpus, the tokens the tree accounts for
  — walked in order through its nodes' extents and the tokens each form spells — are the file's
  tokens (newlines aside). Checked on every build under `MARA_TREE=check`; `MARA_TREE=dump`
  prints it.
- **The checker**: the old checker is the oracle. Under `MARA_CHECKER=new` the new checker runs
  instead, and graphdiff compares the two programs' graphs — dumps identical, diagnostics
  identical — on every fixture, the multi-file fixtures, Pounce, `design/all` and test_1M; then
  irdiff, the suite and the ask corpus as ever. Progress is counted in programs whose graph is
  identical, as phase 3 counted declines.

## Stages

1. **The builder off the tree.** `graph.odin` takes what it takes from statements (a span, a
   kind, an id, a scope's declaration) as data from its caller, not as `Stmt` / `^Stmt_Scope`;
   `Type_Scope`'s back-references to its declaring statement and a param's default expression
   become ids the checker resolves. After it, only the parser, the checker, hittest and the
   parse dump touch the pointer tree. Gate: everything identical.
2. **The flat tree** beside the pointer tree: a new parser over the same tokens, the views, the
   dump, the no-token-lost check on every build. hittest moves onto it.
3. **The new checker** beside the old, behind `MARA_CHECKER=new`, grown construct by construct
   until every program's graph is the old checker's.
4. **The switch**: the new checker is the checker; the old parser, the pointer tree, the old
   checker and the clones are deleted.

## Checklist

- [x] 1. The builder off the tree (2026-09-30: 2b1df66, ae368f6, 6e2703e). What the builder
      took from statements and expressions it takes as data: a construct's span and the few
      facts it reads (`Graph_Loop`, `Graph_Arm`'s else and union, a literal's name and
      zero-init, an assert's text and sides, a take's keyword, a destructure's names and
      stores); what a statement outside any body declares (`Graph_Decl`: id, span, kind, form
      — names, an import, a constant, a scope, a block, a group, foreign funs, a union, a
      type, a dispatch — made by the checker, `stmt_graph_decl`); a named constant
      (`Graph_Named`: its value's id, or its value known) and the table's constant names by
      id. The passes after checking ask the checker what they asked of the tree
      (`scope_is_written`, `scope_is_intrinsic`, `scope_body_is_empty`, `field_has_default`,
      `distinct_is_sized`), and the checker checks a param's `void` default itself
      (`check_void_defaults`). The builder's keys are still the old tree's ids (`Stmt_Id`,
      `Expr_Id`); the new checker's are its node ids. Left on the pointer tree: the parser,
      the checker, hittest, the parse dump and the driver's has-`main` / has-`#expose` tests.
      Graph, IR and `mara ask` identical. (An empty body skipping missing-return is on
      purpose: `Arena`'s empty methods declare the shape a `~Arena` param matches.)
- [ ] 2. The flat tree beside the pointer tree
- [ ] 3. The new checker: every program's graph identical
- [ ] 4. The switch
