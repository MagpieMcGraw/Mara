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

### Its shape (stage 3)

- **What it keeps.** The type representation (`Type_Scope`, the `Type_*` variants, the symbol
  table) and everything of the old checker that never reads syntax: type equality and names,
  layout and sizes, numeric widening and the inference cells, environments (`type_env_*`), the
  graph builder's API. What reads syntax is new: registration, type resolution, statements,
  expressions, calls, the builder calls, generic instances.
- **Files and names.** `tc_*.odin`, procs prefixed `tc_` while both checkers exist (renamed
  plainly at the switch). `MARA_CHECKER=new` runs it in place of the old one.
- **One walk per body.** A module's definitions are registered from its statements as written;
  a body is checked once per instance, its statements in order, building its graph as it goes
  (the builder's fusion calls, unchanged). What it finds about a node — its type, what a name
  resolved to, a call's callee — is in arrays over the body's node range, made for the
  instance and dropped once its graph is built.
- **Generics.** An instance is its template's body range and its bindings (the type params'
  types, in the instance's env): the same nodes checked again, with fresh arrays. Nothing is
  cloned, so there are no fresh ids and no instance copies to keep apart.
- **The builder's keys.** The builder keys statements and expressions by an id of either
  tree's (`Syntax_Id`): the old checker passes its `Stmt_Id` / `Expr_Id`, the new its node ids.
- **A struct's fields are its body's.** A struct's body is its constructor, checked once —
  first, or sooner by whatever needs its fields — and each field declaration's type is what
  checking it finds: its annotation, else its value's (a width its uses leave open settles at
  the end, as a local's does). The old checker guessed field types from their defaults in a
  pass of their own before the body was checked; that pass has no counterpart.
- **Generics without clones.** An instance is its template's own nodes checked again with
  its type params bound, its graph its own; the old checker cloned the body per instance.
  Two behaviors of the clones are kept for identical IR until the switch: an instance's
  compound assignment walks its target again (the clone's operation held a copy of it),
  and an instance's scope chains to its call site's (as the clone's did).
- **Genericity read off the tree.** The old parser lowered `$T` in a signature and a
  struct's shape or size params into generic params; the tree keeps them as written, and
  the checker reads a definition's type params off it (tc_generic.odin).
- **Explained differences.** A program the new checker builds differently for a reason
  (its answer the documented one, say) is listed in `test/tc_explained.txt` with why;
  tcdiff counts those apart from the matches.
- **Text from tokens.** What the old parser captured as text for later phases (an assert's
  condition and sides) is read from the tokens where it is needed.
- **Order.** Grown by what programs need, simplest first: functions over integers, locals,
  control flow, calls, print; then structs and fields, arrays and slices, text, constants,
  unions and match, defaults and constructors, generics, modules and imports, byte views,
  takes, the arena. Progress is the count of programs whose IR is the old checker's.

## The proof

- **The tree**: it loses nothing. For every file of the corpus, the tokens the tree accounts for
  — walked in order through its nodes' extents and the tokens each form spells — are the file's
  tokens (newlines aside). Checked on every build under `MARA_TREE=check`; `MARA_TREE=dump`
  prints it.
- **The checker**: the old checker is the oracle for what the program means, not for how the
  graph is built (decided 2026-09-30: take the architectural wins). Under `MARA_CHECKER=new` the
  new checker runs instead, and the two builds of every fixture, multi-file fixture, Pounce,
  `design/all` and test_1M must agree on the IR (byte-identical, or modulo naming with each
  difference explained), on what the programs print when run, and on the diagnostics — then
  the suite and the ask corpus as ever. Their graphs are compared too, and each difference is
  either gone or explained: a simpler construction may build a different graph for the same
  program. Progress is counted in programs whose IR is the old checker's.

## Stages

1. **The builder off the tree.** `graph.odin` takes what it takes from statements (a span, a
   kind, an id, a scope's declaration) as data from its caller, not as `Stmt` / `^Stmt_Scope`;
   `Type_Scope`'s back-references to its declaring statement and a param's default expression
   become ids the checker resolves. After it, only the parser, the checker, hittest and the
   parse dump touch the pointer tree. Gate: everything identical.
2. **The flat tree** beside the pointer tree: a new parser over the same tokens, the views, the
   dump, the no-token-lost check on every build.
3. **The new checker** beside the old, behind `MARA_CHECKER=new`, grown construct by construct
   until every program's IR, runs and diagnostics are the old checker's.
4. **The switch**: the new checker is the checker; hittest moves onto the flat tree; the old
   parser, the pointer tree, the old checker and the clones are deleted.

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
- [x] 2. The flat tree beside the pointer tree (2026-09-30, 989f54f). `tree.odin`: the table
      (`Tree_Id`; tag, report point, extent, `a`, `b`; lists and records in `extra`), each
      tag's shape (what its fields hold: a child, a list, a token, a token list, a record),
      so children, tokens, the dump and the check are one walk over any node; views for the
      forms of more than two fields. `tree_parser.odin`: the old grammar, lookaheads and all,
      recorded as written; report points the old parser's. `MARA_TREE=dump` prints it,
      `MARA_TREE=check` checks it — each node inside its parent and after its elder
      sibling, every token that says something (a name, a literal, an operator, a
      directive) recorded by a node, and a file one parser rejects rejected by the other.
      `test/treecheck.sh`: all 301 programs lose nothing; test_1M is 5.1M nodes and 6.3M
      words of lists and records, 0 problems. hittest moves at the switch (stage 4): its
      labels change with the tree, and the point-query corpus stays a fixed gate through
      stage 3.
- [x] 3. The new checker: every program's IR, runs and diagnostics identical
  - [x] Scaffolding (2026-09-30: d83ff08, e916025): `MARA_CHECKER=new`, the builder keyed
        by `Syntax_Id`, `test/tcdiff.sh` — every program built by both checkers, a program
        matching when its diagnostics, IR and run do; the matches are recorded in
        `test/tc_match.txt` and a lost one fails the run. Any form not yet checked is an
        error saying so (`tc: … is not supported yet`), so a program fails visibly rather
        than differently.
  - [x] Functions over integers, locals, control flow, calls, print (e3f8af0, 45b1397)
  - [x] Structs, fields, arrays, slices, text, constants
  - [x] Unions and match, defaults and constructors
  - [x] Generics, modules and imports — generic funs, structs and unions
  - [x] Byte views, takes, the arena, the rest
  - Done (2026-10-01, 1bb6cf2): 286 of 288 programs match — byte-identical IR, the same
    diagnostics, the same runs — and the other 2 differ as explained
    (`test/tc_explained.txt`), awaiting a ruling. Forms the tree keeps as written and the
    old parser lowered are given that meaning in the checker: `&x.f()` (f's receiver
    addressed), `x in lo..hi`, `[]T(n)`, the shape shortcut, `#expose`, param tuple
    defaults. Old-checker quirks mirrored for parity, to revisit after the switch: a
    fun's name is a value only when it has params; a broadcast declaration's copies drop
    its annotation; field-broadcast and `using` errors are said at the struct.
- [ ] 4. The switch
