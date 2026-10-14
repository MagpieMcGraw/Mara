# Name resolution

Decided with the user (2026-10-13): names are resolved by a pass of their own over the tree,
before checking. Its result is what each name refers to, kept in the annotations; the scope
it walks with is a stack, thrown away once the pass is done. The checker reads the result.
`Type_Scope` stops being an environment and keeps only what the checker finds about a
declaration. This doc is the plan; its checklist is at the end.

## Why

`Type_Scope` is two things in one structure:

- **An environment**: a chain of name tables (`parent_scope`, `types`, `functions`, `refs`,
  `includes`), one per module, file, struct, fun and block, that the checker looks names up
  in as it checks.
- **A declaration's record**: what the checker finds about a fun or a struct — its flat name,
  its signature, its fields' types, its instance's arguments — and, beside that, copies of
  what the tree says of it (its name's text, its span, `#packed`, `#expose`, …).

The environment half is the tree again, in a second structure: every block of the tree has a
scope object, and the declarations it holds are the tree's statements. Pulling only the copied
fields out would leave two systems; the user's call is to remove the environment instead.
(Scopes as a structure may come back in mara3.)

## Scopes, unified

Mara has one kind of scope. A module is its files' text in one scope; a file is a scope for
what it uses; a struct's body, a fun's body and a block are scopes. The rules don't change
with the kind:

- **Definitions** (`name :: …`: a fun, a struct, a union, an enum, a distinct type, an alias,
  a constant) are seen throughout the scope they are written in and every scope inside it,
  nested funs and structs included, whatever their order. A file's definitions are its
  module's.
- **Variables** (a param, a named result, a `:=`, a loop's variable, a match arm's binding, a
  `let`) are seen from their declaration to the end of their scope, and in the blocks inside
  it — never in a nested fun or struct. A module's variables are no different: no fun sees
  them.
- **Uses**: `use m` makes m's definitions seen in the scope it is written in (a file's: that
  file); `include m` makes them seen in the whole module too (not by its users: a use brings
  in a module's own definitions only). `name :: use m` names the module, in the file.
- **Lookup** goes from the innermost scope out: a variable seen there, else a definition;
  only when none is found, what the uses bring in, from the nearest scope that has it — two
  different ones there is ambiguous.

What a name means by its type is not resolution: a field or method (`x.f`), a variant against
the type expected (`.Red`, a bare `Red` where a `Color` goes), a dispatch's or an operator's
member, a literal's field names. The checker finds those in the type's declaration, as now.

## The resolver

- **Input**: the build's tree — every module's files, parsed — and its modules' names.
- **The stack**: the names in sight, innermost last, and a mark where each scope starts; a
  name's entries by name, for lookup without a scan. A scope's definitions are pushed when it
  is entered, its variables as they are declared; leaving it pops back to its mark. Crossing
  into a fun or a struct hides the variables below.
- **Output**: for each name node, its `Ref` (the declaring token, the kind) in the
  annotations' instance 0. A generic's body is resolved once: its names mean the same in every
  instance; only its type params' bindings differ, and those are the checker's.
- **Errors** it can tell alone: a name with no declaration (save what the checker finds by
  type), an ambiguous use, a variable shadowing one in sight, a fun reaching for an outer
  variable.

## Stages

1. **The resolver, checked against the checker.** `resolve.odin` resolves every name it can
   without types; `MARA_RESOLVE=check` compares each with the ref the checker recorded and
   reports each disagreement — the rules above made to match what the checker does, case by
   case, or a checker bug found. No behavior changes. Gate: no disagreements over the corpus;
   `irdiff.sh` identical.
2. **The checker reads the refs.** Its lookups — `scope_find`, `scope_lookup`,
   `scope_find_ref`, `resolve_with_ambiguity`, `resolve_type_name`, `fn_ambiguous_owners` —
   become the name's ref and a table from a declaring token to what the checker found for it
   (a fun's or a struct's scope, a type, a constant, a variable's type in the instance being
   checked). The resolver knows the name errors; the checker says them where it did (after
   what it knows by type: a variant by the type expected). Gate: `irdiff.sh` identical, the
   expected diagnostics (`run.sh`), `annotcheck.sh`, `ask.sh`.
3. **The environments go.** Block, file and module scopes; `parent_scope`, `includes`, the
   name maps; `TC_Scope`'s `env`. What stays of `Type_Scope` is the declaration's record, read
   by its token; what it copied of the tree is read from the tree. Completion and hittest ask
   the resolver what is in sight at a point (it walks the fun to it). Gate: as stage 2.
4. **Faster.** Each module's bodies resolved in parallel (the definitions in sight are read
   only); a generic's body once, not per instance.

## Stage 1, as found

The rules above, and what the checker does that they had to say (`test/resolvecheck.sh`):

- **Order**: a scope's definitions are pushed when it's entered (a module's from all its
  files, before any is walked); a declaration's value and type are resolved before its names
  are in sight. Builtin calls (`print`, `len`, the casts, …) are the builtin's before any
  definition of the name.
- **Type params**: a fun's or a struct's generics, a `$T` in a param's or a result's type,
  a generic union's params — and a struct's param of a type `$T` or a shape `~S`
  (`struct(item: $T)`: `item` is a type its methods name), a definition, not a variable.
- **`Self`**: the innermost struct or fun; in a signature, the one it is in.
- **A union match's arm** with no binding rebinds a subject that is a name: the variant's
  payload, declared by the subject's token.
- **Qualified names** (`A.B.C`, `m.f(…)`, `Color.Red`, `TTF.Glyph_Header`): the first part
  in sight, each next one a member — a module's definitions (else its enums' variants), a
  struct's own definitions, a union's or an error set's variants, a distinct type's or an
  alias's base's. A module's own name is no name in it: `pkg.X` inside pkg is its constant
  X, and only that (a module named as a fun it uses is the fun).
- **What the checker records otherwise, by design** (counted apart, not disagreements): a
  dispatch's call — the member its arguments chose, where the resolver has the dispatch; a
  variable named in a type (`size_of(x)`, `fn f`) or as a callee (`h(1)`, h holding a fun)
  — the declaration of what it holds; a type param — the declaration of the type it's bound
  to.
- **Left to the checker** (what a name means by a type): fields and methods of values,
  header fields (`.len`), variants by the type expected (`.Red`, a bare `Red`), a union's
  variant built by its params (`Rect(5)`).

Over the corpus's 252 programs with no errors: 120,789 names agree, none differ; 461 are a
dispatch's member, 87 what a variable holds; 22,754 only the checker resolves (all by type);
1,511 only the resolver (names the checker never reads: an uninstantiated generic's body, a
default's value).

## Stage 2, as found

What reading the refs took, beyond the lookups themselves:

- **Bindings** are by declaring token, dense (`k.bound`: a per-token index into `k.binds`). An
  instance binds its template's type params (the resolver lists each generic's:
  `type_params_of`) and gives its template's tokens back at its end; a dispatch's trial of a
  generic member binds them and gives them back. A union's variant is bound to its struct
  (`Shape.Rect`), an enum's variant to its enum (`m.Red`), a union's tag enum to its
  `union`'s token.
- **Registered when named**: a struct's or a fun's own definitions are registered when it's
  checked, or when one of them is named — by the owner the resolver records for each
  (`owners`), its own owner first.
- **Templates** are by declaring token (a union's too): two modules' generics of one name no
  longer share an entry (the first one's, before).
- **A fun's own definitions are its members** (`alpha.bump(7)`), as the checker had them.
- **Dispatch groups of one name join** across the modules in sight — a program's `add` and
  core's: what a call by that name chooses among is the module's own groups, then each module
  its file or its module uses (`resolve_dispatches`); an operator's, the groups its module's
  and those modules' `overload`s name (`resolve_overloads`). A group's members are what their
  tokens refer to where the group is written, not where it's called.
- **Errors** stay in the order they were said: the resolver records why a name failed (whose
  local it is, past a fun's boundary; which modules have it — `misses`) and what a
  declaration runs into (`clashes`); the checker says it once nothing it knows by type
  applies. Changed: a constant two modules in sight have lists those modules (its own first),
  not every module with one; a variable shadows a constant in sight, not any constant
  anywhere.
- **Left for stage 3**: the builtins, found by name in the root scope (`tc_ref_type`'s
  `.Builtin`); the scopes' own binds (`scope_bind`), a union's tag enum's by name included;
  type params bound into an instance's scope by name (`tc_type_param_decl`).

## Checklist

- [x] 1. The resolver, checked against the checker (2026-10-13)
- [x] 2. The checker reads the refs (2026-10-14)
  - [x] a. The resolver runs before the check, kept for it (`k.rs`; names written as tokens —
        a dispatch's members, an overload's — by token: `token_refs`) (2026-10-14)
  - [x] b. What each declaration means, beside the scopes: `k.bound` by declaring token, an
        instance's own given back at its end, a union arm's rebound subject after the arm;
        `MARA_RESOLVE=check` compares it at each lookup (78,936 agree, none differ). Its cost
        on test_1M: the resolver ~140 ms (a name's slot hashed once a push and a lookup), the
        bindings ~10 ms (dense by token: a map's inserts missed the cache, ~170 ms)
  - [x] c. The lookups read the ref and the binding, family by family, each gated: names,
        calls, writes, qualifiers (a517c6d); types (35b6b34); members and constants
        (4522524); dispatch groups and overloads (f4f7f7d); the rest (2026-10-14)
  - [x] d. The name errors: the resolver knows why a name failed and what a declaration runs
        into; the checker says it where it did (2026-10-14)
- [ ] 3. The environments go
- [ ] 4. Faster
