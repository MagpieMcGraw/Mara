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
  file); `include m` makes them the module's too, and its users'. `name :: use m` names the
  module, in the file.
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
   checked). The resolver reports the name errors. Gate: `irdiff.sh` identical, the expected
   diagnostics (`run.sh`), `annotcheck.sh`, `ask.sh`.
3. **The environments go.** Block, file and module scopes; `parent_scope`, `includes`, the
   name maps; `TC_Scope`'s `env`. What stays of `Type_Scope` is the declaration's record, read
   by its token; what it copied of the tree is read from the tree. Completion and hittest ask
   the resolver what is in sight at a point (it walks the fun to it). Gate: as stage 2.
4. **Faster.** Each module's bodies resolved in parallel (the definitions in sight are read
   only); a generic's body once, not per instance.

## Checklist

- [ ] 1. The resolver, checked against the checker
- [ ] 2. The checker reads the refs
- [ ] 3. The environments go
- [ ] 4. Faster
