# Mara

A programming language written in Odin.
The goal is a production ready compiler for under 50k lines.

## Building and running

The compiler:
odin build . -debug

Mara code:
mara build game    	# build module "game" from all .mara files with `module game`
mara build         	# build module matching current directory name

## Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.

# Surprise

I may make small edits to various files while you are working. Usually touching Mara code or my notes. I almost never touch the compiler code so a conflict there is unlilely. Don't worry about it.

# Reference

Old odin game project can be found at C:\Users\magpie\Desktop\Warlock Odin

# Analyzer (`mara ask`)

A graph-based code analyzer that reveals the structure and data flow of Mara
programs — from the compiler itself. Full write-up in `design/mara_ask.txt`
(this spec + matrix) and `design/mara_ask.md` (rationale, algorithms, limits).

## Basic usage

```
mara ask                # info about the modules in cwd
mara ask name           # info about a symbol — a module, struct, function, or variable;
                        # with no filters, a general overview of name
```

Every query has two axes — **3 kinds of analysis** (`types`, `call`, `flow`) and
**2 directions** (`above`, `below`). Omitting a kind widens to all that apply;
omitting a direction gives both. What each direction means, per kind:

```
types  above  — what I contain / what I need to be constructed
       below  — who contains me, after I'm constructed
call   above  — function calls that supply me
       below  — function calls that I supply
flow   above  — the tree of variables that supply me, across function calls
       below  — the tree of variables that I supply, across function calls
```

## Other arguments

```
mara ask name 2              # number — limit analysis depth (default: infinite)
mara ask var in fn           # query a specific variable or struct field
mara ask at file:line        # query the variable defined at that spot (note: `at`, not `in`)
mara ask return in fn        # what feeds a function's return value (the inside view)
mara ask name in module      # narrow where name resolves (also `in file`); scopes compose
mara ask var in fn flow above control   # `control` adds control-dependence (see below)
```

## The matrix — subject × kind × direction

```
module type above   # structs this module imports and uses
module type below   # structs defined in this module, imported and used elsewhere
struct type above   # structs that are fields of this struct
struct type below   # structs that this struct is a field of
fun    type above   # the type analysis of this function's arguments
fun    type below   # the type analysis of this function's return values
var    type above   # run `type above` on the type of var
var    type below   # run `type below` on the type of var

module call above   # functions this module imports and calls
module call below   # functions defined in this module, imported and called elsewhere
struct call above   # functions that need to be called to make this struct
struct call below   # functions that take this struct as an arg
fun    call above   # functions called by this function
fun    call below   # functions that call this function, and dispatch blocks
var    call above   # function calls which supply this variable
var    call below   # function calls this variable supplies

var    flow above   # chain of variables and operations that supply this variable
var    flow below   # chain of variables and operations that this variable supplies
fun    flow above   # `flow above` on all call sites of this function
fun    flow below   # `flow below` on all call sites of this function
struct flow above   # `flow above` on all fields of all instances of this struct
struct flow below   # `flow below` on all fields of all instances of this struct
module flow above   # `flow above` on all instances of everything in the module
module flow below   # `flow below` on all instances of everything in the module
```

## Spec vs. actual (2026-06-23)

What the tool does today, and where it diverges from the matrix above.

**Implemented (matches the matrix):**
- `struct` / `fun` / `var` × `type` / `call` / `flow` × `above` / `below` — all live.
- `fun type`: above = parameter types, below = return types.
- `fun call`: above = callees, below = callers (off the materialized call graph).
- `struct call`: below = fns that take it, above = fns that return it.
- `struct type below`: now ONLY structs that contain/embed it — fns that take/return it moved to `call`.
- `var type`: the type graph of the variable's own type.
- `var call`: above = calls that supply it, below = calls it supplies.

**Deferred (not built):**
- All MODULE-level analysis. `mara ask <module>` shows the module SURFACE
  (declared types ranked by user-count, plus funs), not the above/below
  analyses; a kind/dir filter on a module is currently ignored.

**Divergences from the matrix:**
- `var flow above` is the LINEAGE tree (producer tree, following the calls that
  build the value). This folded in what was a separate `lineage` verb — the
  `lineage`/`source` keyword is **retired**. (`flow below` = forward slice.)
- A bare `<var> in <fn>` (no kind) shows FLOW only — a variable's natural view;
  `types`/`call` on a variable are explicit opt-ins. A bare `<fn>` or `<struct>`
  still shows all three kinds.
- `struct call above` = functions that RETURN the struct by value (factories). It
  does NOT include the auto-generated constructor, and is not yet a true "what
  builds this value" producer analysis.

**Extra (beyond the matrix):**
- `control` — a FLAG (not a kind) that adds control dependence (the branches/loops
  a value drives, or that guard what feeds it) to a flow slice. Off by default: it
  needs the slow post-dominator pass.
- `in <module>` / `in <file>` scopes; two `in` scopes compose (`<var> in <fn> in
  <module>`, any order). Every `in` NARROWS where the name resolves over a fixed
  root — the cwd program (cwd + the stdlib it uses); it never re-roots. A module
  on disk but not pulled in by the cwd project isn't part of the program (plain
  not-found, no fallback).
- `return in <fn>` — slices what feeds a function's return (the inside view).