# Mara

A programming language written in Odin.
The goal is a production ready compiler for under 50k lines.

## Building and running

The compiler:
odin build . -debug

Mara code:
mara build game    	# build module "game" from all .mara files with `module game`
mara build         	# build module matching current directory name

# Analyzer

Mara has a graph-based code analyzer that reveals the structure and data flow of
Mara programs — type dependencies and forward/backward program slices — from the
compiler itself.

```
mara ask                     # the cwd project: every module at a glance
mara ask name                # a type, function, or module — everything about it

# Two filter axes, composable, in any order:
mara ask name types          # only the type graph (fields / params / returns / embeds)
mara ask name flow           # only the data-flow slice (the "outside" view)
mara ask name above          # only the sources   (what it's built from / what feeds it)
mara ask name below          # only the consumers (what depends on it / what it feeds)
mara ask name types above    # filters combine — just the type sources
mara ask name 2              # a number is the type-graph depth (0 = direct edges only)

# `flow` is the "outside" view, consistent across subjects:
mara ask Type flow           # aggregate the slice over every value of that type
mara ask fn flow             # the call-site view: what feeds the args / where results go

# Slicing — address a variable, then it gets sliced (above = feeds it, below = it feeds):
mara ask var in fn           # a local or parameter inside a function
mara ask return in fn        # what feeds a function's return value (the inside view)
mara ask at file:line        # the variable defined at that exact spot (precise)

# Narrow where a name resolves:
mara ask name in module      # analyze a different discovered module
mara ask name in file        # resolve the name within one file
```

`types`/`flow` pick the graph, `above`/`below` the direction; omit either to get
both. Depth (a number) bounds the type graph only — slices are always full.

## Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.

# Surprise

I may make small edits to various files while you are working. Usually touching Mara code or my notes. I almost never touch the compiler code so a conflict there is unlilely. Don't worry about it.