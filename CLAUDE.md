# Mara

A programming language written in Odin.
The goal is a production ready compiler for under 50k lines.

# Building and running

The compiler's source is in src/; the exe goes in the repo root, beside code/, runtime/ and tools/.

The compiler (mara.exe, optimized — the one on the path):
odin build src -o:speed -out:mara.exe

Mara code:
mara build game    	# build module "game" from all .mara files with `module game`
mara build         	# build the module in the current directory. If there are several, tries to build the one named as the folder.

"build.mara" file can be used to provide command line arguments to mara build.

# Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

# Testing

We don't do any.

# Surprise

I may make small edits to various files while you are working. Usually touching Mara code or my notes. I almost never touch the compiler code so a conflict there is unlilely. Don't worry about it.

# Analyzer (`mara ask`)

It provides various data, including forward and backward slice. Use "mara ask help" for the full guide.