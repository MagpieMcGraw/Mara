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

Mara has a graph based code analyzer that can reveal information about the structure of Mara programs. Eventually it will support forward and backward slice analysis.

mara ask			# gives info about cwd
mara ask name		# gives info about module or type or function or variable

You can pass a number to specify the depth
You can use "deps|user" to narrow the output
You can pass "in module" to narrow the output

## Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.

# Surprise

I may make small edits to various files while you are working. Usually touching Mara code or my notes. I almost never touch the compiler code so a conflict there is unlilely. Don't worry about it.