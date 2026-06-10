# Mara

A programming language written in Odin.

## Building and running

The compiler:
odin build . -debug

Mara code:
mara build game       # build module "game" from all .mara files with `module game`
mara build            # build module matching current directory name

## Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.