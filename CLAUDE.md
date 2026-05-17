# Mara

A programming language written in Odin.

## Building and running

```
odin build . -debug
```
Module build mode:
```
mara build game       # build module "game" from all .mara files with `module game`
mara build            # build module matching current directory name
```
## Workflow

Make a git commit before starting work.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder (e.g. `cd test && ../Mara.exe test.mara`) so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.