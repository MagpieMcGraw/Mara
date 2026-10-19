# Mara memory-safety probes (commit 864b2ce, Linux)

Each file is its own module: put it in a folder of the same name and `mara build`.

## bugs/ — compile, then misbehave at runtime
- unionswap, unionswap2, unionloop: a union given another variant while a match arm's binding views it; the binding reads a forged pointer (segfault at 0x41414141...).
- pastcap, oobwrite: `xs[a:b]` slice ends not checked against the capacity; out-of-bounds read, and a write that overwrites a neighbouring variable.
- negslice: `xs[3:1]` makes a slice of len -2 (indexing it is caught; the slice should not exist).
- forgeptr, byteptr: `let(^i64, ...)` and a byte read into `^i64` turn arbitrary bytes into a pointer.
- forgeslice: byte writes over storage that slice() carved a []i64 view from; the view's len becomes huge, so its bounds checks pass for any index.
- shift, ftoi, minover, poison: unchecked `<<` past the width or negative, float-to-int out of range (LLVM poison), and i64 min / -1 (hardware trap). poison takes a number argument: `./poison 64`.

## compiler_errors/ — internal errors on valid-looking code
- literalview: `&views + [1, 2, 3][:]` — "can't lower 'main' ... its local 'temp'".
- let_call_index: `let(i64, &storage[pick(12)])` — "a take from no plain place".

## held/ — attacks that were correctly rejected or caught
Escape through callbacks, by-value params, generics, methods, dispatch, next(), appends, match bindings, multi-value and list returns, `with` blocks, captures; defer vs arena reset; big returns; index, byte-view and let bounds; division by zero; invalid enum index.
