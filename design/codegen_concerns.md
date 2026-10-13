# What code generation decides that it shouldn't

Found while writing the x86 backend (2026-10-13). Code generation —
`llvm.odin` and the emit helpers in `codegen*.odin` — should only say how each
operation of the lowered program is done on the machine. In places it still
decides what the program means: questions the checker, lowering or storage
should have answered. The x86 backend doesn't repeat any of it (it reads the
instructions those decisions produced), but any other consumer of the lowered
program would have to, and each one is a place where the lowered program
doesn't say everything about the program.

Each item names where it is (function, as of commit 8342517) and where it
belongs.

## Lowering's decisions, made late

- **What `void` does depends on the statement.** `llvm_write_void` asks
  `graph_stmt(pg, op).kind == .Decl`: a declaration's `x : T = void` zeroes a
  scalar and stamps a partial array's header; an assignment's `x = void` keeps
  the bytes. Lowering knows which it built — it could emit the operation that
  means each (a zero, a header stamp, nothing).
- **Where a take's header is built depends on the statement too.**
  `llvm_carve_header` builds `slice([:n]T, s)`'s header in the declared
  variable when the write is a declaration (or the result slot), else in a
  temporary. That's a storage fact, like `storage_calls`' places for call
  results.
- **Whether a union literal writes its fields** is found by scanning the rest
  of the run (`llvm_variant_written`, for a niche union's null). Lowering
  builds the literal; it knows.
- **"In range by construction" is implicit.** An index skips its bounds check
  when `pg.written[op] == .Synthetic` (`llvm_op`'s `.Index`,
  `llvm_slice_index`): a loop's element index is in range because lowering
  made it. That's a contract between two stages carried by an unrelated flag;
  it should be an explicit fact (a checked/unchecked index, or the check as its
  own operation).

## Representation chosen from the next operation

Several operations look at their one user (`e.st.user[op]`) to decide how
they're built — decisions about where values live, which is storage's job:

- `.Swizzle`: several components written are the array itself; read, they're
  gathered into a temporary.
- `llvm_slice_op`: a slice written to is the run of elements the write fills;
  a whole fixed array only copied from is the array, no header; a whole array
  viewed into a slice's place gets its header built there; a slice written to a
  held view becomes header values.
- `llvm_view`: a positional slice carve takes its own run of the bytes; a
  partial array in bytes bound by `let` is the memory, copied out whole it
  keeps its bytes' header.
- `.Read` of a big-endian view: only a write may consume it.

## The runtime checks are chosen and worded here

Every runtime check — which ones an operation has, when one can be skipped,
and the message it prints — is decided in code generation: bounds
(`emit_bounds_check`), overflow (`emit_checked_arith`), division by zero,
slice len (`emit_slice_len_check`), byte spans and reads (`llvm_view`,
`llvm_copy_into`, `llvm_byte_read`, `llvm_sized_read`), takes (`llvm_carve`),
`cstring` (`emit_cstring_check`), a match on a bad tag. There are 12
`emit_fail` sites in `llvm.odin` alone, plus the `RUNTIME_FAILS` helpers.
These are the language's semantics; lowering could make each check an
operation of its own (`check index < len`, with its message), and code
generation would only compare and branch.

## Type questions answered by refusing

Some mismatches surface as code generation refusing a function ("can't
lower"), not as the checker's error or lowering's conversion:

- `.Address` of a place taken as a pointer to another type — a view of bytes
  (`llvm_op`).
- `.Write` of a non-byte value into bytes, or bytes into another type's place,
  outside the byte-view forms (`llvm_op`'s `.Write`).
- `llvm_same_type` mismatches in `llvm_operand` generally.

Either the checker rejects these or lowering makes the conversion explicit
(a `View`).

## Special cases by name

- The program's struct is skipped by name in a constructor
  (`llvm_variables`: `e.g.checked.table.funs["Program"]`), and `this_program`
  is recognized by `storage_this_program` in `.Var`.

## Semantics that live only in code generation

- **Printing.** How each type prints — numbers, floats, text, slices,
  structs, enums, errs, the `%` placeholders — is `codegen_print.odin`
  (~780 lines) and `llvm_print`. It's the language's `print`; it could be
  lowered to a few primitive print operations, or be a runtime library.
- **Text constants have no header.** `llvm_text` special-cases text
  throughout: indexing it, slicing it, casting it to a slice, passing it for a
  partial-array param (a header made on the spot), printing it, `cstring` of
  it. One representation decision, made a dozen times; lowering could give
  text one form.
- **Partial arrays point into themselves.** A copy re-points their headers
  (`reanchor_partial_arrays`, `fixup_partial_array_fields`,
  `stamp_zero_partial_arrays`); every aggregate copy has to remember. That's
  layout semantics; it could be part of what a copy operation means in the
  lowered program.

## Where they'd go

Most of these become facts the lowered program carries (storage facts, or
explicit operations: checks, header stamps, conversions) — then a backend
reads them and decides nothing, as the x86 backend already doesn't.
