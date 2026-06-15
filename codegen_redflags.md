# Codegen architectural red flags

Running notes from working on storage routing (big-value stack/arena). The
codegen is older code (pre-8/8/8 in places); these are the structural smells
worth a deliberate cleanup, not one-off bugs.

## Storage routing (stack vs arena)

1. **Two parallel size systems.** The type checker has `checker_type_byte_size`
   (operates on `Type`); codegen has `struct_byte_size` / `elem_byte_size` /
   `ir_type_byte_size` (operate on IR type *strings*). They can drift, and the
   IR-string sizers re-parse `[N x T]` / `{...}` text. Codegen usually has the
   `Type` in hand (`assign.var_type`) and could just call the checker's sizer —
   which is now the single "Op 1" for routing.

2. **Threshold drift between stages.** [FIXED] The type-check guard routes on
   `routes_to_arena` = whole-struct bytes ≥ 1024 (header + backing). The
   plain-PA-decl codegen path gated on `total_bytes >= 1024` counting *backing
   only*. A PA with ~1000-byte backing is "big" to the guard (1000+24 ≥ 1024)
   but "small" to codegen → the guard forces an allocator that codegen then
   ignores, stack-allocating anyway. Fixed: both codegen PA paths now gate on
   `routes_to_arena(pa)`, the same predicate the guard uses.

3. **Scattered, inconsistent routing decisions.** [PARTLY FIXED] PA backing
   storage is allocated in two places — the plain decl path
   (`codegen_stmt.odin` ~385) and the byte-read path
   (`gen_partial_array_alloc_and_register`, `codegen_array.odin` ~2273). The
   latter *always* `alloca`'d regardless of size, so `arr : [..N]T = bytes[off]`
   (e.g. font loca staging, ~131 KB) put the whole backing on the stack. [FIXED]
   Both PA storage paths now call the one `emit_partial_array_storage` primitive
   (see #5) — single decision site, no drift.

4. **`context_enabled && size >= threshold` was the wrong gate.** [FIXED]
   Codegen used to route to the arena only when an allocator was declared; with
   none, a big value fell through to `alloca`. `emit_partial_array_storage` now
   routes on `routes_to_arena` alone — no `context_enabled`. The type-check
   guard (`check_storage_sizes`) is the primary gate (clean early error); for a
   path the guard doesn't reach (e.g. a comptime `#if` arm, which bypasses
   check_scope) `emit_arena_bump` fatals — the loud backstop — instead of
   silently stack-allocating. Verified both. (Extending the guard to `#if` arms
   so they too get the clean early error, rather than the codegen fatal, is a
   small follow-up — the guard's coverage, not the routing.)

## PA decl codegen shape

5. **The partial-array decl dispatch is a branchy maze.** [PARTLY FIXED]
   `codegen_stmt.odin` ~135–430 still forks across byte-read / slice-expr /
   init-value(string|ident|field) / reassign-existing / plain-decl, each gated
   on `get_slice` existence and subtle source-expression shape checks — that
   dispatch structure is unchanged (a larger refactor). But the duplicated,
   drift-prone part — the alloca-vs-arena storage decision — is now a single
   `emit_partial_array_storage(dst, pa, name, span)` primitive that the
   plain-decl path and the byte-read path both call. Header init still lives
   per-path (the two genuinely differ: plain-decl stamps ptr/len/cap then
   element-constructs; byte-read memsets then byte-fills + sets len).

## Other

6. **Multi-return aggregate slot emitted malformed IR.** [FIXED] `return big_pa, x`
   produced `%buf` typed `ptr` where a `{ i64, i64, ptr, [N x T] }` was expected
   (clang rejected it). Both sides were missing a partial-array case:
   `gen_return_tuple` fell through to a scalar `store {..} <ptr>`, and the
   destructure (`gen_multi_return_assign`) bound the slot as a `Scalar_Var` so
   indexing failed. Added PA cases mirroring the slice/fixed-array handling.

7. **`buf[i] = <int literal>` into a byte buffer wrote 8 bytes, not 1.**
   [FIXED — as a type error] A byte buffer's indexed write is a *reinterpret*
   write of `sizeof(value)` bytes (`buf[off] = some_u32` writes 4), so it's the
   value's width that decides the byte count. An untyped literal has no concrete
   width; the old path defaulted it to i64 and silently wrote 8 bytes (corrupting
   adjacent memory, or trapping near the buffer's end). Rather than *guess* a
   width, `check_index_assign` now rejects an untyped-number RHS into a byte
   buffer (`TYPE_BYTE_BUFFER_WRITE_UNTYPED`) and tells the user to cast — `u8(v)`
   for 1 byte, `u32(v)` for 4. Concrete-typed values carry their own width and
   are unaffected.
