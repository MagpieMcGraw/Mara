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
   (e.g. font loca staging, ~131 KB) put the whole backing on the stack. Both
   now route on `routes_to_arena`, BUT they're still two separate copies of the
   "alloca-or-arena + header init" logic. A single
   `emit_partial_array_storage(name, pa, span) -> ptr` would dedupe them.

4. **`context_enabled && size >= threshold` is the wrong gate.** [REMAINING]
   Codegen still only routes to the arena when an allocator is declared; with
   none, a big value falls through to `alloca`. The type-check guard
   (`check_storage_sizes`) now catches that at compile time for the common
   cases, so it's no longer the silent-overflow bug it was — but a big value in
   a path the guard doesn't reach (e.g. a comptime `#if` arm, which bypasses
   check_scope) would still silently stack-alloc. Cleaner end state: drop
   `context_enabled` and route on size alone — `emit_arena_bump` already fatals
   when no allocator is wired, the correct loud backstop. Deferred (adds new
   fatal paths; wanted to keep this change low-risk).

## PA decl codegen shape

5. **The partial-array decl dispatch is a branchy maze.**
   `codegen_stmt.odin` ~135–430 forks across byte-read / slice-expr /
   init-value(string|ident|field) / reassign-existing / plain-decl, each gated
   on `get_slice` existence and subtle source-expression shape checks. It's hard
   to be sure which branch a given decl takes, and storage allocation + header
   init are duplicated across several of them. A single
   `emit_partial_array_storage(name, pa) -> ptr` (alloca-or-arena, header init)
   would centralize it.

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
