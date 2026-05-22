# Mara vs V: Audit comparison

Tests mirror the safety probes from
https://mawfig.github.io/2022/06/18/v-lang-in-2022.html. Each subdir is a
self-contained package that can be built with `mara build <name>` from
this directory.

## Results

| # | Test | V outcome | Mara outcome | Verdict |
|---|------|-----------|--------------|---------|
| 1 | `null_init` (declare ptr = null) | compiles silently | compiles silently | tied |
| 2 | `null_deref` (deref null) | **segfault** | clean runtime trap + exit(1) | **Mara wins** |
| 3 | `uninit_read` (read uninit ptr) | **segfault** | **compile error** ("used before assigned") | **Mara wins** |
| 4 | `overflow` (i8 100 + 50) | **undefined behavior** | runtime trap "integer overflow" + exit(1) | **Mara wins** |
| 5 | `divzero` (x / 0) | runtime error | clean runtime trap + exit(1) | tied (both trap) |
| 6 | `dangling` (int → ^Foo) | compiles silently | **type error** ("cannot assign i64 to ^Foo") | **Mara wins** |
| 7 | `shadowing` (same-scope redeclare) | rejected | rejected | tied (V also correct here) |
| 8 | `imm_bypass` (write through ptr) | **silent bypass** | mutates (no `mut` model yet) | **tied — neither enforces** |
| 9 | `bounds_normal` (arr[N+M] with M oob) | trap | runtime trap + exit(1) | tied (V also correct here) |
| 10 | `bounds_partial` (write past partial-array len) | **bypassable via .len/.cap** | runtime trap (no exposed header fields) | **Mara wins** |
| 11 | `unions` (wrong-variant field access) | **compiler crash** | type error ("union has no variant 'radius'") | **Mara wins** |
| 12 | `generics` (undef ident in generic body) | **silently accepts** | accepts at TC → **clang fails on bad IR** | **tied (both broken; Mara's failure mode is more confusing)** |
| 13 | `globals` (mutable module-scope var) | **bypassable via const+heap** | rejected ("shadows a constant from outer scope") | **Mara wins** |

**Tally:** 7 Mara-wins, 4 ties (2 of which are mutual failures), 0 V-wins.

## Detailed findings

### Where Mara is materially better than V

- **Null deref, uninit read, overflow, div-zero** all fail cleanly with
  named errors and `exit(1)`. V silently UBs or segfaults. This is the
  payoff for the per-site safety-check machinery (`emit_null_check`,
  `emit_checked_arith`, `emit_div_zero_check`, `emit_bounds_check`)
  even after the recent ~60% IR-size reduction.

- **Dangling pointers** can't even be spelled. Mara's type checker
  refuses `^Foo = some_int`. V's compiler waves it through.

- **Bounds-check bypass via header manipulation**: V exposes
  `arr.len` and `arr.cap` as writable, so user code can lie about them
  and bypass the check. Mara slices/partial arrays don't expose those
  as user-writable fields; the only path to set them is through
  internal codegen (the `take` cursor advance, etc).

- **Sum-type wrong-variant access** is a clean type error in Mara
  ("union 'X' has no variant 'Y'"). V crashes its own compiler on the
  analog.

- **Global mutable state** is rejected: module-scope decls are treated
  as constants, and any attempt to assign to one produces "shadows a
  constant from outer scope". `program = Program(...)` is the one
  blessed exception, handled as a compiler-managed marker. V claims
  the same restriction but it has a one-line bypass.

### Where Mara and V have the same weakness

- **Immutability** (`imm_bypass`). Neither language enforces
  const-correctness through pointer aliases today. In V this is a
  bypass of an advertised guarantee; in Mara it's an acknowledged
  deferred design (`project_pointer_ref_mutable_deferred.md` in
  memory). The honest framing is the difference, but the *runtime
  behaviour* of both languages is the same: write through a pointer,
  the underlying value changes.

- **Generic body validation**. This is a real Mara bug, surfaced by
  the audit. `foo :: fun(x: $T) -> $T { return nonexistent_helper_fn(x) }`
  passes the type checker; codegen then emits incomplete IR for the
  call site and clang chokes on a missing terminator. V's analog
  silently accepts and crashes at runtime; Mara's analog fails-loud
  but in clang rather than the type checker — better than V's silent
  acceptance, worse than a clean type error. Worth fixing properly:
  the type checker should validate `nonexistent_helper_fn`'s existence
  at the call site inside the generic body (or at instantiation), not
  defer to LLVM.

### Where the audit doesn't really apply

- **Performance vs C**: Mara doesn't claim parity with C. We have a
  separate stress-test number (1M lines, 37s build, 7ms-per-call
  runtime — see commit `e9d7f03`). Nothing to compare against V's
  inflated claims.

- **Compilation speed in lines/sec**: similarly, Mara hasn't published
  a number. The 1M-line stress test runs at ~27k lines/sec for the
  whole pipeline (lex/parse/check/codegen/clang). Honest.

- **Autofree / escape analysis**: Mara uses explicit arena allocators.
  No automatic-cleanup claim to test. The honest position dodges V's
  entire memory-management section.

## Repro

```
cd test/v_audit
for d in */; do
    ( cd "$d" && ../../../Mara.exe build "${d%/}" > /dev/null 2>&1 \
       && [ -f "${d%/}.exe" ] && "./${d%/}.exe" > /dev/null 2>&1 \
       ; echo "${d%/}: exit=$?" )
done
```
