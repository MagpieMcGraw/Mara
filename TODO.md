1 item per line, 1 line space between items.

Constructor call refactor: DONE. `check_constructor_call` removed; the two callsites in `check_generic_call` route through a shared `check_pure_struct_construction` helper that also backs `check_call`'s pure-struct branch. `Foo(_, x)` underscore substitution works against field defaults. Constructor body codegen rewritten — fields pre-bind to GEPs into %sret so writes go straight to the caller's slot; the per-field alloca + copy-locals-to-sret epilogue is gone (-58 allocas in test.ll). `check_dispatch_call` now handles both `_` (per-candidate default substitution) and trailing-default fill (candidate's params may exceed supplied args if the missing positions have defaults). When more than one candidate matches the same call shape — typically because a trailing-default overload overlaps an exact-arity overload — dispatch rejects the call with an ambiguity error rather than picking by declaration order.

Arbitrary-precision compile-time numeric literals. Mara now stores number literals as `Expr_Number{value: f64, int_value: i64}` — exact for everything in i64 range, which covers all practical systems-programming literals. Beyond that (Zig/Go-style robust tier) you'd want literals to live as arbitrary-precision integers/rationals at compile time, with coercion-time overflow checks per target type. Lets you write `1 << 64` in a constant expression without overflow, compare bigger-than-i64 literals exactly, get exact diagnostics like "this literal is too big for u32." Implementation needs an arbitrary-precision integer type in the compiler plus a constant-folding interpreter operating in that space. Not load-bearing for game/bootstrap workloads — defer until a concrete need surfaces (cryptography, big-number math, or u64 hex literals like `0xFFFFFFFFFFFFFFFF` for sentinel values).

Dynamic arena: if we allocate past the cap, commit more virtual memory. If we free to below the cap, decommit up to the cap. Allow users to manually commit more, some may want to comntrol the timing of the commit. Also allow modifying the cap at runtime?

Modules are not structs. See register_and_check_declarations vs register scope defs for examples.

When lexing, save file sizes, pass them on to the parser, to know roughly how much memory to allocate.

Figure out auto deref semantics. How often should we auto deref? And what's the relation between pointers and mutability. This whole topics needs discussion.

Steal string formatting from python.

Write build script for .c code in mara to test capabilities

Should generic constructors take values? Should type only arguments even be allowed in generic struct constructors? A constructor is supposed to construct a ready to use struct, which implies that all values are intiialized.

DLLs need an init function where the arena layout is defined.

How do you use Mara code as a static lib? Dll should work, but how would a static lib manage it's memory? Analyze the lib and rewrite it to use explicit allocation?

Trait system where each type describes how it achieves a certain operation. Array would define elem access as an offset, a slice as a ptr deref. Traits might have to be very small, for example, "I have a len" "I have a cap" "I have elements". Fixed arrays and slices composed from these.

Since everything is a scope... can we do metaprogramming by injecting a scope in place of another scope? A scope as value?

Should a param list be parsed as a scope? And then have it's fields extracted? How would we detect where the scope ends?

Storage buffers as a type? Can that help out the depth analysis?