1 item per line, 1 line space between items.

Foreign blocks could allow specifying location of related files. Right now every subdirectory of `code/` becomes a `-L` path automatically, and the lib must live somewhere down there. A per-block path option would let foreign blocks point at libs outside the repo (system SDKs like `C:\VulkanSDK\...\Lib`, or shared toolchain paths) without copy/symlink. Same hook could carry per-platform paths if it ever matters.

Constructor calls should be refactored into the regular-function call path. Today `check_constructor_call` is a separate machine that duplicates the args-to-params mapping logic from `check_call`. Features added to the regular path (currently: `_` for default-arg substitution; previously fill_default_args, dispatch routing) have to be ported manually or are missed entirely. Concretely: `Foo(_, x)` on a constructor with defaults won't substitute `_` today because the underscore pass lives in `check_call`, not `check_constructor_call`. Unifying the paths means constructors automatically inherit every call-site feature; the constructor's "args map to fields vs params" distinction can become a flag or a small specialization at the end rather than a parallel implementation. Same logic applies to `check_dispatch_call` and `check_generic_call` — both should funnel through the same args-to-params engine. Ctor should take pointer to their struct.

Arbitrary-precision compile-time numeric literals. Mara now stores number literals as `Expr_Number{value: f64, int_value: i64}` — exact for everything in i64 range, which covers all practical systems-programming literals. Beyond that (Zig/Go-style robust tier) you'd want literals to live as arbitrary-precision integers/rationals at compile time, with coercion-time overflow checks per target type. Lets you write `1 << 64` in a constant expression without overflow, compare bigger-than-i64 literals exactly, get exact diagnostics like "this literal is too big for u32." Implementation needs an arbitrary-precision integer type in the compiler plus a constant-folding interpreter operating in that space. Not load-bearing for game/bootstrap workloads — defer until a concrete need surfaces (cryptography, big-number math, or u64 hex literals like `0xFFFFFFFFFFFFFFFF` for sentinel values).

Dynamic arena: if we allocate past the cap, commit more virtual memory. If we free to below the cap, decommit up to the cap. Allow users to manually commit more, some may want to comntrol the timing of the commit. Also allow modifying the cap at runtime?

Modules are not structs. See register_and_check_declarations vs register scope defs for examples.

Unify declaration parsing across params/returns and statement-level decls. DONE. parse_decl_tail is the single shared core; param/return contexts call it from parse_typed_decl_group, statement context calls it from try_parse_assign's multi-name branch, struct fields ride the statement path via Stmt_Decl. Tuple-destructure-as-default (`fun(x, y := get_pair())`) is also working — see Expr_Tuple_Default for the codegen-side dedup that calls the source once per call site and routes its tuple slots to the bindings. Test: test/test_param_tuple_destructure.mara.

When lexing, save file sizes, pass them on to the parser, to know roughly how much memory to allocate.

Figure out auto deref semantics. How often should we auto deref? And what's the relation between pointers and mutability. This whole topics needs discussion.

Steal string formatting from python.

Write build script for .c code in mara to test capabilities

Should generic constructors take values? Should type only arguments even be allowed in generic struct constructors? A constructor is supposed to construct a ready to use struct, which implies that all values are intiialized.

DLLs need an init function where the arena layout is defined.

How do you use Mara code as a static lib? Dll should work, but how would a static lib manage it's memory? Analyze the lib and rewrite it to use explicit allocation?

Trait system where each type describes how it achieves a certain operation. Array would define elem access as an offset, a slice as a ptr deref. Traits might have to be very small, for example, "I have a len" "I have a cap" "I have elements". Fixed arrays and slices composed from these.

Since everything is a scope... can we do metaprogramming by injecting a scope in place of another scope? A scope as value?