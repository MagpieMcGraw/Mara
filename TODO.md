1 item per line, 1 line space between items.

Dynamic arena: if we allocate past the cap, commit more virtual memory. If we free to below the cap, decommit up to the cap. Allow users to manually commit more, some may want to comntrol the timing of the commit. Also allow modifying the cap at runtime?

Modules are not structs. See register_and_check_declarations vs register scope defs for examples.

When lexing, save file sizes, pass them on to the parser, to know roughly how much memory to allocate.

Figure out auto deref semantics. How often should we auto deref? And what's the relation between pointers and mutability. This whole topics needs discussion.

Steal string formatting from python.

Write build script for .c code in mara to test capabilities

DLLs need an init function where the arena layout is defined.

How do you use Mara code as a static lib? Dll should work, but how would a static lib manage it's memory? Analyze the lib and rewrite it to use explicit allocation?

Trait system where each type describes how it achieves a certain operation. Array would define elem access as an offset, a slice as a ptr deref. Traits might have to be very small, for example, "I have a len" "I have a cap" "I have elements". Fixed arrays and slices composed from these.

Since everything is a scope... can we do metaprogramming by injecting a scope in place of another scope? A scope as value?

Should a param list be parsed as a scope? And then have it's fields extracted? How would we detect where the scope ends?

Scope literals.

Can we drop fn from function pointers?

Storage buffers as a type? Can that help out the depth analysis?

Language features that enable less IR generation. Functional stuff?

When parsing, put defs and decls in two different arrays. Can loop over each without interdependence?

Byte reads might need new syntax. Maybe an = to read without auto-len, and a += to read with auto len. Also figure out what ops should set the len.

Maybe constructors need return values? Could be good for error handling.

Findings from the Fable 5 code review, 10 Jun 2026. Same format: 1 item per line, 1 line space between items. Roughly ordered: bugs, then language decisions, then stdlib fixes, then docs/tooling.

BUG draw_state_append writes batch.instances[i] using the object index and never increments instance_count. Should be instances[batch.instance_count] then increment, in both the main and highlight paths. As written, render sees count 0 and draws nothing.

BUG quat_slerp Taylor asin is off by 2x near d=0.99. Either drop the nlerp cutoff from 0.9995 to ~0.9, or use a real acos (libm acosf, or llvm.acos intrinsic in LLVM 19+). Also replace sin(f32(theta)) with sqrt(1 - d*d), exact and free.

BUG Arena_Debug.reset with current_mark == -1 reads base[-1]. Debug arena should crash loudly on reset-without-mark instead.

BUG hmtx advance read in load_glyphs (hmtx_loc + glyph_index * 4) is only valid while glyph_index < hhea.num_of_long_hor_metrics. Past that, glyphs share the last advance and the array degrades to 2-byte entries. Clamp using the Hhea already parsed. (DONE 10 Jun 2026, commit 25cdbeb — metric index clamped via min; cell-fit asserts added in rasterize_msdf in the same pass.)

BUG broadcast x, y = 7 segfaults in non-main fn (disabled test, dated 2026-05-30).

BUG enum-indexed array access rejected ("index must be i32") — omitted test, dated 2026-05-30.

BUG calling a fn-typed parameter fails in codegen — omitted test, dated 2026-05-30.

LEAK load_and_compile: if the fragment shader fails to compile, the vertex shader is never deleted. Harmless today (fatal path), becomes real the day live shader reload exists. errdefer or restructure to one cleanup site.

DECIDE the slice law, then assert it in all.mara: explicit high bound claims the window as data (len = cap = hi - lo, even over unfilled storage); open high bound inherits fullness (len = parent.len - lo, cap = parent.cap - lo). Convert test_slice_view prints to asserts; expected len 0 cap 32 under this rule.

DECIDE #self construction order. Zero-init then decl-order initializers means c := helper(#self) in test_early_self sees a = b = 0, so c == 0.0, not 3.0. Assert whichever is intended and write the rule in all.mara.

DECIDE mixed signed/unsigned arithmetic under auto-widening. Suggest: widen both to the smallest lossless common type, compile error if none exists (u64 vs i64). Also decide int-to-float: i32 to f32 and i64 to f64 are lossy and should require casts if the rule is honest.

DECIDE union containing partial arrays: copy fixup needs the tag, so either consult it in copy codegen or forbid element-owning members in unions. Same question for the disk-load relocate walk.

DECIDE one return-type grammar. fun(a, b: i64) i64 and fun(a, b: i64) -> i64 both parse today (test_io_arrow exists to prove it). Pick one.

DECIDE class vs struct canonical spelling. memory.mara says class, everything else says struct; a reader parses the difference as semantic. Keep the alias as the joke, lint for one spelling.

DECIDED 10 Jun 2026 — asserts stay ON in release (TigerStyle); explicit `-no assert` flag compiles them out (`-no <feature>` parses as two argv tokens, unknown feature = hard error). (Output upgrade DONE same day: "Assert failed at <loc> / Expected game.running == false, but game.running was true" — comparison asserts name each non-literal operand with its value; bools print true/false, utf8 prints the glyph, enums print the variant name via gen_print_enum, escaped literals keep their source spelling, condition text keeps source spacing.)

ADD must-use err: warn when an err value is neither returned, branched on, nor discarded with _ =. Makes the return-the-error discipline mechanical while keeping ignoring legal.

ADD err second field in debug builds: raise-site span (and on Windows, GetLastError at the os boundary). Same machinery as the arena debug headers. Print then says what failed, where, and why.

ADD seed asserts from the review: arena mark/reset well-nesting (when Arena_Basic is uncommented), partial-array fixup invariant (arr.ptr == own elements) where received by ref. (DONE 10 Jun 2026: slice_add capacity, parse_glyph point-count cap + end-of-parse cursor <= bytes.len.)

BUG u64 literals above i64 max don't parse: 18446744073709551615 wraps to -1 internally, then the range check reports "constant -1 overflows u64". Literal pipeline needs an unsigned path (found writing assertu.mara). (DONE 10 Jun 2026: decimal literals accumulate in i128 like hex, exact to u64 max; past that is a parse error with the literal text. Also fixed -9223372036854775808 (i64 min), which wrapped positive through the old i64 path. test/u64dec + test/failures/test_literal_overflow_dec_fail.)

ADD redundant-cast warning: flag casts where implicit widening would succeed identically. Then sweep the i32()/i64() fossils from the 4/4/8 era (data.len = i32(read) in file_read, the i32 len wrappers in font.mara).

FIX retire string.mara add_str in favor of core's generic slice_add (the fix already exists; resolve the duplicate + dispatch). If keeping a string-specific one, src should be []utf8 not str.

FIX find_byte returns i32 where find returns i64; also unify -> (a, b) vs -> a, b return-type style between them.

FIX retire Big_Slice / sys_alloc_big now that slices are 8/8/8. When Arena_Basic is uncommented, it should hold a plain []byte like Arena_Debug.

FIX Arena_Debug.offset duplicates base.len now that len is the cursor. One field can go.

FIX font data to persistent storage per plan. (The other half — first codepoint 0 -> 32 — DONE 10 Jun 2026, commit 25cdbeb.)

FIX mat4_inverse returns identity on singular input silently — the one quiet fallback in a codebase that prints diagnostics elsewhere.

FIX PI and TAU are one digit short of full f64 (…589793, …79586). Mesh gen also inlines its own truncated copies — use the constants.

FIX abs_int overflows on i64 min; @llvm.abs.i64 exists and matches the f32/f64 siblings.

FIX instance_capacity in DrawState is stored but never checked before BufferSubData.

FIX fps := 60.9 — comment it if it is the deliberate vsync-undershoot trick, correct it if it is a typo.

FIX Windows ANSI paths: CreateFileA breaks on non-ASCII paths (Lithuanian user dirs). One-line app manifest setting activeCodePage to UTF-8 fixes every A-suffix call at once.

ADD self-hosted crash handler: rewrite code/mara_crash.c as runtime.mara, compiled+cached to a .o by the compiler's own pipeline (same ensure_crash_runtime trick — we wrap clang, so a .mara source works as well as a .c). Settled shape from the 10 Jun discussion: runtime module is dependency-free (own foreign fopen/fwrite/time declares, no `use` — avoids duplicate defines vs user TUs); interface is one buffer handoff crash_report(msg, len) with codegen snprintf-ing segments into a stack buffer (no C varargs, no held FILE*, no mutable global); compiler builds it with -no assert (handler can't recurse into itself; bounds traps already printf+exit directly, safe); cache invalidates on runtime.mara mtime OR compiler binary mtime (generated IR tracks compiler version). First tenant of the runtime module; self-hosting starts here.

CHECK whether partial-array indexing in codegen loads the stored header pointer or computes base + offset. Direct compute is faster and shrinks the surface that depends on fixup correctness. One IR dump of a leaf function answers it.

CHECK main bootstrap ordering: scope arena provisioning vs the this_program assignment that creates it. Works today; write down why.

DOCS all.mara: fix "it's" -> "its" (also in README build section). Add the slice-law section with asserts. Graduate each margin question to a rule or a dated test.

DOCS README: add the perf block screenshot (1M lines / 7.5s, 273ms hot) and an OOM dump screenshot. Those two images carry the language's character better than prose.

TOOLING golden-output file for the print-based tests in test.mara: run once when known-good, diff every build.

TOOLING fix and regenerate the 1M-line benchmark, then grow it adversarially: one giant dispatch block, one 100K-line function, deep use chains. Name the cliffs before a real project finds them.

TOOLING formatter opinion on tabs vs spaces (gfx_mesh_generation.mara is the spaces outlier) and on class vs struct.