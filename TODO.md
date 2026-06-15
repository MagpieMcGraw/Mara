1 item per line, 1 line space between items.

Give slices a .hdr field. Make it the only way to reassign the slice header.

casting vec3 to bool causes a codegen error

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

Language features that enable less IR generation. Functional stuff?

When parsing, put defs and decls in two different arrays. Can loop over each without interdependence?

Byte reads might need new syntax. Maybe an = to read without auto-len, and a += to read with auto len. Also figure out what ops should set the len.

[DEEP] BUG broadcast x, y = 7 segfaults in non-main fn (disabled test, dated 2026-05-30). No decision — codegen investigation.

[DEEP] BUG enum-indexed array access rejected ("index must be i32") — omitted test, dated 2026-05-30. No decision — codegen investigation.

[DEEP] BUG calling a fn-typed parameter fails in codegen — omitted test, dated 2026-05-30. No decision — codegen investigation.

[DEEP] TOOLING fix and regenerate the 1M-line benchmark, then grow it adversarially: one giant dispatch block, one 100K-line function, deep use chains. Name the cliffs before a real project finds them.
