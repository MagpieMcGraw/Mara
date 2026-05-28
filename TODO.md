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

Byte reads might need new syntax. Maybe an = to read without auto-len, and a += to read with auto len...

Take a personal look at gen address chain. I have a bad feeling about it.