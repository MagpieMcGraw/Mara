1 item per line, 1 line space between items.

# Compiler — mara build

The program shouldn't re-describe what the text already describes one-to-one.

Code generation still decides what the program means in places (void by statement kind, checks and their messages, representations chosen from an op's user, type mismatches as refusals, print, text without a header): move each into lowering or storage. The list: design/codegen_concerns.md.

Name resolution in parallel — each module's bodies at once — when the checker goes parallel (it stays sequential for now; the rest is done: design/name_resolution.md).

Give slices a .hdr field. Make it the only way to reassign the slice header.

casting vec3 to bool causes a codegen error

Modules are not structs.

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

When parsing, put defs and decls in two different arrays. Can loop over each without interdependence?

Byte reads might need new syntax. Maybe an = to read without auto-len, and a += to read with auto len. Also figure out what ops should set the len.

Figure out syntax for writing to bytes. Should number literals be writable? How about arrays? What should the casting syntax be for that, especially for arrays?

Validate top level statements investigation. Do we actually need it?

Type checking of unions and distinct is fucked up for some reason.

🚩 parameterized structs. We have regular structs with constructors, and we have generics. Parameterized is not a struct thing.

🚩 (the genuine {}/() merge)

🚩 Why do we track which module is the main module?

Fix FFI functions for mara ask. Probably some array on type scope was skipped?



# Analyzer — mara ask

Handle constants

Flow analysis doesn't account for arrays and their indexing.

Mara ask, record all queries(instead of graphs), so you can later replay them in the viewer. Render the whole program graph, color the queried parts. That data can be overlaid for a more complete picture. Also distunguish results, a direct ask shows where the AI attention is.

Make flow analysis show up as text highlights in sublime