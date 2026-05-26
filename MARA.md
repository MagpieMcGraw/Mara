Features:

Scope allocator - an arena that marks and resets in every scope that has a big value. Created by the user, managed by the compiler

Chained RVO for fixed size return values, including arrays

Depth checking prevents returning pointers to stack memory.


Idioms:

Memory management is manual, but almost invisible. Variables either go on the stack, or if they are big, to the scope allocator. All variables get freed at the end of scope. Memory leaks or use after free are essentially impossible.

Fixed sized variables, including arrays, can be declared in functions and returned from them. RVO makes sure they are valid in the higher scope they are returned to.

Slices are used to return runtime sized data from functions, by carving a buffer passed from a higher scope.


Important learnings:

Define codegen types and stick to them. No hardcoded sizes


Quirks:

Slice from slice/array copies reference
some_slice := other_slice[0:128]

Array from slice copies data
my_array : [..256]byte = some_slice[64:128]

The default slice notation [:] slices up to len
If you want cap, be explicit

Slice parameters accept fixed arrays, BUT!
Only do this if your fixed array is full
If it's partially full, make a partial array [..n]Item