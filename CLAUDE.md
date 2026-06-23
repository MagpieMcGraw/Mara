# Mara

A programming language written in Odin.
The goal is a production ready compiler for under 50k lines.

## Building and running

The compiler:
odin build . -debug

Mara code:
mara build game    	# build module "game" from all .mara files with `module game`
mara build         	# build module matching current directory name

## Workflow

Make a git commit before starting work.
That means all the changes, every time.

When implementing a feature, prefer hard errors over silent fallbacks for unhandled cases. A printf + continue pattern in codegen is a hidden bug factory — emit the diagnostic and abort the relevant codepath instead.

## Testing

Always build tests from inside the test folder so the resulting `test.exe` and `output.ll` land there instead of polluting the repo root.

# Surprise

I may make small edits to various files while you are working. Usually touching Mara code or my notes. I almost never touch the compiler code so a conflict there is unlilely. Don't worry about it.

# Reference

Old odin game project can be found at C:\Users\magpie\Desktop\Warlock Odin

# Analyzer (`mara ask`)

A graph-based code analyzer that reveals the structure and data flow of Mara
programs. Call from cwd where you have your module.

MODULES ANALYSIS ONLY RETURNS BASIC OVERVIEWS FOR NOW

mara ask                # info about the modules in cwd
mara ask name           # info about a module, struct, function, or variable

3 types of analysis: type and call and flow
2 types of direction: above and below

For type analysis:
above|bfor - what I contain, what I need to be constructed
below|aftr - who contains me after I have been constructed

For call analysis:
above|bfor - Function calls that supply me, what I call
below|aftr - Function calls that I supply, who calls me

For flow analysis:
above|bfor - the tree of variables that supply me, inlcuding across function calls
below|aftr - the tree of variables that I supply, including across function calls

Other arguments:
mara ask name 2				# number - limit analysis depth, default infinite
mara ask var in scope 		# query specific variables or struct fields.
mara ask var at file:line 	# query variable in a file


Argument matrix

module type above   # structs this module imports and uses
module type below   # structs defined in this module, imported and used elsewhere
struct type above   # structs that are fields of this struct
struct type below   # structs that this struct is a field of
fun    type above   # the type analysis of this function's arguments
fun    type below   # the type analysis of this function's return values
var    type above   # flowy - the types of variables that supply me
var    type below   # flowy - the types of variables that I supply

module call above   # functions this module imports and calls
module call below   # functions defined in this module, imported and called elsewhere
struct call above   # functions that need to be called to make this struct
struct call below   # functions that take this struct as an arg
fun    call above   # functions called by this function
fun    call below   # functions that call this function, and dispatch blocks
var    call above   # function calls which supply this variable
var    call below   # function calls this variable supplies

var    flow above   # chain of variables and operations that supply this variable
var    flow below   # chain of variables and operations that this variable supplies
fun    flow above   # `flow above` on all call sites of this function
fun    flow below   # `flow below` on all call sites of this function
struct flow above   # `flow above` on all fields of all instances of this struct
struct flow below   # `flow below` on all fields of all instances of this struct
module flow above   # `flow above` on all instances of everything in the module
module flow below   # `flow below` on all instances of everything in the module