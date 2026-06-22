# Slice analysis — plan

Goal: forward and backward program slices, surfaced as `mara ask` queries.
Backward = what affects a value at a point. Forward = what that value affects.

Where we stand: the backward *data* direction mostly already exists — escape
analysis / arg-sets is, in effect, a backward interprocedural slice collapsed to
parameter indices, and the call graph already provides the interprocedural
summary engine. Forward dataflow and control dependence are not built. One
primitive is missing underneath all of it: a link from a variable's use back to
its declaration (today resolution only yields a type, and the flow passes track
variables by name).

**Status: shipped.** All five phases below are implemented and surfaced as
`mara ask <fn> contributors` (backward) and `mara ask <fn> affects` (forward).
Commits: f594d89 (1) · 1a83d75 (2) · 71ce3ce (3) · 367d812 (4) · 4b2c93f (5).
Control dependence is now exact: a real control-flow graph (cfg.odin) drives both
missing-return checking and post-dominator control dependence — early-return /
break guard clauses included. CFG: 81d0e6d (build) · 2642583 (return-check) ·
00c3ef6 (control dependence).

## Phases (cheapest-useful first)

1. **Variable identity.** Give every variable use a stable link to its
   declaration. This is the unblocker — everything else sits on it.

2. **Def-use graph (intraprocedural).** Generalize the existing flow walk so it
   records which definitions reach which uses, with real loop handling. One
   graph serves *both* slice directions inside a function.

3. **Backward slice across calls.** Walk the def-use graph backward and cross
   call boundaries using the call graph's existing summaries. Closest to
   shippable — the hard interprocedural backbone is already there.

4. **Control dependence.** Track which branch conditions guard each statement,
   so a slice also pulls in the predicates that decide whether relevant code
   runs. Turns a data slice into a full program slice.

5. **Forward slice across calls.** Forward is nearly free inside a function (same
   graph, walked the other way); across calls it needs the mirror image of
   today's backward summaries.

Each direction gets wired into `mara ask` as its own query as it lands, reusing
the existing graph + renderer.

Shape of the effort: the backward data slice is incremental (most of the way
there); forward and control dependence are new work, but all of it rests on the
identity + def-use foundation from phases 1–2.
