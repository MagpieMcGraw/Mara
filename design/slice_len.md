# What a slice's len means

A survey of how code uses a slice's len, for the user's idea (2026-10-28): slices made empty
with room to their cap, and loops that run to cap. Parked here to get back to. The surveys
were temporary probes in the checker, logging every slice use while the code checked; the
probes are gone, and the numbers are as of 105c8a4 and sooblivion on 2026-10-28.

## The idea, and the rule floated so far

- A slice made by slicing (`x[a:b]`, `x[:]`) is empty: len 0, cap the size of the slicing.
- A loop over a slice runs to its cap. To loop to len, reslice: `for v in s[0:s.len]`.
- A list seen as a slice keeps its len. A list and a slice are both arrays with a len, so the
  len carries over (the user, 2026-10-28).

Why: a slicing today is made with len = cap, so its len says the same as its cap, and code
that wants a room to fill has to set `.len = 0` itself.

## Every `.len` read of a slice in sooblivion: 574

The survey classed each read by what the slice is:

- **A view:** made once by slicing, from a list, or handed in, and never grown. Its len is
  its size, as its cap would be.
- **A room:** something fills it. Its len is moved by an append, a len write, a take, or
  carving from it, or it is passed with `&` to a `^[]T` param whose len moves. Its len
  counts what has been put in.
- **Fed by a room:** a room's slice that was copied or passed somewhere else and read there.

| What the len is | Reads | Share |
|---|---:|---:|
| A. The view's size: `.cap` would say the same | 328 | 57% |
| B. A fill count, read in the filling code | 143 | 25% |
| B. A fill count, read elsewhere (fed by a room) | 103 | 18% |

### A. The view's size: 328

| Read as | Reads |
|---|---:|
| a comparison or bounds check | 182 |
| an emptiness check | 47 |
| arithmetic (`- / + * %`) | 46 |
| a slice bound | 18 |
| a range loop's end | 13 |
| stored, an argument, returned | 22 |

Examples:

- `if at + 20 > data.len do return` (bounds check before reading a record from file bytes)
- `if place.len == 0 do return`
- `if args.len > 3`
- `rest := view[got : view.len]`
- `if ends_with(folder_path, "\\") do folder_path = folder_path[0 : folder_path.len - 1]`

These slices are made once and never grown. Renaming these reads to `.cap` changes nothing
they do.

### B. A fill count, read in the filling code: 143

| Read as | Reads |
|---|---:|
| `len + n` (a cursor, a fits check) | 63 |
| stored | 22 |
| an argument | 17 |
| an emptiness check | 12 |
| a comparison | 8 |
| other arithmetic, a slice bound, a range end, an index | 21 |

Examples:

- `got += rest.len` (after a file read into a room)
- `if renderer.parts.len + built.parts.len > renderer.parts.cap`
- `for k in 1:track.rotations.len`
- `fits(text.len + more.len, …)` (building log text)

### B. A fill count, read elsewhere: 103

| Read as | Reads |
|---|---:|
| a comparison | 40 |
| stored | 14 |
| an emptiness check | 13 |
| an argument | 11 |
| arithmetic | 17 |
| a range end, a slice bound, other | 8 |

Examples:

- `for k in 0:blades.len` (grass blades, filled by the loader)
- `if data >= mesh.blocks.len` (a model's blocks)
- `if angles.len == 0` (an animation track's angles)

These read a room someone else filled. The cap is the room, and the len is how much of it
is real, but nothing at the read says which of the two it needs. Written as `.cap`, they would
read the unfilled tail with no error. They keep their meaning only if every filler cuts the
room to its len before handing it on.

## How the reads were sorted

- A variable, field or param that is a room or was fed by one is B; everything else is A.
- Struct fields are judged program-wide: if any `Model`'s `parts` is appended to, every
  `model.parts.len` is B.
- A param is B if any caller passes a room.
- A slice a call gives back is taken as a view; no reads fell in that class.
- The full listing, every read with its line, is beside this file in `slice_len_reads.md`.

## Earlier surveys (2026-10-27/28)

- **`x[:]`, full or empty:** 485 sites across stdlib, tests, docs, view, Pounce, sooblivion
  and mara3. 483 want the items, none want it empty. Of all 966 slicings, 13 want empty, and
  each says so with `.len = 0` right after or a field filled later. Only 6 of those are
  `[0 : x.cap]`, the form an empty `[:]` would replace.
- **What `x[:]` does:** stripping all 332 `[:]` from real code (stdlib, view, Pounce,
  sooblivion), 323 change nothing. 4 make a view where `v := x` would copy. 4 the checker
  needs: 2 returns, a fixed array named as a view then passed with `&`, and a `^list` used as
  a slice. Its one real job: a view where `:=` or return would copy or refuse. The strip also
  found 3 compiler bugs, fixed in fdc83a7, 161b24f and c0524d5.
- **Slice variables by use (sooblivion, 438: 216 locals, 222 params):** 47 only looped
  over; most are params given converted lists, len < cap, so loop-to-cap would overrun unless
  a list converts with its len kept. 27 looped and indexed, 5 filled, 94 kept in structs or
  returned. 262 read the len some other way: 151 bounds checks, 35 emptiness checks, 13
  `0:x.len` loop ends, 66 other. Of ~150 slicings, 2 go straight into a loop. view: 4 of 164
  loop-only; Pounce: 0 of 27; mara3: 3 of 11.
- Under the copy rule, an empty `[:]` handed straight to a `[]T` param can never be filled.
  An empty slicing only helps when it is stored, then passed with `&`.
