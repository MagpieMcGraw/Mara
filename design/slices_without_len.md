# Slices without a fill len: plan

Written 2026-10-29, after the user's call: "If you want appendable storage, get a list."
Revised the same day: a mutable list is `^[$N]T`, and a mutable slice `^[]T` is a writable
view that can't grow. Not started. It replaces the no-len slices, `start_fill` and len
inheritance built the same day (6748dfd, 0afb7b6, 79522bc, 6bbdec0).

## Why

- Most languages with slices give them no fill state. A Rust `&[T]`, a Zig `[]T` and an
  Odin `[]T` are a pointer and a count, and growable storage is its own type (`Vec`,
  `ArrayList`, `[dynamic]T`). Go is the exception: its slices carry len and cap, and
  `append` grows them. But Go's `append` returns a new slice, and may move it.
- Mara already has the growable type, the list `[N]T`. A pointer to a list of any room,
  `^[$N]T`, works today (checked 2026-10-29): `push :: fun(xs: ^[$N]i64, x: i64)` takes an
  `[8]i64` and a `[4]i64`, one copy each (`push__const_8`, `push__const_4`), and a struct
  field can be `^[8]i64`. `join` already takes `[$N]$T`.
- Few slices are actually appended to. The 2026-10-29 probe (an emitter probe, then a
  fixpoint over the params that move a len; scratchpad `append_probe/analyze.py`) found:

  | Code | Appends into lists | Appends into a slice's own len |
  |---|---:|---:|
  | sooblivion | 1,387 | 171 (31 more through `^[]T` variables, not traced) |
  | view | 274 | 0 (15 through `^[]T` variables) |
  | Pounce | 19 | 11 |
  | mara3 | 9 | 0 traced (19 through File's `^[]T` fields, which point at slices) |
  | stdlib | | the arena's cursor, `filter`/`group`, `dir_read`, `read_entire_file` |

  sooblivion's 171 are three kinds:
  - **90 load rooms.** `Load_Room`'s `file`, `blocks`, `model` and `texture` are lists of 64,
    16, 64 and 64 MB, the same sizes at all five places that make one. `load_room`
    (viewer.mara:481) slices them to their cap so that a struct can hold them. They are lists
    already: fields `^[64 * MB]byte` and so on would do.
  - **65 carved rooms.** `slice([:n]T, &storage)` with n known only at run time: animation
    tracks, model parts and palettes, mesh vertices and indices, speedtree growth. They are
    filled by appends. They can't be lists, because a list's room is part of its type. They
    would be written by index, with a count kept beside them.
  - **16 reads** where the len says how much came: `file_read`, `read_exactly`,
    `tcp_receive`, `inflate`.

  Also in sooblivion: 165 params of its own functions, `^[]T` today, grow what they point
  at. They would become `^[$N]T`. (view, Pounce: 1 each; mara3: 2.)

## The model

| Type | What it is | Grows? |
|---|---|---|
| `[N]T` | a list: its items, its len how many, its room N | yes |
| `^[N]T`, `^[$N]T` | a mutable list: a pointer to a list, of that room or of any | yes |
| `[]T` | a slice: a view, read-only as a param | no |
| `^[]T` | a mutable slice: a writable view | no |

- **Only lists grow.** Appends, `next`, takes from storage and `.len =` writes take a list or
  a mutable list. The stdlib's appends take `dst: ^[$N]$T`, so `&view + x` has nothing to
  call.
- **A slice's len is set when it's made and never moves after that.** For a smaller view,
  reslice it: `s = s[0:n]`.
- **A mutable slice `^[]T`** can write the items of the view it points at, and can replace that
  view whole: `rest^ = rest^[n:]`, a cursor the callee moves along. It can't grow it. It is
  what a function takes to write into part of a caller's memory: a file read into a window of
  a buffer, a sort in place, font's coverage buffer. `[]T` params are read-only (the copy
  rule).
- **A slicing `x[a:b]`** shows exactly its b - a items: len = cap = b - a, whatever x's len.
  This is the rule before 2026-10-29, with no no-len bit and no inherited len.
- **A list given where a slice goes** is a view of its items: len = its len, cap = its room,
  as today. A mutable list given where a mutable slice goes is a writable view of its items
  (`sort(&list)`).
- **Reads go to the len**, everywhere: loops, print, `==`, appends from it, copies.
- **Indexing a slice is checked against its len**, its size, as Go does; the cap only bounds a
  reslicing and cstring's look for a 0. (Today it's checked against the cap, because the len
  was a fill count.) A list's indexing stays checked against its room, N: its room is memory
  you can write by index.

## What `^[$N]T` costs

- **One copy of a function per room size it's called with.** For the appends, which are tiny
  and inlined in release builds, that's nothing there and more code in debug builds. For
  functions that take storage (`read_entire_file`, `dir_read`, font loading, sooblivion's
  readers), it's one copy per storage size. sooblivion's rooms come in a few fixed sizes.
- **A struct field names its room** (`lines: ^[MB]i64`), or the struct becomes generic over it.
- **Nothing sized at run time is a list**, as now. Rooms carved with a count known only at run
  time are views, with a count kept beside them.

## Decisions for you

1. **Where `x[:]` and `x[lo:]` of a list end.**
   - *(Recommended)* At its len: its items. A room is a list now, so a view of the unfilled
     part has nothing to do. 483 of 485 `[:]` once wanted the items.
   - Or at its cap, as built today, which then needs `x[lo:.len]` for the items.
2. **Whether slices keep a cap.**
   - *(Recommended)* Keep the three-word header {len, cap, ptr}. cstring needs the cap to know
     a 0 after the text is still inside the memory. That's how the bindings take `[]utf8` and
     hand C a pointer without copying.
   - Or shrink to {ptr, len}. That's a smaller value, but cstring of a slice could no longer
     be checked, and the layout touches the ABI, debug info, the const tables and mara_mem.c.
3. **Reads that report how much came.**
   - *(Recommended)* Take a mutable slice, the window to read into, and return the count:
     `view := room[at : at + want]`, then `got := file_read(id, &view)?`. This reads into any
     part of any memory, the middle of a big buffer included, as `read_entire_file` does.
   - Or take a mutable list and set its len to what came. That's fewer changes, but you can
     only read into a whole list.
4. **Writing a slice's len.**
   - *(Recommended)* Refused, with an error that says to reslice.
   - Or allowed only to shrink (`view.len = got` with got ≤ len), which keeps some code as it
     is but blurs "a slice's len never moves".

## The compiler

- **Checker errors**, each at the place it happens:
  - an append into a slice, or through a mutable slice: "a slice can't grow: append to a
    list, or a `^[$N]T` pointing at one". The dispatch finds no add for it, so the error is
    worded for that case.
  - a `.len =` write on a slice or through a mutable slice (decision 4);
  - a take from a slice (`slice([:n]T, &view)`, `let(T, &view)`), and `next(&view)`.
- **A mutable slice is a view.** `^[]T` stays a reference {where the len is, the cap, the data}
  for writing items and replacing the view. The paths that move its len through it go: the
  appends no longer take it. Whether its layout can shrink to a pointer to the slice is for
  later.
- **A slice's index check** uses its len, not its cap.
- **Taken out:** the no-len bit (SLICE_NO_LEN, emit_no_len, emit_len_count and the masks on
  len reads), emit_window_len, the `start_fill` builtin and its Carve "fill", and the cap bound
  lw_slice gives an open end (decision 1). A slicing's len is back to its window's size.
- **Kept: the append speed.** 200M appends take 0.094 s now and took 0.38 s before. The gain
  came from LLVM knowing the len it appends at isn't negative, which `start_fill`'s value told
  it. With `^[$N]T`, each copy knows its N, so the room check is against a constant. The len's
  non-negativity can come from range information on a list's len loads (0 ..= N). Measure it
  with the scratchpad bench (`bench_nolen.mara`) before and after.
- **The slice layout stays** the same (decision 2), and so do the x86 backend, debug info
  and the runtime.

## The stdlib

- **Appends:** `slice_add`, `slice_add_item`, `utf8_add`, `utf8_add_item` and `next` take
  `^[$N]$T` (text, `^[$N]utf8`). Their bodies are as before 6748dfd.
- **Storage:** `read_entire_file`, `dir_read`, `filter`, `filter2` and `group` take
  `storage: ^[$N]byte`. Takes (`slice([:n]T, &storage)`, `let`) need a list or a mutable list
  as storage.
- **Reads** (decision 3): `file_read`, `pipe_read`, `udp_receive` and `tcp_receive`, on Windows
  and Linux, take `data: ^[]byte` and return the count beside what they return today. The exact
  shapes are settled when they're built: several results only where several go, and no -1 for
  "ended".
- **`read_entire_file`** reads each piece into a window of storage past its len, adds the
  counts, then moves storage's len once.
- **`dir_read`** writes its entries by index into the carved room and returns `entries[0:k]`,
  as before 6bbdec0.
- **`filter`, `filter2`, `group`** carve their views, then write by index with a count. For
  `group`, that's one count per kind.
- **`Arena_Basic` and `Arena_Debug`** keep their bump cursor in a field (`used: i64`) instead
  of `base.len` (8 places in memory.mara). Their base is memory from the system, sized as the
  program runs, so it's a slice, not a list.
- **font.mara** sets lens through `^[]T` params (`atlas.len`, `glyphs.len`, `acc.len`,
  `out.len`, an outline's points). Where a function fills a caller's list, it takes `^[$N]T`.
  Where it writes into a view, it keeps `^[]T` and doesn't set the len.

## Code outside the compiler

These lists come from the probe. The checker errors will give the exact sites.

- **sooblivion:**
  - The 90 load rooms: `Load_Room`'s fields become `^[64 * MB]byte`, `^[16 * MB]byte` and so
    on, `load_room` keeps the four list pointers, and `room.file.len = 0` empties the list
    itself.
  - The 65 carved rooms are written by index with a count.
  - The 16 reads take a window and the count returned.
  - The 165 params that grow what they point at become `^[$N]T`.
  - sooblivion takes releases, so the release waits until it has moved.
- **Pounce (11):** 4 `file_read` calls in cache.mara (223, 253, 267, 286) and 7 appends in
  gfx_mesh_generation.mara (39–53).
- **mara3:** `File`'s `lines` and `tokens` point at `line_slice := lines[:.cap]` and
  `token_slice := tokens[:.cap]` (compiler.mara:86–90), and lex appends through them. They
  would be `^[MB]i64` and `^[MB]Token`, pointing at `&lines` and `&tokens`. The user's code:
  they move it.
- **view:** none traced. The 15 appends through `^[]T` variables are to be checked when the
  checker errors are on.
- **tests:** the checker errors will list them.

## Order of work

1. You decide 1–4.
2. The checker errors are first a probe only, a list per code base from no-link builds:
   stdlib, tests, docs, view, Pounce, sooblivion and mara3.
3. The stdlib changes: the appends and storage functions to `^[$N]T`, reads, arenas,
   `filter`/`group`, `dir_read`.
4. The compiler: errors on, the no-len machinery out, slicing back to its window, slice
   indexing against the len, the append speed kept and measured.
5. Tests, docs, view and Pounce moved. Then the no-link sweep, and the suite once.
6. sooblivion's and mara3's lists go to you. Release when sooblivion has moved.
