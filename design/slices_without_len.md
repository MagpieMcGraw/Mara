# Slices without a fill len: plan

Written 2026-10-29, after the user's call: "If you want appendable storage, get a list." Not
started. It replaces the no-len slices, `start_fill` and len inheritance built the same day
(6748dfd, 0afb7b6, 79522bc, 6bbdec0).

## Why

- Most languages with slices give them no fill state. A Rust `&[T]`, a Zig `[]T` and an
  Odin `[]T` are a pointer and a count, and growable storage is its own type (`Vec`,
  `ArrayList`, `[dynamic]T`). Go is the exception: its slices carry len and cap, and
  `append` grows them. But Go's `append` returns a new slice, and may move it.
- Mara already has the growable type: the list `[N]T`, and the mutable slice `^[]T`, which
  can point at a list of any room.
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
  - **90 load rooms.** `Load_Room`'s `file`, `blocks`, `model` and `texture` are four 16–64 MB
    lists, sliced to their cap by `load_room` (viewer.mara:481) so that a struct can hold them.
    They are lists already: `^[]byte` fields would do.
  - **65 carved rooms.** `slice([:n]T, &storage)` with n known only at run time: animation
    tracks, model parts and palettes, mesh vertices and indices, speedtree growth. They are
    filled by appends. They can't be lists, because a list's room is part of its type. They
    would be written by index, with a count kept beside them.
  - **16 reads** where the len says how much came: `file_read`, `read_exactly`,
    `tcp_receive`, `inflate`.

## The model

- **A list `[N]T`** holds items. Its len says how many; its room is N. Appends, `next`, takes
  from it and `.len =` writes all work on lists.
- **A mutable slice `^[]T`** points at a list of any room: appends through it move that list's
  len. (What else it may point at: decision 1.)
- **A slice `[]T`** is a view: a pointer, its len (how many items it shows) and its cap (how
  far its memory goes: what it may be resliced to, and where cstring looks for a 0). Its len
  is set when it's made and never moves after that: no appends into it, no `.len =` writes, no
  takes from it. For a smaller view, reslice it: `s = s[0:n]`.
- **A slicing `x[a:b]`** shows exactly its b - a items: len = cap = b - a, whatever x's len.
  This is the rule before 2026-10-29, with no no-len bit and no inherited len.
- **A list given where a slice goes** is a view of its items: len = its len, cap = its room,
  as today.
- **Reads go to the len**, everywhere: loops, print, `==`, appends from it, copies.
- **Indexing a slice is checked against its len**, its size, as Go does; the cap only bounds a
  reslicing and cstring's look for a 0. (Today it's checked against the cap, because the len
  was a fill count.) A list's indexing stays checked against its room, N: its room is memory
  you can write by index.

## Decisions for you

1. **What a `^[]T` may point at.**
   - *(Recommended)* A list or a slice. Through it you can write a slice's items and repoint
     it (`p^ = s`), but an append into a slice stops the program as it runs: a `^[]T` made
     from a slice gets the slice's len as its room, so an append finds none. This needs no
     new type, and `sort(&view)` style code keeps working.
   - Or only lists, checked when the program is checked, with a different type for a writable
     view. That catches more before running, but it's a new type and every writable-view param
     changes.
2. **Where `x[:]` and `x[lo:]` of a list end.**
   - *(Recommended)* At its len: its items. A room is a list now, so a view of the unfilled
     part has nothing to do. 483 of 485 `[:]` once wanted the items.
   - Or at its cap, as built today, which then needs `x[lo:.len]` for the items.
3. **Whether slices keep a cap.**
   - *(Recommended)* Keep the three-word header {len, cap, ptr}. cstring needs the cap to know
     a 0 after the text is still inside the memory. That's how the bindings take `[]utf8` and
     hand C a pointer without copying.
   - Or shrink to {ptr, len}. That's a smaller value, but cstring of a slice could no longer
     be checked, and the layout touches the ABI, debug info, the const tables and mara_mem.c.
4. **Reads that report how much came.**
   - *(Recommended)* Take a view and return the count:
     `got := file_read(id, room[at : at + want])?`. This reads into any part of any memory,
     the middle of a big buffer included, as `read_entire_file` does.
   - Or keep `data: ^[]byte` pointing at a list, its len set to what came. That's fewer
     changes, but you can only read into a whole list.
5. **Writing a slice's len.**
   - *(Recommended)* Refused, with an error that says to reslice.
   - Or allowed only to shrink (`view.len = got` with got ≤ len), which keeps some code as it
     is but blurs "a slice's len never moves".

## The compiler

- **Checker errors**, each at the place it happens:
  - an append into a slice: "a slice can't grow: append to a list, or a ^[]T pointing at one";
  - a `.len =` write on a slice (decision 5);
  - a take from a slice (`slice([:n]T, &view)`, `let(T, &view)`);
  - `next(&view)`.
- **A slice's index check** uses its len, not its cap. A `^[]T` made from a slice gets the
  slice's len as its room (decision 1).
- **Taken out:** the no-len bit (SLICE_NO_LEN, emit_no_len, emit_len_count and the masks on
  len reads), emit_window_len, the `start_fill` builtin and its Carve "fill", and the cap bound
  lw_slice gives an open end (decision 2). A slicing's len is back to its window's size.
- **Kept: the append speed.** 200M appends take 0.094 s now and took 0.38 s before. The gain
  came from LLVM knowing the len it appends at isn't negative, which `start_fill`'s value told
  it. Without `start_fill`, the same knowledge can come from range information on a list's len
  loads (0 ..= N), or a `n := dst.len` that the emitter marks as not negative. Measure it with
  the scratchpad bench (`bench_nolen.mara`) before and after.
- **The layout stays** the same (decision 3), and so do the x86 backend, debug info and the
  runtime.

## The stdlib

- **Reads** (decision 4): `file_read`, `pipe_read`, `udp_receive` and `tcp_receive`, on Windows
  and Linux, take `data: []byte` and return the count beside what they return today. The exact
  shapes are settled when they're built: several results only where several go, and no -1 for
  "ended".
- **`read_entire_file`** reads each piece into a view of storage past its len, adds the counts,
  then moves storage's len once.
- **`dir_read`** writes its entries by index into the carved room and returns `entries[0:k]`,
  as before 6bbdec0.
- **`filter`, `filter2`, `group`** carve their views, then write by index with a count. For
  `group`, that's one count per kind.
- **`Arena_Basic` and `Arena_Debug`** keep their bump cursor in a field (`used: i64`) instead
  of `base.len` (8 places in memory.mara).
- **`next`, `slice_add`, `utf8_add`** and the others work as they did before 6748dfd, on lists
  through `^[]T`.
- **font.mara** sets lens through `^[]T` params (`atlas.len`, `glyphs.len`, `acc.len`,
  `out.len`, an outline's points). That's fine where callers pass lists. Its callers are to be
  checked when the checker errors are on.

## Code outside the compiler

These lists come from the probe. The checker errors will give the exact sites.

- **sooblivion (171):**
  - The 90 load rooms become `^[]byte` fields: `load_room` keeps the four list pointers, and
    `room.file.len = 0` then empties the list itself.
  - The 65 carved rooms are written by index with a count.
  - The 16 reads take the count returned.
  - sooblivion takes releases, so the release waits until it has moved.
- **Pounce (11):** 4 `file_read` calls in cache.mara (223, 253, 267, 286) and 7 appends in
  gfx_mesh_generation.mara (39–53).
- **mara3:** `File`'s `lines` and `tokens` point at `line_slice := lines[:.cap]` and
  `token_slice := tokens[:.cap]` (compiler.mara:86–90), and lex appends through them. They
  would point at the lists, `&lines` and `&tokens`. The user's code: they move it.
- **view:** none traced. The 15 appends through `^[]T` variables are to be checked when the
  checker errors are on.
- **tests:** the checker errors will list them.

## Order of work

1. You decide 1–5.
2. The checker errors are first a probe only, a list per code base from no-link builds:
   stdlib, tests, docs, view, Pounce, sooblivion and mara3.
3. The stdlib changes: reads, arenas, `filter`/`group`, `dir_read`.
4. The compiler: errors on, the no-len machinery out, slicing back to its window, the append
   speed kept and measured.
5. Tests, docs, view and Pounce moved. Then the no-link sweep, and the suite once.
6. sooblivion's and mara3's lists go to you. Release when sooblivion has moved.
