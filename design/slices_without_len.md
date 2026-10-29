# Slices without a len: plan

Written 2026-10-29, after the user's call: "If you want appendable storage, get a list."
Revised the same day twice:
- a mutable list is `^[$N]T`, and a mutable slice `^[]T` is a writable view that can't grow;
- a slice is a pointer and a count, 16 bytes, with no len field. cstring's rule stays: a
  slice passes only when its 0 is inside it;
- the user's decisions: a list loops and slices up to its len (`x[:]`, `x[lo:]` included),
  and a read gives back a slice of what came.

Not started. It replaces the no-len slices, `start_fill` and len inheritance built the same
day (6748dfd, 0afb7b6, 79522bc, 6bbdec0).

## Status (2026-10-29)

- 4be1308: the compiler and stdlib back to before the no-len work; a slicing shows its window.
- e2a920b: only lists grow — appends, next and storage take `^[$N]T`; a take is a view of n.
- de4dd15: the readers give back the slice they filled.
- e705e8b: arenas keep a `used` cursor; the bindings take text for C as `[$N]utf8`.
- 7aee70b: a slice's len and cap can't be written; nothing is taken from a slice.
- The layout: a slice is {len, ptr}, 16 bytes; a `^[]T` is {where the len is, the data},
  16 bytes too (a reference by value, not a pointer to a slice: `&list` as a `^[]T` needs no
  temporary, and sees the list's live len). A list given as a slice is a view of its items.
- Left: sooblivion and mara3 moved (their lists), then a release.

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

| Type | What it is | Size | Grows? |
|---|---|---:|---|
| `[N]T` | a list: its len (how many items), then its room of N | 8 + N items | yes |
| `^[N]T`, `^[$N]T` | a mutable list: a pointer to a list, of that room or of any | 8 | yes |
| `[]T` | a slice: a pointer and a count, a view; read-only as a param | 16 | no |
| `^[]T` | a mutable slice: a pointer to a slice, a writable view | 8 | no |

- **Only lists grow.** Appends, `next`, takes from storage and `.len =` writes take a list or
  a mutable list. The stdlib's appends take `dst: ^[$N]$T`, so `&view + x` has nothing to
  call.
- **A slice has one count**, how many items it shows. `.len` and `.cap` both read it: for a
  view they're the same number, and the reads of `.len` everywhere (574 in sooblivion, and
  every `for k in 0:xs.len`) stay as they are. Neither can be written. For a smaller view,
  reslice it: `s = s[0:n]`.
- **A mutable slice `^[]T`** can write the items of the view it points at, and can replace that
  view whole: `rest^ = rest^[n:]`, a cursor the callee moves along. It can't grow it. It is
  what a function takes to write into part of a caller's memory: a file read into a window of
  a buffer, a sort in place, font's coverage buffer. `[]T` params are read-only (the copy
  rule). A mutable list given where a mutable slice goes (`sort(&list)`) points at a view of
  its items.
- **A slicing `x[a:b]`** shows exactly its b - a items, whatever x's len. With no hi,
  `x[:]` and `x[lo:]` of a list end at its len: its items, as a loop over it does. (Of a
  slice, at its count; of a fixed array, at its size.) To see a list's room past its items,
  say so: `x[0 : x.cap]`.
- **A list given where a slice goes** is a view of its items: its count is the list's len.
  The room past them isn't in the view.
- **Indexing a slice** is checked against its count, as today. A list's indexing stays checked
  against its room, N: its room is memory you can write by index.
- **cstring doesn't change:** it never copies, and it checks for a 0. A list passes when its
  0 is in its room, at `list[len]`, as today. A slice passes when its 0 is its last item: slice
  it with the 0 at the end (`buf[0 : buf.len + 1]`; a list's appends write a 0 after its
  text). A text literal or a list given where a slice goes no longer has its 0 in the view,
  so `cstring` of it stops the program.
  - **Bindings that hand text to C take a list of known room** (`str256`, `Path`), not
    `[]utf8`: its 0 is in reach and nothing is copied. A literal fits any list it fits in.
    The SDL bindings have 16 cstring calls, the OpenGL ones 4. os.mara's paths already go
    through `c_path`, which copies.

## What `^[$N]T` costs

- **One copy of a function per room size it's called with.** For the appends, which are tiny
  and inlined in release builds, that's nothing there and more code in debug builds. For
  functions that take storage (`read_entire_file`, `dir_read`, font loading, sooblivion's
  readers), it's one copy per storage size. sooblivion's rooms come in a few fixed sizes.
- **A struct field names its room** (`lines: ^[MB]i64`), or the struct becomes generic over it.
- **Nothing sized at run time is a list**, as now. Rooms carved with a count known only at run
  time are views, with a count kept beside them.

## Decided

1. **`x[:]` and `x[lo:]` of a list end at its len** (the user, 2026-10-29: "list can loop and
   slice up to len"). Today's cap bound in lw_slice goes.
2. **A read gives back a slice of what came** (the user: "file_read could just return a
   slice. Its len/cap would be the number of bytes read"). It takes the window to read into,
   a mutable slice, and returns the part of it that was filled:
   `got := file_read(id, &room)?`, `got.len` the bytes read. It reads into any part of any
   memory: a window of a big buffer (`view := buf[at : at + want]`), or a list's room
   (`view := list[0 : list.cap]`).

## The compiler

- **The slice layout:** a slice is {ptr, count}, 16 bytes; a mutable slice is a pointer to
  one, 8 bytes, not today's 24-byte reference {where the len is, the cap, the data}. A list's
  layout, {len, [N]T}, doesn't change. The places that know the layout:
  - layout.odin (`slice_header_fields`, `slice_ref_layout`) and the IR types (`SLICE_IR_TYPE`,
    `slice_ref_ir_type`; codegen.odin's `SLICE` field numbers);
  - the emitter: every header it builds or reads (`emit_build_temp_slice`,
    `emit_slice_header_at`, the held views, `slice_ref_to`, `llvm_write_through_ref`, the list
    and atom views made in `.Cast`, takes, byte views, `llvm_copy_into`, `llvm_elements_into`,
    from_text, cstring, print);
  - the C ABI (abi.odin classes a slice as memory, "exceeds an eightbyte": at 16 bytes it's
    two);
  - debug info (codeview.odin's slice record and its raddbg view, `array(ptr, len)`);
  - the runtime (mara_mem.c's `Mara_Header` and `Mara_Slice_Ref`);
  - the constant tables (codegen_const.odin) and `main`'s args (codegen_module.odin builds
    them as {len, cap, ptr}).
- **Checker errors**, each at the place it happens:
  - an append into a slice, or through a mutable slice: "a slice can't grow: append to a
    list, or a `^[$N]T` pointing at one". The dispatch finds no add for it, so the error is
    worded for that case.
  - a `.len =` or `.cap =` write on a slice: "a slice's count is its size: reslice it";
  - a take from a slice (`slice([:n]T, &view)`, `let(T, &view)`), and `next(&view)`.
- **Taken out:** the no-len bit (SLICE_NO_LEN, emit_no_len, emit_len_count and the masks on
  len reads), emit_window_len, the `start_fill` builtin and its Carve "fill", and the cap bound
  lw_slice gives an open end (decided: 1).
- **cstring:** for a slice, the check is its last item (`s[count - 1] == 0`); for a list,
  `list[len]` within N, as today.
- **Kept: the append speed.** 200M appends take 0.094 s now and took 0.38 s before. The gain
  came from LLVM knowing the len it appends at isn't negative, which `start_fill`'s value told
  it. With `^[$N]T`, each copy knows its N, so the room check is against a constant. The len's
  non-negativity can come from range information on a list's len loads (0 ..= N). Measure it
  with the scratchpad bench (`bench_nolen.mara`) before and after.
- **Gained:** a slice fits in two registers when it's passed.

## The stdlib

- **Appends:** `slice_add`, `slice_add_item`, `utf8_add`, `utf8_add_item` and `next` take
  `^[$N]$T` (text, `^[$N]utf8`). Their bodies are as before 6748dfd.
- **Storage:** `read_entire_file`, `dir_read`, `filter`, `filter2` and `group` take
  `storage: ^[$N]byte`. Takes (`slice([:n]T, &storage)`, `let`) need a list or a mutable list
  as storage.
- **Reads** (decided: 2): `file_read`, `pipe_read`, `udp_receive` and `tcp_receive`, on
  Windows and Linux, take `data: ^[]byte`, the window to read into, and give back the slice of
  it that was filled, beside what they give back today: `file_read(id, data: ^[]byte) ->
  []byte, err`; `pipe_read` and `tcp_receive` keep their bool for "still open", `udp_receive`
  its bool for "a packet came" and the sender.
- **`read_entire_file`** reads each piece into a window of storage past its len, adds up what
  came, then moves storage's len once.
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
- **The SDL and OpenGL bindings** take text for C as lists of known room (see cstring above).

## Code outside the compiler

These lists come from the probe. The checker errors will give the exact sites.

- **sooblivion:**
  - The 90 load rooms: `Load_Room`'s fields become `^[64 * MB]byte`, `^[16 * MB]byte` and so
    on, `load_room` keeps the four list pointers, and `room.file.len = 0` empties the list
    itself.
  - The 65 carved rooms are written by index with a count.
  - The 16 reads take a window and use the slice given back.
  - The 165 params that grow what they point at become `^[$N]T`.
  - Text it hands the bindings goes as lists. A slice or a literal given to them is now a
    type error, so the checker lists them.
  - sooblivion takes releases, so the release waits until it has moved.
- **Pounce (11):** 4 `file_read` calls in cache.mara (223, 253, 267, 286) and 7 appends in
  gfx_mesh_generation.mara (39–53). Its shader text goes to OpenGL's binding.
- **mara3:** `File`'s `lines` and `tokens` point at `line_slice := lines[:.cap]` and
  `token_slice := tokens[:.cap]` (compiler.mara:86–90), and lex appends through them. They
  would be `^[MB]i64` and `^[MB]Token`, pointing at `&lines` and `&tokens`. The user's code:
  they move it.
- **view:** none traced. The 15 appends through `^[]T` variables are to be checked when the
  checker errors are on.
- **tests:** the checker errors will list them.

## Order of work

1. Decided (see above).
2. The checker errors are first a probe only, a list per code base from no-link builds:
   stdlib, tests, docs, view, Pounce, sooblivion and mara3.
3. The stdlib changes: the appends and storage functions to `^[$N]T`, reads, arenas,
   `filter`/`group`, `dir_read`, the bindings' text as lists.
4. The compiler, on today's layout first: errors on, the no-len machinery out, slicing back to
   its window, cstring's check for slices, the append speed kept and measured.
5. Then the layout: a slice to {ptr, count}, a mutable slice to a pointer. The suite checks
   the two steps apart.
6. Tests, docs, view and Pounce moved. Then the no-link sweep, and the suite once per step.
7. sooblivion's and mara3's lists go to you. Release when sooblivion has moved.
