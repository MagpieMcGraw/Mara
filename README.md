# Mara

A small, statically-typed systems programming language. Compiles to LLVM IR
and then to a native executable via a bundled clang + lld toolchain. Pure
hobby project — built in the open as I figure out what shape I want it to
have.

Status: early. Windows-only for now (Linux port in progress); ABI not stable;
expect rough edges. The test fixtures pass and the included [Pounce](Pounce/)
game project builds and runs against it.

## What it looks like

```mara
module hello

main :: fun() {
    print("Hello, Mara")
}
```

Slices use a sized-declaration form and a `take` builtin that carves typed
regions out of a backing buffer:

```mara
buf : []byte(256)              // backing storage, cursor starts at 0

p : Pair = take(Pair, &buf)    // carve a Pair; cursor advances by sizeof(Pair)
p.a = 7
p.b = 11

nums : [4]i64 = take([4]i64, &buf)
nums[0] = 100
```

No `let` keyword; declarations are `name := value` for inference or
`name : Type = value` when you want a specific type.

Multi-return uses an explicit tuple return type:

```mara
divmod :: fun(a: i64, b: i64) -> (i64, i64) {
    return a / b, a % b
}

q, r := divmod(17, 5)
```

## Building the compiler

The Mara compiler is written in [Odin](https://odin-lang.org/). To rebuild
it from source you need Odin on PATH; everything else (clang, lld) ships in
[`tools/`](tools/).

```
odin build .
```

That produces `Mara.exe` in the repo root. The build relies on `core:sys/windows`
on Windows and `os.read_link` on Linux to find its own exe path; both are in
Odin's core, no extra packages required.

## Using Mara

One command, with `cwd` set to the directory containing your `.mara` files:

```
mara build [<package-name>]
```

If you don't pass a package name, Mara infers it from the current directory's
name. Files in `cwd` are grouped by their `module <name>` declaration; the
package whose name you asked for is the entry point.

Flags:

- `-web` — build for browser via Emscripten (emits `pkg.html` + a wasm).
  Requires Emscripten installed at the path baked into `main.odin`;
  you'll need to edit that for now.
- `-dump` — write the post-typecheck program to `checked_dump.txt` and stop.
  Useful for debugging the type checker.

Build pipeline (each stage timed in the perf summary printed at the end):

```
discover  →  lex  →  parse  →  type check  →  codegen  →  link
```

The whole compilation lives in a single growing arena; the OS reclaims it
at process exit. No incremental builds yet — every `mara build` is a fresh
compile.

## Project layout

```
.                       Mara compiler source (Odin)
code/                   Mara standard library + FFI bindings
  *.mara                stdlib modules (module mara.math, mara.memory, ...)
  SDL/, SDL2/           SDL bindings
  Open_GL/              OpenGL function-pointer loader
Pounce/                 Game project used as the main compiler test target
test/                   Small `.mara` test fixtures
  failures/             Intentional-failure fixtures (not picked up by discovery)
tools/                  Bundled clang + lld-link binaries (Windows)
compiler_dir_*.odin     Per-OS exe-path discovery
c_api.odin              `proc "c"` exports for foreign drivers
```

## Foreign blocks

A `foreign` block binds names from a native library:

```mara
foreign static_lib "kernel32" {
    fun GetTickCount() -> u32
}

foreign dynamic_lib "SDL3" {
    fun SDL_Init(flags: u32) -> i32
}
```

`static_lib` links at build time (`-lname` to the linker, or `<name>.lib`-style
on Windows). `dynamic_lib` emits a runtime loader that calls
`LoadLibraryA`/`GetProcAddress` on Windows or `dlopen`/`dlsym` on Linux at
program startup. The bound function names then resolve through function-pointer
globals — no per-call lookup overhead.

You can also pass precompiled object/library files directly:

```mara
foreign static_lib "my_helper.o" { ... }
foreign static_lib "my_helper.a" { ... }
```

Mara resolves the file from `code/<name>/` or the project directory.

## Things that aren't done yet

- Linux port: compiler-side work is in place, but the stdlib's `#linux`
  branch in `code/os.mara` is missing `mmap`-based virtual memory and
  `dlopen`-based dynamic loading. Anything using `context.scope_allocator`
  (i.e. arenas) won't link on Linux until those wrappers exist.
- Error system: no `try` / typed errors yet. Today, errors are checked
  manually at FFI boundaries; runtime safety checks (bounds, null, div-by-zero)
  print a message and `exit(1)`.
- Generics / parametric polymorphism: limited (`fun foo($T)` exists; most
  builtins are still hard-coded per type).
- Documentation: this file is essentially it.

## License

See [LICENSE](LICENSE).
