# Mara

Is a vibe-coded programming language. Directed by me, and written by Claude Opus 4.6 and 4.7. Mara's birthday is 3 Feb 2026.

## What it looks like

Hello world looks like this

```mara
module hello

main :: fun() {
    print("Hello there!")
}
```

And real code looks like that

![main loop](readme/mainloop.png)

Main feature of Mara is stack-like memory allocation. Everything in Mara lives until the end of scope. You can get data out of functions by returning it, or by passing in a block of memory and writing to it.

![basic mesh loading](readme/prim.png)

## Building the compiler

The Mara compiler is written in [Odin](https://odin-lang.org/). You need
Odin on PATH to compile it. From the repo root:

```
odin build .
```

That produces `Mara.exe` (Windows) or `Mara` (Linux) in the repo root.

### Windows

Everything else (clang, lld) ships in [`tools/`](tools/). Nothing to install.

### Linux

System packages required (Fedora examples — Debian/Ubuntu names in parens):

```
sudo dnf install clang lld SDL2-devel    # (apt: clang lld libsdl2-dev)
```

Mara invokes system `clang` and `ld.lld` via PATH. The `tools/*.exe` in this
repo are Windows-only and harmlessly ignored on Linux. No precompiled libs
or extra build steps needed — Mara resolves foreign blocks like
`foreign static_lib "open_gl"` by looking for a precompiled `.lib` (Windows)
or `.a` (Linux/macOS) under `code/<binding>/`. If neither exists but a
matching `.c` source is there, Mara compiles it into a static lib alongside
on the first build — subsequent builds find the cached artifact and skip
the compile step. On Linux this means the first build of a project that
uses `open_gl` produces `code/Open_GL/open_gl.a` automatically; later builds
reuse it.

## Using Mara

Go to the folder where you have your Mara source code and type

```
mara build <module-name>
```

If you don't pass a module name, Mara infers it from the current folder's
name. My typical workflow is:

```
cd C:\Code\Mara\Pounce
mara build
```

## Project layout

Mara std lib is in the code folder. We don't have much at the moment. We do have some partial SDL bindings.

If you want example code, look in the Pounce folder. It's an empty open_gl project. Opens a window, draws a square, takes input.

## License

See [LICENSE](LICENSE).
