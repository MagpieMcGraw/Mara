package mara

import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:slice"
import "core:strings"
import "core:c/libc"
import "core:path/filepath"

// get_compiler_dir lives in platform-suffixed files (compiler_dir_windows.odin,
// compiler_dir_linux.odin) — each uses its native API to find the exe path.

// ---------------------------------------------------------------------------
// Platform-specific filenames + extensions
// ---------------------------------------------------------------------------

// Native executable extension. Windows binaries are `.exe`; POSIX has none.
NATIVE_EXE_EXT :: ".exe" when ODIN_OS == .Windows else ""

// Bundled clang's filename inside tools/. We ship a Windows clang in this
// repo; on Linux we expect the user's system clang on PATH (apt install clang),
// so the "bundled" name is just `clang` and we resolve through PATH at exec.
CLANG_BIN :: "clang.exe" when ODIN_OS == .Windows else "clang"

// Static-library extension per target. Used when a `foreign static_lib "name"`
// block names a bare identifier (no extension) — Mara looks in code/<binding>/
// for `name<STATIC_LIB_EXT>` and passes it to the linker as a file input.
// Falls back to `-l<name>` if no bundled file exists, so system libs still
// work without the user spelling out their extension.
STATIC_LIB_EXT :: ".lib" when ODIN_OS == .Windows else ".a"

// ---------------------------------------------------------------------------
// Stage 1: discovery — find every .mara file the compiler can see
// ---------------------------------------------------------------------------

// Read just enough of `source` to know which `module <name>` (or `package
// <name>`) it declares. Returns "" when the source doesn't start with a
// module/package declaration. Skips leading whitespace + // line comments.
extract_package_name :: proc(source: string) -> string {
    i := 0
    for i < len(source) && (source[i] == ' ' || source[i] == '\t' || source[i] == '\r' || source[i] == '\n') {
        i += 1
    }
    for i + 1 < len(source) && source[i] == '/' && source[i+1] == '/' {
        for i < len(source) && source[i] != '\n' { i += 1 }
        for i < len(source) && (source[i] == ' ' || source[i] == '\t' || source[i] == '\r' || source[i] == '\n') {
            i += 1
        }
    }
    rest := source[i:]
    is_package := strings.has_prefix(rest, "package ") || strings.has_prefix(rest, "package\t")
    is_module  := strings.has_prefix(rest, "module ")  || strings.has_prefix(rest, "module\t")
    if !is_package && !is_module { return "" }
    j := 7 if is_package else 6
    for j < len(rest) && (rest[j] == ' ' || rest[j] == '\t') { j += 1 }
    name_start := j
    // Module names may be dotted (`module mara.math`); accept dots/underscores
    // so the full identity survives.
    for j < len(rest) && (is_alpha(rest[j]) || is_digit(rest[j]) || rest[j] == '.' || rest[j] == '_') {
        j += 1
    }
    if j == name_start { return "" }
    return rest[name_start:j]
}

// Walk every .mara source dir the compiler knows about and index files by
// their declared module name. User-package files shadow stdlib files of the
// same name. Order of scans:
//
//   1. <compiler_dir>/code/           — stdlib loose .mara files
//   2. <compiler_dir>/code/*/         — binding subfolders (SDL/, Open_GL/, ...)
//   3. <search_dir>                   — user project (overrides on conflict)
discover_all_files :: proc(compiler_dir: string, search_dir: string) -> map[string][dynamic]string {
    result: map[string][dynamic]string

    scan_dir :: proc(dir: string, out: ^map[string][dynamic]string) {
        dh, err := os.open(dir)
        if err != nil { return }
        defer os.close(dh)
        entries, _ := os.read_dir(dh, -1, context.allocator)
        for entry in entries {
            if entry.type == .Directory { continue }
            if !strings.has_suffix(entry.name, ".mara") { continue }
            path, _ := filepath.join({dir, entry.name})
            data, rerr := os.read_entire_file_from_path(path, context.allocator)
            if rerr != nil { continue }
            pkg := extract_package_name(string(data))
            if pkg == "" { continue }
            if pkg not_in out^ { out^[pkg] = {} }
            append(&out^[pkg], path)
        }
    }

    if compiler_dir != "" {
        code_dir, _ := filepath.join({compiler_dir, "code"})
        scan_dir(code_dir, &result)
        if dh, err := os.open(code_dir); err == nil {
            defer os.close(dh)
            entries, _ := os.read_dir(dh, -1, context.allocator)
            for entry in entries {
                if entry.type != .Directory { continue }
                sub, _ := filepath.join({code_dir, entry.name})
                scan_dir(sub, &result)
            }
        }
    }

    // User project files shadow stdlib bare names on conflict.
    user: map[string][dynamic]string
    scan_dir(search_dir, &user)
    for name, files in user { result[name] = files }

    return result
}

// ---------------------------------------------------------------------------
// Stage 2 + 3: lex + parse, driven by the target's use-closure
// ---------------------------------------------------------------------------

// Collect every `use`/`include` path referenced at the top of a parsed stmt.
// Mirrors the shape the type checker uses in its use-graph walk: bare
// `use path` lowers to Stmt_Decl with an Expr_Include init; aliased
// `name :: use path` lowers to Stmt_Define; the older `name := use path`
// spelling lands as Stmt_Assign. Stmt_Multi_Assign rolls up multiple at once.
collect_include_paths :: proc(stmt: Stmt, out: ^[dynamic]string) {
    #partial switch s in stmt {
    case ^Stmt_Decl:
        for v in s.init_values {
            if inc, ok := v.(^Expr_Include); ok { append(out, inc.path) }
        }
    case ^Stmt_Assign:
        if inc, ok := s.value.(^Expr_Include); ok { append(out, inc.path) }
    case ^Stmt_Define:
        if inc, ok := s.value.(^Expr_Include); ok { append(out, inc.path) }
    case ^Stmt_Multi_Assign:
        for a in s.assigns {
            if inc, ok := a.value.(^Expr_Include); ok { append(out, inc.path) }
        }
    }
}

// Lex + parse only the modules reachable from `target`. Seeds a worklist with
// `target`, parses each module's files in sorted path order, walks the
// resulting AST for `use`/`include`, and enqueues every discovered module
// matching that path (exact match plus dotted submodules — same prefix rule
// the type checker's find_matching_modules uses). Modules outside this
// closure are left untouched: their parse errors never run, their tokens
// never get allocated. Without this, an unrelated `.mara` file in the search
// directory would dump its parse errors into the user's terminal even though
// it has no bearing on the build.
parse_target_closure :: proc(files: map[string][dynamic]string, target: string) -> (programs: map[string]^Program, errors: map[string]int) {
    visited: map[string]bool
    worklist: [dynamic]string
    append(&worklist, target)

    for len(worklist) > 0 {
        module := pop(&worklist)
        if visited[module] { continue }
        visited[module] = true

        paths, has := files[module]
        if !has { continue }  // missing module — the type checker will diagnose if it matters

        ordered := slice.clone(paths[:])
        slice.sort(ordered)

        merged := new(Program)
        module_errors := 0
        for path in ordered {
            data, rerr := os.read_entire_file_from_path(path, context.allocator)
            if rerr != nil {
                fmt.printf("Error: could not read '%s'\n", path)
                os.exit(1)
            }
            tokens := lex_all(string(data), path)
            p := parser_init(tokens)
            parsed := parse_program(p)
            for stmt in parsed^ { append(merged, stmt) }
            module_errors += p.errors
        }
        programs[module] = merged
        if module_errors > 0 { errors[module] = module_errors }

        // Walk the merged AST for use/include paths, enqueue every matching
        // discovered module (exact + dotted submodules).
        deps: [dynamic]string
        defer delete(deps)
        for stmt in merged^ {
            collect_include_paths(stmt, &deps)
        }
        for path in deps {
            prefix_dot := strings.concatenate({path, "."})
            for fmod in files {
                if fmod == path || strings.has_prefix(fmod, prefix_dot) {
                    if !visited[fmod] { append(&worklist, fmod) }
                }
            }
        }
    }
    return programs, errors
}

// ---------------------------------------------------------------------------
// Linking — native (lld-link) and web (emcc) paths
// ---------------------------------------------------------------------------

// emcc is a Python script (emcc.bat -> emcc.py); its launcher needs
// EMSDK_PYTHON to find the bundled Python under emsdk/python/.
EMSDK_DIR    :: `C:\Apps\Emscripten`
EMCC_PATH    :: `"C:\Apps\Emscripten\upstream\emscripten\emcc.bat"`
EMSDK_PYTHON :: `"C:\Apps\Emscripten\python\3.13.3_64bit\python.exe"`

Link_Flags :: struct {
    // Web path (emcc) keeps clang-style flags as pre-formatted strings.
    lib_flags:    string,
    extra_inputs: string,  // .c / .o / .obj / .lib / .a — passed directly to emcc/lld-link
    // Native path (lld-link) consumes raw names + dirs and formats them itself
    // (lld-link wants `<name>.lib` and `/libpath:<dir>`, not -l/-L).
    native_libs:   [dynamic]string,
    native_search: [dynamic]string,
    ok:           bool,
}

// True if `name` looks like a file we hand to clang/lld directly (source or
// precompiled) rather than a bare library name we resolve through `-l<name>`.
is_foreign_file :: proc(name: string) -> bool {
    return strings.has_suffix(name, ".c")   ||
           strings.has_suffix(name, ".o")   ||
           strings.has_suffix(name, ".obj") ||
           strings.has_suffix(name, ".lib") ||
           strings.has_suffix(name, ".a")
}

// Map a foreign library to its emscripten equivalent when building for web.
emscripten_port_flag :: proc(lib: string) -> (flag: string, ok: bool) {
    switch lib {
    case "SDL2":       return "-sUSE_SDL=2", true
    case "SDL3":       return "-sUSE_SDL=3", true
    case "opengl32":   return "", true  // WebGL resolves through emcc runtime
    case "emscripten": return "", true  // emcc's own runtime functions
    case:              return "", false
    }
}

// Compile a C source into a precompiled static lib next to it. Used by the
// foreign-block resolver: a foreign `static_lib "foo"` block with no
// existing `foo.lib` / `foo.a` but with a `foo.c` sibling triggers this to
// produce the missing static lib once, after which subsequent builds use
// the cached output directly.
//
// Returns true on success. Prints a diagnostic and returns false on failure;
// the caller decides whether to abort or fall through.
//
// Two steps regardless of OS:
//   1. clang -c <c_path> -o <c_path>.o
//   2. Wrap the object into a static lib:
//        Windows: lld-link /lib /out:<lib_path> <obj_path>   (bundled lld-link)
//        POSIX:   ar rcs <lib_path> <obj_path>               (system binutils)
// The intermediate .o is deleted after the archive succeeds.
compile_c_to_static_lib :: proc(c_path, lib_path, compiler_dir: string) -> bool {
    obj_path := strings.concatenate({c_path[:len(c_path)-2], ".o"})

    // Pass -I <c_path's dir> so the source can `#include "neighbor.h"` against
    // headers sitting next to it. Quoted-form includes (`#include "x.h"`) already
    // resolve relative to the file doing the include, but for the wrapper-and-
    // amalgamate pattern — and any future case where the .c reaches for sibling
    // headers via plain names — having -I makes the lookup unambiguous.
    c_dir := filepath.dir(c_path)

    // ---- Step 1: compile .c to .o
    compile_cmd: string
    when ODIN_OS == .Windows {
        clang_path, _ := filepath.join({compiler_dir, "tools", CLANG_BIN})
        inner_c := strings.concatenate({`"`, clang_path, `" -c "`, c_path, `" -o "`, obj_path, `" -I "`, c_dir, `"`})
        compile_cmd = strings.concatenate({`"`, inner_c, `"`})
    } else {
        compile_cmd = strings.concatenate({CLANG_BIN, ` -c "`, c_path, `" -o "`, obj_path, `" -I "`, c_dir, `"`})
    }
    if libc.system(strings.clone_to_cstring(compile_cmd)) != 0 {
        fmt.printf("Error: clang failed to compile '%s'\n", c_path)
        return false
    }

    // ---- Step 2: wrap .o into static lib
    archive_cmd: string
    when ODIN_OS == .Windows {
        lld_path, _ := filepath.join({compiler_dir, "tools", "lld-link.exe"})
        inner_a := strings.concatenate({`"`, lld_path, `" /lib /out:"`, lib_path, `" "`, obj_path, `"`})
        archive_cmd = strings.concatenate({`"`, inner_a, `"`})
    } else {
        archive_cmd = strings.concatenate({`ar rcs "`, lib_path, `" "`, obj_path, `"`})
    }
    if libc.system(strings.clone_to_cstring(archive_cmd)) != 0 {
        fmt.printf("Error: archive creation failed for '%s'\n", lib_path)
        return false
    }

    // Best-effort cleanup of the intermediate object; harmless if it fails.
    os.remove(obj_path)
    return true
}

// Translate well-known cross-platform system-library names whose system
// linker convention differs by OS. Foreign blocks can use the Windows name
// (the historical first target) and Mara silently emits the equivalent
// `-l<name>` on Linux/macOS. Keep entries narrow — only true cross-platform
// libs that have a stable counterpart, not "Windows-specific symbol that
// happens to exist on Linux too."
translate_system_lib :: proc(name: string) -> string {
    when ODIN_OS == .Linux {
        switch name {
        case "opengl32": return "GL"  // Windows opengl32.lib -> Linux libGL.so
        }
    } else when ODIN_OS == .Darwin {
        switch name {
        case "opengl32": return "GL"  // macOS also exposes libGL (Frameworks would be better)
        }
    }
    return name
}

build_link_flags :: proc(checked: ^Checked_Program, web: bool = false) -> Link_Flags {
    lib_flags_b:    strings.Builder
    extra_inputs_b: strings.Builder
    seen_libs:      map[string]bool

    compiler_dir := get_compiler_dir()

    resolve_foreign_file :: proc(name: string, compiler_dir: string) -> string {
        code_base, _  := filepath.join({compiler_dir, "code"})
        loose_path, _ := filepath.join({code_base, name})
        if os.exists(loose_path) { return loose_path }
        ldh, lerr := os.open(code_base)
        if lerr == nil {
            defer os.close(ldh)
            lentries, _ := os.read_dir(ldh, -1, context.allocator)
            for lentry in lentries {
                if lentry.type != .Directory { continue }
                sub_path, _ := filepath.join({code_base, lentry.name, name})
                if os.exists(sub_path) { return sub_path }
            }
        }
        fmt.printf("Error: foreign file '%s' not found under %s\n", name, code_base)
        os.exit(1)
    }

    // Locate `<name>.c` under code/ (root or one-level subdir) and *always*
    // re-compile it into a sibling `<name><STATIC_LIB_EXT>`, returning the
    // resulting library path.
    //
    // Triggered by the explicit "force recompile" form of foreign blocks:
    // `foreign static_lib "raylib.c"` says "treat this source as live —
    // rebuild the static lib every link." Unlike try_resolve_bundled_lib
    // (which caches forever), this overwrites any existing .lib on every
    // build. Once the source is stable, switch the foreign block to the
    // bare name (`"raylib"`) so subsequent builds reuse the cached output.
    force_recompile_bundled_lib :: proc(c_name: string, compiler_dir: string) -> (string, bool) {
        // Caller already checked the `.c` suffix; strip it for the lib name.
        base := c_name[:len(c_name) - 2]
        lib_name := strings.concatenate({base, STATIC_LIB_EXT})
        code_base, _ := filepath.join({compiler_dir, "code"})

        compile_in :: proc(dir, c_file, lib_name, compiler_dir: string) -> (string, bool) {
            c_path, _ := filepath.join({dir, c_file})
            if !os.exists(c_path) { return "", false }
            lib_path, _ := filepath.join({dir, lib_name})
            if !compile_c_to_static_lib(c_path, lib_path, compiler_dir) {
                fmt.printf("Error: forced recompile of '%s' failed\n", c_path)
                os.exit(1)
            }
            return lib_path, true
        }

        if path, ok := compile_in(code_base, c_name, lib_name, compiler_dir); ok {
            return path, true
        }
        ldh, lerr := os.open(code_base)
        if lerr != nil { return "", false }
        defer os.close(ldh)
        entries, _ := os.read_dir(ldh, -1, context.allocator)
        for entry in entries {
            if entry.type != .Directory { continue }
            sub, _ := filepath.join({code_base, entry.name})
            if path, ok := compile_in(sub, c_name, lib_name, compiler_dir); ok {
                return path, true
            }
        }
        return "", false
    }

    // Look for a bundled lib backing for a bare-name foreign reference under
    // code/*. Returns the path to a static lib usable as a linker input, or
    // ("", false) if no match exists (caller falls back to `-l<name>`).
    //
    // Resolution per directory: if `<name><STATIC_LIB_EXT>` already exists,
    // use it. Otherwise, if `<name>.c` exists, compile it into a static lib
    // alongside (one-time cost; subsequent builds find the cached lib on the
    // first branch). The `.c` -> `.lib`/`.a` compile uses bundled clang on
    // Windows and system clang on Linux.
    try_resolve_bundled_lib :: proc(name: string, compiler_dir: string) -> (string, bool) {
        lib_name := strings.concatenate({name, STATIC_LIB_EXT})
        c_name   := strings.concatenate({name, ".c"})
        code_base, _ := filepath.join({compiler_dir, "code"})

        // Per-directory check: returns the static-lib path if a `.lib`/`.a`
        // is present, OR if a `.c` exists that can be compiled into one.
        check :: proc(dir: string, lib_name, c_name, compiler_dir: string) -> (string, bool) {
            lib_path, _ := filepath.join({dir, lib_name})
            if os.exists(lib_path) { return lib_path, true }
            c_path, _ := filepath.join({dir, c_name})
            if os.exists(c_path) {
                if compile_c_to_static_lib(c_path, lib_path, compiler_dir) {
                    return lib_path, true
                }
                // Compile failed — abort. Falling through to `-l<name>` would
                // hide the real error behind a confusing linker complaint.
                fmt.printf("Error: failed to build static lib from '%s'\n", c_path)
                os.exit(1)
            }
            return "", false
        }

        // Check code/ root first (stdlib bundled libs)
        if path, ok := check(code_base, lib_name, c_name, compiler_dir); ok {
            return path, true
        }
        // Then each subfolder of code/ (one level deep, e.g. code/SDL/)
        ldh, lerr := os.open(code_base)
        if lerr == nil {
            defer os.close(ldh)
            entries, _ := os.read_dir(ldh, -1, context.allocator)
            for entry in entries {
                if entry.type != .Directory { continue }
                sub, _ := filepath.join({code_base, entry.name})
                if path, ok := check(sub, lib_name, c_name, compiler_dir); ok {
                    return path, true
                }
            }
        }
        // Finally, the user's current working directory — project-local C
        // sources (e.g. a test fixture or a project-private helper) sit next
        // to the .mara that consumes them instead of needing a slot under
        // code/. Skip if cwd already happens to be code_base.
        cwd, _ := os.get_working_directory(context.allocator)
        if cwd != code_base {
            if path, ok := check(cwd, lib_name, c_name, compiler_dir); ok {
                return path, true
            }
        }
        return "", false
    }

    if web {
        all_libs: map[string]bool
        for _, cs in checked.functions {
            if fo, is_foreign := cs.origin.(Origin_Foreign); is_foreign {
                all_libs[fo.library] = true
            }
        }
        for lib in checked.foreign_libs { all_libs[lib] = true }
        ok := true
        for lib in all_libs {
            if is_foreign_file(lib) {
                resolved := resolve_foreign_file(lib, compiler_dir)
                strings.write_string(&extra_inputs_b, " ")
                strings.write_string(&extra_inputs_b, resolved)
                continue
            }
            flag, port_ok := emscripten_port_flag(lib)
            if !port_ok {
                fmt.printf("Error: foreign library '%s' has no known emscripten equivalent.\n", lib)
                fmt.printf("  Known web ports: SDL2, SDL3, opengl32. Rename the foreign block\n")
                fmt.printf("  to one of these, or compile the dependency from a .c source.\n")
                ok = false
                continue
            }
            if flag != "" {
                strings.write_string(&lib_flags_b, " ")
                strings.write_string(&lib_flags_b, flag)
            }
        }
        return Link_Flags{
            lib_flags    = strings.to_string(lib_flags_b),
            extra_inputs = strings.to_string(extra_inputs_b),
            ok           = ok,
        }
    }

    native_libs:   [dynamic]string
    native_search: [dynamic]string

    collect :: proc(libs: map[string]bool, seen: ^map[string]bool, src_b: ^strings.Builder, native_libs: ^[dynamic]string, compiler_dir: string) {
        for lib in libs {
            if lib in seen^ { continue }
            seen^[lib] = true
            // `.c` suffix = explicit "force recompile" form. Always rebuild
            // the static lib from source, then hand the .lib to the linker.
            // Same artifact the bare-name path would produce — so a user can
            // iterate with `"raylib.c"` and switch to `"raylib"` once stable,
            // reusing the freshly-built cache.
            if strings.has_suffix(lib, ".c") {
                if bundled, ok := force_recompile_bundled_lib(lib, compiler_dir); ok {
                    strings.write_string(src_b, " ")
                    strings.write_string(src_b, bundled)
                    continue
                }
                fmt.printf("Error: foreign source '%s' not found under code/\n", lib)
                os.exit(1)
            }
            if is_foreign_file(lib) {
                resolved := resolve_foreign_file(lib, compiler_dir)
                strings.write_string(src_b, " ")
                strings.write_string(src_b, resolved)
            } else if bundled, ok := try_resolve_bundled_lib(lib, compiler_dir); ok {
                // Bare name with a bundled OS-specific static lib (e.g. `open_gl`
                // resolves to code/Open_GL/open_gl.lib on Windows or
                // code/Open_GL/open_gl.a on Linux).
                strings.write_string(src_b, " ")
                strings.write_string(src_b, bundled)
            } else {
                // Bare name with no bundled match — let the linker find it in
                // system paths via `-l<name>` (e.g. SDL3, kernel32). Translate
                // well-known cross-platform libs whose name differs per OS
                // (e.g. Windows "opengl32" -> Linux "GL").
                append(native_libs, translate_system_lib(lib))
            }
        }
    }

    // Every foreign lib is static_lib now — hand them all to the linker.
    collect(checked.foreign_libs, &seen_libs, &extra_inputs_b, &native_libs, compiler_dir)

    code_base, _ := filepath.join({compiler_dir, "code"})
    ldh, lerr := os.open(code_base)
    if lerr == nil {
        defer os.close(ldh)
        lentries, _ := os.read_dir(ldh, -1, context.allocator)
        for lentry in lentries {
            if lentry.type != .Directory { continue }
            sub, _ := filepath.join({code_base, lentry.name})
            append(&native_search, sub)
        }
    }

    return Link_Flags{
        lib_flags     = strings.to_string(lib_flags_b),
        extra_inputs  = strings.to_string(extra_inputs_b),
        native_libs   = native_libs,
        native_search = native_search,
        ok            = true,
    }
}

// Native link step: invoke clang as the driver. Clang handles all the
// platform-specific glue (MSVC + Windows SDK lookup on Windows, libc /
// crt files on Linux), so this command shape is nearly identical across
// targets — only the executable name and output extension differ per OS.
//
// On Windows we use the bundled tools/clang.exe so users don't need to
// install LLVM separately. On Linux we use system clang via PATH (i.e.,
// `dnf install clang`) — bundling a Linux LLVM toolchain isn't a goal yet.
//
// -fuse-ld=lld points clang at lld-link.exe (bundled on Windows; lld via
// PATH on Linux). -Wno-override-module silences the warning our IR
// module's target triple triggers.
link_native :: proc(ll_path, exe_name: string, checked: ^Checked_Program, compiler_dir: string, shared: bool = false) -> bool {
    lf := build_link_flags(checked)
    if !lf.ok { return false }

    b: strings.Builder
    when ODIN_OS == .Windows {
        clang_path, _ := filepath.join({compiler_dir, "tools", CLANG_BIN})
        strings.write_byte(&b, '"'); strings.write_string(&b, clang_path); strings.write_byte(&b, '"')
    } else {
        strings.write_string(&b, CLANG_BIN)  // bare `clang`; resolved via PATH
    }
    strings.write_string(&b, " ")
    strings.write_string(&b, ll_path)
    strings.write_string(&b, lf.extra_inputs)
    strings.write_string(&b, ` -o "`); strings.write_string(&b, exe_name); strings.write_byte(&b, '"')
    // Always use lld for consistency across platforms. Windows finds
    // tools/lld-link.exe next to tools/clang.exe (bundled in this repo);
    // Linux/macOS expect `ld.lld` on PATH via the system `lld` package
    // (`dnf install lld` / `apt install lld`).
    strings.write_string(&b, " -Wno-override-module -fuse-ld=lld")
    // Shared mode: build a DLL/SO instead of an executable. clang's `-shared`
    // works across platforms — lld produces a .dll on Windows and a .so on
    // Linux. No entry-point symbol required (DllMain stub is auto-generated).
    if shared {
        strings.write_string(&b, " -shared")
    }
    for path in lf.native_search {
        strings.write_string(&b, ` "-L`); strings.write_string(&b, path); strings.write_byte(&b, '"')
    }
    for lib in lf.native_libs {
        strings.write_string(&b, " -l"); strings.write_string(&b, lib)
    }
    when ODIN_OS == .Linux {
        // libm provides sinf/cosf/floorf etc. — separate from libc on Linux
        // (Windows tucks math into the universal CRT, which clang already
        // links by default). Add unconditionally; cost is negligible if
        // unused, missing it produces "undefined reference to sinf" errors
        // for any program that touches math.
        strings.write_string(&b, " -lm")
    }

    cmd: string
    when ODIN_OS == .Windows {
        // cmd.exe quoting hack: a command starting with a quoted exe path AND
        // containing other quoted args confuses cmd.exe's quote stripping.
        // Wrapping the whole thing in another pair of quotes makes cmd.exe
        // treat the inner string as one literal command line.
        cmd = strings.concatenate({`"`, strings.to_string(b), `"`})
    } else {
        // POSIX shells (sh, bash, etc.) parse quotes sanely.
        cmd = strings.to_string(b)
    }

    cmd_cstr := strings.clone_to_cstring(cmd)
    ret := libc.system(cmd_cstr)
    if ret != 0 {
        fmt.printf("clang failed (exit code %d)\n", ret)
        return false
    }
    return true
}

// Web link step: emcc consumes the .ll directly. EMSDK_PYTHON is set inline
// so the user's shell environment doesn't need emsdk_env.bat to have run.
link_web :: proc(ll_path, exe_name: string, checked: ^Checked_Program) -> bool {
    lf := build_link_flags(checked, web = true)
    if !lf.ok { return false }
    cmd := strings.concatenate({
        "set EMSDK_PYTHON=", EMSDK_PYTHON, " && ",
        EMCC_PATH, " ", ll_path, lf.extra_inputs,
        " -o ", exe_name,
        " -Wno-override-module",
        // Pounce's arena alone wants 192MB; let the heap grow rather than
        // pre-committing a giant INITIAL_MEMORY.
        " -sALLOW_MEMORY_GROWTH=1",
        // WebGL2 lets us run GLES 3.0 shaders. Without MAX_WEBGL_VERSION=2,
        // SDL2 creates a WebGL1 context and 300-es shaders fail to compile.
        " -sMAX_WEBGL_VERSION=2 -sMIN_WEBGL_VERSION=2 -sFULL_ES3=1",
        lf.lib_flags,
    })
    cmd_cstr := strings.clone_to_cstring(cmd)
    ret := libc.system(cmd_cstr)
    if ret != 0 {
        fmt.printf("emcc failed (exit code %d)\n", ret)
        return false
    }
    return true
}

// ---------------------------------------------------------------------------
// Args + entry point
// ---------------------------------------------------------------------------

CLI_Args :: struct {
    pkg_name:     string,
    search_dir:   string,
    compiler_dir: string,
    web:          bool,
    shared:       bool,    // -shared — emit a .dll/.so instead of an executable
    dump:         bool,
    ok:           bool,
}

parse_args :: proc() -> CLI_Args {
    args: CLI_Args
    args.compiler_dir = get_compiler_dir()
    args.search_dir   = "."

    if len(os.args) < 2 {
        fmt.println("Usage: mara build [package-name] [-web] [-shared] [-dump]")
        return args
    }

    positional: [dynamic]string
    for arg in os.args {
        if arg == "-web"    { args.web    = true; continue }
        if arg == "-shared" { args.shared = true; continue }
        if arg == "-dump"   { args.dump   = true; continue }
        append(&positional, arg)
    }

    // positional[0] is the exe name itself. positional[1] should be "build".
    if len(positional) < 2 || positional[1] != "build" {
        fmt.println("Usage: mara build [package-name] [-web] [-shared] [-dump]")
        return args
    }

    if len(positional) >= 3 {
        args.pkg_name = positional[2]
    } else {
        // Infer pkg name from cwd.
        cwd, _ := os.get_working_directory(context.allocator)
        args.pkg_name = filepath.base(cwd)
    }
    args.ok = true
    return args
}

main :: proc() {
    // Whole compilation lives in one growing arena; OS reclaims at process exit.
    arena: virtual.Arena
    if virtual.arena_init_growing(&arena) == nil {
        context.allocator = virtual.arena_allocator(&arena)
    }

    args := parse_args()
    if !args.ok { return }

    perf: Performance_Timer
    perf_timer_begin(&perf, "discover")

    files := discover_all_files(args.compiler_dir, args.search_dir)

    // Validate up front that the requested package was discovered so the user
    // gets one clean error block rather than partial-build noise.
    missing := false
    if args.pkg_name not_in files {
        fmt.println("Error: no files found for the following modules:")
        fmt.printf("  %s\n", args.pkg_name)
        missing = true
    }
    if missing {
        fmt.println("Available modules:")
        for name in files { fmt.printf("  %s\n", name) }
        return
    }

    perf_timer_mark(&perf, "parse")
    programs, parse_errors := parse_target_closure(files, args.pkg_name)
    // Non-target parse errors are still surfaced (inline by the parser) for
    // modules the target actually imports; modules outside the use-closure
    // never get parsed, so unrelated `.mara` files in the search directory
    // can't dump diagnostics into the build.

    target_os: Target_OS = .Windows
    when ODIN_OS == .Linux  { target_os = .Linux  }
    when ODIN_OS == .Darwin { target_os = .Mac    }

    // Per-package build mode detection: a package with a top-level `main`
    // becomes an executable; a package without becomes a DLL. The `-shared`
    // CLI flag still works as a force-all-shared override.
    pkg_has_main :: proc(program: ^Program) -> bool {
        for stmt in program^ {
            if scope, ok := stmt.(^Stmt_Scope); ok && scope.name == "main" {
                return true
            }
        }
        return false
    }

    // Abort early on parse errors in the requested package.
    if main_errs, has := parse_errors[args.pkg_name]; has {
        fmt.printf("Found %d parse error(s) in '%s'. Aborting.\n", main_errs, args.pkg_name)
        return
    }

    // A build needs an entry point — `main` for an exe or an `#expose`
    // function for a DLL. A package with neither is typically a user
    // mistake; bail with a hint.
    pkg_has_expose :: proc(program: ^Program) -> bool {
        for stmt in program^ {
            if scope, ok := stmt.(^Stmt_Scope); ok && scope.is_exposed {
                return true
            }
        }
        return false
    }
    if !args.shared {
        if !pkg_has_main(programs[args.pkg_name]) && !pkg_has_expose(programs[args.pkg_name]) {
            fmt.printf("Error: package '%s' has no `main` and no `#expose` function. Add an entry point, or pass `-shared` to build an empty DLL.\n", args.pkg_name)
            return
        }
    }

    // DLL when the package has no main (or -shared was requested).
    pkg_shared := args.shared || !pkg_has_main(programs[args.pkg_name])

    perf_timer_mark(&perf, "type check")
    checked := check_program(programs, args.pkg_name,
                             compiler_dir = args.compiler_dir,
                             search_dir   = args.search_dir,
                             web          = args.web,
                             shared       = pkg_shared,
                             target_os    = target_os)
    if checked.errors > 0 {
        fmt.printf("Found %d type error(s). Aborting.\n", checked.errors)
        return
    }

    if args.dump {
        dump_checked_program("checked_dump.txt", checked)
        return
    }

    perf_timer_mark(&perf, "codegen")
    ll_path := strings.concatenate({args.pkg_name, ".ll"})
    if !generate_program(ll_path, checked, web = args.web, shared = pkg_shared) {
        fmt.printf("Code generation failed for '%s'.\n", args.pkg_name)
        return
    }

    // Output extension: .html for web, .dll/.so for shared, native exe otherwise.
    out_ext: string
    switch {
    case args.web:                                    out_ext = ".html"
    case pkg_shared && ODIN_OS == .Windows:           out_ext = ".dll"
    case pkg_shared:                                  out_ext = ".so"  // Linux / Mac
    case:                                             out_ext = NATIVE_EXE_EXT
    }
    out_name := strings.concatenate({args.pkg_name, out_ext})

    perf_timer_mark(&perf, "clang")
    if args.web {
        if !link_web(ll_path, out_name, checked) { return }
    } else {
        if !link_native(ll_path, out_name, checked, args.compiler_dir, pkg_shared) { return }
    }

    fmt.printf("Compiled package '%s' -> %s\n", args.pkg_name, out_name)

    perf_timer_end(&perf)
}
