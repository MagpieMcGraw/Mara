package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strings"

// build.mara: what `mara build` builds in a folder — constants of core's
// Build struct (code/build.mara), one build each, named by the constant:
//
//     module build
//     use mara.build
//
//     game :: Build{dirs = ["../engine"], flags = [.release]}
//
// Read as written, not checked or run: each field's value is text in quotes,
// or a list in square brackets — of text, or of Build_Flag's variants. A build.mara that isn't
// `module build` is a module's file like any other.

// One build build.mara declares.
Build_Spec :: struct {
    name:    string,            // the constant's
    module:  string,            // what it builds: its module_name, else its name
    dirs:    [dynamic]string,   // more folders searched for modules (relative: to build.mara's folder)
    out:     string,            // the program's name, its extension left off; "": the module's
    release: bool,
    llvm:    bool,
}

// What Build's fields hold (code/build.mara): their rooms, checked here as
// the checker would.
BUILD_NAME_ROOM :: 64    // module_name, out: str64
BUILD_DIRS_MAX  :: 8     // dirs: [8][120]utf8
BUILD_DIR_ROOM  :: 120
BUILD_FLAGS_MAX :: 4     // flags: [4]Build_Flag

BUILD_FIELDS :: "module_name, dirs, out, flags"

// The builds the build.mara in `dir` declares. found: there is one, `module
// build`. problem: what's wrong in it, said where.
build_file_read :: proc(dir: string) -> (specs: [dynamic]Build_Spec, found: bool, problem: string) {
    path, _ := filepath.join({dir, "build.mara"})
    data, err := os.read_entire_file_from_path(path, context.allocator)
    if err != nil { return }
    source := string(data)
    if extract_package_name(source) != "build" { return }
    found = true

    // Its tokens, on their own (not the build's: build.mara is no module of it).
    Tok :: struct {
        kind:   Token_Kind,
        offset: int,
        text:   string,   // a string's value; else its source
    }
    toks := make([dynamic]Tok, context.temp_allocator)
    l := lexer_init(source, path)
    for {
        t := next_token(&l)
        text := l.value if t.kind == .String else source[t.offset:][:t.len]
        append(&toks, Tok{t.kind, int(t.offset), strings.clone(text)})
        if t.kind == .EOF { break }
    }
    if l.errors > 0 { return specs, found, fmt.tprintf("%sbuild.mara doesn't read as Mara (above).", take_diagnostics()) }

    // (Said as the checker says its errors: `[build.mara:6:12] Build error: ...`.)
    say :: proc(path, source: string, t: Tok, format: string, args: ..any) -> string {
        line, col := 1, 1
        for c, i in transmute([]u8)source {
            if i >= t.offset { break }
            if c == '\n' { line, col = line + 1, 1 } else { col += 1 }
        }
        return fmt.tprintf("[%s:%d:%d] Build error: %s", filepath.base(path), line, col, fmt.tprintf(format, ..args))
    }

    i := 0
    skip_newlines :: proc(toks: []Tok, i: ^int) { for toks[i^].kind == .Newline { i^ += 1 } }
    for {
        skip_newlines(toks[:], &i)
        t := toks[i]
        if t.kind == .EOF { break }
        // (`module build`, `use mara.build`: as a module's file has them.)
        if t.kind == .Module || t.kind == .Use {
            for toks[i].kind != .Newline && toks[i].kind != .EOF { i += 1 }
            continue
        }
        if t.kind != .Identifier || toks[i + 1].kind != .Double_Colon || toks[i + 2].kind != .Identifier || toks[i + 2].text != "Build" || toks[i + 3].kind != .Left_Brace {
            return specs, found, say(path, source, t, "build.mara holds builds, each `name :: Build{...}`: not `%s` here.", t.text)
        }
        spec := Build_Spec{name = t.text}
        for s in specs {
            if s.name == spec.name { return specs, found, say(path, source, t, "a second build named `%s`.", spec.name) }
        }
        i += 4
        // Its fields, `name = value`, a comma or a line between.
        for {
            for toks[i].kind == .Newline || toks[i].kind == .Comma { i += 1 }
            f := toks[i]
            if f.kind == .Right_Brace { i += 1; break }
            if f.kind != .Identifier || toks[i + 1].kind != .Equals {
                return specs, found, say(path, source, f, "a Build's fields are set by name, `release = true`: not `%s`.", f.text)
            }
            i += 2
            v := toks[i]
            text :: proc(v: Tok, room: int) -> (string, bool) {
                return v.text, v.kind == .String && len(v.text) <= room
            }
            switch f.text {
            case "module_name", "out":
                s, ok := text(v, BUILD_NAME_ROOM)
                if !ok { return specs, found, say(path, source, v, "`%s` is text of up to %d bytes, in quotes.", f.text, BUILD_NAME_ROOM) }
                if f.text == "out" { spec.out = s } else { spec.module = s }
                i += 1
            case "flags":
                if v.kind != .Left_Bracket { return specs, found, say(path, source, v, "`flags` is a list in square brackets: `flags = [.release]`.") }
                i += 1
                n := 0
                for {
                    for toks[i].kind == .Newline || toks[i].kind == .Comma { i += 1 }
                    if toks[i].kind == .Right_Bracket { i += 1; break }
                    if toks[i].kind == .Dot { i += 1 }   // (`.release`, or `release`)
                    flag := toks[i]
                    if n == BUILD_FLAGS_MAX { return specs, found, say(path, source, flag, "`flags` has room for %d.", BUILD_FLAGS_MAX) }
                    switch {
                    case flag.kind == .Identifier && flag.text == "release": spec.release = true
                    case flag.kind == .Identifier && flag.text == "llvm":    spec.llvm = true
                    case: return specs, found, say(path, source, flag, "Build_Flag has no `%s`: its flags are release, llvm.", flag.text)
                    }
                    n += 1
                    i += 1
                }
            case "dirs":
                if v.kind != .Left_Bracket { return specs, found, say(path, source, v, "`dirs` is a list of folders in square brackets: `dirs = [\"../engine\"]`.") }
                i += 1
                for {
                    for toks[i].kind == .Newline || toks[i].kind == .Comma { i += 1 }
                    d := toks[i]
                    if d.kind == .Right_Bracket { i += 1; break }
                    s, ok := text(d, BUILD_DIR_ROOM)
                    if !ok { return specs, found, say(path, source, d, "each of `dirs` is a folder's path of up to %d bytes, in quotes.", BUILD_DIR_ROOM) }
                    if len(spec.dirs) == BUILD_DIRS_MAX { return specs, found, say(path, source, d, "`dirs` has room for %d folders.", BUILD_DIRS_MAX) }
                    full := s
                    if !filepath.is_abs(s) { full, _ = filepath.join({dir, s}) }
                    if !os.is_dir(full) { return specs, found, say(path, source, d, "no folder `%s` (from build.mara's folder).", s) }
                    append(&spec.dirs, full)
                    i += 1
                }
            case:
                return specs, found, say(path, source, f, "Build has no field `%s`: its fields are %s.", f.text, BUILD_FIELDS)
            }
        }
        if spec.module == "" { spec.module = spec.name }
        append(&specs, spec)
    }
    return
}

// The build a command means here: the one named `name`; none named, the one
// named as the folder, or the only one. ok false: none of them (`name` not
// one: a module, as without build.mara); problem: build.mara has several and
// names none — said.
build_pick :: proc(specs: []Build_Spec, name, folder, command: string) -> (spec: Build_Spec, ok: bool, problem: string) {
    if len(specs) == 0 { return }
    if name != "" {
        for s in specs { if s.name == name { return s, true, "" } }
        return
    }
    for s in specs { if s.name == folder { return s, true, "" } }
    if len(specs) == 1 { return specs[0], true, "" }
    b := strings.builder_make()
    fmt.sbprintf(&b, "mara %s: which build? build.mara here declares several, none named as the folder (%s):\n", command, folder)
    for s in specs { fmt.sbprintf(&b, "  %s\n", s.name) }
    fmt.sbprintf(&b, "Name it: mara %s <build>", command)
    return {}, false, strings.to_string(b)
}

// Every folder any build here searches: where the tools (ask, serve, view)
// look for modules when no one build is meant.
build_all_dirs :: proc(specs: []Build_Spec) -> []string {
    out := make([dynamic]string)
    for s in specs {
        for d in s.dirs {
            seen := false
            for o in out { if o == d { seen = true } }
            if !seen { append(&out, d) }
        }
    }
    return out[:]
}
