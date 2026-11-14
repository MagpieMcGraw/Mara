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
//     game :: Build(){dirs = ["../engine"], icon = "game.ico", release = true}
//
// (`Build()` its defaults, then the fields written: Mara's construct and
// override. `Build{...}`, a literal, is read the same.) Read as written, not
// checked or run: each field's value is text in quotes, true or false, or a
// list of text in square brackets. A build.mara that isn't `module build` is
// a module's file like any other.

// One build build.mara declares.
Build_Spec :: struct {
    name:    string,            // the constant's
    module:  string,            // what it builds: its module_name, else its name
    dirs:    [dynamic]string,   // more folders searched for modules (relative: to build.mara's folder)
    out:     string,            // the program's name, its extension left off; "": the module's
    icon:    string,            // its icon on Windows, an .ico file (the path as dirs'); "": none
    release: bool,
    llvm:    bool,
    no_console: bool,           // console = false
    crt:        bool,           // crt = true
}

// What Build's fields hold (code/build.mara): their rooms, checked here as
// the checker would.
BUILD_NAME_ROOM :: 64    // module_name, out: str64
BUILD_DIRS_MAX  :: 6     // dirs: [6][96]utf8, icon: [96]utf8 (a whole Build under the stack's 1 KB)
BUILD_PATH_ROOM :: 96

BUILD_FIELDS :: "module_name, dirs, out, icon, release, llvm, console, crt"

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
        // (`Build(){...}` — constructed, then the fields written — or `Build{...}`.)
        constructed := toks[i + 3].kind == .Left_Paren && toks[i + 4].kind == .Right_Paren
        brace := i + 5 if constructed else i + 3
        if t.kind != .Identifier || toks[i + 1].kind != .Double_Colon || toks[i + 2].kind != .Identifier || toks[i + 2].text != "Build" || toks[brace].kind != .Left_Brace {
            return specs, found, say(path, source, t, "build.mara holds builds, each `name :: Build(){...}`: not `%s` here.", t.text)
        }
        spec := Build_Spec{name = t.text}
        for s in specs {
            if s.name == spec.name { return specs, found, say(path, source, t, "a second build named `%s`.", spec.name) }
        }
        i = brace + 1
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
            case "release", "llvm", "console", "crt":
                if v.kind != .True && v.kind != .False { return specs, found, say(path, source, v, "`%s` is true or false.", f.text) }
                switch f.text {
                case "release": spec.release = v.kind == .True
                case "llvm":    spec.llvm = v.kind == .True
                case "crt":     spec.crt = v.kind == .True
                case:           spec.no_console = v.kind == .False
                }
                i += 1
            case "dirs":
                if v.kind != .Left_Bracket { return specs, found, say(path, source, v, "`dirs` is a list of folders in square brackets: `dirs = [\"../engine\"]`.") }
                i += 1
                for {
                    for toks[i].kind == .Newline || toks[i].kind == .Comma { i += 1 }
                    d := toks[i]
                    if d.kind == .Right_Bracket { i += 1; break }
                    s, ok := text(d, BUILD_PATH_ROOM)
                    if !ok { return specs, found, say(path, source, d, "each of `dirs` is a folder's path of up to %d bytes, in quotes.", BUILD_PATH_ROOM) }
                    if len(spec.dirs) == BUILD_DIRS_MAX { return specs, found, say(path, source, d, "`dirs` has room for %d folders.", BUILD_DIRS_MAX) }
                    full := s
                    if !filepath.is_abs(s) { full, _ = filepath.join({dir, s}) }
                    if !os.is_dir(full) { return specs, found, say(path, source, d, "no folder `%s` (from build.mara's folder).", s) }
                    append(&spec.dirs, full)
                    i += 1
                }
            case "icon":
                s, ok := text(v, BUILD_PATH_ROOM)
                if !ok { return specs, found, say(path, source, v, "`icon` is an .ico file's path of up to %d bytes, in quotes.", BUILD_PATH_ROOM) }
                if s != "" {
                    if !strings.equal_fold(filepath.ext(s), ".ico") { return specs, found, say(path, source, v, "`icon` is an .ico file: not `%s`.", s) }
                    full := s
                    if !filepath.is_abs(s) { full, _ = filepath.join({dir, s}) }
                    if !os.is_file(full) { return specs, found, say(path, source, v, "no file `%s` (from build.mara's folder).", s) }
                    spec.icon = full
                }
                i += 1
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

// The Windows resources that make an .ico file a program's icon, as a .res
// file (the linker takes it as it is): each of the icon's images an RT_ICON,
// numbered from 1, and an RT_GROUP_ICON, 1, that lists them. A program's
// first group icon is the one Explorer shows, and the one SDL gives its
// windows. problem: why `ico` isn't an icon file.
icon_resource :: proc(ico: []u8) -> (res: []u8, problem: string) {
    get16 :: proc(b: []u8, at: int) -> int { return int(b[at]) | int(b[at + 1]) << 8 }
    get32 :: proc(b: []u8, at: int) -> int { return get16(b, at) | get16(b, at + 2) << 16 }
    put16 :: proc(out: ^[dynamic]u8, v: int) { append(out, u8(v), u8(v >> 8)) }
    put32 :: proc(out: ^[dynamic]u8, v: int) { put16(out, v); put16(out, v >> 16) }
    // One resource: its header (its type and name numbers, 32 bytes), its
    // data, then zeros to a multiple of 4.
    resource :: proc(out: ^[dynamic]u8, type, name, flags, language: int, data: []u8) {
        put32(out, len(data)); put32(out, 32)
        put16(out, 0xFFFF); put16(out, type)
        put16(out, 0xFFFF); put16(out, name)
        put32(out, 0)                  // data version
        put16(out, flags); put16(out, language)
        put32(out, 0); put32(out, 0)   // version, characteristics
        append(out, ..data)
        for len(out) % 4 != 0 { append(out, 0) }
    }
    RT_ICON       :: 3
    RT_GROUP_ICON :: 14
    EN_US         :: 0x0409   // (rc's language when none is said)

    // The .ico: 0, 1 (an icon), how many images; then 16 bytes on each —
    // width, height, colours, 0, planes, bits per pixel, size, where.
    if len(ico) < 6 || get16(ico, 0) != 0 || get16(ico, 2) != 1 { return nil, "it doesn't start as an icon file does" }
    n := get16(ico, 4)
    if n == 0 { return nil, "it holds no images" }
    if len(ico) < 6 + 16 * n { return nil, "it ends inside its list of images" }

    out := make([dynamic]u8)
    resource(&out, 0, 0, 0, 0, nil)   // (a .res file starts with an empty one)
    group := make([dynamic]u8, context.temp_allocator)
    put16(&group, 0); put16(&group, 1); put16(&group, n)
    for k in 0..<n {
        e := 6 + 16 * k
        size, at := get32(ico, e + 8), get32(ico, e + 12)
        if size == 0 || at + size > len(ico) { return nil, fmt.tprintf("its image %d is outside the file", k + 1) }
        image := ico[at:][:size]
        resource(&out, RT_ICON, k + 1, 0x1010, EN_US, image)   // (moveable, discardable)
        // Its line in the group, as the .ico's, with its number for where:
        // planes and bits read from the image where the .ico leaves them 0
        // (Windows picks the image to show by them).
        planes, bits := get16(ico, e + 4), get16(ico, e + 6)
        if planes == 0 || bits == 0 {
            if size >= 16 && get32(image, 0) == 40 {   // (a bitmap's header)
                planes, bits = get16(image, 12), get16(image, 14)
            } else {                                  // (a PNG's: 32 bits)
                planes, bits = 1, 32
            }
        }
        append(&group, ..ico[e:][:4])
        put16(&group, planes); put16(&group, bits)
        put32(&group, size); put16(&group, k + 1)
    }
    resource(&out, RT_GROUP_ICON, 1, 0x1030, EN_US, group[:])   // (moveable, pure, discardable)
    return out[:], ""
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
