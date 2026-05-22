package generator

// A stress-test project generator for Mara.
//
// Produces a directory of .mara files with controllable scale (file count,
// lines per file), topology (isolated / short-chain / long-chain), and
// feature mix (operator overloads, edge-case sprinkles). Same seed + same
// knobs → byte-identical output.
//
// Usage:
//   generator -out test_1M
//   generator -out test_100k -files 30 -lines 3333 -isolated 15 -short 9 -long 6
//   generator -out gen_opover -files 50 -opover 30

import "core:fmt"
import "core:math/rand"
import "core:os"
import "core:strconv"
import "core:strings"

Config :: struct {
    out_dir:    string,
    seed:       u64,
    files:      int,
    lines:      int, // target lines per file
    isolated:   int,
    short:      int,
    long:       int,
    opover_pct: int, // 0..100
    edge_pct:   int, // 0..100
}

default_config :: proc() -> Config {
    return Config{
        seed       = 42,
        files      = 100,
        lines      = 10000,
        isolated   = 50,
        short      = 30,
        long       = 20,
        opover_pct = 5,
        edge_pct   = 10,
    }
}

print_usage :: proc() {
    fmt.eprintln("usage: generator -out <dir> [options]")
    fmt.eprintln("  -seed N         RNG seed (default 42)")
    fmt.eprintln("  -files N        total files (default 100)")
    fmt.eprintln("  -lines N        target lines per file (default 10000)")
    fmt.eprintln("  -isolated N     isolated file count (default 50)")
    fmt.eprintln("  -short N        short-chain (depth 2-3) count (default 30)")
    fmt.eprintln("  -long N         long-chain (depth 5-7) count (default 20)")
    fmt.eprintln("  -opover PCT     operator-overload frequency 0..100 (default 5)")
    fmt.eprintln("  -edge-bias PCT  edge-case sprinkle frequency 0..100 (default 10)")
}

// Pop the next arg as a string value for the named flag, or report and bail.
expect_value :: proc(args: []string, i: int, name: string) -> (string, bool) {
    if i+1 >= len(args) {
        fmt.eprintfln("flag %s requires a value", name)
        return "", false
    }
    return args[i+1], true
}

parse_int_or :: proc(s: string, default_val: int) -> int {
    n, ok := strconv.parse_int(s)
    if !ok { return default_val }
    return n
}

parse_u64_or :: proc(s: string, default_val: u64) -> u64 {
    n, ok := strconv.parse_u64(s)
    if !ok { return default_val }
    return n
}

parse_args :: proc() -> (cfg: Config, ok: bool) {
    cfg = default_config()
    args := os.args[1:]
    i := 0
    for i < len(args) {
        a := args[i]
        switch a {
        case "-out":
            v, vok := expect_value(args, i, "-out"); if !vok { return cfg, false }
            cfg.out_dir = v
            i += 2
        case "-seed":
            v, vok := expect_value(args, i, "-seed"); if !vok { return cfg, false }
            cfg.seed = parse_u64_or(v, cfg.seed)
            i += 2
        case "-files":
            v, vok := expect_value(args, i, "-files"); if !vok { return cfg, false }
            cfg.files = parse_int_or(v, cfg.files)
            i += 2
        case "-lines":
            v, vok := expect_value(args, i, "-lines"); if !vok { return cfg, false }
            cfg.lines = parse_int_or(v, cfg.lines)
            i += 2
        case "-isolated":
            v, vok := expect_value(args, i, "-isolated"); if !vok { return cfg, false }
            cfg.isolated = parse_int_or(v, cfg.isolated)
            i += 2
        case "-short":
            v, vok := expect_value(args, i, "-short"); if !vok { return cfg, false }
            cfg.short = parse_int_or(v, cfg.short)
            i += 2
        case "-long":
            v, vok := expect_value(args, i, "-long"); if !vok { return cfg, false }
            cfg.long = parse_int_or(v, cfg.long)
            i += 2
        case "-opover":
            v, vok := expect_value(args, i, "-opover"); if !vok { return cfg, false }
            cfg.opover_pct = parse_int_or(v, cfg.opover_pct)
            i += 2
        case "-edge-bias":
            v, vok := expect_value(args, i, "-edge-bias"); if !vok { return cfg, false }
            cfg.edge_pct = parse_int_or(v, cfg.edge_pct)
            i += 2
        case "-h", "--help":
            print_usage()
            return cfg, false
        case:
            fmt.eprintfln("unknown flag: %s", a)
            print_usage()
            return cfg, false
        }
    }
    if cfg.out_dir == "" {
        fmt.eprintln("missing required -out flag")
        print_usage()
        return cfg, false
    }
    if cfg.isolated+cfg.short+cfg.long != cfg.files {
        fmt.eprintfln("warning: isolated+short+long (%d) != files (%d) — adjusting files to match buckets",
            cfg.isolated+cfg.short+cfg.long, cfg.files)
        cfg.files = cfg.isolated+cfg.short+cfg.long
    }
    ok = true
    return
}

main :: proc() {
    cfg, ok := parse_args()
    if !ok { os.exit(1) }
    rand.reset(cfg.seed)

    if !os.exists(cfg.out_dir) {
        err := os.make_directory(cfg.out_dir)
        if err != nil {
            fmt.eprintfln("could not create directory %s: %v", cfg.out_dir, err)
            os.exit(1)
        }
    }

    fmt.printfln("Generating into %s/", cfg.out_dir)
    fmt.printfln("  files: %d (%d isolated + %d short + %d long)",
        cfg.files, cfg.isolated, cfg.short, cfg.long)
    fmt.printfln("  target lines/file: %d", cfg.lines)
    fmt.printfln("  opover frequency: %d%%   edge bias: %d%%", cfg.opover_pct, cfg.edge_pct)
    fmt.printfln("  seed: %d", cfg.seed)

    generate(&cfg)
    fmt.println("Done.")
}

// ---------------------------------------------------------------------------
// Generation orchestration. Phase A: emit isolated files of arithmetic +
// fixed-array functions only. Topology + cross-file calls come in later
// phases.
// ---------------------------------------------------------------------------

// Global function-name counter so every generated function has a unique
// suffix across all files in this generation run.
g_fn_counter: int = 0

VERBS  := []string{
    "emit", "compute", "calculate", "process", "transform", "apply", "merge",
    "blend", "damp", "clamp", "rotate", "scale", "shift", "lerp", "hash",
    "iterate", "accumulate", "normalize", "validate", "resolve", "gather",
    "dispatch", "inject", "render", "load", "build", "sort", "check",
}
NOUNS  := []string{
    "vertex", "color", "velocity", "normal", "weight", "torque", "field",
    "block", "frame", "tile", "voxel", "node", "edge", "anchor", "layer",
    "range", "pixel", "axis", "joint", "buffer", "cache", "slot", "index",
    "depth", "stride", "offset", "mass", "wave", "orbit",
}

pick_fn_name :: proc() -> string {
    v := VERBS[rand.int_max(len(VERBS))]
    n := NOUNS[rand.int_max(len(NOUNS))]
    id := g_fn_counter
    g_fn_counter += 1
    return fmt.aprintf("%s_%s_%04d", v, n, id)
}

// Tracks what one generated file emits — so later dep files can `use` it
// and call into its functions.
File_Info :: struct {
    module_name: string,
    specs:       [dynamic]Fn_Spec,
}

generate :: proc(cfg: ^Config) {
    files: [dynamic]File_Info
    defer {
        for &f in files { delete(f.specs) }
        delete(files)
    }

    // 1. Isolated files: no `use`, no externs.
    for i in 0..<cfg.isolated {
        idx_str := fmt.tprintf("%03d", i)
        name := strings.concatenate({"iso_", idx_str})
        per_file := emit_dep_file(cfg, name, nil, nil)
        append(&files, File_Info{module_name = name, specs = per_file})
    }

    // 2. Short-chain files: each `use`s 2-3 already-generated files.
    for i in 0..<cfg.short {
        idx_str := fmt.tprintf("%03d", i)
        name := strings.concatenate({"sht_", idx_str})
        n_deps := 2 + rand.int_max(2)  // 2..3
        deps := pick_dep_files(files[:], n_deps)
        defer delete(deps)
        per_file := emit_dep_file(cfg, name, deps[:], files[:])
        append(&files, File_Info{module_name = name, specs = per_file})
    }

    // 3. Long-chain files: each `use`s 5-7.
    for i in 0..<cfg.long {
        idx_str := fmt.tprintf("%03d", i)
        name := strings.concatenate({"lng_", idx_str})
        n_deps := 5 + rand.int_max(3)  // 5..7
        deps := pick_dep_files(files[:], n_deps)
        defer delete(deps)
        per_file := emit_dep_file(cfg, name, deps[:], files[:])
        append(&files, File_Info{module_name = name, specs = per_file})
    }

    // Main pulls every file in.
    all_specs: [dynamic]Fn_Spec
    defer delete(all_specs)
    for &f in files {
        append(&all_specs, ..f.specs[:])
    }
    emit_main(cfg, files[:], all_specs[:])

    fmt.printfln("Emitted %d files (%d iso + %d short + %d long), %d total fns",
        len(files), cfg.isolated, cfg.short, cfg.long, len(all_specs))
}

// Pick `n` distinct files from the pool for use as deps. If the pool is
// smaller than n, returns whatever's available.
pick_dep_files :: proc(pool: []File_Info, n: int) -> [dynamic]File_Info {
    out: [dynamic]File_Info
    if len(pool) == 0 { return out }
    actual := min(n, len(pool))
    used: map[int]bool
    defer delete(used)
    for len(out) < actual {
        i := rand.int_max(len(pool))
        if used[i] { continue }
        used[i] = true
        append(&out, pool[i])
    }
    return out
}

// fmt.tprintf/sbprintfln treat `{` and `}` as format directives, so any line
// containing literal braces (Mara function bodies, structs, etc.) must be
// composed via strings.write_string / write to avoid mangled output. The `w`
// helper below is the standard escape hatch — append a chain of literal parts
// in one call.
w :: proc(b: ^strings.Builder, parts: ..string) {
    for p in parts {
        strings.write_string(b, p)
    }
}

// Emit one file, optionally `use`ing earlier files. `deps` lists the
// modules this file imports; their specs are the externs visible inside
// this file's function bodies (so they get called).
emit_dep_file :: proc(cfg: ^Config, name: string, deps: []File_Info, _all_files: []File_Info) -> [dynamic]Fn_Spec {
    path := strings.concatenate({cfg.out_dir, "/", name, ".mara"})

    b := strings.builder_make()
    w(&b, "module ", name, "\n\n")
    for d in deps {
        w(&b, "use ", d.module_name, "\n")
    }
    if len(deps) > 0 { w(&b, "\n") }

    // Build the extern pool from all deps' specs.
    externs: [dynamic]Fn_Spec
    defer delete(externs)
    for d in deps {
        append(&externs, ..d.specs[:])
    }

    // Struct defs: roughly one per ~500 target lines, capped at 20.
    n_structs := min(20, max(3, cfg.lines / 500))
    structs: [dynamic]Struct_Spec
    defer delete(structs)
    for i in 0..<n_structs {
        append(&structs, gen_struct_def(&b))
    }

    // Operator overloads driven by -opover: that percentage of structs
    // get a +/-/* overload set (declaration + dispatch + 2 variant fns).
    // Doesn't go into Fn_Spec (overloads aren't user-callable from main
    // by name), but stresses the type checker's dispatch resolution.
    for sd in structs {
        if rand.int_max(100) < cfg.opover_pct {
            gen_overload_set(&b, sd)
        }
    }

    specs: [dynamic]Fn_Spec
    line_count := count_lines(strings.to_string(b))
    for line_count < cfg.lines {
        fn := pick_fn_name()
        before := strings.builder_len(b)
        spec: Fn_Spec
        if rand.int_max(100) < 30 && len(structs) > 0 {
            spec = gen_struct_consumer_fn(&b, fn, structs[:])
        } else {
            spec = gen_arith_fn(&b, fn, externs[:])
        }
        append(&specs, spec)
        added := strings.builder_len(b) - before
        s := strings.to_string(b)
        for i := strings.builder_len(b) - added; i < strings.builder_len(b); i += 1 {
            if s[i] == '\n' { line_count += 1 }
        }
    }
    write_file(path, strings.to_string(b))
    return specs
}

count_lines :: proc(s: string) -> int {
    n := 0
    for i in 0..<len(s) {
        if s[i] == '\n' { n += 1 }
    }
    return n
}

emit_main :: proc(cfg: ^Config, files: []File_Info, all_specs: []Fn_Spec) {
    path := strings.concatenate({cfg.out_dir, "/main.mara"})
    b := strings.builder_make()
    w(&b, "module ", cfg.out_dir, "\n\n")
    for f in files {
        w(&b, "use ", f.module_name, "\n")
    }
    w(&b, "\nmain :: fun() -> i64 {\n")
    sample_count := min(len(all_specs), 1000)

    // Pre-sample so we know which structs we need locals for. Mara's codegen
    // currently rejects `StructName{}` as a call-arg literal (lowers to
    // `ptr 0` in IR), so we declare a zero-init local for each unique
    // struct type and pass it by name from the call sites below.
    sampled: [dynamic]Fn_Spec
    defer delete(sampled)
    struct_locals: map[string]string
    defer delete(struct_locals)
    for i in 0..<sample_count {
        spec := all_specs[rand.int_max(len(all_specs))]
        append(&sampled, spec)
        for p in spec.params {
            if p.struct_name != "" {
                if _, exists := struct_locals[p.struct_name]; !exists {
                    local := fmt.aprintf("__sarg_%d", len(struct_locals))
                    struct_locals[p.struct_name] = local
                }
            }
        }
    }
    for sname, local in struct_locals {
        w(&b, "\t", local, " : ", sname, "\n")
    }
    for spec in sampled {
        w(&b, "\t", spec.name, "(")
        for p, j in spec.params {
            if j > 0 { w(&b, ", ") }
            if p.struct_name != "" {
                w(&b, struct_locals[p.struct_name])
            } else {
                w(&b, literal_for(p.kind))
            }
        }
        w(&b, ")\n")
    }
    w(&b, "\treturn 0\n")
    w(&b, "}\n")
    write_file(path, strings.to_string(b))
}

write_file :: proc(path: string, content: string) {
    werr := os.write_entire_file(path, transmute([]u8)content)
    if werr != nil {
        fmt.eprintfln("could not write %s: %v", path, werr)
        os.exit(1)
    }
}
