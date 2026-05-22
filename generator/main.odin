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

generate :: proc(cfg: ^Config) {
    // Phase A: emit only isolated files (ignores -short / -long for now).
    specs: [dynamic]Fn_Spec
    defer delete(specs)
    for i in 0..<cfg.isolated {
        per_file := emit_isolated_file(cfg, i)
        append(&specs, ..per_file[:])
    }
    emit_main(cfg, specs[:])
    fmt.printfln("Emitted %d isolated files, %d total fns", cfg.isolated, len(specs))
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

emit_isolated_file :: proc(cfg: ^Config, idx: int) -> [dynamic]Fn_Spec {
    idx_str := fmt.tprintf("%03d", idx)
    name := strings.concatenate({"iso_", idx_str})
    path := strings.concatenate({cfg.out_dir, "/", name, ".mara"})

    b := strings.builder_make()
    w(&b, "module ", name, "\n\n")

    specs: [dynamic]Fn_Spec
    line_count := 2
    for line_count < cfg.lines {
        fn := pick_fn_name()
        before := strings.builder_len(b)
        spec := gen_arith_fn(&b, fn)
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

emit_main :: proc(cfg: ^Config, all_specs: []Fn_Spec) {
    path := strings.concatenate({cfg.out_dir, "/main.mara"})
    b := strings.builder_make()
    w(&b, "module ", cfg.out_dir, "\n\n")
    for i in 0..<cfg.isolated {
        idx_str := fmt.tprintf("%03d", i)
        w(&b, "use iso_", idx_str, "\n")
    }
    w(&b, "\nmain :: fun() -> i64 {\n")
    sample_count := min(len(all_specs), 1000)
    for i in 0..<sample_count {
        spec := all_specs[rand.int_max(len(all_specs))]
        w(&b, "\t", spec.name, "(")
        for k, j in spec.param_kinds {
            if j > 0 { w(&b, ", ") }
            w(&b, literal_for(k))
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
