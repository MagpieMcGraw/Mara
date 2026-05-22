package generator

// Code-generation palette. Each `emit_*` proc appends a syntactically and
// type-correct Mara fragment to the builder. The palette grows over time:
// Phase A (this file) covers numeric arithmetic, fixed arrays, and minimal
// control flow. Subsequent phases add structs, generics, match, etc.
//
// Fragments are type-tracked through Fn_State.locals so cross-references
// emit the right casts. The generator never produces an expression whose
// type doesn't match its target slot — Mara would reject it.

import "core:fmt"
import "core:math/rand"
import "core:strings"

// Numeric types we exercise. Float kinds are kept disjoint from int kinds
// to keep cast emission deterministic (every int→float and float→int gets
// an explicit cast).
Type_Kind :: enum {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

type_str :: proc(k: Type_Kind) -> string {
    switch k {
    case .I8:  return "i8"
    case .I16: return "i16"
    case .I32: return "i32"
    case .I64: return "i64"
    case .U8:  return "u8"
    case .U16: return "u16"
    case .U32: return "u32"
    case .U64: return "u64"
    case .F32: return "f32"
    case .F64: return "f64"
    }
    return "i64"
}

is_int_kind :: proc(k: Type_Kind) -> bool {
    #partial switch k {
    case .F32, .F64: return false
    }
    return true
}

is_signed_kind :: proc(k: Type_Kind) -> bool {
    #partial switch k {
    case .I8, .I16, .I32, .I64, .F32, .F64: return true
    }
    return false
}

// Tiny bounded literal. Mara traps on integer overflow at runtime, and
// values compound across statements (each `+` roughly doubles the range
// of plausible magnitudes). To keep ~30 chained arithmetic ops inside the
// narrowest type (i8: ±127), we constrain literals to a tight range and
// drop multiplication entirely from emit_arith_stmt. Unsigned types get
// only positive values so subtraction doesn't underflow either.
literal_for :: proc(k: Type_Kind) -> string {
    switch k {
    case .I8:                return fmt.tprintf("%d", rand.int_max(7) - 3)
    case .I16, .I32, .I64:   return fmt.tprintf("%d", rand.int_max(21) - 10)
    case .U8:                return fmt.tprintf("%d", rand.int_max(3))
    case .U16, .U32, .U64:   return fmt.tprintf("%d", rand.int_max(10))
    case .F32, .F64:         return fmt.tprintf("%.3f", rand.float64() * 4 - 2)
    }
    return "0"
}

Local :: struct {
    name: string,
    kind: Type_Kind,
}

Fn_State :: struct {
    b:       ^strings.Builder,
    locals:  [dynamic]Local,
    next_id: int,
    lines:   int,  // emitted body lines so far
}

fresh_local :: proc(s: ^Fn_State) -> string {
    name := fmt.aprintf("v%d", s.next_id)
    s.next_id += 1
    return name
}

add_local :: proc(s: ^Fn_State, name: string, kind: Type_Kind) {
    append(&s.locals, Local{name = name, kind = kind})
}

// Pick a local of the requested kind. Returns ("", false) if none.
pick_local :: proc(s: ^Fn_State, kind: Type_Kind) -> (Local, bool) {
    count := 0
    for l in s.locals {
        if l.kind == kind { count += 1 }
    }
    if count == 0 { return Local{}, false }
    target := rand.int_max(count)
    for l in s.locals {
        if l.kind == kind {
            if target == 0 { return l, true }
            target -= 1
        }
    }
    return Local{}, false
}

// Render an expression of the requested kind: either pick an existing local
// (with cast if needed) or emit a literal. Always type-correct.
expr_of :: proc(s: ^Fn_State, kind: Type_Kind) -> string {
    // 60% chance to reuse a local if one exists.
    if rand.int_max(100) < 60 {
        if l, ok := pick_local(s, kind); ok {
            return l.name
        }
        // Try casting from another kind.
        for try := 0; try < 4; try += 1 {
            other := Type_Kind(rand.int_max(int(Type_Kind.F64) + 1))
            if other == kind { continue }
            if l, ok := pick_local(s, other); ok {
                return strings.concatenate({type_str(kind), "(", l.name, ")"})
            }
        }
    }
    return literal_for(kind)
}

// One arithmetic binary-op statement: `vN : T = lhs OP rhs`. Only `+` and
// `-` (signed) are used — multiplication compounds too fast for narrow
// types. Unsigned types drop `-` to avoid underflow traps.
emit_arith_stmt :: proc(s: ^Fn_State, kind: Type_Kind) {
    ops: []string
    if is_signed_kind(kind) {
        ops = []string{"+", "-"}
    } else {
        ops = []string{"+"}
    }
    op := ops[rand.int_max(len(ops))]
    lhs := expr_of(s, kind)
    rhs := expr_of(s, kind)
    name := fresh_local(s)
    w(s.b, "\t", name, " : ", type_str(kind), " = ", lhs, " ", op, " ", rhs, "\n")
    add_local(s, name, kind)
    s.lines += 1
}

// Declare a fixed array of size N and write a handful of elements.
emit_fixed_array :: proc(s: ^Fn_State, elem: Type_Kind, size: int) {
    name := fresh_local(s)
    size_str := fmt.tprintf("%d", size)
    w(s.b, "\t", name, " : [", size_str, "]", type_str(elem), "\n")
    s.lines += 1
    writes := min(size, 3 + rand.int_max(4))
    for i in 0..<writes {
        idx := fmt.tprintf("%d", i)
        val := expr_of(s, elem)
        w(s.b, "\t", name, "[", idx, "] = ", val, "\n")
        s.lines += 1
    }
    // Read a couple back into fresh locals for reuse.
    reads := 1 + rand.int_max(2)
    for i in 0..<reads {
        idx := fmt.tprintf("%d", rand.int_max(writes))
        local := fresh_local(s)
        w(s.b, "\t", local, " : ", type_str(elem), " = ", name, "[", idx, "]\n")
        add_local(s, local, elem)
        s.lines += 1
    }
}

// A small if-block that arithmetics on existing locals. Locals declared
// inside the body are block-scoped in Mara — snapshot/restore around the
// body so the outer fn can't accidentally reference them after the close.
emit_if_block :: proc(s: ^Fn_State, kind: Type_Kind) {
    a, ok_a := pick_local(s, kind)
    if !ok_a { return }
    cmp_ops := []string{">", "<", ">=", "<=", "==", "!="}
    op := cmp_ops[rand.int_max(len(cmp_ops))]
    rhs := literal_for(kind)
    w(s.b, "\tif ", a.name, " ", op, " ", rhs, " {\n")
    s.lines += 1
    saved := len(s.locals)
    nested := 1 + rand.int_max(2)
    for _ in 0..<nested {
        w(s.b, "\t")
        emit_arith_stmt(s, kind)
    }
    // Drop block-scoped locals so post-if statements can't pick them.
    resize(&s.locals, saved)
    w(s.b, "\t}\n")
    s.lines += 1
}

// Per-param shape at the call site. Numeric params use `kind`; struct
// params use `struct_name` (and `kind` is ignored). The two-field shape
// lets the call-site emitter dispatch without a union variant.
Param_Spec :: struct {
    kind:        Type_Kind,
    struct_name: string,
}

// Spec returned for each generated function so the call site (main.mara,
// dep-chain bodies) knows how to invoke it with type-correct args.
Fn_Spec :: struct {
    name:   string,
    params: [dynamic]Param_Spec,
    ret:    Type_Kind,
}

// Render a literal valid for the parameter's type.
literal_for_param :: proc(p: Param_Spec) -> string {
    if p.struct_name != "" {
        return strings.concatenate({p.struct_name, "{}"})
    }
    return literal_for(p.kind)
}

// Field of a generated struct.
Field :: struct {
    name: string,
    kind: Type_Kind,
}

// File-scope struct declaration. Tracked so consumer functions in the
// same file can take it as a parameter and read/write its fields.
Struct_Spec :: struct {
    name:   string,
    fields: [dynamic]Field,
}

FIELD_NOUNS := []string{
    "weight", "count", "flags", "scale", "offset", "depth", "stride", "mass",
    "size", "index", "limit", "radius", "phase", "delta", "epoch", "tag",
}

g_struct_counter: int = 0

STRUCT_NOUNS := []string{
    "Cache", "Buffer", "Anchor", "Node", "Slab", "Range", "Layer", "Frame",
    "Block", "Entry", "Field", "Tile", "Vertex", "Edge",
}
STRUCT_ADJS := []string{
    "Hot", "Cold", "Quick", "Slow", "Light", "Heavy", "Open", "Dense",
    "Sparse", "Bright", "Quiet", "Fresh", "Stale",
}

pick_struct_name :: proc() -> string {
    adj := STRUCT_ADJS[rand.int_max(len(STRUCT_ADJS))]
    noun := STRUCT_NOUNS[rand.int_max(len(STRUCT_NOUNS))]
    id := g_struct_counter
    g_struct_counter += 1
    return fmt.aprintf("%s_%s_%d", adj, noun, id)
}

// Emit a struct definition at file scope and return its spec.
gen_struct_def :: proc(b: ^strings.Builder) -> Struct_Spec {
    spec := Struct_Spec{name = pick_struct_name()}
    n_fields := 3 + rand.int_max(6)
    // Track field names used to avoid duplicates within one struct.
    used: map[string]bool
    defer delete(used)
    for len(spec.fields) < n_fields {
        fname := FIELD_NOUNS[rand.int_max(len(FIELD_NOUNS))]
        if used[fname] { continue }
        used[fname] = true
        append(&spec.fields, Field{name = fname, kind = pick_numeric_kind()})
    }
    w(b, spec.name, " :: struct {\n")
    for f in spec.fields {
        // Half the time give the field a default; rest stays zero-init.
        if rand.int_max(2) == 0 {
            w(b, "\t", f.name, ": ", type_str(f.kind), " = ", literal_for(f.kind), "\n")
        } else {
            w(b, "\t", f.name, ": ", type_str(f.kind), "\n")
        }
    }
    w(b, "}\n\n")
    return spec
}

// A function that takes a struct param, reads/writes its fields, returns
// a numeric value. Mixes in 0-2 numeric scalar params.
gen_struct_consumer_fn :: proc(b: ^strings.Builder, name: string, structs: []Struct_Spec) -> Fn_Spec {
    // No structs available: fall back to plain arith so the file fills.
    if len(structs) == 0 {
        return gen_arith_fn(b, name)
    }
    s := Fn_State{b = b}
    defer delete(s.locals)

    chosen := structs[rand.int_max(len(structs))]
    ret_kind := pick_numeric_kind()
    spec := Fn_Spec{name = name, ret = ret_kind}

    // Struct param + 0-2 numeric extras.
    struct_param := fmt.tprintf("p%d", 0)
    append(&spec.params, Param_Spec{struct_name = chosen.name})
    w(b, name, " :: fun(", struct_param, ": ", chosen.name)
    n_extra := rand.int_max(3)
    for i in 0..<n_extra {
        pname := fmt.tprintf("p%d", i+1)
        pkind := pick_numeric_kind()
        w(b, ", ", pname, ": ", type_str(pkind))
        add_local(&s, pname, pkind)
        append(&spec.params, Param_Spec{kind = pkind})
    }
    w(b, ") -> ", type_str(ret_kind), " {\n")

    // Read every field into a local so subsequent arith can use it. This
    // also exercises field-access codegen for each field type in the
    // struct.
    for f in chosen.fields {
        local := fresh_local(&s)
        w(b, "\t", local, " : ", type_str(f.kind), " = ", struct_param, ".", f.name, "\n")
        add_local(&s, local, f.kind)
    }

    // A handful of arith statements that reference the field locals.
    target_stmts := 10 + rand.int_max(8)
    for stmt_i := 0; stmt_i < target_stmts; stmt_i += 1 {
        emit_arith_stmt(&s, pick_numeric_kind())
    }

    // Optional: declare a fresh struct locally and write a couple of fields
    // to exercise the field-write path too.
    if rand.int_max(2) == 0 {
        sl := fresh_local(&s)
        w(b, "\t", sl, " : ", chosen.name, "\n")
        n_writes := 1 + rand.int_max(min(3, len(chosen.fields)))
        for i in 0..<n_writes {
            f := chosen.fields[i]
            w(b, "\t", sl, ".", f.name, " = ", literal_for(f.kind), "\n")
        }
    }

    // Return: pick or synthesize.
    if _, ok := pick_local(&s, ret_kind); !ok {
        emit_arith_stmt(&s, ret_kind)
    }
    ret_local, _ := pick_local(&s, ret_kind)
    w(b, "\treturn ", ret_local.name, "\n")
    w(b, "}\n\n")
    return spec
}

// Emit a full numeric-arithmetic function with the given name. Body size
// is ~20-30 statements, mixing arithmetic, an array, and a conditional.
// Returns the call-site spec.
gen_arith_fn :: proc(b: ^strings.Builder, name: string) -> Fn_Spec {
    s := Fn_State{b = b}
    defer delete(s.locals)

    ret_kind := pick_numeric_kind()
    n_params := 1 + rand.int_max(3)
    spec := Fn_Spec{name = name, ret = ret_kind}
    for i in 0..<n_params {
        append(&spec.params, Param_Spec{kind = pick_numeric_kind()})
    }

    w(b, name, " :: fun(")
    for p, i in spec.params {
        if i > 0 { w(b, ", ") }
        pname := fmt.tprintf("p%d", i)
        w(b, pname, ": ", type_str(p.kind))
        add_local(&s, pname, p.kind)
    }
    w(b, ") -> ", type_str(ret_kind), " {\n")

    target_stmts := 18 + rand.int_max(10)
    for stmt_i := 0; stmt_i < target_stmts; stmt_i += 1 {
        roll := rand.int_max(100)
        switch {
        case roll < 70:
            emit_arith_stmt(&s, pick_numeric_kind())
        case roll < 85:
            emit_fixed_array(&s, pick_numeric_kind_int(), 4 + rand.int_max(12))
        case:
            emit_if_block(&s, pick_numeric_kind())
        }
    }

    if _, ok := pick_local(&s, ret_kind); !ok {
        emit_arith_stmt(&s, ret_kind)
    }
    ret_local, _ := pick_local(&s, ret_kind)
    w(b, "\treturn ", ret_local.name, "\n")
    w(b, "}\n\n")
    return spec
}

pick_numeric_kind :: proc() -> Type_Kind {
    return Type_Kind(rand.int_max(int(Type_Kind.F64) + 1))
}

pick_numeric_kind_int :: proc() -> Type_Kind {
    return Type_Kind(rand.int_max(int(Type_Kind.U64) + 1))
}
