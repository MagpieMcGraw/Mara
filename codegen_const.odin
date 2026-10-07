package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Aggregate constants as read-only tables
//
// A struct, fixed-array or union constant (`ATLAS :: Texture{...}`,
// `RED :: [3]f32{...}`) is compile-time data: its value is computed from its
// code (graph_fold.odin) and laid out here as an LLVM constant initializer,
// stored once for the whole program — the main TU defines the table, every
// other TU that reads it declares it external. A reference is the table's
// global: reads load from it, copies copy out of it, and passing it to a
// function passes its address with no copy. Scalars (PI, sizes) aren't
// tabled — they stay immediates. The checker keeps writes, `&` and slice
// variables off constants, so a table is never written.
//
// The value is what construction built (struct field defaults, nested ones
// too, a union variant's fields); laid out, a part never written is its
// type's zero — a partial array's header pointing at its own elements, a
// union variant's tag.
// ---------------------------------------------------------------------------

Const_Table :: struct {
    def:  string, // the definition, plus any private string globals it points at
    decl: string, // the external declaration other TUs use
}

// State for laying out one table's initializer.
@(private="file")
Const_Ctx :: struct {
    g:      ^Codegen,
    span:   Span,
    global: string,           // the table's symbol
    gtype:  string,           // its IR type — a partial array's header points into it
    path:   [dynamic]string,  // GEP indices from the table's root to the value being built
    extras: strings.Builder,  // private globals the initializer points at
    n_extra: int,
}

// Whether a constant of type `t` is kept as a table (text keeps its rodata
// string global).
is_table_const :: proc(t: Type) -> bool {
    base := distinct_base(t)
    if as_struct_body(base) != nil { return true }
    #partial switch _ in base {
    case ^Type_Fixed_Array, ^Type_Union: return true
    }
    return false
}

// The global of constant `c`'s table, laid out the first time this TU reads
// it; `span` is the reference's.
const_table :: proc(g: ^Codegen, pc: ^Program_Code, c: Syntax_Id, span: Span) -> string {
    key, named := pc.table_names[c]
    if !named { codegen_fatal(g, span, CODE_CONST_TABLE_UNNAMED) }
    name := strings.concatenate({"@mara_const.", ir_safe_name(key)})
    if name not_in g.const_tables {
        g.const_tables[name] = build_const_table(g, name, pc.tables[c], graph_type(pc.consts[c], 0), span)
    }
    return name
}

@(private="file")
ir_safe_name :: proc(key: string) -> string {
    b := strings.builder_make()
    for i in 0..<len(key) {
        c := key[i]
        ok := (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_' || c == '.'
        strings.write_byte(&b, c if ok else '_')
    }
    return strings.to_string(b)
}

@(private="file")
build_const_table :: proc(g: ^Codegen, name: string, v: ^Fold, t: Type, span: Span) -> Const_Table {
    cx := Const_Ctx{g = g, span = span, global = name}
    base := distinct_base(t)
    init: string
    if ut, is_union := base.(^Type_Union); is_union {
        cx.gtype, init = const_union_table(&cx, ut, v)
    } else {
        cx.gtype = llvm_type_from_checker(base)
        init = const_init(&cx, v, base)
    }
    def := fmt.tprintf("%s = unnamed_addr constant %s %s, align 16\n%s", name, cx.gtype, init, strings.to_string(cx.extras))
    decl := fmt.tprintf("%s = external constant %s, align 16", name, cx.gtype)
    return Const_Table{def = def, decl = decl}
}

// A value no layout here holds (the evaluation computed it: this is a gap).
@(private="file")
const_fail :: proc(cx: ^Const_Ctx) -> ! {
    codegen_fatal(cx.g, cx.span, CODE_CONST_TABLE_SHAPE)
}

// Whether a part was never written: its type's zero.
@(private="file")
const_unset :: proc(v: ^Fold) -> bool {
    return v == nil || !v.known && v.parts == nil && v.variant == nil
}

// Value `v` (nil = never written) as an initializer of type `t`: its text.
@(private="file")
const_init :: proc(cx: ^Const_Ctx, v: ^Fold, t: Type) -> string {
    base := distinct_base(t)
    if const_unset(v) { return const_default(cx, base) }
    if sd := as_struct_body(base); sd != nil { return const_struct(cx, sd, v) }
    #partial switch a in base {
    case ^Type_Fixed_Array:   return const_array(cx, a, v)
    case ^Type_Partial_Array: return const_partial(cx, a, v)
    case ^Type_Slice:         return const_slice(cx, a, v)
    case ^Type_Union:
        // A union nested in a constant would need its variant laid out as the
        // payload's bytes; only a table's top level supports variants.
        const_fail(cx)
    }
    return const_scalar(cx, v, base)
}

// A slot never written: zero, with partial-array headers set.
@(private="file")
const_default :: proc(cx: ^Const_Ctx, t: Type) -> string {
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil { return const_struct(cx, sd, nil) }
    #partial switch a in base {
    case ^Type_Fixed_Array:   return const_elements(cx, a.elem, a.size, nil)
    case ^Type_Partial_Array:
        push_index(cx, fmt.tprintf("i32 %d", PARTIAL_ELEMENTS_FIELD))
        elems := const_elements(cx, a.elem, a.size, nil)
        pop_index(cx)
        return const_partial_with(cx, a, 0, elems)
    }
    return "zeroinitializer"
}

@(private="file")
push_index :: proc(cx: ^Const_Ctx, index: string) { append(&cx.path, index) }
@(private="file")
pop_index :: proc(cx: ^Const_Ctx) { pop(&cx.path) }

@(private="file")
const_struct :: proc(cx: ^Const_Ctx, sd: ^Scope_Body, v: ^Fold) -> string {
    parts := make([]string, len(sd.fields), context.temp_allocator)
    all_zero := true
    for &f, i in sd.fields {
        push_index(cx, fmt.tprintf("i32 %d", i))
        text: string
        if sd.is_union_variant && i == 0 {
            text = fmt.tprintf("%d", sd.union_variant_tag) // the discriminant, always set
        } else {
            part: ^Fold
            if v != nil && i < len(v.parts) { part = v.parts[i] }
            text = const_init(cx, part, f.type_)
        }
        pop_index(cx)
        if text != "zeroinitializer" { all_zero = false }
        parts[i] = strings.concatenate({field_ir_type(&f), " ", text})
    }
    if all_zero { return "zeroinitializer" }
    open, close := "{ ", " }"
    if sd.is_packed { open, close = "<{ ", " }>" }
    return strings.concatenate({open, strings.join(parts, ", "), close})
}

// `n` elements of type `elem` from `parts` (none: each its zero), as
// `[T a, T b, ...]` — or zeroinitializer when all zero.
@(private="file")
const_elements :: proc(cx: ^Const_Ctx, elem: Type, n: int, parts: []^Fold) -> string {
    elem_ir := llvm_type_from_checker(elem)
    texts := make([]string, n, context.temp_allocator)
    all_zero := true
    for k in 0..<n {
        push_index(cx, fmt.tprintf("i64 %d", k))
        text := const_init(cx, parts[k] if k < len(parts) else nil, elem)
        pop_index(cx)
        if text != "zeroinitializer" { all_zero = false }
        texts[k] = strings.concatenate({elem_ir, " ", text})
    }
    if all_zero { return "zeroinitializer" }
    return strings.concatenate({"[", strings.join(texts, ", "), "]"})
}

// A byte string's bytes as a `[n x i8]` initializer, zero-padded.
@(private="file")
const_bytes :: proc(cx: ^Const_Ctx, s: string, n: int) -> string {
    if len(s) > n { const_fail(cx) }
    b := strings.builder_make()
    strings.write_string(&b, "c\"")
    strings.write_string(&b, llvm_escape_string(s))
    for _ in len(s)..<n { strings.write_string(&b, "\\00") }
    strings.write_byte(&b, '"')
    return strings.to_string(b)
}

@(private="file")
is_byte_elem_type :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_Utf8, Type_Byte: return true
    case Type_Numeric:         return v.bits == 8 && v.kind != .Float
    }
    return false
}

// Text a value holds, when it's text.
@(private="file")
const_text :: proc(v: ^Fold) -> (string, bool) {
    if v.known && v.c.is_text { return v.c.text, true }
    return "", false
}

@(private="file")
const_array :: proc(cx: ^Const_Ctx, fa: ^Type_Fixed_Array, v: ^Fold) -> string {
    if s, is_text := const_text(v); is_text {
        if !is_byte_elem_type(fa.elem) { const_fail(cx) }
        return const_bytes(cx, s, fa.size)
    }
    if v.known { const_fail(cx) }
    return const_elements(cx, fa.elem, fa.size, v.parts)
}

// A partial array of text: its header (len, cap, and a pointer to its own
// elements, the way construction stamps it) and its bytes.
@(private="file")
const_partial :: proc(cx: ^Const_Ctx, pa: ^Type_Partial_Array, v: ^Fold) -> string {
    s, is_text := const_text(v)
    if !is_text || !is_byte_elem_type(pa.elem) { const_fail(cx) }
    return const_partial_with(cx, pa, len(s), const_bytes(cx, s, pa.size))
}

@(private="file")
const_partial_with :: proc(cx: ^Const_Ctx, pa: ^Type_Partial_Array, n: int, elems: string) -> string {
    elem_ir := llvm_type_from_checker(pa.elem)
    self := strings.concatenate({
        "getelementptr inbounds (", cx.gtype, ", ptr ", cx.global, ", i32 0",
        ", " if len(cx.path) > 0 else "", strings.join(cx.path[:], ", "),
        fmt.tprintf(", i32 %d)", PARTIAL_ELEMENTS_FIELD),
    })
    return fmt.tprintf("{{ %s %d, %s %d, ptr %s, [%d x %s] %s }}",
        SLICE_LEN_IR, n, SLICE_LEN_IR, pa.size, self, pa.size, elem_ir, elems)
}

// A slice field: a view of a string (its bytes in a private global, len =
// byte count and cap one more, like a string passed as a slice).
@(private="file")
const_slice :: proc(cx: ^Const_Ctx, sl: ^Type_Slice, v: ^Fold) -> string {
    s, is_text := const_text(v)
    if !is_text || !is_byte_elem_type(sl.elem) { const_fail(cx) }
    cx.n_extra += 1
    name := fmt.tprintf("%s.s%d", cx.global, cx.n_extra)
    fmt.sbprintf(&cx.extras, "%s = private unnamed_addr constant [%d x i8] %s\n",
        name, len(s) + 1, const_bytes(cx, s, len(s) + 1))
    return fmt.tprintf("{{ %s %d, %s %d, ptr %s }}",
        SLICE_LEN_IR, len(s), SLICE_LEN_IR, len(s) + 1, name)
}

// A union constant's table: the variant's struct (tag included) padded out to
// the union's size — its own IR type, since pointers are opaque and every
// access types the load at the use site.
@(private="file")
const_union_table :: proc(cx: ^Const_Ctx, ut: ^Type_Union, v: ^Fold) -> (gtype: string, init: string) {
    g := cx.g
    if v.variant == nil || is_niche_layout(g, ut) { const_fail(cx) }
    vsd := as_struct_body(distinct_base(v.variant))
    if vsd == nil { const_fail(cx) }
    vname := struct_llvm_name(vsd.name)
    tail := type_size(ut) - struct_layout(vsd).size
    if tail <= 0 {
        cx.gtype = vname
        return vname, const_struct(cx, vsd, v)
    }
    cx.gtype = fmt.tprintf("<{{ %s, [%d x i8] }}>", vname, tail)
    push_index(cx, "i32 0")
    body := const_struct(cx, vsd, v)
    pop_index(cx)
    return cx.gtype, fmt.tprintf("<{{ %s %s, [%d x i8] zeroinitializer }}>", vname, body, tail)
}

// Wrap `i` to a `bits`-wide two's-complement value, as the IR prints it.
@(private="file")
wrap_int :: proc(i: i128, bits: int) -> i128 {
    if bits >= 128 || bits <= 0 { return i }
    m := i128(1) << uint(bits)
    w := i % m
    if w < 0 { w += m }
    if w >= m / 2 { w -= m }
    return w
}

@(private="file")
const_scalar :: proc(cx: ^Const_Ctx, v: ^Fold, t: Type) -> string {
    ir := llvm_type_from_checker(t)
    c := v.c
    if c.is_text { const_fail(cx) }
    switch ir {
    case "ptr":
        return "null"   // (`void`: the one pointer a constant holds)
    case "i1":
        return "true" if (c.float if c.is_float else f64(c.int)) != 0 else "false"
    case "half", "float", "double":
        return emit_number_literal(ir, c.float if c.is_float else f64(c.int), 0, true)
    }
    if c.is_float { const_fail(cx) }
    return fmt.tprintf("%d", wrap_int(c.int, ir_type_bits(ir)))
}

// ---------------------------------------------------------------------------
// Assembly: the main TU defines every table any TU used; each other TU
// declares the ones it imports.
// ---------------------------------------------------------------------------

module_const_ir :: proc(g: ^Codegen, module_name: string, is_main_tu: bool) -> string {
    names: [dynamic]string
    defer delete(names)
    if is_main_tu {
        for name in g.const_tables { append(&names, name) }
    } else if imports, ok := g.module_imports[module_name]; ok {
        for name in imports {
            full := strings.concatenate({"@", name}, context.temp_allocator)
            if full in g.const_tables { append(&names, full) }
        }
    }
    if len(names) == 0 { return "" }
    slice.sort(names[:])
    b := strings.builder_make()
    strings.write_string(&b, "; Constant tables\n")
    for name in names {
        table := g.const_tables[name]
        if is_main_tu {
            strings.write_string(&b, table.def)
        } else {
            strings.write_string(&b, table.decl)
            strings.write_byte(&b, '\n')
        }
    }
    strings.write_byte(&b, '\n')
    return strings.to_string(b)
}

