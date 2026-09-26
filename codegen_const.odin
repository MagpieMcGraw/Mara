package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Aggregate constants as read-only tables
//
// A struct, fixed-array or union constant (`ATLAS :: Texture{...}`,
// `RED :: [3]f32{...}`) is compile-time data. It is evaluated here into an
// LLVM constant initializer and stored once for the whole program: the main
// TU defines the table, every other TU that reads it declares it external. A
// reference binds like a read-only variable whose storage is the table, so
// reads load from it, copies copy out of it, and passing it to a function
// passes its address with no copy. Scalars (PI, sizes) aren't tabled — they
// stay immediates. The checker keeps writes, `&` and slice variables off
// constants, so a table is never written.
//
// The initializer mirrors construction exactly: struct field defaults (nested
// ones too, and per array slot), partial-array headers pointing at their own
// elements, a union variant's tag. A constant whose value needs code to run —
// a call, a struct with constructor params or an imperative body — is a
// compile error.
// ---------------------------------------------------------------------------

Const_Table :: struct {
    def:  string, // the definition, plus any private string globals it points at
    decl: string, // the external declaration other TUs use
}

// State for building one table's initializer.
@(private="file")
Const_Ctx :: struct {
    g:      ^Codegen,
    what:   string,           // the constant's name, for diagnostics
    span:   Span,
    global: string,           // the table's symbol
    gtype:  string,           // its IR type — a partial array's header points into it
    path:   [dynamic]string,  // GEP indices from the table's root to the value being built
    extras: strings.Builder,  // private globals the initializer points at
    n_extra: int,
}

// The identity of an expression node (the pointer every Expr variant holds; a
// union's payload sits at offset 0).
expr_identity :: proc(e: Expr) -> rawptr {
    e := e
    return (^rawptr)(&e)^
}

// Name each constant's table after its longest key in table.constants (a
// module constant is registered under both its flat and bare name). Built once
// on the main thread; workers read it.
build_const_names :: proc(g: ^Codegen, checked: ^Checked_Program) {
    g.const_names = make(map[rawptr]string)
    for key, value in checked.table.constants {
        if value == nil { continue }
        id := expr_identity(value)
        if prev, seen := g.const_names[id]; seen {
            if len(prev) > len(key) || (len(prev) == len(key) && prev < key) { continue }
        }
        g.const_names[id] = key
    }
}

// Whether constant `value` of type `t` is kept as a table rather than inlined.
// String constants keep their rodata string global.
is_table_const :: proc(value: Expr, t: Type) -> bool {
    if _, is_str := value.(^Expr_String); is_str { return false }
    base := distinct_base(t)
    if as_struct_body(base) != nil { return true }
    #partial switch _ in base {
    case ^Type_Fixed_Array, ^Type_Union: return true
    }
    return false
}

// If `expr` names an aggregate constant, the read-only variable for its table.
const_table_ref :: proc(g: ^Codegen, expr: Expr) -> (Var_Entry, bool) {
    value, ok := const_value_of(g, expr)
    if !ok { return nil, false }
    t := expr_type(expr)
    if t == nil { t = expr_type(value) }
    if !is_table_const(value, t) { return nil, false }
    return const_table_var(g, value, t, expr), true
}

// The table for aggregate constant `value` (type `t`) as the storage a
// reference binds to — built the first time any function in this TU reads it.
const_table_var :: proc(g: ^Codegen, value: Expr, t: Type, ref: Expr) -> Var_Entry {
    key, named := g.const_names[expr_identity(value)]
    if !named { codegen_fatal(g, expr_span(ref)^, CODE_CONST_TABLE_UNNAMED) }
    name := strings.concatenate({"@mara_const.", ir_safe_name(key)})
    if name not_in g.const_tables {
        what := key // for diagnostics: the name as written at the reference
        #partial switch r in ref {
        case ^Expr_Ident:        what = r.name
        case ^Expr_Field_Access: what = r.field
        }
        g.const_tables[name] = build_const_table(g, name, what, value, t, expr_span(ref)^)
    }
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil {
        return Struct_Var{alloca = name, struct_name = struct_key(sd)}
    }
    #partial switch v in base {
    case ^Type_Fixed_Array:
        _, utf8 := distinct_base(v.elem).(Type_Utf8)
        return Array_Var{alloca = name, capacity = v.size, elem_type = llvm_type_from_checker(v.elem), is_utf8 = utf8}
    case ^Type_Union:
        return Union_Var{alloca = name, union_name = union_key(v)}
    }
    unreachable()
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
build_const_table :: proc(g: ^Codegen, name, what: string, value: Expr, t: Type, span: Span) -> Const_Table {
    cx := Const_Ctx{g = g, what = what, span = span, global = name}
    base := distinct_base(t)
    init: string
    if ut, is_union := base.(^Type_Union); is_union {
        cx.gtype, init = const_union_table(&cx, ut, value)
    } else {
        cx.gtype = llvm_type_from_checker(base)
        init = const_init(&cx, value, base)
    }
    def := fmt.tprintf("%s = unnamed_addr constant %s %s, align 16\n%s", name, cx.gtype, init, strings.to_string(cx.extras))
    decl := fmt.tprintf("%s = external constant %s, align 16", name, cx.gtype)
    return Const_Table{def = def, decl = decl}
}

@(private="file")
const_fail :: proc(cx: ^Const_Ctx, e: Expr) -> ! {
    span := cx.span
    if e != nil { span = expr_span(e)^ }
    codegen_fatal(cx.g, span, CODE_CONST_NOT_COMPILE_TIME, cx.what)
}

// A constant reference's value, followed through chains of constants.
@(private="file")
const_resolve :: proc(g: ^Codegen, e: Expr) -> Expr {
    e := e
    for {
        v, ok := const_value_of(g, e)
        if !ok { return e }
        e = v
    }
}

// `e` (nil = not given) as an initializer of type `t`: its value text.
@(private="file")
const_init :: proc(cx: ^Const_Ctx, e: Expr, t: Type) -> string {
    if e == nil { return const_default(cx, t, true) }
    e := const_resolve(cx.g, e)
    if _, skip := e.(^Expr_Skip_Constructor); skip { return const_default(cx, t, false) }
    // Part of another constant (`NAMES[0]`, `ATLAS.uv`, `SPOT.x`).
    if part, is_part := const_select(cx, e); is_part { return const_init(cx, part, t) }
    // A distinct conversion (`Vec3(v)`) is the value it wraps.
    if call, is_call := e.(^Expr_Call); is_call {
        if inner, ok := call_passthrough_value(cx.g, call); ok {
            if _, _, _, is_num := cast_target_ir_type(call.name); !is_num {
                return const_init(cx, inner, t)
            }
        }
    }
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil { return const_struct(cx, sd, e, true) }
    #partial switch v in base {
    case ^Type_Fixed_Array:   return const_array(cx, v, e)
    case ^Type_Partial_Array: return const_partial(cx, v, e)
    case ^Type_Slice:         return const_slice(cx, v, e)
    case ^Type_Union:
        // A union nested in a constant would need its variant laid out as the
        // payload's bytes; only a table's top level supports variants.
        const_fail(cx, e)
    }
    return const_scalar(cx, e, base)
}

// The expression for an element or field of a constant's literal — nil when
// the literal leaves that slot to its default. is_part = false when `e`
// isn't such a selection (or not of a constant); a selection that can't be
// made at compile time fails.
@(private="file")
const_select :: proc(cx: ^Const_Ctx, e: Expr) -> (part: Expr, is_part: bool) {
    g := cx.g
    base_expr: Expr
    #partial switch v in e {
    case ^Expr_Index:       base_expr = v.expr
    case ^Expr_Field_Access:
        if v.resolved != nil { return nil, false } // a constant / variant itself
        base_expr = v.expr
    case:
        return nil, false
    }
    if !is_const_rooted(g, base_expr) { return nil, false }
    base := const_resolve(g, base_expr)
    if sub, sub_ok := const_select(cx, base); sub_ok { base = sub }
    if base == nil { const_fail(cx, e) } // a defaulted slot's own parts
    base = const_resolve(g, base)
    #partial switch v in e {
    case ^Expr_Index:
        n, ok := const_num(g, v.index)
        if !ok || n.is_float { const_fail(cx, v.index) }
        values, zero_init := array_literal_values(cx, base)
        if zero_init || n.i < 0 { const_fail(cx, e) }
        return values[int(n.i)] if n.i < i128(len(values)) else nil, true
    case ^Expr_Field_Access:
        if fa, is_fa := distinct_base(expr_type(v.expr)).(^Type_Fixed_Array); is_fa {
            if len(v.field) != 1 || !is_swizzle_field(v.field, fa.size) { const_fail(cx, e) }
            idx := swizzle_char_to_index(v.field[0])
            values, zero_init := array_literal_values(cx, base)
            if zero_init { const_fail(cx, e) }
            return values[idx] if idx < len(values) else nil, true
        }
        sd := as_struct_body(distinct_base(expr_type(v.expr)))
        lit, is_lit := base.(^Expr_Struct_Literal)
        if sd == nil || !is_lit || lit.zero_init || lit.is_spread { const_fail(cx, e) }
        idx := struct_field_index(sd, v.field)
        if idx < 0 { const_fail(cx, e) }
        for field, pos in lit.fields {
            at := first_user_field(sd) + pos if lit.positional else struct_field_index(sd, field.name)
            if at == idx { return field.value, true }
        }
        return sd.fields[idx].default_value, true
    }
    return nil, false
}

// Whether an access path starts at a constant (bare `K`, or qualified `mod.K`).
@(private="file")
is_const_rooted :: proc(g: ^Codegen, e: Expr) -> bool {
    cur := e
    for {
        if _, ok := const_value_of(g, cur); ok { return true }
        #partial switch v in cur {
        case ^Expr_Field_Access: cur = v.expr
        case ^Expr_Index:        cur = v.expr
        case:                    return false
        }
    }
}

// The value a slot of type `t` holds when nothing is given for it: zero, with
// struct defaults applied (unless under `{0}`) and partial-array headers set.
@(private="file")
const_default :: proc(cx: ^Const_Ctx, t: Type, with_defaults: bool) -> string {
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil { return const_struct(cx, sd, nil, with_defaults) }
    #partial switch v in base {
    case ^Type_Fixed_Array:   return const_elements(cx, v.elem, v.size, nil, with_defaults)
    case ^Type_Partial_Array:
        push_index(cx, fmt.tprintf("i32 %d", PARTIAL_ELEMENTS_FIELD))
        elems := const_elements(cx, v.elem, v.size, nil, with_defaults)
        pop_index(cx)
        return const_partial_with(cx, v, 0, elems)
    }
    return "zeroinitializer"
}

@(private="file")
push_index :: proc(cx: ^Const_Ctx, index: string) { append(&cx.path, index) }
@(private="file")
pop_index :: proc(cx: ^Const_Ctx) { pop(&cx.path) }

// A struct with no constructor params and nothing in its body but field
// declarations and definitions: constructing it is zero + field defaults +
// headers, all compile-time. (The declaration forms are the ones
// extract_fields_from_body turns into fields.)
@(private="file")
struct_is_plain_data :: proc(sd: ^Scope_Body) -> bool {
    if sd.ast == nil { return true }
    if len(sd.ast.typed_params) > 0 { return false }
    for s in sd.ast.body {
        #partial switch v in s {
        case ^Stmt_Assign:       if !v.is_decl { return false }
        case ^Stmt_Multi_Assign, ^Stmt_Decl:
        case:                    if !is_scope_def(s) { return false }
        }
    }
    return true
}

@(private="file")
const_struct :: proc(cx: ^Const_Ctx, sd: ^Scope_Body, e: Expr, with_defaults: bool) -> string {
    if !struct_is_plain_data(sd) || sd.backing_bytes > 0 { const_fail(cx, e) }
    with_defaults := with_defaults
    values := make([]Expr, len(sd.fields), context.temp_allocator)
    if e != nil {
        #partial switch v in e {
        case ^Expr_Struct_Literal:
            if v.is_spread || v.override_target != "" { const_fail(cx, e) }
            if v.zero_init { with_defaults = false }
            for field, pos in v.fields {
                idx := first_user_field(sd) + pos if v.positional else struct_field_index(sd, field.name)
                if idx < 0 || idx >= len(values) { const_fail(cx, field.value) }
                values[idx] = field.value
            }
        case ^Expr_Call:
            // `T(a, b)` / `T(){...}` of a plain struct: positional args, then overrides.
            if call_resolved_name(v) != sd.name || v.fn_value != nil { const_fail(cx, e) }
            for arg, i in v.args {
                if i >= len(values) { const_fail(cx, arg) }
                values[i] = arg
            }
            if v.overrides != nil {
                for field in v.overrides.fields {
                    idx := struct_field_index(sd, field.name)
                    if idx < 0 { const_fail(cx, field.value) }
                    values[idx] = field.value
                }
            }
        case:
            const_fail(cx, e)
        }
    }
    parts := make([]string, len(sd.fields), context.temp_allocator)
    all_zero := true
    for &f, i in sd.fields {
        push_index(cx, fmt.tprintf("i32 %d", i))
        text: string
        if sd.is_union_variant && i == 0 {
            text = fmt.tprintf("%d", sd.union_variant_tag) // the discriminant, always set
        } else if values[i] != nil {
            text = const_init(cx, values[i], f.type_)
        } else if with_defaults && f.default_value != nil {
            text = const_init(cx, f.default_value, f.type_)
        } else {
            text = const_default(cx, f.type_, with_defaults)
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

// `n` elements of type `elem` from `values` (nil slots and past the end:
// defaults), as `[T a, T b, ...]` — or zeroinitializer when all zero.
@(private="file")
const_elements :: proc(cx: ^Const_Ctx, elem: Type, n: int, values: []Expr, with_defaults: bool) -> string {
    elem_ir := llvm_type_from_checker(elem)
    parts := make([]string, n, context.temp_allocator)
    all_zero := true
    for k in 0..<n {
        push_index(cx, fmt.tprintf("i64 %d", k))
        text: string
        if k < len(values) && values[k] != nil {
            text = const_init(cx, values[k], elem)
        } else {
            text = const_default(cx, elem, with_defaults)
        }
        pop_index(cx)
        if text != "zeroinitializer" { all_zero = false }
        parts[k] = strings.concatenate({elem_ir, " ", text})
    }
    if all_zero { return "zeroinitializer" }
    return strings.concatenate({"[", strings.join(parts, ", "), "]"})
}

// A byte string's bytes as a `[n x i8]` initializer, zero-padded.
@(private="file")
const_bytes :: proc(cx: ^Const_Ctx, s: string, n: int, at: Expr) -> string {
    if len(s) > n { const_fail(cx, at) }
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

// The slot values of an array-shaped literal, and whether `{0}` zeroed it.
@(private="file")
array_literal_values :: proc(cx: ^Const_Ctx, e: Expr) -> (values: []Expr, zero_init: bool) {
    #partial switch v in e {
    case ^Expr_Array:
        return v.elements[:], false
    case ^Expr_Struct_Literal:
        if v.zero_init { return nil, true }
        if v.array_values != nil { return v.array_values[:], false }
        if len(v.fields) == 0 { return nil, false }
        // Positional values the checker left in `fields` (an anonymous nested
        // array literal).
        if v.positional {
            vals := make([]Expr, len(v.fields), context.temp_allocator)
            for f, i in v.fields { vals[i] = f.value }
            return vals, false
        }
    }
    const_fail(cx, e)
}

@(private="file")
const_array :: proc(cx: ^Const_Ctx, fa: ^Type_Fixed_Array, e: Expr) -> string {
    if s, is_str := e.(^Expr_String); is_str && is_byte_elem_type(fa.elem) {
        return const_bytes(cx, s.value, fa.size, e)
    }
    values, zero_init := array_literal_values(cx, e)
    if len(values) > fa.size { const_fail(cx, e) }
    return const_elements(cx, fa.elem, fa.size, values, !zero_init)
}

// A partial array: its header (len, cap, and a pointer to its own elements,
// the way construction stamps it) and its elements.
@(private="file")
const_partial :: proc(cx: ^Const_Ctx, pa: ^Type_Partial_Array, e: Expr) -> string {
    if s, is_str := e.(^Expr_String); is_str && is_byte_elem_type(pa.elem) {
        return const_partial_with(cx, pa, len(s.value), const_bytes(cx, s.value, pa.size, e))
    }
    values, zero_init := array_literal_values(cx, e)
    if len(values) > pa.size { const_fail(cx, e) }
    push_index(cx, fmt.tprintf("i32 %d", PARTIAL_ELEMENTS_FIELD))
    elems := const_elements(cx, pa.elem, pa.size, values, !zero_init)
    pop_index(cx)
    return const_partial_with(cx, pa, len(values), elems)
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
        slice_layout.len_ir, n, slice_layout.cap_ir, pa.size, self, pa.size, elem_ir, elems)
}

// A slice field: empty, or a view of a string (its bytes in a private global,
// len = byte count and cap one more, like a string passed as a slice).
@(private="file")
const_slice :: proc(cx: ^Const_Ctx, sl: ^Type_Slice, e: Expr) -> string {
    s, is_str := e.(^Expr_String)
    if !is_str || !is_byte_elem_type(sl.elem) { const_fail(cx, e) }
    cx.n_extra += 1
    name := fmt.tprintf("%s.s%d", cx.global, cx.n_extra)
    fmt.sbprintf(&cx.extras, "%s = private unnamed_addr constant [%d x i8] %s\n",
        name, len(s.value) + 1, const_bytes(cx, s.value, len(s.value) + 1, e))
    return fmt.tprintf("{{ %s %d, %s %d, ptr %s }}",
        slice_layout.len_ir, len(s.value), slice_layout.cap_ir, len(s.value) + 1, name)
}

// A union constant's table: the variant's struct (tag included) padded out to
// the union's size — its own IR type, since pointers are opaque and every
// access types the load at the use site.
@(private="file")
const_union_table :: proc(cx: ^Const_Ctx, ut: ^Type_Union, e: Expr) -> (gtype: string, init: string) {
    g := cx.g
    e := const_resolve(g, e)
    variant := ""
    #partial switch v in e {
    case ^Expr_Struct_Literal: variant = v.name
    case ^Expr_Ident:
        if rv, ok := v.resolved.(Resolved_Union_Variant); ok { variant = rv.variant }
    case ^Expr_Field_Access:
        if rv, ok := v.resolved.(Resolved_Union_Variant); ok { variant = rv.variant }
    }
    if variant == "" || is_niche_layout(g, ut) { const_fail(cx, e) }
    vsd, ok := lookup_struct(g, ut.variant_structs[variant])
    if !ok { const_fail(cx, e) }
    vname := struct_llvm_name(struct_key(vsd))
    tail := union_byte_size(g, ut) - struct_byte_size_sd(vsd, g.checked)
    lit: Expr // a payload-less `.None`-style variant has no literal: defaults only
    if _, is_lit := e.(^Expr_Struct_Literal); is_lit { lit = e }
    if tail <= 0 {
        cx.gtype = vname
        return vname, const_struct(cx, vsd, lit, true)
    }
    cx.gtype = fmt.tprintf("<{{ %s, [%d x i8] }}>", vname, tail)
    push_index(cx, "i32 0")
    body := const_struct(cx, vsd, lit, true)
    pop_index(cx)
    return cx.gtype, fmt.tprintf("<{{ %s %s, [%d x i8] zeroinitializer }}>", vname, body, tail)
}

// ---------------------------------------------------------------------------
// Scalars: folded here, since LLVM no longer folds most arithmetic in a
// constant initializer.
// ---------------------------------------------------------------------------

@(private="file")
Const_Num :: struct {
    f:        f64,
    i:        i128,
    is_float: bool,
}

@(private="file")
num_f :: proc(n: Const_Num) -> f64 { return n.f if n.is_float else f64(n.i) }

@(private="file")
const_num :: proc(g: ^Codegen, e: Expr) -> (n: Const_Num, ok: bool) {
    #partial switch v in e {
    case ^Expr_Number: return {v.value, v.int_value, v.is_float}, true
    case ^Expr_Char:   return {f64(v.value), i128(v.value), false}, true
    case ^Expr_Bool:
        n := i128(1) if v.value else i128(0)
        return {f64(n), n, false}, true
    case ^Expr_Unary:
        x := const_num(g, v.operand) or_return
        #partial switch v.op {
        case .Minus: return {-x.f, -x.i, x.is_float}, true
        case .Tilde: if !x.is_float { return {f64(~x.i), ~x.i, false}, true }
        case .Bang, .Not:
            n := i128(1) if x.i == 0 else i128(0)
            return {f64(n), n, false}, true
        }
    case ^Expr_Binary:
        l := const_num(g, v.left) or_return
        r := const_num(g, v.right) or_return
        if l.is_float || r.is_float {
            a, b := num_f(l), num_f(r)
            #partial switch v.op {
            case .Plus:  return {a + b, 0, true}, true
            case .Minus: return {a - b, 0, true}, true
            case .Star:  return {a * b, 0, true}, true
            case .Slash: if b != 0 { return {a / b, 0, true}, true }
            }
            return {}, false
        }
        a, b := l.i, r.i
        #partial switch v.op {
        case .Plus:        return {f64(a + b), a + b, false}, true
        case .Minus:       return {f64(a - b), a - b, false}, true
        case .Star:        return {f64(a * b), a * b, false}, true
        case .Slash:       if b != 0 { return {f64(a / b), a / b, false}, true }
        case .Modulo:      if b != 0 { return {f64(a % b), a % b, false}, true }
        case .Shift_Left:  if b >= 0 { return {f64(a << uint(b)), a << uint(b), false}, true }
        case .Shift_Right: if b >= 0 { return {f64(a >> uint(b)), a >> uint(b), false}, true }
        case .Ampersand:   return {f64(a & b), a & b, false}, true
        case .Pipe:        return {f64(a | b), a | b, false}, true
        case .Tilde:       return {f64(a ~ b), a ~ b, false}, true
        }
    case ^Expr_Call:
        // A numeric conversion (`f32(x)`, `u8(5)`) of a constant.
        if ir, is_float, is_ptr, ok := cast_target_ir_type(v.name); ok && !is_ptr && v.qualifier == nil && len(v.args) == 1 {
            x := const_num(g, v.args[0]) or_return
            if is_float { return {num_f(x), 0, true}, true }
            i := i128(x.f) if x.is_float else x.i
            if ir == "i1" { i = 1 if i != 0 else 0 }
            return {f64(i), i, false}, true
        }
        if inner, ok := call_passthrough_value(g, v); ok { return const_num(g, inner) }
    case ^Expr_Ident:
        if ev, ok := v.resolved.(Resolved_Enum_Variant); ok { return {f64(ev.value), i128(ev.value), false}, true }
        if value, ok := const_value_of(g, e); ok { return const_num(g, value) }
    case ^Expr_Field_Access:
        if ev, ok := v.resolved.(Resolved_Enum_Variant); ok { return {f64(ev.value), i128(ev.value), false}, true }
        if rc, ok := v.resolved.(Resolved_Constant); ok && rc.value_expr == nil {
            return {f64(rc.int_value), i128(rc.int_value), false}, true // `arr.len`
        }
        if value, ok := const_value_of(g, e); ok { return const_num(g, value) }
    }
    return {}, false
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
const_scalar :: proc(cx: ^Const_Ctx, e: Expr, t: Type) -> string {
    ir := llvm_type_from_checker(t)
    if ir == "ptr" {
        if id, is_id := e.(^Expr_Ident); is_id && id.name == "void" { return "null" }
        const_fail(cx, e)
    }
    n, ok := const_num(cx.g, e)
    if !ok { const_fail(cx, e) }
    switch ir {
    case "i1":
        return "true" if num_f(n) != 0 else "false"
    case "half", "float", "double":
        return emit_number_literal(ir, num_f(n), 0, true)
    }
    if n.is_float { const_fail(cx, e) }
    return fmt.tprintf("%d", wrap_int(n.i, ir_type_bits(ir)))
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
