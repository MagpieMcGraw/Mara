package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// What the program says: print's lowering (a value of any type, as text),
// assert's and crash's messages, the runtime checks' — and number literals.
// ---------------------------------------------------------------------------

// A numeric literal as a constant of the given IR type. A float is its exact
// IEEE-754 bits (a float's value as a double's, LLVM's `0x…`; a half's, its
// own); an integer its exact i128 value (an f64 loses precision above 2^53).
emit_number_literal :: proc(target_type: Ir_Type, value: f64, int_value: i128, is_float: bool) -> Val {
    tt := target_type
    if tt == IR_NONE {
        tt = is_float ? IR_DOUBLE : IR_I64
    }
    switch tt {
    case IR_HALF:
        return ir_half(transmute(u16)f16(value))
    case IR_FLOAT:
        return ir_float(transmute(u64)f64(f32(value)))
    case IR_DOUBLE:
        return ir_float(transmute(u64)value)
    case IR_I8, IR_I16, IR_I32, IR_I64, IR_I128:
        return ir_int128(int_value)
    case:
        if is_float {
            return ir_float(transmute(u64)value)
        }
        return ir_int128(int_value)
    }
}

// ---------------------------------------------------------------------------
// Binary expression codegen
// ---------------------------------------------------------------------------

// Whether an assert on a comparison in this IR type reports its sides'
// values: what printf can carry — bools, ints up to 64 bits, floats.
assert_reports :: proc(ir_type: Ir_Type) -> bool {
    switch ir_type {
    case IR_I1, IR_I8, IR_I16, IR_I32, IR_I64, IR_HALF, IR_FLOAT, IR_DOUBLE: return true
    }
    return false
}

// One side of an assert's comparison: its source text ("" when that states
// its value: not reported), its value in the comparison's IR type, and its
// own type.
Assert_Side :: struct {
    text: string,
    val:  Val,
    t:    Type,
}

// An assert's failure: the crash journal opens, the message prints — where,
// what was expected, and each reported side's value, or with no sides, that
// the condition was false — and the program exits. The message is one
// printf format assembled here; only the values are runtime arguments.
emit_assert_fail :: proc(g: ^Codegen, span: Span, cond_text: string, sides: []Assert_Side, ir_type: Ir_Type, is_unsigned: bool) {
    emit_crash_journal_begin(g)
    loc := span_location(span)
    // Embedded source text must not smuggle conversion specs into the
    // format string (`a % b == 0`), so escape every %.
    esc_cond, _ := strings.replace_all(cond_text, "%", "%%", context.temp_allocator)
    msg := strings.builder_make(context.temp_allocator)
    args := make([dynamic]Ir_Arg, context.temp_allocator)
    fmt.sbprintf(&msg, "Assert failed at %s\nExpected %s", loc, esc_cond)
    if len(sides) == 0 { strings.write_string(&msg, ", but it was false") }
    is_float := is_ir_float(ir_type)
    is_bool  := ir_type == IR_I1
    spec := is_bool ? "%s" : (is_float ? "%g" : (is_unsigned ? "%llu" : "%lld"))
    joiner := ", but "
    for side in sides {
        if side.text == "" { continue }
        esc_side, _ := strings.replace_all(side.text, "%", "%%", context.temp_allocator)
        // An enum side prints its variant name through the same inline
        // switch print() uses. That machinery does its own printf calls, so
        // flush the message built so far and let it take over mid-sentence.
        if et, is_enum := distinct_base(side.t).(^Type_Enum); is_enum {
            fmt.sbprintf(&msg, "%s%s was ", joiner, esc_side)
            joiner = " and "
            assert_flush_printf(g, &msg, &args)
            tag_ir := llvm_type_from_checker(et)
            v := side.val
            if ir_type != tag_ir {
                w := fresh_tmp(g)
                op := ir_type_bits(ir_type) > ir_type_bits(tag_ir) ? Ir_Inst.Trunc : .Zext
                ir_cast(g, w, op, ir_type, side.val, tag_ir)
                v = w
            }
            gen_print_enum(g, v, tag_ir, et, label = print_type_label(side.t))
            continue
        }
        // A utf8 side renders as the glyph, same as print() — the value
        // reads like the literal it's compared to: 'e'.
        _, is_utf8 := side.t.(Type_Utf8)
        is_char := !is_bool && !is_float && is_utf8
        fmt.sbprintf(&msg, "%s%s was %s", joiner, esc_side, is_char ? "'%c'" : spec)
        joiner = " and "
        v := side.val
        switch {
        case is_bool:
            t_global := get_string_literal(g, "true")
            f_global := get_string_literal(g, "false")
            sel := fresh_tmp(g)
            ir_select(g, sel, side.val, IR_PTR, t_global, f_global)
            append(&args, Ir_Arg{IR_PTR, sel, {}})
        case is_float:
            if ir_type != IR_DOUBLE {
                v = fresh_tmp(g)
                ir_cast(g, v, .Fpext, ir_type, side.val, IR_DOUBLE)
            }
            append(&args, Ir_Arg{IR_DOUBLE, v, {}})
        case is_char:
            // %c reads an i32 vararg (default promotion).
            if ir_type != IR_I32 {
                v = fresh_tmp(g)
                ir_cast(g, v, ir_type == IR_I64 ? Ir_Inst.Trunc : .Zext, ir_type, side.val, IR_I32)
            }
            append(&args, Ir_Arg{IR_I32, v, {}})
        case:
            if ir_type != IR_I64 {
                v = fresh_tmp(g)
                ir_cast(g, v, is_unsigned ? Ir_Inst.Zext : .Sext, ir_type, side.val, IR_I64)
            }
            append(&args, Ir_Arg{IR_I64, v, {}})
        }
    }
    strings.write_string(&msg, "\n")
    assert_flush_printf(g, &msg, &args)
    emit_crash_journal_end(g)
    ir_call(g, {}, IR_VOID, ir_global("exit"), {IR_I32, ir_int(1), {}})
    ir_unreachable(g)
}

// Emit the pending assert-message segment as one printf and reset the
// builders. Segmented because enum sides print through gen_print_enum's
// inline switch, which does its own printf calls mid-message.
assert_flush_printf :: proc(g: ^Codegen, msg: ^strings.Builder, args: ^[dynamic]Ir_Arg) {
    if strings.builder_len(msg^) == 0 { return }
    msg_global := get_string_literal(g, strings.to_string(msg^))
    all := make([dynamic]Ir_Arg, 0, len(args) + 1, context.temp_allocator)
    append(&all, Ir_Arg{IR_PTR, msg_global, {}})
    append(&all, ..args[:])
    ir_call_va(g, {}, IR_I32, IR_PRINTF, printf_sym(g), ..all[:])
    strings.builder_reset(msg)
    clear(args)
}

// Open/close a crash.txt journal entry around a fail block's message
// emission (native builds only; web has no filesystem). Between the two,
// g.tee routes every print-shaped emission through __mara_tee_printf so the
// message lands in the journal as well as on stdout.
emit_crash_journal_begin :: proc(g: ^Codegen) {
    if g.web { return }
    ir_call(g, {}, IR_VOID, ir_global("__mara_crash_begin"))
    g.tee = true
}

emit_crash_journal_end :: proc(g: ^Codegen) {
    if g.web { return }
    g.tee = false
    ir_call(g, {}, IR_VOID, ir_global("__mara_crash_end"))
}

// A runtime failure: the journal opens, the message prints — `message`, a C
// format, and its `args` — and the program exits. Nothing runs after it.
emit_fail :: proc(g: ^Codegen, message: string, args: ..Ir_Arg) {
    emit_crash_journal_begin(g)
    all := make([dynamic]Ir_Arg, 0, len(args) + 1, context.temp_allocator)
    append(&all, Ir_Arg{IR_PTR, get_string_literal(g, message), {}})
    append(&all, ..args)
    ir_call_va(g, {}, IR_I32, IR_PRINTF, printf_sym(g), ..all[:])
    emit_crash_journal_end(g)
    ir_call(g, {}, IR_VOID, ir_global("exit"), {IR_I32, ir_int(1), {}})
    ir_unreachable(g)
}

// A value at slice header width (SLICE_LEN_IR), as emit_fail's argument.
fail_i64 :: proc(v: Val) -> Ir_Arg {
    return {IR_I64, v, {}}
}

// ---------------------------------------------------------------------------
// Type cast codegen: i32(x), f64(x), etc.
// ---------------------------------------------------------------------------

// A number type's bits; 0 for any other type.
ir_type_bits :: proc(t: Ir_Type) -> int {
    #partial switch info := ir_type_info(t); info.kind {
    case .Int:    return info.n
    case .Half:   return 16
    case .Float:  return 32
    case .Double: return 64
    }
    return 0
}

is_ir_float :: proc(t: Ir_Type) -> bool {
    return t == IR_HALF || t == IR_FLOAT || t == IR_DOUBLE
}

// ---------------------------------------------------------------------------
// Function call codegen
// ---------------------------------------------------------------------------

// cstring(s) — VALIDITY, not content: a 0 must exist inside the slice's
// storage so C can never run past it. len < cap: the byte at [len] must be 0;
// len == cap: the LAST byte [cap-1] must be 0 (and cap > 0). No terminator: a
// loud crash with the location. The data pointer, checked.
emit_cstring_check :: proc(g: ^Codegen, len_val, cap_val, src_ptr: Val, span: Span) -> Val {
    w := SLICE_LEN_IR
    at_len_lbl  := fresh_label(g, "cstring.at_len")
    at_end_lbl  := fresh_label(g, "cstring.at_end")
    end_ok_lbl  := fresh_label(g, "cstring.end_ok")
    pass_lbl    := fresh_label(g, "cstring.pass")
    crash_lbl   := fresh_label(g, "cstring.fail")
    has_room := fresh_tmp(g)
    ir_icmp(g, has_room, .Slt, w, len_val, cap_val)
    emit_cond_br(g, has_room, at_len_lbl, at_end_lbl)
    // len < cap: terminator sits right after the content.
    emit_label(g, at_len_lbl)
    p1 := fresh_tmp(g)
    emit_elem_gep(g, p1, IR_I8, src_ptr, len_val, w)
    b1 := fresh_tmp(g)
    emit_load_into(g, b1, IR_I8, p1)
    ok1 := fresh_tmp(g)
    ir_icmp(g, ok1, .Eq, IR_I8, b1, ir_int(0))
    emit_cond_br(g, ok1, pass_lbl, crash_lbl)
    // len == cap: full view — the last byte must be 0 (and cap > 0 so
    // the [cap-1] read stays inside the storage).
    emit_label(g, at_end_lbl)
    cap_pos := fresh_tmp(g)
    ir_icmp(g, cap_pos, .Sgt, w, cap_val, ir_int(0))
    emit_cond_br(g, cap_pos, end_ok_lbl, crash_lbl)
    emit_label(g, end_ok_lbl)
    last := fresh_tmp(g)
    ir_bin(g, last, .Sub, w, cap_val, ir_int(1))
    p2 := fresh_tmp(g)
    emit_elem_gep(g, p2, IR_I8, src_ptr, last, w)
    b2 := fresh_tmp(g)
    emit_load_into(g, b2, IR_I8, p2)
    ok2 := fresh_tmp(g)
    ir_icmp(g, ok2, .Eq, IR_I8, b2, ir_int(0))
    emit_cond_br(g, ok2, pass_lbl, crash_lbl)
    emit_label(g, crash_lbl)
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    emit_fail(g, fmt.tprintf("runtime error: cstring() at %s: no terminating 0 in the slice (checked [len] since len < cap, or [cap-1] for a full slice) — append into headroom or zero-pad the buffer\n", loc))
    emit_label(g, pass_lbl)
    return src_ptr
}


// A `byte` element — what makes an array a byte buffer (is_byte_buffer), the
// only storage take/let and typed `&buf[off]` pointers reinterpret.
is_byte_elem :: proc(t: Type) -> bool {
    _, is_byte := distinct_base(t).(Type_Byte)
    return is_byte
}

// Whether storage of type `t` could hold a value of type `d` somewhere inside
// it — so a pointer to a `d` could point into it. Byte buffers can hold
// anything: take/let reinterpret their bytes as any type.
type_can_contain :: proc(t: Type, d: Type) -> bool {
    bt, bd := distinct_base(t), distinct_base(d)
    if types_equal(bt, bd) { return true }
    if sd := as_struct_body(bt); sd != nil {
        for &f in sd.fields {
            if type_can_contain(f.type_, d) { return true }
        }
        return false
    }
    #partial switch v in bt {
    case ^Type_Fixed_Array:
        return is_byte_elem(v.elem) || type_can_contain(v.elem, d)
    case ^Type_Partial_Array:
        return is_byte_elem(v.elem) || type_can_contain(v.elem, d)
    case ^Type_Union:
        return true
    }
    return false
}

// A type whose values hold no pointers, so nothing in one can refer to other
// storage. (A partial array's header pointer only ever points at its own
// elements.) Unions, slices, pointers, cstrings and function values don't
// qualify.
is_plain_data :: proc(t: Type) -> bool {
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil {
        for &f in sd.fields {
            if !is_plain_data(f.type_) { return false }
        }
        return true
    }
    #partial switch v in base {
    case Type_F64, Type_Infer_Int, Type_Infer_Float, Type_Bool, Type_Utf8, Type_Byte,
         Type_Numeric, ^Type_Enum, Type_Err, Type_Atom:
        return true
    case ^Type_Fixed_Array:
        return is_plain_data(v.elem)
    case ^Type_Partial_Array:
        return is_plain_data(v.elem)
    }
    return false
}

// ---------------------------------------------------------------------------
// Crash builtin — print message and exit(1)
// ---------------------------------------------------------------------------

// A crash: the journal opens, "Crashed at <where>" and the message (a C
// string, when there is one) print, and the program exits. Code after it in
// the same scope lands in a fresh dead block — IR after `unreachable` is
// invalid.
emit_crash :: proc(g: ^Codegen, span: Span, msg: Val) {
    // (The location line, as an assert's.)
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    if msg.kind != .None {
        emit_fail(g, fmt.tprintf("Crashed at %s\n%%s\n", loc), {IR_PTR, msg, {}})
    } else {
        emit_fail(g, fmt.tprintf("Crashed at %s\n", loc))
    }
    emit_label(g, fresh_label(g, "crash.dead"))
}

// ---------------------------------------------------------------------------
// Print builtin — uses C printf
// ---------------------------------------------------------------------------

// A print's argument, evaluated: a string constant's text, a register value,
// or where an aggregate is.
Print_Arg :: struct {
    text:    string,
    is_text: bool,
    val:     Val,   // a register value; text's bytes' address
    addr:    Val,   // an aggregate's address
    t:       Type,
}

emit_print_operand :: proc(g: ^Codegen, v: Print_Arg) {
    switch {
    case v.is_text:   emit_print_text(g, v.val, ir_int(len(v.text)))
    case v.addr.kind != .None: emit_print_at_addr(g, v.addr, v.t)
    case:             emit_print_value(g, v.val, v.t)
    }
}

// print_cstr, print_int, print_float: the printf spec each prints its value
// with, and the value's IR type.
raw_print :: proc(name: string) -> (spec: string, ir: Ir_Type, ok: bool) {
    switch name {
    case "print_cstr":  return "%s", IR_PTR, true
    case "print_int":   return "%lld", IR_I64, true
    case "print_float": return "%g", IR_DOUBLE, true
    }
    return
}

// Text of `n` bytes (at slice header width) at `data`, printed: bounded, so
// it needs no terminating 0. (`%.*s` takes an int: n, narrowed.)
emit_print_text :: proc(g: ^Codegen, data, n: Val) {
    prec := fresh_tmp(g)
    ir_cast(g, prec, .Trunc, SLICE_LEN_IR, n, IR_I32)
    emit_printf(g, "%.*s", {IR_I32, prec, {}}, {IR_PTR, data, {}})
}

// True if `s` contains a `%` placeholder (i.e. an unescaped `%`). `%%` is the
// escape for a literal `%` and does not count.
string_has_format_pct :: proc(s: string) -> bool {
    i := 0
    for i < len(s) {
        if s[i] == '%' {
            if i+1 < len(s) && s[i+1] == '%' {
                i += 2
                continue
            }
            return true
        }
        i += 1
    }
    return false
}

// Emit the printf calls for a format string with `%` placeholders. Static
// runs are emitted as a single `printf("%s", ...)` per run (with `%%` decoded
// to a literal `%`); each placeholder prints the next (evaluated) arg.
emit_print_format :: proc(g: ^Codegen, fmt_str: string, args: []Print_Arg, call_span: Span) {
    seg_buf: [dynamic]u8
    defer delete(seg_buf)
    arg_idx := 0
    flush :: proc(g: ^Codegen, seg: ^[dynamic]u8) {
        if len(seg^) == 0 { return }
        emit_print_literal(g, string(seg^[:]))
        clear(seg)
    }
    is_format_marker :: proc(c: u8) -> bool {
        // Letter chars after `%` are human-readable shorthand (`%d`, `%s`,
        // `%g`, `%v`, `%x`, ...). Mara picks the actual printf spec from
        // the arg's type, but the marker letter is consumed so it doesn't
        // appear in output. Non-letter chars (spaces, commas, punctuation,
        // digits) are bare-`%` placeholders followed by literal text.
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    }
    i := 0
    for i < len(fmt_str) {
        ch := fmt_str[i]
        if ch == '%' {
            if i+1 < len(fmt_str) && fmt_str[i+1] == '%' {
                append(&seg_buf, '%')
                i += 2
                continue
            }
            flush(g, &seg_buf)
            if arg_idx >= len(args) {
                codegen_fatal(g, call_span, CODE_FORMAT_STRING_MORE_PLACEHOLDERS_THAN)
            }
            emit_print_operand(g, args[arg_idx])
            arg_idx += 1
            // Advance past `%`. If a letter follows, treat it as a human-
            // readable type marker and consume it too (`%d` → emit value,
            // skip both). If anything else follows (space, comma, '0',
            // etc.), the user meant a bare placeholder and we leave that
            // char alone — it's part of the surrounding literal text.
            if i+1 < len(fmt_str) && is_format_marker(fmt_str[i+1]) {
                i += 2
            } else {
                i += 1
            }
            continue
        }
        append(&seg_buf, ch)
        i += 1
    }
    flush(g, &seg_buf)
}

// Emit a printf("%s", literal) for an inline static string.
emit_print_literal :: proc(g: ^Codegen, s: string) {
    emit_printf(g, "%s", {IR_PTR, get_string_literal(g, s), {}})
}

emit_print_newline :: proc(g: ^Codegen) {
    emit_printf(g, "\n")
}

// Print an i1 as `true`/`false`. Shared by scalar args, struct fields, and
// array elements so bool renders consistently everywhere — and never reaches
// an integer printf format, which would either mistype the i1 (scalar: i1 in
// an i64 vararg slot → invalid IR) or sext it to a garbage value (array: true
// → -1).
gen_print_bool :: proc(g: ^Codegen, val_i1: Val) {
    true_ptr := get_string_literal(g, "true")
    false_ptr := get_string_literal(g, "false")
    bool_str := fresh_tmp(g)
    ir_select(g, bool_str, val_i1, IR_PTR, true_ptr, false_ptr)
    emit_printf(g, "%s", {IR_PTR, bool_str, {}})
}

// Print an already-loaded scalar VALUE given its Mara type — the single source
// of truth for how a scalar renders: print's own arguments, struct fields and
// array elements all route through here, so they match a bare `print(x)`:
// chars as glyphs, sign-aware integers, %g floats. Non-scalars (a nested struct/array field reaching here) hard-error rather than
// mis-emit — aggregates are handled by their own recursion before this is called.
emit_print_value :: proc(g: ^Codegen, val: Val, ty: Type) {
    if ty == nil { codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, "<unknown>") }
    bt := distinct_base(ty)

    if _, ok := bt.(Type_Bool); ok { gen_print_bool(g, val); return }
    if _, ok := bt.(Type_Utf8); ok {
        // utf8 scalar = a character: render the glyph, not the code point.
        ext := fresh_tmp(g)
        ir_cast(g, ext, .Zext, IR_I8, val, IR_I32)
        emit_printf(g, "%c", {IR_I32, ext, {}})
        return
    }
    if et, ok := bt.(^Type_Enum); ok {
        gen_print_enum(g, val, llvm_type_from_checker(et), et, label = print_type_label(ty))
        return
    }
    if _, ok := bt.(Type_Err); ok {
        ir_call(g, {}, IR_VOID, ir_global("__mara_print_err"), {IR_I64, val, {}})
        return
    }
    if _, ok := bt.(Type_Atom); ok {   // (its text, looked up)
        data, n := emit_atom_text(g, val, g.print_span)
        emit_print_text(g, data, n)
        return
    }
    if pt, ok := bt.(^Type_Ptr); ok {
        spec := "%p"
        if _, b := pt.elem.(Type_Byte); b { spec = "%s" }
        if _, u := pt.elem.(Type_Utf8); u { spec = "%s" }
        emit_printf(g, spec, {IR_PTR, val, {}})
        return
    }
    if _, ok := bt.(Type_CString); ok {
        emit_printf(g, "%s", {IR_PTR, val, {}})
        return
    }

    // Numeric (integers + floats): IR-width driven with sign awareness. (A
    // float prints as a double, an integer under 32 bits as an int: C's
    // varargs promote them.)
    is_unsigned := llvm_unsigned(ty)
    nt := llvm_type_from_checker(ty)
    switch nt {
    case IR_DOUBLE:
        emit_printf(g, "%g", {IR_DOUBLE, val, {}})
    case IR_FLOAT, IR_HALF:
        ext := fresh_tmp(g)
        ir_cast(g, ext, .Fpext, nt, val, IR_DOUBLE)
        emit_printf(g, "%g", {IR_DOUBLE, ext, {}})
    case IR_I64:
        emit_printf(g, is_unsigned ? "%llu" : "%lld", {IR_I64, val, {}})
    case IR_I32:
        emit_printf(g, is_unsigned ? "%u" : "%d", {IR_I32, val, {}})
    case IR_I1:
        gen_print_bool(g, val)
    case IR_I8, IR_I16:
        ext := fresh_tmp(g)
        ir_cast(g, ext, is_unsigned ? Ir_Inst.Zext : .Sext, nt, val, IR_I32)
        emit_printf(g, is_unsigned ? "%u" : "%d", {IR_I32, ext, {}})
    case IR_I128:
        gen_print_i128(g, val, is_unsigned)
    case:
        codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, type_name(ty))
    }
}

// A 128-bit integer printed. printf has no spec for one (and dividing one
// would call a runtime library), so its magnitude is cut into base-10^9
// chunks — long division of its four 32-bit limbs, 64-bit arithmetic only —
// and printed from its highest nonzero chunk, the others padded to nine
// digits. A negative one: "-", then its magnitude.
gen_print_i128 :: proc(g: ^Codegen, val: Val, is_unsigned: bool) {
    CHUNK :: 1_000_000_000
    mag := val
    if !is_unsigned {
        neg := fresh_tmp(g)
        ir_icmp(g, neg, .Slt, IR_I128, val, ir_int(0))
        minus, rest := fresh_label(g, "print128.minus"), fresh_label(g, "print128.rest")
        emit_cond_br(g, neg, minus, rest)
        emit_label(g, minus)
        emit_printf(g, "-")
        emit_br(g, rest)
        emit_label(g, rest)
        negated := fresh_tmp(g)
        ir_bin(g, negated, .Sub, IR_I128, ir_int(0), val)
        mag = fresh_tmp(g)
        ir_select(g, mag, neg, IR_I128, negated, val)
    }
    // Its limbs, most significant first.
    lo, high, hi := fresh_tmp(g), fresh_tmp(g), fresh_tmp(g)
    ir_cast(g, lo, .Trunc, IR_I128, mag, IR_I64)
    ir_bin(g, high, .Lshr, IR_I128, mag, ir_int(64))
    ir_cast(g, hi, .Trunc, IR_I128, high, IR_I64)
    limbs: [4]Val
    for half, i in ([2]Val{hi, lo}) {
        limbs[2 * i] = fresh_tmp(g)
        ir_bin(g, limbs[2 * i], .Lshr, IR_I64, half, ir_int(32))
        limbs[2 * i + 1] = fresh_tmp(g)
        ir_bin(g, limbs[2 * i + 1], .And, IR_I64, half, ir_int(0xFFFF_FFFF))
    }
    // Divided by 10^9 four times: each time's remainder a chunk, least
    // significant first; what's left (under 341) the last.
    chunks: [5]Val
    for c in 0 ..< 4 {
        r := ir_int(0)
        for i in 0 ..< 4 {
            cur := limbs[i]
            if i > 0 {
                up, joined := fresh_tmp(g), fresh_tmp(g)
                ir_bin(g, up, .Shl, IR_I64, r, ir_int(32))
                ir_bin(g, joined, .Or, IR_I64, up, limbs[i])
                cur = joined
            }
            q, rem := fresh_tmp(g), fresh_tmp(g)
            ir_bin(g, q, .Udiv, IR_I64, cur, ir_int(CHUNK))
            ir_bin(g, rem, .Urem, IR_I64, cur, ir_int(CHUNK))
            limbs[i], r = q, rem
        }
        chunks[c] = r
    }
    chunks[4] = limbs[3]
    // From the highest nonzero chunk.
    done := fresh_label(g, "print128.done")
    for top := 4; top > 0; top -= 1 {
        here, below := fresh_label(g, "print128.top"), fresh_label(g, "print128.below")
        nonzero := fresh_tmp(g)
        ir_icmp(g, nonzero, .Ne, IR_I64, chunks[top], ir_int(0))
        emit_cond_br(g, nonzero, here, below)
        emit_label(g, here)
        format := strings.builder_make(context.temp_allocator)
        strings.write_string(&format, "%llu")
        args := make([dynamic]Ir_Arg, 0, top + 1, context.temp_allocator)
        append(&args, Ir_Arg{IR_I64, chunks[top], {}})
        for c := top - 1; c >= 0; c -= 1 {
            strings.write_string(&format, "%09llu")
            append(&args, Ir_Arg{IR_I64, chunks[c], {}})
        }
        emit_printf(g, strings.to_string(format), ..args[:])
        emit_br(g, done)
        emit_label(g, below)
    }
    emit_printf(g, "%llu", {IR_I64, chunks[0], {}})
    emit_br(g, done)
    emit_label(g, done)
}

// Print whatever lives at `addr` given its Mara type — the recursive core of
// aggregate printing. Scalars load + emit_print_value; structs and fixed arrays
// recurse. This is what lets struct fields and array elements render like a bare
// print at any nesting depth (struct-in-struct, array-of-structs, ...).
emit_print_at_addr :: proc(g: ^Codegen, addr: Val, ty: Type) {
    // (A distinct one's, under its own name: print_type_label.)
    if ut, is_union := distinct_base(ty).(^Type_Union); is_union {
        gen_print_union(g, addr, ut, print_type_label(ty))
        return
    }
    if sd := as_struct_body(distinct_base(ty)); sd != nil {
        gen_print_struct(g, addr, sd, print_type_label(ty))
        return
    }
    bt := distinct_base(ty)

    // An array: its elements, `[a, b]` — a utf8 one (a string) as text, like
    // a bare print(string). A fixed one's are here, as many as its size; a
    // slice's or a partial array's are its header's, as many as its len.
    if fa, ok := bt.(^Type_Fixed_Array); ok {
        if _, u := distinct_base(fa.elem).(Type_Utf8); u {
            emit_print_text(g, addr, ir_int(fa.size))
        } else {
            gen_print_array_inline(g, addr, fa.size, fa.elem)
        }
        return
    }
    if elem := llvm_header_elem(bt); elem != nil {
        data := hdr_data_at(g, addr, bt)
        n := emit_header_field(g, addr, SLICE.len)
        if pa, is_list := bt.(^Type_Partial_Array); is_list { emit_len_check(g, n, ir_int(pa.size), g.print_span) }
        if _, u := distinct_base(elem).(Type_Utf8); u {
            emit_print_text(g, data, n)
        } else {
            gen_print_elements(g, data, n, elem)
        }
        return
    }

    // Scalar — load at its IR width and route through the value printer.
    val := fresh_tmp(g)
    emit_load_into(g, val, llvm_type_from_checker(ty), addr)
    emit_print_value(g, val, ty)
}

// A struct printed: `P { x: 4, y: 5 }` — its name as written (`name`, when
// given); a union variant's, its tag's (the variant's name), the tag itself
// not a field.
gen_print_struct :: proc(g: ^Codegen, addr: Val, st: ^Scope_Body, name := "") {
    say :: proc(g: ^Codegen, text: string) { emit_printf(g, text) }
    st_llvm := ir_class_type(st)
    first := first_user_field(st)
    if name != "" {
        say(g, name)
    } else if st.is_union_variant {
        // (Its tag, by the variant's bare name: it names the struct.)
        at := fresh_tmp(g)
        emit_field_gep_into(g, at, st_llvm, addr, 0)
        et := distinct_base(st.fields[0].type_).(^Type_Enum)
        tag_ir := llvm_type_from_checker(et)
        tag := fresh_tmp(g)
        emit_load_into(g, tag, tag_ir, at)
        gen_print_enum(g, tag, tag_ir, et, named = false)
    } else {
        say(g, print_struct_name(st))
    }
    user := st.fields[first:]
    say(g, " {}" if len(user) == 0 else " { ")
    for &f, i in user {
        if i > 0 { say(g, ", ") }
        say(g, fmt.tprintf("%s: ", f.name))
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, addr, first + i)
        // One field, by its Mara type — scalar, nested struct, or array, each
        // rendered identically to a bare print(field).
        emit_print_at_addr(g, gep, f.type_)
    }
    if len(user) > 0 { say(g, " }") }
}

// A union printed: the variant it holds, as that variant prints — `Rect {
// w: 3 }` — chosen by its tag when the program runs (a niche union's, its
// pointer's nullness). A tag no variant has prints `Shape(7)`.
gen_print_union :: proc(g: ^Codegen, addr: Val, ut: ^Type_Union, label := "") {
    tag_ir := union_tag_ir_type(ut)
    tag := load_union_tag(g, ut, addr)
    unknown, done := fresh_label(g, "union.unknown"), fresh_label(g, "union.done")
    arms := make([]Ir_Label, len(ut.variants), context.temp_allocator)
    cases := make([]Ir_Arg, len(ut.variants))
    for vname, i in ut.variants {
        arms[i] = fresh_label(g, "union.variant")
        cases[i] = {tag_ir, ir_int(ut.tag_map[vname]), arms[i]}
    }
    ir_switch(g, tag_ir, tag, unknown, cases)
    for vname, i in ut.variants {
        emit_label(g, arms[i])
        // (Each variant overlays the union's storage at its start.)
        if vst := ut.variant_structs[vname]; vst != nil {
            gen_print_struct(g, addr, &vst.sd, vname)
        } else {
            codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, type_name(ut))
        }
        emit_br(g, done)
    }
    emit_label(g, unknown)
    emit_print_literal(g, strings.concatenate({label if label != "" else type_name(ut), "("}, context.temp_allocator))
    emit_print_value(g, tag, Type_Numeric{kind = .Unsigned if union_tag_unsigned(ut) else .Signed, bits = i32(ir_type_bits(tag_ir))})
    emit_print_literal(g, ")")
    emit_br(g, done)
    emit_label(g, done)
}

// The name a value prints under when its type is a distinct one — `PD {
// x: 3 }`, `CD.Green` — its own, as written ("": its base's, as an alias's
// is: `type P` is P, and prints as one).
print_type_label :: proc(ty: Type) -> string {
    if dt, is_distinct := unwrap_alias(ty).(^Type_Distinct); is_distinct {
        return dt.source_name if dt.source_name != "" else dt.name
    }
    return ""
}

// A struct's name as print shows it: as written — `P`, `Box(i64)`.
print_struct_name :: proc(sd: ^Scope_Body) -> string {
    if sd.generic_base == "" { return sd.source_name if sd.source_name != "" else sd.name }
    args := make([dynamic]string, 0, len(sd.generic_args), context.temp_allocator)
    for a in sd.generic_args {
        if c, is_const := a.(Type_Const_Int); is_const {
            append(&args, fmt.tprintf("%d", c.value))
        } else if ab := as_struct_body(a); ab != nil {
            append(&args, print_struct_name(ab))
        } else {
            append(&args, type_name(a))
        }
    }
    return fmt.tprintf("%s(%s)", sd.generic_base, strings.join(args[:], ", ", context.temp_allocator))
}

// Inline switch that prints the variant name matching `val`, or
// "EnumName(<tag>)" when nothing matches (e.g. flag-combo, out-of-range raw
// tag). Variants are sorted by value for stable IR; same-value aliases keep
// the first in name order — LLVM's switch requires unique case values, so
// duplicates are folded into one case.
gen_print_enum :: proc(g: ^Codegen, val: Val, tag_ir: Ir_Type, et: ^Type_Enum, named := true, label := "") {
    // (Its name: a distinct enum's own — label — else the enum's.)
    enum_name := label if label != "" else et.source_name if et.source_name != "" else et.name
    Variant :: struct { name: string, value: int }
    entries := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
    for name, value in et.variants {
        append(&entries, Variant{name = name, value = value})
    }
    slice.sort_by(entries[:], proc(a, b: Variant) -> bool {
        if a.value != b.value { return a.value < b.value }
        return a.name < b.name
    })
    // Fold same-value aliases: first wins.
    dedup := make([dynamic]Variant, 0, len(entries), context.temp_allocator)
    for entry in entries {
        if len(dedup) > 0 && dedup[len(dedup)-1].value == entry.value { continue }
        append(&dedup, entry)
    }

    unknown_lbl := fresh_label(g, "enum.unknown")
    done_lbl    := fresh_label(g, "enum.done")
    case_labels := make([]Ir_Label, len(dedup), context.temp_allocator)
    for _, i in dedup {
        case_labels[i] = fresh_label(g, "enum.case")
    }

    cases := make([]Ir_Arg, len(dedup))
    for entry, i in dedup { cases[i] = {tag_ir, ir_int(entry.value), case_labels[i]} }
    ir_switch(g, tag_ir, val, unknown_lbl, cases)

    // A variant prints with its enum's name (`Color.Green`, `File_Error.Not_Found`,
    // a union's tag `Shape_Tag.Rect`): a variant's name alone can be any enum's.
    // (Not `named`: the variant's alone, as a union variant's struct is named.)
    name_prefix := ""
    if named { name_prefix = strings.concatenate({enum_name, "."}, context.temp_allocator) }

    for entry, i in dedup {
        emit_label(g, case_labels[i])
        emit_print_literal(g, strings.concatenate({name_prefix, entry.name}, context.temp_allocator))
        emit_br(g, done_lbl)
    }

    emit_label(g, unknown_lbl)
    emit_print_literal(g, fmt.tprintf("%s(", enum_name))
    switch tag_ir {
    case IR_I64:
        emit_printf(g, "%lld", {IR_I64, val, {}})
    case IR_I32:
        emit_printf(g, "%d", {IR_I32, val, {}})
    case:
        // i16 / i8: zext to i32 for printf's default-int varargs promotion.
        // zext (not sext) — enum tags are unsigned-shaped values, no two's-
        // complement bits to preserve.
        ext := fresh_tmp(g)
        ir_cast(g, ext, .Zext, tag_ir, val, IR_I32)
        emit_printf(g, "%d", {IR_I32, ext, {}})
    }
    emit_print_literal(g, ")")
    emit_br(g, done_lbl)

    emit_label(g, done_lbl)
}

// A fixed array's `size` elements at `data`, printed: [v1, v2, v3] (an
// element an array, as its own — [[1, 2], [3, 4]]).
gen_print_array_inline :: proc(g: ^Codegen, data: Val, size: int, elem: Type) {
    emit_printf(g, "[")
    arr_type := ir_array_type(size, llvm_type_from_checker(elem))
    for i := 0; i < size; i += 1 {
        if i > 0 { emit_printf(g, ", ") }
        gep := fresh_tmp(g)
        emit_array_gep_const(g, gep, arr_type, data, i)
        emit_print_at_addr(g, gep, elem)
    }
    emit_printf(g, "]")
}

// A slice's or a partial array's `n` elements at `data` (n known when the
// program runs), printed as a fixed array's are.
gen_print_elements :: proc(g: ^Codegen, data, n: Val, elem: Type) {
    emit_printf(g, "[")
    l := emit_loop_begin(g, n, "pah")
    sep, after := fresh_label(g, "pah.sep"), fresh_label(g, "pah.after")
    first := fresh_tmp(g)
    ir_icmp(g, first, .Eq, SLICE_LEN_IR, l.i, ir_int(0))
    emit_cond_br(g, first, after, sep)
    emit_label(g, sep)
    emit_printf(g, ", ")
    emit_br(g, after)
    emit_label(g, after)
    gep := fresh_tmp(g)
    emit_elem_gep(g, gep, llvm_type_from_checker(elem), data, l.i, SLICE_LEN_IR)
    emit_print_at_addr(g, gep, elem)
    emit_loop_end(g, l)
    emit_printf(g, "]")
}
