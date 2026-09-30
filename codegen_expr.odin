package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Expression codegen
// ---------------------------------------------------------------------------

// Lower a numeric literal to an LLVM constant for the given IR target type.
// Floats use the exact IEEE-754 hex bit-pattern (`0x…`) — a decimal print (`%f`)
// defaults to 3 fractional digits in Odin and silently truncates the value
// (3.14159… -> 3.142); hex is exact and is how clang itself writes floats.
// Integers use the exact i128 form (e.value is f64 and loses precision above
// 2^53). Shared by Expr_Number and module-constant (Resolved_Constant) access so
// a qualified `math.PI` lowers identically to a bare `PI`.
emit_number_literal :: proc(target_type: string, value: f64, int_value: i128, is_float: bool) -> string {
    tt := target_type
    if tt == "" {
        tt = is_float ? "double" : "i64"
    }
    switch tt {
    case "half":
        // LLVM half literals use the `0xH<4 hex>` form. Cast through f16 first.
        return fmt.tprintf("0xH%04X", transmute(u16)f16(value))
    case "float":
        return fmt.tprintf("0x%016X", transmute(u64)f64(f32(value)))
    case "double":
        return fmt.tprintf("0x%016X", transmute(u64)value)
    case "i8", "i16", "i32", "i64", "i128":
        return fmt.tprintf("%d", int_value)
    case:
        if is_float {
            return fmt.tprintf("0x%016X", transmute(u64)value)
        }
        return fmt.tprintf("%d", int_value)
    }
}

// ---------------------------------------------------------------------------
// Binary expression codegen
// ---------------------------------------------------------------------------

// A comparison side whose source text already states its value — a number,
// bool, or char literal (incl. a negated number), or an enum/union variant
// reference (.Paused, State.Paused) — is omitted from the assert failure
// report: `game.running == false` reports only game.running. Named constants
// are NOT literals: their text doesn't show their value, so they report.
assert_side_is_literal :: proc(ex: Expr) -> bool {
    #partial switch v in ex {
    case ^Expr_Number: return true
    case ^Expr_Bool:   return true
    case ^Expr_Char:   return true
    case ^Expr_Unary:
        if v.op == .Minus {
            if _, is_num := v.operand.(^Expr_Number); is_num { return true }
        }
    case ^Expr_Ident:
        #partial switch _ in v.resolved {
        case Resolved_Enum_Variant, Resolved_Union_Variant: return true
        }
    case ^Expr_Field_Access:
        #partial switch _ in v.resolved {
        case Resolved_Enum_Variant, Resolved_Union_Variant: return true
        }
    }
    return false
}

// Whether an assert on a comparison in this IR type reports its sides'
// values: what printf can carry — bools, ints up to 64 bits, floats.
assert_reports :: proc(ir_type: string) -> bool {
    switch ir_type {
    case "i1", "i8", "i16", "i32", "i64", "half", "float", "double": return true
    }
    return false
}

// One side of an assert's comparison: its source text ("" when that states
// its value: not reported), its value in the comparison's IR type, and its
// own type.
Assert_Side :: struct {
    text, val: string,
    t:         Type,
}

// An assert's failure: the crash journal opens, the message prints — where,
// what was expected, and each reported side's value, or with no sides, that
// the condition was false — and the program exits. The message is one
// printf format assembled here; only the values are runtime arguments.
emit_assert_fail :: proc(g: ^Codegen, span: Span, cond_text: string, sides: []Assert_Side, ir_type: string, is_unsigned: bool) {
    emit_crash_journal_begin(g)
    loc := format_location(span.file, span.line, span.col)
    // Embedded source text must not smuggle conversion specs into the
    // format string (`a % b == 0`), so escape every %.
    esc_cond, _ := strings.replace_all(cond_text, "%", "%%", context.temp_allocator)
    msg := strings.builder_make(context.temp_allocator)
    args := strings.builder_make(context.temp_allocator)
    fmt.sbprintf(&msg, "Assert failed at %s\nExpected %s", loc, esc_cond)
    if len(sides) == 0 { strings.write_string(&msg, ", but it was false") }
    is_float := is_ir_float(ir_type)
    is_bool  := ir_type == "i1"
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
            tag_ir := "i64"
            if et.tag_type != "" { tag_ir = tag_type_to_ir(et.tag_type) }
            v := side.val
            if ir_type != tag_ir {
                w := fresh_tmp(g)
                op := ir_type_bits(ir_type) > ir_type_bits(tag_ir) ? "trunc" : "zext"
                emit(g, "  %s = %s %s %s to %s", w, op, ir_type, side.val, tag_ir)
                v = w
            }
            gen_print_enum(g, v, tag_ir, et)
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
            t_global, _ := get_string_literal(g, "true")
            f_global, _ := get_string_literal(g, "false")
            sel := fresh_tmp(g)
            emit(g, "  %s = select i1 %s, ptr %s, ptr %s", sel, side.val, t_global, f_global)
            fmt.sbprintf(&args, ", ptr %s", sel)
        case is_float:
            if ir_type != "double" {
                v = fresh_tmp(g)
                emit(g, "  %s = fpext %s %s to double", v, ir_type, side.val)
            }
            fmt.sbprintf(&args, ", double %s", v)
        case is_char:
            // %c reads an i32 vararg (default promotion).
            if ir_type != "i32" {
                v = fresh_tmp(g)
                emit(g, "  %s = %s %s %s to i32", v, ir_type == "i64" ? "trunc" : "zext", ir_type, side.val)
            }
            fmt.sbprintf(&args, ", i32 %s", v)
        case:
            if ir_type != "i64" {
                v = fresh_tmp(g)
                emit(g, "  %s = %s %s %s to i64", v, is_unsigned ? "zext" : "sext", ir_type, side.val)
            }
            fmt.sbprintf(&args, ", i64 %s", v)
        }
    }
    strings.write_string(&msg, "\n")
    assert_flush_printf(g, &msg, &args)
    emit_crash_journal_end(g)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
}

// Emit the pending assert-message segment as one printf and reset the
// builders. Segmented because enum sides print through gen_print_enum's
// inline switch, which does its own printf calls mid-message.
assert_flush_printf :: proc(g: ^Codegen, msg: ^strings.Builder, args: ^strings.Builder) {
    if strings.builder_len(msg^) == 0 { return }
    msg_global, _ := get_string_literal(g, strings.to_string(msg^))
    emit(g, "  call i32 (ptr, ...) %s(ptr %s%s)", printf_sym(g), msg_global, strings.to_string(args^))
    strings.builder_reset(msg)
    strings.builder_reset(args)
}

// Open/close a crash.txt journal entry around a fail block's message
// emission (native builds only; web has no filesystem). Between the two,
// g.tee routes every print-shaped emission through __mara_tee_printf so the
// message lands in the journal as well as on stdout.
emit_crash_journal_begin :: proc(g: ^Codegen) {
    if g.web { return }
    emit(g, "  call void @__mara_crash_begin()")
    g.tee = true
}

emit_crash_journal_end :: proc(g: ^Codegen) {
    if g.web { return }
    g.tee = false
    emit(g, "  call void @__mara_crash_end()")
}

// ---------------------------------------------------------------------------
// Type cast codegen: i32(x), f64(x), etc.
// ---------------------------------------------------------------------------

cast_target_ir_type :: proc(name: string) -> (ir_type: string, is_float: bool, is_ptr: bool, ok: bool) {
    switch name {
    case "int", "i64":  return "i64", false, false, true
    case "uint", "u64": return "i64", false, false, true
    case "i128":        return "i128", false, false, true
    case "u128":        return "i128", false, false, true
    case "i32":         return "i32", false, false, true
    case "i16":         return "i16", false, false, true
    case "i8", "utf8": return "i8", false, false, true
    case "u32":         return "i32", false, false, true
    case "u16":         return "i16", false, false, true
    case "u8":          return "i8", false, false, true
    case "usize", "isize":
        // Word-sized: same flag the codegen uses for llvm_type_from_checker.
        return "i32" if word_size_is_32 else "i64", false, false, true
    case "f64":         return "double", true, false, true
    case "f32":         return "float", true, false, true
    case "f16":         return "half", true, false, true
    case "bool":        return "i1", false, false, true
    }
    return "", false, false, false
}

ir_type_bits :: proc(t: string) -> int {
    switch t {
    case "i1":     return 1
    case "i8":     return 8
    case "i16":    return 16
    case "i32":    return 32
    case "i64":    return 64
    case "i128":   return 128
    case "half":   return 16
    case "float":  return 32
    case "double": return 64
    }
    return 0
}

is_ir_float :: proc(t: string) -> bool {
    return t == "half" || t == "float" || t == "double"
}

// ---------------------------------------------------------------------------
// Function call codegen
// ---------------------------------------------------------------------------

// cstring(s) — VALIDITY, not content: a 0 must exist inside the slice's
// storage so C can never run past it. len < cap: the byte at [len] must be 0;
// len == cap: the LAST byte [cap-1] must be 0 (and cap > 0). No terminator: a
// loud crash with the location. The data pointer, checked.
emit_cstring_check :: proc(g: ^Codegen, len_val, cap_val, src_ptr: string, span: Span) -> string {
    w := slice_layout.len_ir
    at_len_lbl  := fresh_label(g, "cstring.at_len")
    at_end_lbl  := fresh_label(g, "cstring.at_end")
    end_ok_lbl  := fresh_label(g, "cstring.end_ok")
    pass_lbl    := fresh_label(g, "cstring.pass")
    crash_lbl   := fresh_label(g, "cstring.fail")
    has_room := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", has_room, w, len_val, cap_val)
    emit_cond_br(g, has_room, at_len_lbl, at_end_lbl)
    // len < cap: terminator sits right after the content.
    emit_label(g, at_len_lbl)
    p1 := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", p1, src_ptr, w, len_val)
    b1 := fresh_tmp(g)
    emit_load_into(g, b1, "i8", p1)
    ok1 := fresh_tmp(g)
    emit(g, "  %s = icmp eq i8 %s, 0", ok1, b1)
    emit_cond_br(g, ok1, pass_lbl, crash_lbl)
    // len == cap: full view — the last byte must be 0 (and cap > 0 so
    // the [cap-1] read stays inside the storage).
    emit_label(g, at_end_lbl)
    cap_pos := fresh_tmp(g)
    emit(g, "  %s = icmp sgt %s %s, 0", cap_pos, w, cap_val)
    emit_cond_br(g, cap_pos, end_ok_lbl, crash_lbl)
    emit_label(g, end_ok_lbl)
    last := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, 1", last, w, cap_val)
    p2 := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", p2, src_ptr, w, last)
    b2 := fresh_tmp(g)
    emit_load_into(g, b2, "i8", p2)
    ok2 := fresh_tmp(g)
    emit(g, "  %s = icmp eq i8 %s, 0", ok2, b2)
    emit_cond_br(g, ok2, pass_lbl, crash_lbl)
    emit_label(g, crash_lbl)
    loc := format_location(span.file, span.line, span.col)
    err_msg := fmt.tprintf("runtime error: cstring() at %s: no terminating 0 in the slice (checked [len] since len < cap, or [cap-1] for a full slice) — append into headroom or zero-pad the buffer\n", loc)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", err_ptr)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, pass_lbl)
    return src_ptr
}

// (Terminate-in-place cstring conversion used to live here. It's gone: the
// explicit `cstring(s)` builtin copies into a fresh buffer instead, and the
// checker rejects implicit runtime-string → cstring arguments, so codegen
// never converts implicitly. Literals reach cstring params as raw rodata
// pointers via gen_expr's Expr_String handling.)

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
         Type_Numeric, ^Type_Enum, Type_Err:
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
emit_crash :: proc(g: ^Codegen, span: Span, msg: string) {
    emit_crash_journal_begin(g)

    // Location line, same family as the assert message.
    loc := format_location(span.file, span.line, span.col)
    esc_loc, _ := strings.replace_all(loc, "%", "%%", context.temp_allocator)
    loc_global, _ := get_string_literal(g, strings.concatenate({"Crashed at ", esc_loc, "\n"}, context.temp_allocator))
    emit(g, "  call i32 (ptr, ...) %s(ptr %s)", printf_sym(g), loc_global)
    if msg != "" {
        emit_printf_ptr(g, emit_fmt_ptr(g, "%s"), msg)
        emit_print_newline(g)
    }
    emit_crash_journal_end(g)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
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
    val:     string,   // a register value; text's bytes' address
    addr:    string,   // an aggregate's address
    t:       Type,
}

emit_print_operand :: proc(g: ^Codegen, v: Print_Arg) {
    switch {
    case v.is_text:   emit_print_text_at(g, v.val, len(v.text))
    case v.addr != "": emit_print_at_addr(g, v.addr, v.t)
    case:             emit_print_value(g, v.val, v.t)
    }
}

// print_cstr, print_int, print_float: the printf spec each prints its value
// with, and the value's IR type.
raw_print :: proc(name: string) -> (spec, ir: string, ok: bool) {
    switch name {
    case "print_cstr":  return "%s", "ptr", true
    case "print_int":   return "%lld", "i64", true
    case "print_float": return "%g", "double", true
    }
    return
}

emit_print_raw :: proc(g: ^Codegen, spec, ir, val: string) {
    emit(g, "  call i32 (ptr, ...) %s(ptr %s, %s %s)", printf_sym(g), emit_fmt_ptr(g, spec), ir, val)
}

// Text of `n` bytes at `data`, printed.
emit_print_text_at :: proc(g: ^Codegen, data: string, n: int) {
    h := Array_Handle{fixed_alloca = data, elem_type = "i8", static_cap = n, is_utf8 = true}
    emit_array_print(g, &h)
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
    str_name, str_len := get_string_literal(g, s)
    str_ptr := fresh_tmp(g)
    emit_string_gep(g, str_ptr, str_len, str_name)
    fmt_name, fmt_len := get_string_literal(g, "%s")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    emit_printf_ptr(g, fmt_ptr, str_ptr)
}

emit_print_newline :: proc(g: ^Codegen) {
    nl_name, nl_len := get_string_literal(g, "\n")
    nl_ptr := fresh_tmp(g)
    emit_string_gep(g, nl_ptr, nl_len, nl_name)
    emit_printf_void(g, nl_ptr)
}

// Print an i1 as `true`/`false`. Shared by scalar args, struct fields, and
// array elements so bool renders consistently everywhere — and never reaches
// an integer printf format, which would either mistype the i1 (scalar: i1 in
// an i64 vararg slot → invalid IR) or sext it to a garbage value (array: true
// → -1).
gen_print_bool :: proc(g: ^Codegen, val_i1: string) {
    true_name, true_len := get_string_literal(g, "true")
    false_name, false_len := get_string_literal(g, "false")
    true_ptr := fresh_tmp(g)
    emit_string_gep(g, true_ptr, true_len, true_name)
    false_ptr := fresh_tmp(g)
    emit_string_gep(g, false_ptr, false_len, false_name)
    bool_str := fresh_tmp(g)
    emit(g, "  %s = select i1 %s, ptr %s, ptr %s", bool_str, val_i1, true_ptr, false_ptr)
    fmt_name, fmt_len := get_string_literal(g, "%s")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    emit_printf_ptr(g, fmt_ptr, bool_str)
}

// Print a struct as: StructName { field1: val1, field2: val2 }
// Build a printf format-string pointer for `spec` — folds the get_string_literal
// + GEP pair that every print site otherwise repeats by hand.
emit_fmt_ptr :: proc(g: ^Codegen, spec: string) -> string {
    name, n := get_string_literal(g, spec)
    p := fresh_tmp(g)
    emit_string_gep(g, p, n, name)
    return p
}

// Print an already-loaded scalar VALUE given its Mara type — the single source
// of truth for how a scalar renders: print's own arguments, struct fields and
// array elements all route through here, so they match a bare `print(x)`:
// chars as glyphs, sign-aware integers, %g floats. Non-scalars (a nested struct/array field reaching here) hard-error rather than
// mis-emit — aggregates are handled by their own recursion before this is called.
emit_print_value :: proc(g: ^Codegen, val: string, ty: Type) {
    if ty == nil { codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, "<unknown>") }
    bt := distinct_base(ty)

    if _, ok := bt.(Type_Bool); ok { gen_print_bool(g, val); return }
    if _, ok := bt.(Type_Utf8); ok {
        // utf8 scalar = a character: render the glyph, not the code point.
        ext := fresh_tmp(g)
        emit(g, "  %s = zext i8 %s to i32", ext, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, "%c"), ext)
        return
    }
    if et, ok := bt.(^Type_Enum); ok {
        tag_ir := et.tag_type != "" ? tag_type_to_ir(et.tag_type) : "i64"
        gen_print_enum(g, val, tag_ir, et)
        return
    }
    if _, ok := bt.(Type_Err); ok {
        emit(g, "  call void @__mara_print_err(i32 %s)", val)
        return
    }
    if pt, ok := bt.(^Type_Ptr); ok {
        spec := "%p"
        if _, b := pt.elem.(Type_Byte); b { spec = "%s" }
        if _, u := pt.elem.(Type_Utf8); u { spec = "%s" }
        emit_printf_ptr(g, emit_fmt_ptr(g, spec), val)
        return
    }
    if _, ok := bt.(Type_CString); ok {
        emit_printf_ptr(g, emit_fmt_ptr(g, "%s"), val)
        return
    }

    // Numeric (integers + floats): IR-width driven with sign awareness.
    is_unsigned := false
    if n, ok := bt.(Type_Numeric); ok { is_unsigned = n.kind == .Unsigned }
    if _, ok := bt.(Type_Byte); ok { is_unsigned = true }
    nt := llvm_type_from_checker(ty)
    switch nt {
    case "double":
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), val)
    case "float":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext float %s to double", ext, val)
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), ext)
    case "half":
        ext := fresh_tmp(g)
        emit(g, "  %s = fpext half %s to double", ext, val)
        emit_printf_double(g, emit_fmt_ptr(g, "%g"), ext)
    case "i64":
        emit_printf_i64(g, emit_fmt_ptr(g, is_unsigned ? "%llu" : "%lld"), val)
    case "i32":
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, is_unsigned ? "%u" : "%d"), val)
    case "i1":
        gen_print_bool(g, val)
    case "i8", "i16":
        // C varargs promote sub-int integers to int (i32).
        ext := fresh_tmp(g)
        emit(g, "  %s = %s %s %s to i32", ext, is_unsigned ? "zext" : "sext", nt, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), emit_fmt_ptr(g, is_unsigned ? "%u" : "%d"), ext)
    case:
        codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, type_name(ty))
    }
}

// Print whatever lives at `addr` given its Mara type — the recursive core of
// aggregate printing. Scalars load + emit_print_value; structs and fixed arrays
// recurse. This is what lets struct fields and array elements render like a bare
// print at any nesting depth (struct-in-struct, array-of-structs, ...).
emit_print_at_addr :: proc(g: ^Codegen, addr: string, ty: Type) {
    if sd := as_struct_body(distinct_base(ty)); sd != nil {
        if print_st, ok := lookup_struct(g, sd.name); ok {
            sv := Struct_Var{alloca = addr, struct_name = sd.name}
            gen_print_struct(g, &sv, print_st)
        }
        return
    }
    bt := distinct_base(ty)

    // A utf8 array (fixed / slice / partial) is a string — print it as bounded
    // text (%.*s) like a bare print(string), not element-by-element. Fixed
    // storage anchors the handle at the data; slice/PA anchor at the {len,cap,ptr}
    // header sitting at this address (same shapes resolve_array_handle builds).
    #partial switch t in bt {
    case ^Type_Fixed_Array:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{fixed_alloca = addr, elem_type = "i8", static_cap = t.size, is_utf8 = true}
            emit_array_print(g, &h)
            return
        }
    case ^Type_Slice:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{header_ptr = addr, elem_type = "i8", is_utf8 = true}
            emit_array_print(g, &h)
        } else {
            h := Array_Handle{header_ptr = addr, elem_type = llvm_type_from_checker(t.elem)}
            gen_print_array_handle(g, &h, t.elem)
        }
        return
    case ^Type_Partial_Array:
        if _, u := distinct_base(t.elem).(Type_Utf8); u {
            h := Array_Handle{header_ptr = addr, elem_type = "i8", is_utf8 = true}
            emit_array_print(g, &h)
        } else {
            h := Array_Handle{header_ptr = addr, elem_type = llvm_type_from_checker(t.elem)}
            gen_print_array_handle(g, &h, t.elem)
        }
        return
    }

    // Non-utf8 fixed array → recurse per element (flat or nested rows).
    if fa, ok := bt.(^Type_Fixed_Array); ok {
        elem_ir := llvm_type_from_checker(fa.elem)
        if _, nested := distinct_base(fa.elem).(^Type_Fixed_Array); nested {
            gen_print_nested_array(g, addr, fa.size, elem_ir, fa.elem)
        } else {
            gen_print_array_inline(g, addr, fa.size, elem_ir, fa.elem)
        }
        return
    }

    // Scalar — load at its IR width and route through the value printer.
    val := fresh_tmp(g)
    emit_load_into(g, val, llvm_type_from_checker(ty), addr)
    emit_print_value(g, val, ty)
}

gen_print_struct :: proc(g: ^Codegen, stv: ^Struct_Var, st: ^Scope_Body) {
    st_llvm := struct_llvm_name(struct_key(st))
    // Print "StructName { "
    header_name, header_len := get_string_literal(g, fmt.tprintf("%s {{ ", struct_key(st)))
    header_ptr := fresh_tmp(g)
    emit_string_gep(g, header_ptr, header_len, header_name)
    emit_printf_void(g, header_ptr)

    for &f, fi in st.fields {
        if fi > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        // Print "fieldname: "
        label_name, label_len := get_string_literal(g, fmt.tprintf("%s: ", f.name))
        label_ptr := fresh_tmp(g)
        emit_string_gep(g, label_ptr, label_len, label_name)
        emit_printf_void(g, label_ptr)

        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, stv.alloca, fi)
        // One field, by its Mara type — scalar, nested struct, or array, each
        // rendered identically to a bare print(field).
        emit_print_at_addr(g, gep, f.type_)
    }

    // Print " }"
    close_name, close_len := get_string_literal(g, " }")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Inline switch that prints the variant name matching `val`, or
// "EnumName(<tag>)" when nothing matches (e.g. flag-combo, out-of-range raw
// tag). Variants are sorted by value for stable IR; same-value aliases keep
// the first in name order — LLVM's switch requires unique case values, so
// duplicates are folded into one case.
gen_print_enum :: proc(g: ^Codegen, val: string, tag_ir: string, et: ^Type_Enum) {
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
    case_labels := make([]string, len(dedup), context.temp_allocator)
    for _, i in dedup {
        case_labels[i] = fresh_label(g, "enum.case")
    }

    sw: strings.Builder
    strings.write_string(&sw, fmt.tprintf("  switch %s %s, label %%%s [\n", tag_ir, val, unknown_lbl))
    for entry, i in dedup {
        strings.write_string(&sw, fmt.tprintf("    %s %d, label %%%s\n", tag_ir, entry.value, case_labels[i]))
    }
    strings.write_string(&sw, "  ]")
    emit_raw(g, strings.to_string(sw))

    // error_kinds print namespaced (`File_Error.Not_Found`) so the variant
    // name alone — which can collide across sets — stays unambiguous in logs.
    // Regular enums print just the variant for compactness (Tag_u8.B -> "B").
    name_prefix := ""
    if et.is_error_kind {
        prefix_name := et.source_name
        if prefix_name == "" { prefix_name = et.name }
        name_prefix = strings.concatenate({prefix_name, "."}, context.temp_allocator)
    }

    for entry, i in dedup {
        emit_label(g, case_labels[i])
        emit_print_literal(g, strings.concatenate({name_prefix, entry.name}, context.temp_allocator))
        emit_br(g, done_lbl)
    }

    emit_label(g, unknown_lbl)
    emit_print_literal(g, fmt.tprintf("%s(", et.source_name if et.source_name != "" else et.name))
    fmt_name, fmt_len := get_string_literal(g, tag_ir == "i64" ? "%lld" : "%d")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    switch tag_ir {
    case "i64":
        emit_printf_i64(g, fmt_ptr, val)
    case "i32":
        // Already at printf's default-int width — pass through.
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), fmt_ptr, val)
    case:
        // i16 / i8: zext to i32 for printf's default-int varargs promotion.
        // zext (not sext) — enum tags are unsigned-shaped values, no two's-
        // complement bits to preserve.
        ext := fresh_tmp(g)
        emit(g, "  %s = zext %s %s to i32", ext, tag_ir, val)
        emit(g, "  call i32 (ptr, ...) %s(ptr %s, i32 %s)", printf_sym(g), fmt_ptr, ext)
    }
    emit_print_literal(g, ")")
    emit_br(g, done_lbl)

    emit_label(g, done_lbl)
}

// Print a flat array inline: [v1, v2, v3]
gen_print_array_inline :: proc(g: ^Codegen, data_ptr: string, cap: int, elem_type: string, elem_ty: Type) {
    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    arr_type := fmt.tprintf("[%d x %s]", cap, elem_type)
    for i := 0; i < cap; i += 1 {
        if i > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        gep := fresh_tmp(g)
        emit_array_gep_const(g, gep, arr_type, data_ptr, i)
        emit_print_at_addr(g, gep, elem_ty)
    }

    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print a nested array like [4][4]f32 as: [[v, v, v, v], [v, v, v, v], ...]
gen_print_nested_array :: proc(g: ^Codegen, data_ptr: string, outer_cap: int, inner_ir_type: string, row_ty: Type) {
    inner_cap, inner_elem, _ := parse_array_ir_type(inner_ir_type)
    outer_arr_type := fmt.tprintf("[%d x %s]", outer_cap, inner_ir_type)
    // row_ty is the inner row's Mara type (e.g. [M]T); its element type drives
    // each scalar's sign-aware / char-aware rendering.
    inner_elem_ty: Type = nil
    if fa, ok := distinct_base(row_ty).(^Type_Fixed_Array); ok { inner_elem_ty = fa.elem }

    open_name, open_len := get_string_literal(g, "[")
    open_ptr := fresh_tmp(g)
    emit_string_gep(g, open_ptr, open_len, open_name)
    emit_printf_void(g, open_ptr)

    for i := 0; i < outer_cap; i += 1 {
        if i > 0 {
            sep_name, sep_len := get_string_literal(g, ", ")
            sep_ptr := fresh_tmp(g)
            emit_string_gep(g, sep_ptr, sep_len, sep_name)
            emit_printf_void(g, sep_ptr)
        }
        row_gep := fresh_tmp(g)
        emit_array_gep_const(g, row_gep, outer_arr_type, data_ptr, i)
        gen_print_array_inline(g, row_gep, inner_cap, inner_elem, inner_elem_ty)
    }

    close_name, close_len := get_string_literal(g, "]")
    close_ptr := fresh_tmp(g)
    emit_string_gep(g, close_ptr, close_len, close_name)
    emit_printf_void(g, close_ptr)
}

// Print a slice / partial array as [e0, e1, ...] bounded by its RUNTIME length.
// Works off an Array_Handle (header carries len + data ptr); each element
// recurses through emit_print_at_addr so element structs / nested arrays render
// too. Fixed arrays use the compile-time gen_print_array_inline instead.
gen_print_array_handle :: proc(g: ^Codegen, h: ^Array_Handle, elem_ty: Type) {
    emit_printf_void(g, emit_fmt_ptr(g, "["))
    data := emit_array_data(g, h)
    n := emit_array_len(g, h)
    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(elem_ty)

    idx_ptr := fresh_tmp(g)
    emit_alloca(g, idx_ptr, w)
    emit_store(g, w, "0", idx_ptr)
    cond_l := fresh_label(g, "pah.cond")
    body_l := fresh_label(g, "pah.body")
    end_l  := fresh_label(g, "pah.end")
    emit_br(g, cond_l)

    emit_label(g, cond_l)
    i := fresh_tmp(g)
    emit_load_into(g, i, w, idx_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", cmp, w, i, n)
    emit_cond_br(g, cmp, body_l, end_l)

    emit_label(g, body_l)
    i2 := fresh_tmp(g)
    emit_load_into(g, i2, w, idx_ptr)
    sep_l   := fresh_label(g, "pah.sep")
    nosep_l := fresh_label(g, "pah.nosep")
    after_l := fresh_label(g, "pah.after")
    is_first := fresh_tmp(g)
    emit(g, "  %s = icmp eq %s %s, 0", is_first, w, i2)
    emit_cond_br(g, is_first, nosep_l, sep_l)
    emit_label(g, sep_l)
    emit_printf_void(g, emit_fmt_ptr(g, ", "))
    emit_br(g, after_l)
    emit_label(g, nosep_l)
    emit_br(g, after_l)
    emit_label(g, after_l)
    elem_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, %s %s", elem_gep, elem_ir, data, w, i2)
    emit_print_at_addr(g, elem_gep, elem_ty)
    nxt := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", nxt, w, i2)
    emit_store(g, w, nxt, idx_ptr)
    emit_br(g, cond_l)

    emit_label(g, end_l)
    emit_printf_void(g, emit_fmt_ptr(g, "]"))
}
