package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// What the program says: print's lowering (a value of any type, as text),
// assert's and crash's messages, the runtime checks' — and number literals.
// ---------------------------------------------------------------------------

// Lower a numeric literal to an LLVM constant for the given IR target type.
// Floats use the exact IEEE-754 hex bit-pattern (`0x…`) — a decimal print (`%f`)
// defaults to 3 fractional digits in Odin and silently truncates the value
// (3.14159… -> 3.142); hex is exact and is how clang itself writes floats.
// Integers use the exact i128 form (a value as f64 loses precision above
// 2^53).
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
    loc := span_location(span)
    // Embedded source text must not smuggle conversion specs into the
    // format string (`a % b == 0`), so escape every %.
    esc_cond, _ := strings.replace_all(cond_text, "%", "%%", context.temp_allocator)
    msg := strings.builder_make(context.temp_allocator)
    args := make([dynamic]string, context.temp_allocator)
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
            tag_ir := llvm_type_from_checker(et)
            v := side.val
            if ir_type != tag_ir {
                w := fresh_tmp(g)
                op := ir_type_bits(ir_type) > ir_type_bits(tag_ir) ? "trunc" : "zext"
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
            ir_select(g, sel, side.val, "ptr", t_global, f_global)
            append(&args, fmt.tprintf("ptr %s", sel))
        case is_float:
            if ir_type != "double" {
                v = fresh_tmp(g)
                ir_cast(g, v, "fpext", ir_type, side.val, "double")
            }
            append(&args, fmt.tprintf("double %s", v))
        case is_char:
            // %c reads an i32 vararg (default promotion).
            if ir_type != "i32" {
                v = fresh_tmp(g)
                ir_cast(g, v, ir_type == "i64" ? "trunc" : "zext", ir_type, side.val, "i32")
            }
            append(&args, fmt.tprintf("i32 %s", v))
        case:
            if ir_type != "i64" {
                v = fresh_tmp(g)
                ir_cast(g, v, is_unsigned ? "zext" : "sext", ir_type, side.val, "i64")
            }
            append(&args, fmt.tprintf("i64 %s", v))
        }
    }
    strings.write_string(&msg, "\n")
    assert_flush_printf(g, &msg, &args)
    emit_crash_journal_end(g)
    ir_call(g, "", "void", "@exit", "i32 1")
    ir_unreachable(g)
}

// Emit the pending assert-message segment as one printf and reset the
// builders. Segmented because enum sides print through gen_print_enum's
// inline switch, which does its own printf calls mid-message.
assert_flush_printf :: proc(g: ^Codegen, msg: ^strings.Builder, args: ^[dynamic]string) {
    if strings.builder_len(msg^) == 0 { return }
    msg_global := get_string_literal(g, strings.to_string(msg^))
    all := make([dynamic]string, 0, len(args) + 1, context.temp_allocator)
    append(&all, fmt.tprintf("ptr %s", msg_global))
    append(&all, ..args[:])
    ir_call_va(g, "", "i32", "(ptr, ...)", printf_sym(g), ..all[:])
    strings.builder_reset(msg)
    clear(args)
}

// Open/close a crash.txt journal entry around a fail block's message
// emission (native builds only; web has no filesystem). Between the two,
// g.tee routes every print-shaped emission through __mara_tee_printf so the
// message lands in the journal as well as on stdout.
emit_crash_journal_begin :: proc(g: ^Codegen) {
    if g.web { return }
    ir_call(g, "", "void", "@__mara_crash_begin")
    g.tee = true
}

emit_crash_journal_end :: proc(g: ^Codegen) {
    if g.web { return }
    g.tee = false
    ir_call(g, "", "void", "@__mara_crash_end")
}

// A runtime failure: the journal opens, the message prints — `message`, a C
// format, and its `args`, each "<IR type> <value>" — and the program exits.
// Nothing runs after it.
emit_fail :: proc(g: ^Codegen, message: string, args: ..string) {
    emit_crash_journal_begin(g)
    all := make([dynamic]string, 0, len(args) + 1, context.temp_allocator)
    append(&all, fmt.tprintf("ptr %s", get_string_literal(g, message)))
    append(&all, ..args)
    ir_call_va(g, "", "i32", "(ptr, ...)", printf_sym(g), ..all[:])
    emit_crash_journal_end(g)
    ir_call(g, "", "void", "@exit", "i32 1")
    ir_unreachable(g)
}

// A value at slice header width (SLICE_LEN_IR), as emit_fail's argument.
fail_i64 :: proc(v: string) -> string {
    return fmt.tprintf("i64 %s", v)
}

// ---------------------------------------------------------------------------
// Type cast codegen: i32(x), f64(x), etc.
// ---------------------------------------------------------------------------

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
    w := SLICE_LEN_IR
    at_len_lbl  := fresh_label(g, "cstring.at_len")
    at_end_lbl  := fresh_label(g, "cstring.at_end")
    end_ok_lbl  := fresh_label(g, "cstring.end_ok")
    pass_lbl    := fresh_label(g, "cstring.pass")
    crash_lbl   := fresh_label(g, "cstring.fail")
    has_room := fresh_tmp(g)
    ir_icmp(g, has_room, "slt", w, len_val, cap_val)
    emit_cond_br(g, has_room, at_len_lbl, at_end_lbl)
    // len < cap: terminator sits right after the content.
    emit_label(g, at_len_lbl)
    p1 := fresh_tmp(g)
    emit_elem_gep(g, p1, "i8", src_ptr, len_val, w)
    b1 := fresh_tmp(g)
    emit_load_into(g, b1, "i8", p1)
    ok1 := fresh_tmp(g)
    ir_icmp(g, ok1, "eq", "i8", b1, "0")
    emit_cond_br(g, ok1, pass_lbl, crash_lbl)
    // len == cap: full view — the last byte must be 0 (and cap > 0 so
    // the [cap-1] read stays inside the storage).
    emit_label(g, at_end_lbl)
    cap_pos := fresh_tmp(g)
    ir_icmp(g, cap_pos, "sgt", w, cap_val, "0")
    emit_cond_br(g, cap_pos, end_ok_lbl, crash_lbl)
    emit_label(g, end_ok_lbl)
    last := fresh_tmp(g)
    ir_bin(g, last, "sub", w, cap_val, "1")
    p2 := fresh_tmp(g)
    emit_elem_gep(g, p2, "i8", src_ptr, last, w)
    b2 := fresh_tmp(g)
    emit_load_into(g, b2, "i8", p2)
    ok2 := fresh_tmp(g)
    ir_icmp(g, ok2, "eq", "i8", b2, "0")
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
    // (The location line, as an assert's.)
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    if msg != "" {
        emit_fail(g, fmt.tprintf("Crashed at %s\n%%s\n", loc), fmt.tprintf("ptr %s", msg))
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
    val:     string,   // a register value; text's bytes' address
    addr:    string,   // an aggregate's address
    t:       Type,
}

emit_print_operand :: proc(g: ^Codegen, v: Print_Arg) {
    switch {
    case v.is_text:   emit_print_text(g, v.val, fmt.tprintf("%d", len(v.text)))
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

// Text of `n` bytes (at slice header width) at `data`, printed: bounded, so
// it needs no terminating 0. (`%.*s` takes an int: n, narrowed.)
emit_print_text :: proc(g: ^Codegen, data, n: string) {
    prec := fresh_tmp(g)
    ir_cast(g, prec, "trunc", SLICE_LEN_IR, n, "i32")
    emit_printf(g, "%.*s", fmt.tprintf("i32 %s", prec), fmt.tprintf("ptr %s", data))
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
    emit_printf(g, "%s", fmt.tprintf("ptr %s", get_string_literal(g, s)))
}

emit_print_newline :: proc(g: ^Codegen) {
    emit_printf(g, "\n")
}

// Print an i1 as `true`/`false`. Shared by scalar args, struct fields, and
// array elements so bool renders consistently everywhere — and never reaches
// an integer printf format, which would either mistype the i1 (scalar: i1 in
// an i64 vararg slot → invalid IR) or sext it to a garbage value (array: true
// → -1).
gen_print_bool :: proc(g: ^Codegen, val_i1: string) {
    true_ptr := get_string_literal(g, "true")
    false_ptr := get_string_literal(g, "false")
    bool_str := fresh_tmp(g)
    ir_select(g, bool_str, val_i1, "ptr", true_ptr, false_ptr)
    emit_printf(g, "%s", fmt.tprintf("ptr %s", bool_str))
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
        ir_cast(g, ext, "zext", "i8", val, "i32")
        emit_printf(g, "%c", fmt.tprintf("i32 %s", ext))
        return
    }
    if et, ok := bt.(^Type_Enum); ok {
        gen_print_enum(g, val, llvm_type_from_checker(et), et, label = print_type_label(ty))
        return
    }
    if _, ok := bt.(Type_Err); ok {
        ir_call(g, "", "void", "@__mara_print_err", fmt.tprintf("i32 %s", val))
        return
    }
    if pt, ok := bt.(^Type_Ptr); ok {
        spec := "%p"
        if _, b := pt.elem.(Type_Byte); b { spec = "%s" }
        if _, u := pt.elem.(Type_Utf8); u { spec = "%s" }
        emit_printf(g, spec, fmt.tprintf("ptr %s", val))
        return
    }
    if _, ok := bt.(Type_CString); ok {
        emit_printf(g, "%s", fmt.tprintf("ptr %s", val))
        return
    }

    // Numeric (integers + floats): IR-width driven with sign awareness. (A
    // float prints as a double, an integer under 32 bits as an int: C's
    // varargs promote them.)
    is_unsigned := llvm_unsigned(ty)
    nt := llvm_type_from_checker(ty)
    switch nt {
    case "double":
        emit_printf(g, "%g", fmt.tprintf("double %s", val))
    case "float", "half":
        ext := fresh_tmp(g)
        ir_cast(g, ext, "fpext", nt, val, "double")
        emit_printf(g, "%g", fmt.tprintf("double %s", ext))
    case "i64":
        emit_printf(g, is_unsigned ? "%llu" : "%lld", fmt.tprintf("i64 %s", val))
    case "i32":
        emit_printf(g, is_unsigned ? "%u" : "%d", fmt.tprintf("i32 %s", val))
    case "i1":
        gen_print_bool(g, val)
    case "i8", "i16":
        ext := fresh_tmp(g)
        ir_cast(g, ext, is_unsigned ? "zext" : "sext", nt, val, "i32")
        emit_printf(g, is_unsigned ? "%u" : "%d", fmt.tprintf("i32 %s", ext))
    case:
        codegen_fatal(g, {}, CODE_PRINT_UNSUPPORTED_VALUE, type_name(ty))
    }
}

// Print whatever lives at `addr` given its Mara type — the recursive core of
// aggregate printing. Scalars load + emit_print_value; structs and fixed arrays
// recurse. This is what lets struct fields and array elements render like a bare
// print at any nesting depth (struct-in-struct, array-of-structs, ...).
emit_print_at_addr :: proc(g: ^Codegen, addr: string, ty: Type) {
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
            emit_print_text(g, addr, fmt.tprintf("%d", fa.size))
        } else {
            gen_print_array_inline(g, addr, fa.size, fa.elem)
        }
        return
    }
    if elem := llvm_header_elem(bt); elem != nil {
        data := emit_header_field(g, addr, SLICE.ptr)
        n := emit_header_field(g, addr, SLICE.len)
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
gen_print_struct :: proc(g: ^Codegen, addr: string, st: ^Scope_Body, name := "") {
    say :: proc(g: ^Codegen, text: string) { emit_printf(g, text) }
    st_llvm := struct_llvm_name(st.name)
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
gen_print_union :: proc(g: ^Codegen, addr: string, ut: ^Type_Union, label := "") {
    tag_ir := union_tag_ir_type(ut)
    tag := load_union_tag(g, ut, addr)
    unknown, done := fresh_label(g, "union.unknown"), fresh_label(g, "union.done")
    arms := make([]string, len(ut.variants), context.temp_allocator)
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
gen_print_enum :: proc(g: ^Codegen, val: string, tag_ir: string, et: ^Type_Enum, named := true, label := "") {
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
    case_labels := make([]string, len(dedup), context.temp_allocator)
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
    case "i64":
        emit_printf(g, "%lld", fmt.tprintf("i64 %s", val))
    case "i32":
        emit_printf(g, "%d", fmt.tprintf("i32 %s", val))
    case:
        // i16 / i8: zext to i32 for printf's default-int varargs promotion.
        // zext (not sext) — enum tags are unsigned-shaped values, no two's-
        // complement bits to preserve.
        ext := fresh_tmp(g)
        ir_cast(g, ext, "zext", tag_ir, val, "i32")
        emit_printf(g, "%d", fmt.tprintf("i32 %s", ext))
    }
    emit_print_literal(g, ")")
    emit_br(g, done_lbl)

    emit_label(g, done_lbl)
}

// A fixed array's `size` elements at `data`, printed: [v1, v2, v3] (an
// element an array, as its own — [[1, 2], [3, 4]]).
gen_print_array_inline :: proc(g: ^Codegen, data: string, size: int, elem: Type) {
    emit_printf(g, "[")
    arr_type := fmt.tprintf("[%d x %s]", size, llvm_type_from_checker(elem))
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
gen_print_elements :: proc(g: ^Codegen, data, n: string, elem: Type) {
    emit_printf(g, "[")
    l := emit_loop_begin(g, n, "pah")
    sep, after := fresh_label(g, "pah.sep"), fresh_label(g, "pah.after")
    first := fresh_tmp(g)
    ir_icmp(g, first, "eq", SLICE_LEN_IR, l.i, "0")
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
