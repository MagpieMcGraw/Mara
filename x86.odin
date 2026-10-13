package mara

import "base:runtime"
import "core:fmt"
import "core:mem/virtual"
import "core:os"
import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// The x86-64 backend (Windows). A module's low-level IR — what llvm.odin and
// the emit helpers write for it: the LLVM subset with no phi, ~40
// instructions (loads, stores, address arithmetic, integer and float
// operations, conversions, calls, branches) and a few intrinsics — read and
// encoded as x86-64 machine code into a COFF object, which lld links. It
// decides nothing about the program: every check, layout and conversion is in
// the IR already; what's here is how each instruction is done on the machine.
//
// Every value has a slot in its function's frame; an instruction loads what
// it uses into registers, does its work and stores its result. An address in
// a local's memory at a constant offset is no value at all, but the memory
// its loads and stores name. Calls follow the Win64 convention, Mara's and
// C's alike; each function has unwind info (.pdata, .xdata) and one epilogue
// its returns jump to.
// ---------------------------------------------------------------------------

// A type's layout, as the IR's types lay out on x86-64.
X86_Kind :: enum u8 { Void, Int, F16, F32, F64, Ptr, Array, Struct }

X86_Type :: struct {
    kind:    X86_Kind,
    bits:    int,           // an int's width
    size:    int,
    align:   int,
    elem:    ^X86_Type,     // an array's
    count:   int,
    fields:  []^X86_Type,   // a struct's, at its offsets
    offsets: []int,
}

// The object's sections, in its section table's order.
@(private="file")
X86_Sec :: enum u8 { Text, Data, Bss, Rdata, Pdata, Xdata, Drectve }

@(private="file") X86_SEC_NAME := [X86_Sec]string{.Text = ".text", .Data = ".data", .Bss = ".bss", .Rdata = ".rdata", .Pdata = ".pdata", .Xdata = ".xdata", .Drectve = ".drectve"}
@(private="file") X86_SEC_FLAGS := [X86_Sec]u32{
    .Text    = 0x60500020,   // code, 16-aligned, execute, read
    .Data    = 0xC0500040,   // initialized data, 16-aligned, read, write
    .Bss     = 0xC0500080,   // uninitialized data, 16-aligned, read, write
    .Rdata   = 0x40500040,   // initialized data, 16-aligned, read
    .Pdata   = 0x40300040,   // ... 4-aligned
    .Xdata   = 0x40300040,
    .Drectve = 0x00100A00,   // linker directives, removed from the image
}

// IMAGE_REL_AMD64_*: an address, an address from the image's start, an
// address from the end of the 4 bytes it's in.
@(private="file") X86_ADDR64   :: 1
@(private="file") X86_ADDR32NB :: 3
@(private="file") X86_REL32    :: 4

@(private="file")
X86_Reloc :: struct {
    at:   u32,   // where, in its section (a function's body: in the body)
    sym:  u32,   // the symbol it names (X86_Module.syms)
    kind: u16,
}

@(private="file")
X86_Sym :: struct {
    name:    string,
    sec:     int,    // its section's number (X86_Sec + 1); 0, another object's
    value:   u32,    // its offset in its section
    global:  bool,
    fn:      bool,
    section: bool,   // a section's own symbol
}

// The program's types: every module's IR names the same ones, laid out once.
X86_Program :: struct {
    keep:  runtime.Allocator,
    named: map[string]string,       // %class.X → its body's text
    types: map[string]^X86_Type,    // a type's text → its layout
    i1, i8, i16, i32, i64, ptr, f32, f64, void: ^X86_Type,   // (the common ones, without a lookup)
}

// One module's translation: its object.
@(private="file")
X86_Module :: struct {
    p:       ^X86_Program,
    keep:    runtime.Allocator,      // (what outlives one function)
    sec:     [X86_Sec][dynamic]u8,
    relocs:  [X86_Sec][dynamic]X86_Reloc,
    bss:     int,                    // .bss's size
    syms:    [dynamic]X86_Sym,
    sym_of:  map[string]u32,
    exports: [dynamic]string,        // dllexport functions
}

// A value: a local (an instruction's result, a param, an alloca's address),
// a global's address, a number (a float's bits), or zero.
@(private="file")
X86_Val_Kind :: enum u8 { Zero, Int, Local, Global }

@(private="file")
X86_Val :: struct {
    kind: X86_Val_Kind,
    n:    i64,
    name: string,
}

@(private="file")
X86_Arg :: struct {
    t: ^X86_Type,
    v: X86_Val,
}

// A local's slot: where a value is kept — or memory, its address the value:
// an alloca's, or a constant offset into one.
@(private="file")
X86_Slot :: struct {
    off:    int,
    memory: bool,
    made:   bool,
}

@(private="file")
X86_Fixup :: struct {
    at:    int,      // a jump's rel32, in the body
    label: string,
}

// One function's translation: its body's code, made before its prologue
// (which needs the frame's size).
@(private="file")
X86_Fn :: struct {
    m:      ^X86_Module,
    code:   [dynamic]u8,
    relocs: [dynamic]X86_Reloc,
    slots:  map[string]X86_Slot,
    temps:  [dynamic]X86_Slot,   // (the `%.t<n>` locals', by n: most of them)
    labels: map[string]int,
    fixups: [dynamic]X86_Fixup,
    out:    int,     // the outgoing arguments' area, at the frame's bottom
    top:    int,     // the slots' bytes so far, above it
    nlabel: int,
}

// Registers by their encoding.
@(private="file")
X86_Reg :: enum u8 { AX = 0, CX = 1, DX = 2, SI = 6, DI = 7, R8 = 8, R9 = 9, R10 = 10, R11 = 11 }

// The Win64 argument registers.
@(private="file") X86_ARGS := [4]X86_Reg{.CX, .DX, .R8, .R9}

// Conditions by their encoding (jcc, setcc, cmovcc).
@(private="file")
X86_CC :: enum u8 { O = 0, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G }

// A memory operand: base + disp, or (base X86_RIP) a symbol + disp.
@(private="file")
X86_Mem :: struct {
    base: u8,
    disp: i32,
    sym:  u32,
}

@(private="file") X86_SP  :: 4
@(private="file") X86_RIP :: 255

// What the backend can't translate: an error, not a guess — with the IR line
// it was reading.
@(private="file") x86_line: string

@(private="file")
x86_fail :: proc(what, part: string) -> ! {
    fmt.eprintf("x86 backend: can't translate %s (%s) in: %s\n(`mara build -llvm` builds it with LLVM)\n", what, strings.trim_space(part), strings.trim_space(x86_line))
    os.exit(1)
}

// --- a module ----------------------------------------------------------------------

// The program's types, from its type definitions (`%class.X = type {…}`).
x86_program :: proc(type_decls: []string) -> ^X86_Program {
    p := new(X86_Program)
    p.keep = context.allocator
    p.named = make(map[string]string)
    p.types = make(map[string]^X86_Type)
    for d in type_decls {
        if eq := strings.index(d, " = type "); eq > 0 { p.named[d[:eq]] = strings.trim_space(d[eq + 8:]) }
    }
    p.i1, p.i8, p.i16, p.i32, p.i64 = x86_type(p, "i1"), x86_type(p, "i8"), x86_type(p, "i16"), x86_type(p, "i32"), x86_type(p, "i64")
    p.ptr, p.f32, p.f64, p.void = x86_type(p, "ptr"), x86_type(p, "float"), x86_type(p, "double"), x86_type(p, "void")
    return p
}

// A module's IR — its parts' lines: globals and functions, in order — as a
// COFF object, into `out`.
x86_module :: proc(p: ^X86_Program, parts: []string, out: ^[dynamic]u8) {
    m := X86_Module{p = p, keep = context.allocator}
    m.sym_of = make(map[string]u32)
    m.exports = make([dynamic]string)
    size := 0
    for part in parts { size += len(part) }
    for s in X86_Sec {
        m.sec[s] = make([dynamic]u8, 0, size / 2 if s == .Text else 0)
        m.relocs[s] = make([dynamic]X86_Reloc)
        append(&m.syms, X86_Sym{name = X86_SEC_NAME[s], sec = int(s) + 1, section = true})
    }
    // (Each function's own work is scratch, let go of once it's in the object.)
    scratch: virtual.Arena
    _ = virtual.arena_init_growing(&scratch)
    defer virtual.arena_destroy(&scratch)
    for part in parts {
        rest := part
        for len(rest) > 0 {
            line := rest
            nl := strings.index_byte(rest, '\n')
            if nl >= 0 { line, rest = rest[:nl], rest[nl + 1:] } else { rest = "" }
            switch {
            case strings.has_prefix(line, "define "):
                body, out := x86_body(&rest)
                {
                    context.allocator = virtual.arena_allocator(&scratch)
                    context.temp_allocator = context.allocator
                    x86_function(&m, line, body, out)
                }
                virtual.arena_free_all(&scratch)
            case strings.has_prefix(line, "@"):
                x86_global(&m, line)
            }
        }
    }
    for name in m.exports {
        append(&m.sec[.Drectve], " /EXPORT:")
        append(&m.sec[.Drectve], name)
    }
    x86_coff(&m, out)
}

// A global's symbol name: a private one (`@.str…`) the module's own.
@(private="file")
x86_sym :: proc(name: string) -> string {
    if len(name) > 0 && name[0] == '.' { return strings.concatenate({".L", name}) }
    return name
}

// A symbol by name, made (another object's, until defined) when first named.
@(private="file")
x86_symbol :: proc(m: ^X86_Module, name: string) -> u32 {
    if i, ok := m.sym_of[name]; ok { return i }
    i := u32(len(m.syms))
    append(&m.syms, X86_Sym{name = strings.clone(name, m.keep)})
    m.sym_of[m.syms[i].name] = i
    return i
}

@(private="file")
x86_define :: proc(m: ^X86_Module, name: string, sec: X86_Sec, value: int, global, fn: bool) {
    i := x86_symbol(m, name)   // (first: it may grow syms)
    s := &m.syms[i]
    s.sec, s.value, s.global, s.fn = int(sec) + 1, u32(value), global, fn
}

@(private="file")
x86_align :: proc(n, a: int) -> int {
    return (n + a - 1) / a * a
}

@(private="file")
x86_pad :: proc(b: ^[dynamic]u8, a: int, fill: u8 = 0) {
    for len(b) % a != 0 { append(b, fill) }
}

@(private="file")
x86_u16 :: proc(b: ^[dynamic]u8, v: u16) {
    append(b, u8(v), u8(v >> 8))
}

@(private="file")
x86_u32 :: proc(b: ^[dynamic]u8, v: u32) {
    append(b, u8(v), u8(v >> 8), u8(v >> 16), u8(v >> 24))
}

@(private="file")
x86_u64 :: proc(b: ^[dynamic]u8, v: u64) {
    x86_u32(b, u32(v))
    x86_u32(b, u32(v >> 32))
}

@(private="file")
x86_put32 :: proc(b: []u8, at: int, v: u32) {
    b[at], b[at + 1], b[at + 2], b[at + 3] = u8(v), u8(v >> 8), u8(v >> 16), u8(v >> 24)
}

@(private="file")
x86_atoi :: proc(s: string) -> int {
    n, _ := strconv.parse_int(s)
    return n
}

// --- reading the IR ----------------------------------------------------------------

@(private="file")
X86_Lex :: struct {
    s: string,
    i: int,
}

@(private="file")
x86_ws :: proc(l: ^X86_Lex) {
    for l.i < len(l.s) && (l.s[l.i] == ' ' || l.s[l.i] == '\t' || l.s[l.i] == '\r') { l.i += 1 }
}

@(private="file")
x86_at :: proc(l: ^X86_Lex, c: byte) -> bool {
    x86_ws(l)
    return l.i < len(l.s) && l.s[l.i] == c
}

@(private="file")
x86_eat :: proc(l: ^X86_Lex, c: byte) -> bool {
    if !x86_at(l, c) { return false }
    l.i += 1
    return true
}

// What ends a word.
@(private="file", rodata)
X86_STOP := [256]bool{' ' = true, '\t' = true, '\r' = true, ',' = true, '(' = true, ')' = true, '[' = true, ']' = true, '{' = true, '}' = true, '<' = true, '>' = true, '"' = true, '=' = true}

// A word: a name, a number, a keyword.
@(private="file")
x86_word :: proc(l: ^X86_Lex) -> string {
    x86_ws(l)
    start := l.i
    for l.i < len(l.s) && !X86_STOP[l.s[l.i]] { l.i += 1 }
    return l.s[start:l.i]
}

// Whether the next word is w: then it's read.
@(private="file")
x86_is :: proc(l: ^X86_Lex, w: string) -> bool {
    save := l.i
    if x86_word(l) == w { return true }
    l.i = save
    return false
}

// A type's text: a word, or a bracketed array or struct.
@(private="file")
x86_type_text :: proc(l: ^X86_Lex) -> string {
    x86_ws(l)
    if l.i >= len(l.s) { return "" }
    start := l.i
    switch l.s[l.i] {
    case '[', '{', '<':
        depth := 0
        for l.i < len(l.s) {
            c := l.s[l.i]
            l.i += 1
            switch c {
            case '[', '{', '<': depth += 1
            case ']', '}', '>': depth -= 1
            }
            if depth == 0 { break }
        }
        return l.s[start:l.i]
    }
    return x86_word(l)
}

// A type's layout, by its text.
@(private="file")
x86_type :: proc(m: ^X86_Program, text: string) -> ^X86_Type {
    if m.void != nil && len(text) <= 6 {
        switch text {
        case "i64":    return m.i64
        case "ptr":    return m.ptr
        case "i1":     return m.i1
        case "i32":    return m.i32
        case "i8":     return m.i8
        case "i16":    return m.i16
        case "double": return m.f64
        case "float":  return m.f32
        case "void":   return m.void
        }
    }
    if t, ok := m.types[text]; ok { return t }
    t := new(X86_Type, m.keep)
    m.types[text] = t
    switch {
    case text == "void":   t^ = {kind = .Void, align = 1}
    case text == "ptr":    t^ = {kind = .Ptr, size = 8, align = 8}
    case text == "half":   t^ = {kind = .F16, size = 2, align = 2}
    case text == "float":  t^ = {kind = .F32, size = 4, align = 4}
    case text == "double": t^ = {kind = .F64, size = 8, align = 8}
    case len(text) > 1 && text[0] == 'i':
        bits := x86_atoi(text[1:])
        size := 1
        for size * 8 < bits { size *= 2 }
        t^ = {kind = .Int, bits = bits, size = size, align = size}
    case text[0] == '%':
        body, ok := m.named[text]
        if !ok { x86_fail("a type with no definition", text) }
        t^ = x86_type(m, body)^
    case text[0] == '[':
        l := X86_Lex{text[1:len(text) - 1], 0}
        n := x86_atoi(x86_word(&l))
        x86_word(&l)   // x
        elem := x86_type(m, x86_type_text(&l))
        t^ = {kind = .Array, elem = elem, count = n, size = elem.size * n, align = elem.align}
    case text[0] == '{' || text[0] == '<':
        packed := text[0] == '<'
        l := X86_Lex{text[2:len(text) - 2] if packed else text[1:len(text) - 1], 0}
        fields := make([dynamic]^X86_Type, m.keep)
        offsets := make([dynamic]int, m.keep)
        size, align := 0, 1
        for {
            x86_ws(&l)
            if l.i >= len(l.s) { break }
            f := x86_type(m, x86_type_text(&l))
            a := 1 if packed else f.align
            size = x86_align(size, a)
            append(&fields, f)
            append(&offsets, size)
            size += f.size
            align = max(align, a)
            x86_eat(&l, ',')
        }
        t^ = {kind = .Struct, fields = fields[:], offsets = offsets[:], size = x86_align(size, align), align = align}
    case:
        x86_fail("a type", text)
    }
    return t
}

// A value held in memory, not a register: an array, a struct, a wide int.
@(private="file")
x86_aggregate :: proc(t: ^X86_Type) -> bool {
    return t.kind == .Array || t.kind == .Struct || (t.kind == .Int && t.bits > 64)
}

@(private="file")
x86_float :: proc(t: ^X86_Type) -> bool {
    return t.kind == .F32 || t.kind == .F64
}

// A value of type t.
@(private="file")
x86_value :: proc(l: ^X86_Lex, t: ^X86_Type) -> X86_Val {
    w := x86_word(l)
    if w == "" { return {} }
    switch w[0] {
    case '%': return {kind = .Local, name = w}
    case '@': return {kind = .Global, name = w[1:]}
    }
    switch w {
    case "true":                                                 return {kind = .Int, n = 1}
    case "false", "null", "zeroinitializer", "undef", "poison": return {}
    }
    if strings.has_prefix(w, "0xH") {   // a half's bits
        u, _ := strconv.parse_u64_of_base(w[3:], 16)
        return {kind = .Int, n = i64(u)}
    }
    if strings.has_prefix(w, "0x") {    // a float's or double's, written as a double's bits
        u, _ := strconv.parse_u64_of_base(w[2:], 16)
        if t != nil && t.kind == .F32 { u = u64(transmute(u32)f32(transmute(f64)u)) }
        return {kind = .Int, n = transmute(i64)u}
    }
    if t != nil && (t.kind == .F16 || t.kind == .F32 || t.kind == .F64) {
        v, _ := strconv.parse_f64(w)
        #partial switch t.kind {
        case .F16: return {kind = .Int, n = i64(transmute(u16)f16(v))}
        case .F32: return {kind = .Int, n = i64(transmute(u32)f32(v))}
        }
        return {kind = .Int, n = transmute(i64)v}
    }
    // (An integer, maybe wider than i64 holds as written: its low bits.)
    neg := w[0] == '-'
    u: u64
    for c in transmute([]u8)w[1 if neg else 0:] {
        if c < '0' || c > '9' { x86_fail("a value", w) }
        u = u * 10 + u64(c - '0')
    }
    if neg { u = -u }
    return {kind = .Int, n = transmute(i64)u}
}

@(private="file")
x86_typed :: proc(f: ^X86_Fn, l: ^X86_Lex) -> (^X86_Type, X86_Val) {
    t := x86_type(f.m.p, x86_type_text(l))
    return t, x86_value(l, t)
}

// --- encoding ----------------------------------------------------------------------

// [prefix] [REX] opcode ModRM, the r/m operand a register.
@(private="file")
x86_enc_rr :: proc(f: ^X86_Fn, pre: u8, w: bool, op: []u8, reg, rm: u8) {
    if pre != 0 { append(&f.code, pre) }
    rex := u8(0x40)
    if w { rex |= 8 }
    if reg >= 8 { rex |= 4 }
    if rm >= 8 { rex |= 1 }
    if rex != 0x40 { append(&f.code, rex) }
    append(&f.code, ..op)
    append(&f.code, 0xC0 | (reg & 7) << 3 | (rm & 7))
}

// [prefix] [REX] opcode ModRM [SIB] [disp], the r/m operand memory.
@(private="file")
x86_enc_rm :: proc(f: ^X86_Fn, pre: u8, w: bool, op: []u8, reg: u8, mem: X86_Mem) {
    if pre != 0 { append(&f.code, pre) }
    rex := u8(0x40)
    if w { rex |= 8 }
    if reg >= 8 { rex |= 4 }
    if mem.base != X86_RIP && mem.base >= 8 { rex |= 1 }
    if rex != 0x40 { append(&f.code, rex) }
    append(&f.code, ..op)
    if mem.base == X86_RIP {   // rip-relative: the symbol's address, from the instruction's end
        append(&f.code, (reg & 7) << 3 | 5)
        append(&f.relocs, X86_Reloc{u32(len(f.code)), mem.sym, X86_REL32})
        x86_u32(&f.code, u32(mem.disp))
        return
    }
    mod: u8 = 2
    switch {
    case mem.disp == 0 && mem.base & 7 != 5:      mod = 0
    case mem.disp >= -128 && mem.disp <= 127:     mod = 1
    }
    append(&f.code, mod << 6 | (reg & 7) << 3 | (mem.base & 7))
    if mem.base & 7 == 4 { append(&f.code, 0x24) }   // (rsp's: a SIB byte, no index)
    switch mod {
    case 1: append(&f.code, u8(i8(mem.disp)))
    case 2: x86_u32(&f.code, u32(mem.disp))
    }
}

// An operation's prefix and REX.W by its size: 2, 0x66; 8, W.
@(private="file")
x86_pre :: proc(size: int) -> u8 {
    return 0x66 if size == 2 else 0
}

// `op r/m, reg` — add 0x00, or 0x08, and 0x20, sub 0x28, xor 0x30, cmp
// 0x38, test 0x84, mov 0x88: its byte form, the wider one next. (Byte
// registers: only al, cl and dl are used.)
@(private="file")
x86_rr :: proc(f: ^X86_Fn, size: int, op: u8, dst, src: X86_Reg) {
    x86_enc_rr(f, x86_pre(size), size == 8, {op if size == 1 else op + 1}, u8(src), u8(dst))
}

// `op r/m, imm` (0x80 group): add 0, or 1, and 4, sub 5, xor 6, cmp 7.
@(private="file")
x86_ri :: proc(f: ^X86_Fn, size: int, digit: u8, r: X86_Reg, imm: i64) {
    switch {
    case size == 1:
        x86_enc_rr(f, 0, false, {0x80}, digit, u8(r))
        append(&f.code, u8(imm))
    case imm >= -128 && imm <= 127:
        x86_enc_rr(f, x86_pre(size), size == 8, {0x83}, digit, u8(r))
        append(&f.code, u8(i8(imm)))
    case:
        x86_enc_rr(f, x86_pre(size), size == 8, {0x81}, digit, u8(r))
        if size == 2 { x86_u16(&f.code, u16(imm)) } else { x86_u32(&f.code, u32(imm)) }
    }
}

// The 0xF6/0xF7 group on r: test 0, neg 3, mul 4, imul 5, div 6, idiv 7.
@(private="file")
x86_grp3 :: proc(f: ^X86_Fn, size: int, digit: u8, r: X86_Reg) {
    x86_enc_rr(f, x86_pre(size), size == 8, {0xF6 if size == 1 else 0xF7}, digit, u8(r))
}

// A register from memory, zero-extended (signed: sign-extended).
@(private="file")
x86_load :: proc(f: ^X86_Fn, r: X86_Reg, mem: X86_Mem, size: int, signed := false) {
    switch size {
    case 1: x86_enc_rm(f, 0, signed, {0x0F, 0xBE if signed else 0xB6}, u8(r), mem)
    case 2: x86_enc_rm(f, 0, signed, {0x0F, 0xBF if signed else 0xB7}, u8(r), mem)
    case 4: x86_enc_rm(f, 0, signed, {0x63 if signed else 0x8B}, u8(r), mem)
    case:   x86_enc_rm(f, 0, true, {0x8B}, u8(r), mem)
    }
}

// A register's low `size` bytes into memory.
@(private="file")
x86_store :: proc(f: ^X86_Fn, mem: X86_Mem, r: X86_Reg, size: int) {
    x86_enc_rm(f, x86_pre(size), size == 8, {0x88 if size == 1 else 0x89}, u8(r), mem)
}

@(private="file")
x86_lea :: proc(f: ^X86_Fn, r: X86_Reg, mem: X86_Mem) {
    x86_enc_rm(f, 0, true, {0x8D}, u8(r), mem)
}

@(private="file")
x86_mov :: proc(f: ^X86_Fn, dst, src: X86_Reg) {
    x86_rr(f, 8, 0x88, dst, src)
}

// A number into r.
@(private="file")
x86_imm :: proc(f: ^X86_Fn, r: X86_Reg, n: i64) {
    switch {
    case n == 0:   // xor r32, r32
        x86_enc_rr(f, 0, false, {0x31}, u8(r), u8(r))
    case n > 0 && n <= i64(max(u32)):   // mov r32, imm32: zero-extended
        if u8(r) >= 8 { append(&f.code, 0x41) }
        append(&f.code, 0xB8 + (u8(r) & 7))
        x86_u32(&f.code, u32(n))
    case n < 0 && n >= i64(min(i32)):   // mov r64, imm32: sign-extended
        x86_enc_rr(f, 0, true, {0xC7}, 0, u8(r))
        x86_u32(&f.code, u32(n))
    case:
        append(&f.code, 0x48 | (1 if u8(r) >= 8 else 0), 0xB8 + (u8(r) & 7))
        x86_u64(&f.code, u64(n))
    }
}

// An int of `bits` in r, extended to 64: a value's high bits are whatever its
// instruction left, so what reads them extends it first.
@(private="file")
x86_extend :: proc(f: ^X86_Fn, r: X86_Reg, bits: int, signed: bool) {
    switch bits {
    case 1:
        x86_ri(f, 4, 4, r, 1)
        if signed { x86_grp3(f, 8, 3, r) }
    case 8:  x86_enc_rr(f, 0, signed, {0x0F, 0xBE if signed else 0xB6}, u8(r), u8(r))
    case 16: x86_enc_rr(f, 0, signed, {0x0F, 0xBF if signed else 0xB7}, u8(r), u8(r))
    case 32:
        if signed { x86_enc_rr(f, 0, true, {0x63}, u8(r), u8(r)) } else { x86_rr(f, 4, 0x88, r, r) }
    }
}

@(private="file")
x86_setcc :: proc(f: ^X86_Fn, cc: X86_CC, r: X86_Reg) {
    x86_enc_rr(f, 0, false, {0x0F, 0x90 + u8(cc)}, 0, u8(r))
}

// The flag a setcc made, in al, as a 0 or 1 in eax.
@(private="file")
x86_bool :: proc(f: ^X86_Fn) {
    x86_enc_rr(f, 0, false, {0x0F, 0xB6}, 0, 0)
}

@(private="file")
x86_cmov :: proc(f: ^X86_Fn, cc: X86_CC, dst, src: X86_Reg) {
    x86_enc_rr(f, 0, true, {0x0F, 0x40 + u8(cc)}, u8(dst), u8(src))
}

// SSE: `op xmm, xmm` (or a general register, as the op takes).
@(private="file")
x86_sse :: proc(f: ^X86_Fn, pre: u8, w: bool, op: u8, dst, src: u8) {
    x86_enc_rr(f, pre, w, {0x0F, op}, dst, src)
}

// r's bits into xmm<x> (movq), or back.
@(private="file")
x86_to_xmm :: proc(f: ^X86_Fn, x: u8, r: X86_Reg) {
    x86_sse(f, 0x66, true, 0x6E, x, u8(r))
}

@(private="file")
x86_from_xmm :: proc(f: ^X86_Fn, r: X86_Reg, x: u8) {
    x86_sse(f, 0x66, true, 0x7E, x, u8(r))
}

// The scalar float prefix: F3 for a float's ops, F2 for a double's.
@(private="file")
x86_fpre :: proc(t: ^X86_Type) -> u8 {
    return 0xF3 if t.kind == .F32 else 0xF2
}

// A jump to a label of this function's: jmp, or jcc when cc is given.
@(private="file")
x86_jump :: proc(f: ^X86_Fn, label: string, cc: Maybe(X86_CC) = nil) {
    if c, conditional := cc.?; conditional {
        append(&f.code, 0x0F, 0x80 + u8(c))
    } else {
        append(&f.code, 0xE9)
    }
    append(&f.fixups, X86_Fixup{len(f.code), label})
    x86_u32(&f.code, 0)
}

@(private="file")
x86_place :: proc(f: ^X86_Fn, label: string) {
    f.labels[label] = len(f.code)
}

// A label of the code's own making.
@(private="file")
x86_label :: proc(f: ^X86_Fn) -> string {
    f.nlabel += 1
    buf := make([]byte, 24)
    return strconv.write_int(buf, i64(f.nlabel), 10)
}

@(private="file")
x86_call_sym :: proc(f: ^X86_Fn, name: string) {
    append(&f.code, 0xE8)
    append(&f.relocs, X86_Reloc{u32(len(f.code)), x86_symbol(f.m, name), X86_REL32})
    x86_u32(&f.code, 0)
}

// --- a function --------------------------------------------------------------------

@(private="file")
x86_function :: proc(m: ^X86_Module, header: string, body: string, out: int) {
    x86_line = header
    l := X86_Lex{header, 0}
    x86_word(&l)   // define
    export, local := false, false
    words: for {
        save := l.i
        switch x86_word(&l) {
        case "dllexport":           export = true
        case "internal", "private": local = true
        case "dso_local":
        case:
            l.i = save
            break words
        }
    }
    x86_type_text(&l)   // its result's type: its returns say
    sym := x86_sym(x86_word(&l)[1:])
    f := X86_Fn{m = m}
    f.out = out
    f.slots = make(map[string]X86_Slot)
    f.temps = make([dynamic]X86_Slot)
    f.labels = make(map[string]int)
    params := make([dynamic]X86_Arg)
    x86_eat(&l, '(')
    for !x86_eat(&l, ')') {
        t := x86_type(m.p, x86_type_text(&l))
        name := x86_word(&l)
        x86_slot(&f, name, 8, 8)
        append(&params, X86_Arg{t, {kind = .Local, name = name}})
        x86_eat(&l, ',')
    }
    rest := body
    for len(rest) > 0 {
        line := rest
        if nl := strings.index_byte(rest, '\n'); nl >= 0 { line, rest = rest[:nl], rest[nl + 1:] } else { rest = "" }
        if len(line) == 0 || line[0] == ';' { continue }
        if line[0] != ' ' {   // a label
            x86_place(&f, strings.trim_suffix(line, ":"))
            continue
        }
        if strings.has_prefix(line, "  switch ") {   // its cases, a line each, then `]`
            end := strings.index(rest, "\n  ]")
            if end < 0 { x86_fail("a switch with no end", line) }
            cases, _ := strings.replace_all(rest[:end + 4], "\n", " ")
            line = strings.concatenate({line, " ", cases})
            rest = rest[end + 4:]
            if len(rest) > 0 && rest[0] == '\n' { rest = rest[1:] }
        }
        x86_inst(&f, line)
    }

    // Its frame: the outgoing arguments, then the slots — rsp 16-aligned
    // after the two pushes and the allocation. Its one epilogue.
    frame := x86_align(f.out + f.top, 16) + 8
    x86_place(&f, ".exit")
    append(&f.code, 0x48, 0x81, 0xC4)   // add rsp, frame
    x86_u32(&f.code, u32(frame))
    append(&f.code, 0x5F, 0x5E, 0xC3)   // pop rdi; pop rsi; ret
    for fx in f.fixups {
        to, ok := f.labels[fx.label]
        if !ok { x86_fail("a jump to no label", fx.label) }
        x86_put32(f.code[:], fx.at, u32(i32(to - (fx.at + 4))))
    }

    // Its prologue: rsi and rdi pushed (rep movs/stos use them), the frame
    // allocated — past a page, each one touched in order (__chkstk).
    text := &m.sec[.Text]
    x86_pad(text, 16, 0xCC)
    start := len(text)
    x86_define(m, sym, .Text, start, !local, true)
    append(text, 0x56, 0x57)   // push rsi; push rdi
    if frame >= 4096 {
        append(text, 0xB8)   // mov eax, frame
        x86_u32(text, u32(frame))
        append(text, 0xE8)   // call __chkstk
        append(&m.relocs[.Text], X86_Reloc{u32(len(text)), x86_symbol(m, "__chkstk"), X86_REL32})
        x86_u32(text, 0)
        append(text, 0x48, 0x29, 0xC4)   // sub rsp, rax
    } else {
        append(text, 0x48, 0x81, 0xEC)   // sub rsp, frame
        x86_u32(text, u32(frame))
    }
    prolog := len(text) - start
    // Its params into their slots: the first four from their registers, the
    // rest from the caller's frame (past its return address and home area).
    {
        g := X86_Fn{m = m, out = f.out}
        for p, i in params {
            at := x86_mem(&f, x86_find(&f, p.v.name)^, 0)
            switch {
            case i < 4 && x86_float(p.t):
                x86_enc_rm(&g, 0x66, false, {0x0F, 0xD6}, u8(i), at)   // movq [slot], xmm<i>
            case i < 4:
                x86_store(&g, at, X86_ARGS[i], 8)
            case:
                x86_load(&g, .AX, {base = X86_SP, disp = i32(frame + 16 + 40 + 8 * (i - 4))}, 8)
                x86_store(&g, at, .AX, 8)
            }
        }
        append(text, ..g.code[:])
    }
    base := len(text)
    append(text, ..f.code[:])
    for r in f.relocs { append(&m.relocs[.Text], X86_Reloc{r.at + u32(base), r.sym, r.kind}) }
    end := len(text)

    // Its unwind info: the frame's allocation, then the pushes (rdi's,
    // rsi's), each at its instruction's end in the prologue.
    x := &m.sec[.Xdata]
    x86_pad(x, 4)
    xoff := len(x)
    codes := make([dynamic]u16)
    switch {
    case frame <= 128:    append(&codes, u16(prolog) | (u16(2) | u16((frame - 8) / 8) << 4) << 8)   // UWOP_ALLOC_SMALL
    case frame <= 524280: append(&codes, u16(prolog) | u16(1) << 8, u16(frame / 8))                // UWOP_ALLOC_LARGE
    case:                 append(&codes, u16(prolog) | (u16(1) | u16(1) << 4) << 8, u16(frame), u16(frame >> 16))
    }
    append(&codes, u16(2) | (u16(7) << 4) << 8, u16(1) | (u16(6) << 4) << 8)   // UWOP_PUSH_NONVOL rdi, rsi
    append(x, 1, u8(prolog), u8(len(codes)), 0)
    for c in codes { x86_u16(x, c) }
    if len(codes) % 2 == 1 { x86_u16(x, 0) }
    p := &m.sec[.Pdata]
    for at, k in ([3]int{start, end, xoff}) {
        append(&m.relocs[.Pdata], X86_Reloc{u32(len(p)), u32(X86_Sec.Xdata if k == 2 else X86_Sec.Text), X86_ADDR32NB})
        x86_u32(p, u32(at))
    }
    if export { append(&m.exports, strings.clone(sym, m.keep)) }
}

// A function's body — its lines up to its closing `}`, read past — and its
// outgoing arguments' area: the most any call in it passes, 8 bytes each, and
// at least the 32 the callee may keep its register arguments in; none for a
// function that calls nothing.
@(private="file")
x86_body :: proc(rest: ^string) -> (body: string, out: int) {
    most := -1
    text := rest^
    pos := 0
    for {
        if pos >= len(text) { x86_fail("a function with no end", "") }
        line := text[pos:]
        next := len(text)
        if nl := strings.index_byte(line, '\n'); nl >= 0 {
            line = line[:nl]
            next = pos + nl + 1
        }
        if len(line) > 0 && line[0] == '}' {
            body, rest^ = text[:pos], text[next:]
            break
        }
        pos = next
        // (A call: `  call …`, or `  %x = call …`.)
        if len(line) < 3 || line[0] != ' ' { continue }
        at := 2
        if line[2] == '%' {
            eq := strings.index_byte(line, '=')
            if eq < 0 { continue }
            at = eq + 2
        }
        if !strings.has_prefix(line[min(at, len(line)):], "call ") { continue }
        rest := line[at + 5:]
        c := strings.index_any(rest, "@%")   // the callee: past its result's type and signature
        if c < 0 { continue }
        p := strings.index_byte(rest[c:], '(')
        if p < 0 { continue }
        n, depth, any := 0, 0, false
        count: for ch in transmute([]u8)rest[c + p + 1:] {
            switch ch {
            case '(', '[', '{', '<': depth += 1
            case ')', ']', '}', '>':
                if depth == 0 { break count }
                depth -= 1
            case ',':
                if depth == 0 { n += 1 }
            }
            if ch != ' ' { any = true }
        }
        if any { n += 1 }
        most = max(most, n)
    }
    if most >= 0 { out = x86_align(max(32, 8 * most), 16) }
    return
}

// A local's slot, made when it's first named: memory (an alloca's), or 8
// bytes for a value (more for an aggregate's).
@(private="file")
x86_slot :: proc(f: ^X86_Fn, name: string, size, align: int, memory := false) -> X86_Slot {
    if s := x86_find(f, name); s != nil { return s^ }
    a := max(align, 1 if memory else 8)
    f.top = x86_align(f.top, a)
    s := X86_Slot{off = f.top, memory = memory, made = true}
    f.top += max(size, 1) if memory else x86_align(max(size, 8), 8)
    x86_set_slot(f, name, s)
    return s
}

// A local's slot, if it has one: a `%.t<n>` one's by n.
@(private="file")
x86_find :: proc(f: ^X86_Fn, name: string) -> ^X86_Slot {
    if n, is_temp := x86_temp_number(name); is_temp {
        if n < len(f.temps) && f.temps[n].made { return &f.temps[n] }
        return nil
    }
    return &f.slots[name] or_else nil
}

@(private="file")
x86_set_slot :: proc(f: ^X86_Fn, name: string, s: X86_Slot) {
    s := s
    s.made = true
    if n, is_temp := x86_temp_number(name); is_temp {
        if n >= len(f.temps) { resize(&f.temps, max(n + 1, 2 * len(f.temps))) }
        f.temps[n] = s
        return
    }
    f.slots[name] = s
}

@(private="file")
x86_temp_number :: proc(name: string) -> (int, bool) {
    if len(name) < 4 || name[1] != '.' || name[2] != 't' { return 0, false }
    n := 0
    for c in transmute([]u8)name[3:] {
        if c < '0' || c > '9' { return 0, false }
        n = n * 10 + int(c - '0')
    }
    return n, true
}

// The memory `off` bytes into a slot.
@(private="file")
x86_mem :: proc(f: ^X86_Fn, s: X86_Slot, off: int) -> X86_Mem {
    return {base = X86_SP, disp = i32(f.out + s.off + off)}
}

// A value into register r: a local's (a memory's address), a global's
// address, a number.
@(private="file")
x86_get :: proc(f: ^X86_Fn, v: X86_Val, r: X86_Reg) {
    switch v.kind {
    case .Local:
        s := x86_slot(f, v.name, 8, 8)
        if s.memory { x86_lea(f, r, x86_mem(f, s, 0)) } else { x86_load(f, r, x86_mem(f, s, 0), 8) }
    case .Global:
        x86_lea(f, r, {base = X86_RIP, sym = x86_symbol(f.m, x86_sym(v.name))})
    case .Zero:
        x86_imm(f, r, 0)
    case .Int:
        x86_imm(f, r, v.n)
    }
}

// Where a pointer points, as a memory operand: a local's memory itself, a
// global's (rip-relative); any other pointer, loaded into r.
@(private="file")
x86_ptr :: proc(f: ^X86_Fn, v: X86_Val, r: X86_Reg) -> X86_Mem {
    #partial switch v.kind {
    case .Local:
        if s := x86_slot(f, v.name, 8, 8); s.memory { return x86_mem(f, s, 0) }
    case .Global:
        return {base = X86_RIP, sym = x86_symbol(f.m, x86_sym(v.name))}
    }
    x86_get(f, v, r)
    return {base = u8(r)}
}

// The result, in rax, into its slot.
@(private="file")
x86_put :: proc(f: ^X86_Fn, dest: string) {
    if dest == "" { return }
    x86_store(f, x86_mem(f, x86_slot(f, dest, 8, 8), 0), .AX, 8)
}

// size bytes from rsi to rdi (rep movsb), or zeroed at rdi (rep stosb).
@(private="file")
x86_copy :: proc(f: ^X86_Fn, size: int) {
    x86_imm(f, .CX, i64(size))
    append(&f.code, 0xF3, 0xA4)
}

@(private="file")
x86_zero :: proc(f: ^X86_Fn, size: int) {
    x86_imm(f, .AX, 0)
    x86_imm(f, .CX, i64(size))
    append(&f.code, 0xF3, 0xAA)
}

// --- instructions --------------------------------------------------------------------

@(private="file")
x86_inst :: proc(f: ^X86_Fn, line: string) {
    m := f.m
    x86_line = line
    l := X86_Lex{line, 0}
    dest := ""
    op := x86_word(&l)
    if len(op) > 0 && op[0] == '%' {
        dest = op
        x86_eat(&l, '=')
        op = x86_word(&l)
    }
    for x86_is(&l, "inbounds") || x86_is(&l, "nsw") || x86_is(&l, "nuw") || x86_is(&l, "exact") {}
    switch op {
    case "alloca":
        t := x86_type(m.p, x86_type_text(&l))
        align := t.align
        if x86_eat(&l, ',') && x86_is(&l, "align") { align = max(align, x86_atoi(x86_word(&l))) }
        x86_slot(f, dest, t.size, align, memory = true)

    case "load":
        t := x86_type(m.p, x86_type_text(&l))
        x86_eat(&l, ',')
        _, p := x86_typed(f, &l)
        at := x86_ptr(f, p, .CX)
        if x86_aggregate(t) {
            x86_lea(f, .SI, at)
            x86_lea(f, .DI, x86_mem(f, x86_slot(f, dest, t.size, t.align), 0))
            x86_copy(f, t.size)
            return
        }
        x86_load(f, .AX, at, t.size)
        x86_put(f, dest)

    case "store":
        t, v := x86_typed(f, &l)
        x86_eat(&l, ',')
        _, p := x86_typed(f, &l)
        at := x86_ptr(f, p, .DI)
        if x86_aggregate(t) {
            x86_lea(f, .DI, at)
            switch {
            case v.kind == .Local:
                x86_lea(f, .SI, x86_mem(f, x86_slot(f, v.name, t.size, t.align), 0))
                x86_copy(f, t.size)
            case v.kind == .Zero || (v.kind == .Int && v.n == 0):
                x86_zero(f, t.size)
            case:
                x86_fail("an aggregate's value", line)
            }
            return
        }
        x86_get(f, v, .AX)
        if t.kind == .Int && t.bits == 1 { x86_ri(f, 4, 4, .AX, 1) }   // (a bool: 0 or 1)
        x86_store(f, at, .AX, t.size)

    case "getelementptr":
        t := x86_type(m.p, x86_type_text(&l))
        x86_eat(&l, ',')
        _, base := x86_typed(f, &l)
        // Its constant offset, and the variable indices scaled.
        Scaled :: struct { t: ^X86_Type, v: X86_Val, scale: int }
        vars := make([dynamic]Scaled, context.temp_allocator)
        off := 0
        cur := t
        first := true
        for x86_eat(&l, ',') {
            it, idx := x86_typed(f, &l)
            scale := 0
            switch {
            case first:
                scale = cur.size   // (the first steps over whole Ts)
                first = false
            case cur.kind == .Struct:
                if idx.kind == .Local { x86_fail("a field by a variable", line) }
                off += cur.offsets[idx.n]
                cur = cur.fields[idx.n]
                continue
            case cur.kind == .Array:
                scale = cur.elem.size
                cur = cur.elem
            case:
                x86_fail("an index", line)
            }
            if idx.kind == .Local { append(&vars, Scaled{it, idx, scale}) } else { off += int(idx.n) * scale }
        }
        // Into a local's memory at a constant offset: that memory, no value.
        if len(vars) == 0 && base.kind == .Local && x86_find(f, dest) == nil {
            if s := x86_slot(f, base.name, 8, 8); s.memory {
                x86_set_slot(f, dest, {off = s.off + off, memory = true})
                return
            }
        }
        x86_get(f, base, .AX)
        for sv in vars {
            x86_get(f, sv.v, .CX)
            x86_extend(f, .CX, sv.t.bits, true)
            if sv.scale != 1 {   // imul rcx, rcx, scale
                x86_enc_rr(f, 0, true, {0x69}, u8(X86_Reg.CX), u8(X86_Reg.CX))
                x86_u32(&f.code, u32(sv.scale))
            }
            x86_rr(f, 8, 0x00, .AX, .CX)
        }
        if off != 0 { x86_lea(f, .AX, {base = u8(X86_Reg.AX), disp = i32(off)}) }
        x86_put(f, dest)

    case "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "sdiv", "srem", "udiv", "urem":
        t, a := x86_typed(f, &l)
        x86_eat(&l, ',')
        b := x86_value(&l, t)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        switch op {
        case "add": x86_rr(f, 8, 0x00, .AX, .CX)
        case "sub": x86_rr(f, 8, 0x28, .AX, .CX)
        case "and": x86_rr(f, 8, 0x20, .AX, .CX)
        case "or":  x86_rr(f, 8, 0x08, .AX, .CX)
        case "xor": x86_rr(f, 8, 0x30, .AX, .CX)
        case "mul": x86_enc_rr(f, 0, true, {0x0F, 0xAF}, u8(X86_Reg.AX), u8(X86_Reg.CX))
        case "shl": x86_enc_rr(f, 0, true, {0xD3}, 4, u8(X86_Reg.AX))
        case "lshr":
            x86_extend(f, .AX, t.bits, false)
            x86_enc_rr(f, 0, true, {0xD3}, 5, u8(X86_Reg.AX))
        case "ashr":
            x86_extend(f, .AX, t.bits, true)
            x86_enc_rr(f, 0, true, {0xD3}, 7, u8(X86_Reg.AX))
        case "sdiv", "srem":
            x86_extend(f, .AX, t.bits, true)
            x86_extend(f, .CX, t.bits, true)
            append(&f.code, 0x48, 0x99)   // cqo
            x86_grp3(f, 8, 7, .CX)        // idiv rcx
            if op == "srem" { x86_mov(f, .AX, .DX) }
        case "udiv", "urem":
            x86_extend(f, .AX, t.bits, false)
            x86_extend(f, .CX, t.bits, false)
            x86_imm(f, .DX, 0)
            x86_grp3(f, 8, 6, .CX)        // div rcx
            if op == "urem" { x86_mov(f, .AX, .DX) }
        }
        x86_put(f, dest)

    case "fadd", "fsub", "fmul", "fdiv":
        t, a := x86_typed(f, &l)
        x86_eat(&l, ',')
        b := x86_value(&l, t)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        x86_to_xmm(f, 0, .AX)
        x86_to_xmm(f, 1, .CX)
        code: u8
        switch op {
        case "fadd": code = 0x58
        case "fsub": code = 0x5C
        case "fmul": code = 0x59
        case "fdiv": code = 0x5E
        }
        x86_sse(f, x86_fpre(t), false, code, 0, 1)
        x86_from_xmm(f, .AX, 0)
        x86_put(f, dest)

    case "fneg":
        t, a := x86_typed(f, &l)
        x86_get(f, a, .AX)
        if t.kind == .F32 {
            x86_ri(f, 4, 6, .AX, 0x80000000)   // xor eax, sign
        } else {
            x86_enc_rr(f, 0, true, {0x0F, 0xBA}, 7, u8(X86_Reg.AX))   // btc rax, 63
            append(&f.code, 63)
        }
        x86_put(f, dest)

    case "icmp":
        pred := x86_word(&l)
        t, a := x86_typed(f, &l)
        x86_eat(&l, ',')
        b := x86_value(&l, t)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        x86_rr(f, t.size, 0x38, .AX, .CX)
        cc: X86_CC
        switch pred {
        case "eq":  cc = .E
        case "ne":  cc = .NE
        case "slt": cc = .L
        case "sle": cc = .LE
        case "sgt": cc = .G
        case "sge": cc = .GE
        case "ult": cc = .B
        case "ule": cc = .BE
        case "ugt": cc = .A
        case "uge": cc = .AE
        case:       x86_fail("a comparison", pred)
        }
        x86_setcc(f, cc, .AX)
        x86_bool(f)
        x86_put(f, dest)

    case "fcmp":
        // (Ordered: false when either is NaN — ucomis says unordered with
        // ZF, PF and CF all set; une, true then.)
        pred := x86_word(&l)
        t, a := x86_typed(f, &l)
        x86_eat(&l, ',')
        b := x86_value(&l, t)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        x86_to_xmm(f, 0, .AX)
        x86_to_xmm(f, 1, .CX)
        ucomis :: proc(f: ^X86_Fn, t: ^X86_Type, a, b: u8) { x86_sse(f, 0 if t.kind == .F32 else 0x66, false, 0x2E, a, b) }
        switch pred {
        case "oeq":
            ucomis(f, t, 0, 1)
            x86_setcc(f, .E, .AX)
            x86_setcc(f, .NP, .CX)
            x86_rr(f, 1, 0x20, .AX, .CX)
        case "une":
            ucomis(f, t, 0, 1)
            x86_setcc(f, .NE, .AX)
            x86_setcc(f, .P, .CX)
            x86_rr(f, 1, 0x08, .AX, .CX)
        case "olt":
            ucomis(f, t, 1, 0)
            x86_setcc(f, .A, .AX)
        case "ole":
            ucomis(f, t, 1, 0)
            x86_setcc(f, .AE, .AX)
        case "ogt":
            ucomis(f, t, 0, 1)
            x86_setcc(f, .A, .AX)
        case "oge":
            ucomis(f, t, 0, 1)
            x86_setcc(f, .AE, .AX)
        case:
            x86_fail("a float comparison", pred)
        }
        x86_bool(f)
        x86_put(f, dest)

    case "select":
        _, c := x86_typed(f, &l)
        x86_eat(&l, ',')
        t, a := x86_typed(f, &l)
        x86_eat(&l, ',')
        _, b := x86_typed(f, &l)
        if x86_aggregate(t) { x86_fail("a select of aggregates", op) }
        x86_get(f, c, .DX)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        x86_grp3(f, 1, 0, .DX)   // test dl, 1
        append(&f.code, 1)
        x86_cmov(f, .E, .AX, .CX)
        x86_put(f, dest)

    case "zext", "sext", "trunc", "fpext", "fptrunc", "sitofp", "uitofp", "fptosi", "fptoui", "ptrtoint", "inttoptr", "bitcast":
        ft, v := x86_typed(f, &l)
        x86_is(&l, "to")
        tt := x86_type(m.p, x86_type_text(&l))
        x86_get(f, v, .AX)
        x86_convert(f, op, ft, tt)
        x86_put(f, dest)

    case "extractvalue":
        at, v := x86_typed(f, &l)
        if v.kind != .Local { x86_fail("a part of a constant", op) }
        off := 0
        cur := at
        for x86_eat(&l, ',') {
            k := x86_atoi(x86_word(&l))
            if cur.kind == .Struct {
                off += cur.offsets[k]
                cur = cur.fields[k]
            } else {
                off += k * cur.elem.size
                cur = cur.elem
            }
        }
        x86_load(f, .AX, x86_mem(f, x86_slot(f, v.name, at.size, at.align), off), cur.size)
        x86_put(f, dest)

    case "call":
        rt := x86_type(m.p, x86_type_text(&l))
        if x86_at(&l, '(') {   // a variadic callee's signature: its arguments say what they are
            depth := 0
            for l.i < len(l.s) {
                c := l.s[l.i]
                l.i += 1
                if c == '(' { depth += 1 }
                if c == ')' { depth -= 1; if depth == 0 { break } }
            }
        }
        callee := x86_word(&l)
        x86_eat(&l, '(')
        args := make([dynamic]X86_Arg, context.temp_allocator)
        for !x86_eat(&l, ')') {
            at, av := x86_typed(f, &l)
            append(&args, X86_Arg{at, av})
            x86_eat(&l, ',')
        }
        if strings.has_prefix(callee, "@llvm.") {
            x86_intrinsic(f, callee[6:], rt, args[:], dest)
        } else {
            x86_call(f, callee, rt, args[:], dest)
        }

    case "ret":
        t := x86_type(m.p, x86_type_text(&l))
        if t.kind != .Void {
            x86_get(f, x86_value(&l, t), .AX)
            if x86_float(t) { x86_to_xmm(f, 0, .AX) }
        }
        x86_jump(f, ".exit")

    case "br":
        if x86_is(&l, "label") {
            x86_jump(f, x86_word(&l)[1:])
            return
        }
        _, c := x86_typed(f, &l)
        x86_eat(&l, ',')
        x86_is(&l, "label")
        yes := x86_word(&l)
        x86_eat(&l, ',')
        x86_is(&l, "label")
        no := x86_word(&l)
        x86_get(f, c, .AX)
        x86_grp3(f, 1, 0, .AX)   // test al, 1
        append(&f.code, 1)
        x86_jump(f, yes[1:], X86_CC.NE)
        x86_jump(f, no[1:])

    case "switch":
        t, v := x86_typed(f, &l)
        x86_eat(&l, ',')
        x86_is(&l, "label")
        default := x86_word(&l)
        x86_eat(&l, '[')
        x86_get(f, v, .AX)
        for !x86_eat(&l, ']') {
            _, c := x86_typed(f, &l)
            x86_eat(&l, ',')
            x86_is(&l, "label")
            to := x86_word(&l)
            if c.n >= i64(min(i32)) && c.n <= i64(max(i32)) {
                x86_ri(f, t.size, 7, .AX, c.n)
            } else {
                x86_get(f, c, .CX)
                x86_rr(f, 8, 0x38, .AX, .CX)
            }
            x86_jump(f, to[1:], X86_CC.E)
        }
        x86_jump(f, default[1:])

    case "unreachable":
        append(&f.code, 0x0F, 0x0B)   // ud2

    case:
        x86_fail("the instruction", op)
    }
}

// A conversion of the value in rax, from ft to tt.
@(private="file")
x86_convert :: proc(f: ^X86_Fn, op: string, ft, tt: ^X86_Type) {
    switch op {
    case "zext":
        x86_extend(f, .AX, ft.bits, false)
    case "sext":
        x86_extend(f, .AX, ft.bits, true)
    case "trunc":
        if tt.bits == 1 { x86_ri(f, 4, 4, .AX, 1) }
    case "fpext", "fptrunc":
        if !x86_float(ft) || !x86_float(tt) { x86_fail("a conversion", op) }
        x86_to_xmm(f, 0, .AX)
        x86_sse(f, x86_fpre(ft), false, 0x5A, 0, 0)   // cvtss2sd / cvtsd2ss
        x86_from_xmm(f, .AX, 0)
    case "sitofp":
        x86_extend(f, .AX, ft.bits, true)
        x86_sse(f, x86_fpre(tt), true, 0x2A, 0, u8(X86_Reg.AX))   // cvtsi2s? xmm0, rax
        x86_from_xmm(f, .AX, 0)
    case "uitofp":
        x86_extend(f, .AX, ft.bits, false)
        if ft.bits < 64 {   // (below 2^63: as a signed one)
            x86_sse(f, x86_fpre(tt), true, 0x2A, 0, u8(X86_Reg.AX))
        } else {
            // Its top bit set: half of it (the low bit kept, for rounding),
            // converted, doubled.
            big, done := x86_label(f), x86_label(f)
            x86_rr(f, 8, 0x84, .AX, .AX)   // test rax, rax
            x86_jump(f, big, X86_CC.S)
            x86_sse(f, x86_fpre(tt), true, 0x2A, 0, u8(X86_Reg.AX))
            x86_jump(f, done)
            x86_place(f, big)
            x86_mov(f, .CX, .AX)
            x86_enc_rr(f, 0, true, {0xD1}, 5, u8(X86_Reg.CX))   // shr rcx, 1
            x86_ri(f, 4, 4, .AX, 1)
            x86_rr(f, 8, 0x08, .CX, .AX)
            x86_sse(f, x86_fpre(tt), true, 0x2A, 0, u8(X86_Reg.CX))
            x86_sse(f, x86_fpre(tt), false, 0x58, 0, 0)   // add xmm0, xmm0
            x86_place(f, done)
        }
        x86_from_xmm(f, .AX, 0)
    case "fptosi", "fptoui":
        x86_to_xmm(f, 0, .AX)
        if op == "fptosi" || tt.bits < 64 {   // (below 2^63: as a signed one)
            x86_sse(f, x86_fpre(ft), true, 0x2C, u8(X86_Reg.AX), 0)   // cvtts?2si rax, xmm0
            return
        }
        // 2^63 and past: less 2^63, converted, its top bit set.
        big, done := x86_label(f), x86_label(f)
        x86_imm(f, .CX, transmute(i64)u64(0x43E0000000000000) if ft.kind == .F64 else 0x5F000000)
        x86_to_xmm(f, 1, .CX)
        x86_sse(f, 0 if ft.kind == .F32 else 0x66, false, 0x2E, 0, 1)   // ucomis xmm0, xmm1
        x86_jump(f, big, X86_CC.AE)
        x86_sse(f, x86_fpre(ft), true, 0x2C, u8(X86_Reg.AX), 0)
        x86_jump(f, done)
        x86_place(f, big)
        x86_sse(f, x86_fpre(ft), false, 0x5C, 0, 1)   // sub xmm0, xmm1
        x86_sse(f, x86_fpre(ft), true, 0x2C, u8(X86_Reg.AX), 0)
        x86_enc_rr(f, 0, true, {0x0F, 0xBA}, 7, u8(X86_Reg.AX))   // btc rax, 63
        append(&f.code, 63)
        x86_place(f, done)
    case "ptrtoint", "inttoptr", "bitcast":
    }
}

// A call, by the Win64 convention: the first four arguments in rcx, rdx, r8,
// r9 — a float in xmm0–3, and its bits in the integer register too, for a
// variadic callee — the rest on the stack past the 32-byte home area; the
// result in rax or xmm0.
@(private="file")
x86_call :: proc(f: ^X86_Fn, callee: string, rt: ^X86_Type, args: []X86_Arg, dest: string) {
    for a, i in args {
        if i < 4 { continue }
        x86_get(f, a.v, .AX)
        x86_store(f, {base = X86_SP, disp = i32(32 + 8 * (i - 4))}, .AX, 8)
    }
    for a, i in args {
        if i >= 4 { break }
        x86_get(f, a.v, X86_ARGS[i])
        if x86_float(a.t) { x86_to_xmm(f, u8(i), X86_ARGS[i]) }
    }
    if callee[0] == '@' {
        x86_call_sym(f, x86_sym(callee[1:]))
    } else {   // a function value
        x86_get(f, {kind = .Local, name = callee}, .R11)
        append(&f.code, 0x41, 0xFF, 0xD3)   // call r11
    }
    if rt.kind == .Void || dest == "" { return }
    if x86_float(rt) { x86_from_xmm(f, .AX, 0) }
    x86_put(f, dest)
}

// An LLVM intrinsic: the machine's instruction for it, or the C library's
// function.
@(private="file")
x86_intrinsic :: proc(f: ^X86_Fn, name: string, rt: ^X86_Type, args: []X86_Arg, dest: string) {
    op := name
    if dot := strings.index_byte(name, '.'); dot >= 0 { op = name[:dot] }
    switch op {
    case "memcpy":
        x86_get(f, args[0].v, .DI)
        x86_get(f, args[1].v, .SI)
        x86_get(f, args[2].v, .CX)
        append(&f.code, 0xF3, 0xA4)   // rep movsb
    case "memset":
        x86_get(f, args[0].v, .DI)
        x86_get(f, args[1].v, .AX)
        x86_get(f, args[2].v, .CX)
        append(&f.code, 0xF3, 0xAA)   // rep stosb
    case "sadd", "uadd", "ssub", "usub", "smul", "umul":
        // The result and whether it overflowed, as a { iN, i1 }.
        t := args[0].t
        n := t.size
        x86_get(f, args[0].v, .AX)
        x86_get(f, args[1].v, .CX)
        switch op {
        case "sadd", "uadd": x86_rr(f, n, 0x00, .AX, .CX)
        case "ssub", "usub": x86_rr(f, n, 0x28, .AX, .CX)
        case "smul":
            if n == 1 { x86_grp3(f, 1, 5, .CX) } else { x86_enc_rr(f, x86_pre(n), n == 8, {0x0F, 0xAF}, u8(X86_Reg.AX), u8(X86_Reg.CX)) }
        case "umul":
            x86_grp3(f, n, 4, .CX)
        }
        x86_setcc(f, .B if op == "uadd" || op == "usub" else .O, .DX)
        s := x86_slot(f, dest, rt.size, rt.align)
        x86_store(f, x86_mem(f, s, 0), .AX, n)
        x86_store(f, x86_mem(f, s, rt.offsets[1]), .DX, 1)
    case "smin", "smax", "umin", "umax":
        t := args[0].t
        x86_get(f, args[0].v, .AX)
        x86_get(f, args[1].v, .CX)
        x86_rr(f, t.size, 0x38, .AX, .CX)
        cc: X86_CC
        switch op {
        case "smin": cc = .G   // a > b: b
        case "smax": cc = .L
        case "umin": cc = .A
        case "umax": cc = .B
        }
        x86_cmov(f, cc, .AX, .CX)
        x86_put(f, dest)
    case "bswap":
        x86_get(f, args[0].v, .AX)
        switch args[0].t.size {
        case 2:   // rol ax, 8
            x86_enc_rr(f, 0x66, false, {0xC1}, 0, u8(X86_Reg.AX))
            append(&f.code, 8)
        case 4: append(&f.code, 0x0F, 0xC8)
        case 8: append(&f.code, 0x48, 0x0F, 0xC8)
        case:   x86_fail("a byte swap", name)
        }
        x86_put(f, dest)
    case "sqrt":
        x86_get(f, args[0].v, .AX)
        x86_to_xmm(f, 0, .AX)
        x86_sse(f, x86_fpre(args[0].t), false, 0x51, 0, 0)
        x86_from_xmm(f, .AX, 0)
        x86_put(f, dest)
    case "fabs":
        x86_get(f, args[0].v, .AX)
        if args[0].t.kind == .F32 {
            x86_ri(f, 4, 4, .AX, 0x7fffffff)
        } else {
            x86_enc_rr(f, 0, true, {0x0F, 0xBA}, 6, u8(X86_Reg.AX))   // btr rax, 63
            append(&f.code, 63)
        }
        x86_put(f, dest)
    case "floor", "ceil", "trunc":
        // (roundss/roundsd: 1 down, 2 up, 3 toward zero; 8, no precision
        // exception.)
        x86_get(f, args[0].v, .AX)
        x86_to_xmm(f, 0, .AX)
        x86_enc_rr(f, 0x66, false, {0x0F, 0x3A, 0x0A if args[0].t.kind == .F32 else 0x0B}, 0, 0)
        append(&f.code, 9 if op == "floor" else 10 if op == "ceil" else 11)
        x86_from_xmm(f, .AX, 0)
        x86_put(f, dest)
    case "sin", "cos", "tan", "asin", "acos", "atan", "atan2", "pow", "exp", "exp2", "log", "log2", "log10", "minnum", "maxnum", "fma", "round":
        c := op
        switch op {
        case "minnum": c = "fmin"
        case "maxnum": c = "fmax"
        }
        if args[0].t.kind == .F32 { c = strings.concatenate({c, "f"}) }
        x86_call(f, strings.concatenate({"@", c}), rt, args, dest)
    case:
        x86_fail("the intrinsic", name)
    }
}

// --- data --------------------------------------------------------------------------

// A global: its section, its alignment, its symbol, its bytes. (An external
// one is another object's: a name its uses link to.)
@(private="file")
x86_global :: proc(m: ^X86_Module, line: string) {
    x86_line = line
    l := X86_Lex{line, 0}
    name := x86_word(&l)
    x86_eat(&l, '=')
    local, constant := false, false
    words: for {
        save := l.i
        switch x86_word(&l) {
        case "private", "internal": local = true
        case "unnamed_addr", "local_unnamed_addr", "dso_local":
        case "external":            return
        case "constant":
            constant = true
            break words
        case "global":
            break words
        case:
            l.i = save
            break words
        }
    }
    t := x86_type(m.p, x86_type_text(&l))
    align := t.align
    if !strings.has_suffix(line, "\"") {
        if a := strings.last_index(line, ", align "); a >= 0 { align = max(align, x86_atoi(line[a + 8:])) }
    }
    zero := false
    {
        save := l.i
        zero = x86_word(&l) == "zeroinitializer"
        l.i = save
    }
    sym := x86_sym(name[1:])
    if zero && !constant {   // .bss: its room, no bytes
        m.bss = x86_align(m.bss, max(align, 1))
        x86_define(m, sym, .Bss, m.bss, !local, false)
        m.bss += t.size
        return
    }
    sec: X86_Sec = .Rdata if constant else .Data
    x86_pad(&m.sec[sec], max(align, 1))
    x86_define(m, sym, sec, len(m.sec[sec]), !local, false)
    x86_data(m, sec, t, &l)
}

// A constant of type t, as bytes in sec.
@(private="file")
x86_data :: proc(m: ^X86_Module, sec: X86_Sec, t: ^X86_Type, l: ^X86_Lex) {
    b := &m.sec[sec]
    if x86_is(l, "zeroinitializer") || x86_is(l, "undef") || x86_is(l, "poison") {
        for _ in 0 ..< t.size { append(b, 0) }
        return
    }
    switch t.kind {
    case .Void:
    case .Int, .F16, .F32, .F64:
        v := x86_value(l, t)
        n := u64(v.n)
        for k in 0 ..< min(t.size, 8) { append(b, u8(n >> uint(8 * k))) }
        for _ in 8 ..< t.size { append(b, 0xFF if v.n < 0 else 0) }
    case .Ptr:
        sym: u32
        off := 0
        switch {
        case x86_is(l, "null"):
            x86_u64(b, 0)
            return
        case x86_is(l, "getelementptr"):
            // An address into a global: its symbol, at the offset its
            // constant indices reach.
            x86_is(l, "inbounds")
            x86_eat(l, '(')
            cur := x86_type(m.p, x86_type_text(l))
            x86_eat(l, ',')
            x86_type_text(l)
            sym = x86_symbol(m, x86_sym(x86_word(l)[1:]))
            first := true
            for x86_eat(l, ',') {
                x86_type_text(l)
                k := x86_atoi(x86_word(l))
                switch {
                case first:
                    off += k * cur.size
                    first = false
                case cur.kind == .Struct:
                    off += cur.offsets[k]
                    cur = cur.fields[k]
                case:
                    off += k * cur.elem.size
                    cur = cur.elem
                }
            }
            x86_eat(l, ')')
        case:
            w := x86_word(l)
            if len(w) == 0 || w[0] != '@' { x86_fail("a pointer's value", w) }
            sym = x86_symbol(m, x86_sym(w[1:]))
        }
        append(&m.relocs[sec], X86_Reloc{u32(len(b)), sym, X86_ADDR64})
        x86_u64(b, u64(off))
    case .Array:
        if x86_at(l, 'c') {   // c"…", its bytes (\XX for those not written as they are)
            l.i += 2
            n := 0
            for l.i < len(l.s) && l.s[l.i] != '"' {
                c := l.s[l.i]
                if c == '\\' {
                    u, _ := strconv.parse_u64_of_base(l.s[l.i + 1:l.i + 3], 16)
                    c = u8(u)
                    l.i += 3
                } else {
                    l.i += 1
                }
                append(b, c)
                n += 1
            }
            l.i += 1
            for _ in n ..< t.size { append(b, 0) }
            return
        }
        x86_eat(l, '[')
        for k in 0 ..< t.count {
            if k > 0 { x86_eat(l, ',') }
            x86_type_text(l)
            x86_data(m, sec, t.elem, l)
        }
        x86_eat(l, ']')
    case .Struct:
        packed := x86_eat(l, '<')
        x86_eat(l, '{')
        start := len(b)
        for ft, k in t.fields {
            if k > 0 { x86_eat(l, ',') }
            for len(b) - start < t.offsets[k] { append(b, 0) }
            x86_type_text(l)
            x86_data(m, sec, ft, l)
        }
        x86_eat(l, '}')
        if packed { x86_eat(l, '>') }
        for len(b) - start < t.size { append(b, 0) }
    }
}

// --- the object --------------------------------------------------------------------

// The module as a COFF object: its header, its sections' headers, their
// bytes and relocations, its symbols and their names.
@(private="file")
x86_coff :: proc(m: ^X86_Module, out: ^[dynamic]u8) {
    // Each symbol's index: a section's own takes two (its aux record).
    index := make([]u32, len(m.syms))
    n := u32(0)
    for s, i in m.syms {
        index[i] = n
        n += 2 if s.section else 1
    }
    secs := len(X86_Sec)
    // The layout: the headers, then each section's bytes and relocations.
    pos := 20 + 40 * secs
    raw, rel: [X86_Sec]int
    nrel: [X86_Sec]int
    for s in X86_Sec {
        if int(s) >= secs { break }
        nrel[s] = len(m.relocs[s])
        if nrel[s] > 0xFFFF { nrel[s] += 1 }   // (past 65535: the count is the first one's)
        if s != .Bss && len(m.sec[s]) > 0 {
            raw[s] = pos
            pos += len(m.sec[s])
        }
        if nrel[s] > 0 {
            rel[s] = pos
            pos += 10 * nrel[s]
        }
    }
    symtab := pos
    strtab := make([dynamic]u8)
    x86_u32(&strtab, 0)   // (its size, set when it's done)
    name8 :: proc(b: ^[dynamic]u8, strtab: ^[dynamic]u8, name: string) {
        if len(name) <= 8 {
            append(b, name)
            for _ in len(name) ..< 8 { append(b, 0) }
            return
        }
        x86_u32(b, 0)
        x86_u32(b, u32(len(strtab)))
        append(strtab, name)
        append(strtab, 0)
    }

    b := out
    x86_u16(b, 0x8664)   // AMD64
    x86_u16(b, u16(secs))
    x86_u32(b, 0)
    x86_u32(b, u32(symtab))
    x86_u32(b, n)
    x86_u16(b, 0)
    x86_u16(b, 0)
    for s in X86_Sec {
        if int(s) >= secs { break }
        name8(b, &strtab, X86_SEC_NAME[s])
        x86_u32(b, 0)   // (its virtual size and address: an image's)
        x86_u32(b, 0)
        x86_u32(b, u32(m.bss if s == .Bss else len(m.sec[s])))
        x86_u32(b, u32(raw[s]))
        x86_u32(b, u32(rel[s]))
        x86_u32(b, 0)
        x86_u16(b, u16(min(nrel[s], 0xFFFF)))
        x86_u16(b, 0)
        x86_u32(b, X86_SEC_FLAGS[s] | (0x01000000 if nrel[s] > 0xFFFF else 0))
    }
    for s in X86_Sec {
        if int(s) >= secs { break }
        if s != .Bss { append(b, ..m.sec[s][:]) }
        if nrel[s] > 0xFFFF {
            x86_u32(b, u32(nrel[s]))
            x86_u32(b, 0)
            x86_u16(b, 0)
        }
        for r in m.relocs[s] {
            x86_u32(b, r.at)
            x86_u32(b, index[r.sym])
            x86_u16(b, r.kind)
        }
    }
    for s in m.syms {
        name8(b, &strtab, s.name)
        x86_u32(b, s.value)
        x86_u16(b, u16(s.sec))
        x86_u16(b, 0x20 if s.fn else 0)
        append(b, 2 if s.global || s.sec == 0 else 3)   // external, or static
        if !s.section {
            append(b, 0)
            continue
        }
        // A section's: its aux record — its length, its relocations.
        sec := X86_Sec(s.sec - 1)
        append(b, 1)
        x86_u32(b, u32(m.bss if sec == .Bss else len(m.sec[sec])))
        x86_u16(b, u16(min(nrel[sec], 0xFFFF)))
        x86_u16(b, 0)
        x86_u32(b, 0)
        x86_u16(b, 0)
        append(b, 0, 0, 0, 0)
    }
    x86_put32(strtab[:], 0, u32(len(strtab)))
    append(b, ..strtab[:])
}
