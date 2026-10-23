package mara

import "base:runtime"
import "core:fmt"
import "core:os"
import "core:strings"

// ---------------------------------------------------------------------------
// The x86-64 backend (Windows). Each function's low-level instructions — what
// llvm.odin and the emit helpers make of it (ir.odin: the LLVM subset, no
// phi, its values and labels data) — encoded as x86-64 machine code as the
// function is made, and the module's globals as their bytes, into its COFF
// object, which lld links. It reads no text: types are laid out from their
// structure (ir.odin's table). It decides
// nothing about the program: every check, layout and conversion is in the
// instructions already; what's here is how each one is done on the machine.
//
// Every value has a slot in its function's frame; an instruction loads what
// it uses into registers, does its work and stores its result. An address in
// a local's memory at a constant offset is no value at all, but the memory
// its loads and stores name. Calls follow the Win64 convention, Mara's and
// C's alike; each function has unwind info (.pdata, .xdata) and one epilogue
// its returns jump to.
// ---------------------------------------------------------------------------

// A type's layout, as the IR's types lay out on x86-64 (x86_layout).
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

// The object's sections, in its section table's order: the debug info's
// last, left out when empty (codeview.odin).
@(private="file")
X86_Sec :: enum u8 { Text, Data, Bss, Rdata, Pdata, Xdata, Drectve, Debug_S, Debug_T, Raddbg }

@(private="file") X86_SEC_NAME := [X86_Sec]string{.Text = ".text", .Data = ".data", .Bss = ".bss", .Rdata = ".rdata", .Pdata = ".pdata", .Xdata = ".xdata", .Drectve = ".drectve",
                                                    .Debug_S = ".debug$S", .Debug_T = ".debug$T", .Raddbg = ".raddbg"}
@(private="file") X86_SEC_FLAGS := [X86_Sec]u32{
    .Text    = 0x60500020,   // code, 16-aligned, execute, read
    .Data    = 0xC0500040,   // initialized data, 16-aligned, read, write
    .Bss     = 0xC0500080,   // uninitialized data, 16-aligned, read, write
    .Rdata   = 0x40500040,   // initialized data, 16-aligned, read
    .Pdata   = 0x40300040,   // ... 4-aligned
    .Xdata   = 0x40300040,
    .Drectve = 0x00100A00,   // linker directives, removed from the image
    .Debug_S = 0x42100040,   // ... 1-aligned, read, discarded from the image (the PDB's)
    .Debug_T = 0x42100040,
    .Raddbg  = 0xC0100040,   // ... read, write: raddbg's type views
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

// The types' layouts, as one worker asks for them (the table of types is the
// program's; each worker lays out the ones it meets, itself).
X86_Program :: struct {
    keep:    runtime.Allocator,
    layouts: [dynamic]^X86_Type,    // by type id; nil until asked for
    i1, i8, i16, i32, i64, ptr, f32, f64, void: ^X86_Type,   // (the common ones, at hand)
}

// One module's object, as its functions and globals go in.
X86_Module :: struct {
    p:       ^X86_Program,
    keep:    runtime.Allocator,      // (what outlives one function)
    sec:     [X86_Sec][dynamic]u8,
    relocs:  [X86_Sec][dynamic]X86_Reloc,
    bss:     int,                    // .bss's size
    syms:    [dynamic]X86_Sym,
    sym_of:  map[string]u32,
    exports: [dynamic]string,        // dllexport functions
    cv:      ^Cv_Module,             // its debug info (codeview.odin); nil, none
}

// A value: a local — a temporary (an instruction's result) by its number, a
// named one (a param, an alloca's address) by its name — a global's address,
// a number (a float's bits), or zero.
@(private="file")
X86_Val_Kind :: enum u8 { Zero, Int, Temp, Local, Global }

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
    label: i32,      // an Ir_Label's id; less than 0, the backend's own (X86_EXIT, x86_label)
}

@(private="file") X86_EXIT :: -1   // the function's epilogue

// One function's translation: its body's code, made before its prologue
// (which needs the frame's size).
@(private="file")
X86_Fn :: struct {
    m:      ^X86_Module,
    code:   [dynamic]u8,
    relocs: [dynamic]X86_Reloc,
    slots:  map[string]X86_Slot,  // the named locals'
    temps:  [dynamic]X86_Slot,    // the temporaries', by number: most of them
    labels: [dynamic]int,         // where each label is, by id (-1: not yet)
    own:    [dynamic]int,         // the backend's own labels', by -id
    fixups: [dynamic]X86_Fixup,
    lines:  [dynamic]Cv_Line,     // where each source line's code starts (Ir .Line), for the debug info
    out:    int,     // the outgoing arguments' area, at the frame's bottom
    top:    int,     // the slots' bytes so far, above it
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

// What the backend can't translate: an error, not a guess — with what it was
// reading: an instruction, or a line (a global's, a function's head).
@(private="file", thread_local) x86_line: string
@(private="file", thread_local) x86_ins: ^Ir

@(private="file")
x86_fail :: proc(what, part: string) -> ! {
    at := strings.trim_space(x86_line)
    if x86_ins != nil {
        b := strings.builder_make()
        ir_print(&b, x86_ins^)
        at = strings.trim_space(strings.to_string(b))
    }
    fmt.eprintf("x86 backend: can't translate %s (%s) in: %s\n(`mara build -llvm` builds it with LLVM)\n", what, strings.trim_space(part), at)
    os.exit(1)
}

// --- a module ----------------------------------------------------------------------

// A worker's layouts of the program's types.
x86_program :: proc() -> ^X86_Program {
    p := new(X86_Program)
    p.keep = context.allocator
    p.layouts = make([dynamic]^X86_Type)
    p.i1, p.i8, p.i16, p.i32, p.i64 = x86_layout(p, IR_I1), x86_layout(p, IR_I8), x86_layout(p, IR_I16), x86_layout(p, IR_I32), x86_layout(p, IR_I64)
    p.ptr, p.f32, p.f64, p.void = x86_layout(p, IR_PTR), x86_layout(p, IR_FLOAT), x86_layout(p, IR_DOUBLE), x86_layout(p, IR_VOID)
    return p
}

// A module's object, begun: its functions (x86_function) and globals
// (x86_global) go in as they're made; x86_finish writes it. With the
// program, its debug info too.
x86_begin :: proc(p: ^X86_Program, debug: ^Checked_Program = nil, name := "") -> ^X86_Module {
    m := new(X86_Module)
    m.p, m.keep = p, context.allocator
    if debug != nil { m.cv = cv_begin(debug, name) }
    m.sym_of = make(map[string]u32)
    m.exports = make([dynamic]string)
    for s in X86_Sec {
        m.sec[s] = make([dynamic]u8)
        m.relocs[s] = make([dynamic]X86_Reloc)
        append(&m.syms, X86_Sym{name = X86_SEC_NAME[s], sec = int(s) + 1, section = true})
    }
    return m
}

// The module's object, written into `out`: its exports' directives, then
// the COFF.
x86_finish :: proc(m: ^X86_Module, out: ^[dynamic]u8) {
    for name in m.exports {
        append(&m.sec[.Drectve], " /EXPORT:")
        append(&m.sec[.Drectve], name)
    }
    if m.cv != nil {
        cv_finish(m.cv)
        append(&m.sec[.Debug_S], ..m.cv.sym[:])
        append(&m.sec[.Debug_T], ..m.cv.types[:])
        for r in m.cv.relocs { append(&m.relocs[.Debug_S], X86_Reloc{r.at, r.sym, r.kind}) }
    }
    x86_coff(m, out)
}

// raddbg's type views (codeview.odin), into the object's .raddbg: each one
// zero-ended, after a zero (the byte raddbg once marked itself attached in).
x86_raddbg :: proc(m: ^X86_Module, views: []string) {
    b := &m.sec[.Raddbg]
    append(b, 0)
    for v in views {
        append(b, v)
        append(b, 0)
    }
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

// --- types ---------------------------------------------------------------------------

// A type's layout: laid out when first asked for — an array's elements, a
// struct's fields at their alignments (packed: none), a named one's body.
@(private="file")
x86_layout :: proc(p: ^X86_Program, t: Ir_Type) -> ^X86_Type {
    if int(t) < len(p.layouts) {
        if l := p.layouts[t]; l != nil { return l }
    }
    info := ir_type_info(t)
    l := new(X86_Type, p.keep)
    switch info.kind {
    case .None, .Sig: x86_fail("a type", info.text)
    case .Vector:     x86_fail("a vector type", info.text)
    case .Void:   l^ = {kind = .Void, align = 1}
    case .Ptr:    l^ = {kind = .Ptr, size = 8, align = 8}
    case .Half:   l^ = {kind = .F16, size = 2, align = 2}
    case .Float:  l^ = {kind = .F32, size = 4, align = 4}
    case .Double: l^ = {kind = .F64, size = 8, align = 8}
    case .Int:
        size := 1
        for size * 8 < info.n { size *= 2 }
        l^ = {kind = .Int, bits = info.n, size = size, align = size}
    case .Array:
        elem := x86_layout(p, info.elem)
        l^ = {kind = .Array, elem = elem, count = info.n, size = elem.size * info.n, align = elem.align}
    case .Struct:
        fields := make([]^X86_Type, len(info.fields), p.keep)
        offsets := make([]int, len(info.fields), p.keep)
        size, align := 0, 1
        for ft, k in info.fields {
            f := x86_layout(p, ft)
            a := 1 if info.packed else f.align
            size = x86_align(size, a)
            fields[k], offsets[k] = f, size
            size += f.size
            align = max(align, a)
        }
        l^ = {kind = .Struct, fields = fields, offsets = offsets, size = x86_align(size, align), align = align}
    case .Named:
        l^ = x86_layout(p, info.elem)^
    }
    for len(p.layouts) <= int(t) { append(&p.layouts, nil) }
    p.layouts[t] = l
    return l
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

// An operand of type t: a local or a global as itself, a constant as its
// bits — a float's value as a double's made a float's when t is one. (An int
// wider than 64 bits: its low ones.)
@(private="file")
x86_val :: proc(v: Val, t: ^X86_Type) -> X86_Val {
    switch v.kind {
    case .None, .Null, .Zero, .Fzero: return {}
    case .Temp:   return {kind = .Temp, n = i64(v.n)}
    case .Local:  return {kind = .Local, name = v.name}
    case .Global: return {kind = .Global, name = v.name}
    case .Int, .Bool, .Half: return {kind = .Int, n = i64(v.n)}
    case .Float:
        u := u64(v.n)
        if t != nil && t.kind == .F32 { u = u64(transmute(u32)f32(transmute(f64)u)) }
        return {kind = .Int, n = transmute(i64)u}
    }
    return {}
}

// Whether a value is a local's: in its slot.
@(private="file")
x86_local :: proc(v: X86_Val) -> bool {
    return v.kind == .Temp || v.kind == .Local
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
x86_jump :: proc(f: ^X86_Fn, label: i32, cc: Maybe(X86_CC) = nil) {
    if c, conditional := cc.?; conditional {
        append(&f.code, 0x0F, 0x80 + u8(c))
    } else {
        append(&f.code, 0xE9)
    }
    append(&f.fixups, X86_Fixup{len(f.code), label})
    x86_u32(&f.code, 0)
}

@(private="file")
x86_place :: proc(f: ^X86_Fn, label: i32) {
    at := &f.labels
    k := int(label)
    if label < 0 { at, k = &f.own, int(-label) }
    for len(at^) <= k { append(at, -1) }
    at^[k] = len(f.code)
}

// A label of the code's own making (from -2: -1 is the exit's).
@(private="file")
x86_label :: proc(f: ^X86_Fn) -> i32 {
    for len(f.own) < 2 { append(&f.own, -1) }
    append(&f.own, -1)
    return -i32(len(f.own) - 1)
}

@(private="file")
x86_call_sym :: proc(f: ^X86_Fn, name: string) {
    append(&f.code, 0xE8)
    append(&f.relocs, X86_Reloc{u32(len(f.code)), x86_symbol(f.m, name), X86_REL32})
    x86_u32(&f.code, 0)
}

// --- a function --------------------------------------------------------------------

// A function into the module's object: its head, its code's parts in order
// (codegen_function); for its debug info, what the emitter says of it.
x86_function :: proc(m: ^X86_Module, head: Ir_Head, code: [][]Ir, dbg: ^Dbg_Fun = nil) {
    x86_line, x86_ins = head.name, nil
    sym := x86_sym(head.name)
    f := X86_Fn{m = m}
    f.out = x86_out_area(code)
    f.slots = make(map[string]X86_Slot)
    f.temps = make([dynamic]X86_Slot)
    f.labels = make([dynamic]int)
    f.own = make([dynamic]int)
    params := make([dynamic]X86_Arg)
    for x in head.params {
        v := x86_val(x.v, nil)
        x86_slot(&f, v, 8, 8)
        append(&params, X86_Arg{x86_layout(m.p, x.ty), v})
    }
    for part in code {
        for &ins in part { x86_inst(&f, &ins) }
    }
    x86_ins = nil

    // Its frame: the outgoing arguments, then the slots — rsp 16-aligned
    // after the two pushes and the allocation. Its one epilogue.
    frame := x86_align(f.out + f.top, 16) + 8
    x86_place(&f, X86_EXIT)
    append(&f.code, 0x48, 0x81, 0xC4)   // add rsp, frame
    x86_u32(&f.code, u32(frame))
    append(&f.code, 0x5F, 0x5E, 0xC3)   // pop rdi; pop rsi; ret
    for fx in f.fixups {
        at, k := f.labels[:], int(fx.label)
        if fx.label < 0 { at, k = f.own[:], int(-fx.label) }
        if k >= len(at) || at[k] < 0 { x86_fail("a jump to no label", fmt.tprint(fx.label)) }
        x86_put32(f.code[:], fx.at, u32(i32(at[k] - (fx.at + 4))))
    }

    // Its prologue: rsi and rdi pushed (rep movs/stos use them), the frame
    // allocated — past a page, each one touched in order (__chkstk).
    text := &m.sec[.Text]
    x86_pad(text, 16, 0xCC)
    start := len(text)
    x86_define(m, sym, .Text, start, true, true)
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
            at := x86_mem(&f, x86_find(&f, p.v)^, 0)
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
    if head.export { append(&m.exports, strings.clone(sym, m.keep)) }
    if m.cv != nil { x86_debug(&f, sym, dbg, start, base, end, frame) }
}

// A function's debug info: its variables where its frame has them — a
// local's memory, or a slot holding its value or its address — and its
// lines, from its definition's at its start.
@(private="file")
x86_debug :: proc(f: ^X86_Fn, sym: string, dbg: ^Dbg_Fun, start, base, end, frame: int) {
    m := f.m
    vars := make([dynamic]Cv_Var, context.temp_allocator)
    lines := make([dynamic]Cv_Line, context.temp_allocator)
    name := sym
    if dbg != nil {
        name = dbg.name
        for v in dbg.vars {
            s := x86_find(f, x86_val(v.at, nil))
            if s == nil { continue }
            append(&vars, Cv_Var{v.name, v.type_, f.out + s.off, v.addr && !s.memory})
        }
        if dbg.line > 0 { append(&lines, Cv_Line{0, u32(dbg.line), u16(dbg.file)}) }
    }
    for l in f.lines {
        l := l
        l.at += u32(base - start)
        if n := len(lines); n > 0 {
            last := &lines[n - 1]
            if last.at == l.at { last^ = l; continue }   // (a line with no code of its own)
            if last.line == l.line && last.file == l.file { continue }
        }
        append(&lines, l)
    }
    cv_function(m.cv, name, x86_symbol(m, sym), end - start, base - start, base - start + f.own[1], frame, vars[:], lines[:])
}

// The outgoing arguments' area: the most any call passes, 8 bytes each, and
// at least the 32 the callee may keep its register arguments in; none for a
// function that calls nothing.
@(private="file")
x86_out_area :: proc(code: [][]Ir) -> int {
    most := -1
    for part in code {
        for ins in part { if ins.op == .Call { most = max(most, len(ins.args)) } }
    }
    if most < 0 { return 0 }
    return x86_align(max(32, 8 * most), 16)
}

// A local's slot, made when it's first named: memory (an alloca's), or 8
// bytes for a value (more for an aggregate's).
@(private="file")
x86_slot :: proc(f: ^X86_Fn, v: X86_Val, size, align: int, memory := false) -> X86_Slot {
    if s := x86_find(f, v); s != nil { return s^ }
    a := max(align, 1 if memory else 8)
    f.top = x86_align(f.top, a)
    s := X86_Slot{off = f.top, memory = memory, made = true}
    f.top += max(size, 1) if memory else x86_align(max(size, 8), 8)
    x86_set_slot(f, v, s)
    return s
}

// A local's slot, if it has one: a temporary's by its number, a named one's
// by its name.
@(private="file")
x86_find :: proc(f: ^X86_Fn, v: X86_Val) -> ^X86_Slot {
    if v.kind == .Temp {
        if int(v.n) < len(f.temps) && f.temps[v.n].made { return &f.temps[v.n] }
        return nil
    }
    return &f.slots[v.name] or_else nil
}

@(private="file")
x86_set_slot :: proc(f: ^X86_Fn, v: X86_Val, s: X86_Slot) {
    s := s
    s.made = true
    if v.kind == .Temp {
        n := int(v.n)
        if n >= len(f.temps) { resize(&f.temps, max(n + 1, 2 * len(f.temps))) }
        f.temps[n] = s
        return
    }
    f.slots[v.name] = s
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
    case .Temp, .Local:
        s := x86_slot(f, v, 8, 8)
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
    case .Temp, .Local:
        if s := x86_slot(f, v, 8, 8); s.memory { return x86_mem(f, s, 0) }
    case .Global:
        return {base = X86_RIP, sym = x86_symbol(f.m, x86_sym(v.name))}
    }
    x86_get(f, v, r)
    return {base = u8(r)}
}

// The result, in rax, into its slot.
@(private="file")
x86_put :: proc(f: ^X86_Fn, dest: Val) {
    if dest.kind == .None { return }
    x86_store(f, x86_mem(f, x86_slot(f, x86_val(dest, nil), 8, 8), 0), .AX, 8)
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
x86_inst :: proc(f: ^X86_Fn, ins: ^Ir) {
    m := f.m
    x86_ins = ins
    p := m.p
    dest := ins.dest
    switch ins.op {
    case .Label:
        x86_place(f, ins.l.id)

    case .Line:
        append(&f.lines, Cv_Line{u32(len(f.code)), u32(ins.a.n), u16(ins.b.n)})

    case .Alloca:
        t := x86_layout(p, ins.ty)
        x86_slot(f, x86_val(dest, nil), t.size, max(t.align, int(ins.align)), memory = true)

    case .Load:
        t := x86_layout(p, ins.ty)
        at := x86_ptr(f, x86_val(ins.a, p.ptr), .CX)
        if x86_aggregate(t) {
            x86_lea(f, .SI, at)
            x86_lea(f, .DI, x86_mem(f, x86_slot(f, x86_val(dest, nil), t.size, t.align), 0))
            x86_copy(f, t.size)
            return
        }
        x86_load(f, .AX, at, t.size)
        x86_put(f, dest)

    case .Store:
        t := x86_layout(p, ins.ty)
        v := x86_val(ins.a, t)
        at := x86_ptr(f, x86_val(ins.b, p.ptr), .DI)
        if x86_aggregate(t) {
            x86_lea(f, .DI, at)
            switch {
            case x86_local(v):
                x86_lea(f, .SI, x86_mem(f, x86_slot(f, v, t.size, t.align), 0))
                x86_copy(f, t.size)
            case v.kind == .Zero || (v.kind == .Int && v.n == 0):
                x86_zero(f, t.size)
            case:
                x86_fail("an aggregate's value", "")
            }
            return
        }
        x86_get(f, v, .AX)
        if t.kind == .Int && t.bits == 1 { x86_ri(f, 4, 4, .AX, 1) }   // (a bool: 0 or 1)
        x86_store(f, at, .AX, t.size)

    case .Gep:
        base := x86_val(ins.a, p.ptr)
        // Its constant offset, and the variable indices scaled.
        Scaled :: struct { t: ^X86_Type, v: X86_Val, scale: int }
        vars := make([dynamic]Scaled, context.temp_allocator)
        off := 0
        cur := x86_layout(p, ins.ty)
        for x, k in ins.args {
            it := x86_layout(p, x.ty)
            idx := x86_val(x.v, it)
            scale := 0
            switch {
            case k == 0:
                scale = cur.size   // (the first steps over whole Ts)
            case cur.kind == .Struct:
                if x86_local(idx) { x86_fail("a field by a variable", "") }
                off += cur.offsets[idx.n]
                cur = cur.fields[idx.n]
                continue
            case cur.kind == .Array:
                scale = cur.elem.size
                cur = cur.elem
            case:
                x86_fail("an index", "")
            }
            if x86_local(idx) { append(&vars, Scaled{it, idx, scale}) } else { off += int(idx.n) * scale }
        }
        // Into a local's memory at a constant offset: that memory, no value.
        if d := x86_val(dest, nil); len(vars) == 0 && x86_local(base) && x86_find(f, d) == nil {
            if s := x86_slot(f, base, 8, 8); s.memory {
                x86_set_slot(f, d, {off = s.off + off, memory = true})
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

    case .Bin:
        t := x86_layout(p, ins.ty)
        a, b := x86_val(ins.a, t), x86_val(ins.b, t)
        x86_get(f, a, .AX)
        x86_get(f, b, .CX)
        #partial switch ins.inst {
        case .Add: x86_rr(f, 8, 0x00, .AX, .CX)
        case .Sub: x86_rr(f, 8, 0x28, .AX, .CX)
        case .And: x86_rr(f, 8, 0x20, .AX, .CX)
        case .Or:  x86_rr(f, 8, 0x08, .AX, .CX)
        case .Xor: x86_rr(f, 8, 0x30, .AX, .CX)
        case .Mul: x86_enc_rr(f, 0, true, {0x0F, 0xAF}, u8(X86_Reg.AX), u8(X86_Reg.CX))
        case .Shl: x86_enc_rr(f, 0, true, {0xD3}, 4, u8(X86_Reg.AX))
        case .Lshr:
            x86_extend(f, .AX, t.bits, false)
            x86_enc_rr(f, 0, true, {0xD3}, 5, u8(X86_Reg.AX))
        case .Ashr:
            x86_extend(f, .AX, t.bits, true)
            x86_enc_rr(f, 0, true, {0xD3}, 7, u8(X86_Reg.AX))
        case .Sdiv, .Srem:
            x86_extend(f, .AX, t.bits, true)
            x86_extend(f, .CX, t.bits, true)
            append(&f.code, 0x48, 0x99)   // cqo
            x86_grp3(f, 8, 7, .CX)        // idiv rcx
            if ins.inst == .Srem { x86_mov(f, .AX, .DX) }
        case .Udiv, .Urem:
            x86_extend(f, .AX, t.bits, false)
            x86_extend(f, .CX, t.bits, false)
            x86_imm(f, .DX, 0)
            x86_grp3(f, 8, 6, .CX)        // div rcx
            if ins.inst == .Urem { x86_mov(f, .AX, .DX) }
        case .Fadd, .Fsub, .Fmul, .Fdiv:
            x86_to_xmm(f, 0, .AX)
            x86_to_xmm(f, 1, .CX)
            code: u8
            #partial switch ins.inst {
            case .Fadd: code = 0x58
            case .Fsub: code = 0x5C
            case .Fmul: code = 0x59
            case .Fdiv: code = 0x5E
            }
            x86_sse(f, x86_fpre(t), false, code, 0, 1)
            x86_from_xmm(f, .AX, 0)
        case:
            x86_fail("the operation", IR_INST_NAME[ins.inst])
        }
        x86_put(f, dest)

    case .Fneg:
        t := x86_layout(p, ins.ty)
        x86_get(f, x86_val(ins.a, t), .AX)
        if t.kind == .F32 {
            x86_ri(f, 4, 6, .AX, 0x80000000)   // xor eax, sign
        } else {
            x86_enc_rr(f, 0, true, {0x0F, 0xBA}, 7, u8(X86_Reg.AX))   // btc rax, 63
            append(&f.code, 63)
        }
        x86_put(f, dest)

    case .Icmp:
        t := x86_layout(p, ins.ty)
        x86_get(f, x86_val(ins.a, t), .AX)
        x86_get(f, x86_val(ins.b, t), .CX)
        x86_rr(f, t.size, 0x38, .AX, .CX)
        cc: X86_CC
        #partial switch ins.inst {
        case .Eq:  cc = .E
        case .Ne:  cc = .NE
        case .Slt: cc = .L
        case .Sle: cc = .LE
        case .Sgt: cc = .G
        case .Sge: cc = .GE
        case .Ult: cc = .B
        case .Ule: cc = .BE
        case .Ugt: cc = .A
        case .Uge: cc = .AE
        case:       x86_fail("a comparison", IR_INST_NAME[ins.inst])
        }
        x86_setcc(f, cc, .AX)
        x86_bool(f)
        x86_put(f, dest)

    case .Fcmp:
        // (Ordered: false when either is NaN — ucomis says unordered with
        // ZF, PF and CF all set; une, true then.)
        t := x86_layout(p, ins.ty)
        x86_get(f, x86_val(ins.a, t), .AX)
        x86_get(f, x86_val(ins.b, t), .CX)
        x86_to_xmm(f, 0, .AX)
        x86_to_xmm(f, 1, .CX)
        ucomis :: proc(f: ^X86_Fn, t: ^X86_Type, a, b: u8) { x86_sse(f, 0 if t.kind == .F32 else 0x66, false, 0x2E, a, b) }
        #partial switch ins.inst {
        case .Oeq:
            ucomis(f, t, 0, 1)
            x86_setcc(f, .E, .AX)
            x86_setcc(f, .NP, .CX)
            x86_rr(f, 1, 0x20, .AX, .CX)
        case .Une:
            ucomis(f, t, 0, 1)
            x86_setcc(f, .NE, .AX)
            x86_setcc(f, .P, .CX)
            x86_rr(f, 1, 0x08, .AX, .CX)
        case .Olt:
            ucomis(f, t, 1, 0)
            x86_setcc(f, .A, .AX)
        case .Ole:
            ucomis(f, t, 1, 0)
            x86_setcc(f, .AE, .AX)
        case .Ogt:
            ucomis(f, t, 0, 1)
            x86_setcc(f, .A, .AX)
        case .Oge:
            ucomis(f, t, 0, 1)
            x86_setcc(f, .AE, .AX)
        case:
            x86_fail("a float comparison", IR_INST_NAME[ins.inst])
        }
        x86_bool(f)
        x86_put(f, dest)

    case .Select:
        t := x86_layout(p, ins.ty)
        if x86_aggregate(t) { x86_fail("a select of aggregates", ir_type_text(ins.ty)) }
        x86_get(f, x86_val(ins.a, p.i1), .DX)
        x86_get(f, x86_val(ins.b, t), .AX)
        x86_get(f, x86_val(ins.c, t), .CX)
        x86_grp3(f, 1, 0, .DX)   // test dl, 1
        append(&f.code, 1)
        x86_cmov(f, .E, .AX, .CX)
        x86_put(f, dest)

    case .Cast:
        ft, tt := x86_layout(p, ins.ty), x86_layout(p, ins.to)
        x86_get(f, x86_val(ins.a, ft), .AX)
        x86_convert(f, ins.inst, ft, tt)
        x86_put(f, dest)

    case .Extract:
        at := x86_layout(p, ins.ty)
        v := x86_val(ins.a, at)
        if !x86_local(v) { x86_fail("a part of a constant", "") }
        k := int(ins.b.n)
        off, cur := 0, at
        if cur.kind == .Struct {
            off, cur = cur.offsets[k], cur.fields[k]
        } else {
            off, cur = k * cur.elem.size, cur.elem
        }
        x86_load(f, .AX, x86_mem(f, x86_slot(f, v, at.size, at.align), off), cur.size)
        x86_put(f, dest)

    case .Call:
        rt := x86_layout(p, ins.ty)
        args := make([]X86_Arg, len(ins.args), context.temp_allocator)
        for x, i in ins.args {
            t := x86_layout(p, x.ty)
            args[i] = {t, x86_val(x.v, t)}
        }
        if ins.a.kind == .Global && strings.has_prefix(ins.a.name, "llvm.") {
            x86_intrinsic(f, ins.a.name[5:], rt, args, dest)
        } else {
            x86_call(f, x86_val(ins.a, p.ptr), rt, args, dest)
        }

    case .Ret:
        t := x86_layout(p, ins.ty)
        if t.kind != .Void {
            x86_get(f, x86_val(ins.a, t), .AX)
            if x86_float(t) { x86_to_xmm(f, 0, .AX) }
        }
        x86_jump(f, X86_EXIT)

    case .Br:
        x86_jump(f, ins.l.id)

    case .Cond_Br:
        x86_get(f, x86_val(ins.a, p.i1), .AX)
        x86_grp3(f, 1, 0, .AX)   // test al, 1
        append(&f.code, 1)
        x86_jump(f, ins.l.id, X86_CC.NE)
        x86_jump(f, ins.l2.id)

    case .Switch:
        t := x86_layout(p, ins.ty)
        x86_get(f, x86_val(ins.a, t), .AX)
        for x in ins.args {
            c := x86_val(x.v, t)
            if c.n >= i64(min(i32)) && c.n <= i64(max(i32)) {
                x86_ri(f, t.size, 7, .AX, c.n)
            } else {
                x86_get(f, c, .CX)
                x86_rr(f, 8, 0x38, .AX, .CX)
            }
            x86_jump(f, x.l.id, X86_CC.E)
        }
        x86_jump(f, ins.l.id)

    case .Unreachable:
        append(&f.code, 0x0F, 0x0B)   // ud2
    }
}

// A conversion of the value in rax, from ft to tt.
@(private="file")
x86_convert :: proc(f: ^X86_Fn, op: Ir_Inst, ft, tt: ^X86_Type) {
    #partial switch op {
    case .Zext:
        x86_extend(f, .AX, ft.bits, false)
    case .Sext:
        x86_extend(f, .AX, ft.bits, true)
    case .Trunc:
        if tt.bits == 1 { x86_ri(f, 4, 4, .AX, 1) }
    case .Fpext, .Fptrunc:
        if !x86_float(ft) || !x86_float(tt) { x86_fail("a conversion", IR_INST_NAME[op]) }
        x86_to_xmm(f, 0, .AX)
        x86_sse(f, x86_fpre(ft), false, 0x5A, 0, 0)   // cvtss2sd / cvtsd2ss
        x86_from_xmm(f, .AX, 0)
    case .Sitofp:
        x86_extend(f, .AX, ft.bits, true)
        x86_sse(f, x86_fpre(tt), true, 0x2A, 0, u8(X86_Reg.AX))   // cvtsi2s? xmm0, rax
        x86_from_xmm(f, .AX, 0)
    case .Uitofp:
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
    case .Fptosi, .Fptoui:
        x86_to_xmm(f, 0, .AX)
        if op == .Fptosi || tt.bits < 64 {   // (below 2^63: as a signed one)
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
    case .Ptrtoint, .Inttoptr, .Bitcast:
    }
}

// A call, by the Win64 convention: the first four arguments in rcx, rdx, r8,
// r9 — a float in xmm0–3, and its bits in the integer register too, for a
// variadic callee — the rest on the stack past the 32-byte home area; the
// result in rax or xmm0.
@(private="file")
x86_call :: proc(f: ^X86_Fn, callee: X86_Val, rt: ^X86_Type, args: []X86_Arg, dest: Val) {
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
    if callee.kind == .Global {
        x86_call_sym(f, x86_sym(callee.name))
    } else {   // a function value
        x86_get(f, callee, .R11)
        append(&f.code, 0x41, 0xFF, 0xD3)   // call r11
    }
    if rt.kind == .Void || dest.kind == .None { return }
    if x86_float(rt) { x86_from_xmm(f, .AX, 0) }
    x86_put(f, dest)
}

// A copy's or a fill's byte count when it's a constant small enough to do
// with plain moves (up to 64 bytes).
@(private="file")
x86_small_size :: proc(v: X86_Val) -> (int, bool) {
    if v.kind != .Int || v.n <= 0 || v.n > 64 { return 0, false }
    return int(v.n), true
}

// The widest move that fits in what's left: 8, 4, 2 or 1 bytes.
@(private="file")
x86_chunk :: proc(left: int) -> int {
    switch {
    case left >= 8: return 8
    case left >= 4: return 4
    case left >= 2: return 2
    }
    return 1
}

// An LLVM intrinsic: the machine's instructions for it. (None calls the C
// library: math.mara computes sin, cos, acos and pow itself.)
@(private="file")
x86_intrinsic :: proc(f: ^X86_Fn, name: string, rt: ^X86_Type, args: []X86_Arg, dest: Val) {
    op := name
    if dot := strings.index_byte(name, '.'); dot >= 0 { op = name[:dot] }
    switch op {
    case "memcpy":
        x86_get(f, args[0].v, .DI)
        x86_get(f, args[1].v, .SI)
        // (A small copy of a known size — a slice's header, a ^[]T: a few
        // moves; `rep movsb` costs dozens of cycles before its first byte.)
        if n, small := x86_small_size(args[2].v); small {
            for off := 0; off < n; {
                size := x86_chunk(n - off)
                x86_load(f, .AX, {base = u8(X86_Reg.SI), disp = i32(off)}, size)
                x86_store(f, {base = u8(X86_Reg.DI), disp = i32(off)}, .AX, size)
                off += size
            }
            break
        }
        x86_get(f, args[2].v, .CX)
        append(&f.code, 0xF3, 0xA4)   // rep movsb
    case "memset":
        x86_get(f, args[0].v, .DI)
        // (A small run of zeros of a known size: as many stores.)
        zero := args[1].v.kind == .Zero || args[1].v.kind == .Int && args[1].v.n == 0
        if n, small := x86_small_size(args[2].v); small && zero {
            x86_rr(f, 4, 0x30, .AX, .AX)   // xor eax, eax
            for off := 0; off < n; {
                size := x86_chunk(n - off)
                x86_store(f, {base = u8(X86_Reg.DI), disp = i32(off)}, .AX, size)
                off += size
            }
            break
        }
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
        s := x86_slot(f, x86_val(dest, nil), rt.size, rt.align)
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
    case "cttz":
        // (bsf: the lowest 1 bit's place, and ZF when there's none, then the
        // width instead. A narrow value widened first, 0s above it.)
        n := args[0].t.size
        x86_get(f, args[0].v, .AX)
        switch n {
        case 1: x86_enc_rr(f, 0, false, {0x0F, 0xB6}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, al
        case 2: x86_enc_rr(f, 0, false, {0x0F, 0xB7}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, ax
        }
        x86_enc_rr(f, 0, n == 8, {0x0F, 0xBC}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // bsf
        x86_imm(f, .CX, i64(n * 8))   // (a mov: the flags left as bsf set them)
        x86_cmov(f, .E, .AX, .CX)
        x86_put(f, dest)
    case "ctlz":
        // (bsr: the highest 1 bit's place, and ZF when there's none, then -1;
        // width - 1 - place is the count, the width for 0.)
        n := args[0].t.size
        x86_get(f, args[0].v, .AX)
        switch n {
        case 1: x86_enc_rr(f, 0, false, {0x0F, 0xB6}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, al
        case 2: x86_enc_rr(f, 0, false, {0x0F, 0xB7}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, ax
        }
        x86_enc_rr(f, 0, n == 8, {0x0F, 0xBD}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // bsr
        x86_imm(f, .CX, -1)
        x86_cmov(f, .E, .AX, .CX)
        x86_imm(f, .CX, i64(n * 8 - 1))
        x86_rr(f, 8, 0x28, .CX, .AX)   // sub rcx, rax
        x86_mov(f, .AX, .CX)
        x86_put(f, dest)
    case "ctpop":
        // (popcnt: x86-64-v2, as every machine Windows 11 runs on has; the
        // backend's roundsd, SSE4.1, about as old.)
        n := args[0].t.size
        x86_get(f, args[0].v, .AX)
        switch n {
        case 1: x86_enc_rr(f, 0, false, {0x0F, 0xB6}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, al
        case 2: x86_enc_rr(f, 0, false, {0x0F, 0xB7}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // movzx eax, ax
        }
        x86_enc_rr(f, 0xF3, n == 8, {0x0F, 0xB8}, u8(X86_Reg.AX), u8(X86_Reg.AX))   // popcnt
        x86_put(f, dest)
    case "fshl", "fshr":
        // (shld/shrd: a's and b's bits as one, shifted by n modulo the width
        // — 32 or 64: shld's count for 16 bits isn't taken modulo 16.)
        n := args[0].t.size
        if n != 4 && n != 8 { x86_fail("a funnel shift narrower than 32 bits", name) }
        if op == "fshl" {
            x86_get(f, args[0].v, .AX)   // shld rax, rdx, cl: rax's bits, then rdx's
            x86_get(f, args[1].v, .DX)
        } else {
            x86_get(f, args[1].v, .AX)   // shrd rax, rdx, cl: rdx's bits, then rax's
            x86_get(f, args[0].v, .DX)
        }
        x86_get(f, args[2].v, .CX)
        x86_enc_rr(f, 0, n == 8, {0x0F, 0xA5 if op == "fshl" else 0xAD}, u8(X86_Reg.DX), u8(X86_Reg.AX))
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
    case "minnum", "maxnum":
        // (mins?/maxs? xmm0, xmm1 give xmm1 when either is a NaN: right when
        // a is, but minnum's answer for a NaN b is a — so b's checked first.)
        x86_get(f, args[0].v, .AX)
        x86_get(f, args[1].v, .CX)
        x86_to_xmm(f, 0, .AX)
        x86_to_xmm(f, 1, .CX)
        done := x86_label(f)
        x86_sse(f, 0 if args[0].t.kind == .F32 else 0x66, false, 0x2E, 1, 1)   // ucomis xmm1, xmm1
        x86_jump(f, done, X86_CC.P)
        x86_sse(f, x86_fpre(args[0].t), false, 0x5D if op == "minnum" else 0x5F, 0, 1)
        x86_place(f, done)
        x86_from_xmm(f, .AX, 0)
        x86_put(f, dest)
    case:
        x86_fail("the intrinsic", name)
    }
}

// --- data --------------------------------------------------------------------------

// A global: its section, its alignment, its symbol, its bytes. (An external
// one is another object's: a name its uses link to.)
x86_global :: proc(m: ^X86_Module, gl: Ir_Global) {
    x86_line, x86_ins = gl.name, nil
    if gl.linkage == .External { return }
    local := gl.linkage == .Private || gl.linkage == .Internal
    t := x86_layout(m.p, gl.ty)
    align := max(t.align, int(gl.align))
    sym := x86_sym(gl.name)
    if ir_const_zero(gl.init) && !gl.constant {   // .bss: its room, no bytes
        m.bss = x86_align(m.bss, max(align, 1))
        x86_define(m, sym, .Bss, m.bss, !local, false)
        m.bss += t.size
        return
    }
    sec: X86_Sec = .Rdata if gl.constant else .Data
    x86_pad(&m.sec[sec], max(align, 1))
    x86_define(m, sym, sec, len(m.sec[sec]), !local, false)
    x86_data(m, sec, t, gl.init)
}

// A constant of type t, as bytes in sec.
@(private="file")
x86_data :: proc(m: ^X86_Module, sec: X86_Sec, t: ^X86_Type, c: Ir_Const) {
    b := &m.sec[sec]
    if c.kind == .Val && (c.v.kind == .Zero || c.v.kind == .Null || c.v.kind == .Fzero) {
        for _ in 0 ..< t.size { append(b, 0) }
        return
    }
    switch t.kind {
    case .Void:
    case .Int, .F16, .F32, .F64:
        if c.kind != .Val { x86_fail("a number's value", "") }
        n := u128(c.v.n) if c.v.kind == .Int else u128(u64(x86_val(c.v, t).n))
        for k in 0 ..< t.size { append(b, u8(n >> uint(8 * k))) }
    case .Ptr:
        sym: u32
        off := 0
        #partial switch c.kind {
        case .Gep:
            // An address into a global: its symbol, at the offset its
            // constant indices reach.
            cur := x86_layout(m.p, c.src)
            sym = x86_symbol(m, x86_sym(c.v.name))
            for x, i in c.parts {
                k := int(x.v.n)
                switch {
                case i == 0:
                    off += k * cur.size
                case cur.kind == .Struct:
                    off += cur.offsets[k]
                    cur = cur.fields[k]
                case:
                    off += k * cur.elem.size
                    cur = cur.elem
                }
            }
        case .Val:
            if c.v.kind != .Global { x86_fail("a pointer's value", "") }
            sym = x86_symbol(m, x86_sym(c.v.name))
        case:
            x86_fail("a pointer's value", "")
        }
        append(&m.relocs[sec], X86_Reloc{u32(len(b)), sym, X86_ADDR64})
        x86_u64(b, u64(off))
    case .Array:
        #partial switch c.kind {
        case .Bytes:
            append(b, c.bytes)
            for _ in len(c.bytes) ..< t.size { append(b, 0) }
        case .Array:
            for part in c.parts { x86_data(m, sec, t.elem, part) }
        case:
            x86_fail("an array's value", "")
        }
    case .Struct:
        if c.kind != .Struct && c.kind != .Packed { x86_fail("a struct's value", "") }
        start := len(b)
        for ft, k in t.fields {
            for len(b) - start < t.offsets[k] { append(b, 0) }
            x86_data(m, sec, ft, c.parts[k])
        }
        for len(b) - start < t.size { append(b, 0) }
    }
}

// --- the object --------------------------------------------------------------------

// The module as a COFF object: its header, its sections' headers, their
// bytes and relocations, its symbols and their names.
@(private="file")
x86_coff :: proc(m: ^X86_Module, out: ^[dynamic]u8) {
    // Its sections: the debug info's left out when empty.
    secs := len(X86_Sec)
    for secs > int(X86_Sec.Drectve) + 1 && len(m.sec[X86_Sec(secs - 1)]) == 0 { secs -= 1 }
    // Each symbol's index: a section's own takes two (its aux record); one
    // left out, none.
    index := make([]u32, len(m.syms))
    n := u32(0)
    for s, i in m.syms {
        index[i] = n
        if s.section && s.sec > secs { continue }
        n += 2 if s.section else 1
    }
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
        if s.section && s.sec > secs { continue }
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
