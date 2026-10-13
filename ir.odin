package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// A function's low-level instructions, as data: what llvm.odin and the emit
// helpers make of each operation of the lowered program — the LLVM subset,
// no phi: allocas, loads and stores, address arithmetic, integer and float
// operations, conversions, calls, branches. Printed, they're the LLVM
// backend's IR (ir_print); read, the x86 backend's input (x86.odin).
//
// Their values are data (Val): a temporary by its number, a named local or a
// global by its name, a constant by its kind and value; a block by its label
// (Ir_Label). So are a function's head (Ir_Head) and a module's globals with
// their initializers (Ir_Global, Ir_Const). Types are as LLVM writes them:
// `i64`, `ptr`, `%class.P`, `[4 x float]`.
// ---------------------------------------------------------------------------

Ir_Op :: enum u8 {
    Label,         // l:
    Alloca,        // dest = alloca ty[, align n]
    Load,          // dest = load ty, ptr a[, align n]
    Store,         // store ty a, ptr b[, align n]
    Gep,           // dest = getelementptr [inbounds] ty, ptr a, args — each `ty v`
    Bin,           // dest = inst ty a, b
    Icmp,          // dest = icmp inst ty a, b
    Fcmp,          // dest = fcmp inst ty a, b
    Select,        // dest = select i1 a, ty b, ty c
    Cast,          // dest = inst ty a to to
    Fneg,          // dest = fneg ty a
    Extract,       // dest = extractvalue ty a, b — b, the part's index
    Call,          // [dest = ]call ty [to ]a(args) — a, the callee; to, a variadic one's signature
    Ret,           // ret ty[ a]
    Br,            // br label %l
    Cond_Br,       // br i1 a, label %l, label %l2
    Switch,        // switch ty a, label %l [ args: ty v, label %l … ]
    Unreachable,
}

Ir :: struct {
    op:       Ir_Op,
    inbounds: bool,
    align:    i32,
    inst:     Ir_Inst,     // a Bin's, a comparison's, a Cast's operation
    ty, to:   string,
    dest:     Val,
    a, b, c:  Val,
    l, l2:    Ir_Label,
    args:     []Ir_Arg,
}

// An operation: a Bin's, a comparison's predicate (Icmp: Eq…Uge; Fcmp,
// ordered: Oeq…Oge, and Une), a Cast's.
Ir_Inst :: enum u8 {
    None,
    Add, Sub, Mul, Sdiv, Udiv, Srem, Urem, And, Or, Xor, Shl, Lshr, Ashr,
    Fadd, Fsub, Fmul, Fdiv, Frem,
    Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge,
    Oeq, Une, Olt, Ole, Ogt, Oge,
    Zext, Sext, Trunc, Fpext, Fptrunc, Sitofp, Uitofp, Fptosi, Fptoui, Ptrtoint, Inttoptr, Bitcast,
}

// Each as LLVM writes it.
IR_INST_NAME := [Ir_Inst]string{
    .None = "",
    .Add = "add",
    .Sub = "sub",
    .Mul = "mul",
    .Sdiv = "sdiv",
    .Udiv = "udiv",
    .Srem = "srem",
    .Urem = "urem",
    .And = "and",
    .Or = "or",
    .Xor = "xor",
    .Shl = "shl",
    .Lshr = "lshr",
    .Ashr = "ashr",
    .Fadd = "fadd",
    .Fsub = "fsub",
    .Fmul = "fmul",
    .Fdiv = "fdiv",
    .Frem = "frem",
    .Eq = "eq",
    .Ne = "ne",
    .Slt = "slt",
    .Sle = "sle",
    .Sgt = "sgt",
    .Sge = "sge",
    .Ult = "ult",
    .Ule = "ule",
    .Ugt = "ugt",
    .Uge = "uge",
    .Oeq = "oeq",
    .Une = "une",
    .Olt = "olt",
    .Ole = "ole",
    .Ogt = "ogt",
    .Oge = "oge",
    .Zext = "zext",
    .Sext = "sext",
    .Trunc = "trunc",
    .Fpext = "fpext",
    .Fptrunc = "fptrunc",
    .Sitofp = "sitofp",
    .Uitofp = "uitofp",
    .Fptosi = "fptosi",
    .Fptoui = "fptoui",
    .Ptrtoint = "ptrtoint",
    .Inttoptr = "inttoptr",
    .Bitcast = "bitcast",
}

// A typed operand — a GEP's index, a call's argument, a param — or a
// switch's case (its value and the block it goes to).
Ir_Arg :: struct {
    ty: string,
    v:  Val,
    l:  Ir_Label,
}

// --- values ------------------------------------------------------------------------

Val_Kind :: enum u8 {
    None,     // no value (a void return's)
    Temp,     // %.t<n>: an instruction's result
    Local,    // %<name>: a param, a named alloca, a result slot
    Global,   // @<name>: a function's or a global's address
    Int,      // n
    Bool,     // true, false
    Float,    // a double's bits — a float's value as a double — written 0x<16 hex>
    Half,     // a half's bits, written 0xH<4 hex>
    Fzero,    // 0.0
    Null,
    Zero,     // zeroinitializer
}

Val :: struct {
    kind: Val_Kind,
    name: string,   // a Local's, a Global's
    n:    i128,     // a Temp's number; an Int's or a Bool's value; a Float's or a Half's bits
}

IR_NULL  :: Val{kind = .Null}
IR_ZERO  :: Val{kind = .Zero}
IR_FZERO :: Val{kind = .Fzero}
IR_TRUE  :: Val{kind = .Bool, n = 1}
IR_FALSE :: Val{kind = .Bool}

ir_int :: proc(n: int) -> Val { return {kind = .Int, n = i128(n)} }
ir_int128 :: proc(n: i128) -> Val { return {kind = .Int, n = n} }
ir_local :: proc(name: string) -> Val { return {kind = .Local, name = name} }
ir_global :: proc(name: string) -> Val { return {kind = .Global, name = name} }
ir_float :: proc(bits: u64) -> Val { return {kind = .Float, n = i128(bits)} }
ir_half :: proc(bits: u16) -> Val { return {kind = .Half, n = i128(bits)} }

// A typed operand.
ir_a :: proc(ty: string, v: Val) -> Ir_Arg { return {ty = ty, v = v} }

// --- labels ------------------------------------------------------------------------

// A block's label: its id, its function's own number for it (from 1), and its
// name — `name` then `n`, when it has one.
Ir_Label :: struct {
    id:   i32,
    n:    i32,
    name: string,
}

// A label for a block of the function being made.
ir_label :: proc(g: ^Codegen, name: string, n := -1) -> Ir_Label {
    g.label_ids += 1
    return {id = g.label_ids, n = i32(n), name = name}
}

// --- a function's head; a module's globals ----------------------------------------

// A function's `define` line: its symbol, its result's type, its params (each
// a Local), whether it's in a DLL's export table.
Ir_Head :: struct {
    name:   string,
    ret:    string,
    params: []Ir_Arg,
    export: bool,
}

Ir_Linkage :: enum u8 { Default, Private, Internal, External }

// A global: a module's own (its initializer with it), or another's
// (External: its type only).
Ir_Global :: struct {
    name:     string,
    linkage:  Ir_Linkage,
    unnamed:  bool,       // unnamed_addr: its address means nothing
    constant: bool,       // read only
    ty:       string,
    init:     Ir_Const,
    align:    i32,
}

Ir_Const_Kind :: enum u8 { Val, Bytes, Struct, Packed, Array, Gep }

// A global's initializer, or a part of one.
Ir_Const :: struct {
    kind:  Ir_Const_Kind,
    ty:    string,       // its type, where an aggregate's part writes it
    v:     Val,          // .Val: it; .Gep: the global its address is into
    src:   string,       // .Gep: the type its indices step through
    bytes: string,       // .Bytes: all of them
    parts: []Ir_Const,   // .Struct, .Packed, .Array: its parts; .Gep: its indices
}

ir_const :: proc(ty: string, v: Val) -> Ir_Const { return {kind = .Val, ty = ty, v = v} }

ir_const_zero :: proc(c: Ir_Const) -> bool { return c.kind == .Val && c.v.kind == .Zero }

// --- making instructions -----------------------------------------------------------

// An instruction into the function's code: its body while its allocas are
// hoisted (emit_alloca), else where the code is being made.
ir_emit :: proc(g: ^Codegen, ins: Ir) {
    append(&g.body if g.hoist_allocas else &g.code, ins)
}

ir_bin :: proc(g: ^Codegen, dest: Val, inst: Ir_Inst, ty: string, a, b: Val) {
    ir_emit(g, {op = .Bin, dest = dest, inst = inst, ty = ty, a = a, b = b})
}

ir_icmp :: proc(g: ^Codegen, dest: Val, pred: Ir_Inst, ty: string, a, b: Val) {
    ir_emit(g, {op = .Icmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_fcmp :: proc(g: ^Codegen, dest: Val, pred: Ir_Inst, ty: string, a, b: Val) {
    ir_emit(g, {op = .Fcmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_select :: proc(g: ^Codegen, dest, cond: Val, ty: string, a, b: Val) {
    ir_emit(g, {op = .Select, dest = dest, ty = ty, a = cond, b = a, c = b})
}

ir_cast :: proc(g: ^Codegen, dest: Val, inst: Ir_Inst, from: string, v: Val, to: string) {
    ir_emit(g, {op = .Cast, dest = dest, inst = inst, ty = from, a = v, to = to})
}

ir_fneg :: proc(g: ^Codegen, dest: Val, ty: string, v: Val) {
    ir_emit(g, {op = .Fneg, dest = dest, ty = ty, a = v})
}

ir_extract :: proc(g: ^Codegen, dest: Val, ty: string, v: Val, index: int) {
    ir_emit(g, {op = .Extract, dest = dest, ty = ty, a = v, b = ir_int(index)})
}

// `getelementptr ty, ptr base, <index>…`.
ir_gep :: proc(g: ^Codegen, dest: Val, ty: string, base: Val, indices: ..Ir_Arg) {
    ir_emit(g, {op = .Gep, dest = dest, ty = ty, a = base, args = ir_indices(..indices)})
}

ir_gep_inbounds :: proc(g: ^Codegen, dest: Val, ty: string, base: Val, indices: ..Ir_Arg) {
    ir_emit(g, {op = .Gep, inbounds = true, dest = dest, ty = ty, a = base, args = ir_indices(..indices)})
}

// Operands kept: a variadic call's are the caller's, gone when it returns.
ir_indices :: proc(xs: ..Ir_Arg) -> []Ir_Arg {
    out := make([]Ir_Arg, len(xs))
    copy(out, xs)
    return out
}

ir_load :: proc(g: ^Codegen, dest: Val, ty: string, ptr: Val, align: i32 = 0) {
    ir_emit(g, {op = .Load, dest = dest, ty = ty, a = ptr, align = align})
}

ir_store :: proc(g: ^Codegen, ty: string, v, ptr: Val, align: i32 = 0) {
    ir_emit(g, {op = .Store, ty = ty, a = v, b = ptr, align = align})
}

// A call; dest none for no result.
ir_call :: proc(g: ^Codegen, dest: Val, ret: string, callee: Val, args: ..Ir_Arg) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, a = callee, args = ir_indices(..args)})
}

// A call to a variadic callee, its signature (`(ptr, ...)`) before its name.
ir_call_va :: proc(g: ^Codegen, dest: Val, ret, sig: string, callee: Val, args: ..Ir_Arg) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, to = sig, a = callee, args = ir_indices(..args)})
}

ir_ret :: proc(g: ^Codegen, ty: string, v := Val{}) {
    ir_emit(g, {op = .Ret, ty = ty, a = v})
}

ir_unreachable :: proc(g: ^Codegen) {
    ir_emit(g, {op = .Unreachable})
}

// A switch on v (of type ty): each case's value to its block, else default.
ir_switch :: proc(g: ^Codegen, ty: string, v: Val, default: Ir_Label, cases: []Ir_Arg) {
    ir_emit(g, {op = .Switch, ty = ty, a = v, l = default, args = cases})
}

// --- printing ----------------------------------------------------------------------

// A value as LLVM writes it.
ir_print_val :: proc(b: ^strings.Builder, v: Val) {
    w :: strings.write_string
    switch v.kind {
    case .None:
    case .Temp:
        w(b, "%.t")
        strings.write_i64(b, i64(v.n))
    case .Local:
        strings.write_byte(b, '%')
        w(b, v.name)
    case .Global:
        strings.write_byte(b, '@')
        w(b, v.name)
    case .Int:
        if v.n >= i128(min(i64)) && v.n <= i128(max(i64)) { strings.write_i64(b, i64(v.n)) } else { fmt.sbprintf(b, "%d", v.n) }
    case .Bool:  w(b, "true" if v.n != 0 else "false")
    case .Float: ir_print_hex(b, "0x", u64(v.n), 16)
    case .Half:  ir_print_hex(b, "0xH", u64(v.n), 4)
    case .Fzero: w(b, "0.0")
    case .Null:  w(b, "null")
    case .Zero:  w(b, "zeroinitializer")
    }
}

@(private="file")
ir_print_hex :: proc(b: ^strings.Builder, prefix: string, bits: u64, digits: uint) {
    w :: strings.write_string
    HEX := "0123456789ABCDEF"
    w(b, prefix)
    for k := digits; k > 0; k -= 1 { strings.write_byte(b, HEX[(bits >> (4 * (k - 1))) & 15]) }
}

ir_print_label :: proc(b: ^strings.Builder, l: Ir_Label) {
    w :: strings.write_string
    w(b, l.name)
    if l.n >= 0 { strings.write_i64(b, i64(l.n)) }
}

@(private="file")
ir_print_arg :: proc(b: ^strings.Builder, x: Ir_Arg) {
    w :: strings.write_string
    w(b, x.ty)
    strings.write_byte(b, ' ')
    ir_print_val(b, x.v)
}

// An instruction as LLVM IR, a line of it.
ir_print :: proc(b: ^strings.Builder, ins: Ir) {
    w :: strings.write_string
    v :: ir_print_val
    if ins.op == .Label {
        ir_print_label(b, ins.l)
        w(b, ":\n")
        return
    }
    w(b, "  ")
    if ins.dest.kind != .None {
        v(b, ins.dest)
        w(b, " = ")
    }
    align :: proc(b: ^strings.Builder, n: i32) {
        if n == 0 { return }
        w(b, ", align ")
        strings.write_int(b, int(n))
    }
    switch ins.op {
    case .Label:
    case .Alloca:
        w(b, "alloca "); w(b, ins.ty)
        align(b, ins.align)
    case .Load:
        w(b, "load "); w(b, ins.ty); w(b, ", ptr "); v(b, ins.a)
        align(b, ins.align)
    case .Store:
        w(b, "store "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, ", ptr "); v(b, ins.b)
        align(b, ins.align)
    case .Gep:
        w(b, "getelementptr inbounds " if ins.inbounds else "getelementptr ")
        w(b, ins.ty); w(b, ", ptr "); v(b, ins.a)
        for x in ins.args { w(b, ", "); ir_print_arg(b, x) }
    case .Bin:
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Icmp, .Fcmp:
        w(b, "icmp " if ins.op == .Icmp else "fcmp ")
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Select:
        w(b, "select i1 "); v(b, ins.a); w(b, ", ")
        w(b, ins.ty); w(b, " "); v(b, ins.b); w(b, ", ")
        w(b, ins.ty); w(b, " "); v(b, ins.c)
    case .Cast:
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, " to "); w(b, ins.to)
    case .Fneg:
        w(b, "fneg "); w(b, ins.ty); w(b, " "); v(b, ins.a)
    case .Extract:
        w(b, "extractvalue "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Call:
        w(b, "call "); w(b, ins.ty); w(b, " ")
        if ins.to != "" { w(b, ins.to); w(b, " ") }
        v(b, ins.a); w(b, "(")
        for x, i in ins.args {
            if i > 0 { w(b, ", ") }
            ir_print_arg(b, x)
        }
        w(b, ")")
    case .Ret:
        w(b, "ret "); w(b, ins.ty)
        if ins.a.kind != .None { w(b, " "); v(b, ins.a) }
    case .Br:
        w(b, "br label %"); ir_print_label(b, ins.l)
    case .Cond_Br:
        w(b, "br i1 "); v(b, ins.a); w(b, ", label %"); ir_print_label(b, ins.l); w(b, ", label %"); ir_print_label(b, ins.l2)
    case .Switch:
        w(b, "switch "); w(b, ins.ty); w(b, " "); v(b, ins.a); w(b, ", label %"); ir_print_label(b, ins.l); w(b, " [\n")
        for x in ins.args { w(b, "    "); ir_print_arg(b, x); w(b, ", label %"); ir_print_label(b, x.l); w(b, "\n") }
        w(b, "  ]")
    case .Unreachable:
        w(b, "unreachable")
    }
    w(b, "\n")
}

ir_print_all :: proc(b: ^strings.Builder, code: []Ir) {
    for ins in code { ir_print(b, ins) }
}

// A function's `define` line, its `{` ending it.
ir_print_head :: proc(b: ^strings.Builder, h: Ir_Head) {
    w :: strings.write_string
    w(b, "define ")
    if h.export { w(b, "dllexport ") }
    w(b, h.ret)
    w(b, " @")
    w(b, h.name)
    w(b, "(")
    for x, i in h.params {
        if i > 0 { w(b, ", ") }
        ir_print_arg(b, x)
    }
    w(b, ") {")
}

// A global's line, its newline ending it.
ir_print_global :: proc(b: ^strings.Builder, gl: Ir_Global) {
    w :: strings.write_string
    strings.write_byte(b, '@')
    w(b, gl.name)
    w(b, " = ")
    switch gl.linkage {
    case .Default:
    case .Private:  w(b, "private ")
    case .Internal: w(b, "internal ")
    case .External: w(b, "external ")
    }
    if gl.unnamed { w(b, "unnamed_addr ") }
    w(b, "constant " if gl.constant else "global ")
    w(b, gl.ty)
    if gl.linkage != .External {
        strings.write_byte(b, ' ')
        ir_print_const(b, gl.init)
    }
    if gl.align != 0 {
        w(b, ", align ")
        strings.write_int(b, int(gl.align))
    }
    strings.write_byte(b, '\n')
}

// An initializer as LLVM writes it (without its type: its part's, its
// global's, say that).
ir_print_const :: proc(b: ^strings.Builder, c: Ir_Const) {
    w :: strings.write_string
    part :: proc(b: ^strings.Builder, p: Ir_Const) {
        w(b, p.ty)
        strings.write_byte(b, ' ')
        ir_print_const(b, p)
    }
    switch c.kind {
    case .Val:
        ir_print_val(b, c.v)
    case .Bytes:
        w(b, "c\"")
        w(b, llvm_escape_string(c.bytes))
        strings.write_byte(b, '"')
    case .Struct, .Packed, .Array:
        open, close := "{ ", " }"
        if c.kind == .Packed { open, close = "<{ ", " }>" }
        if c.kind == .Array { open, close = "[", "]" }
        w(b, open)
        for p, i in c.parts {
            if i > 0 { w(b, ", ") }
            part(b, p)
        }
        w(b, close)
    case .Gep:
        w(b, "getelementptr inbounds (")
        w(b, c.src)
        w(b, ", ptr ")
        ir_print_val(b, c.v)
        for p in c.parts {
            w(b, ", ")
            part(b, p)
        }
        w(b, ")")
    }
}

ir_global_text :: proc(gls: []Ir_Global) -> string {
    b := strings.builder_make()
    for gl in gls { ir_print_global(&b, gl) }
    return strings.to_string(b)
}
