package mara

import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// A function's low-level instructions, as data: what llvm.odin and the emit
// helpers make of each operation of the lowered program — the LLVM subset,
// no phi: allocas, loads and stores, address arithmetic, integer and float
// operations, conversions, calls, branches. Printed, they're the LLVM
// backend's IR (ir_print); read, the x86 backend's input (x86.odin). Values
// and types are as LLVM writes them: `%.t3`, `@.str…`, `42`, `0x3FF0…`, `null`;
// `i64`, `ptr`, `%class.P`, `[4 x float]`.
// ---------------------------------------------------------------------------

Ir_Op :: enum u8 {
    Label,         // inst:
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
    Extract,       // dest = extractvalue ty a, b
    Call,          // [dest = ]call ty [to ]inst(args) — to, a variadic callee's signature
    Ret,           // ret ty[ a]
    Br,            // br label %a
    Cond_Br,       // br i1 a, label %b, label %c
    Switch,        // switch ty a, label %b [ args: ty v, label %label … ]
    Unreachable,
}

Ir :: struct {
    op:       Ir_Op,
    inbounds: bool,
    align:    i32,
    dest:     string,
    inst:     string,
    ty, to:   string,
    a, b, c:  string,
    args:     []Ir_Arg,
}

// A typed operand — a GEP's index, a call's argument — or a switch's case
// (its value and the label it goes to).
Ir_Arg :: struct {
    ty, v, label: string,
}

// An operand as LLVM writes one, `<type> <value>`: a value has no space in it,
// a type may (`{ i64, i1 }`).
ir_arg :: proc(s: string) -> Ir_Arg {
    sp := strings.last_index_byte(s, ' ')
    return {ty = s[:sp], v = s[sp + 1:]}
}

ir_args :: proc(ss: []string) -> []Ir_Arg {
    args := make([]Ir_Arg, len(ss))
    for s, i in ss { args[i] = ir_arg(s) }
    return args
}

// An instruction into the function's code: its body while its allocas are
// hoisted (emit_alloca), else where the code is being made.
ir_emit :: proc(g: ^Codegen, ins: Ir) {
    append(&g.body if g.hoist_allocas else &g.code, ins)
}

ir_bin :: proc(g: ^Codegen, dest, inst, ty, a, b: string) {
    ir_emit(g, {op = .Bin, dest = dest, inst = inst, ty = ty, a = a, b = b})
}

ir_icmp :: proc(g: ^Codegen, dest, pred, ty, a, b: string) {
    ir_emit(g, {op = .Icmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_fcmp :: proc(g: ^Codegen, dest, pred, ty, a, b: string) {
    ir_emit(g, {op = .Fcmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_select :: proc(g: ^Codegen, dest, cond, ty, a, b: string) {
    ir_emit(g, {op = .Select, dest = dest, ty = ty, a = cond, b = a, c = b})
}

ir_cast :: proc(g: ^Codegen, dest, inst, from, v, to: string) {
    ir_emit(g, {op = .Cast, dest = dest, inst = inst, ty = from, a = v, to = to})
}

ir_fneg :: proc(g: ^Codegen, dest, ty, v: string) {
    ir_emit(g, {op = .Fneg, dest = dest, ty = ty, a = v})
}

ir_extract :: proc(g: ^Codegen, dest, ty, v, index: string) {
    ir_emit(g, {op = .Extract, dest = dest, ty = ty, a = v, b = index})
}

// `getelementptr ty, ptr base, <index>…`: each index `<type> <value>`.
ir_gep :: proc(g: ^Codegen, dest, ty, base: string, indices: ..string) {
    ir_emit(g, {op = .Gep, dest = dest, ty = ty, a = base, args = ir_args(indices)})
}

ir_gep_inbounds :: proc(g: ^Codegen, dest, ty, base: string, indices: ..string) {
    ir_emit(g, {op = .Gep, inbounds = true, dest = dest, ty = ty, a = base, args = ir_args(indices)})
}

ir_load :: proc(g: ^Codegen, dest, ty, ptr: string, align: i32 = 0) {
    ir_emit(g, {op = .Load, dest = dest, ty = ty, a = ptr, align = align})
}

ir_store :: proc(g: ^Codegen, ty, v, ptr: string, align: i32 = 0) {
    ir_emit(g, {op = .Store, ty = ty, a = v, b = ptr, align = align})
}

// A call: each argument `<type> <value>`; dest "" for none.
ir_call :: proc(g: ^Codegen, dest, ret, callee: string, args: ..string) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, inst = callee, args = ir_args(args)})
}

// A call to a variadic callee, its signature (`(ptr, ...)`) before its name.
ir_call_va :: proc(g: ^Codegen, dest, ret, sig, callee: string, args: ..string) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, to = sig, inst = callee, args = ir_args(args)})
}

ir_ret :: proc(g: ^Codegen, ty: string, v := "") {
    ir_emit(g, {op = .Ret, ty = ty, a = v})
}

ir_unreachable :: proc(g: ^Codegen) {
    ir_emit(g, {op = .Unreachable})
}

// A switch on v (of type ty): each case's value to its label, else default.
ir_switch :: proc(g: ^Codegen, ty, v, default: string, cases: []Ir_Arg) {
    ir_emit(g, {op = .Switch, ty = ty, a = v, b = default, args = cases})
}

// --- printing ----------------------------------------------------------------------

// An instruction as LLVM IR, a line of it.
ir_print :: proc(b: ^strings.Builder, ins: Ir) {
    w :: strings.write_string
    if ins.op == .Label {
        w(b, ins.inst)
        w(b, ":\n")
        return
    }
    w(b, "  ")
    if ins.dest != "" {
        w(b, ins.dest)
        w(b, " = ")
    }
    align :: proc(b: ^strings.Builder, n: i32) {
        if n == 0 { return }
        strings.write_string(b, ", align ")
        strings.write_int(b, int(n))
    }
    switch ins.op {
    case .Label:
    case .Alloca:
        w(b, "alloca "); w(b, ins.ty)
        align(b, ins.align)
    case .Load:
        w(b, "load "); w(b, ins.ty); w(b, ", ptr "); w(b, ins.a)
        align(b, ins.align)
    case .Store:
        w(b, "store "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, ", ptr "); w(b, ins.b)
        align(b, ins.align)
    case .Gep:
        w(b, "getelementptr inbounds " if ins.inbounds else "getelementptr ")
        w(b, ins.ty); w(b, ", ptr "); w(b, ins.a)
        for x in ins.args { w(b, ", "); w(b, x.ty); w(b, " "); w(b, x.v) }
    case .Bin:
        w(b, ins.inst); w(b, " "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, ", "); w(b, ins.b)
    case .Icmp, .Fcmp:
        w(b, "icmp " if ins.op == .Icmp else "fcmp ")
        w(b, ins.inst); w(b, " "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, ", "); w(b, ins.b)
    case .Select:
        w(b, "select i1 "); w(b, ins.a); w(b, ", ")
        w(b, ins.ty); w(b, " "); w(b, ins.b); w(b, ", ")
        w(b, ins.ty); w(b, " "); w(b, ins.c)
    case .Cast:
        w(b, ins.inst); w(b, " "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, " to "); w(b, ins.to)
    case .Fneg:
        w(b, "fneg "); w(b, ins.ty); w(b, " "); w(b, ins.a)
    case .Extract:
        w(b, "extractvalue "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, ", "); w(b, ins.b)
    case .Call:
        w(b, "call "); w(b, ins.ty); w(b, " ")
        if ins.to != "" { w(b, ins.to); w(b, " ") }
        w(b, ins.inst); w(b, "(")
        for x, i in ins.args {
            if i > 0 { w(b, ", ") }
            w(b, x.ty); w(b, " "); w(b, x.v)
        }
        w(b, ")")
    case .Ret:
        w(b, "ret "); w(b, ins.ty)
        if ins.a != "" { w(b, " "); w(b, ins.a) }
    case .Br:
        w(b, "br label %"); w(b, ins.a)
    case .Cond_Br:
        w(b, "br i1 "); w(b, ins.a); w(b, ", label %"); w(b, ins.b); w(b, ", label %"); w(b, ins.c)
    case .Switch:
        w(b, "switch "); w(b, ins.ty); w(b, " "); w(b, ins.a); w(b, ", label %"); w(b, ins.b); w(b, " [\n")
        for x in ins.args { w(b, "    "); w(b, x.ty); w(b, " "); w(b, x.v); w(b, ", label %"); w(b, x.label); w(b, "\n") }
        w(b, "  ]")
    case .Unreachable:
        w(b, "unreachable")
    }
    w(b, "\n")
}

ir_print_all :: proc(b: ^strings.Builder, code: []Ir) {
    for ins in code { ir_print(b, ins) }
}

// A number as an operand's text.
ir_int :: proc(n: int) -> string {
    buf := make([]byte, 24, context.temp_allocator)
    return strconv.write_int(buf, i64(n), 10)
}
