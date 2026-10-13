package mara

import "base:runtime"
import "core:fmt"
import "core:strings"
import "core:sync"

// ---------------------------------------------------------------------------
// A function's low-level instructions, as data: what llvm.odin and the emit
// helpers make of each operation of the lowered program — the LLVM subset,
// no phi: allocas, loads and stores, address arithmetic, integer and float
// operations, conversions, calls, branches. Printed, they're the LLVM
// backend's IR (ir_print); read, the x86 backend's input (x86.odin).
//
// Everything in them is data: an operation is an Ir_Inst; a value a Val — a
// temporary by its number, a named local or a global by its name, a constant
// by its kind and value; a block its label (Ir_Label); a type an Ir_Type, an
// id in the program's table of types. So are a function's head (Ir_Head) and
// a module's globals with their initializers (Ir_Global, Ir_Const).
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
    ty, to:   Ir_Type,
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
    ty: Ir_Type,
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
ir_a :: proc(ty: Ir_Type, v: Val) -> Ir_Arg { return {ty = ty, v = v} }

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
    ret:    Ir_Type,
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
    ty:       Ir_Type,
    init:     Ir_Const,
    align:    i32,
}

Ir_Const_Kind :: enum u8 { Val, Bytes, Struct, Packed, Array, Gep }

// A global's initializer, or a part of one.
Ir_Const :: struct {
    kind:  Ir_Const_Kind,
    ty:    Ir_Type,      // its type, where an aggregate's part writes it
    v:     Val,          // .Val: it; .Gep: the global its address is into
    src:   Ir_Type,      // .Gep: the type its indices step through
    bytes: string,       // .Bytes: all of them
    parts: []Ir_Const,   // .Struct, .Packed, .Array: its parts; .Gep: its indices
}

ir_const :: proc(ty: Ir_Type, v: Val) -> Ir_Const { return {kind = .Val, ty = ty, v = v} }

ir_const_zero :: proc(c: Ir_Const) -> bool { return c.kind == .Val && c.v.kind == .Zero }

// --- types -------------------------------------------------------------------------

// A type: its id in the program's table of them, the same on every thread.
// The common ones have fixed ids; any other — an array, a struct, a named
// struct or union, a pointer argument with its attributes, a variadic
// callee's signature — is made once, by its structure, with its text.
Ir_Type :: distinct u32

Ir_Type_Kind :: enum u8 { None, Void, Int, Half, Float, Double, Ptr, Array, Vector, Struct, Named, Sig }

Ir_Type_Info :: struct {
    kind:   Ir_Type_Kind,
    packed: bool,          // a Struct's: no padding between its fields
    n:      int,           // an Int's bits; an Array's or a Vector's count
    elem:   Ir_Type,       // an Array's or a Vector's element; a Named one's body
    fields: []Ir_Type,     // a Struct's
    text:   string,        // as LLVM writes it
}

IR_NONE   :: Ir_Type(0)
IR_VOID   :: Ir_Type(1)
IR_I1     :: Ir_Type(2)
IR_I8     :: Ir_Type(3)
IR_I16    :: Ir_Type(4)
IR_I32    :: Ir_Type(5)
IR_I64    :: Ir_Type(6)
IR_I128   :: Ir_Type(7)
IR_HALF   :: Ir_Type(8)
IR_FLOAT  :: Ir_Type(9)
IR_DOUBLE :: Ir_Type(10)
IR_PTR    :: Ir_Type(11)
IR_SLICE  :: Ir_Type(12)   // a slice's header, { i64, i64, ptr }
IR_EMPTY  :: Ir_Type(13)   // {}, a value with nothing in it
IR_PRINTF :: Ir_Type(14)   // (ptr, ...), printf's signature

// The table: its types in pages that never move (a type is read without the
// lock: its id was had after it was made), found by their text when made.
@(private="file") IR_TYPE_PAGE :: 1024

@(private="file")
Ir_Type_Table :: struct {
    lock:    sync.Mutex,
    pages:   [16384]^[IR_TYPE_PAGE]Ir_Type_Info,
    count:   u32,
    by_text: map[string]Ir_Type,
}

@(private="file") ir_type_table: Ir_Type_Table

// Each thread's memo of the types it has asked for — by structure, and by
// what it was made from — so asking again takes no lock. (What a type was
// made from is a checker type: a check forgets those — `mara serve` checks
// again in one process, and a new check's types may sit where an old's did.)
@(private="file")
Ir_Type_Memo :: struct {
    ready:   bool,
    arrays:  map[[2]u64]Ir_Type,   // count, element
    structs: map[string]Ir_Type,   // its fields' ids' bytes, then packed
    of:      map[rawptr]Ir_Type,   // what it was made from (a checker type) → it
}

@(private="file", thread_local) ir_type_memo: Ir_Type_Memo

@(private="file")
ir_memo :: proc() -> ^Ir_Type_Memo {
    m := &ir_type_memo
    if !m.ready {
        heap := runtime.heap_allocator()
        m.arrays, m.structs, m.of = make(map[[2]u64]Ir_Type, heap), make(map[string]Ir_Type, heap), make(map[rawptr]Ir_Type, heap)
        m.ready = true
    }
    return m
}

@(init, private="file")
ir_types_init :: proc "contextless" () {
    context = runtime.default_context()
    basic :: proc(want: Ir_Type, info: Ir_Type_Info) {
        if ir_type_add(info) != want { panic("ir_types_init: a common type's id") }
    }
    ir_type_table.by_text = make(map[string]Ir_Type, runtime.heap_allocator())
    basic(IR_NONE,   {kind = .None})
    basic(IR_VOID,   {kind = .Void, text = "void"})
    basic(IR_I1,     {kind = .Int, n = 1, text = "i1"})
    basic(IR_I8,     {kind = .Int, n = 8, text = "i8"})
    basic(IR_I16,    {kind = .Int, n = 16, text = "i16"})
    basic(IR_I32,    {kind = .Int, n = 32, text = "i32"})
    basic(IR_I64,    {kind = .Int, n = 64, text = "i64"})
    basic(IR_I128,   {kind = .Int, n = 128, text = "i128"})
    basic(IR_HALF,   {kind = .Half, text = "half"})
    basic(IR_FLOAT,  {kind = .Float, text = "float"})
    basic(IR_DOUBLE, {kind = .Double, text = "double"})
    basic(IR_PTR,    {kind = .Ptr, text = "ptr"})
    slice_fields := [3]Ir_Type{IR_I64, IR_I64, IR_PTR}
    basic(IR_SLICE,  {kind = .Struct, fields = slice_fields[:], text = "{ i64, i64, ptr }"})
    basic(IR_EMPTY,  {kind = .Struct, text = "{}"})
    basic(IR_PRINTF, {kind = .Sig, text = "(ptr, ...)"})
}

// A type made, or found: by its text, under the table's lock.
@(private="file")
ir_type_add :: proc(info: Ir_Type_Info) -> Ir_Type {
    tb := &ir_type_table
    sync.mutex_lock(&tb.lock)
    defer sync.mutex_unlock(&tb.lock)
    if t, ok := tb.by_text[info.text]; ok && tb.count > 0 { return t }
    heap := runtime.heap_allocator()
    id := tb.count
    page := id / IR_TYPE_PAGE
    if int(page) >= len(tb.pages) { panic("ir_type_add: more types than the table holds") }
    if tb.pages[page] == nil { tb.pages[page] = new([IR_TYPE_PAGE]Ir_Type_Info, heap) }
    kept := info
    kept.text = strings.clone(info.text, heap)
    if len(info.fields) > 0 {
        kept.fields = make([]Ir_Type, len(info.fields), heap)
        copy(kept.fields, info.fields)
    }
    tb.pages[page][id % IR_TYPE_PAGE] = kept
    tb.count += 1
    tb.by_text[kept.text] = Ir_Type(id)
    return Ir_Type(id)
}

ir_type_info :: proc(t: Ir_Type) -> ^Ir_Type_Info {
    return &ir_type_table.pages[u32(t) / IR_TYPE_PAGE][u32(t) % IR_TYPE_PAGE]
}

ir_type_text :: proc(t: Ir_Type) -> string {
    return ir_type_info(t).text
}

// An integer type of `bits`.
ir_int_type :: proc(bits: int) -> Ir_Type {
    switch bits {
    case 1:   return IR_I1
    case 8:   return IR_I8
    case 16:  return IR_I16
    case 32:  return IR_I32
    case 64:  return IR_I64
    case 128: return IR_I128
    }
    return ir_type_add({kind = .Int, n = bits, text = fmt.tprintf("i%d", bits)})
}

// `[n x elem]`.
ir_array_type :: proc(n: int, elem: Ir_Type) -> Ir_Type {
    m := ir_memo()
    key := [2]u64{u64(n), u64(elem)}
    if t, ok := m.arrays[key]; ok { return t }
    t := ir_type_add({kind = .Array, n = n, elem = elem, text = fmt.tprintf("[%d x %s]", n, ir_type_text(elem))})
    m.arrays[key] = t
    return t
}

// `<n x elem>`, a vector (SysV's two floats in one register).
ir_vector_type :: proc(n: int, elem: Ir_Type) -> Ir_Type {
    return ir_type_add({kind = .Vector, n = n, elem = elem, text = fmt.tprintf("<%d x %s>", n, ir_type_text(elem))})
}

// `{ a, b, … }`, or packed `<{ a, b, … }>`; `{}` with none.
ir_struct_type :: proc(fields: []Ir_Type, packed := false) -> Ir_Type {
    m := ir_memo()
    buf: [64]u8
    key: string
    if n := len(fields) * size_of(Ir_Type) + 1; n <= len(buf) {
        copy(buf[:], transmute([]u8)runtime.Raw_Slice{raw_data(fields), n - 1})
        buf[n - 1] = 1 if packed else 0
        key = string(buf[:n])
    } else {
        b := make([]u8, n, context.temp_allocator)
        copy(b, transmute([]u8)runtime.Raw_Slice{raw_data(fields), n - 1})
        b[n - 1] = 1 if packed else 0
        key = string(b)
    }
    if t, ok := m.structs[key]; ok { return t }
    tb := strings.builder_make(context.temp_allocator)
    if len(fields) == 0 {
        strings.write_string(&tb, "{}")
    } else {
        strings.write_string(&tb, "<{ " if packed else "{ ")
        for f, i in fields {
            if i > 0 { strings.write_string(&tb, ", ") }
            strings.write_string(&tb, ir_type_text(f))
        }
        strings.write_string(&tb, " }>" if packed else " }")
    }
    t := ir_type_add({kind = .Struct, packed = packed, fields = fields, text = strings.to_string(tb)})
    m.structs[strings.clone(key, runtime.heap_allocator())] = t
    return t
}

// A named type, `%<name>` — a struct's or a union's — and its body.
ir_named_type :: proc(name: string, body: Ir_Type) -> Ir_Type {
    return ir_type_add({kind = .Named, elem = body, text = strings.concatenate({"%", name}, context.temp_allocator)})
}

// A pointer argument with its attributes (`ptr sret(%class.R)`): a pointer,
// as the callee sees it.
ir_ptr_attr :: proc(attr: string, of: Ir_Type) -> Ir_Type {
    return ir_type_add({kind = .Ptr, elem = of, text = fmt.tprintf("ptr %s(%s)", attr, ir_type_text(of))})
}

// The type made from `key` (a checker type's pointer), when this thread has
// made it before; ir_type_remember keeps it.
ir_type_recalled :: proc(key: rawptr) -> (Ir_Type, bool) {
    t, ok := ir_memo().of[key]
    return t, ok
}

ir_type_remember :: proc(key: rawptr, t: Ir_Type) -> Ir_Type {
    ir_memo().of[key] = t
    return t
}

// What this thread made types from forgotten (a check's start).
ir_types_forget :: proc() {
    clear(&ir_memo().of)
}

// --- making instructions -----------------------------------------------------------

// An instruction into the function's code: its body while its allocas are
// hoisted (emit_alloca), else where the code is being made.
ir_emit :: proc(g: ^Codegen, ins: Ir) {
    append(&g.body if g.hoist_allocas else &g.code, ins)
}

ir_bin :: proc(g: ^Codegen, dest: Val, inst: Ir_Inst, ty: Ir_Type, a, b: Val) {
    ir_emit(g, {op = .Bin, dest = dest, inst = inst, ty = ty, a = a, b = b})
}

ir_icmp :: proc(g: ^Codegen, dest: Val, pred: Ir_Inst, ty: Ir_Type, a, b: Val) {
    ir_emit(g, {op = .Icmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_fcmp :: proc(g: ^Codegen, dest: Val, pred: Ir_Inst, ty: Ir_Type, a, b: Val) {
    ir_emit(g, {op = .Fcmp, dest = dest, inst = pred, ty = ty, a = a, b = b})
}

ir_select :: proc(g: ^Codegen, dest, cond: Val, ty: Ir_Type, a, b: Val) {
    ir_emit(g, {op = .Select, dest = dest, ty = ty, a = cond, b = a, c = b})
}

ir_cast :: proc(g: ^Codegen, dest: Val, inst: Ir_Inst, from: Ir_Type, v: Val, to: Ir_Type) {
    ir_emit(g, {op = .Cast, dest = dest, inst = inst, ty = from, a = v, to = to})
}

ir_fneg :: proc(g: ^Codegen, dest: Val, ty: Ir_Type, v: Val) {
    ir_emit(g, {op = .Fneg, dest = dest, ty = ty, a = v})
}

ir_extract :: proc(g: ^Codegen, dest: Val, ty: Ir_Type, v: Val, index: int) {
    ir_emit(g, {op = .Extract, dest = dest, ty = ty, a = v, b = ir_int(index)})
}

// `getelementptr ty, ptr base, <index>…`.
ir_gep :: proc(g: ^Codegen, dest: Val, ty: Ir_Type, base: Val, indices: ..Ir_Arg) {
    ir_emit(g, {op = .Gep, dest = dest, ty = ty, a = base, args = ir_indices(..indices)})
}

ir_gep_inbounds :: proc(g: ^Codegen, dest: Val, ty: Ir_Type, base: Val, indices: ..Ir_Arg) {
    ir_emit(g, {op = .Gep, inbounds = true, dest = dest, ty = ty, a = base, args = ir_indices(..indices)})
}

// Operands kept: a variadic call's are the caller's, gone when it returns.
ir_indices :: proc(xs: ..Ir_Arg) -> []Ir_Arg {
    out := make([]Ir_Arg, len(xs))
    copy(out, xs)
    return out
}

ir_load :: proc(g: ^Codegen, dest: Val, ty: Ir_Type, ptr: Val, align: i32 = 0) {
    ir_emit(g, {op = .Load, dest = dest, ty = ty, a = ptr, align = align})
}

ir_store :: proc(g: ^Codegen, ty: Ir_Type, v, ptr: Val, align: i32 = 0) {
    ir_emit(g, {op = .Store, ty = ty, a = v, b = ptr, align = align})
}

// A call; dest none for no result.
ir_call :: proc(g: ^Codegen, dest: Val, ret: Ir_Type, callee: Val, args: ..Ir_Arg) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, a = callee, args = ir_indices(..args)})
}

// A call to a variadic callee, its signature (`(ptr, ...)`) before its name.
ir_call_va :: proc(g: ^Codegen, dest: Val, ret, sig: Ir_Type, callee: Val, args: ..Ir_Arg) {
    ir_emit(g, {op = .Call, dest = dest, ty = ret, to = sig, a = callee, args = ir_indices(..args)})
}

ir_ret :: proc(g: ^Codegen, ty: Ir_Type, v := Val{}) {
    ir_emit(g, {op = .Ret, ty = ty, a = v})
}

ir_unreachable :: proc(g: ^Codegen) {
    ir_emit(g, {op = .Unreachable})
}

// A switch on v (of type ty): each case's value to its block, else default.
ir_switch :: proc(g: ^Codegen, ty: Ir_Type, v: Val, default: Ir_Label, cases: []Ir_Arg) {
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
    w(b, ir_type_text(x.ty))
    strings.write_byte(b, ' ')
    ir_print_val(b, x.v)
}

// An instruction as LLVM IR, a line of it.
ir_print :: proc(b: ^strings.Builder, ins: Ir) {
    w :: strings.write_string
    v :: ir_print_val
    ty, to := ir_type_text(ins.ty), ir_type_text(ins.to)
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
        w(b, "alloca "); w(b, ty)
        align(b, ins.align)
    case .Load:
        w(b, "load "); w(b, ty); w(b, ", ptr "); v(b, ins.a)
        align(b, ins.align)
    case .Store:
        w(b, "store "); w(b, ty); w(b, " "); v(b, ins.a); w(b, ", ptr "); v(b, ins.b)
        align(b, ins.align)
    case .Gep:
        w(b, "getelementptr inbounds " if ins.inbounds else "getelementptr ")
        w(b, ty); w(b, ", ptr "); v(b, ins.a)
        for x in ins.args { w(b, ", "); ir_print_arg(b, x) }
    case .Bin:
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Icmp, .Fcmp:
        w(b, "icmp " if ins.op == .Icmp else "fcmp ")
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Select:
        w(b, "select i1 "); v(b, ins.a); w(b, ", ")
        w(b, ty); w(b, " "); v(b, ins.b); w(b, ", ")
        w(b, ty); w(b, " "); v(b, ins.c)
    case .Cast:
        w(b, IR_INST_NAME[ins.inst]); w(b, " "); w(b, ty); w(b, " "); v(b, ins.a); w(b, " to "); w(b, to)
    case .Fneg:
        w(b, "fneg "); w(b, ty); w(b, " "); v(b, ins.a)
    case .Extract:
        w(b, "extractvalue "); w(b, ty); w(b, " "); v(b, ins.a); w(b, ", "); v(b, ins.b)
    case .Call:
        w(b, "call "); w(b, ty); w(b, " ")
        if ins.to != IR_NONE { w(b, to); w(b, " ") }
        v(b, ins.a); w(b, "(")
        for x, i in ins.args {
            if i > 0 { w(b, ", ") }
            ir_print_arg(b, x)
        }
        w(b, ")")
    case .Ret:
        w(b, "ret "); w(b, ty)
        if ins.a.kind != .None { w(b, " "); v(b, ins.a) }
    case .Br:
        w(b, "br label %"); ir_print_label(b, ins.l)
    case .Cond_Br:
        w(b, "br i1 "); v(b, ins.a); w(b, ", label %"); ir_print_label(b, ins.l); w(b, ", label %"); ir_print_label(b, ins.l2)
    case .Switch:
        w(b, "switch "); w(b, ty); w(b, " "); v(b, ins.a); w(b, ", label %"); ir_print_label(b, ins.l); w(b, " [\n")
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
    strings.write_string(b, "define ")
    ir_print_signature(b, h)
    strings.write_string(b, " {")
}

// Its `declare` line, for another module that calls it.
ir_print_declare :: proc(b: ^strings.Builder, h: Ir_Head) {
    strings.write_string(b, "declare ")
    ir_print_signature(b, h)
}

@(private="file")
ir_print_signature :: proc(b: ^strings.Builder, h: Ir_Head) {
    w :: strings.write_string
    if h.export { w(b, "dllexport ") }
    w(b, ir_type_text(h.ret))
    w(b, " @")
    w(b, h.name)
    w(b, "(")
    for x, i in h.params {
        if i > 0 { w(b, ", ") }
        ir_print_arg(b, x)
    }
    w(b, ")")
}

// A named type's definition, `%class.X = type { … }`.
ir_print_type_def :: proc(b: ^strings.Builder, t: Ir_Type) {
    strings.write_string(b, ir_type_text(t))
    strings.write_string(b, " = type ")
    strings.write_string(b, ir_type_text(ir_type_info(t).elem))
    strings.write_byte(b, '\n')
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
    w(b, ir_type_text(gl.ty))
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
        w(b, ir_type_text(p.ty))
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
        w(b, ir_type_text(c.src))
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
