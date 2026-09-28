package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// LLVM IR from the program graph (design/graph_retrofit.md, phase 3).
//
// A fun's code is its runs: each becomes a block — the entry's first, the rest
// in the order they were built — and each operation in them lowers as the
// operations table in design/program_graph.md says. A variable lives in an
// alloca at the top of the entry block; a scalar param is its argument; a
// synthetic scalar local written once, before every read, is just that value.
//
// The worker loop asks llvm_function for every fun. It emits into a scratch
// buffer and declines — having emitted nothing — the moment it meets what it
// doesn't lower yet; the syntax-tree emitter (codegen_fn.odin) does those,
// until it does nothing and is deleted.
// ---------------------------------------------------------------------------

// One fun's emission.
@(private="file")
Llvm :: struct {
    g:     ^Codegen,
    pg:    ^Program_Graph,
    ft:    ^Type_Scope,
    node:  Node_Id,
    runs:  [dynamic]i32,        // the runs its entry reaches: the entry's, then as built
    label: map[i32]string,      // a run → its block's label
    value: []string,            // by id - node: an operation's result, a variable's storage
    held:  []bool,              // by id - node: a variable held as its one value
    ret:   string,              // its IR return type
    head:  string,              // its `define` line

    // Its allocas, in the order its code first needs them: one for the named
    // locals of one name and type (their scopes never overlap — a name can't
    // be declared again where it is visible).
    allocas: strings.Builder,
    shared:  map[string]string,
    used:    map[string]bool,
}

// Emit a fun from the graph. False, having emitted nothing, when some part of
// it isn't lowered yet.
llvm_function :: proc(g: ^Codegen, cf: ^Type_Scope) -> bool {
    if _, src := cf.origin.(Origin_Source); !src || cf.is_exposed { return false }
    pg := &g.checked.graph
    node, ok := pg.scope_node[cf]
    if !ok || pg.kind[node] != .Fun { return false }
    e := Llvm{g = g, pg = pg, ft = cf, node = node}
    own := graph_code_runs(pg, g.run_starts, node, &e.runs)
    if own == 0 || own != len(e.runs) { return false }   // no code; defer blocks (later)
    size := int(pg.last[node] - node) + 1
    e.value = make([]string, size)
    e.held = make([]bool, size)

    // Emit the body into a scratch buffer, and keep it only when every part
    // lowered: the `define`, the entry's allocas, then the body.
    saved := g.out
    g.out = strings.builder_make()
    g.tmp_counter, g.label_counter = 0, 0
    lowered := llvm_emit(&e)
    body := strings.to_string(g.out)
    g.out = saved
    if lowered {
        strings.write_string(&g.out, e.head)
        strings.write_string(&g.out, "\nentry:\n")
        strings.write_string(&g.out, strings.to_string(e.allocas))
        strings.write_string(&g.out, body)
    }
    return lowered
}

@(private="file")
llvm_emit :: proc(e: ^Llvm) -> bool {
    g, pg, cf := e.g, e.pg, e.ft

    // The signature: scalars in, at most one scalar out.
    if len(cf.cg_returns) > 1 || len(cf.return_binding_names) > 0 { return false }
    e.ret = "void"
    if len(cf.cg_returns) == 1 {
        if !llvm_scalar(cf.cg_returns[0]) { return false }
        e.ret = llvm_type_from_checker(cf.cg_returns[0])
    }
    params := make([dynamic]string, 0, len(cf.cg_params), context.temp_allocator)
    for p in cf.cg_params {
        if !llvm_scalar(p.type_) { return false }
        append(&params, fmt.tprintf("%s %%%s.arg", llvm_type_from_checker(p.type_), p.name))
    }
    e.head = strings.concatenate({"define ", e.ret, " ", mara_fn_name(g, cf.name), "(",
        strings.join(params[:], ", ", context.temp_allocator), ") {"})

    // Entry first, then the runs as they were built; each gets its label.
    entry := g.run_starts[llvm_first_then(pg, e.node)]
    for r, i in e.runs {
        if r == entry { e.runs[0], e.runs[i] = e.runs[i], e.runs[0] }
    }
    llvm_sort_runs(e.runs[1:])
    for r in e.runs[1:] { e.label[r] = fmt.tprintf("run%d", r) }

    if !llvm_variables(e) { return false }
    for r, i in e.runs {
        if i > 0 { emit_label(g, e.label[r]) }
        for op in graph_run(pg, int(r)) {
            if !llvm_op(e, op) { return false }
        }
    }
    emit(g, "}")
    emit_raw(g, "")
    return true
}

// The first operation of the run a scope's code enters.
@(private="file")
llvm_first_then :: proc(pg: ^Program_Graph, scope: Node_Id) -> Node_Id {
    for edge in graph_out(pg, scope) { if edge.kind == .Then { return edge.to } }
    return NO_NODE
}

@(private="file")
llvm_sort_runs :: proc(runs: []i32) {
    for i in 1 ..< len(runs) {
        for j := i; j > 0 && runs[j - 1] > runs[j]; j -= 1 { runs[j - 1], runs[j] = runs[j], runs[j - 1] }
    }
}

// --- variables -------------------------------------------------------------------

// Each variable's storage: a param is its argument; a synthetic scalar written
// once, before every read, is held as that value; every other local gets an
// alloca in the entry block when its code first needs it (llvm_storage).
@(private="file")
llvm_variables :: proc(e: ^Llvm) -> bool {
    pg := e.pg
    for id := e.node + 1; id <= pg.last[e.node]; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct, .Union, .Enum:
            id = pg.last[id]
        case .Param:
            if !llvm_scalar(pg.type_[id]) { return false }
            e.value[id - e.node] = fmt.tprintf("%%%s.arg", pg.name[id])
        case .Local:
            if !llvm_scalar(pg.type_[id]) { return false }
            if pg.written[id] == .Synthetic && llvm_holds(e, id) { e.held[id - e.node] = true }
        case .Result, .Block, .Const, .Import, .Type_Def, .Dispatch, .Op:
        case:
            return false
        }
    }
    return true
}

// A local's alloca, made where its code first needs it: named after it, and
// one for the named locals of one name and type.
@(private="file")
llvm_storage :: proc(e: ^Llvm, d: Node_Id) -> string {
    pg := e.pg
    if slot := e.value[d - e.node]; slot != "" { return slot }
    ir := llvm_type_from_checker(pg.type_[d])
    explicit := pg.written[d] == .Explicit
    key := fmt.tprintf("%s %s", pg.name[d], ir)
    if slot, ok := e.shared[key]; ok && explicit {
        e.value[d - e.node] = slot
        return slot
    }
    name := fmt.tprintf("%%%s", pg.name[d])
    for n := 2; e.used[name]; n += 1 { name = fmt.tprintf("%%%s.%d", pg.name[d], n) }
    e.used[name] = true
    if explicit { e.shared[key] = name }
    e.value[d - e.node] = name
    fmt.sbprintf(&e.allocas, "  %s = alloca %s\n", name, ir)
    return name
}

// Whether a synthetic local is written once, before each of its reads: then
// it is that value, and needs no storage.
@(private="file")
llvm_holds :: proc(e: ^Llvm, v: Node_Id) -> bool {
    pg := e.pg
    write_run, write_at := -1, -1
    Read :: struct { run, at: int }
    reads := make([dynamic]Read, 0, 4, context.temp_allocator)
    for r, ri in e.runs {
        for op, at in graph_run(pg, int(r)) {
            ops := graph_operands(pg, op)
            for o, k in ops {
                if o.op == NO_NODE || pg.op[o.op] != .Var || pg.refers[o.op] != v { continue }
                switch {
                case pg.op[op] == .Write && k == 0:
                    if write_run >= 0 { return false }
                    write_run, write_at = ri, at
                case pg.op[op] == .Read:
                    append(&reads, Read{ri, at})
                case:
                    return false   // addressed, or a place of something larger
                }
            }
        }
    }
    if write_run < 0 { return false }
    for rd in reads {
        if rd.run == write_run {
            if rd.at < write_at { return false }
        } else if !llvm_dominates(e, write_run, rd.run) {
            return false
        }
    }
    return true
}

// Whether every path from the entry to run b passes through run a (both
// positions in e.runs).
@(private="file")
llvm_dominates :: proc(e: ^Llvm, a, b: int) -> bool {
    // Reach b from the entry without passing through a: then a doesn't dominate.
    pg := e.pg
    at: map[i32]int
    defer delete(at)
    for r, i in e.runs { at[r] = i }
    seen := make([]bool, len(e.runs), context.temp_allocator)
    todo := make([dynamic]int, 0, 8, context.temp_allocator)
    if a == 0 { return true }
    append(&todo, 0)
    seen[0] = true
    for len(todo) > 0 {
        i := pop(&todo)
        if i == b { return false }
        ops := graph_run(pg, int(e.runs[i]))
        for edge in graph_out(pg, ops[len(ops) - 1]) {
            if edge.kind != .Then { continue }
            j, ok := at[e.g.run_starts[edge.to]]
            if !ok || seen[j] || j == a { continue }
            seen[j] = true
            append(&todo, j)
        }
    }
    return true
}

// --- operations ------------------------------------------------------------------

@(private="file")
llvm_op :: proc(e: ^Llvm, op: Node_Id) -> bool {
    g, pg := e.g, e.pg
    ops := graph_operands(pg, op)
    span := pg.origin[op]
    switch pg.op[op] {
    case .Var:
        d := pg.refers[op]
        if d <= e.node || d > pg.last[e.node] { return false }   // not this fun's
        if pg.kind[d] == .Local && !e.held[d - e.node] {
            e.value[op - e.node] = llvm_storage(e, d)
        }
    case .Const:
        v, ok := llvm_const(e, op)
        if !ok { return false }
        e.value[op - e.node] = v
    case .Read:
        place := ops[0].op
        if pg.op[place] != .Var { return false }
        d := pg.refers[place]
        if pg.kind[d] == .Param || e.held[d - e.node] {
            e.value[op - e.node] = e.value[d - e.node]
            return true
        }
        tmp := fresh_tmp(g)
        emit_load_into(g, tmp, llvm_type_from_checker(pg.type_[op]), e.value[place - e.node])
        e.value[op - e.node] = tmp
    case .Write:
        place := ops[0].op
        if pg.op[place] != .Var { return false }
        d := pg.refers[place]
        if pg.kind[d] == .Param { return false }
        val, ok := llvm_operand(e, ops[1], pg.type_[place])
        if !ok { return false }
        if e.held[d - e.node] {
            e.value[d - e.node] = val
            return true
        }
        emit_store(g, llvm_type_from_checker(pg.type_[place]), val, e.value[place - e.node])
    case .Arith:
        return llvm_arith(e, op, ops, span)
    case .Compare:
        return llvm_compare(e, op, ops)
    case .Unary:
        return llvm_unary(e, op, ops, span)
    case .Cast:
        x := ops[0].op
        from, to := pg.type_[x], pg.type_[op]
        if !llvm_scalar(from) || !llvm_scalar(to) { return false }
        e.value[op - e.node] = llvm_convert(e, e.value[x - e.node], from, to)
    case .Call:
        return llvm_call(e, op, ops)
    case .Jump:
        emit_br(g, e.label[llvm_target(e, op, 0)])
    case .Branch:
        c, ok := llvm_operand(e, ops[0], Type_Bool{})
        if !ok { return false }
        emit_cond_br(g, c, e.label[llvm_target(e, op, 0)], e.label[llvm_target(e, op, 1)])
    case .Return:
        if len(ops) == 0 {
            if e.ret != "void" { return false }
            emit(g, "  ret void")
            return true
        }
        if len(ops) != 1 || e.ret == "void" { return false }
        v, ok := llvm_operand(e, ops[0], e.ft.cg_returns[0])
        if !ok { return false }
        emit(g, "  ret %s %s", e.ret, v)
    case .Assert:
        if pg.written[op] != .Synthetic || pg.name[op] != "range" { return false }
        c, ok := llvm_operand(e, ops[0], Type_Bool{})
        if !ok { return false }
        emit_range_check(g, c, span)
    case .Global, .Field, .Index, .Deref, .Variant, .Swizzle, .Slice,
         .Address, .Zero, .Construct, .Fill, .Carve, .Byte_Read, .Arena_Alloc,
         .Print, .Crash, .Switch, .Run_Defer, .Arena_Mark, .Arena_Reset:
        return false
    }
    return true
}

// An operand's IR value, which must already be of the type its use takes.
@(private="file")
llvm_operand :: proc(e: ^Llvm, o: Operand, want: Type) -> (string, bool) {
    if o.op == NO_NODE || o.out != 0 { return "", false }
    have := e.pg.type_[o.op]
    if llvm_type_from_checker(have) != llvm_type_from_checker(want) { return "", false }
    return e.value[o.op - e.node], true
}

// The run the k-th Then edge of an operation leads to.
@(private="file")
llvm_target :: proc(e: ^Llvm, op: Node_Id, k: int) -> i32 {
    n := 0
    for edge in graph_out(e.pg, op) {
        if edge.kind != .Then { continue }
        if n == k { return e.g.run_starts[edge.to] }
        n += 1
    }
    return -1
}

// A constant's IR literal at its type.
@(private="file")
llvm_const :: proc(e: ^Llvm, op: Node_Id) -> (string, bool) {
    t := e.pg.type_[op]
    v, ok := e.pg.consts[op]
    if !ok || !llvm_scalar(t) { return "", false }
    ir := llvm_type_from_checker(t)
    if ir == "i1" { return "true" if v.int != 0 else "false", true }
    return emit_number_literal(ir, v.float if v.is_float else f64(v.int), v.int, v.is_float), true
}

@(private="file")
llvm_arith :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    t := pg.type_[op]
    if !llvm_scalar(t) { return false }
    l, lok := llvm_operand(e, ops[0], t)
    r, rok := llvm_operand(e, ops[1], t)
    if !lok || !rok { return false }
    ir := llvm_type_from_checker(t)
    name := pg.name[op]
    tmp: string
    if is_ir_float(ir) {
        inst := ""
        switch name {
        case "+": inst = "fadd"
        case "-": inst = "fsub"
        case "*": inst = "fmul"
        case "/": inst = "fdiv"
        case "%": inst = "frem"
        case:     return false
        }
        tmp = fresh_tmp(g)
        emit(g, "  %s = %s %s %s, %s", tmp, inst, ir, l, r)
    } else {
        unsigned := llvm_unsigned(t)
        switch name {
        case "+":  tmp = emit_checked_arith(g, "uadd" if unsigned else "sadd", ir, l, r, span)
        case "-":  tmp = emit_checked_arith(g, "usub" if unsigned else "ssub", ir, l, r, span)
        case "*":  tmp = emit_checked_arith(g, "umul" if unsigned else "smul", ir, l, r, span)
        case "/", "%":
            emit_div_zero_check(g, r, ir, span)
            inst := "udiv" if unsigned else "sdiv"
            if name == "%" { inst = "urem" if unsigned else "srem" }
            tmp = fresh_tmp(g)
            emit(g, "  %s = %s %s %s, %s", tmp, inst, ir, l, r)
        case:
            inst := ""
            switch name {
            case "+%": inst = "add"
            case "-%": inst = "sub"
            case "*%": inst = "mul"
            case "&":  inst = "and"
            case "|":  inst = "or"
            case "~":  inst = "xor"
            case "<<": inst = "shl"
            case ">>": inst = "lshr" if unsigned else "ashr"
            case:      return false
            }
            tmp = fresh_tmp(g)
            emit(g, "  %s = %s %s %s, %s", tmp, inst, ir, l, r)
        }
    }
    e.value[op - e.node] = tmp
    return true
}

@(private="file")
llvm_compare :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    t := pg.type_[ops[0].op]
    if !llvm_scalar(t) { return false }
    l, lok := llvm_operand(e, ops[0], t)
    r, rok := llvm_operand(e, ops[1], t)
    if !lok || !rok { return false }
    ir := llvm_type_from_checker(t)
    name := pg.name[op]
    tmp := fresh_tmp(g)
    if is_ir_float(ir) {
        pred := ""
        switch name {
        case "==": pred = "oeq"
        case "!=": pred = "une"
        case "<":  pred = "olt"
        case "<=": pred = "ole"
        case ">":  pred = "ogt"
        case ">=": pred = "oge"
        case:      return false
        }
        emit(g, "  %s = fcmp %s %s %s, %s", tmp, pred, ir, l, r)
    } else {
        unsigned := llvm_unsigned(t)
        pred := ""
        switch name {
        case "==": pred = "eq"
        case "!=": pred = "ne"
        case "<":  pred = "ult" if unsigned else "slt"
        case "<=": pred = "ule" if unsigned else "sle"
        case ">":  pred = "ugt" if unsigned else "sgt"
        case ">=": pred = "uge" if unsigned else "sge"
        case:      return false
        }
        emit(g, "  %s = icmp %s %s %s, %s", tmp, pred, ir, l, r)
    }
    e.value[op - e.node] = tmp
    return true
}

@(private="file")
llvm_unary :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    t := pg.type_[op]
    if !llvm_scalar(t) { return false }
    x, ok := llvm_operand(e, ops[0], t)
    if !ok { return false }
    ir := llvm_type_from_checker(t)
    tmp: string
    switch pg.name[op] {
    case "-":
        if is_ir_float(ir) {
            tmp = fresh_tmp(g)
            emit(g, "  %s = fneg %s %s", tmp, ir, x)
        } else {
            // Integer negation is `0 - x`, overflow-checked: -MIN traps.
            tmp = emit_checked_arith(g, "usub" if llvm_unsigned(t) else "ssub", ir, "0", x, span)
        }
    case "-%":
        tmp = fresh_tmp(g)
        emit(g, "  %s = sub %s 0, %s", tmp, ir, x)
    case "not":
        tmp = fresh_tmp(g)
        emit(g, "  %s = xor i1 %s, true", tmp, x)
    case "~":
        tmp = fresh_tmp(g)
        emit(g, "  %s = xor %s %s, -1", tmp, ir, x)
    case:
        return false
    }
    e.value[op - e.node] = tmp
    return true
}

// A number's conversion: widening by the source's signedness, narrowing by
// truncation, between ints and floats by the target's (to an int) or the
// source's (from one) signedness.
@(private="file")
llvm_convert :: proc(e: ^Llvm, v: string, from, to: Type) -> string {
    g := e.g
    fi, ti := llvm_type_from_checker(from), llvm_type_from_checker(to)
    if fi == ti { return v }
    tmp := fresh_tmp(g)
    ff, tf := is_ir_float(fi), is_ir_float(ti)
    fb, tb := ir_type_bits(fi), ir_type_bits(ti)
    inst := ""
    switch {
    case ff && tf:  inst = "fpext" if fb < tb else "fptrunc"
    case ff:        inst = "fptoui" if llvm_unsigned(to) else "fptosi"
    case tf:        inst = "uitofp" if llvm_unsigned(from) else "sitofp"
    case fb == tb:  return v
    case fb < tb:   inst = "zext" if llvm_unsigned(from) else "sext"
    case:           inst = "trunc"
    }
    emit(g, "  %s = %s %s %s to %s", tmp, inst, fi, v, ti)
    return tmp
}

@(private="file")
llvm_call :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    callee: ^Type_Scope
    for edge in graph_out(pg, op) {
        if edge.kind == .Calls { callee = pg.type_[edge.to].(^Type_Scope) }
    }
    if callee == nil || callee.kind != .Fun { return false }   // through a function value (later)
    if _, src := callee.origin.(Origin_Source); !src { return false }
    if len(callee.cg_returns) > 1 || len(ops) != len(callee.cg_params) { return false }
    ret := "void"
    if len(callee.cg_returns) == 1 {
        if !llvm_scalar(callee.cg_returns[0]) { return false }
        ret = llvm_type_from_checker(callee.cg_returns[0])
    }
    args := make([dynamic]string, 0, len(ops), context.temp_allocator)
    for p, i in callee.cg_params {
        if !llvm_scalar(p.type_) { return false }
        v, ok := llvm_operand(e, ops[i], p.type_)
        if !ok { return false }
        append(&args, fmt.tprintf("%s %s", llvm_type_from_checker(p.type_), v))
    }
    joined := strings.join(args[:], ", ", context.temp_allocator)
    name := mara_fn_name(g, callee.name)
    if ret == "void" {
        emit(g, "  call void %s(%s)", name, joined)
        return true
    }
    tmp := fresh_tmp(g)
    emit(g, "  %s = call %s %s(%s)", tmp, ret, name, joined)
    e.value[op - e.node] = tmp
    return true
}

// --- types -----------------------------------------------------------------------

// A value held in one register: a number, a bool, a byte, an enum.
@(private="file")
llvm_scalar :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(resolve_infer(t)) {
    case Type_Numeric, Type_F64, Type_Bool, Type_Utf8, Type_Byte, ^Type_Enum:
        return true
    }
    return false
}

// Unsigned: unsigned ints, bytes, chars and bools.
@(private="file")
llvm_unsigned :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_Numeric:                   return v.kind == .Unsigned
    case Type_Byte, Type_Utf8, Type_Bool: return true
    }
    return false
}
