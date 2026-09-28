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
    sret:  Type,                // a struct result, built in the caller's slot (%sret)
    ctor:  bool,                // a struct's code: it builds Self in %sret, which starts zeroed
    fields: strings.Builder,    // a constructor's field addresses, first in its entry
    head:  string,              // its `define` line
    user:  []Node_Id,           // by id - node: the one operation using an operation's value

    // Its named allocas: one for the named locals of one name and type (their
    // scopes never overlap — a name can't be declared again where it is
    // visible).
    shared:  map[string]string,
    used:    map[string]bool,
}

// Emit a fun from the graph. False, having emitted nothing, when some part of
// it isn't lowered yet.
llvm_function :: proc(g: ^Codegen, cf: ^Type_Scope) -> bool {
    if _, src := cf.origin.(Origin_Source); !src || cf.is_exposed { return false }
    pg := &g.checked.graph
    node, ok := pg.scope_node[cf]
    if !ok || (pg.kind[node] != .Fun && pg.kind[node] != .Struct) { return false }
    e := Llvm{g = g, pg = pg, ft = cf, node = node, ctor = pg.kind[node] == .Struct}
    own := graph_code_runs(pg, g.run_starts, node, &e.runs)
    if own == 0 || own != len(e.runs) { return false }   // no code; defer blocks (later)
    size := int(pg.last[node] - node) + 1
    e.value = make([]string, size)
    e.held = make([]bool, size)

    // Emit as the old emitter does, allocas hoisted: every alloca into the
    // entry's buffer in the order code first needs it, the rest into the
    // body's. Keep them only when every part lowered: the `define`, the
    // entry's field addresses and allocas, then the body.
    g.tmp_counter, g.label_counter = 0, 0
    g.emitted_allocas = {}
    begin_alloca_hoist(g)
    lowered := llvm_emit(&e)
    g.hoist_allocas = false
    if lowered {
        strings.write_string(&g.out, e.head)
        strings.write_string(&g.out, "\nentry:\n")
        strings.write_string(&g.out, strings.to_string(e.fields))
        strings.write_string(&g.out, strings.to_string(g.alloca_buf))
        strings.write_string(&g.out, strings.to_string(g.body_buf))
    }
    return lowered
}

@(private="file")
llvm_emit :: proc(e: ^Llvm) -> bool {
    g, pg, cf := e.g, e.pg, e.ft

    // The signature: its params, then its result — a scalar returned, or a
    // struct built in the caller's slot (a constructor's is Self).
    if len(cf.cg_returns) > 1 || len(cf.return_binding_names) > 0 { return false }
    e.ret = "void"
    if e.ctor {
        if len(cf.cg_returns) != 1 || llvm_struct(cf.cg_returns[0]) == nil { return false }
        e.sret = cf.cg_returns[0]
    } else if len(cf.cg_returns) == 1 {
        rt := cf.cg_returns[0]
        switch {
        case llvm_scalar(rt):        e.ret = llvm_type_from_checker(rt)
        case llvm_struct(rt) != nil: e.sret = rt
        case:                        return false
        }
    }
    // A fun that consumes a param into its result (its opening copy is
    // skipped when the caller passes that storage as the slot): later.
    if _, consumes := consumed_param_of(cf).?; consumes { return false }
    params := make([dynamic]string, 0, len(cf.cg_params), context.temp_allocator)
    for p in cf.cg_params {
        ir := llvm_param_type(p.type_) or_return
        append(&params, fmt.tprintf("%s %%%s.arg", ir, p.name))
    }
    if e.sret != nil { append(&params, "ptr %sret") }
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
    llvm_users(e)
    if e.sret != nil { llvm_result_slot(e) }
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
            _ = llvm_param_type(pg.type_[id]) or_return
            e.value[id - e.node] = fmt.tprintf("%%%s.arg", pg.name[id])
        case .Local:
            t := pg.type_[id]
            if !llvm_scalar(t) && llvm_struct(t) == nil { return false }
            if pg.written[id] == .Synthetic && llvm_scalar(t) && llvm_holds(e, id) { e.held[id - e.node] = true }
        case .Field:
            // A constructor's field: its place in Self, first thing in the entry.
            t := pg.type_[id]
            if !e.ctor || pg.parent[id] != e.node || (!llvm_scalar(t) && llvm_struct(t) == nil) { return false }
            i := struct_field_index(llvm_struct(e.sret), pg.name[id])
            if i < 0 { return false }
            at := fresh_tmp(e.g)
            fmt.sbprintf(&e.fields, "  %s = getelementptr %s, ptr %%sret, i32 0, i32 %d\n", at, llvm_type_from_checker(e.sret), i)
            e.value[id - e.node] = at
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
    emit_alloca(e.g, name, ir)
    return name
}

// Each operation's user, when it has exactly one (-1 for none, -2 for several).
@(private="file")
llvm_users :: proc(e: ^Llvm) {
    pg := e.pg
    e.user = make([]Node_Id, len(e.value))
    for &u in e.user { u = -1 }
    for r in e.runs {
        for op in graph_run(pg, int(r)) {
            for o in graph_operands(pg, op) {
                if o.op == NO_NODE { continue }
                u := &e.user[o.op - e.node]
                u^ = op if u^ == -1 else -2
            }
        }
    }
}

// What a struct-returning fun builds in its caller's slot rather than in
// storage of its own: the local every return returns (NRVO), and a
// temporary whose one read is a return (a literal or construction returned).
@(private="file")
llvm_result_slot :: proc(e: ^Llvm) {
    pg := e.pg
    returned := NO_NODE   // the local every return returns, so far
    every := true
    for r in e.runs {
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Return { continue }
            ops := graph_operands(pg, op)
            v := NO_NODE
            if len(ops) == 1 && ops[0].op != NO_NODE && pg.op[ops[0].op] == .Read {
                place := graph_operands(pg, ops[0].op)[0].op
                if pg.op[place] == .Var && pg.kind[pg.refers[place]] == .Local { v = pg.refers[place] }
            }
            if v != NO_NODE && pg.written[v] == .Synthetic {
                if llvm_reads(e, v) == 1 { e.value[v - e.node] = "%sret" }
                v = NO_NODE   // a temporary is no named local
            }
            switch {
            case v == NO_NODE:                        every = false
            case returned == NO_NODE:                 returned = v
            case returned != v:                       every = false
            }
        }
    }
    if every && returned != NO_NODE { e.value[returned - e.node] = "%sret" }
}

// How many reads a variable has.
@(private="file")
llvm_reads :: proc(e: ^Llvm, v: Node_Id) -> int {
    pg := e.pg
    n := 0
    for r in e.runs {
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Read { continue }
            place := graph_operands(pg, op)[0].op
            if pg.op[place] == .Var && pg.refers[place] == v { n += 1 }
        }
    }
    return n
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
        if e.ctor && d == e.node {   // Self: the value under construction
            e.value[op - e.node] = "%sret"
            return true
        }
        if d <= e.node || d > pg.last[e.node] { return false }   // not this fun's
        switch {
        case pg.kind[d] == .Param || pg.kind[d] == .Field: e.value[op - e.node] = e.value[d - e.node]
        case !e.held[d - e.node]:                          e.value[op - e.node] = llvm_storage(e, d)
        }
    case .Const:
        v, ok := llvm_const(e, op)
        if !ok { return false }
        e.value[op - e.node] = v
    case .Read:
        // A struct is read as where it is; a register value is loaded.
        place := ops[0].op
        t := pg.type_[op]
        switch {
        case llvm_direct(e, place):
            e.value[op - e.node] = llvm_direct_value(e, place)
        case llvm_struct(t) != nil:
            e.value[op - e.node] = e.value[place - e.node]
        case llvm_scalar(t):
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, llvm_type_from_checker(t), e.value[place - e.node])
            e.value[op - e.node] = tmp
        case:
            return false
        }
    case .Write:
        place := ops[0].op
        t := pg.type_[place]
        val, ok := llvm_operand(e, ops[1], t)
        if !ok { return false }
        if llvm_struct(t) != nil {
            // A struct is copied into the place, unless a call built it there.
            if llvm_direct(e, place) { return false }
            if val != e.value[place - e.node] { emit_memcpy(g, e.value[place - e.node], val, llvm_size(e, t)) }
            return true
        }
        if !llvm_scalar(t) { return false }
        if llvm_direct(e, place) {
            d := pg.refers[place]
            if !e.held[d - e.node] { return false }   // a param is read-only
            e.value[d - e.node] = val
            return true
        }
        emit_store(g, llvm_type_from_checker(t), val, e.value[place - e.node])
    case .Deref:
        // What a pointer points at: the pointer's value is the place.
        place := ops[0].op
        if llvm_direct(e, place) {
            e.value[op - e.node] = llvm_direct_value(e, place)
        } else {
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, "ptr", e.value[place - e.node])
            e.value[op - e.node] = tmp
        }
    case .Field:
        base := ops[0].op
        sd := llvm_struct(pg.type_[base])
        if sd == nil || llvm_direct(e, base) { return false }   // slice / union headers (later)
        i := struct_field_index(sd, pg.name[op])
        if i < 0 { return false }                                // through a `using` field (later)
        tmp := fresh_tmp(g)
        emit_field_gep_into(g, tmp, llvm_type_from_checker(pg.type_[base]), e.value[base - e.node], i)
        e.value[op - e.node] = tmp
    case .Address:
        place := ops[0].op
        if llvm_direct(e, place) { return false }
        e.value[op - e.node] = e.value[place - e.node]
    case .Construct:
        return llvm_construct(e, op, ops)
    case .Zero:
        // A bare scalar declaration: zero.
        place := ops[0].op
        t := pg.type_[place]
        if len(ops) != 1 || !llvm_scalar(t) || llvm_direct(e, place) { return false }
        if llvm_zeroed(e, place) { return true }
        emit_store(g, llvm_type_from_checker(t), llvm_zero(t), e.value[place - e.node])
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
        if e.ctor {   // Self was built in place
            if len(ops) != 0 { return false }
            emit(g, "  ret void")
            return true
        }
        if e.sret != nil {
            // Into the caller's slot, unless it was built there.
            if len(ops) != 1 { return false }
            v := llvm_operand(e, ops[0], e.sret) or_return
            if v != "%sret" { emit_memcpy(g, "%sret", v, llvm_size(e, e.sret)) }
            emit(g, "  ret void")
            return true
        }
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
    case .Global, .Index, .Variant, .Swizzle, .Slice,
         .Fill, .Carve, .Byte_Read, .Arena_Alloc,
         .Print, .Crash, .Switch, .Run_Defer, .Arena_Mark, .Arena_Reset:
        return false
    }
    return true
}

// A place's address, even before its operation is reached: a variable names
// its storage whatever comes first (a declaration's value precedes its var).
@(private="file")
llvm_place :: proc(e: ^Llvm, place: Node_Id) -> string {
    pg := e.pg
    if pg.op[place] != .Var { return e.value[place - e.node] }
    d := pg.refers[place]
    switch {
    case e.ctor && d == e.node:                          return "%sret"
    case pg.kind[d] == .Param || pg.kind[d] == .Field:   return e.value[d - e.node]
    }
    return llvm_storage(e, d)
}

// Whether a place holds its value directly, not at an address: a scalar param
// (read-only, its argument) or a held synthetic local.
@(private="file")
llvm_direct :: proc(e: ^Llvm, place: Node_Id) -> bool {
    pg := e.pg
    if pg.op[place] != .Var { return false }
    d := pg.refers[place]
    if pg.kind[d] == .Param { return llvm_scalar(pg.type_[d]) }
    return e.held[d - e.node]
}

@(private="file")
llvm_direct_value :: proc(e: ^Llvm, place: Node_Id) -> string {
    return e.value[e.pg.refers[place] - e.node]
}

// An operand's IR value, which must already be of the type its use takes.
@(private="file")
llvm_operand :: proc(e: ^Llvm, o: Operand, want: Type) -> (string, bool) {
    if o.op == NO_NODE || o.out != 0 { return "", false }
    have := e.pg.type_[o.op]
    if !llvm_same_type(have, want) { return "", false }
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

// Whether a place is already zero: a constructor's field — a constructor
// runs on storage its caller zeroed.
@(private="file")
llvm_zeroed :: proc(e: ^Llvm, place: Node_Id) -> bool {
    pg := e.pg
    return e.ctor && pg.op[place] == .Var && pg.refers[place] != NO_NODE && pg.kind[pg.refers[place]] == .Field
}

// The fun or struct a call or construction runs; nil through a function value.
@(private="file")
llvm_callee :: proc(e: ^Llvm, op: Node_Id) -> ^Type_Scope {
    for edge in graph_out(e.pg, op) {
        if edge.kind == .Calls { return e.pg.type_[edge.to].(^Type_Scope) }
    }
    return nil
}

// A struct built in place: its storage zeroed, then its constructor run on it
// with the arguments, the place last.
@(private="file")
llvm_construct :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    t := pg.type_[op]
    callee := llvm_callee(e, op)
    if callee == nil || callee.kind != .Struct || llvm_struct(t) == nil || llvm_direct(e, dest) { return false }
    if !llvm_same_type(pg.type_[dest], t) { return false }   // an array's elements (later)
    if _, src := callee.origin.(Origin_Source); !src { return false }
    // A bare construction passes the constructor's defaults (later).
    if len(ops) - 1 != len(callee.cg_params) { return false }
    args := make([dynamic]string, 0, len(ops), context.temp_allocator)
    for p, i in callee.cg_params {
        ir := llvm_param_type(p.type_) or_return
        v := llvm_operand(e, ops[i + 1], p.type_) or_return
        append(&args, fmt.tprintf("%s %s", ir, v))
    }
    at := e.value[dest - e.node]
    append(&args, fmt.tprintf("ptr %s", at))
    // A bare field of a constructor is already zero; a literal is a fresh value anywhere.
    if !(llvm_zeroed(e, dest) && pg.written[op] == .Synthetic) { emit_memset_zero(g, at, llvm_size(e, t)) }
    emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, callee.name), "(",
        strings.join(args[:], ", ", context.temp_allocator), ")"}))
    return true
}

@(private="file")
llvm_call :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g := e.g
    callee := llvm_callee(e, op)
    if callee == nil || callee.kind != .Fun { return false }   // through a function value (later)
    if _, src := callee.origin.(Origin_Source); !src { return false }
    if len(callee.cg_returns) > 1 || len(ops) != len(callee.cg_params) { return false }
    ret := "void"
    result: Type
    if len(callee.cg_returns) == 1 {
        result = callee.cg_returns[0]
        switch {
        case llvm_scalar(result):        ret = llvm_type_from_checker(result)
        case llvm_struct(result) != nil:
        case:                            return false
        }
    }
    args := make([dynamic]string, 0, len(ops) + 1, context.temp_allocator)
    for p, i in callee.cg_params {
        ir := llvm_param_type(p.type_) or_return
        v := llvm_operand(e, ops[i], p.type_) or_return
        append(&args, fmt.tprintf("%s %s", ir, v))
    }
    name := mara_fn_name(g, callee.name)
    if ret == "void" && result != nil {
        // A struct result, built where it goes (llvm_result_place).
        at := llvm_result_place(e, op, callee, result) or_return
        append(&args, fmt.tprintf("ptr %s", at))
        emit(g, "  call void %s(%s)", name, strings.join(args[:], ", ", context.temp_allocator))
        e.value[op - e.node] = at
        return true
    }
    joined := strings.join(args[:], ", ", context.temp_allocator)
    if ret == "void" {
        emit(g, "  call void %s(%s)", name, joined)
        return true
    }
    tmp := fresh_tmp(g)
    emit(g, "  %s = call %s %s(%s)", tmp, ret, name, joined)
    e.value[op - e.node] = tmp
    return true
}

// Where a call builds its struct result. Straight into where it goes when
// that is safe: this fun's own slot for a returned call; a declaration's or
// a temporary's fresh storage; an existing place when no argument passes the
// callee storage it could still be reading while it writes the result (else
// a temporary, copied in by the write). Anything else is a temporary.
@(private="file")
llvm_result_place :: proc(e: ^Llvm, op: Node_Id, callee: ^Type_Scope, result: Type) -> (string, bool) {
    pg := e.pg
    u := e.user[op - e.node]
    if u >= 0 {
        uops := graph_operands(pg, u)
        #partial switch pg.op[u] {
        case .Return:
            if e.sret != nil { return "%sret", true }
        case .Write:
            dest := uops[0].op
            if uops[1].op == op && !llvm_direct(e, dest) {
                fresh := false
                if pg.op[dest] == .Var {
                    d := pg.refers[dest]
                    s := pg.stmt[u]
                    fresh = pg.written[d] == .Synthetic || (s >= 0 && pg.stmts[s].kind == .Decl)
                }
                if fresh { return llvm_place(e, dest), true }
                // An update `x = f(x, …)` built in place: later.
                if _, consumes := consumed_param_of(callee).?; consumes { return "", false }
                if !llvm_passes_storage(callee) { return llvm_place(e, dest), true }
            }
        }
    }
    tmp := fresh_tmp(e.g)
    emit_alloca(e.g, tmp, llvm_type_from_checker(result))
    return tmp, true
}

// Whether a call hands its callee storage: a param passed by address.
@(private="file")
llvm_passes_storage :: proc(callee: ^Type_Scope) -> bool {
    for p in callee.cg_params {
        if ir, _ := llvm_param_type(p.type_); ir == "ptr" { return true }
    }
    return false
}

// --- types -----------------------------------------------------------------------

// A value held in one register: a number, a bool, a byte, an enum, a pointer.
@(private="file")
llvm_scalar :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(resolve_infer(t)) {
    case Type_Numeric, Type_F64, Type_Bool, Type_Utf8, Type_Byte, ^Type_Enum, ^Type_Ptr, Type_CString:
        return true
    }
    return false
}

// A struct: a value handled by its address — a param is a pointer to the
// caller's, and reading one yields where it is. (One holding a partial array,
// re-pointed when copied, or a sized slice's backing storage: later.)
@(private="file")
llvm_struct :: proc(t: Type) -> ^Scope_Body {
    if t == nil { return nil }
    sd := as_struct_body(t)
    if sd == nil || llvm_points_into_itself(t) { return nil }
    return sd
}

@(private="file")
llvm_points_into_itself :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Partial_Array: return true
    case ^Type_Fixed_Array:   return llvm_points_into_itself(v.elem)
    case ^Type_Scope:
        sd := as_struct_body(v)
        if sd == nil { return false }
        if sd.backing_bytes > 0 { return true }
        for &f in sd.fields { if llvm_points_into_itself(f.type_) { return true } }
    }
    return false
}

// Whether two types lower to one IR type. An unresolved one matches nothing:
// the fun is declined rather than guessed at.
@(private="file")
llvm_same_type :: proc(a, b: Type) -> bool {
    if a == nil || b == nil || is_infer(a) || is_infer(b) { return false }
    return llvm_type_from_checker(a) == llvm_type_from_checker(b)
}

// A type's size in bytes, as its IR type lays it out.
@(private="file")
llvm_size :: proc(e: ^Llvm, t: Type) -> int {
    return elem_byte_size(llvm_type_from_checker(t), e.g.checked)
}

// A register value's zero.
@(private="file")
llvm_zero :: proc(t: Type) -> string {
    switch ir := llvm_type_from_checker(t); {
    case is_ir_float(ir): return "0.0"
    case ir == "ptr":     return "null"
    case ir == "i1":      return "false"
    }
    return "0"
}

// A param's IR type: a struct goes by address.
@(private="file")
llvm_param_type :: proc(t: Type) -> (string, bool) {
    if llvm_scalar(t) { return llvm_type_from_checker(t), true }
    if llvm_struct(t) != nil { return "ptr", true }
    return "", false
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
