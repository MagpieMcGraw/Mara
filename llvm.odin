package mara

import "core:fmt"
import "core:path/filepath"
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
// The worker loop asks llvm_function for every fun with a body, the
// program's setup llvm_main for main's. What it doesn't lower is an error at
// the operation it stopped at.
// ---------------------------------------------------------------------------

// One fun's emission.
@(private="file")
Llvm :: struct {
    g:     ^Codegen,
    pg:    ^Program_Graph,
    ft:    ^Type_Scope,
    runs:  [dynamic]i32,        // the runs its entry reaches: the entry's, then as built; then its defers'
    own:   int,                 // how many of the runs are its own code's (the rest, defer blocks')
    label: map[i32]string,      // a run → its block's label
    value: []string,            // by id: an operation's result, a variable's storage
    held:  []bool,              // by id: a variable held as its one value
    ret:   string,              // its IR return type
    sret:  Type,                // a struct result, built in the caller's slot (%sret)
    rets:    []Type,            // several results: each into the caller's slot for it, %sret.<i>
    slot:    string,            // the result slot: %sret, or a fallible constructor's Self, %sret.0
    consumed: string,           // a param the result is built from (graph_consumed): its argument
    ctor:  bool,                // a struct's code: it builds Self in %sret, which starts zeroed
    main:  bool,                // main's body: `@main` returns i64, 0 when it falls off its end
    fields: [dynamic]Ir,        // a constructor's field addresses, first in its entry
    head:  string,              // its `define` line
    probe: string,              // -profile: its slot, when it's timed (llvm_probe)
    st:    ^Storage,            // where each value lives (storage.odin): read here, decided there

    // Its named allocas: one for the named locals of one name and type (their
    // scopes never overlap — a name can't be declared again where it is
    // visible).
    shared:  map[string]string,
    used:    map[string]bool,
    hdr:     map[Node_Id]Llvm_Header,   // a view held as its header's values (Storage.views): those values
    ahead:   map[Node_Id]bool,          // operations done ahead of their turn (a call builds its result there; a swap's)
    outs:    map[Node_Id][]string,      // a call with several results: where each is (a temporary it wrote)
    out_run: map[Node_Id]i32,           // the run such a call is in
    loaded:  map[Operand]string,        // a result loaded in its call's run (which dominates every use)
    temps:   map[Operand]string,        // a call's big result's temporary: on the arena from the fun's entry (Storage.temps)
    stop:     Node_Id,             // where it stopped, when it can't lower something (llvm_unlowered)
    note:    string,              // and what it met there, when that says more
    run:     i32,                 // the run being emitted
}

// Emit a fun with a body from the graph.
llvm_function :: proc(g: ^Codegen, cf: ^Type_Scope) {
    g.tmp_counter, g.label_counter = 0, 0
    llvm_code(g, cf, main = false)
}

// Main's body, after the program's setup (emit_main_prologue, made in
// g.code) — its `define` line `head`, the caller's. Its falling off the end,
// or a bare return, returns 0.
llvm_main :: proc(g: ^Codegen, cf: ^Type_Scope, head: string) {
    llvm_code(g, cf, main = true, head = head)
}

@(private="file")
llvm_code :: proc(g: ^Codegen, cf: ^Type_Scope, main: bool, head := "") {
    pg := g.checked.code.funs[cf] or_else nil
    if pg == nil || (pg.kind[0] != .Fun && pg.kind[0] != .Struct) { codegen_fatal(g, {}, CODE_GRAPH_NO_SCOPE, cf.name) }
    e := Llvm{g = g, pg = pg, ft = cf, ctor = pg.kind[0] == .Struct, main = main}
    e.own = graph_code_runs(pg, 0, &e.runs)
    if e.own == 0 { codegen_fatal(g, {}, CODE_GRAPH_NO_CODE, cf.name) }
    size := int(pg.end) + 1
    e.value = make([]string, size)
    e.held = make([]bool, size)

    // Allocas hoisted: every alloca into the entry's in the order code first
    // needs it, the rest into the body; then its code in order — what was
    // made before its body (main's setup), the entry's field addresses and
    // allocas, the body.
    begin_alloca_hoist(g)
    e.stop = 0
    if !llvm_emit(&e) { llvm_unlowered(&e) }
    g.hoist_allocas = false
    if main { e.head = head }
    code := [?][]Ir{g.code[:], e.fields[:], g.allocas[:], g.body[:]}
    codegen_function(g, e.head, code[:], gap = !main)   // (@main's end: its caller's)
    g.code = {}
}

// What the emitter doesn't lower: an error at the operation or
// variable it stopped at (the fun itself for its signature).
@(private="file")
llvm_unlowered :: proc(e: ^Llvm) -> ! {
    pg := e.pg
    at := e.stop
    what := graph_kind_word(pg.kind[at])
    if pg.kind[at] == .Op { what = graph_op_word(pg.op[at]) }
    note := fmt.tprintf(" (%s)", e.note) if e.note != "" else ""
    codegen_fatal(e.g, graph_origin(pg, at), CODE_GRAPH_UNLOWERED, e.ft.name, what, graph_name(pg, at), note)
}

// -profile: a fun worth timing — main, and one that does work a probe is
// worth (llvm_works) — tells the profiler (runtime/mara_prof.c) when it's
// entered, here, first thing, and when it's left, before each return
// (llvm_ret). Both name its slot: its name and where it's written, for its
// line in the profile, and the profiler's record of it, filled on its first
// call. Straight-line code that calls nothing costs its caller less than the
// probes would; its time is the caller's own.
@(private="file")
llvm_probe :: proc(e: ^Llvm) {
    g, cf := e.g, e.ft
    if g.profile == "" || !(e.main || llvm_works(&g.checked.code, e.pg, constructs = true)) { return }
    name := llvm_probe_name(cf)
    at := fmt.tprintf("%s:%d", filepath.base(span_file(cf.body_span)), span_line(cf.body_span))
    e.probe = strings.concatenate({"@.prof.", mara_fn_name(g, cf.name)[1:]}, codegen_keep(g))
    append(&g.string_decls, strings.concatenate({e.probe, " = internal global { ptr, ptr, ptr } { ptr ",
        get_string_literal(g, name), ", ptr ", get_string_literal(g, at), ", ptr null }"}, codegen_keep(g)))
    ir_call(g, "", "void", "@__mara_prof_enter", strings.concatenate({"ptr ", e.probe}, context.temp_allocator))
}

// A fun's name in the profile: as written, after the structs and funs it's in
// (`Player.update`). A generic's instance has its types after it, as its
// flat name has them (`total_of[i64]`).
@(private="file")
llvm_probe_name :: proc(cf: ^Type_Scope) -> string {
    if cf.source_name == "" && cf.decl != 0 {
        written := tc_text(cf.decl)
        at := strings.index(cf.name, strings.concatenate({written, "__"}))
        if at < 0 { return written }
        args, _ := strings.replace_all(cf.name[at + len(written) + 2:], "__", ", ")
        return strings.concatenate({written, "[", args, "]"})
    }
    name := scope_display_name(cf)
    for p := cf.parent_scope; p != nil && !p.is_module; p = p.parent_scope {
        if outer := scope_display_name(p); outer != "" { name = strings.concatenate({outer, ".", name}) }
    }
    return name
}

// Whether a code does work worth a probe: it loops, or calls something — a
// fun (not an intrinsic: that's code in place), a print, an arena. A
// construct counts when the struct's code calls or loops.
@(private="file")
llvm_works :: proc(pc: ^Program_Code, pg: ^Program_Graph, constructs: bool) -> bool {
    for id := Node_Id(0); id <= pg.end; id += 1 { if graph_stmt(pg, id).kind == .Loop { return true } }
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct: id = graph_last(pg, id); continue   // (another scope's)
        case .Op:
        case: continue
        }
        #partial switch pg.op[id] {
        case .Call:
            if callee := graph_called(pg, id); callee == nil || !scope_is_intrinsic(callee) { return true }
        case .Print, .Arena_Alloc:
            return true
        case .Construct:
            callee := graph_called(pg, id)
            if c := pc.funs[callee] or_else nil; constructs && c != nil && llvm_works(pc, c, constructs = false) { return true }
        }
    }
    return false
}

// A return (of `v`, of IR type `ty`; "void" for none), after the profiler is
// told the fun is left (llvm_probe) and its big temporaries are freed
// (llvm_temps).
@(private="file")
llvm_ret :: proc(e: ^Llvm, ty: string, v := "") {
    if e.probe != "" { ir_call(e.g, "", "void", "@__mara_prof_exit", strings.concatenate({"ptr ", e.probe}, context.temp_allocator)) }
    if len(e.st.temps) > 0 && !e.main { emit_arena_reset(e.g) }
    ir_ret(e.g, ty, v)
}

// The fun's big temporaries (Storage.temps), each bumped on the arena now,
// at its entry, after a mark its returns reset to (llvm_ret). Main's are
// the program's: no mark, no reset.
@(private="file")
llvm_temps :: proc(e: ^Llvm) {
    pg := e.pg
    if len(e.st.temps) > 0 && !e.main { emit_arena_mark(e.g) }
    for tp in e.st.temps {
        at := emit_arena_bump(e.g, type_size(tp.t), graph_name(pg, tp.at.op) if pg.kind[tp.at.op] == .Local else "temp", span_location(graph_origin(pg, tp.at.op)))
        if pg.kind[tp.at.op] == .Local { e.value[tp.at.op] = at } else { e.temps[tp.at] = at }
    }
}

@(private="file")
llvm_emit :: proc(e: ^Llvm) -> bool {
    g, pg, cf := e.g, e.pg, e.ft

    // The signature: its params, then its result — a scalar returned, or a
    // struct built in the caller's slot (a constructor's is Self).
    e.ret = "void"
    e.slot = "%sret"
    if e.ctor {
        // Self, built in the caller's slot; a fallible constructor's declared
        // results (its err) follow it, each in the slot after.
        if fn_result_count(cf) < 1 || llvm_struct(fn_result(cf, 0)) == nil { return false }
        e.sret = fn_result(cf, 0)
        if fn_result_count(cf) > 1 {
            for ri in 1 ..< fn_result_count(cf) { if !llvm_scalar(fn_result(cf, ri)) { e.note = "result type"; return false } }
            e.slot, e.rets = "%sret.0", fn_results(cf)
        }
    } else if fn_result_count(cf) > 1 {
        // Several results: each written into the caller's slot for it.
        for ri in 0 ..< fn_result_count(cf) {
            rt := fn_result(cf, ri)
            if !llvm_scalar(rt) && !llvm_aggregate(rt) { e.note = "result type"; return false }
        }
        e.rets = fn_results(cf)
    } else if fn_result_count(cf) == 1 {
        rt := fn_result(cf, 0)
        switch {
        case llvm_scalar(rt):        e.ret = llvm_type_from_checker(rt)
        case llvm_aggregate(rt):     e.sret = rt
        case:                        e.note = "result type"; return false
        }
    }
    // A fun that consumes a param into its result: its opening copy is
    // skipped when the caller passes that storage as the slot.
    if k, consumes := graph_consumed(&e.g.checked.code, cf).?; consumes { e.consumed = fmt.tprintf("%%%s.arg", cf.params[k].name) }
    params := make([dynamic]string, 0, len(cf.params), context.temp_allocator)
    for _, pi in cf.params {
        p := fn_param(cf, pi)
        ir, ok := llvm_param_type(p.type_)
        if !ok { e.note = fmt.tprintf("param '%s'", p.name); return false }
        append(&params, fmt.tprintf("%s %%%s.arg", ir, p.name))
    }
    if e.rets != nil {
        for _, i in e.rets { append(&params, fmt.tprintf("ptr %%sret.%d", i)) }
    } else if e.sret != nil {
        append(&params, "ptr %sret")
    }
    // (The result slots' names taken: a local named `sret` gets another.)
    for p in params { if at := strings.index_byte(p, '%'); at >= 0 && strings.has_prefix(p[at:], "%sret") { e.used[p[at:]] = true } }
    // `#expose`: in a DLL's export table, and the host's program — its first
    // param — is the one the DLL's code reads, set first thing.
    linkage := "dllexport " if cf.is_exposed else ""
    e.head = strings.concatenate({"define ", linkage, e.ret, " ", mara_fn_name(g, cf.name), "(",
        strings.join(params[:], ", ", context.temp_allocator), ") {"})
    if cf.is_exposed && len(cf.params) > 0 {
        append(&e.fields, Ir{op = .Store, ty = "ptr", a = fmt.tprintf("%%%s.arg", cf.params[0].name), b = "@__mara_program"})
    }

    // Entry first, then the runs as they were built; each gets its label, by
    // its place in the fun (not the program's: one fun's IR doesn't change
    // when another's runs do).
    entry := pg.run_starts[llvm_first_then(pg, 0)]
    for r, i in e.runs {
        if r == entry { e.runs[0], e.runs[i] = e.runs[i], e.runs[0] }
    }
    llvm_sort_runs(e.runs[1:e.own])
    for r, i in e.runs[1:e.own] { e.label[r] = fmt.tprintf("run%d", i + 1) }
    // (Labels share the locals' names: a variable named entry or run1 is
    // %entry.2, %run1.2.)
    e.used["%entry"] = true
    for i in 1 ..< e.own { e.used[fmt.tprintf("%%run%d", i)] = true }

    if !llvm_variables(e) { return false }
    // Where each value lives — held as a value, in the caller's slot, built in
    // place, on the arena — decided for the whole fun (storage.odin).
    e.st = storage_of(g.checked, pg, &g.summaries, e.runs[:], e.own, e.ctor, e.main, e.sret, e.rets)
    if e.st.stop != NO_NODE {
        e.stop = e.st.stop
        return false
    }
    copy(e.held, e.st.held)
    for v in e.st.views { e.hdr[v] = {} }
    for op in e.st.done { e.ahead[op] = true }
    for v, k in e.st.result { e.value[v] = e.slot if e.st.one_slot else fmt.tprintf("%%sret.%d", k) }
    llvm_probe(e)
    llvm_temps(e)
    for r, i in e.runs[:e.own] {   // (a defer block's: where it runs, llvm_run_defer)
        if i > 0 { emit_label(g, e.label[r]) }
        e.run = r
        for op in graph_run(pg, int(r)) {
            if op in e.ahead { delete_key(&e.ahead, op); continue }   // done already
            if d, is := e.st.alias[op]; is { e.value[op] = e.value[d]; continue }
            e.stop = op
            if !llvm_hoist_reads(e, op) { return false }
            if !llvm_op(e, op) { return false }
        }
    }
    return true
}

// Two places of one type swapped (storage_swaps): 64 bytes at a time through a
// buffer of that size — copied out of a, b's into a, the buffer's into b —
// then each one's partial arrays re-pointed at its own elements.
@(private="file")
llvm_emit_swap :: proc(e: ^Llvm, a, b: Node_Id) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, a)
    pa, pb := llvm_place(e, a), llvm_place(e, b)
    if pa == "" || pb == "" { return false }
    size := type_size(t)
    buf, slot := fresh_tmp(g), fresh_tmp(g)
    emit_alloca(g, buf, "[64 x i8]")
    emit_alloca(g, slot, "i64")
    emit_store(g, "i64", "0", slot)
    loop, body, done := fresh_label(g, "swap.loop"), fresh_label(g, "swap.body"), fresh_label(g, "swap.end")
    emit_br(g, loop)
    emit_label(g, loop)
    off := fresh_tmp(g)
    emit_load_into(g, off, "i64", slot)
    more := fresh_tmp(g)
    ir_icmp(g, more, "slt", "i64", off, ir_int(int(size)))
    emit_cond_br(g, more, body, done)
    emit_label(g, body)
    rest, small, n := fresh_tmp(g), fresh_tmp(g), fresh_tmp(g)
    ir_bin(g, rest, "sub", "i64", ir_int(int(size)), off)
    ir_icmp(g, small, "slt", "i64", rest, "64")
    ir_select(g, n, small, "i64", rest, "64")
    xa, xb := fresh_tmp(g), fresh_tmp(g)
    ir_gep(g, xa, "i8", pa, strings.concatenate({"i64 ", off}, context.temp_allocator))
    ir_gep(g, xb, "i8", pb, strings.concatenate({"i64 ", off}, context.temp_allocator))
    emit_memcpy_runtime(g, buf, xa, n)
    emit_memcpy_runtime(g, xa, xb, n)
    emit_memcpy_runtime(g, xb, buf, n)
    next := fresh_tmp(g)
    ir_bin(g, next, "add", "i64", off, "64")
    emit_store(g, "i64", next, slot)
    emit_br(g, loop)
    emit_label(g, done)
    if value_has_partial_array(g, t) {
        reanchor_partial_arrays(g, t, pa)
        reanchor_partial_arrays(g, t, pb)
    }
    return true
}

// The first operation of the run a scope's code enters.
@(private="file")
llvm_first_then :: proc(pg: ^Program_Graph, scope: Node_Id) -> Node_Id {
    for edge in graph_out(pg, scope) { return edge.to }
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
    for id := Node_Id(1); id <= pg.end; id += 1 {
        e.stop = id
        #partial switch pg.kind[id] {
        case .Fun, .Struct:
            id = graph_last(pg, id)
        case .Param:
            _ = llvm_param_type(graph_type(pg, id)) or_return
            e.value[id] = fmt.tprintf("%%%s.arg", graph_name(pg, id))
        case .Result:
            if pg.written[id] == .Explicit && !llvm_named_result(e, id) { return false }
        case .Local:
            t := graph_type(pg, id)
            if !llvm_scalar(t) && !llvm_aggregate(t) { return false }
        case .Field:
            // The program's struct is set up by main's entry (`this_program =
            // Program(…)` names the arena), never constructed: its fields,
            // nothing.
            if e.ctor && e.ft == (e.g.checked.table.funs["Program"] or_else nil) { continue }
            // A constructor's field: its place in Self, first thing in the entry.
            t := graph_type(pg, id)
            if !e.ctor || pg.parent[id] != 0 || (!llvm_scalar(t) && !llvm_aggregate(t)) { return false }
            i := struct_field_index(llvm_struct(e.sret), graph_name(pg, id))
            if i < 0 { return false }
            at := fresh_tmp(e.g)
            append(&e.fields, Ir{op = .Gep, dest = at, ty = llvm_type_from_checker(e.sret), a = e.slot,
                                 args = ir_indices({"i32", "0", ""}, {"i32", ir_int(i), ""})})
            e.value[id] = at
            // A partial array: its header stamped over its elements, and those
            // constructed, right after its address (its zero is not all zeros).
            if pa := llvm_partial(t); pa != nil {
                llvm_into_fields(e, true)
                emit_partial_array_zero(e.g, at, pa, zero = false)
                gen_construct_partial_array_elements(e.g, at, pa)
                llvm_into_fields(e, false)
            }
            // An array of them: each one so.
            inner := t
            for a := llvm_array(inner); a != nil; a = llvm_array(inner) { inner = a.elem }
            if fa := llvm_array(t); fa != nil && llvm_partial(inner) != nil {
                llvm_into_fields(e, true)
                gen_construct_elements(e.g, at, fa.elem, fa.size)
                llvm_into_fields(e, false)
            }
        case .Block, .Const, .Op:
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
    if slot := e.value[d]; slot != "" { return slot }
    if at, ok := e.st.in_place[d]; ok {
        e.value[d] = llvm_place(e, at)
        return e.value[d]
    }
    if c, ok := e.st.carved[d]; ok { return e.value[c] }   // the carved memory
    if v, ok := e.st.bound[d]; ok { return e.value[v] }    // the payload
    ir := llvm_type_from_checker(graph_type(pg, d))
    explicit := pg.written[d] == .Explicit
    key := fmt.tprintf("%s %s", graph_name(pg, d), ir)
    if slot, ok := e.shared[key]; ok && explicit {
        e.value[d] = slot
        return slot
    }
    name := fmt.tprintf("%%%s", graph_name(pg, d))
    for n := 2; e.used[name]; n += 1 { name = fmt.tprintf("%%%s.%d", graph_name(pg, d), n) }
    e.used[name] = true
    if explicit { e.shared[key] = name }
    e.value[d] = name
    emit_alloca(e.g, name, llvm_alloca_type(graph_type(pg, d)))
    return name
}

// A local's IR type as allocated: bytes held inline aligned for any value
// viewed in them.
@(private="file")
llvm_alloca_type :: proc(t: Type) -> string {
    ir := llvm_type_from_checker(t)
    if pa := llvm_partial(t); pa != nil && llvm_type_from_checker(pa.elem) == "i8" { return strings.concatenate({ir, ", align 16"}) }
    return ir
}

// Point the emit helpers' output at a constructor's entry prefix (e.fields),
// where its fields' addresses go, or back.
@(private="file")
llvm_into_fields :: proc(e: ^Llvm, on: bool) {
    e.fields, e.g.code = e.g.code, e.fields
    e.g.hoist_allocas = !on
}

// A value copied: its bytes, then the partial arrays in it re-pointed at the
// copy's own elements.
@(private="file")
llvm_copy :: proc(e: ^Llvm, dest, src: string, t: Type) {
    emit_memcpy(e.g, dest, src, type_size(t))
    reanchor_partial_arrays(e.g, t, dest)
}

// The reads of a value's place taken before its first write in place
// (storage_builds_alone): each read now, its place computed ahead — then
// skipped at its turn.
@(private="file")
llvm_hoist_reads :: proc(e: ^Llvm, at: Node_Id) -> bool {
    reads, has := e.st.hoist[at]
    if !has { return true }
    for r in reads {
        if !llvm_ahead(e, graph_operands(e.pg, r)[0].op) { return false }
        if !llvm_op(e, r) { return false }
        e.ahead[r] = true
    }
    return true
}

// A swizzle's components between the array they name (`base`, of type `at`)
// and an array of just them (`part`, of type `pt`), element by element:
// gathered into part, or scattered from it.
@(private="file")
llvm_swizzle_copy :: proc(e: ^Llvm, name: string, at: Type, base: string, pt: Type, part: string, gather: bool) {
    g := e.g
    ir := llvm_type_from_checker(llvm_array(at).elem)
    for c, i in transmute([]u8)name {
        in_base, in_part := fresh_tmp(g), fresh_tmp(g)
        emit_array_gep_const(g, in_base, llvm_type_from_checker(at), base, swizzle_char_to_index(c))
        emit_array_gep_const(g, in_part, llvm_type_from_checker(pt), part, i)
        v := fresh_tmp(g)
        emit_load_into(g, v, ir, in_base if gather else in_part)
        emit_store(g, ir, v, in_part if gather else in_base)
    }
}

// --- operations ------------------------------------------------------------------

@(private="file")
llvm_op :: proc(e: ^Llvm, op: Node_Id) -> bool {
    g, pg := e.g, e.pg
    ops := graph_operands(pg, op)
    span := graph_origin(pg, op)
    switch pg.op[op] {
    case .Var:
        d := pg.refers[op]
        if e.ctor && d == 0 {   // Self: the value under construction
            e.value[op] = e.slot
            return true
        }
        if storage_this_program(e.pg, d) {
            // The program's own storage, which main hands over: at each use,
            // where @__mara_program points.
            at := fresh_tmp(g)
            ir_load(g, at, "ptr", "@__mara_program")
            e.value[op] = at
            return true
        }
        if d <= 0 || d > pg.end { return false }   // not this fun's
        if pg.kind[d] == .Const { return false }   // a constant has no storage: a use reads its value
        if d in e.hdr { return true }   // a view held as values: no storage
        switch {
        case pg.kind[d] == .Param || pg.kind[d] == .Field: e.value[op] = e.value[d]
        case d in e.st.arena:                                 e.value[op] = e.value[d]   // its arena alloc gives it storage
        case !e.held[d]:                          e.value[op] = llvm_storage(e, d)
        }
    case .Const:
        // `void`, the uninitialized value: a pointer's null, a number's zero
        // (a write of it decides what's stored: llvm_write_void); an
        // aggregate's, nothing.
        if graph_name(pg, op) == "void" {
            t := graph_type(pg, op)
            switch {
            case !llvm_scalar(t):                        e.value[op] = "void"
            case llvm_type_from_checker(t) == "ptr":    e.value[op] = "null"
            case:                                        e.value[op] = llvm_zero(t)
            }
            return true
        }
        // A result's zero value (what `?` returns beside an error), of any type.
        if pg.written[op] == .Implied && graph_name(pg, op) == "zero" {
            e.value[op] = "zeroinitializer"
            return true
        }
        v, ok := llvm_const(e, op)
        if !ok { return false }
        e.value[op] = v
    case .Read:
        // An aggregate is read as where it is; a register value is loaded.
        place := ops[0].op
        t := graph_type(pg, op)
        big := pg.op[place] == .View && graph_name(pg, place) == "#big_endian"
        switch {
        case llvm_direct(e, place):
            e.value[op] = llvm_direct_value(e, place)
        case llvm_aggregate(t):
            // A big-endian view's bytes are swapped as they're copied: only
            // a write of them can.
            if u := e.st.user[op]; big && (u < 0 || pg.op[u] != .Write || graph_operands(pg, u)[1].op != op) {
                return false
            }
            e.value[op] = e.value[place]
        case llvm_union_tag(e, place) != nil:   // a union's tag, read as a match reads it
            e.value[op] = load_union_tag(g, llvm_union_tag(e, place), e.value[place])
        case llvm_scalar(t) && pg.op[place] == .View:
            // From bytes at any address: align 1; big-endian, swapped.
            tmp := fresh_tmp(g)
            ir_load(g, tmp, llvm_type_from_checker(t), e.value[place], 1)
            e.value[op] = emit_bswap_value(g, tmp, t) if big else tmp
        case llvm_scalar(t):
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, llvm_type_from_checker(t), e.value[place])
            e.value[op] = tmp
        case:
            return false
        }
    case .Write:
        if pair, is := e.st.swaps[op]; is { return llvm_emit_swap(e, pair[0], pair[1]) }   // (a swap's first put: the swap)
        place := ops[0].op
        if pg.op[place] == .Slice { return llvm_copy_into(e, ops, span) }
        if pg.op[place] == .Swizzle && len(graph_name(pg, place)) > 1 {
            // Into several components: each its element of the value.
            t := graph_type(pg, place)
            val := llvm_operand(e, ops[1], t) or_return
            sw := graph_operands(pg, place)[0].op
            llvm_swizzle_copy(e, graph_name(pg, place), graph_type(pg, sw), e.value[place], t, val, gather = false)
            return true
        }
        if v := ops[1].op; v != NO_NODE && pg.op[v] == .Const && graph_name(pg, v) == "void" { return llvm_write_void(e, op, place) }
        if llvm_union_tag(e, place) != nil { return false }   // a union's tag is its variant's: a construct writes it
        t := graph_type(pg, place)
        // Another type's value into bytes is a write through a view of them (later).
        if ops[1].op != NO_NODE && is_byte_elem(t) != is_byte_elem(graph_type(pg, ops[1].op)) { return false }
        // Into a partial array, text or a slice's elements fill a prefix.
        if pa := llvm_partial(t); pa != nil && ops[1].op != NO_NODE && !llvm_direct(e, place) {
            if text, is_text := llvm_text(e, ops[1].op); is_text { return llvm_text_into(e, place, pa, text) }
            if llvm_slice(graph_type(pg, ops[1].op)) != nil { return llvm_elements_into(e, place, pa, ops[1].op) }
        }
        // Into a fixed utf8 array, text: the array zeroed, then its bytes.
        if fa := llvm_array(t); fa != nil && ops[1].op != NO_NODE && !llvm_direct(e, place) {
            if text, is_text := llvm_text(e, ops[1].op); is_text && llvm_type_from_checker(fa.elem) == "i8" {
                emit_text_into_array(g, e.value[place], text, type_size(t))
                return true
            }
        }
        val, ok := llvm_operand(e, ops[1], t)
        if !ok { e.note = "the value's type"; return false }
        if pg.op[place] == .Var && pg.refers[place] in e.hdr { return true }   // held at its slice
        if pg.op[place] == .Var && e.st.carved[pg.refers[place]] == ops[1].op && ops[1].op != NO_NODE {
            return true   // a `let` declaration: the name is the carved memory
        }
        if pg.op[place] == .View && graph_name(pg, place) != "" { return false }   // a big-endian write (none yet)
        if llvm_aggregate(t) {
            // An aggregate is copied into the place, unless a call built it
            // there; from a big-endian view, its integers are swapped in the copy.
            if llvm_direct(e, place) { return false }
            if val == e.consumed && e.value[place] == e.slot {
                // The consumed param into the result: nothing to copy when the
                // caller passed its storage as the slot (`x = f(x, …)`).
                same := fresh_tmp(g)
                ir_icmp(g, same, "eq", "ptr", e.slot, val)
                copy, done := fresh_label(g, "consume.copy"), fresh_label(g, "consume.done")
                emit_cond_br(g, same, done, copy)
                emit_label(g, copy)
                llvm_copy(e, e.slot, val, t)
                emit_br(g, done)
                emit_label(g, done)
                return true
            }
            // From bytes (a view), copied as they are (llvm_view).
            from := NO_NODE
            if r := ops[1].op; pg.op[r] == .Read { from = graph_operands(pg, r)[0].op }
            if val != e.value[place] {
                if from != NO_NODE && pg.op[from] == .View {
                    emit_memcpy(g, e.value[place], val, type_size(t))
                } else {
                    llvm_copy(e, e.value[place], val, t)
                }
            }
            if from != NO_NODE && pg.op[from] == .View && graph_name(pg, from) == "#big_endian" {
                emit_bswap_in_place(g, e.value[place], llvm_type_from_checker(t), t)
            }
            return true
        }
        if !llvm_scalar(t) { return false }
        if llvm_direct(e, place) {
            d := pg.refers[place]
            if !e.held[d] { return false }   // a param is read-only
            e.value[d] = val
            return true
        }
        // A slice's len stays within 0 ..= its cap.
        if pg.op[place] == .Field && graph_name(pg, place) == "len" {
            hdr := graph_operands(pg, place)[0].op
            if llvm_header_elem(graph_type(pg, hdr)) != nil { emit_slice_len_check(g, e.value[hdr], val, span) }
        }
        if pg.op[place] == .View {   // into bytes at any address
            ir_store(g, llvm_type_from_checker(t), val, e.value[place], 1)
            return true
        }
        emit_store(g, llvm_type_from_checker(t), val, e.value[place])
    case .Deref:
        // What a pointer points at: the pointer's value is the place.
        place := ops[0].op
        if llvm_direct(e, place) {
            e.value[op] = llvm_direct_value(e, place)
        } else {
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, "ptr", e.value[place])
            e.value[op] = tmp
        }
    case .Field:
        base := ops[0].op
        if ut := llvm_union(graph_type(pg, base)); ut != nil {
            // A union's tag is at its start — read as load_union_tag reads it
            // (a niche union's is its pointer's nullness); its padding, just
            // past the tag.
            if llvm_direct(e, base) { return false }
            at := e.value[base]
            switch graph_name(pg, op) {
            case "tag": e.value[op] = at
            case "pad":
                if ut.tag_pad == nil { return false }
                pad := fresh_tmp(g)
                ir_gep(g, pad, "i8", at, strings.concatenate({"i32 ", ir_int(int(tag_bytes(ut.tag_type)))}, context.temp_allocator))
                e.value[op] = pad
            case: return false
            }
            return true
        }
        if llvm_header_elem(graph_type(pg, base)) != nil {
            // A slice header's len or cap; a held view's is its value.
            i := llvm_header_field(graph_name(pg, op))
            if i < 0 { return false }
            if h, held := llvm_held_header(e, base); held {
                e.value[op] = h.len if i == SLICE.len else h.cap if i == SLICE.cap else h.data
                e.held[op] = true
                return true
            }
            if llvm_direct(e, base) { return false }
            tmp := fresh_tmp(g)
            emit_slice_gep(g, tmp, e.value[base], i)
            e.value[op] = tmp
            return true
        }
        sd := llvm_struct(graph_type(pg, base))
        if sd == nil || llvm_direct(e, base) { return false }   // slice / union headers (later)
        i := struct_field_index(sd, graph_name(pg, op))
        if i < 0 { return false }                                // through a `using` field (later)
        tmp := fresh_tmp(g)
        emit_field_gep_into(g, tmp, llvm_type_from_checker(graph_type(pg, base)), e.value[base], i)
        e.value[op] = tmp
    case .Address:
        place := ops[0].op
        if llvm_direct(e, place) { return false }
        // A pointer to a place read as another type — a view of bytes: later.
        if pt, is_ptr := distinct_base(graph_type(pg, op)).(^Type_Ptr); is_ptr && !llvm_same_type(pt.elem, graph_type(pg, place)) {
            return false
        }
        e.value[op] = e.value[place]
    case .Construct:
        return llvm_construct(e, op, ops)
    case .Zero:
        // A bare declaration, or the start of a literal: zero.
        place := ops[0].op
        t := graph_type(pg, place)
        if len(ops) != 1 || llvm_direct(e, place) { return false }
        if llvm_zeroed(e, place) && pg.written[op] == .Synthetic { return true }
        switch {
        case llvm_scalar(t):    emit_store(g, llvm_type_from_checker(t), llvm_zero(t), e.value[place])
        case llvm_partial(t) != nil: emit_partial_array_zero(g, e.value[place], llvm_partial(t))
        case llvm_aggregate(t):
            emit_memset_zero(g, e.value[place], type_size(t))
            stamp_zero_partial_arrays(g, e.value[place], t)
        case:                   return false
        }
    case .Index:
        base := ops[0].op
        at := graph_type(pg, base)
        // Text has no header: a byte of it, bounded like its slice (the
        // terminating 0 counts).
        if text, is_text := llvm_text(e, base); is_text {
            i := llvm_operand(e, ops[1], slice_header_width_type) or_return
            global := get_string_literal(g, text)
            n := llvm_string_byte_length(text) + 1
            name := graph_place_name(pg, ops[0])
            emit_bounds_check(g, i, fmt.tprintf("%d", n), name if name != "" else "array", span)
            tmp := fresh_tmp(g)
            emit_array_gep_var(g, tmp, fmt.tprintf("[%d x i8]", n), global, i, "i64")
            e.value[op] = tmp
            return true
        }
        if elem := llvm_header_elem(at); elem != nil { return llvm_slice_index(e, op, ops, elem, span) }
        // An array's element: the index checked against its length — unless
        // the graph built it in range (a loop's element) — then its address.
        fa := llvm_array(at)
        if fa == nil || llvm_direct(e, base) { return false }   // slices, partial arrays (later)
        i := llvm_operand(e, ops[1], slice_header_width_type) or_return
        if pg.written[op] != .Synthetic {
            name := graph_place_name(pg, ops[0])
            emit_bounds_check(g, i, fmt.tprintf("%d", fa.size), name if name != "" else "array", span)
        }
        tmp := fresh_tmp(g)
        emit_array_gep_var(g, tmp, llvm_type_from_checker(at), e.value[base], i, "i64")
        e.value[op] = tmp
    case .Swizzle:
        // One component of a small array is its element. Several, written,
        // are the array (the write scatters into them); otherwise gathered
        // into a temporary, their value.
        base := ops[0].op
        at := graph_type(pg, base)
        fa := llvm_array(at)
        name := graph_name(pg, op)
        if fa == nil || llvm_direct(e, base) { return false }
        for c in transmute([]u8)name {
            if k := swizzle_char_to_index(c); k < 0 || k >= fa.size { return false }
        }
        from := e.value[base]
        if len(name) == 1 {
            tmp := fresh_tmp(g)
            emit_array_gep_const(g, tmp, llvm_type_from_checker(at), from, swizzle_char_to_index(name[0]))
            e.value[op] = tmp
            return true
        }
        if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write && graph_operands(pg, u)[0].op == op {
            e.value[op] = from
            return true
        }
        t := graph_type(pg, op)
        tmp := fresh_tmp(g)
        emit_alloca(g, tmp, llvm_type_from_checker(t))
        llvm_swizzle_copy(e, name, at, from, t, tmp, gather = true)
        e.value[op] = tmp
    case .Fill:
        return llvm_fill(e, ops)
    case .Arith:
        return llvm_arith(e, op, ops, span)
    case .Compare:
        return llvm_compare(e, op, ops)
    case .Unary:
        return llvm_unary(e, op, ops, span)
    case .Cast:
        x := ops[0].op
        from, to := graph_type(pg, x), graph_type(pg, op)
        if llvm_is_cstring(to) && !llvm_is_cstring(from) { return llvm_cstring(e, op, x, span) }
        // A partial array taken as a slice is its own header: no instruction.
        if llvm_partial(from) != nil && llvm_slice(to) != nil {
            // Text is no header: a view of its bytes, len its length (cap
            // counts the terminating zero).
            if text, is_text := llvm_text(e, x); is_text {
                n := len(text)
                e.value[op] = emit_build_temp_slice(g, e.value[x], fmt.tprintf("%d", n), fmt.tprintf("%d", n + 1))
                return true
            }
            e.value[op] = e.value[x]
            return true
        }
        from = llvm_type_of(e, ops[0])   // (a call's result: its own type)
        // A distinct conversion of an aggregate (`V3(raw)`): the same bytes,
        // where they are.
        if llvm_aggregate(from) && llvm_same_type(distinct_base(from), distinct_base(to)) {
            e.value[op] = e.value[x]
            return true
        }
        if !llvm_scalar(from) || !llvm_scalar(to) { return false }
        v := llvm_operand(e, ops[0], from) or_return
        e.value[op] = llvm_convert(e, v, from, to)
    case .Call:
        return llvm_call(e, op, ops)
    case .Jump:
        emit_br(g, e.label[llvm_target(e, op, 0)])
    case .Branch:
        c, ok := llvm_operand(e, ops[0], Type_Bool{})
        if !ok { return false }
        emit_cond_br(g, c, e.label[llvm_target(e, op, 0)], e.label[llvm_target(e, op, 1)])
    case .Return:
        if e.ctor {
            // Self was built in place; the declared results after it (a
            // fallible constructor's err) are stored.
            if len(ops) != max(len(e.rets) - 1, 0) { return false }
            for o, i in ops {
                rt := e.rets[i + 1]
                v := llvm_operand(e, o, rt) or_return
                emit_store(g, llvm_type_from_checker(rt), v, fmt.tprintf("%%sret.%d", i + 1))
            }
            llvm_ret(e, "void")
            return true
        }
        // Falling off the end with a result (a shape's method, no body — the
        // checker lets nothing else): the slot as it is, a register's zero.
        fell_off := len(ops) == 0 && pg.written[op] == .Synthetic
        if e.sret != nil {
            if fell_off {
                llvm_ret(e, "void")
                return true
            }
            // Into the caller's slot, unless it was built there.
            if len(ops) != 1 { return false }
            v := llvm_operand(e, ops[0], e.sret) or_return
            if v != e.slot { llvm_copy(e, e.slot, v, e.sret) }
            llvm_ret(e, "void")
            return true
        }
        if e.rets != nil {
            // Each result into the caller's slot for it: a register value stored,
            // an aggregate copied (unless built there), a zero value stored whole.
            if len(ops) != len(e.rets) { return false }
            for rt, i in e.rets {
                at := fmt.tprintf("%%sret.%d", i)
                v := llvm_operand(e, ops[i], rt) or_return
                switch {
                case v == "zeroinitializer" || llvm_scalar(rt):
                    emit_store(g, llvm_type_from_checker(rt), v, at)
                case v != at:
                    llvm_copy(e, at, v, rt)
                }
            }
            llvm_ret(e, "void")
            return true
        }
        if len(ops) == 0 {
            if e.main {   // the C entry point: 0, the program went well
                llvm_ret(e, "i64", "0")
                return true
            }
            if e.ret != "void" && fell_off {
                llvm_ret(e, e.ret, llvm_zero(fn_result(e.ft, 0)))
                return true
            }
            if e.ret != "void" { return false }
            llvm_ret(e, "void")
            return true
        }
        if len(ops) != 1 || e.ret == "void" { return false }
        v, ok := llvm_operand(e, ops[0], fn_result(e.ft, 0))
        if !ok { return false }
        llvm_ret(e, e.ret, v)
    case .Assert:
        return llvm_assert(e, op, ops, span)
    case .Slice:
        return llvm_slice_op(e, op, ops)
    case .View:
        return llvm_view(e, op, ops, span)
    case .Carve:
        return llvm_carve(e, op, ops, span)
    case .Global:
        // A string constant: its bytes' address (its text is in the
        // constants table). A constant table: its global, read-only. A
        // function: its symbol.
        if ft, is_fn := graph_type(pg, op).(^Type_Scope); is_fn && ft.kind == .Fun {
            if fo, is_foreign := ft.origin.(Origin_Foreign); is_foreign {   // a C function: its link symbol
                e.value[op] = strings.concatenate({"@", fo.link_name if fo.link_name != "" else ft.name})
                return true
            }
            if _, src := ft.origin.(Origin_Source); !src { return false }   // (an intrinsic's: later)
            e.value[op] = mara_fn_name(g, ft.name)
            return true
        }
        if c, has := graph_value(pg, op); has && c.is_text {
            tmp := get_string_literal(g, c.text)
            e.value[op] = tmp
            return true
        }
        c := pg.constant[op]
        if c == 0 || c not_in g.checked.code.tables || !is_table_const(graph_type(pg, op)) { return false }
        e.value[op] = const_table(g, &g.checked.code, c, span)
    case .Byte_Read:
        return llvm_byte_read(e, op, ops, span)
    case .Print:
        return llvm_print(e, op, ops, span)
    case .Crash:
        // Its message is text (one computed at runtime: later).
        msg := ""
        if len(ops) == 1 {
            if _, is_text := llvm_text(e, ops[0].op); !is_text { return false }
            msg = e.value[ops[0].op]
        }
        emit_crash(g, span, msg)
    case .Variant:
        // A union seen as one of its variants: each variant's struct overlays
        // the union from its start, so it is the union's own address.
        u := ops[0].op
        if llvm_union(graph_type(pg, u)) == nil || llvm_struct(graph_type(pg, op)) == nil || llvm_direct(e, u) { return false }
        e.value[op] = e.value[u]
    case .Switch:
        return llvm_switch(e, op, ops, span)
    case .Run_Defer:
        return llvm_run_defer(e, op)
    case .Arena_Mark:
        emit_arena_mark(g)
    case .Arena_Reset:
        emit_arena_reset(g)
    case .Arena_Alloc:
        // A big local: its storage, bumped from the arena (reset when its
        // scope is left).
        d := pg.refers[ops[0].op]
        if d <= 0 || d > pg.end || pg.kind[d] != .Local { return false }
        e.value[d] = emit_arena_bump(g, type_size(graph_type(pg, op)), graph_name(pg, d), span_location(span))
    }
    return true
}

// A place's address, even before its operation is reached: a variable names
// its storage whatever comes first (a declaration's value precedes its var).
@(private="file")
llvm_place :: proc(e: ^Llvm, place: Node_Id) -> string {
    pg := e.pg
    if pg.op[place] != .Var { return e.value[place] }
    d := pg.refers[place]
    switch {
    case e.ctor && d == 0:                          return e.slot
    case pg.kind[d] == .Param || pg.kind[d] == .Field:   return e.value[d]
    }
    return llvm_storage(e, d)
}

// A named result: a local the code writes, kept where its result goes. With
// several results, a struct or fixed array in the caller's slot for it, a
// register value a local of its own, zeroed first; a single struct result the
// result slot itself, its partial arrays' headers stamped first; a single
// register value a plain local.
@(private="file")
llvm_named_result :: proc(e: ^Llvm, d: Node_Id) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, d)
    i := 0   // which result
    for id := Node_Id(1); id < d; id += 1 { if pg.kind[id] == .Result && pg.parent[id] == 0 { i += 1 } }
    if e.rets != nil && !e.ctor {
        switch {
        case llvm_struct(t) != nil || llvm_array(t) != nil:
            e.value[d] = fmt.tprintf("%%sret.%d", i)
        case llvm_scalar(t):
            // (At the entry, before the code's own allocas.)
            name := fmt.tprintf("%%%s", graph_name(pg, d))
            for n := 2; e.used[name]; n += 1 { name = fmt.tprintf("%%%s.%d", graph_name(pg, d), n) }
            e.used[name] = true
            ir := llvm_type_from_checker(t)
            append(&e.fields, Ir{op = .Alloca, dest = name, ty = ir}, Ir{op = .Store, ty = ir, a = llvm_zero(t), b = name})
            e.value[d] = name
        case:
            e.note = "a named result's type"
            return false
        }
        return true
    }
    // A single register value: a local like any other, its alloca where the
    // code first needs it (llvm_storage).
    if e.sret == nil && !e.ctor && llvm_scalar(t) { return true }
    st := llvm_struct(t)
    if e.sret == nil || st == nil || e.ctor { e.note = "a named result"; return false }
    e.value[d] = e.slot
    llvm_into_fields(e, true)
    fixup_partial_array_fields(g, e.slot, st)
    llvm_into_fields(e, false)
    return true
}

// `{all x}`: every element of an array — a fixed array's, or all of a
// partial array's, its len then its cap — the one value: a register value
// stored, an aggregate copied (its partial arrays re-pointed).
@(private="file")
llvm_fill :: proc(e: ^Llvm, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    place := ops[0].op
    at := graph_type(pg, place)
    if llvm_direct(e, place) { return false }
    to := e.value[place]
    elem: Type
    n: int
    pa := llvm_partial(at)
    if fa := llvm_array(at); fa != nil {
        elem, n = fa.elem, fa.size
    } else if pa != nil {
        elem, n = pa.elem, pa.size
    } else {
        return false
    }
    if !llvm_scalar(elem) && !llvm_aggregate(elem) { return false }
    v := llvm_operand(e, ops[1], elem) or_return
    ir := llvm_type_from_checker(elem)
    for k in 0 ..< n {
        slot := fresh_tmp(g)
        if pa != nil {
            ir_gep_inbounds(g, slot, partial_array_ir_type(ir, pa.size), to, "i32 0", strings.concatenate({"i32 ", ir_int(int(PARTIAL_ELEMENTS_FIELD))}, context.temp_allocator), strings.concatenate({"i32 ", ir_int(int(k))}, context.temp_allocator))
        } else {
            emit_array_gep_const(g, slot, llvm_type_from_checker(at), to, k)
        }
        if llvm_scalar(elem) { emit_store(g, ir, v, slot) } else { llvm_copy(e, slot, v, elem) }
    }
    if pa != nil {
        emit_header_set(g, to, SLICE.len, fmt.tprintf("%d", pa.size))
    }
    return true
}

// `x = void`, or a declaration `x : T = void`: uninitialized. A pointer is
// null either way. A declared scalar is zero (a read of it before a write is
// the flow check's to catch); a reassigned one keeps its bytes. A declared
// partial array gets its header — its elements left as they are; a declared
// local struct is zero; any other aggregate nothing.
@(private="file")
llvm_write_void :: proc(e: ^Llvm, op, place: Node_Id) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, place)
    decl := graph_stmt(pg, op).kind == .Decl
    if llvm_direct(e, place) { return false }
    // A constructor's field is left as Self's zero (its caller zeroed Self):
    // nothing written, but a pointer's null.
    if llvm_zeroed(e, place) && llvm_type_from_checker(t) != "ptr" { return true }
    switch {
    case llvm_scalar(t):
        ir := llvm_type_from_checker(t)
        if ir == "ptr" { emit_store(g, ir, "null", e.value[place]) }
        else if decl { emit_store(g, ir, llvm_zero(t), e.value[place]) }
    case llvm_partial(t) != nil:
        if decl { emit_partial_array_zero(g, e.value[place], llvm_partial(t), zero = false) }
    case llvm_struct(t) != nil:
        // A declared local struct is zero (a constructor's field is left as
        // it is, in Self zeroed already).
        local := pg.op[place] == .Var && pg.kind[pg.refers[place]] == .Local
        if decl && local { emit_memset_zero(g, e.value[place], type_size(t)) }
    case llvm_aggregate(t):
    case:
        return false
    }
    return true
}

// Whether a place holds its value directly, not at an address: a scalar param
// (read-only, its argument) or a held synthetic local.
@(private="file")
llvm_direct :: proc(e: ^Llvm, place: Node_Id) -> bool {
    pg := e.pg
    if pg.op[place] != .Var { return e.held[place] }   // a held view's len or cap
    d := pg.refers[place]
    if pg.kind[d] == .Param { return llvm_scalar(graph_type(pg, d)) }
    if d <= 0 || d > pg.end { return false }   // this_program's: in memory
    return e.held[d]
}

@(private="file")
llvm_direct_value :: proc(e: ^Llvm, place: Node_Id) -> string {
    if e.pg.op[place] != .Var { return e.value[place] }
    return e.value[e.pg.refers[place]]
}

// An operand's IR value, which must already be of the type its use takes.
@(private="file")
llvm_operand :: proc(e: ^Llvm, o: Operand, want: Type) -> (string, bool) {
    if o.op == NO_NODE { return "", false }
    if at, several := e.outs[o.op]; several { return llvm_output(e, o, at, want) }
    if o.out != 0 { return "", false }
    have := graph_type(e.pg, o.op)
    if !llvm_same_type(have, want) { return "", false }
    return e.value[o.op], true
}

// A call's k-th result, from the temporary it wrote it into: a register value
// loaded where it is used, an aggregate its temporary.
@(private="file")
llvm_output :: proc(e: ^Llvm, o: Operand, at: []string, want: Type) -> (string, bool) {
    if int(o.out) >= len(at) { return "", false }
    t := llvm_type_of(e, o)
    if !llvm_same_type(t, want) { return "", false }
    if !llvm_scalar(t) { return at[o.out], true }
    if v, done := e.loaded[o]; done { return v, true }
    v := fresh_tmp(e.g)
    emit_load_into(e.g, v, llvm_type_from_checker(t), at[o.out])
    if e.run == e.out_run[o.op] { e.loaded[o] = v }
    return v, true
}

// The type of an operation's output: a call's k-th result, else its own.
@(private="file")
llvm_type_of :: proc(e: ^Llvm, o: Operand) -> Type {
    if o.op in e.outs {
        callee := graph_signature(e.pg, o.op)
        if callee != nil && int(o.out) < fn_result_count(callee) { return fn_result(callee, int(o.out)) }
    }
    return graph_type(e.pg, o.op)
}

// The run the k-th Then edge of an operation leads to.
@(private="file")
llvm_target :: proc(e: ^Llvm, op: Node_Id, k: int) -> i32 {
    n := 0
    for edge in graph_out(e.pg, op) {
        if n == k { return e.pg.run_starts[edge.to] }
        n += 1
    }
    return -1
}

// A constant's IR literal at its type.
@(private="file")
llvm_const :: proc(e: ^Llvm, op: Node_Id) -> (string, bool) {
    t := graph_type(e.pg, op)
    v, ok := graph_value(e.pg, op)
    if !ok || !llvm_scalar(t) { return "", false }
    ir := llvm_type_from_checker(t)
    if ir == "i1" { return "true" if v.int != 0 else "false", true }
    return emit_number_literal(ir, v.float if v.is_float else f64(v.int), v.int, v.is_float), true
}

@(private="file")
llvm_arith :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, op)
    if !llvm_scalar(t) { return false }
    l, lok := llvm_operand(e, ops[0], t)
    r, rok := llvm_operand(e, ops[1], t)
    if !lok || !rok { return false }
    ir := llvm_type_from_checker(t)
    name := graph_name(pg, op)
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
        ir_bin(g, tmp, inst, ir, l, r)
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
            ir_bin(g, tmp, inst, ir, l, r)
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
            ir_bin(g, tmp, inst, ir, l, r)
        }
    }
    e.value[op] = tmp
    return true
}

@(private="file")
llvm_compare :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, ops[0].op)
    if !llvm_scalar(t) { return false }
    l, lok := llvm_operand(e, ops[0], t)
    r, rok := llvm_operand(e, ops[1], t)
    if !lok || !rok { return false }
    ir := llvm_type_from_checker(t)
    name := graph_name(pg, op)
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
        ir_fcmp(g, tmp, pred, ir, l, r)
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
        ir_icmp(g, tmp, pred, ir, l, r)
    }
    e.value[op] = tmp
    return true
}

@(private="file")
llvm_unary :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    t := graph_type(pg, op)
    if !llvm_scalar(t) { return false }
    x, ok := llvm_operand(e, ops[0], t)
    if !ok { return false }
    ir := llvm_type_from_checker(t)
    tmp: string
    switch graph_name(pg, op) {
    case "-":
        if is_ir_float(ir) {
            tmp = fresh_tmp(g)
            ir_fneg(g, tmp, ir, x)
        } else {
            // Integer negation is `0 - x`, overflow-checked: -MIN traps.
            tmp = emit_checked_arith(g, "usub" if llvm_unsigned(t) else "ssub", ir, "0", x, span)
        }
    case "-%":
        tmp = fresh_tmp(g)
        ir_bin(g, tmp, "sub", ir, "0", x)
    case "not":
        tmp = fresh_tmp(g)
        ir_bin(g, tmp, "xor", "i1", x, "true")
    case "~":
        tmp = fresh_tmp(g)
        ir_bin(g, tmp, "xor", ir, x, "-1")
    case:
        return false
    }
    e.value[op] = tmp
    return true
}

// A number's conversion: widening by the source's signedness, narrowing by
// truncation, between ints and floats by the target's (to an int) or the
// source's (from one) signedness; to a bool, whether it's nonzero.
@(private="file")
llvm_convert :: proc(e: ^Llvm, v: string, from, to: Type) -> string {
    g := e.g
    fi, ti := llvm_type_from_checker(from), llvm_type_from_checker(to)
    if fi == ti { return v }
    tmp := fresh_tmp(g)
    if ti == "i1" && fi == "ptr" {   // to bool: whether it's not null
        ir_icmp(g, tmp, "ne", "ptr", v, "null")
        return tmp
    }
    // A pointer as a number (`i64(w)`, a handle), or back: its address.
    if fi == "ptr" || ti == "ptr" {
        ir_cast(g, tmp, "ptrtoint" if fi == "ptr" else "inttoptr", fi, v, ti)
        return tmp
    }
    ff, tf := is_ir_float(fi), is_ir_float(ti)
    if ti == "i1" && !ff {   // to bool: whether it's nonzero
        ir_icmp(g, tmp, "ne", fi, v, "0")
        return tmp
    }
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
    ir_cast(g, tmp, inst, fi, v, ti)
    return tmp
}

// Whether a place is already zero: a constructor's field — a constructor
// runs on storage its caller zeroed.
@(private="file")
llvm_zeroed :: proc(e: ^Llvm, place: Node_Id) -> bool {
    pg := e.pg
    return e.ctor && pg.op[place] == .Var && pg.refers[place] != NO_NODE && pg.kind[pg.refers[place]] == .Field
}

// A construction's arguments, past its place: each at its constructor's
// param's type, typed ("i64 6").
@(private="file")
llvm_ctor_args :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> (args: []string, ok: bool) {
    if len(ops) == 1 { return nil, true }
    callee := graph_called(e.pg, op)
    if callee == nil || len(ops) - 1 != len(callee.params) { return nil, false }
    args = make([]string, len(callee.params), context.temp_allocator)
    for _, i in callee.params {
        p := fn_param(callee, i)
        ir := llvm_param_type(p.type_) or_return
        v := llvm_operand(e, ops[i + 1], p.type_) or_return
        args[i] = fmt.tprintf("%s %s", ir, v)
    }
    return args, true
}

// A variant's constructor run at `at` on `args` (its params'), when it has
// one — a body: its fields' defaults; a variant's body with no constructor
// built is an error. (The arguments are the caller's to compute first: the
// union is zeroed before the call.)
@(private="file")
llvm_variant_ctor :: proc(e: ^Llvm, op: Node_Id, at: string, args: []string) -> bool {
    callee := graph_called(e.pg, op)
    if callee == nil || callee.node == 0 { return len(args) == 0 }
    if _, built := e.g.checked.functions[callee.name]; !built { e.note = "a variant's constructor"; return false }
    all := make([dynamic]string, 0, len(args) + 1, context.temp_allocator)
    append(&all, ..args)
    append(&all, fmt.tprintf("ptr %s", at))
    ir_call(e.g, "", "void", mara_fn_name(e.g, callee.name), ..all[:])
    return true
}

// A struct built in place: its storage zeroed, then its constructor run on it
// with the arguments, the place last. An array's elements, zeroed already,
// each run theirs.
@(private="file")
llvm_construct :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    t := graph_type(pg, op)
    if ut := llvm_union(graph_type(pg, dest)); ut != nil && llvm_same_type(graph_type(pg, dest), t) {
        // A variant: the union zeroed — its bytes past the variant too — then
        // its tag, and its partial arrays' headers. (Its defaults and fields
        // are the writes that follow.)
        if llvm_direct(e, dest) { return false }
        args := llvm_ctor_args(e, op, ops) or_return   // (before the union is zeroed)
        at := e.value[dest]
        if some := ut.niche_some; some != "" {
            // A niche union is its Some variant's pointer: None is null, Some
            // the pointer its literal writes next (none written: null).
            if graph_name(pg, op) != some || !llvm_variant_written(e, op, dest) { emit_store(g, "ptr", "null", at) }
            return llvm_variant_ctor(e, op, at, args)
        }
        st := ut.variant_structs[graph_name(pg, op)]
        if st == nil { return false }
        emit_memset_zero(g, at, type_size(graph_type(pg, dest)))
        tag := fresh_tmp(g)
        emit_field_gep_into(g, tag, llvm_type_from_checker(st), at, 0)
        emit_store(g, union_tag_ir_type(ut), fmt.tprintf("%d", ut.tag_map[graph_name(pg, op)]), tag)
        stamp_zero_partial_arrays(g, at, st)   // (a partial array's zero isn't all zeros: no constructor stamps a variant's)
        return llvm_variant_ctor(e, op, at, args)
    }
    // An array's elements: each constructed on the same arguments.
    if fa := llvm_array(graph_type(pg, dest)); fa != nil && llvm_same_type(fa.elem, t) {
        if llvm_direct(e, dest) { return false }
        args := llvm_ctor_args(e, op, ops) or_return
        gen_construct_elements(g, e.value[dest], fa.elem, fa.size, args)
        return true
    }
    if pa := llvm_partial(graph_type(pg, dest)); pa != nil && llvm_same_type(pa.elem, t) {
        if llvm_direct(e, dest) { return false }
        if llvm_zeroed(e, dest) { return true }   // a constructor's field: at its entry
        args := llvm_ctor_args(e, op, ops) or_return
        elements := partial_elements(g, e.value[dest], pa)
        gen_construct_elements(g, elements, pa.elem, pa.size, args)
        return true
    }
    callee := graph_called(e.pg, op)
    if callee == nil || callee.kind != .Struct || llvm_struct(t) == nil || llvm_direct(e, dest) { return false }
    if !llvm_same_type(graph_type(pg, dest), t) { return false }   // an array's elements (later)
    if callee.is_union_variant {
        // A union's variant as a struct of its own: zeroed, its tag in field
        // 0, its partial arrays' headers, then its constructor.
        args := llvm_ctor_args(e, op, ops) or_return   // (before it is zeroed)
        at := e.value[dest]
        emit_memset_zero(g, at, type_size(t))
        tag := fresh_tmp(g)
        emit_field_gep_into(g, tag, llvm_type_from_checker(t), at, 0)
        emit_store(g, field_ir_type(&callee.fields[0]), fmt.tprintf("%d", callee.union_variant_tag), tag)
        stamp_zero_partial_arrays(g, at, callee)
        return llvm_variant_ctor(e, op, at, args)
    }
    if _, has_init := g.checked.functions[callee.name]; !has_init && len(ops) == 1 {
        // Nothing to run — no defaults, no partial arrays (a generic instance
        // whose fields a shape shortcut fills): its zero.
        if !(llvm_zeroed(e, dest) && pg.written[op] == .Synthetic) { emit_memset_zero(g, e.value[dest], type_size(t)) }
        return true
    }
    if _, src := callee.origin.(Origin_Source); !src { return false }
    ctor := llvm_ctor_args(e, op, ops) or_return
    args := make([dynamic]string, 0, len(ops), context.temp_allocator)
    append(&args, ..ctor)
    at := e.value[dest]
    append(&args, fmt.tprintf("ptr %s", at))
    // A fallible constructor's declared results (its err) after Self: each
    // into a temporary, where its uses find it (Self is the place).
    if fn_result_count(callee) > 1 {
        outs := make([]string, fn_result_count(callee))
        outs[0] = at
        for ri in 1 ..< fn_result_count(callee) {
            rt, i := fn_result(callee, ri), ri - 1
            if !llvm_scalar(rt) { e.note = "result type"; return false }
            outs[i + 1] = fresh_tmp(g)
            emit_alloca(g, outs[i + 1], llvm_type_from_checker(rt))
            append(&args, fmt.tprintf("ptr %s", outs[i + 1]))
        }
        e.outs[op], e.out_run[op] = outs, e.run
    }
    // A bare field of a constructor is already zero; a literal is a fresh value anywhere.
    if !(llvm_zeroed(e, dest) && pg.written[op] == .Synthetic) { emit_memset_zero(g, at, type_size(t)) }
    ir_call(g, "", "void", mara_fn_name(g, callee.name), ..args[:])
    return true
}

// A slice's element: the header's pointer, and — unless the graph built the
// index in range (a loop's element) — its cap, the index checked against it;
// then the element's address.
@(private="file")
llvm_slice_index :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, elem: Type, span: Span) -> bool {
    g, pg := e.g, e.pg
    base := ops[0].op
    if llvm_direct(e, base) { return false }
    i := llvm_operand(e, ops[1], slice_header_width_type) or_return
    h, held := llvm_held_header(e, base)
    hdr := e.value[base]
    data := h.data
    if !held {
        data = emit_header_field(g, hdr, SLICE.ptr)
    }
    if pg.written[op] != .Synthetic {
        cap_val := h.cap
        if !held {
            cap_val = emit_header_field(g, hdr, SLICE.cap)
        }
        name := graph_place_name(pg, ops[0])
        emit_bounds_check(g, i, cap_val, name if name != "" else "slice", span)
    }
    tmp := fresh_tmp(g)
    emit_elem_gep(g, tmp, llvm_type_from_checker(elem), data, i, SLICE_LEN_IR)
    e.value[op] = tmp
    return true
}

// Whether a slice operation views a whole fixed array: no bounds given.
@(private="file")
llvm_whole_array :: proc(e: ^Llvm, op: Node_Id) -> bool {
    pg := e.pg
    if pg.op[op] != .Slice || graph_name(pg, op) != "" { return false }
    ops := graph_operands(pg, op)
    if len(ops) == 0 || ops[0].op == NO_NODE || llvm_array(graph_type(pg, ops[0].op)) == nil { return false }
    for o in ops[1:] { if o.op != NO_NODE { return false } }
    return true
}

// A slice of an array or a slice: the elements from lo up to hi — lo 0 and
// hi the array's size or the slice's len when not given — as a new header,
// len = cap = hi - lo.
@(private="file")
llvm_slice_op :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    if graph_name(pg, op) == "slice_from_ptr" {
        // Over raw memory: its pointer, len = cap = the count given.
        if len(ops) != 2 || ops[0].op == NO_NODE { return false }
        if _, is_ptr := distinct_base(graph_type(pg, ops[0].op)).(^Type_Ptr); !is_ptr { return false }
        n := llvm_operand(e, ops[1], slice_header_width_type) or_return
        e.value[op] = emit_build_temp_slice(g, e.value[ops[0].op], n, n)
        return true
    }
    if graph_name(pg, op) != "" { return false }
    // Written to, it's the run of elements a write fills (llvm_copy_into).
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write && graph_operands(pg, u)[0].op == op { return true }
    // A whole fixed array viewed only to be copied from: the array itself, no
    // header (llvm_copy_into reads it as the array).
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write && graph_operands(pg, u)[1].op == op &&
       pg.op[graph_operands(pg, u)[0].op] == .Slice && llvm_whole_array(e, op) {
        e.value[op] = e.value[ops[0].op]
        return true
    }
    // A whole fixed array — not a constant's table — viewed into a slice's
    // place (a field, an element, what a pointer points at): its header built
    // there (the write then has nothing to copy).
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write && graph_operands(pg, u)[1].op == op && llvm_whole_array(e, op) && pg.op[ops[0].op] != .Global {
        dest := graph_operands(pg, u)[0].op
        #partial switch pg.op[dest] {
        case .Field, .Index, .Deref:
        case:
            dest = NO_NODE
        }
        if dest != NO_NODE && llvm_slice(graph_type(pg, dest)) != nil && !llvm_direct(e, dest) && llvm_ahead(e, dest) {
            at := llvm_place(e, dest)
            n := fmt.tprintf("%d", llvm_array(graph_type(pg, ops[0].op)).size)
            emit_slice_header_at(g, at, e.value[ops[0].op], n, n)
            e.value[op] = at
            return true
        }
    }
    base := ops[0].op
    if base == NO_NODE || llvm_direct(e, base) { return false }
    lo, hi: string
    if len(ops) > 1 && ops[1].op != NO_NODE { lo = llvm_operand(e, ops[1], slice_header_width_type) or_return }
    if len(ops) > 2 && ops[2].op != NO_NODE { hi = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    bt := graph_type(pg, base)
    at := e.value[base]
    data: string
    if text, is_text := llvm_text(e, base); is_text {
        // Text in its global (a constant's, a literal's): its bytes' address,
        // its length known — no header there to read.
        data = at
        if hi == "" { hi = fmt.tprintf("%d", len(text)) }
        if lo != "" {
            data = fresh_tmp(g)
            emit_elem_gep(g, data, "i8", at, lo, SLICE_LEN_IR)
        }
    } else if fa := llvm_array(bt); fa != nil {
        data = at
        if hi == "" { hi = fmt.tprintf("%d", fa.size) }
        if lo != "" {
            data = fresh_tmp(g)
            emit_array_gep_var(g, data, llvm_type_from_checker(bt), at, lo, SLICE_LEN_IR)
        }
    } else if elem := llvm_header_elem(bt); elem != nil {
        data = emit_header_field(g, at, SLICE.ptr)
        if hi == "" {
            hi = emit_header_field(g, at, SLICE.len)
        }
        if lo != "" {
            from := data
            data = fresh_tmp(g)
            emit_elem_gep(g, data, llvm_type_from_checker(elem), from, lo, SLICE_LEN_IR)
        }
    } else {
        return false   // a partial array (later)
    }
    n := hi
    if lo != "" {
        n = fresh_tmp(g)
        ir_bin(g, n, "sub", SLICE_LEN_IR, hi, lo)
    }
    // Written to a held view: its values, no header in memory.
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write {
        if d := graph_operands(pg, u)[0].op; pg.op[d] == .Var && pg.refers[d] in e.hdr {
            e.hdr[pg.refers[d]] = {data, n, n}
            return true
        }
    }
    e.value[op] = emit_build_temp_slice(g, data, n, n)
    return true
}

// Bytes at an offset seen as a T: the buffer's data and its bound — a byte
// slice's or partial array's pointer and cap, a byte array's own address and
// size — the offset checked (offset + the size of T within the bound), then
// the byte's address. What's read or written there is a T at any alignment.
@(private="file")
llvm_view :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    base := ops[0].op
    t := graph_type(pg, op)
    // A positional slice carve takes its own run of the bytes (llvm_carve).
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Carve && graph_name(pg, u) == "slice" { return true }
    // A partial array in the bytes: bound by a `let`, it is the memory
    // itself; copied out whole into a place (`h : T = bytes[0]`), its header
    // comes with the bytes, as they are — what fills it next restamps it
    // (a view read any other way: later).
    u := e.st.user[op]
    bound_here := u >= 0 && pg.op[u] == .Carve && graph_name(pg, u) == "let"
    copied := u >= 0 && pg.op[u] == .Read && e.st.user[u] >= 0 && pg.op[e.st.user[u]] == .Write &&
              graph_operands(pg, e.st.user[u])[1].op == u
    if llvm_direct(e, base) || (!llvm_scalar(t) && !llvm_aggregate(t)) || (value_has_partial_array(g, t) && !bound_here && !copied) { return false }
    off := llvm_operand(e, ops[1], slice_header_width_type) or_return
    data, bound := llvm_bytes(e, base) or_return
    emit_byte_size_bounds_check(g, bound, off, type_size(t), "view", span)
    // (A span written, lo:hi: as many bytes as the value has — where its
    // bounds aren't numbers; the checker said so where they are.)
    if len(ops) > 2 && ops[2].op != NO_NODE {
        hi := llvm_operand(e, ops[2], slice_header_width_type) or_return
        if !can_elide_span_check(off, hi) {
            w := SLICE_LEN_IR
            n := fresh_tmp(g)
            ir_bin(g, n, "sub", w, hi, off)
            ok, bad := fresh_label(g, "byte.span.ok"), fresh_label(g, "byte.span.err")
            cmp := fresh_tmp(g)
            ir_icmp(g, cmp, "ne", w, n, ir_int(int(type_size(t))))
            emit_cond_br(g, cmp, bad, ok)
            emit_label(g, bad)
            loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
            emit_fail(g, fmt.tprintf("%s runtime error: byte buffer write: the span is %%lld bytes, the value %d\n", loc, type_size(t)), fail_i64(n))
            emit_label(g, ok)
        }
    }
    tmp := fresh_tmp(g)
    ir_gep(g, tmp, "i8", data, strings.concatenate({SLICE_LEN_IR, " ", off}, context.temp_allocator))
    e.value[op] = tmp
    return true
}

// `dst[lo:hi] = src`: src's elements copied into dst from lo on — hi - lo of
// them, or, hi open, all of src's — with lo within dst's cap and hi no
// further than it; each copied element's partial arrays re-pointed.
@(private="file")
llvm_copy_into :: proc(e: ^Llvm, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    run := ops[0].op
    rops := graph_operands(pg, run)
    base, src := rops[0].op, ops[1].op
    if graph_name(pg, run) != "" || len(rops) < 2 || rops[1].op == NO_NODE || src == NO_NODE || llvm_direct(e, base) { return false }
    lo := llvm_operand(e, rops[1], slice_header_width_type) or_return
    hi := ""
    if len(rops) > 2 && rops[2].op != NO_NODE { hi = llvm_operand(e, rops[2], slice_header_width_type) or_return }
    // Each side's data and extent: a fixed array's own, else its header's.
    Side :: struct { data, bound: string, fixed: int, elem: Type }
    side :: proc(e: ^Llvm, at: Node_Id, bound_field: int) -> (s: Side, ok: bool) {
        g, pg := e.g, e.pg
        t := graph_type(pg, at)
        if llvm_whole_array(e, at) { t = graph_type(pg, graph_operands(pg, at)[0].op) }   // the array it views
        addr := e.value[at]
        if fa := llvm_array(t); fa != nil { return {addr, fmt.tprintf("%d", fa.size), fa.size, fa.elem}, true }
        s.elem = llvm_header_elem(t)
        if s.elem == nil { return }
        s.data = emit_header_field(g, addr, SLICE.ptr)
        if bound_field >= 0 { s.bound = emit_header_field(g, addr, bound_field) }
        return s, true
    }
    dst := side(e, base, SLICE.cap) or_return
    from := side(e, src, -1) or_return
    w := SLICE_LEN_IR
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    if !llvm_same_type(dst.elem, from.elem) && is_byte_elem(from.elem) && !is_byte_elem(dst.elem) {
        // From bytes into another type's elements (tc_byte_read_run): the
        // bytes copied in raw — an open run as many elements as they make (a
        // whole number), a written one exactly its elements' bytes — within
        // dst's cap. (Elements holding a partial array: their headers would
        // point into the bytes — later.)
        if value_has_partial_array(g, dst.elem) { return false }
        size := type_size(dst.elem)
        elem_name := type_name(dst.elem)
        nbytes := from.bound if from.bound != "" else emit_header_field(g, e.value[src], SLICE.len)
        count := fresh_tmp(g)
        ok, bad := fresh_label(g, "byte.read.ok"), fresh_label(g, "byte.read.err")
        cmp := fresh_tmp(g)
        if hi == "" {
            rem := fresh_tmp(g)
            ir_bin(g, rem, "urem", w, nbytes, ir_int(int(size)))
            ir_icmp(g, cmp, "ne", w, rem, "0")
            emit_cond_br(g, cmp, bad, ok)
            emit_label(g, bad)
            emit_fail(g, fmt.tprintf("%s runtime error: byte read: %%lld bytes aren't a whole number of %s (%d bytes each)\n", loc, elem_name, size), fail_i64(nbytes))
            emit_label(g, ok)
            ir_bin(g, count, "udiv", w, nbytes, ir_int(int(size)))
        } else {
            ir_bin(g, count, "sub", w, hi, lo)
            want := fresh_tmp(g)
            ir_bin(g, want, "mul", w, count, ir_int(int(size)))
            ir_icmp(g, cmp, "ne", w, want, nbytes)
            emit_cond_br(g, cmp, bad, ok)
            emit_label(g, bad)
            emit_fail(g, fmt.tprintf("%s runtime error: byte read: a run of %%lld %s is %%lld bytes, but the bytes are %%lld\n", loc, elem_name),
                      fail_i64(count), fail_i64(want), fail_i64(nbytes))
            emit_label(g, ok)
        }
        in_ok, in_bad := fresh_label(g, "byte.read.in"), fresh_label(g, "byte.read.past")
        emit_cond_br(g, emit_byte_span_outside(g, lo, count, dst.bound), in_bad, in_ok)
        emit_label(g, in_bad)
        emit_fail(g, fmt.tprintf("%s runtime error: byte read out of bounds: offset %%lld + %%lld elements > capacity %%lld\n", loc),
                  fail_i64(lo), fail_i64(count), fail_i64(dst.bound))
        emit_label(g, in_ok)
        at := fresh_tmp(g)
        emit_elem_gep(g, at, llvm_type_from_checker(dst.elem), dst.data, lo, w)
        emit_memcpy_runtime(g, at, from.data, nbytes)
        return true
    }
    if !llvm_same_type(dst.elem, from.elem) {
        if !is_byte_elem(dst.elem) || is_byte_elem(from.elem) { return false }
        // Into bytes, src's elements' raw bytes (a slice's, a partial array's:
        // tc_byte_span_checks): count × size, from lo — within the bytes' cap,
        // and the span's size when hi is written.
        size := type_size(from.elem)
        count := from.bound if from.bound != "" else emit_header_field(g, e.value[src], SLICE.len)
        nbytes := fresh_tmp(g)
        ir_bin(g, nbytes, "mul", w, count, ir_int(int(size)))
        if hi != "" {
            span_n := fresh_tmp(g)
            ir_bin(g, span_n, "sub", w, hi, lo)
            ok, bad := fresh_label(g, "byte.span.ok"), fresh_label(g, "byte.span.err")
            cmp := fresh_tmp(g)
            ir_icmp(g, cmp, "ne", w, span_n, nbytes)
            emit_cond_br(g, cmp, bad, ok)
            emit_label(g, bad)
            emit_fail(g, fmt.tprintf("%s runtime error: byte buffer write: the span is %%lld bytes, the value %%lld\n", loc), fail_i64(span_n), fail_i64(nbytes))
            emit_label(g, ok)
        }
        ok, bad := fresh_label(g, "byte.copy.ok"), fresh_label(g, "byte.copy.err")
        emit_cond_br(g, emit_byte_span_outside(g, lo, count, dst.bound, size), bad, ok)
        emit_label(g, bad)
        emit_fail(g, fmt.tprintf("%s runtime error: byte buffer write out of bounds: offset %%lld + %%lld bytes > capacity %%lld\n", loc),
                  fail_i64(lo), fail_i64(nbytes), fail_i64(dst.bound))
        emit_label(g, ok)
        at := fresh_tmp(g)
        ir_gep(g, at, "i8", dst.data, strings.concatenate({w, " ", lo}, context.temp_allocator))
        emit_memcpy_runtime(g, at, from.data, nbytes)
        return true
    }
    run_given := hi != ""   // (hi written: the run's hi - lo, which src must have)
    if hi == "" {
        n := fmt.tprintf("%d", from.fixed)
        if from.fixed == 0 {
            n = emit_header_field(g, e.value[src], SLICE.len)
        }
        hi = fresh_tmp(g)
        ir_bin(g, hi, "add", w, lo, n)
    }
    name := ""
    #partial switch pg.op[base] {
    case .Var, .Field: name = graph_name(pg, base)
    case .Deref:       name = graph_name(pg, graph_operands(pg, base)[0].op)
    }
    emit_bounds_check(g, lo, dst.bound, name, span)
    hi_ok, hi_err := fresh_label(g, "slice.high.ok"), fresh_label(g, "slice.high.err")
    hi_cmp := fresh_tmp(g)
    ir_icmp(g, hi_cmp, "sgt", w, hi, dst.bound)
    emit_cond_br(g, hi_cmp, hi_err, hi_ok)
    emit_label(g, hi_err)
    emit_fail(g, fmt.tprintf("runtime error: slice assignment out of bounds: high %%lld > capacity %%lld for '%s'\n", name),
              fail_i64(hi), fail_i64(dst.bound))
    emit_label(g, hi_ok)
    // (A run written, lo:hi: src holds hi - lo elements, else the copy would
    // read past its end. A longer src gives its first hi - lo.)
    if run_given {
        have := from.bound if from.bound != "" else emit_header_field(g, e.value[src], SLICE.len)
        if !can_elide_source_check(lo, hi, have) {
            want := fresh_tmp(g)
            ir_bin(g, want, "sub", w, hi, lo)
            src_ok, src_err := fresh_label(g, "slice.src.ok"), fresh_label(g, "slice.src.err")
            src_cmp := fresh_tmp(g)
            ir_icmp(g, src_cmp, "sgt", w, want, have)
            emit_cond_br(g, src_cmp, src_err, src_ok)
            emit_label(g, src_err)
            emit_fail(g, fmt.tprintf("%s runtime error: slice assignment of %%lld elements into '%s', from a value of %%lld\n", loc, name),
                      fail_i64(want), fail_i64(have))
            emit_label(g, src_ok)
        }
    }
    loop, body, done := fresh_label(g, "slice.loop"), fresh_label(g, "slice.body"), fresh_label(g, "slice.end")
    i_slot := fresh_tmp(g)
    emit_alloca(g, i_slot, w)
    emit_store(g, w, "0", i_slot)
    count := fresh_tmp(g)
    ir_bin(g, count, "sub", w, hi, lo)
    emit_br(g, loop)
    emit_label(g, loop)
    i := fresh_tmp(g)
    emit_load_into(g, i, w, i_slot)
    more := fresh_tmp(g)
    ir_icmp(g, more, "slt", w, i, count)
    emit_cond_br(g, more, body, done)
    emit_label(g, body)
    elem_ir := llvm_type_from_checker(dst.elem)
    src_gep := fresh_tmp(g)
    emit_elem_gep(g, src_gep, llvm_type_from_checker(from.elem), from.data, i, w)
    v := fresh_tmp(g)
    emit_load_into(g, v, elem_ir, src_gep)
    at := fresh_tmp(g)
    ir_bin(g, at, "add", w, lo, i)
    dst_gep := fresh_tmp(g)
    emit_array_gep_var(g, dst_gep, fmt.tprintf("[%d x %s]", dst.fixed, elem_ir), dst.data, at, w)
    emit_store(g, elem_ir, v, dst_gep)
    reanchor_partial_arrays(g, dst.elem, dst_gep)
    next := fresh_tmp(g)
    ir_bin(g, next, "add", w, i, "1")
    emit_store(g, w, next, i_slot)
    emit_br(g, loop)
    emit_label(g, done)
    return true
}

// A string constant's text, when an operation's value is one: its global,
// or a read of it.
@(private="file")
llvm_text :: proc(e: ^Llvm, op: Node_Id) -> (string, bool) {
    return graph_const_text(e.pg, op)
}

// Text into a partial array: its bytes into the elements — with the
// terminating zero when there's room — and len its length; the elements past
// it keep what they held.
@(private="file")
llvm_text_into :: proc(e: ^Llvm, place: Node_Id, pa: ^Type_Partial_Array, text: string) -> bool {
    g := e.g
    if llvm_type_from_checker(pa.elem) != "i8" || len(text) > pa.size { return false }
    at := e.value[place]
    elements := partial_elements(g, at, pa)
    if len(text) > 0 {
        src := get_string_literal(g, text)
        emit_memcpy(g, elements, src, len(text) + 1 if pa.size > len(text) else len(text))
    }
    emit_header_set(g, at, SLICE.len, fmt.tprintf("%d", len(text)))
    return true
}

// A slice's elements into a partial array: as many as fit (up to its cap),
// len their count; the elements past them keep what they held.
@(private="file")
llvm_elements_into :: proc(e: ^Llvm, place: Node_Id, pa: ^Type_Partial_Array, src: Node_Id) -> bool {
    g, pg := e.g, e.pg
    if !llvm_same_type(llvm_slice(graph_type(pg, src)).elem, pa.elem) { return false }
    w := SLICE_LEN_IR
    at, hdr := e.value[place], e.value[src]
    data := emit_header_field(g, hdr, SLICE.ptr)
    n0 := emit_header_field(g, hdr, SLICE.len)
    cmp := fresh_tmp(g); ir_icmp(g, cmp, "slt", w, n0, ir_int(int(pa.size)))
    n := fresh_tmp(g); ir_select(g, n, cmp, w, n0, ir_int(int(pa.size)))
    elements := partial_elements(g, at, pa)
    nbytes := fresh_tmp(g); ir_bin(g, nbytes, "mul", w, n, ir_int(int(type_size(pa.elem))))
    ir_call(g, "", "void", "@llvm.memcpy.p0.p0.i64", strings.concatenate({"ptr ", elements}, context.temp_allocator), strings.concatenate({"ptr ", data}, context.temp_allocator), strings.concatenate({"i64 ", nbytes}, context.temp_allocator), "i1 false")
    emit_header_set(g, at, SLICE.len, n)
    return true
}

// A byte buffer's data and its bound: a byte slice's or partial array's
// pointer and cap (the room it has: what indexing is checked against), a
// byte array's own address and size. `held`: its len instead (the bytes it
// holds) — where an open span `bytes[lo:]` ends, as an open slice does.
@(private="file")
llvm_bytes :: proc(e: ^Llvm, base: Node_Id, held := false) -> (data, bound: string, ok: bool) {
    g, pg := e.g, e.pg
    if llvm_direct(e, base) { return }
    bt := graph_type(pg, base)
    at := e.value[base]
    if fa := llvm_array(bt); fa != nil && is_byte_elem(fa.elem) {
        return at, fmt.tprintf("%d", fa.size), true
    }
    elem := llvm_header_elem(bt)
    if elem == nil || !is_byte_elem(elem) { return }
    data = emit_header_field(g, at, SLICE.ptr)
    bound = emit_header_field(g, at, SLICE.len if held else SLICE.cap)
    return data, bound, true
}

// Bytes read into a partial array: its header stamped, the span's elements
// copied in (whole elements, no more than its cap; `#big_endian` swapped),
// its len their count. The index form `bytes[off]` is an array's worth of
// memory from off, clipped at the source's cap: as many whole elements as
// fit there, up to the array's cap (off past the source's cap: an error).
// A span `bytes[lo:hi]` is those bytes, hi within the source's cap — open,
// its len, as an open slice ends (`bytes[lo:]`: only the bytes it holds).
// (Into a struct or an array: later.)
@(private="file")
llvm_byte_read :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    if llvm_direct(e, dest) || len(ops) < 3 { return false }
    pa := llvm_partial(graph_type(pg, dest))
    if pa == nil { return llvm_sized_read(e, op, ops, span) }
    lo := "0"
    if ops[2].op != NO_NODE { lo = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    spanned := len(ops) > 3
    hi := ""
    if spanned && ops[3].op != NO_NODE { hi = llvm_operand(e, ops[3], slice_header_width_type) or_return }
    data, bound := llvm_bytes(e, ops[1].op) or_return
    w := SLICE_LEN_IR
    bytes := ""
    if !spanned {
        // (The room past off, in whole elements, or the array's worth when
        // less. Unsigned: off past the cap leaves the room huge, the array's
        // worth asked for, and the span check fails on off.)
        size := type_size(pa.elem)
        room := fresh_tmp(g)
        ir_bin(g, room, "sub", w, bound, lo)
        part := fresh_tmp(g)
        ir_bin(g, part, "urem", w, room, ir_int(int(size)))
        whole := fresh_tmp(g)
        ir_bin(g, whole, "sub", w, room, part)
        short := fresh_tmp(g)
        ir_icmp(g, short, "ult", w, whole, ir_int(int(pa.size * size)))
        bytes = fresh_tmp(g)
        ir_select(g, bytes, short, w, whole, ir_int(int(pa.size * size)))
    } else {
        if hi == "" { _, hi = llvm_bytes(e, ops[1].op, held = true) or_return }
        inv_ok, inv_err := fresh_label(g, "pa.inv.ok"), fresh_label(g, "pa.inv.err")
        inv_cmp := fresh_tmp(g)
        ir_icmp(g, inv_cmp, "slt", w, hi, lo)
        emit_cond_br(g, inv_cmp, inv_err, inv_ok)
        emit_label(g, inv_err)
        emit_fail(g, "runtime error: partial-array byte read slice bounds inverted (low=%lld, high=%lld) for partial-array byte read\n",
                  fail_i64(lo), fail_i64(hi))
        emit_label(g, inv_ok)
        bytes = fresh_tmp(g)
        ir_bin(g, bytes, "sub", w, hi, lo)
    }
    gen_partial_array_byte_fill_at_core(g, e.value[dest], pa, data, bound, lo, bytes, graph_name(pg, op) == "#big_endian", span)
    return true
}

// Bytes `bytes[lo:hi]` read into a struct or an array: the span within the
// source (lo + span <= its cap) and within the value (span <= its size), the
// value zeroed, the span copied in — the rest stays zero — the partial arrays
// in it made valid, and `#big_endian`, its integers swapped.
@(private="file")
llvm_sized_read :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    t := graph_type(pg, dest)
    sd := llvm_struct(t)
    if len(ops) < 4 || (sd == nil && llvm_array(t) == nil) { return false }
    lo := "0"
    if ops[2].op != NO_NODE { lo = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    hi := ""
    if ops[3].op != NO_NODE { hi = llvm_operand(e, ops[3], slice_header_width_type) or_return }
    data, bound := llvm_bytes(e, ops[1].op) or_return
    if hi == "" { _, hi = llvm_bytes(e, ops[1].op, held = true) or_return }
    w := SLICE_LEN_IR
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    size := type_size(t)
    n := fresh_tmp(g)
    ir_bin(g, n, "sub", w, hi, lo)
    src_ok, src_err := fresh_label(g, "span.src.ok"), fresh_label(g, "span.src.err")
    src_cmp := emit_byte_span_outside(g, lo, n, bound)
    emit_cond_br(g, src_cmp, src_err, src_ok)
    emit_label(g, src_err)
    emit_fail(g, fmt.tprintf("<%s> runtime error: sized read runs past the source buffer\n", loc))
    emit_label(g, src_ok)
    dst_ok, dst_err := fresh_label(g, "span.dst.ok"), fresh_label(g, "span.dst.err")
    dst_cmp := fresh_tmp(g)
    ir_icmp(g, dst_cmp, "ugt", w, n, ir_int(int(size)))
    emit_cond_br(g, dst_cmp, dst_err, dst_ok)
    emit_label(g, dst_err)
    emit_fail(g, fmt.tprintf("<%s> runtime error: sized read of %%lld bytes exceeds destination (%d bytes)\n", loc, size), fail_i64(n))
    emit_label(g, dst_ok)
    src := fresh_tmp(g)
    ir_gep(g, src, "i8", data, strings.concatenate({w, " ", lo}, context.temp_allocator))
    at := e.value[dest]
    emit_memset_zero(g, at, size)
    emit_memcpy_runtime(g, at, src, n)
    if sd != nil { fixup_partial_array_fields(g, at, sd) }
    if graph_name(pg, op) == "#big_endian" { emit_bswap_in_place(g, at, llvm_type_from_checker(t), t) }
    return true
}

// A take from storage's cursor: storage's pointer and len (the cursor), the
// cursor aligned for what's taken, that address, the cursor moved past it —
// checked against storage's cap — and stored as its len. `let(T, s)` is that
// memory; `slice([:n]T, s)` a header over n of them (len = cap = n), built
// where it goes when that's fresh, as a call's result is. Positional (a view
// of bytes for storage): `let` is the view; `slice`, n at its offset.
@(private="file")
llvm_carve :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    storage := ops[0].op
    if storage == NO_NODE || llvm_direct(e, storage) { return false }
    let := graph_name(pg, op) == "let"
    if pg.op[storage] == .View {
        if let {
            e.value[op] = e.value[storage]
            return true
        }
        // `slice([:n]T, &bytes[i])`: n of them at the view's offset, checked
        // against the bytes' cap (the view checked nothing: llvm_view), and a
        // header over them.
        sl := llvm_slice(graph_type(pg, op))
        if sl == nil || len(ops) < 2 { return false }
        n := llvm_operand(e, ops[1], slice_header_width_type) or_return
        vops := graph_operands(pg, storage)
        off := llvm_operand(e, vops[1], slice_header_width_type) or_return
        data, bound := llvm_bytes(e, vops[0].op) or_return
        at := emit_byte_count_ptr(g, data, bound, off, n, type_size(sl.elem), "slice")
        llvm_carve_header(e, op, at, n)
        return true
    }
    if llvm_header_elem(graph_type(pg, storage)) == nil { return false }
    // A `let` is only a declaration's (it names the memory); anything else later.
    if u := e.st.user[op]; let && (u < 0 || pg.op[u] != .Write || pg.refers[graph_operands(pg, u)[0].op] not_in e.st.carved) {
        return false
    }
    t := graph_type(pg, op)
    elem := t
    count := ""
    if !let {
        sl := llvm_slice(t)
        if sl == nil || len(ops) < 2 { return false }
        elem = sl.elem
        count = llvm_operand(e, ops[1], slice_header_width_type) or_return
    }
    w := SLICE_LEN_IR
    size, align := type_size(elem), type_align(elem)
    hdr := e.value[storage]
    data := emit_header_field(g, hdr, SLICE.ptr)
    cursor := emit_header_field(g, hdr, SLICE.len)
    advance := fmt.tprintf("%d", size)
    if !let {
        advance = fresh_tmp(g)
        ir_bin(g, advance, "mul", w, count, ir_int(int(size)))
    }
    if align > 1 {
        bumped := fresh_tmp(g)
        ir_bin(g, bumped, "add", w, cursor, ir_int(int(align - 1)))
        cursor = fresh_tmp(g)
        ir_bin(g, cursor, "and", w, bumped, ir_int(int(-align)))
    }
    at := fresh_tmp(g)
    ir_gep(g, at, "i8", data, strings.concatenate({w, " ", cursor}, context.temp_allocator))
    moved := fresh_tmp(g)
    ir_bin(g, moved, "add", w, cursor, advance)
    cap_val := emit_header_field(g, hdr, SLICE.cap)
    // (Its count of elements, or its one value, in the room past the aligned
    // cursor: a negative count is outside.)
    over := ""
    if let {
        over = emit_byte_span_outside(g, cursor, advance, cap_val)
    } else {
        over = emit_byte_span_outside(g, cursor, count, cap_val, size)
    }
    fail, ok := fresh_label(g, "take.fail"), fresh_label(g, "take.ok")
    emit_cond_br(g, over, fail, ok)
    emit_label(g, fail)
    loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
    name := graph_place_name(pg, ops[0])
    // What was asked for, as asked (the advance itself may have wrapped).
    asked := "1" if let else count
    emit_fail(g, fmt.tprintf("%s runtime error: take overflows storage: %%lld of %d bytes at %%lld exceed cap %%lld for '%s'\n", loc, size, name),
              fail_i64(asked), fail_i64(cursor), fail_i64(cap_val))
    emit_label(g, ok)
    emit_header_set(g, hdr, SLICE.len, moved)
    if let {
        e.value[op] = at
        return true
    }
    llvm_carve_header(e, op, at, count)
    return true
}

// A carved slice's header over `count` elements at `at` (len = cap = count):
// in a fresh declaration's (or the result's) slot, else a temporary.
@(private="file")
llvm_carve_header :: proc(e: ^Llvm, op: Node_Id, at, count: string) {
    g, pg := e.g, e.pg
    out := ""
    if u := e.st.user[op]; u >= 0 && pg.op[u] == .Write {
        dest := graph_operands(pg, u)[0].op
        if pg.op[dest] == .Var {
            if graph_stmt(pg, u).kind == .Decl || llvm_place(e, dest) == e.slot { out = llvm_place(e, dest) }
        }
    }
    if out == "" {
        out = fresh_tmp(g)
        emit_alloca(g, out, SLICE_IR_TYPE)
    }
    emit_header_set(g, out, SLICE.ptr, at)
    emit_header_set(g, out, SLICE.len, count)
    emit_header_set(g, out, SLICE.cap, count)
    e.value[op] = out
}

// A print: its operands are values already. Each prints by its type (text
// as its bytes, an aggregate from where it is), spaced apart or into the `%`
// places of a first operand that is text with them; then a newline. The raw
// printers print their one value as C does.
@(private="file")
llvm_print :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    args := make([dynamic]Print_Arg, 0, len(ops), context.temp_allocator)
    for o in ops {
        if o.op == NO_NODE || o.out != 0 { return false }
        t, v := graph_type(pg, o.op), e.value[o.op]
        if v == "" { return false }   // a held view (later)
        text, is_text := llvm_text(e, o.op)
        switch {
        case is_text && llvm_aggregate(t):   // (text at a ^byte prints as a C string)
            append(&args, Print_Arg{text = text, is_text = true, val = v, t = t})
        case llvm_aggregate(t): append(&args, Print_Arg{addr = v, t = t})
        case llvm_scalar(t):    append(&args, Print_Arg{val = v, t = t})
        case:                   return false
        }
    }
    if spec, ir, raw := raw_print(graph_name(pg, op)); raw {
        if len(args) != 1 || args[0].addr != "" || llvm_type_from_checker(args[0].t) != ir { return false }
        emit_printf(g, spec, fmt.tprintf("%s %s", ir, args[0].val))
        return true
    }
    if len(args) > 0 && args[0].is_text && string_has_format_pct(args[0].text) {
        emit_print_format(g, args[0].text, args[1:], span)
    } else {
        for a, i in args {
            if i > 0 { emit_print_literal(g, " ") }
            // (The first text's `%%` is one `%`, placeholders or none.)
            if i == 0 && a.is_text && strings.contains(a.text, "%%") {
                text, _ := strings.replace_all(a.text, "%%", "%", context.temp_allocator)
                emit_print_literal(g, text)
                continue
            }
            emit_print_operand(g, a)
        }
    }
    emit_print_newline(g)
    return true
}

// An assert: its condition, a value already, branches to the failure, which
// reports a comparison's sides by their text and value (emit_assert_fail).
@(private="file")
llvm_assert :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    c := llvm_operand(e, ops[0], Type_Bool{}) or_return
    ok_label := fresh_label(g, "assert.ok")
    fail_label := fresh_label(g, "assert.fail")
    emit_cond_br(g, c, ok_label, fail_label)
    emit_label(g, fail_label)
    sides: [2]Assert_Side
    reported: []Assert_Side
    ir := ""
    unsigned := false
    if texts, has := pg.assert_sides[op]; has && pg.op[ops[0].op] == .Compare {
        compared := graph_operands(pg, ops[0].op)
        t := graph_type(pg, compared[0].op)
        if assert_reports(llvm_type_from_checker(t)) {
            ir, unsigned = llvm_type_from_checker(t), llvm_unsigned(t)
            for &s, i in sides { s = {texts[i], e.value[compared[i].op], t} }
            reported = sides[:]
        }
    }
    emit_assert_fail(g, span, graph_name(pg, op), reported, ir, unsigned)
    emit_label(g, ok_label)
    return true
}

// A switch, a match: to the arm whose value the subject holds — a union's
// tag, picked by an LLVM switch; a value, by a chain of compares — else to the
// default: the last target, when there is one more than there are values, or,
// the arms covering every variant, a failure (another tag is corrupt memory).
@(private="file")
llvm_switch :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    cases := ops[1:]
    targets := len(graph_out(pg, op))
    if targets != len(cases) && targets != len(cases) + 1 { return false }
    target :: proc(e: ^Llvm, op: Node_Id, k: int) -> string { return e.label[llvm_target(e, op, k)] }
    fail := targets == len(cases)
    subject := ops[0].op
    if ut := llvm_union(graph_type(pg, subject)); ut != nil {
        if llvm_direct(e, subject) { return false }
        tag, ir := load_union_tag(g, ut, e.value[subject]), union_tag_ir_type(ut)
        default := fresh_label(g, "match.fail") if fail else target(e, op, len(cases))
        arms := make([]Ir_Arg, len(cases))
        for c, i in cases {
            v, has := graph_value(pg, c.op)
            if !has || v.is_float { return false }
            arms[i] = {ir, fmt.tprintf("%d", v.int), target(e, op, i)}
        }
        ir_switch(g, ir, tag, default, arms)
        if fail {
            emit_label(g, default)
            emit_match_fail(g, span, tag, ir, union_tag_unsigned(ut))
        }
        return true
    }
    t := graph_type(pg, subject)
    if !llvm_scalar(t) { return false }
    value := llvm_operand(e, ops[0], t) or_return
    ir := llvm_type_from_checker(t)
    last := fresh_label(g, "match.fail") if fail else target(e, op, len(cases))
    if len(cases) == 0 { emit_br(g, last) }
    for c, i in cases {
        v := llvm_operand(e, c, t) or_return
        next := last
        if i < len(cases) - 1 { next = fresh_label(g, "match.next") }
        cmp := fresh_tmp(g)
        ir_icmp(g, cmp, "eq", ir, value, v)
        emit_cond_br(g, cmp, target(e, op, i), next)
        if i < len(cases) - 1 { emit_label(g, next) }
    }
    if fail {
        emit_label(g, last)
        emit_match_fail(g, span, value, ir, match_value_unsigned(t))
    }
    return true
}

// Whether the run, after construct `op`, writes a field of its union through
// a variant place: the literal's fields.
@(private="file")
llvm_variant_written :: proc(e: ^Llvm, op, dest: Node_Id) -> bool {
    pg := e.pg
    root := storage_where(e.st, dest).root
    after := false
    for o in graph_run(pg, int(e.run)) {
        if o == op { after = true; continue }
        if !after || pg.op[o] != .Write { continue }
        p := graph_operands(pg, o)[0].op
        if pg.op[p] != .Field { continue }
        v := graph_operands(pg, p)[0].op
        if pg.op[v] == .Variant && storage_where(e.st, v).root == root { return true }
    }
    return false
}

// A defer's block, run where its scope is left: its code emitted here — a
// copy at each exit, as though written there — its labels fresh, its entry
// going on in the current block, its end falling through to what follows.
@(private="file")
llvm_run_defer :: proc(e: ^Llvm, op: Node_Id) -> bool {
    g, pg := e.g, e.pg
    d, ok := pg.defer_of[op]
    if !ok { return false }
    runs: [dynamic]i32
    runs.allocator = context.temp_allocator
    body := runs[:graph_code_runs(pg, d, &runs)]
    llvm_sort_runs(body[1:])
    for r in body {
        for o in graph_run(pg, int(r)) {
            for edge in graph_out(pg, o) {
                if pg.run_starts[edge.to] == body[0] { return false }   // its entry a loop's head: later
            }
        }
    }
    for r in body[1:] { e.label[r] = fresh_label(g, "defer") }
    end := ""
    saved := e.run
    defer e.run = saved
    for r, i in body {
        if i > 0 { emit_label(g, e.label[r]) }
        e.run = r
        ops := graph_run(pg, int(r))
        for o, k in ops {
            if pg.op[o] == .Return {
                // The block's end: back where it ran — straight on from the
                // last of its code.
                if i == len(body) - 1 && k == len(ops) - 1 { continue }
                if end == "" { end = fresh_label(g, "defer.end") }
                emit_br(g, end)
                continue
            }
            if o in e.ahead { delete_key(&e.ahead, o); continue }
            e.stop = o
            if !llvm_op(e, o) { return false }
        }
    }
    if end != "" { emit_label(g, end) }
    return true
}

// A view held as its header's values (Storage.views).
@(private="file")
Llvm_Header :: struct {
    data, len, cap: string,
}

@(private="file")
llvm_held_header :: proc(e: ^Llvm, place: Node_Id) -> (Llvm_Header, bool) {
    if e.pg.op[place] != .Var { return {}, false }
    return e.hdr[e.pg.refers[place]]
}

@(private="file")
llvm_call :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g := e.g
    ops := ops
    // What's called: the callee, or — through a function value, the first
    // operand — that value, by its type's signature (the same ABI).
    callee := graph_called(e.pg, op)
    name := ""
    if callee == nil {
        callee = graph_signature(e.pg, op)
        if callee == nil { e.note = "a function value"; return false }
        name = llvm_operand(e, ops[0], graph_type(e.pg, ops[0].op)) or_return
        ops = ops[1:]
    } else {
        if callee.kind != .Fun { return false }
        if oi, is_intrinsic := callee.origin.(Origin_Intrinsic); is_intrinsic { return llvm_intrinsic(e, op, ops, callee, oi.llvm_name) }
        if fo, is_foreign := callee.origin.(Origin_Foreign); is_foreign { return llvm_c_call(e, op, ops, callee, fo.link_name if fo.link_name != "" else callee.name) }
        if _, src := callee.origin.(Origin_Source); !src { e.note = "foreign"; return false }
        name = mara_fn_name(g, callee.name)
    }
    if len(ops) != len(callee.params) { e.note = "arguments left to defaults"; return false }
    ret := "void"
    result: Type
    if fn_result_count(callee) == 1 {
        result = fn_result(callee, 0)
        switch {
        case llvm_scalar(result):        ret = llvm_type_from_checker(result)
        case llvm_aggregate(result):
        case:                            e.note = "result type"; return false
        }
    }
    args := make([dynamic]string, 0, len(ops) + 1, context.temp_allocator)
    for _, i in callee.params {
        p := fn_param(callee, i)
        ir, ok := llvm_param_type(p.type_)
        if !ok { e.note = fmt.tprintf("param '%s'", p.name); return false }
        v, vok := llvm_operand(e, ops[i], p.type_)
        if !vok { e.note = fmt.tprintf("argument '%s'", p.name); return false }
        // Text taken as a partial array is only its bytes in memory: the
        // callee gets a header over them (it reads the elements through ptr).
        if text, is_text := llvm_text(e, ops[i].op); is_text && llvm_partial(p.type_) != nil {
            v = emit_build_temp_slice(g, v, fmt.tprintf("%d", len(text)), fmt.tprintf("%d", len(text) + 1))
        }
        append(&args, fmt.tprintf("%s %s", ir, v))
    }
    if fn_result_count(callee) > 1 {
        // Several results: each into a temporary, where its uses find it —
        // an aggregate that a declaration takes, straight into its storage.
        at := make([]string, fn_result_count(callee))
        for i in 0 ..< fn_result_count(callee) {
            rt := fn_result(callee, i)
            if !llvm_scalar(rt) && !llvm_aggregate(rt) { e.note = "result type"; return false }
            if d, declared := e.st.out_at[Operand{op, i32(i)}]; declared { at[i] = llvm_place(e, d) }
            if at[i] == "" { at[i] = llvm_temporary(e, {op, i32(i)}, rt, llvm_alloca_type(rt)) }
            append(&args, fmt.tprintf("ptr %s", at[i]))
        }
        ir_call(g, "", "void", name, ..args[:])
        e.outs[op], e.out_run[op] = at, e.run
        e.value[op] = at[0]
        return true
    }
    if ret == "void" && result != nil {
        // A struct result, built where it goes (llvm_result_place).
        at := llvm_result_place(e, op, callee, result) or_return
        append(&args, fmt.tprintf("ptr %s", at))
        ir_call(g, "", "void", name, ..args[:])
        e.value[op] = at
        return true
    }
    if ret == "void" {
        ir_call(g, "", "void", name, ..args[:])
        return true
    }
    tmp := fresh_tmp(g)
    ir_call(g, tmp, ret, name, ..args[:])
    e.value[op] = tmp
    return true
}

// A call to a foreign (C) function, by the platform's C ABI (abi.odin): each
// argument by its lowering — a register value as itself (text for a cstring
// its bytes' address), an aggregate in registers loaded in 8-byte parts from
// where it is, or by address (byval) — and the result returned (an aggregate
// in parts put back together in a temporary) or written to a hidden slot.
@(private="file")
llvm_c_call :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, callee: ^Type_Scope, name: string) -> bool {
    g := e.g
    os := g.checked.target_os
    if len(ops) != len(callee.params) { e.note = "a foreign call's variadic arguments"; return false }
    args := make([dynamic]string, 0, len(ops) + 1, context.temp_allocator)
    // The result: none, returned, or in a hidden slot (first).
    result: Type
    if fn_result_count(callee) == 1 && !is_untyped(fn_result(callee, 0)) { result = fn_result(callee, 0) }
    if fn_result_count(callee) > 1 { e.note = "a foreign call's results"; return false }
    ret_ir, slot := "void", ""
    ret_low: Lowering
    if result != nil {
        if !llvm_scalar(result) && !llvm_aggregate(result) { e.note = "result type"; return false }
        ret_low = classify(result, os)
        switch r in ret_low {
        case Lowering_Direct:
            ret_ir = direct_ir_for_return(r.parts[:])
        case Lowering_Indirect:
            slot = llvm_temporary(e, {op, 0}, result)
            append(&args, fmt.tprintf("ptr sret(%s) %s", llvm_type_from_checker(result), slot))
        }
    }
    for _, i in callee.params {
        p := fn_param(callee, i)
        pt := p.type_
        v := ""
        if _, is_text := llvm_text(e, ops[i].op); is_text && llvm_is_cstring(pt) {
            v = e.value[ops[i].op]   // text for a cstring: its bytes, already terminated
        } else {
            ok: bool
            v, ok = llvm_operand(e, ops[i], pt)
            // A C pointer is a pointer: what it points at is the callee's to
            // know (`const void *data` is `^byte`, handed any pointer).
            if at := llvm_type_of(e, ops[i]); !ok && ops[i].out == 0 && llvm_scalar(at) && llvm_type_from_checker(at) == "ptr" && llvm_type_from_checker(pt) == "ptr" {
                v, ok = e.value[ops[i].op], true
            }
            if !ok { e.note = fmt.tprintf("argument '%s'", p.name); return false }
        }
        switch pl in classify(pt, os) {
        case Lowering_Direct:
            if llvm_aggregate(pt) {
                for part, k in pl.parts {
                    at := v
                    if k > 0 {
                        at = fresh_tmp(g)
                        ir_gep(g, at, "i8", v, strings.concatenate({"i64 ", ir_int(int(k * 8))}, context.temp_allocator))
                    }
                    loaded := fresh_tmp(g)
                    emit_load_into(g, loaded, part, at)
                    append(&args, fmt.tprintf("%s %s", part, loaded))
                }
                continue
            }
            if pl.parts[0] == "ptr" && v == "0" { v = "null" }
            append(&args, fmt.tprintf("%s %s", pl.parts[0], v))
        case Lowering_Indirect:
            append(&args, fmt.tprintf("ptr byval(%s) %s", llvm_type_from_checker(pt), v))
        }
    }
    callee_sym := strings.concatenate({"@", name}, context.temp_allocator)
    if ret_ir == "void" {
        ir_call(g, "", "void", callee_sym, ..args[:])
        if slot != "" { e.value[op] = slot }
        return true
    }
    tmp := fresh_tmp(g)
    ir_call(g, tmp, ret_ir, callee_sym, ..args[:])
    e.value[op] = tmp
    // An aggregate returned in registers: put back together where it can be
    // read as one.
    if direct, is_direct := ret_low.(Lowering_Direct); is_direct && llvm_aggregate(result) {
        at := fresh_tmp(g)
        emit_alloca(g, at, llvm_type_from_checker(result))
        if len(direct.parts) == 1 {
            emit_store(g, direct.parts[0], tmp, at)
        } else {
            for part, k in direct.parts {
                ev := fresh_tmp(g)
                ir_extract(g, ev, ret_ir, tmp, ir_int(int(k)))
                to := at
                if k > 0 {
                    to = fresh_tmp(g)
                    ir_gep(g, to, "i8", at, strings.concatenate({"i64 ", ir_int(int(k * 8))}, context.temp_allocator))
                }
                emit_store(g, part, ev, to)
            }
        }
        e.value[op] = at
    }
    return true
}

// `cstring(s)`: s's bytes for C — text as they are (terminated), a slice or a
// partial array checked to hold a terminating 0 (emit_cstring_check).
@(private="file")
llvm_cstring :: proc(e: ^Llvm, op, x: Node_Id, span: Span) -> bool {
    g, pg := e.g, e.pg
    if _, is_text := llvm_text(e, x); is_text {
        e.value[op] = e.value[x]
        return true
    }
    if llvm_header_elem(graph_type(pg, x)) == nil || e.value[x] == "" { return false }
    hdr := e.value[x]
    n := emit_header_field(g, hdr, SLICE.len)
    c := emit_header_field(g, hdr, SLICE.cap)
    data := emit_header_field(g, hdr, SLICE.ptr)
    e.value[op] = emit_cstring_check(g, n, c, data, span)
    return true
}

// Whether a type is cstring.
@(private="file")
llvm_is_cstring :: proc(t: Type) -> bool {
    _, is := distinct_base(t).(Type_CString)
    return is
}

// A call to an LLVM intrinsic (a fun whose body names one): its arguments at
// the param types — a fixed array by value, loaded from where it is — and its
// result a register value.
@(private="file")
llvm_intrinsic :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, callee: ^Type_Scope, name: string) -> bool {
    g := e.g
    if name == "" || len(ops) != len(callee.params) || fn_result_count(callee) != 1 || !llvm_scalar(fn_result(callee, 0)) {
        e.note = "an intrinsic's shape"
        return false
    }
    args := make([dynamic]string, 0, len(ops), context.temp_allocator)
    for _, i in callee.params {
        p := fn_param(callee, i)
        v := llvm_operand(e, ops[i], p.type_) or_return
        ir := llvm_type_from_checker(p.type_)
        if fa := llvm_array(p.type_); fa != nil {
            loaded := fresh_tmp(g)
            emit_load_into(g, loaded, ir, v)
            v = loaded
        } else if !llvm_scalar(p.type_) {
            e.note = fmt.tprintf("param '%s'", p.name)
            return false
        }
        append(&args, fmt.tprintf("%s %s", ir, v))
    }
    tmp := fresh_tmp(g)
    ir_call(g, tmp, llvm_type_from_checker(fn_result(callee, 0)), strings.concatenate({"@", name}, context.temp_allocator), ..args[:])
    e.value[op] = tmp
    return true
}

// Where a call builds its struct result. Straight into where it goes when
// that is safe: this fun's own slot for a returned call; a declaration's or
// a temporary's fresh storage; an existing place when the call can't reach
// it while it writes the result (llvm_call_reaches; else a temporary, copied
// in by the write). Anything else is a temporary.
@(private="file")
llvm_result_place :: proc(e: ^Llvm, op: Node_Id, callee: ^Type_Scope, result: Type) -> (string, bool) {
    switch e.st.calls[op] {
    case .Result_Slot:
        return e.slot, true
    case .Dest:
        // (Its address at hand, as storage_had found: computed now if not yet.)
        dest := graph_operands(e.pg, e.st.user[op])[0].op
        if !llvm_ahead(e, dest) {
            e.note = "a call's destination ahead of it"
            return "", false
        }
        return llvm_place(e, dest), true
    case .Temporary:
    }
    return llvm_temporary(e, {op, 0}, result), true
}

// A temporary for a call's result `o`: on the stack — or one as big as a
// local gets an arena for (routes_to_arena), the fun's, on the arena from
// its entry (llvm_temps). (A Mara fun's struct or union result is one only
// when it can't be built where it goes, llvm_result_place: a declaration's
// always can. A C fun's slot always is.)
@(private="file")
llvm_temporary :: proc(e: ^Llvm, o: Operand, t: Type, ir: string = "") -> string {
    if routes_to_arena(t) {
        if at, held := e.temps[o]; held { return at }
        codegen_fatal(e.g, graph_origin(e.pg, o.op), CODE_TEMPORARY_UNLISTED, type_name(t), type_size(t))
    }
    tmp := fresh_tmp(e.g)
    emit_alloca(e.g, tmp, ir if ir != "" else llvm_type_from_checker(t))
    return tmp
}

// Place p's address, for a call to build its result in: computed, or — a
// variable, or a field or constant index of one — computed now, ahead of its
// turn (the graph has the value before the place; its turn then skips it).
// False when it can't be had (storage_had says when it can).
@(private="file")
llvm_ahead :: proc(e: ^Llvm, p: Node_Id) -> bool {
    pg := e.pg
    if e.value[p] != "" || pg.op[p] == .Var { return true }
    ops := graph_operands(pg, p)
    #partial switch pg.op[p] {
    case .Field, .Variant, .Deref:   // (a union's variant: the union's own address; a pointer's target: its value)
        if !llvm_ahead(e, ops[0].op) { return false }
    case .Index:
        if ops[1].op == NO_NODE || pg.op[ops[1].op] != .Const || !llvm_ahead(e, ops[0].op) { return false }
        if !llvm_op(e, ops[1].op) { return false }
        e.ahead[ops[1].op] = true
    case:
        return false
    }
    if pg.op[ops[0].op] == .Var && e.value[ops[0].op] == "" {
        if !llvm_op(e, ops[0].op) { return false }
        e.ahead[ops[0].op] = true
    }
    if !llvm_op(e, p) { return false }
    e.ahead[p] = true
    return true
}

// --- types -----------------------------------------------------------------------

// A value held in one register: a number, a bool, a byte, an enum, a pointer.
llvm_scalar :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(resolve_infer(t)) {
    case Type_Numeric, Type_F64, Type_Bool, Type_Utf8, Type_Byte, ^Type_Enum, ^Type_Ptr, Type_CString, Type_Err:
        return true
    case ^Type_Scope:
        return v.kind == .Fun   // a function value: its pointer
    }
    return false
}

// An aggregate — a struct, a fixed array, a slice's header, a partial array, a
// union — is a value handled by its address: a param is a pointer to the
// caller's, and reading one yields where it is; a copy re-points the partial
// arrays in it at its own elements.
llvm_aggregate :: proc(t: Type) -> bool {
    return llvm_struct(t) != nil || llvm_array(t) != nil || llvm_slice(t) != nil || llvm_partial(t) != nil || llvm_union(t) != nil
}

// The union whose `.tag` place p is; nil when p is no union's tag.
@(private="file")
llvm_union_tag :: proc(e: ^Llvm, p: Node_Id) -> ^Type_Union {
    pg := e.pg
    if pg.op[p] != .Field || graph_name(pg, p) != "tag" { return nil }
    return llvm_union(graph_type(pg, graph_operands(pg, p)[0].op))
}

// A union: its tag and the payload its variants overlay at its start (a niche
// union's storage is its Some variant's pointer alone).
@(private="file")
llvm_union :: proc(t: Type) -> ^Type_Union {
    if t == nil { return nil }
    ut, ok := distinct_base(t).(^Type_Union)
    if !ok { return nil }
    return ut
}

// A partial array: a slice header over its own inline elements, `ptr`
// pointing at them.
@(private="file")
llvm_partial :: proc(t: Type) -> ^Type_Partial_Array {
    if t == nil || is_infer(t) { return nil }
    pa, ok := distinct_base(t).(^Type_Partial_Array)
    if !ok || pa.elem == nil || is_infer(pa.elem) { return nil }
    return pa
}

// The element type of what a slice header describes — a slice's or a
// partial array's; nil for anything else.
llvm_header_elem :: proc(t: Type) -> Type {
    if sl := llvm_slice(t); sl != nil { return sl.elem }
    if pa := llvm_partial(t); pa != nil { return pa.elem }
    return nil
}

// A slice: its header, {len, cap, ptr}, is the aggregate.
llvm_slice :: proc(t: Type) -> ^Type_Slice {
    if t == nil || is_infer(t) { return nil }
    sl, ok := distinct_base(t).(^Type_Slice)
    if !ok || sl.elem == nil || is_infer(sl.elem) { return nil }
    return sl
}

// A slice header's field by name; -1 for none.
llvm_header_field :: proc(name: string) -> int {
    switch name {
    case "len": return SLICE.len
    case "cap": return SLICE.cap
    case "ptr": return SLICE.ptr
    }
    return -1
}

llvm_struct :: proc(t: Type) -> ^Scope_Body {
    if t == nil { return nil }
    sd := as_struct_body(distinct_base(t))   // a distinct struct's is its base's
    return sd
}

// A fixed array of register values or aggregates.
llvm_array :: proc(t: Type) -> ^Type_Fixed_Array {
    if t == nil || is_infer(t) { return nil }
    fa, ok := distinct_base(t).(^Type_Fixed_Array)
    if !ok || (!llvm_scalar(fa.elem) && !llvm_aggregate(fa.elem)) { return nil }
    return fa
}

// Whether two types lower to one IR type. An unresolved one matches nothing:
// the fun is refused rather than guessed at.
llvm_same_type :: proc(a, b: Type) -> bool {
    if a == nil || b == nil || is_infer(a) || is_infer(b) { return false }
    // Pointers lower alike; what they point to must match too (a byte
    // address taken as a pointer to T is a view of bytes: later).
    pa, a_ptr := distinct_base(a).(^Type_Ptr)
    pb, b_ptr := distinct_base(b).(^Type_Ptr)
    if a_ptr && b_ptr { return llvm_same_type(pa.elem, pb.elem) }
    return llvm_type_from_checker(a) == llvm_type_from_checker(b)
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

// A param's IR type: an aggregate goes by address.
llvm_param_type :: proc(t: Type) -> (string, bool) {
    if llvm_scalar(t) { return llvm_type_from_checker(t), true }
    if llvm_aggregate(t) { return "ptr", true }
    return "", false
}

// Unsigned: unsigned ints, bytes, chars and bools.
llvm_unsigned :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case Type_Numeric:                   return v.kind == .Unsigned
    case Type_Byte, Type_Utf8, Type_Bool: return true
    }
    return false
}
