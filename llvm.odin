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
    runs:  [dynamic]i32,        // the runs its entry reaches: the entry's, then as built; then its defers'
    own:   int,                 // how many of the runs are its own code's (the rest, defer blocks')
    label: map[i32]string,      // a run → its block's label
    value: []string,            // by id - node: an operation's result, a variable's storage
    held:  []bool,              // by id - node: a variable held as its one value
    ret:   string,              // its IR return type
    sret:  Type,                // a struct result, built in the caller's slot (%sret)
    by_value: Type,             // a union result: returned as an IR value (the old ABI; a slot like the rest: later)
    ctor:  bool,                // a struct's code: it builds Self in %sret, which starts zeroed
    main:  bool,                // main's body: `@main` returns i64, 0 when it falls off its end
    fields: strings.Builder,    // a constructor's field addresses, first in its entry
    head:  string,              // its `define` line
    user:  []Node_Id,           // by id - node: the one operation using an operation's value

    // Its named allocas: one for the named locals of one name and type (their
    // scopes never overlap — a name can't be declared again where it is
    // visible).
    shared:  map[string]string,
    used:    map[string]bool,
    in_place: map[Node_Id]Node_Id,  // a temporary → the place it is built in (llvm_in_place)
    hdr:     map[Node_Id]Llvm_Header,   // a view held as its header's values (llvm_holds_header)
    carved:  map[Node_Id]Node_Id,       // a local declared from a `let` take → that take (it is the memory)
    bound:   map[Node_Id]Node_Id,       // a match arm's binding → its variant place (it is the payload)
    arena:   map[Node_Id]bool,          // a big local: its storage from the arena (its arena alloc)
    ahead:   map[Node_Id]bool,          // places computed ahead of their turn (a call builds its result there)
    why:     Node_Id,             // where it declined (for MARA_GRAPH_CG=log)
    run:     i32,                 // the run being emitted
}

// Emit a fun from the graph. False, having emitted nothing, when some part of
// it isn't lowered yet.
llvm_function :: proc(g: ^Codegen, cf: ^Type_Scope) -> bool {
    if _, src := cf.origin.(Origin_Source); !src { return false }
    g.tmp_counter, g.label_counter = 0, 0
    g.emitted_allocas = {}
    return llvm_code(g, cf, main = false)
}

// Main's body, after the program's setup (emit_main_prologue) — `@main`'s
// `define` and entry the caller has written. Its falling off the end, or a
// bare return, returns 0.
llvm_main :: proc(g: ^Codegen, cf: ^Type_Scope) -> bool {
    // A decline leaves the syntax tree's emitter what it found: the counters,
    // and no allocas named (it would take one for its own, and skip it).
    tmp, label := g.tmp_counter, g.label_counter
    named := make(map[string]string, len(g.emitted_allocas), context.temp_allocator)
    for k, v in g.emitted_allocas { named[k] = v }
    if llvm_code(g, cf, main = true) { return true }
    g.tmp_counter, g.label_counter = tmp, label
    clear(&g.emitted_allocas)
    for k, v in named { g.emitted_allocas[k] = v }
    return false
}

@(private="file")
llvm_code :: proc(g: ^Codegen, cf: ^Type_Scope, main: bool) -> bool {
    pg := &g.checked.graph
    node, ok := pg.scope_node[cf]
    if !ok || (pg.kind[node] != .Fun && pg.kind[node] != .Struct) { return false }
    e := Llvm{g = g, pg = pg, ft = cf, node = node, ctor = pg.kind[node] == .Struct, main = main}
    e.own = graph_code_runs(pg, g.run_starts, node, &e.runs)
    if e.own == 0 { return false }   // no code
    size := int(pg.last[node] - node) + 1
    e.value = make([]string, size)
    e.held = make([]bool, size)

    // Emit as the old emitter does, allocas hoisted: every alloca into the
    // entry's buffer in the order code first needs it, the rest into the
    // body's. Keep them only when every part lowered: the `define`, the
    // entry's field addresses and allocas, then the body.
    begin_alloca_hoist(g)
    e.why = node
    lowered := llvm_emit(&e)
    g.hoist_allocas = false
    if !lowered && g.graph_cg_log { llvm_why(&e) }
    if lowered {
        if !main {
            strings.write_string(&g.out, e.head)
            strings.write_string(&g.out, "\nentry:\n")
        }
        strings.write_string(&g.out, strings.to_string(e.fields))
        strings.write_string(&g.out, strings.to_string(g.alloca_buf))
        strings.write_string(&g.out, strings.to_string(g.body_buf))
    }
    return lowered
}

// Where a fun was declined: the operation or variable it stopped at (the fun
// itself for its signature).
@(private="file")
llvm_why :: proc(e: ^Llvm) {
    pg := e.pg
    at := e.why
    what := graph_kind_word(pg.kind[at])
    if pg.kind[at] == .Op { what = graph_op_word(pg.op[at]) }
    s := pg.origin[at]
    fmt.eprintfln("graph-cg no: %s at %s '%s' %s:%d", e.ft.name, what, pg.name[at], s.file, s.line)
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
        case llvm_union(rt) != nil:   e.ret, e.by_value = llvm_type_from_checker(rt), rt
        case llvm_aggregate(rt):     e.sret = rt
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
    // `#expose`: in a DLL's export table, and the host's program — its first
    // param — is the one the DLL's code reads, set first thing.
    linkage := "dllexport " if cf.is_exposed else ""
    e.head = strings.concatenate({"define ", linkage, e.ret, " ", mara_fn_name(g, cf.name), "(",
        strings.join(params[:], ", ", context.temp_allocator), ") {"})
    if cf.is_exposed && len(cf.cg_params) > 0 {
        fmt.sbprintf(&e.fields, "  store ptr %%%s.arg, ptr @__mara_program\n", cf.cg_params[0].name)
    }

    // Entry first, then the runs as they were built; each gets its label.
    entry := g.run_starts[llvm_first_then(pg, e.node)]
    for r, i in e.runs {
        if r == entry { e.runs[0], e.runs[i] = e.runs[i], e.runs[0] }
    }
    llvm_sort_runs(e.runs[1:e.own])
    for r in e.runs[1:e.own] { e.label[r] = fmt.tprintf("run%d", r) }

    llvm_users(e)
    if !llvm_variables(e) { return false }
    llvm_carved(e)
    if e.sret != nil { llvm_result_slot(e) }
    // A big variable lives on the arena, or in the caller's slot (a big
    // temporary: later).
    for id := e.node + 1; id <= e.pg.last[e.node]; id += 1 {
        if e.pg.kind[id] != .Local || !routes_to_arena(e.pg.type_[id]) || id in e.arena { continue }
        if e.value[id - e.node] != "%sret" { e.why = id; return false }
    }
    llvm_in_place(e)
    for r, i in e.runs[:e.own] {   // (a defer block's: where it runs, llvm_run_defer)
        if i > 0 { emit_label(g, e.label[r]) }
        e.run = r
        for op in graph_run(pg, int(r)) {
            if op in e.ahead { delete_key(&e.ahead, op); continue }   // done already
            e.why = op
            if !llvm_op(e, op) { return false }
        }
    }
    emit(g, "}")
    if !e.main { emit_raw(g, "") }   // (@main's end: its caller's)
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
        e.why = id
        #partial switch pg.kind[id] {
        case .Fun, .Struct, .Union, .Enum:
            id = pg.last[id]
        case .Param:
            _ = llvm_param_type(pg.type_[id]) or_return
            e.value[id - e.node] = fmt.tprintf("%%%s.arg", pg.name[id])
        case .Local:
            t := pg.type_[id]
            if !llvm_scalar(t) && !llvm_aggregate(t) { return false }
            if pg.written[id] == .Synthetic && llvm_scalar(t) && llvm_holds(e, id) { e.held[id - e.node] = true }
            if pg.written[id] == .Synthetic && llvm_slice(t) != nil && llvm_holds_header(e, id) { e.hdr[id] = {} }
        case .Field:
            // A constructor's field: its place in Self, first thing in the entry.
            t := pg.type_[id]
            if !e.ctor || pg.parent[id] != e.node || (!llvm_scalar(t) && !llvm_aggregate(t)) { return false }
            i := struct_field_index(llvm_struct(e.sret), pg.name[id])
            if i < 0 { return false }
            at := fresh_tmp(e.g)
            fmt.sbprintf(&e.fields, "  %s = getelementptr %s, ptr %%sret, i32 0, i32 %d\n", at, llvm_type_from_checker(e.sret), i)
            e.value[id - e.node] = at
            // A partial array: its header stamped over its elements, and those
            // constructed, right after its address (its zero is not all zeros).
            if pa := llvm_partial(t); pa != nil {
                llvm_into_fields(e, true)
                stamp_partial_array_header(e.g, at, pa)
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
    if at, ok := e.in_place[d]; ok {
        e.value[d - e.node] = llvm_place(e, at)
        return e.value[d - e.node]
    }
    if c, ok := e.carved[d]; ok { return e.value[c - e.node] }   // the carved memory
    if v, ok := e.bound[d]; ok { return e.value[v - e.node] }    // the payload
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
    // Bytes held inline are aligned for any value viewed in them.
    if pa := llvm_partial(pg.type_[d]); pa != nil && llvm_type_from_checker(pa.elem) == "i8" {
        ir = strings.concatenate({ir, ", align 16"})
    }
    emit_alloca(e.g, name, ir)
    return name
}

// Point the emit helpers' output at a constructor's entry prefix (e.fields),
// where its fields' addresses go, or back.
@(private="file")
llvm_into_fields :: proc(e: ^Llvm, on: bool) {
    e.fields, e.g.out = e.g.out, e.fields
    e.g.hoist_allocas = !on
}

// A value copied: its bytes, then the partial arrays in it re-pointed at the
// copy's own elements.
@(private="file")
llvm_copy :: proc(e: ^Llvm, dest, src: string, t: Type) {
    emit_memcpy(e.g, dest, src, llvm_size(e, t))
    reanchor_partial_arrays(e.g, t, dest)
}

// Each operation's user, when it has exactly one (-1 for none, -2 for
// several); and each match binding's variant place.
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
            // A match arm's binding is the payload's place.
            if pg.op[op] == .Variant && pg.refers[op] != NO_NODE { e.bound[pg.refers[op]] = op }
            if pg.op[op] == .Arena_Alloc { e.arena[pg.refers[graph_operands(pg, op)[0].op]] = true }
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
    for r in e.runs[:e.own] {   // (a defer block's return goes back where it ran)
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Return { continue }
            ops := graph_operands(pg, op)
            v := NO_NODE
            if len(ops) == 1 && ops[0].op != NO_NODE && pg.op[ops[0].op] == .Read {
                place := graph_operands(pg, ops[0].op)[0].op
                if pg.op[place] == .Var && pg.kind[pg.refers[place]] == .Local { v = pg.refers[place] }
            }
            if v in e.carved { v, every = NO_NODE, false }   // the carved memory: copied out
            if v != NO_NODE && pg.written[v] == .Synthetic {
                // (Not an `if` expression's, written by its arms: its own.)
                if llvm_reads(e, v) == 1 && llvm_written_only_in(e, v, r) { e.value[v - e.node] = "%sret" }
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

// Whether every write to variable v is in run r.
@(private="file")
llvm_written_only_in :: proc(e: ^Llvm, v: Node_Id, r: i32) -> bool {
    pg := e.pg
    for q in e.runs {
        if q == r { continue }
        for op in graph_run(pg, int(q)) {
            #partial switch pg.op[op] {
            case .Zero, .Construct, .Fill, .Write, .Byte_Read:
                if llvm_where(e, graph_operands(pg, op)[0].op).root == v { return false }
            }
        }
    }
    return true
}

// Which temporaries are built in the storage they are then written to. The
// graph builds a literal or construction assigned to existing storage whole,
// in a temporary — it may read what it replaces; it is built in place when,
// from its first write on, nothing it reads can be that storage
// (llvm_overlaps), and — a construction — its callee is handed none of the
// caller's storage (the old emitter's rule for calls, as in llvm_result_place).
@(private="file")
llvm_in_place :: proc(e: ^Llvm) {
    pg := e.pg
    for r in e.runs {
        ops := graph_run(pg, int(r))
        for w, at in ops {
            if pg.op[w] != .Write { continue }
            wops := graph_operands(pg, w)
            x, v := wops[0].op, wops[1].op
            if v == NO_NODE || wops[1].out != 0 || pg.op[v] != .Read || !llvm_aggregate(pg.type_[v]) { continue }
            tv := graph_operands(pg, v)[0].op
            if pg.op[tv] != .Var || llvm_direct(e, x) { continue }
            t := pg.refers[tv]
            if t <= e.node || t > pg.last[e.node] || pg.kind[t] != .Local || pg.written[t] != .Synthetic { continue }
            if e.value[t - e.node] != "" || llvm_reads(e, t) != 1 { continue }
            if llvm_builds_alone(e, ops[:at], t, x) { e.in_place[t] = x }
        }
    }
}

// Which locals are declared from a `let` take: such a local is the carved
// memory itself — its declaration binds it, copying nothing.
@(private="file")
llvm_carved :: proc(e: ^Llvm) {
    pg := e.pg
    for r in e.runs {
        for w in graph_run(pg, int(r)) {
            if pg.op[w] != .Write { continue }
            ops := graph_operands(pg, w)
            c, dest := ops[1].op, ops[0].op
            if c == NO_NODE || pg.op[c] != .Carve || pg.name[c] != "let" || pg.op[dest] != .Var { continue }
            s := pg.stmt[w]
            if d := pg.refers[dest]; pg.kind[d] == .Local && s >= 0 && pg.stmts[s].kind == .Decl { e.carved[d] = c }
        }
    }
}

// Whether temporary t, built in `before` (the operations of one run ahead of
// the write that reads it), can be built at place x instead.
@(private="file")
llvm_builds_alone :: proc(e: ^Llvm, before: []Node_Id, t, x: Node_Id) -> bool {
    pg := e.pg
    // All of t's code is here, and x is known before t's first write.
    uses, here := 0, 0
    for r in e.runs {
        for op in graph_run(pg, int(r)) { if pg.op[op] == .Var && pg.refers[op] == t { uses += 1 } }
    }
    first := -1
    for op, i in before {
        if pg.op[op] == .Var && pg.refers[op] == t { here += 1 }
        #partial switch pg.op[op] {
        case .Zero, .Construct, .Fill, .Write:
            if first < 0 && llvm_where(e, graph_operands(pg, op)[0].op).root == t { first = i }
        }
    }
    if uses != here || first < 0 { return false }
    if pg.op[x] != .Var {
        known := false
        for op in before[:first] { if op == x { known = true } }
        if !known { return false }
    }
    // From its first write on, nothing read (or pointed at) is x's storage.
    for op in before[first:] {
        ops := graph_operands(pg, op)
        #partial switch pg.op[op] {
        case .Read, .Address:
            if llvm_where(e, ops[0].op).root == t { continue }
            if pg.op[op] == .Read && llvm_direct(e, ops[0].op) { continue }   // a value, in no memory
            if llvm_overlaps(e, ops[0].op, x) { return false }
        case .Construct:
            // t's own construction, handed arguments.
            if len(ops) == 1 || pg.op[ops[0].op] != .Var || pg.refers[ops[0].op] != t { continue }
            callee := llvm_callee(e, op)
            if callee == nil || llvm_passes_storage(callee) { return false }
            if _, consumes := consumed_param_of(callee).?; consumes { return false }
        }
    }
    return true
}

// Where a place lives: the variable at the root of its path; whether the
// path crosses a pointer (then the root says nothing about where it is), and
// once it does, `region`, the type of the object the last crossing lands in —
// else the root variable's type; whether a pointer is dereferenced as written.
@(private="file")
Llvm_Where :: struct {
    root:     Node_Id,
    via_ptr:  bool,
    region:   Type,
    explicit: bool,
}

@(private="file")
llvm_where :: proc(e: ^Llvm, p: Node_Id) -> Llvm_Where {
    pg := e.pg
    w := Llvm_Where{root = NO_NODE}
    for id := p; id != NO_NODE; {
        ops := graph_operands(pg, id)
        #partial switch pg.op[id] {
        case .Var:
            w.root = pg.refers[id]
            if !w.via_ptr { w.region = pg.type_[id] }
            return w
        case .Deref:
            if pg.written[id] != .Implied { w.explicit = true }
            if !w.via_ptr { w.via_ptr, w.region = true, pg.type_[id] }
            id = ops[0].op
        case .Index:
            if _, is_slice := distinct_base(pg.type_[ops[0].op]).(^Type_Slice); is_slice && !w.via_ptr {
                w.via_ptr, w.region = true, pg.type_[id]
            }
            id = ops[0].op
        case .Field, .Swizzle, .Variant, .Slice:
            id = ops[0].op
        case:
            return w   // unknown: no root
        }
    }
    return w
}

// Whether reading place `read` can observe place `dest` — the old emitter's
// rule (storage_read_hits). Yes when both are one variable's own storage, when
// what is read holds pointers, or when either is unknown. Otherwise it comes
// down to where each can live: a variable's own storage is an object of its
// type, one through a pointer an object of the pointee's; two overlap only if
// one's object type can hold the other's, and a local's own storage is never
// inside anything — but the caller's (a param, the result slot) can be. And
// the result slot never overlaps what a param reaches: a caller hands over a
// fresh slot whenever an argument carries storage.
@(private="file")
llvm_overlaps :: proc(e: ^Llvm, read, dest: Node_Id) -> bool {
    pg := e.pg
    if pg.op[read] == .Global { return false }   // a constant table is never written
    r, d := llvm_where(e, read), llvm_where(e, dest)
    if r.root == NO_NODE || d.root == NO_NODE || r.explicit { return true }
    if !d.via_ptr && llvm_in_result(e, d.root) && pg.kind[r.root] == .Param { return false }
    if !r.via_ptr && !d.via_ptr && r.root == d.root { return true }
    if !is_plain_data(pg.type_[read]) { return true }
    if !r.via_ptr && !d.via_ptr { return false }   // two variables' own storage
    read_own := !r.via_ptr && !llvm_in_result(e, r.root) && pg.kind[r.root] != .Param
    dest_own := !d.via_ptr && !llvm_in_result(e, d.root)
    if r.region == nil || d.region == nil { return true }
    return (!read_own && type_can_contain(d.region, r.region)) || (!dest_own && type_can_contain(r.region, d.region))
}

// Whether a variable lives in the caller's result slot: Self and its fields in
// a constructor, the local every return returns.
@(private="file")
llvm_in_result :: proc(e: ^Llvm, d: Node_Id) -> bool {
    if e.ctor && (d == e.node || e.pg.kind[d] == .Field) { return true }
    return d > e.node && d <= e.pg.last[e.node] && e.value[d - e.node] == "%sret"
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
    return llvm_once_before(e, v, false)
}

// Whether a synthetic slice local — a view — is its header's values: written
// once, from a slice, before every use, and used only through its len or cap
// (read) and its elements. Then its header is read once, where the slice is
// taken, into registers (a collection loop's view of its collection).
@(private="file")
llvm_holds_header :: proc(e: ^Llvm, v: Node_Id) -> bool {
    if !llvm_once_before(e, v, true) { return false }
    pg := e.pg
    for r in e.runs {
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Write { continue }
            ops := graph_operands(pg, op)
            if pg.op[ops[0].op] != .Var || pg.refers[ops[0].op] != v { continue }
            s := ops[1].op
            return s != NO_NODE && pg.op[s] == .Slice && e.user[s - e.node] == op
        }
    }
    return false
}

// Whether a variable is written once, before each of its uses: reads — or, a
// view (`header`), reads of its len or cap and its elements.
@(private="file")
llvm_once_before :: proc(e: ^Llvm, v: Node_Id, header: bool) -> bool {
    pg := e.pg
    write_run, write_at := -1, -1
    Read :: struct { run, at: int }
    reads := make([dynamic]Read, 0, 4, context.temp_allocator)
    for r, ri in e.runs {
        for op, at in graph_run(pg, int(r)) {
            ops := graph_operands(pg, op)
            for o, k in ops {
                if o.op == NO_NODE || pg.op[o.op] != .Var || pg.refers[o.op] != v { continue }
                u := e.user[op - e.node]
                switch {
                case pg.op[op] == .Write && k == 0:
                    if write_run >= 0 { return false }
                    write_run, write_at = ri, at
                case (pg.op[op] == .Read || pg.op[op] == .Deref) && !header:   // (a pointer's deref reads it)
                    append(&reads, Read{ri, at})
                case header && pg.op[op] == .Field && llvm_header_field(pg.name[op]) >= 0 && u >= 0 && pg.op[u] == .Read,
                     header && pg.op[op] == .Index && k == 0:
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
        if pg.kind[d] == .Const { return false }   // a constant has no storage: a use reads its value
        if d in e.hdr { return true }   // a view held as values: no storage
        switch {
        case pg.kind[d] == .Param || pg.kind[d] == .Field: e.value[op - e.node] = e.value[d - e.node]
        case d in e.arena:                                 e.value[op - e.node] = e.value[d - e.node]   // its arena alloc gives it storage
        case !e.held[d - e.node]:                          e.value[op - e.node] = llvm_storage(e, d)
        }
    case .Const:
        v, ok := llvm_const(e, op)
        if !ok { return false }
        e.value[op - e.node] = v
    case .Read:
        // An aggregate is read as where it is; a register value is loaded.
        place := ops[0].op
        t := pg.type_[op]
        big := pg.op[place] == .View && pg.name[place] == "#big_endian"
        switch {
        case llvm_direct(e, place):
            e.value[op - e.node] = llvm_direct_value(e, place)
        case llvm_aggregate(t):
            // A big-endian view's bytes are swapped as they're copied: only
            // a write of them can.
            if u := e.user[op - e.node]; big && (u < 0 || pg.op[u] != .Write || graph_operands(pg, u)[1].op != op) {
                return false
            }
            e.value[op - e.node] = e.value[place - e.node]
        case llvm_union_tag(e, place) != nil:   // a union's tag, read as a match reads it
            e.value[op - e.node] = load_union_tag(g, llvm_union_tag(e, place), e.value[place - e.node])
        case llvm_scalar(t) && pg.op[place] == .View:
            // From bytes at any address: align 1; big-endian, swapped.
            tmp := fresh_tmp(g)
            emit(g, "  %s = load %s, ptr %s, align 1", tmp, llvm_type_from_checker(t), e.value[place - e.node])
            e.value[op - e.node] = emit_bswap_value(g, tmp, t) if big else tmp
        case llvm_scalar(t):
            tmp := fresh_tmp(g)
            emit_load_into(g, tmp, llvm_type_from_checker(t), e.value[place - e.node])
            e.value[op - e.node] = tmp
        case:
            return false
        }
    case .Write:
        place := ops[0].op
        if pg.op[place] == .Slice { return llvm_copy_into(e, ops, span) }
        if llvm_union_tag(e, place) != nil { return false }   // a union's tag is its variant's: a construct writes it
        t := pg.type_[place]
        // Another type's value into bytes is a write through a view of them (later).
        if ops[1].op != NO_NODE && llvm_is_byte(t) != llvm_is_byte(pg.type_[ops[1].op]) { return false }
        // Into a partial array, text or a slice's elements fill a prefix.
        if pa := llvm_partial(t); pa != nil && ops[1].op != NO_NODE && !llvm_direct(e, place) {
            if text, is_text := llvm_text(e, ops[1].op); is_text { return llvm_text_into(e, place, pa, text) }
            if llvm_slice(pg.type_[ops[1].op]) != nil { return llvm_elements_into(e, place, pa, ops[1].op) }
        }
        val, ok := llvm_operand(e, ops[1], t)
        if !ok { return false }
        if pg.op[place] == .Var && pg.refers[place] in e.hdr { return true }   // held at its slice
        if pg.op[place] == .Var && e.carved[pg.refers[place]] == ops[1].op && ops[1].op != NO_NODE {
            return true   // a `let` declaration: the name is the carved memory
        }
        if pg.op[place] == .View && pg.name[place] != "" { return false }   // a big-endian write (none yet)
        if llvm_aggregate(t) {
            // An aggregate is copied into the place, unless a call built it
            // there; from a big-endian view, its integers are swapped in the copy.
            if llvm_direct(e, place) { return false }
            if val != e.value[place - e.node] { llvm_copy(e, e.value[place - e.node], val, t) }
            if r := ops[1].op; pg.op[r] == .Read {
                from := graph_operands(pg, r)[0].op
                if pg.op[from] == .View && pg.name[from] == "#big_endian" {
                    emit_bswap_in_place(g, e.value[place - e.node], llvm_type_from_checker(t), t)
                }
            }
            return true
        }
        if !llvm_scalar(t) { return false }
        if llvm_direct(e, place) {
            d := pg.refers[place]
            if !e.held[d - e.node] { return false }   // a param is read-only
            e.value[d - e.node] = val
            return true
        }
        // A slice's len stays within 0 ..= its cap.
        if pg.op[place] == .Field && pg.name[place] == "len" {
            hdr := graph_operands(pg, place)[0].op
            if llvm_header_elem(pg.type_[hdr]) != nil { emit_slice_len_check(g, e.value[hdr - e.node], val, span) }
        }
        if pg.op[place] == .View {   // into bytes at any address
            emit(g, "  store %s %s, ptr %s, align 1", llvm_type_from_checker(t), val, e.value[place - e.node])
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
        if ut := llvm_union(pg.type_[base]); ut != nil {
            // A union's tag is at its start — read as load_union_tag reads it
            // (a niche union's is its pointer's nullness); its padding, just
            // past the tag.
            if llvm_direct(e, base) { return false }
            at := e.value[base - e.node]
            switch pg.name[op] {
            case "tag": e.value[op - e.node] = at
            case "pad":
                if ut.tag_pad == nil { return false }
                pad := fresh_tmp(g)
                emit(g, "  %s = getelementptr i8, ptr %s, i32 %d", pad, at, elem_byte_size(union_tag_ir_type(ut)))
                e.value[op - e.node] = pad
            case: return false
            }
            return true
        }
        if llvm_header_elem(pg.type_[base]) != nil {
            // A slice header's len or cap; a held view's is its value.
            i := llvm_header_field(pg.name[op])
            if i < 0 { return false }
            if h, held := llvm_held_header(e, base); held {
                e.value[op - e.node] = h.len if i == SLICE.len else h.cap
                e.held[op - e.node] = true
                return true
            }
            if llvm_direct(e, base) { return false }
            tmp := fresh_tmp(g)
            emit_slice_gep(g, tmp, e.value[base - e.node], i)
            e.value[op - e.node] = tmp
            return true
        }
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
        // A pointer to a place read as another type — a view of bytes: later.
        if pt, is_ptr := distinct_base(pg.type_[op]).(^Type_Ptr); is_ptr && !llvm_same_type(pt.elem, pg.type_[place]) {
            return false
        }
        e.value[op - e.node] = e.value[place - e.node]
    case .Construct:
        return llvm_construct(e, op, ops)
    case .Zero:
        // A bare declaration, or the start of a literal: zero.
        place := ops[0].op
        t := pg.type_[place]
        if len(ops) == 2 { return llvm_sized_slice(e, op, ops) }
        if len(ops) != 1 || llvm_direct(e, place) { return false }
        if llvm_zeroed(e, place) && pg.written[op] == .Synthetic { return true }
        switch {
        case llvm_scalar(t):    emit_store(g, llvm_type_from_checker(t), llvm_zero(t), e.value[place - e.node])
        case llvm_partial(t) != nil: emit_partial_array_zero(g, e.value[place - e.node], llvm_partial(t))
        case llvm_aggregate(t):
            emit_memset_zero(g, e.value[place - e.node], llvm_size(e, t))
            stamp_zero_partial_arrays(g, e.value[place - e.node], t)
        case:                   return false
        }
    case .Index:
        base := ops[0].op
        at := pg.type_[base]
        // Text has no header: a byte of it, bounded like its slice (the
        // terminating 0 counts).
        if text, is_text := llvm_text(e, base); is_text {
            i := llvm_operand(e, ops[1], slice_header_width_type) or_return
            global, n := get_string_literal(g, text)
            name := graph_place_name(pg, ops[0])
            emit_bounds_check(g, i, fmt.tprintf("%d", n), name if name != "" else "array", span)
            tmp := fresh_tmp(g)
            emit_array_gep_var(g, tmp, fmt.tprintf("[%d x i8]", n), global, i, "i64")
            e.value[op - e.node] = tmp
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
        emit_array_gep_var(g, tmp, llvm_type_from_checker(at), e.value[base - e.node], i, "i64")
        e.value[op - e.node] = tmp
    case .Swizzle:
        // One component of a small array is its element (several: later).
        base := ops[0].op
        at := pg.type_[base]
        fa := llvm_array(at)
        name := pg.name[op]
        if fa == nil || len(name) != 1 || llvm_direct(e, base) { return false }
        k := swizzle_char_to_index(name[0])
        if k < 0 || k >= fa.size { return false }
        tmp := fresh_tmp(g)
        emit_array_gep_const(g, tmp, llvm_type_from_checker(at), e.value[base - e.node], k)
        e.value[op - e.node] = tmp
    case .Fill:
        // Every element of an array the one value.
        place := ops[0].op
        at := pg.type_[place]
        fa := llvm_array(at)
        if fa == nil || !llvm_scalar(fa.elem) || llvm_direct(e, place) { return false }
        v := llvm_operand(e, ops[1], fa.elem) or_return
        ir := llvm_type_from_checker(fa.elem)
        for k in 0 ..< fa.size {
            tmp := fresh_tmp(g)
            emit_array_gep_const(g, tmp, llvm_type_from_checker(at), e.value[place - e.node], k)
            emit_store(g, ir, v, tmp)
        }
    case .Arith:
        return llvm_arith(e, op, ops, span)
    case .Compare:
        return llvm_compare(e, op, ops)
    case .Unary:
        return llvm_unary(e, op, ops, span)
    case .Cast:
        x := ops[0].op
        from, to := pg.type_[x], pg.type_[op]
        // A partial array taken as a slice is its own header: no instruction.
        if llvm_partial(from) != nil && llvm_slice(to) != nil {
            // Text is no header: a view of its bytes, len its length (cap
            // counts the terminating zero).
            if text, is_text := llvm_text(e, x); is_text {
                n := len(text)
                e.value[op - e.node] = emit_build_temp_slice(g, e.value[x - e.node], fmt.tprintf("%d", n), fmt.tprintf("%d", n + 1))
                return true
            }
            e.value[op - e.node] = e.value[x - e.node]
            return true
        }
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
            if v != "%sret" { llvm_copy(e, "%sret", v, e.sret) }
            emit(g, "  ret void")
            return true
        }
        if e.by_value != nil {
            // A union: its value, loaded from where it is.
            if len(ops) != 1 { return false }
            at := llvm_operand(e, ops[0], e.by_value) or_return
            v := fresh_tmp(g)
            emit_load_into(g, v, e.ret, at)
            emit(g, "  ret %s %s", e.ret, v)
            return true
        }
        if len(ops) == 0 {
            if e.main {   // the C entry point: 0, the program went well
                emit(g, "  ret i64 0")
                return true
            }
            if e.ret != "void" { return false }
            emit(g, "  ret void")
            return true
        }
        if len(ops) != 1 || e.ret == "void" { return false }
        v, ok := llvm_operand(e, ops[0], e.ft.cg_returns[0])
        if !ok { return false }
        emit(g, "  ret %s %s", e.ret, v)
    case .Assert:
        if pg.written[op] != .Synthetic || pg.name[op] != "range" { return llvm_assert(e, op, ops, span) }
        c, ok := llvm_operand(e, ops[0], Type_Bool{})
        if !ok { return false }
        emit_range_check(g, c, span)
    case .Slice:
        return llvm_slice_op(e, op, ops)
    case .View:
        return llvm_view(e, op, ops, span)
    case .Carve:
        return llvm_carve(e, op, ops, span)
    case .Global:
        // A string constant: its bytes' address (its text is in the
        // constants table). A constant table: its global, read-only. (A
        // function: later.)
        if c, has := pg.consts[op]; has && c.is_text {
            global, n := get_string_literal(g, c.text)
            tmp := fresh_tmp(g)
            emit_string_gep(g, tmp, n, global)
            e.value[op - e.node] = tmp
            return true
        }
        d := pg.refers[op]
        value, is_table := pg.const_values[d]
        if d == NO_NODE || !is_table || !is_table_const(value, pg.type_[op]) { return false }
        e.value[op - e.node] = const_table(g, value, pg.type_[op], pg.name[op], span)
    case .Byte_Read:
        return llvm_byte_read(e, op, ops, span)
    case .Print:
        return llvm_print(e, op, ops, span)
    case .Crash:
        // Its message is text (one computed at runtime: later).
        msg := ""
        if len(ops) == 1 {
            if _, is_text := llvm_text(e, ops[0].op); !is_text { return false }
            msg = e.value[ops[0].op - e.node]
        }
        emit_crash(g, span, msg)
    case .Variant:
        // A union seen as one of its variants: each variant's struct overlays
        // the union from its start, so it is the union's own address.
        u := ops[0].op
        if llvm_union(pg.type_[u]) == nil || llvm_struct(pg.type_[op]) == nil || llvm_direct(e, u) { return false }
        e.value[op - e.node] = e.value[u - e.node]
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
        if d <= e.node || d > pg.last[e.node] || pg.kind[d] != .Local { return false }
        e.value[d - e.node] = emit_arena_bump(g, llvm_size(e, pg.type_[op]), pg.name[d], format_location(span.file, span.line, span.col))
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
    if pg.op[place] != .Var { return e.held[place - e.node] }   // a held view's len or cap
    d := pg.refers[place]
    if pg.kind[d] == .Param { return llvm_scalar(pg.type_[d]) }
    return e.held[d - e.node]
}

@(private="file")
llvm_direct_value :: proc(e: ^Llvm, place: Node_Id) -> string {
    if e.pg.op[place] != .Var { return e.value[place - e.node] }
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
// with the arguments, the place last. An array's elements, zeroed already,
// each run theirs.
@(private="file")
llvm_construct :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    t := pg.type_[op]
    if ut := llvm_union(pg.type_[dest]); ut != nil && llvm_same_type(pg.type_[dest], t) {
        // A variant: the union zeroed — its bytes past the variant too — then
        // its tag, and its partial arrays' headers. (Its defaults and fields
        // are the writes that follow.)
        if len(ops) != 1 || llvm_direct(e, dest) { return false }
        at := e.value[dest - e.node]
        if is_niche_layout(g, ut) {
            // A niche union is its Some variant's pointer: None is null, Some
            // the pointer its literal writes next (none written: null).
            some, _ := niche_variants(g, ut)
            if pg.name[op] != some || !llvm_variant_written(e, op, dest) { emit_store(g, "ptr", "null", at) }
            return true
        }
        sname, has := ut.variant_structs[pg.name[op]]
        st, found := g.checked.table.structs[sname]
        if !has || !found { return false }
        emit_memset_zero(g, at, llvm_size(e, pg.type_[dest]))
        tag := fresh_tmp(g)
        emit_field_gep_into(g, tag, llvm_type_from_checker(st), at, 0)
        emit_store(g, union_tag_ir_type(ut), fmt.tprintf("%d", ut.tag_map[pg.name[op]]), tag)
        stamp_zero_partial_arrays(g, at, st)   // (a partial array's zero isn't all zeros: no constructor stamps a variant's)
        return true
    }
    if fa := llvm_array(pg.type_[dest]); fa != nil && llvm_same_type(fa.elem, t) {
        if len(ops) != 1 || llvm_direct(e, dest) { return false }
        gen_construct_elements(g, e.value[dest - e.node], fa.elem, fa.size)
        return true
    }
    if pa := llvm_partial(pg.type_[dest]); pa != nil && llvm_same_type(pa.elem, t) {
        if len(ops) != 1 || llvm_direct(e, dest) { return false }
        if llvm_zeroed(e, dest) { return true }   // a constructor's field: at its entry
        elements := emit_partial_array_zero(g, e.value[dest - e.node], pa, stamp = false)
        gen_construct_elements(g, elements, pa.elem, pa.size)
        return true
    }
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
    hdr := e.value[base - e.node]
    data := h.data
    if !held {
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, hdr, SLICE.ptr)
        data = fresh_tmp(g)
        emit_load_into(g, data, "ptr", data_gep)
    }
    if pg.written[op] != .Synthetic {
        cap_val := h.cap
        if !held {
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, hdr, SLICE.cap)
            cap_val = fresh_tmp(g)
            emit_typed_load_cap(g, cap_val, cap_gep)
        }
        name := graph_place_name(pg, ops[0])
        emit_bounds_check(g, i, cap_val, name if name != "" else "slice", span)
    }
    tmp := fresh_tmp(g)
    emit_elem_gep(g, tmp, llvm_type_from_checker(elem), data, i, slice_layout.len_ir)
    e.value[op - e.node] = tmp
    return true
}

// A slice of an array or a slice: the elements from lo up to hi — lo 0 and
// hi the array's size or the slice's len when not given — as a new header,
// len = cap = hi - lo.
@(private="file")
llvm_slice_op :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    if pg.name[op] == "slice_from_ptr" {
        // Over raw memory: its pointer, len = cap = the count given.
        if len(ops) != 2 || ops[0].op == NO_NODE { return false }
        if _, is_ptr := distinct_base(pg.type_[ops[0].op]).(^Type_Ptr); !is_ptr { return false }
        n := llvm_operand(e, ops[1], slice_header_width_type) or_return
        e.value[op - e.node] = emit_build_temp_slice(g, e.value[ops[0].op - e.node], n, n)
        return true
    }
    if pg.name[op] != "" { return false }
    // Written to, it's the run of elements a write fills (llvm_copy_into).
    if u := e.user[op - e.node]; u >= 0 && pg.op[u] == .Write && graph_operands(pg, u)[0].op == op { return true }
    base := ops[0].op
    if base == NO_NODE || llvm_direct(e, base) { return false }
    lo, hi: string
    if len(ops) > 1 && ops[1].op != NO_NODE { lo = llvm_operand(e, ops[1], slice_header_width_type) or_return }
    if len(ops) > 2 && ops[2].op != NO_NODE { hi = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    bt := pg.type_[base]
    at := e.value[base - e.node]
    data: string
    if fa := llvm_array(bt); fa != nil {
        data = at
        if hi == "" { hi = fmt.tprintf("%d", fa.size) }
        if lo != "" {
            data = fresh_tmp(g)
            emit_array_gep_var(g, data, llvm_type_from_checker(bt), at, lo, slice_layout.len_ir)
        }
    } else if elem := llvm_header_elem(bt); elem != nil {
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, at, SLICE.ptr)
        data = fresh_tmp(g)
        emit_load_into(g, data, "ptr", data_gep)
        if hi == "" {
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, at, SLICE.len)
            hi = fresh_tmp(g)
            emit_typed_load_len(g, hi, len_gep)
        }
        if lo != "" {
            from := data
            data = fresh_tmp(g)
            emit_elem_gep(g, data, llvm_type_from_checker(elem), from, lo, slice_layout.len_ir)
        }
    } else {
        return false   // a partial array (later)
    }
    n := hi
    if lo != "" {
        n = fresh_tmp(g)
        emit(g, "  %s = sub %s %s, %s", n, slice_layout.len_ir, hi, lo)
    }
    // Written to a held view: its values, no header in memory.
    if u := e.user[op - e.node]; u >= 0 && pg.op[u] == .Write {
        if d := graph_operands(pg, u)[0].op; pg.op[d] == .Var && pg.refers[d] in e.hdr {
            e.hdr[pg.refers[d]] = {data, n, n}
            return true
        }
    }
    e.value[op - e.node] = emit_build_temp_slice(g, data, n, n)
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
    t := pg.type_[op]
    if llvm_direct(e, base) || (!llvm_scalar(t) && !llvm_aggregate(t)) || value_has_partial_array(g, t) { return false }
    off := llvm_operand(e, ops[1], slice_header_width_type) or_return
    data, bound := llvm_bytes(e, base) or_return
    emit_byte_size_bounds_check(g, bound, off, checker_type_byte_size(t), "view")
    tmp := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", tmp, data, slice_layout.len_ir, off)
    e.value[op - e.node] = tmp
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
    if pg.name[run] != "" || len(rops) < 2 || rops[1].op == NO_NODE || src == NO_NODE || llvm_direct(e, base) { return false }
    lo := llvm_operand(e, rops[1], slice_header_width_type) or_return
    hi := ""
    if len(rops) > 2 && rops[2].op != NO_NODE { hi = llvm_operand(e, rops[2], slice_header_width_type) or_return }
    // Each side's data and extent: a fixed array's own, else its header's.
    Side :: struct { data, bound: string, fixed: int, elem: Type }
    side :: proc(e: ^Llvm, at: Node_Id, bound_field: int) -> (s: Side, ok: bool) {
        g, pg := e.g, e.pg
        t := pg.type_[at]
        addr := e.value[at - e.node]
        if fa := llvm_array(t); fa != nil { return {addr, fmt.tprintf("%d", fa.size), fa.size, fa.elem}, true }
        s.elem = llvm_header_elem(t)
        if s.elem == nil { return }
        data_gep := fresh_tmp(g)
        emit_slice_gep(g, data_gep, addr, SLICE.ptr)
        s.data = fresh_tmp(g)
        emit_load_into(g, s.data, "ptr", data_gep)
        if bound_field >= 0 {
            b_gep := fresh_tmp(g)
            emit_slice_gep(g, b_gep, addr, bound_field)
            s.bound = fresh_tmp(g)
            emit_load_into(g, s.bound, slice_layout.len_ir, b_gep)
        }
        return s, true
    }
    dst := side(e, base, SLICE.cap) or_return
    from := side(e, src, -1) or_return
    if !llvm_same_type(dst.elem, from.elem) { return false }
    w := slice_layout.len_ir
    if hi == "" {
        n := fmt.tprintf("%d", from.fixed)
        if from.fixed == 0 {
            len_gep := fresh_tmp(g)
            emit_slice_gep(g, len_gep, e.value[src - e.node], SLICE.len)
            n = fresh_tmp(g)
            emit_typed_load_len(g, n, len_gep)
        }
        hi = fresh_tmp(g)
        emit(g, "  %s = add %s %s, %s", hi, w, lo, n)
    }
    name := ""
    #partial switch pg.op[base] {
    case .Var, .Field: name = pg.name[base]
    case .Deref:       name = pg.name[graph_operands(pg, base)[0].op]
    }
    emit_bounds_check(g, lo, dst.bound, name, span)
    hi_ok, hi_err := fresh_label(g, "slice.high.ok"), fresh_label(g, "slice.high.err")
    hi_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sgt %s %s, %s", hi_cmp, w, hi, dst.bound)
    emit_cond_br(g, hi_cmp, hi_err, hi_ok)
    emit_label(g, hi_err)
    msg_global, msg_len := get_string_literal(g, fmt.tprintf("runtime error: slice assignment out of bounds: high %%d > capacity %%d for '%s'\n", name))
    msg := fresh_tmp(g)
    emit_string_gep(g, msg, msg_len, msg_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", msg, w, hi, w, dst.bound)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, hi_ok)
    loop, body, done := fresh_label(g, "slice.loop"), fresh_label(g, "slice.body"), fresh_label(g, "slice.end")
    i_slot := fresh_tmp(g)
    emit_alloca(g, i_slot, w)
    emit_store(g, w, "0", i_slot)
    count := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", count, w, hi, lo)
    emit_br(g, loop)
    emit_label(g, loop)
    i := fresh_tmp(g)
    emit_load_into(g, i, w, i_slot)
    more := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", more, w, i, count)
    emit_cond_br(g, more, body, done)
    emit_label(g, body)
    elem_ir := llvm_type_from_checker(dst.elem)
    src_gep := fresh_tmp(g)
    emit_elem_gep(g, src_gep, llvm_type_from_checker(from.elem), from.data, i, w)
    v := fresh_tmp(g)
    emit_load_into(g, v, elem_ir, src_gep)
    at := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", at, w, lo, i)
    dst_gep := fresh_tmp(g)
    emit_array_gep_var(g, dst_gep, fmt.tprintf("[%d x %s]", dst.fixed, elem_ir), dst.data, at, w)
    emit_store(g, elem_ir, v, dst_gep)
    reanchor_partial_arrays(g, dst.elem, dst_gep)
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, i)
    emit_store(g, w, next, i_slot)
    emit_br(g, loop)
    emit_label(g, done)
    return true
}

// A string constant's text, when an operation's value is one: its global,
// or a read of it.
@(private="file")
llvm_text :: proc(e: ^Llvm, op: Node_Id) -> (string, bool) {
    pg := e.pg
    at := op
    if pg.op[at] == .Read { at = graph_operands(pg, at)[0].op }
    if at == NO_NODE || pg.op[at] != .Global { return "", false }
    c, has := pg.consts[at]
    return c.text, has && c.is_text
}

// Text into a partial array: its bytes into the elements — with the
// terminating zero when there's room — and len its length; the elements past
// it keep what they held.
@(private="file")
llvm_text_into :: proc(e: ^Llvm, place: Node_Id, pa: ^Type_Partial_Array, text: string) -> bool {
    g := e.g
    if llvm_type_from_checker(pa.elem) != "i8" || len(text) > pa.size { return false }
    at := e.value[place - e.node]
    elements := emit_partial_array_zero(g, at, pa, stamp = false)
    if len(text) > 0 {
        global, n := get_string_literal(g, text)
        src := fresh_tmp(g)
        emit_string_gep(g, src, n, global)
        emit_memcpy(g, elements, src, len(text) + 1 if pa.size > len(text) else len(text))
    }
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, at, SLICE.len)
    emit_typed_store_len(g, fmt.tprintf("%d", len(text)), len_gep)
    return true
}

// A slice's elements into a partial array: as many as fit (up to its cap),
// len their count; the elements past them keep what they held.
@(private="file")
llvm_elements_into :: proc(e: ^Llvm, place: Node_Id, pa: ^Type_Partial_Array, src: Node_Id) -> bool {
    g, pg := e.g, e.pg
    if !llvm_same_type(llvm_slice(pg.type_[src]).elem, pa.elem) { return false }
    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(pa.elem)
    at, hdr := e.value[place - e.node], e.value[src - e.node]
    dptr := fresh_tmp(g); emit_slice_gep(g, dptr, hdr, SLICE.ptr)
    data := fresh_tmp(g); emit_load_into(g, data, "ptr", dptr)
    slen := fresh_tmp(g); emit_slice_gep(g, slen, hdr, SLICE.len)
    n0 := fresh_tmp(g); emit_typed_load_len(g, n0, slen)
    cmp := fresh_tmp(g); emit(g, "  %s = icmp slt %s %s, %d", cmp, w, n0, pa.size)
    n := fresh_tmp(g); emit(g, "  %s = select i1 %s, %s %s, %s %d", n, cmp, w, n0, w, pa.size)
    elements := emit_partial_array_zero(g, at, pa, stamp = false)
    nbytes := fresh_tmp(g); emit(g, "  %s = mul %s %s, %d", nbytes, w, n, elem_byte_size(elem_ir, g.checked))
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %s, i1 false)", elements, data, nbytes)
    plen := fresh_tmp(g); emit_slice_gep(g, plen, at, SLICE.len)
    emit_typed_store_len(g, n, plen)
    return true
}

// A byte buffer's data and its bound: a byte slice's or partial array's
// pointer and cap, a byte array's own address and size.
@(private="file")
llvm_bytes :: proc(e: ^Llvm, base: Node_Id) -> (data, bound: string, ok: bool) {
    g, pg := e.g, e.pg
    if llvm_direct(e, base) { return }
    bt := pg.type_[base]
    at := e.value[base - e.node]
    if fa := llvm_array(bt); fa != nil && llvm_is_byte(fa.elem) {
        return at, fmt.tprintf("%d", fa.size), true
    }
    elem := llvm_header_elem(bt)
    if elem == nil || !llvm_is_byte(elem) { return }
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, at, SLICE.ptr)
    data = fresh_tmp(g)
    emit_load_into(g, data, "ptr", data_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, at, SLICE.cap)
    bound = fresh_tmp(g)
    emit_typed_load_cap(g, bound, cap_gep)
    return data, bound, true
}

// Bytes read into a partial array: its header stamped, the span's elements
// copied in (whole elements, no more than its cap; `#big_endian` swapped),
// its len their count. The index form `bytes[off]` spans a full cap's worth
// (a span `bytes[lo:hi]`: the source's cap when hi is open; lo <= hi).
// (Into a struct or an array: later.)
@(private="file")
llvm_byte_read :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    if llvm_direct(e, dest) || len(ops) < 3 { return false }
    pa := llvm_partial(pg.type_[dest])
    if pa == nil { return llvm_sized_read(e, op, ops, span) }
    lo := "0"
    if ops[2].op != NO_NODE { lo = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    spanned := len(ops) > 3
    hi := ""
    if spanned && ops[3].op != NO_NODE { hi = llvm_operand(e, ops[3], slice_header_width_type) or_return }
    data, bound := llvm_bytes(e, ops[1].op) or_return
    bytes := fmt.tprintf("%d", pa.size * elem_byte_size(llvm_type_from_checker(pa.elem), g.checked))
    if spanned {
        if hi == "" { hi = bound }
        w := slice_layout.len_ir
        inv_ok, inv_err := fresh_label(g, "pa.inv.ok"), fresh_label(g, "pa.inv.err")
        inv_cmp := fresh_tmp(g)
        emit(g, "  %s = icmp slt %s %s, %s", inv_cmp, w, hi, lo)
        emit_cond_br(g, inv_cmp, inv_err, inv_ok)
        emit_label(g, inv_err)
        inv_global, inv_len := get_string_literal(g, "runtime error: partial-array byte read slice bounds inverted (low=%d, high=%d) for partial-array byte read\n")
        inv_ptr := fresh_tmp(g)
        emit_string_gep(g, inv_ptr, inv_len, inv_global)
        emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", inv_ptr, w, lo, w, hi)
        emit(g, "  call void @exit(i32 1)")
        emit(g, "  unreachable")
        emit_label(g, inv_ok)
        bytes = fresh_tmp(g)
        emit(g, "  %s = sub %s %s, %s", bytes, w, hi, lo)
    }
    gen_partial_array_byte_fill_at_core(g, e.value[dest - e.node], pa, data, lo, bytes, pg.name[op] == "#big_endian", span)
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
    t := pg.type_[dest]
    sd := llvm_struct(t)
    if len(ops) < 4 || (sd == nil && llvm_array(t) == nil) { return false }
    lo := "0"
    if ops[2].op != NO_NODE { lo = llvm_operand(e, ops[2], slice_header_width_type) or_return }
    hi := ""
    if ops[3].op != NO_NODE { hi = llvm_operand(e, ops[3], slice_header_width_type) or_return }
    data, bound := llvm_bytes(e, ops[1].op) or_return
    if hi == "" { hi = bound }
    w := slice_layout.len_ir
    loc := format_location(span.file, span.line, span.col)
    size := checker_type_byte_size(t)
    n := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", n, w, hi, lo)
    end := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", end, w, lo, n)
    src_ok, src_err := fresh_label(g, "span.src.ok"), fresh_label(g, "span.src.err")
    src_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", src_cmp, w, end, bound)
    emit_cond_br(g, src_cmp, src_err, src_ok)
    emit_label(g, src_err)
    src_global, src_len := get_string_literal(g, fmt.tprintf("<%s> runtime error: sized read runs past the source buffer\n", loc))
    src_msg := fresh_tmp(g)
    emit_string_gep(g, src_msg, src_len, src_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s)", src_msg)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, src_ok)
    dst_ok, dst_err := fresh_label(g, "span.dst.ok"), fresh_label(g, "span.dst.err")
    dst_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %d", dst_cmp, w, n, size)
    emit_cond_br(g, dst_cmp, dst_err, dst_ok)
    emit_label(g, dst_err)
    dst_global, dst_len := get_string_literal(g, fmt.tprintf("<%s> runtime error: sized read of %%d bytes exceeds destination (%d bytes)\n", loc, size))
    dst_msg := fresh_tmp(g)
    emit_string_gep(g, dst_msg, dst_len, dst_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s)", dst_msg, w, n)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, dst_ok)
    src := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", src, data, w, lo)
    at := e.value[dest - e.node]
    emit_memset_zero(g, at, size)
    emit_memcpy_runtime(g, at, src, n)
    if sd != nil { fixup_partial_array_fields(g, at, sd) }
    if pg.name[op] == "#big_endian" { emit_bswap_in_place(g, at, llvm_type_from_checker(t), t) }
    return true
}

// A sized slice, `s : []T(n)`: storage for n elements on the stack (bytes
// 16-aligned, for what's taken from them), zeroed, and s's header over it —
// len 0, cap n. (A big one, on the arena: later.)
@(private="file")
llvm_sized_slice :: proc(e: ^Llvm, op: Node_Id, ops: []Operand) -> bool {
    g, pg := e.g, e.pg
    dest := ops[0].op
    sl := llvm_slice(pg.type_[dest])
    if sl == nil || pg.op[dest] != .Var || llvm_direct(e, dest) { return false }
    n := llvm_operand(e, ops[1], slice_header_width_type) or_return
    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(sl.elem)
    size := elem_byte_size(elem_ir, g.checked)
    name := fmt.tprintf("%%%s.data", pg.name[pg.refers[dest]])
    for k := 2; e.used[name]; k += 1 { name = fmt.tprintf("%%%s.data.%d", pg.name[pg.refers[dest]], k) }
    e.used[name] = true
    if c, is_const := pg.consts[ops[1].op]; is_const {
        total := int(c.int) * size
        if total >= 1024 { return false }
        emit_alloca(g, name, fmt.tprintf("[%d x %s]%s", c.int, elem_ir, ", align 16" if elem_ir == "i8" else ""))
        emit_memset_zero(g, name, total)
    } else {
        emit_alloca_runtime(g, name, elem_ir, w, n, 16 if elem_ir == "i8" else 0)
        bytes := n
        if size != 1 {
            bytes = fresh_tmp(g)
            emit(g, "  %s = mul %s %s, %d", bytes, w, n, size)
        }
        emit(g, "  call void @llvm.memset.p0.i64(ptr %s, i8 0, i64 %s, i1 false)", name, bytes)
    }
    hdr := e.value[dest - e.node]
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, hdr, SLICE.ptr)
    emit_store(g, "ptr", name, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, hdr, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, hdr, SLICE.cap)
    emit_typed_store_cap(g, n, cap_gep)
    return true
}

// A take from storage's cursor: storage's pointer and len (the cursor), the
// cursor aligned for what's taken, that address, the cursor moved past it —
// checked against storage's cap — and stored as its len. `let(T, s)` is that
// memory; `slice([:n]T, s)` a header over n of them (len = cap = n), built
// where it goes when that's fresh, as a call's result is. Positional (a view
// of bytes for storage): `let` is the view (`slice`: later).
@(private="file")
llvm_carve :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    storage := ops[0].op
    if storage == NO_NODE || llvm_direct(e, storage) { return false }
    let := pg.name[op] == "let"
    if pg.op[storage] == .View {
        if !let { return false }
        e.value[op - e.node] = e.value[storage - e.node]
        return true
    }
    if llvm_header_elem(pg.type_[storage]) == nil { return false }
    // A `let` is only a declaration's (it names the memory); anything else later.
    if u := e.user[op - e.node]; let && (u < 0 || pg.op[u] != .Write || pg.refers[graph_operands(pg, u)[0].op] not_in e.carved) {
        return false
    }
    t := pg.type_[op]
    elem := t
    count := ""
    if !let {
        sl := llvm_slice(t)
        if sl == nil || len(ops) < 2 { return false }
        elem = sl.elem
        count = llvm_operand(e, ops[1], slice_header_width_type) or_return
    }
    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(elem)
    size, align := elem_byte_size(elem_ir, g.checked), elem_alignment(elem_ir, g.checked)
    hdr := e.value[storage - e.node]
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, hdr, SLICE.ptr)
    data := fresh_tmp(g)
    emit_load_into(g, data, "ptr", data_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, hdr, SLICE.len)
    cursor := fresh_tmp(g)
    emit_typed_load_len(g, cursor, len_gep)
    advance := fmt.tprintf("%d", size)
    if !let {
        advance = fresh_tmp(g)
        emit(g, "  %s = mul %s %s, %d", advance, w, count, size)
    }
    if align > 1 {
        bumped := fresh_tmp(g)
        emit(g, "  %s = add %s %s, %d", bumped, w, cursor, align - 1)
        cursor = fresh_tmp(g)
        emit(g, "  %s = and %s %s, %d", cursor, w, bumped, -align)
    }
    at := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", at, data, w, cursor)
    moved := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", moved, w, cursor, advance)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, hdr, SLICE.cap)
    cap_val := fresh_tmp(g)
    emit_typed_load_cap(g, cap_val, cap_gep)
    over := fresh_tmp(g)
    emit(g, "  %s = icmp sgt %s %s, %s", over, w, moved, cap_val)
    fail, ok := fresh_label(g, "take.fail"), fresh_label(g, "take.ok")
    emit_cond_br(g, over, fail, ok)
    emit_label(g, fail)
    loc := format_location(span.file, span.line, span.col)
    name := graph_place_name(pg, ops[0])
    msg := fmt.tprintf("%s runtime error: take overflows storage: advance to %%d exceeds cap %%d for '%s'\n", loc, name)
    msg_global, msg_len := get_string_literal(g, msg)
    msg_ptr := fresh_tmp(g)
    emit_string_gep(g, msg_ptr, msg_len, msg_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", msg_ptr, w, moved, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok)
    emit_typed_store_len(g, moved, len_gep)
    if let {
        e.value[op - e.node] = at
        return true
    }
    // The header: in a fresh declaration's (or the result's) slot, else a temporary.
    out := ""
    if u := e.user[op - e.node]; u >= 0 && pg.op[u] == .Write {
        dest := graph_operands(pg, u)[0].op
        if pg.op[dest] == .Var {
            s := pg.stmt[u]
            if (s >= 0 && pg.stmts[s].kind == .Decl) || llvm_place(e, dest) == "%sret" { out = llvm_place(e, dest) }
        }
    }
    if out == "" {
        out = fresh_tmp(g)
        emit_alloca(g, out, SLICE_IR_TYPE)
    }
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, out, SLICE.ptr)
    emit_store(g, "ptr", at, ptr_gep)
    n_gep := fresh_tmp(g)
    emit_slice_gep(g, n_gep, out, SLICE.len)
    emit_typed_store_len(g, count, n_gep)
    c_gep := fresh_tmp(g)
    emit_slice_gep(g, c_gep, out, SLICE.cap)
    emit_typed_store_cap(g, count, c_gep)
    e.value[op - e.node] = out
    return true
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
        t, v := pg.type_[o.op], e.value[o.op - e.node]
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
    if spec, ir, raw := raw_print(pg.name[op]); raw {
        if len(args) != 1 || args[0].addr != "" || llvm_type_from_checker(args[0].t) != ir { return false }
        emit_print_raw(g, spec, ir, args[0].val)
        return true
    }
    if len(args) > 0 && args[0].is_text && string_has_format_pct(args[0].text) {
        emit_print_format(g, args[0].text, args[1:], span)
    } else {
        for a, i in args {
            if i > 0 { emit_print_literal(g, " ") }
            emit_print_operand(g, a)
        }
    }
    emit_print_newline(g)
    return true
}

// An assert: its condition, a value already, branches to the failure, which
// reports a comparison's sides by their text and value (emit_assert_fail).
// With `-no assert` the condition isn't evaluated either: later.
@(private="file")
llvm_assert :: proc(e: ^Llvm, op: Node_Id, ops: []Operand, span: Span) -> bool {
    g, pg := e.g, e.pg
    if g.no_assert { return false }
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
        t := pg.type_[compared[0].op]
        if assert_reports(llvm_type_from_checker(t)) {
            ir, unsigned = llvm_type_from_checker(t), llvm_unsigned(t)
            for &s, i in sides { s = {texts[i], e.value[compared[i].op - e.node], t} }
            reported = sides[:]
        }
    }
    emit_assert_fail(g, span, pg.name[op], reported, ir, unsigned)
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
    targets := 0
    for edge in graph_out(pg, op) { if edge.kind == .Then { targets += 1 } }
    if targets != len(cases) && targets != len(cases) + 1 { return false }
    target :: proc(e: ^Llvm, op: Node_Id, k: int) -> string { return e.label[llvm_target(e, op, k)] }
    fail := targets == len(cases)
    subject := ops[0].op
    if ut := llvm_union(pg.type_[subject]); ut != nil {
        if llvm_direct(e, subject) { return false }
        tag, ir := load_union_tag(g, ut, e.value[subject - e.node]), union_tag_ir_type(ut)
        default := fresh_label(g, "match.fail") if fail else target(e, op, len(cases))
        sw := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&sw, "  switch %s %s, label %%%s [\n", ir, tag, default)
        for c, i in cases {
            v, has := pg.consts[c.op]
            if !has || v.is_float { return false }
            fmt.sbprintf(&sw, "    %s %d, label %%%s\n", ir, v.int, target(e, op, i))
        }
        strings.write_string(&sw, "  ]")
        emit_raw(g, strings.to_string(sw))
        if fail {
            emit_label(g, default)
            emit_match_fail(g, span, tag, ir, union_tag_unsigned(ut))
        }
        return true
    }
    t := pg.type_[subject]
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
        emit(g, "  %s = icmp eq %s %s, %s", cmp, ir, value, v)
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
    root := llvm_where(e, dest).root
    after := false
    for o in graph_run(pg, int(e.run)) {
        if o == op { after = true; continue }
        if !after || pg.op[o] != .Write { continue }
        p := graph_operands(pg, o)[0].op
        if pg.op[p] != .Field { continue }
        v := graph_operands(pg, p)[0].op
        if pg.op[v] == .Variant && llvm_where(e, v).root == root { return true }
    }
    return false
}

// A defer's block, run where its scope is left: its code emitted here — a
// copy at each exit, as though written there — its labels fresh, its entry
// going on in the current block, its end falling through to what follows.
@(private="file")
llvm_run_defer :: proc(e: ^Llvm, op: Node_Id) -> bool {
    g, pg := e.g, e.pg
    d := NO_NODE
    for edge in graph_out(pg, op) { if edge.kind == .Runs { d = edge.to } }
    if d == NO_NODE { return false }
    runs: [dynamic]i32
    runs.allocator = context.temp_allocator
    body := runs[:graph_code_runs(pg, g.run_starts, d, &runs)]
    llvm_sort_runs(body[1:])
    for r in body {
        for o in graph_run(pg, int(r)) {
            for edge in graph_out(pg, o) {
                if edge.kind == .Then && g.run_starts[edge.to] == body[0] { return false }   // its entry a loop's head: later
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
            e.why = o
            if !llvm_op(e, o) { return false }
        }
    }
    if end != "" { emit_label(g, end) }
    return true
}

// A view held as its header's values (llvm_holds_header).
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
        case llvm_union(result) != nil:  ret = llvm_type_from_checker(result)   // as a value (the old ABI)
        case llvm_aggregate(result):
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
    if llvm_union(result) != nil {
        // A union value, kept where it can be read as one: the synthetic
        // local it initializes (a match's subject), else a temporary the
        // write copies from (the old emitter's; a slot like a struct's: later).
        at := ""
        pg := e.pg
        if u := e.user[op - e.node]; u >= 0 && pg.op[u] == .Write {
            dest := graph_operands(pg, u)[0].op
            if pg.op[dest] == .Var && pg.written[pg.refers[dest]] == .Synthetic &&
               !llvm_direct(e, dest) && llvm_ahead(e, dest) {
                at = llvm_place(e, dest)
            }
        }
        if at == "" {
            at = fresh_tmp(g)
            emit_alloca(g, at, ret)
        }
        emit_store(g, ret, tmp, at)
        e.value[op - e.node] = at
    }
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
                // (The result slot is no fresher than any place: the local
                // every return returns lives there, and `x = f(x)` passes it.)
                if fresh && llvm_ahead(e, dest) { return llvm_place(e, dest), true }
                // An update `x = f(x, …)` built in place: later.
                if _, consumes := consumed_param_of(callee).?; consumes { return "", false }
                if !llvm_passes_storage(callee) && llvm_ahead(e, dest) { return llvm_place(e, dest), true }
            }
        }
    }
    if routes_to_arena(result) { return "", false }   // a temporary on the arena (later)
    tmp := fresh_tmp(e.g)
    emit_alloca(e.g, tmp, llvm_type_from_checker(result))
    return tmp, true
}

// Whether place p's address is at hand for a call to build its result in: it
// was computed, or it is a variable, or a field or constant index of one —
// computed now, ahead of its turn (the graph has the value before the place;
// its turn then skips it).
@(private="file")
llvm_ahead :: proc(e: ^Llvm, p: Node_Id) -> bool {
    pg := e.pg
    if e.value[p - e.node] != "" || pg.op[p] == .Var { return true }
    ops := graph_operands(pg, p)
    #partial switch pg.op[p] {
    case .Field:
        if !llvm_ahead(e, ops[0].op) { return false }
    case .Index:
        if ops[1].op == NO_NODE || pg.op[ops[1].op] != .Const || !llvm_ahead(e, ops[0].op) { return false }
        if !llvm_op(e, ops[1].op) { return false }
        e.ahead[ops[1].op] = true
    case:
        return false
    }
    if pg.op[ops[0].op] == .Var && e.value[ops[0].op - e.node] == "" {
        if !llvm_op(e, ops[0].op) { return false }
        e.ahead[ops[0].op] = true
    }
    if !llvm_op(e, p) { return false }
    e.ahead[p] = true
    return true
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

// An aggregate — a struct, a fixed array, a slice's header, a partial array, a
// union — is a value handled by its address: a param is a pointer to the
// caller's, and reading one yields where it is; a copy re-points the partial
// arrays in it at its own elements. (One holding a sized slice's backing: later.)
@(private="file")
llvm_aggregate :: proc(t: Type) -> bool {
    return llvm_struct(t) != nil || llvm_array(t) != nil || llvm_slice(t) != nil || llvm_partial(t) != nil || llvm_union(t) != nil
}

// The union whose `.tag` place p is; nil when p is no union's tag.
@(private="file")
llvm_union_tag :: proc(e: ^Llvm, p: Node_Id) -> ^Type_Union {
    pg := e.pg
    if pg.op[p] != .Field || pg.name[p] != "tag" { return nil }
    return llvm_union(pg.type_[graph_operands(pg, p)[0].op])
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
    if !ok || pa.elem == nil || is_infer(pa.elem) || llvm_has_backing(pa.elem) { return nil }
    return pa
}

// The element type of what a slice header describes — a slice's or a
// partial array's; nil for anything else.
@(private="file")
llvm_header_elem :: proc(t: Type) -> Type {
    if sl := llvm_slice(t); sl != nil { return sl.elem }
    if pa := llvm_partial(t); pa != nil { return pa.elem }
    return nil
}

// A slice: its header, {len, cap, ptr}, is the aggregate.
@(private="file")
llvm_slice :: proc(t: Type) -> ^Type_Slice {
    if t == nil || is_infer(t) { return nil }
    sl, ok := distinct_base(t).(^Type_Slice)
    if !ok || sl.elem == nil || is_infer(sl.elem) { return nil }
    return sl
}

// A slice header's field by name; -1 for none.
@(private="file")
llvm_header_field :: proc(name: string) -> int {
    switch name {
    case "len": return SLICE.len
    case "cap": return SLICE.cap
    }
    return -1
}

@(private="file")
llvm_struct :: proc(t: Type) -> ^Scope_Body {
    if t == nil { return nil }
    sd := as_struct_body(t)
    if sd == nil || llvm_has_backing(t) { return nil }
    return sd
}

// A fixed array of register values or aggregates.
@(private="file")
llvm_array :: proc(t: Type) -> ^Type_Fixed_Array {
    if t == nil || is_infer(t) { return nil }
    fa, ok := distinct_base(t).(^Type_Fixed_Array)
    if !ok || llvm_has_backing(t) || (!llvm_scalar(fa.elem) && !llvm_aggregate(fa.elem)) { return nil }
    return fa
}

// Whether a value holds a sized slice's backing storage (later).
@(private="file")
llvm_has_backing :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Partial_Array: return llvm_has_backing(v.elem)
    case ^Type_Fixed_Array:   return llvm_has_backing(v.elem)
    case ^Type_Scope:
        sd := as_struct_body(v)
        if sd == nil { return false }
        if sd.backing_bytes > 0 { return true }
        for &f in sd.fields { if llvm_has_backing(f.type_) { return true } }
    }
    return false
}

// Whether two types lower to one IR type. An unresolved one matches nothing:
// the fun is declined rather than guessed at.
@(private="file")
llvm_same_type :: proc(a, b: Type) -> bool {
    if a == nil || b == nil || is_infer(a) || is_infer(b) { return false }
    // Pointers lower alike; what they point to must match too (a byte
    // address taken as a pointer to T is a view of bytes: later).
    pa, a_ptr := distinct_base(a).(^Type_Ptr)
    pb, b_ptr := distinct_base(b).(^Type_Ptr)
    if a_ptr && b_ptr { return llvm_same_type(pa.elem, pb.elem) }
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

// A param's IR type: an aggregate goes by address.
@(private="file")
llvm_param_type :: proc(t: Type) -> (string, bool) {
    if llvm_scalar(t) { return llvm_type_from_checker(t), true }
    if llvm_aggregate(t) { return "ptr", true }
    return "", false
}

@(private="file")
llvm_is_byte :: proc(t: Type) -> bool {
    _, is_byte := distinct_base(t).(Type_Byte)
    return is_byte
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
