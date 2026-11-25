package mara

import "core:fmt"
import "core:os"

// storage.odin — where each value of a fun's code lives, decided for the
// whole fun before a backend emits it: which locals need storage of their own
// and which are a value, a view's header values, carved memory, a match's
// payload or the caller's result slot; which temporaries are built in the
// place they are then written to; which functional updates build into their
// argument; which swaps are done in place; which big temporaries the fun
// holds on the arena. A backend reads these facts; it decides none of them.
//
// (Read off a fun's code in the lowered program, the third layer, as codegen
// read them while it emitted.)

Storage :: struct {
    pc:        ^Program_Code,
    pg:        ^Program_Graph,
    summaries: ^Reach_Summaries,   // (what each callee reaches: reach_summary's cache)
    runs:      []i32,              // the code's runs, its entry's first; then its defer blocks'
    own:       int,                // how many of the runs are its own code's
    ctor:      bool,               // a struct's code: Self is built in the caller's slot
    main:      bool,               // main's body
    one_slot:  bool,               // its aggregate result is one slot (one result, or a constructor's Self)

    user:     []Node_Id,                    // by id: the one operation using an operation's value (-1: none, -2: several)
    out_user: map[Operand]Node_Id,          // each output's user, as `user` is each operation's
    bound:    map[Node_Id]Node_Id,          // a match arm's binding → its variant place: it is the payload
    arena:    map[Node_Id]bool,             // a big local with an arena alloc of its own
    held:     []bool,                       // by id: a synthetic scalar local written once, before every read: that value, no storage
    views:    map[Node_Id]bool,             // a synthetic view used only through its header: its header's values, no storage
    update:   map[Node_Id]bool,             // a call `x = f(x, …)` building its result in x, its argument (storage_in_place_updates)
    alias:    map[Node_Id]Node_Id,          // ... the argument's place's operations: the destination's, computed before
    carved:   map[Node_Id]Node_Id,          // a local declared from a `let` take → that take: it is the carved memory
    result:   map[Node_Id]int,              // a local built in the caller's result slot → which result's
    in_place: map[Node_Id]Node_Id,          // a temporary → the place it is built in
    hoist:    map[Node_Id][dynamic]Node_Id, // that place's first write → the reads of it taken before it
    swaps:    map[Node_Id][2]Node_Id,       // a swap's first put → the two places it swaps
    swapped:  map[Node_Id]bool,             // a swap's held locals: no storage
    done:     map[Node_Id]bool,             // operations a swap does: nothing to do where they are
    temps:    [dynamic]Storage_Temp,        // its big temporaries: on the arena from its entry until it returns (main's, its run's)
    addressed: map[Node_Id]bool,            // a local some pointer or view may reach: its address taken, a view of it made (storage_views)
    calls:    map[Node_Id]Call_Place,       // a call's aggregate result: where it's built (none: a temporary of its own)
    out_at:   map[Operand]Node_Id,          // one of several results, an aggregate: the declared variable it's built in (none: a temporary)
    placed:   bool,                         // the temporaries built in place are known (storage_in_result)
    pos:      []i32,                        // by id: an operation's place in the order the code runs its own runs (-1: none)

    stop: Node_Id,   // a variable no storage can be found for (the backend stops there); NO_NODE: none
}

// Where a call builds its aggregate result: in a temporary of its own, in the
// fun's result slot (its user returns it), or in the place its user writes it
// to (the user's destination).
Call_Place :: enum u8 { Temporary, Result_Slot, Dest }

// A big temporary: a synthetic local's storage (`at` the local), or where a
// call builds a result that has no place to go (`at` that output).
Storage_Temp :: struct {
    at: Operand,
    t:  Type,
}

// A fun's storage. (`sret`, `rets`: its result, built in the caller's slot —
// a struct or array, or several results each in one.)
storage_of :: proc(checked: ^Checked_Program, pg: ^Program_Graph, summaries: ^Reach_Summaries, runs: []i32, own: int,
                   ctor, main: bool, sret: Type, rets: []Type) -> ^Storage {
    s := new(Storage)
    s^ = {pc = &checked.code, pg = pg, summaries = summaries, runs = runs, own = own, ctor = ctor, main = main, stop = NO_NODE}
    s.one_slot = rets == nil || ctor
    storage_users(s)
    storage_named_results(s, sret, rets)
    storage_variables(s)
    storage_in_place_updates(s)
    storage_carved(s)
    storage_views(s)
    if sret != nil || rets != nil { storage_result_slot(s, rets) }
    storage_in_place(s)
    storage_swaps(s)
    storage_big_temps(s)
    if s.stop == NO_NODE {
        storage_calls(s, sret)
        storage_census(s)
    }
    if len(s.temps) > 0 && !checked.table.has_scope_allocator && !checked.table.context_expected_at_runtime {
        tp := s.temps[0]
        storage_fatal(graph_origin(pg, tp.at.op), CODE_TEMPORARY_NO_ARENA, type_name(tp.t), type_size(tp.t))
    }
    return s
}

// MARA_TEMPS=1: each temporary an aggregate is held in, a line to stderr —
// what it is (a call's result, one of several results, a local lowering
// made), what uses it (a write copies it, a call takes it as an argument),
// its type, its size, its place. A census: what a rule against temporaries
// would stop.
@(private="file") storage_census_on: i8

@(private="file")
storage_census :: proc(s: ^Storage) {
    if storage_census_on == 0 { storage_census_on = 1 if os.get_env("MARA_TEMPS", context.temp_allocator) != "" else 2 }
    if storage_census_on != 1 { return }
    pg := s.pg
    said :: proc(pg: ^Program_Graph, what, use: string, t: Type, at: Node_Id) {
        fmt.eprintf("TEMP\t%s\t%s\t%s\t%d\t%s\n", what, use, type_name(t), type_size(t), span_location(graph_origin(pg, at)))
    }
    use_of :: proc(s: ^Storage, u: Node_Id) -> string {
        if u == NO_NODE { return "unused" }
        if u < 0 { return "several" }
        #partial switch graph_op_of(s.pg, u) {
        case .Write:            return "copied"
        case .Call, .Construct: return "argument"
        }
        return fmt.tprintf("%v", graph_op_of(s.pg, u))
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Call { continue }
            callee := graph_called(pg, op)
            what := "call"
            if callee == nil {
                callee = graph_signature(pg, op)
            } else if _, src := callee.origin.(Origin_Source); !src || callee.kind != .Fun {
                what = "c call"
            }
            if callee == nil { continue }
            n := fn_result_count(callee)
            for i in 0 ..< n {
                rt := fn_result(callee, i)
                if llvm_scalar(rt) || !llvm_aggregate(rt) { continue }
                if n == 1 {
                    if op not_in s.calls { said(pg, what, use_of(s, s.user[graph_ix(pg, op)]), rt, op) }
                    continue
                }
                o := Operand{op, i32(i)}
                if o in s.out_at { continue }
                u, used := s.out_user[o]
                said(pg, "result" if what == "call" else "c result", use_of(s, u if used else NO_NODE), rt, op)
            }
        }
    }
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct: id = graph_last(pg, id); continue   // (another scope's)
        }
        if pg.kind[id] != .Local || pg.written[id] != .Synthetic { continue }
        t := graph_type(pg, id)
        if t == nil || llvm_scalar(t) || !llvm_aggregate(t) { continue }
        if id in s.in_place || id in s.result || id in s.carved || id in s.bound || id in s.swapped || id in s.views || s.held[id] { continue }
        copied, argument, parts, other := false, false, false, ""
        for r in s.runs {
            for op in graph_run(pg, int(r)) {
                for o, k in graph_operands(pg, op) {
                    if graph_leaf_decl(pg, o.op) != id { continue }
                    use := ""
                    #partial switch graph_op_of(pg, op) {
                    case .Read:    use = use_of(s, s.user[graph_ix(pg, op)])
                    case .Address: use = use_of(s, s.user[graph_ix(pg, op)])
                    case .Write, .Zero, .Construct, .Fill, .Byte_Read, .Arena_Alloc:
                        if k == 0 { continue }   // (its building)
                        use = "copied" if graph_op_of(pg, op) == .Write else "argument"
                    case .Call:    use = "argument"
                    case .Field, .Index, .Slice, .Variant, .View, .Swizzle: use = "parts"
                    case:          use = fmt.tprintf("%v", graph_op_of(pg, op))
                    }
                    switch use {
                    case "copied":   copied = true
                    case "argument": argument = true
                    case "parts":    parts = true
                    case:            other = use
                    }
                }
            }
        }
        use := "copied" if copied else "argument" if argument else "parts" if parts else other if other != "" else "unused"
        said(pg, fmt.tprintf("local %s", graph_name(pg, id)), use, t, id)
    }
}

// What storage can't be had for — a big temporary with no arena to live on,
// a result built over what its call reads — stops the build.
storage_fatal :: proc(span: Span, format: string, args: ..any) -> ! {
    codegen_fatal(nil, span, format, ..args)
}

// Each operation's user, when it has exactly one (-1 for none, -2 for
// several); each match binding's variant place; each big local's arena alloc.
@(private="file")
storage_users :: proc(s: ^Storage) {
    pg := s.pg
    s.user = make([]Node_Id, graph_ix_count(pg))
    for &u in s.user { u = -1 }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            for o in graph_operands(pg, op) {
                if o.op == NO_NODE || o.op >= CONST && o.op < READ { continue }
                u := &s.user[graph_ix(s.pg, o.op)]
                u^ = op if u^ == -1 else -2
                ou, seen := s.out_user[o]
                s.out_user[o] = -2 if seen && ou != op else op
            }
            // A match arm's binding is the payload's place.
            if graph_op_of(pg, op) == .Variant && graph_refers(pg, op) != NO_NODE { s.bound[graph_refers(pg, op)] = op }
            if graph_op_of(pg, op) == .Arena_Alloc { s.arena[graph_refers(pg, graph_operands(pg, op)[0].op)] = true }
        }
    }
}

// --- variables -------------------------------------------------------------------

// A named result in the caller's slot for it: with several results, a struct
// or fixed array one; a fun's single struct result. (A register value is a
// local of its own.)
@(private="file")
storage_named_results :: proc(s: ^Storage, sret: Type, rets: []Type) {
    pg := s.pg
    if s.ctor { return }
    i := 0   // which result
    for d := Node_Id(1); d <= pg.end; d += 1 {
        if graph_kind_of(pg, d) != .Result || pg.parent[d] != 0 { continue }
        defer i += 1
        if graph_written(pg, d) != .Explicit { continue }
        t := graph_type(pg, d)
        switch {
        case rets != nil:
            if llvm_struct(t) != nil || llvm_array(t) != nil { s.result[d] = i }
        case sret != nil && llvm_struct(t) != nil:
            s.result[d] = 0
        }
    }
}

// Which synthetic locals need no storage: a scalar written once, before every
// read, is that value; a view used only through its header, its header's
// values.
@(private="file")
storage_variables :: proc(s: ^Storage) {
    pg := s.pg
    s.held = make([]bool, int(pg.end) + 1)
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct:
            id = graph_last(pg, id)
        case .Local:
            if pg.written[id] != .Synthetic { continue }
            t := graph_type(pg, id)
            if llvm_scalar(t) && storage_holds(s, id) { s.held[id] = true }
            if llvm_slice(t) != nil && storage_holds_header(s, id) { s.views[id] = true }
        }
    }
}

// Whether a synthetic local is written once, before each of its reads: then
// it is that value, and needs no storage.
@(private="file")
storage_holds :: proc(s: ^Storage, v: Node_Id) -> bool {
    return storage_once_before(s, v, false)
}

// Whether a synthetic slice local — a view — is its header's values: written
// once, from a slice, before every use, and used only through its len or cap
// (read) and its elements. Then its header is read once, where the slice is
// taken, into registers (a collection loop's view of its collection).
@(private="file")
storage_holds_header :: proc(s: ^Storage, v: Node_Id) -> bool {
    if !storage_once_before(s, v, true) { return false }
    pg := s.pg
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Write { continue }
            ops := graph_operands(pg, op)
            if graph_leaf_decl(pg, ops[0].op) != v { continue }
            x := ops[1].op
            return x != NO_NODE && graph_op_of(pg, x) == .Slice && s.user[graph_ix(s.pg, x)] == op
        }
    }
    return false
}

// Whether a variable is written once, before each of its uses: reads — or, a
// view (`header`), reads of its len or cap and its elements.
@(private="file")
storage_once_before :: proc(s: ^Storage, v: Node_Id, header: bool) -> bool {
    pg := s.pg
    write_run, write_at := -1, -1
    Read :: struct { run, at: int }
    reads := make([dynamic]Read, 0, 4, context.temp_allocator)
    for r, ri in s.runs {
        for op, at in graph_run(pg, int(r)) {
            ops := graph_operands(pg, op)
            for o, k in ops {
                if graph_leaf_decl(pg, o.op) != v { continue }
                u := s.user[graph_ix(s.pg, op)]
                switch {
                case graph_op_of(pg, op) == .Write && k == 0:
                    if write_run >= 0 { return false }
                    write_run, write_at = ri, at
                case (graph_op_of(pg, op) == .Read || graph_op_of(pg, op) == .Deref) && !header:   // (a pointer's deref reads it)
                    append(&reads, Read{ri, at})
                case header && graph_op_of(pg, op) == .Field && llvm_header_field(graph_name(pg, op)) >= 0 && u >= 0 && graph_op_of(pg, u) == .Read,
                     header && graph_op_of(pg, op) == .Index && k == 0:
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
        } else if !storage_dominates(s, write_run, rd.run) {
            return false
        }
    }
    return true
}

// Whether every path from the entry to run b passes through run a (both
// positions in s.runs).
@(private="file")
storage_dominates :: proc(s: ^Storage, a, b: int) -> bool {
    // Reach b from the entry without passing through a: then a doesn't dominate.
    pg := s.pg
    at: map[i32]int
    defer delete(at)
    for r, i in s.runs { at[r] = i }
    seen := make([]bool, len(s.runs), context.temp_allocator)
    todo := make([dynamic]int, 0, 8, context.temp_allocator)
    if a == 0 { return true }
    append(&todo, 0)
    seen[0] = true
    for len(todo) > 0 {
        i := pop(&todo)
        if i == b { return false }
        ops := graph_run(pg, int(s.runs[i]))
        for edge in graph_out(pg, ops[len(ops) - 1]) {
            j, ok := at[graph_run_starting(pg, edge.to)]
            if !ok || seen[j] || j == a { continue }
            seen[j] = true
            append(&todo, j)
        }
    }
    return true
}

// How many reads a variable has.
@(private="file")
storage_reads :: proc(s: ^Storage, v: Node_Id) -> int {
    pg := s.pg
    n := 0
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Read { continue }
            if graph_leaf_decl(pg, graph_operands(pg, op)[0].op) == v { n += 1 }
        }
    }
    return n
}

// Whether a place holds its value directly, not at an address: a scalar param
// (read-only, its argument) or a held synthetic local.
@(private="file")
storage_direct :: proc(s: ^Storage, place: Node_Id) -> bool {
    pg := s.pg
    if !graph_is_leaf(place) { return false }   // (a held view's len or cap is one only as it's emitted)
    d := graph_refers(pg, place)
    if graph_kind_of(pg, d) == .Param { return llvm_scalar(graph_type(pg, d)) }
    if d <= 0 || d > pg.end { return false }   // (not this code's)
    return s.held[d]
}

// --- in place -------------------------------------------------------------------

// Each functional update `x = f(x, …)` — f consumes that argument (builds its
// result from it alone, graph_consumed) and nothing else it's handed can
// reach x: x is both the argument and the result slot, and f skips its
// opening copy. The argument's place is the destination's, computed before it
// (a write's place comes first): the same operations, not done again.
@(private="file")
storage_in_place_updates :: proc(s: ^Storage) {
    pg := s.pg
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Call { continue }
            callee := graph_called(pg, op)
            if callee == nil { continue }
            k, consumes := graph_consumed(s.pc, callee).?
            u := s.user[graph_ix(s.pg, op)]
            if !consumes || u < 0 || graph_op_of(pg, u) != .Write { continue }
            uops := graph_operands(pg, u)
            dest := uops[0].op
            if uops[1].op != op || storage_direct(s, dest) || !storage_updates_in_place(s, op, k, dest) { continue }
            s.update[op] = true
            storage_alias_place(s, graph_operands(pg, graph_operands(pg, op)[k].op)[0].op, dest)
        }
    }
}

// Place a — the same storage as d, spelled the same (storage_same) — as d's
// operations, computed before it: each of a's, and its index's read, d's.
// (A variable, a leaf, computes nothing: not aliased.)
@(private="file")
storage_alias_place :: proc(s: ^Storage, a, d: Node_Id) {
    pg := s.pg
    if a == NO_NODE || d == NO_NODE || a == d || graph_is_leaf(a) || graph_is_leaf(d) || d > a { return }
    s.alias[a] = d
    ao, do_ := graph_operands(pg, a), graph_operands(pg, d)
    #partial switch graph_op_of(pg, a) {
    case .Field, .Deref, .Read:
        storage_alias_place(s, ao[0].op, do_[0].op)
    case .Index:
        storage_alias_place(s, ao[0].op, do_[0].op)
        if ai, di := ao[1].op, do_[1].op; ai != NO_NODE && di != NO_NODE && graph_op_of(pg, ai) == .Read && graph_op_of(pg, di) == .Read {
            storage_alias_place(s, ai, di)   // the index's read
        }
    }
}

// Whether a call's k-th argument is its destination's storage (a read of
// it, spelled the same) and each other argument can't reach that storage.
@(private="file")
storage_updates_in_place :: proc(s: ^Storage, call: Node_Id, k: int, dest: Node_Id) -> bool {
    pg := s.pg
    ops := graph_operands(pg, call)
    if k >= len(ops) || ops[k].op == NO_NODE || graph_op_of(pg, ops[k].op) != .Read { return false }
    if !storage_same(s, graph_operands(pg, ops[k].op)[0].op, dest) { return false }
    d := storage_where(s, dest)
    if d.root == NO_NODE { return false }
    for a, i in ops {
        if i != k && !storage_cannot_reach(s, a, d) { return false }
    }
    return true
}

// Whether two places are one storage, as spelled: the same variable, the same
// field of it, the same element (by the same constant, or variable's value),
// what the same pointer points at.
@(private="file")
storage_same :: proc(s: ^Storage, a, b: Node_Id) -> bool {
    pg := s.pg
    if a == NO_NODE || b == NO_NODE || graph_op_of(pg, a) != graph_op_of(pg, b) { return false }
    if graph_is_leaf(a) { return graph_refers(pg, a) == graph_refers(pg, b) }
    ao, bo := graph_operands(pg, a), graph_operands(pg, b)
    #partial switch graph_op_of(pg, a) {
    case .Field:
        return graph_name(pg, a) == graph_name(pg, b) && storage_same(s, ao[0].op, bo[0].op)
    case .Index:
        if !storage_same(s, ao[0].op, bo[0].op) { return false }
        ai, bi := ao[1].op, bo[1].op
        if ai == NO_NODE || bi == NO_NODE || graph_op_of(pg, ai) != graph_op_of(pg, bi) { return false }
        #partial switch graph_op_of(pg, ai) {
        case .Const:
            av, aok := graph_value(pg, ai)
            bv, bok := graph_value(pg, bi)
            return aok && bok && !av.is_float && !bv.is_float && av.int == bv.int
        case .Read:
            ap, bp := graph_leaf_decl(pg, graph_operands(pg, ai)[0].op), graph_leaf_decl(pg, graph_operands(pg, bi)[0].op)
            return ap != NO_NODE && ap == bp
        }
    case .Deref:
        return storage_same(s, ao[0].op, bo[0].op)   // the pointer's place (or its read)
    case .Read:
        return storage_same(s, ao[0].op, bo[0].op)
    }
    return false
}

// Whether an argument can't reach storage `d` while the callee runs: it holds
// no pointers, and it's a value in a register, or read from a different
// variable's own storage (a temporary included), no pointer on either path.
@(private="file")
storage_cannot_reach :: proc(s: ^Storage, a: Operand, d: Place_Where) -> bool {
    pg := s.pg
    if a.op == NO_NODE { return true }
    t := graph_type(pg, a.op)
    if !is_plain_data(t) { return false }
    if llvm_scalar(t) { return true }
    if graph_op_of(pg, a.op) != .Read { return false }
    w := storage_where(s, graph_operands(pg, a.op)[0].op)
    return w.root != NO_NODE && !d.via_ptr && !w.via_ptr && w.root != d.root
}

// --- views ----------------------------------------------------------------------

// Which locals are the place they're copied from, copying nothing: a struct
// or array bigger than two registers, written once — `x := place`, a loop's
// `for x in xs` — from a place, then only read (storage_view_only_read), and
// nothing that could change that place runs from the write to its last read
// (storage_view_unchanged). Such a local is that place, as a match arm's
// binding is its payload (s.bound); its write does nothing (s.done).
@(private="file")
storage_views :: proc(s: ^Storage) {
    pg := s.pg
    storage_view_addressed(s)
    for r, ri in s.runs[:s.own] {
        for w, at in graph_run(pg, int(r)) {
            if graph_op_of(pg, w) != .Write { continue }
            wops := graph_operands(pg, w)
            x, v := wops[0].op, wops[1].op
            if !graph_is_leaf(x) || v == NO_NODE || wops[1].out != 0 || graph_op_of(pg, v) != .Read { continue }
            d := graph_refers(pg, x)
            if d <= 0 || d > pg.end || graph_kind_of(pg, d) != .Local || pg.written[d] != .Explicit { continue }
            t := graph_type(pg, d)
            if !llvm_aggregate(t) || type_size(t) <= 16 { continue }
            if d in s.result || d in s.arena || d in s.bound || d in s.carved || s.held[d] { continue }
            if s.user[graph_ix(pg, v)] != w { continue }
            p := graph_operands(pg, v)[0].op
            if p == NO_NODE || graph_is_const(p) || p >= READ { continue }
            // (A temporary read into it: built there instead, storage_in_place.)
            if graph_is_leaf(p) {
                src := graph_refers(pg, p)
                if src <= 0 || src > pg.end || graph_kind_of(pg, src) == .Local && pg.written[src] == .Synthetic { continue }
            }
            if ot, _ := storage_view_object(s, storage_view_where(s, p)); ot == nil { continue }
            if !storage_view_only_read(s, d, w) || !storage_view_unchanged(s, d, ri, at, p) { continue }
            s.bound[d] = p
            s.done[w] = true
        }
    }
}

// Which locals some pointer or view may reach: a place rooted at one has its
// address taken, a view or a slice made of it, memory carved from it, or is
// handed to a fun that may keep it (storage_view_arg_kept). Any other local's
// own storage nothing reaches but its name.
@(private="file")
storage_view_addressed :: proc(s: ^Storage) {
    pg := s.pg
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            kind := graph_op_of(pg, op)
            for o, k in graph_operands(pg, op) {
                if o.op == NO_NODE || graph_is_const(o.op) || o.op >= READ { continue }
                pw := storage_view_where(s, o.op)
                if pw.via_ptr || pw.root <= 0 || pw.root > pg.end || graph_kind_of(pg, pw.root) != .Local { continue }
                #partial switch kind {
                case .Address, .Slice, .View, .Carve:
                    s.addressed[pw.root] = true
                case .Call, .Construct:
                    if (kind != .Construct || k > 0) && storage_view_arg_kept(s, op, k) { s.addressed[pw.root] = true }
                }
            }
        }
    }
}

// Where a place lives, as storage_where says — through the places locals
// view (s.bound) — read with care: a pointer's value read, a constant, no
// place (root unknown; past a pointer, its region still known).
@(private="file")
storage_view_where :: proc(s: ^Storage, p: Node_Id) -> Place_Where {
    pg := s.pg
    w := Place_Where{root = NO_NODE}
    for id := p; id != NO_NODE; {
        if graph_is_leaf(id) {
            if v, bound := s.bound[graph_refers(pg, id)]; bound {
                id = v
                continue
            }
            w.root = graph_refers(pg, id)
            return w
        }
        if id >= CONST || graph_kind_of(pg, id) != .Op { return w }
        ops := graph_operands(pg, id)
        #partial switch graph_op_of(pg, id) {
        case .Deref:
            if pg.written[id] != .Implied { w.explicit = true }
            if !w.via_ptr { w.via_ptr, w.region = true, graph_type(pg, id) }
            id = ops[0].op
        case .Index:
            if _, is_slice := distinct_base(graph_type(pg, ops[0].op)).(^Type_Slice); is_slice && !w.via_ptr {
                w.via_ptr, w.region = true, graph_type(pg, id)
            }
            id = ops[0].op
        case .Field, .Swizzle, .Variant, .Slice:
            id = ops[0].op
        case:
            return w
        }
    }
    return w
}

// The object a place lives in and whether it is a local's own storage: past
// a pointer, the region it lands in; a param's, the caller's object of its
// type; a local's, its variable. nil: not known (a carved local is bytes
// somewhere, the result slot the caller's).
@(private="file")
storage_view_object :: proc(s: ^Storage, w: Place_Where) -> (t: Type, own: bool) {
    pg := s.pg
    if w.explicit { return nil, false }
    if w.via_ptr { return w.region, false }
    r := w.root
    if r <= 0 || r > pg.end || r in s.carved || r in s.result { return nil, false }
    #partial switch graph_kind_of(pg, r) {
    case .Local: return graph_type(pg, r), true
    case .Param: return graph_type(pg, r), false
    }
    return nil, false
}

// Whether writing place x may change place p: one variable's own storage
// spelled apart (places_disjoint) never; two variables' own storage only if
// they're one; else by the objects they live in — one can be inside the
// other only if its type can hold the other's, and nothing is inside a
// local's own storage but what its type holds.
@(private="file")
storage_view_overlaps :: proc(s: ^Storage, p, x: Node_Id) -> bool {
    if places_disjoint(s.pg, s.bound, p, x) { return false }
    pw, xw := storage_view_where(s, p), storage_view_where(s, x)
    pt, pown := storage_view_object(s, pw)
    xt, xown := storage_view_object(s, xw)
    if pt == nil || xt == nil { return true }
    switch {
    case pown && xown: return pw.root == xw.root
    case pown:         return pw.root in s.addressed && type_can_contain(pt, xt)
    case xown:         return xw.root in s.addressed && type_can_contain(xt, pt)
    }
    return type_can_contain(pt, xt) || type_can_contain(xt, pt)
}

// Whether local d, past its write w, is only read: every place rooted at it
// read, its parts' places read, a pointer in it followed — a whole value
// read copied (written elsewhere, returned, compared, printed) or passed to
// a fun whose result can't hold it. Never written, its address never taken,
// no view of it made.
@(private="file")
storage_view_only_read :: proc(s: ^Storage, d, w: Node_Id) -> bool {
    pg := s.pg
    rooted :: proc(s: ^Storage, o, d: Node_Id) -> bool {
        if o == NO_NODE || graph_is_const(o) || o >= READ { return false }
        pw := storage_view_where(s, o)
        return pw.root == d && !pw.via_ptr
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            kind := graph_op_of(pg, op)
            for o, k in graph_operands(pg, op) {
                if !rooted(s, o.op, d) || op == w && k == 0 { continue }
                #partial switch kind {
                case .Field, .Index, .Swizzle, .Variant, .Deref:
                    if k == 0 { continue }   // (a part of it, or a pointer in it: its own uses met in turn)
                case .Switch, .Compare, .Print, .Assert, .Return:
                    continue   // (read where it is)
                case .Read:
                    if storage_view_read_kept(s, op) { return false }
                    continue
                case .Call, .Construct:
                    if storage_view_arg_kept(s, op, k) { return false }
                    continue
                }
                return false
            }
        }
    }
    return true
}

// Whether a read of a viewed local (or a part) may outlive the read: a
// number is a value; a struct or array read is its storage, copied by a
// write, a return, a compare, a print — or passed to a fun that may keep it.
@(private="file")
storage_view_read_kept :: proc(s: ^Storage, read: Node_Id) -> bool {
    pg := s.pg
    if llvm_scalar(graph_type(pg, read)) { return false }
    u := s.user[graph_ix(pg, read)]
    if u == -1 { return false }
    if u < 0 { return true }
    #partial switch graph_op_of(pg, u) {
    case .Write:
        return graph_operands(pg, u)[0].op == read   // (a value written, not where)
    case .Return, .Compare, .Print, .Assert:
        return false
    case .Call, .Construct:
        for o, k in graph_operands(pg, u) {
            if o.op == read && storage_view_arg_kept(s, u, k) { return true }
        }
        return false
    }
    return true
}

// Whether a call's k-th operand, a viewed local's storage, may be kept past
// it: a fun with no code of its own (foreign, an intrinsic), one through a
// fun value, or one whose result may hold that param.
@(private="file")
storage_view_arg_kept :: proc(s: ^Storage, op: Node_Id, k: int) -> bool {
    pg := s.pg
    callee := graph_called(pg, op)
    if callee == nil { return true }
    if _, src := callee.origin.(Origin_Source); !src { return true }
    first := 1 if graph_op_of(pg, op) == .Construct else 0
    i := k - first
    sum := reach_summary(s.pc, s.summaries, callee)
    return i < 0 || i >= len(sum.returned) || sum.returned[i]
}

// Whether nothing that could change place p runs while local d views it:
// from its write (`wat` in run `wri`) to its last read — each operation after
// the write in its run, and each in a run the write's run reaches, not
// through it again, that reaches one of d's reads (storage_view_may_change).
// A read in a defer's block: not known when it runs.
@(private="file")
storage_view_unchanged :: proc(s: ^Storage, d: Node_Id, wri, wat: int, p: Node_Id) -> bool {
    pg := s.pg
    n := s.own
    at := make(map[i32]int, n, context.temp_allocator)
    for r, i in s.runs[:n] { at[r] = i }
    succ := make([][dynamic]int, n, context.temp_allocator)
    pred := make([][dynamic]int, n, context.temp_allocator)
    uses := make([]bool, n, context.temp_allocator)
    for r, i in s.runs {
        ops := graph_run(pg, int(r))
        for op in ops {
            for o in graph_operands(pg, op) {
                if o.op == NO_NODE || graph_is_const(o.op) || o.op >= READ { continue }
                if pw := storage_view_where(s, o.op); pw.root != d || pw.via_ptr { continue }
                if i >= n { return false }
                uses[i] = true
            }
        }
        if i >= n || len(ops) == 0 { continue }
        for edge in graph_out(pg, ops[len(ops) - 1]) {
            if edge.to == NO_NODE { return false }
            if j, ok := at[graph_run_starting(pg, edge.to)]; ok {
                append(&succ[i], j)
                append(&pred[j], i)
            }
        }
    }
    walk :: proc(next: [][dynamic]int, from: []int, skip: int, seen: []bool) {
        todo := make([dynamic]int, context.temp_allocator)
        for f in from { if f != skip && !seen[f] { seen[f] = true; append(&todo, f) } }
        for len(todo) > 0 {
            i := pop(&todo)
            for j in next[i] { if j != skip && !seen[j] { seen[j] = true; append(&todo, j) } }
        }
    }
    after := make([]bool, n, context.temp_allocator)    // reached from the write's run
    before := make([]bool, n, context.temp_allocator)   // reaching a read
    walk(succ, succ[wri][:], wri, after)
    starts := make([dynamic]int, context.temp_allocator)
    for u, i in uses { if u { append(&starts, i) } }
    walk(pred, starts[:], wri, before)
    for op in graph_run(pg, int(s.runs[wri]))[wat + 1:] {
        if storage_view_may_change(s, op, p) { return false }
    }
    for i in 0 ..< n {
        if i == wri || !after[i] || !before[i] { continue }
        for op in graph_run(pg, int(s.runs[i])) {
            if storage_view_may_change(s, op, p) { return false }
        }
    }
    return true
}

// Whether an operation may change place p: a write whose place may overlap
// it, a call handed storage it may write through that may hold it, a
// defer's block, an arena reset, a `let` carving memory.
@(private="file")
storage_view_may_change :: proc(s: ^Storage, op: Node_Id, p: Node_Id) -> bool {
    pg := s.pg
    if op >= CONST { return false }   // (a read)
    #partial switch graph_op_of(pg, op) {
    case .Write, .Zero, .Fill, .Byte_Read:
        return storage_view_overlaps(s, p, graph_operands(pg, op)[0].op)
    case .Construct:
        return storage_view_overlaps(s, p, graph_operands(pg, op)[0].op) || storage_view_call_writes(s, op, p, 1)
    case .Call:
        return storage_view_call_writes(s, op, p, 0)
    case .Carve, .Run_Defer, .Arena_Reset:
        return true
    }
    return false
}

// Whether a call may write p through what it's handed: a param it reaches
// through that is a pointer (a param of a fun with no code: any handed
// storage) — the place `&place` hands over, or the object a pointer's value
// points at, plain data apart from p. A call through a fun value: anything.
@(private="file")
storage_view_call_writes :: proc(s: ^Storage, op: Node_Id, p: Node_Id, first: int) -> bool {
    pg := s.pg
    callee := graph_called(pg, op)
    if callee == nil { return true }
    _, src := callee.origin.(Origin_Source)
    sum := reach_summary(s.pc, s.summaries, callee)
    ops := graph_operands(pg, op)[first:]
    if len(ops) != len(sum.reaches) || len(ops) != len(callee.params) { return true }
    for o, k in ops {
        if !sum.reaches[k] || o.op == NO_NODE || graph_is_const(o.op) { continue }
        pt := fn_param(callee, k).type_
        _, is_ptr := pt.(^Type_Ptr)
        // (A value, or an immutable slice: read only — unless a pointer in it
        // reaches out, `h.p.a = 55` through a Holder handed by value.)
        if src && !is_ptr && !holds_pointer(pt) { continue }
        a := o.op
        for a < CONST && graph_op_of(pg, a) == .Cast { a = graph_operands(pg, a)[0].op }
        if _, is_text := graph_const_text(pg, a); is_text { continue }
        // (Storage handed over: `&place`'s place, an aggregate's own — a
        // pointer variable handed on is its value.)
        place := NO_NODE
        #partial switch graph_op_of(pg, a) {
        case .Address:
            place = graph_operands(pg, a)[0].op
        case .Var, .Field, .Index, .Deref, .Variant:
            if _, is_ptr := distinct_base(graph_type(pg, a)).(^Type_Ptr); !is_ptr { place = a }
        }
        if place != NO_NODE {
            if !is_plain_data(graph_type(pg, place)) || storage_view_overlaps(s, p, place) { return true }
            continue
        }
        // (A pointer's value: the callee reaches the object it points at.)
        ptr, holds := distinct_base(graph_type(pg, a)).(^Type_Ptr)
        if !holds || !is_plain_data(ptr.elem) { return true }
        pw := storage_view_where(s, p)
        pt_, pown := storage_view_object(s, pw)
        if pt_ == nil { return true }
        if pown && pw.root not_in s.addressed { continue }   // (no pointer reaches it)
        if type_can_contain(pt_, ptr.elem) || type_can_contain(ptr.elem, pt_) { return true }
    }
    return false
}

// Which locals are declared from a `let` take: such a local is the carved
// memory itself — its declaration binds it, copying nothing.
@(private="file")
storage_carved :: proc(s: ^Storage) {
    pg := s.pg
    for r in s.runs {
        for w in graph_run(pg, int(r)) {
            if graph_op_of(pg, w) != .Write { continue }
            ops := graph_operands(pg, w)
            c, dest := ops[1].op, ops[0].op
            if c == NO_NODE || graph_op_of(pg, c) != .Carve || graph_name(pg, c) != "let" || !graph_is_leaf(dest) { continue }
            if d := graph_refers(pg, dest); graph_kind_of(pg, d) == .Local && graph_stmt(pg, w).kind == .Decl { s.carved[d] = c }
        }
    }
}

// What a fun returning aggregates builds in its caller's slots rather than in
// storage of its own: the local every return returns (NRVO), and a
// temporary whose one read is a return (a literal or construction returned).
// With several results, each aggregate one's slot. (A caller hands over a
// fresh slot for each: a variable its declaration makes, or a temporary —
// storage_declared_at — so nothing the fun is handed is in it.)
@(private="file")
storage_result_slot :: proc(s: ^Storage, rets: []Type) {
    if s.one_slot {
        storage_result_slot_at(s, 0, 1, named = true)
        return
    }
    for rt, i in rets {
        if !llvm_aggregate(rt) { continue }
        storage_result_slot_at(s, i, len(rets), named = true)
    }
}

// Local d built in the caller's k-th slot: no storage of its own — a big
// one's arena alloc (lowering's) does nothing.
@(private="file")
storage_in_slot :: proc(s: ^Storage, d: Node_Id, k: int) {
    pg := s.pg
    s.result[d] = k
    if d not_in s.arena { return }
    delete_key(&s.arena, d)
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) == .Arena_Alloc && graph_refers(pg, graph_operands(pg, op)[0].op) == d { s.done[op] = true }
        }
    }
}

// The k-th result's slot, of n: what lives there (a `?`'s return, of zeros,
// returns no local).
@(private="file")
storage_result_slot_at :: proc(s: ^Storage, k, n: int, named: bool) {
    pg := s.pg
    returned := NO_NODE   // the local every return returns, so far
    every := true
    for r in s.runs[:s.own] {   // (a defer block's return goes back where it ran)
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Return || graph_written(pg, op) == .Implied { continue }
            ops := graph_operands(pg, op)
            // (A failure alone, `return Too_Many_Chars`: zeros too.)
            if len(ops) == n && ops[k].op != NO_NODE && graph_is_const(ops[k].op) && graph_written(pg, ops[k].op) == .Implied && graph_name(pg, ops[k].op) == "zero" { continue }
            v := NO_NODE
            if len(ops) == n && ops[k].op != NO_NODE && graph_op_of(pg, ops[k].op) == .Read {
                if d := graph_leaf_decl(pg, graph_operands(pg, ops[k].op)[0].op); d >= 0 && graph_kind_of(pg, d) == .Local { v = d }
            }
            // (The carved memory, or the place a local views — storage_views:
            // copied out.)
            if v in s.carved || v in s.bound { v, every = NO_NODE, false }
            if v != NO_NODE && graph_written(pg, v) == .Synthetic {
                // (Not an `if` expression's, written by its arms: its own.)
                if storage_reads(s, v) == 1 && storage_written_only_in(s, v, r) { storage_in_slot(s, v, k) }
                v = NO_NODE   // a temporary is no named local
            }
            switch {
            case v == NO_NODE:                        every = false
            case returned == NO_NODE:                 returned = v
            case returned != v:                       every = false
            }
        }
    }
    if named && every && returned != NO_NODE { storage_in_slot(s, returned, k) }
}

// Whether a variable lives in the fun's result slot — the one slot, not one
// of several: Self and its fields in a constructor, a named result, the local
// every return returns; once the temporaries built in place are known, one
// built there.
@(private="file")
storage_in_result :: proc(s: ^Storage, d: Node_Id) -> bool {
    if s.ctor && (d == 0 || (graph_kind_of(s.pg, d) == .Field && s.pg.parent[d] == 0)) { return true }
    if d <= 0 || d > s.pg.end { return false }
    if s.one_slot && d in s.result { return true }
    at, built := s.in_place[d]
    return s.placed && built && storage_is_slot(s, at)
}

// Whether a place is the result slot itself, not a part of it: a variable
// there, a union's variant of one, a temporary built in one, a match arm's
// binding of one.
@(private="file")
storage_is_slot :: proc(s: ^Storage, p: Node_Id) -> bool {
    pg := s.pg
    at := p
    for {
        #partial switch graph_op_of(pg, at) {
        case .Variant:
            at = graph_operands(pg, at)[0].op
            continue
        case .Var:
            d := graph_refers(pg, at)
            if s.ctor && d == 0 { return true }
            if d <= 0 || d > pg.end || graph_kind_of(pg, d) == .Param || graph_kind_of(pg, d) == .Field { return false }
            if s.one_slot && d in s.result { return true }
            if d in s.arena { return false }
            if x, built := s.in_place[d]; built { at = x; continue }
            if v, bound := s.bound[d]; bound { at = v; continue }
        }
        return false
    }
}

// Whether every write to variable v is in run r.
@(private="file")
storage_written_only_in :: proc(s: ^Storage, v: Node_Id, r: i32) -> bool {
    pg := s.pg
    for q in s.runs {
        if q == r { continue }
        for op in graph_run(pg, int(q)) {
            #partial switch graph_op_of(pg, op) {
            case .Zero, .Construct, .Fill, .Write, .Byte_Read:
                if storage_where(s, graph_operands(pg, op)[0].op).root == v { return false }
            }
        }
    }
    return true
}

// Which temporaries are built in the storage they are then written to. The
// graph builds a literal or construction assigned to existing storage whole,
// in a temporary — it may read what it replaces; it is built in place when,
// from its first write on, nothing it reads can be that storage
// (storage_overlaps), and — a construction — its callee is handed none of the
// caller's storage (the rule for calls). One built before a `?`, `x =
// Holder(1)?`, is built in place too: a failure leaves x part built, as a
// failing constructor leaves what it was building.
@(private="file")
storage_in_place :: proc(s: ^Storage) {
    pg := s.pg
    tries := storage_tries(s)
    for r in s.runs {
        ops := graph_run(pg, int(r))
        for w, at in ops {
            if graph_op_of(pg, w) != .Write { continue }
            wops := graph_operands(pg, w)
            x, v := wops[0].op, wops[1].op
            if v == NO_NODE || wops[1].out != 0 || graph_op_of(pg, v) != .Read || !llvm_aggregate(graph_type(pg, v)) { continue }
            tv := graph_operands(pg, v)[0].op
            if !graph_is_leaf(tv) || storage_direct(s, x) { continue }
            if graph_op_of(pg, x) == .Swizzle { continue }   // components, not one array's storage
            if graph_op_of(pg, x) == .Slice { continue }     // a run of elements the value's are copied into, no storage of one type
            t := graph_refers(pg, tv)
            if t <= 0 || t > pg.end || graph_kind_of(pg, t) != .Local || graph_written(pg, t) != .Synthetic { continue }
            if t in s.result || storage_reads(s, t) != 1 { continue }
            before := ops[:at]
            if _, tried := tries[r]; tried {
                // (The runs each `?` went on from, in order, then this one's.)
                back := make([dynamic]i32, context.temp_allocator)
                for q, more := tries[r]; more; q, more = tries[q] { append(&back, q) }
                all := make([dynamic]Node_Id, context.temp_allocator)
                #reverse for q in back { append(&all, ..graph_run(pg, int(q))) }
                append(&all, ..ops[:at])
                before = all[:]
            }
            if storage_builds_alone(s, before, t, x) { s.in_place[t] = x }
        }
    }
}

// Whether a run is a `?`'s failure: it returns the err, implied.
@(private="file")
storage_fails :: proc(s: ^Storage, r: i32) -> bool {
    ops := graph_run(s.pg, int(r))
    if len(ops) == 0 { return false }
    last := ops[len(ops) - 1]
    return graph_op_of(s.pg, last) == .Return && graph_written(s.pg, last) == .Implied
}

// The run each `?` goes on from, by the run it goes on in: the one ending in
// the `?`'s branch, whose other way is its failure.
@(private="file")
storage_tries :: proc(s: ^Storage) -> map[i32]i32 {
    pg := s.pg
    tries := make(map[i32]i32, 8, context.temp_allocator)
    for r in s.runs[:s.own] {
        ops := graph_run(pg, int(r))
        if len(ops) == 0 { continue }
        last := ops[len(ops) - 1]
        if graph_op_of(pg, last) != .Branch || graph_written(pg, last) != .Implied { continue }
        on, fails, ways := i32(-1), false, 0
        for edge in graph_out(pg, last) {
            to := i32(graph_run_starting(pg, edge.to))
            ways += 1
            if storage_fails(s, to) { fails = true } else { on = to }
        }
        if ways == 2 && fails && on >= 0 { tries[on] = r }
    }
    return tries
}

// Whether temporary t, built in `before` (the operations of one run ahead of
// the write that reads it), can be built at place x instead.
@(private="file")
storage_builds_alone :: proc(s: ^Storage, before: []Node_Id, t, x: Node_Id) -> bool {
    pg := s.pg
    // All of t's code is here, and x is known before t's first write.
    uses, here := 0, 0
    names :: proc(pg: ^Program_Graph, op, t: Node_Id) -> (n: int) {   // (its leaves naming t)
        for o in graph_operands(pg, op) { if graph_leaf_decl(pg, o.op) == t { n += 1 } }
        return
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) { uses += names(pg, op, t) }
    }
    first := -1
    for op, i in before {
        here += names(pg, op, t)
        #partial switch graph_op_of(pg, op) {
        case .Zero, .Construct, .Fill, .Write:
            if first < 0 && storage_where(s, graph_operands(pg, op)[0].op).root == t { first = i }
        }
    }
    if uses != here || first < 0 { return false }
    if !graph_is_leaf(x) {
        known := false
        for op in before[:first] { if op == x { known = true } }
        if !known { return false }
    }
    // From its first write on, nothing read (or pointed at) is x's storage —
    // but a number read from it with nothing written anywhere else first (no
    // call, no other write: `x = X{n = x.n + 5}`) is read before the first
    // write instead, as the temporary would have read it (the backend reads it
    // ahead: hoist).
    hoists := make([dynamic]Node_Id, context.temp_allocator)
    clean := true   // (nothing but t's own writes and pure operations so far)
    for op in before[first:] {
        ops := graph_operands(pg, op)
        #partial switch graph_op_of(pg, op) {
        case .Read, .Address:
            if storage_where(s, ops[0].op).root == t { continue }
            if graph_op_of(pg, op) == .Read && storage_direct(s, ops[0].op) { continue }   // a value, in no memory
            if storage_overlaps(s, ops[0].op, x) {
                if graph_op_of(pg, op) == .Read && clean && llvm_scalar(graph_type(pg, op)) && storage_ahead_able(s, ops[0].op) {
                    append(&hoists, op)
                    continue
                }
                return false
            }
        case .Construct:
            // t's own construction, handed arguments (handed no storage, its
            // constructor writes nothing but t: still clean). Another's: not.
            if graph_leaf_decl(pg, ops[0].op) != t { clean = false; continue }
            if len(ops) == 1 { continue }
            callee := graph_called(pg, op)
            if callee == nil { return false }
            if storage_passes_storage(callee) {
                reaches, mine := storage_call_reaches(s, op, x, first = 1)
                if mine != NO_NODE { storage_reads_its_dest(pg, op, mine, x, callee) }
                if reaches { return false }
            }
            if _, consumes := graph_consumed(s.pc, callee).?; consumes { return false }
        case .Write, .Zero, .Fill:
            if storage_where(s, ops[0].op).root != t { clean = false }
        case .Field, .Variant, .Index, .Deref, .Const, .Arith, .Compare, .Unary, .Cast, .Swizzle, .Global:
        case:
            clean = false
        }
    }
    if len(hoists) > 0 {
        if before[first] not_in s.hoist { s.hoist[before[first]] = make([dynamic]Node_Id, context.temp_allocator) }
        append(&s.hoist[before[first]], ..hoists[:])
    }
    return true
}

// Whether place p's address can be had ahead of its turn: a variable, a field
// or variant of one such, a constant element, what a pointer variable points
// at.
@(private="file")
storage_ahead_able :: proc(s: ^Storage, p: Node_Id) -> bool {
    pg := s.pg
    if graph_is_leaf(p) { return true }
    ops := graph_operands(pg, p)
    #partial switch graph_op_of(pg, p) {
    case .Field, .Variant, .Deref: return storage_ahead_able(s, ops[0].op)
    case .Index: return graph_is_const(ops[1].op) && storage_ahead_able(s, ops[0].op)
    }
    return false
}

// --- places ---------------------------------------------------------------------

// Where a place lives: the variable at the root of its path; whether the
// path crosses a pointer (then the root says nothing about where it is), and
// once it does, `region`, the type of the object the last crossing lands in —
// else the root variable's type; whether a pointer is dereferenced as written.
Place_Where :: struct {
    root:     Node_Id,
    via_ptr:  bool,
    region:   Type,
    explicit: bool,
}

storage_where :: proc(s: ^Storage, p: Node_Id) -> Place_Where {
    pg := s.pg
    w := Place_Where{root = NO_NODE}
    for id := p; id != NO_NODE; {
        if graph_is_leaf(id) {
            // A match arm's binding is its scrutinee's payload: where that is.
            if v, bound := s.bound[graph_refers(pg, id)]; bound {
                id = v
                continue
            }
            w.root = graph_refers(pg, id)
            return w
        }
        ops := graph_operands(pg, id)
        #partial switch pg.op[id] {
        case .Deref:
            if pg.written[id] != .Implied { w.explicit = true }
            if !w.via_ptr { w.via_ptr, w.region = true, graph_type(pg, id) }
            id = ops[0].op
        case .Index:
            if _, is_slice := distinct_base(graph_type(pg, ops[0].op)).(^Type_Slice); is_slice && !w.via_ptr {
                w.via_ptr, w.region = true, graph_type(pg, id)
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

// Whether reading place `read` can observe place `dest`. Yes when both are
// one variable's own storage, when what is read holds pointers, or when
// either is unknown. Otherwise it comes down to where each can live: a
// variable's own storage is an object of its type, one through a pointer an
// object of the pointee's; two overlap only if one's object type can hold
// the other's, and a local's own storage is never
// inside anything — but the caller's (a param, the result slot) can be. And
// the result slot never overlaps what a param reaches: a caller hands over a
// fresh slot whenever an argument carries storage.
@(private="file")
storage_overlaps :: proc(s: ^Storage, read, dest: Node_Id) -> bool {
    pg := s.pg
    if graph_op_of(pg, read) == .Global { return false }   // a constant table is never written
    r, d := storage_where(s, read), storage_where(s, dest)
    if r.root == NO_NODE || d.root == NO_NODE || r.explicit { return true }
    if places_disjoint(pg, s.bound, read, dest) { return false }
    if !d.via_ptr && storage_in_result(s, d.root) && graph_kind_of(pg, r.root) == .Param { return false }
    if !r.via_ptr && !d.via_ptr && r.root == d.root { return true }
    if !is_plain_data(graph_type(pg, read)) { return true }
    if !r.via_ptr && !d.via_ptr { return false }   // two variables' own storage
    read_own := !r.via_ptr && !storage_in_result(s, r.root) && graph_kind_of(pg, r.root) != .Param
    dest_own := !d.via_ptr && !storage_in_result(s, d.root)
    if r.region == nil || d.region == nil { return true }
    return (!read_own && type_can_contain(d.region, r.region)) || (!dest_own && type_can_contain(r.region, d.region))
}

// --- what a call can reach ---------------------------------------------------------
//
// A call's struct result is built where it goes only if the call can't reach
// that place while it runs: it would read, or write over, what it has already
// written there. A call reaches what it's passed as storage (a pointer; an
// aggregate, passed by its address) where its code — or a fun it calls —
// reads or writes through it. Nothing else: no code names a place outside it
// but through what it's passed.

// Whether a call may reach `dest`, the place its result goes, while it runs:
// through an argument passed as storage its callee reaches through — unless
// the argument is constant text, which no place being built can be, or the
// storage it hands over is plain data apart from dest (storage_overlaps): what
// the callee reaches is that storage, and no pointer out of it.
// (`mine`: an argument that is `&place`, place surely overlapping dest —
// it would read what its result is overwriting: storage_reads_its_dest.)
@(private="file")
storage_call_reaches :: proc(s: ^Storage, op: Node_Id, dest: Node_Id, first := 0) -> (reaches: bool, mine: Node_Id) {
    pg := s.pg
    mine = NO_NODE
    callee := graph_called(pg, op)
    if callee == nil { return true, mine }   // (through a function value: unknown)
    sum := reach_summary(s.pc, s.summaries, callee)
    ops := graph_operands(pg, op)[first:]
    if len(ops) != len(sum.reaches) { return true, mine }
    for o, k in ops {
        if !sum.reaches[k] { continue }
        at := o.op
        for graph_op_of(pg, at) == .Cast { at = graph_operands(pg, at)[0].op }   // (text as a slice: over it)
        if _, is_text := graph_const_text(pg, at); is_text { continue }
        // (The storage handed over: `&place`'s place, an aggregate's own.)
        place := NO_NODE
        #partial switch graph_op_of(pg, at) {
        case .Address, .Read: place = graph_operands(pg, at)[0].op
        case .Var, .Field, .Index, .Deref, .Variant: place = at
        }
        if place != NO_NODE && is_plain_data(graph_type(pg, place)) && !storage_overlaps(s, place, dest) { continue }
        if graph_op_of(pg, at) == .Address && mine == NO_NODE && places_contain(pg, s.bound, place, dest) { mine = at }
        reaches = true
    }
    return
}

// Building a result where it goes while handed that place — `v = swap(&v)`,
// `g.big = make(&g)`: what it reads is what it overwrites. An error, not a
// hidden copy: the result built under a name of its own first, then
// assigned, says so.
storage_reads_its_dest :: proc(pg: ^Program_Graph, op, arg, dest: Node_Id, callee: ^Type_Scope) -> ! {
    name := scope_display_name(callee)
    held := graph_place_name(pg, Operand{op = graph_operands(pg, arg)[0].op})
    into := graph_place_name(pg, Operand{op = dest})
    storage_fatal(graph_origin(pg, op), TYPE_RESULT_READS_DEST, name, held, into, name, into)
}

// Whether a call hands its callee storage: a param passed by address.
storage_passes_storage :: proc(callee: ^Type_Scope) -> bool {
    for _, i in callee.params {
        p := fn_param(callee, i)
        if ir, _ := llvm_param_type(p.type_); ir == IR_PTR { return true }
    }
    return false
}

// --- swaps ----------------------------------------------------------------------

// A swap — `a, b = b, a`: two big places of one type, each one's held value
// read straight from the other — done in place, a piece at a time through a
// small buffer, not held whole: its held locals take no storage, their holds
// and the second put are done by it, the first put swaps. Only when the two
// are one place or surely apart (places_disjoint): two that may partly
// overlap are held as any parallel assignment's values are.
@(private="file")
storage_swaps :: proc(s: ^Storage) {
    pg := s.pg
    // (Each parallel local's writes; and the puts, in order: writes of one's
    // value into its target.)
    Put :: struct { w, target, local, read, var_op: Node_Id }
    holds := make(map[Node_Id][dynamic]Node_Id, allocator = context.temp_allocator)
    puts := make([dynamic]Put, context.temp_allocator)
    is_held :: proc(pg: ^Program_Graph, d: Node_Id) -> bool {
        return d > 0 && d <= pg.end && graph_kind_of(pg, d) == .Local && graph_written(pg, d) == .Synthetic && graph_name(pg, d) == "parallel"
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Write { continue }
            ops := graph_operands(pg, op)
            dest, v := ops[0].op, ops[1].op
            if graph_is_leaf(dest) && is_held(pg, graph_refers(pg, dest)) {
                d := graph_refers(pg, dest)
                if d not_in holds { holds[d] = make([dynamic]Node_Id, context.temp_allocator) }
                append(&holds[d], op)
                continue
            }
            if v != NO_NODE && graph_op_of(pg, v) == .Read {
                if src := graph_operands(pg, v)[0].op; graph_is_leaf(src) && is_held(pg, graph_refers(pg, src)) {
                    append(&puts, Put{op, dest, graph_refers(pg, src), v, src})
                }
            }
        }
    }
    // (A local's one hold — a read of a place: that place.)
    held_from :: proc(s: ^Storage, holds: map[Node_Id][dynamic]Node_Id, d: Node_Id) -> (w, read, src: Node_Id, ok: bool) {
        pg := s.pg
        ws, has := holds[d]
        if !has || len(ws) != 1 || storage_reads(s, d) != 1 { return }
        w = ws[0]
        read = graph_operands(pg, w)[1].op
        if read == NO_NODE || graph_op_of(pg, read) != .Read { return }
        return w, read, graph_operands(pg, read)[0].op, true
    }
    for i := 0; i + 1 < len(puts); i += 1 {
        p, q := puts[i], puts[i + 1]
        t := graph_type(pg, p.local)
        if !routes_to_arena(t) || !llvm_same_type(t, graph_type(pg, q.local)) || p.local == q.local { continue }
        pw, pr, ps, pok := held_from(s, holds, p.local)
        qw, qr, qs, qok := held_from(s, holds, q.local)
        if !pok || !qok { continue }
        if !places_same(pg, s.bound, ps, q.target) || !places_same(pg, s.bound, qs, p.target) { continue }
        if !places_same(pg, s.bound, p.target, q.target) && !places_disjoint(pg, s.bound, p.target, q.target) { continue }
        s.swaps[p.w] = {p.target, q.target}
        s.swapped[p.local], s.swapped[q.local] = true, true
        for skip in ([]Node_Id{pw, pr, graph_operands(pg, pw)[0].op, qw, qr, graph_operands(pg, qw)[0].op,
                               p.read, p.var_op, q.w, q.read, q.var_op}) {
            s.done[skip] = true   // (done: the swap is all of it)
        }
        i += 1
    }
}

// --- the arena ------------------------------------------------------------------

// The big temporaries: each big local that has no arena alloc of its own and
// no other storage — built in place, carved, a payload, swapped, the
// caller's slot. A named one always has its alloc (lowering's); a temporary
// is the fun's, on the arena from its entry until it returns, as a call's
// big result with nowhere to go is (storage_calls).
@(private="file")
storage_big_temps :: proc(s: ^Storage) {
    pg := s.pg
    for id := Node_Id(1); id <= pg.end; id += 1 {
        #partial switch pg.kind[id] {
        case .Fun, .Struct: id = graph_last(pg, id); continue   // (another scope's)
        }
        if pg.kind[id] != .Local || !routes_to_arena(graph_type(pg, id)) || id in s.arena || id in s.in_place || id in s.carved || id in s.bound || id in s.swapped { continue }
        if id in s.result { continue }
        if pg.written[id] != .Synthetic {
            s.stop = id
            return
        }
        append(&s.temps, Storage_Temp{{id, 0}, graph_type(pg, id)})
    }
}

// A call's aggregate result built in a temporary of its own: a big one, one
// of the fun's big temporaries (storage_big_temps).
@(private="file")
storage_held :: proc(s: ^Storage, o: Operand, t: Type) {
    if routes_to_arena(t) { append(&s.temps, Storage_Temp{o, t}) }
}

// --- calls ------------------------------------------------------------------------

// Where each call to a Mara fun with several results builds each aggregate
// one: the variable a declaration takes it into (storage_declared_at), else
// a temporary. And where one with one aggregate result builds it: the
// fun's result slot when it's returned; the place it's written to when that
// place is fresh — a declaration's, a temporary's — or the functional update
// `x = f(x, …)`'s x, or one the call can't reach while it runs
// (storage_call_reaches) — and that place's address can be had when the call
// is made; else a temporary of its own. A call handed `&place` whose result
// goes over that place is an error (storage_reads_its_dest).
@(private="file")
storage_calls :: proc(s: ^Storage, sret: Type) {
    pg := s.pg
    s.placed = true
    s.pos = make([]i32, graph_ix_count(pg))
    for &p in s.pos { p = -1 }
    n := i32(0)
    for r in s.runs[:s.own] {
        for op in graph_run(pg, int(r)) {
            s.pos[graph_ix(s.pg, op)] = n
            n += 1
        }
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if graph_op_of(pg, op) != .Call { continue }
            callee := graph_called(pg, op)
            args := len(graph_operands(pg, op))
            placed := true
            if callee == nil {   // (through a function value, its first operand: by its type's signature)
                callee = graph_signature(pg, op)
                args -= 1
                if callee == nil { continue }
            } else {
                // (A C fun's results, and what isn't a fun's: each aggregate
                // one in a temporary.)
                _, src := callee.origin.(Origin_Source)
                placed = callee.kind == .Fun && src
            }
            placed = placed && args == len(callee.params)
            if fn_result_count(callee) > 1 {
                assigned := false
                for i in 0 ..< fn_result_count(callee) {
                    rt := fn_result(callee, i)
                    if !llvm_aggregate(rt) { continue }
                    o := Operand{op, i32(i)}
                    d := NO_NODE
                    if placed { d = storage_declared_at(s, o) }
                    // (One at most into a place that was there: two could overlap.)
                    if placed && d == NO_NODE && !assigned {
                        d = storage_assigned_at(s, op, o, rt)
                        assigned = d != NO_NODE
                    }
                    if d != NO_NODE {
                        s.out_at[o] = d
                    } else {
                        storage_held(s, o, rt)
                    }
                }
                continue
            }
            if fn_result_count(callee) != 1 { continue }
            result := fn_result(callee, 0)
            if llvm_scalar(result) || !llvm_aggregate(result) { continue }
            if at := storage_call_place(s, op, callee, sret) if placed else .Temporary; at != .Temporary {
                s.calls[op] = at
            } else {
                storage_held(s, {op, 0}, result)
            }
        }
    }
}

@(private="file")
storage_call_place :: proc(s: ^Storage, op: Node_Id, callee: ^Type_Scope, sret: Type) -> Call_Place {
    pg := s.pg
    u := s.user[graph_ix(s.pg, op)]
    if u < 0 { return .Temporary }
    uops := graph_operands(pg, u)
    #partial switch graph_op_of(pg, u) {
    case .Return:
        if sret != nil { return .Result_Slot }
    case .Write:
        dest := uops[0].op
        // (Several components of an array aren't one's storage: a temporary.)
        if uops[1].op != op || storage_direct(s, dest) || graph_op_of(pg, dest) == .Swizzle { return .Temporary }
        fresh := false
        if graph_is_leaf(dest) {
            d := graph_refers(pg, dest)
            fresh = graph_written(pg, d) == .Synthetic || graph_stmt(pg, u).kind == .Decl
        }
        // (The result slot is no fresher than any place: the local every
        // return returns lives there, and `x = f(x)` passes it.)
        if fresh && storage_had(s, dest, op) { return .Dest }
        if s.update[op] && storage_had(s, dest, op) { return .Dest }
        reaches, mine := storage_call_reaches(s, op, dest)
        if mine != NO_NODE { storage_reads_its_dest(pg, op, mine, dest, callee) }
        if !reaches && storage_had(s, dest, op) { return .Dest }
    }
    return .Temporary
}

// Where a declaration takes one of a call's several results, when that is all
// the result does: the declared variable (the write then has nothing to
// copy). NO_NODE: none.
@(private="file")
storage_declared_at :: proc(s: ^Storage, o: Operand) -> Node_Id {
    pg := s.pg
    u, ok := s.out_user[o]
    if !ok || u < 0 || graph_op_of(pg, u) != .Write { return NO_NODE }
    uops := graph_operands(pg, u)
    dest := uops[0].op
    if uops[1] != o || !graph_is_leaf(dest) || storage_direct(s, dest) { return NO_NODE }
    d := graph_refers(pg, dest)
    // (A constructor's field, declared there: new as a local is — Self's slot is.)
    field := s.ctor && graph_kind_of(pg, d) == .Field && pg.parent[d] == 0
    if graph_kind_of(pg, d) != .Local && !field { return NO_NODE }
    if graph_written(pg, d) != .Synthetic && graph_stmt(pg, d).node != graph_stmt(pg, u).node { return NO_NODE }
    return dest
}

// Where an assignment takes one of a call's several results, `x = f()?`,
// `g.big, n = f()`, a literal's field given `f()?`: the place written, of
// the result's type, when the call can't reach it while it runs
// (storage_call_reaches), its address can be had when the call is made, and
// nothing from the call to the write reads or writes it — a `?`'s failure
// apart, which leaves it part built. NO_NODE: none.
@(private="file")
storage_assigned_at :: proc(s: ^Storage, op: Node_Id, o: Operand, rt: Type) -> Node_Id {
    pg := s.pg
    u, ok := s.out_user[o]
    if !ok || u < 0 || graph_op_of(pg, u) != .Write { return NO_NODE }
    uops := graph_operands(pg, u)
    dest := uops[0].op
    if uops[1] != o || storage_direct(s, dest) { return NO_NODE }
    if graph_op_of(pg, dest) == .Swizzle || graph_op_of(pg, dest) == .Slice || !llvm_same_type(graph_type(pg, dest), rt) { return NO_NODE }
    from, to := s.pos[graph_ix(pg, op)], s.pos[graph_ix(pg, u)]
    if from < 0 || to <= from { return NO_NODE }
    if reaches, _ := storage_call_reaches(s, op, dest); reaches || !storage_had(s, dest, op) { return NO_NODE }
    for r in s.runs[:s.own] {
        if storage_fails(s, r) { continue }
        for x in graph_run(pg, int(r)) {
            if at := s.pos[graph_ix(pg, x)]; at <= from || at >= to { continue }
            xops := graph_operands(pg, x)
            #partial switch graph_op_of(pg, x) {
            case .Read, .Address:
                if graph_op_of(pg, x) == .Read && storage_direct(s, xops[0].op) { continue }   // a value, in no memory
                if storage_overlaps(s, xops[0].op, dest) { return NO_NODE }
            case .Write, .Zero, .Fill, .Construct, .Byte_Read:
                if storage_overlaps(s, xops[0].op, dest) { return NO_NODE }
                if len(xops) > 1 && graph_is_leaf(xops[1].op) && graph_leaf_decl(pg, xops[1].op) >= 0 && storage_overlaps(s, xops[1].op, dest) { return NO_NODE }
            case .Field, .Variant, .Index, .Deref, .Const, .Arith, .Compare, .Unary, .Cast, .Swizzle, .Global, .Branch:
            case:
                return NO_NODE
            }
        }
    }
    return dest
}

// Whether place p's address is at hand when operation `at` runs: it was
// computed before it, or it is a variable, or a field or constant index of
// one (computed then, ahead of its turn).
@(private="file")
storage_had :: proc(s: ^Storage, p, at: Node_Id) -> bool {
    pg := s.pg
    if graph_is_leaf(p) { return true }
    if s.pos[graph_ix(s.pg, p)] >= 0 && s.pos[graph_ix(s.pg, at)] >= 0 && s.pos[graph_ix(s.pg, p)] < s.pos[graph_ix(s.pg, at)] { return true }
    ops := graph_operands(pg, p)
    #partial switch graph_op_of(pg, p) {
    case .Field, .Variant, .Deref:   // (a union's variant: the union's own address; a pointer's target: its value)
        return storage_had(s, ops[0].op, at)
    case .Index:
        return graph_is_const(ops[1].op) && storage_had(s, ops[0].op, at)
    }
    return false
}

// Whether a call's operation is constant text, read or not: its text.
graph_const_text :: proc(pg: ^Program_Graph, op: Node_Id) -> (string, bool) {
    at := op
    if graph_op_of(pg, at) == .Read { at = graph_operands(pg, at)[0].op }
    if at == NO_NODE || graph_op_of(pg, at) != .Global { return "", false }
    c, has := graph_value(pg, at)
    return c.text, has && c.is_text
}

