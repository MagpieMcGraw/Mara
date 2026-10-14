package mara

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
    if sret != nil || rets != nil { storage_result_slot(s, rets) }
    storage_in_place(s)
    storage_swaps(s)
    storage_big_temps(s)
    if s.stop == NO_NODE { storage_calls(s, sret) }
    if len(s.temps) > 0 && !checked.table.has_scope_allocator && !checked.table.context_expected_at_runtime {
        tp := s.temps[0]
        storage_fatal(graph_origin(pg, tp.at.op), CODE_TEMPORARY_NO_ARENA, type_name(tp.t), type_size(tp.t))
    }
    return s
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
    if d <= 0 || d > pg.end { return false }   // this_program's: in memory
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
// With several results, each aggregate one's slot — a returned local only
// when a fixed array (the others: later).
@(private="file")
storage_result_slot :: proc(s: ^Storage, rets: []Type) {
    if s.one_slot {
        storage_result_slot_at(s, 0, 1, named = true)
        return
    }
    for rt, i in rets {
        if !llvm_aggregate(rt) { continue }
        storage_result_slot_at(s, i, len(rets), named = llvm_array(rt) != nil)
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
            v := NO_NODE
            if len(ops) == n && ops[k].op != NO_NODE && graph_op_of(pg, ops[k].op) == .Read {
                if d := graph_leaf_decl(pg, graph_operands(pg, ops[k].op)[0].op); d >= 0 && graph_kind_of(pg, d) == .Local { v = d }
            }
            if v in s.carved { v, every = NO_NODE, false }   // the carved memory: copied out
            if v != NO_NODE && graph_written(pg, v) == .Synthetic {
                // (Not an `if` expression's, written by its arms: its own.)
                if storage_reads(s, v) == 1 && storage_written_only_in(s, v, r) { s.result[v] = k }
                v = NO_NODE   // a temporary is no named local
            }
            switch {
            case v == NO_NODE:                        every = false
            case returned == NO_NODE:                 returned = v
            case returned != v:                       every = false
            }
        }
    }
    if named && every && returned != NO_NODE { s.result[returned] = k }
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
// caller's storage (the rule for calls).
@(private="file")
storage_in_place :: proc(s: ^Storage) {
    pg := s.pg
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
            if storage_builds_alone(s, ops[:at], t, x) { s.in_place[t] = x }
        }
    }
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
            // this_program is an object of its type, reached through the
            // pointer the program's code is handed.
            if !w.via_ptr { w.via_ptr, w.region = storage_this_program(pg, w.root), graph_type(pg, id) }
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

// Whether a variable is `this_program`, the compiler's global: a declaration
// the code names from outside it.
storage_this_program :: proc(pg: ^Program_Graph, d: Node_Id) -> bool {
    return d > pg.end && graph_name(pg, d) == "this_program"
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
// reads or writes through it. Nothing else: `this_program`, which every fun
// can read, is read only (tc_in_program) — no place being built is in it,
// and its arena's bookkeeping is in it.

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
        if s.one_slot && id in s.result { continue }
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
                for i in 0 ..< fn_result_count(callee) {
                    rt := fn_result(callee, i)
                    if !llvm_aggregate(rt) { continue }
                    o := Operand{op, i32(i)}
                    if d := storage_declared_at(s, o) if placed else NO_NODE; d != NO_NODE {
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
    if graph_kind_of(pg, d) != .Local || (graph_written(pg, d) != .Synthetic && graph_stmt(pg, d).node != graph_stmt(pg, u).node) { return NO_NODE }
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

