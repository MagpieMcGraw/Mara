package mara

// storage.odin — where each value of a fun's code lives, decided for the
// whole fun before a backend emits it: which locals need storage of their own
// and which are a value, a view's header values, carved memory, a match's
// payload or the caller's result slot; which temporaries are built in the
// place they are then written to; which functional updates build into their
// argument; which swaps are done in place; where big temporaries go on the
// arena. A backend reads these facts; it decides none of them.
//
// (Read off the program graph for now, as codegen read them while it emitted;
// they move to the typed tree with the rest of the third layer.)

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
    marked:   map[Node_Id]bool,             // the scopes that mark the arena
    temps_at: map[Node_Id][dynamic]Node_Id, // a marked scope → its big temporaries, bumped at its mark
    lazy:     map[Node_Id]bool,             // a big temporary in main's body: bumped where it's first named
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
    storage_big_temps(s, checked.table.has_scope_allocator)
    if s.stop == NO_NODE { storage_calls(s, sret) }
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
    s.user = make([]Node_Id, int(pg.end) + 1)
    for &u in s.user { u = -1 }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            for o in graph_operands(pg, op) {
                if o.op == NO_NODE { continue }
                u := &s.user[o.op]
                u^ = op if u^ == -1 else -2
                ou, seen := s.out_user[o]
                s.out_user[o] = -2 if seen && ou != op else op
            }
            // A match arm's binding is the payload's place.
            if pg.op[op] == .Variant && pg.refers[op] != NO_NODE { s.bound[pg.refers[op]] = op }
            if pg.op[op] == .Arena_Alloc { s.arena[pg.refers[graph_operands(pg, op)[0].op]] = true }
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
        if pg.kind[d] != .Result || pg.parent[d] != 0 { continue }
        defer i += 1
        if pg.written[d] != .Explicit { continue }
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
            if pg.op[op] != .Write { continue }
            ops := graph_operands(pg, op)
            if pg.op[ops[0].op] != .Var || pg.refers[ops[0].op] != v { continue }
            x := ops[1].op
            return x != NO_NODE && pg.op[x] == .Slice && s.user[x] == op
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
                if o.op == NO_NODE || pg.op[o.op] != .Var || pg.refers[o.op] != v { continue }
                u := s.user[op]
                switch {
                case pg.op[op] == .Write && k == 0:
                    if write_run >= 0 { return false }
                    write_run, write_at = ri, at
                case (pg.op[op] == .Read || pg.op[op] == .Deref) && !header:   // (a pointer's deref reads it)
                    append(&reads, Read{ri, at})
                case header && pg.op[op] == .Field && llvm_header_field(graph_name(pg, op)) >= 0 && u >= 0 && pg.op[u] == .Read,
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
            j, ok := at[pg.run_starts[edge.to]]
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
            if pg.op[op] != .Read { continue }
            place := graph_operands(pg, op)[0].op
            if pg.op[place] == .Var && pg.refers[place] == v { n += 1 }
        }
    }
    return n
}

// Whether a place holds its value directly, not at an address: a scalar param
// (read-only, its argument) or a held synthetic local.
@(private="file")
storage_direct :: proc(s: ^Storage, place: Node_Id) -> bool {
    pg := s.pg
    if pg.op[place] != .Var { return false }   // (a held view's len or cap is one only as it's emitted)
    d := pg.refers[place]
    if pg.kind[d] == .Param { return llvm_scalar(graph_type(pg, d)) }
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
            if pg.op[op] != .Call { continue }
            callee := graph_called(pg, op)
            if callee == nil { continue }
            k, consumes := graph_consumed(s.pc, callee).?
            u := s.user[op]
            if !consumes || u < 0 || pg.op[u] != .Write { continue }
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
// (A variable's operation computes nothing: not aliased.)
@(private="file")
storage_alias_place :: proc(s: ^Storage, a, d: Node_Id) {
    pg := s.pg
    if a == NO_NODE || d == NO_NODE || a == d || d > a || pg.op[a] == .Var { return }
    s.alias[a] = d
    ao, do_ := graph_operands(pg, a), graph_operands(pg, d)
    #partial switch pg.op[a] {
    case .Field, .Deref, .Read:
        storage_alias_place(s, ao[0].op, do_[0].op)
    case .Index:
        storage_alias_place(s, ao[0].op, do_[0].op)
        if ai, di := ao[1].op, do_[1].op; ai != NO_NODE && di != NO_NODE && pg.op[ai] == .Read && pg.op[di] == .Read {
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
    if k >= len(ops) || ops[k].op == NO_NODE || pg.op[ops[k].op] != .Read { return false }
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
    if a == NO_NODE || b == NO_NODE || pg.op[a] != pg.op[b] { return false }
    ao, bo := graph_operands(pg, a), graph_operands(pg, b)
    #partial switch pg.op[a] {
    case .Var:
        return pg.refers[a] == pg.refers[b]
    case .Field:
        return graph_name(pg, a) == graph_name(pg, b) && storage_same(s, ao[0].op, bo[0].op)
    case .Index:
        if !storage_same(s, ao[0].op, bo[0].op) { return false }
        ai, bi := ao[1].op, bo[1].op
        if ai == NO_NODE || bi == NO_NODE || pg.op[ai] != pg.op[bi] { return false }
        #partial switch pg.op[ai] {
        case .Const:
            av, aok := graph_value(pg, ai)
            bv, bok := graph_value(pg, bi)
            return aok && bok && !av.is_float && !bv.is_float && av.int == bv.int
        case .Read:
            ap, bp := graph_operands(pg, ai)[0].op, graph_operands(pg, bi)[0].op
            return pg.op[ap] == .Var && pg.op[bp] == .Var && pg.refers[ap] == pg.refers[bp]
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
    if pg.op[a.op] != .Read { return false }
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
            if pg.op[w] != .Write { continue }
            ops := graph_operands(pg, w)
            c, dest := ops[1].op, ops[0].op
            if c == NO_NODE || pg.op[c] != .Carve || graph_name(pg, c) != "let" || pg.op[dest] != .Var { continue }
            st := pg.stmt[w]
            if d := pg.refers[dest]; pg.kind[d] == .Local && st >= 0 && pg.stmts[st].kind == .Decl { s.carved[d] = c }
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
            if pg.op[op] != .Return || pg.written[op] == .Implied { continue }
            ops := graph_operands(pg, op)
            v := NO_NODE
            if len(ops) == n && ops[k].op != NO_NODE && pg.op[ops[k].op] == .Read {
                place := graph_operands(pg, ops[k].op)[0].op
                if pg.op[place] == .Var && pg.kind[pg.refers[place]] == .Local { v = pg.refers[place] }
            }
            if v in s.carved { v, every = NO_NODE, false }   // the carved memory: copied out
            if v != NO_NODE && pg.written[v] == .Synthetic {
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
    if s.ctor && (d == 0 || (s.pg.kind[d] == .Field && s.pg.parent[d] == 0)) { return true }
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
        #partial switch pg.op[at] {
        case .Variant:
            at = graph_operands(pg, at)[0].op
            continue
        case .Var:
            d := pg.refers[at]
            if s.ctor && d == 0 { return true }
            if d <= 0 || d > pg.end || pg.kind[d] == .Param || pg.kind[d] == .Field { return false }
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
            #partial switch pg.op[op] {
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
            if pg.op[w] != .Write { continue }
            wops := graph_operands(pg, w)
            x, v := wops[0].op, wops[1].op
            if v == NO_NODE || wops[1].out != 0 || pg.op[v] != .Read || !llvm_aggregate(graph_type(pg, v)) { continue }
            tv := graph_operands(pg, v)[0].op
            if pg.op[tv] != .Var || storage_direct(s, x) { continue }
            if pg.op[x] == .Swizzle { continue }   // components, not one array's storage
            if pg.op[x] == .Slice { continue }     // a run of elements the value's are copied into, no storage of one type
            t := pg.refers[tv]
            if t <= 0 || t > pg.end || pg.kind[t] != .Local || pg.written[t] != .Synthetic { continue }
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
    for r in s.runs {
        for op in graph_run(pg, int(r)) { if pg.op[op] == .Var && pg.refers[op] == t { uses += 1 } }
    }
    first := -1
    for op, i in before {
        if pg.op[op] == .Var && pg.refers[op] == t { here += 1 }
        #partial switch pg.op[op] {
        case .Zero, .Construct, .Fill, .Write:
            if first < 0 && storage_where(s, graph_operands(pg, op)[0].op).root == t { first = i }
        }
    }
    if uses != here || first < 0 { return false }
    if pg.op[x] != .Var {
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
        #partial switch pg.op[op] {
        case .Read, .Address:
            if storage_where(s, ops[0].op).root == t { continue }
            if pg.op[op] == .Read && storage_direct(s, ops[0].op) { continue }   // a value, in no memory
            if storage_overlaps(s, ops[0].op, x) {
                if pg.op[op] == .Read && clean && llvm_scalar(graph_type(pg, op)) && storage_ahead_able(s, ops[0].op) {
                    append(&hoists, op)
                    continue
                }
                return false
            }
        case .Construct:
            // t's own construction, handed arguments (handed no storage, its
            // constructor writes nothing but t: still clean). Another's: not.
            if pg.op[ops[0].op] != .Var || pg.refers[ops[0].op] != t { clean = false; continue }
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
        case .Var, .Field, .Variant, .Index, .Deref, .Const, .Arith, .Compare, .Unary, .Cast, .Swizzle, .Global:
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
    if pg.op[p] == .Var { return true }
    ops := graph_operands(pg, p)
    #partial switch pg.op[p] {
    case .Field, .Variant, .Deref: return storage_ahead_able(s, ops[0].op)
    case .Index: return ops[1].op != NO_NODE && pg.op[ops[1].op] == .Const && storage_ahead_able(s, ops[0].op)
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
        ops := graph_operands(pg, id)
        #partial switch pg.op[id] {
        case .Var:
            // A match arm's binding is its scrutinee's payload: where that is.
            if v, bound := s.bound[pg.refers[id]]; bound {
                id = v
                continue
            }
            w.root = pg.refers[id]
            // this_program is an object of its type, reached through the
            // pointer the program's code is handed.
            if !w.via_ptr { w.via_ptr, w.region = storage_this_program(pg, w.root), graph_type(pg, id) }
            return w
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
    if pg.op[read] == .Global { return false }   // a constant table is never written
    r, d := storage_where(s, read), storage_where(s, dest)
    if r.root == NO_NODE || d.root == NO_NODE || r.explicit { return true }
    if places_disjoint(pg, s.bound, read, dest) { return false }
    if !d.via_ptr && storage_in_result(s, d.root) && pg.kind[r.root] == .Param { return false }
    if !r.via_ptr && !d.via_ptr && r.root == d.root { return true }
    if !is_plain_data(graph_type(pg, read)) { return true }
    if !r.via_ptr && !d.via_ptr { return false }   // two variables' own storage
    read_own := !r.via_ptr && !storage_in_result(s, r.root) && pg.kind[r.root] != .Param
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
        for pg.op[at] == .Cast { at = graph_operands(pg, at)[0].op }   // (text as a slice: over it)
        if _, is_text := graph_const_text(pg, at); is_text { continue }
        // (The storage handed over: `&place`'s place, an aggregate's own.)
        place := NO_NODE
        #partial switch pg.op[at] {
        case .Address, .Read: place = graph_operands(pg, at)[0].op
        case .Var, .Field, .Index, .Deref, .Variant: place = at
        }
        if place != NO_NODE && is_plain_data(graph_type(pg, place)) && !storage_overlaps(s, place, dest) { continue }
        if pg.op[at] == .Address && mine == NO_NODE && places_contain(pg, s.bound, place, dest) { mine = at }
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
    storage_fatal(pg.origin[op], TYPE_RESULT_READS_DEST, name, held, into, name, into)
}

// Whether a call hands its callee storage: a param passed by address.
storage_passes_storage :: proc(callee: ^Type_Scope) -> bool {
    for p in callee.cg_params {
        if ir, _ := llvm_param_type(p.type_); ir == "ptr" { return true }
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
        return d > 0 && d <= pg.end && pg.kind[d] == .Local && pg.written[d] == .Synthetic && graph_name(pg, d) == "parallel"
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Write { continue }
            ops := graph_operands(pg, op)
            dest, v := ops[0].op, ops[1].op
            if pg.op[dest] == .Var && is_held(pg, pg.refers[dest]) {
                d := pg.refers[dest]
                if d not_in holds { holds[d] = make([dynamic]Node_Id, context.temp_allocator) }
                append(&holds[d], op)
                continue
            }
            if v != NO_NODE && pg.op[v] == .Read {
                if src := graph_operands(pg, v)[0].op; pg.op[src] == .Var && is_held(pg, pg.refers[src]) {
                    append(&puts, Put{op, dest, pg.refers[src], v, src})
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
        if read == NO_NODE || pg.op[read] != .Read { return }
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

// Where each big local that has no arena alloc of its own lives. A named one
// always has one (lowering's), unless it's in the caller's slot. A temporary
// not built in place lives on the arena as a big local does: bumped at the
// mark of the nearest scope around it that has one — once each time that
// scope is entered, its reset freeing it — or, in main's body (which marks
// nothing: its scope ends with the program), where it's first named. A
// temporary with neither is lowering's miss (lw_big_temps): an error.
@(private="file")
storage_big_temps :: proc(s: ^Storage, scope_allocator: bool) {
    pg := s.pg
    for r in s.runs {
        for op in graph_run(pg, int(r)) { if pg.op[op] == .Arena_Mark { s.marked[pg.parent[op]] = true } }
    }
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
        scope := NO_NODE
        for sc := pg.parent[id]; sc != NO_NODE; sc = pg.parent[sc] {
            if sc in s.marked { scope = sc; break }
            if pg.kind[sc] == .Fun || pg.kind[sc] == .Struct { break }
        }
        switch {
        case scope != NO_NODE:
            if scope not_in s.temps_at { s.temps_at[scope] = make([dynamic]Node_Id, context.temp_allocator) }
            append(&s.temps_at[scope], id)
        case s.main:
            s.lazy[id] = true
        case:
            msg := CODE_TEMPORARY_NO_ARENA_SCOPE if scope_allocator else CODE_TEMPORARY_NO_ARENA
            storage_fatal(pg.origin[id], msg, type_name(graph_type(pg, id)), type_size(graph_type(pg, id)))
        }
    }
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
    s.pos = make([]i32, int(pg.end) + 1)
    for &p in s.pos { p = -1 }
    n := i32(0)
    for r in s.runs[:s.own] {
        for op in graph_run(pg, int(r)) {
            s.pos[op] = n
            n += 1
        }
    }
    for r in s.runs {
        for op in graph_run(pg, int(r)) {
            if pg.op[op] != .Call { continue }
            callee := graph_called(pg, op)
            args := len(graph_operands(pg, op))
            if callee == nil {   // (through a function value, its first operand: by its type's signature)
                callee = graph_signature(pg, op)
                args -= 1
                if callee == nil { continue }
            } else {
                if callee.kind != .Fun { continue }
                if _, src := callee.origin.(Origin_Source); !src { continue }
            }
            if args != len(callee.cg_params) { continue }
            if len(callee.cg_returns) > 1 {
                for rt, i in callee.cg_returns {
                    if !llvm_aggregate(rt) { continue }
                    o := Operand{op, i32(i)}
                    if d := storage_declared_at(s, o); d != NO_NODE { s.out_at[o] = d }
                }
                continue
            }
            if len(callee.cg_returns) != 1 { continue }
            if result := callee.cg_returns[0]; llvm_scalar(result) || !llvm_aggregate(result) { continue }
            if at := storage_call_place(s, op, callee, sret); at != .Temporary { s.calls[op] = at }
        }
    }
}

@(private="file")
storage_call_place :: proc(s: ^Storage, op: Node_Id, callee: ^Type_Scope, sret: Type) -> Call_Place {
    pg := s.pg
    u := s.user[op]
    if u < 0 { return .Temporary }
    uops := graph_operands(pg, u)
    #partial switch pg.op[u] {
    case .Return:
        if sret != nil { return .Result_Slot }
    case .Write:
        dest := uops[0].op
        // (Several components of an array aren't one's storage: a temporary.)
        if uops[1].op != op || storage_direct(s, dest) || pg.op[dest] == .Swizzle { return .Temporary }
        fresh := false
        if pg.op[dest] == .Var {
            d := pg.refers[dest]
            st := pg.stmt[u]
            fresh = pg.written[d] == .Synthetic || (st >= 0 && pg.stmts[st].kind == .Decl)
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
    if !ok || u < 0 || pg.op[u] != .Write { return NO_NODE }
    uops := graph_operands(pg, u)
    dest := uops[0].op
    if uops[1] != o || pg.op[dest] != .Var || storage_direct(s, dest) { return NO_NODE }
    d := pg.refers[dest]
    if pg.kind[d] != .Local || (pg.written[d] != .Synthetic && pg.stmt[d] != pg.stmt[u]) { return NO_NODE }
    return dest
}

// Whether place p's address is at hand when operation `at` runs: it was
// computed before it, or it is a variable, or a field or constant index of
// one (computed then, ahead of its turn).
@(private="file")
storage_had :: proc(s: ^Storage, p, at: Node_Id) -> bool {
    pg := s.pg
    if s.pos[p] >= 0 && s.pos[at] >= 0 && s.pos[p] < s.pos[at] { return true }
    if pg.op[p] == .Var { return true }
    ops := graph_operands(pg, p)
    #partial switch pg.op[p] {
    case .Field, .Variant, .Deref:   // (a union's variant: the union's own address; a pointer's target: its value)
        return storage_had(s, ops[0].op, at)
    case .Index:
        return ops[1].op != NO_NODE && pg.op[ops[1].op] == .Const && storage_had(s, ops[0].op, at)
    }
    return false
}

// Whether a call's operation is constant text, read or not: its text.
graph_const_text :: proc(pg: ^Program_Graph, op: Node_Id) -> (string, bool) {
    at := op
    if pg.op[at] == .Read { at = graph_operands(pg, at)[0].op }
    if at == NO_NODE || pg.op[at] != .Global { return "", false }
    c, has := graph_value(pg, at)
    return c.text, has && c.is_text
}

