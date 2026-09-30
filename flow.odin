package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// flow.odin — post-check intraprocedural flow analysis: the diagnostics about
// how a function's code runs and what it reads.
//
// On the program graph (a clean check builds it; design/graph_retrofit.md,
// phase 2): all-paths-return (a fun whose runs reach the end of its body),
// unreachable code (a statement right after a return, break or continue),
// must-use err (an err local nothing reads) and a defer changing what a return
// returns. Still over each function's body:
// definite assignment (no read-before-init of a pointer or slice) and the void
// checks. MARA_DUMP_FLOW=1 dumps coverage and what was flagged.

Flow_Stats :: struct {
    functions:  int, // source functions walked

    // Functions flagged for "missing return on all code paths" — the first
    // analysis this pass OWNS (emitted below, not just collected).
    missing_return: [dynamic]string,
}

// Entry point — called post-check (after build_call_graph). Walks every source
// function and raises the intraprocedural diagnostics it owns. Takes the Checker
// purely as the error sink (check_error); the analysis itself reads only the
// durable Checked_Program.
// (`void_defaults`: the spans of params' `void` defaults the checker reported,
// check_void_defaults.)
flow_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program, void_defaults: map[Span]bool) {
    stats: Flow_Stats
    // Missing-return reads the program graph's runs, built from a clean check.
    graphed := len(checked.graph.kind) > 0
    starts: map[Node_Id]i32
    if graphed { starts = graph_run_starts(&checked.graph) }
    defer delete(starts)
    if graphed {
        flow_check_unreachable(c, checked)
        flow_check_literal_ranges(c, checked)
        flow_check_unused(c, checked)
        flow_check_init(c, checked, starts)
        flow_check_defer_writes(c, checked, starts)
        flow_check_void(c, checked, void_defaults)
        flow_check_constants(c, checked)
    }
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        // Source bodies only: intrinsics/foreigns have no Mara statements. An
        // empty one declares a shape (`Arena`'s methods, which a `~Arena`
        // param's type must have): nothing to return from.
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        if scope_body_is_empty(ft) { continue }
        stats.functions += 1
        if graphed && flow_missing_return(checked, starts, ft) {
            name := ft.source_name if ft.source_name != "" else ft.name
            // Same message + span the inline check used (ft.body_span == s.span).
            check_error(c, ft.body_span, TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, name)
            append(&stats.missing_return, name)
        }
    }
    flow_dump_stats(stats)
}

// Missing-return: a non-void function whose first return isn't `any` and whose
// returns aren't all-err must return on every path: no path through its runs
// reaches the synthetic return that ends its body (graph_falls_off).
flow_missing_return :: proc(checked: ^Checked_Program, starts: map[Node_Id]i32, ft: ^Type_Scope) -> bool {
    if len(ft.return_types) == 0 { return false }       // void
    if is_any(ft.return_types[0]) { return false }      // unresolved generic return
    if all_err_returns(ft.return_types) { return false } // all-err can fall off (.Ok fill)
    n, ok := checked.graph.scope_node[ft]
    if !ok { fmt.panicf("missing return: '%s' has no node in the program graph", ft.name) }
    return graph_falls_off(&checked.graph, starts, n)
}

// Unreachable code: a statement right after a return, break or continue (the
// graph records the first of each stretch). Codegen would put it after the
// terminator.
flow_check_unreachable :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for span in checked.graph.unreachable {
        if span in seen { continue }
        seen[span] = true
        check_error(c, span, TYPE_UNREACHABLE_CODE)
    }
}

// Literal ranges: a literal whose type is its use's — the width its `:=`
// adopted, an operand's — must fit it, as one written at that type must
// (`first := -1` adopting a u16 index's width was 65535, never below 0).
flow_check_literal_ranges :: proc(c: ^Checker, checked: ^Checked_Program) {
    g := &checked.graph
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for id in g.settled {
        v, ok := g.consts[id]
        if !ok || v.is_text { continue }
        span := g.origin[id]
        if span in seen { continue }
        seen[span] = true
        check_value_range(c, v.float if v.is_float else f64(v.int), v.int, g.type_[id], span)
    }
}

// --- must-use-err ---------------------------------------------------------
// An err-typed local that is declared but never read — not checked, not
// propagated with `?` (which leaves no binding), not discarded with `_` — is an
// error. On the graph a declaration is read where a var operation names it,
// except where a whole write lands (`e = f()` writes e, it reads nothing);
// refers-to has resolved shadowing, and a read in a nested block or a defer's
// block is a read like any other.
flow_check_unused :: proc(c: ^Checker, checked: ^Checked_Program) {
    g := &checked.graph
    dest := make([]bool, len(g.kind))   // where a whole write lands
    defer delete(dest)
    read := make([]bool, len(g.kind))
    defer delete(read)
    for k, id in g.kind {
        if k != .Op { continue }
        #partial switch g.op[id] {
        case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Arena_Alloc:
            ops := graph_operands(g, Node_Id(id))
            if len(ops) > 0 && ops[0].op != NO_NODE && g.kind[ops[0].op] == .Op && g.op[ops[0].op] == .Var {
                dest[ops[0].op] = true
            }
        }
    }
    for k, id in g.kind {
        if k == .Op && g.op[id] == .Var && !dest[id] && g.refers[id] != NO_NODE { read[g.refers[id]] = true }
    }
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for k, id in g.kind {
        if k != .Local || g.written[id] != .Explicit || read[id] || !is_err_type(g.type_[id]) { continue }
        // Declared by a statement, as `e := f()` or `v, e := f()`: not a loop's
        // variable or a match arm's binding.
        s := g.stmt[id]
        if s < 0 || (g.stmts[s].kind != .Decl && g.stmts[s].kind != .Destructure) { continue }
        span := g.origin[id]
        if span in seen { continue }
        seen[span] = true
        check_error(c, span, TYPE_UNUSED_ERR, g.name[id])
    }
}

// --- defers and returned values -------------------------------------------
// A return takes its values, then the defers it leaves run. One of those
// defers changing a local the return returns — writing it, a field or an
// element of it, or taking its address — would change what the caller gets
// or not depending on how the value travels (a copy, or built in place), so
// it is an error. A value the return computes is no local; a write through a
// pointer that aliases one is not seen (field-insensitive, like escape).
flow_check_defer_writes :: proc(c: ^Checker, checked: ^Checked_Program, starts: map[Node_Id]i32) {
    g := &checked.graph
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    runs, block: [dynamic]i32
    defer { delete(runs); delete(block) }
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }
        node, ok := g.scope_node[ft]
        if !ok || g.kind[node] != .Fun { continue }
        clear(&runs)
        own := graph_code_runs(g, starts, node, &runs)
        for r in runs[:own] {
            ops := graph_run(g, int(r))
            ret := ops[len(ops) - 1]
            if g.op[ret] != .Return { continue }
            // The defers it runs: the run defers just before it.
            for k := len(ops) - 2; k >= 0; k -= 1 {
                if g.op[ops[k]] == .Arena_Reset { continue }
                if g.op[ops[k]] != .Run_Defer { break }
                for edge in graph_out(g, ops[k]) {
                    if edge.kind != .Runs { continue }
                    clear(&block)
                    graph_code_runs(g, starts, edge.to, &block)
                    flow_defer_writes(c, g, ret, block[:], &seen)
                }
            }
        }
    }
}

// A defer block's changes to what `ret` returns.
@(private="file")
flow_defer_writes :: proc(c: ^Checker, g: ^Program_Graph, ret: Node_Id, block: []i32, seen: ^map[Span]bool) {
    for o in graph_operands(g, ret) {
        v := flow_returned_local(g, o.op)
        if v == NO_NODE { continue }
        for r in block {
            for op in graph_run(g, int(r)) {
                #partial switch g.op[op] {
                case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Carve, .Address:
                case:
                    continue
                }
                ops := graph_operands(g, op)
                if len(ops) == 0 || flow_storage_root(g, ops[0].op) != v { continue }
                span := g.origin[op]
                if span in seen^ { continue }
                seen[span] = true
                check_error(c, span, TYPE_DEFER_CHANGES_RETURNED, g.name[v], span_line(g.origin[ret]))
            }
        }
    }
}

// The local a returned value is, as read (through an implied widening); none
// for a value computed.
@(private="file")
flow_returned_local :: proc(g: ^Program_Graph, v: Node_Id) -> Node_Id {
    v := v
    for v != NO_NODE && g.op[v] == .Cast && g.written[v] == .Implied { v = graph_operands(g, v)[0].op }
    if v == NO_NODE || g.op[v] != .Read { return NO_NODE }
    root := flow_storage_root(g, graph_operands(g, v)[0].op)
    if root == NO_NODE || (g.kind[root] != .Local && g.kind[root] != .Result) { return NO_NODE }
    return root
}

// The variable whose own storage a place is in: through fields, elements and
// views, not through a pointer.
@(private="file")
flow_storage_root :: proc(g: ^Program_Graph, p: Node_Id) -> Node_Id {
    for id := p; id != NO_NODE; {
        #partial switch g.op[id] {
        case .Var:
            return g.refers[id]
        case .Field, .Index, .View, .Swizzle, .Variant, .Slice:
            id = graph_operands(g, id)[0].op
        case:
            return NO_NODE
        }
    }
    return NO_NODE
}

// --- definite assignment --------------------------------------------------
// Reading a pointer, a slice or a scalar set to `void` before it holds a value
// is an error, and so is reading a pointer or slice field of a struct built
// without one (`n : Node` leaves `n.next` unset). Forward dataflow over each
// fun's runs: the state is what may be unset — variables, and a struct
// variable's fields — unioned at joins, so a read is flagged when some path
// reaches it unset. Loops iterate to their fixpoint, and a defer's block sees
// the state at each exit that runs it.
//
// A call handed a variable's address (`init(&h)`, `load(&h.buf)`, or a pointer
// known to alias it) may assign through it: from there it counts as set. An
// alias is a pointer every write of which is `&x`: `it = &root` makes `it.next`
// read `root.next`.

@(private="file")
Init_Key :: struct {
    var:   Node_Id,
    field: string,   // "" for the variable itself
}

@(private="file")
Init :: struct {
    g:     ^Program_Graph,
    keys:  map[Init_Key]int,
    alias: map[Node_Id]Node_Id,   // a pointer local → the local it always points at
    user:  map[Node_Id]Node_Id,   // an operation → the one that takes its output
    words: int,
    c:     ^Checker,
    seen:  ^map[Span]bool,       // reads reported (generic instances share spans)
}

flow_check_init :: proc(c: ^Checker, checked: ^Checked_Program, starts: map[Node_Id]i32) {
    g := &checked.graph
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }
        node, ok := g.scope_node[ft]
        if !ok { continue }
        flow_init_fun(c, g, starts, node, &seen)
    }
}

@(private="file")
flow_init_fun :: proc(c: ^Checker, g: ^Program_Graph, starts: map[Node_Id]i32, node: Node_Id, seen: ^map[Span]bool) {
    runs: [dynamic]i32
    defer delete(runs)
    graph_code_runs(g, starts, node, &runs)
    if len(runs) == 0 { return }

    s := Init{g = g, c = c, seen = seen}
    defer { delete(s.keys); delete(s.alias); delete(s.user) }

    // What can be unset: its locals that are pointers, slices or scalars, and
    // the pointer and slice fields of its struct locals that have no default.
    for id := node + 1; id <= g.last[node]; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct, .Union, .Enum:
            id = g.last[id]
            continue
        case .Local:
            if g.written[id] != .Explicit { continue }
        case:
            continue
        }
        base := distinct_base(g.type_[id])
        if flow_can_be_unset(base) {
            s.keys[Init_Key{id, ""}] = len(s.keys)
        } else if sd := as_scope_body(base); sd != nil {
            for &f in sd.fields {
                if field_has_default(f) || !flow_field_can_be_unset(f.type_) { continue }
                s.keys[Init_Key{id, f.name}] = len(s.keys)
            }
        }
    }
    if len(s.keys) == 0 { return }
    s.words = (len(s.keys) + 63) / 64

    // Who takes each operation's output, and which pointers are aliases.
    not_alias: map[Node_Id]bool
    defer delete(not_alias)
    for r in runs {
        for op in graph_run(g, int(r)) {
            for o in graph_operands(g, op) { if o.op != NO_NODE { s.user[o.op] = op } }
            v, whole, is_write := flow_written(g, op)
            if !is_write || !whole || g.op[op] != .Write { continue }
            val := graph_operands(g, op)[1].op
            target := NO_NODE
            if val != NO_NODE && g.op[val] == .Address {
                if p := graph_operands(g, val)[0].op; g.op[p] == .Var { target = g.refers[p] }
            }
            if target == NO_NODE || (v in s.alias && s.alias[v] != target) {
                not_alias[v] = true
            } else {
                s.alias[v] = target
            }
        }
    }
    for v in not_alias { delete_key(&s.alias, v) }

    // The fixpoint: each run's entry state.
    at: map[i32]int
    defer delete(at)
    for r, i in runs { at[r] = i }
    in_state := make([][]u64, len(runs))
    defer { for x in in_state { delete(x) }; delete(in_state) }
    for &x in in_state { x = make([]u64, s.words) }
    entered := make([]bool, len(runs))
    defer delete(entered)
    state := make([]u64, s.words)
    defer delete(state)
    todo: [dynamic]int
    defer delete(todo)
    entered[0] = true
    append(&todo, 0)
    merge :: proc(dst, src: []u64) -> bool {
        grew := false
        for w, i in src { if dst[i] | w != dst[i] { dst[i] |= w; grew = true } }
        return grew
    }
    enter :: proc(i: int, state: []u64, in_state: [][]u64, entered: []bool, todo: ^[dynamic]int) {
        if merge(in_state[i], state) || !entered[i] { entered[i] = true; append(todo, i) }
    }
    for len(todo) > 0 {
        ri := pop(&todo)
        copy(state, in_state[ri])
        ops := graph_run(g, int(runs[ri]))
        for op in ops {
            flow_init_op(&s, op, state, false)
            if g.op[op] != .Run_Defer { continue }
            for e in graph_out(g, op) {
                if e.kind != .Runs { continue }
                for e2 in graph_out(g, e.to) {
                    if e2.kind != .Then { continue }
                    if di, ok := at[starts[e2.to]]; ok { enter(di, state, in_state, entered, &todo) }
                }
            }
        }
        for e in graph_out(g, ops[len(ops) - 1]) {
            if e.kind != .Then { continue }
            if si, ok := at[starts[e.to]]; ok { enter(si, state, in_state, entered, &todo) }
        }
    }

    // The reads, against the fixpoint, in the order the runs list them.
    for r, ri in runs {
        if !entered[ri] { continue }
        copy(state, in_state[ri])
        for op in graph_run(g, int(r)) { flow_init_op(&s, op, state, true) }
    }
}

// Whether a variable of this type can be read unset: a pointer, a slice, or a
// scalar (unset only by `void`).
@(private="file")
flow_can_be_unset :: proc(base: Type) -> bool {
    #partial switch _ in base {
    case ^Type_Ptr, ^Type_Slice: return true
    case Type_Error:             return false
    case Type_Bool, Type_Utf8, Type_Byte, Type_CString, Type_Err: return true
    }
    return is_numeric(base)
}

// A struct's field that a bare construction leaves unset: a pointer or a
// slice (not a distinct slice that sizes its own storage).
@(private="file")
flow_field_can_be_unset :: proc(t: Type) -> bool {
    if dt, ok := t.(^Type_Distinct); ok {
        if _, sl := dt.base_type.(^Type_Slice); sl && distinct_is_sized(dt) { return false }
    }
    #partial switch _ in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice: return true
    }
    return false
}

// The variable a write replaces as a whole: its destination is the variable.
@(private="file")
flow_written :: proc(g: ^Program_Graph, op: Node_Id) -> (v: Node_Id, whole: bool, ok: bool) {
    #partial switch g.op[op] {
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
    case:
        return
    }
    ops := graph_operands(g, op)
    if len(ops) == 0 || ops[0].op == NO_NODE || g.kind[ops[0].op] != .Op { return }
    d := ops[0].op
    if g.op[d] == .Var { return g.refers[d], true, true }
    return NO_NODE, false, false
}

@(private="file")
flow_set :: proc(s: ^Init, state: []u64, k: Init_Key, unset: bool) {
    i, ok := s.keys[k]
    if !ok { return }
    if unset { state[i / 64] |= 1 << uint(i % 64) } else { state[i / 64] &~= 1 << uint(i % 64) }
}

@(private="file")
flow_is_unset :: proc(s: ^Init, state: []u64, k: Init_Key) -> bool {
    i, ok := s.keys[k]
    return ok && state[i / 64] & (1 << uint(i % 64)) != 0
}

// Every field of a struct variable, set or unset (a whole write, `void`).
@(private="file")
flow_set_fields :: proc(s: ^Init, state: []u64, v: Node_Id, unset: bool) {
    for k in s.keys { if k.var == v && k.field != "" { flow_set(s, state, k, unset) } }
}

// The struct variable and field a place names: `x.f`, or `p.f` through a
// pointer that aliases x.
@(private="file")
flow_field_place :: proc(s: ^Init, f: Node_Id) -> (key: Init_Key, via: Node_Id, ok: bool) {
    g := s.g
    if g.op[f] != .Field { return }
    base := graph_operands(g, f)[0].op
    if base == NO_NODE || g.kind[base] != .Op { return }
    #partial switch g.op[base] {
    case .Var:
        return Init_Key{g.refers[base], g.name[f]}, NO_NODE, true
    case .Deref:
        p := graph_operands(g, base)[0].op
        if p == NO_NODE || g.op[p] != .Var { return }
        if target, is_alias := s.alias[g.refers[p]]; is_alias {
            return Init_Key{target, g.name[f]}, g.refers[p], true
        }
    }
    return
}

// Whether a place's output is read: not written to as a whole, not only
// addressed, not only a step toward a field.
@(private="file")
flow_read_by :: proc(s: ^Init, op: Node_Id) -> bool {
    g := s.g
    u, has := s.user[op]
    if !has { return false }
    #partial switch g.op[u] {
    case .Address, .Arena_Alloc, .Field, .Swizzle, .Variant:
        return false
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
        return graph_operands(g, u)[0].op != op
    }
    return true
}

// One operation's effect on the state; reporting, its unset reads too.
@(private="file")
flow_init_op :: proc(s: ^Init, op: Node_Id, state: []u64, reporting: bool) {
    g := s.g
    report :: proc(s: ^Init, span: Span, msg: string, args: ..any) {
        if span in s.seen^ { return }
        s.seen^[span] = true
        check_error(s.c, span, msg, ..args)
    }
    #partial switch g.op[op] {
    case .Var:
        k := Init_Key{g.refers[op], ""}
        if reporting && flow_is_unset(s, state, k) && flow_read_by(s, op) {
            report(s, g.origin[op], TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE, g.name[op])
        }
    case .Field:
        k, via, ok := flow_field_place(s, op)
        if !ok || !reporting || !flow_is_unset(s, state, k) { break }
        u, has := s.user[op]
        if !has { break }
        if g.op[u] == .Write || g.op[u] == .Fill || g.op[u] == .Zero || g.op[u] == .Construct || g.op[u] == .Byte_Read {
            if graph_operands(g, u)[0].op == op { break }   // written, not read
        }
        if g.op[u] == .Address || g.op[u] == .Field || g.op[u] == .Swizzle { break }
        if via != NO_NODE {
            report(s, g.origin[op], TYPE_FIELD_ALIASED_VIA_USED_BEFORE, k.field, g.name[k.var], g.name[via])
        } else {
            report(s, g.origin[op], TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, k.field, g.name[k.var])
        }
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
        ops := graph_operands(g, op)
        d := ops[0].op if len(ops) > 0 else NO_NODE
        if d == NO_NODE || g.kind[d] != .Op { break }
        if g.op[d] == .Var {
            v := g.refers[d]
            unset, fields_unset := false, false
            #partial switch g.op[op] {
            case .Write:
                val := ops[1].op
                unset = val != NO_NODE && g.op[val] == .Const && g.name[val] == "void"
                fields_unset = unset
            case .Zero:
                // A bare `p : ^T` or `s : []T` (a sized slice has its storage, a
                // bare scalar is zero).
                #partial switch _ in distinct_base(g.type_[v]) {
                case ^Type_Ptr, ^Type_Slice: unset = g.written[op] == .Synthetic && len(ops) == 1
                }
            case .Construct:
                // Built bare or from braces, a struct has only what it is given
                // (the braces' writes follow); a constructor call may set anything.
                fields_unset = g.written[op] == .Synthetic || strings.has_suffix(g.name[op], "{}")
            }
            flow_set(s, state, Init_Key{v, ""}, unset)
            flow_set_fields(s, state, v, fields_unset)
        } else if k, _, ok := flow_field_place(s, d); ok {
            flow_set(s, state, k, false)
        }
        if g.op[op] == .Construct { flow_init_out_params(s, op, state) }
    case .Call:
        flow_init_out_params(s, op, state)
    }
}

// A call's arguments that hand it a variable's address: from the call on, it
// (or that field) counts as set.
@(private="file")
flow_init_out_params :: proc(s: ^Init, op: Node_Id, state: []u64) {
    g := s.g
    for a in du_call_args(g, op) {
        x := a.op
        if x == NO_NODE || g.kind[x] != .Op { continue }
        #partial switch g.op[x] {
        case .Address:
            p := graph_operands(g, x)[0].op
            if p == NO_NODE || g.kind[p] != .Op { continue }
            if g.op[p] == .Var {
                flow_set(s, state, Init_Key{g.refers[p], ""}, false)
                flow_set_fields(s, state, g.refers[p], false)
            } else if k, _, ok := flow_field_place(s, p); ok {
                flow_set(s, state, k, false)
            }
        case .Read:
            p := graph_operands(g, x)[0].op
            if p == NO_NODE || g.op[p] != .Var { continue }
            if target, is_alias := s.alias[g.refers[p]]; is_alias {
                flow_set(s, state, Init_Key{target, ""}, false)
                flow_set_fields(s, state, target, false)
            }
        }
    }
}


flow_dump_stats :: proc(stats: Flow_Stats) {
    buf: [8]byte
    if os.get_env_buf(buf[:], "MARA_DUMP_FLOW") != "1" { return }
    fmt.eprintf("[flow] %d source funcs\n", stats.functions)
    fmt.eprintf("[flow] missing-return flagged: %d %v\n",
        len(stats.missing_return), stats.missing_return)
}

// --- constants -----------------------------------------------------------------
// A use of a constant whose value can't be known before the program runs
// (graph_fold_uses: a call in it, a struct's construction with arguments).

flow_check_constants :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for e in checked.graph.fold_errors {
        if seen[e.span] { continue }
        seen[e.span] = true
        check_error(c, e.span, TYPE_CONST_NOT_COMPILE_TIME, e.name)
    }
}

// --- void into pointers ------------------------------------------------------
// A pointer always points at something that exists in the program. `void` is no
// pointer value: it DE-INITIALIZES a variable — `p = void`, `p : ^T = void`, and
// reading p is then an error (flow_check_init) — or passes a C function a null
// for a nullable parameter; it can be compared against (`p == void`). Anywhere
// else a void headed for a pointer — a return, an argument, a field, an element,
// a store through a field/index/deref, an if-branch, a default — is an error.

flow_check_void :: proc(c: ^Checker, checked: ^Checked_Program, void_defaults: map[Span]bool) {
    g := &checked.graph
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    // (A parameter's default: the checker's, check_void_defaults.)
    for sp in void_defaults { seen[sp] = true }
    // Every other: a void as written, where the operation that takes it
    // stores it — its type its use's.
    for i in 0 ..< len(g.kind) {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        for o, k in graph_operands(g, id) {
            v := o.op
            if v == NO_NODE || g.op[v] != .Const || g.name[v] != "void" { continue }
            if g.written[v] != .Explicit { continue }
            if where_, stored := void_where(g, id, k); stored {
                void_error(c, &seen, g.origin[v], g.type_[v], where_)
            }
        }
    }
}

// A pointer, or a value that is one underneath (a cstring, a function).
void_is_pointer :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Ptr, Type_CString: return true
    case ^Type_Scope:             return v.kind == .Fun
    }
    return false
}

// A void stored where a `dest` goes: an error when dest is a pointer.
void_error :: proc(c: ^Checker, seen: ^map[Span]bool, sp: Span, dest: Type, where_: string) {
    if !void_is_pointer(dest) || seen[sp] { return }
    seen[sp] = true
    check_error(c, sp, TYPE_VOID_INTO_POINTER, where_, type_name(dest))
}

// Where operation `op` stores its k-th operand, when that is somewhere a
// void can't go: not a whole variable (its de-init), a C function's
// argument (a null), a comparison.
@(private="file")
void_where :: proc(g: ^Program_Graph, op: Node_Id, k: int) -> (string, bool) {
    ops := graph_operands(g, op)
    #partial switch g.op[op] {
    case .Write:
        if k != 1 { return "", false }
        dest := ops[0].op
        #partial switch g.op[dest] {
        case .Field:        return fmt.tprintf("field '%s'", g.name[dest]), true
        case .Index, .View: return "an array element", true
        case .Deref:        return "a dereferenced pointer", true
        case .Var:
            // A struct body's field, and the slot an if-expression's
            // branches go into, are no variables.
            d := g.refers[dest]
            if d == NO_NODE { return "", false }
            if g.kind[d] == .Field { return fmt.tprintf("field '%s'", g.name[d]), true }
            if g.kind[d] == .Local && g.written[d] == .Synthetic && g.name[d] == "if" {
                return "a branch of an if-expression", true
            }
        }
    case .Call, .Construct:
        sig := graph_signature(g, op)
        if sig == nil || sig.calling_conv == .C { return "", false }
        // (A construction's first operand is where it builds; a call
        // through a function value's, the value.)
        n := k + 1 if g.op[op] == .Call && graph_called(g, op) != nil else k
        return fmt.tprintf("argument %d of '%s'", n, g.name[op]), true
    case .Return:
        return "a return value", true
    }
    return "", false
}

// The checked functions in name order: a map's order changes from run to run,
// and the diagnostics would follow it.
flow_functions :: proc(checked: ^Checked_Program) -> []^Type_Scope {
    names := make([dynamic]string, 0, len(checked.functions), context.temp_allocator)
    for name in checked.functions { append(&names, name) }
    slice.sort(names[:])
    out := make([]^Type_Scope, len(names), context.temp_allocator)
    for name, i in names { out[i] = checked.functions[name] }
    return out
}
