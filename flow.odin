package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// flow.odin — post-check intraprocedural flow analysis: the diagnostics about
// how a function's code runs and what it reads, on the program graph (a clean
// check builds it): all-paths-return (a fun whose runs reach the end of its
// body), unreachable code (a statement right after a return, break or
// continue), must-use err (an err local nothing reads), a defer changing what a
// return returns, definite assignment (no read-before-init of a pointer, a
// slice or a `void` scalar), the void checks, literal ranges and constants
// that can't be known before the program runs.

// Entry point — called post-check (after build_call_graph). Walks every source
// function and raises the intraprocedural diagnostics it owns. Takes the Checker
// purely as the error sink (check_error); the analysis itself reads only the
// durable Checked_Program.
// (`void_defaults`: the spans of params' `void` defaults the checker reported,
// tc_void_defaults.)
flow_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program, void_defaults: map[Span]bool) {
    // Missing-return reads the program graph's runs, built from a clean check.
    graphed := len(checked.code.codes) > 0
    if graphed {
        flow_check_unreachable(c, checked)
        flow_check_literal_ranges(c, checked)
        flow_check_unused(c, checked)
        flow_check_init(c, checked)
        flow_check_defer_writes(c, checked)
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
        if graphed && flow_missing_return(checked, ft) {
            name := ft.source_name if ft.source_name != "" else ft.name
            check_error(c, ft.body_span, TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, name)
        }
    }
}

// Missing-return: a non-void function whose first return isn't `any` and whose
// returns aren't all-err must return on every path: no path through its runs
// reaches the synthetic return that ends its body (graph_falls_off).
flow_missing_return :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> bool {
    if len(ft.return_types) == 0 { return false }       // void
    if is_any(ft.return_types[0]) { return false }      // unresolved generic return
    if all_err_returns(ft.return_types) { return false } // all-err can fall off (.Ok fill)
    g := checked.code.funs[ft] or_else nil
    if g == nil { fmt.panicf("missing return: '%s' has no code", ft.name) }
    return graph_falls_off(g, 0)
}

// Unreachable code: a statement right after a return, break or continue (the
// graph records the first of each stretch). Codegen would put it after the
// terminator.
flow_check_unreachable :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for span in checked.code.unreachable {
        if span in seen { continue }
        seen[span] = true
        check_error(c, span, TYPE_UNREACHABLE_CODE)
    }
}

// Literal ranges: a literal whose type is its use's — the width its `:=`
// adopted, an operand's — must fit it, as one written at that type must
// (`first := -1` adopting a u16 index's width was 65535, never below 0).
flow_check_literal_ranges :: proc(c: ^Checker, checked: ^Checked_Program) {
    // (Generic instances share their template's spans: an error repeated at
    // one is reported once, check_error's rule; each instance is checked.)
    for g in checked.code.codes {
        for id in g.settled {
            v, ok := graph_value(g, id)
            if !ok || v.is_text { continue }
            check_value_range(c, v.float if v.is_float else f64(v.int), v.int, graph_type(g, id), g.origin[id])
        }
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
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for g in checked.code.codes {
        dest := make([]bool, len(g.kind), context.temp_allocator)   // where a whole write lands
        read := make([]bool, len(g.kind), context.temp_allocator)
        for k, id in g.kind {
            if k != .Op { continue }
            if d := graph_whole_write_dest(g, Node_Id(id)); d != NO_NODE { dest[d] = true }
        }
        for k, id in g.kind {
            if k == .Op && g.op[id] == .Var && !dest[id] && g.refers[id] != NO_NODE { read[g.refers[id]] = true }
        }
        for k, id in g.kind {
            if k != .Local || g.written[id] != .Explicit || read[id] || !is_err_type(graph_type(g, Node_Id(id))) { continue }
            // Declared by a statement, as `e := f()` or `v, e := f()`: not a loop's
            // variable or a match arm's binding.
            s := g.stmt[id]
            if s < 0 || (g.stmts[s].kind != .Decl && g.stmts[s].kind != .Destructure) { continue }
            span := g.origin[id]
            if span in seen { continue }
            seen[span] = true
            check_error(c, span, TYPE_UNUSED_ERR, graph_name(g, Node_Id(id)))
        }
    }
}

// --- defers and returned values -------------------------------------------
// A return takes its values, then the defers it leaves run. One of those
// defers changing a local the return returns — writing it, a field or an
// element of it, or taking its address — would change what the caller gets
// or not depending on how the value travels (a copy, or built in place), so
// it is an error. A value the return computes is no local; a write through a
// pointer that aliases one is not seen (field-insensitive, like escape).
flow_check_defer_writes :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    runs, block: [dynamic]i32
    defer { delete(runs); delete(block) }
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }
        g := checked.code.funs[ft] or_else nil
        node := Node_Id(0)
        if g == nil || g.kind[node] != .Fun { continue }
        clear(&runs)
        own := graph_code_runs(g, node, &runs)
        for r in runs[:own] {
            ops := graph_run(g, int(r))
            ret := ops[len(ops) - 1]
            if g.op[ret] != .Return { continue }
            // The defers it runs: the run defers just before it.
            for k := len(ops) - 2; k >= 0; k -= 1 {
                if g.op[ops[k]] == .Arena_Reset { continue }
                if g.op[ops[k]] != .Run_Defer { break }
                clear(&block)
                graph_code_runs(g, g.defer_of[ops[k]], &block)
                flow_defer_writes(c, g, ret, block[:], &seen)
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
                check_error(c, span, TYPE_DEFER_CHANGES_RETURNED, graph_name(g, v), span_line(g.origin[ret]))
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

// What can be unset in one fun, and who reads what: arrays by `id - node`
// over the fun's subtree.
@(private="file")
Init :: struct {
    g:       ^Program_Graph,
    node:    Node_Id,
    own:     []i32,            // a local's own bit; -1 when it can't be unset
    fields:  [][2]i32,         // a struct local's fields that can be unset: [first, count) of field_of
    field_of: [dynamic]Init_Field,
    alias:   map[Node_Id]Node_Id,   // a pointer local → the local it always points at
    user:    []Node_Id,        // an operation → the one that takes its output (NO_NODE: none)
    words:   int,
    c:       ^Checker,
    seen:    ^map[Span]bool,   // reads reported (generic instances share spans)
}

@(private="file")
Init_Field :: struct {
    name: string,
    bit:  i32,
}

flow_check_init :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }
        g := checked.code.funs[ft] or_else nil
        node := Node_Id(0)
        if g == nil { continue }
        flow_init_fun(c, g, node, &seen)
    }
}

@(private="file")
flow_init_fun :: proc(c: ^Checker, g: ^Program_Graph, node: Node_Id, seen: ^map[Span]bool) {
    runs: [dynamic]i32
    defer delete(runs)
    graph_code_runs(g, node, &runs)
    if len(runs) == 0 { return }

    size := int(graph_last(g, node) - node) + 1
    s := Init{g = g, c = c, seen = seen, node = node}
    s.own = make([]i32, size)
    s.fields = make([][2]i32, size)
    defer { delete(s.own); delete(s.fields); delete(s.field_of); delete(s.alias); delete(s.user) }
    slice.fill(s.own, -1)

    // What can be unset: its locals that are pointers, slices or scalars, and
    // the pointer and slice fields of its struct locals that have no default.
    bits: i32 = 0
    end := graph_last(g, node)
    for id := node + 1; id <= end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Local:
            if g.written[id] != .Explicit { continue }
        case:
            continue
        }
        base := distinct_base(graph_type(g, id))
        if flow_can_be_unset(base) {
            s.own[id - node] = bits
            bits += 1
        } else if sd := as_scope_body(base); sd != nil {
            first := i32(len(s.field_of))
            for &f in sd.fields {
                if field_has_default(f) || !flow_field_can_be_unset(f.type_) { continue }
                append(&s.field_of, Init_Field{f.name, bits})
                bits += 1
            }
            s.fields[id - node] = {first, i32(len(s.field_of)) - first}
        }
    }
    if bits == 0 { return }
    s.words = (int(bits) + 63) / 64

    // Who takes each operation's output, and which pointers are aliases.
    s.user = make([]Node_Id, size)
    slice.fill(s.user, NO_NODE)
    not_alias: map[Node_Id]bool
    defer delete(not_alias)
    for r in runs {
        for op in graph_run(g, int(r)) {
            for o in graph_operands(g, op) {
                if o.op >= node && o.op <= graph_last(g, node) { s.user[o.op - node] = op }
            }
            // (A pointer every write of which is `&x`.)
            d := graph_whole_write_dest(g, op)
            if g.op[op] != .Write || d == NO_NODE { continue }
            v := g.refers[d]
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

    // The fixpoint: each run's entry state (nothing unset on entry).
    fl := run_flow_make(g, runs[:], s.words, bits_copy, bits_union)
    defer run_flow_free(&fl)
    state := make([]u64, s.words)
    defer delete(state)
    run_flow_solve(&fl, state, &s, proc(s: ^Init, ri: int, op: Node_Id, state: []u64) { flow_init_op(s, op, state, false) })

    // The reads, against the fixpoint, in the order the runs list them.
    for r, ri in runs {
        if !fl.entered[ri] { continue }
        copy(state, fl.in_state[ri])
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
// slice.
@(private="file")
flow_field_can_be_unset :: proc(t: Type) -> bool {
    #partial switch _ in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice: return true
    }
    return false
}

// Whether declaration v is one of this fun's own.
@(private="file")
flow_own :: proc(s: ^Init, v: Node_Id) -> bool {
    return v > s.node && v <= graph_last(s.g, s.node)
}

// A variable's own bit: -1 when it can't be unset.
@(private="file")
flow_var_bit :: proc(s: ^Init, v: Node_Id) -> i32 {
    return s.own[v - s.node] if flow_own(s, v) else -1
}

// A struct variable's field's bit: -1 when it can't be unset.
@(private="file")
flow_field_bit :: proc(s: ^Init, v: Node_Id, field: string) -> i32 {
    if !flow_own(s, v) { return -1 }
    r := s.fields[v - s.node]
    for f in s.field_of[r[0]:r[0] + r[1]] { if f.name == field { return f.bit } }
    return -1
}

@(private="file")
flow_set :: proc(state: []u64, bit: i32, unset: bool) {
    if bit < 0 { return }
    if unset { bits_set(state, int(bit)) } else { bits_clear(state, int(bit)) }
}

@(private="file")
flow_is_unset :: proc(state: []u64, bit: i32) -> bool {
    return bit >= 0 && bits_has(state, int(bit))
}

// A variable as a whole, set or unset: itself, and (`fields`) every field.
@(private="file")
flow_set_var :: proc(s: ^Init, state: []u64, v: Node_Id, unset, fields_unset: bool) {
    if !flow_own(s, v) { return }
    flow_set(state, s.own[v - s.node], unset)
    r := s.fields[v - s.node]
    for f in s.field_of[r[0]:r[0] + r[1]] { flow_set(state, f.bit, fields_unset) }
}

// The struct variable and field a place names: `x.f`, or `p.f` through a
// pointer that aliases x.
@(private="file")
flow_field_place :: proc(s: ^Init, f: Node_Id) -> (var: Node_Id, field: string, via: Node_Id, ok: bool) {
    g := s.g
    if g.op[f] != .Field { return }
    base := graph_operands(g, f)[0].op
    if base == NO_NODE || g.kind[base] != .Op { return }
    #partial switch g.op[base] {
    case .Var:
        return g.refers[base], graph_name(g, f), NO_NODE, true
    case .Deref:
        p := graph_operands(g, base)[0].op
        if p == NO_NODE || g.op[p] != .Var { return }
        if target, is_alias := s.alias[g.refers[p]]; is_alias {
            return target, graph_name(g, f), g.refers[p], true
        }
    }
    return
}

// Who takes an operation's output; NO_NODE for none.
@(private="file")
flow_user :: proc(s: ^Init, op: Node_Id) -> Node_Id {
    return s.user[op - s.node] if op >= s.node && op <= graph_last(s.g, s.node) else NO_NODE
}

// Whether a place's output is read: not written to as a whole, not only
// addressed, not only a step toward a field.
@(private="file")
flow_read_by :: proc(s: ^Init, op: Node_Id) -> bool {
    g := s.g
    u := flow_user(s, op)
    if u == NO_NODE { return false }
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
        if reporting && flow_is_unset(state, flow_var_bit(s, g.refers[op])) && flow_read_by(s, op) {
            report(s, g.origin[op], TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE, graph_name(g, op))
        }
    case .Field:
        if !reporting { break }
        v, field, via, ok := flow_field_place(s, op)
        if !ok || !flow_is_unset(state, flow_field_bit(s, v, field)) { break }
        u := flow_user(s, op)
        if u == NO_NODE { break }
        if g.op[u] == .Write || g.op[u] == .Fill || g.op[u] == .Zero || g.op[u] == .Construct || g.op[u] == .Byte_Read {
            if graph_operands(g, u)[0].op == op { break }   // written, not read
        }
        if g.op[u] == .Address || g.op[u] == .Field || g.op[u] == .Swizzle { break }
        if via != NO_NODE {
            report(s, g.origin[op], TYPE_FIELD_ALIASED_VIA_USED_BEFORE, field, graph_name(g, v), graph_name(g, via))
        } else {
            report(s, g.origin[op], TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, field, graph_name(g, v))
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
                unset = val != NO_NODE && g.op[val] == .Const && graph_name(g, val) == "void"
                fields_unset = unset
            case .Zero:
                // A bare `p : ^T` or `s : []T` (a sized slice has its storage, a
                // bare scalar is zero).
                #partial switch _ in distinct_base(graph_type(g, v)) {
                case ^Type_Ptr, ^Type_Slice: unset = g.written[op] == .Synthetic && len(ops) == 1
                }
            case .Construct:
                // Built bare or from braces, a struct has only what it is given
                // (the braces' writes follow); a constructor call may set anything.
                fields_unset = g.written[op] == .Synthetic || strings.has_suffix(graph_name(g, op), "{}")
            }
            flow_set_var(s, state, v, unset, fields_unset)
        } else if v, field, _, ok := flow_field_place(s, d); ok {
            flow_set(state, flow_field_bit(s, v, field), false)
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
                flow_set_var(s, state, g.refers[p], false, false)
            } else if v, field, _, ok := flow_field_place(s, p); ok {
                flow_set(state, flow_field_bit(s, v, field), false)
            }
        case .Read:
            p := graph_operands(g, x)[0].op
            if p == NO_NODE || g.op[p] != .Var { continue }
            if target, is_alias := s.alias[g.refers[p]]; is_alias {
                flow_set_var(s, state, target, false, false)
            }
        }
    }
}

// --- constants -----------------------------------------------------------------
// A use of a constant whose value can't be known before the program runs
// (graph_fold_uses: a call in it, a struct's construction with arguments).

flow_check_constants :: proc(c: ^Checker, checked: ^Checked_Program) {
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    for e in checked.code.fold_errors {
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
    seen: map[Span]bool   // generic instances share their template's spans
    defer delete(seen)
    // (A parameter's default: the checker's, tc_void_defaults.)
    for sp in void_defaults { seen[sp] = true }
    // Every other: a void as written, where the operation that takes it
    // stores it — its type its use's.
    for g in checked.code.codes {
        for i in 0 ..< len(g.kind) {
            id := Node_Id(i)
            if g.kind[id] != .Op { continue }
            for o, k in graph_operands(g, id) {
                v := o.op
                if v == NO_NODE || g.op[v] != .Const || graph_name(g, v) != "void" { continue }
                if g.written[v] != .Explicit { continue }
                if where_, stored := void_where(g, id, k); stored {
                    void_error(c, &seen, g.origin[v], graph_type(g, v), where_)
                }
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
        case .Field:        return fmt.tprintf("field '%s'", graph_name(g, dest)), true
        case .Index, .View: return "an array element", true
        case .Deref:        return "a dereferenced pointer", true
        case .Var:
            // A struct body's field, and the slot an if-expression's
            // branches go into, are no variables.
            d := g.refers[dest]
            if d == NO_NODE { return "", false }
            if g.kind[d] == .Field { return fmt.tprintf("field '%s'", graph_name(g, d)), true }
            if g.kind[d] == .Local && g.written[d] == .Synthetic && graph_name(g, d) == "if" {
                return "a branch of an if-expression", true
            }
        }
    case .Call, .Construct:
        sig := graph_signature(g, op)
        if sig == nil || sig.calling_conv == .C { return "", false }
        // (A construction's first operand is where it builds; a call
        // through a function value's, the value.)
        n := k + 1 if g.op[op] == .Call && graph_called(g, op) != nil else k
        return fmt.tprintf("argument %d of '%s'", n, graph_name(g, op)), true
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
