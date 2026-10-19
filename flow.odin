package mara

import "core:fmt"
import "core:mem"
import "core:mem/virtual"
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

// What flow analysis found in one code (flow_code: the middle end runs it on
// each, middle.odin), kept until every code is analysed and then reported
// (flow_report) in the checks' own order: each
// over the program's codes in written order, or its funs in name order — as
// one pass over the whole program would. A check that reports a span once
// (a generic's instances share their template's) does so as it reports.
Flow_Pass :: struct {
    found:   map[^Program_Graph][dynamic]Flow_Finding,
    sources: map[^Type_Scope]bool,   // the checked source funs (whose codes the fun checks read)
    walk:    virtual.Arena,          // what a walk makes, until the next (flow_init_fun)
    pc:      ^Program_Code,          // the program's codes: a construction's constructor's (flow_ctor_unset)
    heap:    mem.Allocator,          // what outlives a walk: ...
    ctor_unset: map[^Type_Scope][]string,   // ... each struct's constructor's unset fields, once worked out
}

Flow_Finding :: struct {
    check: Flow_Check,
    span:  Span,
    msg:   string,
}

Flow_Check :: enum u8 { Literal_Range, Unused, Init, Defer_Write, Void, Missing_Return }

flow_pass_make :: proc(fns: []^Type_Scope, pc: ^Program_Code = nil) -> Flow_Pass {
    fp: Flow_Pass
    fp.pc, fp.heap = pc, context.allocator
    fp.ctor_unset = make(map[^Type_Scope][]string, allocator = fp.heap)
    for ft in fns {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); src { fp.sources[ft] = true }
    }
    if err := virtual.arena_init_growing(&fp.walk); err != nil {
        fmt.panicf("flow analysis: no arena for its walks (%v)", err)
    }
    return fp
}

flow_pass_free :: proc(fp: ^Flow_Pass) {
    virtual.arena_destroy(&fp.walk)
    delete(fp.ctor_unset)
    for _, list in fp.found { delete(list) }
    delete(fp.found)
    delete(fp.sources)
}

// One code's findings: its literals' ranges, its unused errs, the void it
// stores into pointers; a source fun's reads before assignment, its defers'
// writes to what it returns, and whether it falls off its end.
flow_code :: proc(fp: ^Flow_Pass, g: ^Program_Graph) {
    if g not_in fp.found { fp.found[g] = {} }   // (`&m[k]` takes no missing key's place)
    found := &fp.found[g]
    flow_literal_ranges(g, found)
    flow_unused(g, found)
    if ts, is_scope := graph_type(g, 0).(^Type_Scope); is_scope && fp.sources[ts] {
        flow_init_fun(fp, g, found)
        if graph_kind_of(g, 0) == .Fun { flow_defers(g, found) }
        if !scope_body_is_empty(ts) && flow_missing_return(g, ts) {
            name := ts.source_name if ts.source_name != "" else ts.name
            append(found, Flow_Finding{.Missing_Return, ts.body_span, fmt.aprintf(TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, name)})
        }
    }
    flow_void(g, found)
}

// Every code's findings reported, check by check.
flow_report :: proc(c: ^Checker, checked: ^Checked_Program, passes: []^Flow_Pass, fns: []^Type_Scope, void_defaults: map[Span]bool) {
    // (Each code is one pass's: their findings, together.)
    fp := passes[0]
    for other in passes[1:] {
        for g, list in other.found { fp.found[g] = list }
        clear(&other.found)
    }
    codes := checked.code.codes[:]
    graphed := len(codes) > 0
    of_codes :: proc(c: ^Checker, fp: ^Flow_Pass, codes: []^Program_Graph, check: Flow_Check, seen: ^map[Span]bool = nil) {
        for g in codes { flow_report_found(c, fp.found[g][:], check, seen) }
    }
    of_funs :: proc(c: ^Checker, checked: ^Checked_Program, fp: ^Flow_Pass, fns: []^Type_Scope, check: Flow_Check, seen: ^map[Span]bool = nil) {
        for ft in fns {
            if ft == nil || !fp.sources[ft] { continue }
            if g := checked.code.funs[ft] or_else nil; g != nil { flow_report_found(c, fp.found[g][:], check, seen) }
        }
    }
    if graphed {
        // (Generic instances share their template's spans: check_error
        // reports one once — and the checks that say so, once a span.)
        for span in checked.code.unreachable { check_error(c, span, TYPE_UNREACHABLE_CODE) }
        for gap in checked.code.literal_gaps {
            check_error(c, gap.span, TYPE_VARIANT_LITERAL_LEAVES_UNSET if gap.variant else TYPE_LITERAL_LEAVES_UNSET, gap.field, gap.owner, gap.owner)
        }
        of_codes(c, fp, codes, .Literal_Range)
        of_codes(c, fp, codes, .Unused)
        reads: map[Span]bool
        defer delete(reads)
        of_funs(c, checked, fp, fns, .Init, &reads)
        writes: map[Span]bool
        defer delete(writes)
        of_funs(c, checked, fp, fns, .Defer_Write, &writes)
        voids: map[Span]bool   // (a parameter's default: the checker's, tc_void_defaults)
        defer delete(voids)
        for sp in void_defaults { voids[sp] = true }
        of_codes(c, fp, codes, .Void, &voids)
        for e in checked.code.fold_errors { check_error(c, e.span, TYPE_CONST_NOT_COMPILE_TIME, e.name) }
    }
    for ft in fns {
        if ft == nil { continue }
        // Source bodies only: intrinsics/foreigns have no Mara statements. An
        // empty one declares a shape (`Arena`'s methods, which a `~Arena`
        // param's type must have): nothing to return from.
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        if scope_body_is_empty(ft) || !graphed { continue }
        g := checked.code.funs[ft] or_else nil
        if g == nil { fmt.panicf("missing return: '%s' has no code", ft.name) }
        flow_report_found(c, fp.found[g][:], .Missing_Return)
    }
}

// One code's findings of one check, reported (`seen`: the spans reported,
// one a span).
@(private="file")
flow_report_found :: proc(c: ^Checker, found: []Flow_Finding, check: Flow_Check, seen: ^map[Span]bool = nil) {
    for f in found {
        if f.check != check { continue }
        if seen != nil {
            if f.span in seen^ { continue }
            seen^[f.span] = true
        }
        check_error(c, f.span, "%s", f.msg)
    }
}

// Missing-return: a non-void function whose first return isn't `any` and whose
// returns aren't all-err must return on every path: no path through its runs
// reaches the synthetic return that ends its body (graph_falls_off).
flow_missing_return :: proc(g: ^Program_Graph, ft: ^Type_Scope) -> bool {
    if len(ft.return_types) == 0 { return false }       // void
    if is_any(ft.return_types[0]) { return false }      // unresolved generic return
    if all_err_returns(ft.return_types) { return false } // all-err can fall off (.Ok fill)
    return graph_falls_off(g, 0)
}

// Unreachable code: a statement right after a return, break or continue (the
// graph records the first of each stretch, Program_Code.unreachable; flow_report
// reports them). Codegen would put it after the terminator.

// Literal ranges: a literal whose type is its use's — the width its `:=`
// adopted, an operand's — must fit it, as one written at that type must
// (`first := -1` adopting a u16 index's width was 65535, never below 0).
@(private="file")
flow_literal_ranges :: proc(g: ^Program_Graph, found: ^[dynamic]Flow_Finding) {
    // (Generic instances share their template's spans: an error repeated at
    // one is reported once, check_error's rule; each instance is checked.)
    for id in g.settled {
        v, ok := graph_value(g, id)
        if !ok || v.is_text { continue }
        if msg := value_range_error(v.float if v.is_float else f64(v.int), v.int, graph_type(g, id)); msg != "" {
            append(found, Flow_Finding{.Literal_Range, graph_origin(g, id), msg})
        }
    }
}

// --- must-use-err ---------------------------------------------------------
// An err-typed local that is declared but never read — not checked, not
// propagated with `?` (which leaves no binding), not discarded with `_` — is an
// error. On the graph a declaration is read where a leaf names it,
// except where a whole write lands (`e = f()` writes e, it reads nothing);
// refers-to has resolved shadowing, and a read in a nested block or a defer's
// block is a read like any other.
@(private="file")
flow_unused :: proc(g: ^Program_Graph, found: ^[dynamic]Flow_Finding) {
    // (A code of no err local, most: nothing to find.)
    any_err := false
    for k, id in g.kind {
        if k == .Local && g.written[id] == .Explicit && is_err_type(graph_type(g, Node_Id(id))) { any_err = true; break }
    }
    if !any_err { return }
    dest := make([]bool, len(g.leaves), context.temp_allocator)   // the leaves a whole write lands on
    read := make([]bool, len(g.kind), context.temp_allocator)
    for k, id in g.kind {
        if k != .Op { continue }
        if d := graph_whole_write_dest(g, Node_Id(id)); d != NO_NODE { dest[d - LEAF] = true }
    }
    for l, i in g.leaves {
        if !dest[i] { read[l.decl] = true }
    }
    for k, id in g.kind {
        if k != .Local || g.written[id] != .Explicit || read[id] || !is_err_type(graph_type(g, Node_Id(id))) { continue }
        // Declared by a statement, as `e := f()` or `v, e := f()`: not a loop's
        // variable or a match arm's binding.
        if s := graph_stmt(g, Node_Id(id)).kind; s != .Decl && s != .Destructure { continue }
        append(found, Flow_Finding{.Unused, graph_origin(g, Node_Id(id)), fmt.aprintf(TYPE_UNUSED_ERR, graph_name(g, Node_Id(id)))})
    }
}

// --- defers and returned values -------------------------------------------
// A return takes its values, then the defers it leaves run. One of those
// defers changing a local the return returns — writing it, a field or an
// element of it, or taking its address — would change what the caller gets
// or not depending on how the value travels (a copy, or built in place), so
// it is an error. A value the return computes is no local; a write through a
// pointer that aliases one is not seen (field-insensitive, like escape).
@(private="file")
flow_defers :: proc(g: ^Program_Graph, found: ^[dynamic]Flow_Finding) {
    runs, block: [dynamic]i32
    defer { delete(runs); delete(block) }
    own := graph_code_runs(g, 0, &runs)
    for r in runs[:own] {
        ops := graph_run(g, int(r))
        ret := ops[len(ops) - 1]
        if graph_op_of(g, ret) != .Return { continue }
        // The defers it runs: the run defers just before it.
        for k := len(ops) - 2; k >= 0; k -= 1 {
            if graph_op_of(g, ops[k]) == .Arena_Reset { continue }
            if graph_op_of(g, ops[k]) != .Run_Defer { break }
            clear(&block)
            graph_code_runs(g, g.defer_of[ops[k]], &block)
            flow_defer_writes(g, ret, block[:], found)
        }
    }
}

// A defer block's changes to what `ret` returns.
@(private="file")
flow_defer_writes :: proc(g: ^Program_Graph, ret: Node_Id, block: []i32, found: ^[dynamic]Flow_Finding) {
    for o in graph_operands(g, ret) {
        v := flow_returned_local(g, o.op)
        if v == NO_NODE { continue }
        for r in block {
            for op in graph_run(g, int(r)) {
                #partial switch graph_op_of(g, op) {
                case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Carve, .Address:
                case:
                    continue
                }
                ops := graph_operands(g, op)
                if len(ops) == 0 || flow_storage_root(g, ops[0].op) != v { continue }
                span := graph_origin(g, op)
                append(found, Flow_Finding{.Defer_Write, span, fmt.aprintf(TYPE_DEFER_CHANGES_RETURNED, graph_name(g, v), span_line(graph_origin(g, ret)))})
            }
        }
    }
}

// The local a returned value is, as read (through an implied widening); none
// for a value computed.
@(private="file")
flow_returned_local :: proc(g: ^Program_Graph, v: Node_Id) -> Node_Id {
    v := v
    for v != NO_NODE && graph_op_of(g, v) == .Cast && graph_written(g, v) == .Implied { v = graph_operands(g, v)[0].op }
    if v == NO_NODE || graph_op_of(g, v) != .Read { return NO_NODE }
    root := flow_storage_root(g, graph_operands(g, v)[0].op)
    if root == NO_NODE || (graph_kind_of(g, root) != .Local && graph_kind_of(g, root) != .Result) { return NO_NODE }
    return root
}

// The variable whose own storage a place is in: through fields, elements and
// views, not through a pointer.
@(private="file")
flow_storage_root :: proc(g: ^Program_Graph, p: Node_Id) -> Node_Id {
    for id := p; id != NO_NODE; {
        #partial switch graph_op_of(g, id) {
        case .Var:
            return graph_refers(g, id)
        case .Field, .Index, .View, .Swizzle, .Variant, .Slice:
            id = graph_operands(g, id)[0].op
        case:
            return NO_NODE
        }
    }
    return NO_NODE
}

// --- definite assignment --------------------------------------------------
// Reading what holds no value yet is an error: a pointer, a slice or a scalar
// set to `void`; a struct declared bare (`n : Node` — its constructor doesn't
// run: it is unset until written), any field of it — a struct field's own
// fields by their path, `n.pos.x` — read before it's written, or the struct
// read whole while one isn't (a partial array's zero, an empty one, is a
// value: never unset). A literal (`n := Node{next = p}`) runs no
// constructor: what it doesn't give is unset (where nothing can write it
// after, lowering says so at the literal: Literal_Gap). A construction (`n :=
// Node()`) leaves unset what its constructor does: its struct's fields
// declared bare that its body never writes (flow_ctor_unset). In a struct's own code, its
// constructor, its fields are its variables: a bare one is unset there too.
// Forward dataflow over each fun's runs: the state is what may be unset,
// unioned at joins, so a read is flagged when some path reaches it unset.
// Loops iterate to their fixpoint, and a defer's block sees the state at each
// exit that runs it.
//
// A call handed a variable's address (`init(&h)`, `load(&h.buf)`, or a pointer
// known to alias it) may assign through it: from there it counts as set — so
// does an address taken any other way but for an alias. An alias is a pointer
// every write of which is `&x`: `it = &root` makes `it.next` read
// `root.next`. An array's elements count as one: a write to any sets it.

FLOW_FIELD_DEPTH :: 6     // how deep a struct variable's fields are followed, by path
FLOW_FIELD_BITS  :: 512   // the most bits a variable's fields get: past them, a struct field is one

// What can be unset in one fun, and who reads what: arrays by `id - node`
// over the fun's subtree.
@(private="file")
Init :: struct {
    g:       ^Program_Graph,
    fp:      ^Flow_Pass,
    own:     []i32,            // a local's own bit + 1; 0 when it can't be unset
    fields:  [][2]i32,         // a struct local's fields: [first, count) of field_of
    field_of: [dynamic]Init_Field,
    alias:   map[Node_Id]Node_Id,   // a pointer local → the local it always points at
    user:    []Node_Id,        // an operation → the one that takes its output (0: none)
    words:   int,
    found:   ^[dynamic]Flow_Finding,   // the reads found unset
    in_ctor: bool,             // a struct's own code: its fields its variables
    scratch: mem.Allocator,    // a place's path, worked out: the walk's
}

// A struct variable's field, by its path from the variable (`pos.x`).
@(private="file")
Init_Field :: struct {
    path: string,
    bit:  i32,
}

@(private="file")
flow_init_fun :: proc(fp: ^Flow_Pass, g: ^Program_Graph, found: ^[dynamic]Flow_Finding) {
    // (What the fun's walk makes is `walk`'s, the last fun's freed; the
    // diagnostics, the reads', outlive it.)
    in_ctor := graph_kind_of(g, 0) == .Struct
    if !flow_init_unsets(fp, g, in_ctor) { return }
    kept := context.allocator
    virtual.arena_free_all(&fp.walk)
    context.allocator = virtual.arena_allocator(&fp.walk)
    runs: [dynamic]i32
    graph_code_runs(g, 0, &runs)
    if len(runs) == 0 { return }

    size := int(g.end) + 1
    s := Init{g = g, fp = fp, found = found, in_ctor = in_ctor, scratch = context.allocator}
    s.own = make([]i32, size)
    s.fields = make([][2]i32, size)

    // What can be unset: its locals that are pointers, slices or scalars, and
    // every field of its struct locals (a constructor's, its own fields).
    bits: i32 = 0
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Local:
            if g.written[id] != .Explicit { continue }
        case .Field:
            if !in_ctor { continue }
        case:
            continue
        }
        base := distinct_base(graph_type(g, id))
        if flow_can_be_unset(base) {
            s.own[id] = bits + 1
            bits += 1
        } else if sd := as_struct_body(base); sd != nil {
            first := i32(len(s.field_of))
            flow_add_fields(&s, sd, "", 0, &bits)
            s.fields[id] = {first, i32(len(s.field_of)) - first}
        }
    }
    if bits == 0 { return }
    s.words = (int(bits) + 63) / 64

    // Who takes each operation's output, and which pointers are aliases.
    s.user = make([]Node_Id, size)
    not_alias: map[Node_Id]bool
    for r in runs {
        for op in graph_run(g, int(r)) {
            for o in graph_operands(g, op) {
                if o.op >= 0 && o.op <= g.end { s.user[o.op] = op }
            }
            // (A pointer every write of which is `&x`.)
            d := graph_whole_write_dest(g, op)
            if graph_op_of(g, op) != .Write || d == NO_NODE { continue }
            v := graph_refers(g, d)
            val := graph_operands(g, op)[1].op
            target := NO_NODE
            if val != NO_NODE && graph_op_of(g, val) == .Address {
                if p := graph_operands(g, val)[0].op; graph_is_leaf(p) { target = graph_refers(g, p) }
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
    state := make([]u64, s.words)
    run_flow_solve(&fl, state, &s, proc(s: ^Init, ri: int, op: Node_Id, state: []u64) { flow_init_op(s, op, state, false) })

    // The reads, against the fixpoint, in the order the runs list them.
    context.allocator = kept
    run_flow_replay(&fl, &s, proc(s: ^Init, ri: int, op: Node_Id, state: []u64) { flow_init_op(s, op, state, true) })
}

// A struct's fields, each a bit by its path past `prefix` — a struct field's
// own fields instead, while they're few and not too deep.
@(private="file")
flow_add_fields :: proc(s: ^Init, sd: ^Scope_Body, prefix: string, depth: int, bits: ^i32) {
    for &f in sd.fields {
        if strings.has_prefix(f.name, "__") { continue }   // (a variant's tag and padding)
        if _, pa := distinct_base(f.type_).(^Type_Partial_Array); pa { continue }   // (its zero an empty one: a value)
        path := f.name if prefix == "" else strings.concatenate({prefix, ".", f.name})
        if sub := as_struct_body(distinct_base(f.type_)); sub != nil && depth + 1 < FLOW_FIELD_DEPTH && int(bits^) + len(sub.fields) <= FLOW_FIELD_BITS {
            flow_add_fields(s, sub, path, depth + 1, bits)
            continue
        }
        append(&s.field_of, Init_Field{path, bits^})
        bits^ += 1
    }
}

// Whether anything in a code can leave one of its variables unset — `void`
// written to it, a bare pointer, slice or struct, a construction whose
// constructor leaves a field unset; in a constructor, a bare field. Without,
// nothing is ever unset: there's no unset read to find.
@(private="file")
flow_init_unsets :: proc(fp: ^Flow_Pass, g: ^Program_Graph, in_ctor: bool) -> bool {
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Op:
        case:
            continue
        }
        #partial switch g.op[id] {
        case .Write, .Zero, .Construct:
        case:
            continue
        }
        ops := graph_operands(g, id)
        d := ops[0].op if len(ops) > 0 else NO_NODE
        if g.op[id] == .Construct {
            if flow_is_literal(g, id) || len(flow_ctor_unset(fp, graph_called(g, id))) > 0 { return true }
            continue
        }
        if !graph_is_leaf(d) { continue }   // (only a whole variable is made unset)
        v := graph_refers(g, d)
        if v <= 0 || v > g.end { continue }   // (its own only: flow_own)
        #partial switch g.op[id] {
        case .Write:
            val := ops[1].op
            if val != NO_NODE && graph_op_of(g, val) == .Const && graph_name(g, val) == "void" { return true }
        case .Zero:
            if g.written[id] != .Synthetic && !flow_is_literal(g, id) { continue }
            if in_ctor && g.kind[v] == .Field { return true }
            base := distinct_base(graph_type(g, v))
            #partial switch _ in base {
            case ^Type_Ptr, ^Type_Slice: return true
            }
            if as_struct_body(base) != nil { return true }
        }
    }
    return false
}

// Whether a variable of this type can be read unset: a pointer, a slice, or a
// scalar (unset only by `void` — or, a constructor's field, declared bare).
@(private="file")
flow_can_be_unset :: proc(base: Type) -> bool {
    #partial switch _ in base {
    case ^Type_Ptr, ^Type_Slice: return true
    case Type_Error:             return false
    case Type_Bool, Type_Utf8, Type_Byte, Type_CString, Type_Err, Type_Atom: return true
    }
    return is_numeric(base)
}

// What a struct's constructor leaves unset, by path from what it builds: its
// fields declared bare that its code never writes — nor hands out the address
// of — and, of a field it constructs whole, what that field's constructor
// leaves unset and its code doesn't write after (`wrap := Wrap{data = d}`).
// Worked out once a struct (each worker's own), from its code.
flow_ctor_unset :: proc(fp: ^Flow_Pass, ts: ^Type_Scope, depth := 0) -> []string {
    if ts == nil || fp.pc == nil || depth > FLOW_FIELD_DEPTH { return nil }
    if known, ok := fp.ctor_unset[ts]; ok { return known }
    fp.ctor_unset[ts] = nil   // (while it's worked out: a struct that builds itself leaves nothing)
    g := graph_fun_code(fp.pc, ts)
    if g == nil || graph_kind_of(g, 0) != .Struct { return nil }
    bare := make(map[Node_Id]bool, allocator = context.temp_allocator)
    written := make(map[Node_Id]bool, allocator = context.temp_allocator)
    built := make(map[Node_Id]^Type_Scope, allocator = context.temp_allocator)
    paths := make([dynamic]string, context.temp_allocator)   // the fields' parts written, by path (not a construction's own)
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Op:
        case:
            continue
        }
        #partial switch g.op[id] {
        case .Write, .Fill, .Byte_Read, .Zero, .Construct, .Address, .Arena_Alloc:
        case:
            continue
        }
        ops := graph_operands(g, id)
        if len(ops) == 0 { continue }
        d := ops[0].op
        if g.op[id] == .Zero && g.written[id] == .Synthetic && graph_is_leaf(d) {
            if v := graph_refers(g, d); v > 0 && v <= g.end && g.kind[v] == .Field {
                // (A partial array's zero is an empty one: a value.)
                if _, pa := distinct_base(graph_type(g, v)).(^Type_Partial_Array); !pa { bare[v] = true }
            }
            continue
        }
        root, path := flow_ctor_path(g, d)
        if root <= 0 || root > g.end || g.kind[root] != .Field { continue }
        written[root] = true
        if g.op[id] == .Construct && graph_is_leaf(d) {
            built[root] = graph_called(g, id)
        } else {
            append(&paths, path)
        }
    }
    unset := make([dynamic]string, fp.heap)
    for v in bare {
        if !written[v] { append(&unset, graph_name(g, v)) }
    }
    for v, st in built {
        nested: for p in flow_ctor_unset(fp, st, depth + 1) {
            at := strings.concatenate({graph_name(g, v), ".", p}, context.temp_allocator)
            for w in paths {
                if w == at || (len(at) > len(w) && strings.has_prefix(at, w) && at[len(w)] == '.') { continue nested }
            }
            append(&unset, strings.clone(at, fp.heap))
        }
    }
    slice.sort(unset[:])
    fp.ctor_unset[ts] = unset[:]
    return unset[:]
}

// The constructor's field a place is in, and the place's path from it
// (`wrap.data`; past an element, the field it's in).
@(private="file")
flow_ctor_path :: proc(g: ^Program_Graph, p: Node_Id) -> (root: Node_Id, path: string) {
    names := make([dynamic]string, context.temp_allocator)
    for id := p; id != NO_NODE; {
        if graph_is_leaf(id) {
            root = graph_refers(g, id)
            break
        }
        if graph_kind_of(g, id) != .Op { return NO_NODE, "" }
        #partial switch graph_op_of(g, id) {
        case .Var:
            root = graph_refers(g, id)
            id = NO_NODE
            continue
        case .Field:
            append(&names, graph_name(g, id))
        case .Index, .View, .Slice, .Swizzle, .Variant:
            clear(&names)
        case:
            return NO_NODE, ""
        }
        id = graph_operands(g, id)[0].op
    }
    if root <= 0 || root > g.end { return NO_NODE, "" }
    append(&names, graph_name(g, root))
    slice.reverse(names[:])
    return root, strings.join(names[:], ".", context.temp_allocator)
}

// Whether an operation starts a literal: `{}` — its fields unset till its
// entries write them (a struct's zero; a variant's, its tag).
@(private="file")
flow_is_literal :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    name := graph_name(g, op)
    return len(name) >= 2 && name[len(name) - 2:] == "{}"
}

// Whether declaration v is one of this fun's own.
@(private="file")
flow_own :: proc(s: ^Init, v: Node_Id) -> bool {
    return v > 0 && v <= s.g.end
}

// A variable's own bit: -1 when it can't be unset.
@(private="file")
flow_var_bit :: proc(s: ^Init, v: Node_Id) -> i32 {
    return s.own[v] - 1 if flow_own(s, v) else -1
}

// A struct variable's fields, by path.
@(private="file")
flow_var_fields :: proc(s: ^Init, v: Node_Id) -> []Init_Field {
    if !flow_own(s, v) { return nil }
    r := s.fields[v]
    return s.field_of[r[0]:r[0] + r[1]]
}

// Whether a field's path and a place's touch: the same, one inside the other.
@(private="file")
flow_paths_meet :: proc(field, place: string) -> bool {
    if place == "" || field == place { return true }
    if len(field) > len(place) { return strings.has_prefix(field, place) && field[len(place)] == '.' }
    return strings.has_prefix(place, field) && place[len(field)] == '.'
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
    flow_set(state, s.own[v] - 1, unset)
    for f in flow_var_fields(s, v) { flow_set(state, f.bit, fields_unset) }
}

// The fields of v a place at `path` touches, set or unset ("": all of them).
@(private="file")
flow_set_path :: proc(s: ^Init, state: []u64, v: Node_Id, path: string, unset: bool) {
    for f in flow_var_fields(s, v) {
        if flow_paths_meet(f.path, path) { flow_set(state, f.bit, unset) }
    }
}

// A construction of `callee` at v's `path` ("": v itself): what its
// constructor leaves unset is, the rest set.
@(private="file")
flow_construct :: proc(s: ^Init, state: []u64, v: Node_Id, path: string, callee: ^Type_Scope) {
    if path == "" { flow_set_var(s, state, v, false, false) } else { flow_set_path(s, state, v, path, false) }
    for p in flow_ctor_unset(s.fp, callee) {
        at := p if path == "" else strings.concatenate({path, ".", p}, s.scratch)
        flow_set_path(s, state, v, at, true)
    }
}

// The first of v's fields a place at `path` touches that is unset: its path.
@(private="file")
flow_first_unset :: proc(s: ^Init, state: []u64, v: Node_Id, path: string) -> (string, bool) {
    for f in flow_var_fields(s, v) {
        if flow_paths_meet(f.path, path) && flow_is_unset(state, f.bit) { return f.path, true }
    }
    return "", false
}

// The struct variable and the path of its fields a place names: `x.pos.y` —
// or `p.pos.y` through a pointer that aliases x. Past an element or a view
// (`x.list[i].n`), the field it's in (`list`): its elements count as one.
@(private="file")
flow_place_path :: proc(s: ^Init, p: Node_Id) -> (var: Node_Id, path: string, via: Node_Id, ok: bool) {
    g := s.g
    via = NO_NODE
    names := make([dynamic]string, s.scratch)
    for id := p; id != NO_NODE; {
        if graph_is_leaf(id) {
            var = graph_refers(g, id)
            break
        }
        if graph_kind_of(g, id) != .Op { return }
        #partial switch graph_op_of(g, id) {
        case .Var:
            var = graph_refers(g, id)
            id = NO_NODE
            continue
        case .Field:
            append(&names, graph_name(g, id))
        case .Index, .View, .Slice, .Swizzle, .Variant:
            clear(&names)   // (inside an element: the field it's in, as a whole)
        case .Deref:
            ptr := graph_operands(g, id)[0].op
            if !graph_is_leaf(ptr) { return }
            target, is_alias := s.alias[graph_refers(g, ptr)]
            if !is_alias { return }
            var, via = target, graph_refers(g, ptr)
            id = NO_NODE
            continue
        case:
            return
        }
        id = graph_operands(g, id)[0].op
    }
    if var == NO_NODE { return }
    slice.reverse(names[:])
    return var, strings.join(names[:], ".", s.scratch), via, true
}

// Who takes an operation's output; NO_NODE for none.
@(private="file")
flow_user :: proc(s: ^Init, op: Node_Id) -> Node_Id {
    if op < 0 || op > s.g.end { return NO_NODE }
    if u := s.user[op]; u != 0 { return u }   // (0: none — no operation is the code's root)
    return NO_NODE
}

// Whether op names a place step: a field, an element, a view of what's
// below it.
@(private="file")
flow_is_step :: proc(g: ^Program_Graph, op: Node_Id) -> bool {
    #partial switch graph_op_of(g, op) {
    case .Field, .Index, .View, .Slice, .Swizzle, .Variant: return true
    }
    return false
}

// Whether operation u reads its k-th operand, a place: not written to as a
// whole, not only addressed, not only a step toward a field.
@(private="file")
flow_reads :: proc(g: ^Program_Graph, u: Node_Id, k: int) -> bool {
    #partial switch graph_op_of(g, u) {
    case .Address, .Arena_Alloc, .Field, .Swizzle, .Variant:
        return false
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
        return k != 0
    }
    return true
}

// One operation's effect on the state; reporting, its unset reads too.
@(private="file")
flow_init_op :: proc(s: ^Init, op: Node_Id, state: []u64, reporting: bool) {
    g := s.g
    report :: proc(s: ^Init, span: Span, msg: string, args: ..any) {
        append(s.found, Flow_Finding{.Init, span, fmt.aprintf(msg, ..args)})
    }
    if reporting {   // (its variables read, as they are when it runs: one whole, any field unset)
        for o, k in graph_operands(g, op) {
            if !graph_is_leaf(o.op) || !flow_reads(g, op, k) { continue }
            v := graph_refers(g, o.op)
            if flow_is_unset(state, flow_var_bit(s, v)) {
                report(s, graph_origin(g, o.op), TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE, graph_name(g, o.op))
            } else if field, unset := flow_first_unset(s, state, v, ""); unset {
                report(s, graph_origin(g, o.op), TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, field, graph_name(g, o.op))
            }
        }
    }
    #partial switch graph_op_of(g, op) {
    case .Field, .Index, .View, .Slice, .Swizzle, .Variant:
        // (The top of a place — `x.pos.y`, `x.list[i]` — as what takes it uses it.)
        if !reporting || (graph_op_of(g, op) != .Field && graph_op_of(g, op) != .Index) { break }
        u := flow_user(s, op)
        if u == NO_NODE || flow_is_step(g, u) { break }
        uk := graph_op_of(g, u)
        if uk == .Address || uk == .Arena_Alloc { break }
        if (uk == .Write || uk == .Fill || uk == .Zero || uk == .Construct || uk == .Byte_Read) && graph_operands(g, u)[0].op == op { break }   // written, not read
        v, path, via, ok := flow_place_path(s, op)
        if !ok { break }
        field, unset := flow_first_unset(s, state, v, path)
        if !unset { break }
        if via != NO_NODE {
            report(s, graph_origin(g, op), TYPE_FIELD_ALIASED_VIA_USED_BEFORE, field, graph_name(g, v), graph_name(g, via))
        } else {
            report(s, graph_origin(g, op), TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, field, graph_name(g, v))
        }
    case .Address:
        // An address taken may be written through — but an alias's, which
        // the reads through it follow.
        p := graph_operands(g, op)[0].op
        if p == NO_NODE { break }
        if u := flow_user(s, op); u != NO_NODE && graph_op_of(g, u) == .Write {
            if d := graph_whole_write_dest(g, u); d != NO_NODE && graph_refers(g, d) in s.alias { break }
        }
        if graph_is_leaf(p) {
            flow_set_var(s, state, graph_refers(g, p), false, false)
        } else if v, path, _, ok := flow_place_path(s, p); ok {
            flow_set_path(s, state, v, path, false)
        }
    case .Write, .Fill, .Byte_Read, .Zero, .Construct:
        ops := graph_operands(g, op)
        d := ops[0].op if len(ops) > 0 else NO_NODE
        if d == NO_NODE || graph_kind_of(g, d) != .Op { break }
        kind := graph_op_of(g, op)
        if graph_is_leaf(d) {
            v := graph_refers(g, d)
            unset, fields_unset := false, false
            #partial switch kind {
            case .Write:
                val := ops[1].op
                unset = val != NO_NODE && graph_op_of(g, val) == .Const && graph_name(g, val) == "void"
                fields_unset = unset
            case .Zero:
                // A bare declaration: a pointer or a slice unset (a bare scalar
                // is zero), a struct's every field; a constructor's bare field.
                // A literal's start (`{}`): every field, till its entries.
                if graph_written(g, op) == .Synthetic {
                    #partial switch _ in distinct_base(graph_type(g, v)) {
                    case ^Type_Ptr, ^Type_Slice: unset = true
                    }
                    if s.in_ctor && flow_own(s, v) && g.kind[v] == .Field { unset = true }
                    fields_unset = true
                } else if graph_name(g, op) == "{}" {
                    fields_unset = true
                }
            case .Construct:
                if flow_is_literal(g, op) {
                    flow_set_var(s, state, v, false, true)   // (a variant's literal: no body run)
                } else {
                    flow_construct(s, state, v, "", graph_called(g, op))
                }
                flow_init_out_params(s, op, state)
                return
            }
            flow_set_var(s, state, v, unset, fields_unset)
        } else if v, path, _, ok := flow_place_path(s, d); ok {
            if kind == .Construct && !flow_is_literal(g, op) {
                flow_construct(s, state, v, path, graph_called(g, op))
            } else {
                // (A literal's start, `{}`: the field's fields unset, till its entries.)
                flow_set_path(s, state, v, path, (kind == .Zero || kind == .Construct) && flow_is_literal(g, op))
            }
        }
        if kind == .Construct { flow_init_out_params(s, op, state) }
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
        if x == NO_NODE || graph_kind_of(g, x) != .Op { continue }
        #partial switch graph_op_of(g, x) {
        case .Address:
            p := graph_operands(g, x)[0].op
            if p == NO_NODE || graph_kind_of(g, p) != .Op { continue }
            if graph_is_leaf(p) {
                flow_set_var(s, state, graph_refers(g, p), false, false)
            } else if v, path, _, ok := flow_place_path(s, p); ok {
                flow_set_path(s, state, v, path, false)
            }
        case .Read:
            p := graph_operands(g, x)[0].op
            if !graph_is_leaf(p) { continue }
            if target, is_alias := s.alias[graph_refers(g, p)]; is_alias {
                flow_set_var(s, state, target, false, false)
            }
        }
    }
}

// --- constants -----------------------------------------------------------------
// A use of a constant whose value can't be known before the program runs
// (graph_fold_code: a call in it, a struct's construction with arguments):
// Program_Code.fold_errors, reported by flow_report.

// --- void into pointers ------------------------------------------------------
// A pointer always points at something that exists in the program. `void` is no
// pointer value: it DE-INITIALIZES a variable — `p = void`, `p : ^T = void`, and
// reading p is then an error (flow_check_init) — or passes a C function a null
// for a nullable parameter; it can be compared against (`p == void`). Anywhere
// else a void headed for a pointer — a return, an argument, a field, an element,
// a store through a field/index/deref, an if-branch, a default — is an error.

@(private="file")
flow_void :: proc(g: ^Program_Graph, found: ^[dynamic]Flow_Finding) {
    // A void as written, where the operation that takes it stores it — its
    // type its use's. (A parameter's default: the checker's,
    // tc_void_defaults; flow_report reports a span once.)
    any_void := false   // (a code of none, most: nothing to find)
    for c in g.consts { if g.names[c.name] == "void" { any_void = true; break } }
    if !any_void { return }
    for i in 0 ..< len(g.kind) {
        id := Node_Id(i)
        if g.kind[id] != .Op { continue }
        for o, k in graph_operands(g, id) {
            v := o.op
            if v == NO_NODE || graph_op_of(g, v) != .Const || graph_name(g, v) != "void" { continue }
            if graph_written(g, v) != .Explicit { continue }
            if where_, stored := void_where(g, id, k); stored && void_is_pointer(graph_type(g, v)) {
                append(found, Flow_Finding{.Void, graph_origin(g, v), fmt.aprintf(TYPE_VOID_INTO_POINTER, where_, type_name(graph_type(g, v)))})
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
    #partial switch graph_op_of(g, op) {
    case .Write:
        if k != 1 { return "", false }
        dest := ops[0].op
        #partial switch graph_op_of(g, dest) {
        case .Field:        return fmt.tprintf("field '%s'", graph_name(g, dest)), true
        case .Index, .View: return "an array element", true
        case .Deref:        return "a dereferenced pointer", true
        case .Var:
            // A struct body's field, and the slot an if-expression's
            // branches go into, are no variables.
            d := graph_refers(g, dest)
            if d == NO_NODE { return "", false }
            if graph_kind_of(g, d) == .Field { return fmt.tprintf("field '%s'", graph_name(g, d)), true }
            if graph_kind_of(g, d) == .Local && graph_written(g, d) == .Synthetic && graph_name(g, d) == "if" {
                return "a branch of an if-expression", true
            }
        }
    case .Call, .Construct:
        sig := graph_signature(g, op)
        if sig == nil || sig.calling_conv == .C { return "", false }
        // (A construction's first operand is where it builds; a call
        // through a function value's, the value.)
        n := k + 1 if graph_op_of(g, op) == .Call && graph_called(g, op) != nil else k
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
