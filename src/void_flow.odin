package mara

import "core:fmt"
import "core:mem/virtual"
import "core:path/filepath"
import "core:strings"

// void_flow.odin — reads through what may be void. A pointer's `void` (a fun
// value's, a cstring's, a field reference's) is its null, a value; reading
// through one crashes. So a read through a value that may be void is an
// error until a test says it isn't: `if p != void { … }`, `if p == void do
// return`, `assert(p != void)`. What may be void is worked out from where
// void comes from — `void` written, a C function's pointer, memory zeroed
// (`{all 0}`, a bare array), from_text's miss — and where it goes, over the
// whole program: a field that's ever given one may be void wherever it's
// read, a param any call passes one, a result any return gives one.
//
// Each code is a forward dataflow over its runs (dataflow.odin): the state is
// which of its places may be void — its pointer locals and params, its struct
// locals' pointer fields by path, and the places it compares with void (`n.next
// != void`), which a test makes not void on the way it says so (a branch's
// edge). What the program's other codes may make void are facts (Void_Facts):
// a struct's field, a fun's param or result, what's written through a pointer
// of a type, a signature's param or result for calls through fun values. A
// code reads some and makes some void; the codes are run until no fact
// changes (a code again when a fact it read did), then once more to report.
//
// A pointer void only because it was zeroed — a bare declaration, a literal
// that doesn't give it, a constructor's bare field (void_ctor_leaves) — is
// the code's own: it must be written or tested before it's followed there,
// and its address handed out counts as a write (the callee may fill it). A
// copy of it elsewhere is void there as any is.
//
// Not followed: a write through one pointer to what another pointer's test
// said (they may alias); a call between a test and a read, writing void where
// the test looked; a fun value C calls back; a struct built at a heap place
// whose constructor leaves a pointer field bare.

// What may be void, program-wide.
Void_Fact_Kind :: enum u8 { Field, Param, Result, Typed, Sig_Param, Sig_Result }

Void_Fact_Key :: struct {
    kind:  Void_Fact_Kind,
    owner: rawptr,   // the struct or fun (^Type_Scope); nil for a type's or a signature's
    name:  string,   // a field's name; a type's or a signature's text
    index: int,      // a param's or a result's
}

Void_Facts :: struct {
    pc:      ^Program_Code,
    leaves:  map[^Type_Scope][]string,  // what each constructor leaves zeroed (void_ctor_leaves)
    ids:     map[Void_Fact_Key]int,
    void:    [dynamic]bool,
    why:     [dynamic]string,           // what made it void: said after the error
    readers: [dynamic][dynamic]int,     // the codes that read it (by index)
    changed: [dynamic]int,              // made void since their readers ran
}

// One place a code follows: var's value at path ("": var itself; `.f` a
// field, `^` through a pointer, `[]` an element — elements count as one).
Void_Key :: struct {
    var:   Node_Id,
    path:  string,
    entry: int,    // the fact it holds when the code starts (-1: not void — a local's, written first)
    home:  int,    // the fact what's written there from elsewhere makes it, and what it escapes to (-1: none)
    elems: bool,   // past an element: written one at a time, a write never makes it not void
}

Void_Code :: struct {
    vf:       ^Void_Facts,
    g:        ^Program_Graph,
    fun:      ^Type_Scope,
    ci:       int,
    file:     string,
    keys:     [dynamic]Void_Key,
    key_of:   map[Void_Place]i32,
    of_var:   map[Node_Id][dynamic]i32,    // each var's keys
    params:   map[Node_Id]int,             // a param's node → its index
    slots:    map[Node_Id][dynamic]Operand,   // an `and` / `or` slot → what's written to it
    why:      []string,                    // each key's: what made it void (the latest)
    words:    int,
    read:     map[int]bool,                // the facts it read
    found:    ^[dynamic]Flow_Finding,      // reporting: the reads through void found
    call_addrs: map[Node_Id]bool,          // the addresses handed straight to a call (void_args: a zeroed place there is filled)
}

Void_Place :: struct {
    var:  Node_Id,
    path: string,
}

VOID_KEYS_MOST  :: 4096   // the most places a code follows
VOID_PATH_DEPTH :: 4      // how deep a struct local's fields are followed

// The reads through void in the program's codes, each said once.
void_flow_program :: proc(checked: ^Checked_Program) -> []Flow_Finding {
    codes := checked.code.codes[:]
    vf: Void_Facts
    vf.pc = &checked.code
    defer {
        for _, l in vf.leaves { for p in l { delete(p) }; delete(l) }
        delete(vf.leaves)
    }
    // (What a code's run works out is its own: freed once it's done.)
    scratch: virtual.Arena
    if err := virtual.arena_init_growing(&scratch); err != nil { fmt.panicf("void flow: no arena (%v)", err) }
    defer virtual.arena_destroy(&scratch)
    kept_temp := context.temp_allocator
    context.temp_allocator = virtual.arena_allocator(&scratch)
    defer context.temp_allocator = kept_temp
    work := make([dynamic]int, 0, len(codes))
    defer delete(work)
    queued := make([]bool, len(codes))
    defer delete(queued)
    // (A code that makes no void of its own, every fact it may read not
    // void, has nothing void in it: no dataflow to run until one is.)
    sums := make([]Void_Summary, len(codes))
    defer {
        for &sm in sums { delete(sm.facts) }
        delete(sums)
    }
    quiet :: proc(vf: ^Void_Facts, sm: ^Void_Summary) -> bool {
        if sm.sources { return false }
        for f in sm.facts { if vf.void[f] { return false } }
        return true
    }
    for g, i in codes {
        if !void_code_runs(g) { continue }
        void_summarize(&vf, g, i, &sums[i])
        append(&work, i)
        queued[i] = true
    }
    for head := 0; head < len(work); head += 1 {
        ci := work[head]
        queued[ci] = false
        if quiet(&vf, &sums[ci]) { continue }
        void_code(&vf, codes[ci], ci, nil)
        virtual.arena_free_all(&scratch)
        for id in vf.changed {
            for r in vf.readers[id] {
                if !queued[r] { queued[r] = true; append(&work, r) }
            }
        }
        clear(&vf.changed)
    }
    found := make([dynamic]Flow_Finding)
    for g, i in codes {
        if !void_code_runs(g) || quiet(&vf, &sums[i]) { continue }
        void_code(&vf, g, i, &found)
        virtual.arena_free_all(&scratch)
    }
    delete(vf.ids)
    for r in vf.readers { delete(r) }
    delete(vf.readers)
    delete(vf.void)
    delete(vf.why)
    delete(vf.changed)
    return found[:]
}

// What a code may make void, worked out once from its operations: whether it
// makes any itself (a `void`, a C function's pointer, memory zeroed, a
// number made a pointer), and every fact it may read — its readers list it,
// so a fact made void runs it again.
Void_Summary :: struct {
    sources: bool,
    facts:   [dynamic]int,
}

@(private="file")
void_summarize :: proc(vf: ^Void_Facts, g: ^Program_Graph, ci: int, sm: ^Void_Summary) {
    c := Void_Code{vf = vf, g = g, fun = graph_type(g, 0).(^Type_Scope), ci = ci}
    add :: proc(c: ^Void_Code, sm: ^Void_Summary, id: int) {
        if id < 0 { return }
        r := &c.vf.readers[id]
        if len(r) > 0 && r[len(r) - 1] == c.ci { return }
        append(r, c.ci)
        append(&sm.facts, id)
    }
    for i in 0 ..< len(g.consts) {
        id := CONST + Node_Id(i)
        if graph_name(g, id) == "void" && void_is_value(graph_type(g, id)) { sm.sources = true }
    }
    n := 0
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Param, .Local, .Field:
            t := graph_type(g, id)
            if g.kind[id] == .Param && g.parent[id] == 0 {
                if void_is_value(t) { add(&c, sm, void_fact(vf, {.Param, rawptr(c.fun), "", n})) }
                n += 1
            }
            if void_is_value(t) {
                add(&c, sm, void_typed_fact(&c, t))
                if g.kind[id] == .Field { add(&c, sm, void_field_fact(&c, c.fun, graph_name(g, id))) }
            } else {
                void_type_facts(&c, sm, t, 0, add)
            }
        case .Op:
            t := graph_type(g, id)
            #partial switch g.op[id] {
            case .Field, .Index, .View, .Slice, .Deref:
                if void_is_value(t) { add(&c, sm, void_place_fact(&c, id)) }
            case .Address:
                if ops := graph_operands(g, id); len(ops) > 0 && ops[0].op != NO_NODE {
                    pt := graph_type(g, ops[0].op)
                    if void_is_value(pt) { add(&c, sm, void_typed_fact(&c, pt)) } else { void_type_facts(&c, sm, pt, 0, add) }
                }
            case .Construct:
                void_type_facts(&c, sm, t, 0, add)
                if len(void_ctor_leaves(vf, graph_called(g, id))) > 0 { sm.sources = true }
            case .Zero:
                if void_holds(t, 0) { sm.sources = true }
            case .Cast:
                if void_is_value(t) { sm.sources = true }
            case .Call:
                callee := graph_called(g, id)
                if callee == nil {
                    if sig := graph_signature(g, id); sig != nil {
                        for r, k in sig.return_types { if void_is_value(r) { add(&c, sm, void_fact(vf, {.Sig_Result, nil, void_sig(sig), k})) } }
                    }
                    continue
                }
                #partial switch o in callee.origin {
                case Origin_Foreign:
                    for r in callee.return_types { if void_is_value(r) && !o.fails { sm.sources = true } }
                    continue
                case Origin_Field_From_Text:
                    sm.sources = true
                    continue
                }
                for r, k in callee.return_types { if void_is_value(r) { add(&c, sm, void_fact(vf, {.Result, rawptr(callee), "", k})) } }
            }
        }
    }
}

// The facts a value of type t may hold void in: its pointer fields', its
// pointer items' (an array in a field: the field's).
@(private="file")
void_type_facts :: proc(c: ^Void_Code, sm: ^Void_Summary, t: Type, depth: int, add: proc(c: ^Void_Code, sm: ^Void_Summary, id: int)) {
    if depth >= VOID_PATH_DEPTH { return }
    #partial switch at in distinct_base(t) {
    case ^Type_Scope:
        if at.kind != .Struct { return }
        for f in at.sd.fields {
            if strings.has_prefix(f.name, "__") { continue }
            if void_is_value(f.type_) {
                add(c, sm, void_field_fact(c, at, f.name))
                continue
            }
            elem: Type
            #partial switch ft in distinct_base(f.type_) {
            case ^Type_Fixed_Array:   elem = ft.elem
            case ^Type_Partial_Array: elem = ft.elem
            }
            if elem != nil && void_is_value(elem) { add(c, sm, void_field_fact(c, at, f.name)) }
            void_type_facts(c, sm, f.type_, depth + 1, add)
        }
    case ^Type_Fixed_Array:
        if void_is_value(at.elem) { add(c, sm, void_typed_fact(c, at.elem)) } else { void_type_facts(c, sm, at.elem, depth + 1, add) }
    case ^Type_Partial_Array:
        if void_is_value(at.elem) { add(c, sm, void_typed_fact(c, at.elem)) } else { void_type_facts(c, sm, at.elem, depth + 1, add) }
    }
}

// Whether a type holds anything whose void is a value.
@(private="file")
void_holds :: proc(t: Type, depth: int) -> bool {
    if depth >= VOID_PATH_DEPTH { return false }
    if void_is_value(t) { return true }
    #partial switch at in distinct_base(t) {
    case ^Type_Scope:
        if at.kind != .Struct { return false }
        for f in at.sd.fields { if void_holds(f.type_, depth + 1) { return true } }
    case ^Type_Fixed_Array:   return void_holds(at.elem, depth + 1)
    case ^Type_Partial_Array: return void_holds(at.elem, depth + 1)
    case ^Type_Union:
        for _, vs in at.variant_structs { if void_holds(vs, depth + 1) { return true } }
    }
    return false
}

// Whether a code is a fun's or a struct's: one that runs.
@(private="file")
void_code_runs :: proc(g: ^Program_Graph) -> bool {
    if g == nil || g.end < 0 { return false }
    k := graph_kind_of(g, 0)
    if k != .Fun && k != .Struct { return false }
    _, is_scope := graph_type(g, 0).(^Type_Scope)
    return is_scope
}

// --- facts --------------------------------------------------------------------

@(private="file")
void_fact :: proc(vf: ^Void_Facts, key: Void_Fact_Key) -> int {
    if id, ok := vf.ids[key]; ok { return id }
    id := len(vf.void)
    k := key
    k.name = strings.clone(key.name)
    vf.ids[k] = id
    append(&vf.void, false)
    append(&vf.why, "")
    append(&vf.readers, [dynamic]int{})
    return id
}

// Whether fact id is void — this code reading it (it runs again if it becomes so).
@(private="file")
void_fact_is :: proc(c: ^Void_Code, id: int) -> bool {
    if id < 0 { return false }
    if id not_in c.read {
        c.read[id] = true
        r := &c.vf.readers[id]
        if len(r) == 0 || r[len(r) - 1] != c.ci { append(r, c.ci) }
    }
    return c.vf.void[id]
}

// Fact id made void, `why` said after the errors it leads to.
@(private="file")
void_raise :: proc(c: ^Void_Code, id: int, why: string) {
    if id < 0 || c.vf.void[id] { return }
    c.vf.void[id] = true
    c.vf.why[id] = strings.clone(why)
    append(&c.vf.changed, id)
}

@(private="file")
void_field_fact :: proc(c: ^Void_Code, owner: Type, name: string) -> int {
    ts, ok := distinct_base(owner).(^Type_Scope)
    if !ok { return -1 }
    return void_fact(c.vf, {.Field, rawptr(ts), name, 0})
}

@(private="file")
void_typed_fact :: proc(c: ^Void_Code, t: Type) -> int {
    return void_fact(c.vf, {.Typed, nil, type_name(t), 0})
}

// A fun's signature as text: what calls through fun values are matched by.
@(private="file")
void_sig :: proc(ft: ^Type_Scope) -> string {
    b := strings.builder_make(context.temp_allocator)
    strings.write_string(&b, "(")
    for p, i in ft.params {
        if i > 0 { strings.write_string(&b, ", ") }
        strings.write_string(&b, type_name(p.type_))
    }
    strings.write_string(&b, ") ->")
    for r in ft.return_types {
        strings.write_string(&b, " ")
        strings.write_string(&b, type_name(r))
    }
    return strings.to_string(b)
}

// --- a code ---------------------------------------------------------------------

@(private="file")
void_code :: proc(vf: ^Void_Facts, g: ^Program_Graph, ci: int, found: ^[dynamic]Flow_Finding) {
    runs: [dynamic]i32
    defer delete(runs)
    graph_code_runs(g, 0, &runs)
    if len(runs) == 0 { return }
    c := Void_Code{vf = vf, g = g, fun = graph_type(g, 0).(^Type_Scope), ci = ci, found = found}
    c.file = span_file(graph_origin(g, 0))
    defer {
        for k in c.keys { delete(k.path) }
        delete(c.keys)
        delete(c.key_of)
        for _, l in c.of_var { delete(l) }
        delete(c.of_var)
        delete(c.params)
        for _, l in c.slots { delete(l) }
        delete(c.slots)
        delete(c.why)
        delete(c.read)
        delete(c.call_addrs)
    }
    void_keys(&c)
    c.words = max(1, (2 * len(c.keys) + 63) / 64)   // (each key's void bit, then its zeroed bit: void_set_zeroed)
    c.why = make([]string, len(c.keys))
    entry := make([]u64, c.words)
    defer delete(entry)
    for k, i in c.keys {
        if k.entry >= 0 && void_fact_is(&c, k.entry) {
            bits_set(entry, i)
            c.why[i] = vf.why[k.entry]
        }
    }
    fl := run_flow_make(g, runs[:], c.words, bits_copy, bits_union)
    defer run_flow_free(&fl)
    run_flow_solve_edges(&fl, entry, &c, proc(c: ^Void_Code, ri: int, op: Node_Id, state: []u64) { void_op(c, op, state, false) }, void_edge)
    if found != nil {
        run_flow_replay(&fl, &c, proc(c: ^Void_Code, ri: int, op: Node_Id, state: []u64) { void_op(c, op, state, true) })
    }
}

// The places a code follows: its pointer locals and params, its struct and
// array locals' pointer fields and elements by path, and what it compares
// with void.
@(private="file")
void_keys :: proc(c: ^Void_Code) {
    g := c.g
    in_ctor := graph_kind_of(g, 0) == .Struct
    n := 0
    for id := Node_Id(1); id <= g.end; id += 1 {
        #partial switch g.kind[id] {
        case .Fun, .Struct:
            id = graph_last(g, id)
            continue
        case .Param:
            if g.parent[id] == 0 { c.params[id] = n; n += 1 }
            void_var_keys(c, id, .Param)
        case .Local:
            void_var_keys(c, id, .Local)
        case .Field:
            if in_ctor && g.parent[id] == 0 { void_var_keys(c, id, .Field) }
        case .Op:
            if g.op[id] == .Call || g.op[id] == .Construct {
                for a in du_call_args(g, id) {
                    if x := a.op; x != NO_NODE && x < CONST && graph_kind_of(g, x) == .Op && graph_op_of(g, x) == .Address { c.call_addrs[x] = true }
                }
            }
            if g.op[id] == .Write {
                ops := graph_operands(g, id)
                d := ops[0].op
                if graph_is_leaf(d) {
                    if v := graph_refers(g, d); v > 0 && v <= g.end && g.kind[v] == .Local && g.written[v] == .Synthetic && (graph_name(g, v) == "and" || graph_name(g, v) == "or") {
                        if v not_in c.slots { c.slots[v] = {} }
                        append(&c.slots[v], ops[1])
                    }
                }
            }
            if g.op[id] != .Compare { continue }
            ops := graph_operands(g, id)
            if len(ops) != 2 { continue }
            x := ops[0].op if void_is_void(g, ops[1].op) else ops[1].op if void_is_void(g, ops[0].op) else NO_NODE
            if x == NO_NODE { continue }
            p := void_value_place(g, x)
            if p == NO_NODE || graph_is_leaf(p) { continue }
            var, path, ok := void_place_path(c, p)
            if !ok || strings.contains(path, "[]") { continue }
            if (Void_Place{var, path}) in c.key_of { continue }
            fact := void_place_fact(c, p)
            void_add_key(c, var, path, fact if void_is_param_root(c, var) else -1, fact, false)
        }
    }
}

// Whether a var is a param of the code (a narrowed place through it holds
// what the program says from the start).
@(private="file")
void_is_param_root :: proc(c: ^Void_Code, var: Node_Id) -> bool {
    return var > 0 && var <= c.g.end && c.g.kind[var] == .Param
}

@(private="file")
void_add_key :: proc(c: ^Void_Code, var: Node_Id, path: string, entry, home: int, elems: bool) {
    if len(c.keys) >= VOID_KEYS_MOST { return }
    p := strings.clone(path)
    c.key_of[Void_Place{var, p}] = i32(len(c.keys))
    append(&c.keys, Void_Key{var = var, path = p, entry = entry, home = home, elems = elems})
    if var not_in c.of_var { c.of_var[var] = {} }
    append(&c.of_var[var], i32(len(c.keys) - 1))
}

Void_Var_Kind :: enum u8 { Local, Param, Field }

// A var's keys: itself, when its void is a value; its fields' and elements'
// that are, by path.
@(private="file")
void_var_keys :: proc(c: ^Void_Code, v: Node_Id, kind: Void_Var_Kind) {
    g := c.g
    t := graph_type(g, v)
    if void_is_value(t) {
        entry, home := -1, void_typed_fact(c, t)
        switch kind {
        case .Param:
            i := c.params[v]
            entry = void_fact(c.vf, {.Param, rawptr(c.fun), "", i})
        case .Field:
            home = void_field_fact(c, c.fun, graph_name(g, v))
        case .Local:
        }
        void_add_key(c, v, "", entry, home, false)
        return
    }
    void_path_keys(c, v, kind, t, "", 0, false)
}

@(private="file")
void_path_keys :: proc(c: ^Void_Code, v: Node_Id, kind: Void_Var_Kind, t: Type, path: string, depth: int, elems: bool) {
    if depth >= VOID_PATH_DEPTH || len(c.keys) >= VOID_KEYS_MOST { return }
    #partial switch at in distinct_base(t) {
    case ^Type_Scope:
        if at.kind != .Struct { return }
        for f in at.sd.fields {
            if strings.has_prefix(f.name, "__") { continue }
            sub := strings.concatenate({path, ".", f.name}, context.temp_allocator)
            if void_is_value(f.type_) {
                home := void_field_fact(c, at, f.name)
                void_add_key(c, v, sub, home if kind == .Param else -1, home, elems)
            } else {
                void_path_keys(c, v, kind, f.type_, sub, depth + 1, elems)
            }
        }
    case ^Type_Fixed_Array:
        void_elem_keys(c, v, kind, at.elem, path, depth)
    case ^Type_Partial_Array:
        void_elem_keys(c, v, kind, at.elem, path, depth)
    }
}

@(private="file")
void_elem_keys :: proc(c: ^Void_Code, v: Node_Id, kind: Void_Var_Kind, elem: Type, path: string, depth: int) {
    sub := strings.concatenate({path, "[]"}, context.temp_allocator)
    if void_is_value(elem) {
        // (An array in a field: its elements are the field's fact.)
        home := void_typed_fact(c, elem)
        if dot := strings.last_index(path, "."); dot >= 0 && !strings.contains(path[dot:], "[") {
            if owner := void_path_owner(c, v, path[:dot]); owner != nil { home = void_field_fact(c, owner, path[dot + 1:]) }
        }
        void_add_key(c, v, sub, home if kind == .Param else -1, home, true)
        return
    }
    void_path_keys(c, v, kind, elem, sub, depth + 1, true)
}

// The struct type at a var's path (one with no element in it).
@(private="file")
void_path_owner :: proc(c: ^Void_Code, v: Node_Id, path: string) -> Type {
    t := graph_type(c.g, v)
    rest := path
    for len(rest) > 0 {
        if rest[0] == '.' { rest = rest[1:] }
        end := strings.index_byte(rest, '.')
        name := rest if end < 0 else rest[:end]
        ts, ok := distinct_base(t).(^Type_Scope)
        if !ok { return nil }
        found := false
        for f in ts.sd.fields {
            if f.name == name { t = f.type_; found = true; break }
        }
        if !found { return nil }
        rest = "" if end < 0 else rest[end:]
    }
    return t
}

// --- places and values -----------------------------------------------------------

@(private="file")
void_is_void :: proc(g: ^Program_Graph, x: Node_Id) -> bool {
    return x != NO_NODE && graph_op_of(g, x) == .Const && graph_name(g, x) == "void"
}

// The place a value is read from: a read's, a leaf's own; NO_NODE for a value
// read from nowhere.
@(private="file")
void_value_place :: proc(g: ^Program_Graph, x: Node_Id) -> Node_Id {
    if x == NO_NODE { return NO_NODE }
    if x >= READ { return g.reads[x - READ].op }
    if graph_is_leaf(x) { return x }
    if graph_kind_of(g, x) == .Op && graph_op_of(g, x) == .Read { return graph_operands(g, x)[0].op }
    return NO_NODE
}

// The var a place is in and its path from it.
@(private="file")
void_place_path :: proc(c: ^Void_Code, p: Node_Id) -> (var: Node_Id, path: string, ok: bool) {
    g := c.g
    steps := make([dynamic]string, 0, 4, context.temp_allocator)
    for id := p; true; {
        if id == NO_NODE { return }
        if graph_is_leaf(id) {
            var = graph_refers(g, id)
            break
        }
        if graph_kind_of(g, id) != .Op { return }
        #partial switch graph_op_of(g, id) {
        case .Var:
            var = graph_refers(g, id)
        case .Field:
            append(&steps, strings.concatenate({".", graph_name(g, id)}, context.temp_allocator))
        case .Deref:
            append(&steps, "^")
        case .Index, .View, .Slice:
            append(&steps, "[]")
        case .Variant:
            // (A variant's fields are its union's place: the union's struct
            // is the variant's.)
        case:
            return
        }
        if graph_op_of(g, id) == .Var { break }
        id = graph_operands(g, id)[0].op
    }
    if var <= 0 || var > g.end { return }
    b := strings.builder_make(context.temp_allocator)
    for i := len(steps) - 1; i >= 0; i -= 1 { strings.write_string(&b, steps[i]) }
    return var, strings.to_string(b), true
}

@(private="file")
void_key :: proc(c: ^Void_Code, p: Node_Id) -> i32 {
    var, path, ok := void_place_path(c, p)
    if !ok { return -1 }
    return c.key_of[Void_Place{var, path}] or_else -1
}

// The fact a place's value is, past what the code follows: a field's, an
// element of a field's (the field's), what's written through a pointer or into
// a slice of its type.
@(private="file")
void_place_fact :: proc(c: ^Void_Code, p: Node_Id) -> int {
    g := c.g
    if p == NO_NODE || graph_is_leaf(p) || graph_kind_of(g, p) != .Op { return -1 }
    #partial switch graph_op_of(g, p) {
    case .Field:
        return void_field_fact(c, graph_type(g, graph_operands(g, p)[0].op), graph_name(g, p))
    case .Index, .View, .Slice:
        base := graph_operands(g, p)[0].op
        if base != NO_NODE && !graph_is_leaf(base) && graph_kind_of(g, base) == .Op && graph_op_of(g, base) == .Field {
            return void_field_fact(c, graph_type(g, graph_operands(g, base)[0].op), graph_name(g, base))
        }
        return void_typed_fact(c, graph_type(g, p))
    case .Deref:
        return void_typed_fact(c, graph_type(g, p))
    }
    return -1
}

// Whether the value at a place may be void, and what made it so.
@(private="file")
void_place_is :: proc(c: ^Void_Code, p: Node_Id, state: []u64) -> (bool, string) {
    if p == NO_NODE { return false, "" }
    if !void_is_value(graph_type(c.g, p)) { return false, "" }
    if k := void_key(c, p); k >= 0 {
        if bits_has(state, int(k)) { return true, c.why[k] }
        return false, ""
    }
    if graph_is_leaf(p) { return false, "" }
    f := void_place_fact(c, p)
    if void_fact_is(c, f) { return true, c.vf.why[f] }
    return false, ""
}

// Whether a value may be void, and what made it so.
@(private="file")
void_value_is :: proc(c: ^Void_Code, x: Node_Id, out: i32, state: []u64) -> (bool, string) {
    g := c.g
    if x == NO_NODE { return false, "" }
    if void_is_void(g, x) { return true, fmt.tprintf("it's set to void at %s", void_where(c, graph_origin(g, x))) }
    if p := void_value_place(g, x); p != NO_NODE { return void_place_is(c, p, state) }
    if x >= CONST || graph_kind_of(g, x) != .Op { return false, "" }
    #partial switch graph_op_of(g, x) {
    case .Call:
        callee := graph_called(g, x)
        if callee == nil {
            sig := graph_signature(g, x)
            if sig == nil || int(out) >= len(sig.return_types) || !void_is_value(sig.return_types[out]) { return false, "" }
            f := void_fact(c.vf, {.Sig_Result, nil, void_sig(sig), int(out)})
            if void_fact_is(c, f) { return true, c.vf.why[f] }
            return false, ""
        }
        #partial switch o in callee.origin {
        case Origin_Foreign:
            if o.fails || int(out) >= len(callee.return_types) || !void_is_value(callee.return_types[out]) { return false, "" }
            return true, fmt.tprintf("it comes from '%s', a C function, which can give void", callee.source_name if callee.source_name != "" else callee.name)
        case Origin_Field_From_Text:
            if out == 0 { return true, "it comes from from_text, which gives void when the text names no field" }
            return false, ""
        }
        if int(out) >= len(callee.return_types) || !void_is_value(callee.return_types[out]) { return false, "" }
        f := void_fact(c.vf, {.Result, rawptr(callee), "", int(out)})
        if void_fact_is(c, f) { return true, c.vf.why[f] }
    case .Cast:
        if !void_is_value(graph_type(g, x)) { return false, "" }
        ops := graph_operands(g, x)
        if len(ops) == 0 { return false, "" }
        if void_is_value(graph_type(g, ops[0].op)) { return void_value_is(c, ops[0].op, ops[0].out, state) }
        return true, fmt.tprintf("it's made from a number at %s", void_where(c, graph_origin(g, x)))
    }
    return false, ""
}

// "line 12", or "file.mara:12" for another file's.
@(private="file")
void_where :: proc(c: ^Void_Code, s: Span) -> string {
    file := span_file(s)
    if file == c.file || file == "" { return fmt.tprintf("line %d", span_line(s)) }
    return fmt.tprintf("%s:%d", filepath.base(file), span_line(s))
}

// What a value or a place is called, as it's written: `b.next`, `ks[0]`.
@(private="file")
void_text :: proc(c: ^Void_Code, x: Node_Id, depth := 0) -> string {
    g := c.g
    if x == NO_NODE || depth > 16 { return "it" }
    if x >= READ { return void_text(c, g.reads[x - READ].op, depth + 1) }
    if graph_is_leaf(x) { return graph_name(g, x) }
    if x >= CONST { return graph_name(g, x) }
    if graph_kind_of(g, x) != .Op { return "it" }
    ops := graph_operands(g, x)
    #partial switch graph_op_of(g, x) {
    case .Read, .Variant:
        return void_text(c, ops[0].op, depth + 1)
    case .Var:
        return graph_name(g, graph_refers(g, x))
    case .Field:
        return fmt.tprintf("%s.%s", void_text(c, ops[0].op, depth + 1), graph_name(g, x))
    case .Deref:
        base := void_text(c, ops[0].op, depth + 1)
        return base if graph_written(g, x) != .Explicit else fmt.tprintf("%s^", base)
    case .Index:
        i := "_"
        if len(ops) > 1 {
            ix := ops[1].op
            if v, known := graph_value(g, ix); known && !v.is_float && !v.is_text { i = fmt.tprint(v.int) } else if ix >= READ || graph_is_leaf(ix) { i = void_text(c, ix, depth + 1) }
        }
        return fmt.tprintf("%s[%s]", void_text(c, ops[0].op, depth + 1), i)
    case .View, .Slice:
        return fmt.tprintf("%s[_]", void_text(c, ops[0].op, depth + 1))
    case .Call:
        if callee := graph_called(g, x); callee != nil { return fmt.tprintf("%s()", callee.source_name if callee.source_name != "" else callee.name) }
    }
    return "it"
}

// What a fact is said as: `Node.next`, `'f''s 'p'`.
@(private="file")
void_fact_text :: proc(c: ^Void_Code, id: int) -> string {
    for key, i in c.vf.ids {
        if i != id { continue }
        switch key.kind {
        case .Field:
            ts := (^Type_Scope)(key.owner)
            return fmt.tprintf("%s.%s", ts.source_name if ts.source_name != "" else ts.name, key.name)
        case .Param, .Sig_Param:
            return "a param"
        case .Result, .Sig_Result:
            return "a result"
        case .Typed:
            return fmt.tprintf("a `%s` written through a pointer", key.name)
        }
    }
    return "it"
}

// --- the state ---------------------------------------------------------------------

@(private="file")
void_set :: proc(c: ^Void_Code, state: []u64, k: i32, is_void: bool, why: string) {
    if k < 0 { return }
    bits_clear(state, len(c.keys) + int(k))
    if is_void {
        bits_set(state, int(k))
        if why != "" { c.why[k] = why }
    } else {
        bits_clear(state, int(k))
    }
}

// A key void only because it's zeroed (a bare declaration's, a literal's
// start, a constructor's bare field): the code's own to write or test.
@(private="file")
void_set_zeroed :: proc(c: ^Void_Code, state: []u64, k: i32, why: string) {
    if k < 0 { return }
    void_set(c, state, k, true, why)
    bits_set(state, len(c.keys) + int(k))
}

@(private="file")
void_zeroed :: proc(c: ^Void_Code, state: []u64, k: i32) -> bool {
    return bits_has(state, len(c.keys) + int(k))
}

// The keys under a place (deeper than it; `whole`: itself too), each by its
// path past the place.
@(private="file")
void_under :: proc(c: ^Void_Code, var: Node_Id, path: string, whole: bool) -> [dynamic]i32 {
    out := make([dynamic]i32, context.temp_allocator)
    list, ok := c.of_var[var]
    if !ok { return out }
    for k in list {
        kp := c.keys[k].path
        if !strings.has_prefix(kp, path) { continue }
        if len(kp) == len(path) {
            if whole { append(&out, k) }
            continue
        }
        if path == "" || kp[len(path)] == '.' || kp[len(path)] == '^' || kp[len(path)] == '[' { append(&out, k) }
    }
    return out
}

// What's under a place written whole from `src` (a place the code follows,
// NO_NODE for none): each key under it as src's at the same path, or what
// its home fact says.
@(private="file")
void_copy_under :: proc(c: ^Void_Code, state: []u64, dest: Node_Id, src: Node_Id) {
    var, path, ok := void_place_path(c, dest)
    if !ok { return }
    svar, spath, sok := Node_Id(0), "", false
    if src != NO_NODE { svar, spath, sok = void_place_path(c, src) }
    for k in void_under(c, var, path, false) {
        key := c.keys[k]
        if sok {
            from := strings.concatenate({spath, key.path[len(path):]}, context.temp_allocator)
            if sk, has := c.key_of[Void_Place{svar, from}]; has {
                if void_zeroed(c, state, sk) { void_set_zeroed(c, state, k, c.why[sk]) } else { void_set(c, state, k, bits_has(state, int(sk)), c.why[sk]) }
                continue
            }
        }
        void_set(c, state, k, void_fact_is(c, key.home), c.vf.why[key.home] if key.home >= 0 else "")
    }
}

// A struct built at a followed place by its constructor: the pointers it
// leaves zeroed there (void_ctor_leaves), the code's own to write or test.
@(private="file")
void_construct :: proc(c: ^Void_Code, state: []u64, dest: Node_Id, ts: ^Type_Scope, span: Span) {
    leaves := void_ctor_leaves(c.vf, ts)
    if len(leaves) == 0 { return }
    var, path, ok := void_place_path(c, dest)
    if !ok { return }
    name := ts.source_name if ts.source_name != "" else ts.name
    why := fmt.tprintf("%s's constructor leaves it void (at %s)", name, void_where(c, span))
    for l in leaves {
        if k, has := c.key_of[Void_Place{var, strings.concatenate({path, l}, context.temp_allocator)}]; has { void_set_zeroed(c, state, k, why) }
    }
}

// The pointers a struct's constructor leaves zeroed, by path (`.next`,
// `.pos.owner`): under its fields declared bare (or given a literal that
// leaves them out) or built by a constructor that leaves them so, that its
// code never writes — nor hands out the address of. Worked out once a
// struct, from its code.
void_ctor_leaves :: proc(vf: ^Void_Facts, ts: ^Type_Scope, depth := 0) -> []string {
    if ts == nil || vf.pc == nil || depth > VOID_PATH_DEPTH { return nil }
    if known, ok := vf.leaves[ts]; ok { return known }
    vf.leaves[ts] = nil   // (while it's worked out: a struct that builds itself leaves nothing)
    g := graph_fun_code(vf.pc, ts)
    if g == nil || graph_kind_of(g, 0) != .Struct { return nil }
    zeroed := make([dynamic]string, context.temp_allocator)
    written := make([dynamic]string, context.temp_allocator)
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
        root, path := void_field_path(g, d)
        if root == NO_NODE { continue }
        whole := graph_is_leaf(d)
        if whole && g.op[id] == .Zero && (g.written[id] == .Synthetic || flow_is_literal_name(graph_name(g, id))) {
            void_pointer_paths(graph_type(g, root), path, &zeroed, 0)
            continue
        }
        if whole && g.op[id] == .Construct && !flow_is_literal_name(graph_name(g, id)) {
            for l in void_ctor_leaves(vf, graph_called(g, id), depth + 1) { append(&zeroed, strings.concatenate({path, l}, context.temp_allocator)) }
            continue
        }
        append(&written, path)
    }
    left := make([dynamic]string)
    each: for z in zeroed {
        for w in written {
            if z == w || len(z) > len(w) && strings.has_prefix(z, w) && z[len(w)] == '.' { continue each }
        }
        append(&left, strings.clone(z))
    }
    vf.leaves[ts] = left[:]
    return left[:]
}

// A constructor's own field a place is rooted at (`.wrap.data`; past an
// element, the field it's in), as a key's path.
@(private="file")
void_field_path :: proc(g: ^Program_Graph, p: Node_Id) -> (root: Node_Id, path: string) {
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
    if root <= 0 || root > g.end || g.kind[root] != .Field || g.parent[root] != 0 { return NO_NODE, "" }
    b := strings.builder_make(context.temp_allocator)
    strings.write_string(&b, ".")
    strings.write_string(&b, graph_name(g, root))
    #reverse for n in names {
        strings.write_string(&b, ".")
        strings.write_string(&b, n)
    }
    return root, strings.to_string(b)
}

// Each pointer under a value of t, by path past `prefix` (a struct's fields,
// not too deep; an array's items aren't followed here).
@(private="file")
void_pointer_paths :: proc(t: Type, prefix: string, out: ^[dynamic]string, depth: int) {
    if depth >= VOID_PATH_DEPTH { return }
    if void_is_value(t) {
        append(out, prefix)
        return
    }
    sd := as_struct_body(distinct_base(t))
    if sd == nil { return }
    for f in sd.fields {
        if strings.has_prefix(f.name, "__") { continue }
        void_pointer_paths(f.type_, strings.concatenate({prefix, ".", f.name}, context.temp_allocator), out, depth + 1)
    }
}

// What's under a followed place, gone where the code doesn't follow it (its
// address taken, a copy of it written elsewhere, passed, returned): each key
// that may be void makes its home fact so.
@(private="file")
void_escape :: proc(c: ^Void_Code, state: []u64, p: Node_Id, whole: bool, address := false) {
    var, path, ok := void_place_path(c, p)
    if !ok { return }
    for k in void_under(c, var, path, whole) {
        // (Its address handed out, a zeroed one may be filled there: written.)
        if address && void_zeroed(c, state, k) {
            void_set(c, state, k, false, "")
            continue
        }
        if !bits_has(state, int(k)) || c.keys[k].home < 0 || c.vf.void[c.keys[k].home] { continue }
        void_raise(c, c.keys[k].home, fmt.tprintf("%s can be void: %s", void_fact_text(c, c.keys[k].home), c.why[k]))
    }
}

// A place (and what's under it) zeroed: `{all 0}` every pointer under it void;
// a bare declaration, a fixed array's elements.
@(private="file")
Void_Zero :: enum u8 {
    All,       // `{all 0}`: every pointer under it void
    Bare,      // a bare declaration: a fixed array's elements void (the rest is definite assignment's)
    Literal,   // a literal's start: what it doesn't give, definite assignment's
}

void_zero :: proc(c: ^Void_Code, state: []u64, dest: Node_Id, mode: Void_Zero, span: Span) {
    var, path, ok := void_place_path(c, dest)
    why := fmt.tprintf("it's zeroed at %s", void_where(c, span))
    if !ok {
        // (Somewhere else: every pointer field under its type may be void.)
        if mode == .All { void_raise_zeroed(c, graph_type(c.g, dest), why, 0) }
        return
    }
    for k in void_under(c, var, path, true) {
        key := c.keys[k]
        if strings.contains(key.path[len(path):], "^") {
            void_set(c, state, k, void_fact_is(c, key.home), c.vf.why[key.home] if key.home >= 0 else "")
            continue
        }
        // (`{all 0}` and a bare fixed array's items: void, as written; an
        // array literal's items and a list's aren't (written one at a time,
        // an item never stops being void). A bare declaration's zero, a
        // literal's start: zeroed, the code's own — till its entries or
        // writes give one.)
        if mode == .All || mode == .Bare && key.elems && void_fixed_elems(c, var, key.path) {
            void_set(c, state, k, true, why)
            // (A constructor's own field: the struct's, wherever it's read.)
            if var <= c.g.end && c.g.kind[var] == .Field { void_raise(c, key.home, why) }
        } else if key.elems {
            void_set(c, state, k, false, why)
        } else {
            void_set_zeroed(c, state, k, why)
        }
    }
}

// Whether a path's elements are a fixed array's: zeroed, they're there to
// read (a list's past its len aren't).
@(private="file")
void_fixed_elems :: proc(c: ^Void_Code, var: Node_Id, path: string) -> bool {
    at := strings.index(path, "[]")
    if at < 0 { return false }
    t := graph_type(c.g, var) if at == 0 else void_path_owner(c, var, path[:at])
    _, fixed := distinct_base(t).(^Type_Fixed_Array)
    return fixed
}

// Every pointer field under a type zeroed somewhere: void.
@(private="file")
void_raise_zeroed :: proc(c: ^Void_Code, t: Type, why: string, depth: int) {
    if depth >= VOID_PATH_DEPTH { return }
    #partial switch at in distinct_base(t) {
    case ^Type_Scope:
        if at.kind != .Struct { return }
        for f in at.sd.fields {
            if strings.has_prefix(f.name, "__") { continue }
            if void_is_value(f.type_) {
                void_raise(c, void_field_fact(c, at, f.name), why)
            } else {
                void_raise_zeroed(c, f.type_, why, depth + 1)
            }
        }
    case ^Type_Fixed_Array:
        if void_is_value(at.elem) { void_raise(c, void_typed_fact(c, at.elem), why) } else { void_raise_zeroed(c, at.elem, why, depth + 1) }
    case ^Type_Union:
        for _, vs in at.variant_structs { void_raise_zeroed(c, vs, why, depth + 1) }
    }
}

// A value written into a place.
@(private="file")
void_write :: proc(c: ^Void_Code, state: []u64, dest: Node_Id, val: Operand, span: Span) {
    g := c.g
    t := graph_type(g, dest)
    if void_is_value(t) {
        is_void, why := void_value_is(c, val.op, val.out, state)
        if k := void_key(c, dest); k >= 0 {
            key := c.keys[k]
            if !key.elems || is_void { void_set(c, state, k, is_void, why) }
            // (What was narrowed through it holds what the program says.)
            for u in void_under(c, key.var, key.path, false) {
                uk := c.keys[u]
                void_set(c, state, u, void_fact_is(c, uk.home), c.vf.why[uk.home] if uk.home >= 0 else "")
            }
            // (A constructor's own field: the struct's, wherever it's read.)
            if is_void && key.var <= g.end && g.kind[key.var] == .Field {
                void_raise(c, key.home, fmt.tprintf("%s is set to void at %s", void_field_name(c, c.fun, graph_name(g, key.var)), void_where(c, span)))
            }
            return
        }
        if is_void { void_raise(c, void_place_fact(c, dest), void_store_why(c, dest, span)) }
        return
    }
    // A whole struct or array: what's under it, as where it comes from says.
    src := void_value_place(g, val.op)
    if void_key_under(c, dest) {
        void_copy_under(c, state, dest, src)
    } else if src != NO_NODE {
        void_escape(c, state, src, true)
    }
}

// Whether the code follows anything under a place.
@(private="file")
void_key_under :: proc(c: ^Void_Code, p: Node_Id) -> bool {
    var, path, ok := void_place_path(c, p)
    return ok && len(void_under(c, var, path, true)) > 0
}

@(private="file")
void_field_name :: proc(c: ^Void_Code, owner: Type, name: string) -> string {
    ts, ok := distinct_base(owner).(^Type_Scope)
    if !ok { return name }
    return fmt.tprintf("%s.%s", ts.source_name if ts.source_name != "" else ts.name, name)
}

// What a void stored somewhere the code doesn't follow is said as.
@(private="file")
void_store_why :: proc(c: ^Void_Code, dest: Node_Id, span: Span) -> string {
    g := c.g
    if !graph_is_leaf(dest) && graph_kind_of(g, dest) == .Op {
        #partial switch graph_op_of(g, dest) {
        case .Field:
            return fmt.tprintf("%s is set to void at %s", void_field_name(c, graph_type(g, graph_operands(g, dest)[0].op), graph_name(g, dest)), void_where(c, span))
        case .Index, .View, .Slice:
            base := graph_operands(g, dest)[0].op
            if base != NO_NODE && !graph_is_leaf(base) && graph_kind_of(g, base) == .Op && graph_op_of(g, base) == .Field {
                return fmt.tprintf("an item of %s is set to void at %s", void_field_name(c, graph_type(g, graph_operands(g, base)[0].op), graph_name(g, base)), void_where(c, span))
            }
        }
    }
    return fmt.tprintf("a `%s` is written as void through a pointer at %s", type_name(graph_type(g, dest)), void_where(c, span))
}

// A call's (or a construction's) arguments: what each param may be given.
@(private="file")
void_args :: proc(c: ^Void_Code, state: []u64, op: Node_Id) {
    g := c.g
    callee := graph_called(g, op)
    sig := graph_signature(g, op)
    if sig == nil { return }
    to_c := false
    if callee != nil {
        _, to_c = callee.origin.(Origin_Foreign)
    }
    name := callee.source_name if callee != nil && callee.source_name != "" else callee.name if callee != nil else "a fun value"
    for a, k in du_call_args(g, op) {
        x := a.op
        if x == NO_NODE { continue }
        // (An address handed over: what's under it may be written there.)
        if x < CONST && graph_kind_of(g, x) == .Op && graph_op_of(g, x) == .Address {
            p := graph_operands(g, x)[0].op
            void_escape(c, state, p, true, address = true)
            if var, path, ok := void_place_path(c, p); ok {
                for u in void_under(c, var, path, true) {
                    uk := c.keys[u]
                    void_set(c, state, u, void_fact_is(c, uk.home), c.vf.why[uk.home] if uk.home >= 0 else "")
                }
            }
            continue
        }
        if to_c || k >= len(sig.params) { continue }
        if void_is_value(sig.params[k].type_) {
            is_void, _ := void_value_is(c, x, a.out, state)
            if !is_void { continue }
            why := fmt.tprintf("'%s' is given void for '%s' at %s", name, sig.params[k].name, void_where(c, graph_origin(g, x)))
            if callee != nil {
                void_raise(c, void_fact(c.vf, {.Param, rawptr(callee), "", k}), why)
            } else {
                void_raise(c, void_fact(c.vf, {.Sig_Param, nil, void_sig(sig), k}), why)
            }
        } else if p := void_value_place(g, x); p != NO_NODE {
            void_escape(c, state, p, true)   // (a struct passed by value: its fields, there)
        }
    }
}

// --- one operation --------------------------------------------------------------------

@(private="file")
void_op :: proc(c: ^Void_Code, op: Node_Id, state: []u64, reporting: bool) {
    g := c.g
    if op >= CONST || graph_kind_of(g, op) != .Op { return }
    ops := graph_operands(g, op)
    #partial switch graph_op_of(g, op) {
    case .Deref:
        if len(ops) > 0 { void_read_through(c, state, op, ops[0].op, true, reporting) }
    case .Call:
        if graph_called(g, op) == nil && len(ops) > 0 {
            void_read_through(c, state, op, ops[0].op, false, reporting)
        }
        void_args(c, state, op)
        // (A call's results go where its outputs are written: void_write.)
    case .Construct:
        void_args(c, state, op)
        if len(ops) > 0 && void_is_place(g, ops[0].op) {
            if flow_is_literal_name(graph_name(g, op)) {
                void_zero(c, state, ops[0].op, .Literal, graph_origin(g, op))
            } else {
                void_copy_under(c, state, ops[0].op, NO_NODE)
                void_construct(c, state, ops[0].op, graph_called(g, op), graph_origin(g, op))
            }
        }
    case .Assert:
        if len(ops) == 0 { break }
        if graph_written(g, op) == .Explicit {
            void_narrow(c, state, ops[0], true)
        } else if graph_name(g, op) == VOID_READ_TEXT {
            cond := ops[0].op
            if cond < CONST && graph_kind_of(g, cond) == .Op && graph_op_of(g, cond) == .Compare {
                void_read_through(c, state, op, graph_operands(g, cond)[0].op, false, reporting)
            }
        }
    case .Write:
        if len(ops) < 2 || ops[0].op == NO_NODE { break }
        void_write(c, state, ops[0].op, ops[1], graph_origin(g, op))
    case .Fill:
        if len(ops) < 2 || ops[0].op == NO_NODE { break }
        // (Every item one value.)
        if void_is_value(graph_type(g, ops[1].op)) {
            is_void, why := void_value_is(c, ops[1].op, ops[1].out, state)
            if var, path, ok := void_place_path(c, ops[0].op); ok {
                for u in void_under(c, var, path, false) { void_set(c, state, u, is_void, why) }
            } else if is_void {
                void_raise(c, void_typed_fact(c, graph_type(g, ops[1].op)), void_store_why(c, ops[0].op, graph_origin(g, op)))
            }
        }
    case .Zero:
        if len(ops) == 0 || ops[0].op == NO_NODE { break }
        // (`{all 0}`'s is named so; a bare declaration's is unnamed, on a
        // variable as written; an array literal's, the rest.)
        mode := Void_Zero.Literal
        if graph_name(g, op) == "{0}" {
            mode = .All
        } else if graph_written(g, op) == .Synthetic && graph_name(g, op) == "" {
            if var, _, ok := void_place_path(c, ops[0].op); ok && (g.kind[var] == .Field || g.kind[var] == .Local && g.written[var] == .Explicit) { mode = .Bare }
        }
        void_zero(c, state, ops[0].op, mode, graph_origin(g, op))
    case .Address:
        // (A pointer to a followed place, kept or passed on: what may be void
        // under it is, wherever it's read through. One handed straight to a
        // call is the call's: void_args.)
        if len(ops) > 0 && !c.call_addrs[op] { void_escape(c, state, ops[0].op, true) }
    case .Slice:
        // (A slice of a followed array: its items, wherever it's read.)
        if len(ops) > 0 { void_escape(c, state, ops[0].op, false) }
    case .Return:
        if c.fun == nil || c.fun.kind != .Fun { break }
        for o, k in ops {
            if k >= len(c.fun.return_types) { break }
            if void_is_value(c.fun.return_types[k]) {
                is_void, why := void_value_is(c, o.op, o.out, state)
                if !is_void { continue }
                what := fmt.tprintf("'%s' can return void (%s)", c.fun.source_name if c.fun.source_name != "" else c.fun.name, why)
                void_raise(c, void_fact(c.vf, {.Result, rawptr(c.fun), "", k}), what)
                void_raise(c, void_fact(c.vf, {.Sig_Result, nil, void_sig(c.fun), k}), what)
            } else if p := void_value_place(g, o.op); p != NO_NODE {
                void_escape(c, state, p, true)
            }
        }
    }
}

// Whether x names a place: a variable, a field, an element, what a pointer
// points at.
@(private="file")
void_is_place :: proc(g: ^Program_Graph, x: Node_Id) -> bool {
    if x == NO_NODE || x >= READ || (x >= CONST && x < LEAF) { return false }
    if graph_is_leaf(x) { return true }
    #partial switch graph_op_of(g, x) {
    case .Var, .Global, .Field, .Index, .View, .Deref, .Variant, .Swizzle, .Slice: return true
    }
    return false
}

@(private="file")
flow_is_literal_name :: proc(name: string) -> bool {
    return len(name) >= 2 && name[len(name) - 2:] == "{}"
}

// A read through x (a place holding a pointer, `deref`; else a value): an
// error where it may be void. Past it, x isn't — had it been, the program
// would have crashed here.
@(private="file")
void_read_through :: proc(c: ^Void_Code, state: []u64, op: Node_Id, x: Node_Id, deref: bool, reporting: bool) {
    g := c.g
    is_void: bool
    why: string
    p := x if deref else void_value_place(g, x)
    if deref {
        is_void, why = void_place_is(c, x, state)
    } else {
        is_void, why = void_value_is(c, x, 0, state)
    }
    if !is_void { return }
    if reporting && c.found != nil {
        name := void_text(c, x)
        append(c.found, Flow_Finding{.Void_Read, graph_origin(g, x), fmt.aprintf(TYPE_VOID_READ, name, name, name, why)})
    }
    if p != NO_NODE { void_set(c, state, void_key(c, p), false, "") }
}

// --- tests ----------------------------------------------------------------------------

// A branch's way out: what its condition says, when it took that way.
@(private="file")
void_edge :: proc(c: ^Void_Code, last: Node_Id, k: int, state: []u64) {
    g := c.g
    if graph_op_of(g, last) != .Branch || k > 1 { return }
    ops := graph_operands(g, last)
    if len(ops) == 0 { return }
    void_narrow(c, state, ops[0], k == 0)
}

// What a condition being `truth` says isn't void: each such place's key
// cleared.
@(private="file")
void_narrow :: proc(c: ^Void_Code, state: []u64, cond: Operand, truth: bool, depth := 0) {
    g := c.g
    x := cond.op
    if x == NO_NODE || depth > 32 { return }
    if p := void_value_place(g, x); p != NO_NODE {
        // (An `and` / `or`: true, an `and`'s sides each were; false, an `or`'s.)
        if graph_is_leaf(p) {
            v := graph_refers(g, p)
            if writes, is_slot := c.slots[v]; is_slot {
                word := graph_name(g, v)
                if (word == "and") == truth {
                    for w in writes { void_narrow(c, state, w, truth, depth + 1) }
                }
            }
        }
        return
    }
    if x >= CONST || graph_kind_of(g, x) != .Op { return }
    ops := graph_operands(g, x)
    #partial switch graph_op_of(g, x) {
    case .Unary:
        if graph_name(g, x) == "not" && len(ops) == 1 { void_narrow(c, state, ops[0], !truth, depth + 1) }
    case .Compare:
        if len(ops) != 2 { return }
        name := graph_name(g, x)
        if name != "==" && name != "!=" { return }
        other := ops[0].op if void_is_void(g, ops[1].op) else ops[1].op if void_is_void(g, ops[0].op) else NO_NODE
        if other == NO_NODE || (name == "!=") != truth { return }
        if p := void_value_place(g, other); p != NO_NODE { void_set(c, state, void_key(c, p), false, "") }
    }
}
