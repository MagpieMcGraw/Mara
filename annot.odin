package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"

// ---------------------------------------------------------------------------
// The annotations (design/annotated_tree.md): what the checker finds about
// each node, kept per instance beside the flat tree, for the passes after it.
//
// A node is read in an instance. Instance 0 is the tree as written; each
// generic fun's or struct's instance, numbered as it is made, is its
// template's nodes checked again with its type params bound (the builder's
// salt: tc_sid). Instance 0's columns span the whole tree; an instance's,
// its template's nodes. A template itself is syntax only: instance 0 says
// nothing about its nodes.
// ---------------------------------------------------------------------------

Instance_Id :: distinct u32

Instance :: struct {
    lo, hi: Tree_Id,       // its nodes: [lo, hi]
    scope:  ^Type_Scope,   // the fun or struct it is; nil for instance 0
}

// What a name refers to: the token that declares it — 0 when no source does
// (a builtin) — and what kind of name it is.
Ref :: struct {
    decl: Token_Id,
    kind: Ref_Kind,
}

Ref_Kind :: enum u8 {
    None,
    Local,     // a body's variable: a local, a loop's, a match arm's binding, a `let`
    Param,
    Result,    // a named result
    Field,     // a struct's field: declared in its body, or reached through a value
    Global,    // a module's variable
    Const,
    Variant,   // an enum's, a union's or an error set's
    Fun,       // a fun, a method, a struct's constructor (its struct)
    Type,      // a struct, a union, an enum, a distinct type, a type param
    Module,    // a module, by the `use` that names it
    Builtin,   // what no source declares: `void`, `this_program`, a builtin type
}

// What a param of a call receives: an argument written at the call, the
// receiver a method is called on, or the param's default — its expression in
// its fun's signature, run at the call (a group's one value: which of its
// results), or `#caller_name`'s, given where the call is.
Arg :: struct {
    node: Tree_Id,
    kind: Arg_Kind,
    slot: i32,   // a default that is one of its group's value's results; -1: none
}

Arg_Kind :: enum u8 { Written, Receiver, Default, Call_Site }

// How a call is made: a fun or a constructor named, one a dispatch chose, a
// generic's instance, a builtin, a distinct type's conversion, or through a
// fun's value.
Call_Form :: enum u8 { Fun, Dispatch, Generic, Builtin, Conversion, Value }

// A variable a fun's or a struct's body binds: the token that declares it,
// what kind of name it is (a param, a named result, a local — a loop's, a
// match arm's binding, a `let`'s), its type as bound. (A union match's arms
// that rebind their subject's name bind it each at its own payload: one token,
// several variables, told apart by their types.)
Var_Decl :: struct {
    tok:   Token_Id,
    kind:  Ref_Kind,
    type_: Type,
}

// Code checked in an instance: a fun's or a struct's body — what its nodes
// [lo, hi] (its definition's) run in — or a constant's value (no scope: what
// it calls, it runs at no function's call).
Annot_Body :: struct {
    scope:  ^Type_Scope,
    inst:   Instance_Id,
    lo, hi: Tree_Id,
}

Annotations :: struct {
    instances: [dynamic]Instance,
    types:     [dynamic][]Type,   // each instance's nodes' types, by n - lo
    refs:      [dynamic][]Ref,    // what each name refers to (a declaration's name, itself)

    // What only some nodes have, by node and instance (annot_key).
    callees:    map[Syntax_Id]^Type_Scope,   // a call's fun, or struct (its constructor)
    args:       map[Syntax_Id][]Arg,         // ... what each of its params receives, in order
    forms:      map[Syntax_Id]Call_Form,     // ... how it is made
    overrides:  map[Syntax_Id]bool,          // a literal statement that writes into the variable it names (`v{x = 1}`)
    receivers:  map[Syntax_Id]bool,          // a method call whose receiver is built as a value first
    call_names: map[Syntax_Id]string,        // a method call's name, as its qualifier resolved it
    size_of:    map[Syntax_Id]Type,          // a size_of's type
    dot_bases:  map[Syntax_Id]Tree_Id,       // a `.len` in a subscript: the subscript's base

    // Each fun's and struct's variables, in the order its body binds them.
    vars: map[^Type_Scope][dynamic]Var_Decl,
    // Each body and constant value checked, in the order checked.
    bodies: [dynamic]Annot_Body,
}

// A node in an instance, as one key: the builder's Syntax_Id (tc_sid).
annot_key :: proc(i: Instance_Id, n: Tree_Id) -> Syntax_Id {
    return Syntax_Id(u64(i) << 32 | u64(n))
}

annot_new :: proc(t: ^Tree) -> ^Annotations {
    a := new(Annotations)
    append(&a.instances, Instance{lo = 0, hi = Tree_Id(len(t.tag) - 1)})
    append(&a.types, make([]Type, len(t.tag)))
    append(&a.refs, make([]Ref, len(t.tag)))
    return a
}

// A generic's instance, its template's nodes [lo, hi]: its number.
annot_instance :: proc(a: ^Annotations, lo, hi: Tree_Id, scope: ^Type_Scope) -> Instance_Id {
    append(&a.instances, Instance{lo = lo, hi = hi, scope = scope})
    append(&a.types, make([]Type, int(hi - lo) + 1))
    append(&a.refs, make([]Ref, int(hi - lo) + 1))
    return Instance_Id(len(a.instances) - 1)
}

annot_ref :: proc(a: ^Annotations, i: Instance_Id, n: Tree_Id) -> Ref {
    return a.refs[i][n - a.instances[i].lo]
}

annot_set_ref :: proc(a: ^Annotations, i: Instance_Id, n: Tree_Id, r: Ref) {
    a.refs[i][n - a.instances[i].lo] = r
}

annot_type :: proc(a: ^Annotations, i: Instance_Id, n: Tree_Id) -> Type {
    return a.types[i][n - a.instances[i].lo]
}

annot_set_type :: proc(a: ^Annotations, i: Instance_Id, n: Tree_Id, t: Type) {
    a.types[i][n - a.instances[i].lo] = t
}

// A variable `owner`'s body binds.
annot_add_var :: proc(a: ^Annotations, owner: ^Type_Scope, v: Var_Decl) {
    vars := a.vars[owner]
    append(&vars, v)
    a.vars[owner] = vars
}

// The variable of `owner` its token declares, at type `t` when the token
// declares several (a union match's rebound subject): its index in the
// owner's variables, or -1.
annot_var :: proc(a: ^Annotations, owner: ^Type_Scope, tok: Token_Id, t: Type) -> int {
    vars, _ := a.vars[owner]
    first := -1
    for v, i in vars {
        if v.tok != tok { continue }
        if types_equal(solidify_type(v.type_), solidify_type(t)) { return i }
        if first < 0 { first = i }
    }
    return first
}

// --- the check --------------------------------------------------------------

// MARA_ANNOT=check: the annotations, checked against what the checker built
// (design/annotated_tree.md, stage 1's proof).
//
//   - Complete: each name the checker typed in an instance — an identifier, a
//     variant, a member, a call's name, a type's — says what it names.
//   - Agreeing with the graph: each variable operation written in the source
//     refers to the declaration its name's annotation names (the same name,
//     declared inside that declaration's statement); each call's Calls edge
//     runs the callee its annotation names.
//
// One line a problem, then a count: "annot: N problems".
annot_check :: proc(a: ^Annotations, t: ^Tree, pc: ^Program_Code, errors: int) {
    if os.get_env("MARA_ANNOT", context.temp_allocator) != "check" || errors > 0 { return }
    names, vars, calls, args, loops, decls := 0, 0, 0, 0, 0, 0
    problems := 0
    report :: proc(problems: ^int, t: ^Tree, n: Tree_Id, inst: Instance_Id, format: string, args: ..any) {
        problems^ += 1
        sp := tree_span(t, n)
        fmt.printf("annot: %s:%d:%d (instance %d, %v '%s'): ", filepath.base(span_file(sp)), span_line(sp), span_col(sp),
            inst, t.tag[n], token_text(build_tokens[t.main[n]]))
        fmt.printf(format, ..args)
        fmt.println()
    }

    // Complete.
    for inst, i in a.instances {
        for n in inst.lo ..= inst.hi {
            if n == 0 || annot_type(a, Instance_Id(i), n) == nil { continue }
            #partial switch t.tag[n] {
            case .Ident, .Dot_Ident, .Field, .Call, .Method_Call, .Type_Name, .Type_Generic, .Type_Keyword:
            case: continue
            }
            if _, is_error := annot_type(a, Instance_Id(i), n).(Type_Error); is_error && t.tag[n] != .Call && t.tag[n] != .Method_Call { continue }
            if token_text(build_tokens[t.main[n]]) == "_" { continue }
            names += 1
            if annot_ref(a, Instance_Id(i), n).kind == .None { report(&problems, t, n, Instance_Id(i), "names nothing") }
        }
    }

    // Agreeing with the graph: its operations, found where they are written.
    if len(pc.codes) > 0 {
        at := make(map[Span][dynamic]Tree_Id, len(t.tag))
        defer {
            for _, list in at { delete(list) }
            delete(at)
        }
        for n in 1 ..< len(t.tag) {
            sp := tree_span(t, Tree_Id(n))
            if sp not_in at { at[sp] = make([dynamic]Tree_Id) }
            append(&at[sp], Tree_Id(n))
        }
        Made :: struct { g: ^Program_Graph, op: Node_Id }
        made := make(map[Syntax_Id]Made, len(a.callees), context.temp_allocator)   // (the annotated calls the graph makes: each one's operation, in its code)
        // (An operation's instance: the one its code's body was checked in.)
        inst_of := make(map[^Type_Scope]Instance_Id, len(a.bodies), context.temp_allocator)
        for body in a.bodies { if body.scope != nil { inst_of[body.scope] = body.inst } }
        instance :: proc(g: ^Program_Graph, inst_of: map[^Type_Scope]Instance_Id, op: Node_Id) -> Instance_Id {
            if ts := graph_caller(g, op); ts != nil { return inst_of[ts] or_else 0 }
            return 0
        }
        for g in pc.codes {
            for id in 0 ..< len(g.kind) {
                op := Node_Id(id)
                if g.kind[op] != .Op { continue }
                // (What the graph says: a variable's declaration, written — not
                // the compiler's own; a call's callee.)
                d := NO_NODE
                want: ^Type_Scope
                #partial switch g.op[op] {
                case .Var:
                    if g.written[op] != .Explicit { continue }
                    d = g.refers[op]
                    if d < 0 || g.origin[d].at == 0 { continue }
                    #partial switch g.kind[d] {
                    case .Local, .Param, .Result, .Field:
                    case: continue
                    }
                case .Call, .Construct:
                    if want = graph_called(g, op); want == nil { continue }
                case:
                    continue
                }
                i := instance(g, inst_of, op)
                compared := false
                nodes, _ := at[g.origin[op]]   // (none: a node it isn't written at, its own span)
                for n in nodes {
                    n := n
                    if n < a.instances[i].lo || n > a.instances[i].hi { continue }
                    if d != NO_NODE {
                        // (A name: written as itself, as a count in a type, as the
                        // fun value a call calls, as what an override writes into.)
                        if t.tag[n] == .Literal && t.a[n] != 0 && t.tag[t.a[n]] == .Ident { n = Tree_Id(t.a[n]) }
                        #partial switch t.tag[n] {
                        case .Ident, .Type_Name, .Call, .Method_Call:
                            if token_text(build_tokens[t.main[n]]) != graph_name(g, d) { continue }
                        case: continue
                        }
                        compared = true
                        vars += 1
                        r := annot_ref(a, i, n)
                        within := r.decl != 0 && r.decl >= g.origin[d].tok && r.decl < g.origin[d].end
                        if r.decl == 0 || token_text(build_tokens[r.decl]) != graph_name(g, d) || !within {
                            report(&problems, t, n, i, "refers to %v %v; the graph's declaration is %v '%s' at %d:%d",
                                r.kind, r.decl, g.kind[d], graph_name(g, d), span_line(g.origin[d]), span_col(g.origin[d]))
                        }
                    } else {
                        #partial switch t.tag[n] {
                        case .Call, .Method_Call, .Binary, .Unary, .Literal:
                        case: continue
                        }
                        compared = true
                        calls += 1
                        made[annot_key(i, n)] = {g, op}
                        got := a.callees[annot_key(i, n)] or_else nil
                        if got != want {
                            report(&problems, t, n, i, "calls %s; the graph's Calls edge runs %s", got.name if got != nil else "nothing", want.name)
                        }
                    }
                }
                // (A variable written where no name is — a declaration's, an
                // assignment's: the name its statement writes.)
                if !compared && d != NO_NODE && g.stmt[op] >= 0 {
                    stmt_nodes, _ := at[g.stmts[g.stmt[op]].span]
                    for sn in stmt_nodes {
                        sn := sn
                        if t.tag[sn] == .Using { sn = Tree_Id(t.a[sn]) }   // (its declaration's)
                        if sn < a.instances[i].lo || sn > a.instances[i].hi { continue }
                        targets: []Tree_Id
                        #partial switch t.tag[sn] {
                        case .Decl:     targets = decl_view(t, sn).targets
                        case .Assign:   targets = tree_list(t, t.a[sn])
                        case .Compound: targets = []Tree_Id{Tree_Id(t.a[sn])}
                        }
                        for n in targets {
                            if t.tag[n] != .Ident || token_text(build_tokens[t.main[n]]) != graph_name(g, d) { continue }
                            compared = true
                            vars += 1
                            r := annot_ref(a, i, n)
                            if r.decl == 0 || r.decl < g.origin[d].tok || r.decl >= g.origin[d].end {
                                report(&problems, t, n, i, "refers to %v %v; the graph's declaration is %v '%s' at %d:%d",
                                    r.kind, r.decl, g.kind[d], graph_name(g, d), span_line(g.origin[d]), span_col(g.origin[d]))
                            }
                        }
                    }
                }
                // (A call made where no call is written — a bare declaration's
                // construction, a compound assignment's operator: on the name it
                // constructs, or on the statement.)
                if !compared && want != nil && g.stmt[op] >= 0 {
                    dest := ""
                    if ops := graph_operands(g, op); len(ops) > 0 && ops[0].op >= 0 && g.kind[ops[0].op] == .Op && g.op[ops[0].op] == .Var {
                        dest = graph_name(g, ops[0].op)
                    }
                    stmt_nodes, _ := at[g.stmts[g.stmt[op]].span]
                    for sn in stmt_nodes {
                        sn := sn
                        if t.tag[sn] == .Using { sn = Tree_Id(t.a[sn]) }   // (its declaration's)
                        if sn < a.instances[i].lo || sn > a.instances[i].hi { continue }
                        on := make([dynamic]Tree_Id, context.temp_allocator)
                        #partial switch t.tag[sn] {
                        case .Decl:
                            for n in decl_view(t, sn).targets {
                                if t.tag[n] == .Ident && token_text(build_tokens[t.main[n]]) == dest { append(&on, n) }
                            }
                        case .Compound, .Assign:
                            append(&on, sn)
                        }
                        for n in on {
                            compared = true
                            calls += 1
                            made[annot_key(i, n)] = {g, op}
                            got := a.callees[annot_key(i, n)] or_else nil
                            if got != want {
                                report(&problems, t, n, i, "calls %s; the graph's Calls edge runs %s", got.name if got != nil else "nothing", want.name)
                            }
                        }
                    }
                }
                // (A loop's variable, written by the loop: declared by a token
                // in its header, no name node — what reads it is checked.)
                if !compared && d != NO_NODE && g.stmt[op] >= 0 {
                    stmt_nodes, _ := at[g.stmts[g.stmt[op]].span]
                    for sn in stmt_nodes {
                        if t.tag[sn] != .For_Range && t.tag[sn] != .For_Each { continue }
                        v := for_view(t, sn)
                        for tok in ([]Token_Id{v.var, v.elem, v.index}) {
                            if tok != 0 && token_text(build_tokens[tok]) == graph_name(g, d) && tok >= g.origin[d].tok && tok < g.origin[d].end {
                                compared = true
                                loops += 1
                                break
                            }
                        }
                    }
                }
                if !compared {
                    tags := make([dynamic]Tree_Tag, context.temp_allocator)
                    for n in nodes { append(&tags, t.tag[n]) }
                    problems += 1
                    fmt.printf("annot: %v '%s' at %s:%d:%d is found at no node (nodes there: %v)\n", g.op[op], graph_name(g, op),
                        filepath.base(span_file(g.origin[op])), span_line(g.origin[op]), span_col(g.origin[op]), tags[:])
                }
            }
        }
        // And the other way: each call annotated is one the graph makes — but
        // a call through a function value (the honest seam: no Calls edge).
        for key, ts in a.callees {
            if key in made { continue }
            i, n := Instance_Id(u64(key) >> 32), Tree_Id(u64(key) & 0xffff_ffff)
            #partial switch annot_ref(a, i, n).kind {
            case .Local, .Param, .Result, .Field, .Global: continue
            }
            report(&problems, t, n, i, "is annotated as calling %s; the graph makes no such call", ts.name if ts != nil else "nothing")
        }
        // Each call's arguments: one a param, and each the graph passes
        // computed from what its annotation says the param receives — an
        // operation on its way written inside that node (a widen at the call
        // is not). A `#caller_name` is the call site's: no node of its own.
        inside :: proc(t: ^Tree, n: Tree_Id, sp: Span) -> bool {
            return sp.tok >= t.first[n] && sp.end <= t.end[n] && sp.end > sp.tok
        }
        // (A temporary the compiler holds a value in — a literal a slice
        // views, bytes read as an array: what is written into it.)
        // (Each code's writes into its temporaries.)
        writes_of :: proc(g: ^Program_Graph) -> map[Node_Id][dynamic]Node_Id {
            writes := make(map[Node_Id][dynamic]Node_Id, context.temp_allocator)
            for id in 0 ..< len(g.kind) {
                if dst := graph_whole_write_dest(g, Node_Id(id)); dst != NO_NODE {
                    if d := g.refers[dst]; d >= 0 && g.written[d] != .Explicit {
                        if d not_in writes { writes[d] = make([dynamic]Node_Id, context.temp_allocator) }
                        append(&writes[d], Node_Id(id))
                    }
                }
            }
            return writes
        }
        code_writes := make(map[^Program_Graph]map[Node_Id][dynamic]Node_Id, context.temp_allocator)
        // (Whether an argument's value comes from inside a node: an operation
        // on its way there written inside it — a few steps back at most.)
        from :: proc(t: ^Tree, g: ^Program_Graph, writes: map[Node_Id][dynamic]Node_Id, n: Tree_Id, v: Node_Id) -> bool {
            todo := make([dynamic]Node_Id, context.temp_allocator)
            seen := make(map[Node_Id]bool, context.temp_allocator)
            append(&todo, v)
            for steps := 0; len(todo) > 0 && steps < 64; steps += 1 {
                x := pop_front(&todo)
                if x < 0 || x in seen { continue }
                seen[x] = true
                if inside(t, n, g.origin[x]) { return true }
                for o in graph_operands(g, x) { append(&todo, o.op) }
                if g.kind[x] == .Op && g.op[x] == .Var && g.refers[x] >= 0 {
                    ws, _ := writes[g.refers[x]]   // (none: a variable the compiler doesn't hold a value in)
                    for w in ws { append(&todo, w) }
                }
            }
            return false
        }
        for key, m in made {
            g, op := m.g, m.op
            if g not_in code_writes { code_writes[g] = writes_of(g) }
            writes := code_writes[g]
            i, n := Instance_Id(u64(key) >> 32), Tree_Id(u64(key) & 0xffff_ffff)
            given, has := a.args[key]
            if !has {
                report(&problems, t, n, i, "calls with no arguments annotated")
                continue
            }
            passed := graph_operands(g, op)
            if g.op[op] == .Construct { passed = passed[1:] }   // (its destination first)
            if len(given) != len(passed) {
                report(&problems, t, n, i, "is annotated with %d arguments; the graph passes %d", len(given), len(passed))
                continue
            }
            for arg, j in given {
                args += 1
                if arg.kind == .Call_Site { continue }
                if !from(t, g, writes, arg.node, passed[j].op) {
                    what := "nothing"
                    if v := passed[j].op; v >= 0 {
                        what = fmt.tprintf("%v '%s' from %d:%d", g.op[v], graph_name(g, v), span_line(g.origin[v]), span_col(g.origin[v]))
                    }
                    report(&problems, t, n, i, "param %d is annotated as receiving %v %v; the graph passes %s",
                        j + 1, arg.kind, t.tag[arg.node], what)
                }
            }
        }

        // Each body's variables: the graph's declarations written in its code
        // (its params, named results and locals — not a nested fun's), each
        // the token that declares it, of the same name and type.
        report_var :: proc(problems: ^int, tok: Token_Id, owner: ^Type_Scope, format: string, args: ..any) {
            problems^ += 1
            sp := Span{at = tok}
            fmt.printf("annot: %s:%d:%d (%s's '%s'): ", filepath.base(span_file(sp)), span_line(sp), span_col(sp),
                owner.name, token_text(build_tokens[tok]) if tok != 0 else "?")
            fmt.printf(format, ..args)
            fmt.println()
        }
        for g in pc.codes {
            if g.kind[0] != .Fun && g.kind[0] != .Struct { continue }
            ts := graph_type(g, 0).(^Type_Scope)
            vars_of, _ := a.vars[ts]
            have := make([]bool, len(vars_of), context.temp_allocator)
            for id := Node_Id(1); id <= g.end; id += 1 {
                #partial switch g.kind[id] {
                case .Fun, .Struct:
                    id = graph_last(g, id)
                    continue
                case .Param, .Local, .Result:
                case:
                    continue
                }
                if g.written[id] != .Explicit { continue }
                tok := g.decl_tok[id]
                if tok == 0 {
                    report_var(&problems, tok, ts, "the graph's %v '%s' names no token", g.kind[id], graph_name(g, id))
                    continue
                }
                i := annot_var(a, ts, tok, graph_type(g, id))
                if i < 0 {
                    report_var(&problems, tok, ts, "the graph's %v is none of its annotated variables", g.kind[id])
                    continue
                }
                v := vars_of[i]
                decls += 1
                have[i] = true
                if token_text(build_tokens[tok]) != graph_name(g, id) {
                    report_var(&problems, tok, ts, "the graph's %v is named '%s'", g.kind[id], graph_name(g, id))
                }
                // (A distinct type the graph holds as its base: a destructured local's, a loop's element.)
                if !types_equal(distinct_base(solidify_type(v.type_)), distinct_base(solidify_type(graph_type(g, id)))) {
                    report_var(&problems, tok, ts, "is annotated %s; the graph's %v is %s", type_name(v.type_), g.kind[id], type_name(graph_type(g, id)))
                }
            }
            for v, i in vars_of {
                if !have[i] { report_var(&problems, v.tok, ts, "is an annotated %v the graph declares nowhere", v.kind) }
            }
        }
    }
    fmt.printf("annot: %d problems (%d names, %d variables, %d calls, %d arguments checked; %d loop variables written by their loop; %d declarations)\n",
        problems, names, vars, calls, args, loops, decls)
}
