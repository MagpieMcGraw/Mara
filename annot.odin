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
    types:     [dynamic][]Type_Id,   // each instance's nodes' types, by n - lo
    type_table: ^Type_Table,         // ... their table: the program's types
    refs:      [dynamic][]Ref,    // what each name refers to (a declaration's name, itself)
    ops:       [dynamic][]Op_At,  // where each was lowered to, once the program is (graph_index_ops)

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

// ... and back.
annot_split :: proc(key: Syntax_Id) -> (Instance_Id, Tree_Id) {
    return Instance_Id(u64(key) >> 32), Tree_Id(u64(key) & 0xffff_ffff)
}

annot_new :: proc(t: ^Tree) -> ^Annotations {
    a := new(Annotations)
    a.type_table = type_table_new()
    append(&a.instances, Instance{lo = 0, hi = Tree_Id(len(t.tag) - 1)})
    append(&a.types, make([]Type_Id, len(t.tag)))
    append(&a.refs, make([]Ref, len(t.tag)))
    return a
}

// A generic's instance, its template's nodes [lo, hi]: its number.
annot_instance :: proc(a: ^Annotations, lo, hi: Tree_Id, scope: ^Type_Scope) -> Instance_Id {
    append(&a.instances, Instance{lo = lo, hi = hi, scope = scope})
    append(&a.types, make([]Type_Id, int(hi - lo) + 1))
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
    return a.type_table.types[a.types[i][n - a.instances[i].lo]]
}

annot_set_type :: proc(a: ^Annotations, i: Instance_Id, n: Tree_Id, t: Type) {
    a.types[i][n - a.instances[i].lo] = type_id(a.type_table, t)
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
//     runs the callee its annotation names — each checked at the tree node it
//     was lowered from.
//
// One line a problem, then a count: "annot: N problems". Then the build
// stops: the check is all it's for (no code, no program to scan).
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

    // Agreeing with the graph: each operation checked at the tree node it
    // was lowered from (Program_Graph.syntax).
    if len(pc.codes) > 0 {
        Made :: struct { g: ^Program_Graph, op: Node_Id }
        made := make(map[Syntax_Id]Made, len(a.callees), context.temp_allocator)   // (the annotated calls the graph makes: each one's operation, in its code)
        // (A default's nodes — what a call leaving it off lowers as the call's,
        // Graph_Builder.pin.)
        in_default := make(map[Tree_Id]bool, context.temp_allocator)
        defaults := make([dynamic]Span, context.temp_allocator)   // (where each is written)
        for _, given in a.args {
            for arg in given {
                if arg.kind == .Default && arg.node != 0 && arg.node not_in in_default {
                    for n in tree_lo(t, arg.node) ..= arg.node { in_default[n] = true }
                    append(&defaults, tree_span(t, arg.node))
                }
            }
        }
        on := make([dynamic]Tree_Id, context.temp_allocator)
        for g in pc.codes {
            for id in 0 ..= int(g.end) {
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
                // (Written in a default a call leaves off, lowered as the
                // call's: its calls are the default's, checked as they're
                // annotated there.)
                pinned := false
                for sp in defaults {
                    if o := g.origin[op]; o.tok >= sp.tok && o.end <= sp.end { pinned = true }
                }
                if pinned { continue }
                i, at := annot_split(g.syntax[op])
                // (Where it's checked: its node — a name, the name an override
                // writes into; or what its statement writes: a declaration's
                // names, an assignment's targets, the statement.)
                clear(&on)
                n := at
                if t.tag[n] == .Using { n = Tree_Id(t.a[n]) }   // (its declaration's)
                if d != NO_NODE && t.tag[n] == .Literal && t.a[n] != 0 && t.tag[t.a[n]] == .Ident { n = Tree_Id(t.a[n]) }
                #partial switch t.tag[n] {
                case .Decl:     append(&on, ..decl_view(t, n).targets)
                case .Assign:   append(&on, ..tree_list(t, t.a[n])); append(&on, n)
                case .Compound: append(&on, Tree_Id(t.a[n]), n)
                case:           append(&on, n)
                }
                compared := false
                if d != NO_NODE {
                    for x in on {
                        #partial switch t.tag[x] {
                        case .Ident, .Type_Name, .Call, .Method_Call:
                            if token_text(build_tokens[t.main[x]]) != graph_name(g, d) { continue }
                        case: continue
                        }
                        compared = true
                        vars += 1
                        r := annot_ref(a, i, x)
                        within := r.decl != 0 && r.decl >= g.origin[d].tok && r.decl < g.origin[d].end
                        if r.decl == 0 || token_text(build_tokens[r.decl]) != graph_name(g, d) || !within {
                            report(&problems, t, x, i, "refers to %v %v; the graph's declaration is %v '%s' at %d:%d",
                                r.kind, r.decl, g.kind[d], graph_name(g, d), span_line(g.origin[d]), span_col(g.origin[d]))
                        }
                    }
                    // (A loop's variable, written by its loop: declared by a
                    // token in its header, no name node — what reads it is checked.)
                    if !compared && (t.tag[n] == .For_Range || t.tag[n] == .For_Each) {
                        v := for_view(t, n)
                        for tok in ([]Token_Id{v.var, v.elem, v.index}) {
                            if tok != 0 && token_text(build_tokens[tok]) == graph_name(g, d) && tok >= g.origin[d].tok && tok < g.origin[d].end {
                                compared = true
                                loops += 1
                                break
                            }
                        }
                    }
                } else {
                    // (A call: written, an operator's, a literal's, a union's
                    // variant named as a value; a bare declaration's
                    // construction, on the name it constructs; a compound
                    // assignment's operator, on the statement.)
                    for x in on {
                        key := annot_key(i, x)
                        got, annotated := a.callees[key]
                        if !annotated { continue }
                        compared = true
                        calls += 1
                        made[key] = {g, op}
                        if got != want {
                            report(&problems, t, x, i, "calls %s; the graph's Calls edge runs %s", got.name if got != nil else "nothing", want.name)
                        }
                        break
                    }
                }
                if !compared {
                    problems += 1
                    fmt.printf("annot: %v '%s' at %s:%d:%d is found at no node (its node: %v)\n", g.op[op], graph_name(g, op),
                        filepath.base(span_file(g.origin[op])), span_line(g.origin[op]), span_col(g.origin[op]), t.tag[at])
                }
            }
        }
        // And the other way: each call annotated is one the graph makes — but
        // a call through a function value (the honest seam: no Calls edge), or
        // one in a default (each call leaving it off makes it, as its own).
        for key, ts in a.callees {
            if key in made { continue }
            i, n := annot_split(key)
            if n in in_default { continue }
            #partial switch annot_ref(a, i, n).kind {
            case .Local, .Param, .Result, .Field, .Global: continue
            }
            report(&problems, t, n, i, "is annotated as calling %s; the graph makes no such call", ts.name if ts != nil else "nothing")
        }
        // Each call's arguments: one a param, and each the graph passes
        // computed from what its annotation says the param receives — an
        // operation on its way lowered from inside that node, as written (a
        // widening at the call is not). A default left off is the call's
        // (Graph_Builder.pin); a `#caller_name`, the call site's: no node of
        // its own.
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
        // (Whether an argument's value comes from a node, in an instance —
        // its nodes [lo, n]: an operation on its way there lowered from one
        // of them, as written — a few steps back at most.)
        from :: proc(g: ^Program_Graph, writes: map[Node_Id][dynamic]Node_Id, i: Instance_Id, lo, n: Tree_Id, v: Node_Id) -> bool {
            todo := make([dynamic]Node_Id, context.temp_allocator)
            seen := make(map[Node_Id]bool, context.temp_allocator)
            append(&todo, v)
            for steps := 0; len(todo) > 0 && steps < 64; steps += 1 {
                x := pop_front(&todo)
                if x < 0 || x in seen { continue }
                seen[x] = true
                if xi, xn := annot_split(g.syntax[x]); g.written[x] == .Explicit && xi == i && xn >= lo && xn <= n { return true }
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
            i, n := annot_split(key)
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
                ok := false
                #partial switch arg.kind {
                case .Call_Site: continue
                case .Default:   ok = passed[j].op >= 0 && g.syntax[passed[j].op] == g.syntax[op]   // (built as the call is)
                case:            ok = from(g, writes, i, tree_lo(t, arg.node), arg.node, passed[j].op)
                }
                if !ok {
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
                // (A distinct type the graph holds as its base: a destructured local's, a loop's element.
                // A width never decided, as the graph settles it: `p := &x`, x's never used as a width.)
                if !types_equal(distinct_base(solidify_type(graph_settled(v.type_))), distinct_base(solidify_type(graph_type(g, id)))) {
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
    os.exit(0)
}
