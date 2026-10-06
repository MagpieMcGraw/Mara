package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strings"

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

Annotations :: struct {
    instances: [dynamic]Instance,
    types:     [dynamic][]Type,   // each instance's nodes' types, by n - lo
    refs:      [dynamic][]Ref,    // what each name refers to (a declaration's name, itself)

    // What only some nodes have, by node and instance (annot_key).
    callees:    map[Syntax_Id]^Type_Scope,   // a call's fun, or struct (its constructor)
    call_names: map[Syntax_Id]string,        // a method call's name, as its qualifier resolved it
    size_of:    map[Syntax_Id]Type,          // a size_of's type
    dot_bases:  map[Syntax_Id]Tree_Id,       // a `.len` in a subscript: the subscript's base
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

// --- dump -------------------------------------------------------------------

// MARA_ANNOT=dump: each instance's annotated nodes, one a line in id order —
// its tag, where it is written, what was found about it.
annot_dump :: proc(a: ^Annotations, t: ^Tree) {
    if os.get_env("MARA_ANNOT", context.temp_allocator) != "dump" { return }
    sb := strings.builder_make()
    for inst, i in a.instances {
        if i == 0 {
            fmt.sbprintf(&sb, "instance 0: the tree\n")
        } else {
            fmt.sbprintf(&sb, "instance %d: %s [%d, %d]\n", i, inst.scope.name if inst.scope != nil else "?", inst.lo, inst.hi)
        }
        for n in inst.lo ..= inst.hi {
            key := annot_key(Instance_Id(i), n)
            line := strings.builder_make(context.temp_allocator)
            if ty := annot_type(a, Instance_Id(i), n); ty != nil { fmt.sbprintf(&line, " t=%s", type_name(ty)) }
            if r := annot_ref(a, Instance_Id(i), n); r.kind != .None {
                if r.decl != 0 {
                    tk := build_tokens[r.decl]
                    fmt.sbprintf(&line, " ref=%v:%s@%s:%d:%d", r.kind, token_text(tk), filepath.base(span_file(Span{at = r.decl})), span_line(Span{at = r.decl}), span_col(Span{at = r.decl}))
                } else {
                    fmt.sbprintf(&line, " ref=%v", r.kind)
                }
            }
            if ts := a.callees[key] or_else nil; ts != nil { fmt.sbprintf(&line, " callee=%s", ts.name) }
            if name, ok := a.call_names[key]; ok { fmt.sbprintf(&line, " call_name=%s", name) }
            if st, ok := a.size_of[key]; ok { fmt.sbprintf(&line, " size_of=%s", type_name(st)) }
            if base, ok := a.dot_bases[key]; ok { fmt.sbprintf(&line, " dot_base=%d", base) }
            if strings.builder_len(line) == 0 { continue }
            sp := tree_span(t, n)
            where_ := "-"
            if span_file(sp) != "" { where_ = fmt.tprintf("%s:%d:%d", filepath.base(span_file(sp)), span_line(sp), span_col(sp)) }
            fmt.sbprintf(&sb, "  %d %v %s%s\n", n, t.tag[n], where_, strings.to_string(line))
        }
    }
    fmt.print(strings.to_string(sb))
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
annot_check :: proc(a: ^Annotations, t: ^Tree, g: ^Program_Graph, errors: int) {
    if os.get_env("MARA_ANNOT", context.temp_allocator) != "check" || errors > 0 { return }
    names, vars, calls, unmatched := 0, 0, 0, 0
    verbose := os.get_env("MARA_ANNOT_VERBOSE", context.temp_allocator) != ""
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
    if len(g.kind) > 0 {
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
        inst_of := make(map[^Type_Scope]Instance_Id, len(a.instances), context.temp_allocator)
        for inst, i in a.instances { if inst.scope != nil { inst_of[inst.scope] = Instance_Id(i) } }
        // (An operation's instance: the generic instance's code it is in.)
        instance :: proc(g: ^Program_Graph, inst_of: map[^Type_Scope]Instance_Id, op: Node_Id) -> Instance_Id {
            for p := g.parent[op]; p != NO_NODE; p = g.parent[p] {
                if g.kind[p] != .Fun && g.kind[p] != .Struct { continue }
                if ts, is_scope := g.type_[p].(^Type_Scope); is_scope {
                    if i, ok := inst_of[ts]; ok { return i }
                }
            }
            return 0
        }
        for id in 0 ..< len(g.kind) {
            op := Node_Id(id)
            if g.kind[op] != .Op || g.written[op] != .Explicit { continue }
            // (What the graph says: a variable's declaration, written — not
            // the compiler's own; a call's callee.)
            d := NO_NODE
            want: ^Type_Scope
            #partial switch g.op[op] {
            case .Var:
                d = g.refers[op]
                if d < 0 || g.origin[d].at == 0 { continue }
                #partial switch g.kind[d] {
                case .Local, .Param, .Result, .Field:
                case: continue
                }
            case .Call:
                if want = graph_called(g, op); want == nil { continue }
            case:
                continue
            }
            i := instance(g, inst_of, op)
            compared := false
            nodes, _ := at[g.origin[op]]   // (none: a node it isn't written at, its own span)
            for n in nodes {
                if n < a.instances[i].lo || n > a.instances[i].hi { continue }
                if d != NO_NODE {
                    if t.tag[n] != .Ident { continue }
                    compared = true
                    vars += 1
                    r := annot_ref(a, i, n)
                    within := r.decl != 0 && r.decl >= g.origin[d].tok && r.decl < g.origin[d].end
                    if r.decl == 0 || token_text(build_tokens[r.decl]) != g.name[d] || !within {
                        report(&problems, t, n, i, "refers to %v %v; the graph's declaration is %v '%s' at %d:%d",
                            r.kind, r.decl, g.kind[d], g.name[d], span_line(g.origin[d]), span_col(g.origin[d]))
                    }
                } else {
                    if t.tag[n] != .Call && t.tag[n] != .Method_Call { continue }
                    compared = true
                    calls += 1
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
                    if sn < a.instances[i].lo || sn > a.instances[i].hi { continue }
                    targets: []Tree_Id
                    #partial switch t.tag[sn] {
                    case .Decl:     targets = decl_view(t, sn).targets
                    case .Assign:   targets = tree_list(t, t.a[sn])
                    case .Compound: targets = []Tree_Id{Tree_Id(t.a[sn])}
                    }
                    for n in targets {
                        if t.tag[n] != .Ident || token_text(build_tokens[t.main[n]]) != g.name[d] { continue }
                        compared = true
                        vars += 1
                        r := annot_ref(a, i, n)
                        if r.decl == 0 || r.decl < g.origin[d].tok || r.decl >= g.origin[d].end {
                            report(&problems, t, n, i, "refers to %v %v; the graph's declaration is %v '%s' at %d:%d",
                                r.kind, r.decl, g.kind[d], g.name[d], span_line(g.origin[d]), span_col(g.origin[d]))
                        }
                    }
                }
            }
            if !compared {
                unmatched += 1
                if verbose {
                    tags := make([dynamic]Tree_Tag, context.temp_allocator)
                    for n in nodes { append(&tags, t.tag[n]) }
                    fmt.printf("annot: unmatched %v %s at %s:%d:%d, nodes there: %v\n", g.op[op], g.name[op],
                        filepath.base(span_file(g.origin[op])), span_line(g.origin[op]), span_col(g.origin[op]), tags[:])
                }
            }
        }
    }
    fmt.printf("annot: %d problems (%d names, %d variables, %d calls checked; %d operations not found where written)\n",
        problems, names, vars, calls, unmatched)
}
