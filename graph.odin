package mara

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The program graph (design/program_graph.md): the program's shape, built from
// the checked syntax tree. Phase 1 of design/graph_retrofit.md — built beside
// the pipeline after checking; nothing reads it yet.
//
// Nodes are scopes and the names they declare (operations come next). Each
// fact is a column indexed by Node_Id. Ids are handed out depth-first in
// written order, so a scope's subtree is one run of ids: [id, last[id]].
//
// A generic's instances are nodes (they are what runs); the template is only
// syntax. Every instance points at the template as its origin.
// ---------------------------------------------------------------------------

Node_Id :: distinct i32
NO_NODE :: Node_Id(-1)

Node_Kind :: enum u8 {
    // Scopes
    Module, Struct, Union, Enum, Fun, Block,
    // Names declared in a scope
    Field, Param, Result, Local, Const, Import, Variant, Type_Def, Dispatch,
}

// How a node is written (design/program_graph.md, Identity and editing).
Written :: enum u8 { Explicit, Implied, Synthetic }

Program_Graph :: struct {
    kind:    [dynamic]Node_Kind,
    written: [dynamic]Written,
    parent:  [dynamic]Node_Id,
    last:    [dynamic]Node_Id,  // the subtree's last id
    name:    [dynamic]string,
    type_:   [dynamic]Type,     // has type; nil when the node has none
    origin:  [dynamic]Span,     // where it is written, or what caused a synthetic node
}

@(private="file")
Graph_Builder :: struct {
    g:       ^Program_Graph,
    checked: ^Checked_Program,
    // Checked types by the span of the statement declaring them. A generic's
    // instances share their template's span, so one span can hold several.
    by_span: map[Span][dynamic]Type,
}

// What a plain declaration becomes where it is written, and the struct whose
// fields it declares (their types come from the checked struct).
@(private="file")
Decl_Site :: struct {
    kind:  Node_Kind,    // .Field, .Local or .Const
    owner: ^Type_Scope,  // the struct, for .Field
}

build_program_graph :: proc(checked: ^Checked_Program, programs: map[string]^Program) -> Program_Graph {
    g: Program_Graph
    b := Graph_Builder{ g = &g, checked = checked }
    defer {
        for _, list in b.by_span { delete(list) }
        delete(b.by_span)
    }
    graph_index(&b)

    modules := make([dynamic]string, 0, len(programs), context.temp_allocator)
    for name in programs { append(&modules, name) }
    slice.sort(modules[:])
    for name in modules {
        m := graph_node(&b, .Module, .Explicit, NO_NODE, name, nil, {})
        for s in programs[name]^ { graph_stmt(&b, s, m, {kind = .Const}) }
        graph_close(&b, m)
    }
    when ODIN_DEBUG { graph_check_coverage(&b) }
    graph_dump(&g)
    return g
}

// --- building ---------------------------------------------------------------

@(private="file")
graph_node :: proc(b: ^Graph_Builder, kind: Node_Kind, written: Written, parent: Node_Id,
                   name: string, t: Type, origin: Span) -> Node_Id {
    g := b.g
    id := Node_Id(len(g.kind))
    append(&g.kind, kind)
    append(&g.written, written)
    append(&g.parent, parent)
    append(&g.last, id)
    append(&g.name, name)
    append(&g.type_, t)
    append(&g.origin, origin)
    return id
}

// End a scope: its subtree is everything added since it.
@(private="file")
graph_close :: proc(b: ^Graph_Builder, id: Node_Id) {
    b.g.last[id] = Node_Id(len(b.g.kind) - 1)
}

@(private="file")
graph_fatal :: proc(span: Span, format: string, args: ..any) -> ! {
    loc := format_location(span.file, span.line, span.col) if span.file != "" else ""
    emit_diagnostic(.Graph_Error, loc, format, ..args)
    flush_diagnostics()
    os.exit(1)
}

// The pointer behind a checked scope or type, for identity.
@(private="file")
graph_type_ptr :: proc(t: Type) -> rawptr {
    #partial switch v in t {
    case ^Type_Scope:    return v
    case ^Type_Union:    return v
    case ^Type_Enum:     return v
    case ^Type_Distinct: return v
    }
    return nil
}

@(private="file")
graph_index :: proc(b: ^Graph_Builder) {
    add :: proc(b: ^Graph_Builder, span: Span, t: Type) {
        if span == {} { return }
        if span not_in b.by_span { b.by_span[span] = {} }
        list := &b.by_span[span]
        for x in list { if graph_type_ptr(x) == graph_type_ptr(t) { return } }
        append(list, t)
    }
    t := b.checked.table
    for _, st in t.structs          { add(b, st.body_span, st) }
    for _, ft in t.funs             { add(b, ft.body_span, ft) }
    for _, ft in b.checked.functions { add(b, ft.body_span, ft) }
    for _, u in t.unions            { add(b, u.span, u) }
    for _, e in t.enums             { add(b, e.span, e) }
    for _, d in t.distinct_types    { add(b, d.span, d) }
    // The tables are maps; order a span's instances by name so ids are stable.
    for _, list in b.by_span {
        slice.sort_by(list[:], proc(x, y: Type) -> bool { return ask_type_name(x) < ask_type_name(y) })
    }
}

@(private="file")
graph_stmt :: proc(b: ^Graph_Builder, s: Stmt, parent: Node_Id, site: Decl_Site) {
    switch v in s {
    case ^Stmt_Decl:
        if site.kind == .Field {
            for name in v.names { graph_decl(b, site, parent, name, nil, v.span) }
        } else if len(v.checked) > 0 {
            for inner in v.checked { graph_stmt(b, inner, parent, site) }
        } else {
            graph_fatal(v.span, "declaration of '%s' reached the graph unchecked", v.names[0])
        }
    case ^Stmt_Assign:
        if _, is_import := v.value.(^Expr_Include); is_import {
            graph_node(b, .Import, .Explicit, parent, v.name, v.env_type if v.env_type != nil else v.var_type, v.span)
        } else if v.is_decl && v.target == nil {
            graph_decl(b, site, parent, v.name, v.env_type if v.env_type != nil else v.var_type, v.span)
        }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { graph_stmt(b, a, parent, site) }
    case ^Stmt_Multi_Return_Assign:
        if len(v.checked) > 0 {
            for inner in v.checked { graph_stmt(b, inner, parent, site) }
        } else if v.is_decl {
            for name, i in v.names {
                if name == "" || name == "_" { continue }
                if i < len(v.targets) && v.targets[i] != nil { continue }   // an lvalue stores
                t: Type = v.var_types[i] if i < len(v.var_types) else nil
                graph_decl(b, site, parent, name, t, v.span)
            }
        }
    case ^Stmt_Define:
        t := v.env_type if v.env_type != nil else v.var_type
        kind: Node_Kind = .Const
        if _, is_import := v.value.(^Expr_Include); is_import { kind = .Import }   // `core :: include mara.core`
        graph_node(b, kind, .Explicit, parent, v.name, t, v.span)
    case Stmt_Call, Stmt_Return, Stmt_Break, Stmt_Continue, Stmt_Overload, Stmt_Module:
        // Nothing declared: these are operations (the next step) or rules.
    case ^Stmt_If:
        graph_block(b, "if", v.body[:], parent, v.span)
        if len(v.else_body) > 0 { graph_block(b, "else", v.else_body[:], parent, v.span) }
    case ^Stmt_For:
        f := graph_node(b, .Block, .Explicit, parent, "for", nil, v.span)
        if v.init != nil       { graph_stmt(b, v.init, f, {kind = .Local}) }
        if v.loop_var != ""    { graph_node(b, .Local, .Explicit, f, v.loop_var, v.var_type, v.span) }
        if v.elem_var != ""    { graph_node(b, .Local, .Explicit, f, v.elem_var, v.elem_type_, v.span) }
        if v.index_var != "" {
            // As the checker binds it (type_checker.odin, collection loops).
            graph_node(b, .Local, .Explicit, f, v.index_var, Type_Numeric{kind = .Signed, bits = 32}, v.span)
        }
        for s2 in v.body { graph_stmt(b, s2, f, {kind = .Local}) }
        if v.post != nil { graph_stmt(b, v.post, f, {kind = .Local}) }
        graph_close(b, f)
    case ^Stmt_Scope:
        graph_scope(b, v, parent)
    case ^Stmt_Defer:
        graph_block(b, "defer", v.body[:], parent, v.span)
    case ^Stmt_Match:
        for &arm in v.arms {
            label := "else" if arm.is_else else fmt.aprintf("arm %s", arm.variant)
            a := graph_node(b, .Block, .Explicit, parent, label, nil, v.span)
            if arm.is_union_arm && arm.bound_name != "" {
                graph_node(b, .Local, .Explicit, a, arm.bound_name, graph_arm_type(b, &arm, v.span), v.span)
            }
            for s2 in arm.body { graph_stmt(b, s2, a, {kind = .Local}) }
            graph_close(b, a)
        }
    case ^Stmt_Foreign:
        for &f in v.decls { graph_foreign(b, &f, parent) }
    case ^Stmt_Union_Def:
        graph_union(b, v, parent)
    case ^Stmt_Distinct_Def:
        d := graph_one(b, v.span, v.name)
        graph_node(b, .Type_Def, .Explicit, parent, v.name, d, v.span)
    case ^Stmt_Dispatch_Def:
        graph_node(b, .Dispatch, .Explicit, parent, v.name, nil, v.span)
    }
}

// A plain declaration, as a field of the owning struct or a local / constant.
@(private="file")
graph_decl :: proc(b: ^Graph_Builder, site: Decl_Site, parent: Node_Id, name: string, t: Type, span: Span) {
    t := t
    if site.kind == .Field {
        // Signatures resolve on demand, so a struct nothing uses has no typed
        // fields yet: the field exists, its type is unknown.
        if i, ok := site.owner.field_map[name]; ok {
            t = site.owner.fields[i].type_
        } else if site.owner.sig_state == .Resolved {
            graph_fatal(span, "field '%s' is missing from struct '%s'", name, site.owner.name)
        }
    }
    graph_node(b, site.kind, .Explicit, parent, name, t, span)
}

@(private="file")
graph_block :: proc(b: ^Graph_Builder, label: string, body: []Stmt, parent: Node_Id, span: Span) {
    n := graph_node(b, .Block, .Explicit, parent, label, nil, span)
    for s in body { graph_stmt(b, s, n, {kind = .Local}) }
    graph_close(b, n)
}

// The one checked type a non-generic declaration resolved to.
@(private="file")
graph_one :: proc(b: ^Graph_Builder, span: Span, name: string) -> Type {
    list, ok := b.by_span[span]
    if !ok || len(list) != 1 {
        graph_fatal(span, "'%s' should have one checked type, has %d", name, len(list) if ok else 0)
    }
    return list[0]
}

@(private="file")
graph_scope :: proc(b: ^Graph_Builder, s: ^Stmt_Scope, parent: Node_Id) {
    if s.kind == .Block {
        graph_block(b, "block", s.body[:], parent, s.span)
        return
    }
    generic := len(s.generic_params) > 0
    list, ok := b.by_span[s.span]
    if !ok {
        if generic { return }   // a generic nothing instantiates: syntax only
        graph_fatal(s.span, "'%s' reached the graph unchecked", scope_name(s))
    }
    for t in list {
        ts, is_scope := t.(^Type_Scope)
        if !is_scope || ts.is_module { continue }
        graph_scope_node(b, ts, s, parent, .Synthetic if generic else .Explicit)
    }
}

@(private="file")
graph_scope_node :: proc(b: ^Graph_Builder, ts: ^Type_Scope, s: ^Stmt_Scope, parent: Node_Id, written: Written) {
    kind: Node_Kind = .Fun if ts.kind == .Fun else .Struct
    name := s.name if written == .Explicit else ask_demangle(ts.name, ts.home_package)
    n := graph_node(b, kind, written, parent, name, ts, s.span)
    for p in ts.params { graph_node(b, .Param, .Explicit, n, p.name, p.type_, s.span) }
    graph_results(b, ts, n, s.span)
    // An instance's body is its own checked copy; a struct's is the template's,
    // with each field typed by the instance.
    body := ts.body[:] if kind == .Fun && written == .Synthetic else s.body[:]
    site := Decl_Site{kind = .Local} if kind == .Fun else Decl_Site{kind = .Field, owner = ts}
    graph_scope_stmts(b, s.defs[:], body, n, site)
    graph_close(b, n)
}

// A scope's statements in written order. Its `::` definitions (nested funs,
// structs, constants) are held apart from its body, so the two are merged by
// position.
@(private="file")
graph_scope_stmts :: proc(b: ^Graph_Builder, defs, body: []Stmt, parent: Node_Id, site: Decl_Site) {
    before :: proc(x, y: Stmt) -> bool {
        a, c := stmt_span(x), stmt_span(y)
        return a.line < c.line || (a.line == c.line && a.col < c.col)
    }
    i, j := 0, 0
    for i < len(defs) || j < len(body) {
        if j >= len(body) || (i < len(defs) && before(defs[i], body[j])) {
            graph_stmt(b, defs[i], parent, site)
            i += 1
        } else {
            graph_stmt(b, body[j], parent, site)
            j += 1
        }
    }
}

// A function's results: named ones by name, else `result` (or `result1`, … when several).
@(private="file")
graph_results :: proc(b: ^Graph_Builder, ts: ^Type_Scope, parent: Node_Id, span: Span) {
    for rt, i in ts.return_types {
        name := "result"
        if i < len(ts.return_binding_names) {
            name = ts.return_binding_names[i]
        } else if len(ts.return_types) > 1 {
            name = fmt.aprintf("result%d", i + 1)
        }
        graph_node(b, .Result, .Explicit, parent, name, rt, span)
    }
}

@(private="file")
graph_foreign :: proc(b: ^Graph_Builder, f: ^Foreign_Fun, parent: Node_Id) {
    ts, ok := graph_one(b, f.span, f.name).(^Type_Scope)
    if !ok { graph_fatal(f.span, "foreign '%s' is not a function", f.name) }
    n := graph_node(b, .Fun, .Explicit, parent, f.name, ts, f.span)
    for p in ts.params { graph_node(b, .Param, .Explicit, n, p.name, p.type_, f.span) }
    graph_results(b, ts, n, f.span)
    graph_close(b, n)
}

// A union holds its variants, each a struct; an enum holds its variant names.
@(private="file")
graph_union :: proc(b: ^Graph_Builder, v: ^Stmt_Union_Def, parent: Node_Id) {
    generic := len(v.generic_params) > 0
    written: Written = .Synthetic if generic else .Explicit
    found := false
    for t in b.by_span[v.span] {
        #partial switch u in t {
        case ^Type_Union:
            found = true
            name := v.name if !generic else ask_demangle(u.name, u.home_package)
            n := graph_node(b, .Union, written, parent, name, u, v.span)
            for variant in u.variants {
                st, st_ok := b.checked.table.structs[u.variant_structs[variant]]
                if !st_ok { graph_fatal(v.span, "variant '%s' of '%s' has no struct", variant, v.name) }
                vn := graph_node(b, .Struct, .Explicit, n, variant, st, st.body_span)
                for f in st.fields {
                    fw: Written = .Synthetic if strings.has_prefix(f.name, "__") else .Explicit   // the tag, its padding
                    graph_node(b, .Field, fw, vn, f.name, f.type_, st.body_span)
                }
                graph_close(b, vn)
            }
            graph_close(b, n)
        case ^Type_Enum:
            if u.is_synthetic { continue }   // a union's tag enum
            found = true
            n := graph_node(b, .Enum, written, parent, v.name, u, v.span)
            for variant in v.variants { graph_node(b, .Variant, .Explicit, n, variant.name, u, variant.span) }
            graph_close(b, n)
        }
    }
    if !found && !generic { graph_fatal(v.span, "'%s' reached the graph unchecked", v.name) }
}

// A union arm's payload: the variant struct the checker resolved.
@(private="file")
graph_arm_type :: proc(b: ^Graph_Builder, arm: ^Match_Arm, span: Span) -> Type {
    if st, ok := b.checked.table.structs[arm.resolved_struct]; ok { return st }
    if ft, ok := b.checked.table.funs[arm.resolved_struct]; ok    { return ft }
    graph_fatal(span, "match arm '%s' has no resolved variant", arm.variant)
}

// Every checked scope and type the program declares is exactly one node.
@(private="file")
graph_check_coverage :: proc(b: ^Graph_Builder) {
    count: map[rawptr]int
    defer delete(count)
    for t, id in b.g.type_ {
        #partial switch b.g.kind[id] {
        case .Fun, .Struct, .Union, .Enum, .Type_Def: count[graph_type_ptr(t)] += 1
        }
    }
    bad := 0
    check :: proc(count: ^map[rawptr]int, bad: ^int, t: Type, span: Span) {
        if span == {} { return }
        if n := count[graph_type_ptr(t)]; n != 1 {
            loc := format_location(span.file, span.line, span.col)
            emit_diagnostic(.Graph_Error, loc, "'%s' is %d nodes of the graph, not 1", ask_type_name(t), n)
            bad^ += 1
        }
    }
    t := b.checked.table
    for _, ft in b.checked.functions { if !ft.is_module { check(&count, &bad, ft, ft.body_span) } }
    for _, st in t.structs           { if !st.is_module { check(&count, &bad, st, st.body_span) } }
    for _, u in t.unions             { check(&count, &bad, u, u.span) }
    for _, e in t.enums              { if !e.is_synthetic { check(&count, &bad, e, e.span) } }
    for _, d in t.distinct_types     { check(&count, &bad, d, d.span) }
    if bad > 0 {
        flush_diagnostics()
        os.exit(1)
    }
}

// --- dump -------------------------------------------------------------------

// MARA_GRAPH=all prints the whole graph; MARA_GRAPH=<name> prints the subtree
// of every node with that name.
@(private="file")
graph_dump :: proc(g: ^Program_Graph) {
    want := os.get_env("MARA_GRAPH", context.temp_allocator)
    if want == "" { return }
    fmt.printf("graph: %d nodes\n", len(g.kind))
    for id in 0 ..< len(g.kind) {
        if want != "all" && g.name[id] != want { continue }
        if want == "all" && g.parent[id] != NO_NODE { continue }   // roots print their subtrees
        base := graph_depth(g, Node_Id(id))
        for n in id ..= int(g.last[id]) {
            graph_dump_node(g, Node_Id(n), graph_depth(g, Node_Id(n)) - base)
        }
    }
}

@(private="file")
graph_depth :: proc(g: ^Program_Graph, id: Node_Id) -> int {
    d := 0
    for p := g.parent[id]; p != NO_NODE; p = g.parent[p] { d += 1 }
    return d
}

@(private="file")
graph_dump_node :: proc(g: ^Program_Graph, id: Node_Id, indent: int) {
    b := strings.builder_make(context.temp_allocator)
    for _ in 0 ..< indent { strings.write_string(&b, "  ") }
    fmt.sbprintf(&b, "%d %s %s", id, graph_kind_word(g.kind[id]), g.name[id])
    if t := g.type_[id]; t != nil {
        #partial switch g.kind[id] {
        case .Field, .Param, .Result, .Local, .Const, .Import, .Type_Def:
            fmt.sbprintf(&b, " : %s", type_name(t))
        }
    }
    if o := g.origin[id]; o.file != "" { fmt.sbprintf(&b, "   %s:%d", filepath.base(o.file), o.line) }
    if g.written[id] == .Synthetic { strings.write_string(&b, "   (synthetic)") }
    fmt.println(strings.to_string(b))
}

@(private="file")
graph_kind_word :: proc(k: Node_Kind) -> string {
    switch k {
    case .Module:   return "module"
    case .Struct:   return "struct"
    case .Union:    return "union"
    case .Enum:     return "enum"
    case .Fun:      return "fun"
    case .Block:    return "block"
    case .Field:    return "field"
    case .Param:    return "param"
    case .Result:   return "result"
    case .Local:    return "local"
    case .Const:    return "const"
    case .Import:   return "import"
    case .Variant:  return "variant"
    case .Type_Def: return "type"
    case .Dispatch: return "dispatch"
    }
    return "?"
}
