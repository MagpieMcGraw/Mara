package mara

import "core:fmt"
import "core:os"
import "core:strings"

// The type checker on the flat tree (design/flat_tree.md, stage 3), beside
// the old one until the switch: MARA_CHECKER=new runs it instead. It fills
// the same Checked_Program — the symbol table, the Type_Scopes, the program
// graph (built as each body is checked, through the builder), the
// diagnostics — from the tree as written: nothing lowered, nothing cloned.
//
// What checking an expression builds is what it returns (tc_expr: its type
// and what it built), not a side channel. What the checker finds about a node
// is kept by its id (tc_node_type).

TC :: struct {
    t:             ^Tree,
    c:             ^Checker,          // the error sink and table the shared passes and helpers take
    table:         ^SymbolTable,
    checked:       ^Checked_Program,
    gb:            ^Graph_Builder,
    modules:       map[string][]Tree_Id,   // each module's files' roots, in path order
    pkg:           string,            // the module being checked
    root:          ^Type_Scope,       // the main module's scope: the root env
    main_package:  string,
    shared:        bool,
    types:         [dynamic]Type,     // each node's type, as checked (by its id)
    hint:          Type,              // the type the expression being checked is expected at
    funs:          [dynamic]TC_Fun,   // the functions registered, to check and extract
}

// A function as registered: its type, its definition, the scope its name is
// declared in.
TC_Fun :: struct {
    ft:   ^Type_Scope,
    def:  Tree_Id,   // its Define
    fun:  Tree_Id,   // its Fun_Def
    env:  ^Type_Scope,
}

tc_error :: proc(k: ^TC, span: Span, msg: string, args: ..any) {
    check_error(k.c, span, msg, ..args)
}

// What this checker doesn't check yet: an error, so the program fails
// visibly rather than differently.
tc_unsupported :: proc(k: ^TC, n: Tree_Id, what: string) {
    tc_error(k, tree_span(k.t, n), "tc: %s is not supported yet (%v)", what, k.t.tag[n])
}

tc_node_type :: proc(k: ^TC, n: Tree_Id) -> Type {
    return k.types[n] if int(n) < len(k.types) else nil
}

tc_set_type :: proc(k: ^TC, n: Tree_Id, t: Type) {
    if n == 0 { return }
    if int(n) >= len(k.types) { resize(&k.types, max(int(n) + 1, 2 * len(k.types))) }
    k.types[n] = t
}

tc_text :: proc(tok: Token_Id) -> string {
    return token_text(build_tokens[tok])
}

// A node's name: its report point's text (a Define's, an Ident's).
tc_name :: proc(k: ^TC, n: Tree_Id) -> string {
    return tc_text(k.t.main[n])
}

// The builder, while the body being checked is one the checker builds and
// nothing has stopped it.
tc_building :: proc(k: ^TC) -> ^Graph_Builder {
    b := k.gb
    if b == nil || b.fuse == nil || b.fuse.failed != "" || k.c.errors > 0 { return nil }
    return b
}

tc_fail :: proc(k: ^TC, reason: string) {
    if b := tc_building(k); b != nil { graph_fuse_fail(b, b.fuse, reason) }
}

// --- the program --------------------------------------------------------------

tc_check_program :: proc(t: ^Tree, modules: map[string][]Tree_Id, main_package: string,
                         shared: bool = false, web: bool = false, target_os: Target_OS = .Windows,
                         analysis_only: bool = false, perf: ^Performance_Timer = nil) -> ^Checked_Program {
    table := new(SymbolTable)
    main_mod := new(Type_Scope)
    main_mod.name = main_package
    main_mod.home_package = main_package
    main_mod.kind = .Struct
    main_mod.is_module = true
    table.root_env = main_mod

    c := new(Checker)
    c.table = table
    checked := new(Checked_Program)
    checked.table = table
    checked.target_os = target_os
    checked.main_package = main_package
    c.checked = checked
    c.target_web, c.target_shared, c.target_os, c.analysis_only = web, shared, target_os, analysis_only

    k := &TC{t = t, c = c, table = table, checked = checked, modules = modules, root = main_mod, main_package = main_package, shared = shared}
    resize(&k.types, len(t.tag))

    files, ok := modules[main_package]
    if !ok {
        tc_error(k, {}, "no parsed program for main module '%s'", main_package)
        checked.errors = c.errors
        return checked
    }

    std_fun := new(Type_Scope)
    std_fun.name = "std"
    std_fun.home_package = "std"
    std_fun.kind = .Struct
    type_env_set(main_mod, "std", std_fun)

    k.gb = graph_builder_new(checked, tc_module_graph_decls(k))
    c.gb = k.gb

    // The program's struct (the compiler-managed global): its args, as the
    // old checker makes it (an arena when `this_program = Program(...)`).
    {
        arg_slice := new(Type_Slice)
        arg_slice.elem = Type_Utf8{}
        args_type := new(Type_Partial_Array)
        args_type.size = 64
        args_type.elem = arg_slice
        prog_type := new(Type_Scope)
        prog_type.name = "Program"
        prog_type.home_package = main_package
        prog_type.kind = .Struct
        append(&prog_type.fields, Struct_Type_Field{name = "args", type_ = args_type})
        prog_type.field_map["args"] = 0
        table.funs["Program"] = prog_type
        type_env_set(main_mod, "this_program", prog_type)
        type_env_set(main_mod, "Program", prog_type)
    }
    void_type := new(Type_Ptr)
    void_type.elem = Type_Any{}
    type_env_set(main_mod, "void", void_type)

    k.pkg = main_package
    tc_check_module_files(k, files, main_mod)

    tc_extract(k, checked)
    tc_validate_main(k, files)

    if c.errors == 0 {
        if perf != nil { perf_timer_mark(perf, "graph") }
        checked.graph = build_program_graph(k.gb)
        if perf != nil { perf_timer_mark(perf, "analysis") }
        checked.call_graph = build_call_graph(checked)
        c.cg = &checked.call_graph
    } else {
        graph_builder_free(k.gb)
        if perf != nil { perf_timer_mark(perf, "analysis") }
    }
    k.gb, c.gb = nil, nil
    void_defaults: map[Span]bool
    flow_analyze_program(c, checked, void_defaults)
    escape_analyze_program(c, checked)
    checked.errors = c.errors
    return checked
}

// A module's files: each its own scope (its imports its own), chained to the
// module's, where its definitions are declared; their names registered, then
// their bodies checked.
tc_check_module_files :: proc(k: ^TC, files: []Tree_Id, mod: ^Type_Scope) {
    envs := make([]^Type_Scope, len(files), context.temp_allocator)
    for f, i in files {
        fe := new(Type_Scope)
        fe.kind = .Block
        fe.home_package = mod.home_package
        fe.parent_scope = mod
        envs[i] = fe
    }
    for f, i in files {
        for s in tree_list(k.t, k.t.a[f]) { tc_register(k, s, envs[i], mod) }
    }
    for &fn in k.funs { tc_signature(k, &fn) }
    for &fn in k.funs {
        tc_fun_body(k, &fn)
        if k.gb != nil { graph_module_stmt(k.gb, syntax_id(fn.def), {kind = .Other, set = true}) }
    }
}

// A module statement's declaration, registered: a fun's name, its type made.
tc_register :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, mod: ^Type_Scope) {
    t := k.t
    #partial switch t.tag[s] {
    case .Module:
        return
    case .Expr_Stmt:
        if e := Tree_Id(t.a[s]); t.tag[e] == .Import {
            tc_unsupported(k, e, "an import")
            return
        }
    case .Define:
        value := Tree_Id(t.b[s])
        if t.a[s] == 0 && value != 0 && t.tag[value] == .Fun_Def {
            tc_register_fun(k, s, value, env, mod)
            return
        }
        if value != 0 {
            tc_unsupported(k, value, "this module definition")
            return
        }
    }
    tc_unsupported(k, s, "this module statement")
}

tc_register_fun :: proc(k: ^TC, def, fun: Tree_Id, env: ^Type_Scope, mod: ^Type_Scope) {
    name := tc_name(k, def)
    v := scope_view(k.t, fun)
    if len(v.generics) > 0 {
        tc_unsupported(k, def, "a generic fun")
        return
    }
    flat := make_flat_name(k.pkg, name)
    if flat in k.table.funs {
        tc_error(k, tree_span(k.t, def), TYPE_FUNCTION_ALREADY_DEFINED, name)
        return
    }
    ft := new(Type_Scope)
    ft.has_parens = build_tokens[k.t.main[fun] + 1].kind == .Left_Paren
    ft.name = flat
    ft.home_package = k.pkg
    ft.node = fun
    ft.source_name = name
    ft.decl_env = env
    ft.kind = .Fun
    ft.parent_scope = env
    k.table.funs[flat] = ft
    type_env_set(mod, name, ft)
    k.table.fun_homes[name] = k.pkg
    k.c.declared_funs[name] = true
    if mod.functions == nil { mod.functions = make(map[string]^Type_Scope) }
    mod.functions[name] = ft
    append(&k.funs, TC_Fun{ft = ft, def = def, fun = fun, env = env})
}

// A fun's params and returns, resolved in the scope it is declared in.
tc_signature :: proc(k: ^TC, fn: ^TC_Fun) {
    t := k.t
    v := scope_view(t, fn.fun)
    ft := fn.ft
    if len(ft.params) > 0 || len(ft.return_types) > 0 { return }
    span := tree_span(t, fn.def)
    for g in v.params {
        pv := params_view(t, g)
        if pv.type_ == 0 || len(pv.values) > 0 {
            tc_unsupported(k, g, "a param with a default")
            continue
        }
        pt := tc_type(k, pv.type_, fn.env, span)
        for name in pv.names {
            append(&ft.params, Struct_Type_Field{name = tc_text(name), type_ = pt})
        }
    }
    build_param_map(ft)
    for r in v.returns {
        if t.tag[r] == .Param_Group {
            tc_unsupported(k, r, "a named result")
            continue
        }
        append(&ft.return_types, tc_type(k, r, fn.env, span))
    }
}

// Each checked fun, for the emitter: its name (the module's prefix, `main`
// as itself), its origin, its signature for codegen.
tc_extract :: proc(k: ^TC, checked: ^Checked_Program) {
    for &fn in k.funs {
        ft := fn.ft
        name := ft.source_name
        key := name
        if name != "main" && k.main_package != "" { key = make_flat_name(k.main_package, name) }
        ft.origin = Origin_Source{}
        v := scope_view(k.t, fn.fun)
        if v.intrinsic != 0 {
            ft.origin = Origin_Intrinsic{llvm_name = tc_intrinsic_name(k, v.intrinsic)}
        }
        ft.body_span = tree_span(k.t, fn.def)
        populate_cg_signature(ft)
        _, already := checked.functions[key]
        ft.name = key
        checked.functions[key] = ft
        if !already { append(&checked.function_order, key) }
    }
}

tc_intrinsic_name :: proc(k: ^TC, n: Tree_Id) -> string {
    sb := strings.builder_make()
    for part, i in tree_token_list(k.t, k.t.a[n]) {
        if i > 0 { strings.write_byte(&sb, '.') }
        strings.write_string(&sb, tc_text(part))
    }
    return strings.to_string(sb)
}

// The main package defines `main`, which returns nothing or an i64 (the
// exit code) and takes no params.
tc_validate_main :: proc(k: ^TC, files: []Tree_Id) {
    found := false
    for &fn in k.funs {
        if fn.ft.source_name != "main" { continue }
        found = true
        span := tree_span(k.t, fn.def)
        rts := fn.ft.return_types
        ok := len(rts) == 0
        if len(rts) == 1 {
            if vn, is_num := rts[0].(Type_Numeric); is_num && vn.kind == .Signed && vn.bits == 64 { ok = true }
            if is_any(rts[0]) { ok = true }
        }
        if !ok { tc_error(k, span, TYPE_FUN_MAIN_RETURN_INT_RETURN) }
        if len(fn.ft.params) != 0 { tc_error(k, span, TYPE_FUN_MAIN_TAKE_PARAMETERS) }
    }
    if !found && !k.shared {
        tc_error(k, {}, "module '%s' must define fun main()", k.main_package)
    }
}

// Each module's statements, as the builder builds them (tc_graph_decl).
tc_module_graph_decls :: proc(k: ^TC) -> map[string][]Graph_Decl {
    out := make(map[string][]Graph_Decl, len(k.modules), context.temp_allocator)
    for name, files in k.modules {
        decls: [dynamic]Graph_Decl
        for f in files {
            for s in tree_list(k.t, k.t.a[f]) { append(&decls, tc_graph_decl(k, s)) }
        }
        out[name] = decls[:]
    }
    return out
}

// What a statement outside any body declares, as the builder builds it.
tc_graph_decl :: proc(k: ^TC, s: Tree_Id) -> Graph_Decl {
    t := k.t
    d := Graph_Decl{id = syntax_id(s), span = tree_span(t, s), kind = tc_stmt_kind(k, s)}
    #partial switch t.tag[s] {
    case .Module, .Expr_Stmt, .Return, .Break, .Continue, .Overload:
        d.form = .None
    case .Define:
        d.settles, d.name = true, tc_name(k, s)
        value := Tree_Id(t.b[s])
        switch {
        case value != 0 && t.tag[value] == .Fun_Def || value != 0 && t.tag[value] == .Struct_Def:
            d.form, d.settles = .Scope, false
            d.generic = len(scope_view(t, value).generics) > 0
        case value != 0 && t.tag[value] == .Import:
            d.form = .Import
        case:
            d.form = .Const
            d.value = syntax_id(value)
        }
    case:
        d.form = .Code
    }
    return d
}

// What a statement does to the variables it writes, as the graph's statements
// table has it.
tc_stmt_kind :: proc(k: ^TC, s: Tree_Id) -> Stmt_Kind {
    #partial switch k.t.tag[s] {
    case .Decl:     return .Decl
    case .Assign:
        targets := tree_list(k.t, k.t.a[s])
        if len(targets) == 1 {
            if k.t.tag[targets[0]] != .Ident { return .Write }
            name := tc_name(k, targets[0])
            if name == "_" || name == "this_program" { return .Other }
            return .Assign
        }
        return .Destructure
    case .Compound:
        if k.t.tag[k.t.a[s]] != .Ident { return .Write }
        return .Assign
    case .For_Range, .For_Each, .For_C, .For_Cond: return .Loop
    case .If:    return .If
    case .Match: return .Match
    }
    return .Other
}

// The modules the build parsed, each its files' roots in path order — the
// new checker's input (main.odin, under MARA_CHECKER=new).
tc_modules :: proc() -> map[string][]Tree_Id {
    by_module := make(map[string][dynamic]^Source_File, context.temp_allocator)
    for f in build_files {
        if f.module not_in by_module { by_module[f.module] = make([dynamic]^Source_File, context.temp_allocator) }
        append(&by_module[f.module], f)
    }
    out: map[string][]Tree_Id
    roots := make(map[^Source_File]Tree_Id, context.temp_allocator)
    for f, i in build_files { roots[f] = build_tree.files[i] }
    for name, fs in by_module {
        sorted := fs[:]
        for i in 1 ..< len(sorted) {   // (by path: the old checker's statement order)
            for j := i; j > 0 && sorted[j].path < sorted[j - 1].path; j -= 1 { sorted[j], sorted[j - 1] = sorted[j - 1], sorted[j] }
        }
        ids := make([]Tree_Id, len(sorted))
        for f, i in sorted { ids[i] = roots[f] }
        out[name] = ids
    }
    return out
}

tc_mode :: proc() -> string {
    return os.get_env("MARA_CHECKER", context.temp_allocator)
}

_ :: fmt
