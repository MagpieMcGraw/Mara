package mara

import "core:fmt"
import "core:os"
import "core:slice"
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
    scopes:        [dynamic]^TC_Scope,   // the funs and structs registered, to check and extract
    scope_of:      map[^Type_Scope]int,   // each one's, by its type
    mine:          ^[dynamic]int,     // the ones the module being checked registered
    by_module:     map[string][]int,  // each module's, once checked
    checked_modules: map[string]^Type_Scope,
    in_progress:   map[string]bool,
    std:           ^Type_Scope,
    salt:          u64,               // the instance being checked's number (0: none): tc_sid
    salt_lo, salt_hi: Tree_Id,        // its template's body's nodes
    instance_count: u64,
    templates:     map[string]TC_Template,   // the generic definitions, by name
    consts:        map[string]^TC_Const,     // the constants, by flat name (and bare, unless two modules share it)
    const_owners:  map[string]string,        // each bare name's module ("": more than one)
    scope_consts:  map[^Type_Scope]map[string]^TC_Const,   // the constants a body, or a struct, defines
    instances:     map[string]^Type_Scope,   // each generic fun's instances, by mangled name
    instance_order: [dynamic]string,
    subst:         map[string]Type,   // the type params bound, in an instance being checked
    callees:       map[Tree_Id]^Type_Scope,   // each call's fun, or struct (its constructor)
    const_nodes:   map[Tree_Id]bool,  // the names that resolved to a constant
    variant_nodes: map[Tree_Id]bool,  // the names that resolved to an enum's variant
    size_of:       map[Tree_Id]Type,  // each size_of's type, as checked
    compound:      struct { target: Tree_Id, place: Operand },   // a compound assignment's target, its place built
}

// A fun or a struct as registered: its type, its definition, the scope its
// name is declared in.
TC_Scope :: struct {
    ts:   ^Type_Scope,
    def:  Tree_Id,   // its Define
    node: Tree_Id,   // its Fun_Def or Struct_Def
    env:  ^Type_Scope,
    nested: [dynamic]int,   // the funs and structs defined in its body
    consts: [dynamic]^TC_Const,   // the constants defined in its body
    subst:  map[string]Type,   // an instance's: its type params bound
    synthetic: bool,           // an instance: the compiler's, written nowhere
    registered: bool,       // (they are)
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
    k.std = std_fun
    k.checked_modules[main_package] = main_mod

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
    main := tc_check_module_files(k, files, main_mod)

    tc_extract(k, main, main_package, is_main = true)
    // (Each generic fun's instances, for codegen: in the functions, in no order.)
    for mangled in k.instance_order {
        ft := k.instances[mangled]
        sc := k.scopes[k.scope_of[ft]]
        key := make_flat_name(ft.home_package, mangled)
        ft.name, ft.body_span = key, tree_span(k.t, sc.def)
        ft.origin = Origin_Source{}
        populate_cg_signature(ft)
        checked.functions[key] = ft
    }
    tc_program_struct(k)
    tc_validate_main(k, main)

    if c.errors == 0 {
        if perf != nil { perf_timer_mark(perf, "graph") }
        // (Each constant's names, by its value, for the builder to name tables.)
        for key, kc in k.consts { k.gb.constant_names[key] = kc.sid }
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
tc_check_module_files :: proc(k: ^TC, files: []Tree_Id, mod: ^Type_Scope) -> []int {
    // (The scopes this module registers: a `use` in it checks another, whose
    // own are its.)
    saved := k.mine
    list: [dynamic]int
    k.mine = &list
    defer k.mine = saved
    envs := make([]^Type_Scope, len(files), context.temp_allocator)
    for f, i in files {
        fe := new(Type_Scope)
        fe.kind = .Block
        fe.home_package = mod.home_package
        fe.parent_scope = mod
        envs[i] = fe
    }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_register_types(k, s, envs[i], mod) }
    }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_register(k, s, envs[i], mod) }
    }
    mine := list[:]
    // (Signatures first: a constant's value may call a fun — an error, but
    // one found at its call, as the old checker's were on demand.)
    for i in mine { tc_signature(k, k.scopes[i]) }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_resolve(k, s, envs[i]) }
    }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_validate(k, s, envs[i]) }
    }
    // A struct's fields are what its body declares: each struct's body is
    // checked first (or sooner, by what needs its fields), then each fun's.
    for i in mine { tc_struct_ensure(k, k.scopes[i].ts) }
    for i in mine {
        if ts := k.scopes[i].ts; ts != nil && ts.kind == .Fun { tc_scope_body(k, k.scopes[i]) }
    }
    for i in mine {
        if k.gb != nil { graph_module_stmt(k.gb, tc_sid(k, k.scopes[i].def), {kind = .Other, set = true}) }
    }
    // (Its foreign funs, for the emitter.)
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) {
            if k.t.tag[s] == .Foreign { tc_extract_foreign(k, s, envs[i], k.pkg) }
        }
    }
    return mine
}

// A struct's body checked, its fields found, when something needs them
// first. (One that needs its own is a cycle.)
tc_struct_ensure :: proc(k: ^TC, ts: ^Type_Scope) {
    if ts == nil || ts.node == 0 || ts.kind != .Struct || ts.sig_state == .Resolved { return }
    i, ok := k.scope_of[ts]
    if !ok { return }
    if ts.sig_state == .In_Progress {
        tc_unsupported(k, k.scopes[i].def, "a struct whose fields need its own")
        return
    }
    tc_scope_body(k, k.scopes[i])
}

// A module statement's declaration, registered: a fun's name, its type made.
// A module statement's names, the first pass (the old checker's 1a): its
// funs, structs, types and unions declared, its constants listed — before
// any `use` in the module checks another.
tc_register_types :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, mod: ^Type_Scope) {
    t := k.t
    if t.tag[s] != .Define { return }
    value := Tree_Id(t.b[s])
    if value == 0 { return }
    if t.a[s] == 0 {
        #partial switch t.tag[value] {
        case .Fun_Def, .Struct_Def:
            tc_register_scope(k, s, value, env, mod)
            return
        case .Alias_Def, .Distinct_Def:
            tc_register_distinct(k, s, value, mod)
            return
        case .Union_Def, .Error_Def:
            tc_register_union(k, s, value, env, mod)
            return
        }
    }
    if !tc_is_definition(t.tag[value]) { tc_register_const(k, s, value, env, mod) }
}

// The rest of a module statement, the second pass: a `use`, a dispatch, an
// overload.
tc_register :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope, mod: ^Type_Scope) {
    t := k.t
    #partial switch t.tag[s] {
    case .Module:
        return
    case .Expr_Stmt:
        if e := Tree_Id(t.a[s]); t.tag[e] == .Import {
            tc_use(k, e, env, mod)
            if k.gb != nil { graph_module_stmt(k.gb, tc_sid(k, s), {kind = .Decl, set = true}) }
            return
        }
    case .Define:
        value := Tree_Id(t.b[s])
        if value != 0 && t.tag[value] == .Import {
            m := tc_use(k, value, env, mod, alias = tc_name(k, s))
            if k.gb != nil { graph_module_stmt(k.gb, tc_sid(k, s), {types = slice.clone([]Type{m}), kind = .Other, set = true}) }
            return
        }
        if value != 0 && t.tag[value] == .Dispatch_Def && t.a[s] == 0 {
            // (Its functions are checked to exist once every name is known.)
            name := tc_name(k, s)
            if name not_in k.c.dispatch_groups { k.c.dispatch_groups[name] = {} }
            for f in tree_token_list(t, t.a[value]) { append(&k.c.dispatch_groups[name], tc_text(f)) }
            return
        }
        #partial switch t.tag[value] {
        case .Fun_Def, .Struct_Def, .Alias_Def, .Distinct_Def, .Union_Def, .Error_Def:
            if t.a[s] == 0 { return }   // (the first pass's)
        case:
            if value != 0 && !tc_is_definition(t.tag[value]) { return }   // (a constant: the first pass's)
        }
        if value != 0 {
            tc_unsupported(k, value, "this module definition")
            return
        }
    case .Foreign:
        tc_register_foreign(k, s, env, mod)
        return
    case .Overload:
        op := build_tokens[t.a[s]].kind
        if op not_in k.c.operator_overloads { k.c.operator_overloads[op] = {} }
        append(&k.c.operator_overloads[op], tc_text(Token_Id(t.b[s])))
        return
    }
    tc_unsupported(k, s, "this module statement")
}

// `T :: type U`, `T :: distinct U`: its name (its base once every name is
// known: tc_resolve).
tc_register_distinct :: proc(k: ^TC, def, node: Tree_Id, mod: ^Type_Scope) {
    name := tc_name(k, def)
    span := tree_span(k.t, def)
    alias := k.t.tag[node] == .Alias_Def
    flat := make_flat_name(k.pkg, name)
    if flat in k.table.distinct_types {
        tc_error(k, span, TYPE_ALREADY_DEFINED, "type" if alias else "distinct type", name)
        return
    }
    dt := new(Type_Distinct)
    dt.name, dt.source_name, dt.span, dt.home_package = flat, name, span, k.pkg
    dt.is_alias = alias
    k.table.distinct_types[flat] = dt
    type_env_set(mod, name, dt)
}

// What a module statement leaves for every name to be known: a distinct
// type's base.
tc_resolve :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    if t.tag[s] != .Define { return }
    value := Tree_Id(t.b[s])
    if value != 0 && !tc_is_definition(t.tag[value]) {
        // (A constant: checked, and built, here in its module's order.)
        if kc, ok := k.consts[make_flat_name(k.pkg, tc_name(k, s))]; ok && kc.def == s {
            tc_check_const(k, kc)
            if k.gb != nil { graph_module_stmt(k.gb, tc_sid(k, s), {types = slice.clone([]Type{kc.t}), kind = .Other, set = true}) }
        }
        return
    }
    if t.a[s] != 0 { return }
    if value != 0 && t.tag[value] == .Union_Def {
        tc_resolve_union(k, s, value, env)
        return
    }
    if value == 0 || (t.tag[value] != .Alias_Def && t.tag[value] != .Distinct_Def) { return }
    if dt, ok := k.table.distinct_types[make_flat_name(k.pkg, tc_name(k, s))]; ok && dt.base_type == nil {
        dt.base_type = tc_type(k, Tree_Id(t.a[value]), env, tree_span(t, s))
    }
}

// What a module statement is checked for once its signatures are: a
// dispatch's functions, an overload's dispatch.
tc_validate :: proc(k: ^TC, s: Tree_Id, env: ^Type_Scope) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Define:
        value := Tree_Id(t.b[s])
        if value == 0 || t.tag[value] != .Dispatch_Def { return }
        name := tc_name(k, s)
        for tok in tree_token_list(t, t.a[value]) {
            f := tc_text(tok)
            if found, ok := type_env_get(env, f); ok {
                if tf, is_scope := found.(^Type_Scope); !is_scope || len(tf.params) == 0 {
                    tc_error(k, span, TYPE_DISPATCH_GROUP_FUNCTION, name, f)
                }
            } else if f not_in k.templates {
                tc_error(k, span, TYPE_DISPATCH_GROUP_FUNCTION_DEFINED, name, f)
            }
        }
    case .Overload:
        name := tc_text(Token_Id(t.b[s]))
        if _, ok := find_dispatch(k.c, env, name); !ok { tc_error(k, span, TYPE_OVERLOAD_DISPATCH_GROUP, name) }
    }
}

// A fun or a struct: its name declared in its module, its type made (its
// signature and body wait).
tc_register_scope :: proc(k: ^TC, def, node: Tree_Id, env: ^Type_Scope, mod: ^Type_Scope) {
    t := k.t
    name := tc_name(k, def)
    span := tree_span(t, def)
    v := scope_view(t, node)
    is_struct := t.tag[node] == .Struct_Def
    if tc_is_generic(k, node) {
        // (A template: checked as each instance.)
        if name not_in k.templates { k.templates[name] = TC_Template{def = def, node = node, lo = tc_subtree_lo(k, node), env = env, pkg = k.pkg} }
        if !is_struct && len(v.params) > 0 { k.c.declared_funs[name] = true }
        // (Its place in the module's order: a template the module's scope
        // binds a type to is that type's declaration — mara.core's `Program`
        // is the compiler's program struct — extracted there: tc_extract.)
        append(k.mine, len(k.scopes))
        append(&k.scopes, new_clone(TC_Scope{def = def, node = node, env = env}))
        return
    }
    switch {
    case is_struct && len(v.returns) > 0:
        tc_unsupported(k, def, "a struct's results")
        return
    }
    flat := make_flat_name(k.pkg, name)
    if is_struct && (flat in k.table.structs || flat in k.table.funs) {
        tc_error(k, span, TYPE_TYPE_ALREADY_DEFINED, name)
        return
    }
    if !is_struct && flat in k.table.funs {
        tc_error(k, span, TYPE_FUNCTION_ALREADY_DEFINED, name)
        return
    }
    ts := new(Type_Scope)
    ts.name, ts.source_name, ts.home_package = flat, name, k.pkg
    ts.kind = .Struct if is_struct else .Fun
    ts.node, ts.decl_env, ts.parent_scope = node, env, env
    ts.has_parens = build_tokens[t.main[node] + 1].kind == .Left_Paren
    ts.is_packed = v.packed != 0
    // (A struct with params is constructed by a call, as a fun is.)
    callable := !is_struct || len(v.params) > 0
    if callable { k.table.funs[flat] = ts } else { k.table.structs[flat] = ts }
    type_env_set(mod, name, ts)
    k.table.fun_homes[name] = k.pkg
    if callable {
        k.c.declared_funs[name] = true
        if mod.functions == nil { mod.functions = make(map[string]^Type_Scope) }
        mod.functions[name] = ts
    }
    k.scope_of[ts] = len(k.scopes)
    append(k.mine, len(k.scopes))
    append(&k.scopes, new_clone(TC_Scope{ts = ts, def = def, node = node, env = env}))
}

// A fun's or a struct's params and a fun's results, resolved in the scope
// it is declared in.
tc_signature :: proc(k: ^TC, sc: ^TC_Scope) {
    if sc.ts == nil { return }   // (a template: its instances')
    t := k.t
    v := scope_view(t, sc.node)
    ts := sc.ts
    if len(ts.params) > 0 || len(ts.return_types) > 0 { return }
    span := tree_span(t, sc.def)
    for g in v.params {
        pv := params_view(t, g)
        for name, i in pv.names {
            def := pv.values[i] if i < len(pv.values) else 0
            pt := tc_param_type(k, tc_text(name), pv.type_, def, sc.env, span)
            append(&ts.params, Struct_Type_Field{name = tc_text(name), type_ = pt, default_node = def})
        }
    }
    build_param_map(ts)
    for r in v.returns {
        if t.tag[r] == .Param_Group {
            tc_unsupported(k, r, "a named result")
            continue
        }
        append(&ts.return_types, tc_type(k, r, sc.env, span))
    }
}

// Each checked fun, for the emitter: its name (the module's prefix, `main`
// as itself), its origin, its signature for codegen.
tc_extract :: proc(k: ^TC, list: []int, module: string, is_main: bool, nested := false) {
    checked := k.checked
    for i in list {
        sc := k.scopes[i]
        ft := sc.ts
        if ft == nil {
            // A template, extracted as the type its module's scope binds its
            // name to (mara.core's `Program`: the compiler's), when one does.
            name := tc_name(k, sc.def)
            found, _ := type_env_get(sc.env, name)
            if ft = found.(^Type_Scope) or_else nil; ft == nil { continue }
            key := make_flat_name(module, name)
            ft.origin = Origin_Source{}
            ft.body_span = tree_span(k.t, sc.def)
            populate_cg_signature(ft)
            _, already := checked.functions[key]
            ft.name = key
            checked.functions[key] = ft
            if !already { append(&checked.function_order, key) }
            continue
        }
        // (Its own definitions first.)
        tc_extract(k, sc.nested[:], module, is_main, nested = true)
        name := ft.source_name
        // (`main` is the entry's, its bare name: the main module's only.)
        if name == "main" && !is_main && !nested { continue }
        key := name
        if nested {
            // (Named for its owner already: `mara_core_Arena_mark`.)
            key = ft.name
            flat_pkg, _ := strings.replace_all(module, ".", "_")
            if module != "" && !strings.has_prefix(key, fmt.tprintf("%s_", flat_pkg)) { key = make_flat_name(module, key) }
        } else if name != "main" && module != "" {
            key = make_flat_name(module, name)
        }
        ft.origin = Origin_Source{}
        v := scope_view(k.t, sc.node)
        if v.intrinsic != 0 {
            ft.origin = Origin_Intrinsic{llvm_name = tc_intrinsic_name(k, v.intrinsic)}
        }
        ft.body_span = tree_span(k.t, sc.def)
        populate_cg_signature(ft)
        _, already := checked.functions[key]
        ft.name = key
        checked.functions[key] = ft
        if !already || nested { append(&checked.function_order, key) }
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
tc_validate_main :: proc(k: ^TC, main: []int) {
    found := false
    for i in main {
        sc := k.scopes[i]
        fn := sc.ts
        if fn == nil || fn.kind != .Fun || fn.source_name != "main" { continue }
        found = true
        span := tree_span(k.t, sc.def)
        rts := fn.return_types
        ok := len(rts) == 0
        if len(rts) == 1 {
            if vn, is_num := rts[0].(Type_Numeric); is_num && vn.kind == .Signed && vn.bits == 64 { ok = true }
            if is_any(rts[0]) { ok = true }
        }
        if !ok { tc_error(k, span, TYPE_FUN_MAIN_RETURN_INT_RETURN) }
        if len(fn.params) != 0 { tc_error(k, span, TYPE_FUN_MAIN_TAKE_PARAMETERS) }
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
            for s in tc_live(k, tree_list(k.t, k.t.a[f])) { append(&decls, tc_graph_decl(k, s)) }
        }
        out[name] = decls[:]
    }
    return out
}

// What a statement outside any body declares, as the builder builds it.
tc_graph_decl :: proc(k: ^TC, s: Tree_Id) -> Graph_Decl {
    t := k.t
    d := Graph_Decl{id = tc_sid(k, s), span = tree_span(t, s), kind = tc_stmt_kind(k, s)}
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        d.form = .None
        if imp := Tree_Id(t.a[s]); t.tag[imp] == .Import {
            // (A bare `use m` declares m's last name, as the old tree had it.)
            d.form, d.settles, d.names = .Names, true, slice.clone([]string{tc_use_name(k, imp)})
        }
    case .Module, .Return, .Break, .Continue, .Overload:
        d.form = .None
    case .Foreign:
        d.form = .Foreign
        funs := foreign_view(t, s).funs
        parts := make([]Graph_Decl_Part, len(funs))
        for ff, i in funs { parts[i] = {tc_text(foreign_fun_view(t, ff).name), tree_span(t, ff)} }
        d.parts = parts
    case .Define:
        d.settles, d.name = true, tc_name(k, s)
        value := Tree_Id(t.b[s])
        switch {
        case value != 0 && t.tag[value] == .Fun_Def || value != 0 && t.tag[value] == .Struct_Def:
            d.form, d.settles = .Scope, false
            d.generic = tc_is_generic(k, value)
        case value != 0 && t.tag[value] == .Import:
            d.form = .Import
        case value != 0 && (t.tag[value] == .Alias_Def || t.tag[value] == .Distinct_Def):
            d.form, d.settles = .Type, false
        case value != 0 && t.tag[value] == .Dispatch_Def:
            d.form, d.settles = .Dispatch, false
        case value != 0 && t.tag[value] == .Union_Def:
            d.form, d.settles = .Union, false
            variants := tree_list(t, t.b[value])
            parts := make([]Graph_Decl_Part, len(variants))
            for vn, i in variants { parts[i] = {tc_name(k, vn), tree_span(t, vn)} }
            d.parts = parts
        case value != 0 && t.tag[value] == .Error_Def:
            d.form, d.settles = .Union, false
            names := tree_token_list(t, t.a[value])
            parts := make([]Graph_Decl_Part, len(names))
            for tok, i in names { parts[i] = {tc_text(tok), Span{at = tok, tok = tok, end = tok + 1}} }
            d.parts = parts
        case:
            d.form = .Const
            d.value = tc_sid(k, value)
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
    case .Expr_Stmt:
        if k.t.tag[k.t.a[s]] == .Import { return .Decl }
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

// Whether a definition's value is a definition of its own (a fun, a type, an
// import, …), not a constant's value.
tc_is_definition :: proc(tag: Tree_Tag) -> bool {
    #partial switch tag {
    case .Fun_Def, .Struct_Def, .Import, .Alias_Def, .Distinct_Def, .Dispatch_Def, .Union_Def, .Error_Def, .Intrinsic_Body:
        return true
    }
    return false
}

// A param's type: as written; else its default's — a whole number's width
// the one the body uses it at (a cell, settled once the body is checked), a
// fraction f64, anything else its checked type.
tc_param_type :: proc(k: ^TC, name: string, type_, def: Tree_Id, env: ^Type_Scope, span: Span) -> Type {
    if type_ != 0 { return tc_type(k, type_, env, span) }
    if def == 0 { return Type_Error{} }
    if k.t.tag[def] == .Number {
        if strings.index_byte(tc_text(k.t.main[def]), '.') >= 0 { return Type_F64{} }
        cell := new(Infer_Cell)
        cell.name, cell.span = name, span
        return Type_Infer_Int{cell = cell}
    }
    return solidify_type(tc_check(k, def, env))
}

// A node's id as the builder keys it. In a generic's instance, its
// template's body is checked again: its nodes are that instance's own (the
// old checker's clones had ids of their own), salted with the instance's
// number. (The template's definition itself is the instance's: unsalted.)
tc_sid :: proc(k: ^TC, n: Tree_Id) -> Syntax_Id {
    id := Syntax_Id(n)
    if k.salt != 0 && n >= k.salt_lo && n <= k.salt_hi { id |= Syntax_Id(k.salt) << 32 }
    return id
}

// The lowest node of a subtree: its nodes are [it, n] (children are made
// before their parents).
tc_subtree_lo :: proc(k: ^TC, n: Tree_Id) -> Tree_Id {
    lo := n
    kids := make([dynamic]Tree_Id, context.temp_allocator)
    tree_children(k.t, n, &kids)
    for c in kids { lo = min(lo, tc_subtree_lo(k, c)) }
    return lo
}
