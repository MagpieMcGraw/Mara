package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// The type checker, on the flat tree (design/flat_tree.md). It fills the
// Checked_Program — the symbol table, the Type_Scopes, the diagnostics —
// from the tree as written: nothing desugared, nothing cloned. It only
// checks: what it finds about a node is kept by its id, in the instance it
// is checked in (annot.odin), and the program graph is lowered from the
// tree and those annotations once it is done (lower.odin;
// design/annotated_tree.md).
//
// Checking an expression returns its type (tc_check), not a side channel.

TC :: struct {
    t:             ^Tree,
    c:             ^Checker,          // the error sink and table the shared passes and helpers take
    table:         ^SymbolTable,
    checked:       ^Checked_Program,
    gb:            ^Graph_Builder,    // lowering's builder, while it runs (lower.odin)
    // `&x.f()` calls being checked (tc_method_call). One checked again inside
    // itself — `f(&x)` with no f: its argument, the `&` around the call,
    // checked for the error — stops there.
    addressed_calls: map[Tree_Id]bool,
    modules:       map[string][]Tree_Id,   // each module's files' roots, in path order
    pkg:           string,            // the module being checked
    root:          ^Type_Scope,       // the main module's scope: the root env
    main_package:  string,
    shared:        bool,
    no_assert:     bool,              // -no assert: each assert lowered behind a branch never taken (lw_assert)
    annot:         ^Annotations,      // what it finds about each node, per instance (annot.odin)
    events:        [dynamic]TC_Event, // what it checked, in order: what lowering builds
    lowering:      bool,              // lowering is running (lower.odin): the checker isn't
    lower:         Lower,             // ... its state
    const_by_decl: map[u64]^TC_Const,   // each constant, by its instance and the token that declares it (lowering's)
    hint:          Type,              // the type the expression being checked is expected at
    scopes:        [dynamic]^TC_Scope,   // the funs and structs registered, to check and extract
    scope_of:      map[^Type_Scope]int,   // each one's, by its type
    mine:          ^[dynamic]int,     // the ones the module being checked registered
    checked_modules: map[string]^Type_Scope,
    in_progress:   map[string]bool,
    std:           ^Type_Scope,
    salt:          u64,               // the instance being checked's number (0: none): tc_sid
    salt_lo, salt_hi: Tree_Id,        // its template's body's nodes
    instance_count: u64,
    infer_at:      Span,              // the argument a generic's type param is bound from (tc_generic_call)
    templates:     map[string]TC_Template,   // the generic definitions, by name
    consts:        map[string]^TC_Const,     // the constants, by flat name (and bare, unless two modules share it)
    const_owners:  map[string]string,        // each bare name's module ("": more than one)
    scope_consts:  map[^Type_Scope]map[string]^TC_Const,   // the constants a body, or a struct, defines
    instances:     map[string]^Type_Scope,   // each generic fun's instances, by mangled name
    instance_order: [dynamic]string,
    subst:         map[string]Type,   // the type params bound, in an instance being checked
    recv:          TC_Recv,           // the call being checked's receiver, checked
    body:          ^Type_Scope,       // the fun or struct whose body is being checked: what its bindings are variables of
    vars:          [dynamic]Var_Decl, // ... the variables it has bound so far (Annotations.vars once it is done)
    decls:         ^[dynamic]TC_Decl_Note,   // the block being checked's declarations
    field_default: TC_Field_Default,  // the struct field whose value is being checked
    struct_instances: [dynamic]int,   // each generic struct's instance's scope, as made
    variant_scopes:   [dynamic]int,   // each union variant's struct's scope (one with a body: tc_variant_struct)
    union_templates: map[string]TC_Template,   // each generic union, by name
    exposed:       map[Tree_Id]bool,  // each definition `#expose` marks (a DLL's entry)
    arena_size:    Tree_Id,           // the program's arena's size (tc_scan_allocator) ...
    arena_env:     ^Type_Scope,       // ... and where it is written
}

// What the checker checked, in the order it did — a body, a constant, a
// module's statement settled, the program's struct — and where: the instance
// and the module it was checked in. What lowering builds, in that order
// (lower.odin).
TC_Event :: struct {
    kind:     TC_Event_Kind,
    sc:       ^TC_Scope,         // .Body
    kc:       ^TC_Const,         // .Const
    sid:      Syntax_Id,         // .Module_Stmt
    declared: Graph_Declared,    // .Module_Stmt
    salt:     TC_Salt,
    pkg:      string,
    subst:    map[string]Type,
}

TC_Event_Kind :: enum u8 { Body, Const, Module_Stmt, Program_Struct }

tc_event :: proc(k: ^TC, e: TC_Event) {
    e := e
    e.salt, e.pkg, e.subst = {k.salt, k.salt_lo, k.salt_hi}, k.pkg, k.subst
    append(&k.events, e)
}

// A module's statement settled: what it declares, for lowering.
// A name bound in `env`; a variable of the body being checked — a param, a
// named result, a local — kept as one of its variables (Annotations.vars).
// (`_` names no variable.)
tc_bind :: proc(k: ^TC, env: ^Type_Scope, name: string, t: Type, ref: Ref) {
    scope_bind(env, name, t, ref)
    #partial switch ref.kind {
    case .Local, .Param, .Result:
        if k.body != nil && ref.decl != 0 && name != "_" { append(&k.vars, Var_Decl{ref.decl, ref.kind, t}) }
    }
}

tc_module_stmt :: proc(k: ^TC, sid: Syntax_Id, declared: Graph_Declared) {
    tc_event(k, {kind = .Module_Stmt, sid = sid, declared = declared})
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

// What the checker doesn't check yet: an error, so the program fails
// visibly rather than differently.
tc_unsupported :: proc(k: ^TC, n: Tree_Id, what: string) {
    tc_error(k, tree_span(k.t, n), "%s is not supported yet (%v)", what, k.t.tag[n])
}

tc_node_type :: proc(k: ^TC, n: Tree_Id) -> Type {
    if n == 0 { return nil }
    return annot_type(k.annot, tc_instance(k, n), n)
}

tc_set_type :: proc(k: ^TC, n: Tree_Id, t: Type) {
    if n == 0 { return }
    annot_set_type(k.annot, tc_instance(k, n), n, t)
}

// The instance a node is checked in: the generic's being checked, for its
// template's nodes; else the tree as written (as tc_sid salts it).
tc_instance :: proc(k: ^TC, n: Tree_Id) -> Instance_Id {
    if k.salt != 0 && n >= k.salt_lo && n <= k.salt_hi { return Instance_Id(k.salt) }
    return 0
}

// A generic's instance made: numbered, and its template's nodes checked as
// its own (tc_sid, tc_instance) until tc_instance_end puts back the one
// being checked before.
tc_instance_begin :: proc(k: ^TC, tmpl: TC_Template, ts: ^Type_Scope) -> (saved: TC_Salt) {
    saved = {k.salt, k.salt_lo, k.salt_hi}
    k.instance_count += 1
    id := annot_instance(k.annot, tmpl.lo, tmpl.node, ts)
    assert(u64(id) == k.instance_count)
    k.salt, k.salt_lo, k.salt_hi = k.instance_count, tmpl.lo, tmpl.node
    return
}

tc_instance_end :: proc(k: ^TC, saved: TC_Salt) {
    k.salt, k.salt_lo, k.salt_hi = saved.salt, saved.lo, saved.hi
}

TC_Salt :: struct {
    salt:   u64,
    lo, hi: Tree_Id,
}

tc_text :: proc(tok: Token_Id) -> string {
    return token_text(build_tokens[tok])
}

// A node's name: its report point's text (a Define's, an Ident's).
tc_name :: proc(k: ^TC, n: Tree_Id) -> string {
    return tc_text(k.t.main[n])
}

// A call's name: a method's as its qualifier resolved it, else as written.
tc_call_name :: proc(k: ^TC, n: Tree_Id) -> string {
    if name, ok := k.annot.call_names[tc_sid(k, n)]; ok { return name }
    if k.t.tag[n] == .Method_Call { return tc_text(method_view(k.t, n).name) }
    return tc_name(k, n)
}

// Whether a node is a call: plain, or of a method.
tc_is_call :: proc(k: ^TC, n: Tree_Id) -> bool {
    return k.t.tag[n] == .Call || k.t.tag[n] == .Method_Call
}

// --- the program --------------------------------------------------------------

tc_check_program :: proc(t: ^Tree, modules: map[string][]Tree_Id, main_package: string,
                         shared: bool = false, web: bool = false, target_os: Target_OS = .Windows,
                         analysis_only: bool = false, no_assert: bool = false, perf: ^Performance_Timer = nil,
                         lower := true) -> ^Checked_Program {
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
    c.target_web, c.target_os, c.analysis_only = web, target_os, analysis_only

    // (Kept past the check: lowering a code again — codegen's — copies it.)
    k := new_clone(TC{t = t, c = c, table = table, checked = checked, modules = modules, root = main_mod, main_package = main_package, shared = shared, no_assert = no_assert})
    k.annot = annot_new(t)
    checked.annot = k.annot

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
    scope_bind(main_mod, "std", std_fun, {kind = .Builtin})
    k.std = std_fun
    k.checked_modules[main_package] = main_mod

    tc_scan_allocator(k)
    // (A DLL with an entry `#expose` marks: its host passes the context.)
    if shared {
        for f in files {
            for s in tc_live(k, tree_list(t, t.a[f])) { if k.exposed[s] { table.context_expected_at_runtime = true } }
        }
    }

    // The program's struct (the compiler-managed global): its args (an
    // arena when `this_program = Program(...)`).
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
        if table.has_scope_allocator {
            // (Its type the arena's, once that is found: tc_validate_allocator.)
            append(&prog_type.fields, Struct_Type_Field{name = "scope_allocator", type_ = Type_Any{}})
            prog_type.field_map["scope_allocator"] = 0
        }
        prog_type.field_map["args"] = len(prog_type.fields)
        append(&prog_type.fields, Struct_Type_Field{name = "args", type_ = args_type})
        table.funs["Program"] = prog_type
        scope_bind(main_mod, "this_program", prog_type, {kind = .Builtin})
        scope_bind(main_mod, "Program", prog_type, {kind = .Builtin})
    }
    void_type := new(Type_Ptr)
    void_type.elem = Type_Any{}
    scope_bind(main_mod, "void", void_type, {kind = .Builtin})

    k.pkg = main_package
    main := tc_check_module_files(k, files, main_mod)

    // (Generic structs' instances: their methods, their inits — before the
    // main module's.)
    for i in k.struct_instances { tc_extract(k, []int{i}, k.scopes[i].ts.home_package, false, nested = true) }
    for i in k.variant_scopes { tc_extract(k, []int{i}, k.scopes[i].ts.home_package, false, nested = true) }
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
    tc_event(k, {kind = .Program_Struct})
    tc_validate_allocator(k)
    tc_validate_main(k, main)

    // (lower false: the annotations are all that's wanted — mara lsp's.)
    fns := flow_functions(checked)   // (in name order, once)
    mid: Middle
    if c.errors == 0 && lower {
        // The checker only checks: each code is lowered from the annotated
        // tree once it is done, and analysed (middle.odin).
        if perf != nil { perf_timer_mark(perf, "lower") }
        checked.call_graph = build_call_graph(checked)
        c.cg = &checked.call_graph
        mid = middle_program(k, c, checked, fns)
        if perf != nil { perf_timer_mark(perf, "graph") }
        // (Each constant's names, by its value, for the builder to name tables.)
        for key, kc in k.consts { mid.prog.constant_names[key] = kc.sid }
        checked.code = build_program_graph(mid.prog)
        checked.again = {k = k, bodies = mid.bodies}
        if perf != nil { perf_timer_mark(perf, "analysis") }
    } else {
        if k.gb != nil { graph_builder_free(k.gb) }
        if perf != nil { perf_timer_mark(perf, "analysis") }
    }
    k.gb = nil
    void_defaults: map[Span]bool
    if len(checked.code.codes) > 0 { void_defaults = tc_void_defaults(k, checked, fns) }
    if mid.on {
        middle_report(c, checked, &mid, fns, void_defaults)
        middle_free(&mid)
    }
    annot_check(k.annot, t, &checked.code, c.errors)
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
    for _, i in files {
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
    // one found at its call.)
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
        tc_module_stmt(k, tc_sid(k, k.scopes[i].def), {kind = .Other, set = true})
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
// A module statement's names, the first pass: its
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
            tc_module_stmt(k, tc_sid(k, s), {kind = .Decl, set = true})
            return
        }
    case .Define:
        value := Tree_Id(t.b[s])
        if value != 0 && t.tag[value] == .Import {
            m := tc_use(k, value, env, mod, alias = t.main[s])
            tc_module_stmt(k, tc_sid(k, s), {kind = .Other, set = true})
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
    case .Decl:
        tc_module_decl(k, s, env)
        return
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
    scope_bind(mod, name, dt, {k.t.main[def], .Type})
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
            tc_module_stmt(k, tc_sid(k, s), {kind = .Other, set = true})
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
        if base := Tree_Id(t.a[value]); t.tag[base] == .Type_Slice && t.a[base] != 0 {
            tc_error(k, tree_span(t, base), TYPE_SLICE_ALIAS_CAPACITY)
        }
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
            if found, ok := scope_lookup(env, f); ok {
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
        if name not_in k.templates { k.templates[name] = TC_Template{def = def, node = node, lo = tree_lo(k.t, node), env = env, pkg = k.pkg} }
        if !is_struct && len(v.params) > 0 { k.c.declared_funs[name] = true }
        // (Its place in the module's order: a template the module's scope
        // binds a type to is that type's declaration — mara.core's `Program`
        // is the compiler's program struct — extracted there: tc_extract.)
        append(k.mine, len(k.scopes))
        append(&k.scopes, new_clone(TC_Scope{def = def, node = node, env = env}))
        return
    }
    // (A struct's constructor may fail: one of no params has none.)
    if is_struct && len(v.returns) > 0 && len(v.params) == 0 { tc_error(k, span, TYPE_STRUCT_CLASS_CANNOT_DECLARE_RETURN, name) }
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
    ts.node, ts.parent_scope = node, env
    ts.has_parens = build_tokens[t.main[node] + 1].kind == .Left_Paren
    ts.is_packed = v.packed != 0
    ts.is_exposed = k.exposed[def]
    // (A struct with params is constructed by a call, as a fun is.)
    callable := !is_struct || len(v.params) > 0
    if callable { k.table.funs[flat] = ts } else { k.table.structs[flat] = ts }
    ts.decl = t.main[def]
    scope_bind(mod, name, ts, {ts.decl, .Type if is_struct else .Fun})
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
            // (`x, y := f()`, `a, b: i64 = 7`: one value, each its slot.)
            slot: Maybe(int)
            if len(pv.values) == 1 && len(pv.names) > 1 { def, slot = pv.values[0], i }
            pt := tc_param_type(k, tc_text(name), pv.type_, def, sc.env, span, slot)
            append(&ts.params, Struct_Type_Field{name = tc_text(name), decl = name, type_ = pt, default_node = def, default_slot = slot})
        }
    }
    if ts.kind == .Struct && len(v.params) == 0 { return }   // (no constructor: no results)
    for r in v.returns {
        if t.tag[r] == .Param_Group {
            // (Named: locals its body binds.)
            pv := params_view(t, r)
            rt := tc_type(k, pv.type_, sc.env, span)
            for name in pv.names {
                append(&ts.return_types, rt)
                append(&ts.return_binding_names, tc_text(name))
                append(&ts.return_binding_decls, name)
            }
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
            found, _ := scope_lookup(sc.env, name)
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
        // (A DLL's entry takes the host's context first: a ^Program.)
        if fn != nil && fn.is_exposed {
            ok := false
            if len(fn.params) > 0 {
                if pt, is_ptr := fn.params[0].type_.(^Type_Ptr); is_ptr {
                    if ps, is_scope := pt.elem.(^Type_Scope); is_scope && ps.name == "Program" { ok = true }
                }
            }
            if !ok { tc_error(k, tree_span(k.t, sc.def), TYPE_EXPOSE_FUNCTION_TAKE_FIRST_PARAMETER, fn.source_name) }
        }
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
            for s in tc_live(k, tree_list(k.t, k.t.a[f])) {
                append(&decls, tc_graph_decl(k, s))
                tc_variant_graph_decls(k, s, &decls)
            }
        }
        out[name] = decls[:]
    }
    return out
}

// A union's variants with bodies, after its statement: each a struct's
// constructor (a generic union's, each instance's), placed as a struct's is.
tc_variant_graph_decls :: proc(k: ^TC, s: Tree_Id, decls: ^[dynamic]Graph_Decl) {
    t := k.t
    if t.tag[s] != .Define || t.a[s] != 0 { return }
    node := Tree_Id(t.b[s])
    if node == 0 || t.tag[node] != .Union_Def { return }
    kind := tc_stmt_kind(k, s)
    generic := tc_union_is_generic(k, node)
    for vn in tree_list(t, t.b[node]) {
        if v := tc_variant(k, vn, 0); v.fields {
            name := strings.concatenate({tc_name(k, s), "_", v.name}, context.temp_allocator)
            append(decls, Graph_Decl{id = tc_sid(k, vn), span = tree_span(t, vn), kind = kind, form = .Scope, name = name, generic = generic})
        }
    }
}

// What a statement outside any body declares, as the builder builds it.
tc_graph_decl :: proc(k: ^TC, s: Tree_Id) -> Graph_Decl {
    t := k.t
    d := Graph_Decl{id = tc_sid(k, s), span = tree_span(t, s), kind = tc_stmt_kind(k, s)}
    #partial switch t.tag[s] {
    case .Expr_Stmt:
        // (A bare `use m` the checker settles.)
        if imp := Tree_Id(t.a[s]); t.tag[imp] == .Import { d.settles = true }
    case .Module, .Return, .Break, .Continue, .Overload, .Foreign:
    case .Define:
        d.name = tc_name(k, s)
        value := Tree_Id(t.b[s])
        tag := t.tag[value] if value != 0 else .Define
        #partial switch tag {
        case .Fun_Def, .Struct_Def:
            d.form, d.generic = .Scope, tc_is_generic(k, value)
        case .Import:
            d.settles = true
        case .Alias_Def, .Distinct_Def, .Dispatch_Def, .Union_Def, .Error_Def:
            // (A type, a dispatch: no code of its own.)
        case:
            d.settles, d.value = true, tc_sid(k, value)   // a constant
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
    case .Using:    return tc_stmt_kind(k, Tree_Id(k.t.a[s]))   // (its declaration's)
    case .Expr_Stmt:
        if k.t.tag[k.t.a[s]] == .Import { return .Decl }
    case .Decl:
        // (Several names from one value: a destructure — a broadcast's, its
        // copies': tc_broadcast.)
        v := decl_view(k.t, s)
        if len(v.targets) > 1 && len(v.values) == 1 { return .Destructure }
        return .Decl
    case .Assign:
        targets := tree_list(k.t, k.t.a[s])
        if len(targets) > 1 && len(targets) == len(tree_list(k.t, k.t.b[s])) { return .Other }   // (its assignments')
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
// checker's input (main.odin).
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
        for i in 1 ..< len(sorted) {   // (by path: the statement order)
            for j := i; j > 0 && sorted[j].path < sorted[j - 1].path; j -= 1 { sorted[j], sorted[j - 1] = sorted[j - 1], sorted[j] }
        }
        ids := make([]Tree_Id, len(sorted))
        for f, i in sorted { ids[i] = roots[f] }
        out[name] = ids
    }
    return out
}


// Whether a definition's value is a definition of its own (a fun, a type, an
// import, …), not a constant's value.
tc_is_definition :: proc(tag: Tree_Tag) -> bool {
    #partial switch tag {
    case .Fun_Def, .Struct_Def, .Import, .Alias_Def, .Distinct_Def, .Dispatch_Def, .Union_Def, .Error_Def, .Intrinsic_Body:
        return true
    }
    return false
}

// A binding whose uses haven't given it a width yet (`n := 0`, so far).
tc_open_binding :: proc(t: Type) -> bool {
    return infer_cell_of(t) != nil && is_infer(t)
}

// A decision that needs a width, met by a binding no use has given one yet
// (a generic's type param, a byte view's size, a dispatch's member): the
// binding's default from here on — any other use, after or before in the
// code, a conflict. The width, solid.
tc_pin_default :: proc(k: ^TC, t: Type, span: Span) -> Type {
    w := solidify_type(t)
    if tc_open_binding(t) { unify_infer_concrete(k.c, infer_cell_of(t), w, span) }
    return w
}

// A param's type: as written; else its default's — a whole number's width
// the one the body uses it at (a cell, settled once the body is checked), a
// fraction f64, anything else its checked type.
tc_param_type :: proc(k: ^TC, name: string, type_, def: Tree_Id, env: ^Type_Scope, span: Span, slot: Maybe(int) = nil) -> Type {
    if type_ != 0 { return tc_type(k, type_, env, span) }
    if def == 0 { return Type_Error{} }
    // (A slot of a call's results: that result's type; else the value's.)
    if at, is_slot := slot.?; is_slot {
        if call := tc_unparen(k, def); tc_is_call(k, call) {
            if t, ok := scope_lookup(env, tc_call_name(k, call)); ok {
                if ft, is_scope := t.(^Type_Scope); is_scope && ft.kind == .Fun && at < len(ft.return_types) { return ft.return_types[at] }
            }
        }
        return solidify_type(tc_check(k, def, env))
    }
    if k.t.tag[def] == .Number {
        if strings.index_byte(tc_text(k.t.main[def]), '.') >= 0 { return Type_F64{} }
        cell := new(Infer_Cell)
        cell.name, cell.span = name, span
        return Type_Infer_Int{cell = cell}
    }
    return solidify_type(tc_check(k, def, env))
}

// A node's id as the builder keys it. In a generic's instance, its
// template's body is checked again: its nodes are that instance's own,
// salted with the instance's
// number. (The template's definition itself is the instance's: unsalted.)
tc_sid :: proc(k: ^TC, n: Tree_Id) -> Syntax_Id {
    return annot_key(tc_instance(k, n), n)
}

// What a name refers to, as checked (a declaration's name: itself).
tc_ref :: proc(k: ^TC, n: Tree_Id) -> Ref {
    if n == 0 { return {} }
    return annot_ref(k.annot, tc_instance(k, n), n)
}

tc_set_ref :: proc(k: ^TC, n: Tree_Id, r: Ref) {
    if n == 0 { return }
    annot_set_ref(k.annot, tc_instance(k, n), n, r)
}

// A call's fun, or struct (its constructor), as checked; nil when none is
// known yet.
tc_callee :: proc(k: ^TC, n: Tree_Id) -> ^Type_Scope {
    return k.annot.callees[tc_sid(k, n)] or_else nil
}

// What each param of the call at n receives, in order.
tc_set_args :: proc(k: ^TC, n: Tree_Id, args: []Arg) {
    if n == 0 { return }
    k.annot.args[tc_sid(k, n)] = slice.clone(args)
}

// A construction's arguments when none are written: each param's default.
tc_default_args :: proc(ts: ^Type_Scope) -> []Arg {
    args := make([]Arg, len(ts.params), context.temp_allocator)
    for p, i in ts.params { args[i] = {p.default_node, .Default, i32(p.default_slot.? or_else -1)} }
    return args
}

tc_set_callee :: proc(k: ^TC, n: Tree_Id, ts: ^Type_Scope) {
    if n == 0 { return }
    k.annot.callees[tc_sid(k, n)] = ts
}

// ---------------------------------------------------------------------------
// What checking produces (Checked_Program), the symbol table it fills, and
// the state the checker shares with the passes after it (Checker).
// ---------------------------------------------------------------------------

// The complete output of tc_check_program: everything the type checker knows
// about the program — type definitions, function signatures, the program
// graph. What runs after the check (the analyses, `mara ask`, codegen) reads
// this, never the tree.
Checked_Program :: struct {
    // Shared symbol table (type definitions, constants, generics, etc.)
    table:          ^SymbolTable,

    errors:         int,

    // Functions — source, foreign, and intrinsic all live here, distinguished
    // by their origin. Codegen iterates this map and dispatches on the
    // origin variant when emitting bodies, declares, and the dynamic loader.
    functions:      map[string]^Type_Scope,
    foreign_libs:   map[string]bool,

    // Function names in the order they are written (for emission)
    function_order: [dynamic]string,

    // Materialized call graph (nodes = callable scopes, edges = resolved calls,
    // + strongly-connected components): an index over the annotated calls.
    // See callgraph.odin / design/mara_ask.md §12.
    call_graph:     Call_Graph,

    // The program's code (graph.odin): each fun's, struct's and constant's,
    // lowered from the annotated tree once it is checked: the analyses' and the
    // emitter's input.
    code:           Program_Code,

    // Target platform — drives ABI lowering for .C-convention functions.
    // Inherited from the checker; stamped at check completion.
    target_os:      Target_OS,

    // The main package name (e.g. "Pounce" or "test_1M"). Used by codegen as
    // the default home for symbols not attributable to any specific module
    // — compiler-synthesized helpers, @main, etc. — so per-module emission
    // has a single canonical "main TU" to drop them into.
    main_package:   string,

    // Def-use over the program graph (defuse.odin), built per function on the
    // first `mara ask` flow query that needs it: what the flow views slice.
    du:             Def_Use,

    // What the checker found about each node, per instance (annot.odin).
    annot:          ^Annotations,

    // What lowering a fun's or struct's code again needs (codegen's: it
    // lowers each as it emits it).
    again:          Lower_Again,
}

// ---------------------------------------------------------------------------
// Symbol table — single source of truth for all type/symbol information.
// Persists across checking phases; shared between Checker and Checked_Program.
// ---------------------------------------------------------------------------

SymbolTable :: struct {
    // Type registries
    structs:        map[string]^Type_Scope,      // data-layout scopes (struct/class with or without params)
    funs:           map[string]^Type_Scope,      // callable funs and struct constructors (kind=.Struct + params, or kind=.Fun)
    enums:          map[string]^Type_Enum,
    unions:         map[string]^Type_Union,
    distinct_types: map[string]^Type_Distinct,

    // Error_kind set ID assignment counter — incremented as each
    // `Name :: error { ... }` is registered. Encoded as the high 16 bits of
    // each variant's u32 tag so any error_kind variant fits in the open
    // `err` type with a globally unique value.
    error_set_counter: int,

    // Name resolution helpers
    variant_to_enum: map[string]string,

    // Monomorphization cache
    mono_cache:       map[string]^Type_Scope,        // unified: both data and callable monomorphizations
    mono_union_cache: map[string]^Type_Union,        // monomorphized union templates (Maybe(int) -> ^Type_Union)
    fun_homes:      map[string]string,              // bare name -> home package; used by post-check phases that lack env

    // Config
    has_scope_allocator: bool,
    scope_allocator_name: string,        // bare name from source ("Arena_Basic")
    scope_allocator_type: ^Type_Scope,     // resolved allocator fun (Arena_Basic, Arena_Debug, etc.)

    scope_allocator_size: Maybe(i64),    // the first: the arena's size (a constant: nothing but constants exists before main runs)

    // Shared (DLL/SO) build with `#expose` fn(s) present: the host promises
    // to pass a real Context at runtime, so arena-using constructs (`var`,
    // big-array auto-promotion) are permitted inside the DLL without a local
    // `context.scope_allocator = X` declaration. Gated separately from
    // has_scope_allocator so the *codegen* path still requires the type to
    // be declared (errors at codegen if arena calls would be emitted).
    context_expected_at_runtime: bool,

    // Root type environment (top-level scope)
    root_env: ^Type_Scope,
}

// ---------------------------------------------------------------------------
// Checker state: the shared SymbolTable, what checking produces, and the
// build's settings. (The checker's own walk state is TC's: tc.odin.)
// ---------------------------------------------------------------------------

Checker :: struct {
    table:           ^SymbolTable,
    errors:          int,

    target_web:      bool,                // -web build flag, drives #web / #native intrinsics

    target_os:       Target_OS,           // OS target, drives #windows / #linux / #mac intrinsics
    analysis_only:   bool,                // `mara ask` — read-only static analysis; never emits or runs code, so runtime-shape guards (e.g. the arena/stack-size routing check) that assume an executable with a `main` are skipped
    declared_funs:   map[string]bool,  // bare names of fun declarations (direct calls vs variables)
    // The materialized call graph (set post-check, after build_call_graph) — its
    // bottom-up summaries back the escape pass and the `ask` slicer. Points at
    // checked.call_graph.
    cg:              ^Call_Graph,
    // True while resolving a `foreign` declaration's signature — the only
    // context where `cstring` may be named as a type.
    in_foreign_sig: bool,
    // Dispatch and operator overloading (per-package, saved/restored on module boundaries)
    dispatch_groups:    map[string][dynamic]string,
    operator_overloads: map[Token_Kind][dynamic]string,
}

check_error :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    // Once per place: two checks can reach one node (a declaration's
    // literal is checked as a value and as what the declaration holds).
    if emit_diagnostic_once(.Type_Error, span_location(span), msg, ..args) {
        c.errors += 1
    }
}

check_warning :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    emit_diagnostic(.Warning, span_location(span), msg, ..args)
}

