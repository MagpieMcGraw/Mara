package mara

import "core:fmt"
import "core:mem/virtual"
import "core:os"
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
    several_ok:    Tree_Id,           // the call (or `?`) about to be checked where several results go — tc_call
    modules:       map[string][]Tree_Id,   // each module's files' roots, in path order
    pkg:           string,            // the module being checked
    // The block scopes and the names bound in them: what name resolution
    // works in while the check runs — scratch, gone once it's done
    // (tc_blocks_end); the annotations keep what each name refers to.
    blocks:        ^virtual.Arena,
    flat_names:    map[[2]string]string,   // a name in a module, flat — each made once (resolve_type_name)
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
    scope_at:      map[Tree_Id]int,       // ... by its node (no instance's): whose definitions a name may need registered
    mine:          ^[dynamic]int,     // the ones the module being checked registered
    checked_modules: map[string]^Type_Scope,
    in_progress:   map[string]bool,
    std:           ^Type_Scope,
    salt:          u64,               // the instance being checked's number (0: none): tc_sid
    salt_lo, salt_hi: Tree_Id,        // its template's body's nodes
    instance_count: u64,
    infer_at:      Span,              // the argument a generic's type param is bound from (tc_generic_call)
    templates:     map[Token_Id]TC_Template, // the generic definitions (a union's too), by the token that declares them
    consts:        map[string]^TC_Const,     // the constants, by their symbols (a module's flat name, a body's owner-named)
    scope_consts:  map[^Type_Scope]map[string]^TC_Const,   // the constants a body, or a struct, defines
    const_at:      map[Token_Id]^TC_Const,   // each constant, by the token that declares it (a body's: its latest instance's)
    instances:     map[string]^Type_Scope,   // each generic fun's instances, by mangled name
    instance_order: [dynamic]string,
    recv:          TC_Recv,           // the call being checked's receiver, checked
    body:          ^Type_Scope,       // the fun or struct whose body is being checked: what its bindings are variables of
    vars:          [dynamic]Var_Decl, // ... the variables it has bound so far (Annotations.vars once it is done)
    decls:         ^[dynamic]TC_Decl_Note,   // the block being checked's declarations
    field_default: TC_Field_Default,  // the struct field whose value is being checked
    struct_instances: [dynamic]int,   // each generic struct's instance's scope, as made
    variant_scopes:   [dynamic]int,   // each union variant's struct's scope (one with a body: tc_variant_struct)
    exposed:       map[Tree_Id]bool,  // each definition `#expose` marks (a DLL's entry)
    arena_size:    Tree_Id,           // the program's arena's size (tc_scan_allocator) ...

    // Names (design/name_resolution.md): what each refers to, the resolver's,
    // found before the check; and what each declaration means now — a
    // definition's type, a variable's in the body being checked, a template's
    // in the instance being checked — by the token that declares it.
    rs:            ^Resolver,
    top:           bool,                // a body's own block being checked (not a nested one's): tc_scope
    in_defer:      bool,                // a defer's block being checked (its body's)
    loops:         int,                 // the loops around the statement being checked (in its body, or its defer's block)
    module_scopes: map[string]^Type_Scope,   // each module's record, by its name: what its definitions are declared in
    bound:         []u32,               // by token: its binding's place in binds (0: none)
    binds:         [dynamic]Type,       // (dense, in the order they're bound: a map's inserts miss the cache)
    bound_log:     [dynamic]TC_Bound,   // each binding's before, for an instance to give back (tc_instance_end)
}

// A binding's before: what the token meant, if anything.
TC_Bound :: struct {
    tok: Token_Id,
    was: Type,
    had: bool,
}

// A declaration's meaning, from here on. (In an instance, what it meant is
// kept: the instance gives its template's tokens back when it's done.)
tc_bound_set :: proc(k: ^TC, tok: Token_Id, t: Type) {
    if tok == 0 { return }
    if k.salt != 0 {
        was, had := tc_bound(k, tok)
        append(&k.bound_log, TC_Bound{tok, was, had})
    }
    tc_bound_put(k, tok, t)
}

// What a declaration meant once the check was done (a builtin's: by name).
checked_binding :: proc(c: ^Checked_Program, ref: Ref, name: string) -> (Type, bool) {
    if ref.kind == .Builtin {
        t, ok := c.table.builtins[name]
        return t, ok
    }
    if ref.decl == 0 || int(ref.decl) >= len(c.bound) { return nil, false }
    at := c.bound[ref.decl]
    return c.binds[at], at != 0
}

// What a declaration means now, if it's bound.
tc_bound :: proc(k: ^TC, tok: Token_Id) -> (Type, bool) {
    at := k.bound[tok]
    return k.binds[at], at != 0
}

tc_bound_put :: proc(k: ^TC, tok: Token_Id, t: Type) {
    if at := k.bound[tok]; at != 0 { k.binds[at] = t; return }
    k.bound[tok] = u32(len(k.binds))
    append(&k.binds, t)
}

// A binding given back: what the token meant before (or nothing).
tc_bound_restore :: proc(k: ^TC, tok: Token_Id, was: Type, had: bool) {
    if had { tc_bound_put(k, tok, was) } else { k.bound[tok] = 0 }
}

// What a name means: its declaration's binding (a builtin's, by its name).
// A struct's or a fun's definitions are registered when it's checked, or
// when one is named: here, when the name is one of them.
tc_ref_type :: proc(k: ^TC, ref: Ref, name: string) -> (Type, bool) {
    if ref.kind == .Builtin {
        t, ok := k.table.builtins[name]
        return t, ok
    }
    if ref.decl == 0 { return nil, false }
    if t, ok := tc_bound(k, ref.decl); ok { return t, true }
    if ref.kind != .Type && ref.kind != .Fun && ref.kind != .Const { return nil, false }
    if !tc_owner_registered(k, ref.decl) { return nil, false }
    return tc_bound(k, ref.decl)
}

// A definition's owner — the fun or struct whose body has it — registered,
// its own owner first. (False: it has none, or none registered: a module's.)
tc_owner_registered :: proc(k: ^TC, decl: Token_Id) -> bool {
    owner := k.rs.owners[decl] or_else 0
    if owner == 0 { return false }
    def := k.rs.defs[owner] or_else 0
    if def == 0 { return false }
    node := Tree_Id(k.t.b[def])
    i, ok := k.scope_at[node]
    if !ok {
        // (A nested one: its own owner registers it.)
        if !tc_owner_registered(k, owner) { return false }
        i, ok = k.scope_at[node]
        if !ok { return false }
    }
    tc_register_defs(k, k.scopes[i])
    return true
}

// A generic's type params, each by the token that declares it: what an
// instance (or a dispatch's trial of one) binds it to.
TC_Bindings :: map[Token_Id]Type

// A generic's type params bound: an instance's (tc_instance_begin), or a
// trial's — given back after (tc_type_params_restore).
tc_type_params_bind :: proc(k: ^TC, subst: TC_Bindings) -> []TC_Bound {
    was := make([dynamic]TC_Bound, 0, len(subst), context.temp_allocator)
    for tok, bound in subst {
        if bound == nil { continue }
        t, had := tc_bound(k, tok)
        append(&was, TC_Bound{tok, t, had})
        tc_bound_set(k, tok, bound)
    }
    return was[:]
}

tc_type_params_restore :: proc(k: ^TC, was: []TC_Bound) {
    for b in was { tc_bound_restore(k, b.tok, b.was, b.had) }
}

// A dispatch group's member: its name, what it refers to (resolved where
// the group is written).
TC_Member :: struct {
    name: string,
    ref:  Ref,
}

// The members of dispatch groups (by the tokens that declare them), in order.
tc_dispatch_members :: proc(k: ^TC, groups: []Token_Id) -> []TC_Member {
    t := k.t
    out := make([dynamic]TC_Member, context.temp_allocator)
    for g in groups {
        def := k.rs.defs[g] or_else 0
        if def == 0 { continue }
        for tok in tree_token_list(t, t.a[t.b[def]]) { append(&out, TC_Member{tc_text(tok), k.rs.token_refs[tok] or_else {}}) }
    }
    return out[:]
}

// The constant a name refers to (nil: none).
tc_const_named :: proc(k: ^TC, n: Tree_Id) -> ^TC_Const {
    ref := k.rs.refs[n]
    if ref.kind != .Const { return nil }
    return k.const_at[ref.decl] or_else nil
}

// Whether a ref names a definition of a module's or a type's — what a
// qualified name's members are the resolver's for.
tc_names_def :: proc(ref: Ref) -> bool {
    #partial switch ref.kind {
    case .Module, .Type, .Fun: return true
    }
    return false
}

// A name bound in scope s, and its declaration's meaning.
tc_scope_bind :: proc(k: ^TC, s: ^Type_Scope, name: string, t: Type, ref: Ref) {
    scope_bind(s, name, t)
    tc_bound_set(k, ref.decl, t)
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
    salt:     TC_Salt,
    pkg:      string,
}

TC_Event_Kind :: enum u8 { Body, Const, Module_Stmt, Program_Struct }

tc_event :: proc(k: ^TC, e: TC_Event) {
    e := e
    e.salt, e.pkg = {salt = k.salt, lo = k.salt_lo, hi = k.salt_hi}, k.pkg
    append(&k.events, e)
}

// The results of the fun (or constructor) whose body is being checked.
// Empty: none, or no body (a module's constant).
tc_results :: proc(k: ^TC) -> []Type {
    if k.body == nil { return nil }
    return k.body.return_types[:]
}

// A name declared: what it means (its binding); a variable of the body being
// checked — a param, a named result, a local — kept as one of its variables
// (Annotations.vars). (`_` names no variable.)
tc_bind :: proc(k: ^TC, name: string, t: Type, ref: Ref) {
    tc_bound_set(k, ref.decl, t)
    #partial switch ref.kind {
    case .Local, .Param, .Result:
        if k.body != nil && ref.decl != 0 && name != "_" { append(&k.vars, Var_Decl{ref.decl, ref.kind, t}) }
    }
}

// The check done: its scratch goes (TC.blocks: its blocks' declarations).
tc_blocks_end :: proc(k: ^TC) {
    virtual.arena_destroy(k.blocks)
    free(k.blocks)
    k.blocks = nil
}

tc_module_stmt :: proc(k: ^TC, sid: Syntax_Id) {
    tc_event(k, {kind = .Module_Stmt, sid = sid})
}

// A fun or a struct as registered: its type, its definition, the scope its
// name is declared in.
TC_Scope :: struct {
    ts:   ^Type_Scope,
    def:  Tree_Id,   // its Define
    node: Tree_Id,   // its Fun_Def or Struct_Def
    nested: [dynamic]int,   // the funs and structs defined in its body
    consts: [dynamic]^TC_Const,   // the constants defined in its body
    subst:  TC_Bindings,       // an instance's: its type params bound
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
tc_instance_begin :: proc(k: ^TC, tmpl: TC_Template, ts: ^Type_Scope, subst: TC_Bindings) -> (saved: TC_Salt) {
    saved = {k.salt, k.salt_lo, k.salt_hi, len(k.bound_log), k.t.first[tmpl.def], k.t.end[tmpl.def]}
    k.instance_count += 1
    id := annot_instance(k.annot, tmpl.lo, tmpl.node, ts)
    assert(u64(id) == k.instance_count)
    k.salt, k.salt_lo, k.salt_hi = k.instance_count, tmpl.lo, tmpl.node
    tc_type_params_bind(k, subst)   // (its type params: what it binds them to)
    return
}

// The instance a node is read in, set (lowering's: as each event was checked).
tc_salt_set :: proc(k: ^TC, salt: TC_Salt) {
    k.salt, k.salt_lo, k.salt_hi = salt.salt, salt.lo, salt.hi
}

tc_instance_end :: proc(k: ^TC, saved: TC_Salt) {
    k.salt, k.salt_lo, k.salt_hi = saved.salt, saved.lo, saved.hi
    // (What its template's tokens meant before it, back; the rest — what it
    // checked of the program's on the way — stays.)
    for i := len(k.bound_log) - 1; i >= saved.log; i -= 1 {
        b := k.bound_log[i]
        if b.tok < saved.first || b.tok >= saved.end { continue }
        tc_bound_restore(k, b.tok, b.was, b.had)
    }
}

TC_Salt :: struct {
    salt:   u64,
    lo, hi: Tree_Id,
    log:    int,                  // the bindings so far, at its start
    first, end: Token_Id,         // its template's tokens: what it binds its own way
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
                         shared: bool = false, web: bool = false, target_os: Target_OS = .Windows, profile_memory := false,
                         analysis_only: bool = false, no_assert: bool = false, perf: ^Performance_Timer = nil,
                         lower := true) -> ^Checked_Program {
    table := new(SymbolTable)
    main_mod := new(Type_Scope)
    main_mod.name = main_package
    main_mod.home_package = main_package
    main_mod.kind = .Struct
    main_mod.is_module = true
    k_module_scopes := make(map[string]^Type_Scope)
    k_module_scopes[main_package] = main_mod

    c := new(Checker)
    c.table = table
    checked := new(Checked_Program)
    checked.table = table
    checked.target_os = target_os
    checked.main_package = main_package
    c.target_web, c.target_os, c.analysis_only = web, target_os, analysis_only
    c.profile_memory = profile_memory

    k := &TC{t = t, c = c, table = table, checked = checked, modules = modules, main_package = main_package, shared = shared, no_assert = no_assert, module_scopes = k_module_scopes}
    // (What the check finds, reported in source order: diagnostics_sort.)
    diagnosed := diagnostics_count()
    ir_types_forget()   // (a check of serve's, after another: its types are new)
    types_forget_shapes()
    k.rs = resolve_program(k)
    k.bound = make([]u32, len(build_tokens))
    append(&k.binds, nil)   // (place 0: none)
    k.annot = annot_new(t)
    checked.annot = k.annot
    k.blocks = new(virtual.Arena)
    if err := virtual.arena_init_growing(k.blocks); err != nil { fmt.panicf("no arena for the block scopes (%v)", err) }

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
    table.builtins["std"] = std_fun
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
        args_type := type_partial_array(64, type_slice(Type_Utf8{}))
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
        table.builtins["this_program"] = prog_type
        table.builtins["Program"] = prog_type
    }
    void_type := type_ptr(Type_Any{})
    table.builtins["void"] = void_type

    k.pkg = main_package
    main := tc_check_module_files(k, files)

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
        checked.functions[key] = ft
    }
    tc_event(k, {kind = .Program_Struct})
    tc_validate_allocator(k)
    tc_validate_main(k, main)
    tc_blocks_end(k)
    diagnostics_sort(diagnosed)

    // (lower false: the annotations are all that's wanted — mara lsp's.)
    fns := flow_functions(checked)   // (in name order, once)
    mid: Middle
    if c.errors == 0 && lower {
        // The checker only checks: each code is lowered from the annotated
        // tree once it is done, and analysed (middle.odin).
        if perf != nil { perf_timer_mark(perf, "lower") }
        checked.call_graph = build_call_graph(checked)
        c.cg = &checked.call_graph
        tree_parents(t)   // (each code's statements are the tree's: graph_stmt climbs to them)
        mid = middle_program(k, c, checked, fns)
        // (Each constant's names, by its value, for the builder to name tables.)
        for key, kc in k.consts { mid.prog.constant_names[key] = kc.sid }
        checked.code = build_program_graph(mid.prog)
        // (The analyses ran as each code was lowered: their time is
        // analysis's, with the report of what they found.)
        if perf != nil { perf_timer_mark_carry(perf, "analysis", mid.analysed) }
    } else {
        if k.gb != nil { graph_builder_free(k.gb) }
    }
    k.gb = nil
    void_defaults: map[Span]bool
    if len(checked.code.codes) > 0 { void_defaults = tc_void_defaults(k, checked, fns) }
    if mid.on {
        middle_report(c, checked, &mid, fns, void_defaults)
        middle_free(&mid)
    }
    annot_check(k.annot, t, &checked.code, c.errors)
    resolve_check(k)
    checked.rs, checked.bound, checked.binds = k.rs, k.bound, k.binds[:]
    checked.errors = c.errors
    return checked
}

// A module's files: each its own scope (its imports its own), chained to the
// module's, where its definitions are declared; their names registered, then
// their bodies checked.
tc_check_module_files :: proc(k: ^TC, files: []Tree_Id) -> []int {
    // (The scopes this module registers: a `use` in it checks another, whose
    // own are its.)
    saved := k.mine
    list: [dynamic]int
    k.mine = &list
    defer k.mine = saved
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_register_types(k, s) }
    }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_register(k, s) }
    }
    mine := list[:]
    // (Signatures first: a constant's value may call a fun — an error, but
    // one found at its call.)
    for i in mine { tc_signature(k, k.scopes[i]) }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_resolve(k, s) }
    }
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) { tc_validate(k, s) }
    }
    // A struct's fields are what its body declares: each struct's body is
    // checked first (or sooner, by what needs its fields), then each fun's.
    for i in mine { tc_struct_ensure(k, k.scopes[i].ts) }
    for i in mine {
        if ts := k.scopes[i].ts; ts != nil && ts.kind == .Fun { tc_scope_body(k, k.scopes[i]) }
    }
    for i in mine {
        tc_module_stmt(k, tc_sid(k, k.scopes[i].def))
    }
    // (Its foreign funs, for the emitter.)
    for f, i in files {
        for s in tc_live(k, tree_list(k.t, k.t.a[f])) {
            if k.t.tag[s] == .Foreign { tc_extract_foreign(k, s, k.pkg) }
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
tc_register_types :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    if t.tag[s] != .Define { return }
    value := Tree_Id(t.b[s])
    if value == 0 { return }
    if t.a[s] == 0 {
        #partial switch t.tag[value] {
        case .Fun_Def, .Struct_Def:
            tc_register_scope(k, s, value)
            return
        case .Alias_Def, .Distinct_Def:
            tc_register_distinct(k, s, value)
            return
        case .Union_Def, .Error_Def:
            tc_register_union(k, s, value)
            return
        }
    }
    if !tc_is_definition(t.tag[value]) { tc_register_const(k, s, value) }
}

// The rest of a module statement, the second pass: a `use`, a dispatch, an
// overload.
tc_register :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    #partial switch t.tag[s] {
    case .Module:
        return
    case .Expr_Stmt:
        if e := Tree_Id(t.a[s]); t.tag[e] == .Import {
            tc_use(k, e)
            tc_module_stmt(k, tc_sid(k, s))
            return
        }
    case .Define:
        value := Tree_Id(t.b[s])
        if value != 0 && t.tag[value] == .Import {
            m := tc_use(k, value, alias = t.main[s])
            tc_module_stmt(k, tc_sid(k, s))
            return
        }
        if value != 0 && t.tag[value] == .Dispatch_Def && t.a[s] == 0 {
            return   // (the resolver's: its members are checked to exist once every name is known)
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
        tc_module_decl(k, s)
        return
    case .Foreign:
        tc_register_foreign(k, s)
        return
    case .Overload:
        return   // (the resolver's: resolve_overloads)
    }
    tc_unsupported(k, s, "this module statement")
}

// `T :: type U`, `T :: distinct U`: its name (its base once every name is
// known: tc_resolve). (`owner`: the body defining it — named for it.)
tc_register_distinct :: proc(k: ^TC, def, node: Tree_Id, owner: ^Type_Scope = nil) {
    name := tc_name(k, def)
    span := tree_span(k.t, def)
    alias := k.t.tag[node] == .Alias_Def
    flat := make_flat_name(k.pkg, name) if owner == nil else fmt.aprintf("%s_%s", owner.name, name)
    if flat in k.table.distinct_types {
        tc_error(k, span, TYPE_ALREADY_DEFINED, "type" if alias else "distinct type", name)
        return
    }
    dt := new(Type_Distinct)
    dt.name, dt.source_name, dt.span, dt.home_package = flat, name, span, k.pkg
    dt.is_alias = alias
    k.table.distinct_types[flat] = dt
    tc_bound_set(k, k.t.main[def], dt)
}

// What a module statement leaves for every name to be known: a distinct
// type's base.
tc_resolve :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    if t.tag[s] != .Define { return }
    value := Tree_Id(t.b[s])
    if value != 0 && !tc_is_definition(t.tag[value]) {
        // (A constant: checked, and built, here in its module's order.)
        if kc := k.const_at[t.main[s]] or_else nil; kc != nil && kc.def == s {
            tc_check_const(k, kc)
            tc_module_stmt(k, tc_sid(k, s))
        }
        return
    }
    if t.a[s] != 0 { return }
    if value != 0 && t.tag[value] == .Union_Def {
        tc_resolve_union(k, s, value)
        return
    }
    if value == 0 || (t.tag[value] != .Alias_Def && t.tag[value] != .Distinct_Def) { return }
    tc_resolve_distinct(k, s, value)
}

// `T :: distinct U`'s (or `type U`'s) base, once every name is known.
tc_resolve_distinct :: proc(k: ^TC, s, value: Tree_Id) {
    t := k.t
    if dt, ok := tc_bound(k, t.main[s]); ok && dt.(^Type_Distinct).base_type == nil {
        dt := dt.(^Type_Distinct)
        if base := Tree_Id(t.a[value]); t.tag[base] == .Type_Slice && t.a[base] != 0 {
            tc_error(k, tree_span(t, base), TYPE_SLICE_ALIAS_CAPACITY)
        }
        dt.base_type = tc_type(k, Tree_Id(t.a[value]), tree_span(t, s))
    }
}

// What a module statement is checked for once its signatures are: a
// dispatch's functions, an overload's dispatch.
tc_validate :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    #partial switch t.tag[s] {
    case .Define:
        value := Tree_Id(t.b[s])
        if value == 0 || t.tag[value] != .Dispatch_Def { return }
        name := tc_name(k, s)
        for m in tc_dispatch_members(k, {t.main[s]}) {
            if found, ok := tc_ref_type(k, m.ref, m.name); ok {
                if tf, is_scope := found.(^Type_Scope); !is_scope || len(tf.params) == 0 {
                    tc_error(k, span, TYPE_DISPATCH_GROUP_FUNCTION, name, m.name)
                }
            } else if _, is_template := tc_template(k, m.ref); !is_template {
                tc_error(k, span, TYPE_DISPATCH_GROUP_FUNCTION_DEFINED, name, m.name)
            }
        }
    case .Overload:
        name := tc_text(Token_Id(t.b[s]))
        if len(resolve_dispatches(k.rs, Token_Id(t.b[s]), name)) == 0 { tc_error(k, span, TYPE_OVERLOAD_DISPATCH_GROUP, name) }
    }
}

// A fun or a struct: its name declared in its module, its type made (its
// signature and body wait).
tc_register_scope :: proc(k: ^TC, def, node: Tree_Id) {
    t := k.t
    name := tc_name(k, def)
    span := tree_span(t, def)
    v := scope_view(t, node)
    is_struct := t.tag[node] == .Struct_Def
    if tc_is_generic(k, node) {
        // (A template: checked as each instance.)
        k.templates[t.main[def]] = TC_Template{def = def, node = node, lo = tree_lo(k.t, node), pkg = k.pkg}
        // (Its place in the module's order: a template the module's scope
        // binds a type to is that type's declaration — mara.core's `Program`
        // is the compiler's program struct — extracted there: tc_extract.)
        append(k.mine, len(k.scopes))
        append(&k.scopes, new_clone(TC_Scope{def = def, node = node}))
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
    ts.node, ts.parent_scope = node, k.module_scopes[k.pkg] or_else nil
    ts.has_parens = build_tokens[t.main[node] + 1].kind == .Left_Paren
    ts.is_packed = v.packed != 0
    ts.is_exposed = k.exposed[def]
    // (A struct with params is constructed by a call, as a fun is.)
    callable := !is_struct || len(v.params) > 0
    if callable { k.table.funs[flat] = ts } else { k.table.structs[flat] = ts }
    ts.decl = t.main[def]
    tc_bound_set(k, ts.decl, ts)
    k.scope_of[ts] = len(k.scopes)
    append(k.mine, len(k.scopes))
    k.scope_at[node] = len(k.scopes)
    append(&k.scopes, new_clone(TC_Scope{ts = ts, def = def, node = node}))
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
            pt := tc_param_type(k, tc_text(name), pv.type_, def, span, slot)
            append(&ts.params, Struct_Type_Field{name = tc_text(name), decl = name, type_ = pt, default_node = def, default_slot = slot})
        }
    }
    if ts.kind == .Struct && len(v.params) == 0 { return }   // (no constructor: no results)
    for r in v.returns {
        if t.tag[r] == .Param_Group {
            // (Named: locals its body binds.)
            pv := params_view(t, r)
            rt := tc_type(k, pv.type_, span)
            for name in pv.names {
                append(&ts.return_types, rt)
                append(&ts.return_binding_names, tc_text(name))
                append(&ts.return_binding_decls, name)
            }
            continue
        }
        append(&ts.return_types, tc_type(k, r, span))
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
            // A template, extracted as the builtin type of its name (mara.core's
            // `Program`: the compiler's), when there's one.
            name := tc_name(k, sc.def)
            found, _ := tc_ref_type(k, {kind = .Builtin}, name)
            if ft = found.(^Type_Scope) or_else nil; ft == nil { continue }
            key := make_flat_name(module, name)
            k.annot.decls[tc_sid(k, sc.node)] = ft
            ft.origin = Origin_Source{}
            ft.body_span = tree_span(k.t, sc.def)
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
    generic := tc_union_is_generic(k, node)
    for vn in tree_list(t, t.b[node]) {
        if v := tc_variant(k, vn, 0); v.fields {
            name := strings.concatenate({tc_name(k, s), "_", v.name}, context.temp_allocator)
            append(decls, Graph_Decl{id = tc_sid(k, vn), span = tree_span(t, vn), form = .Scope, name = name, generic = generic, node = tc_sid(k, Tree_Id(t.b[vn]))})
        }
    }
}

// What a statement outside any body declares, as the builder builds it.
tc_graph_decl :: proc(k: ^TC, s: Tree_Id) -> Graph_Decl {
    t := k.t
    d := Graph_Decl{id = tc_sid(k, s), span = tree_span(t, s)}
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
            d.form, d.generic, d.node = .Scope, tc_is_generic(k, value), tc_sid(k, value)
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
tc_param_type :: proc(k: ^TC, name: string, type_, def: Tree_Id, span: Span, slot: Maybe(int) = nil) -> Type {
    if type_ != 0 { return tc_type(k, type_, span) }
    if def == 0 { return Type_Error{} }
    // (A slot of a call's results: that result's type; else the value's.)
    if at, is_slot := slot.?; is_slot {
        if call := tc_unparen(k, def); tc_is_call(k, call) {
            if t, ok := tc_ref_type(k, tc_callee_ref(k, call), tc_call_name(k, call)); ok {
                if ft, is_scope := t.(^Type_Scope); is_scope && ft.kind == .Fun && at < len(ft.return_types) { return ft.return_types[at] }
            }
        }
        return solidify_type(tc_check(k, def))
    }
    if k.t.tag[def] == .Number {
        if strings.index_byte(tc_text(k.t.main[def]), '.') >= 0 { return Type_F64{} }
        cell := new(Infer_Cell)
        cell.name, cell.span = name, span
        return Type_Infer_Int{cell = cell}
    }
    return solidify_type(tc_check(k, def))
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

    // Its names (design/name_resolution.md): the resolver's, and what each
    // declaration meant once the check was done (checked_binding) — mara
    // lsp's completion's.
    rs:             ^Resolver,
    bound:          []u32,
    binds:          []Type,

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

    // What no source declares, by name: this_program, Program, std, void.
    builtins: map[string]Type,
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
    profile_memory:  bool,                // -profile memory, drives #profile_memory (mara.memory's arenas report their use)
    analysis_only:   bool,                // `mara ask` — read-only static analysis; never emits or runs code, so runtime-shape guards (e.g. the arena/stack-size routing check) that assume an executable with a `main` are skipped
    // The materialized call graph (set post-check, after build_call_graph) — its
    // bottom-up summaries back the escape pass and the `ask` slicer. Points at
    // checked.call_graph.
    cg:              ^Call_Graph,
    // True while resolving a `foreign` declaration's signature — the only
    // context where `cstring` may be named as a type.
    in_foreign_sig: bool,
}

check_error :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    // Once per place: two checks can reach one node (a declaration's
    // literal is checked as a value and as what the declaration holds).
    if emit_diagnostic_once(.Type_Error, span, msg, ..args) {
        c.errors += 1
    }
}

check_warning :: proc(c: ^Checker, span: Span, msg: string, args: ..any) {
    emit_diagnostic_at(.Warning, span, msg, ..args)
}

