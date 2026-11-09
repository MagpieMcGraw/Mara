package mara

import "core:fmt"
import "core:strings"

// The program's arena: `#allocator Arena_Debug(16 * MB)`, at the top of the
// module main is in (a DLL's — the module built — names the kind alone,
// `#allocator Arena_Basic`: its host's arena is the one that runs). Found
// before anything is checked — what is too big for the stack goes on it —
// its size checked where it's written (nothing built: main's entry makes
// the arena), its type checked for what an arena has once every module is.
// Another arena of its kind is a value (`Arena_Basic(1 * MB)`), and a block
// runs on it with `with &a {…}`.

// The main module's `#allocator` — at its top, or among main's own
// statements (main's entry makes the arena either way: what comes before it
// runs on it too): the arena's name, and its size's node.
tc_scan_allocator :: proc(k: ^TC) {
    t := k.t
    scan :: proc(k: ^TC, s: Tree_Id) {
        t := k.t
        if k.table.has_scope_allocator { return }   // (a second: tc_allocator says)
        k.table.has_scope_allocator = true
        if name, args, _, ok := tc_allocator_arena(k, tc_unparen(k, Tree_Id(t.a[s]))); ok {
            k.table.scope_allocator_name = name
            k.arena_size = args[0] if len(args) > 0 else 0
            k.arena_stmt = s
        }
    }
    for file in k.modules[k.main_package] or_else nil {
        for s in tc_live(k, tree_list(t, t.a[file])) {
            if t.tag[s] == .Allocator { scan(k, s); continue }
            is_main := t.tag[s] == .Define && tc_name(k, s) == "main" && t.tag[t.b[s]] == .Fun_Def
            if !is_main { continue }
            for b in tc_live(k, scope_view(t, Tree_Id(t.b[s])).body) {
                if t.tag[b] != .Allocator { continue }
                append(&k.main_allocators, b)
                scan(k, b)
            }
        }
    }
}

// The arena an #allocator names: `Arena_Basic(16 * MB)`, or through a name for
// its module, `mem.Arena_Basic(…)`; in a DLL, with no size. Its name, its args,
// and whether it's written as a call. Not ok: it's something else.
tc_allocator_arena :: proc(k: ^TC, arena: Tree_Id) -> (name: string, args: []Tree_Id, called, ok: bool) {
    t := k.t
    names_module :: proc(k: ^TC, n: Tree_Id) -> bool { return k.t.tag[n] == .Ident && k.rs.refs[n].kind == .Module }
    #partial switch t.tag[arena] {
    case .Call:
        return tc_name(k, arena), tree_list(t, t.a[arena]), true, true
    case .Ident:
        return tc_name(k, arena), nil, false, true
    case .Method_Call:
        if v := method_view(t, arena); names_module(k, v.receiver) { return tc_text(v.name), v.args, true, true }
    case .Field:
        if names_module(k, Tree_Id(t.a[arena])) { return tc_text(Token_Id(t.b[arena])), nil, false, true }
    }
    return
}

// `#allocator …` where it's written (a module statement, or one of main's
// own): in the module main is in, once — its size's expression checked (a
// constant: tc_validate_allocator) — or, in a DLL, the kind alone.
tc_allocator :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    span := tree_span(t, s)
    if k.pkg != k.main_package {
        tc_error(k, span, TYPE_ALLOCATOR_IN_MAIN_MODULE)
        return
    }
    if k.allocator_at != 0 && k.allocator_at != s {
        tc_error(k, span, TYPE_ALLOCATOR_TWICE)
        return
    }
    k.allocator_at = s
    arena := tc_unparen(k, Tree_Id(t.a[s]))
    name, args, called, ok := tc_allocator_arena(k, arena)
    if !ok {
        tc_error(k, span, TYPE_PROGRAM_GLOBAL_REQUIRES_ALLOCATOR_TYPE)
        return
    }
    // (By itself, its module used under a name: it's that name's to reach.)
    if bare := t.tag[arena] == .Call || t.tag[arena] == .Ident; bare && k.rs.refs[arena].kind == .None && tc_behind_use(k, span, name) { return }
    for a in args { tc_check(k, a) }
    if called && len(args) == 0 || !called && !k.shared { tc_error(k, span, TYPE_ALLOCATOR_NEEDS_SIZE, name, name) }
}

// Whether t is the program's arena's type, the one #allocator names (by
// name: the type itself is known once every module is checked).
tc_is_program_arena :: proc(k: ^TC, t: Type) -> bool {
    name := k.table.scope_allocator_name
    ts, is_scope := unwrap_alias(t).(^Type_Scope)
    if name == "" || !is_scope { return false }
    return ts.name == name || strings.has_suffix(ts.name, strings.concatenate({"_", name}, context.temp_allocator))
}

// Whether t is a pointer to an arena of the program's kind.
tc_is_arena_ptr :: proc(k: ^TC, t: Type) -> bool {
    p, is_ptr := unwrap_alias(t).(^Type_Ptr)
    return is_ptr && tc_is_program_arena(k, p.elem)
}

// `with &a {…}` (or `with &a do s`): its block run on another arena — a, of
// the program's kind: what the block, and everything it calls, puts on an
// arena goes on a. The arena it was is back at every way out of the block,
// as a defer's block runs: its callers never see a.
tc_with :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    p := Tree_Id(t.a[s])
    pt := tc_check(k, p)
    span := tree_span(t, p)
    switch {
    case is_any(pt):
    case !k.table.has_scope_allocator:
        tc_error(k, span, TYPE_WITH_NEEDS_ALLOCATOR)
    case tc_is_program_arena(k, pt):
        name := tc_diag_name(k, p)
        tc_error(k, span, TYPE_WITH_NEEDS_ARENA_ADDRESS, name if name != "" else "a")
    case !tc_is_arena_ptr(k, pt):
        tc_error(k, span, TYPE_WITH_NEEDS_ARENA_POINTER, k.table.scope_allocator_name, type_name(pt))
    }
    append(&k.withs, TC_With{span = tree_span(t, s), sid = tc_sid(k, s)})
    tc_scope(k, tree_list(t, t.b[s]))
}

// mara.memory's arena_swap: what `with` sets the arena with, and puts it
// back with (nil: not in the program).
tc_arena_swap :: proc(table: ^SymbolTable) -> ^Type_Scope {
    for _, ft in table.funs {
        if ft != nil && ft.kind == .Fun && ft.home_package == "mara.memory" && (ft.source_name == "arena_swap" || ft.name == "arena_swap") { return ft }
    }
    return nil
}

// A `with` checked: where it is, and its node (in the instance it was
// checked in) — a call of arena_swap's, as the call graph is told.
TC_With :: struct {
    span: Span,
    sid:  Syntax_Id,
}

// Every `with`: mara.memory there, its arena_swap with it — and, to the call
// graph (made from the annotations: callees first), a call of it, the `with`
// its call.
tc_validate_withs :: proc(k: ^TC) {
    if len(k.withs) == 0 { return }
    swap := tc_arena_swap(k.table)
    for w in k.withs {
        if swap == nil {
            tc_error(k, w.span, TYPE_WITH_NEEDS_MEMORY)
            continue
        }
        k.annot.callees[w.sid] = swap
        k.annot.forms[w.sid] = .Fun
    }
}

// The arena's type #allocator names, `*_<name>` among the funs (nil: none
// yet — its module not checked — or no such type).
tc_find_allocator :: proc(k: ^TC) -> ^Type_Scope {
    name := k.table.scope_allocator_name
    if name == "" { return nil }
    suffix := strings.concatenate({"_", name}, context.temp_allocator)
    for fname, ft in k.table.funs {
        if ft == nil || ft.functions == nil { continue }
        if strings.has_suffix(fname, suffix) || fname == name { return ft }
    }
    return nil
}

// mara.memory's Arena_Basic: the shape of an arena (nil: not in the program).
tc_arena_shape :: proc(table: ^SymbolTable) -> ^Type_Scope {
    for _, ft in table.funs {
        if ft != nil && ft.kind == .Struct && ft.home_package == "mara.memory" && (ft.source_name == "Arena_Basic" || ft.name == "Arena_Basic") { return ft }
    }
    return nil
}

// The arena's type: a fun `*_<name>` shaped as Arena_Basic is (`~Arena_Basic`:
// its methods, each with its signature) — and, for the calls the compiler
// makes itself, made with its size alone, its methods with no params past
// Arena_Basic's, its memory in `base`; its size, a constant.
tc_validate_allocator :: proc(k: ^TC) {
    if !k.table.has_scope_allocator { return }
    name := k.table.scope_allocator_name
    if name == "" {
        tc_error(k, {}, TYPE_PROGRAM_GLOBAL_REQUIRES_ALLOCATOR_TYPE)
        k.table.has_scope_allocator = false
        return
    }
    alloc := tc_find_allocator(k)
    if alloc == nil {
        tc_error(k, {}, TYPE_PROGRAM_SCOPE_ALLOCATOR_KNOWN_TYPE, name)
        k.table.has_scope_allocator = false
        return
    }
    span := tree_span(k.t, k.arena_stmt)
    shape := tc_arena_shape(k.table)
    if shape == nil {
        tc_error(k, span, TYPE_ALLOCATOR_NEEDS_MEMORY, name)
        k.table.has_scope_allocator = false
        return
    }
    before := k.c.errors
    check_shape_constraint(k.c, "#allocator", "Arena_Basic", shape, alloc, span)
    if k.c.errors == before {
        for fname, shape_fn in shape.functions {
            if fn := alloc.functions[fname]; len(fn.params) != len(shape_fn.params) {
                tc_error(k, span, TYPE_ALLOCATOR_EXTRA_PARAM, name, fname, len(fn.params), len(shape_fn.params))
            }
        }
        base := struct_field_index(&alloc.sd, "base")
        if base < 0 || !types_equal(alloc.sd.fields[base].type_, shape.sd.fields[struct_field_index(&shape.sd, "base")].type_) {
            tc_error(k, span, TYPE_ALLOCATOR_NEEDS_BASE, name)
        }
        if len(alloc.params) != 1 || !types_equal(alloc.params[0].type_, shape.params[0].type_) {
            tc_error(k, span, TYPE_ALLOCATOR_MADE_WITH_SIZE, name, name)
        }
    }
    if k.c.errors != before {
        k.table.has_scope_allocator = false
        return
    }
    k.table.scope_allocator_type = alloc
    if k.arena_size == 0 { return }
    if n, is_const := tc_comptime_int(k, k.arena_size); is_const {
        k.table.scope_allocator_size = n
    } else {
        tc_error(k, tree_span(k.t, k.arena_size), TYPE_ARENA_SIZE_CONSTANT)
    }
}

// A param's default of `void`: an error but a pointer's (its null), nothing
// checks a param's reads (the flow pass's other void stores, through the
// graph, skip these).
tc_void_defaults :: proc(k: ^TC, checked: ^Checked_Program, fns: []^Type_Scope) -> map[Span]bool {
    seen: map[Span]bool   // (a generic's instances share their template's nodes)
    for ft in fns {
        if ft == nil { continue }
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        for p in ft.params {
            if p.default_node == 0 || !tc_is_void(k, p.default_node) { continue }
            void_error(k.c, &seen, tree_span(k.t, p.default_node), p.type_, fmt.tprintf("the default of parameter '%s'", p.name))
        }
    }
    return seen
}
