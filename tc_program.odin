package mara

import "core:fmt"
import "core:strings"

// The program's arena: `this_program = Program(Arena_Debug(16 * MB))`, in
// main or a main of a module it uses. Found before anything is checked —
// what is too big for the stack goes on it — its arguments checked where it
// is written (nothing built: main's entry makes the program's storage), its
// type checked for what an arena has once every module is.

// The arena named by any main the program reaches (in a shared build, any
// fun): its name, and its size's node.
tc_scan_allocator :: proc(k: ^TC) {
    t := k.t
    seen := make(map[string]bool, context.temp_allocator)
    queue := make([dynamic]string, context.temp_allocator)
    seen[k.main_package] = true
    append(&queue, k.main_package)
    for i := 0; i < len(queue); i += 1 {
        for file in k.modules[queue[i]] or_else nil {
            for s in tc_live(k, tree_list(t, t.a[file])) {
                imp: Tree_Id
                #partial switch t.tag[s] {
                case .Expr_Stmt: imp = Tree_Id(t.a[s])
                case .Define:    imp = Tree_Id(t.b[s])
                }
                if imp == 0 || t.tag[imp] != .Import { continue }
                if path := tc_path(k, imp); !seen[path] {
                    seen[path] = true
                    append(&queue, path)
                }
            }
        }
    }
    for pkg in queue {
        for file in k.modules[pkg] or_else nil {
            for s in tc_live(k, tree_list(t, t.a[file])) {
                value := Tree_Id(t.b[s])
                if t.tag[s] != .Define || value == 0 || t.tag[value] != .Fun_Def { continue }
                if tc_name(k, s) != "main" && !k.shared { continue }
                for bs in tc_live(k, scope_view(t, value).body) { tc_scan_program_assign(k, bs) }
            }
        }
    }
}

// `this_program = Program(Arena(size))`, or `Program(Arena)` — the type
// alone. (`Program()`: no arena.)
tc_scan_program_assign :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    if t.tag[s] != .Assign { return }
    targets, values := tree_list(t, t.a[s]), tree_list(t, t.b[s])
    if len(targets) != 1 || len(values) != 1 { return }
    if t.tag[targets[0]] != .Ident || tc_name(k, targets[0]) != "this_program" { return }
    args, ok := tc_program_args(k, values[0])
    if !ok || len(args) == 0 { return }
    k.table.has_scope_allocator = true
    #partial switch arena := tc_unparen(k, args[0]); t.tag[arena] {
    case .Call:
        k.table.scope_allocator_name = tc_name(k, arena)
        inner := tree_list(t, t.a[arena])
        k.arena_size = inner[0] if len(inner) > 0 else 0
    case .Ident:
        k.table.scope_allocator_name = tc_name(k, arena)
    }
}

// Whether a place is in `this_program`'s storage — its arena, its args (each
// arg's slot, not the text it views) — which is read only: written there,
// pointed at or sliced, it could be changed. The place's name, before any
// pointer or slice it goes through (past one, it's what that views).
tc_in_program :: proc(k: ^TC, n: Tree_Id) -> bool {
    tr := k.t
    cur := n
    for {
        #partial switch tr.tag[cur] {
        case .Paren:
            cur = Tree_Id(tr.a[cur])
            continue
        case .Field, .Index, .Slice:
            inner := Tree_Id(tr.a[cur])
            #partial switch _ in distinct_base(tc_node_type(k, inner)) {
            case ^Type_Ptr, ^Type_Slice: return false
            }
            cur = inner
        case .Ident:
            return tc_name(k, cur) == "this_program" && tc_ref(k, cur).kind == .Builtin
        case:
            return false
        }
    }
}

// `this_program = Program(…)` where it's set: a statement of main's body (a
// shared build's, any fun's) — where tc_scan_allocator finds it.
tc_program_set_here :: proc(k: ^TC, s: Tree_Id) -> bool {
    f := k.body
    if f == nil || f.kind != .Fun || f.node == 0 || (scope_display_name(f) != "main" && !k.shared) { return false }
    for bs in scope_view(k.t, f.node).body { if bs == s { return true } }
    return false
}

// `Program(args)`'s arguments.
tc_program_args :: proc(k: ^TC, value: Tree_Id) -> ([]Tree_Id, bool) {
    call := tc_unparen(k, value)
    if k.t.tag[call] != .Call || tc_name(k, call) != "Program" { return nil, false }
    return tree_list(k.t, k.t.a[call]), true
}

// `this_program = Program(...)`, checked: its arena's arguments — read at
// main's entry, before any code runs.
tc_program_assign :: proc(k: ^TC, value: Tree_Id) {
    t := k.t
    args, ok := tc_program_args(k, value)
    if !ok || len(args) == 0 { return }
    arena := tc_unparen(k, args[0])
    if t.tag[arena] != .Call { return }
    inner := tree_list(t, t.a[arena])
    for a in inner { tc_check(k, a) }
}

// `Program(Arena_Basic(size))` as a value (not main's `this_program =
// Program(…)`): another program, its own arena, the program's kind — a
// block run on it with `with &p {…}`. Its size needn't be a constant: it's
// built when this runs.
tc_program_value :: proc(k: ^TC, n: Tree_Id, args: []Tree_Id) -> Type {
    span := tree_span(k.t, n)
    pt := k.table.builtins["Program"]
    if len(args) != 1 {
        tc_error(k, span, TYPE_PROGRAM_VALUE_ONE_ARENA, len(args))
        for a in args { tc_check(k, a) }
        return pt
    }
    at := tc_check(k, args[0])
    if !k.table.has_scope_allocator {
        tc_error(k, span, TYPE_PROGRAM_VALUE_NEEDS_ARENA)
        return pt
    }
    if is_any(at) { return pt }
    name := k.table.scope_allocator_name
    ats, is_scope := at.(^Type_Scope)
    if !is_scope || !(ats.name == name || strings.has_suffix(ats.name, strings.concatenate({"_", name}, context.temp_allocator))) {
        tc_error(k, span, TYPE_PROGRAM_VALUE_ARENA_KIND, name, type_name(at))
    }
    return pt
}

// Whether t is ^Program.
tc_is_program_ptr :: proc(k: ^TC, t: Type) -> bool {
    p, is_ptr := unwrap_alias(t).(^Type_Ptr)
    if !is_ptr { return false }
    ps, is_scope := p.elem.(^Type_Scope)
    return is_scope && ps == (k.table.builtins["Program"].(^Type_Scope) or_else nil)
}

// `with p {…}` (or `with p do s`): its block run on another program — p a
// ^Program; what the block, and everything it calls, puts on an arena goes
// on p's, and this_program is p there. The program it was is back at every
// way out of the block, as a defer's block runs: its callers never see p.
tc_with :: proc(k: ^TC, s: Tree_Id) {
    t := k.t
    p := Tree_Id(t.a[s])
    pt := tc_check(k, p)
    if ps, is_scope := pt.(^Type_Scope); is_scope && ps == (k.table.builtins["Program"].(^Type_Scope) or_else nil) {
        name := tc_diag_name(k, p)
        tc_error(k, tree_span(t, p), TYPE_WITH_NEEDS_PROGRAM_ADDRESS, name if name != "" else "p")
    } else if !is_any(pt) && !tc_is_program_ptr(k, pt) {
        tc_error(k, tree_span(t, p), TYPE_WITH_NEEDS_PROGRAM_POINTER, type_name(pt))
    }
    append(&k.withs, TC_With{span = tree_span(t, s), sid = tc_sid(k, s)})
    tc_scope(k, tree_list(t, t.b[s]))
}

// mara.memory's program_swap: what `with` sets the program with, and puts it
// back with (nil: not in the program).
tc_program_swap :: proc(table: ^SymbolTable) -> ^Type_Scope {
    for _, ft in table.funs {
        if ft != nil && ft.kind == .Fun && ft.home_package == "mara.memory" && (ft.source_name == "program_swap" || ft.name == "program_swap") { return ft }
    }
    return nil
}

// A `with` checked: where it is, and its node (in the instance it was
// checked in) — a call of program_swap's, as the call graph is told.
TC_With :: struct {
    span: Span,
    sid:  Syntax_Id,
}

// Every `with`: mara.memory there, its program_swap with it — and, to the
// call graph (made from the annotations: callees first), a call of it, the
// `with` its call.
tc_validate_withs :: proc(k: ^TC) {
    if len(k.withs) == 0 { return }
    swap := tc_program_swap(k.table)
    for w in k.withs {
        if swap == nil {
            tc_error(k, w.span, TYPE_WITH_NEEDS_MEMORY)
            continue
        }
        k.annot.callees[w.sid] = swap
        k.annot.forms[w.sid] = .Fun
    }
}

// The arena's type main names, `*_<name>` among the funs (nil: none yet —
// its module not checked, or no such type).
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

// The program's struct's arena field typed as soon as the arena's type is
// known (tc_validate_allocator, at the end, at the latest): a read through
// it — `this_program.scope_allocator.base.len`, a Program value's — is of a
// type, then, not a placeholder.
tc_program_arena_typed :: proc(k: ^TC) {
    prog, ok := k.table.builtins["Program"].(^Type_Scope)
    if !ok || len(prog.fields) == 0 || prog.fields[0].name != "scope_allocator" { return }
    if _, placeholder := prog.fields[0].type_.(Type_Any); !placeholder { return }
    if alloc := tc_find_allocator(k); alloc != nil { prog.fields[0].type_ = alloc }
}

// The arena's type: a fun `*_<name>` with what an arena has (mark, alloc,
// reset); its size, a constant.
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
    for req in ([]string{"mark", "alloc", "reset"}) {
        if req not_in alloc.functions {
            tc_error(k, {}, TYPE_PROGRAM_SCOPE_ALLOCATOR_MISSING_REQUIRED, name, req)
            k.table.has_scope_allocator = false
            return
        }
    }
    k.table.scope_allocator_type = alloc
    // (The program's struct holds it: its field, a placeholder until now.)
    if prog, ok := k.table.builtins["Program"].(^Type_Scope); ok && len(prog.fields) > 0 && prog.fields[0].name == "scope_allocator" {
        prog.fields[0].type_ = alloc
    }
    if k.arena_size == 0 { return }
    if n, is_const := tc_comptime_int(k, k.arena_size); is_const {
        k.table.scope_allocator_size = n
    } else {
        tc_error(k, tree_span(k.t, k.arena_size), TYPE_ARENA_SIZE_CONSTANT)
    }
}

// A param's default of `void` where the param is a pointer: an error (the
// flow pass's other void stores, through the graph, skip these).
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
