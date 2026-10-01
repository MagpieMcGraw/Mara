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

// `Program(args)`'s arguments.
tc_program_args :: proc(k: ^TC, value: Tree_Id) -> ([]Tree_Id, bool) {
    call := tc_unparen(k, value)
    if k.t.tag[call] != .Call || tc_name(k, call) != "Program" { return nil, false }
    return tree_list(k.t, k.t.a[call]), true
}

// `this_program = Program(...)`, checked: its arena's arguments — read at
// main's entry, before any code runs.
tc_program_assign :: proc(k: ^TC, value: Tree_Id, env: ^Type_Scope) {
    t := k.t
    args, ok := tc_program_args(k, value)
    if !ok || len(args) == 0 { return }
    arena := tc_unparen(k, args[0])
    if t.tag[arena] != .Call { return }
    inner := tree_list(t, t.a[arena])
    for a in inner { tc_check(k, a, env) }
    if len(inner) > 0 && inner[0] == k.arena_size { k.arena_env = env }
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
    suffix := strings.concatenate({"_", name}, context.temp_allocator)
    alloc: ^Type_Scope
    for fname, ft in k.table.funs {
        if ft.functions == nil { continue }
        if strings.has_suffix(fname, suffix) || fname == name {
            alloc = ft
            break
        }
    }
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
    if prog, ok := k.table.funs["Program"]; ok && len(prog.fields) > 0 && prog.fields[0].name == "scope_allocator" {
        prog.fields[0].type_ = alloc
    }
    if k.arena_size == 0 { return }
    env := k.arena_env if k.arena_env != nil else k.root
    if n, is_const := tc_comptime_int(k, k.arena_size, env); is_const {
        k.table.scope_allocator_size = n
    } else {
        tc_error(k, tree_span(k.t, k.arena_size), TYPE_ARENA_SIZE_CONSTANT)
    }
}

// A param's default of `void` where the param is a pointer: an error (the
// flow pass's other void stores, through the graph, skip these).
tc_void_defaults :: proc(k: ^TC, checked: ^Checked_Program) -> map[Span]bool {
    seen: map[Span]bool   // (a generic's instances share their template's nodes)
    for ft in flow_functions(checked) {
        if ft == nil { continue }
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        for p in ft.params {
            if p.default_node == 0 || !tc_is_void(k, p.default_node) { continue }
            void_error(k.c, &seen, tree_span(k.t, p.default_node), p.type_, fmt.tprintf("the default of parameter '%s'", p.name))
        }
    }
    return seen
}
