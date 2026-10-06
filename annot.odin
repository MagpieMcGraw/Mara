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

Annotations :: struct {
    instances: [dynamic]Instance,
    types:     [dynamic][]Type,   // each instance's nodes' types, by n - lo

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
    return a
}

// A generic's instance, its template's nodes [lo, hi]: its number.
annot_instance :: proc(a: ^Annotations, lo, hi: Tree_Id, scope: ^Type_Scope) -> Instance_Id {
    append(&a.instances, Instance{lo = lo, hi = hi, scope = scope})
    append(&a.types, make([]Type, int(hi - lo) + 1))
    return Instance_Id(len(a.instances) - 1)
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
