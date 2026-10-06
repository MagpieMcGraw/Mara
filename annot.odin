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
// its tag, where it is written, its type.
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
            ty := annot_type(a, Instance_Id(i), n)
            if ty == nil { continue }
            sp := tree_span(t, n)
            where_ := "-"
            if span_file(sp) != "" { where_ = fmt.tprintf("%s:%d:%d", filepath.base(span_file(sp)), span_line(sp), span_col(sp)) }
            fmt.sbprintf(&sb, "  %d %v %s t=%s\n", n, t.tag[n], where_, type_name(ty))
        }
    }
    fmt.print(strings.to_string(sb))
}
