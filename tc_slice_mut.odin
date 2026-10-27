package mara

import "core:slice"

// A slice keeps its mutability through copies. An immutable param's slice
// (`s: []T`, or one reached from an immutable param through no pointer) is
// immutable, and so is every copy of it: a local, a field, a loop's item,
// what a fun gives back. Nothing is written through an immutable slice: no
// append, no item, no len. (Through the param itself that's said where it's
// written: tc_write_root_param.)
//
// The checker notes, as it goes, what's put in each variable and field and
// what each fun gives back, and each write through a slice. Once every body
// is checked (a field filled in one fun is written in another), the copies of
// immutable params are found and the writes through them said.

// Where a value comes from: an immutable param (origin), the variables and
// fields it's a copy of (deps), the funs whose results it is (funs).
Mut_Source :: struct {
    origin: Token_Id,
    deps:   [dynamic]Token_Id,
    funs:   [dynamic]^Type_Scope,
}

// A write through a slice: the slice, and the variables and fields it's
// reached through (up to a pointer).
Mut_Write :: struct {
    span:  Span,
    slice: Tree_Id,
    locs:  []Token_Id,
}

Slice_Mut :: struct {
    stores:  map[Token_Id][dynamic]Mut_Source,      // a variable's, a field's: what's put in it
    returns: map[^Type_Scope][dynamic]Mut_Source,   // a fun's: what it gives back
    writes:  [dynamic]Mut_Write,
}

// Where value comes from.
tc_mut_source :: proc(k: ^TC, value: Tree_Id) -> (src: Mut_Source) {
    tr := k.t
    cur := value
    for cur != 0 {
        #partial switch tr.tag[cur] {
        case .Paren:
            cur = Tree_Id(tr.a[cur])
        case .Field, .Index, .Slice:
            if tr.tag[cur] == .Field {
                if r := tc_ref(k, cur); r.kind == .Field && r.decl != 0 { append(&src.deps, r.decl) }
            }
            base := Tree_Id(tr.a[cur])
            if tc_is_pointer(tc_node_type(k, base)) { return }   // (a mutable one's)
            cur = base
        case .Ident:
            ref := k.rs.refs[cur]
            #partial switch ref.kind {
            case .Param:
                if pt, ok := tc_bound(k, ref.decl); ok && is_immutable_param_type(pt) { src.origin = ref.decl }
            case .Local, .Result, .Field, .Global:
                if ref.decl != 0 { append(&src.deps, ref.decl) }
            }
            return
        case .Call, .Method_Call:
            if callee := tc_callee(k, cur); callee != nil && callee.kind == .Fun { append(&src.funs, callee) }
            return
        case:
            return
        }
    }
    return
}

// Whether a value of type t holds a slice: is one, or has one among its
// elements, fields, variants (not through a pointer: that's a mutable one).
type_holds_slice :: proc(t: Type, depth := 0) -> bool {
    if depth > 8 { return false }
    bt := distinct_base(t)
    #partial switch v in bt {
    case ^Type_Slice:         return true
    case ^Type_Fixed_Array:   return type_holds_slice(v.elem, depth + 1)
    case ^Type_Partial_Array: return type_holds_slice(v.elem, depth + 1)
    case ^Type_Union:
        for _, vs in v.variant_structs {
            if sd := as_scope_body(vs); sd != nil {
                for f in sd.fields { if type_holds_slice(f.type_, depth + 1) { return true } }
            }
        }
        return false
    }
    if sd := as_scope_body(bt); sd != nil {
        for f in sd.fields { if type_holds_slice(f.type_, depth + 1) { return true } }
    }
    return false
}

// value, of type t, put in the variable or field dest declares. (A value
// that holds no slice, a number copied, carries no mutability.)
tc_mut_store :: proc(k: ^TC, dest: Token_Id, value: Tree_Id, t: Type = nil) {
    if dest == 0 || value == 0 { return }
    if !type_holds_slice(t if t != nil else tc_node_type(k, value)) { return }
    src := tc_mut_source(k, value)
    if src.origin == 0 && len(src.deps) == 0 && len(src.funs) == 0 { return }
    if dest not_in k.mut.stores { k.mut.stores[dest] = {} }
    append(&k.mut.stores[dest], src)
}

// value put in a place, `x.f = v`, `a[i] = v`: in each variable and field
// it's reached through (up to a pointer).
tc_mut_store_place :: proc(k: ^TC, target, value: Tree_Id) {
    for d in tc_mut_places(k, target) { tc_mut_store(k, d, value) }
}

// value given back by the fun being checked.
tc_mut_return :: proc(k: ^TC, value: Tree_Id) {
    if k.body == nil || value == 0 { return }
    if !type_holds_slice(tc_node_type(k, value)) { return }
    src := tc_mut_source(k, value)
    if src.origin == 0 && len(src.deps) == 0 && len(src.funs) == 0 { return }
    if k.body not_in k.mut.returns { k.mut.returns[k.body] = {} }
    append(&k.mut.returns[k.body], src)
}

// The variables and fields a place is reached through, nearest first, up
// to a pointer.
tc_mut_places :: proc(k: ^TC, n: Tree_Id) -> []Token_Id {
    tr := k.t
    locs := make([dynamic]Token_Id)
    cur := tc_unparen(k, n)
    loop: for cur != 0 {
        #partial switch tr.tag[cur] {
        case .Field, .Index, .Slice:
            if tr.tag[cur] == .Field {
                if r := tc_ref(k, cur); r.kind == .Field && r.decl != 0 { append(&locs, r.decl) }
            }
            base := Tree_Id(tr.a[cur])
            if tc_is_pointer(tc_node_type(k, base)) { break loop }
            cur = tc_unparen(k, base)
        case .Ident:
            ref := k.rs.refs[cur]
            #partial switch ref.kind {
            case .Local, .Result, .Field, .Global:
                if ref.decl != 0 { append(&locs, ref.decl) }
            }
            break loop
        case:
            break loop
        }
    }
    return locs[:]
}

// A write into n: through the slice nearest it (of n itself — an address
// taken, `&s` — or, from_base, of what n is part of: `s[i]`, `s.len`), if
// one comes before a pointer.
tc_note_slice_write :: proc(k: ^TC, n: Tree_Id, from_base: bool) {
    tr := k.t
    cur := tc_unparen(k, n)
    if from_base {
        #partial switch tr.tag[cur] {
        case .Field, .Index, .Slice: cur = tc_unparen(k, Tree_Id(tr.a[cur]))
        case: return
        }
    }
    for {
        if _, is_slice := distinct_base(tc_node_type(k, cur)).(^Type_Slice); is_slice { break }
        #partial switch tr.tag[cur] {
        case .Field, .Index, .Slice:
            base := Tree_Id(tr.a[cur])
            if tc_is_pointer(tc_node_type(k, base)) { return }
            cur = tc_unparen(k, base)
        case:
            return
        }
    }
    locs := tc_mut_places(k, cur)
    if len(locs) == 0 { return }
    append(&k.mut.writes, Mut_Write{span = tree_span(tr, n), slice = cur, locs = locs})
}

// Each write through a copy of an immutable param's slice, said — once
// every body is checked.
tc_slice_mut_check :: proc(k: ^TC) {
    m := &k.mut
    if len(m.writes) == 0 { return }
    // (A variable or field, a fun: the immutable param it's a copy of.)
    ro := make(map[Token_Id]Token_Id, context.temp_allocator)
    fun_ro := make(map[^Type_Scope]Token_Id, context.temp_allocator)
    from :: proc(src: Mut_Source, ro: ^map[Token_Id]Token_Id, fun_ro: ^map[^Type_Scope]Token_Id) -> Token_Id {
        if src.origin != 0 { return src.origin }
        for d in src.deps { if o, ok := ro[d]; ok { return o } }
        for f in src.funs { if o, ok := fun_ro[f]; ok { return o } }
        return 0
    }
    // (In source order, so the param named is the same each build.)
    dests := make([dynamic]Token_Id, context.temp_allocator)
    for d in m.stores { append(&dests, d) }
    slice.sort(dests[:])
    funs := make([dynamic]^Type_Scope, context.temp_allocator)
    for f in m.returns { append(&funs, f) }
    slice.sort_by(funs[:], proc(a, b: ^Type_Scope) -> bool { return a.decl < b.decl })
    for changed := true; changed; {
        changed = false
        for d in dests {
            if d in ro { continue }
            for s in m.stores[d] {
                if o := from(s, &ro, &fun_ro); o != 0 { ro[d] = o; changed = true; break }
            }
        }
        for f in funs {
            if f in fun_ro { continue }
            for s in m.returns[f] {
                if o := from(s, &ro, &fun_ro); o != 0 { fun_ro[f] = o; changed = true; break }
            }
        }
    }
    said := make(map[Span]bool, context.temp_allocator)   // (an instance's write, said once)
    for w in m.writes {
        for d in w.locs {
            o, is_ro := ro[d]
            if !is_ro { continue }
            if w.span not_in said {
                said[w.span] = true
                at := Span{at = o, tok = o, end = o + 1}
                tc_error(k, w.span, TYPE_SLICE_COPY_IMMUTABLE, tc_written(k, w.slice), tc_text(o), span_location(at), tc_text(o))
            }
            break
        }
    }
}
