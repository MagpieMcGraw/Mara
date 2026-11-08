package mara

import "core:fmt"
import "core:slice"

// ---------------------------------------------------------------------------
// Field references: a field of a struct's type held as a value. `f :=
// Event_State.mouse.xrel` is one, and `events[f]` is that field of events,
// read, written or compared like any other. Its type is the struct's and the
// field's, written `Event_State.f32` (^Type_Field); its value is the field's
// offset in bytes.
//
// A path goes through the struct's own fields, fixed arrays and lists, by any
// index, known or not: a list's within its cap, as indexing it is. Never
// through a pointer or a slice: what they hold isn't in the struct.
//
// Its value counts from the first field of its type the struct holds (its
// type's base, field_ref_base): 0 is that field, so a reference never set —
// declared with no value, made `{all 0}`, from_text's miss — is always a
// field, as an enum's zero is its `= 0` variant. A type whose struct holds no
// field of it, or a field of no size, is an error (tc_validate_field_refs).
//
// f.text() names the field, `keyboard.held[W]`, and `R.from_text(text)`, R an
// alias of the reference's type, finds it again. Both know every field of that
// type the struct holds, by its path (field_ref_paths): through a `using`
// field by the name without it too, `hp` for `base.hp`, and an enum-indexed
// array's item by each variant of its value, the first declared printed.
// ---------------------------------------------------------------------------

// The most fields of one type a struct can have named.
FIELD_REF_NAMES_MOST :: 4096

Field_Path :: struct {
    text:   string,
    value:  int,    // the reference's value: its offset less its type's base
    offset: int,    // (its offset in the struct)
    short:  bool,   // (a name through a using field, without it)
}

// The struct a type is, by value; nil for anything else.
field_ref_struct :: proc(t: Type) -> ^Scope_Body {
    ts, is_scope := distinct_base(t).(^Type_Scope)
    if !is_scope || ts.kind != .Struct || ts.is_module { return nil }
    return &ts.sd
}

// A struct's i-th field's offset in bytes.
struct_field_offset :: proc(sd: ^Scope_Body, i: int) -> int {
    l := Layout{0, 1}
    for f, k in sd.fields {
        at := layout_field(&l, type_layout(f.type_), sd.is_packed)
        if k == i { return at }
    }
    return 0
}

// A struct's field by name, through a `using` field too: its type, its offset
// and its declaration; ok false for none.
struct_field_at :: proc(sd: ^Scope_Body, name: string) -> (t: Type, offset: int, decl: Token_Id, ok: bool) {
    if i, has := sd.field_map[name]; has {
        return sd.fields[i].type_, struct_field_offset(sd, i), sd.fields[i].decl, true
    }
    path, through := struct_using_path(sd, name)
    if !through { return }
    at := sd
    for step in path {
        i, has := at.field_map[step.name]
        if !has { return }
        offset += struct_field_offset(at, i)
        at = field_ref_struct(step.type_)
        if at == nil { return }
    }
    i, has := at.field_map[name]
    if !has { return }
    return at.fields[i].type_, offset + struct_field_offset(at, i), at.fields[i].decl, true
}

// The items a path can go into: a fixed array's, or a list's (after its len),
// within the cap. at is where the first is from the array's start; index_type
// an enum-indexed array's enum. ok false for anything else.
Field_Ref_Items :: struct {
    elem:       Type,
    count:      int,
    at:         int,
    index_type: Type,
}
field_ref_items :: proc(t: Type) -> (items: Field_Ref_Items, ok: bool) {
    #partial switch v in distinct_base(t) {
    case ^Type_Fixed_Array:
        return {v.elem, v.size, 0, v.index_type}, true
    case ^Type_Partial_Array:
        l := Layout{0, 1}
        layout_field(&l, {8, 8})
        at := layout_field(&l, type_layout(v.elem))
        return {v.elem, v.size, at, nil}, true
    }
    return
}

// Whether a value of t holds a value of elem somewhere a path reaches.
@(private="file")
field_ref_holds :: proc(t, elem: Type) -> bool {
    if types_equal(t, elem) { return true }
    if sd := field_ref_struct(t); sd != nil {
        for f in sd.fields {
            if field_ref_holds(f.type_, elem) { return true }
        }
        return false
    }
    if items, has := field_ref_items(t); has { return field_ref_holds(items.elem, elem) }
    return false
}

// Every field of type elem that owner holds, by its path and value, in the
// order the struct lists them; false when there are more than most. An array
// indexed by an enum names its items by its variants, in the order they're
// declared (the first of a value printed). A field through a using field has
// its name without it first, when no other path is named that.
field_ref_paths :: proc(owner, elem: Type, most := FIELD_REF_NAMES_MOST) -> ([]Field_Path, bool) {
    out := make([dynamic]Field_Path, context.temp_allocator)
    walk :: proc(out: ^[dynamic]Field_Path, t, elem: Type, full, short: string, at, most: int) -> bool {
        if full != "" && types_equal(t, elem) {
            if len(out) >= most { return false }
            if short != full { append(out, Field_Path{text = short, offset = at, short = true}) }
            append(out, Field_Path{text = full, offset = at})
        }
        if !field_ref_holds(t, elem) { return true }
        join :: proc(prefix, name: string) -> string { return name if prefix == "" else fmt.tprintf("%s.%s", prefix, name) }
        if sd := field_ref_struct(t); sd != nil {
            for f, i in sd.fields {
                if f.decl == 0 { continue }   // (a union variant's tag: no field written)
                // (A using field's own fields are the struct's: named without it too.)
                inner_short := join(short, f.name)
                if f.is_using && !types_equal(f.type_, elem) { inner_short = short }
                walk(out, f.type_, elem, join(full, f.name), inner_short, at + struct_field_offset(sd, i), most) or_return
            }
            return true
        }
        fa, is_array := field_ref_items(t)
        if !is_array { return true }
        size := type_size(fa.elem)
        at := at + fa.at
        if et, by_enum := distinct_base(fa.index_type).(^Type_Enum); by_enum && fa.index_type != nil {
            Variant :: struct { name: string, value: int, decl: Token_Id }
            variants := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
            for name, value in et.variants { append(&variants, Variant{name, value, et.variant_decls[name]}) }
            slice.sort_by(variants[:], proc(a, b: Variant) -> bool {
                if a.value != b.value { return a.value < b.value }
                if a.decl != b.decl { return a.decl < b.decl }
                return a.name < b.name
            })
            for v in variants {
                if v.value < 0 || v.value >= fa.count { continue }
                walk(out, fa.elem, elem, fmt.tprintf("%s[%s]", full, v.name), fmt.tprintf("%s[%s]", short, v.name), at + v.value * size, most) or_return
            }
            return true
        }
        for i in 0 ..< fa.count {
            walk(out, fa.elem, elem, fmt.tprintf("%s[%d]", full, i), fmt.tprintf("%s[%d]", short, i), at + i * size, most) or_return
        }
        return true
    }
    ok := walk(&out, owner, elem, "", "", 0, most)
    if len(out) == 0 { return out[:], ok }
    base := out[0].offset
    // (A short name another path has too names neither: dropped.)
    kept := make([dynamic]Field_Path, 0, len(out), context.temp_allocator)
    for p, i in out {
        p := p
        p.value = p.offset - base
        if p.short {
            taken := false
            for q, j in out { if j != i && q.text == p.text && q.offset != p.offset { taken = true; break } }
            if taken { continue }
        }
        append(&kept, p)
    }
    return kept[:], ok
}

// Where a reference type's values count from: the offset of the first field
// of the type its struct holds; 0 for none (an error, tc_validate_field_refs).
field_ref_base :: proc(owner, elem: Type) -> int {
    paths, _ := field_ref_paths(owner, elem, 1)
    return paths[0].offset if len(paths) > 0 else 0
}

// --- checking ---------------------------------------------------------------

// Whether n names a struct's type, `Event_State` or `m.Event_State`: a field
// after it is a field reference.
tc_names_struct :: proc(k: ^TC, n: Tree_Id, t: Type) -> bool {
    if k.t.tag[n] != .Ident && k.t.tag[n] != .Field { return false }
    return tc_ref(k, n).kind == .Type && field_ref_struct(t) != nil
}

// `S.field`, or `r.field` for r a reference to a struct `at`: a reference to
// that field of S, or of r's struct.
tc_field_ref :: proc(k: ^TC, n: Tree_Id, owner, at: Type, field: string, span: Span) -> Type {
    sd := field_ref_struct(at)
    if sd == nil {
        tc_error(k, span, TYPE_FIELD_REF_THROUGH, type_name(at), tc_written(k, n))
        return Type_Error{}
    }
    t, _, decl, has := struct_field_at(sd, field)
    if !has {
        tc_error(k, span, TYPE_CLASS_FIELD, scope_display_name(sd), field)
        return Type_Error{}
    }
    tc_set_ref(k, n, {decl, .Field})
    append(&k.field_ref_types, Field_Ref_Use{owner, t, span})
    return type_field(owner, t)
}

// `r[i]`, r a reference to a fixed array or a list: a reference to its i-th
// item, i a number or the array's enum, checked as an array's index is.
tc_field_ref_index :: proc(k: ^TC, n, idx_n: Tree_Id, fr: ^Type_Field, span: Span) -> Type {
    fa, is_array := field_ref_items(fr.elem)
    if !is_array {
        tc_check(k, idx_n)
        tc_error(k, span, TYPE_FIELD_REF_THROUGH, type_name(fr.elem), tc_written(k, n))
        return Type_Error{}
    }
    if fa.index_type != nil { k.hint = fa.index_type }
    it := tc_check_at(k, idx_n, slice_header_width_type)
    if !is_numeric(it) {
        tc_error(k, span, TYPE_INDEX_NUMBER, type_name(it))
    } else if !coerces_to_index_width(it) {
        tc_error(k, span, TYPE_INDEX_WIDTH, type_name(slice_header_width_type), type_name(it))
    }
    if at, known := tc_comptime_int(k, idx_n); known && (at < 0 || at >= i64(fa.count)) {
        tc_error(k, span, TYPE_INDEX_OUT_OF_BOUNDS_CONST, at, fa.count, fa.count - 1)
    }
    append(&k.field_ref_types, Field_Ref_Use{fr.owner, fa.elem, span})
    return type_field(fr.owner, fa.elem)
}

// `s[f]`, s a struct (or a pointer to one) and f a reference to one of its
// fields: that field.
tc_index_by_field :: proc(k: ^TC, idx_n: Tree_Id, st: Type, span: Span) -> Type {
    it := tc_check(k, idx_n)
    fr, is_ref := distinct_base(it).(^Type_Field)
    if !is_ref {
        if !is_any(it) { tc_error(k, span, TYPE_CANNOT_INDEX_INTO, type_name(st)) }
        return Type_Error{}
    }
    if !types_equal(fr.owner, st) {
        tc_error(k, span, TYPE_FIELD_REF_OWNER, type_name(it), type_name(fr.owner), type_name(st))
        return Type_Error{}
    }
    return fr.elem
}

// A field reference's type, spelled or made, where: checked once every
// struct's fields are known (a struct can hold a reference to itself).
Field_Ref_Use :: struct {
    owner, elem: Type,
    span:        Span,
}

// Each reference type the program has: its struct holds a field of its type
// — its zero is the first (field_ref_base) — and one of some size, else
// every such field is at one place, none told apart.
tc_validate_field_refs :: proc(k: ^TC) {
    done := make([dynamic]Field_Ref_Use, context.temp_allocator)
    each: for u in k.field_ref_types {
        for d in done { if types_equal(d.owner, u.owner) && types_equal(d.elem, u.elem) { continue each } }
        append(&done, u)
        tc_ensure_layout(k, u.owner)
        tc_ensure_layout(k, u.elem)
        if type_size(u.elem) == 0 {
            tc_error(k, u.span, TYPE_FIELD_REF_NO_SIZE, type_name(u.elem))
        } else if paths, _ := field_ref_paths(u.owner, u.elem, 1); len(paths) == 0 {
            tc_error(k, u.span, TYPE_FIELD_REF_NO_FIELD, type_name(u.owner), type_name(u.elem), type_name(type_field(u.owner, u.elem)))
        }
    }
}

// The struct a base indexed by a field reference is: itself, or what it
// points at; nil when it's no struct.
index_struct :: proc(bt: Type) -> Type {
    t := bt
    if pt, is_ptr := distinct_base(t).(^Type_Ptr); is_ptr { t = pt.elem }
    if field_ref_struct(t) == nil { return nil }
    return t
}

// The names a reference of this type can have, as atoms, made now in a fixed
// order (the same ids each build); false when there are too many, said.
tc_field_atoms :: proc(k: ^TC, qt: Type, fr: ^Type_Field, span: Span) -> bool {
    paths, ok := field_ref_paths(fr.owner, fr.elem)
    if !ok {
        tc_error(k, span, TYPE_FIELD_REF_TOO_MANY, type_name(fr.owner), type_name(fr.elem), FIELD_REF_NAMES_MOST)
        return false
    }
    checked_atom(k.checked, "?")
    for p in paths { checked_atom(k.checked, p.text) }
    return true
}

// `r.text()`: its fun, made at each call, its body generated where it's
// called (Origin_Field_Text): the field's path as an atom, "?" for an offset
// no field of its type has.
field_text_fun :: proc(qt: Type, fr: ^Type_Field) -> ^Type_Scope {
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.name = fmt.aprintf("%s.text", type_name(qt))
    ft.source_name = "text"
    append(&ft.params, Struct_Type_Field{name = "value", type_ = qt})
    append(&ft.return_types, Type_Atom{})
    ft.origin = Origin_Field_Text{field = fr}
    return ft
}

// `R.from_text(text)`, R a reference's type: its fun, made at each call, its
// body generated where it's called (Origin_Field_From_Text): the reference
// whose path text is, and true; none, 0 and false.
field_from_text_fun :: proc(qt: Type, fr: ^Type_Field) -> ^Type_Scope {
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.name = fmt.aprintf("%s.from_text", type_name(qt))
    ft.source_name = "from_text"
    append(&ft.params, Struct_Type_Field{name = "text", type_ = type_slice(Type_Utf8{})})
    append(&ft.return_types, qt)
    append(&ft.return_types, Type_Bool{})
    ft.origin = Origin_Field_From_Text{field = fr}
    return ft
}

// --- lowering ---------------------------------------------------------------

// Whether n makes a field reference, `S.field`, `r.field`, `r[i]` — not a
// read of one held in a variable or a field.
lw_makes_field_ref :: proc(k: ^TC, n: Tree_Id) -> bool {
    t := k.t
    if _, is_ref := distinct_base(tc_node_type(k, n)).(^Type_Field); !is_ref { return false }
    #partial switch t.tag[n] {
    case .Field:
        base := Tree_Id(t.a[n])
        if _, from_ref := distinct_base(tc_node_type(k, base)).(^Type_Field); from_ref { return true }
        return tc_ref(k, base).kind == .Type
    case .Index:
        _, from_ref := distinct_base(tc_node_type(k, Tree_Id(t.a[n]))).(^Type_Field)
        return from_ref
    }
    return false
}

@(private="file")
lw_number :: proc(b: ^Graph_Builder, span: Span, c: int) -> Operand {
    return graph_const(b, .Synthetic, span, slice_header_width_type, fmt.tprint(c), Const_Value{int = i128(c)})
}

// A field reference made, `S.path`: its value, typed as the reference (what
// print and llvm_view know one by) — its offset less its type's base.
lw_field_ref_offset :: proc(k: ^TC, n: Tree_Id) -> Operand {
    b := k.gb
    span := tree_span(k.t, n)
    t := tc_node_type(k, n)
    fr := distinct_base(t).(^Type_Field)
    dyn, at := lw_field_ref_abs(k, n)
    at -= field_ref_base(fr.owner, fr.elem)
    if dyn == NO_VALUE { return graph_const(b, .Synthetic, span, t, fmt.tprint(at), Const_Value{int = i128(at)}) }
    return graph_op_value(b, .Arith, .Synthetic, span, t, "+", dyn, lw_number(b, span, at))
}

// A reference's offset in its struct: a part known only when it runs
// (NO_VALUE for none) and a known part. A field's is known; an item's adds
// where the items start (a list's after its len) and its index times the
// item's size, the index checked to be within the array's cap. One held, in
// a variable or a field: its value and its type's base.
@(private="file")
lw_field_ref_abs :: proc(k: ^TC, n: Tree_Id) -> (dyn: Operand, at: int) {
    t := k.t
    b := k.gb
    span := tree_span(t, n)
    wide := slice_header_width_type
    if !lw_makes_field_ref(k, n) {
        fr := distinct_base(tc_node_type(k, n)).(^Type_Field)
        return lw_expr(k, n, .Value).v, field_ref_base(fr.owner, fr.elem)
    }
    base := Tree_Id(t.a[n])
    #partial switch t.tag[n] {
    case .Field:
        of: Type
        if fr, is_ref := distinct_base(tc_node_type(k, base)).(^Type_Field); is_ref {
            of = fr.elem
            dyn, at = lw_field_ref_abs(k, base)
        } else {
            of, dyn = tc_node_type(k, base), NO_VALUE
        }
        _, offset, _, _ := struct_field_at(field_ref_struct(of), tc_text(Token_Id(t.b[n])))
        return dyn, at + offset
    case .Index:
        fr := distinct_base(tc_node_type(k, base)).(^Type_Field)
        fa, _ := field_ref_items(fr.elem)
        dyn, at = lw_field_ref_abs(k, base)
        at += fa.at
        idx_n := Tree_Id(t.b[n])
        ir := lw_expr(k, idx_n, .Value, .Explicit)
        ix := build_index_value(b, ir.v, tc_node_type(k, idx_n), span)
        if _, known := tc_comptime_int(k, idx_n); !known {
            text := fmt.tprintf("a field reference's index within its %d items", fa.count)
            graph_assert(b, span, text, graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, ">=", ix, lw_number(b, span, 0)), .Implied, nil)
            graph_assert(b, span, text, graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, "<", ix, lw_number(b, span, fa.count)), .Implied, nil)
        }
        scaled := graph_op_value(b, .Arith, .Synthetic, span, wide, "*", ix, lw_number(b, span, type_size(fa.elem)))
        if dyn == NO_VALUE { return scaled, at }
        return graph_op_value(b, .Arith, .Synthetic, span, wide, "+", dyn, scaled), at
    }
    lw_fail(k, n, "a field reference made of this")
}

// `s[f]`'s offset in s: f's value and its type's base, typed as f is (what
// llvm_view knows a field's view by).
lw_field_ref_at :: proc(k: ^TC, idx_n: Tree_Id, span: Span, w: Written) -> Operand {
    b := k.gb
    t := tc_node_type(k, idx_n)
    fr := distinct_base(t).(^Type_Field)
    v := lw_expr(k, idx_n, .Value, w).v
    base := field_ref_base(fr.owner, fr.elem)
    if base == 0 { return v }
    return graph_op_value(b, .Arith, .Synthetic, span, t, "+", v, lw_number(b, span, base))
}
