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
// A path goes through the struct's own fields and fixed arrays, by any index,
// known or not. Never through a pointer, a slice or a list: what they hold
// isn't at a fixed place in the struct.
//
// f.text() names the field, `keyboard.held[W]`, and `R.from_text(text)`, R an
// alias of the reference's type, finds it again. Both know every field of that
// type the struct holds, by its path (field_ref_paths).
// ---------------------------------------------------------------------------

// The most fields of one type a struct can have named.
FIELD_REF_NAMES_MOST :: 4096

Field_Path :: struct {
    text:   string,
    offset: int,
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
    if fa, is_array := distinct_base(t).(^Type_Fixed_Array); is_array { return field_ref_holds(fa.elem, elem) }
    return false
}

// Every field of type elem that owner holds, by its path and offset, in the
// order the struct lists them; false when there are more than
// FIELD_REF_NAMES_MOST. An array indexed by an enum names its items by its
// variants, one name a value, the first by name.
field_ref_paths :: proc(owner, elem: Type) -> ([]Field_Path, bool) {
    out := make([dynamic]Field_Path, context.temp_allocator)
    walk :: proc(out: ^[dynamic]Field_Path, t, elem: Type, prefix: string, at: int) -> bool {
        if prefix != "" && types_equal(t, elem) {
            if len(out) >= FIELD_REF_NAMES_MOST { return false }
            append(out, Field_Path{prefix, at})
        }
        if !field_ref_holds(t, elem) { return true }
        if sd := field_ref_struct(t); sd != nil {
            for f, i in sd.fields {
                if f.decl == 0 { continue }   // (a union variant's tag: no field written)
                name := f.name if prefix == "" else fmt.tprintf("%s.%s", prefix, f.name)
                walk(out, f.type_, elem, name, at + struct_field_offset(sd, i)) or_return
            }
            return true
        }
        fa, is_array := distinct_base(t).(^Type_Fixed_Array)
        if !is_array { return true }
        size := type_size(fa.elem)
        if et, by_enum := distinct_base(fa.index_type).(^Type_Enum); by_enum && fa.index_type != nil {
            Variant :: struct { name: string, value: int }
            variants := make([dynamic]Variant, 0, len(et.variants), context.temp_allocator)
            for name, value in et.variants { append(&variants, Variant{name, value}) }
            slice.sort_by(variants[:], proc(a, b: Variant) -> bool { return a.value < b.value || a.value == b.value && a.name < b.name })
            for v, k in variants {
                if v.value < 0 || v.value >= fa.size || k > 0 && v.value == variants[k - 1].value { continue }
                walk(out, fa.elem, elem, fmt.tprintf("%s[%s]", prefix, v.name), at + v.value * size) or_return
            }
            return true
        }
        for i in 0 ..< fa.size {
            walk(out, fa.elem, elem, fmt.tprintf("%s[%d]", prefix, i), at + i * size) or_return
        }
        return true
    }
    ok := walk(&out, owner, elem, "", 0)
    return out[:], ok
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
    return type_field(owner, t)
}

// `r[i]`, r a reference to a fixed array: a reference to its i-th item, i a
// number or the array's enum, checked as an array's index is.
tc_field_ref_index :: proc(k: ^TC, n, idx_n: Tree_Id, fr: ^Type_Field, span: Span) -> Type {
    fa, is_array := distinct_base(fr.elem).(^Type_Fixed_Array)
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
    if at, known := tc_comptime_int(k, idx_n); known && (at < 0 || at >= i64(fa.size)) {
        tc_error(k, span, TYPE_INDEX_OUT_OF_BOUNDS_CONST, at, fa.size, fa.size - 1)
    }
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

// A field reference's value: its offset in bytes. A field's is known; an
// item's adds its index times the item's size, the index checked to be in
// the array.
lw_field_ref_offset :: proc(k: ^TC, n: Tree_Id) -> Operand {
    t := k.t
    b := k.gb
    span := tree_span(t, n)
    wide := slice_header_width_type
    number :: proc(b: ^Graph_Builder, span: Span, c: int) -> Operand {
        return graph_const(b, .Synthetic, span, slice_header_width_type, fmt.tprint(c), Const_Value{int = i128(c)})
    }
    if !lw_makes_field_ref(k, n) { return lw_expr(k, n, .Value).v }   // (one held: its value)
    base := Tree_Id(t.a[n])
    #partial switch t.tag[n] {
    case .Field:
        at: Type
        from: Operand
        if fr, is_ref := distinct_base(tc_node_type(k, base)).(^Type_Field); is_ref {
            at, from = fr.elem, lw_field_ref_offset(k, base)
        } else {
            at, from = tc_node_type(k, base), number(b, span, 0)
        }
        _, offset, _, _ := struct_field_at(field_ref_struct(at), tc_text(Token_Id(t.b[n])))
        if offset == 0 { return from }
        return graph_op_value(b, .Arith, .Synthetic, span, wide, "+", from, number(b, span, offset))
    case .Index:
        fr := distinct_base(tc_node_type(k, base)).(^Type_Field)
        fa := distinct_base(fr.elem).(^Type_Fixed_Array)
        from := lw_field_ref_offset(k, base)
        idx_n := Tree_Id(t.b[n])
        ir := lw_expr(k, idx_n, .Value, .Explicit)
        at := build_index_value(b, ir.v, tc_node_type(k, idx_n), span)
        if _, known := tc_comptime_int(k, idx_n); !known {
            text := fmt.tprintf("a field reference's index within its %d items", fa.size)
            graph_assert(b, span, text, graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, ">=", at, number(b, span, 0)), .Implied, nil)
            graph_assert(b, span, text, graph_op_value(b, .Compare, .Synthetic, span, Type_Bool{}, "<", at, number(b, span, fa.size)), .Implied, nil)
        }
        scaled := graph_op_value(b, .Arith, .Synthetic, span, wide, "*", at, number(b, span, type_size(fa.elem)))
        return graph_op_value(b, .Arith, .Synthetic, span, wide, "+", from, scaled)
    }
    lw_fail(k, n, "a field reference made of this")
}
