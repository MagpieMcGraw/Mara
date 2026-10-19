package mara

// The layout of a value: its size and alignment in bytes, as LLVM lays out
// the IR type the emitter gives it (llvm_type_from_checker) on the target —
// x86-64, or wasm32 for a web build. The one table everything reads: the
// checker's storage routing and byte views, size_of, the constant folder, the
// C ABI and the emitter.

// A web build's target: 32-bit words and pointers. Set once, before checking.
word_size_is_32: bool

Layout :: struct {
    size, align: int,
}

type_size  :: proc(t: Type) -> int { return type_layout(t).size }
type_align :: proc(t: Type) -> int { return type_layout(t).align }

type_layout :: proc(t: Type) -> Layout {
    switch v in resolve_infer(t) {
    case Type_Bool, Type_Utf8, Type_Byte:
        return {1, 1}
    case Type_F64, Type_Infer_Int, Type_Infer_Float:
        return {8, 8}
    case Type_Numeric:
        n := word_bytes() if v.bits == 0 else int(v.bits) / 8
        return {n, n}
    case Type_Err:
        return {4, 4}   // an i32: its set's id and its tag
    case Type_Void:
        return {0, 1}   // `{}`
    case ^Type_Ptr:
        if slice_ref_of(v) != nil { return slice_ref_layout() }
        return {word_bytes(), word_bytes()}
    case Type_CString:
        return {word_bytes(), word_bytes()}
    case ^Type_Scope:
        if v.kind != .Struct { return {word_bytes(), word_bytes()} }   // a fun value: its address
        return struct_layout(&v.sd)
    case ^Type_Fixed_Array:
        e := type_layout(v.elem)
        return {v.size * e.size, e.align}
    case ^Type_Slice:
        return slice_header_layout()
    case ^Type_Partial_Array:
        // `{ len, cap, ptr, [N x T] }`: a slice header over its own elements.
        l := slice_header_fields()
        e := type_layout(v.elem)
        layout_field(&l, {v.size * e.size, e.align})
        return layout_close(l)
    case ^Type_Enum:
        n := tag_bytes(v.tag_type)
        return {n, n}
    case ^Type_Union:
        return union_layout(v)
    case ^Type_Distinct:
        return type_layout(v.base_type)
    case Type_Const_Int, Type_Any, Type_Error, nil:
        // (No value's type: what checking reports. Sized as a word.)
        return {8, 8}
    }
    return {8, 8}
}

// A ^[]T — a reference to a slice's or a list's elements, by value: where
// its len is, its cap, its data (`{ ptr, i64, ptr }`: its cap and data where
// a slice header's are).
slice_ref_layout :: proc() -> Layout {
    l := Layout{0, 1}
    layout_field(&l, {word_bytes(), word_bytes()})
    layout_field(&l, {8, 8})
    layout_field(&l, {word_bytes(), word_bytes()})
    return layout_close(l)
}

// The slice a ^[]T refers to (nil: t is no ^[]T).
slice_ref_of :: proc(t: Type) -> ^Type_Slice {
    pt, is_ptr := distinct_base(t).(^Type_Ptr)
    if !is_ptr || pt.elem == nil { return nil }
    sl, is_slice := distinct_base(pt.elem).(^Type_Slice)
    if !is_slice { return nil }
    return sl
}

word_bytes :: proc() -> int {
    return 4 if word_size_is_32 else 8
}

// A union tag's width: its declared type's, or an i64's.
tag_bytes :: proc(tag_type: string) -> int {
    switch tag_type {
    case "i8", "u8":   return 1
    case "i16", "u16": return 2
    case "i32", "u32": return 4
    }
    return 8
}

// A struct: its fields in order, each at its alignment (packed: none, and
// aligned to a byte), padded at the end to the struct's alignment.
struct_layout :: proc(sd: ^Scope_Body) -> Layout {
    l := Layout{0, 1}
    for &f in sd.fields { layout_field(&l, type_layout(f.type_), sd.is_packed) }
    return layout_close(l)
}

// A record's next field, placed: its offset.
layout_field :: proc(l: ^Layout, f: Layout, packed := false) -> (offset: int) {
    if !packed {
        l.size = round_up(l.size, f.align)
        l.align = max(l.align, f.align)
    }
    offset = l.size
    l.size += f.size
    return
}

// A record's size: its fields' end, padded to its alignment.
layout_close :: proc(l: Layout) -> Layout {
    return {round_up(l.size, l.align), l.align}
}

round_up :: proc(n, align: int) -> int {
    return (n + align - 1) / align * align
}

// A slice's header, `{ len, cap, ptr }`: its fields, still open (a partial
// array's elements follow them).
slice_header_fields :: proc() -> Layout {
    l := Layout{0, 1}
    layout_field(&l, {8, 8})
    layout_field(&l, {8, 8})
    layout_field(&l, {word_bytes(), word_bytes()})
    return l
}

slice_header_layout :: proc() -> Layout {
    return layout_close(slice_header_fields())
}

// A union: as big as its largest variant — each variant's struct begins with
// the tag (and the pad), so that is the union laid out holding it — at least
// its declared size; aligned as its tag is, or to a byte with a pad (how a
// union mirrors a C layout). A niche union is its Some variant's pointer.
union_layout :: proc(ut: ^Type_Union) -> Layout {
    if ut.niche_some != "" { return {word_bytes(), word_bytes()} }
    size := ut.min_size
    for _, st in ut.variant_structs { size = max(size, type_size(st)) }
    return layout_close({size, 1 if ut.tag_pad != nil else tag_bytes(ut.tag_type)})
}

// The bytes a tagged union's variants begin with: its tag, then its pad.
union_header_bytes :: proc(ut: ^Type_Union) -> int {
    n := tag_bytes(ut.tag_type)
    if ut.tag_pad != nil { n += type_size(ut.tag_pad) }
    return n
}
