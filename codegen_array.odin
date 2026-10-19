package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Slice IR helpers
// ---------------------------------------------------------------------------

// GEP into a slice header by field index — see SLICE constants (codegen.odin)
// for the canonical len/cap/ptr ordering.
emit_slice_gep :: proc(g: ^Codegen, result, src: Val, field: int) {
    emit_field_gep_into(g, result, SLICE_IR_TYPE, src, field)
}

emit_slice_alloca :: proc(g: ^Codegen, result: Val) {
    emit_alloca(g, result, SLICE_IR_TYPE)
}

// A field of the slice header (or partial array) at `header` — SLICE.len,
// .cap (at SLICE_LEN_IR) or .ptr — loaded.
emit_header_field :: proc(g: ^Codegen, header: Val, field: int) -> Val {
    gep := fresh_tmp(g)
    emit_slice_gep(g, gep, header, field)
    v := fresh_tmp(g)
    emit_load_into(g, v, IR_PTR if field == SLICE.ptr else SLICE_LEN_IR, gep)
    return v
}

// ... and stored.
emit_header_set :: proc(g: ^Codegen, header: Val, field: int, v: Val) {
    gep := fresh_tmp(g)
    emit_slice_gep(g, gep, header, field)
    emit_store(g, IR_PTR if field == SLICE.ptr else SLICE_LEN_IR, v, gep)
}

// A value of type `t` at `ptr` made a valid zero value: each list in it —
// through struct fields and array elements, a list's own elements too —
// empty, its len 0. (Nothing is constructed: a bare declaration is its zero.)
// Over zeroed storage (`zeroed`) that is so already; under -profile memory,
// each list there is still a new instance of its site.
stamp_zero_partial_arrays :: proc(g: ^Codegen, ptr: Val, t: Type, zeroed := false) {
    if zeroed && !g.profile_memory { return }
    stamp :: proc(g: ^Codegen, ptr: Val, t: Type, _: []Ir_Arg) { stamp_zero_partial_arrays(g, ptr, t) }
    base := distinct_base(t)
    if pa, is_pa := base.(^Type_Partial_Array); is_pa {
        emit_partial_array_zero(g, ptr, pa, zero = false)
        mem_probe_new(g, ptr, pa)
        if pa.size > 0 && value_has_partial_array(g, pa.elem) {
            was := mem_elements(g)
            emit_each_element(g, partial_elements(g, ptr, pa), pa.elem, pa.size, stamp)
            mem_restore(g, was)
        }
        return
    }
    // An array whose elements hold partial arrays: each element.
    if fa, is_fa := base.(^Type_Fixed_Array); is_fa {
        if fa.size > 0 && value_has_partial_array(g, fa.elem) {
            was := mem_elements(g)
            emit_each_element(g, ptr, fa.elem, fa.size, stamp)
            mem_restore(g, was)
        }
        return
    }
    sd := as_struct_body(base)
    if sd == nil { return }
    llvm_name := ir_class_type(sd)
    for &f, i in sd.fields {
        if !value_has_partial_array(g, f.type_) { continue }
        #partial switch _ in distinct_base(f.type_) {
        case ^Type_Partial_Array, ^Type_Scope, ^Type_Fixed_Array:
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, ptr, i)
            was := mem_field(g, sd, &f)
            stamp_zero_partial_arrays(g, gep, f.type_)
            mem_restore(g, was)
        }
    }
}

// A value of type `t` copied in at `ptr`: under -profile memory, each list in
// it the instance there (a list holds nothing that points at itself, so a
// copy is whole as it is).
reanchor_partial_arrays :: proc(g: ^Codegen, t: Type, ptr: Val) {
    if !g.profile_memory || !value_has_partial_array(g, t) { return }
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil {
        llvm_name := ir_class_type(sd)
        for &f, i in sd.fields {
            if !value_has_partial_array(g, f.type_) { continue }
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, ptr, i)
            was := mem_field(g, sd, &f)
            reanchor_partial_arrays(g, f.type_, gep)
            mem_restore(g, was)
        }
        return
    }
    #partial switch v in base {
    case ^Type_Partial_Array:
        elem_ir := llvm_type_from_checker(v.elem)
        elements_ptr := partial_elements(g, ptr, v)
        mem_probe_into(g, ptr, v)
        if value_has_partial_array(g, v.elem) {
            was := mem_elements(g)
            reanchor_slots(g, v.elem, ir_array_type(v.size, elem_ir), elements_ptr, ir_int(v.size))
            mem_restore(g, was)
        }
    case ^Type_Fixed_Array:
        was := mem_elements(g)
        defer mem_restore(g, was)
        arr_ir := ir_array_type(v.size, llvm_type_from_checker(v.elem))
        if v.size <= 4 {
            for i in 0..<v.size {
                gep := fresh_tmp(g)
                emit_array_gep_const(g, gep, arr_ir, ptr, i)
                reanchor_partial_arrays(g, v.elem, gep)
            }
        } else {
            reanchor_slots(g, v.elem, arr_ir, ptr, ir_int(v.size))
        }
    case ^Type_Union:
        // Only the live variant's fields exist: dispatch on the tag.
        tag_ir := union_tag_ir_type(v)
        tag := load_union_tag(g, v, ptr)
        for name in v.variants {
            vst := v.variant_structs[name]
            if vst == nil || !value_has_partial_array(g, vst) { continue }
            is_it := fresh_tmp(g)
            ir_icmp(g, is_it, .Eq, tag_ir, tag, ir_int(v.tag_map[name]))
            fix_label := fresh_label(g, "reanchor.variant")
            next_label := fresh_label(g, "reanchor.next")
            emit_cond_br(g, is_it, fix_label, next_label)
            emit_label(g, fix_label)
            reanchor_partial_arrays(g, sd_type_scope(vst), ptr) // the variant overlays the union at offset 0
            emit_br(g, next_label)
            emit_label(g, next_label)
        }
    }
}

// reanchor_partial_arrays over `count` consecutive `elem` slots of array type
// `arr_ir` at `base` — a runtime loop, so a big array doesn't unroll.
reanchor_slots :: proc(g: ^Codegen, elem: Type, arr_ir: Ir_Type, base, count: Val) {
    l := emit_loop_begin(g, count, "reanchor")
    gep := fresh_tmp(g)
    emit_array_gep_var(g, gep, arr_ir, base, l.i, SLICE_LEN_IR)
    reanchor_partial_arrays(g, elem, gep)
    emit_loop_end(g, l)
}

// A counted loop, at runtime: i from 0 while i < count (signed, at slice
// header width), its counter in a slot — so a big array loops, not unrolls.
// emit_loop_begin leaves the code in its body, i loaded; emit_loop_end steps
// i and closes it.
Count_Loop :: struct { slot, i: Val, cond, end: Ir_Label }

emit_loop_begin :: proc(g: ^Codegen, count: Val, name: string) -> (l: Count_Loop) {
    w := SLICE_LEN_IR
    l.slot = fresh_tmp(g)
    emit_alloca(g, l.slot, w)
    emit_store(g, w, ir_int(0), l.slot)
    l.cond = fresh_label(g, fmt.tprintf("%s.cond", name))
    body := fresh_label(g, fmt.tprintf("%s.body", name))
    l.end = fresh_label(g, fmt.tprintf("%s.end", name))
    emit_br(g, l.cond)
    emit_label(g, l.cond)
    l.i = fresh_tmp(g)
    emit_load_into(g, l.i, w, l.slot)
    more := fresh_tmp(g)
    ir_icmp(g, more, .Slt, w, l.i, count)
    emit_cond_br(g, more, body, l.end)
    emit_label(g, body)
    return
}

emit_loop_end :: proc(g: ^Codegen, l: Count_Loop) {
    next := fresh_tmp(g)
    ir_bin(g, next, .Add, SLICE_LEN_IR, l.i, ir_int(1))
    emit_store(g, SLICE_LEN_IR, next, l.slot)
    emit_br(g, l.cond)
    emit_label(g, l.end)
}

// Text into a fixed byte array: the array zeroed, then the text's bytes — the
// zeros past them end it. (Not its terminating zero: text that fills the array
// has no room for one; copying it wrote a byte past the array.)
emit_text_into_array :: proc(g: ^Codegen, dst: Val, text: string, total_bytes: int) {
    if len(text) > total_bytes { codegen_fatal(g, {}, CODE_TEXT_LONGER_THAN_ARRAY, len(text), total_bytes) }
    if len(text) == 0 {
        emit_memset_zero(g, dst, total_bytes)
        return
    }
    src := get_string_literal(g, text)
    emit_memset_zero(g, dst, total_bytes)
    emit_memcpy(g, dst, src, len(text))
}

// Whether a value of type `t` holds a partial array anywhere inside it —
// directly, in a struct field, an array slot, or a union variant.
value_has_partial_array :: proc(g: ^Codegen, t: Type) -> bool {
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil {
        for &f in sd.fields {
            if value_has_partial_array(g, f.type_) { return true }
        }
        return false
    }
    #partial switch v in base {
    case ^Type_Partial_Array:
        return true
    case ^Type_Fixed_Array:
        return value_has_partial_array(g, v.elem)
    case ^Type_Union:
        for name in v.variants {
            if vst := v.variant_structs[name]; vst != nil && value_has_partial_array(g, vst) {
                return true
            }
        }
    }
    return false
}

// Alloca a slice header (SLICE_IR_TYPE) and store data_ptr / len / cap into
// its fields. Returns the alloca ptr. Callers load from it to get the slice value.
emit_build_temp_slice :: proc(g: ^Codegen, data_ptr, len_val, cap_val: Val) -> Val {
    slice_alloca := fresh_tmp(g)
    emit_slice_alloca(g, slice_alloca)
    emit_slice_header_at(g, slice_alloca, data_ptr, len_val, cap_val)
    return slice_alloca
}

// A list's len where it bounds memory: checked within its N (emit_len_check).
list_len_checked :: proc(g: ^Codegen, at: Val, pa: ^Type_Partial_Array, span: Span = {}) -> Val {
    n := emit_header_field(g, at, SLICE.len)
    emit_len_check(g, n, ir_int(pa.size), span)
    return n
}

// A header's cap and data where it is, by its type: a slice's header holds
// them; a list's are its type's N and its own elements.
hdr_cap_at :: proc(g: ^Codegen, at: Val, t: Type) -> Val {
    if pa, is_list := distinct_base(t).(^Type_Partial_Array); is_list { return ir_int(pa.size) }
    return emit_header_field(g, at, SLICE.cap)
}

hdr_data_at :: proc(g: ^Codegen, at: Val, t: Type) -> Val {
    if pa, is_list := distinct_base(t).(^Type_Partial_Array); is_list { return partial_elements(g, at, pa) }
    return emit_header_field(g, at, SLICE.ptr)
}

// A ^[]T made (slice_ref_ir_type): where the len is, the cap, the data — in
// a temporary of its own (an aggregate is where it is). A slice's: its
// header's address, cap -1 (slice_ref_to).
emit_slice_ref :: proc(g: ^Codegen, len_at, cap, data: Val) -> Val {
    ref := fresh_tmp(g)
    emit_alloca(g, ref, slice_ref_ir_type())
    at := fresh_tmp(g)
    emit_slice_gep(g, at, ref, SLICE.len)
    emit_store(g, IR_PTR, len_at, at)
    emit_header_set(g, ref, SLICE.cap, cap)
    emit_header_set(g, ref, SLICE.ptr, data)
    return ref
}

// A ^[]T to the header at `at` of type t: a list's, its len's address, its
// cap and data; a slice's, its header's address and cap -1 (its cap and data
// read from it when used).
slice_ref_to :: proc(g: ^Codegen, at: Val, t: Type) -> Val {
    if _, is_list := distinct_base(t).(^Type_Partial_Array); is_list {
        len_at := fresh_tmp(g)
        emit_slice_gep(g, len_at, at, SLICE.len)
        return emit_slice_ref(g, len_at, hdr_cap_at(g, at, t), hdr_data_at(g, at, t))
    }
    return emit_slice_ref(g, at, ir_int(-1), IR_NULL)
}

// A slice header's fields stored at `at`: ptr, len, cap.
emit_slice_header_at :: proc(g: ^Codegen, at, data_ptr, len_val, cap_val: Val) {
    emit_header_set(g, at, SLICE.ptr, data_ptr)
    emit_header_set(g, at, SLICE.len, len_val)
    emit_header_set(g, at, SLICE.cap, cap_val)
}

// ---------------------------------------------------------------------------
// Array codegen
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Byte-buffer reinterpret codegen
//
// Covers []byte, [N!]byte, and Array(byte, N). All three share the same shape:
//   1. Resolve the buffer to (data_ptr, cap_val)
//   2. Check offset + size <= cap
//   3. GEP by i8 at the offset, store/load sized by value type
// The only real difference between buffer kinds is step 1.
// ---------------------------------------------------------------------------

// The address of `count` elements of `size` bytes at byte `offset` of the
// buffer at data_ptr, cap_val bytes long — checked to lie within it.
emit_byte_count_ptr :: proc(g: ^Codegen, data_ptr, cap_val, offset, count: Val, size: int, label: string) -> Val {
    w := SLICE_LEN_IR
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := emit_byte_span_outside(g, offset, count, cap_val, size)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    bytes := fresh_tmp(g)
    ir_bin(g, bytes, .Mul, w, count, ir_int(size))
    emit_fail(g, fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%lld + %%lld > capacity %%lld\n", label),
              fail_i64(offset), fail_i64(bytes), fail_i64(cap_val))
    emit_label(g, ok_lbl)

    elem_ptr := fresh_tmp(g)
    emit_elem_gep(g, elem_ptr, IR_I8, data_ptr, offset, w)
    return elem_ptr
}

// Whether n elements of `size` bytes at byte offset off fall outside a
// buffer of cap_val bytes: off past the cap, or n more than fit in the room
// after it. Compared unsigned, a negative offset or count is outside too,
// and nothing wraps — no `off + n * size`, which let -1 + 4 through and a
// huge count's product wrap small. All at SLICE_LEN_IR. The i1 is
// true when outside.
emit_byte_span_outside :: proc(g: ^Codegen, off, n, cap_val: Val, size := 1) -> Val {
    w := SLICE_LEN_IR
    past := fresh_tmp(g)
    ir_icmp(g, past, .Ugt, w, off, cap_val)
    room := fresh_tmp(g)
    ir_bin(g, room, .Sub, w, cap_val, off)
    if size > 1 {
        fits := fresh_tmp(g)
        ir_bin(g, fits, .Udiv, w, room, ir_int(size))
        room = fits
    }
    over := fresh_tmp(g)
    ir_icmp(g, over, .Ugt, w, n, room)
    outside := fresh_tmp(g)
    ir_bin(g, outside, .Or, IR_I1, past, over)
    return outside
}

// Bounds check for byte-buffer access at offset [low, low+size), at
// SLICE_LEN_IR: the caller has low and cap_val at that width.
emit_byte_size_bounds_check :: proc(g: ^Codegen, cap_val, low: Val, size: int, label: string, span: Span = {}) {
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := emit_byte_span_outside(g, low, ir_int(size), cap_val)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    // (Where, when the caller knows: as a bounds check's message says it.)
    at := ""
    if span != {} {
        loc, _ := strings.replace_all(span_location(span), "%", "%%", context.temp_allocator)
        at = strings.concatenate({loc, " "}, context.temp_allocator)
    }
    emit_fail(g, fmt.tprintf("%sruntime error: byte buffer %s out of bounds: offset %%lld + %d > capacity %%lld\n", at, label, size),
              fail_i64(low), fail_i64(cap_val))
    emit_label(g, ok_lbl)
}

// A big-endian integer's value in the machine's order: its bytes swapped
// (an integer of 16 bits or more; anything else is itself).
emit_bswap_value :: proc(g: ^Codegen, val: Val, t: Type) -> Val {
    if !is_swappable_integer(t) { return val }
    bits := type_size(t) * 8
    if bits < 16 { return val }
    g.bswap_intrinsics[bits] = true
    swapped := fresh_tmp(g)
    ty := ir_int_type(bits)
    ir_call(g, swapped, ty, ir_global(fmt.tprintf("llvm.bswap.i%d", bits)), {ty, val, {}})
    return swapped
}

// Big-endian byte-swap in place: walks `ty` rooted at `base_ptr` and emits
// llvm.bswap on every multi-byte integer leaf. Used by `#big_endian` byte-
// buffer reads after the load/memcpy.
//
// `base_ir_type` is the LLVM aggregate type at `base_ptr` (used for struct/
// array GEPs). For scalar leaves it's unused — the bit width comes from
// type_size.
//
// Skipped leaves: 1-byte primitives (byte/utf8/c8/u8/i8/bool — already in
// order); floats, pointers, slices, partial arrays (bswap is meaningless).
emit_bswap_in_place :: proc(g: ^Codegen, base_ptr: Val, base_ir_type: Ir_Type, ty: Type) {
    base := distinct_base(ty)

    if sd := as_struct_body(base); sd != nil {
        st_llvm := ir_class_type(sd)
        for &f, idx in sd.fields {
            field_ir := field_ir_type(&f)
            field_gep := fresh_tmp(g)
            emit_field_gep_into(g, field_gep, st_llvm, base_ptr, idx)
            emit_bswap_in_place(g, field_gep, field_ir, f.type_)
        }
        return
    }

    if fa, ok := base.(^Type_Fixed_Array); ok {
        elem_bytes := type_size(fa.elem)
        if elem_bytes <= 1 { return }
        elem_ir := llvm_type_from_checker(fa.elem)
        // Bounded unroll: large fixed arrays (e.g. `[65536!]u32` for a TTF loca
        // table) produce ~4 IR lines per element times fa.size — a few hundred
        // is fine, tens of thousands ruins the IR file and clang. Past the
        // threshold, emit the same counter-driven loop the partial-array path
        // uses. The threshold is empirical: 16 keeps small Mat4/Vec swizzles
        // and per-table-entry record bswaps unrolled (fast paths) while
        // catching the bulk-array case.
        BSWAP_UNROLL_THRESHOLD :: 16
        if fa.size > BSWAP_UNROLL_THRESHOLD {
            // Build a ptr to element 0, then loop count = fa.size.
            elem0 := fresh_tmp(g)
            emit_array_gep_const(g, elem0, base_ir_type, base_ptr, 0)
            emit_partial_bswap_loop(g, elem0, ir_int(fa.size), fa.elem)
            return
        }
        for i in 0..<fa.size {
            elem_gep := fresh_tmp(g)
            emit_array_gep_const(g, elem_gep, base_ir_type, base_ptr, i)
            emit_bswap_in_place(g, elem_gep, elem_ir, fa.elem)
        }
        return
    }

    if !is_swappable_integer(base) { return }
    bits := type_size(base) * 8
    if bits < 16 { return }
    intrinsic := fmt.tprintf("llvm.bswap.i%d", bits)
    g.bswap_intrinsics[bits] = true
    loaded := fresh_tmp(g)
    ty := ir_int_type(bits)
    ir_load(g, loaded, ty, base_ptr, 1)
    swapped := fresh_tmp(g)
    ir_call(g, swapped, ty, ir_global(intrinsic), {ty, loaded, {}})
    ir_store(g, ty, swapped, base_ptr, 1)
}

// True when `t` is a multi-byte integer type — the kind bswap is meaningful for.
// Returns true for signed/unsigned Type_Numeric (incl. i64), Type_Enum
// (integer tag). Returns false for byte/utf8/c8/bool (1 byte), floats, pointers,
// slices, etc. Caller filters out widths < 16 bits.
is_swappable_integer :: proc(t: Type) -> bool {
    bt := distinct_base(t)
    #partial switch v in bt {
    case Type_Numeric:
        return v.kind == .Signed || v.kind == .Unsigned
    case ^Type_Enum:
        return true
    }
    return false
}

// ---- No-arg construction of array element backings ------------------------
//
// Array slots are zero-filled, not constructed — so the elements of a
// `[N]Font` / `[N!]str64` come up with field defaults un-applied and nested
// partial-array headers null (cap = 0). These helpers run each element type's
// no-arg constructor at array-declaration / struct-construction time, so any
// slot you later index or append into is already a valid value. (User decision
// 2026-06-13: "no-arg constructors should run for arrays — might as well do it
// when the array is declared.")

// True when a value of `t` needs more than the zero-fill to be fully formed: a
// struct with an auto-init function (field defaults or partial-array fields), a
// partial array (needs a stamped header), or a fixed array whose element does.
// Plain scalars and trivial all-zero structs return false — no per-element work.
type_needs_construction :: proc(g: ^Codegen, t: Type) -> bool {
    bt := distinct_base(t)
    #partial switch v in bt {
    case ^Type_Scope:
        if v.kind == .Struct {
            // (An element that can't be built bare stays zero: its
            // constructor needs arguments, or can fail.)
            _, has_init := g.checked.functions[v.name]
            return has_init && constructs_bare(v)
        }
    case ^Type_Partial_Array:
        return true
    case ^Type_Fixed_Array:
        return type_needs_construction(g, v.elem)
    }
    return false
}

// Emit a call to struct `st_name`'s auto-init on the slot at `addr`, supplying
// param defaults for a paramized constructor or just the sret pointer for a
// pure-data struct. No-op if
// the struct has no init function (trivial — the zero-fill already finished it).
// `args`: its constructor's arguments, the construction's (its params'
// defaults, which the checker built where it's written).
emit_struct_init_call :: proc(g: ^Codegen, st_name: string, addr: Val, args: []Ir_Arg = nil) {
    init_fn, has_init := g.checked.functions[st_name]
    if !has_init { return }
    if init_fn != nil && len(init_fn.params) > 0 {
        if len(args) != len(init_fn.params) {
            codegen_fatal(g, {}, CODE_BARE_CONSTRUCTION_ARGUMENT, st_name, init_fn.params[len(args) if len(args) < len(init_fn.params) else 0].name)
        }
        all := make([dynamic]Ir_Arg, 0, len(args) + 1, context.temp_allocator)
        append(&all, ..args)
        append(&all, Ir_Arg{ty = IR_PTR, v = addr})
        ir_call(g, {}, IR_VOID, mara_fn(g, st_name), ..all[:])
    } else {
        ir_call(g, {}, IR_VOID, mara_fn(g, st_name), {IR_PTR, addr, {}})
    }
}

// Construct the value of type `t` at the already-zeroed slot `ptr`: call its
// auto-init (struct), stamp its header + construct its inline elements (partial
// array), or construct each element (fixed array). Mutually recursive with
// gen_construct_elements.
gen_construct_value_at :: proc(g: ^Codegen, ptr: Val, t: Type, args: []Ir_Arg = nil) {
    bt := distinct_base(t)
    #partial switch v in bt {
    case ^Type_Scope:
        if v.kind == .Struct {
            emit_struct_init_call(g, v.name, ptr, args)
        }
    case ^Type_Partial_Array:
        emit_partial_array_zero(g, ptr, v, zero = false)
        gen_construct_partial_array_elements(g, ptr, v, args)
    case ^Type_Fixed_Array:
        gen_construct_elements(g, ptr, v.elem, v.size, args)
    }
}

// Construct each inline element of a (already header-stamped) partial array at
// `pa_addr`. Skipped entirely when the element type is trivially zero-formed.
gen_construct_partial_array_elements :: proc(g: ^Codegen, pa_addr: Val, pa: ^Type_Partial_Array, args: []Ir_Arg = nil) {
    if !type_needs_construction(g, pa.elem) { return }
    gen_construct_elements(g, partial_elements(g, pa_addr, pa), pa.elem, pa.size, args)
}

// Run no-arg construction over `count` elements starting at `elements_ptr` (a
// pointer to element 0), but only when the element type needs it.
gen_construct_elements :: proc(g: ^Codegen, elements_ptr: Val, elem: Type, count: int, args: []Ir_Arg = nil) {
    if count <= 0 { return }
    if !type_needs_construction(g, elem) { return }
    emit_each_element(g, elements_ptr, elem, count, gen_construct_value_at, args)
}

// `each` over `count` elements of type `elem` starting at `elements_ptr` (a
// pointer to element 0): a runtime counted loop, so `[256]Font` is a
// handful of instructions, not 256 unrolled ones.
emit_each_element :: proc(g: ^Codegen, elements_ptr: Val, elem: Type, count: int, each: proc(g: ^Codegen, ptr: Val, t: Type, args: []Ir_Arg), args: []Ir_Arg = nil) {
    l := emit_loop_begin(g, ir_int(count), "ctor")
    elem_ptr := fresh_tmp(g)
    emit_elem_gep(g, elem_ptr, llvm_type_from_checker(elem), elements_ptr, l.i, SLICE_LEN_IR)
    each(g, elem_ptr, elem, args)
    emit_loop_end(g, l)
}

// A partial array's elements: their address, past its header.
partial_elements :: proc(g: ^Codegen, addr: Val, pa: ^Type_Partial_Array) -> Val {
    elements_ptr := fresh_tmp(g)
    ir_gep_inbounds(g, elements_ptr, partial_array_ir_type(llvm_type_from_checker(pa.elem), pa.size), addr,
                    {IR_I32, ir_int(0), {}}, {IR_I32, ir_int(PARTIAL_ELEMENTS_FIELD), {}}, {IR_I32, ir_int(0), {}})
    return elements_ptr
}

// A list's zero value at `addr`: its elements zeroed (`zero`; over zeroed
// storage, not), its len 0. Returns the elements' address.
emit_partial_array_zero :: proc(g: ^Codegen, addr: Val, pa: ^Type_Partial_Array, zero := true) -> Val {
    elements_ptr := partial_elements(g, addr, pa)
    if zero { emit_memset_zero(g, elements_ptr, pa.size * type_size(pa.elem)) }
    emit_header_set(g, addr, SLICE.len, ir_int(0))
    return elements_ptr
}

// Initialize a partial-array slot in place AND populate its inline elements
// from a byte-buffer span. Used by both the standalone-decl path (after
// `alloca`) and the field-assign path (slot_ptr is the field's GEP).
// Handles the header init (.ptr → elements, .len = count, .cap = N), the
// byte-span memcpy into the elements area, and optional `#big_endian`
// per-element bswap. Runtime checks: the span lies within the source's
// src_cap bytes (it read past them), source bytes is divisible by elem
// size, and produces count <= cap.
gen_partial_array_byte_fill_at_core :: proc(g: ^Codegen, slot_ptr: Val, pa: ^Type_Partial_Array,
                                             src_data_ptr, src_cap, src_low, src_bytes: Val,
                                             is_big_endian: bool, span: Span) {
    cap_n := pa.size
    elem_bytes := type_size(pa.elem)

    // Its header: len 0 (the count added at the end).
    elements_ptr := emit_partial_array_zero(g, slot_ptr, pa, zero = false)

    w := SLICE_LEN_IR

    // Runtime check 0: the span within the source buffer.
    src_ok := fresh_label(g, "byte.view.ok")
    src_err := fresh_label(g, "byte.view.err")
    emit_cond_br(g, emit_byte_span_outside(g, src_low, src_bytes, src_cap), src_err, src_ok)
    emit_label(g, src_err)
    emit_fail(g, "runtime error: byte buffer view out of bounds: offset %lld + %lld > capacity %lld\n",
              fail_i64(src_low), fail_i64(src_bytes), fail_i64(src_cap))
    emit_label(g, src_ok)

    // Runtime check 1: src_bytes % elem_bytes == 0.
    rem := fresh_tmp(g)
    ir_bin(g, rem, .Urem, w, src_bytes, ir_int(elem_bytes))
    rem_ok := fresh_label(g, "pa.div.ok")
    rem_err := fresh_label(g, "pa.div.err")
    rem_cmp := fresh_tmp(g)
    ir_icmp(g, rem_cmp, .Ne, w, rem, ir_int(0))
    emit_cond_br(g, rem_cmp, rem_err, rem_ok)
    emit_label(g, rem_err)
    emit_fail(g, fmt.tprintf("runtime error: partial-array byte read at offset %%lld: %%lld bytes not divisible by elem size %d\n", elem_bytes),
              fail_i64(src_low), fail_i64(src_bytes))
    emit_label(g, rem_ok)

    // count = src_bytes / elem_bytes.
    count := fresh_tmp(g)
    ir_bin(g, count, .Udiv, w, src_bytes, ir_int(elem_bytes))

    // Runtime check 2: count <= cap.
    cap_ok := fresh_label(g, "pa.cap.ok")
    cap_err := fresh_label(g, "pa.cap.err")
    cap_cmp := fresh_tmp(g)
    ir_icmp(g, cap_cmp, .Ugt, w, count, ir_int(cap_n))
    emit_cond_br(g, cap_cmp, cap_err, cap_ok)
    emit_label(g, cap_err)
    emit_fail(g, fmt.tprintf("runtime error: partial-array byte read at offset %%lld: produced %%lld elements, exceeds cap %d\n", cap_n),
              fail_i64(src_low), fail_i64(count))
    emit_label(g, cap_ok)

    // memcpy(elements_ptr, src_data_ptr + src_low, src_bytes).
    src_offset_ptr := fresh_tmp(g)
    emit_elem_gep(g, src_offset_ptr, IR_I8, src_data_ptr, src_low, w)
    emit_memcpy_runtime(g, elements_ptr, src_offset_ptr, src_bytes)

    // `#big_endian` decorator on the source: byte-swap each element in
    // place. Count is runtime, so we emit a counter-driven loop wrapping the
    // per-element bswap.
    if is_big_endian {
        emit_partial_bswap_loop(g, elements_ptr, count, pa.elem)
    }

    // Auto-add to len. For a fresh decl this is + 0, so the final len = count.
    cur_len := emit_header_field(g, slot_ptr, SLICE.len)
    new_len := fresh_tmp(g)
    ir_bin(g, new_len, .Add, w, cur_len, count)
    emit_header_set(g, slot_ptr, SLICE.len, new_len)
    mem_probe_len(g, slot_ptr)
}

// Counter-driven loop that calls emit_bswap_in_place on each of `count`
// elements rooted at `elements_ptr`. Count is an SSA value at slice-header
// width. Used by `#big_endian` on partial-array reads — the count is only
// known at runtime, so the per-element swap can't be unrolled.
//
// If `elem_ty` contains no multi-byte integer leaves (e.g. `[N]byte`), the
// inner body is a no-op and an optimizer will see through it — but skip the
// loop entirely as a cheap source-level guard.
emit_partial_bswap_loop :: proc(g: ^Codegen, elements_ptr, count: Val, elem_ty: Type) {
    if !type_has_swappable_leaf(elem_ty) { return }

    elem_ir := llvm_type_from_checker(elem_ty)
    l := emit_loop_begin(g, count, "bswap")   // (a count: never negative)
    elem_gep := fresh_tmp(g)
    emit_elem_gep(g, elem_gep, elem_ir, elements_ptr, l.i, SLICE_LEN_IR)
    emit_bswap_in_place(g, elem_gep, elem_ir, elem_ty)
    emit_loop_end(g, l)
}

// True if `ty` contains any multi-byte integer leaf — i.e. emit_bswap_in_place
// would emit at least one bswap. Lets callers skip the wrapping loop entirely
// when the element layout has nothing to swap.
type_has_swappable_leaf :: proc(ty: Type) -> bool {
    base := distinct_base(ty)
    if sd := as_struct_body(base); sd != nil {
        for &f in sd.fields {
            if type_has_swappable_leaf(f.type_) { return true }
        }
        return false
    }
    if fa, ok := base.(^Type_Fixed_Array); ok {
        return type_has_swappable_leaf(fa.elem)
    }
    if !is_swappable_integer(base) { return false }
    return type_size(base) >= 2
}

// Runtime-sized memcpy. Used when the byte count is an SSA value, not a
// compile-time literal — e.g. partial-array byte-buffer reads where the
// source span size is computed from runtime slice bounds. `bytes` is at
// slice header width (SLICE_LEN_IR: i64), the intrinsic's.
emit_memcpy_runtime :: proc(g: ^Codegen, dst, src, bytes: Val) {
    ir_call(g, {}, IR_VOID, ir_global("llvm.memcpy.p0.p0.i64"), {IR_PTR, dst, {}}, {IR_PTR, src, {}}, {IR_I64, bytes, {}}, {IR_I1, IR_FALSE, {}})
}

// ---------------------------------------------------------------------------
// Array and slice IR helpers
// ---------------------------------------------------------------------------


// A new `.len` for a header is within 0 ..= its cap (cap_val), or the
// program stops.
emit_slice_len_check :: proc(g: ^Codegen, cap_val, val: Val, span: Span) {

    w := SLICE_LEN_IR
    ok_label   := fresh_label(g, "slice_len.ok")
    fail_label := fresh_label(g, "slice_len.fail")

    neg_cmp := fresh_tmp(g)
    ir_icmp(g, neg_cmp, .Slt, w, val, ir_int(0))
    upper_cmp := fresh_tmp(g)
    ir_icmp(g, upper_cmp, .Sgt, w, val, cap_val)
    combined := fresh_tmp(g)
    ir_bin(g, combined, .Or, IR_I1, neg_cmp, upper_cmp)
    emit_cond_br(g, combined, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := span_location(span)
    loc_global := get_string_literal(g, loc)
    name_global := get_string_literal(g, "slice")
    ir_call(g, {}, IR_VOID, ir_global(__MARA_SLICE_LEN_FAIL), {IR_PTR, loc_global, {}}, {w, val, {}}, {w, cap_val, {}}, {IR_PTR, name_global, {}})
    ir_unreachable(g)

    emit_label(g, ok_label)
}

// ---------------------------------------------------------------------------
// Partial-array headers stamped over zero-filled storage
// ---------------------------------------------------------------------------


// Walk a zero-filled struct instance at `base_ptr` and stamp valid headers for
// every partial-array field, recursing into nested struct fields. Makes a
// struct *value* with partial-array fields usable straight out of zero-init —
// e.g. a function's named struct return, whose %sret the caller zero-filled.
// (A constructor stamps its own fields as it builds them.)
fixup_partial_array_fields :: proc(g: ^Codegen, base_ptr: Val, sd: ^Scope_Body) {
    st_llvm := ir_class_type(sd)
    for &f, i in sd.fields {
        ft := distinct_base(f.type_)
        #partial switch v in ft {
        case ^Type_Partial_Array:
            addr := fresh_tmp(g)
            emit_field_gep_into(g, addr, st_llvm, base_ptr, i)
            emit_partial_array_zero(g, addr, v, zero = false)
            was := mem_field(g, sd, &f)
            mem_probe_new(g, addr, v)
            mem_restore(g, was)
            gen_construct_partial_array_elements(g, addr, v)
        case ^Type_Fixed_Array:
            if type_needs_construction(g, v.elem) {
                addr := fresh_tmp(g)
                emit_field_gep_into(g, addr, st_llvm, base_ptr, i)
                gen_construct_elements(g, addr, v.elem, v.size)
            }
        case ^Type_Scope:
            if v.kind == .Struct {
                addr := fresh_tmp(g)
                emit_field_gep_into(g, addr, st_llvm, base_ptr, i)
                fixup_partial_array_fields(g, addr, &v.sd)
            }
        }
    }
}
