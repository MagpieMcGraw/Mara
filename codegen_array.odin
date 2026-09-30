package mara

import "core:fmt"
import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// Slice IR helpers (emit_raw with strings.concatenate to avoid fmt brace issues)
// ---------------------------------------------------------------------------

// GEP into a slice header by field index — see SLICE constants (codegen.odin)
// for the canonical len/cap/ptr ordering.
emit_slice_gep :: proc(g: ^Codegen, result: string, src: string, field: int) {
    field_suffix := ", i32 0, i32 0"
    switch field {
    case 0: field_suffix = ", i32 0, i32 0"
    case 1: field_suffix = ", i32 0, i32 1"
    case 2: field_suffix = ", i32 0, i32 2"
    }
    emit_raw(g, strings.concatenate({"  ", result, " = getelementptr ", SLICE_IR_TYPE, ", ptr ", src, field_suffix}))
}

emit_slice_alloca :: proc(g: ^Codegen, result: string) {
    emit_raw(g, strings.concatenate({"  ", result, " = alloca ", SLICE_IR_TYPE}))
}

// Store an i64 value (SSA name or literal like "0", "42") into the slot
// addressed by `field_gep`, truncating to the layout's storage type if
// narrower than i64. The caller does the GEP and passes the result here;
// this lets sites that reuse the gep continue to do so.
// Store at the slice header's natural len/cap width. Caller must pass
// the value already at slice_layout.len_ir / cap_ir width. Integer
// literals are width-agnostic in IR so they pass through unchanged.
emit_typed_store_len :: proc(g: ^Codegen, val: string, field_gep: string) {
    emit_store(g, slice_layout.len_ir, val, field_gep)
}

emit_typed_store_cap :: proc(g: ^Codegen, val: string, field_gep: string) {
    emit_store(g, slice_layout.cap_ir, val, field_gep)
}

// Load len/cap from `field_gep` at natural width — no zext to i64.
// Callers operate at slice_layout.len_ir / cap_ir (today: i32). Sites
// that genuinely need a wider arithmetic context insert an explicit
// conversion at use rather than paying for the round-trip here.
emit_typed_load_len :: proc(g: ^Codegen, result: string, field_gep: string) {
    emit_load_into(g, result, slice_layout.len_ir, field_gep)
}

emit_typed_load_cap :: proc(g: ^Codegen, result: string, field_gep: string) {
    emit_load_into(g, result, slice_layout.cap_ir, field_gep)
}

// After a raw copy of a `t` value to `ptr`, point every partial array inside it
// — directly, in a struct field, in an array or partial-array slot, in a
// union's live variant — back at its own inline elements: the copied header
// still aims at the SOURCE's. Every copy of such a value goes through here (or
// emit_value_copy / partial_array_copy, which call it), so
// structs holding strings copy like any other value.
// A zeroed value of type `t` at `ptr` made a valid zero value: each partial
// array in it — through struct fields and array elements — gets its header
// (ptr → its elements, cap N), since a partial array's zero is not all zeros.
stamp_zero_partial_arrays :: proc(g: ^Codegen, ptr: string, t: Type) {
    base := distinct_base(t)
    if pa, is_pa := base.(^Type_Partial_Array); is_pa {
        stamp_partial_array_header(g, ptr, pa)
        return
    }
    // An array of partial arrays: each element. (An array of structs is
    // constructed next, which stamps them.)
    if fa, is_fa := base.(^Type_Fixed_Array); is_fa {
        inner := distinct_base(fa.elem)
        for a, nested := inner.(^Type_Fixed_Array); nested; a, nested = inner.(^Type_Fixed_Array) { inner = distinct_base(a.elem) }
        stamp :: proc(g: ^Codegen, ptr: string, t: Type, _: []string) { stamp_zero_partial_arrays(g, ptr, t) }
        if _, pa := inner.(^Type_Partial_Array); pa && fa.size > 0 { emit_each_element(g, ptr, fa.elem, fa.size, stamp) }
        return
    }
    sd := as_struct_body(base)
    if sd == nil { return }
    llvm_name := struct_llvm_name(struct_key(sd))
    for &f, i in sd.fields {
        if !value_has_partial_array(g, f.type_) { continue }
        #partial switch _ in distinct_base(f.type_) {
        case ^Type_Partial_Array, ^Type_Scope, ^Type_Fixed_Array:
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, ptr, i)
            stamp_zero_partial_arrays(g, gep, f.type_)
        }
    }
}

reanchor_partial_arrays :: proc(g: ^Codegen, t: Type, ptr: string) {
    if !value_has_partial_array(g, t) { return }
    base := distinct_base(t)
    if sd := as_struct_body(base); sd != nil {
        llvm_name := struct_llvm_name(struct_key(sd))
        for &f, i in sd.fields {
            if !value_has_partial_array(g, f.type_) { continue }
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, ptr, i)
            reanchor_partial_arrays(g, f.type_, gep)
        }
        return
    }
    #partial switch v in base {
    case ^Type_Partial_Array:
        elem_ir := llvm_type_from_checker(v.elem)
        ir_type := partial_array_ir_type(elem_ir, v.size)
        elements_ptr := fresh_tmp(g)
        emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
        ptr_gep := fresh_tmp(g)
        emit_slice_gep(g, ptr_gep, ptr, SLICE.ptr)
        emit_store(g, "ptr", elements_ptr, ptr_gep)
        if value_has_partial_array(g, v.elem) {
            reanchor_slots(g, v.elem, fmt.tprintf("[%d x %s]", v.size, elem_ir), elements_ptr, fmt.tprintf("%d", v.size))
        }
    case ^Type_Fixed_Array:
        arr_ir := fmt.tprintf("[%d x %s]", v.size, llvm_type_from_checker(v.elem))
        if v.size <= 4 {
            for i in 0..<v.size {
                gep := fresh_tmp(g)
                emit_array_gep_const(g, gep, arr_ir, ptr, i)
                reanchor_partial_arrays(g, v.elem, gep)
            }
        } else {
            reanchor_slots(g, v.elem, arr_ir, ptr, fmt.tprintf("%d", v.size))
        }
    case ^Type_Union:
        // Only the live variant's fields exist: dispatch on the tag.
        ukey := union_key(v)
        tag_ir := union_tag_ir_type(v)
        tag_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, union_llvm_name(ukey), ptr)
        tag := fresh_tmp(g)
        emit_load_into(g, tag, tag_ir, tag_ptr)
        for name in v.variants {
            vst, ok := lookup_struct(g, v.variant_structs[name] or_else name)
            if !ok || !value_has_partial_array(g, sd_type_scope(vst)) { continue }
            is_it := fresh_tmp(g)
            emit(g, "  %s = icmp eq %s %s, %d", is_it, tag_ir, tag, v.tag_map[name])
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
reanchor_slots :: proc(g: ^Codegen, elem: Type, arr_ir: string, base: string, count: string) {
    w := slice_layout.len_ir
    idx_ptr := fresh_tmp(g)
    emit_alloca(g, idx_ptr, w)
    emit_store(g, w, "0", idx_ptr)
    cond_label := fresh_label(g, "reanchor.cond")
    body_label := fresh_label(g, "reanchor.body")
    end_label := fresh_label(g, "reanchor.end")
    emit_br(g, cond_label)
    emit_label(g, cond_label)
    i := fresh_tmp(g)
    emit_load_into(g, i, w, idx_ptr)
    more := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %s", more, w, i, count)
    emit_cond_br(g, more, body_label, end_label)
    emit_label(g, body_label)
    gep := fresh_tmp(g)
    emit_array_gep_var(g, gep, arr_ir, base, i, w)
    reanchor_partial_arrays(g, elem, gep)
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, i)
    emit_store(g, w, next, idx_ptr)
    emit_br(g, cond_label)
    emit_label(g, end_label)
}

// Text into a fixed byte array: the array zeroed, then the text's bytes — the
// zeros past them end it. (Not its terminating zero: text that fills the array
// has no room for one; copying it wrote a byte past the array.)
emit_text_into_array :: proc(g: ^Codegen, dst: string, text: string, total_bytes: int) {
    if len(text) > total_bytes { codegen_fatal(g, {}, CODE_TEXT_LONGER_THAN_ARRAY, len(text), total_bytes) }
    if len(text) == 0 {
        emit_memset_zero(g, dst, total_bytes)
        return
    }
    global, n := get_string_literal(g, text)
    src := fresh_tmp(g)
    emit_string_gep(g, src, n, global)
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
            if vst, ok := lookup_struct(g, v.variant_structs[name] or_else name); ok && value_has_partial_array(g, sd_type_scope(vst)) {
                return true
            }
        }
    }
    return false
}

// Alloca a slice header (SLICE_IR_TYPE) and store data_ptr / len / cap into
// its fields. Returns the alloca ptr. Callers load from it to get the slice value.
emit_build_temp_slice :: proc(g: ^Codegen, data_ptr: string, len_val: string, cap_val: string) -> string {
    slice_alloca := fresh_tmp(g)
    emit_slice_alloca(g, slice_alloca)
    emit_slice_header_at(g, slice_alloca, data_ptr, len_val, cap_val)
    return slice_alloca
}

// A slice header's fields stored at `at`: ptr, len, cap.
emit_slice_header_at :: proc(g: ^Codegen, at: string, data_ptr: string, len_val: string, cap_val: string) {
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, at, SLICE.ptr)
    emit_store(g, "ptr", data_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, at, SLICE.len)
    emit_typed_store_len(g, len_val, len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, at, SLICE.cap)
    emit_typed_store_cap(g, cap_val, cap_gep)
}

// ---------------------------------------------------------------------------
// Array codegen
// ---------------------------------------------------------------------------

// If `expr` is a reference the checker resolved to a constant — bare `X`,
// `Module.X`, or `Self.X` — return the constant's value expression. The single
// place codegen turns a constant reference into its value, without re-resolving
// the name or knowing anything about module qualifiers (that was the checker's
// job). Used to substitute a constant RHS with its literal before materializing.
resolved_const_value :: proc(expr: Expr) -> (Expr, bool) {
    #partial switch e in expr {
    case ^Expr_Ident:
        if rc, ok := e.resolved.(Resolved_Constant); ok && rc.value_expr != nil { return rc.value_expr, true }
    case ^Expr_Field_Access:
        if rc, ok := e.resolved.(Resolved_Constant); ok && rc.value_expr != nil { return rc.value_expr, true }
    }
    return nil, false
}

// Like resolved_const_value, but also covers a scope-local constant (function-
// body `::`) — which the checker doesn't annotate (it's not a module constant),
// so it's still found by its unique name. Module constants always go through the
// annotation; the table is only consulted for an un-annotated local ident.
const_value_of :: proc(g: ^Codegen, expr: Expr) -> (Expr, bool) {
    if v, ok := resolved_const_value(expr); ok { return v, true }
    if ident, ok := expr.(^Expr_Ident); ok {
        if v, ok := g.checked.table.constants[ident.name]; ok { return v, true }
    }
    return nil, false
}

// ---------------------------------------------------------------------------
// Byte-buffer reinterpret codegen
//
// Covers []byte, [N]byte, and Array(byte, N). All three share the same shape:
//   1. Resolve the buffer to (data_ptr, cap_val)
//   2. Check offset + size <= cap
//   3. GEP by i8 at the offset, store/load sized by value type
// The only real difference between buffer kinds is step 1.
// ---------------------------------------------------------------------------

// The address of `count` elements of `size` bytes at byte `offset` of the
// buffer at data_ptr, cap_val bytes long — checked to lie within it.
emit_byte_count_ptr :: proc(g: ^Codegen, data_ptr, cap_val, offset, count: string, size: int, label: string) -> string {
    w := slice_layout.len_ir
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := emit_byte_span_outside(g, offset, count, cap_val, size)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    err_msg := fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%lld + %%lld > capacity %%lld\n", label)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    bytes := fresh_tmp(g)
    emit(g, "  %s = mul %s %s, %d", bytes, w, count, size)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s, %s %s)", err_ptr, w, offset, w, bytes, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok_lbl)

    elem_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", elem_ptr, data_ptr, w, offset)
    return elem_ptr
}

// Whether n elements of `size` bytes at byte offset off fall outside a
// buffer of cap_val bytes: off past the cap, or n more than fit in the room
// after it. Compared unsigned, a negative offset or count is outside too,
// and nothing wraps — no `off + n * size`, which let -1 + 4 through and a
// huge count's product wrap small. All at slice_layout.len_ir. The i1 is
// true when outside.
emit_byte_span_outside :: proc(g: ^Codegen, off, n, cap_val: string, size := 1) -> string {
    w := slice_layout.len_ir
    past := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", past, w, off, cap_val)
    room := fresh_tmp(g)
    emit(g, "  %s = sub %s %s, %s", room, w, cap_val, off)
    if size > 1 {
        fits := fresh_tmp(g)
        emit(g, "  %s = udiv %s %s, %d", fits, w, room, size)
        room = fits
    }
    over := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", over, w, n, room)
    outside := fresh_tmp(g)
    emit(g, "  %s = or i1 %s, %s", outside, past, over)
    return outside
}

// Bounds check for byte-buffer access at offset [low, low+size). Operates
// at slice_layout.len_ir — caller has already normalised low and cap_val
// to that width via emit_byte_offset_ptr / resolve_byte_target.
emit_byte_size_bounds_check :: proc(g: ^Codegen, cap_val: string, low: string, size: int, label: string) {
    w := slice_layout.len_ir
    ok_lbl := fresh_label(g, fmt.tprintf("byte.%s.ok", label))
    err_lbl := fresh_label(g, fmt.tprintf("byte.%s.err", label))
    cmp := emit_byte_span_outside(g, low, fmt.tprintf("%d", size), cap_val)
    emit_cond_br(g, cmp, err_lbl, ok_lbl)
    emit_label(g, err_lbl)
    err_msg := fmt.tprintf("runtime error: byte buffer %s out of bounds: offset %%lld + %d > capacity %%lld\n", label, size)
    err_name, err_len := get_string_literal(g, err_msg)
    err_ptr := fresh_tmp(g)
    emit_string_gep(g, err_ptr, err_len, err_name)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", err_ptr, w, low, w, cap_val)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, ok_lbl)
}

// A big-endian integer's value in the machine's order: its bytes swapped
// (an integer of 16 bits or more; anything else is itself).
emit_bswap_value :: proc(g: ^Codegen, val: string, t: Type) -> string {
    if !is_swappable_integer(t) { return val }
    bits := checker_type_byte_size(t) * 8
    if bits < 16 { return val }
    g.bswap_intrinsics[bits] = true
    swapped := fresh_tmp(g)
    emit(g, "  %s = call i%d @llvm.bswap.i%d(i%d %s)", swapped, bits, bits, bits, val)
    return swapped
}

// Big-endian byte-swap in place: walks `ty` rooted at `base_ptr` and emits
// llvm.bswap on every multi-byte integer leaf. Used by `#big_endian` byte-
// buffer reads after the load/memcpy.
//
// `base_ir_type` is the LLVM aggregate type at `base_ptr` (used for struct/
// array GEPs). For scalar leaves it's unused — the bit width comes from
// checker_type_byte_size.
//
// Skipped leaves: 1-byte primitives (byte/utf8/c8/u8/i8/bool — already in
// order); floats, pointers, slices, partial arrays (bswap is meaningless).
emit_bswap_in_place :: proc(g: ^Codegen, base_ptr: string, base_ir_type: string, ty: Type) {
    base := distinct_base(ty)

    if sd := as_struct_body(base); sd != nil {
        st_llvm := struct_llvm_name(struct_key(sd))
        for &f, idx in sd.fields {
            field_ir := field_ir_type(&f)
            field_gep := fresh_tmp(g)
            emit_field_gep_into(g, field_gep, st_llvm, base_ptr, idx)
            emit_bswap_in_place(g, field_gep, field_ir, f.type_)
        }
        return
    }

    if fa, ok := base.(^Type_Fixed_Array); ok {
        elem_bytes := checker_type_byte_size(fa.elem)
        if elem_bytes <= 1 { return }
        elem_ir := llvm_type_from_checker(fa.elem)
        // Bounded unroll: large fixed arrays (e.g. `[65536]u32` for a TTF loca
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
            count_str := fmt.tprintf("%d", fa.size)
            emit_partial_bswap_loop(g, elem0, count_str, fa.elem)
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
    bits := checker_type_byte_size(base) * 8
    if bits < 16 { return }
    intrinsic := fmt.tprintf("llvm.bswap.i%d", bits)
    g.bswap_intrinsics[bits] = true
    loaded := fresh_tmp(g)
    emit(g, "  %s = load i%d, ptr %s, align 1", loaded, bits, base_ptr)
    swapped := fresh_tmp(g)
    emit(g, "  %s = call i%d @%s(i%d %s)", swapped, bits, intrinsic, bits, loaded)
    emit(g, "  store i%d %s, ptr %s, align 1", bits, swapped, base_ptr)
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
// `[..N]Font` / `[N]str64` come up with field defaults un-applied and nested
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
// param defaults for a paramized constructor (mirrors the bare-decl path in
// gen_struct_assign) or just the sret pointer for a pure-data struct. No-op if
// the struct has no init function (trivial — the zero-fill already finished it).
// `args`: its constructor's arguments, typed ("i64 6"), the construction's
// (its params' defaults, which the checker built where it's written).
emit_struct_init_call :: proc(g: ^Codegen, st_name: string, addr: string, args: []string = nil) {
    init_fn, has_init := g.checked.functions[st_name]
    if !has_init { return }
    if init_fn != nil && len(init_fn.cg_params) > 0 {
        if len(args) != len(init_fn.cg_params) {
            codegen_fatal(g, {}, CODE_BARE_CONSTRUCTION_ARGUMENT, st_name, init_fn.cg_params[len(args) if len(args) < len(init_fn.cg_params) else 0].name)
        }
        arg_strs := make([dynamic]string, 0, len(args) + 1, context.temp_allocator)
        append(&arg_strs, ..args)
        append(&arg_strs, fmt.tprintf("ptr %s", addr))
        emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st_name), "(", strings.join(arg_strs[:], ", "), ")"}))
    } else {
        emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st_name), "(ptr ", addr, ")"}))
    }
}

// Construct the value of type `t` at the already-zeroed slot `ptr`: call its
// auto-init (struct), stamp its header + construct its inline elements (partial
// array), or construct each element (fixed array). Mutually recursive with
// gen_construct_elements.
gen_construct_value_at :: proc(g: ^Codegen, ptr: string, t: Type, args: []string = nil) {
    bt := distinct_base(t)
    #partial switch v in bt {
    case ^Type_Scope:
        if v.kind == .Struct {
            emit_struct_init_call(g, v.name, ptr, args)
        }
    case ^Type_Partial_Array:
        stamp_partial_array_header(g, ptr, v)
        gen_construct_partial_array_elements(g, ptr, v, args)
    case ^Type_Fixed_Array:
        gen_construct_elements(g, ptr, v.elem, v.size, args)
    }
}

// Construct each inline element of a (already header-stamped) partial array at
// `pa_addr`. Skipped entirely when the element type is trivially zero-formed.
gen_construct_partial_array_elements :: proc(g: ^Codegen, pa_addr: string, pa: ^Type_Partial_Array, args: []string = nil) {
    if !type_needs_construction(g, pa.elem) { return }
    elem_ir := llvm_type_from_checker(pa.elem)
    pa_ir := partial_array_ir_type(elem_ir, pa.size)
    inline_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", inline_ptr, " = getelementptr inbounds ", pa_ir, ", ptr ", pa_addr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    gen_construct_elements(g, inline_ptr, pa.elem, pa.size, args)
}

// Run no-arg construction over `count` elements starting at `elements_ptr` (a
// pointer to element 0), but only when the element type needs it.
gen_construct_elements :: proc(g: ^Codegen, elements_ptr: string, elem: Type, count: int, args: []string = nil) {
    if count <= 0 { return }
    if !type_needs_construction(g, elem) { return }
    emit_each_element(g, elements_ptr, elem, count, gen_construct_value_at, args)
}

// `each` over `count` elements of type `elem` starting at `elements_ptr` (a
// pointer to element 0): a runtime counted loop, so `[..256]Font` is a
// handful of instructions, not 256 unrolled ones.
emit_each_element :: proc(g: ^Codegen, elements_ptr: string, elem: Type, count: int, each: proc(g: ^Codegen, ptr: string, t: Type, args: []string), args: []string = nil) {
    elem_ir := llvm_type_from_checker(elem)
    w := slice_layout.len_ir
    cond_label := fresh_label(g, "ctor.cond")
    body_label := fresh_label(g, "ctor.body")
    end_label  := fresh_label(g, "ctor.end")

    idx_ptr := fresh_tmp(g)
    emit_alloca(g, idx_ptr, w)
    emit_store(g, w, "0", idx_ptr)
    emit_br(g, cond_label)

    emit_label(g, cond_label)
    idx := fresh_tmp(g)
    emit_load_into(g, idx, w, idx_ptr)
    cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, %d", cmp, w, idx, count)
    emit_cond_br(g, cmp, body_label, end_label)

    emit_label(g, body_label)
    idx2 := fresh_tmp(g)
    emit_load_into(g, idx2, w, idx_ptr)
    elem_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, %s %s", elem_ptr, elem_ir, elements_ptr, w, idx2)
    each(g, elem_ptr, elem, args)
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, idx2)
    emit_store(g, w, next, idx_ptr)
    emit_br(g, cond_label)

    emit_label(g, end_label)
}

// emit_partial_array_storage binds the SSA name `dst` to a partial array's
// { ptr, len, cap, [N x elem] } storage. This is the ONE place the stack-vs-
// arena decision is made for PA storage, so it can't drift between the decl
// path and the byte-read path (it did: the byte-read path used to always
// alloca).
//
// Big PAs (routes_to_arena: whole-struct bytes >= ARENA_THRESHOLD) bump the
// struct from the scope arena. There's deliberately no `context_enabled` gate:
// the type checker (check_storage_sizes) already rejects a big value with no
// allocator, so a big PA reaching codegen has one — and if some path slips past
// the guard (e.g. a comptime `#if` arm), emit_arena_bump fatals, the loud
// backstop, instead of silently putting a big buffer on the stack. Small PAs
// get a stack alloca; i8 backings are over-aligned to 16 to match the
// take()/byte-fill alignment policy.
// A partial array's zero value at `addr`: its elements zeroed (`zero`), and
// its header over them (`stamp`) — ptr → the elements, len 0, cap N. Returns
// the elements' address.
emit_partial_array_zero :: proc(g: ^Codegen, addr: string, pa: ^Type_Partial_Array, stamp := true, zero := true) -> string {
    elem_t := llvm_type_from_checker(pa.elem)
    ir_type := partial_array_ir_type(elem_t, pa.size)
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", addr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    if !stamp { return elements_ptr }
    if zero { emit_memset_zero(g, elements_ptr, pa.size * elem_byte_size(elem_t, g.checked)) }
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, addr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, addr, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, addr, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", pa.size), cap_gep)
    return elements_ptr
}

// Initialize a partial-array slot in place AND populate its inline elements
// from a byte-buffer span. Used by both the standalone-decl path (after
// `alloca`) and the field-assign path (slot_ptr is the field's GEP).
// Handles the header init (.ptr → elements, .len = count, .cap = N), the
// byte-span memcpy into the elements area, and optional `#big_endian`
// per-element bswap. Runtime checks: the span lies within the source's
// src_cap bytes (it read past them), source bytes is divisible by elem
// size, and produces count <= cap. The slice-range inverted-bounds check
// lives in the Expr_Slice entry — the Expr_Index entry uses a static byte
// count that can't be negative.
gen_partial_array_byte_fill_at_core :: proc(g: ^Codegen, slot_ptr: string, pa: ^Type_Partial_Array,
                                             src_data_ptr, src_cap, src_low, src_bytes: string,
                                             is_big_endian: bool, span: Span) {
    elem_t := llvm_type_from_checker(pa.elem)
    cap_n := pa.size
    alloc_cap := cap_n
    ir_type := partial_array_ir_type(elem_t, alloc_cap)
    elem_bytes := elem_byte_size(elem_t, g.checked)

    // Initialise header: ptr → elements, len → 0 (auto-add at the end),
    // cap → N. Mirrors the literal init helper.
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", slot_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, slot_ptr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, slot_ptr, SLICE.len)
    emit_typed_store_len(g, "0", len_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, slot_ptr, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)

    w := slice_layout.len_ir

    // Runtime check 0: the span within the source buffer.
    src_ok := fresh_label(g, "byte.view.ok")
    src_err := fresh_label(g, "byte.view.err")
    emit_cond_br(g, emit_byte_span_outside(g, src_low, src_bytes, src_cap), src_err, src_ok)
    emit_label(g, src_err)
    src_global, src_len := get_string_literal(g, "runtime error: byte buffer view out of bounds: offset %lld + %lld > capacity %lld\n")
    src_msg := fresh_tmp(g)
    emit_string_gep(g, src_msg, src_len, src_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s, %s %s)", src_msg, w, src_low, w, src_bytes, w, src_cap)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, src_ok)

    // Runtime check 1: src_bytes % elem_bytes == 0.
    rem := fresh_tmp(g)
    emit(g, "  %s = urem %s %s, %d", rem, w, src_bytes, elem_bytes)
    rem_ok := fresh_label(g, "pa.div.ok")
    rem_err := fresh_label(g, "pa.div.err")
    rem_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ne %s %s, 0", rem_cmp, w, rem)
    emit_cond_br(g, rem_cmp, rem_err, rem_ok)
    emit_label(g, rem_err)
    rem_msg := fmt.tprintf("runtime error: partial-array byte read at offset %%d: %%d bytes not divisible by elem size %d\n", elem_bytes)
    rem_global, rem_byte_len := get_string_literal(g, rem_msg)
    rem_ptr := fresh_tmp(g)
    emit_string_gep(g, rem_ptr, rem_byte_len, rem_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", rem_ptr, w, src_low, w, src_bytes)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, rem_ok)

    // count = src_bytes / elem_bytes.
    count := fresh_tmp(g)
    emit(g, "  %s = udiv %s %s, %d", count, w, src_bytes, elem_bytes)

    // Runtime check 2: count <= cap.
    cap_str := fmt.tprintf("%d", cap_n)
    cap_ok := fresh_label(g, "pa.cap.ok")
    cap_err := fresh_label(g, "pa.cap.err")
    cap_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp ugt %s %s, %s", cap_cmp, w, count, cap_str)
    emit_cond_br(g, cap_cmp, cap_err, cap_ok)
    emit_label(g, cap_err)
    cap_msg := fmt.tprintf("runtime error: partial-array byte read at offset %%d: produced %%d elements, exceeds cap %d\n", cap_n)
    cap_global, cap_byte_len := get_string_literal(g, cap_msg)
    cap_msg_ptr := fresh_tmp(g)
    emit_string_gep(g, cap_msg_ptr, cap_byte_len, cap_global)
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, %s %s, %s %s)", cap_msg_ptr, w, src_low, w, count)
    emit(g, "  call void @exit(i32 1)")
    emit(g, "  unreachable")
    emit_label(g, cap_ok)

    // memcpy(elements_ptr, src_data_ptr + src_low, src_bytes).
    src_offset_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr i8, ptr %s, %s %s", src_offset_ptr, src_data_ptr, w, src_low)
    emit_memcpy_runtime(g, elements_ptr, src_offset_ptr, src_bytes)

    // `#big_endian` decorator on the source: byte-swap each element in
    // place. Count is runtime, so we emit a counter-driven loop wrapping the
    // per-element bswap.
    if is_big_endian {
        emit_partial_bswap_loop(g, elements_ptr, count, pa.elem)
    }

    // Auto-add to len. For a fresh decl this is + 0, so the final len = count.
    cur_len := fresh_tmp(g)
    emit_typed_load_len(g, cur_len, len_gep)
    new_len := fresh_tmp(g)
    emit(g, "  %s = add %s %s, %s", new_len, w, cur_len, count)
    emit_typed_store_len(g, new_len, len_gep)
}

// Counter-driven loop that calls emit_bswap_in_place on each of `count`
// elements rooted at `elements_ptr`. Count is an SSA value at slice-header
// width. Used by `#big_endian` on partial-array reads — the count is only
// known at runtime, so the per-element swap can't be unrolled.
//
// If `elem_ty` contains no multi-byte integer leaves (e.g. `[..N]byte`), the
// inner body is a no-op and an optimizer will see through it — but skip the
// loop entirely as a cheap source-level guard.
emit_partial_bswap_loop :: proc(g: ^Codegen, elements_ptr: string, count: string, elem_ty: Type) {
    if !type_has_swappable_leaf(elem_ty) { return }

    w := slice_layout.len_ir
    elem_ir := llvm_type_from_checker(elem_ty)
    idx_slot := fresh_tmp(g)
    emit(g, "  %s = alloca %s", idx_slot, w)
    emit_typed_store_len(g, "0", idx_slot)
    loop_lbl := fresh_label(g, "bswap.loop")
    body_lbl := fresh_label(g, "bswap.body")
    end_lbl  := fresh_label(g, "bswap.end")
    emit(g, "  br label %%%s", loop_lbl)
    emit_label(g, loop_lbl)
    cur := fresh_tmp(g)
    emit_typed_load_len(g, cur, idx_slot)
    done := fresh_tmp(g)
    emit(g, "  %s = icmp uge %s %s, %s", done, w, cur, count)
    emit_cond_br(g, done, end_lbl, body_lbl)
    emit_label(g, body_lbl)
    elem_gep := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, %s %s", elem_gep, elem_ir, elements_ptr, w, cur)
    emit_bswap_in_place(g, elem_gep, elem_ir, elem_ty)
    next := fresh_tmp(g)
    emit(g, "  %s = add %s %s, 1", next, w, cur)
    emit_typed_store_len(g, next, idx_slot)
    emit(g, "  br label %%%s", loop_lbl)
    emit_label(g, end_lbl)
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
    return checker_type_byte_size(base) >= 2
}

// Runtime-sized memcpy. Used when the byte count is an SSA value, not a
// compile-time literal — e.g. partial-array byte-buffer reads where the
// source span size is computed from runtime slice bounds. `bytes` is at
// slice header width (i32); the memcpy intrinsic takes i64, so we zext.
emit_memcpy_runtime :: proc(g: ^Codegen, dst, src, bytes: string) {
    w := slice_layout.len_ir
    n64 := bytes
    if w != "i64" {
        n64 = fresh_tmp(g)
        emit(g, "  %s = zext %s %s to i64", n64, w, bytes)
    }
    emit(g, "  call void @llvm.memcpy.p0.p0.i64(ptr %s, ptr %s, i64 %s, i1 false)", dst, src, n64)
}

// ---------------------------------------------------------------------------
// Array and slice IR helpers
// ---------------------------------------------------------------------------

// Parse an LLVM array type string like "[512 x i1]" into capacity and element type.
parse_array_ir_type :: proc(ir_type: string) -> (cap: int, elem: string, ok: bool) {
    if !strings.has_prefix(ir_type, "[") { return 0, "", false }
    rest := ir_type[1:]  // "512 x i1]"
    x_idx := strings.index(rest, " x ")
    if x_idx < 0 { return 0, "", false }
    cap_str := rest[:x_idx]
    elem_str := strings.trim_right(rest[x_idx+3:], "]")
    n, n_ok := strconv.parse_int(cap_str)
    if !n_ok { return 0, "", false }
    return n, elem_str, true
}

// If `t` is a sized-slice type (distinct alias wrapping a slice with a default
// cap, e.g. `String :: type([, 0]utf8(128))`), return (cap_n, slice, true).
sized_slice_info :: proc(g: ^Codegen, t: Type) -> (int, ^Type_Slice, bool) {
    dt, is_distinct := t.(^Type_Distinct)
    if !is_distinct { return 0, nil, false }
    sl, is_slice := dt.base_type.(^Type_Slice)
    if !is_slice { return 0, nil, false }
    if dt.default_cap_expr == nil { return 0, nil, false }
    n, n_ok := codegen_const_eval_int(g, dt.default_cap_expr)
    if !n_ok { return 0, nil, false }
    return n, sl, true
}

// A new `.len` for the slice header at `hdr` is within 0 ..= its cap, or the
// program stops.
emit_slice_len_check :: proc(g: ^Codegen, hdr, val: string, span: Span) {
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, hdr, SLICE.cap)
    cap_val := fresh_tmp(g)
    emit_typed_load_cap(g, cap_val, cap_gep)

    w := slice_layout.len_ir
    ok_label   := fresh_label(g, "slice_len.ok")
    fail_label := fresh_label(g, "slice_len.fail")

    neg_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp slt %s %s, 0", neg_cmp, w, val)
    upper_cmp := fresh_tmp(g)
    emit(g, "  %s = icmp sgt %s %s, %s", upper_cmp, w, val, cap_val)
    combined := fresh_tmp(g)
    emit(g, "  %s = or i1 %s, %s", combined, neg_cmp, upper_cmp)
    emit_cond_br(g, combined, fail_label, ok_label)

    emit_label(g, fail_label)
    loc := format_location(span.file, span.line, span.col)
    loc_global,  _ := get_string_literal(g, loc)
    name_global, _ := get_string_literal(g, "slice")
    emit(g, "  call void %s(ptr %s, %s %s, %s %s, ptr %s)",
        __MARA_SLICE_LEN_FAIL, loc_global, w, val, w, cap_val, name_global)
    emit(g, "  unreachable")

    emit_label(g, ok_label)
}
