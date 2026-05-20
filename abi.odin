package mara

// =============================================================================
// ABI calling convention and per-platform lowering.
//
// Two axes:
//   - Convention: .Mara (default) vs .C (cross-language boundary)
//   - Platform:   Linux (SysV AMD64), Windows (Win64), Web (wasm32)
//
// classify_arg / classify_ret are the entry points. They dispatch by
// convention, then (for .C) by platform.
//
// Phase 1: pure functions over `Type`. No callers yet — the codegen layers
// that consume Lowering live in later phases.
// =============================================================================

Calling_Conv :: enum { Mara, C }

// Target_OS is defined in type_checker.odin: { Windows, Linux, Mac }.
// macOS uses SysV AMD64 (same as Linux on x86-64).

// Per-eightbyte classification, SysV style. Win64 has no analogue —
// its rule is purely size-based.
ABI_Class :: enum { No_Class, Integer, SSE, Memory }

// How a single argument or return value crosses a function boundary.
// Direct: passed in registers, possibly decomposed into multiple parts.
// Indirect: passed by hidden pointer. For args: caller-allocates and passes
//   ptr (with `byval` IR attribute at emission time). For returns: callee
//   takes an extra `sret` ptr param and returns void.
Lowering :: union {
    Lowering_Direct,
    Lowering_Indirect,
}

Lowering_Direct :: struct {
    // LLVM IR types for each register slot — usually 1 entry (scalars,
    // small aggregates) but can be 2 for SysV when an aggregate spans
    // two eightbytes.
    parts: [dynamic]string,
}

Lowering_Indirect :: struct {
    // Carries no extra data; the IR shape is always `ptr` to the
    // original aggregate. The byval/sret attribute decision lives at
    // the IR emission site.
}

// -----------------------------------------------------------------------------
// Public entry points
// -----------------------------------------------------------------------------

classify_arg :: proc(t: Type, conv: Calling_Conv, os: Target_OS) -> Lowering {
    return classify(t, conv, os)
}

// Returns and args share classification rules on both SysV and Win64.
// IR emission differs (Indirect return → sret param + void; Indirect arg →
// byval ptr param), but the classifier itself doesn't care.
classify_ret :: proc(t: Type, conv: Calling_Conv, os: Target_OS) -> Lowering {
    return classify(t, conv, os)
}

classify :: proc(t: Type, conv: Calling_Conv, os: Target_OS) -> Lowering {
    switch conv {
    case .Mara: return classify_mara(t, os)
    case .C:    return classify_c(t, os)
    }
    return Lowering_Direct{}
}

// -----------------------------------------------------------------------------
// .Mara convention: everything by pointer / sret.
//
// Same on all platforms today. Per-platform branches are reserved here so
// that we can later specialize (e.g. pack small structs into registers on
// Linux for faster internal calls) without restructuring the dispatch.
// -----------------------------------------------------------------------------

classify_mara :: proc(t: Type, os: Target_OS) -> Lowering {
    switch os {
    case .Linux:   return classify_mara_uniform(t)
    case .Windows: return classify_mara_uniform(t)
    case .Mac:     return classify_mara_uniform(t)
    }
    return classify_mara_uniform(t)
}

classify_mara_uniform :: proc(t: Type) -> Lowering {
    if is_aggregate(t) {
        return Lowering_Indirect{}
    }
    return Lowering_Direct{parts = scalar_parts(t)}
}

// -----------------------------------------------------------------------------
// .C convention: platform dispatch.
// -----------------------------------------------------------------------------

classify_c :: proc(t: Type, os: Target_OS) -> Lowering {
    switch os {
    case .Linux:   return classify_sysv(t)
    case .Mac:     return classify_sysv(t)  // macOS on x86-64 uses SysV
    case .Windows: return classify_win64(t)
    }
    return Lowering_Direct{}
}

// -----------------------------------------------------------------------------
// Win64 (Microsoft x64): a struct passes in a register iff its size is
// exactly 1, 2, 4, or 8 bytes. Otherwise hidden pointer. Float / int
// classification doesn't apply — even all-float aggregates go through GP
// registers as integers carrying the bit pattern.
// -----------------------------------------------------------------------------

classify_win64 :: proc(t: Type) -> Lowering {
    if !is_aggregate(t) {
        return Lowering_Direct{parts = scalar_parts(t)}
    }
    size := checker_type_byte_size(t)
    switch size {
    case 1: return direct_single("i8")
    case 2: return direct_single("i16")
    case 4: return direct_single("i32")
    case 8: return direct_single("i64")
    }
    return Lowering_Indirect{}
}

// -----------------------------------------------------------------------------
// System V AMD64: aggregates > 16 bytes go by hidden pointer. ≤ 16 bytes
// are split into 8-byte chunks ("eightbytes"); each eightbyte is classified
// independently. If any eightbyte resolves to MEMORY, the whole aggregate
// spills to a hidden pointer.
// -----------------------------------------------------------------------------

classify_sysv :: proc(t: Type) -> Lowering {
    if !is_aggregate(t) {
        return Lowering_Direct{parts = scalar_parts(t)}
    }
    size := checker_type_byte_size(t)
    if size > 16 {
        return Lowering_Indirect{}
    }

    eb_count := (size + 7) / 8
    classes: [2]ABI_Class
    for i in 0..<eb_count {
        start  := i * 8
        length := min(8, size - start)
        classes[i] = classify_eightbyte_sysv(t, start, length)
    }

    // Merge: any MEMORY ⇒ whole aggregate is MEMORY.
    for i in 0..<eb_count {
        if classes[i] == .Memory {
            return Lowering_Indirect{}
        }
    }

    parts: [dynamic]string
    for i in 0..<eb_count {
        eb_size := min(8, size - i*8)
        ir := sysv_eightbyte_ir(classes[i], eb_size, t, i*8)
        append(&parts, ir)
    }
    return Lowering_Direct{parts = parts}
}

// Classify one eightbyte by walking every leaf field overlapping the range
// and merging classes per the SysV rules.
classify_eightbyte_sysv :: proc(t: Type, start, length: int) -> ABI_Class {
    cls := ABI_Class.No_Class
    walk_leaf_fields(t, start, length, 0, &cls)
    // An all-padding eightbyte is technically NO_CLASS, but ends up as
    // INTEGER in any well-formed lowering.
    if cls == .No_Class {
        return .Integer
    }
    return cls
}

// Walk every leaf (scalar) sub-field of `t` overlapping [start, start+length),
// merging each leaf's class into `cls^`. `base_offset` is the absolute offset
// of `t` within the original aggregate being classified.
walk_leaf_fields :: proc(t: Type, start, length: int, base_offset: int, cls: ^ABI_Class) {
    eb_end := start + length

    #partial switch v in t {
    case ^Type_Scope:
        if v.kind == .Struct {
            offset := base_offset
            for &f in v.fields {
                ft := f.type_
                a := type_alignment(ft)
                if a > 0 && offset % a != 0 {
                    offset += a - (offset % a)
                }
                fsize := checker_type_byte_size(ft)
                if offset < eb_end && offset + fsize > start {
                    walk_leaf_fields(ft, start, length, offset, cls)
                }
                offset += fsize
            }
            return
        }
    case ^Type_Fixed_Array:
        elem_size := checker_type_byte_size(v.elem)
        if elem_size == 0 { return }
        total := v.size
        if v.has_sentinel { total += 1 }
        for i in 0..<total {
            elem_off := base_offset + i * elem_size
            if elem_off >= eb_end { break }
            if elem_off + elem_size <= start { continue }
            walk_leaf_fields(v.elem, start, length, elem_off, cls)
        }
        return
    case ^Type_Distinct:
        walk_leaf_fields(v.base_type, start, length, base_offset, cls)
        return
    }

    // Leaf: classify this scalar and merge.
    leaf := classify_leaf(t)
    merge_class(cls, leaf)
}

classify_leaf :: proc(t: Type) -> ABI_Class {
    #partial switch v in t {
    case Type_F64, Type_Infer_Float:
        return .SSE
    case Type_Numeric:
        if v.kind == .Float { return .SSE }
        return .Integer
    case Type_Int, Type_Infer_Int, Type_Bool, Type_C8, Type_Utf8, Type_Byte,
         Type_CString, ^Type_Ptr, ^Type_Enum,
         Type_Const_Int, Type_Runtime_Size, Type_Any:
        return .Integer
    case ^Type_Slice, ^Type_Partial_Array, ^Type_Tuple, ^Type_Union:
        // These exceed an eightbyte on their own; landing here as a sub-field
        // of an aggregate ≤ 16 bytes shouldn't happen. Treat as MEMORY to
        // force the parent into the indirect path conservatively.
        return .Memory
    case ^Type_Scope:
        // Should be flattened by walk_leaf_fields before reaching here.
        return .Memory
    case ^Type_Fixed_Array:
        return .Memory
    case ^Type_Distinct:
        return classify_leaf(v.base_type)
    }
    return .No_Class
}

// SysV merge rules (without X87, which Mara doesn't have):
//   X        + X        = X
//   NO_CLASS + X        = X
//   MEMORY   + anything = MEMORY
//   INTEGER  + SSE      = INTEGER
//   SSE      + SSE      = SSE
merge_class :: proc(cls: ^ABI_Class, other: ABI_Class) {
    if cls^ == .Memory || other == .Memory { cls^ = .Memory; return }
    if cls^ == .No_Class { cls^ = other; return }
    if other == .No_Class { return }
    if cls^ == .Integer || other == .Integer { cls^ = .Integer; return }
    cls^ = .SSE
}

// Convert an eightbyte's class + occupied size to the IR type at the boundary.
sysv_eightbyte_ir :: proc(cls: ABI_Class, eb_size: int, t: Type, eb_start: int) -> string {
    switch cls {
    case .Integer:
        switch eb_size {
        case 1: return "i8"
        case 2: return "i16"
        case 4: return "i32"
        case 8: return "i64"
        }
        return "i64"
    case .SSE:
        return choose_sse_ir(t, eb_start, eb_size)
    case .Memory, .No_Class:
        return "i64" // unreachable in well-formed lowering
    }
    return "i64"
}

// Pick the SSE-class IR type for an eightbyte by inspecting its contents.
// Two contiguous floats → <2 x float>; one double → double; one float → float.
choose_sse_ir :: proc(t: Type, eb_start, eb_size: int) -> string {
    f_count, d_count := count_floats_doubles(t, eb_start, eb_size, 0)
    if d_count > 0 { return "double" }
    if f_count >= 2 { return "<2 x float>" }
    return "float"
}

count_floats_doubles :: proc(t: Type, start, length: int, base_offset: int) -> (floats, doubles: int) {
    eb_end := start + length

    #partial switch v in t {
    case ^Type_Scope:
        if v.kind == .Struct {
            offset := base_offset
            for &f in v.fields {
                ft := f.type_
                a := type_alignment(ft)
                if a > 0 && offset % a != 0 {
                    offset += a - (offset % a)
                }
                fsize := checker_type_byte_size(ft)
                if offset < eb_end && offset + fsize > start {
                    fc, dc := count_floats_doubles(ft, start, length, offset)
                    floats  += fc
                    doubles += dc
                }
                offset += fsize
            }
            return
        }
    case ^Type_Fixed_Array:
        elem_size := checker_type_byte_size(v.elem)
        if elem_size == 0 { return }
        total := v.size
        if v.has_sentinel { total += 1 }
        for i in 0..<total {
            elem_off := base_offset + i * elem_size
            if elem_off >= eb_end { break }
            if elem_off + elem_size <= start { continue }
            fc, dc := count_floats_doubles(v.elem, start, length, elem_off)
            floats  += fc
            doubles += dc
        }
        return
    case ^Type_Distinct:
        return count_floats_doubles(v.base_type, start, length, base_offset)
    }

    // Leaf
    #partial switch v in t {
    case Type_F64, Type_Infer_Float:
        doubles += 1
    case Type_Numeric:
        if v.kind == .Float {
            if v.bits == 32 { floats += 1 } else { doubles += 1 }
        }
    }
    return
}

// -----------------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------------

// True for types that need ABI classification at the .C boundary.
// Function-pointer Type_Scope (kind=.Fun) is NOT an aggregate — it's a ptr.
is_aggregate :: proc(t: Type) -> bool {
    #partial switch v in t {
    case ^Type_Scope:
        return v.kind == .Struct
    case ^Type_Fixed_Array, ^Type_Slice, ^Type_Partial_Array, ^Type_Tuple, ^Type_Union:
        return true
    case ^Type_Distinct:
        return is_aggregate(v.base_type)
    }
    return false
}

scalar_parts :: proc(t: Type) -> [dynamic]string {
    parts: [dynamic]string
    append(&parts, llvm_type_from_checker(t))
    return parts
}

direct_single :: proc(ir: string) -> Lowering {
    parts: [dynamic]string
    append(&parts, ir)
    return Lowering_Direct{parts = parts}
}

// Natural alignment for a checker type. Mirrors C/LLVM rules.
type_alignment :: proc(t: Type) -> int {
    #partial switch v in t {
    case Type_F64, Type_Infer_Float:
        return 8
    case Type_Numeric:
        if v.bits == 0 { return 8 }
        return v.bits / 8
    case Type_Int, Type_Infer_Int, ^Type_Ptr, Type_CString,
         Type_Const_Int, Type_Runtime_Size,
         ^Type_Union, ^Type_Tuple, Type_Any, Type_Error:
        return 8
    case Type_Bool, Type_C8, Type_Utf8, Type_Byte:
        return 1
    case ^Type_Slice, ^Type_Partial_Array:
        return 8
    case ^Type_Scope:
        if v.kind == .Struct {
            max_a := 1
            for &f in v.fields {
                a := type_alignment(f.type_)
                if a > max_a { max_a = a }
            }
            return max_a
        }
        return 8
    case ^Type_Fixed_Array:
        return type_alignment(v.elem)
    case ^Type_Enum:
        return checker_type_byte_size(t)
    case ^Type_Distinct:
        return type_alignment(v.base_type)
    }
    return 8
}
