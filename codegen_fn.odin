package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Function definition codegen
// ---------------------------------------------------------------------------

// Stamp a valid partial-array header at `addr` over a zero-filled slot:
// ptr → &inline elements, cap = N. A flat zero-fill leaves cap=0 / ptr=null —
// an unusable partial array, even though the static capacity is right there in
// the type. `len` is left as the zero-fill set it (0).
stamp_partial_array_header :: proc(g: ^Codegen, addr: string, v: ^Type_Partial_Array) {
    elem_t := llvm_type_from_checker(v.elem)
    ir_type := partial_array_ir_type(elem_t, v.size)
    elements_ptr := fresh_tmp(g)
    emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", addr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
    ptr_gep := fresh_tmp(g)
    emit_slice_gep(g, ptr_gep, addr, SLICE.ptr)
    emit_store(g, "ptr", elements_ptr, ptr_gep)
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, addr, SLICE.cap)
    emit_typed_store_cap(g, fmt.tprintf("%d", v.size), cap_gep)
}

// Walk a zero-filled struct instance at `base_ptr` and stamp valid headers for
// every partial-array field, recursing into nested struct fields. Makes a
// struct *value* with partial-array fields usable straight out of zero-init —
// e.g. a function's named struct return, whose %sret the caller zero-filled.
// The constructor path binds field names AND stamps (via prebind_field_var);
// this is the stamp-only half, for non-constructor struct returns.
fixup_partial_array_fields :: proc(g: ^Codegen, base_ptr: string, sd: ^Scope_Body) {
    st_llvm := struct_llvm_name(sd.name)
    for &f, i in sd.fields {
        ft := distinct_base(f.type_)
        #partial switch v in ft {
        case ^Type_Partial_Array:
            addr := fresh_tmp(g)
            emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", addr, st_llvm, base_ptr, i)
            stamp_partial_array_header(g, addr, v)
            gen_construct_partial_array_elements(g, addr, v)
        case ^Type_Fixed_Array:
            if type_needs_construction(g, v.elem) {
                addr := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", addr, st_llvm, base_ptr, i)
                gen_construct_elements(g, addr, v.elem, v.size)
            }
        case ^Type_Scope:
            if v.kind == .Struct {
                addr := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", addr, st_llvm, base_ptr, i)
                fixup_partial_array_fields(g, addr, &v.sd)
            }
        }
    }
}
