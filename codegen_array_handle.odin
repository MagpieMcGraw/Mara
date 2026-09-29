package mara

import "core:fmt"

// Array_Handle is the unified codegen view of "something array-shaped".
// Three storage shapes feed into it — fixed arrays (raw [N x T] alloca),
// slices (heap of {len, cap, ptr} header pointing at separate backing), and
// partial arrays (one alloca holding the header and inline storage together).
// Most operations on these shapes are identical once you have the right
// pointers in hand; the codegen used to branch by source-noun at every site
// and re-derive the same facts in each branch, which is where the
// print / cap bugs came from.
//
// Two pointers live on the handle:
//   header_ptr   — non-empty for slices and partial arrays; points at a
//                  `{len, cap, ptr}` header. Verbs load len/cap/data through
//                  this. Empty for fixed arrays.
//   fixed_alloca — non-empty for fixed arrays; the raw `[N x T]` alloca that
//                  is itself the data pointer. Empty for slices/partial
//                  arrays.
// Exactly one of the two is set on a valid handle.
//
// For fixed arrays, `static_cap` is the capacity (matching
// `Array_Var.capacity`). For slices and partial arrays, cap is held in the
// header and read at runtime — static_cap stays 0.
Array_Handle :: struct {
    header_ptr:     string,
    fixed_alloca:   string,
    elem_type:      string,
    static_cap:     int,
    static_cap_str: string, // SSA value of cap for VLA fixed arrays; "" otherwise
    is_utf8:        bool,
}

handle_is_fixed :: proc(h: ^Array_Handle) -> bool { return h.fixed_alloca != "" }

// Load (or compute) the current length of the array as an i64 SSA value.
// Fixed arrays don't have a separate len field — for them len == capacity.
emit_array_len :: proc(g: ^Codegen, h: ^Array_Handle) -> string {
    if handle_is_fixed(h) {
        if h.static_cap_str != "" { return h.static_cap_str }
        return fmt.tprintf("%d", h.static_cap)
    }
    len_gep := fresh_tmp(g)
    emit_slice_gep(g, len_gep, h.header_ptr, SLICE.len)
    out := fresh_tmp(g)
    emit_typed_load_len(g, out, len_gep)
    return out
}

// Return a ptr-typed SSA value pointing at the array's first element.
// For fixed arrays this is the alloca itself; for slices/partial arrays it
// is loaded from header.ptr.
emit_array_data :: proc(g: ^Codegen, h: ^Array_Handle) -> string {
    if handle_is_fixed(h) { return h.fixed_alloca }
    data_gep := fresh_tmp(g)
    emit_slice_gep(g, data_gep, h.header_ptr, SLICE.ptr)
    out := fresh_tmp(g)
    emit_load_into(g, out, "ptr", data_gep)
    return out
}

// Emit `printf("%.*s", len, data)` for a utf8 array. Bounded printing —
// works for fixed and dynamic storage. Callers should have already
// established that the handle is utf8.
emit_array_print :: proc(g: ^Codegen, h: ^Array_Handle) {
    fmt_name, fmt_len := get_string_literal(g, "%.*s")
    fmt_ptr := fresh_tmp(g)
    emit_string_gep(g, fmt_ptr, fmt_len, fmt_name)
    data_ptr := emit_array_data(g, h)
    // C's printf `%.*s` precision is an `int` (i32). emit_array_len returns the
    // value at the slice header width, so narrow it to i32 for the call when the
    // header is wider.
    len_val := emit_array_len(g, h)
    prec := len_val
    if slice_layout.len_ir != "i32" {
        prec = fresh_tmp(g)
        emit(g, "  %s = trunc %s %s to i32", prec, slice_layout.len_ir, len_val)
    }
    emit(g, "  call i32 (ptr, ...) @printf(ptr %s, i32 %s, ptr %s)", fmt_ptr, prec, data_ptr)
}
