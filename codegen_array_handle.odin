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

// Build a handle for an array-shaped expression. Mirrors the resolution
// branches that were previously open-coded at every call site: ident lookup
// (local array or slice var), field access (walks the address chain through
// gen_field_access then claims the result), and Expr_String literals (treated
// as fixed utf8 arrays pointing at the literal's global).
//
// CAVEAT: for field-access expressions this calls gen_field_access, which
// emits the chain. Callers must not also resolve the same expression
// elsewhere — the IR would be emitted twice. Practical guideline: call
// resolve_array_handle once per expression argument, then operate on the
// handle.
resolve_array_handle :: proc(g: ^Codegen, expr: Expr) -> (Array_Handle, bool) {
    if ident, ok := expr.(^Expr_Ident); ok {
        if av, av_ok := get_array(g, ident.name); av_ok {
            return array_handle_from_array_var(&av), true
        }
        if sv, sv_ok := get_slice(g, ident.name); sv_ok {
            return array_handle_from_slice_var(&sv), true
        }
    }
    if fa, ok := expr.(^Expr_Field_Access); ok {
        gen_field_access(g, fa)
        if av, av_ok := claim_field_array(g); av_ok {
            return array_handle_from_array_var(&av), true
        }
        if sv, sv_ok := claim_field_slice(g); sv_ok {
            return array_handle_from_slice_var(&sv), true
        }
    }
    if lit, ok := expr.(^Expr_String); ok {
        // Mint a fixed-array handle pointing at the literal's data. The
        // global is emitted with a trailing \0 (for free literal→cstring
        // conversion), and `static_cap` is the byte length of the string
        // body — verbs that bound by len see exactly the literal's content.
        name, _ := get_string_literal(g, lit.value)
        data_ptr := fresh_tmp(g)
        emit_string_gep(g, data_ptr, len(lit.value)+1, name)
        return Array_Handle{
            fixed_alloca = data_ptr,
            elem_type    = "i8",
            static_cap   = len(lit.value),
            is_utf8      = true,
        }, true
    }
    return {}, false
}

array_handle_from_array_var :: proc(av: ^Array_Var) -> Array_Handle {
    return Array_Handle{
        fixed_alloca   = av.alloca,
        elem_type      = av.elem_type,
        static_cap     = av.capacity,
        static_cap_str = av.capacity_val,
        is_utf8        = av.is_utf8,
    }
}

array_handle_from_slice_var :: proc(sv: ^Slice_Var) -> Array_Handle {
    return Array_Handle{
        header_ptr = sv.alloca,
        elem_type  = sv.elem_type,
        is_utf8    = sv.is_utf8,
    }
}

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

// Load (or compute) the capacity at the slice header's natural width
// (slice_layout.cap_ir).
emit_array_raw_cap :: proc(g: ^Codegen, h: ^Array_Handle) -> string {
    if handle_is_fixed(h) {
        if h.static_cap_str != "" { return h.static_cap_str }
        return fmt.tprintf("%d", h.static_cap)
    }
    cap_gep := fresh_tmp(g)
    emit_slice_gep(g, cap_gep, h.header_ptr, SLICE.cap)
    out := fresh_tmp(g)
    emit_typed_load_cap(g, out, cap_gep)
    return out
}

// User-facing capacity. Identical to emit_array_raw_cap since sentinel
// types (and their hidden reserved slot) were removed; kept as a separate
// name because call sites express intent ("bound user writes") with it.
emit_array_cap_user :: proc(g: ^Codegen, h: ^Array_Handle) -> string {
    return emit_array_raw_cap(g, h)
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
