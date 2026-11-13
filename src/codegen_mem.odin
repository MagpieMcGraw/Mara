package mara

import "core:fmt"
import "core:hash"
import "core:path/filepath"
import "core:strings"

// -profile memory: how full each partial array gets, told to the memory
// profiler (runtime/mara_mem.c) by its header's address. A partial array laid
// down (a declaration's zero, a constructor's field) is a new instance of its
// site; one copied in is the instance there, or a new one; a len written is
// looked at. The site — where its N is written, a local or a struct's field —
// is the context the code laying it down sets (g.mem_name, g.mem_where): a
// struct's fields set their own as they're stamped, so a struct anywhere
// counts at its fields.

// A partial array of type pa laid down at hdr: a new instance of the site in
// context (none: not told).
mem_probe_new :: proc(g: ^Codegen, hdr: Val, pa: ^Type_Partial_Array) {
    if !g.profile_memory || g.mem_name == "" { return }
    ir_call(g, {}, IR_VOID, ir_global("__mara_mem_new"), {IR_PTR, hdr, {}}, {IR_PTR, ir_global(mem_site(g, pa)), {}})
}

// A partial array of type pa copied in at hdr: the instance there, or a new
// one of the site in context (none: only one there already).
mem_probe_into :: proc(g: ^Codegen, hdr: Val, pa: ^Type_Partial_Array) {
    if !g.profile_memory { return }
    site := ir_global(mem_site(g, pa)) if g.mem_name != "" else IR_NULL
    ir_call(g, {}, IR_VOID, ir_global("__mara_mem_into"), {IR_PTR, hdr, {}}, {IR_PTR, site, {}})
}

// A value of type t handed out at ptr as it was, not laid down — next()'s
// slot (llvm_call): each list in it, through struct fields and fixed arrays'
// elements, a new instance of its site, its len there not counted (what was
// in the slot before). Nothing is written: the program sees what it would.
mem_probe_slot :: proc(g: ^Codegen, ptr: Val, t: Type) {
    if !g.profile_memory || !value_has_partial_array(g, t) { return }
    each :: proc(g: ^Codegen, ptr: Val, t: Type, _: []Ir_Arg) { mem_probe_slot(g, ptr, t) }
    base := distinct_base(t)
    if pa, is_pa := base.(^Type_Partial_Array); is_pa {
        if g.mem_name != "" {
            ir_call(g, {}, IR_VOID, ir_global("__mara_mem_slot"), {IR_PTR, ptr, {}}, {IR_PTR, ir_global(mem_site(g, pa)), {}})
        }
        return
    }
    if fa, is_fa := base.(^Type_Fixed_Array); is_fa {
        if fa.size > 0 {
            was := mem_elements(g)
            emit_each_element(g, ptr, fa.elem, fa.size, each)
            mem_restore(g, was)
        }
        return
    }
    sd := as_struct_body(base)
    if sd == nil { return }
    llvm_name := ir_class_type(sd)
    for &f, i in sd.fields {
        if !value_has_partial_array(g, f.type_) { continue }
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, llvm_name, ptr, i)
        was := mem_field(g, sd, &f)
        mem_probe_slot(g, gep, f.type_)
        mem_restore(g, was)
    }
}

// A len written at hdr: the instance there sees it.
mem_probe_len :: proc(g: ^Codegen, hdr: Val) {
    if !g.profile_memory { return }
    ir_call(g, {}, IR_VOID, ir_global("__mara_mem_len"), {IR_PTR, hdr, {}})
}

// A take, `slice([:n]T, storage)`, kept at hdr — a slice's header, its len
// first, its data where the storage is: a new instance of the site in
// context (a local, a struct's field), n its cap (0: the header's).
mem_probe_take :: proc(g: ^Codegen, hdr: Val, n: int, elem: Type) {
    if !g.profile_memory || g.mem_name == "" { return }
    ir_call(g, {}, IR_VOID, ir_global("__mara_mem_take"), {IR_PTR, hdr, {}}, {IR_PTR, ir_global(mem_site_sized(g, n, type_size(elem))), {}})
}

// The site in context's global for a partial array of type pa: its name,
// where it's written, its cap, its element's size, and the profiler's record
// (filled on first use). One per site per module.
mem_site :: proc(g: ^Codegen, pa: ^Type_Partial_Array) -> string {
    return mem_site_sized(g, pa.size, type_size(pa.elem))
}

// ... of `cap` elements of `elem_size` bytes (a take's too).
mem_site_sized :: proc(g: ^Codegen, cap: int, elem_size: int) -> string {
    key := fmt.tprintf("%s %s %d", g.mem_name, g.mem_where, cap)
    if sym, ok := g.mem_sites[key]; ok { return sym }
    keep := codegen_keep(g)
    // (Named by its site, with the emitter's prefix, as a string literal is:
    // the parallel codegens' globals in one module never meet.)
    sym := fmt.aprintf(".%smem.%016x", g.string_name_prefix, hash.fnv64a(transmute([]byte)key), allocator = keep)
    parts := make([]Ir_Const, 5, keep)
    parts[0] = ir_const(IR_PTR, get_string_literal(g, g.mem_name))
    parts[1] = ir_const(IR_PTR, get_string_literal(g, g.mem_where))
    parts[2] = ir_const(IR_I64, ir_int(cap))
    parts[3] = ir_const(IR_I64, ir_int(elem_size))
    parts[4] = ir_const(IR_PTR, IR_NULL)
    tys := [5]Ir_Type{IR_PTR, IR_PTR, IR_I64, IR_I64, IR_PTR}
    append(&g.globals, Ir_Global{name = sym, linkage = .Internal, ty = ir_struct_type(tys[:]), init = {kind = .Struct, parts = parts}})
    g.mem_sites[strings.clone(key, keep)] = sym
    return sym
}

// The site context, saved to put back (mem_restore).
Mem_Context :: struct { name, where_: string }

// The context set to a struct's field: `S.f`, where f is declared.
mem_field :: proc(g: ^Codegen, sd: ^Scope_Body, f: ^Struct_Type_Field) -> Mem_Context {
    was := Mem_Context{g.mem_name, g.mem_where}
    if !g.profile_memory { return was }
    owner := sd.source_name if sd.source_name != "" else sd.name
    g.mem_name = fmt.aprintf("%s.%s", owner, f.name, allocator = codegen_keep(g))
    g.mem_where = mem_token_where(g, f.decl)
    return was
}

// The context set to a local's declaration: `fun.name`, where it's declared.
mem_local :: proc(g: ^Codegen, fun_name, name: string, tok: Token_Id) -> Mem_Context {
    was := Mem_Context{g.mem_name, g.mem_where}
    if !g.profile_memory { return was }
    g.mem_name = fmt.aprintf("%s.%s", fun_name, name, allocator = codegen_keep(g))
    g.mem_where = mem_token_where(g, tok)
    return was
}

// The context set to the elements of what's in context: `name[]`.
mem_elements :: proc(g: ^Codegen) -> Mem_Context {
    was := Mem_Context{g.mem_name, g.mem_where}
    if !g.profile_memory || g.mem_name == "" { return was }
    g.mem_name = strings.concatenate({g.mem_name, "[]"}, codegen_keep(g))
    return was
}

// No site in context: what's copied in counts only where one's already there.
mem_none :: proc(g: ^Codegen) -> Mem_Context {
    was := Mem_Context{g.mem_name, g.mem_where}
    g.mem_name, g.mem_where = "", ""
    return was
}

mem_restore :: proc(g: ^Codegen, was: Mem_Context) {
    g.mem_name, g.mem_where = was.name, was.where_
}

// `file:line` of a token ("?" for none).
mem_token_where :: proc(g: ^Codegen, tok: Token_Id) -> string {
    if tok == 0 { return "?" }
    s := token_span(build_tokens[tok])
    return fmt.aprintf("%s:%d", filepath.base(span_file(s)), span_line(s), allocator = codegen_keep(g))
}
