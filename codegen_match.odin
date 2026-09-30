package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Match codegen (union type matching and value matching)
// ---------------------------------------------------------------------------

// A union value's tag, read from its storage. A tagged union keeps it in field
// 0. A niche union stores none — its storage is the Some variant's pointer — so
// its tag is whichever variant the pointer's nullness says it holds.
load_union_tag :: proc(g: ^Codegen, ut: ^Type_Union, union_ptr: string) -> string {
    tag_ir := union_tag_ir_type(ut)
    if is_niche_layout(g, ut) {
        some, none := niche_variants(g, ut)
        ptr := fresh_tmp(g)
        emit_load_into(g, ptr, "ptr", union_ptr)
        live := fresh_tmp(g)
        emit(g, "  %s = icmp ne ptr %s, null", live, ptr)
        tag := fresh_tmp(g)
        emit(g, "  %s = select i1 %s, %s %d, %s %d", tag, live,
             tag_ir, ut.tag_map[some], tag_ir, ut.tag_map[none])
        return tag
    }
    tag_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, union_llvm_name(ut.name), union_ptr)
    tag_val := fresh_tmp(g)
    emit_load_into(g, tag_val, tag_ir, tag_ptr)
    return tag_val
}

// A match's failure: its subject holds no arm's tag — corrupt memory, since
// every match covers every variant. `tag` (of IR type `tag_ir`) is reported.
emit_match_fail :: proc(g: ^Codegen, span: Span, tag, tag_ir: string, unsigned: bool) {
    wide := tag
    if tag_ir != "i64" {
        wide = fresh_tmp(g)
        emit(g, "  %s = %s %s %s to i64", wide, "zext" if unsigned else "sext", tag_ir, tag)
    }
    loc_global, _ := get_string_literal(g, span_location(span))
    emit(g, "  call void %s(ptr %s, i64 %s)", __MARA_MATCH_FAIL, loc_global, wide)
    emit(g, "  unreachable")
}

// Whether a union's tag is unsigned (`union(tag u32)`); the default i64 isn't.
union_tag_unsigned :: proc(ut: ^Type_Union) -> bool {
    return strings.has_prefix(ut.tag_type, "u")
}

// Whether a matched value is unsigned: an enum's declared tag type, a number's kind.
match_value_unsigned :: proc(t: Type) -> bool {
    #partial switch v in distinct_base(t) {
    case ^Type_Enum:   return strings.has_prefix(v.tag_type, "u")
    case Type_Numeric: return v.kind == .Unsigned
    case Type_Byte, Type_Utf8, Type_Bool: return true
    }
    return false
}
