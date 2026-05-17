package mara

import "core:strings"
import "core:strconv"

// LLVM intrinsic registry.
//
// Mara surface syntax: `name :: fun(...) -> T { @llvm.<op>.<suffix> }`.
// The body string is parsed once at type-check time, validated against the
// declared signature using the registry below, and stored on the
// Checked_Scope. Codegen reads the stored name verbatim to emit the call,
// so the registry below is the single source of truth for "which LLVM
// intrinsics may appear in a Mara intrinsic body."
//
// Adding a new intrinsic = one line in `llvm_intrinsic_specs`. No codegen
// edits.

LLVM_Type_Rule :: enum {
    Match_Float_Suffix,      // suffix = f32/f64; all params and return must match that float
    Match_Signed_Int_Suffix, // suffix = iN (8/16/32/64); all params and return must match that signed int
}

LLVM_Intrinsic_Spec :: struct {
    op:    string,
    arity: int,
    rule:  LLVM_Type_Rule,
}

llvm_intrinsic_specs := []LLVM_Intrinsic_Spec{
    {"sqrt",   1, .Match_Float_Suffix},
    {"sin",    1, .Match_Float_Suffix},
    {"cos",    1, .Match_Float_Suffix},
    {"fabs",   1, .Match_Float_Suffix},
    {"pow",    2, .Match_Float_Suffix},
    {"minnum", 2, .Match_Float_Suffix},
    {"maxnum", 2, .Match_Float_Suffix},
    {"smin",   2, .Match_Signed_Int_Suffix},
    {"smax",   2, .Match_Signed_Int_Suffix},
}

find_llvm_intrinsic_spec :: proc(op: string) -> (LLVM_Intrinsic_Spec, bool) {
    for spec in llvm_intrinsic_specs {
        if spec.op == op { return spec, true }
    }
    return {}, false
}

// Map a type suffix like "f32" / "i64" to the Mara Type it implies.
// Returns ok=false if the suffix is malformed.
type_from_llvm_suffix :: proc(suffix: string) -> (Type, bool) {
    switch suffix {
    case "f32": return Type_Numeric{kind = .Float, bits = 32}, true
    case "f64": return Type_F64{}, true
    case "i64": return Type_Int{}, true
    case "i32": return Type_Numeric{kind = .Signed, bits = 32}, true
    case "i16": return Type_Numeric{kind = .Signed, bits = 16}, true
    case "i8":  return Type_Numeric{kind = .Signed, bits = 8}, true
    }
    return nil, false
}

// Split "llvm.sqrt.f32" into ("sqrt", "f32"). Returns ok=false if the name
// doesn't have the `llvm.<op>.<suffix>` shape.
parse_llvm_intrinsic_name :: proc(name: string) -> (op: string, suffix: string, ok: bool) {
    if !strings.has_prefix(name, "llvm.") { return "", "", false }
    rest := name[len("llvm."):]
    dot := strings.index_byte(rest, '.')
    if dot < 0 { return "", "", false }
    op = rest[:dot]
    suffix = rest[dot+1:]
    if op == "" || suffix == "" { return "", "", false }
    return op, suffix, true
}

// suffix_is_signed_int reports whether "iN" is a recognised signed-int suffix.
suffix_is_signed_int :: proc(suffix: string) -> bool {
    if len(suffix) < 2 || suffix[0] != 'i' { return false }
    n, ok := strconv.parse_int(suffix[1:])
    if !ok { return false }
    return n == 8 || n == 16 || n == 32 || n == 64
}

suffix_is_float :: proc(suffix: string) -> bool {
    return suffix == "f32" || suffix == "f64"
}

// Validate that a function declared as `{ @llvm.<op>.<suffix> }` matches the
// LLVM intrinsic's expected shape: known op, correct arity, and all
// param/return types match the suffix per the op's type rule.
//
// On error, calls check_error and returns false. Returns true on success.
check_llvm_intrinsic_signature :: proc(c: ^Checker, ft: ^Type_Scope, name: string, span: Span) -> bool {
    op, suffix, parsed_ok := parse_llvm_intrinsic_name(name)
    if !parsed_ok {
        check_error(c, span, "intrinsic body must be `@llvm.<op>.<type>` (got `@%s`)", name)
        return false
    }

    spec, spec_ok := find_llvm_intrinsic_spec(op)
    if !spec_ok {
        check_error(c, span, "unknown LLVM intrinsic `@%s` — no `%s` in the registry", name, op)
        return false
    }

    if len(ft.params) != spec.arity {
        check_error(c, span, "intrinsic `@%s` takes %d argument%s, but the function declares %d",
            name, spec.arity, spec.arity == 1 ? "" : "s", len(ft.params))
        return false
    }

    expected_type, suffix_ok := type_from_llvm_suffix(suffix)
    if !suffix_ok {
        check_error(c, span, "intrinsic `@%s` has unrecognised type suffix `%s`", name, suffix)
        return false
    }

    switch spec.rule {
    case .Match_Float_Suffix:
        if !suffix_is_float(suffix) {
            check_error(c, span, "intrinsic `@%s` requires a float type suffix (f32/f64), got `%s`", name, suffix)
            return false
        }
    case .Match_Signed_Int_Suffix:
        if !suffix_is_signed_int(suffix) {
            check_error(c, span, "intrinsic `@%s` requires a signed integer type suffix (i8/i16/i32/i64), got `%s`", name, suffix)
            return false
        }
    }

    for p, i in ft.params {
        if !types_equal(distinct_base(p.type_), expected_type) {
            check_error(c, span, "intrinsic `@%s` expects param %d to be `%s`, got `%s`",
                name, i, type_name(expected_type), type_name(p.type_))
            return false
        }
    }

    if !types_equal(distinct_base(ft.return_type), expected_type) {
        check_error(c, span, "intrinsic `@%s` expects return type `%s`, got `%s`",
            name, type_name(expected_type), type_name(ft.return_type))
        return false
    }

    return true
}
