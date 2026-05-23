package mara

// All compiler diagnostics — errors and warnings — live in this file.
// Call sites reference these constants; edits to wording happen here only.
//
// Each constant is the **body** of the message — the location prefix
// (`[file:line:col] `), the phase tag (`Parse error: `, `Type error: `,
// `Warning: `, etc.), and the trailing newline are added by the emit
// helper for that phase (parse_error / check_error / check_warning /
// codegen_fatal). Format placeholders (%s, %d, %v, ...) are passed
// positionally at the call site, same as before.
//
// Naming:
//   PARSE_<topic>     — parser errors  → parse_error
//   TYPE_<topic>      — type-checker errors → check_error
//   CODE_<topic>      — codegen fatals → codegen_fatal
//   WARN_<topic>      — warnings (any phase) → check_warning
//
// The TODO of writing every message in a single authorial voice
// happens by editing the strings below in place. No call sites
// need to change when wording shifts.

// ============================================================
// Parser errors
// ============================================================

PARSE_EXPECTED_TOKEN              :: "expected %v, got %v \"%s\""
PARSE_EXPECTED_INTRINSIC_AFTER_AT :: "expected intrinsic name part after `@`, got `%s`"
PARSE_EXPECTED_INTRINSIC_AFTER_DOT :: "expected intrinsic name part after `.`, got `%s`"
PARSE_BARE_INTRINSIC_REMOVED      :: "bare `intrinsic` body is no longer supported — use `{{ @llvm.<name> }}` instead"
PARSE_MALFORMED_USE_INCLUDE       :: "malformed use/include statement"
PARSE_EXPOSE_NEEDS_FUN_DECL       :: "`#expose` must precede a `name :: fun(...)` declaration"
PARSE_USING_NOT_ALLOWED_ON_INCLUDE :: "`using` is not allowed before `use`/`include` — use bare `use %s` (private) or `include %s` (re-export), or `name :: use path` for qualified access"
PARSE_INCLUDE_NEEDS_COLON_COLON   :: "`:=` is not allowed for `use`/`include` — modules are comptime, use `name :: use path` (private) or `name :: include path` (re-export)"
PARSE_UNEXPECTED_TOKEN_STMT       :: "unexpected token %v \"%s\" (expected statement)"
PARSE_DEFAULT_VALUE_COUNT_MISMATCH :: "%d default values for %d names (expected 0, 1, or %d)"
PARSE_UNION_TAG_NEEDS_TYPE        :: "expected type after `tag` in union header, got `%s`"
PARSE_UNION_SIZE_NEEDS_NUM        :: "expected number after `size` in union header, got `%s`"
PARSE_UNION_HEADER_UNKNOWN        :: "union header takes `$T: type`, `tag <type>`, `pad <type>`, `size <N>`; got `%s`"
PARSE_OVERLOAD_EXPECTED_OP        :: "expected operator after 'overload', got '%s'"
PARSE_FOREIGN_NEEDS_STATIC_LIB    :: "foreign block needs `static_lib`, got `%s`"
PARSE_NESTED_IF_EXPR              :: "nested if-expressions are not allowed"
PARSE_RANGE_FOR_ONE_VAR           :: "range-for loop takes one variable, not two"
PARSE_VAR_WITH_CONSTANT           :: "'var' cannot be combined with '::' (comptime constant)"
PARSE_EXPECTED_TYPE               :: "expected type, got %v \"%s\""
PARSE_RANGE_NEEDS_DOTS            :: "expected '..' after `%sin` in range-membership check"
PARSE_STRUCT_LIT_MIXED_FIELDS     :: "struct literal cannot mix positional and named fields"
PARSE_HEX_OVERFLOWS_U64           :: "hex literal '%s' overflows u64 (max 0xFFFFFFFFFFFFFFFF) — Mara's integer-literal precision tops out at 64 bits"
PARSE_INVALID_NUMBER              :: "invalid number '%s'"
PARSE_EXPECTED_VARIANT_NAME       :: "expected variant name after '.'"
PARSE_UNEXPECTED_LBRACE_IN_EXPR   :: "unexpected '{' in expression"
PARSE_EXPECTED_HASH_NAME          :: "expected intrinsic name after '#'"
PARSE_UNKNOWN_INTRINSIC           :: "unknown compiler intrinsic '#%s'"
PARSE_SEALED_NEEDS_USE_INCLUDE    :: "expected `use` or `include` after `sealed`, got `%s`"
PARSE_UNEXPECTED_TOKEN            :: "unexpected token %v \"%s\""

// ============================================================
// Type-checker errors and warnings — populated in next pass.
// ============================================================

// ============================================================
// Codegen fatals — populated in next pass.
// ============================================================
