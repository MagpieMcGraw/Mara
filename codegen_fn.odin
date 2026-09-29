package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Function definition codegen
// ---------------------------------------------------------------------------

// Same as slice_through_distinct_and_ptr but for partial-array params. The
// first slice_header_bytes of a partial array's layout match a slice header, so the
// fat-pointer-ref ABI works identically: `dst: ^String` where String is a
// `type([..N, 0]utf8)` partial array binds as a Slice_Var with the same
// access shape as a slice param.
partial_through_distinct_and_ptr :: proc(t: Type) -> (^Type_Partial_Array, bool) {
    cur := t
    if pt, ok := cur.(^Type_Ptr); ok { cur = pt.elem }
    if dt, ok := cur.(^Type_Distinct); ok { cur = dt.base_type }
    if pa, ok := cur.(^Type_Partial_Array); ok { return pa, true }
    return nil, false
}

// Scan function body for NRVO candidate: if every return statement returns
// the same named variable, return that name. Otherwise return "".
Nrvo_Scan :: struct { name: string, found: bool, blocked: bool }

// A function that CONSUMES a param into its result: its first statement copies
// param k into the local it returns (`r := pk`, r NRVO'd into the result slot),
// and pk is never mentioned again. Such a function reads pk only while making
// that copy, so a caller doing `x = f(x, …)` can hand it x as BOTH pk and the
// result slot: `r := pk` is then a copy onto itself (skipped at runtime), and
// every write to r lands in x — no temp, no copy back. Returns k, or nil.
// The functional-update shape: `push :: fun(pa: [..N]T, x: T) -> [..N]T
// { r := pa; r[r.len] = x; r.len += 1; return r }`, `state = update(state)`.
consumed_param_of :: proc(cf: ^Type_Scope) -> Maybe(int) {
    if cf.kind != .Fun || len(cf.body) == 0 || len(cf.cg_returns) != 1 { return nil }
    ret := distinct_base(cf.cg_returns[0])
    // Only results built in a caller-supplied slot (sret).
    by_slot := as_struct_body(ret) != nil
    #partial switch _ in ret {
    case ^Type_Fixed_Array, ^Type_Partial_Array: by_slot = true
    }
    if !by_slot { return nil }
    first := opening_decl(cf)
    if first == nil || first.target != nil { return nil }
    src, is_ident := first.value.(^Expr_Ident)
    if !is_ident { return nil }
    k := -1
    for p, i in cf.cg_params {
        if p.name == src.name { k = i; break }
    }
    if k < 0 || !types_equal(distinct_base(cf.cg_params[k].type_), ret) { return nil }
    if find_nrvo_candidate(cf.body[:]) != first.name { return nil }
    if stmts_mention(cf.body[1:], src.name) { return nil }
    return k
}

// The single-name declaration a function body opens with (`r := pk` — the
// parser's Stmt_Decl, whose checked form is one Stmt_Assign), or nil.
opening_decl :: proc(cf: ^Type_Scope) -> ^Stmt_Assign {
    if len(cf.body) == 0 { return nil }
    #partial switch v in cf.body[0] {
    case ^Stmt_Assign:
        if v.is_decl { return v }
    case ^Stmt_Decl:
        if len(v.names) == 1 && len(v.checked) == 1 {
            if a, ok := v.checked[0].(^Stmt_Assign); ok && a.is_decl { return a }
        }
    }
    return nil
}

// Whether `name` appears anywhere in these statements — as a read, a write
// target, or inside a defer. Exhaustive switches on purpose (like expr_span):
// consumed_param_of's soundness rests on never missing a mention, so a new
// Stmt/Expr variant must fail to compile here until it's handled. Nested
// function scopes are skipped: without closures they can't see this frame.
stmts_mention :: proc(stmts: []Stmt, name: string) -> bool {
    for s in stmts {
        if stmt_mentions(s, name) { return true }
    }
    return false
}

stmt_mentions :: proc(s: Stmt, name: string) -> bool {
    switch v in s {
    case ^Stmt_Assign:
        return v.name == name || expr_mentions(v.value, name) || expr_mentions(v.target, name) ||
               expr_mentions(v.slice_cap_expr, name)
    case ^Stmt_Multi_Assign:
        for a in v.assigns { if stmt_mentions(a, name) { return true } }
    case ^Stmt_Multi_Return_Assign:
        for n in v.names { if n == name { return true } }
        for t in v.targets { if expr_mentions(t, name) { return true } }
        for x in v.values { if expr_mentions(x, name) { return true } }
        return stmts_mention(v.checked[:], name)
    case ^Stmt_Decl:
        for n in v.names { if n == name { return true } }
        for x in decl_init(v) { if expr_mentions(x, name) { return true } }
        return expr_mentions(decl_cap(v), name) || stmts_mention(v.checked[:], name)
    case ^Stmt_Define:
        return expr_mentions(v.value, name)
    case Stmt_Call:
        return expr_mentions(v.expr, name)
    case ^Stmt_If:
        return expr_mentions(v.condition, name) || stmts_mention(v.body[:], name) || stmts_mention(v.else_body[:], name)
    case ^Stmt_For:
        return stmt_mentions(v.init, name) || expr_mentions(v.condition, name) || stmt_mentions(v.post, name) ||
               expr_mentions(v.range_low, name) || expr_mentions(v.range_high, name) ||
               expr_mentions(v.collection, name) ||
               stmts_mention(v.body[:], name)
    case Stmt_Return:
        for x in v.values { if expr_mentions(x, name) { return true } }
    case ^Stmt_Defer:
        return stmts_mention(v.body[:], name)
    case ^Stmt_Match:
        if expr_mentions(v.subject, name) { return true }
        for &arm in v.arms {
            if expr_mentions(arm.value, name) || stmts_mention(arm.body[:], name) { return true }
        }
    case ^Stmt_Scope, ^Stmt_Foreign, ^Stmt_Union_Def, ^Stmt_Distinct_Def, ^Stmt_Dispatch_Def,
         Stmt_Overload, Stmt_Module, Stmt_Break, Stmt_Continue:
    case nil:
    }
    return false
}

expr_mentions :: proc(e: Expr, name: string) -> bool {
    switch v in e {
    case ^Expr_Ident:
        return v.name == name
    case ^Expr_Unary:
        return expr_mentions(v.operand, name)
    case ^Expr_Binary:
        return expr_mentions(v.left, name) || expr_mentions(v.right, name)
    case ^Expr_Call:
        if expr_mentions(call_qualifier(v), name) { return true }
        for a in call_args(v) { if expr_mentions(a, name) { return true } }
        if v.overrides != nil { return expr_mentions(v.overrides, name) }
    case ^Expr_Array:
        for x in v.elements { if expr_mentions(x, name) { return true } }
    case ^Expr_Index:
        return expr_mentions(v.expr, name) || expr_mentions(v.index, name)
    case ^Expr_Slice:
        return expr_mentions(v.expr, name) || expr_mentions(v.low, name) || expr_mentions(v.high, name)
    case ^Expr_Struct_Literal:
        if v.override_target == name || expr_mentions(v.broadcast_value, name) { return true }
        for f in v.fields { if expr_mentions(f.value, name) { return true } }
        for x in v.array_values { if expr_mentions(x, name) { return true } }
    case ^Expr_Field_Access:
        return expr_mentions(v.expr, name)
    case ^Expr_Assert:
        return expr_mentions(v.cond, name)
    case ^Expr_Take:
        return expr_mentions(v.storage, name) || expr_mentions(take_count(v), name)
    case ^Expr_If:
        return expr_mentions(v.condition, name) || expr_mentions(v.then_expr, name) || expr_mentions(v.else_expr, name)
    case ^Expr_Tuple_Default:
        return expr_mentions(v.source, name)
    case ^Expr_Try:
        return expr_mentions(v.inner, name)
    case ^Expr_Number, ^Expr_String, ^Expr_Char, ^Expr_Bool, ^Expr_Skip_Constructor, ^Expr_Size_Of,
         ^Expr_Compiler_Intrinsic, ^Expr_Include, ^Expr_Type_Name, ^Expr_Self:
    case nil:
    }
    return false
}

// Recursively gather the NRVO candidate from a function body. Returns the
// identifier that EVERY `return` yields, or "" when any return yields no value,
// a non-ident (literal/call), or a different name — or when there are no
// returns at all. Descends into nested blocks (if/else, for, defer, match arms)
// so a function that only returns from inside branches still qualifies — e.g.
// parse_glyph, whose three `return glyph`s all sit inside if-statements. A
// top-level-only scan saw zero returns there and silently skipped NRVO, forcing
// an alloca + whole-struct copy at each return.
//
// Does NOT descend into Stmt_Scope: that's a nested fn/type definition whose
// returns belong to the inner function, not this one. New block-bearing
// statement kinds must be added to nrvo_scan or NRVO will silently miss their
// returns.
find_nrvo_candidate :: proc(body: []Stmt) -> string {
    st := Nrvo_Scan{}
    nrvo_scan(body, &st)
    if st.blocked || !st.found { return "" }
    return st.name
}

nrvo_scan :: proc(body: []Stmt, st: ^Nrvo_Scan) {
    for s in body {
        if st.blocked { return }
        #partial switch v in s {
        case Stmt_Return:
            if len(v.values) == 0 { st.blocked = true; return }
            ident, id_ok := v.values[0].(^Expr_Ident)
            if !id_ok { st.blocked = true; return }  // returns a literal or call
            if !st.found {
                st.name = ident.name
                st.found = true
            } else if st.name != ident.name {
                st.blocked = true; return  // different variables returned
            }
        case ^Stmt_If:
            nrvo_scan(v.body[:], st)
            nrvo_scan(v.else_body[:], st)
        case ^Stmt_For:
            nrvo_scan(v.body[:], st)
        case ^Stmt_Defer:
            nrvo_scan(v.body[:], st)
        case ^Stmt_Match:
            for &arm in v.arms {
                nrvo_scan(arm.body[:], st)
            }
        }
    }
}

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
