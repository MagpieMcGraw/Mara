package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Function definition codegen
// ---------------------------------------------------------------------------

// Unwrap a parameter type that ultimately resolves to a slice. Slices are
// reference types in Mara, so `s: [:]T`, `s: String` (distinct slice), and
// `s: ^String` (or `^DistinctSlice`) all bind to the same fat-pointer-ref
// shape. Returns the underlying Type_Slice (and ok) for whichever wrapper
// applies; returns false for non-slice types.
slice_through_distinct_and_ptr :: proc(t: Type) -> (^Type_Slice, bool) {
    cur := t
    if pt, ok := cur.(^Type_Ptr); ok { cur = pt.elem }
    if dt, ok := cur.(^Type_Distinct); ok { cur = dt.base_type }
    if sl, ok := cur.(^Type_Slice); ok { return sl, true }
    return nil, false
}

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

// Multi-return version: per-position NRVO candidate. Returns one name per
// position (or "" if that position can't NRVO). Same shape contract as the
// single-position helper: every return must use an Expr_Ident at position i,
// and every return must use the same name for that position.
find_nrvo_candidates :: proc(body: []Stmt, n_positions: int) -> [dynamic]string {
    candidates: [dynamic]string
    for _ in 0..<n_positions { append(&candidates, "") }
    blocked: [dynamic]bool
    defer delete(blocked)
    for _ in 0..<n_positions { append(&blocked, false) }
    found_any := false
    for s in body {
        ret, ok := s.(Stmt_Return)
        if !ok { continue }
        if len(ret.values) != n_positions {
            // Shape mismatch — block all positions for safety.
            for i in 0..<n_positions { candidates[i] = ""; blocked[i] = true }
            return candidates
        }
        for i in 0..<n_positions {
            if blocked[i] { continue }
            ident, id_ok := ret.values[i].(^Expr_Ident)
            if !id_ok {
                candidates[i] = ""
                blocked[i] = true
                continue
            }
            if !found_any {
                candidates[i] = ident.name
            } else if candidates[i] != ident.name {
                candidates[i] = ""
                blocked[i] = true
            }
        }
        found_any = true
    }
    return candidates
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
        case ^Type_Scope:
            if v.kind == .Struct {
                addr := fresh_tmp(g)
                emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 %d", addr, st_llvm, base_ptr, i)
                fixup_partial_array_fields(g, addr, &v.sd)
            }
        }
    }
}

// Register `name` in g.all_vars as the right Var_Entry shape for a field of
// type `ft` whose storage lives at LLVM pointer `addr`. Used to pre-bind a
// struct constructor's fields to GEPs into %sret so the body's references
// route through the caller's slot directly.
prebind_field_var :: proc(g: ^Codegen, name, addr: string, ft: Type) {
    t := distinct_base(ft)
    #partial switch v in t {
    case ^Type_Fixed_Array:
        elem_t := llvm_type_from_checker(v.elem)
        utf8 := false
        if _, u_ok := v.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Array_Var{
            alloca    = addr,
            capacity  = v.size,
            elem_type = elem_t,
            is_utf8   = utf8,
        }
        return
    case ^Type_Slice:
        elem_t := llvm_type_from_checker(v.elem)
        utf8 := false
        if _, u_ok := v.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Slice_Var{
            alloca    = addr,
            elem_type = elem_t,
            is_utf8   = utf8,
        }
        return
    case ^Type_Partial_Array:
        elem_t := llvm_type_from_checker(v.elem)
        utf8 := false
        if _, u_ok := v.elem.(Type_Utf8); u_ok { utf8 = true }
        g.all_vars[name] = Slice_Var{
            alloca    = addr,
            elem_type = elem_t,
            is_utf8   = utf8,
        }
        // The caller's memset zeroed the field; stamp a valid header over it
        // (ptr → &elements, cap = N). Same fixup for non-constructor struct
        // returns lives in fixup_partial_array_fields.
        stamp_partial_array_header(g, addr, v)
        return
    case ^Type_Union:
        g.all_vars[name] = Union_Var{
            alloca     = addr,
            union_name = union_key(v),
        }
        return
    case ^Type_Scope:
        if v.kind == .Struct {
            g.all_vars[name] = Struct_Var{
                alloca      = addr,
                struct_name = v.name,
            }
            return
        }
    }
    g.all_vars[name] = Scalar_Var{alloca = addr}
}

gen_scope_def :: proc(g: ^Codegen, cf: ^Checked_Scope) {
    // Foreigns and intrinsics have no body to emit — foreign calls dispatch
    // through their `declare` and link_name; intrinsic calls expand inline at
    // each call site to an @llvm.* call.
    switch _ in cf.origin {
    case Origin_Source:    // fall through, emit body below
    case Origin_Intrinsic: return
    case Origin_Foreign:   return
    }

    // Determine return type — struct/array/multi-return returns use void + sret param(s)
    ret_type := "i64"
    ret_struct_name := ""
    ret_array_cap := 0
    ret_array_elem := ""
    ret_types: []Type = nil
    ret_slice_elem := ""
    ret_slice_utf8 := false
    ret_partial_elem := ""
    ret_partial_cap := 0
    if len(cf.return_types) > 1 {
        ret_type = "void"
        ret_types = cf.return_types[:]
    } else if len(cf.return_types) == 0 {
        ret_type = "void"
    } else {
        single := cf.return_types[0]
        if sd := as_struct_body(single); sd != nil {
            ret_type = "void"
            ret_struct_name = sd.name
        } else if fa, fa_ok := single.(^Type_Fixed_Array); fa_ok {
            ret_type = "void"
            ret_array_cap = fa.size
            ret_array_elem = llvm_type_from_checker(fa.elem)
        } else if sl, sl_ok := single.(^Type_Slice); sl_ok {
            ret_type = "void"
            ret_slice_elem = llvm_type_from_checker(sl.elem)
            _, ret_slice_utf8 = sl.elem.(Type_Utf8)
        } else if pa, pa_ok := distinct_base(single).(^Type_Partial_Array); pa_ok {
            // Partial array (e.g. str64): build into the caller's slot via sret,
            // like a slice but with the full {len,cap,ptr,[N]} storage. NRVO'd
            // when the returned local is the candidate (see the decl path).
            ret_type = "void"
            ret_partial_elem = llvm_type_from_checker(pa.elem)
            ret_partial_cap = pa.size
        } else if single == nil || is_untyped(single) {
            ret_type = "void"
        } else {
            ret_type = llvm_type_from_checker(single)
        }
    }

    // Build parameter list — struct params passed as ptr, slices as { ptr, i64 }
    param_strs: [dynamic]string
    for p in cf.params {
        if sd := as_struct_body(p.type_); sd != nil {
            append(&param_strs, fmt.tprintf("ptr %%%s.arg", p.name))
        } else if _, ut_ok := p.type_.(^Type_Union); ut_ok {
            append(&param_strs, fmt.tprintf("ptr %%%s.arg", p.name))
        } else if _, sl_ok := slice_through_distinct_and_ptr(p.type_); sl_ok {
            // Slice param: pass by pointer to the slice header (fat pointer is
            // inherently a reference type — cursor mutations propagate to caller).
            // Same lowering for `s: [:]T`, `s: String` (distinct slice), and
            // `s: ^String` (explicit pointer, same ABI).
            append(&param_strs, fmt.tprintf("ptr %%%s.arg", p.name))
        } else if _, pa_ok := partial_through_distinct_and_ptr(p.type_); pa_ok {
            // Partial-array param: same ABI as slice (first slice_header_bytes match).
            // `s: ^String` where String is `type([..N, 0]utf8)` binds here.
            append(&param_strs, fmt.tprintf("ptr %%%s.arg", p.name))
        } else {
            pt := llvm_type_from_checker(p.type_)
            append(&param_strs, fmt.tprintf("%s %%%s.arg", pt, p.name))
        }
    }

    // Struct/array/multi-return/slice return: add hidden sret output parameter(s)
    if ret_struct_name != "" {
        append(&param_strs, "ptr %sret")
    } else if ret_array_cap > 0 {
        append(&param_strs, "ptr %sret")
    } else if ret_slice_elem != "" {
        append(&param_strs, "ptr %sret")
    } else if ret_partial_cap > 0 {
        append(&param_strs, "ptr %sret")
    } else if ret_types != nil {
        for i in 0..<len(ret_types) {
            append(&param_strs, fmt.tprintf("ptr %%sret.%d", i))
        }
    }

    // Sibling-storage escape: hidden ptr params after sret, one per escape
    // local. The caller allocates each buffer (stack or arena) and passes
    // its address; inside the function the local is aliased to that ptr.
    if ret_struct_name != "" {
        if einfo, einfo_ok := lookup_fun_info(g, cf.name); einfo_ok {
            for el in einfo.escape_locals {
                append(&param_strs, fmt.tprintf("ptr %%%s.storage", el.name))
            }
        }
    }

    params_joined := strings.join(param_strs[:], ", ")
    ir_name := mara_fn_name(g, cf.name)
    // `#expose` → dllexport linkage so the symbol is visible in the DLL/SO's
    // export table. The linker still produces a regular static lib otherwise.
    linkage := ""
    if cf.ast != nil && cf.ast.is_exposed {
        linkage = "dllexport "
    }
    fn_header := strings.concatenate({"define ", linkage, ret_type, " ", ir_name, "(", params_joined, ") {"})
    emit_raw(g, fn_header)
    emit(g, "entry:")

    // `#expose` entry points hand the host's Context pointer through their
    // first param; stash it into @__mara_program so internal Mara calls
    // inside the DLL read the host's globals. Validated at type-check time:
    // first param is `^Context`. Use %<name>.arg directly (before the normal
    // per-param alloca dance, which would also write %<name>).
    if cf.ast != nil && cf.ast.is_exposed && len(cf.params) > 0 {
        emit(g, "  store ptr %%%s.arg, ptr @__mara_program", cf.params[0].name)
    }

    // Save and reset codegen state for this function
    old_all_vars := g.all_vars
    old_tmp := g.tmp_counter
    old_scope_stack := g.scope_stack
    old_nrvo_var := g.nrvo_var
    old_emitted_allocas := g.emitted_allocas
    old_fun_body := g.current_fun_body
    old_ctor_self := g.ctor_has_self_sret
    g.all_vars = {}
    g.tmp_counter = 0
    g.scope_stack = {}
    g.emitted_allocas = {}
    g.current_fun_body = cf.body[:]
    // Pending producer/consumer temp results are per-expression state that must
    // never cross a function boundary. The discard-point clear in gen_stmt
    // (Stmt_Call) already enforces this, but reset here too so no future
    // producer/consumer gap can leak a stale buffer into this function's body.
    clear_temp_results(g)
    old_ret_type := g.current_ret_type
    g.current_ret_type = ret_type
    // Recomputed per function (0 / "" for non-partial-array returns), so no
    // save/restore needed — each function overwrites.
    g.ret_partial_cap = ret_partial_cap
    g.ret_partial_elem = ret_partial_elem

    // Register sret pointer for struct-returning functions
    g.nrvo_var = ""
    if ret_struct_name != "" {
        g.all_vars["__sret"] = Struct_Var{
            alloca = "%sret",
            struct_name = ret_struct_name,
        }
        // NRVO: if every `return X` returns the same named local, alias that
        // local to %sret. The body writes directly into the caller's slot —
        // no callee alloca, no memcpy at return. Mirrors the array path below.
        g.nrvo_var = find_nrvo_candidate(cf.body[:])
        if g.nrvo_var != "" {
            g.all_vars[g.nrvo_var] = Struct_Var{
                alloca      = "%sret",
                struct_name = ret_struct_name,
            }
        }
        // Sibling-storage escape: each escape local is aliased to its hidden
        // %<name>.storage param. The body's `verts : [4]T` declaration finds
        // an existing array entry and skips its stack alloca; reads/writes
        // go straight through the caller-provided buffer.
        if info, info_ok := lookup_fun_info(g, cf.name); info_ok && len(info.escape_locals) > 0 {
            for el in info.escape_locals {
                g.all_vars[el.name] = Array_Var{
                    alloca    = fmt.tprintf("%%%s.storage", el.name),
                    capacity  = el.cap,
                    elem_type = el.elem_type,
                    is_utf8   = el.is_utf8,
                }
            }
        }
        // Struct constructor: pre-bind each field to a GEP into %sret. The body's
        // field-decl statements (e.g. `vao : u32`) detect the pre-bound name and
        // skip their own alloca; subsequent reads and writes of bare field names
        // route through the caller's slot directly. Replaces the prior
        // copy-locals-to-sret epilogue.
        if cf.type_ != nil && cf.type_.kind == .Struct {
            if ret_st, rs_ok := lookup_struct(g, ret_struct_name); rs_ok {
                sret_llvm := struct_llvm_name(ret_struct_name)
                for &f, i in ret_st.fields {
                    if _, already := g.all_vars[f.name]; already { continue }
                    addr := fresh_tmp(g)
                    emit(g, "  %s = getelementptr %s, ptr %%sret, i32 0, i32 %d", addr, sret_llvm, i)
                    prebind_field_var(g, f.name, addr, f.type_)
                }
            }
        } else {
            // Regular function with a struct return (not a struct constructor):
            // the caller-provided %sret is zero-filled, so partial-array fields
            // come up cap=0 / ptr=null. Stamp valid headers so the body can
            // populate them — e.g. `-> loca: Loca` where Loca has a [..N] field.
            if ret_st, rs_ok := lookup_struct(g, ret_struct_name); rs_ok {
                fixup_partial_array_fields(g, "%sret", ret_st)
            }
        }
    }

    // Fallible constructor: Self is multi-return sret slot 0, built in place.
    // Pre-bind each field to a GEP into %sret.0 (mirroring the single-return
    // constructor's bind into %sret); the declared returns (trailing err) are
    // slots 1+. The g.ctor_has_self_sret flag tells the return machinery to skip
    // slot 0 — Self is never named in a `return`, only built field-by-field.
    g.ctor_has_self_sret = false
    if ret_struct_name == "" && cf.type_ != nil && cf.type_.kind == .Struct && ret_types != nil {
        if self_sd := as_struct_body(ret_types[0]); self_sd != nil {
            g.ctor_has_self_sret = true
            sret_llvm := struct_llvm_name(self_sd.name)
            if ret_st, rs_ok := lookup_struct(g, self_sd.name); rs_ok {
                for &f, i in ret_st.fields {
                    if _, already := g.all_vars[f.name]; already { continue }
                    addr := fresh_tmp(g)
                    emit(g, "  %s = getelementptr %s, ptr %%sret.0, i32 0, i32 %d", addr, sret_llvm, i)
                    prebind_field_var(g, f.name, addr, f.type_)
                }
            }
        }
    }

    // Register sret pointer for slice-returning functions
    if ret_slice_elem != "" {
        g.all_vars["__sret"] = Slice_Var{
            alloca    = "%sret",
            elem_type = ret_slice_elem,
            is_utf8   = ret_slice_utf8,
        }
        // NRVO: if every `return X` returns the same named local, alias it
        // to %sret. Body writes the slice header directly into the caller's
        // slot — no fresh alloca, no memcpy at return. Mirrors the struct
        // path above, and `s := slice_returning_call()` in the body routes
        // the inner call's sret straight to this slot (see gen_slice_from_expr).
        g.nrvo_var = find_nrvo_candidate(cf.body[:])
        if g.nrvo_var != "" {
            g.all_vars[g.nrvo_var] = Slice_Var{
                alloca    = "%sret",
                elem_type = ret_slice_elem,
                is_utf8   = ret_slice_utf8,
            }
        }
    }

    // Partial-array return: find the NRVO local. Unlike the slice case we don't
    // pre-register __sret or alias the local here — the partial-array decl path
    // aliases the NRVO local's storage to %sret directly (so its header stamps
    // into the caller's slot), and gen_return keys off g.ret_partial_cap. A
    // non-NRVO return (param / branchy / a call) copies into %sret instead.
    if ret_partial_cap > 0 {
        g.nrvo_var = find_nrvo_candidate(cf.body[:])
    }

    // Register sret pointers for multi-return functions
    old_ret_types := g.ret_types
    g.ret_types = ret_types

    // Register named return bindings as local variables (e.g. fun() -> (fwd, up: Vec3)).
    // NRVO: the binding's alloca IS the sret slot, so writes go directly into
    // the caller's slot. gen_return_tuple detects the self-copy at return and skips it.
    if ret_types != nil && cf.ast != nil && len(cf.ast.return_bindings) > 0 {
        for rb, i in cf.ast.return_bindings {
            if i >= len(ret_types) { break }
            rb_type := distinct_base(ret_types[i])
            sret_slot := fmt.tprintf("%%sret.%d", i)
            if fa, fa_ok := rb_type.(^Type_Fixed_Array); fa_ok {
                elem_t := llvm_type_from_checker(fa.elem)
                utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
                g.all_vars[rb.name] = Array_Var{
                    alloca    = sret_slot,
                    capacity  = fa.size,
                    elem_type = elem_t,
                    is_utf8   = utf8,
                }
            } else if sd := as_struct_body(rb_type); sd != nil {
                g.all_vars[rb.name] = Struct_Var{
                    alloca      = sret_slot,
                    struct_name = sd.name,
                }
            } else {
                ir_t := llvm_type_from_checker(rb_type)
                alloca_name := fmt.tprintf("%%%s", rb.name)
                emit_alloca(g, alloca_name, ir_t)
                // LLVM rejects `store float 0` — float and double slots need
                // a float literal, not the integer 0.
                zero_lit := ir_t == "float" || ir_t == "double" ? "0.0" : "0"
                emit_store(g, ir_t, zero_lit, alloca_name)
                g.all_vars[rb.name] = Scalar_Var{alloca = alloca_name}
            }
        }
    } else if ret_types != nil {
        // Positional multi-return NRVO: if every `return v0, v1, ...` uses the
        // same identifier at each position, alias that local to %sret.<i>.
        // Mirrors the single-return NRVO path below. Currently only fixed-array
        // positions are NRVO'd — other shapes still take the alloca+copy route
        // through gen_return_tuple.
        candidates := find_nrvo_candidates(cf.body[:], len(ret_types))
        defer delete(candidates)
        for cand, i in candidates {
            if cand == "" { continue }
            rb_type := distinct_base(ret_types[i])
            sret_slot := fmt.tprintf("%%sret.%d", i)
            if fa, fa_ok := rb_type.(^Type_Fixed_Array); fa_ok {
                elem_t := llvm_type_from_checker(fa.elem)
                utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
                g.all_vars[cand] = Array_Var{
                    alloca    = sret_slot,
                    capacity  = fa.size,
                    elem_type = elem_t,
                    is_utf8   = utf8,
                }
            }
        }
    }

    // Register sret pointer for array-returning functions. (nrvo_var was
    // cleared above before the struct sret block; struct and array returns
    // are mutually exclusive, so only one branch sets it.)
    if ret_array_cap > 0 {
        g.all_vars["__sret"] = Array_Var{
            alloca    = "%sret",
            capacity  = ret_array_cap,
            elem_type = ret_array_elem,
        }

        // NRVO: if every return returns the same variable, alias it to sret
        // so that writes go directly into the caller's buffer with no copy.
        g.nrvo_var = find_nrvo_candidate(cf.body[:])
        if g.nrvo_var != "" {
            g.all_vars[g.nrvo_var] = Array_Var{
                alloca    = "%sret",
                capacity  = ret_array_cap,
                elem_type = ret_array_elem,
            }
        }
    }

    // Alloca for each parameter
    for p in cf.params {
        if sd := as_struct_body(p.type_); sd != nil {
            // Struct param: arg is already a ptr to the struct, no alloca needed
            g.all_vars[p.name] = Struct_Var{
                alloca = fmt.tprintf("%%%s.arg", p.name),
                struct_name = sd.name,
            }
        } else if ut, ut_ok := p.type_.(^Type_Union); ut_ok {
            // Union param: arg is already a ptr to the union, no alloca needed
            g.all_vars[p.name] = Union_Var{
                alloca = fmt.tprintf("%%%s.arg", p.name),
                union_name  = union_key(ut),
            }
        } else if sl, sl_ok := slice_through_distinct_and_ptr(p.type_); sl_ok {
            // Slice param: %name.arg is a ptr to the caller's slice header.
            // Bind directly — no alloca/store; mutations propagate. Handles
            // plain Slice (`s: [:]T`), distinct slice (`s: String`), and
            // ^Slice / ^DistinctSlice (`dst: ^String`) — all collapse to the
            // same fat-pointer-ref shape since slices are reference types.
            // Must come before the ^Type_Ptr branch so `^String` doesn't get
            // intercepted as a pointer-to-distinct-thing.
            elem_t := llvm_type_from_checker(sl.elem)
            _, sl_utf8 := sl.elem.(Type_Utf8)
            g.all_vars[p.name] = Slice_Var{
                alloca    = fmt.tprintf("%%%s.arg", p.name),
                elem_type = elem_t,
                is_utf8   = sl_utf8,
            }
        } else if pa, pa_ok := partial_through_distinct_and_ptr(p.type_); pa_ok {
            // Partial-array param via pointer: same fat-pointer-ref ABI as
            // slice. First slice_header_bytes of the partial-array layout match a
            // slice header — codegen accesses ptr/len/cap identically.
            elem_t := llvm_type_from_checker(pa.elem)
            _, pa_utf8 := pa.elem.(Type_Utf8)
            g.all_vars[p.name] = Slice_Var{
                alloca    = fmt.tprintf("%%%s.arg", p.name),
                elem_type = elem_t,
                is_utf8   = pa_utf8,
            }
        } else if _, pt_ok := p.type_.(^Type_Ptr); pt_ok {
            // Pointer params: bind directly to the .arg SSA value. Mara
            // params are immutable, so the alloca+store+load dance the
            // codegen used to emit was pure waste — every read can just
            // use `%<name>.arg` directly.
            ssa := fmt.tprintf("%%%s.arg", p.name)
            g.all_vars[p.name] = SSA_Var{ssa = ssa, ir_type = "ptr"}
        } else if fa, fa_ok := p.type_.(^Type_Fixed_Array); fa_ok {
            // Array param (including distinct arrays like Vec3 :: distinct [3]f32)
            elem_t := llvm_type_from_checker(fa.elem)
            arr_type := fmt.tprintf("[%d x %s]", fa.size, elem_t)
            data_name := fmt.tprintf("%%%s.data", p.name)
            emit_alloca(g, data_name, arr_type)
            emit(g, "  store %s %%%s.arg, ptr %s", arr_type, p.name, data_name)
            utf8 := false
            if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
            g.all_vars[p.name] = Array_Var{
                alloca    = data_name,
                capacity  = fa.size,
                elem_type = elem_t,
                is_utf8   = utf8,
            }
        } else {
            // Scalar param: same SSA-direct treatment as pointer params.
            ir_t := llvm_type_from_checker(p.type_)
            ssa := fmt.tprintf("%%%s.arg", p.name)
            g.all_vars[p.name] = SSA_Var{ssa = ssa, ir_type = ir_t}
        }
    }

    // Enable alloca hoisting for the function body.
    // During hoist mode, emit() redirects: allocas → alloca_buf, body → body_buf.
    // After body gen, we flush alloca_buf then body_buf into g.out.
    begin_alloca_hoist(g)

    // Struct constructors pre-bind each field to a GEP into %sret (see the
    // prebind_field_var block above), so the body's field-decl statements
    // skip their own alloca and write straight into the caller's slot. No
    // tail-phase copy is needed.

    push_scope(g, .Function, cf.body[:])
    has_ret := false
    for s in cf.body {
        gen_stmt(g, s)
        if _, ok := s.(Stmt_Return); ok {
            has_ret = true
        }
    }

    // Default return if no explicit return
    if !has_ret {
        pop_scope(g)  // normal exit: emit reset before default return

        if ret_types != nil {
            // Multi-return fall-off. The type checker only permits this when
            // every (declared) slot is err-typed; fill each `%sret.N` with
            // `.Ok` before the bare `ret void`. For a fallible constructor,
            // slot 0 is the in-place Self struct — skip it; it's already built.
            start := 0
            if g.ctor_has_self_sret { start = 1 }
            for i in start..<len(ret_types) {
                emit(g, "  store i32 0, ptr %%sret.%d", i)
            }
            emit(g, "  ret void")
        } else if ret_struct_name != "" || ret_array_cap > 0 || ret_type == "void" {
            emit(g, "  ret void")
        } else if ret_type == "i1" {
            emit(g, "  ret i1 false")
        } else if ret_type == "double" {
            emit(g, "  ret double 0.0")
        } else {
            emit(g, "  ret %s 0", ret_type)
        }
    } else {
        // Return already emitted resets; just pop the stack entry
        if len(g.scope_stack) > 0 { pop(&g.scope_stack) }
    }

    // Flush: hoisted allocas first, then body code
    end_alloca_hoist(g)

    emit(g, "}")
    emit_raw(g, "")

    // Restore state
    g.all_vars = old_all_vars
    g.tmp_counter = old_tmp
    g.scope_stack = old_scope_stack
    g.current_ret_type = old_ret_type
    g.nrvo_var = old_nrvo_var
    g.ret_types = old_ret_types
    g.emitted_allocas = old_emitted_allocas
    g.current_fun_body = old_fun_body
    g.ctor_has_self_sret = old_ctor_self
}
