package mara

import "core:fmt"
import "core:strings"

// ---------------------------------------------------------------------------
// Function definition codegen
// ---------------------------------------------------------------------------

// Unwrap a parameter type that ultimately resolves to a slice. Slices are
// reference types in Mara, so `s: []T`, `s: String` (distinct slice), and
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

// Scan function body for NRVO candidate: if every return statement returns
// the same named variable, return that name. Otherwise return "".
find_nrvo_candidate :: proc(body: []Stmt) -> string {
    candidate := ""
    found_any := false
    for s in body {
        ret, ok := s.(Stmt_Return)
        if !ok { continue }
        if len(ret.values) == 0 { return "" }
        ident, id_ok := ret.values[0].(^Expr_Ident)
        if !id_ok { return "" }  // returns a literal or call — can't NRVO
        if !found_any {
            candidate = ident.name
            found_any = true
        } else if candidate != ident.name {
            return ""  // different variables returned — can't NRVO
        }
    }
    return candidate
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

    // Determine return type — struct/array/tuple returns use void + sret param(s)
    ret_type := "i64"
    ret_struct_name := ""
    ret_array_cap := 0
    ret_array_elem := ""
    ret_tuple: ^Type_Tuple = nil
    ret_slice_elem := ""
    ret_slice_utf8 := false
    ret_slice_sentinel := false
    if sd := as_struct_body(cf.return_type); sd != nil {
        ret_type = "void"
        ret_struct_name = sd.name
    } else if fa, fa_ok := cf.return_type.(^Type_Fixed_Array); fa_ok {
        ret_type = "void"
        ret_array_cap = fa.size
        ret_array_elem = llvm_type_from_checker(fa.elem)
    } else if tup, tup_ok := cf.return_type.(^Type_Tuple); tup_ok {
        ret_type = "void"
        ret_tuple = tup
    } else if sl, sl_ok := cf.return_type.(^Type_Slice); sl_ok {
        ret_type = "void"
        ret_slice_elem = llvm_type_from_checker(sl.elem)
        _, ret_slice_utf8 = sl.elem.(Type_Utf8)
        ret_slice_sentinel = sl.has_sentinel
    } else if cf.return_type == nil || is_untyped(cf.return_type) {
        ret_type = "void"
    } else {
        ret_type = llvm_type_from_checker(cf.return_type)
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
            // Same lowering for `s: []T`, `s: String` (distinct slice), and
            // `s: ^String` (explicit pointer, same ABI).
            append(&param_strs, fmt.tprintf("ptr %%%s.arg", p.name))
        } else {
            pt := llvm_type_from_checker(p.type_)
            append(&param_strs, fmt.tprintf("%s %%%s.arg", pt, p.name))
        }
    }

    // Struct/array/tuple/slice return: add hidden sret output parameter(s)
    if ret_struct_name != "" {
        append(&param_strs, "ptr %sret")
    } else if ret_array_cap > 0 {
        append(&param_strs, "ptr %sret")
    } else if ret_slice_elem != "" {
        append(&param_strs, "ptr %sret")
    } else if ret_tuple != nil {
        for i in 0..<len(ret_tuple.elems) {
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
    // first param; stash it into @__mara_context so internal Mara calls
    // inside the DLL read the host's globals. Validated at type-check time:
    // first param is `^Context`. Use %<name>.arg directly (before the normal
    // per-param alloca dance, which would also write %<name>).
    if cf.ast != nil && cf.ast.is_exposed && len(cf.params) > 0 {
        emit(g, "  store ptr %%%s.arg, ptr @__mara_context", cf.params[0].name)
    }

    // Save and reset codegen state for this function
    old_all_vars := g.all_vars
    old_tmp := g.tmp_counter
    old_scope_stack := g.scope_stack
    old_nrvo_var := g.nrvo_var
    old_emitted_allocas := g.emitted_allocas
    old_fun_body := g.current_fun_body
    g.all_vars = {}
    g.tmp_counter = 0
    g.scope_stack = {}
    g.emitted_allocas = {}
    g.current_fun_body = cf.body[:]
    old_ret_type := g.current_ret_type
    g.current_ret_type = ret_type

    // Register sret pointer for struct-returning functions
    if ret_struct_name != "" {
        g.all_vars["__sret"] = Struct_Var{
            alloca = "%sret",
            struct_name = ret_struct_name,
        }
        // Sibling-storage escape: each escape local is aliased to its hidden
        // %<name>.storage param. The body's `verts : [4]T` declaration finds
        // an existing array entry and skips its stack alloca; reads/writes
        // go straight through the caller-provided buffer.
        if info, info_ok := lookup_fun_info(g, cf.name); info_ok && len(info.escape_locals) > 0 {
            for el in info.escape_locals {
                g.all_vars[el.name] = Array_Var{
                    alloca       = fmt.tprintf("%%%s.storage", el.name),
                    capacity     = el.cap,
                    elem_type    = el.elem_type,
                    is_utf8      = el.is_utf8,
                    has_sentinel = el.has_sentinel,
                    sentinel     = el.sentinel,
                }
            }
        }
    }

    // Register sret pointer for slice-returning functions
    if ret_slice_elem != "" {
        g.all_vars["__sret"] = Slice_Var{
            alloca       = "%sret",
            elem_type    = ret_slice_elem,
            is_utf8      = ret_slice_utf8,
            has_sentinel = ret_slice_sentinel,
        }
    }

    // Register sret pointers for tuple-returning functions
    old_ret_tuple := g.ret_tuple
    g.ret_tuple = ret_tuple

    // Register named return bindings as local variables (e.g. fun() -> (fwd, up: Vec3))
    if ret_tuple != nil && cf.ast != nil && len(cf.ast.return_bindings) > 0 {
        for rb, i in cf.ast.return_bindings {
            if i >= len(ret_tuple.elems) { break }
            rb_type := distinct_base(ret_tuple.elems[i])
            if fa, fa_ok := rb_type.(^Type_Fixed_Array); fa_ok {
                elem_t := llvm_type_from_checker(fa.elem)
                arr_type := fmt.tprintf("[%d x %s]", fa.size, elem_t)
                data_name := fmt.tprintf("%%%s.data", rb.name)
                emit(g, "  %s = alloca %s", data_name, arr_type)
                emit(g, "  store %s zeroinitializer, ptr %s", arr_type, data_name)
                utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
                g.all_vars[rb.name] = Array_Var{
                    alloca    = data_name,
                    capacity  = fa.size,
                    elem_type = elem_t,
                    is_utf8   = utf8,
                }
            } else if sd := as_struct_body(rb_type); sd != nil {
                alloca_name := fmt.tprintf("%%%s", rb.name)
                stype := struct_llvm_name(sd.name)
                emit(g, "  %s = alloca %s", alloca_name, stype)
                g.all_vars[rb.name] = Struct_Var{
                    alloca      = alloca_name,
                    struct_name = sd.name,
                }
            } else {
                ir_t := llvm_type_from_checker(rb_type)
                alloca_name := fmt.tprintf("%%%s", rb.name)
                emit(g, "  %s = alloca %s", alloca_name, ir_t)
                emit(g, "  store %s 0, ptr %s", ir_t, alloca_name)
                g.all_vars[rb.name] = Scalar_Var{alloca = alloca_name}
            }
        }
    }

    // Register sret pointer for array-returning functions
    g.nrvo_var = ""
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
            // plain Slice (`s: []T`), distinct slice (`s: String`), and
            // ^Slice / ^DistinctSlice (`dst: ^String`) — all collapse to the
            // same fat-pointer-ref shape since slices are reference types.
            // Must come before the ^Type_Ptr branch so `^String` doesn't get
            // intercepted as a pointer-to-distinct-thing.
            elem_t := llvm_type_from_checker(sl.elem)
            _, sl_utf8 := sl.elem.(Type_Utf8)
            g.all_vars[p.name] = Slice_Var{
                alloca       = fmt.tprintf("%%%s.arg", p.name),
                elem_type    = elem_t,
                is_utf8      = sl_utf8,
                has_sentinel = sl.has_sentinel,
            }
        } else if pt, pt_ok := p.type_.(^Type_Ptr); pt_ok {
            if as_struct_body(pt.elem) != nil {
                // Pointer-to-struct param: alloca a ptr slot, store the arg
                alloca_name := fmt.tprintf("%%%s", p.name)
                emit(g, "  %s = alloca ptr", alloca_name)
                emit(g, "  store ptr %%%s.arg, ptr %s", p.name, alloca_name)
                g.all_vars[p.name] = Scalar_Var{alloca = alloca_name}
            } else {
                ir_t := llvm_type_from_checker(p.type_)
                alloca_name := fmt.tprintf("%%%s", p.name)
                emit(g, "  %s = alloca %s", alloca_name, ir_t)
                emit(g, "  store %s %%%s.arg, ptr %s", ir_t, p.name, alloca_name)
                g.all_vars[p.name] = Scalar_Var{alloca = alloca_name}
            }
        } else if fa, fa_ok := p.type_.(^Type_Fixed_Array); fa_ok {
            // Array param (including distinct arrays like Vec3 :: distinct [3]f32)
            elem_t := llvm_type_from_checker(fa.elem)
            arr_type := fmt.tprintf("[%d x %s]", fa.size, elem_t)
            data_name := fmt.tprintf("%%%s.data", p.name)
            emit(g, "  %s = alloca %s", data_name, arr_type)
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
            ir_t := llvm_type_from_checker(p.type_)
            alloca_name := fmt.tprintf("%%%s", p.name)
            emit(g, "  %s = alloca %s", alloca_name, ir_t)
            emit(g, "  store %s %%%s.arg, ptr %s", ir_t, p.name, alloca_name)
            g.all_vars[p.name] = Scalar_Var{alloca = alloca_name}
        }
    }

    // Enable alloca hoisting for the function body.
    // During hoist mode, emit() redirects: allocas → alloca_buf, body → body_buf.
    // After body gen, we flush alloca_buf then body_buf into g.out.
    begin_alloca_hoist(g)

    // Unified struct construction: every struct's init function executes its
    // body as a normal function body, then a tail phase copies locals named
    // like the struct's fields into %sret. This collapses paramized and
    // non-paramized classes into one codegen path — imperative statements
    // run in source order alongside field initializations, in both cases.
    //
    // Cost: an extra alloca + copy per field for plain POD structs. LLVM's
    // mem2reg + SROA + DCE fold these away in release builds.

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

        // Constructor: copy field values from locals to %sret before returning.
        // Fires for every struct constructor — paramized or not. The body has
        // run as a normal function body, allocating locals named like the
        // struct's fields; this pass moves those locals into the return slot.
        // Fields whose body never bound a value stay zero in %sret.
        if ret_struct_name != "" && cf.type_ != nil && cf.type_.kind == .Struct {
            if ret_st, rs_ok := lookup_struct(g, ret_struct_name); rs_ok {
                sret_type := struct_llvm_name(ret_struct_name)
                for &f, i in ret_st.fields {
                    gep := fresh_tmp(g)
                    emit_raw(g, strings.concatenate({"  ", gep, " = getelementptr ", sret_type, ", ptr %sret, i32 0, i32 ", fmt.tprintf("%d", i)}))
                    // Copy field from local to sret
                    if sv, sv_ok := get_struct(g, f.name); sv_ok {
                        inner_st_name := struct_llvm_name(sv.struct_name)
                        inner_st, _ := lookup_struct(g, sv.struct_name)
                        sz := struct_byte_size(inner_st, g.checked)
                        emit_raw(g, strings.concatenate({"  call void @llvm.memcpy.p0.p0.i64(ptr ", gep, ", ptr ", sv.alloca, ", i64 ", fmt.tprintf("%d", sz), ", i1 false)"}))
                    } else if av, av_ok := get_array(g, f.name); av_ok {
                        total_bytes := av.capacity * elem_byte_size(av.elem_type, g.checked)
                        if av.has_sentinel {
                            total_bytes += elem_byte_size(av.elem_type, g.checked)
                        }
                        emit_raw(g, strings.concatenate({"  call void @llvm.memcpy.p0.p0.i64(ptr ", gep, ", ptr ", av.alloca, ", i64 ", fmt.tprintf("%d", total_bytes), ", i1 false)"}))
                    } else if slv, slv_ok := get_slice(g, f.name); slv_ok {
                        tmp := fresh_tmp(g)
                        emit_raw(g, strings.concatenate({"  ", tmp, " = load ", SLICE_IR_TYPE, ", ptr ", slv.alloca}))
                        emit_raw(g, strings.concatenate({"  store ", SLICE_IR_TYPE, " ", tmp, ", ptr ", gep}))
                    } else if sc_alloca, sc_ok := get_scalar(g, f.name); sc_ok {
                        fir := field_ir_type(&f)
                        tmp := fresh_tmp(g)
                        emit_raw(g, strings.concatenate({"  ", tmp, " = load ", fir, ", ptr ", sc_alloca}))
                        emit_raw(g, strings.concatenate({"  store ", fir, " ", tmp, ", ptr ", gep}))
                    }
                }
            }
        }

        if ret_struct_name != "" || ret_array_cap > 0 || ret_tuple != nil || ret_type == "void" {
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
    g.ret_tuple = old_ret_tuple
    g.emitted_allocas = old_emitted_allocas
    g.current_fun_body = old_fun_body
}
