package mara

import "core:fmt"
import "core:strconv"
import "core:strings"

// ---------------------------------------------------------------------------
// Struct, union, and field access codegen
// Reads directly from checked.funs (Type_Scope) — no shadow Struct_Def.
// ---------------------------------------------------------------------------


// Result of resolving a using-promoted field through an embedded struct
Using_Path :: struct {
    outer_index:    int,          // index of the using field in the outer struct
    outer_llvm:     string,       // LLVM type name of the outer struct (%class.Outer)
    inner_st:       ^Scope_Body, // checked type of the embedded struct
    inner_index:    int,          // index of the target field in the inner struct
    inner_ir_type:  string,       // LLVM type of the target field
    inner_signed:   bool,         // signedness of the target field
}

// Search through using-promoted fields in a struct definition.
// Returns path info if found, ok=false if not.
resolve_using_field :: proc(g: ^Codegen, st: ^Scope_Body, field_name: string) -> (Using_Path, bool) {
    for &f, fi in st.fields {
        if !f.is_using { continue }
        ft := field_ir_type(&f)
        if !strings.has_prefix(ft, "%class.") { continue }
        inner_name := ft[len("%class."):]
        inner_st, inner_ok := lookup_struct(g, inner_name)
        if !inner_ok { continue }
        inner_idx := struct_field_index(inner_st, field_name)
        if inner_idx >= 0 {
            inner_f := &inner_st.fields[inner_idx]
            return Using_Path{
                outer_index   = fi,
                outer_llvm    = struct_llvm_name(st.name),
                inner_st      = inner_st,
                inner_index   = inner_idx,
                inner_ir_type = field_ir_type(inner_f),
                inner_signed  = field_is_signed(inner_f),
            }, true
        }
    }
    return {}, false
}

// (Removed: struct_field_index, struct_field_type, struct_field_info — moved to codegen.odin as helpers on ^Type_Scope)

// Handle VLA struct allocation: the entire struct is bump-allocated on the scope arena
// as one contiguous block (fixed header + variable-length array data).
gen_vla_struct_assign :: proc(g: ^Codegen, name: string, st: ^Scope_Body, value: Expr, vla_size_expr: Expr, span: Span = {}) {
    skey := struct_key(st)
    llvm_name := struct_llvm_name(skey)
    loc := format_location(span.file, span.line, span.col)

    // Find the VLA field and compute sizes
    vla_field_idx := -1
    vla_fa: ^Type_Fixed_Array
    for &f, i in st.fields {
        if fa, fa_ok := f.type_.(^Type_Fixed_Array); fa_ok && fa.is_vla {
            vla_field_idx = i
            vla_fa = fa
            break
        }
    }

    // No VLA field — fixed-size struct being arena-allocated via `var`
    if vla_field_idx < 0 {
        data_ptr: string
        // NRVO: if this is the function's NRVO candidate (pre-registered as
        // Struct_Var aliased to %sret in codegen_fn.odin), reuse that slot
        // instead of allocating a fresh one. Caller has already memset'd it.
        if g.nrvo_var == name {
            if existing_sv, ok := get_struct(g, name); ok && existing_sv.alloca == "%sret" {
                data_ptr = existing_sv.alloca
            }
        }
        if data_ptr == "" {
            total := struct_byte_size(st, g.checked)
            data_ptr = emit_arena_bump(g, total, name, loc)
            emit_memset_zero(g, data_ptr, total)
            g.all_vars[name] = Struct_Var{
                alloca      = data_ptr,
                struct_name = skey,
            }
        }
        // Explicit `#skip_constructor`: alloca only, skip everything else.
        if _, is_uninit := value.(^Expr_Skip_Constructor); is_uninit {
            return
        }
        // Generic value: route through the unified struct-store primitive.
        // Handles literals (with constructor + defaults + overrides), ident
        // copies, field-access copies, struct-returning calls (NRVO into the
        // arena slot), pure-struct constructor calls, and overloaded binary
        // ops. Before this, big-struct decls like `quad := primitive_quad()`
        // silently dropped the RHS, leaving the local zero-initialized.
        if value != nil {
            gen_store_struct_into(g, data_ptr, st, value)
            if !value_is_nrvo_call(g, value) {
                emit_nested_sized_slice_init(g, data_ptr, st)
            }
            return
        }
        // No value: call the struct's init function to apply defaults.
        if init_fn, has_init := g.checked.functions[st.name]; has_init {
            if init_fn.type_ != nil && len(init_fn.type_.params) > 0 {
                arg_strs: [dynamic]string
                for &param in init_fn.type_.params {
                    pt := llvm_type_from_checker(param.type_)
                    if param.default_value != nil {
                        val := gen_expr(g, param.default_value, pt)
                        append(&arg_strs, fmt.tprintf("%s %s", pt, val))
                    } else {
                        append(&arg_strs, fmt.tprintf("%s zeroinitializer", pt))
                    }
                }
                append(&arg_strs, fmt.tprintf("ptr %s", data_ptr))
                args_joined := strings.join(arg_strs[:], ", ")
                emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(", args_joined, ")"}))
            } else {
                emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(ptr ", data_ptr, ")"}))
            }
        }
        emit_nested_sized_slice_init(g, data_ptr, st)
        return
    }

    // Compute fixed header size (all fields except the VLA, which is [0 x T] in the struct type)
    header_size := struct_byte_size(st, g.checked) // This uses [0 x T] for the VLA field

    // All allocation byte counts run at slice header width — that's the type
    // arena_alloc takes (allocations are byte slices, so they share the slice
    // header width). 2GB cap with i32; flip slice_layout to widen.
    w := slice_layout.len_ir

    // Evaluate the per-variable VLA size expression — type checker guarantees
    // it's already at slice header width.
    size_val := gen_expr(g, vla_size_expr, w)

    // Compute VLA array bytes: count * elem_size (+ 1 for sentinel if needed)
    elem_type := llvm_type_from_checker(vla_fa.elem)
    elem_size := elem_byte_size(elem_type)
    array_count := size_val
    if vla_fa.has_sentinel {
        array_count = fresh_tmp(g)
        emit(g, "  %s = add %s %s, 1", array_count, w, size_val)
    }
    array_bytes: string
    if elem_size == 1 {
        array_bytes = array_count
    } else {
        array_bytes = fresh_tmp(g)
        emit(g, "  %s = mul %s %s, %d", array_bytes, w, array_count, elem_size)
    }

    // Total allocation: header + array data
    total_bytes := fresh_tmp(g)
    emit(g, "  %s = add %s %d, %s", total_bytes, w, header_size, array_bytes)

    // Allocate from scope arena
    data_ptr := emit_arena_bump_runtime(g, total_bytes, name, loc)

    // Zero-initialize. memset.p0.<w> matches the byte-count width — no need to
    // widen total_bytes for the intrinsic call.
    emit(g, "  call void @llvm.memset.p0.%s(ptr %s, i8 0, %s %s, i1 false)", w, data_ptr, w, total_bytes)

    // Register as struct variable with runtime VLA capacity
    g.all_vars[name] = Struct_Var{
        alloca      = data_ptr,
        struct_name = skey,
        vla_cap     = size_val,
    }
}

// Handle: name : ClassName = { field: value, ... }
gen_struct_assign :: proc(g: ^Codegen, name: string, st: ^Scope_Body, value: Expr) {
    skey := struct_key(st)
    llvm_name := struct_llvm_name(skey)

    // Alloca if variable doesn't exist yet, or if re-declared with a different struct type
    existing_sv, already_exists := get_struct(g, name)
    needs_alloca := !already_exists || existing_sv.struct_name != skey
    if needs_alloca {
        alloca_name := fmt.tprintf("%%%s", name)
        if already_exists && existing_sv.struct_name != skey {
            // Re-declaration with different struct type — use a fresh name for the alloca
            alloca_name = fresh_tmp(g)
        }
        emit_alloca(g, alloca_name, llvm_name)
        g.all_vars[name] = Struct_Var{
            alloca = alloca_name,
            struct_name = skey,
        }
        // Always zero-init struct allocas (ensures null ptrs, zero ints, etc.)
        total := struct_byte_size(st, g.checked)
        emit_memset_zero(g, alloca_name, total)

        // Sized-slice fields are NOT init'd here — the struct's auto-init
        // function (called below for bare decls) and gen_store_struct_into
        // (called for literals/copies) both memcpy zeros over the slice
        // headers. Defer to after those, see two sites below.
    }

    sv, _ := get_struct(g, name)

    // Explicit `---` initializer: alloca only, no constructor / defaults.
    // The user opts out of automatic construction and takes responsibility
    // for initializing the value before reading it.
    if _, is_uninit := value.(^Expr_Skip_Constructor); is_uninit {
        return
    }

    if value != nil {
        // All RHS shapes funnel through the unified struct store primitive,
        // which handles literals (with constructor / defaults / overrides),
        // ident-to-ident copies, field-access copies, struct-returning call
        // NRVO, pure-struct constructor calls, and overloaded binary ops.
        gen_store_struct_into(g, sv.alloca, st, value)
        // After literal/copy paths have written their fields, lay down backing
        // storage and slice-header init for any sized-slice fields. The literal
        // path zero-memsets first and may call the init function, both of which
        // would clobber an earlier init. Skip when the value is an NRVO-returning
        // call — the callee already wrote correct headers into our slot.
        if !value_is_nrvo_call(g, value) {
            emit_nested_sized_slice_init(g, sv.alloca, st)
        }
        return
    }

    // Bare declaration `x : Struct` — call the struct's init function so
    // its defaults apply (and any imperative body statements run). For a
    // paramized struct, pass its own param defaults as constructor args.
    //
    // Structs without an emitted init function (hardcoded Context, Args,
    // any foreign types) stay zero-initialized from the alloca-time memset
    // above. By construction they have no field defaults to apply.
    if init_fn, has_init := g.checked.functions[st.name]; has_init {
        if init_fn.type_ != nil && len(init_fn.type_.params) > 0 {
            arg_strs: [dynamic]string
            for &param in init_fn.type_.params {
                pt := llvm_type_from_checker(param.type_)
                if param.default_value != nil {
                    val := gen_expr(g, param.default_value, pt)
                    append(&arg_strs, fmt.tprintf("%s %s", pt, val))
                } else {
                    append(&arg_strs, fmt.tprintf("%s zeroinitializer", pt))
                }
            }
            append(&arg_strs, fmt.tprintf("ptr %s", sv.alloca))
            args_joined := strings.join(arg_strs[:], ", ")
            emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(", args_joined, ")"}))
        } else {
            emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(ptr ", sv.alloca, ")"}))
        }
    }
    // Init sized-slice fields AFTER the struct init function has run — the
    // init function memcpys zeros over field positions (including slice
    // headers), so this has to land last to win.
    emit_nested_sized_slice_init(g, sv.alloca, st)
}

// Apply the named fields of a struct literal onto a struct at base_ptr.
// Used both for bare struct-literal rvalues (`x : Foo = { a: 1 }`) and for
// `{...}` overrides attached to a call (`x : Foo = Foo() { a: 1 }`). Handles
// scalar fields, embedded (`using`) struct fields, fixed-array fields, and
// aggregate (slice) fields. Unknown field names are silently skipped — the
// type checker has already reported them.
apply_struct_literal_fields :: proc(g: ^Codegen, lit: ^Expr_Struct_Literal, st: ^Scope_Body, llvm_name: string, base_ptr: string) {
    // Multi-return spread: `Foo{call()}` where call returns a tuple matching
    // Foo's fields. Emit the call (results land in g.tuple_result_ptrs as
    // sret-filled temps), then materialize each struct field from the
    // corresponding temp. Slice fields auto-coerce from array temps by
    // synthesising a slice header that points at the temp's storage.
    if lit.is_spread {
        call, call_ok := lit.fields[0].value.(^Expr_Call)
        if !call_ok {
            codegen_fatal(g, lit.span, CODE_SPREAD_SET_LIT_FIELDS_CALL)
        }
        info, info_ok := lookup_fun_info(g, call_resolved_name(call))
        if !info_ok || info.ret_types == nil {
            codegen_fatal(g, lit.span, CODE_SPREAD_CALL_TUPLE_RETURN_INFO)
        }
        ret_types := info.ret_types
        gen_call(g, call)
        for sf, i in st.fields {
            if i >= len(ret_types) { break }
            src_ptr := g.tuple_result_ptrs[i]
            src_sem := distinct_base(ret_types[i])
            dst_field_gep := fresh_tmp(g)
            emit_field_gep_into(g, dst_field_gep, llvm_name, base_ptr, i)
            // Slice field + array tuple element: build slice header at the field
            // pointing at the temp's storage. Array's compile-time size is the
            // slice's len/cap (the function fully filled it).
            if _, sl_ok := sf.type_.(^Type_Slice); sl_ok {
                if fa, fa_ok := src_sem.(^Type_Fixed_Array); fa_ok {
                    ptr_gep := fresh_tmp(g)
                    emit_slice_gep(g, ptr_gep, dst_field_gep, SLICE.ptr)
                    emit_store(g, "ptr", src_ptr, ptr_gep)
                    len_gep := fresh_tmp(g)
                    emit_slice_gep(g, len_gep, dst_field_gep, SLICE.len)
                    emit_typed_store_len(g, fmt.tprintf("%d", fa.size), len_gep)
                    cap_gep := fresh_tmp(g)
                    emit_slice_gep(g, cap_gep, dst_field_gep, SLICE.cap)
                    emit_typed_store_cap(g, fmt.tprintf("%d", fa.size), cap_gep)
                    continue
                }
            }
            // Direct copy: same shape on both sides.
            size := checker_type_byte_size(sf.type_)
            emit_memcpy(g, dst_field_gep, src_ptr, size)
        }
        clear(&g.tuple_result_ptrs)
        clear(&g.tuple_result_types)
        return
    }
    for field, pos in lit.fields {
        // Positional literals (`Foo{a, b, c}`) carry empty field names; map
        // each entry to the struct field at the same index.
        idx: int
        if lit.positional {
            if pos >= len(st.fields) { break }
            idx = pos
        } else {
            idx = struct_field_index(st, field.name)
            if idx < 0 { continue }
        }
        f := &st.fields[idx]
        ft := field_ir_type(f)
        // Embedded struct field (`using` promoted): GEP into region, store inner fields.
        if f.is_using && strings.has_prefix(ft, "%class.") {
            inner_name := ft[len("%class."):]
            inner_st, inner_ok := lookup_struct(g, inner_name)
            if inner_ok {
                embed_gep := fresh_tmp(g)
                emit_field_gep_into(g, embed_gep, llvm_name, base_ptr, idx)
                inner_llvm := struct_llvm_name(inner_name)
                if inner_lit, il_ok := field.value.(^Expr_Struct_Literal); il_ok {
                    for inner_field in inner_lit.fields {
                        inner_idx := struct_field_index(inner_st, inner_field.name)
                        if inner_idx < 0 { continue }
                        inner_ft := field_ir_type(&inner_st.fields[inner_idx])
                        inner_val := gen_expr(g, inner_field.value, inner_ft)
                        inner_gep := fresh_tmp(g)
                        emit_field_gep_into(g, inner_gep, inner_llvm, embed_gep, inner_idx)
                        emit_store(g, inner_ft, inner_val, inner_gep)
                    }
                } else if ident2, id2_ok := field.value.(^Expr_Ident); id2_ok {
                    if src_sv, src_ok := get_struct(g, ident2.name); src_ok {
                        for &inner_f, inner_i in inner_st.fields {
                            inner_ft := field_ir_type(&inner_f)
                            src_gep := fresh_tmp(g)
                            emit_field_gep_into(g, src_gep, inner_llvm, src_sv.alloca, inner_i)
                            tmp_val := fresh_tmp(g)
                            emit_load_into(g, tmp_val, inner_ft, src_gep)
                            dst_gep := fresh_tmp(g)
                            emit_field_gep_into(g, dst_gep, inner_llvm, embed_gep, inner_i)
                            emit_store(g, inner_ft, tmp_val, dst_gep)
                        }
                    }
                }
                continue
            }
        }
        // Fixed-array field.
        acap := field_array_cap(f)
        if acap > 0 {
            data_gep := fresh_tmp(g)
            emit_field_gep_into(g, data_gep, llvm_name, base_ptr, idx)
            gen_array_field_store(g, data_gep, acap, field_array_elem(f), field.value)
            continue
        }
        // Aggregate field (e.g. []byte = { ptr, i64, i64 }): memcpy from source.
        // For slice fields, route through gen_slice_value_ptr so fixed-array /
        // array-literal / array-class sources get coerced to a slice header
        // automatically — caller writes `Mesh_Data{verts, inds}` without
        // explicit `[:]`.
        if strings.has_prefix(ft, "{ ") {
            src_ptr: string
            if _, is_slice := f.type_.(^Type_Slice); is_slice {
                src_ptr = gen_slice_value_ptr(g, field.value)
            } else {
                src_ptr = gen_expr(g, field.value, ft)
            }
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, base_ptr, idx)
            size := checker_type_byte_size(f.type_)
            emit_memcpy(g, gep, src_ptr, size)
            continue
        }
        // Named-struct field (`%class.X`): the RHS is either a constructor
        // call (gen_expr returns a ptr to its sret alloca) or another struct
        // pointer (ident, field access, etc.). Either way the layout already
        // lives at the source pointer, so memcpy by size into the field slot.
        // Without this, the fallthrough scalar-store path would emit `store
        // %class.X %ptr, ptr %dst` which LLVM rejects (struct value vs ptr).
        if strings.has_prefix(ft, "%class.") {
            src_ptr := gen_expr(g, field.value, ft)
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_name, base_ptr, idx)
            size := checker_type_byte_size(f.type_)
            emit_memcpy(g, gep, src_ptr, size)
            continue
        }
        // Scalar field.
        val := gen_expr(g, field.value, ft)
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, llvm_name, base_ptr, idx)
        emit_store(g, ft, val, gep)
    }
}

// Handle: &obj.field — return pointer to field (GEP without load)
gen_field_address :: proc(g: ^Codegen, e: ^Expr_Field_Access) -> string {
    // Try unified address chain first
    if chain, chain_ok := build_address_chain(g, e); chain_ok {
        return emit_address_chain(g, &chain)
    }
    // Helper: given a resolved struct type and base pointer, GEP to the named field
    field_gep :: proc(g: ^Codegen, st: ^Scope_Body, base_ptr: string, field: string) -> string {
        llvm_n := struct_llvm_name(struct_key(st))
        idx := struct_field_index(st, field)
        if idx >= 0 {
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, llvm_n, base_ptr, idx)
            return gep
        }
        // Try using-promoted field (two-level GEP)
        up, up_ok := resolve_using_field(g, st, field)
        if up_ok {
            gep1 := fresh_tmp(g)
            emit_field_gep_into(g, gep1, llvm_n, base_ptr, up.outer_index)
            gep2 := fresh_tmp(g)
            emit_field_gep_into(g, gep2, struct_llvm_name(struct_key(up.inner_st)), gep1, up.inner_index)
            return gep2
        }
        return "null"
    }

    // Case 1: direct ident — struct var or pointer-to-struct (auto-deref)
    if ident, ok := e.expr.(^Expr_Ident); ok {
        // Desugared ident (namespace-match shorthand): swap in the desugared
        // expression and re-enter so the relevant case below picks it up.
        if ident.desugared != nil {
            new_e := new_clone(Expr_Field_Access{expr = ident.desugared, field = e.field, span = e.span, type_ = e.type_})
            return gen_field_address(g, new_e)
        }
        st, base_ptr, found := resolve_struct_for_field(g, ident.name, ident.type_, ident.span)
        if !found { return "null" }
        return field_gep(g, st, base_ptr, e.field)
    }

    // Case 2: chained field access — e.g. &events.dropfile.name
    if inner_fa, inner_ok := e.expr.(^Expr_Field_Access); inner_ok {
        gen_field_access(g, inner_fa)
        if fr, fr_ok := claim_field_struct(g); fr_ok {
            if inner_st, isd_ok := lookup_struct(g, fr.struct_name); isd_ok {
                return field_gep(g, inner_st, fr.alloca, e.field)
            }
        }
    }

    return "null"
}

// Resolve a struct definition and base pointer for field access.
// Handles both direct struct vars and pointer-to-struct (auto-deref).
// Returns (type_struct, base_ptr, ok)
resolve_struct_for_field :: proc(g: ^Codegen, ident_name: string, ident_type: Type = nil, span: Span = {}) -> (^Scope_Body, string, bool) {
    // Program global: load from @__mara_program (accessible from any function).
    // `this_program` is the compiler-managed name; the synthesized Program
    // struct sits in c.table.funs["Program"] and the env binds `this_program`.
    if ident_name == "this_program" {
        if st, st_ok := lookup_struct(g, "Program"); st_ok {
            ctx_ptr := fresh_tmp(g)
            emit_raw(g, strings.concatenate({"  ", ctx_ptr, " = load ptr, ptr @__mara_program"}))
            return st, ctx_ptr, true
        }
    }
    // Direct struct variable
    if sv, sv_ok := get_struct(g, ident_name); sv_ok {
        if st, st_ok := lookup_struct(g, sv.struct_name); st_ok {
            return st, sv.alloca, true
        }
    }
    // Pointer to struct (auto-deref): use typed AST annotation
    ptr_struct_name := ""
    if pt, pt_ok := ident_type.(^Type_Ptr); pt_ok {
        if sd := as_struct_body(pt.elem); sd != nil {
            ptr_struct_name = sd.name
        }
    }
    if ptr_struct_name != "" {
        if st, st_ok := lookup_struct(g, ptr_struct_name); st_ok {
            // The pointer value may live in a Scalar_Var alloca (locals) or
            // directly as an SSA value (params — they're immutable, no alloca).
            ptr_val: string
            if entry, entry_ok := g.all_vars[ident_name]; entry_ok {
                #partial switch v in entry {
                case SSA_Var:
                    ptr_val = v.ssa
                case Scalar_Var:
                    ptr_val = fresh_tmp(g)
                    emit_load_into(g, ptr_val, "ptr", v.alloca)
                }
            }
            if ptr_val == "" {
                if alloca_name, ok := get_scalar(g, ident_name); ok {
                    ptr_val = fresh_tmp(g)
                    emit_load_into(g, ptr_val, "ptr", alloca_name)
                }
            }
            emit_null_check(g, ptr_val, ident_name, span)
            return st, ptr_val, true
        }
    }
    return nil, "", false
}

// Handle: obj.field (read)
gen_field_access :: proc(g: ^Codegen, e: ^Expr_Field_Access) -> string {
    // Function reference: game.test_print → @mara_Mega_test_print
    if rf, rf_ok := e.resolved.(Resolved_Func); rf_ok {
        ir_name := mara_fn_name(g, rf.name)
        if fir, fir_ok := foreign_ir_name(g, rf.name); fir_ok {
            ir_name = fir
        }
        return ir_name
    }
    // Compile-time constant (e.g. fixed-array .len / .cap).
    // Handled early so it works for both direct ident (arr.len) and
    // chained access (obj.arr.len) without walking the address chain.
    #partial switch r in e.resolved {
    case Resolved_Enum_Variant:
        return fmt.tprintf("%d", r.value)
    case Resolved_Union_Variant:
        return fmt.tprintf("%d", r.tag_value)
    case Resolved_Constant:
        return fmt.tprintf("%d", r.int_value)
    }
    // .tag accessor on a union value: GEP to field 0 + load with the tag IR
    // type. Same load shape match codegen does to drive arm dispatch — see
    // gen_union_match in codegen_match.odin.
    if r, r_ok := e.resolved.(Resolved_Union_Tag); r_ok {
        ut, ut_ok := g.checked.table.unions[r.union_name]
        if !ut_ok { return "0" }
        union_ptr, ptr_ok := union_subject_ptr(g, e.expr, ut)
        if !ptr_ok { return "0" }
        tag_ir := union_tag_ir_type(ut)
        llvm_name := union_llvm_name(r.union_name)
        tag_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, llvm_name, union_ptr)
        tag_val := fresh_tmp(g)
        emit_load_into(g, tag_val, tag_ir, tag_ptr)
        return tag_val
    }
    // .pad accessor: read the typed padding between tag and payload. The pad
    // sits at byte offset tag_bytes within the union's first IR field (the
    // tag-area byte array, when pad > 0). We GEP from the union pointer in i8
    // units to that offset and load with the pad's IR type.
    if r, r_ok := e.resolved.(Resolved_Union_Pad); r_ok {
        ut, ut_ok := g.checked.table.unions[r.union_name]
        if !ut_ok { return "0" }
        union_ptr, ptr_ok := union_subject_ptr(g, e.expr, ut)
        if !ptr_ok { return "0" }
        tag_bytes := ir_type_byte_size(union_tag_ir_type(ut))
        pad_ir := llvm_type_from_checker(ut.tag_pad)
        pad_ptr := fresh_tmp(g)
        emit(g, "  %s = getelementptr i8, ptr %s, i32 %d", pad_ptr, union_ptr, tag_bytes)
        pad_val := fresh_tmp(g)
        emit_load_into(g, pad_val, pad_ir, pad_ptr)
        return pad_val
    }
    // Try unified address chain first — handles chained access efficiently
    if chain, chain_ok := build_address_chain(g, e); chain_ok {
        addr := emit_address_chain(g, &chain)
        switch chain.final_kind {
        case .Scalar:
            return emit_load(g, chain.final_type, addr)
        case .Struct:
            set_field_result(g, Struct_Var{alloca = addr, struct_name = chain.struct_name})
            return addr
        case .Array:
            av := Array_Var{
                alloca    = addr,
                capacity  = chain.array_cap,
                elem_type = chain.array_elem,
            }
            set_field_result(g, av)
            return addr
        case .Slice:
            // Determine elem type / sentinel from the last step's field def.
            // .Slice covers both Type_Slice and Type_Partial_Array fields — they
            // share the first slice_header_bytes of layout, so a Slice_Var pointing
            // at the field's storage handles .len/.cap/.ptr reads for either.
            if len(chain.steps) == 0 {
                codegen_fatal(g, e.span, CODE_ADDRESS_CHAIN_ENDED_SLICE_STEPS)
            }
            sf, sf_ok := chain.steps[len(chain.steps)-1].(Step_Field)
            if !sf_ok {
                codegen_fatal(g, e.span, CODE_ADDRESS_CHAIN_ENDED_SLICE_LAST)
            }
            elem_t := ""
            sentinel := false
            sentinel_val := 0
            utf8 := false
            if sl, sl_ok := distinct_base(sf.field_def.type_).(^Type_Slice); sl_ok {
                elem_t = llvm_type_from_checker(sl.elem)
                sentinel = sl.has_sentinel
                sentinel_val = sl.sentinel
                _, utf8 = sl.elem.(Type_Utf8)
            } else if pa, pa_ok := distinct_base(sf.field_def.type_).(^Type_Partial_Array); pa_ok {
                elem_t = llvm_type_from_checker(pa.elem)
                sentinel = pa.has_sentinel
                sentinel_val = pa.sentinel
                _, utf8 = pa.elem.(Type_Utf8)
            } else {
                codegen_fatal(g, e.span, CODE_ADDRESS_CHAIN_ENDED_SLICE_LAST_2)
            }
            set_field_result(g, Slice_Var{alloca = addr, elem_type = elem_t, is_utf8 = utf8, has_sentinel = sentinel, sentinel = sentinel_val})
            return addr
        }
    }

    // Walk through the expression to find the root variable and struct type
    ident, ok := e.expr.(^Expr_Ident)
    if !ok {
        // Handle chained field access: r.pos.x → gen inner access, use temp_field_result
        if inner_fa, inner_ok := e.expr.(^Expr_Field_Access); inner_ok {
            inner_val := gen_field_access(g, inner_fa)
            // Check if inner access produced an array result (e.g. for swizzle on struct array field)
            if ar, ar_ok := claim_field_array(g); ar_ok {
                // Swizzle on array field: arr.x, arr.xy etc.
                if is_swizzle_field(e.field, ar.capacity) {
                    if len(e.field) == 1 {
                        // Single-component swizzle: if element is itself an array, produce a pointer
                        // to the inner array (for chained swizzle like data.x.xyz)
                        inner_cap, inner_elem, is_nested := parse_array_ir_type(ar.elem_type)
                        if is_nested {
                            idx := swizzle_char_to_index(e.field[0])
                            arr_type := array_var_type(&ar)
                            gep := fresh_tmp(g)
                            emit_array_gep_const(g, gep, arr_type, ar.alloca, idx)
                            set_field_result(g, Array_Var{
                                alloca    = gep,
                                capacity  = inner_cap,
                                elem_type = inner_elem,
                            })
                            return gep
                        }
                        return gen_swizzle_read_single(g, &ar, e.field)
                    } else {
                        return gen_swizzle_read_multi(g, &ar, e.field)
                    }
                }
            }
            // Check if inner access produced a slice result (e.g. a.base.ptr)
            if sv, sv_ok := claim_field_slice(g); sv_ok {
                if e.field == "ptr" {
                    ptr_gep := fresh_tmp(g)
                    emit_slice_gep(g, ptr_gep, sv.alloca, SLICE.ptr)
                    ptr_val := fresh_tmp(g)
                    emit_load_into(g, ptr_val, "ptr", ptr_gep)
                    return ptr_val
                }
                if e.field == "len" {
                    len_gep := fresh_tmp(g)
                    emit_slice_gep(g, len_gep, sv.alloca, SLICE.len)
                    len_val := fresh_tmp(g)
                    emit_typed_load_len(g, len_val, len_gep)
                    return len_val
                }
                if e.field == "cap" {
                    cap_gep := fresh_tmp(g)
                    emit_slice_gep(g, cap_gep, sv.alloca, SLICE.cap)
                    cap_val := fresh_tmp(g)
                    emit_typed_load_cap(g, cap_val, cap_gep)
                    return cap_val
                }
            }
            // Check if inner access produced a struct result
            if fr, fr_ok := claim_field_struct(g); fr_ok {
                if inner_st, isd_ok := lookup_struct(g, fr.struct_name); isd_ok {
                    inner_llvm := struct_llvm_name(fr.struct_name)
                    idx := struct_field_index(inner_st, e.field)
                    if idx >= 0 {
                        f := &inner_st.fields[idx]
                        ft := field_ir_type(f)
                        gep := fresh_tmp(g)
                        emit_field_gep_into(g, gep, inner_llvm, fr.alloca, idx)
                        // Array field in chained access
                        if acap, aelem, autf8, asent, asentv, ok := field_array_info(f); ok {
                            set_field_result(g, Array_Var{
                                alloca       = gep,
                                capacity     = acap,
                                elem_type    = aelem,
                                is_utf8      = autf8,
                                has_sentinel = asent,
                                sentinel     = asentv,
                            })
                            return gep
                        }
                        // Slice field in chained access
                        if ft == SLICE_IR_TYPE {
                            elem_t := "i8"
                            sentinel := false
                            sentinel_val := 0
                            utf8 := false
                            if sl, sl_ok := f.type_.(^Type_Slice); sl_ok {
                                elem_t = llvm_type_from_checker(sl.elem)
                                sentinel = sl.has_sentinel
                                sentinel_val = sl.sentinel
                                _, utf8 = sl.elem.(Type_Utf8)
                            }
                            set_field_result(g, Slice_Var{alloca = gep, elem_type = elem_t, is_utf8 = utf8, has_sentinel = sentinel, sentinel = sentinel_val})
                            return gep
                        }
                        // Sub-struct field in chained access
                        if strings.has_prefix(ft, "%class.") {
                            sub_name := ft[len("%class."):]
                            set_field_result(g, Struct_Var{alloca = gep, struct_name = sub_name})
                            return gep
                        }
                        val := fresh_tmp(g)
                        emit_load_into(g, val, ft, gep)
                        return val
                    }
                }
            }
            return inner_val
        }
        // Handle indexed expression: rot_mx[2].xyz → index into array, then swizzle
        if idx_expr, idx_ok := e.expr.(^Expr_Index); idx_ok {
            ptr := gen_index_address(g, idx_expr)
            // Check type annotation on the index expression to determine element type
            idx_type := distinct_base(expr_type(idx_expr))
            if fa, fa_ok := idx_type.(^Type_Fixed_Array); fa_ok {
                elem_t := llvm_type_from_checker(fa.elem)
                utf8 := false
                if _, u_ok := fa.elem.(Type_Utf8); u_ok { utf8 = true }
                ar := Array_Var{
                    alloca    = ptr,
                    capacity  = fa.size,
                    elem_type = elem_t,
                    is_utf8   = utf8,
                }
                // Swizzle on indexed array element
                if is_swizzle_field(e.field, ar.capacity) {
                    if len(e.field) == 1 {
                        return gen_swizzle_read_single(g, &ar, e.field)
                    } else {
                        return gen_swizzle_read_multi(g, &ar, e.field)
                    }
                }
                // Non-swizzle scalar field on indexed array element.
                codegen_fatal(g, e.span, CODE_FIELD_ARRAY_ELEMENT_VALID_SWIZZLE, e.field)
            }
            // Struct element of an array or slice — GEP into the field and
            // resolve to a scalar / sub-array / sub-struct / sub-slice result.
            // (Without this branch the outer .field was silently dropped and
            // the entire element got loaded as the expression's value.)
            if sd := as_scope_body(idx_type); sd != nil {
                inner_llvm := struct_llvm_name(struct_key(sd))
                fidx := struct_field_index(sd, e.field)
                if fidx >= 0 {
                    f := &sd.fields[fidx]
                    ft := field_ir_type(f)
                    gep := fresh_tmp(g)
                    emit_field_gep_into(g, gep, inner_llvm, ptr, fidx)
                    // Fixed-array field
                    if acap, aelem, autf8, asent, asentv, ok := field_array_info(f); ok {
                        set_field_result(g, Array_Var{
                            alloca       = gep,
                            capacity     = acap,
                            elem_type    = aelem,
                            is_utf8      = autf8,
                            has_sentinel = asent,
                            sentinel     = asentv,
                        })
                        return gep
                    }
                    // Slice field
                    if ft == SLICE_IR_TYPE {
                        elem_t := "i8"
                        sentinel := false
                        sentinel_val := 0
                        utf8 := false
                        if sl, sl_ok := f.type_.(^Type_Slice); sl_ok {
                            elem_t = llvm_type_from_checker(sl.elem)
                            sentinel = sl.has_sentinel
                            sentinel_val = sl.sentinel
                            _, utf8 = sl.elem.(Type_Utf8)
                        }
                        set_field_result(g, Slice_Var{alloca = gep, elem_type = elem_t, is_utf8 = utf8, has_sentinel = sentinel, sentinel = sentinel_val})
                        return gep
                    }
                    // Sub-struct field
                    if strings.has_prefix(ft, "%class.") {
                        sub_name := ft[len("%class."):]
                        set_field_result(g, Struct_Var{alloca = gep, struct_name = sub_name})
                        return gep
                    }
                    // Scalar field — load and return
                    val := fresh_tmp(g)
                    emit_load_into(g, val, ft, gep)
                    return val
                }
            }
            codegen_fatal(g, e.span, CODE_FIELD_ACCESS_INDEXED_ELEMENT_UNKNOWN, e.field)
        }
        codegen_fatal(g, e.span, CODE_FIELD_ACCESS_TARGET_VARIABLE)
    }

    // Check resolved annotation on the node (populated by type checker)
    #partial switch r in e.resolved {
    case Resolved_Enum_Variant:
        return fmt.tprintf("%d", r.value)
    case Resolved_Union_Variant:
        return fmt.tprintf("%d", r.tag_value)
    case Resolved_Constant:
        return fmt.tprintf("%d", r.int_value)
    }

    // Array swizzle read: arr.x, arr.xy, arr.rgba, etc.
    if av, av_ok := get_array(g, ident.name); av_ok {
        if is_swizzle_field(e.field, av.capacity) {
            if len(e.field) == 1 {
                // Single-component swizzle: if element is itself an array, produce a pointer
                // to the inner array (for chained swizzle like data.x.xyz)
                inner_cap, inner_elem, is_nested := parse_array_ir_type(av.elem_type)
                if is_nested {
                    idx := swizzle_char_to_index(e.field[0])
                    arr_type := array_var_type(&av)
                    gep := fresh_tmp(g)
                    emit_array_gep_const(g, gep, arr_type, av.alloca, idx)
                    set_field_result(g, Array_Var{
                        alloca    = gep,
                        capacity  = inner_cap,
                        elem_type = inner_elem,
                    })
                    return gep
                }
                return gen_swizzle_read_single(g, &av, e.field)
            } else {
                return gen_swizzle_read_multi(g, &av, e.field)
            }
        }
    }

    // Slice / partial-array field access: sl.ptr, sl.len, sl.cap.
    // Routes through the array handle so the sentinel-hidden cap convention
    // matches the cap() builtin and emit_print_arg.
    if _, sv_ok := get_slice(g, ident.name); sv_ok {
        if e.field == "ptr" || e.field == "len" || e.field == "cap" {
            h, _ := resolve_array_handle(g, ident)
            switch e.field {
            case "ptr": return emit_array_data(g, &h)
            case "len": return emit_array_len(g, &h)
            case "cap": return emit_array_cap_user(g, &h)
            }
        }
    }

    st, base_ptr, found := resolve_struct_for_field(g, ident.name, ident.type_, ident.span)
    if !found {
        codegen_fatal(g, e.span, CODE_STRUCT_POINTER_STRUCT, ident.name)
    }

    st_llvm := struct_llvm_name(struct_key(st))
    idx := struct_field_index(st, e.field)
    if idx >= 0 {
        f := &st.fields[idx]
        ft := field_ir_type(f)
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
        // If the field is an embedded struct (using), return its pointer (it's already a value in memory)
        if f.is_using && strings.has_prefix(ft, "%class.") {
            inner_name := ft[len("%class."):]
            set_field_result(g, Struct_Var{alloca = gep, struct_name = inner_name})
            return gep
        }
        // Array field — register as Array_Var and return data pointer
        if acap, aelem, autf8, asent, asentv, ok := field_array_info(f); ok {
            set_field_result(g, Array_Var{
                alloca       = gep,
                capacity     = acap,
                elem_type    = aelem,
                is_utf8      = autf8,
                has_sentinel = asent,
                sentinel     = asentv,
            })
            return gep
        }
        // Slice OR partial-array field — both share the first slice_header_bytes
        // ({len, cap, ptr}), so a Slice_Var pointing at the field's storage
        // handles subsequent .len/.cap/.ptr reads for either shape.
        if ft == SLICE_IR_TYPE || strings.has_prefix(ft, PARTIAL_ARRAY_HEADER_PREFIX) {
            elem_t := "i8"
            sentinel := false
            sentinel_val := 0
            utf8 := false
            if sl, sl_ok := distinct_base(f.type_).(^Type_Slice); sl_ok {
                elem_t = llvm_type_from_checker(sl.elem)
                sentinel = sl.has_sentinel
                sentinel_val = sl.sentinel
                _, utf8 = sl.elem.(Type_Utf8)
            } else if pa, pa_ok := distinct_base(f.type_).(^Type_Partial_Array); pa_ok {
                elem_t = llvm_type_from_checker(pa.elem)
                sentinel = pa.has_sentinel
                sentinel_val = pa.sentinel
                _, utf8 = pa.elem.(Type_Utf8)
            }
            set_field_result(g, Slice_Var{alloca = gep, elem_type = elem_t, is_utf8 = utf8, has_sentinel = sentinel, sentinel = sentinel_val})
            return gep
        }
        // If the field is a sub-struct (not using), register for chained access
        if strings.has_prefix(ft, "%class.") {
            inner_name := ft[len("%class."):]
            set_field_result(g, Struct_Var{alloca = gep, struct_name = inner_name})
            return gep
        }
        val := fresh_tmp(g)
        emit_load_into(g, val, ft, gep)
        return val
    }

    // Try using-promoted field (two-level GEP)
    up, up_ok := resolve_using_field(g, st, e.field)
    if up_ok {
        gep1 := fresh_tmp(g)
        emit_field_gep_into(g, gep1, st_llvm, base_ptr, up.outer_index)
        gep2 := fresh_tmp(g)
        emit_field_gep_into(g, gep2, struct_llvm_name(struct_key(up.inner_st)), gep1, up.inner_index)
        val := fresh_tmp(g)
        emit_load_into(g, val, up.inner_ir_type, gep2)
        return val
    }

    codegen_fatal(g, e.span, CODE_CLASS_FIELD, struct_key(st), e.field)
}

// Resolve an expression to a struct type + pointer for chained field assignment.
// Handles Expr_Ident (direct or pointer-to-struct) and Expr_Field_Access (chained).
resolve_lhs_struct :: proc(g: ^Codegen, expr: Expr) -> (^Scope_Body, string, bool) {
    // Unified address chain handles multi-step lvalues like `obj.arr[i].field = val`
    // that the per-shape cases below don't cover.
    if chain, chain_ok := build_address_chain(g, expr); chain_ok {
        if chain.final_kind == .Struct && chain.struct_name != "" {
            if st, st_ok := lookup_struct(g, chain.struct_name); st_ok {
                ptr := emit_address_chain(g, &chain)
                return st, ptr, true
            }
        }
    }
    #partial switch e in expr {
    case ^Expr_Ident:
        return resolve_struct_for_field(g, e.name, e.type_, e.span)
    }
    return nil, "", false
}

// Parse an LLVM array type string like "[512 x i1]" into capacity and element type.
parse_array_ir_type :: proc(ir_type: string) -> (cap: int, elem: string, ok: bool) {
    if !strings.has_prefix(ir_type, "[") { return 0, "", false }
    rest := ir_type[1:]  // "512 x i1]"
    x_idx := strings.index(rest, " x ")
    if x_idx < 0 { return 0, "", false }
    cap_str := rest[:x_idx]
    elem_str := strings.trim_right(rest[x_idx+3:], "]")
    n, n_ok := strconv.parse_int(cap_str)
    if !n_ok { return 0, "", false }
    return n, elem_str, true
}

// Store a value into an array field of a struct.
// data_ptr: GEP to the [N x T] data in the struct
// array_cap/array_elem: the array metadata for this field
// value:    the RHS expression
//
// Thin wrapper over the unified gen_store_array_into. Kept for callers that
// already have raw capacity + elem_type rather than checker metadata.
gen_array_field_store :: proc(g: ^Codegen, data_ptr: string, array_cap: int, array_elem: string, value: Expr) {
    gen_store_array_into(g, data_ptr, array_cap, array_elem, value)
}

// Single point of truth for "store an array value into a destination pointer".
// Handles every RHS shape that can produce a fixed-array value:
//   - nil         → memset zero
//   - {} literal  → memset zero
//   - array literal [a, b, c] → memset (if undersized) + per-element stores
//   - struct literal with array_values (distinct fixed-array structs like Quat) → memset + per-elem
//   - string literal (utf8 arrays)        → memset + memcpy bytes
//   - compiler intrinsic (#caller_name)   → memset + memcpy bytes
//   - ident referring to another array    → loop element copy
//   - swizzle field access (a.xy → temp)  → per-element copy from swizzle result
//   - array-returning function call       → NRVO via gen_call_into_array
//   - fallback expression                 → gen_expr + memcpy from claim_call_result
gen_store_array_into :: proc(g: ^Codegen, dst_ptr: string, capacity: int, elem_type: string, value: Expr, is_utf8: bool = false, has_sentinel: bool = false) {
    alloc_cap := capacity
    if has_sentinel { alloc_cap += 1 }
    arr_type := fmt.tprintf("[%d x %s]", alloc_cap, elem_type)
    ebs := elem_byte_size(elem_type, g.checked)
    total_bytes := alloc_cap * ebs

    if value == nil {
        emit_memset_zero(g, dst_ptr, total_bytes)
        return
    }

    // Empty struct literal `{}` — zero the array.
    if sl, ok := value.(^Expr_Struct_Literal); ok && len(sl.fields) == 0 && sl.array_values == nil {
        emit_memset_zero(g, dst_ptr, total_bytes)
        return
    }

    // String literal targeting a utf8 array.
    if str_lit, ok := value.(^Expr_String); ok {
        global_name, byte_len := get_string_literal(g, str_lit.value)
        src_ptr := fresh_tmp(g)
        emit_string_gep(g, src_ptr, byte_len, global_name)
        emit_memset_zero(g, dst_ptr, total_bytes)
        emit_memcpy(g, dst_ptr, src_ptr, byte_len)
        return
    }

    // Compiler intrinsic (#caller_name etc.) — produces a string literal.
    if intrinsic, ok := value.(^Expr_Compiler_Intrinsic); ok {
        global_name, byte_len := get_string_literal(g, intrinsic.resolved_value)
        src_ptr := fresh_tmp(g)
        emit_string_gep(g, src_ptr, byte_len, global_name)
        emit_memset_zero(g, dst_ptr, total_bytes)
        emit_memcpy(g, dst_ptr, src_ptr, byte_len)
        return
    }

    // Bare array literal [a, b, c].
    if arr_lit, ok := value.(^Expr_Array); ok {
        if len(arr_lit.elements) < alloc_cap {
            emit_memset_zero(g, dst_ptr, total_bytes)
        }
        for elem, i in arr_lit.elements {
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, arr_type, dst_ptr, i)
            emit_store(g, elem_type, val, gep)
        }
        return
    }

    // Distinct-fixed-array struct literal (Quat{...} etc.) — array_values has
    // per-slot exprs, nil meaning zero-fill.
    if sl, ok := value.(^Expr_Struct_Literal); ok && sl.array_values != nil {
        emit_memset_zero(g, dst_ptr, total_bytes)
        for elem, i in sl.array_values {
            if elem == nil { continue }
            val := gen_expr(g, elem, elem_type)
            gep := fresh_tmp(g)
            emit_array_gep_const(g, gep, arr_type, dst_ptr, i)
            emit_store(g, elem_type, val, gep)
        }
        return
    }

    // Ident referring to another array variable — element-wise loop copy.
    if ident, ok := value.(^Expr_Ident); ok {
        if src, src_ok := get_array(g, ident.name); src_ok {
            src_type := array_var_type(&src)
            w := slice_layout.len_ir
            cond_label := fresh_label(g, "copy.cond")
            body_label := fresh_label(g, "copy.body")
            end_label  := fresh_label(g, "copy.end")
            idx_ptr := fresh_tmp(g)
            emit_alloca(g, idx_ptr, w)
            emit_store(g, w, "0", idx_ptr)
            emit_br(g, cond_label)
            emit_label(g, cond_label)
            idx := fresh_tmp(g)
            emit_load_into(g, idx, w, idx_ptr)
            cmp := fresh_tmp(g)
            emit(g, "  %s = icmp slt %s %s, %d", cmp, w, idx, src.capacity)
            emit_cond_br(g, cmp, body_label, end_label)
            emit_label(g, body_label)
            idx2 := fresh_tmp(g)
            emit_load_into(g, idx2, w, idx_ptr)
            src_gep := fresh_tmp(g)
            emit_array_gep_var(g, src_gep, src_type, src.alloca, idx2, w)
            val := fresh_tmp(g)
            emit_load_into(g, val, elem_type, src_gep)
            dst_gep := fresh_tmp(g)
            emit_array_gep_var(g, dst_gep, arr_type, dst_ptr, idx2, w)
            emit_store(g, elem_type, val, dst_gep)
            next := fresh_tmp(g)
            emit(g, "  %s = add %s %s, 1", next, w, idx2)
            emit_store(g, w, next, idx_ptr)
            emit_br(g, cond_label)
            emit_label(g, end_label)
            return
        }
    }

    // Field access yielding an array — either a multi-component swizzle
    // (a.xy → synthesized temp) or a plain array-typed field (obj.uv).
    // gen_field_access stashes the source Array_Var; the right claim
    // helper distinguishes the two shapes.
    if fa, ok := value.(^Expr_Field_Access); ok {
        gen_field_access(g, fa)
        if sr, sr_ok := claim_swizzle_result(g); sr_ok {
            src_arr_type := array_var_type(&sr)
            count := sr.capacity
            for i := 0; i < count; i += 1 {
                src_gep := fresh_tmp(g)
                emit_array_gep_const(g, src_gep, src_arr_type, sr.alloca, i)
                val := fresh_tmp(g)
                emit_load_into(g, val, elem_type, src_gep)
                dst_gep := fresh_tmp(g)
                emit_array_gep_const(g, dst_gep, arr_type, dst_ptr, i)
                emit_store(g, elem_type, val, dst_gep)
            }
            return
        }
        if av, av_ok := claim_field_array(g); av_ok {
            // Source and destination are both flat [N x T] of matching shape
            // (the type checker has verified this). Bulk memcpy is the
            // simplest correct lowering.
            emit_memcpy(g, dst_ptr, av.alloca, total_bytes)
            return
        }
    }

    // Array-returning function call: NRVO directly into dst_ptr.
    if call, ok := value.(^Expr_Call); ok {
        if info, info_ok := lookup_fun_info(g, call_resolved_name(call)); info_ok && info.ret_array_cap > 0 {
            // Build an Array_Var pointing at dst_ptr and route through the
            // existing array NRVO path.
            dst := Array_Var{alloca = dst_ptr, capacity = info.ret_array_cap, elem_type = info.ret_array_elem}
            gen_call_into_array(g, call, &dst, &info)
            return
        }
    }

    // Operator overload returning a fixed-array (e.g. `Quat * Quat → Quat`):
    // synthesize the resolved overload's call (same shape gen_binary builds)
    // and route through gen_call_into_array so the call writes directly into
    // dst_ptr as sret. The straight `gen_binary` path would also leave a
    // dangling temp_call_result set by gen_call's array-NRVO branch, which
    // the next scalar decl would mis-claim.
    if bin, ok := value.(^Expr_Binary); ok {
        if rf, rf_ok := bin.overload_fn.?; rf_ok {
            if info, info_ok := lookup_fun_info(g, rf.name); info_ok && info.ret_array_cap > 0 {
                call := new(Expr_Call)
                call.name = rf.name
                append(&call.args, bin.left)
                append(&call.args, bin.right)
                call.span = bin.span
                call.type_ = bin.type_
                call.resolved_func = rf
                dst := Array_Var{alloca = dst_ptr, capacity = info.ret_array_cap, elem_type = info.ret_array_elem}
                gen_call_into_array(g, call, &dst, &info)
                return
            }
        }
    }

    // Every supported RHS shape was checked above. Falling through here means
    // a new expression kind is reaching the array-store path without a
    // handler; emit a hard error rather than silently zeroing the destination
    // (which is exactly the kind of dropped-computation bug that motivated
    // CLAUDE.md's "errors over fallbacks" rule).
    codegen_fatal(g, {}, CODE_GEN_STORE_ARRAY_UNHANDLED_RHS)
}


// Single point of truth for "store a struct-typed value into a destination
// pointer". Replaces the duplicated dispatch logic that used to live in
// gen_struct_assign (local var), gen_field_assign (obj.f = ...),
// gen_deref_assign (p^ = ...), and gen_struct_store_at (array element).
//
// Handles every RHS shape that can produce a struct value:
//   - struct literal (with optional constructor / defaults / field overrides)
//   - struct ident (memcpy from src var)
//   - struct field-access (memcpy from src field address)
//   - pure-struct constructor call Foo() — zero-arg variant (routes through init)
//   - pure-struct positional constructor Foo(a, b, c) — inline field stores
//   - regular struct-returning function call — NRVO direct into dst
//   - overloaded binary operator returning a struct
//   - fallback expression (memcpy from result pointer)
//
// Call.overrides (the `{...}` block after a constructor call) are applied last
// for every call shape, matching the rule "{} always happens after the
// constructor".
gen_store_struct_into :: proc(g: ^Codegen, dst_ptr: string, st: ^Scope_Body, value: Expr) {
    llvm_name := struct_llvm_name(struct_key(st))
    total := struct_byte_size(st, g.checked)

    if lit, ok := value.(^Expr_Struct_Literal); ok {
        // Zero-init first, run the struct's init function to apply defaults
        // (and any imperative body), then layer the literal's explicit field
        // assignments on top. `{0}` (lit.zero_init) skips the constructor —
        // the zero memset stands alone. Structs without an init function
        // stay zero (no defaults to apply by construction).
        emit_memset_zero(g, dst_ptr, total)
        if !lit.zero_init {
            if _, has_init := g.checked.functions[st.name]; has_init {
                emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(ptr ", dst_ptr, ")"}))
            }
        }
        apply_struct_literal_fields(g, lit, st, llvm_name, dst_ptr)
        return
    }

    if ident, ok := value.(^Expr_Ident); ok {
        if src_sv, sv_ok := get_struct(g, ident.name); sv_ok {
            emit_memcpy(g, dst_ptr, src_sv.alloca, total)
            return
        }
    }

    if fa, ok := value.(^Expr_Field_Access); ok {
        src_ptr := gen_field_address(g, fa)
        if src_ptr != "null" {
            emit_memcpy(g, dst_ptr, src_ptr, total)
            return
        }
    }

    if call, ok := value.(^Expr_Call); ok {
        resolved_name := call_resolved_name(call)

        // Foreign struct-returning call: must use .C ABI lowering at the call
        // site (sret + byval + correct attribute order), so route through
        // gen_call (which dispatches to gen_c_call) and memcpy the result.
        // gen_call_into_struct's NRVO shape is Mara-internal and doesn't
        // emit the C ABI attributes.
        if cs, cs_ok := g.checked.functions[resolved_name]; cs_ok {
            if _, is_foreign := cs.origin.(Origin_Foreign); is_foreign {
                result_ptr := gen_call(g, call)
                if result_ptr != "0" {
                    emit_memcpy(g, dst_ptr, result_ptr, total)
                }
                return
            }
        }

        _, is_pure_struct := g.checked.table.structs[st.name]
        _, has_init := g.checked.functions[st.name]
        // Pure-self-ctor: the call target is the struct's own auto-init function,
        // and the struct has no callable params (pure data layout with field
        // defaults). For these, positional args map to fields — NRVO would
        // pass them as function args, which the zero-arg init can't accept.
        // For paramized structs (Arena_Basic in funs, not structs) is_pure_struct
        // is false, so NRVO still fires correctly and forwards ctor args as
        // function args (which the init does take).
        is_pure_self_ctor := is_pure_struct && resolved_name == st.name

        // NRVO: if this resolves to a function that returns a struct, write
        // into dst_ptr directly. Skipped for pure-self-ctor calls — the
        // positional/zero-arg branches below handle those. Distinct from
        // calls like `o.inner = make_inner()` where the function name differs
        // from the destination struct's name: NRVO still applies there.
        if !is_pure_self_ctor {
            if info, info_ok := lookup_fun_info(g, resolved_name); info_ok && info.ret_struct != "" {
                gen_call_into_struct(g, call, dst_ptr, &info)
                if call.overrides != nil {
                    apply_struct_literal_fields(g, call.overrides, st, llvm_name, dst_ptr)
                }
                return
            }
        }

        // Pure-struct zero-arg constructor `Foo()`: route through init function.
        if is_pure_struct && len(call.args) == 0 && has_init {
            emit_raw(g, strings.concatenate({"  call void ", mara_fn_name(g, st.name), "(ptr ", dst_ptr, ")"}))
            if call.overrides != nil {
                apply_struct_literal_fields(g, call.overrides, st, llvm_name, dst_ptr)
            }
            return
        }

        // Pure-struct positional constructor `Foo(a, b, c)`: inline field stores
        // by position + defaults for unprovided trailing fields.
        if is_pure_self_ctor && len(call.args) > 0 {
            emit_memset_zero(g, dst_ptr, total)
            for arg, i in call.args {
                if i >= len(st.fields) { break }
                field := &st.fields[i]
                ft := field_ir_type(field)
                val := gen_expr(g, arg, ft)
                gep := fresh_tmp(g)
                emit_field_gep_into(g, gep, llvm_name, dst_ptr, i)
                emit_store(g, ft, val, gep)
            }
            for fi := len(call.args); fi < len(st.fields); fi += 1 {
                field := &st.fields[fi]
                if field.default_value != nil {
                    ft := field_ir_type(field)
                    val := gen_expr(g, field.default_value, ft)
                    gep := fresh_tmp(g)
                    emit_field_gep_into(g, gep, llvm_name, dst_ptr, fi)
                    emit_store(g, ft, val, gep)
                }
            }
            if call.overrides != nil {
                apply_struct_literal_fields(g, call.overrides, st, llvm_name, dst_ptr)
            }
            return
        }
    }

    if bin, ok := value.(^Expr_Binary); ok {
        if _, rf_ok := bin.overload_fn.?; rf_ok {
            result_ptr := gen_binary(g, bin)
            emit_memcpy(g, dst_ptr, result_ptr, total)
            return
        }
    }

    // Fallback: evaluate the expression and expect a pointer back, then memcpy.
    src_ptr := gen_expr(g, value, llvm_name)
    emit_memcpy(g, dst_ptr, src_ptr, total)
}

// Thin wrapper over gen_store_struct_into for callers that have a struct name
// rather than a Scope_Body. Kept as the migration target for callers that
// still use the old name.
gen_struct_store_at :: proc(g: ^Codegen, dst_ptr: string, struct_name: string, value: Expr) {
    st, st_ok := lookup_struct(g, struct_name)
    if !st_ok {
        codegen_fatal(g, {}, CODE_GEN_STRUCT_STORE_UNKNOWN_STRUCT, struct_name)
    }
    if value == nil {
        // Bare "store nothing" — same effect as the old fallback: zero + cap init.
        total := struct_byte_size(st, g.checked)
        emit_memset_zero(g, dst_ptr, total)
        return
    }
    gen_store_struct_into(g, dst_ptr, st, value)
}

// If `t` is a sized-slice type (distinct alias wrapping a slice with a default
// cap, e.g. `String :: type([, 0]utf8(128))`), return (cap_n, slice, true).
sized_slice_info :: proc(g: ^Codegen, t: Type) -> (int, ^Type_Slice, bool) {
    dt, is_distinct := t.(^Type_Distinct)
    if !is_distinct { return 0, nil, false }
    sl, is_slice := dt.base_type.(^Type_Slice)
    if !is_slice { return 0, nil, false }
    if dt.default_cap_expr == nil { return 0, nil, false }
    n, n_ok := codegen_const_eval_int(g, dt.default_cap_expr)
    if !n_ok { return 0, nil, false }
    return n, sl, true
}

// True when `value` is a call to a struct-returning function that NRVO's its
// return. The callee then constructs directly into the caller's sret slot,
// including writing sized-slice headers, so any caller-side re-init would
// just store the same values back.
value_is_nrvo_call :: proc(g: ^Codegen, value: Expr) -> bool {
    call, ok := value.(^Expr_Call)
    if !ok { return false }
    info, info_ok := lookup_fun_info(g, call_resolved_name(call))
    if !info_ok { return false }
    return info.uses_struct_nrvo
}

// GEP to the position `offset` within the struct's hidden trailing backing
// buffer (field index = len(st.fields)). Returns a pointer suitable for use
// as a slice's data field.
emit_struct_backing_gep :: proc(g: ^Codegen, st_llvm: string, base_ptr: string, backing_field_idx: int, backing_size: int, offset: int) -> string {
    backing_ptr := fresh_tmp(g)
    emit_field_gep_into(g, backing_ptr, st_llvm, base_ptr, backing_field_idx)
    if offset == 0 { return backing_ptr }
    offset_ptr := fresh_tmp(g)
    backing_arr_type := fmt.tprintf("[%d x i8]", backing_size)
    emit_array_gep_const(g, offset_ptr, backing_arr_type, backing_ptr, offset)
    return offset_ptr
}

// After a struct alloca's memset-zero, walk its fields and initialize slice
// headers for any sized-slice-typed field (direct or inside a fixed-array
// field). The data pointer for each slice points at a slot within the
// struct's own hidden trailing backing buffer, so the backing rides along
// with the struct on sret/memcpy.
//
// Recurses into nested struct fields (their backing is in their own layout).
//
// Caveat: a downstream memcpy of the struct copies the slice headers verbatim,
// so the data pointers still reference the SOURCE's backing — pointers are
// only correct under in-place / RVO construction. Reaching after a copy is
// undefined until copy semantics are addressed (see project_pointer_ref_mutable).
emit_nested_sized_slice_init :: proc(g: ^Codegen, base_ptr: string, st: ^Scope_Body) {
    st_llvm := struct_llvm_name(struct_key(st))
    backing_field_idx := len(st.fields)
    backing_offset := 0
    for &f, fi in st.fields {
        if cap_n, sl, ok := sized_slice_info(g, f.type_); ok {
            alloc_cap := cap_n
            if sl.has_sentinel { alloc_cap += 1 }
            elem_bytes := elem_byte_size(llvm_type_from_checker(sl.elem), g.checked)
            field_size := alloc_cap * elem_bytes

            hdr_ptr := fresh_tmp(g)
            emit_field_gep_into(g, hdr_ptr, st_llvm, base_ptr, fi)
            data_ptr := emit_struct_backing_gep(g, st_llvm, base_ptr, backing_field_idx, st.backing_bytes, backing_offset)
            ptr_gep := fresh_tmp(g)
            emit_slice_gep(g, ptr_gep, hdr_ptr, SLICE.ptr)
            emit_store(g, "ptr", data_ptr, ptr_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, hdr_ptr, SLICE.cap)
            emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)

            backing_offset += field_size
            continue
        }
        if fa, fa_ok := f.type_.(^Type_Fixed_Array); fa_ok {
            if cap_n, sl, ok := sized_slice_info(g, fa.elem); ok {
                alloc_cap := cap_n
                if sl.has_sentinel { alloc_cap += 1 }
                elem_bytes := elem_byte_size(llvm_type_from_checker(sl.elem), g.checked)
                slot_bytes := alloc_cap * elem_bytes

                arr_ptr := fresh_tmp(g)
                emit_field_gep_into(g, arr_ptr, st_llvm, base_ptr, fi)
                arr_type := strings.concatenate({"[", fmt.tprintf("%d", fa.size), " x ", SLICE_IR_TYPE, "]"})

                for i in 0..<fa.size {
                    slot_hdr := fresh_tmp(g)
                    emit_raw(g, strings.concatenate({"  ", slot_hdr, " = getelementptr ", arr_type, ", ptr ", arr_ptr, ", i64 0, i64 ", fmt.tprintf("%d", i)}))

                    slot_offset := backing_offset + i * slot_bytes
                    data_ptr := emit_struct_backing_gep(g, st_llvm, base_ptr, backing_field_idx, st.backing_bytes, slot_offset)
                    ptr_gep := fresh_tmp(g)
                    emit_slice_gep(g, ptr_gep, slot_hdr, SLICE.ptr)
                    emit_store(g, "ptr", data_ptr, ptr_gep)
                    cap_gep := fresh_tmp(g)
                    emit_slice_gep(g, cap_gep, slot_hdr, SLICE.cap)
                    emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)
                }

                backing_offset += fa.size * slot_bytes
                continue
            }
        }
        if pa, pa_ok := distinct_base(f.type_).(^Type_Partial_Array); pa_ok {
            // Partial-array field: header lives at the field's start, inline
            // storage at field 3 of the partial-array shape. The shared
            // memset zeroed both already; here we anchor ptr → &elements and
            // write the physical cap (N+1 when sentinel). Mirrors the local
            // partial-array decl in codegen_stmt.odin's Type_Partial_Array
            // branch. Without this, `Holder{0}` left h.name.cap = 0 and the
            // first append hit a 0-cap bounds failure.
            alloc_cap := pa.size
            if pa.has_sentinel { alloc_cap += 1 }
            elem_t := llvm_type_from_checker(pa.elem)
            ir_type := partial_array_ir_type(elem_t, alloc_cap)
            hdr_ptr := fresh_tmp(g)
            emit_field_gep_into(g, hdr_ptr, st_llvm, base_ptr, fi)
            elements_ptr := fresh_tmp(g)
            emit_raw(g, strings.concatenate({"  ", elements_ptr, " = getelementptr inbounds ", ir_type, ", ptr ", hdr_ptr, ", i32 0, i32 ", fmt.tprintf("%d", PARTIAL_ELEMENTS_FIELD), ", i32 0"}))
            ptr_gep := fresh_tmp(g)
            emit_slice_gep(g, ptr_gep, hdr_ptr, SLICE.ptr)
            emit_store(g, "ptr", elements_ptr, ptr_gep)
            cap_gep := fresh_tmp(g)
            emit_slice_gep(g, cap_gep, hdr_ptr, SLICE.cap)
            emit_typed_store_cap(g, fmt.tprintf("%d", alloc_cap), cap_gep)
            continue
        }
        if inner_sd := as_struct_body(f.type_); inner_sd != nil {
            inner_checked, ic_ok := lookup_struct(g, inner_sd.name)
            if !ic_ok { continue }
            field_gep := fresh_tmp(g)
            emit_field_gep_into(g, field_gep, st_llvm, base_ptr, fi)
            emit_nested_sized_slice_init(g, field_gep, inner_checked)
        }
    }
}

// Handle: obj.field = value (write)
// Write to a slice's `.len` / `.cap` through its header pointer. Slices are
// reference types, so any path that produces the header alloca pointer can
// also feed this — ident slice vars, slice fields, indexed slice elements.
gen_slice_field_store :: proc(g: ^Codegen, slice_hdr_ptr: string, field: string, value: Expr, span: Span) {
    field_ir: string
    field_idx := 0
    switch field {
    case "len":
        field_idx = SLICE.len
        field_ir  = slice_layout.len_ir
    case "cap":
        field_idx = SLICE.cap
        field_ir  = slice_layout.cap_ir
    case:
        codegen_fatal(g, span, CODE_CANNOT_ASSIGN_SLICE_FIELD_ONLY, field)
    }
    // Type checker enforces the value is field-width — store directly,
    // no extend/trunc dance.
    val := gen_expr(g, value, field_ir)

    // Enforce slice invariant on `.len` writes: 0 <= new_len <= cap. Without
    // this, FFI fill patterns (`data.len = i32(bytes_read)`) and other manual
    // bookkeeping could lie about the populated extent, and subsequent
    // indexing would honor the lie. Compile-time elision applies when both
    // new_len and cap are integer literals at codegen time.
    if field == "len" {
        cap_gep := fresh_tmp(g)
        emit_slice_gep(g, cap_gep, slice_hdr_ptr, SLICE.cap)
        cap_val := fresh_tmp(g)
        emit_typed_load_cap(g, cap_val, cap_gep)

        w := slice_layout.len_ir
        ok_label   := fresh_label(g, "slice_len.ok")
        fail_label := fresh_label(g, "slice_len.fail")

        neg_cmp := fresh_tmp(g)
        emit(g, "  %s = icmp slt %s %s, 0", neg_cmp, w, val)
        upper_cmp := fresh_tmp(g)
        emit(g, "  %s = icmp sgt %s %s, %s", upper_cmp, w, val, cap_val)
        combined := fresh_tmp(g)
        emit(g, "  %s = or i1 %s, %s", combined, neg_cmp, upper_cmp)
        emit_cond_br(g, combined, fail_label, ok_label)

        emit_label(g, fail_label)
        loc := format_location(span.file, span.line, span.col)
        loc_global,  _ := get_string_literal(g, loc)
        name_global, _ := get_string_literal(g, "slice")
        emit(g, "  call void %s(ptr %s, %s %s, %s %s, ptr %s)",
            __MARA_SLICE_LEN_FAIL, loc_global, w, val, w, cap_val, name_global)
        emit(g, "  unreachable")

        emit_label(g, ok_label)
    }

    gep := fresh_tmp(g)
    emit_slice_gep(g, gep, slice_hdr_ptr, field_idx)
    emit_store(g, field_ir, val, gep)
}

gen_field_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    fa_expr := s.target.(^Expr_Field_Access)
    st: ^Scope_Body
    base_ptr: string
    found: bool

    ident, ident_ok := fa_expr.expr.(^Expr_Ident)
    if ident_ok {
        // context.scope_allocator = AllocatorType — compiler generates new() call at main setup
        if g.context_enabled && ident.name == "context" && fa_expr.field == "scope_allocator" {
            return // no-op: arena initialization is done in main setup
        }

        // Array swizzle write: arr.x = val, arr.xy = [a, b]
        if av, av_ok := get_array(g, ident.name); av_ok {
            if is_swizzle_field(fa_expr.field, av.capacity) {
                if len(fa_expr.field) == 1 {
                    gen_swizzle_write_single(g, &av, fa_expr.field, s.value)
                } else {
                    gen_swizzle_write_multi(g, &av, fa_expr.field, s.value)
                }
                return
            }
        }

        // Slice field write: slice_var.len = N, slice_var.cap = N
        if slv, slv_ok := get_slice(g, ident.name); slv_ok {
            gen_slice_field_store(g, slv.alloca, fa_expr.field, s.value, s.span)
            return
        }

        st, base_ptr, found = resolve_struct_for_field(g, ident.name, ident.type_, ident.span)
        if !found {
            if is_array(g, ident.name) {
                codegen_fatal(g, s.span, CODE_ARRAY_VALID_SWIZZLE_USE_XYZW, ident.name, fa_expr.field)
            } else {
                codegen_fatal(g, s.span, CODE_FIELD_STRUCT_ARRAY, ident.name, fa_expr.field)
            }
        }
    } else {
        // Try chained field access that ends at an array (for swizzle writes like mvp.data.x.xyz = ...)
        if inner_fa, inner_ok := fa_expr.expr.(^Expr_Field_Access); inner_ok {
            // Only emit gen_field_access (which walks the chain and emits IR)
            // when the inner FA could actually be claimed below as an array or
            // slice. For ordinary struct-typed inner FAs, the address chain
            // would just be re-computed by resolve_lhs_struct further down,
            // and the IR emitted here would be dead code.
            inner_type := distinct_base(expr_type(inner_fa))
            _, inner_is_array := inner_type.(^Type_Fixed_Array)
            _, inner_is_slice := inner_type.(^Type_Slice)
            if inner_is_array || inner_is_slice {
                gen_field_access(g, inner_fa)
                if ar, ar_ok := claim_field_array(g); ar_ok {
                    if is_swizzle_field(fa_expr.field, ar.capacity) {
                        if len(fa_expr.field) == 1 {
                            gen_swizzle_write_single(g, &ar, fa_expr.field, s.value)
                        } else {
                            gen_swizzle_write_multi(g, &ar, fa_expr.field, s.value)
                        }
                        return
                    }
                }
                // Slice field write via chained access: obj.slice_field.len = N
                if slv, slv_ok := claim_field_slice(g); slv_ok {
                    gen_slice_field_store(g, slv.alloca, fa_expr.field, s.value, s.span)
                    return
                }
            }
        }
        // Slice field write via index: arr[i].len = N where arr[i] is a slice.
        // The element address IS the slice header — gen_index_address gives it.
        // Same path covers `arr[i]: [..N]T` partial arrays: their first 24
        // bytes are layout-compatible with a slice header, and the field
        // store hits the same offsets.
        if idx_expr, idx_ok := fa_expr.expr.(^Expr_Index); idx_ok {
            idx_type := distinct_base(expr_type(idx_expr))
            if _, is_slice := idx_type.(^Type_Slice); is_slice {
                slice_hdr_ptr := gen_index_address(g, idx_expr)
                gen_slice_field_store(g, slice_hdr_ptr, fa_expr.field, s.value, s.span)
                return
            }
            if _, is_pa := idx_type.(^Type_Partial_Array); is_pa {
                slice_hdr_ptr := gen_index_address(g, idx_expr)
                gen_slice_field_store(g, slice_hdr_ptr, fa_expr.field, s.value, s.span)
                return
            }
        }
        // Chained field access: obj.inner.field = value
        st, base_ptr, found = resolve_lhs_struct(g, fa_expr.expr)
        if !found {
            codegen_fatal(g, s.span, CODE_FIELD_ASSIGNMENT_TARGET_STRUCT_POINTER)
        }
    }

    st_llvm := struct_llvm_name(struct_key(st))
    idx := struct_field_index(st, fa_expr.field)
    if idx >= 0 {
        f := &st.fields[idx]
        ft := field_ir_type(f)
        // Byte-buffer reinterpret read: obj.field = mem[lo:hi] or obj.field = mem[off].
        // Memcpys field-sized bytes from the source into the field GEP.
        if sl_expr, ok := s.value.(^Expr_Slice); ok && codegen_is_byte_buffer_source(g, sl_expr.expr) {
            gen_byte_target_field_read(g, st_llvm, base_ptr, idx, f, sl_expr.expr, sl_expr.low, s.span)
            return
        }
        if idx_expr, ok := s.value.(^Expr_Index); ok && codegen_is_byte_buffer_source(g, idx_expr.expr) {
            gen_byte_target_field_read(g, st_llvm, base_ptr, idx, f, idx_expr.expr, idx_expr.index, s.span)
            return
        }
        // Array field — dispatch to array store helper
        acap := field_array_cap(f)
        if acap > 0 {
            data_gep := fresh_tmp(g)
            emit_field_gep_into(g, data_gep, st_llvm, base_ptr, idx)
            apply_compound_load_substitute(g, s, data_gep, ft)
            gen_array_field_store(g, data_gep, acap, field_array_elem(f), s.value)
            return
        }
        // Union field — emit tag + payload stores directly into the field GEP
        if ut, ut_ok := f.type_.(^Type_Union); ut_ok {
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
            emit_union_literal_store(g, ut, s.value, gep)
            return
        }
        // Struct field — delegate to the unified struct store primitive.
        // Handles every RHS shape (literal, ident, field access, call with
        // NRVO, constructor, overloaded binary) in one place.
        if field_sd := as_struct_body(f.type_); field_sd != nil {
            if checked_field_st, cs_ok := lookup_struct(g, field_sd.name); cs_ok {
                gep := fresh_tmp(g)
                emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
                apply_compound_load_substitute(g, s, gep, struct_llvm_name(field_sd.name))
                gen_store_struct_into(g, gep, checked_field_st, s.value)
                return
            }
        }
        // Slice field — slice IR is `{ ptr, i64 }`; a scalar store of that
        // type from a `ptr` value would be invalid IR (same shape as the
        // struct bug). Route through gen_store_slice_into.
        if _, sl_ok := f.type_.(^Type_Slice); sl_ok {
            gep := fresh_tmp(g)
            emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
            gen_store_slice_into(g, gep, s.value)
            return
        }
        // Scalar field — compute the GEP first so the compound-load substitute
        // can pre-load the current value through it before gen_expr runs.
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, st_llvm, base_ptr, idx)
        apply_compound_load_substitute(g, s, gep, ft)
        val := gen_expr(g, s.value, ft)
        emit_store(g, ft, val, gep)
        return
    }

    // Try using-promoted field (two-level GEP)
    up, up_ok := resolve_using_field(g, st, fa_expr.field)
    if up_ok {
        val := gen_expr(g, s.value, up.inner_ir_type)
        gep1 := fresh_tmp(g)
        emit_field_gep_into(g, gep1, st_llvm, base_ptr, up.outer_index)
        gep2 := fresh_tmp(g)
        emit_field_gep_into(g, gep2, struct_llvm_name(struct_key(up.inner_st)), gep1, up.inner_index)
        emit_store(g, up.inner_ir_type, val, gep2)
        return
    }

    codegen_fatal(g, s.span, CODE_CLASS_FIELD, struct_key(st), fa_expr.field)
}

gen_deref_assign :: proc(g: ^Codegen, s: ^Stmt_Assign) {
    un := s.target.(^Expr_Unary)
    ptr_val := gen_expr(g, un.operand)

    // Null pointer check before dereference-assign
    deref_name := "ptr"
    if ident, ok := un.operand.(^Expr_Ident); ok {
        deref_name = ident.name
    }
    emit_null_check(g, ptr_val, deref_name, s.span)

    // Determine the store type from the typed AST annotation
    store_type := "i64"
    if s.target_type != nil && !is_untyped(s.target_type) {
        store_type = llvm_type_from_checker(s.target_type)
    }

    // Struct deref-assign: aggregates aren't a single LLVM scalar, so a
    // `store %class.X X, ptr P` form is invalid. Delegate to the unified
    // struct store primitive, which handles every RHS shape (including
    // struct-returning function calls — see test_deref_from_call).
    if sd := as_struct_body(s.target_type); sd != nil {
        if checked_st, cs_ok := lookup_struct(g, sd.name); cs_ok {
            apply_compound_load_substitute(g, s, ptr_val, store_type)
            gen_store_struct_into(g, ptr_val, checked_st, s.value)
            return
        }
    }

    apply_compound_load_substitute(g, s, ptr_val, store_type)
    // Type checker enforces value type matches store_type; pass the target
    // type so infer literals produce the right width directly.
    val := gen_expr(g, s.value, store_type)

    emit_store(g, store_type, val, ptr_val)
}

// ---------------------------------------------------------------------------
// Array swizzle codegen (xyzw / rgba)
// ---------------------------------------------------------------------------

// Single-component swizzle read: arr.x → scalar
gen_swizzle_read_single :: proc(g: ^Codegen, av: ^Array_Var, field: string) -> string {
    idx := swizzle_char_to_index(field[0])
    arr_type := array_var_type(av)
    gep := fresh_tmp(g)
    emit_array_gep_const(g, gep, arr_type, av.alloca, idx)
    val := fresh_tmp(g)
    emit_load_into(g, val, av.elem_type, gep)
    return val
}

// Multi-component swizzle read: arr.xy → new temp array
gen_swizzle_read_multi :: proc(g: ^Codegen, av: ^Array_Var, field: string) -> string {
    count := len(field)
    elem_type := av.elem_type
    tmp_arr_type := fmt.tprintf("[%d x %s]", count, elem_type)

    // Allocate temp array
    data_name := fmt.tprintf("%%__swizzle_%d.data", g.tmp_counter)
    g.tmp_counter += 1
    emit_alloca(g, data_name, tmp_arr_type)

    // Copy each swizzled element from source
    src_arr_type := array_var_type(av)
    for i := 0; i < count; i += 1 {
        idx := swizzle_char_to_index(field[i])
        src_gep := fresh_tmp(g)
        emit_array_gep_const(g, src_gep, src_arr_type, av.alloca, idx)
        val := fresh_tmp(g)
        emit_load_into(g, val, elem_type, src_gep)
        dst_gep := fresh_tmp(g)
        emit_array_gep_const(g, dst_gep, tmp_arr_type, data_name, i)
        emit_store(g, elem_type, val, dst_gep)
    }

    // Register as temp swizzle result so assignment codegen can adopt it
    set_swizzle_result(g, Array_Var{
        alloca    = data_name,
        capacity  = count,
        elem_type = elem_type,
    })

    return data_name
}

// Single-component swizzle write: arr.x = value
gen_swizzle_write_single :: proc(g: ^Codegen, av: ^Array_Var, field: string, value: Expr) {
    idx := swizzle_char_to_index(field[0])
    val := gen_expr(g, value, av.elem_type)
    arr_type := array_var_type(av)
    gep := fresh_tmp(g)
    emit_array_gep_const(g, gep, arr_type, av.alloca, idx)
    emit_store(g, av.elem_type, val, gep)
}

// Multi-component swizzle write: arr.xy = [a, b] or arr.xy = other
gen_swizzle_write_multi :: proc(g: ^Codegen, av: ^Array_Var, field: string, value: Expr) {
    dst_arr_type := array_var_type(av)

    // Case 1: RHS is an array literal — gen each element directly
    if arr_lit, arr_ok := value.(^Expr_Array); arr_ok {
        for i := 0; i < len(field); i += 1 {
            dst_idx := swizzle_char_to_index(field[i])
            if i < len(arr_lit.elements) {
                elem_val := gen_expr(g, arr_lit.elements[i], av.elem_type)
                gep := fresh_tmp(g)
                emit_array_gep_const(g, gep, dst_arr_type, av.alloca, dst_idx)
                emit_store(g, av.elem_type, elem_val, gep)
            }
        }
        return
    }

    // Case 2: RHS is a named array variable
    if ident, id_ok := value.(^Expr_Ident); id_ok {
        if src_av, nav_ok := get_array(g, ident.name); nav_ok {
            src_arr_type := array_var_type(&src_av)
            for i := 0; i < len(field); i += 1 {
                dst_idx := swizzle_char_to_index(field[i])
                src_gep := fresh_tmp(g)
                emit_array_gep_const(g, src_gep, src_arr_type, src_av.alloca, i)
                elem := fresh_tmp(g)
                emit_load_into(g, elem, av.elem_type, src_gep)
                dst_gep := fresh_tmp(g)
                emit_array_gep_const(g, dst_gep, dst_arr_type, av.alloca, dst_idx)
                emit_store(g, av.elem_type, elem, dst_gep)
            }
            return
        }
    }

    // Case 3: RHS is an expression that produces a swizzle result (e.g. another swizzle)
    gen_expr(g, value, av.elem_type)
    if sr, sr_ok := claim_swizzle_result(g); sr_ok {
        src_arr_type := array_var_type(&sr)
        for i := 0; i < len(field); i += 1 {
            dst_idx := swizzle_char_to_index(field[i])
            src_gep := fresh_tmp(g)
            emit_array_gep_const(g, src_gep, src_arr_type, sr.alloca, i)
            elem := fresh_tmp(g)
            emit_load_into(g, elem, av.elem_type, src_gep)
            dst_gep := fresh_tmp(g)
            emit_array_gep_const(g, dst_gep, dst_arr_type, av.alloca, dst_idx)
            emit_store(g, av.elem_type, elem, dst_gep)
        }
        return
    }

    codegen_fatal(g, {}, CODE_MULTI_COMPONENT_SWIZZLE_WRITE_REQUIRES)
}

// ---------------------------------------------------------------------------
// Union codegen
// ---------------------------------------------------------------------------

gen_union_assign :: proc(g: ^Codegen, name: string, ut: ^Type_Union, value: Expr) {
    ukey := union_key(ut)
    llvm_name := union_llvm_name(ukey)

    // Alloca if variable doesn't exist yet
    if _, already_exists := get_union(g, name); !already_exists {
        alloca_name := fmt.tprintf("%%%s", name)
        emit_alloca(g, alloca_name, llvm_name)
        g.all_vars[name] = Union_Var{
            alloca = alloca_name,
            union_name  = ukey,
        }
    }

    uv, _ := get_union(g, name)
    emit_union_literal_store(g, ut, value, uv.alloca)
}

// Emit the tag+payload store sequence for a union literal at `union_ptr`.
// `union_ptr` must point at storage laid out as the union's LLVM type
// (i.e. `%union.X = type { tag, [N x i8] }`). Used by both direct union
// variable assignment and struct-field assignment where the field type
// is a union.
emit_union_literal_store :: proc(g: ^Codegen, ut: ^Type_Union, value: Expr, union_ptr: string) {
    ukey := union_key(ut)
    llvm_name := union_llvm_name(ukey)
    tag_ir := union_tag_ir_type(ut)

    lit, ok := value.(^Expr_Struct_Literal)
    if !ok || lit.name == "" {
        codegen_fatal(g, {}, CODE_UNION_ASSIGNMENT_REQUIRES_NAMED_STRUCT)
    }

    tag, tag_ok := ut.tag_map[lit.name]
    if !tag_ok {
        codegen_fatal(g, lit.span, CODE_VARIANT_UNION, lit.name, ukey)
    }

    // Niche layout: union storage is just a pointer. Some{value = p} writes
    // p; None{} writes null. No tag, no separate payload region.
    if is_niche_layout(g, ut) {
        some_name, _ := niche_variants(g, ut)
        if lit.name == some_name {
            // Find the single pointer field and store its value at offset 0.
            if len(lit.fields) > 0 {
                val := gen_expr(g, lit.fields[0].value, "ptr")
                emit_store(g, "ptr", val, union_ptr)
            } else {
                // Some{} with no fields — caller meant Some(zero); store null.
                emit_store(g, "ptr", "null", union_ptr)
            }
        } else {
            // None{} — store null sentinel.
            emit_store(g, "ptr", "null", union_ptr)
        }
        return
    }

    // Store tag at field 0
    tag_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 0", tag_ptr, llvm_name, union_ptr)
    emit(g, "  store %s %d, ptr %s", tag_ir, tag, tag_ptr)

    // Get payload pointer (field 1)
    payload_ptr := fresh_tmp(g)
    emit(g, "  %s = getelementptr %s, ptr %s, i32 0, i32 1", payload_ptr, llvm_name, union_ptr)

    // Fill payload fields using the variant's struct layout
    variant_struct_name := ut.variant_structs[lit.name]
    vst, vst_ok := lookup_struct(g, variant_struct_name)
    if !vst_ok { return }
    vst_llvm := struct_llvm_name(variant_struct_name)

    for field in lit.fields {
        idx := struct_field_index(vst, field.name)
        if idx < 0 { continue }
        ft := field_ir_type(&vst.fields[idx])
        val := gen_expr(g, field.value, ft)
        gep := fresh_tmp(g)
        emit_field_gep_into(g, gep, vst_llvm, payload_ptr, idx)
        emit_store(g, ft, val, gep)
    }
    // Fill in defaults for variant fields (skip for {0} zero-init)
    if !lit.zero_init {
        for &sdf, sdf_i in vst.fields {
            if sdf.default_value == nil { continue }
            provided := false
            for field in lit.fields {
                if field.name == sdf.name { provided = true; break }
            }
            if !provided {
                sdf_ft := field_ir_type(&sdf)
                val := gen_expr(g, sdf.default_value, sdf_ft)
                gep := fresh_tmp(g)
                emit_field_gep_into(g, gep, vst_llvm, payload_ptr, sdf_i)
                emit_store(g, sdf_ft, val, gep)
            }
        }
    }
}
