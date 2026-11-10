package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// What a value can do, for `mara ask what at` (the window's cursor block): what
// is built in for its type's kind — its fields, methods, operators, loops —
// then, a module to a line, the funs in sight where it's asked whose first
// param takes it (`x.f()` or `f(x)`, `f(&x)` for a pointer param). A dispatch
// group is named for its members; the groups behind operators (core's add for
// `++`) are said by the operator. A generic fun's first param is matched by its
// shape: `[]$T` takes any slice, list or array, `^Map($K, $V)` any Map.
// ---------------------------------------------------------------------------

CAN_DO_FUNS :: 24   // a module's funs shown, at most
CAN_DO_FLOAT :: "+ - * /   == < <= > >=   i64(x) f64(x) f32(x)   text: float_text(x, decimals) in mara.string"

// The "operations" section: what a value of type ty can do, asked where `at` is.
can_do :: proc(sb: ^strings.Builder, checked: ^Checked_Program, ty: Type, at: Token_Id) {
    if checked == nil || ty == nil { return }
    // (A literal's type not settled by its uses: what it is then.)
    ty := resolve_infer(ty)
    #partial switch _ in ty {
    case Type_Infer_Int:   ty = Type_Numeric{kind = .Signed, bits = 64}
    case Type_Infer_Float: ty = Type_F64{}
    }
    built := can_do_builtin(ty)
    funs := can_do_funs(checked, ty, at)
    if len(built) == 0 && len(funs) == 0 { return }
    fmt.sbprint(sb, "\noperations\n")
    for line in built { fmt.sbprintf(sb, "  %s\n", line) }
    for line in funs { fmt.sbprintf(sb, "  %s\n", line) }
}

// What's built in for a type's kind, a line or two.
can_do_builtin :: proc(ty: Type) -> []string {
    out := make([dynamic]string, context.temp_allocator)
    name := type_name(ty)
    if d, is_d := ty.(^Type_Distinct); is_d && !d.is_alias {
        append(&out, fmt.tprintf("%s(x) makes one of its base, %s: a type of its own, mixed with nothing else", name, type_name(d.base_type)))
    }
    #partial switch v in distinct_base(ty) {
    case Type_Numeric:
        if v.kind == .Float {
            append(&out, CAN_DO_FLOAT)
        } else {
            append(&out, "+ - * / %   +% -% *% wrap around   & | ~ << >>   == < <= > >=   f64(x) i64(x) u8(x)   text: int_text(n) in mara.string")
        }
    case Type_F64:
        append(&out, CAN_DO_FLOAT)
    case Type_Bool:
        append(&out, "and  or  not  ==   no text of its own: `if b do \"on\" else \"off\"`")
    case Type_Utf8:
        append(&out, "== < >   i64(c)  utf8(n)   &text ++ c")
    case Type_Byte:
        append(&out, "== (0 to 255)   a value read out of bytes: `v : u8 = bytes[k]`")
    case Type_Atom:
        append(&out, "print   goes where text goes (`&t ++ a`)   ==")
    case Type_CString:
        append(&out, "text for a C fun: `cstring(buf)` makes one")
    case Type_Err:
        append(&out, "if e   ?   ==   match   .text()   .where()   .trace()")
    case ^Type_Ptr:
        line := "p^   p^ = v   == void (test it before reading through it)"
        if sd, is_scope := distinct_base(v.elem).(^Type_Scope); is_scope && sd.kind == .Struct { line = "p.field   p^   p^ = v   == void (test it before reading through it)" }
        append(&out, line)
        for line in can_do_builtin(v.elem) { append(&out, fmt.tprintf("through it: %s", line)) }
    case ^Type_Field:
        append(&out, fmt.tprintf("s[f]   .text()   i64(f)   ==   == void   back from text: R.from_text(s), R :: alias %s", name))
    case ^Type_Enum:
        if v.is_error_kind {
            append(&out, "if e   ?   ==   match   .text()   .where()   .trace()")
        } else {
            append(&out, fmt.tprintf(".text()   %s.from_text(s)   i64(e)   %s(n)   ==   if e   match   for v in %s", name, name, name))
        }
    case ^Type_Union:
        line := ".tag   match   u.tag == .V"
        if v.tag_pad != nil { line = ".tag   .pad   match   u.tag == .V" }
        append(&out, line)
    case ^Type_Slice:
        if _, text := v.elem.(Type_Utf8); text {
            append(&out, ".len .cap   t[i]   t[a:b]   for c, i in t   ==   &t ++ \"more\" within its cap")
        } else {
            append(&out, ".len .cap .ptr   s[i]   s[a:b]   for x, i in s   for &x in s   &s ++ x within its cap")
        }
    case ^Type_Partial_Array:
        if _, text := v.elem.(Type_Utf8); text {
            append(&out, ".len .cap   t[i]   t[a:b]   for c, i in t   ==   &t ++ \"more\"  &t ++ 'c'   t ++ \"x\" a new buffer   cstring(t)")
        } else {
            append(&out, ".len .cap   l[i]   l[a:b]   for x, i in l   for &x in l   x in l   &l ++ x   l ++ x a new list")
        }
    case ^Type_Fixed_Array:
        line := fmt.tprintf(".len .cap (%d)   a[i]   a[a:b]   for x, i in a   for &x in a", v.size)
        if v.index_type != nil {
            e := type_name(v.index_type)
            line = fmt.tprintf("%s   a[%s.v]   for v in %s do a[v] (i in a loop over a is a number)", line, e, e)
        } else if v.size <= 4 {
            line = fmt.tprintf("%s   .x .y .z .w  .xy .xyz", line)
        }
        append(&out, line)
    case ^Type_Scope:
        if v.is_module { break }
        if v.kind == .Fun {
            append(&out, "call it   == void")
            break
        }
        fields := make([dynamic]string, context.temp_allocator)
        for f in v.fields { if !strings.has_prefix(f.name, "_") { append(&fields, fmt.tprintf(".%s", f.name)) } }
        methods := make([dynamic]string, context.temp_allocator)
        for m, fn in v.functions {
            if fn == nil || fn.kind != .Fun || fn.source_name != "" && m != fn.source_name { continue }
            append(&methods, fmt.tprintf(".%s()", m))
        }
        slice.sort(methods[:])
        if len(fields) > 0 { append(&out, strings.join(fields[:], " ", context.temp_allocator)) }
        if len(methods) > 0 { append(&out, strings.join(methods[:], " ", context.temp_allocator)) }
        name = can_do_struct_name(v)
        append(&out, fmt.tprintf("%s{{…}}   print   into bytes: `bytes[k] = s`   for f in %s.T: its fields of type T", name, name))
    }
    return out[:]
}

// A struct's name as written: a generic one's instance by its template's
// (`Map`, not its instance's flat name).
@(private="file")
can_do_struct_name :: proc(sd: ^Type_Scope) -> string {
    t := &build_tree
    if sd.node != 0 {
        if len(t.parent) != len(t.tag) { tree_parents(t) }
        if d := t.parent[sd.node]; t.tag[d] == .Define { return tc_text(t.first[d]) }
    }
    return sd.source_name if sd.source_name != "" else sd.name
}

// A line for each module in sight at `at` with funs whose first param takes
// ty: the module, then the funs (a named use's as `m.f`).
can_do_funs :: proc(checked: ^Checked_Program, ty: Type, at: Token_Id) -> []string {
    rs := checked.rs
    if rs == nil || int(at) >= len(build_tokens) { return nil }
    operators := resolve_overload_names(rs)
    out := make([dynamic]string, context.temp_allocator)
    for m in resolve_modules_in_sight(rs, at) {
        names := make([dynamic]string, context.temp_allocator)
        grouped := make(map[string]bool, allocator = context.temp_allocator)
        for group, decls in m.dispatches {
            // (Its members, each of its declarations' `dispatch{ … }`.)
            members := make([dynamic]Token_Id, context.temp_allocator)
            for d in decls {
                def, has_def := rs.defs[d]
                if !has_def { continue }
                value := Tree_Id(build_tree.b[def])
                if build_tree.tag[value] == .Dispatch_Def { append(&members, ..tree_token_list(&build_tree, build_tree.a[value])) }
            }
            if group in operators {
                // (Said by its operator: its members aren't listed.)
                for each in members { grouped[tc_text(each)] = true }
                continue
            }
            for tok in members {
                member := tc_text(tok)
                ref, has := m.defs[member]
                if has && can_do_takes(checked, m.defs, ref, member, ty) {
                    append(&names, group)
                    for each in members { grouped[tc_text(each)] = true }
                    break
                }
            }
        }
        for name, ref in m.defs {
            if ref.kind != .Fun || strings.has_prefix(name, "__") || name in grouped || name in m.dispatches { continue }
            if can_do_takes(checked, m.defs, ref, name, ty) { append(&names, name) }
        }
        if len(names) == 0 { continue }
        slice.sort(names[:])
        shown := names[:min(len(names), CAN_DO_FUNS)]
        b := strings.builder_make(context.temp_allocator)
        fmt.sbprintf(&b, "%s:", m.name)
        for n in shown { fmt.sbprintf(&b, " %s%s", m.prefix, n) }
        if len(names) > len(shown) { fmt.sbprintf(&b, " … %d more", len(names) - len(shown)) }
        append(&out, strings.to_string(b))
    }
    return out[:]
}

// Whether a fun's first param takes a value of type ty.
@(private="file")
can_do_takes :: proc(checked: ^Checked_Program, defs: map[string]Ref, ref: Ref, name: string, ty: Type) -> bool {
    t := &build_tree
    def, has_def := checked.rs.defs[ref.decl]
    if !has_def { return false }
    value := Tree_Id(t.b[def])
    if value == 0 || t.tag[value] != .Fun_Def { return false }
    sv := scope_view(t, value)
    if len(sv.params) == 0 || t.tag[sv.params[0]] != .Param_Group { return false }
    tn := Tree_Id(tree_rec(t, t.b[sv.params[0]], 2)[0])
    if tn == 0 { return false }
    // (Generic — a `$` in its first param's type: that type as written, by
    // its shape. Else the checker's type of it.)
    if can_do_generic(tn) { return can_do_shape(checked, defs, tn, ty) }
    b, bound := checked_binding(checked, ref, name)
    fs, is_scope := b.(^Type_Scope)
    if !bound || !is_scope || fs.kind != .Fun || len(fs.params) == 0 { return false }
    return can_do_param(fs.params[0].type_, ty)
}

// Whether a type as written has a `$` in it: a generic param's.
@(private="file")
can_do_generic :: proc(tn: Tree_Id) -> bool {
    t := &build_tree
    if tn == 0 { return false }
    #partial switch t.tag[tn] {
    case .Type_Dollar:                return true
    case .Type_Paren, .Type_Pointer:  return can_do_generic(Tree_Id(t.a[tn]))
    case .Type_Slice, .Type_Partial, .Type_Array: return can_do_generic(Tree_Id(t.b[tn]))
    case .Type_Generic:
        for arg in tree_list(t, t.a[tn]) { if can_do_generic(arg) { return true } }
    }
    return false
}

// Whether a param of type p takes a value of type ty: as it is, or its
// pointer (`f(&x)`).
@(private="file")
can_do_param :: proc(p: Type, ty: Type) -> bool {
    #partial switch _ in p {
    case Type_Any, Type_Error, Type_Void, Type_Infer_Int, Type_Infer_Float: return false
    }
    if p == nil || types_equal(p, ty) { return true }
    pt, is_ptr := p.(^Type_Ptr)
    if !is_ptr { return false }
    #partial switch _ in pt.elem {
    case Type_Any, Type_Error, Type_Void: return false
    }
    return types_equal(pt.elem, ty)
}

// Whether a generic param's type, written at tn, takes a value of type ty:
// `[]$T` any slice, list or array (`[]u8` of u8s), `[$N]$T` a list, `[$N!]$T`
// a fixed array, `Name(…)` an instance of the struct Name, `^` any of those
// or its pointer. `$T` alone takes anything: too much to list.
@(private="file")
can_do_shape :: proc(checked: ^Checked_Program, defs: map[string]Ref, tn: Tree_Id, ty: Type) -> bool {
    t := &build_tree
    base := distinct_base(ty)
    #partial switch t.tag[tn] {
    case .Type_Paren:
        return can_do_shape(checked, defs, Tree_Id(t.a[tn]), ty)
    case .Type_Pointer:
        if p, is_ptr := base.(^Type_Ptr); is_ptr { return can_do_shape(checked, defs, Tree_Id(t.a[tn]), p.elem) }
        return can_do_shape(checked, defs, Tree_Id(t.a[tn]), ty)
    case .Type_Slice:
        elem: Type
        #partial switch v in base {
        case ^Type_Slice:         elem = v.elem
        case ^Type_Partial_Array: elem = v.elem
        case ^Type_Fixed_Array:   elem = v.elem
        case: return false
        }
        return can_do_elem(Tree_Id(t.b[tn]), elem)
    case .Type_Partial:
        v, is_list := base.(^Type_Partial_Array)
        return is_list && can_do_elem(Tree_Id(t.b[tn]), v.elem)
    case .Type_Array:
        v, is_fixed := base.(^Type_Fixed_Array)
        return is_fixed && can_do_elem(Tree_Id(t.b[tn]), v.elem)
    case .Type_Generic:
        sd, is_scope := base.(^Type_Scope)
        if !is_scope || sd.node == 0 { return false }
        ref, has := defs[tc_text(t.main[tn])]
        def, has_def := checked.rs.defs[ref.decl]
        return has && has_def && Tree_Id(t.b[def]) == sd.node
    }
    return false
}

// Whether an element type written at tn — `$T`, or a type's keyword — takes elem.
@(private="file")
can_do_elem :: proc(tn: Tree_Id, elem: Type) -> bool {
    t := &build_tree
    #partial switch t.tag[tn] {
    case .Type_Dollar:  return true
    case .Type_Keyword: return tc_text(t.main[tn]) == type_name(elem)
    }
    return false
}
