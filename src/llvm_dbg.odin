package mara

import "base:runtime"
import "core:fmt"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The LLVM backend's debug info: what codeview.odin writes for the x86
// backend, as LLVM metadata in each module's .ll. clang makes CodeView of it
// (DWARF off Windows), lld merges it into the program's PDB. A fun's
// subprogram, the lines its code is on (Ir .Line) as its instructions'
// locations, its variables (Dbg_Fun) declared where their memory is; their
// types, Mara's as C's, with raddbg's type views as the x86 backend's.
//
// Nodes are numbered from `base` (llvm_dbg_begin): the main TU's .ll holds
// two Codegens' — the main package's worker's and @main's — kept apart.
// ---------------------------------------------------------------------------

LLVM_DBG_MAIN  :: 1 << 24   // @main's Codegen's nodes, from here
LLVM_DBG_FLAGS :: 1 << 28   // the module flags' (build_module_ll)

Llvm_Dbg :: struct {
    keep:     runtime.Allocator,
    checked:  ^Checked_Program,
    text:     strings.Builder,     // the nodes, `!N = …` lines
    next:     int,                 // the next node's number
    cu:       int,                 // the compile unit (0: none yet)
    files:    map[u16]int,         // each source file's node
    types:    map[[2]u64]int,      // each type's (type_bits)
    fun_type: int,                 // every fun's: void()
    views:    map[string]bool,     // raddbg's type views the types want
    raddbg:   string,              // (@main's) every module's, the main TU's global
}

// raddbg's type views every module's types want, each once, in order: the
// main TU's `.raddbg` section, as the x86 backend's (x86_raddbg) — each
// zero-ended, after a zero.
llvm_dbg_views :: proc(main: ^Llvm_Dbg, tasks: []^Module_Task) {
    all := make(map[string]bool, context.temp_allocator)
    for v in main.views { all[v] = true }
    for t in tasks {
        if t.dbg != nil { for v in t.dbg.views { all[v] = true } }
    }
    if len(all) == 0 { return }
    views := make([dynamic]string, context.temp_allocator)
    for v in all { append(&views, v) }
    slice.sort(views[:])
    text := strings.builder_make(context.temp_allocator)
    n := 1
    strings.write_string(&text, "\\00")
    for v in views {
        for c in transmute([]u8)v {
            if c == '"' || c == '\\' || c < 0x20 || c > 0x7E { fmt.sbprintf(&text, "\\%02X", c) } else { strings.write_byte(&text, c) }
        }
        strings.write_string(&text, "\\00")
        n += len(v) + 1
    }
    main.raddbg = fmt.aprintf("@__mara_raddbg = private constant [%d x i8] c\"%s\", section \".raddbg\"\n@llvm.used = appending global [1 x ptr] [ptr @__mara_raddbg], section \"llvm.metadata\"\n\n",
                              n, strings.to_string(text), allocator = main.keep)
}

llvm_dbg_begin :: proc(keep: runtime.Allocator, checked: ^Checked_Program, base := 0) -> ^Llvm_Dbg {
    d := new(Llvm_Dbg, keep)
    d.keep, d.checked, d.next = keep, checked, base + 1
    d.text = strings.builder_make(keep)
    d.files, d.types = make(map[u16]int, keep), make(map[[2]u64]int, keep)
    d.views = make(map[string]bool, keep)
    return d
}

// A fun with its debug info: its `define` naming its subprogram, each
// instruction its line's location, each variable declared in memory, as
// clang does without optimizing (LLVM drops what only a register holds, an
// unused param, an address an instruction makes): one in an alloca of its
// own declared there; any other — a param's value, its address, an address
// an instruction makes — held in an alloca made at the entry, stored there
// once it's made.
llvm_dbg_function :: proc(d: ^Llvm_Dbg, b: ^strings.Builder, head: Ir_Head, code: [][]Ir, entry: bool, dbg: ^Dbg_Fun) {
    sp := dbg_subprogram(d, dbg, head.name)
    ir_print_head(b, head, sp)
    strings.write_string(b, "\nentry:\n" if entry else "\n")
    // The locations, by file and line; a file not the fun's its own scope.
    locs := make(map[[2]int]int, context.temp_allocator)
    scopes := make(map[int]int, context.temp_allocator)
    scopes[dbg.file] = sp
    location :: proc(d: ^Llvm_Dbg, locs: ^map[[2]int]int, scopes: ^map[int]int, sp, file, line: int) -> int {
        if n, ok := locs[{file, line}]; ok { return n }
        scope, has := scopes[file]
        if !has {
            scope = dbg_node(d)
            fmt.sbprintf(&d.text, "!%d = !DILexicalBlockFile(scope: !%d, file: !%d, discriminator: 0)\n", scope, sp, dbg_file(d, u16(file)))
            scopes[file] = scope
        }
        n := dbg_node(d)
        fmt.sbprintf(&d.text, "!%d = !DILocation(line: %d, scope: !%d)\n", n, line, scope)
        locs[{file, line}] = n
        return n
    }
    loc := location(d, &locs, &scopes, sp, dbg.file, dbg.line)

    // Each variable's memory: its own alloca, or the one at the entry that
    // holds it (`held`, its param's type for a param's value), or none.
    Dbg_Store :: enum u8 { None, Own, Held }
    store := make([]Dbg_Store, len(dbg.vars), context.temp_allocator)
    held := make([]Ir_Type, len(dbg.vars), context.temp_allocator)
    // A param's: its place (from 1), and the param's own number, the first
    // variable's there (not a match's binding of it, `Some(c)`, after).
    param := make([]int, len(dbg.vars), context.temp_allocator)
    arg := make([]int, len(dbg.vars), context.temp_allocator)
    numbered := make([]bool, len(head.params), context.temp_allocator)
    for v, i in dbg.vars {
        for p, k in head.params {
            if p.v != v.at { continue }
            param[i], store[i], held[i] = k + 1, .Held, IR_PTR if v.addr else p.ty
            if !numbered[k] { arg[i], numbered[k] = k + 1, true }
        }
        if param[i] > 0 || !v.addr { continue }
        find: for part in code {
            for ins in part {
                if ins.dest != v.at { continue }
                store[i], held[i] = .Own if ins.op == .Alloca else .Held, IR_PTR
                break find
            }
        }
    }
    slot :: proc(i: int) -> Val { return ir_local(fmt.tprintf(".dbg.%d", i)) }

    entered := false
    for part in code {
        for ins in part {
            if ins.op == .Line {
                loc = location(d, &locs, &scopes, sp, int(ins.b.n), int(ins.a.n))
                continue
            }
            if !entered && ins.op != .Label {
                // The held ones' allocas, declared; a param's stored now.
                entered = true
                for v, i in dbg.vars {
                    if store[i] != .Held { continue }
                    ir_print(b, Ir{op = .Alloca, dest = slot(i), ty = held[i]}, loc)
                    if param[i] > 0 { ir_print(b, Ir{op = .Store, ty = held[i], a = v.at, b = slot(i)}, loc) }
                    dbg_declare(d, b, slot(i), dbg_variable(d, v, sp, dbg, arg[i]), loc, deref = held[i] == IR_PTR && v.addr)
                }
            }
            ir_print(b, ins, loc)
            if ins.dest.kind == .None { continue }
            for v, i in dbg.vars {
                if v.at != ins.dest || param[i] > 0 { continue }
                #partial switch store[i] {
                case .Own:  dbg_declare(d, b, v.at, dbg_variable(d, v, sp, dbg, 0), loc)
                case .Held: ir_print(b, Ir{op = .Store, ty = IR_PTR, a = v.at, b = slot(i)}, loc)
                }
            }
        }
    }
}

// A variable's record: it's in the memory `at` points to (deref: where the
// pointer there points). A call of llvm.dbg.declare, not a `#dbg_declare`
// record: LLVM before 19 reads only the call (Ubuntu 24.04's clang is 18),
// and later ones still read it.
@(private="file")
dbg_declare :: proc(d: ^Llvm_Dbg, b: ^strings.Builder, at: Val, variable, loc: int, deref := false) {
    strings.write_string(b, "    call void @llvm.dbg.declare(metadata ptr ")
    ir_print_val(b, at)
    fmt.sbprintf(b, ", metadata !%d, metadata !DIExpression(%s)), !dbg !%d\n", variable, "DW_OP_deref" if deref else "", loc)
}

// A variable's node: its name, its type; `arg`, the param it is (from 1).
@(private="file")
dbg_variable :: proc(d: ^Llvm_Dbg, v: Dbg_Var, sp: int, dbg: ^Dbg_Fun, arg: int) -> int {
    t := dbg_type(d, v.type_)
    n := dbg_node(d)
    fmt.sbprintf(&d.text, "!%d = !DILocalVariable(name: %s, ", n, dbg_quote(v.name))
    if arg > 0 { fmt.sbprintf(&d.text, "arg: %d, ", arg) }
    fmt.sbprintf(&d.text, "scope: !%d, file: !%d, line: %d, type: %s)\n", sp, dbg_file(d, u16(dbg.file)), dbg.line, dbg_ref(t))
    return n
}

// A fun's subprogram, its module's compile unit made with the first.
@(private="file")
dbg_subprogram :: proc(d: ^Llvm_Dbg, dbg: ^Dbg_Fun, link: string) -> int {
    file := dbg_file(d, u16(dbg.file))
    if d.cu == 0 {
        d.cu = dbg_node(d)
        fmt.sbprintf(&d.text, "!%d = distinct !DICompileUnit(language: DW_LANG_C99, file: !%d, producer: \"mara\", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug)\n", d.cu, file)
        d.fun_type = dbg_node(d)
        fmt.sbprintf(&d.text, "!%d = !DISubroutineType(types: !{{null}})\n", d.fun_type)
    }
    n := dbg_node(d)
    fmt.sbprintf(&d.text, "!%d = distinct !DISubprogram(name: %s, linkageName: %s, scope: !%d, file: !%d, line: %d, type: !%d, scopeLine: %d, spFlags: DISPFlagDefinition, unit: !%d)\n",
                 n, dbg_quote(dbg.name), dbg_quote(link), file, file, dbg.line, d.fun_type, dbg.line, d.cu)
    return n
}

// A source file's node: its full path, as its name and its folder.
@(private="file")
dbg_file :: proc(d: ^Llvm_Dbg, file: u16) -> int {
    if n, ok := d.files[file]; ok { return n }
    path := build_files[file].path
    if full, err := filepath.abs(path, context.temp_allocator); err == nil { path = full }
    n := dbg_node(d)
    fmt.sbprintf(&d.text, "!%d = !DIFile(filename: %s, directory: %s)\n", n, dbg_quote(filepath.base(path)), dbg_quote(filepath.dir(path)))
    d.files[file] = n
    return n
}

// The module's metadata after its nodes: its compile units (`cus`, the
// nodes' from each Codegen's) and its flags — the debug info's version, and
// on Windows CodeView, not DWARF.
llvm_dbg_module :: proc(b: ^strings.Builder, ds: []^Llvm_Dbg) {
    cus := make([dynamic]int, context.temp_allocator)
    for d in ds {
        if d == nil || d.cu == 0 { continue }
        strings.write_string(b, strings.to_string(d.text))
        append(&cus, d.cu)
    }
    if len(cus) == 0 { return }
    strings.write_string(b, "declare void @llvm.dbg.declare(metadata, metadata, metadata)\n")
    strings.write_string(b, "!llvm.dbg.cu = !{")
    for cu, i in cus { fmt.sbprintf(b, "%s!%d", ", " if i > 0 else "", cu) }
    f := LLVM_DBG_FLAGS
    fmt.sbprintf(b, "}}\n!llvm.module.flags = !{{!%d, !%d}}\n!%d = !{{i32 2, !\"Debug Info Version\", i32 3}}\n", f, f + 1, f)
    when ODIN_OS == .Windows {
        fmt.sbprintf(b, "!%d = !{{i32 2, !\"CodeView\", i32 1}}\n", f + 1)
    } else {
        fmt.sbprintf(b, "!%d = !{{i32 7, !\"Dwarf Version\", i32 4}}\n", f + 1)
    }
}

// --- types -------------------------------------------------------------------

// A type's node, made the first time it's asked for (0: none, void). A
// struct's number is taken before its fields' types are made, so a struct
// can point to itself.
@(private="file")
dbg_type :: proc(d: ^Llvm_Dbg, t: Type) -> int {
    t := unwrap_alias(resolve_infer(t))
    #partial switch v in t {
    case Type_Void, Type_Any, Type_Const_Int, Type_Error, nil:
        return 0
    case ^Type_Distinct:
        return dbg_type(d, v.base_type)
    case ^Type_Partial_Array:
        if v.text != 0 { return dbg_type(d, type_partial_array(v.size, v.elem)) }   // (text: the list it is)
    }
    key := type_bits(t)
    if n, ok := d.types[key]; ok { return n }
    n := dbg_node(d)
    d.types[key] = n
    size := type_size(t) * 8
    basic :: proc(d: ^Llvm_Dbg, n: int, name: string, bits: int, enc: string) {
        fmt.sbprintf(&d.text, "!%d = !DIBasicType(name: %s, size: %d, encoding: %s)\n", n, dbg_quote(name), bits, enc)
    }
    i64t := Type(Type_Numeric{.Signed, 64})
    switch v in t {
    case Type_Void, Type_Any, Type_Const_Int, Type_Error, ^Type_Distinct, nil:
    case Type_Bool:  basic(d, n, "bool", 8, "DW_ATE_boolean")
    case Type_Utf8:  basic(d, n, "utf8", 8, "DW_ATE_UTF")
    case Type_Byte:  basic(d, n, "byte", 8, "DW_ATE_unsigned_char")
    case Type_F64, Type_Infer_Float: basic(d, n, "f64", 64, "DW_ATE_float")
    case Type_Infer_Int, ^Type_Field: basic(d, n, "i64", 64, "DW_ATE_signed")
    case Type_Atom:  basic(d, n, "u32", 32, "DW_ATE_unsigned")
    case Type_Numeric:
        enc := "DW_ATE_float" if v.kind == .Float else "DW_ATE_unsigned" if v.kind == .Unsigned else "DW_ATE_signed"
        basic(d, n, type_name(v), int(v.bits), enc)
    case Type_CString:
        fmt.sbprintf(&d.text, "!%d = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: %s, size: 64)\n", n, dbg_ref(dbg_type(d, Type_Utf8{})))
    case Type_Err:
        names := make([dynamic]string, context.temp_allocator)
        values := make([dynamic]i64, context.temp_allocator)
        append(&names, "Ok")
        append(&values, 0)
        for _, et in d.checked.table.enums {
            if !et.is_error_kind { continue }
            for name, value in et.variants {
                if value == 0 { continue }
                append(&names, fmt.tprintf("%s.%s", et.source_name, name))
                append(&values, i64(value))
            }
        }
        dbg_enum(d, n, "err", "err", 64, true, names[:], values[:])
    case ^Type_Ptr:
        if sl := slice_ref_of(v); sl != nil {
            // A ^[]T: where its len is, its cap, its data.
            names := [3]string{"len_at", "cap", "data"}
            types := [3]int{dbg_pointer(d, dbg_type(d, i64t)), dbg_type(d, i64t), dbg_pointer(d, dbg_type(d, sl.elem))}
            dbg_struct(d, n, debug_name(v), cv_unique(v), size, names[:], types[:], {64, 64, 64}, {0, 64, 128})
            break
        }
        fmt.sbprintf(&d.text, "!%d = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: %s, size: 64)\n", n, dbg_ref(dbg_type(d, v.elem)))
    case ^Type_Scope:
        if v.kind != .Struct {   // a fun's address
            fmt.sbprintf(&d.text, "!%d = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)\n", n)
            break
        }
        names := make([]string, len(v.fields), context.temp_allocator)
        types := make([]int, len(v.fields), context.temp_allocator)
        sizes := make([]int, len(v.fields), context.temp_allocator)
        offsets := make([]int, len(v.fields), context.temp_allocator)
        l := Layout{0, 1}
        for &f, i in v.fields {
            names[i], types[i], sizes[i] = f.name, dbg_type(d, f.type_), type_size(f.type_) * 8
            offsets[i] = layout_field(&l, type_layout(f.type_), v.is_packed) * 8
        }
        dbg_struct(d, n, debug_name(v), v.name, size, names, types, sizes, offsets)
    case ^Type_Fixed_Array:
        fmt.sbprintf(&d.text, "!%d = !DICompositeType(tag: DW_TAG_array_type, baseType: %s, size: %d, elements: !{{!DISubrange(count: %d)}})\n", n, dbg_ref(dbg_type(d, v.elem)), size, v.size)
    case ^Type_Slice:
        // Its header, {len, cap, ptr}: its len elements, as raddbg shows it
        // (no len, a negative word: all its cap's, SLICE_NO_LEN).
        names := [3]string{"len", "cap", "ptr"}
        types := [3]int{dbg_type(d, i64t), dbg_type(d, i64t), dbg_pointer(d, dbg_type(d, v.elem))}
        dbg_struct(d, n, debug_name(v), cv_unique(v), size, names[:], types[:], {64, 64, 64}, {0, 64, 128})
        d.views[raddbg_view(debug_name(v), "array(ptr, len < 0 ? cap : len)", d.keep)] = true
    case ^Type_Partial_Array:
        // Its len, then its elements: its len of them, as raddbg shows it.
        e := type_layout(v.elem)
        elems := dbg_node(d)
        fmt.sbprintf(&d.text, "!%d = !DICompositeType(tag: DW_TAG_array_type, baseType: %s, size: %d, elements: !{{!DISubrange(count: %d)}})\n", elems, dbg_ref(dbg_type(d, v.elem)), v.size * e.size * 8, v.size)
        l := Layout{0, 1}
        layout_field(&l, {8, 8})
        at := layout_field(&l, {v.size * e.size, e.align})
        names := [2]string{"len", "elements"}
        types := [2]int{dbg_type(d, i64t), elems}
        dbg_struct(d, n, debug_name(v), cv_unique(v), size, names[:], types[:], {64, v.size * e.size * 8}, {0, at * 8})
        d.views[raddbg_view(debug_name(v), "array(elements, len)", d.keep)] = true
    case ^Type_Enum:
        names := make([dynamic]string, context.temp_allocator)
        values := make([dynamic]i64, context.temp_allocator)
        for name, value in v.variants {
            append(&names, fmt.tprintf("%s.%s", v.source_name, name) if v.is_error_kind && value != 0 else name)
            append(&values, i64(value))
        }
        dbg_enum(d, n, debug_name(v), v.name, size, v.tag_type != "" && v.tag_type[0] == 'u', names[:], values[:])
    case ^Type_Union:
        // Its tag and its variants over each other, as raddbg shows it the
        // variant its tag names.
        name := debug_name(v)
        names := make([]string, len(v.variants) + 1, context.temp_allocator)
        types := make([]int, len(names), context.temp_allocator)
        sizes := make([]int, len(names), context.temp_allocator)
        names[0], types[0], sizes[0] = "__tag", dbg_type(d, v.tag_enum), type_size(v.tag_enum) * 8
        view := strings.builder_make(context.temp_allocator)
        for vname, i in v.variants {
            vs := v.variant_structs[vname]
            names[i + 1], types[i + 1], sizes[i + 1] = vname, dbg_type(d, vs), type_size(vs) * 8
            if i < len(v.variants) - 1 { fmt.sbprintf(&view, "__tag == %d ? %s : ", v.tag_map[vname], vname) } else { strings.write_string(&view, vname) }
        }
        dbg_struct(d, n, name, v.name, size, names, types, sizes, make([]int, len(names), context.temp_allocator), union_ = true)
        if len(v.variants) > 0 { d.views[raddbg_view(name, strings.to_string(view), d.keep)] = true }
    }
    return n
}

// A struct's (a union's) node: its fields, each its size and its offset in
// bits.
@(private="file")
dbg_struct :: proc(d: ^Llvm_Dbg, n: int, name, unique: string, size: int, names: []string, types, sizes, offsets: []int, union_ := false) {
    fmt.sbprintf(&d.text, "!%d = distinct !DICompositeType(tag: %s, name: %s, size: %d, identifier: %s, elements: !{{",
                 n, "DW_TAG_union_type" if union_ else "DW_TAG_structure_type", dbg_quote(name), size, dbg_quote(unique))
    for f, i in names {
        fmt.sbprintf(&d.text, "%s!DIDerivedType(tag: DW_TAG_member, name: %s, scope: !%d, baseType: %s, size: %d, offset: %d)",
                     ", " if i > 0 else "", dbg_quote(f), n, dbg_ref(types[i]), sizes[i], offsets[i])
    }
    strings.write_string(&d.text, "})\n")
}

// An enum's node: its names and values, held in an integer of its size.
@(private="file")
dbg_enum :: proc(d: ^Llvm_Dbg, n: int, name, unique: string, size: int, unsigned: bool, names: []string, values: []i64) {
    base := dbg_type(d, Type_Numeric{.Unsigned if unsigned else .Signed, i32(size)})
    fmt.sbprintf(&d.text, "!%d = !DICompositeType(tag: DW_TAG_enumeration_type, name: %s, size: %d, baseType: !%d, identifier: %s, elements: !{{", n, dbg_quote(name), size, base, dbg_quote(unique))
    for nm, i in names {
        fmt.sbprintf(&d.text, "%s!DIEnumerator(name: %s, value: %d%s)", ", " if i > 0 else "", dbg_quote(nm), values[i], ", isUnsigned: true" if unsigned else "")
    }
    strings.write_string(&d.text, "})\n")
}

// A pointer to a type's node.
@(private="file")
dbg_pointer :: proc(d: ^Llvm_Dbg, to: int) -> int {
    n := dbg_node(d)
    fmt.sbprintf(&d.text, "!%d = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: %s, size: 64)\n", n, dbg_ref(to))
    return n
}

// --- text --------------------------------------------------------------------

@(private="file")
dbg_node :: proc(d: ^Llvm_Dbg) -> int {
    d.next += 1
    return d.next - 1
}

// A node named in another (null: none).
@(private="file")
dbg_ref :: proc(n: int) -> string {
    return fmt.tprintf("!%d", n) if n != 0 else "null"
}

// A string in quotes, as LLVM reads it: a quote, a backslash or a control
// byte by its hex.
@(private="file")
dbg_quote :: proc(s: string) -> string {
    b := strings.builder_make(context.temp_allocator)
    strings.write_byte(&b, '"')
    for c in transmute([]u8)s {
        if c == '"' || c == '\\' || c < 0x20 { fmt.sbprintf(&b, "\\%02X", c) } else { strings.write_byte(&b, c) }
    }
    strings.write_byte(&b, '"')
    return strings.to_string(b)
}
