package mara

import "base:runtime"
import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The x86 backend's debug info (x86.odin): CodeView, what Windows debuggers
// read — the records clang and MSVC write for C, in each object's .debug$S
// and .debug$T. lld merges every object's into the program's PDB (`-g` at
// the link), what raddbg, Visual Studio and WinDbg read, and dbghelp for a
// crash's stack trace.
//
// .debug$S: each function's record — its name, its code's range, its frame,
// its variables (where each is in the frame, its type) — and its line table,
// which source line each stretch of its code is; then the source files they
// name. .debug$T: those types, Mara's as C's records — a struct's fields, an
// enum's names, a union's variants over each other, a slice's header, a
// partial array's header and elements.
//
// What C's records can't say — a slice is its len elements, a union the
// variant its tag names — raddbg's type views say (Cv_Module.views), in the
// exe's .raddbg section.
// ---------------------------------------------------------------------------

// What the emitter tells the x86 backend about a fun for its debug info
// (llvm.odin): its name as written, where it's defined, its variables.
Dbg_Fun :: struct {
    name:       string,
    file, line: int,
    vars:       [dynamic]Dbg_Var,
}

// A variable: its name, its type, its storage — a local's memory; with addr,
// what holds its address (a struct param, a place in the caller's slot);
// else what holds its value (a scalar param).
Dbg_Var :: struct {
    name:  string,
    type_: Type,
    at:    Val,
    addr:  bool,
}

// A source line, where its code starts in its function (Ir .Line).
Cv_Line :: struct {
    at:   u32,
    line: u32,
    file: u16,    // build_files'
}

// A variable where the function's frame has it: rsp + off, once the prologue
// is done; by_ref, the address of it there.
Cv_Var :: struct {
    name:   string,
    type_:  Type,
    off:    int,
    by_ref: bool,
}

// A relocation in .debug$S: a function's symbol (X86_Module.syms), as its
// offset in its section (SECREL) or its section's number (SECTION).
Cv_Reloc :: struct {
    at:   u32,
    sym:  u32,
    kind: u16,
}

CV_SECTION :: 0x0A   // IMAGE_REL_AMD64_SECTION
CV_SECREL  :: 0x0B   // IMAGE_REL_AMD64_SECREL

// One object's debug info, as its functions go in. (What it holds is made
// with `keep`, the module's: a function's own emission is scratch.)
Cv_Module :: struct {
    keep:      runtime.Allocator,
    checked:   ^Checked_Program,
    sym:       [dynamic]u8,             // .debug$S
    relocs:    [dynamic]Cv_Reloc,
    types:     [dynamic]u8,             // .debug$T
    next:      u32,                     // the next type record's index
    made:      map[[2]u64]u32,          // each type's record (type_bits)
    files:     map[u16]u32,             // each source file's entry in the checksums
    checksums: [dynamic]u8,
    strings:   [dynamic]u8,
    fun_type:  u32,                     // `void()`: every function's type
    views:     map[string]bool,         // raddbg's type views the types want
}

// CodeView's numbers: .debug$S's subsections, its symbol records, the type
// records, the basic types' indices.
@(private="file") CV_SYMBOLS   :: 0xF1
@(private="file") CV_LINES     :: 0xF2
@(private="file") CV_STRINGS   :: 0xF3
@(private="file") CV_FILES     :: 0xF4

@(private="file") S_END        :: 0x0006
@(private="file") S_FRAMEPROC  :: 0x1012
@(private="file") S_OBJNAME    :: 0x1101
@(private="file") S_GPROC32    :: 0x1110
@(private="file") S_REGREL32   :: 0x1111
@(private="file") S_COMPILE3   :: 0x113C

@(private="file") LF_POINTER   :: 0x1002
@(private="file") LF_PROCEDURE :: 0x1008
@(private="file") LF_ARGLIST   :: 0x1201
@(private="file") LF_FIELDLIST :: 0x1203
@(private="file") LF_ENUMERATE :: 0x1502
@(private="file") LF_ARRAY     :: 0x1503
@(private="file") LF_STRUCTURE :: 0x1505
@(private="file") LF_UNION     :: 0x1506
@(private="file") LF_ENUM      :: 0x1507
@(private="file") LF_MEMBER    :: 0x150D

@(private="file") T_VOID   :: 0x0003
@(private="file") T_UCHAR  :: 0x0020   // (a byte)
@(private="file") T_UQUAD  :: 0x0023
@(private="file") T_BOOL08 :: 0x0030
@(private="file") T_REAL32 :: 0x0040
@(private="file") T_REAL64 :: 0x0041
@(private="file") T_REAL16 :: 0x0046
@(private="file") T_RCHAR  :: 0x0070   // (a char: utf8)
@(private="file") T_64PTR  :: 0x0600   // a basic type's pointer: this | the type

// x64's rsp, as CodeView numbers registers.
@(private="file") CV_RSP :: 335

cv_begin :: proc(checked: ^Checked_Program, module_name: string) -> ^Cv_Module {
    cv := new(Cv_Module)
    cv.keep, cv.checked = context.allocator, checked
    cv.next = 0x1000
    cv.sym, cv.types, cv.checksums, cv.strings = make([dynamic]u8), make([dynamic]u8), make([dynamic]u8), make([dynamic]u8)
    cv.relocs = make([dynamic]Cv_Reloc)
    cv.made, cv.files, cv.views = make(map[[2]u64]u32), make(map[u16]u32), make(map[string]bool)
    cv_u32(&cv.sym, 4)     // (CV_SIGNATURE_C13)
    cv_u32(&cv.types, 4)
    append(&cv.strings, 0)
    // The object's name and what made it.
    sub := cv_sub_begin(&cv.sym, CV_SYMBOLS)
    r := cv_rec_begin(&cv.sym, S_OBJNAME)
    cv_u32(&cv.sym, 0)
    cv_name(&cv.sym, module_name)
    cv_rec_end(&cv.sym, r)
    r = cv_rec_begin(&cv.sym, S_COMPILE3)
    cv_u32(&cv.sym, 0)        // its language: C's
    cv_u16(&cv.sym, 0xD0)     // x64
    for _ in 0 ..< 8 { cv_u16(&cv.sym, 0) }   // (its front and back ends' versions)
    cv_name(&cv.sym, "mara")
    cv_rec_end(&cv.sym, r)
    cv_sub_end(&cv.sym, sub)
    return cv
}

// A function's records: its symbol `sym`, its code `size` bytes (its body
// after `prolog`, its epilogue at `epilog`), its frame; its variables, its
// lines (none: no line table).
cv_function :: proc(cv: ^Cv_Module, name: string, sym: u32, size, prolog, epilog, frame: int, vars: []Cv_Var, lines: []Cv_Line) {
    b := &cv.sym
    if cv.fun_type == 0 {
        args := cv_type_begin(cv, LF_ARGLIST)
        cv_u32(&cv.types, 0)
        list := cv_type_end(cv, args)
        f := cv_type_begin(cv, LF_PROCEDURE)
        cv_u32(&cv.types, T_VOID)
        append(&cv.types, 0, 0)   // (C's convention, no attributes)
        cv_u16(&cv.types, 0)
        cv_u32(&cv.types, list)
        cv.fun_type = cv_type_end(cv, f)
    }
    // Each variable's type first: the records below name them.
    types := make([]u32, len(vars), context.temp_allocator)
    for v, i in vars {
        types[i] = cv_type(cv, v.type_)
        if v.by_ref { types[i] = cv_pointer(cv, types[i], ref = true) }
    }

    sub := cv_sub_begin(b, CV_SYMBOLS)
    r := cv_rec_begin(b, S_GPROC32)
    for _ in 0 ..< 3 { cv_u32(b, 0) }   // (its parent, end and next: the linker's)
    cv_u32(b, u32(size))
    cv_u32(b, u32(prolog))
    cv_u32(b, u32(epilog))
    cv_u32(b, cv.fun_type)
    cv_address(cv, sym)
    append(b, 0)   // (no flags)
    cv_name(b, name)
    cv_rec_end(b, r)

    r = cv_rec_begin(b, S_FRAMEPROC)
    cv_u32(b, u32(frame))
    cv_u32(b, 0)
    cv_u32(b, 0)
    cv_u32(b, 16)    // (rsi and rdi, saved)
    cv_u32(b, 0)
    cv_u16(b, 0)
    cv_u32(b, 1 << 14 | 1 << 16)   // locals and params from rsp
    cv_rec_end(b, r)

    for v, i in vars {
        r = cv_rec_begin(b, S_REGREL32)
        cv_u32(b, u32(v.off))
        cv_u32(b, types[i])
        cv_u16(b, CV_RSP)
        cv_name(b, v.name)
        cv_rec_end(b, r)
    }
    r = cv_rec_begin(b, S_END)
    cv_rec_end(b, r)
    cv_sub_end(b, sub)

    if len(lines) == 0 { return }
    // Its line table: the code's lines in blocks, one per run of lines in
    // one file.
    sub = cv_sub_begin(b, CV_LINES)
    cv_address(cv, sym)
    cv_u16(b, 0)   // (no columns)
    cv_u32(b, u32(size))
    for i := 0; i < len(lines); {
        j := i
        for j < len(lines) && lines[j].file == lines[i].file { j += 1 }
        cv_u32(b, cv_file(cv, lines[i].file))
        cv_u32(b, u32(j - i))
        cv_u32(b, u32(12 + 8 * (j - i)))
        for l in lines[i:j] {
            cv_u32(b, l.at)
            cv_u32(b, min(l.line, 0xFFFFFF) | 0x8000_0000)   // (a statement's)
        }
        i = j
    }
    cv_sub_end(b, sub)
}

// The object's .debug$S, done: its source files' names after its functions.
cv_finish :: proc(cv: ^Cv_Module) {
    if len(cv.checksums) > 0 {
        sub := cv_sub_begin(&cv.sym, CV_FILES)
        append(&cv.sym, ..cv.checksums[:])
        cv_sub_end(&cv.sym, sub)
    }
    sub := cv_sub_begin(&cv.sym, CV_STRINGS)
    append(&cv.sym, ..cv.strings[:])
    cv_sub_end(&cv.sym, sub)
}

// A function's address, for the linker to fill: its offset, its section.
@(private="file")
cv_address :: proc(cv: ^Cv_Module, sym: u32) {
    append(&cv.relocs, Cv_Reloc{u32(len(cv.sym)), sym, CV_SECREL})
    cv_u32(&cv.sym, 0)
    append(&cv.relocs, Cv_Reloc{u32(len(cv.sym)), sym, CV_SECTION})
    cv_u16(&cv.sym, 0)
}

// A source file's entry in the checksums (none: no checksum), its full path
// in the strings.
@(private="file")
cv_file :: proc(cv: ^Cv_Module, file: u16) -> u32 {
    if at, ok := cv.files[file]; ok { return at }
    path := build_files[file].path
    if full, err := filepath.abs(path, context.temp_allocator); err == nil { path = full }
    at := u32(len(cv.checksums))
    cv_u32(&cv.checksums, u32(len(cv.strings)))
    append(&cv.strings, path)
    append(&cv.strings, 0)
    append(&cv.checksums, 0, 0, 0, 0)   // (no checksum's size and kind; padding)
    cv.files[file] = at
    return at
}

// --- types -------------------------------------------------------------------

// A type's record: made the first time it's asked for, with the records it
// names before it. A struct's, a union's: its forward reference first, what
// a pointer to it names, so a struct can point to itself.
cv_type :: proc(cv: ^Cv_Module, t: Type) -> u32 {
    t := unwrap_alias(resolve_infer(t))
    switch v in t {
    case Type_Bool:  return T_BOOL08
    case Type_Utf8:  return T_RCHAR
    case Type_Byte:  return T_UCHAR
    case Type_F64:   return T_REAL64
    case Type_Void:  return T_VOID
    case Type_Any:   return T_VOID
    case Type_CString: return T_64PTR | T_RCHAR
    case Type_Infer_Int: return 0x0076
    case Type_Infer_Float: return T_REAL64
    case Type_Numeric:
        if v.kind == .Float {
            switch v.bits {
            case 16: return T_REAL16
            case 32: return T_REAL32
            }
            return T_REAL64
        }
        // T_INT1 0x68 … T_INT16 0x78: signed even, unsigned odd.
        n: u32 = 0x76
        switch v.bits {
        case 8:   n = 0x68
        case 16:  n = 0x72
        case 32:  n = 0x74
        case 128: n = 0x78
        }
        return n + (1 if v.kind == .Unsigned else 0)
    case Type_Const_Int, Type_Error, nil:
        return T_VOID
    case Type_Err, ^Type_Ptr, ^Type_Scope, ^Type_Fixed_Array, ^Type_Slice, ^Type_Partial_Array, ^Type_Enum, ^Type_Union:
    case ^Type_Distinct:
        return cv_type(cv, v.base_type)
    }
    key := type_bits(t)
    if id, ok := cv.made[key]; ok { return id }
    id: u32
    #partial switch v in t {
    case Type_Err:
        id = cv_err(cv)
    case ^Type_Ptr:
        if sl := slice_ref_of(v); sl != nil {
            // A ^[]T: where its len is, its cap (-1: a slice's, read from its
            // header there), its data (a list's).
            name := type_name(v)
            fwd := cv_record_fwd(cv, LF_STRUCTURE, name, cv_unique(v))
            cv.made[key] = fwd
            names := [3]string{"len_at", "cap", "data"}
            types := [3]u32{T_64PTR | 0x76, 0x76, cv_pointer(cv, cv_type(cv, sl.elem))}
            offsets := [3]int{0, 8, 16}
            id = cv_record(cv, LF_STRUCTURE, name, cv_unique(v), type_size(v), names[:], types[:], offsets[:])
            break
        }
        elem := cv_type(cv, v.elem)
        if elem < 0x1000 && elem & T_64PTR == 0 { return T_64PTR | elem }
        id = cv_pointer(cv, elem)
    case ^Type_Scope:
        if v.kind != .Struct { return T_64PTR | T_VOID }   // a fun's address
        fwd := cv_record_fwd(cv, LF_STRUCTURE, scope_display_name(v), v.name)
        cv.made[key] = fwd
        n := len(v.fields)
        names := make([]string, n, context.temp_allocator)
        types := make([]u32, n, context.temp_allocator)
        offsets := make([]int, n, context.temp_allocator)
        l := Layout{0, 1}
        for &f, i in v.fields {
            names[i], types[i] = f.name, cv_type(cv, f.type_)
            offsets[i] = layout_field(&l, type_layout(f.type_), v.is_packed)
        }
        id = cv_record(cv, LF_STRUCTURE, scope_display_name(v), v.name, type_size(v), names, types, offsets)
    case ^Type_Fixed_Array:
        id = cv_array(cv, cv_type(cv, v.elem), type_size(v))
    case ^Type_Slice:
        // Its header, {len, cap, ptr}: its len elements, as raddbg shows it.
        name := type_name(v)
        fwd := cv_record_fwd(cv, LF_STRUCTURE, name, cv_unique(v))
        cv.made[key] = fwd
        ptr := cv_pointer(cv, cv_type(cv, v.elem))
        names := [3]string{"len", "cap", "ptr"}
        types := [3]u32{0x76, 0x76, ptr}
        offsets := [3]int{0, 8, 16}
        id = cv_record(cv, LF_STRUCTURE, name, cv_unique(v), type_size(v), names[:], types[:], offsets[:])
        cv_view(cv, name, "array(ptr, len)")
    case ^Type_Partial_Array:
        // Its len, then its elements: its len of them, as raddbg shows it.
        if v.text != 0 { return cv_type(cv, type_partial_array(v.size, v.elem)) }   // (text: the list it is)
        name := type_name(v)
        fwd := cv_record_fwd(cv, LF_STRUCTURE, name, cv_unique(v))
        cv.made[key] = fwd
        elem := cv_type(cv, v.elem)
        e := type_layout(v.elem)
        elems := cv_array(cv, elem, v.size * e.size)
        l := Layout{0, 1}
        layout_field(&l, {8, 8})
        at := layout_field(&l, {v.size * e.size, e.align})
        names := [2]string{"len", "elements"}
        types := [2]u32{0x76, elems}
        offsets := [2]int{0, at}
        id = cv_record(cv, LF_STRUCTURE, name, cv_unique(v), type_size(v), names[:], types[:], offsets[:])
        cv_view(cv, name, "array(elements, len)")
    case ^Type_Enum:
        id = cv_enum(cv, v)
    case ^Type_Union:
        id = cv_union(cv, v, key)
    }
    cv.made[key] = id
    return id
}

// A pointer to a type's record (ref: a reference, which a debugger shows as
// what it refers to).
@(private="file")
cv_pointer :: proc(cv: ^Cv_Module, to: u32, ref := false) -> u32 {
    if !ref && to < 0x1000 && to & T_64PTR == 0 { return T_64PTR | to }
    r := cv_type_begin(cv, LF_POINTER)
    cv_u32(&cv.types, to)
    cv_u32(&cv.types, 0x0C | (u32(1) << 5 if ref else 0) | 8 << 13)   // 64-bit, a pointer or a reference, 8 bytes
    return cv_type_end(cv, r)
}

// An array of `size` bytes of a type's values.
@(private="file")
cv_array :: proc(cv: ^Cv_Module, elem: u32, size: int) -> u32 {
    r := cv_type_begin(cv, LF_ARRAY)
    cv_u32(&cv.types, elem)
    cv_u32(&cv.types, T_UQUAD)
    cv_number(&cv.types, u64(size))
    cv_name(&cv.types, "")
    return cv_type_end(cv, r)
}

// A name no other type has, for a debugger to find a forward reference's
// record by: as type_name writes types, a struct's, an enum's and a union's
// by its flat name.
@(private="file")
cv_unique :: proc(t: Type) -> string {
    #partial switch v in unwrap_alias(resolve_infer(t)) {
    case ^Type_Scope:          return v.name
    case ^Type_Enum:           return v.name
    case ^Type_Union:          return v.name
    case ^Type_Distinct:       return cv_unique(v.base_type)
    case ^Type_Ptr:            return fmt.tprintf("^%s", cv_unique(v.elem))
    case ^Type_Fixed_Array:    return fmt.tprintf("[%d!]%s", v.size, cv_unique(v.elem))
    case ^Type_Slice:          return fmt.tprintf("[]%s", cv_unique(v.elem))
    case ^Type_Partial_Array:  return fmt.tprintf("[%d]%s", v.size, cv_unique(v.elem))
    }
    return type_name(t)
}

// A struct's or a union's forward reference: its name, nothing more.
@(private="file")
cv_record_fwd :: proc(cv: ^Cv_Module, kind: u16, name, unique: string) -> u32 {
    r := cv_type_begin(cv, kind)
    cv_u16(&cv.types, 0)
    cv_u16(&cv.types, 0x80 | 0x200)   // a forward reference, with a unique name
    cv_u32(&cv.types, 0)
    if kind == LF_STRUCTURE {
        cv_u32(&cv.types, 0)
        cv_u32(&cv.types, 0)
    }
    cv_number(&cv.types, 0)
    cv_name(&cv.types, name)
    cv_name(&cv.types, unique)
    return cv_type_end(cv, r)
}

// A struct's or a union's record: its fields' list, then it.
@(private="file")
cv_record :: proc(cv: ^Cv_Module, kind: u16, name, unique: string, size: int, names: []string, types: []u32, offsets: []int) -> u32 {
    fl := cv_type_begin(cv, LF_FIELDLIST)
    for n, i in names {
        cv_u16(&cv.types, LF_MEMBER)
        cv_u16(&cv.types, 3)   // public
        cv_u32(&cv.types, types[i])
        cv_number(&cv.types, u64(offsets[i]))
        cv_name(&cv.types, n)
        cv_type_pad(cv)
    }
    fields := cv_type_end(cv, fl)
    r := cv_type_begin(cv, kind)
    cv_u16(&cv.types, u16(len(names)))
    cv_u16(&cv.types, 0x200)   // a unique name
    cv_u32(&cv.types, fields)
    if kind == LF_STRUCTURE {
        cv_u32(&cv.types, 0)
        cv_u32(&cv.types, 0)
    }
    cv_number(&cv.types, u64(size))
    cv_name(&cv.types, name)
    cv_name(&cv.types, unique)
    return cv_type_end(cv, r)
}

// An enum's record: its variants' names and values, in their order.
@(private="file")
cv_enum :: proc(cv: ^Cv_Module, et: ^Type_Enum) -> u32 {
    names := make([dynamic]string, context.temp_allocator)
    values := make([dynamic]i64, context.temp_allocator)
    for name, value in et.variants {
        append(&names, fmt.tprintf("%s.%s", et.source_name, name) if et.is_error_kind && value != 0 else name)
        append(&values, i64(value))
    }
    base := u32(0x76)
    switch et.tag_type {
    case "i8": base = 0x68
    case "u8": base = 0x69
    case "i16": base = 0x72
    case "u16": base = 0x73
    case "i32": base = 0x74
    case "u32": base = 0x75
    case "u64": base = 0x77
    }
    return cv_enumeration(cv, et.source_name if et.source_name != "" else et.name, et.name, base, names[:], values[:])
}

// `err`: every error kind's variants, `File_Error.Open_Failed`, and Ok (0).
@(private="file")
cv_err :: proc(cv: ^Cv_Module) -> u32 {
    names := make([dynamic]string, context.temp_allocator)
    values := make([dynamic]i64, context.temp_allocator)
    append(&names, "Ok")
    append(&values, 0)
    for _, et in cv.checked.table.enums {
        if !et.is_error_kind { continue }
        for name, value in et.variants {
            if value == 0 { continue }
            append(&names, fmt.tprintf("%s.%s", et.source_name, name))
            append(&values, i64(value))
        }
    }
    return cv_enumeration(cv, "err", "err", 0x75, names[:], values[:])
}

// An enum's records: its names and values, by value, then it.
@(private="file")
cv_enumeration :: proc(cv: ^Cv_Module, name, unique: string, base: u32, names: []string, values: []i64) -> u32 {
    Named :: struct { value: i64, name: string }
    order := make([]Named, len(names), context.temp_allocator)
    for &o, i in order { o = {values[i], names[i]} }
    slice.sort_by(order, proc(a, b: Named) -> bool { return a.value < b.value || a.value == b.value && a.name < b.name })
    fl := cv_type_begin(cv, LF_FIELDLIST)
    for o in order {
        cv_u16(&cv.types, LF_ENUMERATE)
        cv_u16(&cv.types, 3)
        cv_signed(&cv.types, o.value)
        cv_name(&cv.types, o.name)
        cv_type_pad(cv)
    }
    fields := cv_type_end(cv, fl)
    r := cv_type_begin(cv, LF_ENUM)
    cv_u16(&cv.types, u16(len(names)))
    cv_u16(&cv.types, 0x200)
    cv_u32(&cv.types, base)
    cv_u32(&cv.types, fields)
    cv_name(&cv.types, name)
    cv_name(&cv.types, unique)
    return cv_type_end(cv, r)
}

// A union: its tag and its variants over each other, as raddbg shows it the
// variant its tag names. A niche one: its Some variant's pointer.
@(private="file")
cv_union :: proc(cv: ^Cv_Module, ut: ^Type_Union, key: [2]u64) -> u32 {
    name := ut.source_name if ut.source_name != "" else ut.name
    if ut.niche_some != "" {
        vst := ut.variant_structs[ut.niche_some]
        fwd := cv_record_fwd(cv, LF_STRUCTURE, name, ut.name)
        cv.made[key] = fwd
        names := [1]string{ut.niche_some}
        types := [1]u32{cv_type(cv, vst.fields[0].type_)}
        offsets := [1]int{0}
        return cv_record(cv, LF_STRUCTURE, name, ut.name, type_size(ut), names[:], types[:], offsets[:])
    }
    fwd := cv_record_fwd(cv, LF_UNION, name, ut.name)
    cv.made[key] = fwd
    names := make([]string, len(ut.variants) + 1, context.temp_allocator)
    types := make([]u32, len(names), context.temp_allocator)
    offsets := make([]int, len(names), context.temp_allocator)
    names[0], types[0] = "__tag", cv_type(cv, ut.tag_enum)
    view := strings.builder_make(context.temp_allocator)
    for vname, i in ut.variants {
        names[i + 1], types[i + 1] = vname, cv_type(cv, ut.variant_structs[vname])
        if i < len(ut.variants) - 1 { fmt.sbprintf(&view, "__tag == %d ? %s : ", ut.tag_map[vname], vname) } else { strings.write_string(&view, vname) }
    }
    id := cv_record(cv, LF_UNION, name, ut.name, type_size(ut), names, types, offsets)
    if len(ut.variants) > 0 { cv_view(cv, name, strings.to_string(view)) }
    return id
}

// A raddbg type view: values of the type named `type` shown as `expr` says.
@(private="file")
cv_view :: proc(cv: ^Cv_Module, type, expr: string) {
    cv.views[fmt.aprintf("type_view: {{type: ```%s```, expr: ```%s```}}", type, expr, allocator = cv.keep)] = true
}

// --- bytes -------------------------------------------------------------------

// A subsection of .debug$S, begun (its kind, its length to come), ended (its
// length, padding to 4).
@(private="file")
cv_sub_begin :: proc(b: ^[dynamic]u8, kind: u32) -> int {
    cv_u32(b, kind)
    at := len(b)
    cv_u32(b, 0)
    return at
}

@(private="file")
cv_sub_end :: proc(b: ^[dynamic]u8, at: int) {
    cv_put32(b[:], at, u32(len(b) - at - 4))
    for len(b) % 4 != 0 { append(b, 0) }
}

// A symbol record, begun (its length to come, its kind), ended (padded to 4,
// its length).
@(private="file")
cv_rec_begin :: proc(b: ^[dynamic]u8, kind: u16) -> int {
    at := len(b)
    cv_u16(b, 0)
    cv_u16(b, kind)
    return at
}

@(private="file")
cv_rec_end :: proc(b: ^[dynamic]u8, at: int) {
    for len(b) % 4 != 0 { append(b, 0) }
    n := len(b) - at - 2
    b[at], b[at + 1] = u8(n), u8(n >> 8)
}

// A type record, begun, ended (padded to 4 as CodeView pads: LF_PAD3, 2, 1):
// its index.
@(private="file")
cv_type_begin :: proc(cv: ^Cv_Module, kind: u16) -> int {
    at := len(cv.types)
    cv_u16(&cv.types, 0)
    cv_u16(&cv.types, kind)
    return at
}

@(private="file")
cv_type_end :: proc(cv: ^Cv_Module, at: int) -> u32 {
    cv_type_pad(cv)
    n := len(cv.types) - at - 2
    if n > 0xFF00 {
        fmt.eprintfln("x86 backend: a type's debug record is %d bytes, past CodeView's 64K", n)
        os.exit(1)
    }
    cv.types[at], cv.types[at + 1] = u8(n), u8(n >> 8)
    id := cv.next
    cv.next += 1
    return id
}

@(private="file")
cv_type_pad :: proc(cv: ^Cv_Module) {
    for len(cv.types) % 4 != 0 { append(&cv.types, 0xF0 | u8(4 - len(cv.types) % 4)) }
}

// A numeric leaf: a small number as itself, a bigger one after its kind
// (LF_ULONG, LF_UQUAD; signed, LF_LONG, LF_QUADWORD).
@(private="file")
cv_number :: proc(b: ^[dynamic]u8, n: u64) {
    switch {
    case n < 0x8000:      cv_u16(b, u16(n))
    case n <= 0xFFFFFFFF: cv_u16(b, 0x8004); cv_u32(b, u32(n))
    case:                 cv_u16(b, 0x800A); cv_u32(b, u32(n)); cv_u32(b, u32(n >> 32))
    }
}

@(private="file")
cv_signed :: proc(b: ^[dynamic]u8, n: i64) {
    switch {
    case n >= 0:          cv_number(b, u64(n))
    case n >= -0x8000_0000: cv_u16(b, 0x8003); cv_u32(b, u32(i32(n)))
    case:                 cv_u16(b, 0x8009); cv_u32(b, u32(n)); cv_u32(b, u32(u64(n) >> 32))
    }
}

@(private="file")
cv_name :: proc(b: ^[dynamic]u8, s: string) {
    append(b, s)
    append(b, 0)
}

@(private="file")
cv_u16 :: proc(b: ^[dynamic]u8, v: u16) {
    append(b, u8(v), u8(v >> 8))
}

@(private="file")
cv_u32 :: proc(b: ^[dynamic]u8, v: u32) {
    append(b, u8(v), u8(v >> 8), u8(v >> 16), u8(v >> 24))
}

@(private="file")
cv_put32 :: proc(b: []u8, at: int, v: u32) {
    b[at], b[at + 1], b[at + 2], b[at + 3] = u8(v), u8(v >> 8), u8(v >> 16), u8(v >> 24)
}
