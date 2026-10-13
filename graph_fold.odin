package mara

import "core:slice"

// ---------------------------------------------------------------------------
// Constants, evaluated at compile time
//
// A constant's value is the code the checker built for it
// (graph_const_begin), run here with nothing but constants: a number or
// text, or an aggregate — a struct's fields, an array's elements, a union's
// variant and its fields — built the way the program builds one: a
// construction zeroes it and runs its struct's code, its fields' defaults.
//
// A constant of no width of its own (`PI :: 3.14159`) is computed at the
// width of its use: used as an f32, its arithmetic is rounded at each step,
// as it would be done there. One with a type of its own is computed at it.
//
// Each use takes its constant's value once the graph is put together
// (graph_fold_code). What can't be computed before the program runs — a
// call, a read of anything but a constant, a struct's construction with
// arguments — is an error at the use (flow_check_constants).
// ---------------------------------------------------------------------------

// A value being built or computed: a scalar, text, or an aggregate's parts —
// laid out as its type is, made when first written (a part never written
// is its type's zero, a pointer's null).
Fold :: struct {
    t:       Type,
    c:       Const_Value,   // a scalar's, or text (c.is_text)
    known:   bool,          // c was written
    parts:   []^Fold,       // a struct's fields, an array's elements; a union's variant's fields
    variant: Type,          // a union's variant: its struct
}

// The width an untyped constant is computed at: its own type's (a typed
// one's), or its use's.
Fold_Width :: enum u8 { Own, Single, Double }

Fold_Key :: struct {
    constant: Syntax_Id,
    width:    Fold_Width,
}

// A use that has no value: where, the constant, why.
Fold_Error :: struct {
    span: Span,
    name: string,
}

Folder :: struct {
    pc:      ^Program_Code,
    checked: ^Checked_Program,
    done:   map[Fold_Key]^Fold,
    busy:   map[Fold_Key]bool,   // being computed (a constant defined by itself)
    failed: bool,
    at:     Span,                // what couldn't be computed, when it's an operation
    code:   ^Program_Graph,      // the code whose uses are being folded
    errors: map[^Program_Graph][dynamic]Fold_Error,   // each code's uses with no value
}

// What one piece of code computes: the values its operations output, the
// constant it builds (or, running a struct's code, the struct it
// constructs) and the width its untyped arithmetic takes.
@(private="file")
Fold_Code :: struct {
    g:      ^Program_Graph,   // the code: a constant's, or a struct's constructor's
    self:   Node_Id,          // its root: the constant's declaration, or the struct's node
    root:   ^Fold,
    width:  Fold_Width,
    values: map[Node_Id]^Fold,
}

// Constants folded at their uses a code at a time (graph_fold_code), once
// every constant's code, and every struct's a constant's value may
// construct, is built.
graph_fold_begin :: proc(pc: ^Program_Code, checked: ^Checked_Program) -> Folder {
    return Folder{pc = pc, checked = checked}
}

// Done: the uses with no value, listed in written order (pc.fold_errors).
graph_fold_end :: proc(fo: ^Folder) {
    for g in fo.pc.codes {
        if list, has := fo.errors[g]; has { append(&fo.pc.fold_errors, ..list[:]) }
    }
    for _, list in fo.errors { delete(list) }
    delete(fo.errors)
    delete(fo.done)
    delete(fo.busy)
}

// Every use of a constant in a code (not a constant's own), given its value:
// a number or text as a use's constant, a table's whole value kept for its
// global (pc.tables). A use with no value is listed (graph_fold_end).
graph_fold_code :: proc(fo: ^Folder, b: ^Graph_Builder, g: ^Program_Graph) {
    pc := fo.pc
    fo.code = g
    {
        if g.kind[0] == .Const || len(g.constant) == 0 { return }   // (a constant's own code: computed where it's used)
        uses := make([dynamic]Node_Id, 0, len(g.constant), context.temp_allocator)   // (in order)
        for id in g.constant { append(&uses, id) }
        slice.sort(uses[:])
        for id in uses {
            c := g.constant[id]
            if c == 0 || c not_in pc.consts { continue }
            #partial switch g.op[id] {
            case .Const:
                v := fold_decl(fo, c, fold_width_of(graph_type(g, id)))
                if v == nil || !fold_scalar(v) || llvm_type_from_checker(graph_type(g, id)) == "ptr" {
                    fold_error(fo, g, id, c)
                    continue
                }
                graph_set_value(g, id, v.c)
            case .Global:
                v := fold_decl(fo, c, .Own)
                if v == nil {
                    fold_error(fo, g, id, c)
                    continue
                }
                if v.known && v.c.is_text {
                    graph_set_value(g, id, v.c)
                } else {
                    pc.tables[c] = v
                }
            }
        }
    }
}

// Use `id` (in code g) of constant `c` has no value: reported where what
// couldn't be computed is written (else at the use).
@(private="file")
fold_error :: proc(fo: ^Folder, g: ^Program_Graph, id: Node_Id, c: Syntax_Id) {
    at := fo.at if fo.at != {} else g.origin[id]
    if fo.code not_in fo.errors { fo.errors[fo.code] = {} }
    append(&fo.errors[fo.code], Fold_Error{at, graph_name(fo.pc.consts[c], 0)})
    fo.failed, fo.at = false, {}
}

// A scalar value's width, as a use's: an f32 rounds, everything else is
// computed as a double.
@(private="file")
fold_width_of :: proc(t: Type) -> Fold_Width {
    return .Single if llvm_type_from_checker(t) == "float" else .Double
}

// Whether a computed value is one number (or a zero one).
@(private="file")
fold_scalar :: proc(v: ^Fold) -> bool {
    return v.parts == nil && v.variant == nil && !(v.known && v.c.is_text)
}

// A constant's value at a width: its code, run once for it.
@(private="file")
fold_decl :: proc(fo: ^Folder, c: Syntax_Id, width: Fold_Width) -> ^Fold {
    g := fo.pc.consts[c]
    t := graph_type(g, 0)
    width := Fold_Width.Own if !is_infer(t) else width
    key := Fold_Key{c, width}
    if v, ok := fo.done[key]; ok { return v }
    if fo.busy[key] { return fold_fail(fo) }
    fo.busy[key] = true
    defer delete_key(&fo.busy, key)
    fc := Fold_Code{g = g, self = 0, root = fold_new(t), width = width}
    defer delete(fc.values)
    if !fold_run(fo, &fc, 0) { return nil }
    fo.done[key] = fc.root
    return fc.root
}

// Run the code under node n: its operations in order, to its return.
// (Code of its own inside it — a struct's methods — isn't run.)
@(private="file")
fold_run :: proc(fo: ^Folder, fc: ^Fold_Code, n: Node_Id) -> bool {
    g := fc.g
    end := int(graph_last(g, n))
    for i := int(n) + 1; i <= end; i += 1 {
        id := Node_Id(i)
        if g.kind[id] != .Op {
            i = int(graph_last(g, id))
            continue
        }
        if g.op[id] == .Return { return true }
        if !fold_op(fo, fc, id) { return false }
    }
    return true
}

@(private="file")
fold_fail :: proc(fo: ^Folder) -> ^Fold {
    fo.failed = true
    return nil
}

@(private="file")
fold_new :: proc(t: Type) -> ^Fold {
    v := new(Fold)
    v.t = t
    return v
}

@(private="file")
fold_op :: proc(fo: ^Folder, fc: ^Fold_Code, id: Node_Id) -> bool {
    g := fc.g
    ops := graph_operands(g, id)
    arg :: proc(fc: ^Fold_Code, ops: []Operand, k: int) -> ^Fold {
        if k >= len(ops) || ops[k].op == NO_NODE || ops[k].out != 0 { return nil }
        return fc.values[ops[k].op] or_else nil
    }
    out: ^Fold
    switch g.op[id] {
    case .Const:
        out = fold_const(fo, fc, id)
    case .Global:
        if c, ok := graph_value(g, id); ok && c.is_text {
            out = fold_new(graph_type(g, id))
            out.c, out.known = c, true
        } else if named := g.constant[id]; named != 0 {
            if named in fo.pc.consts { out = fold_decl(fo, named, .Own) }
        }
    case .Var:
        out = fold_var(fo, fc, id)
    case .Field, .Swizzle:
        out = fold_member(fo, arg(fc, ops, 0), graph_name(g, id), g.op[id] == .Swizzle)
    case .Index:
        if base, at := arg(fc, ops, 0), arg(fc, ops, 1); base != nil && at != nil && fold_scalar(at) {
            out = fold_element(fo, base, at.c.int)
        }
    case .Variant:
        if u := arg(fc, ops, 0); u != nil {
            if u.variant != graph_type(g, id) {
                u.variant, u.parts = graph_type(g, id), nil
            }
            out = u
        }
    case .Slice:
        // Text seen as a slice: a view of it.
        if len(ops) == 1 {
            if x := arg(fc, ops, 0); x != nil && x.known && x.c.is_text {
                out = fold_new(graph_type(g, id))
                out.c, out.known = x.c, true
            }
        }
    case .Read:
        out = arg(fc, ops, 0)
    case .Write:
        dst, src := arg(fc, ops, 0), arg(fc, ops, 1)
        if dst == nil || src == nil { return fold_fail(fo) != nil }
        fold_store(dst, src)
        return true
    case .Zero:
        dst := arg(fc, ops, 0)
        if dst == nil { return fold_fail(fo) != nil }
        fold_zero(dst)
        return true
    case .Fill:
        dst, src := arg(fc, ops, 0), arg(fc, ops, 1)
        if dst == nil || src == nil { return fold_fail(fo) != nil }
        n := fold_count(dst.t)
        if n < 0 { return fold_fail(fo) != nil }
        for k in 0 ..< n { fold_store(fold_element(fo, dst, i128(k)), src) }
        return true
    case .Construct:
        return fold_construct(fo, fc, id, ops)
    case .Arith:
        l, r := arg(fc, ops, 0), arg(fc, ops, 1)
        if l != nil && r != nil && fold_scalar(l) && fold_scalar(r) {
            if c, ok := fold_arith(graph_name(g, id), l.c, r.c, fold_single(fc, graph_type(g, id))); ok {
                out = fold_value(graph_type(g, id), c)
            }
        }
    case .Compare:
        l, r := arg(fc, ops, 0), arg(fc, ops, 1)
        if l != nil && r != nil && fold_scalar(l) && fold_scalar(r) {
            if c, ok := fold_compare(graph_name(g, id), l.c, r.c); ok { out = fold_value(graph_type(g, id), c) }
        }
    case .Unary:
        if x := arg(fc, ops, 0); x != nil && fold_scalar(x) {
            if c, ok := fold_unary(graph_name(g, id), x.c); ok { out = fold_value(graph_type(g, id), c) }
        }
    case .Cast:
        // (Text seen as a slice, a partial array: the same text.)
        if x := arg(fc, ops, 0); x != nil && x.known && x.c.is_text {
            out = fold_value(graph_type(g, id), x.c)
        } else if x != nil && fold_scalar(x) {
            if c, ok := fold_cast(x.c, graph_type(g, id)); ok { out = fold_value(graph_type(g, id), c) }
        }
    case .Address, .Deref, .View, .Byte_Read, .Carve, .Arena_Alloc,
         .Call, .Print, .Assert, .Crash,
         .Jump, .Branch, .Switch, .Return,
         .Run_Defer, .Arena_Mark, .Arena_Reset:
        // Code that runs: none of it is known before the program runs.
    }
    if out == nil {
        if fo.at == {} { fo.at = g.origin[id] }
        return fold_fail(fo) != nil
    }
    fc.values[id] = out
    return true
}

// A constant operation's value: a literal's, a named constant's (at the
// width the code computes at), or `void` — a pointer's null.
@(private="file")
fold_const :: proc(fo: ^Folder, fc: ^Fold_Code, id: Node_Id) -> ^Fold {
    g := fc.g
    if c, ok := graph_value(g, id); ok { return fold_value(graph_type(g, id), c) }
    if graph_name(g, id) == "void" { return fold_value(graph_type(g, id), {}) }   // (written: a null)
    named := g.constant[id]
    if named == 0 { return nil }
    if named not_in fo.pc.consts { return nil }
    width := fc.width
    if width == .Own { width = fold_width_of(graph_type(g, id)) }
    return fold_decl(fo, named, width)
}

@(private="file")
fold_value :: proc(t: Type, c: Const_Value) -> ^Fold {
    v := fold_new(t)
    v.c, v.known = c, true
    return v
}

// A variable in the code: the constant being built, or — in a struct's
// code — one of the fields of the struct being constructed.
@(private="file")
fold_var :: proc(fo: ^Folder, fc: ^Fold_Code, id: Node_Id) -> ^Fold {
    g := fc.g
    d := g.refers[id]
    if d == fc.self { return fc.root }
    if d != NO_NODE && g.kind[d] == .Field && g.parent[d] == fc.self {
        return fold_member(fo, fc.root, graph_name(g, d), false)
    }
    return nil
}

// A struct's field (a union's: its variant's), or an array's element named
// by a swizzle letter.
@(private="file")
fold_member :: proc(fo: ^Folder, base: ^Fold, name: string, swizzle: bool) -> ^Fold {
    if base == nil { return nil }
    if swizzle {
        if len(name) != 1 { return nil }
        return fold_element(fo, base, i128(swizzle_char_to_index(name[0])))
    }
    sd := fold_struct(base)
    if sd == nil { return nil }
    i := struct_field_index(sd, name)
    if i < 0 { return nil }
    return fold_parts(base)[i]
}

// An array's element.
@(private="file")
fold_element :: proc(fo: ^Folder, base: ^Fold, i: i128) -> ^Fold {
    n := fold_array_len(base.t)
    if base.known || i < 0 || i >= i128(n) { return nil }
    return fold_parts(base)[i]
}

// What a value is laid out as: a struct's fields, a union's variant's.
@(private="file")
fold_struct :: proc(v: ^Fold) -> ^Scope_Body {
    if v.variant != nil { return as_struct_body(distinct_base(v.variant)) }
    return as_struct_body(distinct_base(v.t))
}

// A fixed or partial array's elements; -1 for anything else.
@(private="file")
fold_array_len :: proc(t: Type) -> int {
    #partial switch a in distinct_base(t) {
    case ^Type_Fixed_Array:   return a.size
    case ^Type_Partial_Array: return a.size
    }
    return -1
}

@(private="file")
fold_count :: proc(t: Type) -> int {
    return fold_array_len(t)
}

// An aggregate's parts, each its type's zero until written.
@(private="file")
fold_parts :: proc(v: ^Fold) -> []^Fold {
    if v.parts != nil { return v.parts }
    if sd := fold_struct(v); sd != nil {
        v.parts = make([]^Fold, len(sd.fields))
        for f, i in sd.fields { v.parts[i] = fold_new(f.type_) }
    } else if n := fold_array_len(v.t); n >= 0 {
        elem := graph_elem_type(v.t)
        v.parts = make([]^Fold, n)
        for i in 0 ..< n { v.parts[i] = fold_new(elem) }
    }
    return v.parts
}

@(private="file")
fold_zero :: proc(v: ^Fold) {
    v.c, v.known, v.parts = {}, false, nil
    if _, is_union := distinct_base(v.t).(^Type_Union); is_union { v.variant = nil }
}

// A value written where another is: a copy of it.
@(private="file")
fold_store :: proc(dst, src: ^Fold) {
    if dst == src { return }
    dst.c, dst.known, dst.variant = src.c, src.known, src.variant
    dst.parts = nil
    if src.parts != nil {
        dst.parts = make([]^Fold, len(src.parts))
        for p, i in src.parts {
            dst.parts[i] = fold_new(p.t)
            fold_store(dst.parts[i], p)
        }
    }
}

// A struct constructed where it goes: zero, then its code — its fields'
// defaults. A union's variant: zero, of that variant, then its code, when it
// has a body. (Construction with arguments is a call: it runs.)
@(private="file")
fold_construct :: proc(fo: ^Folder, fc: ^Fold_Code, id: Node_Id, ops: []Operand) -> bool {
    g := fc.g
    dst: ^Fold
    if len(ops) > 0 && ops[0].op != NO_NODE { dst = fc.values[ops[0].op] or_else nil }
    if dst == nil || len(ops) != 1 { return fold_fail(fo) != nil }
    fold_zero(dst)
    ts := graph_called(g, id)
    if u, is_union := distinct_base(graph_type(g, id)).(^Type_Union); is_union {
        st := u.variant_structs[graph_name(g, id)]
        if st == nil { return fold_fail(fo) != nil }
        dst.variant = st
        if ts == nil { return true }
    } else if ts == nil {
        return fold_fail(fo) != nil
    }
    sc := fo.pc.funs[ts] or_else nil
    if sc == nil { return fold_fail(fo) != nil }
    code := Fold_Code{g = sc, self = 0, root = dst, width = .Own}
    defer delete(code.values)
    return fold_run(fo, &code, 0)
}

// Whether arithmetic rounds to single precision: an untyped constant's at
// an f32 use, a typed one's where its operation is an f32's.
@(private="file")
fold_single :: proc(fc: ^Fold_Code, t: Type) -> bool {
    switch fc.width {
    case .Single: return true
    case .Double: return false
    case .Own:    return llvm_type_from_checker(t) == "float"
    }
    return false
}

// Two numbers' arithmetic: integers exactly (within 64 bits), floats at the
// precision the code computes at.
@(private="file")
fold_arith :: proc(op: string, l, r: Const_Value, single: bool) -> (Const_Value, bool) {
    if l.is_text || r.is_text { return {}, false }
    if l.is_float || r.is_float {
        at :: proc(x: f64, single: bool) -> f64 { return f64(f32(x)) if single else x }
        a := at(l.float if l.is_float else f64(l.int), single)
        b := at(r.float if r.is_float else f64(r.int), single)
        x: f64
        switch op {
        case "+": x = a + b
        case "-": x = a - b
        case "*": x = a * b
        case "/":
            if b == 0 { return {}, false }
            x = a / b
        case:     return {}, false
        }
        return Const_Value{float = at(x, single), is_float = true}, true
    }
    a, b := l.int, r.int
    x: i128
    switch op {
    case "+":  x = a + b
    case "-":  x = a - b
    case "*":  x = a * b
    case "&":  x = a & b
    case "|":  x = a | b
    case "~":  x = a ~ b
    case "/":
        if b == 0 { return {}, false }
        x = a / b   // (truncating, as the code's)
    case "%":
        if b == 0 { return {}, false }
        x = a % b
    case "<<", ">>":
        if b < 0 || b > 63 { return {}, false }
        x = a << uint(b) if op == "<<" else a >> uint(b)
    case:      return {}, false
    }
    if x < -(i128(1) << 63) || x >= i128(1) << 64 { return {}, false }
    return Const_Value{int = x}, true
}

@(private="file")
fold_compare :: proc(op: string, l, r: Const_Value) -> (Const_Value, bool) {
    if l.is_text || r.is_text { return {}, false }
    yes: bool
    if l.is_float || r.is_float {
        a := l.float if l.is_float else f64(l.int)
        b := r.float if r.is_float else f64(r.int)
        switch op {
        case "==": yes = a == b
        case "!=": yes = a != b
        case "<":  yes = a < b
        case "<=": yes = a <= b
        case ">":  yes = a > b
        case ">=": yes = a >= b
        case:      return {}, false
        }
    } else {
        a, b := l.int, r.int
        switch op {
        case "==": yes = a == b
        case "!=": yes = a != b
        case "<":  yes = a < b
        case "<=": yes = a <= b
        case ">":  yes = a > b
        case ">=": yes = a >= b
        case:      return {}, false
        }
    }
    return Const_Value{int = 1 if yes else 0}, true
}

@(private="file")
fold_unary :: proc(op: string, x: Const_Value) -> (Const_Value, bool) {
    if x.is_text { return {}, false }
    switch op {
    case "-":   return Const_Value{int = -x.int, float = -x.float, is_float = x.is_float}, true
    case "~":   if !x.is_float { return Const_Value{int = ~x.int}, true }
    case "not": if !x.is_float { return Const_Value{int = 1 if x.int == 0 else 0}, true }
    }
    return {}, false
}

// A number converted: to a float, its value; to an integer, an integer it
// holds exactly.
@(private="file")
fold_cast :: proc(x: Const_Value, t: Type) -> (Const_Value, bool) {
    if x.is_text { return {}, false }
    #partial switch n in distinct_base(t) {
    case Type_Numeric:
        if n.kind == .Float { return Const_Value{float = x.float if x.is_float else f64(x.int), is_float = true}, true }
        if x.is_float { return {}, false }
        lo, hi: i128 = 0, (i128(1) << uint(n.bits)) - 1
        if n.kind == .Signed { lo, hi = -(i128(1) << uint(n.bits - 1)), (i128(1) << uint(n.bits - 1)) - 1 }
        if x.int < lo || x.int > hi { return {}, false }
        return x, true
    case Type_F64:
        return Const_Value{float = x.float if x.is_float else f64(x.int), is_float = true}, true
    case Type_Infer_Int, Type_Infer_Float:
        return x, true
    }
    return {}, false
}
