package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// The AST-shape invariant: once parsed, the tree's SHAPE is fixed.
//
// The source text is the truth and the AST is its faithful projection. Later
// passes derive from it: they may ANNOTATE a node (type_, resolved,
// resolved_func, a lowering kept beside the source like Stmt_Decl.checked), but
// they may not RESHAPE it — no renaming a node, no replacing a child, no
// splicing nodes into or out of a list. Editor queries resolve a cursor through
// this tree, and source edits will be computed from it; a pass that moves a
// receiver into args[0] or mangles a name in place sends both to the wrong
// place. And a tree the checker has reshaped can no longer be checked again.
//
// MARA_AST_SHAPE=1 turns that into a check. Every module's tree is snapshotted
// right after the `#if` fold — the fold counts as parsing: it decides which
// source is live — then compared after type checking and again after codegen.
// Each difference prints one `ast-shape[<phase>]` line at the node that changed.
//
// A snapshot records what the parser produced and nothing else: node kind,
// source fields (names, operators, literal values, flags), span, and child
// structure. Annotation fields are left out on purpose — writing them is
// allowed. A new field on an AST node therefore needs a decision here: source
// (add it to the node's fields or children) or derived (leave it out).
// ---------------------------------------------------------------------------

Shape :: struct {
    kind:   string,          // "Expr_Call", or "list" for a child list
    fields: string,          // the node's source fields, rendered
    span:   Span,
    kids:   [dynamic]Shape_Kid,
}

// One child slot. `node` is nil when the slot is empty (an absent `else`, a nil
// qualifier), so a pass filling an empty slot shows up as a difference too.
Shape_Kid :: struct {
    role: string,
    node: ^Shape,
}

@(private="file") g_shape_on:   bool
@(private="file") g_shape_last: map[string]^Shape   // module → its tree at the last checkpoint

// Snapshot every module's tree. Called by check_program right after the `#if`
// fold, so this is the baseline every later checkpoint is held to.
ast_shape_begin :: proc(programs: map[string]^Program) {
    buf: [8]byte
    g_shape_on = os.get_env_buf(buf[:], "MARA_AST_SHAPE") != ""
    if !g_shape_on { return }
    g_shape_last = shape_programs(programs)
}

// Compare every module's tree against the previous checkpoint, print one line
// per difference, and make the current tree the new baseline — so the codegen
// checkpoint reports only what codegen changed.
ast_shape_check :: proc(programs: map[string]^Program, phase: string) {
    if !g_shape_on { return }
    now := shape_programs(programs)

    modules := make([dynamic]string, context.temp_allocator)
    for m in g_shape_last { append(&modules, m) }
    for m in now { if m not_in g_shape_last { append(&modules, m) } }
    slice.sort(modules[:])

    // A node shared by two parents (a compound assignment's target is also its
    // value's left operand) is walked twice and would report twice.
    lines := make([dynamic]string, context.temp_allocator)
    seen := make(map[string]bool, allocator = context.temp_allocator)
    for m in modules {
        diffs := make([dynamic]string, context.temp_allocator)
        shape_diff(&diffs, g_shape_last[m], now[m], {}, m)
        for d in diffs {
            if d in seen { continue }
            seen[d] = true
            append(&lines, d)
        }
    }
    for l in lines { fmt.printf("ast-shape[%s] %s\n", phase, l) }
    fmt.printf("ast-shape[%s] total %d\n", phase, len(lines))
    g_shape_last = now
}

// --- comparison ---------------------------------------------------------------

@(private="file")
shape_desc :: proc(s: ^Shape) -> string {
    if s == nil { return "absent" }
    if s.kind == "list" { return fmt.tprintf("%d items", len(s.kids)) }
    if s.fields == "" { return s.kind }
    return fmt.tprintf("%s %s", s.kind, s.fields)
}

// Only the fields that changed: `"mark" → "mara_core_Arena_mark"` rather than
// every field of the node twice. Fields are space-separated; a quoted value may
// contain spaces, so splitting skips over them.
@(private="file")
fields_delta :: proc(a, b: string) -> string {
    split :: proc(s: string) -> [dynamic]string {
        out := make([dynamic]string, context.temp_allocator)
        start, quoted := 0, false
        for i := 0; i < len(s); i += 1 {
            switch {
            case s[i] == '\\' && quoted: i += 1
            case s[i] == '"':            quoted = !quoted
            case s[i] == ' ' && !quoted:
                append(&out, s[start:i]); start = i + 1
            }
        }
        append(&out, s[start:])
        return out
    }
    ta, tb := split(a), split(b)
    if len(ta) != len(tb) { return fmt.tprintf("%s → %s", a, b) }
    sb := strings.builder_make(context.temp_allocator)
    for i in 0 ..< len(ta) {
        if ta[i] == tb[i] { continue }
        if strings.builder_len(sb) > 0 { strings.write_string(&sb, ", ") }
        fmt.sbprintf(&sb, "%s → %s", ta[i], tb[i])
    }
    return strings.to_string(sb)
}

@(private="file")
has_span :: proc(s: Span) -> bool { return s.line > 0 }

@(private="file")
same_span :: proc(a, b: Span) -> bool {
    return a.file == b.file && a.line == b.line && a.col == b.col &&
           a.tok == b.tok && a.tok_end == b.tok_end
}

// `where_` is the nearest enclosing span, for nodes that carry none of their own
// (a param binding, a list). `path` names the slot, e.g. `Expr_Call.args[1]`.
@(private="file")
shape_diff :: proc(out: ^[dynamic]string, a, b: ^Shape, where_: Span, path: string) {
    if a == nil && b == nil { return }
    loc := where_
    if a != nil && has_span(a.span) { loc = a.span }
    at := format_location(loc.file, loc.line, loc.col)

    if a == nil || b == nil || a.kind != b.kind {
        append(out, fmt.tprintf("%s  %s: %s → %s", at, path, shape_desc(a), shape_desc(b)))
        return
    }
    if a.fields != b.fields {
        append(out, fmt.tprintf("%s  %s %s: %s", at, path, a.kind, fields_delta(a.fields, b.fields)))
    }
    if !same_span(a.span, b.span) {
        append(out, fmt.tprintf("%s  %s: span → %s [%d,%d)", at, path,
            format_location(b.span.file, b.span.line, b.span.col), b.span.tok, b.span.tok_end))
    }
    if len(a.kids) != len(b.kids) {
        // Only lists vary in length. Pairing items past a splice would report
        // every later item as changed, so the list is reported once.
        append(out, fmt.tprintf("%s  %s: %s → %s", at, path, shape_desc(a), shape_desc(b)))
        return
    }
    for i in 0 ..< len(a.kids) {
        ka, kb := a.kids[i], b.kids[i]
        sub: string
        if a.kind == "list" {
            sub = fmt.tprintf("%s[%d]", path, i)
        } else {
            sub = fmt.tprintf("%s.%s", a.kind, ka.role)
        }
        shape_diff(out, ka.node, kb.node, loc, sub)
    }
}

// --- snapshot -----------------------------------------------------------------
//
// The switches are exhaustive on purpose, like the hit test's: a new AST variant
// fails to compile here until someone decides what its source shape is.

@(private="file")
Snap :: struct {
    on_path: map[rawptr]bool,   // a node spliced into its own subtree would recurse forever
}

@(private="file")
shape_programs :: proc(programs: map[string]^Program) -> map[string]^Shape {
    out := make(map[string]^Shape)
    s: Snap
    for m, prog in programs {
        out[m] = shape_list(&s, prog^[:])
    }
    delete(s.on_path)
    return out
}

@(private="file")
mk :: proc(kind: string, span: Span, fields := "") -> ^Shape {
    n := new(Shape)
    n.kind = kind
    n.span = span
    n.fields = fields
    return n
}

@(private="file")
kid :: proc(n: ^Shape, role: string, child: ^Shape) {
    append(&n.kids, Shape_Kid{role = role, node = child})
}

@(private="file")
shape_list :: proc(s: ^Snap, stmts: []Stmt) -> ^Shape {
    n := mk("list", {})
    for st in stmts { kid(n, "", shape_stmt(s, st)) }
    return n
}

@(private="file")
shape_exprs :: proc(s: ^Snap, es: []Expr) -> ^Shape {
    n := mk("list", {})
    for e in es { kid(n, "", shape_expr(s, e)) }
    return n
}

@(private="file")
shape_types :: proc(s: ^Snap, ts: []Type_Expr) -> ^Shape {
    n := mk("list", {})
    for t in ts { kid(n, "", shape_type(s, t)) }
    return n
}

@(private="file")
shape_bindings :: proc(s: ^Snap, bs: []Scope_Binding) -> ^Shape {
    n := mk("list", {})
    for b in bs {
        bn := mk("binding", {}, fmt.aprintf("%q using=%v", b.name, b.is_using))
        kid(bn, "type_expr", shape_type(s, b.type_expr))
        kid(bn, "default_value", shape_expr(s, b.default_value))
        kid(n, "", bn)
    }
    return n
}

@(private="file")
shape_generic_params :: proc(s: ^Snap, gs: []Generic_Param) -> ^Shape {
    n := mk("list", {})
    for g in gs {
        gn := mk("generic_param", g.span, fmt.aprintf(
            "%q const=%v %q default=%v has_default=%v constraint=%q",
            g.name, g.is_const, g.const_type, g.default_value, g.has_default, g.shape_constraint))
        kid(gn, "default_type_expr", shape_type(s, g.default_type_expr))
        kid(n, "", gn)
    }
    return n
}

@(private="file")
shape_expr :: proc(s: ^Snap, e: Expr) -> ^Shape {
    if e == nil { return nil }
    key := rawptr(expr_span(e))
    if s.on_path[key] { return mk("cycle", expr_span(e)^) }
    s.on_path[key] = true
    defer delete_key(&s.on_path, key)

    switch v in e {
    case ^Expr_Number:
        f := fmt.aprintf("%v", v.value) if v.is_float else fmt.aprintf("%v", v.int_value)
        return mk("Expr_Number", v.span, f)
    case ^Expr_String:  return mk("Expr_String", v.span, fmt.aprintf("%q", v.value))
    case ^Expr_Char:    return mk("Expr_Char", v.span, fmt.aprintf("%v", v.value))
    case ^Expr_Ident:   return mk("Expr_Ident", v.span, fmt.aprintf("%q dot=%v", v.name, v.is_dot))
    case ^Expr_Bool:    return mk("Expr_Bool", v.span, fmt.aprintf("%v", v.value))
    case ^Expr_Skip_Constructor: return mk("Expr_Skip_Constructor", v.span)
    case ^Expr_Self:    return mk("Expr_Self", v.span)
    case ^Expr_Type_Name: return mk("Expr_Type_Name", v.span, fmt.aprintf("%v", v.kind))
    case ^Expr_Compiler_Intrinsic: return mk("Expr_Compiler_Intrinsic", v.span, fmt.aprintf("%v", v.kind))
    case ^Expr_Include:
        return mk("Expr_Include", v.span, fmt.aprintf("%q sealed=%v reexport=%v", v.path, v.is_sealed, v.is_reexport))

    case ^Expr_Unary:
        n := mk("Expr_Unary", v.span, fmt.aprintf("%v wrapping=%v", v.op, v.wrapping))
        kid(n, "operand", shape_expr(s, v.operand))
        return n
    case ^Expr_Binary:
        n := mk("Expr_Binary", v.span, fmt.aprintf("%v wrapping=%v", v.op, v.wrapping))
        kid(n, "left", shape_expr(s, v.left))
        kid(n, "right", shape_expr(s, v.right))
        return n
    case ^Expr_Call:
        n := mk("Expr_Call", v.span, fmt.aprintf("%q", v.name))
        kid(n, "qualifier", shape_expr(s, v.qualifier))
        kid(n, "args", shape_exprs(s, v.args[:]))
        ov: ^Shape   // a nil ^Expr_Struct_Literal wrapped in Expr is not a nil Expr
        if v.overrides != nil { ov = shape_expr(s, Expr(v.overrides)) }
        kid(n, "overrides", ov)
        return n
    case ^Expr_Array:
        n := mk("Expr_Array", v.span)
        kid(n, "elements", shape_exprs(s, v.elements[:]))
        return n
    case ^Expr_Index:
        n := mk("Expr_Index", v.span, fmt.aprintf("big_endian=%v", v.is_big_endian))
        kid(n, "expr", shape_expr(s, v.expr))
        kid(n, "index", shape_expr(s, v.index))
        return n
    case ^Expr_Slice:
        n := mk("Expr_Slice", v.span, fmt.aprintf("big_endian=%v", v.is_big_endian))
        kid(n, "expr", shape_expr(s, v.expr))
        kid(n, "low", shape_expr(s, v.low))
        kid(n, "high", shape_expr(s, v.high))
        return n
    case ^Expr_Struct_Literal:
        // Not array_values / is_spread / override_target: the checker derives those.
        n := mk("Expr_Struct_Literal", v.span, fmt.aprintf("%q positional=%v zero=%v broadcast=%v",
            v.name, v.positional, v.zero_init, v.is_broadcast))
        fl := mk("list", {})
        for f in v.fields {
            fn := mk("field", {}, fmt.aprintf("%q", f.name))
            kid(fn, "value", shape_expr(s, f.value))
            kid(fl, "", fn)
        }
        kid(n, "fields", fl)
        kid(n, "broadcast_value", shape_expr(s, v.broadcast_value))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        return n
    case ^Expr_Field_Access:
        n := mk("Expr_Field_Access", v.span, fmt.aprintf("%q", v.field))
        kid(n, "expr", shape_expr(s, v.expr))
        return n
    case ^Expr_Size_Of:
        n := mk("Expr_Size_Of", v.span)
        kid(n, "type_expr", shape_type(s, v.type_expr))
        return n
    case ^Expr_Assert:
        n := mk("Expr_Assert", v.span, fmt.aprintf("%q %q %q", v.cond_text, v.lhs_text, v.rhs_text))
        kid(n, "cond", shape_expr(s, v.cond))
        return n
    case ^Expr_Take:
        n := mk("Expr_Take", v.span, fmt.aprintf("%q", v.keyword))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        kid(n, "storage", shape_expr(s, v.storage))
        kid(n, "count_expr", shape_expr(s, v.count_expr))
        return n
    case ^Expr_If:
        n := mk("Expr_If", v.span)
        kid(n, "condition", shape_expr(s, v.condition))
        kid(n, "then_expr", shape_expr(s, v.then_expr))
        kid(n, "else_expr", shape_expr(s, v.else_expr))
        return n
    case ^Expr_Tuple_Default:
        n := mk("Expr_Tuple_Default", v.span, fmt.aprintf("index=%d", v.index))
        kid(n, "source", shape_expr(s, v.source))
        return n
    case ^Expr_Try:
        n := mk("Expr_Try", v.span)
        kid(n, "inner", shape_expr(s, v.inner))
        return n
    }
    return nil
}

@(private="file")
shape_type :: proc(s: ^Snap, t: Type_Expr) -> ^Shape {
    if t == nil { return nil }
    switch v in t {
    case Type_Name:        return mk("Type_Name", v.span, fmt.aprintf("%q tilde=%v", v.name, v.tilde))
    case Type_Of_Name:     return mk("Type_Of_Name", v.span, fmt.aprintf("%q", v.name))
    case Type_Const_Value: return mk("Type_Const_Value", v.span, fmt.aprintf("%d", v.value))
    case Type_Const_Expr:
        n := mk("Type_Const_Expr", v.span)
        kid(n, "expr", shape_expr(s, v.expr))
        return n
    case ^Type_Array:
        n := mk("Type_Array", v.span, fmt.aprintf("size=%d %q", v.size, v.size_name))
        kid(n, "size_expr", shape_expr(s, v.size_expr))
        kid(n, "index_type", shape_type(s, v.index_type))
        kid(n, "elem", shape_type(s, v.elem))
        return n
    case ^Type_Pointer:
        n := mk("Type_Pointer", v.span)
        kid(n, "elem", shape_type(s, v.elem))
        return n
    case ^Type_Slice_Expr:
        n := mk("Type_Slice_Expr", v.span)
        kid(n, "elem", shape_type(s, v.elem))
        kid(n, "cap_expr", shape_expr(s, v.cap_expr))
        return n
    case ^Type_Partial_Array_Expr:
        n := mk("Type_Partial_Array_Expr", v.span, fmt.aprintf("size=%d %q", v.size, v.size_name))
        kid(n, "size_expr", shape_expr(s, v.size_expr))
        kid(n, "elem", shape_type(s, v.elem))
        return n
    case ^Type_Generic_Instance:
        n := mk("Type_Generic_Instance", v.span, fmt.aprintf("%q", v.name))
        kid(n, "type_args", shape_types(s, v.type_args[:]))
        return n
    case ^Type_Func_Expr:
        n := mk("Type_Func_Expr", v.span)
        kid(n, "params", shape_types(s, v.params[:]))
        kid(n, "return_types", shape_types(s, v.return_types[:]))
        return n
    }
    return nil
}

@(private="file")
shape_stmt :: proc(s: ^Snap, st: Stmt) -> ^Shape {
    if st == nil { return nil }
    switch v in st {
    case ^Stmt_Assign:
        // Not var_type / env_type / target_type / assign_value_type / checked.
        n := mk("Stmt_Assign", v.span, fmt.aprintf("%q using=%v decl=%v compound=%v",
            v.name, v.is_using, v.is_decl, v.is_compound))
        kid(n, "value", shape_expr(s, v.value))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        kid(n, "target", shape_expr(s, v.target))
        kid(n, "slice_cap_expr", shape_expr(s, v.slice_cap_expr))
        return n
    case ^Stmt_Multi_Assign:
        n := mk("Stmt_Multi_Assign", v.span)
        l := mk("list", {})
        for a in v.assigns { kid(l, "", shape_stmt(s, a)) }
        kid(n, "assigns", l)
        return n
    case ^Stmt_Multi_Return_Assign:
        // Not var_types / checked.
        n := mk("Stmt_Multi_Return_Assign", v.span, fmt.aprintf("%v decl=%v", v.names[:], v.is_decl))
        kid(n, "targets", shape_exprs(s, v.targets[:]))
        kid(n, "values", shape_exprs(s, v.values[:]))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        return n
    case ^Stmt_Decl:
        // Not checked: the lowering kept beside the source.
        n := mk("Stmt_Decl", v.span, fmt.aprintf("%v using=%v", v.names[:], v.is_using))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        kid(n, "init_values", shape_exprs(s, v.init_values[:]))
        kid(n, "slice_cap_expr", shape_expr(s, v.slice_cap_expr))
        return n
    case ^Stmt_Define:
        n := mk("Stmt_Define", v.span, fmt.aprintf("%q", v.name))
        kid(n, "type_expr", shape_type(s, v.type_expr))
        kid(n, "value", shape_expr(s, v.value))
        return n
    case Stmt_Call:
        n := mk("Stmt_Call", v.span)
        kid(n, "expr", shape_expr(s, v.expr))
        return n
    case ^Stmt_If:
        n := mk("Stmt_If", v.span, fmt.aprintf("comptime=%v", v.is_comptime))
        kid(n, "condition", shape_expr(s, v.condition))
        kid(n, "body", shape_list(s, v.body[:]))
        kid(n, "else_body", shape_list(s, v.else_body[:]))
        return n
    case ^Stmt_For:
        // Not var_type / elem_type_.
        n := mk("Stmt_For", v.span, fmt.aprintf("range=%v %q collection=%v %q %q",
            v.is_range, v.loop_var, v.is_collection_for, v.elem_var, v.index_var))
        kid(n, "init", shape_stmt(s, v.init))
        kid(n, "condition", shape_expr(s, v.condition))
        kid(n, "post", shape_stmt(s, v.post))
        kid(n, "iter_type", shape_type(s, v.iter_type))
        kid(n, "range_low", shape_expr(s, v.range_low))
        kid(n, "range_high", shape_expr(s, v.range_high))
        kid(n, "collection", shape_expr(s, v.collection))
        kid(n, "body", shape_list(s, v.body[:]))
        return n
    case ^Stmt_Scope:
        n := mk("Stmt_Scope", v.span, fmt.aprintf("%q %v parens=%v intrinsic=%v %q exposed=%v packed=%v",
            v.name, v.kind, v.has_parens, v.is_intrinsic, v.intrinsic_name, v.is_exposed, v.is_packed))
        kid(n, "generic_params", shape_generic_params(s, v.generic_params[:]))
        kid(n, "typed_params", shape_bindings(s, v.typed_params[:]))
        kid(n, "return_types", shape_types(s, v.return_types[:]))
        kid(n, "return_bindings", shape_bindings(s, v.return_bindings[:]))
        kid(n, "defs", shape_list(s, v.defs[:]))
        kid(n, "body", shape_list(s, v.body[:]))
        return n
    case Stmt_Return:
        n := mk("Stmt_Return", v.span)
        kid(n, "values", shape_exprs(s, v.values[:]))
        return n
    case Stmt_Break:    return mk("Stmt_Break", v.span)
    case Stmt_Continue: return mk("Stmt_Continue", v.span)
    case ^Stmt_Defer:
        n := mk("Stmt_Defer", v.span)
        kid(n, "body", shape_list(s, v.body[:]))
        return n
    case ^Stmt_Match:
        // Not resolved_tag / resolved_struct.
        n := mk("Stmt_Match", v.span)
        kid(n, "subject", shape_expr(s, v.subject))
        arms := mk("list", {})
        for arm in v.arms {
            an := mk("arm", {}, fmt.aprintf("variant=%q binding=%q union=%v dot=%q else=%v",
                arm.variant_name, arm.binding_name, arm.is_union_arm, arm.dot_shorthand, arm.is_else))
            kid(an, "value", shape_expr(s, arm.value))
            kid(an, "body", shape_list(s, arm.body[:]))
            kid(arms, "", an)
        }
        kid(n, "arms", arms)
        return n
    case ^Stmt_Foreign:
        n := mk("Stmt_Foreign", v.span, fmt.aprintf("%q prefix=%q", v.library, v.prefix))
        decls := mk("list", {})
        for d in v.decls {
            dn := mk("foreign_fun", d.span, fmt.aprintf("%q", d.name))
            kid(dn, "typed_params", shape_bindings(s, d.typed_params[:]))
            kid(dn, "return_types", shape_types(s, d.return_types[:]))
            kid(decls, "", dn)
        }
        kid(n, "decls", decls)
        return n
    case ^Stmt_Union_Def:
        n := mk("Stmt_Union_Def", v.span, fmt.aprintf("%q tag_type=%q min_size=%d error=%v",
            v.name, v.tag_type, v.min_size, v.is_error_kind))
        kid(n, "tag_pad", shape_type(s, v.tag_pad))
        variants := mk("list", {})
        for vr in v.variants {
            vn := mk("variant", vr.span, fmt.aprintf("%q tag=%d has_tag=%v", vr.name, vr.tag, vr.has_tag))
            kid(vn, "fields", shape_bindings(s, vr.fields[:]))
            kid(variants, "", vn)
        }
        kid(n, "variants", variants)
        kid(n, "generic_params", shape_generic_params(s, v.generic_params[:]))
        return n
    case ^Stmt_Distinct_Def:
        n := mk("Stmt_Distinct_Def", v.span, fmt.aprintf("%q alias=%v", v.name, v.is_alias))
        kid(n, "base_type", shape_type(s, v.base_type))
        kid(n, "default_cap_expr", shape_expr(s, v.default_cap_expr))
        return n
    case ^Stmt_Dispatch_Def:
        return mk("Stmt_Dispatch_Def", v.span, fmt.aprintf("%q %v", v.name, v.functions[:]))
    case Stmt_Overload:
        return mk("Stmt_Overload", v.span, fmt.aprintf("%v %q", v.op, v.dispatch_name))
    case Stmt_Module:
        return mk("Stmt_Module", v.span, fmt.aprintf("%q", v.name))
    }
    return nil
}
