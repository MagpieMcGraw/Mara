package mara

import "core:fmt"
import "core:os"

// ---------------------------------------------------------------------------
// Variable identity — slice analysis, step 1 (slice_plan.md).
//
// Resolution yields a Type, never a declaration, and the during-check flow /
// escape passes track variables by NAME STRING (shadow-unsafe). A slicer needs
// the opposite: given a variable USE, the exact binding it refers to, stable and
// shadow-correct. This post-check pass supplies that — the foundation the def-use
// graph (step 2) and the slice queries build on.
//
// It mirrors flow.odin / escape.odin: walk each source function's body with a
// block-scoped frame stack (one frame per lexical block), record each binding as
// it is declared, and link every `Expr_Ident` use to the nearest enclosing
// binding of that name. A binding's identity is its DECLARING NODE (the
// `^Stmt_Assign` for a local) or its parameter slot — so two `x` in sibling
// blocks are distinct bindings, exactly as a precise slice requires.
//
// A name that resolves to no local/param (a global, function, or type) is left
// unlinked — for slicing those are source boundaries, handled later.
// ---------------------------------------------------------------------------

Binding_Kind :: enum { Local, Param }

Var_Binding :: struct {
    name:        string,
    fn:          ^Type_Scope,    // owning function scope
    kind:        Binding_Kind,
    span:        Span,           // declaration site
    decl:        ^Stmt_Assign,   // declaring assignment for locals; nil for params / loop / destructure vars
    param_index: int,            // parameter position when kind == .Param; -1 otherwise
}

@(private="file")
UD :: struct {
    checked: ^Checked_Program,
    fn:      ^Type_Scope,
    frames:  [dynamic]map[string]^Var_Binding,   // lexical scope stack (innermost last)
}

// --- entry -----------------------------------------------------------------

build_use_def :: proc(checked: ^Checked_Program) {
    for _, ft in checked.functions {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }      // foreign/intrinsic: no body
        if ft.ast != nil && len(ft.ast.generic_params) > 0 { continue } // uninstantiated template
        ud_fn(checked, ft)
    }
    ud_dump(checked)
}

ud_fn :: proc(checked: ^Checked_Program, ft: ^Type_Scope) {
    u := UD{ checked = checked, fn = ft }
    defer delete(u.frames)
    ud_push(&u)                          // the function's own frame holds the parameters
    for p, i in ft.params {
        ud_bind(&u, p.name, ud_new(&u, p.name, ft.body_span, .Param, nil, i))
    }
    for s in ft.body { ud_stmt(&u, s) }
    ud_pop(&u)
}

// --- frame stack -----------------------------------------------------------

@(private="file") ud_push :: proc(u: ^UD) { append(&u.frames, make(map[string]^Var_Binding)) }
@(private="file") ud_pop  :: proc(u: ^UD) { f := pop(&u.frames); delete(f) }

@(private="file")
ud_bind :: proc(u: ^UD, name: string, b: ^Var_Binding) {
    if name == "" || name == "_" || b == nil { return }
    u.frames[len(u.frames) - 1][name] = b
}

@(private="file")
ud_lookup :: proc(u: ^UD, name: string) -> ^Var_Binding {
    #reverse for f in u.frames {
        if b, ok := f[name]; ok { return b }
    }
    return nil
}

@(private="file")
ud_new :: proc(u: ^UD, name: string, span: Span, kind: Binding_Kind, decl: ^Stmt_Assign, param_index := -1) -> ^Var_Binding {
    if name == "" || name == "_" { return nil }
    b := new(Var_Binding)
    b^ = Var_Binding{ name = name, fn = u.fn, kind = kind, span = span, decl = decl, param_index = param_index }
    append(&u.checked.var_bindings, b)
    return b
}

// A local declared by `name := …` / loop var / destructure name.
@(private="file")
ud_local :: proc(u: ^UD, name: string, span: Span, decl: ^Stmt_Assign) {
    ud_bind(u, name, ud_new(u, name, span, .Local, decl))
}

// --- statement walk (mirrors flow_init_stmt's structure) -------------------

@(private="file")
ud_block :: proc(u: ^UD, stmts: []Stmt) {
    ud_push(u)
    for s in stmts { ud_stmt(u, s) }
    ud_pop(u)
}

@(private="file")
ud_stmt :: proc(u: ^UD, s: Stmt) {
    #partial switch v in s {
    case ^Stmt_Decl:
        // The checker desugars decls into per-name Stmt_Assigns; walk those.
        if len(v.checked) > 0 {
            for inner in v.checked { ud_stmt(u, inner) }
        } else {
            for e in v.init_values { ud_expr(u, e) }
            for name in v.names { ud_local(u, name, v.span, nil) }
        }
    case ^Stmt_Assign:
        ud_expr(u, v.value)                  // RHS uses resolve before the binding exists
        if v.target != nil { ud_expr(u, v.target) }   // complex LHS: base var is a use (the write is step 2)
        if v.is_decl { ud_local(u, v.name, v.span, v) }
        // simple-name reassignment (`x = e`): a DEF of x, recorded in step 2 — no use node here
    case ^Stmt_Multi_Assign:
        for a in v.assigns { ud_stmt(u, a) }
    case ^Stmt_Multi_Return_Assign:
        for e in v.values  { ud_expr(u, e) }
        for e in v.targets { ud_expr(u, e) }
        if v.is_decl { for name in v.names { ud_local(u, name, v.span, nil) } }
    case Stmt_Call:
        ud_expr(u, v.expr)
    case Stmt_Return:
        for e in v.values { ud_expr(u, e) }
    case ^Stmt_If:
        ud_expr(u, v.condition)
        ud_block(u, v.body[:])
        ud_block(u, v.else_body[:])
    case ^Stmt_For:
        ud_push(u)                           // the loop var and any init decl scope to the loop
        if v.init != nil { ud_stmt(u, v.init) }
        ud_expr(u, v.condition)
        ud_expr(u, v.range_low);  ud_expr(u, v.range_high)
        ud_expr(u, v.collection); ud_expr(u, v.collection_len)
        ud_local(u, v.loop_var,  v.span, nil)
        ud_local(u, v.elem_var,  v.span, nil)
        ud_local(u, v.index_var, v.span, nil)
        ud_block(u, v.body[:])
        if v.post != nil { ud_stmt(u, v.post) }
        ud_pop(u)
    case ^Stmt_Match:
        ud_expr(u, v.subject)
        for arm in v.arms {
            ud_push(u)                       // a union arm binds its payload into the arm scope
            ud_expr(u, arm.value)
            if arm.is_union_arm { ud_local(u, arm.binding_name, v.span, nil) }
            for s2 in arm.body { ud_stmt(u, s2) }
            ud_pop(u)
        }
    case ^Stmt_Defer:
        ud_block(u, v.body[:])
    // nested ^Stmt_Scope (a nested fun/struct) is its own checked.functions entry
    // and is walked on its own — do not descend (matches flow.odin).
    }
}

// --- expression walk: link every Expr_Ident use to its binding -------------

@(private="file")
ud_expr :: proc(u: ^UD, e: Expr) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:
        if b := ud_lookup(u, v.name); b != nil { u.checked.use_def[v] = b }
        // unresolved here = global / function / type — a source boundary, not a local
    case ^Expr_Unary:        ud_expr(u, v.operand)
    case ^Expr_Binary:       ud_expr(u, v.left); ud_expr(u, v.right)
    case ^Expr_Call:
        ud_expr(u, v.qualifier)
        for a in v.args { ud_expr(u, a) }
        if v.overrides != nil { ud_expr(u, v.overrides) }
    case ^Expr_Index:        ud_expr(u, v.expr); ud_expr(u, v.index)
    case ^Expr_Slice:        ud_expr(u, v.expr); ud_expr(u, v.low); ud_expr(u, v.high)
    case ^Expr_Field_Access: ud_expr(u, v.expr)
    case ^Expr_Struct_Literal:
        for f in v.fields { ud_expr(u, f.value) }
        for a in v.array_values { ud_expr(u, a) }
        ud_expr(u, v.broadcast_value)
        // override_target (`var{…}` in-place update) is a string, not a node —
        // a use+write with no Expr_Ident to anchor; deferred.
    case ^Expr_Take:         ud_expr(u, v.storage); ud_expr(u, v.count_expr)
    case ^Expr_Try:          ud_expr(u, v.inner)
    case ^Expr_If:           ud_expr(u, v.condition); ud_expr(u, v.then_expr); ud_expr(u, v.else_expr)
    case ^Expr_Array:        for el in v.elements { ud_expr(u, el) }
    // number / string / bool / type-name / self / size_of / intrinsics: no ident reads
    }
}

// --- diagnostic: MARA_DUMP_USEDEF=1 ----------------------------------------

@(private="file")
ud_dump :: proc(checked: ^Checked_Program) {
    buf: [8]u8
    if os.get_env_buf(buf[:], "MARA_DUMP_USEDEF") == "" { return }
    fmt.eprintln("--- use-def (variable identity) ---")
    for ident, b in checked.use_def {
        kind := "param" if b.kind == .Param else "local"
        fmt.eprintf("  use %-18s %-22s -> %-5s %-18s %s\n",
                    ident.name, span_loc(ident.span), kind, b.name, span_loc(b.span))
    }
    fmt.eprintf("  (%d use->decl links, %d bindings)\n", len(checked.use_def), len(checked.var_bindings))
}
