package mara

import "core:fmt"
import "core:os"

// ---------------------------------------------------------------------------
// Variable identity + the def-use graph — slice analysis steps 1 & 2.
//
// Step 1 (variable identity): resolution yields a Type, never a declaration, so
// a slicer can't tell which binding a use refers to. This pass walks each source
// function's body with a block-scoped frame stack and links every `Expr_Ident`
// use to the nearest enclosing binding of that name — shadow-correct, so two `x`
// in sibling blocks are distinct bindings.
//
// Step 2 (def-use graph): the SAME walk threads a reaching-definitions state —
// for each binding, the set of definitions live at the current point. At a use,
// the binding's reaching set is recorded (`reaching[use]`); at a def, a strong
// update replaces the binding's set (a partial write `x.f = …` is a weak update).
// Control flow mirrors flow.odin: branches clone the state and union at the join;
// LOOPS get a sound back-edge patch — every definition the loop generates may
// reach every use in the loop (any iteration), so after walking the body once we
// add the loop's defs to the loop's uses. The result over-approximates (a sound
// `may-reach`), which is exactly what a slice wants.
//
// Backward slice = walk `reaching` from a use to its defs, then each def's RHS
// uses, transitively. Forward slice = the inverse map. Binding creation and def
// generation happen at the same points, which is why both live in one walk.
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

Def_Kind :: enum { Param, Decl, Assign, Loop_Var, Destructure, Complex }

// One definition site: a point that gives `binding` a value. `value` is the RHS
// that drives it (an assignment's value, a loop's iteration source, a call) —
// nil for a parameter, which is an external input and thus a slice boundary.
Def :: struct {
    binding: ^Var_Binding,
    kind:    Def_Kind,
    span:    Span,
    value:   Expr,
}

// --- reaching-definitions state --------------------------------------------

Def_Set :: map[^Def]bool
Reach   :: map[^Var_Binding]Def_Set   // binding -> the defs reaching the current point

@(private="file")
UD :: struct {
    checked: ^Checked_Program,
    fn:      ^Type_Scope,
    frames:  [dynamic]map[string]^Var_Binding, // lexical scope stack (innermost last)
    uses:    [dynamic]^Expr_Ident,              // every recorded use, in order (for the loop back-edge patch)
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
    defer delete(u.uses)
    st := make(Reach)
    defer reach_free(&st)

    ud_push(&u)                          // the function's own frame holds the parameters
    for p, i in ft.params {
        b := ud_new(&u, p.name, ft.body_span, .Param, nil, i)
        if b == nil { continue }
        ud_bind(&u, p.name, b)
        reach_gen(&st, b, ud_def(&u, b, .Param, ft.body_span, nil))   // a param is defined on entry
    }
    for s in ft.body { ud_stmt(&u, s, &st) }
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

@(private="file")
ud_def :: proc(u: ^UD, b: ^Var_Binding, kind: Def_Kind, span: Span, value: Expr) -> ^Def {
    d := new(Def)
    d^ = Def{ binding = b, kind = kind, span = span, value = value }
    append(&u.checked.defs, d)
    return d
}

// Declare a fresh local and define it (the common `x := value` / loop-var case).
@(private="file")
ud_declare :: proc(u: ^UD, name: string, span: Span, decl: ^Stmt_Assign, kind: Def_Kind, value: Expr, st: ^Reach) {
    b := ud_new(u, name, span, .Local, decl)
    if b == nil { return }
    ud_bind(u, name, b)
    reach_gen(st, b, ud_def(u, b, kind, span, value))
}

// --- reaching-defs set ops -------------------------------------------------

@(private="file")
reach_gen :: proc(r: ^Reach, b: ^Var_Binding, d: ^Def) {   // strong update: a full assignment kills prior defs
    if old, ok := r[b]; ok { delete(old) }
    s := make(Def_Set); s[d] = true
    r[b] = s
}

@(private="file")
reach_add :: proc(r: ^Reach, b: ^Var_Binding, d: ^Def) {   // weak update: a partial write keeps prior defs
    s := r[b]
    if s == nil { s = make(Def_Set) }
    s[d] = true
    r[b] = s
}

@(private="file")
reach_clone :: proc(r: ^Reach) -> Reach {
    n := make(Reach)
    for b, s in r^ {
        ns := make(Def_Set)
        for d in s { ns[d] = true }
        n[b] = ns
    }
    return n
}

@(private="file")
reach_merge :: proc(dst: ^Reach, src: ^Reach) {   // dst |= src
    for b, s in src^ {
        d := dst[b]
        if d == nil { d = make(Def_Set) }
        for k in s { d[k] = true }
        dst[b] = d
    }
}

@(private="file")
reach_clear :: proc(r: ^Reach) { for _, s in r^ { delete(s) }; clear(r) }

@(private="file")
reach_free :: proc(r: ^Reach) { for _, s in r^ { delete(s) }; delete(r^) }

// --- statement walk (mirrors flow_init_stmt's structure) -------------------

@(private="file")
ud_block :: proc(u: ^UD, stmts: []Stmt, st: ^Reach) {
    ud_push(u)
    for s in stmts { ud_stmt(u, s, st) }
    ud_pop(u)
}

@(private="file")
ud_stmt :: proc(u: ^UD, s: Stmt, st: ^Reach) {
    #partial switch v in s {
    case ^Stmt_Decl:
        if len(v.checked) > 0 {
            for inner in v.checked { ud_stmt(u, inner, st) }
        } else {
            for e in v.init_values { ud_expr(u, e, st) }
            for name in v.names { ud_declare(u, name, v.span, nil, .Decl, nil, st) }
        }
    case ^Stmt_Assign:
        ud_expr(u, v.value, st)                  // RHS uses resolve against the state BEFORE this def
        if v.target != nil {
            ud_expr(u, v.target, st)             // complex LHS: the base var is read to write into
            if root := ud_lvalue_root(v.target); root != nil {
                if b := ud_lookup(u, root.name); b != nil {
                    reach_add(st, b, ud_def(u, b, .Complex, v.span, v.value))   // partial write: weak update
                }
            }
        } else if v.is_decl {
            ud_declare(u, v.name, v.span, v, .Decl, v.value, st)
        } else if b := ud_lookup(u, v.name); b != nil {
            reach_gen(st, b, ud_def(u, b, .Assign, v.span, v.value))            // reassignment: strong update
        }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { ud_stmt(u, a, st) }
    case ^Stmt_Multi_Return_Assign:
        for e in v.values  { ud_expr(u, e, st) }
        for e in v.targets { ud_expr(u, e, st) }
        src: Expr = v.values[0] if len(v.values) > 0 else nil
        for name in v.names {
            if v.is_decl {
                ud_declare(u, name, v.span, nil, .Destructure, src, st)
            } else if b := ud_lookup(u, name); b != nil {
                reach_gen(st, b, ud_def(u, b, .Destructure, v.span, src))
            }
        }
    case Stmt_Call:
        ud_expr(u, v.expr, st)
    case Stmt_Return:
        for e in v.values { ud_expr(u, e, st) }
    case ^Stmt_If:
        ud_expr(u, v.condition, st)
        then_st := reach_clone(st)
        else_st := reach_clone(st)
        ud_block(u, v.body[:],      &then_st)
        ud_block(u, v.else_body[:], &else_st)
        reach_clear(st)                          // st := then ∪ else (union at the join)
        reach_merge(st, &then_st)
        reach_merge(st, &else_st)
        reach_free(&then_st); reach_free(&else_st)
    case ^Stmt_For:
        ud_push(u)                               // the loop var / init decl scope to the loop
        pre := reach_clone(st)                   // the 0-iteration path: pre-loop defs survive
        use_start := len(u.uses)
        def_start := len(u.checked.defs)
        if v.init != nil { ud_stmt(u, v.init, st) }
        ud_expr(u, v.condition, st)
        ud_expr(u, v.range_low, st);  ud_expr(u, v.range_high, st)
        ud_expr(u, v.collection, st); ud_expr(u, v.collection_len, st)
        loop_src: Expr = v.collection if v.is_collection_for else v.range_high
        if v.loop_var  != "" { ud_declare(u, v.loop_var,  v.span, nil, .Loop_Var, loop_src,     st) }
        if v.elem_var  != "" { ud_declare(u, v.elem_var,  v.span, nil, .Loop_Var, v.collection, st) }
        if v.index_var != "" { ud_declare(u, v.index_var, v.span, nil, .Loop_Var, nil,          st) }
        ud_block(u, v.body[:], st)
        if v.post != nil { ud_stmt(u, v.post, st) }
        ud_loop_patch(u, use_start, def_start)   // back-edge: loop defs may reach loop uses in a later iteration
        reach_merge(st, &pre)
        reach_free(&pre)
        ud_pop(u)
    case ^Stmt_Match:
        ud_expr(u, v.subject, st)
        arm_states: [dynamic]Reach
        defer delete(arm_states)
        for arm in v.arms {
            as := reach_clone(st)
            ud_push(u)
            ud_expr(u, arm.value, &as)
            if arm.is_union_arm && arm.binding_name != "" {
                ud_declare(u, arm.binding_name, v.span, nil, .Destructure, v.subject, &as)  // payload from the subject
            }
            for s2 in arm.body { ud_stmt(u, s2, &as) }
            ud_pop(u)
            append(&arm_states, as)
        }
        reach_clear(st)                          // st := union of all arms
        for &as in arm_states { reach_merge(st, &as); reach_free(&as) }
    case ^Stmt_Defer:
        dc := reach_clone(st)                    // defers run at scope exit — record uses, don't propagate defs
        ud_block(u, v.body[:], &dc)
        reach_free(&dc)
    // nested ^Stmt_Scope (a nested fun/struct) is its own checked.functions entry
    // and is walked on its own — do not descend (matches flow.odin).
    }
}

// Every definition the loop generates can, via the back-edge, reach every use in
// the loop in some iteration. The forward walk only captured textually-earlier
// defs, so add the loop's defs to the loop's uses (per binding). Sound may-reach.
@(private="file")
ud_loop_patch :: proc(u: ^UD, use_start, def_start: int) {
    n_defs := len(u.checked.defs)
    if def_start >= n_defs { return }
    for ui in use_start ..< len(u.uses) {
        use := u.uses[ui]
        b := u.checked.use_def[use]
        if b == nil { continue }
        seen: Def_Set
        defer delete(seen)
        for d in u.checked.reaching[use] { seen[d] = true }
        grew := false
        for di in def_start ..< n_defs {
            d := u.checked.defs[di]
            if d.binding == b && d not_in seen { seen[d] = true; grew = true }
        }
        if grew {
            merged := make([dynamic]^Def, 0, len(seen))
            for d in seen { append(&merged, d) }
            u.checked.reaching[use] = merged[:]
        }
    }
}

// The root variable an lvalue writes through: `x.f`, `arr[i]`, `p^` -> `x`/`arr`/`p`.
@(private="file")
ud_lvalue_root :: proc(e: Expr) -> ^Expr_Ident {
    cur := e
    for {
        #partial switch v in cur {
        case ^Expr_Ident:        return v
        case ^Expr_Field_Access: cur = v.expr
        case ^Expr_Index:        cur = v.expr
        case ^Expr_Slice:        cur = v.expr
        case ^Expr_Unary:        if v.op == .Caret { cur = v.operand } else { return nil }
        case:                    return nil
        }
    }
}

// --- expression walk: link each use to its binding + reaching defs ----------

@(private="file")
ud_expr :: proc(u: ^UD, e: Expr, st: ^Reach) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:
        if b := ud_lookup(u, v.name); b != nil {
            u.checked.use_def[v] = b
            if s := st[b]; len(s) > 0 {
                defs := make([dynamic]^Def, 0, len(s))
                for d in s { append(&defs, d) }
                u.checked.reaching[v] = defs[:]
            }
            append(&u.uses, v)
        }
        // unresolved here = global / function / type — a source boundary, not a local
    case ^Expr_Unary:        ud_expr(u, v.operand, st)
    case ^Expr_Binary:       ud_expr(u, v.left, st); ud_expr(u, v.right, st)
    case ^Expr_Call:
        ud_expr(u, v.qualifier, st)
        for a in v.args { ud_expr(u, a, st) }
        if v.overrides != nil { ud_expr(u, v.overrides, st) }
    case ^Expr_Index:        ud_expr(u, v.expr, st); ud_expr(u, v.index, st)
    case ^Expr_Slice:        ud_expr(u, v.expr, st); ud_expr(u, v.low, st); ud_expr(u, v.high, st)
    case ^Expr_Field_Access: ud_expr(u, v.expr, st)
    case ^Expr_Struct_Literal:
        for f in v.fields { ud_expr(u, f.value, st) }
        for a in v.array_values { ud_expr(u, a, st) }
        ud_expr(u, v.broadcast_value, st)
        // override_target (`var{…}` in-place update) is a string, not a node — deferred.
    case ^Expr_Take:         ud_expr(u, v.storage, st); ud_expr(u, v.count_expr, st)
    case ^Expr_Try:          ud_expr(u, v.inner, st)
    case ^Expr_If:           ud_expr(u, v.condition, st); ud_expr(u, v.then_expr, st); ud_expr(u, v.else_expr, st)
    case ^Expr_Array:        for el in v.elements { ud_expr(u, el, st) }
    // number / string / bool / type-name / self / size_of / intrinsics: no ident reads
    }
}

// --- diagnostics -----------------------------------------------------------

@(private="file")
ud_dump :: proc(checked: ^Checked_Program) {
    buf: [8]u8
    if os.get_env_buf(buf[:], "MARA_DUMP_USEDEF") != "" {
        fmt.eprintln("--- use-def (variable identity) ---")
        for ident, b in checked.use_def {
            kind := "param" if b.kind == .Param else "local"
            fmt.eprintf("  use %-18s %-22s -> %-5s %-18s %s\n",
                        ident.name, span_loc(ident.span), kind, b.name, span_loc(b.span))
        }
        fmt.eprintf("  (%d use->decl links, %d bindings)\n", len(checked.use_def), len(checked.var_bindings))
    }
    if os.get_env_buf(buf[:], "MARA_DUMP_REACHING") != "" {
        fmt.eprintln("--- reaching definitions (def-use graph) ---")
        for ident, defs in checked.reaching {
            fmt.eprintf("  use %-16s %-22s <- ", ident.name, span_loc(ident.span))
            for d, i in defs {
                if i > 0 { fmt.eprint(", ") }
                fmt.eprintf("%v@%s", d.kind, span_loc(d.span))
            }
            fmt.eprintln()
        }
        fmt.eprintf("  (%d uses with reaching defs, %d def sites)\n", len(checked.reaching), len(checked.defs))
    }
}
