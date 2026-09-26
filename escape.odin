package mara

import "core:fmt"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Escape analysis — Mara's lifetime rule, checked post-check over durable bodies.
//
// DEPTHS. All memory has a lifetime depth: global memory is 0, the caller's
// memory 1, and each lexical block of the function being checked one more (its
// body block is 2). A deeper block dies first — and in Mara it really does die:
// the scope allocator resets when the block ends.
//
// ROOTS. A reference value carries the set of memory it may point into
// (Esc_Roots): global memory, a parameter's caller memory (by index), a local
// variable's own storage (by variable), and anonymous temporaries (literals, call
// results viewed in place) at the block that holds them.
//
// THE RULE. A store is legal only when everything the value may point into
// outlives everything the destination may be:
//
//     deepest(value roots) <= shallowest(destination roots)
//
// `return v` is a store into the caller. Storing into a local's storage adds to
// what that local holds, so reading it back — directly, through a field or an
// index, or through a pointer to it — carries those roots onward. That one check
// is the whole analysis: returns, writes through parameters at any field/index
// depth, writes through aliases of parameters, reassigned locals, and values
// outliving an inner block all fall out of it.
//
// FLOW. A write in the block that declares a variable replaces its roots; a
// write from a nested block (which may not run) joins them. Loop bodies are
// walked quietly to a fixpoint before the reporting walk, so a value stored late
// in a body reaches the statements before it on the next iteration.
//
// SUMMARIES. Inside a callee all caller memory is depth 1, so a callee can't tell
// a long-lived argument from a short-lived one. Instead each function's summary
// records which parameters its result may point into, and which parameter's
// memory each parameter may be stored into. Summaries are computed callees-first
// over the call graph's SCCs (cg_bottom_up iterates recursion to a fixpoint) and
// applied at every call site with the caller's real depths. A summary keeps two
// levels per parameter — the memory the argument points at, and anything deeper
// — so storing into `h.p` isn't confused with storing into `h.p^`. Foreign and
// indirect calls are the honest seam: assumed not to retain their arguments.
// ---------------------------------------------------------------------------

ESC_GLOBAL       :: 0
ESC_CALLER       :: 1
ESC_BODY         :: 2
ESC_STORE_GLOBAL :: -1
ESC_MAX_PARAMS   :: 128

Esc_Param_Set :: bit_set[0 ..< ESC_MAX_PARAMS; u128]

// The memory a reference value may point into.
Esc_Roots :: struct {
    params: Esc_Param_Set,     // the caller memory these parameters point at
    deep:   Esc_Param_Set,     // caller memory reachable further through them
    global: bool,
    temp:   int,               // deepest block holding a temporary it views; 0 = none
    vars:   [dynamic]^Esc_Var, // local variables' own storage
}

Esc_Var :: struct {
    name:     string,
    depth:    int,       // lifetime depth of the variable's storage
    frame:    int,       // declaring frame (a write there replaces, elsewhere joins)
    type_:    Type,
    is_param: bool,
    loc:      Esc_Roots, // its storage: itself, or for a `let` view the storage it views
    contents: Esc_Roots, // what the references it holds may point into
}

// A parameter's memory stored into another's (a function-summary edge): memory
// reachable from `src` may end up referenced from memory reachable from `dst`.
Esc_Store :: struct {
    dst:      int,  // ESC_STORE_GLOBAL: into global memory
    dst_deep: bool,
    src:      int,
    src_deep: bool,
}

Esc_Summary :: struct {
    ret:      Esc_Param_Set, // the result may point at what these arguments point at
    ret_deep: Esc_Param_Set, // ... or at anything reachable through them
    stores:   [dynamic]Esc_Store,
}

@(private="file")
Esc_Frame :: struct {
    vars:        map[string]^Esc_Var,
    loop_header: bool, // a loop's init/post scope: its `post` runs every iteration
}

// Where a store lands, for the diagnostic.
@(private="file")
Esc_Site :: struct {
    target:      Expr,
    target_name: string,
    call:        ^Expr_Call,   // a summarized store at a call site
    callee:      ^Type_Scope,
    st:          Esc_Store,
}

@(private="file")
Esc_Decl_Key :: struct {
    name: string,
    span: Span,
}

@(private="file")
Esc :: struct {
    c:      ^Checker,
    g:      ^Call_Graph,
    ft:     ^Type_Scope,
    ctor:   bool,  // a constructor: its top-level declarations are fields of Self
    report: bool,  // the reporting walk (vs. a summary walk)
    quiet:  int,   // > 0 inside a loop's fixpoint passes
    frames: [dynamic]Esc_Frame,
    decls:  map[Esc_Decl_Key]^Esc_Var, // one variable per declaration across loop re-walks
    sum:    Esc_Summary,
}

@(private="file") g_esc_checker: ^Checker

// Entry point, after build_call_graph: summaries bottom-up, then one reporting
// walk per function against the final summaries.
escape_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program) {
    g := c.cg
    if g == nil { return }
    resize(&g.esc, len(g.nodes))
    g_esc_checker = c
    cg_bottom_up(g, esc_summary_transfer)
    for ft in g.nodes {
        if esc_walkable(ft) { esc_walk(c, g, ft, true) }
    }
}

@(private="file")
esc_summary_transfer :: proc(g: ^Call_Graph, n: int) -> bool {
    ft := g.nodes[n]
    if !esc_walkable(ft) { return false }
    s := esc_walk(g_esc_checker, g, ft, false)
    cur := &g.esc[n]
    changed := false
    if !(s.ret <= cur.ret)           { cur.ret += s.ret; changed = true }
    if !(s.ret_deep <= cur.ret_deep) { cur.ret_deep += s.ret_deep; changed = true }
    for st in s.stores {
        if !slice.contains(cur.stores[:], st) { append(&cur.stores, st); changed = true }
    }
    return changed // monotone: summaries only grow toward the fixpoint
}

@(private="file")
esc_walkable :: proc(ft: ^Type_Scope) -> bool {
    if ft == nil { return false }
    if _, src := ft.origin.(Origin_Source); !src { return false } // foreign / intrinsic: no body
    // An uninstantiated generic template's body is unresolved; each instantiation
    // is walked through its own cloned, typed body.
    if ft.ast != nil && len(ft.ast.generic_params) > 0 && raw_data(ft.body) == raw_data(ft.ast.body) { return false }
    return true
}

@(private="file")
esc_walk :: proc(c: ^Checker, g: ^Call_Graph, ft: ^Type_Scope, report: bool) -> Esc_Summary {
    if len(ft.params) > ESC_MAX_PARAMS {
        fmt.panicf("escape analysis: %s has %d parameters (max %d)", ft.name, len(ft.params), ESC_MAX_PARAMS)
    }
    e := Esc{c = c, g = g, ft = ft, ctor = ft.kind == .Struct, report = report}
    esc_push(&e, false)
    for p, i in ft.params {
        if v := esc_declare(&e, p.name, ft.body_span, p.type_, true); v != nil && esc_has_refs(c, p.type_) {
            v.contents.params = {i}
        }
    }
    for name, i in ft.return_binding_names {
        esc_declare(&e, name, ft.body_span, ft.return_types[i] if i < len(ft.return_types) else nil)
    }
    for s in ft.body { esc_stmt(&e, s) }
    esc_pop(&e)
    return e.sum
}

// --- frames ------------------------------------------------------------------

@(private="file")
esc_push :: proc(e: ^Esc, loop_header: bool) {
    append(&e.frames, Esc_Frame{vars = make(map[string]^Esc_Var), loop_header = loop_header})
}

@(private="file")
esc_pop :: proc(e: ^Esc) {
    f := pop(&e.frames)
    delete(f.vars)
}

// Lifetime depth of the innermost open block.
@(private="file")
esc_depth :: proc(e: ^Esc) -> int { return ESC_BODY + len(e.frames) - 1 }

@(private="file")
esc_declare :: proc(e: ^Esc, name: string, span: Span, t: Type, is_param := false) -> ^Esc_Var {
    if name == "" || name == "_" { return nil }
    key := Esc_Decl_Key{name, span}
    v := e.decls[key]
    if v == nil {
        v = new(Esc_Var)
        e.decls[key] = v
    }
    frame := len(e.frames) - 1
    depth := esc_depth(e)
    // A constructor's top-level declarations are fields of Self, which the
    // caller owns.
    if e.ctor && frame == 0 && !is_param { depth = ESC_CALLER }
    v^ = Esc_Var{name = name, depth = depth, frame = frame, type_ = t, is_param = is_param}
    append(&v.loc.vars, v)
    e.frames[frame].vars[name] = v
    return v
}

@(private="file")
esc_lookup :: proc(e: ^Esc, name: string) -> ^Esc_Var {
    #reverse for &f in e.frames {
        if v, ok := f.vars[name]; ok { return v }
    }
    return nil
}

// A plain variable (not a `let` view): its storage is its own slot.
@(private="file")
esc_is_own_slot :: proc(v: ^Esc_Var) -> bool {
    r := v.loc
    return len(r.vars) == 1 && r.vars[0] == v && r.params == {} && r.deep == {} && !r.global && r.temp == 0
}

// --- roots ---------------------------------------------------------------------

@(private="file")
esc_add_var :: proc(r: ^Esc_Roots, v: ^Esc_Var) {
    for w in r.vars { if w == v { return } }
    append(&r.vars, v)
}

@(private="file")
esc_join :: proc(dst: ^Esc_Roots, src: Esc_Roots) {
    dst.params += src.params
    dst.deep += src.deep
    if src.global { dst.global = true }
    dst.temp = max(dst.temp, src.temp)
    for v in src.vars { esc_add_var(dst, v) }
}

@(private="file")
esc_clone :: proc(r: Esc_Roots) -> Esc_Roots {
    out: Esc_Roots
    esc_join(&out, r)
    return out
}

@(private="file")
esc_equal :: proc(a, b: Esc_Roots) -> bool {
    if a.params != b.params || a.deep != b.deep || a.global != b.global || a.temp != b.temp { return false }
    if len(a.vars) != len(b.vars) { return false }
    for v in a.vars { if !slice.contains(b.vars[:], v) { return false } }
    return true
}

@(private="file")
esc_global_roots :: proc() -> Esc_Roots {
    r: Esc_Roots
    r.global = true
    return r
}

// Deepest root other than caller memory reached through a parameter; -1 if none.
@(private="file")
esc_deepest_local :: proc(r: Esc_Roots) -> int {
    d := -1
    if r.global { d = ESC_GLOBAL }
    d = max(d, r.temp if r.temp > 0 else -1)
    for v in r.vars { d = max(d, v.depth) }
    return d
}

// Shallowest root, parameters' memory counting as the caller's; max(int) if none.
@(private="file")
esc_shallowest :: proc(r: Esc_Roots) -> int {
    d := max(int)
    if r.global { d = ESC_GLOBAL }
    if r.params != {} || r.deep != {} { d = min(d, ESC_CALLER) }
    if r.temp > 0 { d = min(d, r.temp) }
    for v in r.vars { d = min(d, v.depth) }
    return d
}

// What the memory at `r` may hold: one level of indirection further. Memory
// never holds references to anything shorter-lived than itself (that's the
// rule), so a temporary or global holds nothing deeper than itself, and a
// parameter's memory holds more of the caller's memory.
@(private="file")
esc_deref :: proc(r: Esc_Roots) -> Esc_Roots {
    out: Esc_Roots
    out.deep = r.params + r.deep
    out.global = r.global
    out.temp = r.temp
    for v in r.vars { esc_join(&out, v.contents) }
    return out
}

// The data a slice header at `r` points into. A partial array's header points
// into its own inline elements, so it is (also) its own data.
@(private="file")
esc_slice_data :: proc(r: Esc_Roots) -> Esc_Roots {
    out := esc_deref(r)
    for v in r.vars { if esc_self_pointing(v.type_) { esc_add_var(&out, v) } }
    return out
}

// Everything reachable from `r`, at any depth of indirection (r included).
@(private="file")
esc_reach :: proc(r: Esc_Roots) -> Esc_Roots {
    out := esc_clone(r)
    for {
        before := esc_clone(out)
        esc_join(&out, esc_slice_data(out))
        if esc_equal(before, out) { return out }
    }
}

// --- the rule ------------------------------------------------------------------

// Store `val` into memory at `dst`: check the rule, then record that any local
// variable in `dst` now (may) hold what `val` points into.
@(private="file")
esc_store :: proc(e: ^Esc, dst, val: Esc_Roots, site: Esc_Site, span: Span) {
    esc_check(e, dst, val, site, span)
    for v in dst.vars { esc_join(&v.contents, val) }
}

// THE RULE: everything `val` may point into must outlive everything `dst` may be.
@(private="file")
esc_check :: proc(e: ^Esc, dst, val: Esc_Roots, site: Esc_Site, span: Span) {
    if esc_deepest_local(val) > esc_shallowest(dst) {
        esc_report_store(e, val, site, span)
    }
    if val.params == {} && val.deep == {} { return }
    // Caller memory into caller memory can't be judged in here — every parameter
    // is depth 1 to the callee. Summarize it; call sites check it.
    for i in dst.params { esc_record_stores(e, i, false, val) }
    for i in dst.deep   { esc_record_stores(e, i, true, val) }
    if dst.global       { esc_record_stores(e, ESC_STORE_GLOBAL, false, val) }
    // A constructor field is part of the constructed result.
    for v in dst.vars {
        if v.depth == ESC_CALLER {
            e.sum.ret += val.params
            e.sum.ret_deep += val.deep
        }
    }
}

@(private="file")
esc_record_stores :: proc(e: ^Esc, dst: int, dst_deep: bool, val: Esc_Roots) {
    for j in val.params { esc_record(e, Esc_Store{dst, dst_deep, j, false}) }
    for j in val.deep   { esc_record(e, Esc_Store{dst, dst_deep, j, true}) }
}

@(private="file")
esc_record :: proc(e: ^Esc, st: Esc_Store) {
    if !slice.contains(e.sum.stores[:], st) { append(&e.sum.stores, st) }
}

// `return v`: a store into the caller.
@(private="file")
esc_return :: proc(e: ^Esc, val: Esc_Roots, x: Expr, span: Span) {
    e.sum.ret += val.params
    e.sum.ret_deep += val.deep
    if esc_deepest_local(val) <= ESC_CALLER { return }
    if !esc_reporting(e) { return }
    if call, ok := x.(^Expr_Call); ok && esc_report_call_return(e, call, span) { return }
    check_error(e.c, span, TYPE_CANNOT_RETURN_LOCAL_REFERENCE_MEMORY)
}

// --- statements ----------------------------------------------------------------

@(private="file")
esc_block :: proc(e: ^Esc, stmts: []Stmt) {
    esc_push(e, false)
    for s in stmts { esc_stmt(e, s) }
    esc_pop(e)
}

@(private="file")
esc_stmt :: proc(e: ^Esc, s: Stmt) {
    #partial switch v in s {
    case ^Stmt_Decl:
        if len(v.checked) > 0 {
            for inner in v.checked { esc_stmt(e, inner) }
            return
        }
        for name, i in v.names {
            val: Expr
            if i < len(v.init_values)       { val = v.init_values[i] }
            else if len(v.init_values) == 1 { val = v.init_values[0] }
            esc_calls(e, val)
            esc_decl_value(e, name, val, nil, v.span)
        }
    case ^Stmt_Assign:
        esc_calls(e, v.value)
        esc_calls(e, v.target)
        switch {
        case v.is_decl:
            esc_decl_value(e, v.name, v.value, v.var_type, v.span)
        case v.target != nil:
            val: Esc_Roots
            if sl, range_copy := v.target.(^Expr_Slice); range_copy {
                // `dst[a:b] = src` copies src's elements into dst's.
                val = esc_elems(e, v.value, esc_elem_type(expr_type(sl.expr)))
            } else if ix, indexed := v.target.(^Expr_Index); indexed {
                // (target_type is the container here; the slot holds an element.)
                val = esc_val(e, v.value, esc_elem_type(expr_type(ix.expr)))
            } else {
                val = esc_val(e, v.value, v.target_type)
            }
            esc_store(e, esc_loc(e, v.target), val, Esc_Site{target = v.target}, v.span)
        case:
            b := esc_lookup(e, v.name)
            esc_assign_var(e, v.name, esc_val(e, v.value, b.type_ if b != nil else nil), v.span)
        }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { esc_stmt(e, a) }
    case ^Stmt_Multi_Return_Assign:
        if len(v.checked) > 0 { // broadcast: the desugared per-target assigns
            for inner in v.checked { esc_stmt(e, inner) }
            return
        }
        // Destructure: every bound name may hold what any returned value does.
        // (Straight to the call result: a tuple call's expression type is only
        // its first slot, which would hide references in the others.)
        src: Esc_Roots
        for val in v.values {
            esc_calls(e, val)
            call, is_call := val.(^Expr_Call)
            if is_call && call.desugared == nil {
                esc_join(&src, esc_call_result(e, esc_callee(e, call), call.args[:]))
            } else {
                esc_join(&src, esc_prov(e, val))
            }
        }
        for t in v.targets { esc_calls(e, t) }
        for name, i in v.names {
            if i < len(v.targets) && v.targets[i] != nil {
                esc_store(e, esc_loc(e, v.targets[i]), src, Esc_Site{target = v.targets[i]}, v.span)
            } else if v.is_decl {
                esc_bind(e, name, src, v.var_types[i] if i < len(v.var_types) else nil, v.span)
            } else {
                esc_assign_var(e, name, src, v.span)
            }
        }
    case Stmt_Call:
        esc_calls(e, v.expr)
    case Stmt_Return:
        if len(v.values) == 0 {
            // Named returns: a bare `return` hands back the named locals.
            for name in e.ft.return_binding_names {
                if b := esc_lookup(e, name); b != nil { esc_return(e, esc_deref(b.loc), nil, v.span) }
            }
        }
        for val, i in v.values {
            esc_calls(e, val)
            rt: Type = e.ft.return_types[i] if i < len(e.ft.return_types) else nil
            esc_return(e, esc_val(e, val, rt), val, v.span)
        }
    case ^Stmt_If:
        esc_calls(e, v.condition)
        esc_block(e, v.body[:])
        esc_block(e, v.else_body[:])
    case ^Stmt_For:
        esc_for(e, v)
    case ^Stmt_Match:
        esc_calls(e, v.subject)
        for arm in v.arms {
            esc_push(e, false)
            esc_calls(e, arm.value)
            if arm.is_union_arm && arm.binding_name != "" {
                // The payload binding views the subject's storage.
                if b := esc_declare(e, arm.binding_name, v.span, nil); b != nil { b.loc = esc_loc(e, v.subject) }
            }
            for s2 in arm.body { esc_stmt(e, s2) }
            esc_pop(e)
        }
    case ^Stmt_Defer:
        esc_block(e, v.body[:])
    // A nested ^Stmt_Scope (fun/struct) is its own call-graph node.
    }
}

@(private="file")
esc_for :: proc(e: ^Esc, v: ^Stmt_For) {
    esc_push(e, true)
    if v.init != nil { esc_stmt(e, v.init) }
    esc_calls(e, v.condition)
    esc_calls(e, v.range_low)
    esc_calls(e, v.range_high)
    esc_calls(e, v.collection)
    esc_calls(e, v.collection_len)
    if v.loop_var  != "" { esc_declare(e, v.loop_var, v.span, v.var_type) }
    if v.index_var != "" { esc_declare(e, v.index_var, v.span, nil) }
    elem: ^Esc_Var
    if v.elem_var != "" { elem = esc_declare(e, v.elem_var, v.span, v.elem_type_) }
    // Walk the body quietly until what it stores into enclosing variables stops
    // growing, then once more for real. Every write that reaches an enclosing
    // variable from in here joins, so the passes only grow — and they're bounded
    // by the function's declarations.
    for pass := 0; ; pass += 1 {
        before := esc_snapshot(e)
        e.quiet += 1
        esc_for_pass(e, v, elem)
        e.quiet -= 1
        if esc_snapshot_same(before) { break }
        if pass > 10_000 { fmt.panicf("escape analysis: loop at %s did not converge", span_loc(v.span)) }
    }
    esc_for_pass(e, v, elem)
    esc_pop(e)
}

@(private="file")
esc_for_pass :: proc(e: ^Esc, v: ^Stmt_For, elem: ^Esc_Var) {
    // The element variable holds a copy of each element.
    if elem != nil && v.collection != nil { elem.contents = esc_deref(esc_mem(e, v.collection)) }
    esc_block(e, v.body[:])
    if v.post != nil { esc_stmt(e, v.post) }
}

@(private="file")
Esc_Snap :: struct {
    v:        ^Esc_Var,
    contents: Esc_Roots,
}

@(private="file")
esc_snapshot :: proc(e: ^Esc) -> [dynamic]Esc_Snap {
    out: [dynamic]Esc_Snap
    for &f in e.frames {
        for _, v in f.vars { append(&out, Esc_Snap{v, esc_clone(v.contents)}) }
    }
    return out
}

@(private="file")
esc_snapshot_same :: proc(snap: [dynamic]Esc_Snap) -> bool {
    for s in snap { if !esc_equal(s.v.contents, s.contents) { return false } }
    return true
}

// `name := value` / `name : T = value`.
@(private="file")
esc_decl_value :: proc(e: ^Esc, name: string, value: Expr, t: Type, span: Span) {
    dt := t
    if dt == nil && value != nil { dt = expr_type(value) }
    if tk, ok := value.(^Expr_Take); ok && tk.keyword == "let" {
        // `x := let(T, storage)`: x IS the storage it views — no slot of its own.
        view := esc_mem(e, tk.storage)
        if v := esc_declare(e, name, span, dt); v != nil { v.loc = view }
        return
    }
    val: Esc_Roots
    if value != nil { val = esc_val(e, value, dt) }
    esc_bind(e, name, val, dt, span)
}

@(private="file")
esc_bind :: proc(e: ^Esc, name: string, val: Esc_Roots, t: Type, span: Span) {
    v := esc_declare(e, name, span, t)
    if v == nil { return }
    // A value can't point deeper than the block declaring it — except into a
    // constructor field, which outlives the constructor's own locals.
    esc_check(e, v.loc, val, Esc_Site{target_name = name}, span)
    v.contents = esc_clone(val)
}

// `name = value`: a write of the whole variable.
@(private="file")
esc_assign_var :: proc(e: ^Esc, name: string, val: Esc_Roots, span: Span) {
    if name == "" || name == "_" { return }
    site := Esc_Site{target_name = name}
    v := esc_lookup(e, name)
    if v == nil { // a global variable
        esc_check(e, esc_global_roots(), val, site, span)
        return
    }
    if !esc_is_own_slot(v) { // a `let` view: writing it writes the storage it views
        esc_store(e, esc_clone(v.loc), val, site, span)
        return
    }
    esc_check(e, v.loc, val, site, span)
    top := len(e.frames) - 1
    if v.frame == top && !e.frames[top].loop_header {
        v.contents = esc_clone(val)   // a write in the declaring block replaces
    } else {
        esc_join(&v.contents, val)    // a nested block's write may not run: join
    }
}

// --- expressions ---------------------------------------------------------------

// `x` as a value headed into a destination of type `dest` — the destination
// decides what is actually stored. A fixed or partial array decaying to a slice
// becomes a view of the array's own storage; a slice copied into an array copies
// its elements, not the view; and a destination that can't hold a reference
// stores none, whatever the source.
@(private="file")
esc_val :: proc(e: ^Esc, x: Expr, dest: Type) -> Esc_Roots {
    if x == nil { return {} }
    if dest != nil && !esc_has_refs(e.c, dest) { return {} }
    #partial switch db in distinct_base(dest) {
    case ^Type_Slice:
        #partial switch _ in distinct_base(expr_type(x)) {
        case ^Type_Fixed_Array, ^Type_Partial_Array:
            return esc_loc(e, x)
        }
    case ^Type_Fixed_Array:
        return esc_elems(e, x, db.elem)
    case ^Type_Partial_Array:
        return esc_elems(e, x, db.elem)
    }
    return esc_prov(e, x)
}

// What copying `x`'s elements (into elements of type `elem`) stores.
@(private="file")
esc_elems :: proc(e: ^Esc, x: Expr, elem: Type) -> Esc_Roots {
    if !esc_has_refs(e.c, elem) { return {} }
    #partial switch _ in distinct_base(expr_type(x)) {
    case ^Type_Slice, ^Type_Ptr:
        return esc_deref(esc_mem(e, x)) // the elements live where the view points
    }
    return esc_prov(e, x) // an array value: its contents are its elements'
}

// What a value may point into. A value whose type holds no references has none.
@(private="file")
esc_prov :: proc(e: ^Esc, x: Expr) -> Esc_Roots {
    r: Esc_Roots
    if x == nil { return r }
    if t := expr_type(x); t != nil && !esc_has_refs(e.c, t) { return r }
    #partial switch v in x {
    case ^Expr_Ident:
        if b := esc_lookup(e, v.name); b != nil { return esc_deref(b.loc) }
        r.global = true // a global, constant or function
    case ^Expr_Unary:
        #partial switch v.op {
        case .Ampersand: return esc_loc(e, v.operand)
        case .Caret:     return esc_deref(esc_prov(e, v.operand))
        }
        if rf, ok := v.overload_fn.?; ok {
            args := [1]Expr{v.operand}
            return esc_call_result(e, esc_callee_of(e, rf), args[:])
        }
        return esc_prov(e, v.operand)
    case ^Expr_Binary:
        if rf, ok := v.overload_fn.?; ok {
            args := [2]Expr{v.left, v.right}
            return esc_call_result(e, esc_callee_of(e, rf), args[:])
        }
        r = esc_prov(e, v.left)
        esc_join(&r, esc_prov(e, v.right))
    case ^Expr_Field_Access:
        if v.resolved != nil { r.global = true; return r } // enum variant / constant
        return esc_deref(esc_mem(e, v.expr))
    case ^Expr_Index:
        return esc_deref(esc_mem(e, v.expr))
    case ^Expr_Slice:
        return esc_mem(e, v.expr)
    case ^Expr_Struct_Literal:
        for f, i in v.fields { esc_join(&r, esc_val(e, f.value, struct_lit_field_type(e.c, v, i))) }
        for a in v.array_values { esc_join(&r, esc_prov(e, a)) }
        esc_join(&r, esc_prov(e, v.broadcast_value))
    case ^Expr_Array:
        for el in v.elements { esc_join(&r, esc_prov(e, el)) }
    case ^Expr_Call:
        if v.desugared != nil { return esc_prov(e, v.desugared) }
        r = esc_call_result(e, esc_callee(e, v), v.args[:])
        if v.overrides != nil { esc_join(&r, esc_prov(e, v.overrides)) }
    case ^Expr_Take:
        // let(T, s) reads a T out of s's memory; slice(..., s) views it.
        view := esc_mem(e, v.storage)
        return esc_deref(view) if v.keyword == "let" else view
    case ^Expr_If:
        r = esc_prov(e, v.then_expr)
        esc_join(&r, esc_prov(e, v.else_expr))
    case ^Expr_Try:
        return esc_prov(e, v.inner)
    case ^Expr_Self:
        // The value under construction: what its fields hold.
        for b in esc_ctor_fields(e) { esc_join(&r, b.contents) }
    }
    return r
}

// The storage an lvalue designates. An rvalue gets a temporary in the current
// block.
@(private="file")
esc_loc :: proc(e: ^Esc, x: Expr) -> Esc_Roots {
    r: Esc_Roots
    #partial switch v in x {
    case ^Expr_Ident:
        if b := esc_lookup(e, v.name); b != nil { return esc_clone(b.loc) }
        r.global = true
        return r
    case ^Expr_Field_Access:
        if v.resolved != nil { r.global = true; return r }
        return esc_mem(e, v.expr)
    case ^Expr_Index:
        return esc_mem(e, v.expr)
    case ^Expr_Slice:
        return esc_mem(e, v.expr)
    case ^Expr_Unary:
        if v.op == .Caret { return esc_prov(e, v.operand) }
    case ^Expr_Take:
        return esc_mem(e, v.storage)
    case ^Expr_Self:
        for b in esc_ctor_fields(e) { esc_add_var(&r, b) }
        return r
    }
    r.temp = esc_depth(e)
    return r
}

// The memory holding `x`'s fields or elements: through a pointer (Mara
// auto-derefs one level) or a slice, what it points at; otherwise its own
// inline storage.
@(private="file")
esc_mem :: proc(e: ^Esc, x: Expr) -> Esc_Roots {
    #partial switch bt in distinct_base(expr_type(x)) {
    case ^Type_Ptr:
        if _, to_slice := distinct_base(bt.elem).(^Type_Slice); to_slice {
            return esc_slice_data(esc_prov(e, x)) // ^[]T: the data its header points at
        }
        return esc_prov(e, x)
    case ^Type_Slice:
        return esc_prov(e, x)
    }
    return esc_loc(e, x)
}

@(private="file")
esc_ctor_fields :: proc(e: ^Esc) -> [dynamic]^Esc_Var {
    out: [dynamic]^Esc_Var
    if !e.ctor || len(e.frames) == 0 { return out }
    for _, b in e.frames[0].vars { if !b.is_param { append(&out, b) } }
    return out
}

// --- calls ---------------------------------------------------------------------

@(private="file")
esc_callee :: proc(e: ^Esc, call: ^Expr_Call) -> ^Type_Scope {
    if rf, ok := call.resolved_func.?; ok {
        if ts := esc_callee_of(e, rf); ts != nil { return ts }
    }
    if s := lookup_callee_scope(e.c, call); s != nil {
        if n, ok := e.g.stmt_to_node[s]; ok { return e.g.nodes[n] }
    }
    return nil
}

@(private="file")
esc_callee_of :: proc(e: ^Esc, rf: Resolved_Func) -> ^Type_Scope {
    if rf.callee != nil { return rf.callee }
    if ts, ok := e.c.table.funs[rf.name]; ok { return ts }
    return nil
}

@(private="file")
esc_summary_of :: proc(e: ^Esc, callee: ^Type_Scope) -> ^Esc_Summary {
    if callee == nil || callee.calling_conv == .C { return nil }
    if n, ok := e.g.index_of[callee]; ok && n < len(e.g.esc) { return &e.g.esc[n] }
    return nil
}

// Argument `i` as the callee's parameter `i` sees it (decay included).
@(private="file")
esc_arg :: proc(e: ^Esc, callee: ^Type_Scope, args: []Expr, i: int, deep: bool) -> Esc_Roots {
    pt: Type = callee.params[i].type_ if callee != nil && i < len(callee.params) else nil
    r := esc_val(e, args[i], pt)
    return esc_reach(r) if deep else r
}

@(private="file")
esc_call_result :: proc(e: ^Esc, callee: ^Type_Scope, args: []Expr) -> Esc_Roots {
    r: Esc_Roots
    if callee != nil && callee.calling_conv == .C {
        r.global = true // foreign memory
        return r
    }
    sum := esc_summary_of(e, callee)
    if sum == nil {
        // A conversion, built-in or indirect call: the result may view any argument.
        for a in args { esc_join(&r, esc_prov(e, a)) }
        return r
    }
    for i in sum.ret      { if i < len(args) { esc_join(&r, esc_arg(e, callee, args, i, false)) } }
    for i in sum.ret_deep { if i < len(args) { esc_join(&r, esc_arg(e, callee, args, i, true)) } }
    return r
}

// Apply the callee's summarized stores at this call site, with the caller's
// real depths.
@(private="file")
esc_call_stores :: proc(e: ^Esc, call: ^Expr_Call, callee: ^Type_Scope, args: []Expr, span: Span) {
    sum := esc_summary_of(e, callee)
    if sum == nil { return }
    for st in sum.stores {
        if st.src >= len(args) || st.dst >= len(args) { continue }
        val := esc_arg(e, callee, args, st.src, st.src_deep)
        dst := esc_global_roots() if st.dst == ESC_STORE_GLOBAL else esc_arg(e, callee, args, st.dst, st.dst_deep)
        esc_store(e, dst, val, Esc_Site{call = call, callee = callee, st = st}, span)
    }
}

// Visit every call (and in-place struct update) inside an expression once, for
// its effects.
@(private="file")
esc_calls :: proc(e: ^Esc, x: Expr) {
    if x == nil { return }
    #partial switch v in x {
    case ^Expr_Call:
        if v.desugared != nil { esc_calls(e, v.desugared); return }
        esc_calls(e, v.qualifier)
        for a in v.args { esc_calls(e, a) }
        if v.overrides != nil { esc_calls(e, v.overrides) }
        esc_call_stores(e, v, esc_callee(e, v), v.args[:], v.span)
    case ^Expr_Unary:
        esc_calls(e, v.operand)
        if rf, ok := v.overload_fn.?; ok {
            args := [1]Expr{v.operand}
            esc_call_stores(e, nil, esc_callee_of(e, rf), args[:], v.span)
        }
    case ^Expr_Binary:
        esc_calls(e, v.left)
        esc_calls(e, v.right)
        if rf, ok := v.overload_fn.?; ok {
            args := [2]Expr{v.left, v.right}
            esc_call_stores(e, nil, esc_callee_of(e, rf), args[:], v.span)
        }
    case ^Expr_Index:        esc_calls(e, v.expr); esc_calls(e, v.index)
    case ^Expr_Slice:        esc_calls(e, v.expr); esc_calls(e, v.low); esc_calls(e, v.high)
    case ^Expr_Field_Access: esc_calls(e, v.expr)
    case ^Expr_Take:         esc_calls(e, v.storage); esc_calls(e, v.count_expr)
    case ^Expr_Try:          esc_calls(e, v.inner)
    case ^Expr_Assert:       esc_calls(e, v.cond)
    case ^Expr_If:           esc_calls(e, v.condition); esc_calls(e, v.then_expr); esc_calls(e, v.else_expr)
    case ^Expr_Array:        for el in v.elements { esc_calls(e, el) }
    case ^Expr_Struct_Literal:
        for f in v.fields { esc_calls(e, f.value) }
        for a in v.array_values { esc_calls(e, a) }
        esc_calls(e, v.broadcast_value)
        // `var{ a = x }`: an in-place update of var's fields.
        if v.override_target != "" {
            if b := esc_lookup(e, v.override_target); b != nil {
                for f, i in v.fields {
                    val := esc_val(e, f.value, struct_lit_field_type(e.c, v, i))
                    esc_store(e, esc_clone(b.loc), val, Esc_Site{target_name = v.override_target}, v.span)
                }
            }
        }
    }
}

// --- types ---------------------------------------------------------------------

@(private="file") g_esc_refs_cache: map[^Type_Scope]bool
@(private="file") g_esc_self_cache: map[^Type_Scope]bool

// Can a value of this type hold a reference? (Unknown: assume it can.)
esc_has_refs :: proc(c: ^Checker, t: Type) -> bool {
    if t == nil { return true }
    #partial switch bt in distinct_base(t) {
    case ^Type_Ptr, ^Type_Slice, Type_CString, Type_Any:
        return true
    case ^Type_Fixed_Array:
        return esc_has_refs(c, bt.elem)
    case ^Type_Partial_Array:
        return esc_has_refs(c, bt.elem)
    case ^Type_Union:
        for _, sname in bt.variant_structs {
            if st, ok := c.table.structs[sname]; ok && esc_has_refs(c, st) { return true }
        }
    case ^Type_Scope:
        sd := as_struct_body(bt)
        if sd == nil { return false } // a function value points at code
        if cached, ok := g_esc_refs_cache[bt]; ok { return cached }
        g_esc_refs_cache[bt] = false // terminates recursion; a by-value cycle can't exist
        has := false
        for &f in sd.fields {
            if esc_has_refs(c, f.type_) { has = true; break }
        }
        g_esc_refs_cache[bt] = has
        return has
    }
    return false
}

// The element type of an array, slice or partial array — through one pointer,
// as indexing auto-derefs. nil when `t` isn't indexable.
@(private="file")
esc_elem_type :: proc(t: Type) -> Type {
    bt := distinct_base(t)
    if p, ok := bt.(^Type_Ptr); ok { bt = distinct_base(p.elem) }
    #partial switch v in bt {
    case ^Type_Slice:         return v.elem
    case ^Type_Fixed_Array:   return v.elem
    case ^Type_Partial_Array: return v.elem
    }
    return nil
}

// Does a value of this type hold a partial array inline (whose header points
// back into the value itself)?
@(private="file")
esc_self_pointing :: proc(t: Type) -> bool {
    if t == nil { return false }
    #partial switch bt in distinct_base(t) {
    case ^Type_Partial_Array:
        return true
    case ^Type_Fixed_Array:
        return esc_self_pointing(bt.elem)
    case ^Type_Scope:
        sd := as_struct_body(bt)
        if sd == nil { return false }
        if cached, ok := g_esc_self_cache[bt]; ok { return cached }
        g_esc_self_cache[bt] = false
        has := false
        for &f in sd.fields {
            if esc_self_pointing(f.type_) { has = true; break }
        }
        g_esc_self_cache[bt] = has
        return has
    }
    return false
}

// --- diagnostics ---------------------------------------------------------------

@(private="file")
esc_reporting :: proc(e: ^Esc) -> bool { return e.report && e.quiet == 0 }

@(private="file")
esc_report_store :: proc(e: ^Esc, val: Esc_Roots, site: Esc_Site, span: Span) {
    if !esc_reporting(e) { return }
    what := esc_describe(val)
    if site.call != nil || site.callee != nil {
        name := site.call.name if site.call != nil else site.callee.source_name
        src := esc_param_name(site.callee, site.st.src)
        if site.st.dst == ESC_STORE_GLOBAL {
            check_error(e.c, span, TYPE_ESCAPE_CALL_STORE_GLOBAL, name, src, what)
        } else {
            check_error(e.c, span, TYPE_ESCAPE_CALL_STORE, name, src, esc_param_name(site.callee, site.st.dst), what)
        }
        return
    }
    into := site.target_name
    if site.target != nil {
        if n := expr_diag_name(site.target); n != "" { into = n }
    }
    if into != "" {
        check_error(e.c, span, TYPE_ESCAPE_STORE, what, into)
    } else {
        check_error(e.c, span, TYPE_ESCAPE_STORE_ANON, what)
    }
}

// Name the argument(s) that bring local memory into a returned call result.
@(private="file")
esc_report_call_return :: proc(e: ^Esc, call: ^Expr_Call, span: Span) -> bool {
    callee := esc_callee(e, call)
    sum := esc_summary_of(e, callee)
    if sum == nil { return false }
    sb := strings.builder_make(context.temp_allocator)
    n := 0
    for i in 0 ..< len(call.args) {
        if i >= ESC_MAX_PARAMS { break }
        local := false
        if i in sum.ret      && esc_deepest_local(esc_arg(e, callee, call.args[:], i, false)) > ESC_CALLER { local = true }
        if i in sum.ret_deep && esc_deepest_local(esc_arg(e, callee, call.args[:], i, true))  > ESC_CALLER { local = true }
        if !local { continue }
        if n > 0 { strings.write_string(&sb, ", ") }
        fmt.sbprintf(&sb, "parameter `%s`", esc_param_name(callee, i))
        n += 1
    }
    if n == 0 { return false }
    check_error(e.c, span, TYPE_CANNOT_RETURN_RESULT_RETURN_REFERENCE,
        call.name, strings.to_string(sb), "argument" if n == 1 else "arguments")
    return true
}

@(private="file")
esc_param_name :: proc(callee: ^Type_Scope, i: int) -> string {
    if callee != nil && i >= 0 && i < len(callee.params) { return callee.params[i].name }
    return "?"
}

// The shortest-lived thing a value may point into, for a diagnostic.
@(private="file")
esc_describe :: proc(r: Esc_Roots) -> string {
    worst: ^Esc_Var
    for v in r.vars {
        if worst == nil || v.depth > worst.depth { worst = v }
    }
    if worst != nil && worst.depth >= r.temp {
        switch {
        case worst.is_param:        return fmt.tprintf("the local copy of parameter `%s`", worst.name)
        case worst.depth > ESC_BODY: return fmt.tprintf("block-local `%s`", worst.name)
        case:                       return fmt.tprintf("local `%s`", worst.name)
        }
    }
    if r.temp > 0 { return "a temporary" }
    return "local memory"
}
