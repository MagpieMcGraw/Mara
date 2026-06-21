package mara

import "core:fmt"
import "core:os"
import "core:strings"

// flow.odin — post-check intraprocedural flow analysis.
//
// This pass walks each function body over the DURABLE graph (ft.body — the exact
// statements codegen emits) AFTER checking, to re-derive the correctness
// analyses that today run INLINE on the during-check Type_Env traversal:
// definite assignment (no read-before-init of a pointer/slice), must-use-err,
// and all-paths-return. Lifting them here is "step 3" of the Type_Env teardown:
// once the point-sensitive flow state is computed by a self-contained post-check
// pass over the scope graph, Type_Env sheds it and shrinks to (eventually
// disappears as) the lookup mirror that the durable graph already replaced.
//
// Why a post-check pass and not an env relocation: the flow state is genuinely
// point-sensitive (it forks at branches, merges at joins), so it can't live on
// the durable Type_Scope. A pass that OWNS its own transient frame and walks the
// graph in control-flow order is the clean home — and it composes with the
// interprocedural call-graph summaries (purity, fallibility) that already live
// post-check (see callgraph.odin / project_call_graph).
//
// STATUS: the traversal scaffold visits every source function and recurses the
// control-flow tree (if/for/defer/match bodies — the .Block scopes), not nested
// Stmt_Scope (separate functions). It OWNS its first analysis: all-paths-return
// (the inline check at check_scope_body has been removed; this pass raises
// TYPE_FUNCTION_MISSING_RETURN_ALL_CODE). Still to port: must-use-err, then
// definite-assignment (branch-merge). MARA_DUMP_FLOW=1 dumps coverage + what was
// flagged.

Flow_Stats :: struct {
    functions:  int, // source functions walked
    statements: int, // statements visited (all nesting levels)
    decls:      int, // Stmt_Decl — what definite-assignment tracks
    branches:   int, // if / match — the merge points
    max_depth:  int, // deepest control-flow nesting reached

    // Functions flagged for "missing return on all code paths" — the first
    // analysis this pass OWNS (emitted below, not just collected).
    missing_return: [dynamic]string,
}

// Entry point — called post-check (after build_call_graph). Walks every source
// function and raises the intraprocedural diagnostics it owns. Takes the Checker
// purely as the error sink (check_error); the analysis itself reads only the
// durable Checked_Program.
flow_analyze_program :: proc(c: ^Checker, checked: ^Checked_Program) {
    stats: Flow_Stats
    for _, ft in checked.functions {
        if ft == nil { continue }
        // Source bodies only: intrinsics/foreigns have no Mara statements to walk.
        if _, is_source := ft.origin.(Origin_Source); !is_source { continue }
        if len(ft.body) == 0 { continue }
        stats.functions += 1
        flow_walk_stmts(&stats, ft.body[:], 1)
        if flow_missing_return(ft) {
            name := ft.source_name if ft.source_name != "" else ft.name
            // Same message + span the inline check used (ft.body_span == s.span).
            check_error(c, ft.body_span, TYPE_FUNCTION_MISSING_RETURN_ALL_CODE, name)
            append(&stats.missing_return, name)
        }
        flow_check_unused(c, ft)
        flow_check_init(c, ft)
    }
    flow_dump_stats(stats)
}

// All-paths-return analysis, recomputed over the durable scope (ft.return_types
// + ft.body) — a faithful copy of the inline check (check_scope_body ~8778):
// a non-void function whose first return isn't `any` and whose returns aren't
// all-err must return on every path. always_returns / is_any / all_err_returns
// are the same shared helpers the inline site uses, so this is the SAME verdict,
// just relocated to the post-check pass.
flow_missing_return :: proc(ft: ^Type_Scope) -> bool {
    if len(ft.return_types) == 0 { return false }       // void
    if is_any(ft.return_types[0]) { return false }      // unresolved generic return
    if all_err_returns(ft.return_types) { return false } // all-err can fall off (.Ok fill)
    return !always_returns(ft.body)
}

// --- must-use-err ---------------------------------------------------------
// An err-typed local that is declared but never read — not checked, not
// propagated with `?` (which leaves no binding), not discarded with `_` — is an
// error. This reproduces the inline check_unused_locals/flag_unused_local over
// the durable body: a per-block scope close over that block's own err-decls,
// with a read ANYWHERE in the block or a descendant clearing it. Shadowing is
// respected via the frame stack (a read binds the nearest enclosing decl).
//
// The pass OWNS this diagnostic: the inline check_unused_locals/flag_unused_local
// and the whole read-flag machinery (Binding.read, mark_read) are gone.

Flow_Err_Local :: struct {
    span: Span,
    read: bool,
}

// One lexical block's err-typed locals (name -> declared/read). Empty for the
// vast majority of blocks, so the map is allocated lazily on first err-decl.
Flow_Frame :: struct {
    errs: map[string]Flow_Err_Local,
}

flow_check_unused :: proc(c: ^Checker, ft: ^Type_Scope) {
    stack: [dynamic]^Flow_Frame
    defer delete(stack)
    flow_unused_block(c, &stack, ft.body[:])
}

// Walk one block: push a frame, process its statements (recording err-decls and
// marking reads on the stack), then at close emit TYPE_UNUSED_ERR for every
// err-decl left unread.
flow_unused_block :: proc(c: ^Checker, stack: ^[dynamic]^Flow_Frame, stmts: []Stmt) {
    frame: Flow_Frame
    append(stack, &frame)
    for s in stmts { flow_unused_stmt(c, stack, s) }
    for name, loc in frame.errs {
        if !loc.read { check_error(c, loc.span, TYPE_UNUSED_ERR, name) }
    }
    delete(frame.errs)
    pop(stack)
}

flow_unused_stmt :: proc(c: ^Checker, stack: ^[dynamic]^Flow_Frame, s: Stmt) {
    #partial switch v in s {
    case ^Stmt_Decl:
        for e in v.init_values { flow_expr_reads(stack, e) }
        flow_expr_reads(stack, v.slice_cap_expr)
        // The desugared `.checked` carries the per-name resolved types; the span
        // stays the Stmt_Decl's, matching the inline flag_unused_local location.
        for inner in v.checked {
            #partial switch a in inner {
            case ^Stmt_Assign:
                if a.is_decl { flow_record_err_decl(stack, a.name, a.var_type, v.span) }
            case ^Stmt_Multi_Return_Assign:
                if a.is_decl {
                    for n, i in a.names {
                        if i < len(a.var_types) { flow_record_err_decl(stack, n, a.var_types[i], v.span) }
                    }
                }
            }
        }
    case ^Stmt_Assign:
        flow_expr_reads(stack, v.value)
        flow_expr_reads(stack, v.target)
        if v.is_decl { flow_record_err_decl(stack, v.name, v.var_type, v.span) }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { flow_unused_stmt(c, stack, a) }
    case ^Stmt_Multi_Return_Assign:
        for e in v.values { flow_expr_reads(stack, e) }
        for e in v.targets { flow_expr_reads(stack, e) }
    case Stmt_Call:
        flow_expr_reads(stack, v.expr)
    case Stmt_Return:
        for e in v.values { flow_expr_reads(stack, e) }
    case ^Stmt_If:
        flow_expr_reads(stack, v.condition)
        flow_unused_block(c, stack, v.body[:])
        flow_unused_block(c, stack, v.else_body[:])
    case ^Stmt_For:
        if v.init != nil { flow_unused_stmt(c, stack, v.init) }
        flow_expr_reads(stack, v.condition)
        flow_expr_reads(stack, v.range_low)
        flow_expr_reads(stack, v.range_high)
        flow_expr_reads(stack, v.collection)
        flow_expr_reads(stack, v.collection_len)
        flow_unused_block(c, stack, v.body[:])
        if v.post != nil { flow_unused_stmt(c, stack, v.post) }
    case ^Stmt_Match:
        flow_expr_reads(stack, v.subject)
        for arm in v.arms {
            flow_expr_reads(stack, arm.value)
            flow_unused_block(c, stack, arm.body[:])
        }
    case ^Stmt_Defer:
        flow_unused_block(c, stack, v.body[:])
    }
}

// Record an err-typed declared name into the innermost frame. Skips `_` and
// non-err types — exactly what flag_unused_local actions today.
flow_record_err_decl :: proc(stack: ^[dynamic]^Flow_Frame, name: string, t: Type, span: Span) {
    if name == "_" || name == "" { return }
    if !is_err_type(t) { return }
    top := stack[len(stack) - 1]
    if top.errs == nil { top.errs = make(map[string]Flow_Err_Local) }
    top.errs[name] = Flow_Err_Local{span = span, read = false}
}

// Mark a name read in the NEAREST enclosing frame that declared it as an err —
// the shadowing-correct equivalent of the inline read flag reaching the binding's
// declaring env via the chain.
flow_mark_read :: proc(stack: ^[dynamic]^Flow_Frame, name: string) {
    #reverse for frame in stack^ {
        if loc, ok := frame.errs[name]; ok {
            loc.read = true
            frame.errs[name] = loc
            return
        }
    }
}

// Recursively mark every identifier read in an expression. A bare Expr_Ident is
// the read; everything else just recurses into sub-expressions. Leaves
// (literals, Self, size_of, type names) contain no local reads. Call names are
// NOT reads — the inline checker marks reads at Expr_Ident sites only, and a
// call's callee is a name string, not an ident.
flow_expr_reads :: proc(stack: ^[dynamic]^Flow_Frame, e: Expr) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:
        flow_mark_read(stack, v.name)
    case ^Expr_Unary:
        flow_expr_reads(stack, v.operand)
    case ^Expr_Binary:
        flow_expr_reads(stack, v.left)
        flow_expr_reads(stack, v.right)
    case ^Expr_Call:
        flow_expr_reads(stack, v.qualifier)
        for a in v.args { flow_expr_reads(stack, a) }
        if v.overrides != nil {
            for f in v.overrides.fields { flow_expr_reads(stack, f.value) }
        }
    case ^Expr_Index:
        flow_expr_reads(stack, v.expr)
        flow_expr_reads(stack, v.index)
    case ^Expr_Slice:
        flow_expr_reads(stack, v.expr)
        flow_expr_reads(stack, v.low)
        flow_expr_reads(stack, v.high)
    case ^Expr_Field_Access:
        flow_expr_reads(stack, v.expr)
    case ^Expr_Array:
        for el in v.elements { flow_expr_reads(stack, el) }
    case ^Expr_Struct_Literal:
        for f in v.fields { flow_expr_reads(stack, f.value) }
    case ^Expr_Try:
        flow_expr_reads(stack, v.inner)
    case ^Expr_If:
        flow_expr_reads(stack, v.condition)
        flow_expr_reads(stack, v.then_expr)
        flow_expr_reads(stack, v.else_expr)
    case ^Expr_Assert:
        flow_expr_reads(stack, v.cond)
    case ^Expr_Take:
        flow_expr_reads(stack, v.storage)
        flow_expr_reads(stack, v.count_expr)
    }
}

// --- definite assignment --------------------------------------------------
// Reading a pointer/slice (or a struct's pointer/slice field) before it has been
// given a usable value is an error. This is a FORWARD DATAFLOW: a single mutable
// `uninit` set of keys (plain `name`, or `var.field` composites) threaded through
// the walk, CLONED at each branch and INTERSECTED at the join — a key stays
// uninit after an if/match iff some non-diverging branch left it uninit (the
// inline promote_branch_inits, recomputed directly). Because the pass owns one
// mutable set, the inline `newly_inited` env-merge artifact dissolves entirely.
//
// VALIDATION MODE: flagged reads are collected into `out`, NOT emitted — the
// inline is_invalid_ref checks are still authoritative. A program that compiles
// must collect nothing; an uninit-read fixture must show up.

Flow_Uninit_Read :: struct {
    span:         Span,
    name:         string, // the variable (the receiver, for a field read)
    field:        string, // "" for a plain var read; the field name for `var.field`
    alias_target: string, // non-"" → field reached because `name` aliases this var (`name = &target`)
}

// The current function's `x = &y` aliases, for the field-uninit redirect
// (`it = &root` makes `it.next` fire on `root.next`). A pass-local var rather
// than a threaded param: the pass is synchronous and only the field-access read
// consults it. Reset per function. Block-scoping/branch-forking of aliases is
// not modelled — a stale alias is only ever consulted on an in-scope receiver,
// so the worst case is the same refinement firing one extra/fewer time in
// contrived nested-reassignment code; the common `it = &root; it.f` is exact.
@(private = "file") g_flow_alias: map[string]string

flow_check_init :: proc(c: ^Checker, ft: ^Type_Scope) {
    uninit: map[string]bool
    defer delete(uninit)
    reads: [dynamic]Flow_Uninit_Read
    defer delete(reads)
    clear(&g_flow_alias)
    flow_init_block(c, ft.body[:], &uninit, &reads)
    // Emit in walk (source) order — the same three diagnostics the inline
    // is_invalid_ref checks raised (var / field / aliased field).
    for r in reads {
        if r.field == "" {
            check_error(c, r.span, TYPE_VARIABLE_USED_BEFORE_ASSIGNED_VALUE, r.name)
        } else if r.alias_target != "" {
            check_error(c, r.span, TYPE_FIELD_ALIASED_VIA_USED_BEFORE, r.field, r.alias_target, r.name)
        } else {
            check_error(c, r.span, TYPE_FIELD_USED_BEFORE_ASSIGNED_VALUE, r.field, r.name)
        }
    }
}

// Record/clear `name`'s alias from its assigned value (`name = &ident`).
flow_update_alias :: proc(name: string, value: Expr) {
    if name == "_" || name == "" || value == nil { return }
    if tgt, ok := address_of_ident(value); ok {
        g_flow_alias[name] = tgt
    } else {
        delete_key(&g_flow_alias, name)
    }
}

flow_clone_set :: proc(m: map[string]bool) -> map[string]bool {
    r := make(map[string]bool)
    for k in m { r[k] = true }
    return r
}

// True if the statement list's tail diverges (return/break/continue) — the same
// test branch_diverges applies, over a slice.
flow_diverges :: proc(stmts: []Stmt) -> bool {
    if len(stmts) == 0 { return false }
    #partial switch _ in stmts[len(stmts) - 1] {
    case Stmt_Return, Stmt_Break, Stmt_Continue:
        return true
    }
    return false
}

// Walk a block: mutate `uninit` in place, drop keys this block itself declared at
// close (out of scope), and report whether the block diverges.
flow_init_block :: proc(c: ^Checker, stmts: []Stmt, uninit: ^map[string]bool, out: ^[dynamic]Flow_Uninit_Read) -> bool {
    local: [dynamic]string
    defer delete(local)
    for s in stmts { flow_init_stmt(c, s, uninit, &local, out) }
    for k in local { delete_key(uninit, k) }
    return flow_diverges(stmts)
}

// Merge sibling branches (if/else, match arms) back into `uninit`: a key is
// uninit-after iff some non-diverging branch left it uninit. All branches
// diverge → the code after is unreachable, leave `uninit` unchanged.
flow_init_merge :: proc(c: ^Checker, uninit: ^map[string]bool, out: ^[dynamic]Flow_Uninit_Read, branches: [][]Stmt) {
    merged: map[string]bool
    defer delete(merged)
    any_live := false
    for b in branches {
        bc := flow_clone_set(uninit^)
        div := flow_init_block(c, b, &bc, out)
        if !div {
            any_live = true
            for k in bc { merged[k] = true }
        }
        delete(bc)
    }
    if any_live {
        clear(uninit)
        for k in merged { uninit^[k] = true }
    }
}

flow_init_stmt :: proc(c: ^Checker, s: Stmt, uninit: ^map[string]bool, local: ^[dynamic]string, out: ^[dynamic]Flow_Uninit_Read) {
    #partial switch v in s {
    case ^Stmt_Decl:
        for e in v.init_values { flow_init_reads(c, e, uninit, out) }
        flow_init_reads(c, v.slice_cap_expr, uninit, out)
        for inner in v.checked {
            #partial switch a in inner {
            case ^Stmt_Assign:
                if a.is_decl {
                    flow_apply_decl(uninit, local, a.name, a.var_type, a.value, a.slice_cap_expr != nil, a.type_expr != nil)
                    flow_update_alias(a.name, a.value)
                }
            // Multi_Return_Assign names take the call's results — always inited.
            }
        }
    case ^Stmt_Assign:
        flow_init_reads(c, v.value, uninit, out)
        if v.target != nil {
            // Complex LHS write. `ident.field =` clears that field key and
            // read-checks only the base; index/deref targets are ordinary reads.
            if fa, ok := v.target.(^Expr_Field_Access); ok {
                if id, idok := fa.expr.(^Expr_Ident); idok {
                    delete_key(uninit, strings.concatenate({id.name, ".", fa.field}))
                }
                flow_init_reads(c, fa.expr, uninit, out)
            } else {
                flow_init_reads(c, v.target, uninit, out)
            }
        } else if v.is_decl {
            flow_apply_decl(uninit, local, v.name, v.var_type, v.value, v.slice_cap_expr != nil, v.type_expr != nil)
            flow_update_alias(v.name, v.value)
        } else {
            // Reassignment: `= void` de-inits a scalar/pointer; otherwise the
            // whole var is inited and its field entries cleared.
            if v.value != nil && is_void_literal(v.value) {
                flow_apply_decl(uninit, local, v.name, v.var_type, v.value, false, false)
            } else {
                delete_key(uninit, v.name)
                flow_clear_fields(uninit, v.name)
            }
            flow_update_alias(v.name, v.value)
        }
    case ^Stmt_Multi_Assign:
        for a in v.assigns { flow_init_stmt(c, a, uninit, local, out) }
    case ^Stmt_Multi_Return_Assign:
        for e in v.values { flow_init_reads(c, e, uninit, out) }
        for e in v.targets { flow_init_reads(c, e, uninit, out) }
        for n in v.names { delete_key(uninit, n) } // inited from the call results
    case Stmt_Call:
        flow_init_reads(c, v.expr, uninit, out)
    case Stmt_Return:
        for e in v.values { flow_init_reads(c, e, uninit, out) }
    case ^Stmt_If:
        flow_init_reads(c, v.condition, uninit, out)
        branches := [2][]Stmt{ v.body[:], v.else_body[:] }
        flow_init_merge(c, uninit, out, branches[:])
    case ^Stmt_For:
        if v.init != nil { flow_init_stmt(c, v.init, uninit, local, out) }
        flow_init_reads(c, v.condition, uninit, out)
        flow_init_reads(c, v.range_low, uninit, out)
        flow_init_reads(c, v.range_high, uninit, out)
        flow_init_reads(c, v.collection, uninit, out)
        flow_init_reads(c, v.collection_len, uninit, out)
        // The body may run zero times, so its inits don't promote — walk a clone
        // for the read-checks inside, then discard.
        bc := flow_clone_set(uninit^)
        flow_init_block(c, v.body[:], &bc, out)
        delete(bc)
        if v.post != nil { flow_init_stmt(c, v.post, uninit, local, out) }
    case ^Stmt_Match:
        flow_init_reads(c, v.subject, uninit, out)
        branches: [dynamic][]Stmt
        defer delete(branches)
        for arm in v.arms { append(&branches, arm.body[:]) }
        flow_init_merge(c, uninit, out, branches[:])
    case ^Stmt_Defer:
        // Runs at scope exit — its inits don't affect the main flow. Read-check
        // on a clone.
        bc := flow_clone_set(uninit^)
        flow_init_block(c, v.body[:], &bc, out)
        delete(bc)
    }
}

// Apply a declaration's effect on the uninit set. A pointer/slice declared
// without a usable value (no initializer, or `= void`) becomes uninit; anything
// else is initialized. (Struct fields are Phase B.)
flow_apply_decl :: proc(uninit: ^map[string]bool, local: ^[dynamic]string, name: string, t: Type, value: Expr, has_slice_cap: bool, annotated: bool) {
    if name == "_" || name == "" { return }
    base := distinct_base(t)
    no_value := value == nil
    if !no_value {
        if _, skip := value.(^Expr_Skip_Constructor); skip { no_value = true }
    }
    is_void := value != nil && is_void_literal(value)
    if _, is_ptr := base.(^Type_Ptr); is_ptr {
        if no_value || is_void {
            uninit^[name] = true
            append(local, name)
        } else {
            delete_key(uninit, name)
        }
        return
    }
    if _, is_slice := base.(^Type_Slice); is_slice {
        if no_value && !has_slice_cap {
            uninit^[name] = true
            append(local, name)
        } else {
            delete_key(uninit, name)
        }
        return
    }
    // Struct: track uninit ptr/slice FIELDS — but ONLY for an ANNOTATED decl, to
    // match the inline (which tracks fields at `x : Struct` and `x : Struct =
    // Foo{}`, never for an inferred `a := Foo{...}`). A no-value decl leaves every
    // such field uninit; an annotated struct literal leaves the ones it doesn't
    // provide; any other initializer (a call, etc.) fully inits the struct.
    if !annotated { return }
    if sd := as_scope_body(base); sd != nil && len(sd.fields) > 0 {
        provided: map[string]bool
        defer delete(provided)
        track := no_value
        if lit, ok := value.(^Expr_Struct_Literal); ok {
            track = true
            for f in lit.fields { provided[f.name] = true }
        }
        if track { flow_add_struct_fields(uninit, local, name, sd, provided) }
    }
}

// Mirror of add_struct_invalid_fields: mark each ptr/slice field without a
// default (and not provided in a literal, not an auto-init sized slice) uninit.
flow_add_struct_fields :: proc(uninit: ^map[string]bool, local: ^[dynamic]string, var_name: string, sd: ^Scope_Body, provided: map[string]bool) {
    for &f in sd.fields {
        if f.name in provided { continue }
        if f.default_value != nil { continue }
        if dt, ok := f.type_.(^Type_Distinct); ok {
            if _, sl := dt.base_type.(^Type_Slice); sl && dt.default_cap_expr != nil { continue }
        }
        base := distinct_base(f.type_)
        is_ref := false
        #partial switch _ in base {
        case ^Type_Ptr, ^Type_Slice:
            is_ref = true
        }
        if is_ref {
            key := strings.concatenate({var_name, ".", f.name})
            uninit^[key] = true
            append(local, key)
        }
    }
}

// Clear every `var.field` entry for a variable (whole-struct reassignment).
flow_clear_fields :: proc(uninit: ^map[string]bool, var_name: string) {
    prefix := strings.concatenate({var_name, "."})
    defer delete(prefix)
    to_del: [dynamic]string
    defer delete(to_del)
    for k in uninit^ {
        if strings.has_prefix(k, prefix) { append(&to_del, k) }
    }
    for k in to_del { delete_key(uninit, k) }
}

// Read-check walk: at each Expr_Ident or `ident.field` access, if the key is in
// the uninit set, collect a flagged read. Recurses sub-expressions exactly like
// flow_expr_reads. (Field keys are Phase B; the base ident is still checked.)
flow_init_reads :: proc(c: ^Checker, e: Expr, uninit: ^map[string]bool, out: ^[dynamic]Flow_Uninit_Read) {
    if e == nil { return }
    #partial switch v in e {
    case ^Expr_Ident:
        if v.name in uninit^ { append(out, Flow_Uninit_Read{span = v.span, name = v.name}) }
    case ^Expr_Unary:
        flow_init_reads(c, v.operand, uninit, out)
    case ^Expr_Binary:
        flow_init_reads(c, v.left, uninit, out)
        flow_init_reads(c, v.right, uninit, out)
    case ^Expr_Call:
        flow_init_reads(c, v.qualifier, uninit, out)
        for a in v.args { flow_init_reads(c, a, uninit, out) }
        if v.overrides != nil {
            for f in v.overrides.fields { flow_init_reads(c, f.value, uninit, out) }
        }
    case ^Expr_Index:
        flow_init_reads(c, v.expr, uninit, out)
        flow_init_reads(c, v.index, uninit, out)
    case ^Expr_Slice:
        flow_init_reads(c, v.expr, uninit, out)
        flow_init_reads(c, v.low, uninit, out)
        flow_init_reads(c, v.high, uninit, out)
    case ^Expr_Field_Access:
        if id, ok := v.expr.(^Expr_Ident); ok {
            key := strings.concatenate({id.name, ".", v.field})
            if key in uninit^ {
                append(out, Flow_Uninit_Read{span = v.span, name = id.name, field = v.field})
            } else if tgt, has := g_flow_alias[id.name]; has {
                // `id` aliases `tgt` (id = &tgt) — id.field reads tgt.field.
                akey := strings.concatenate({tgt, ".", v.field})
                if akey in uninit^ {
                    append(out, Flow_Uninit_Read{span = v.span, name = id.name, field = v.field, alias_target = tgt})
                }
                delete(akey)
            }
            delete(key)
        }
        flow_init_reads(c, v.expr, uninit, out)
    case ^Expr_Array:
        for el in v.elements { flow_init_reads(c, el, uninit, out) }
    case ^Expr_Struct_Literal:
        for f in v.fields { flow_init_reads(c, f.value, uninit, out) }
    case ^Expr_Try:
        flow_init_reads(c, v.inner, uninit, out)
    case ^Expr_If:
        flow_init_reads(c, v.condition, uninit, out)
        flow_init_reads(c, v.then_expr, uninit, out)
        flow_init_reads(c, v.else_expr, uninit, out)
    case ^Expr_Assert:
        flow_init_reads(c, v.cond, uninit, out)
    case ^Expr_Take:
        flow_init_reads(c, v.storage, uninit, out)
        flow_init_reads(c, v.count_expr, uninit, out)
    }
}

// Recurse the control-flow tree, counting coverage. Descends if/for/defer/match
// bodies (the .Block scopes) but NOT a nested Stmt_Scope — a nested fun/struct is
// a separate function with its own checked.functions entry and its own flow, so
// it is walked on its own, not inlined here.
flow_walk_stmts :: proc(stats: ^Flow_Stats, stmts: []Stmt, depth: int) {
    if depth > stats.max_depth { stats.max_depth = depth }
    for s in stmts {
        stats.statements += 1
        #partial switch v in s {
        case ^Stmt_Decl:
            stats.decls += 1
        case ^Stmt_If:
            stats.branches += 1
            flow_walk_stmts(stats, v.body[:], depth + 1)
            flow_walk_stmts(stats, v.else_body[:], depth + 1)
        case ^Stmt_For:
            flow_walk_stmts(stats, v.body[:], depth + 1)
        case ^Stmt_Defer:
            flow_walk_stmts(stats, v.body[:], depth + 1)
        case ^Stmt_Match:
            stats.branches += 1
            for arm in v.arms {
                flow_walk_stmts(stats, arm.body[:], depth + 1)
            }
        }
    }
}

flow_dump_stats :: proc(stats: Flow_Stats) {
    buf: [8]byte
    if os.get_env_buf(buf[:], "MARA_DUMP_FLOW") != "1" { return }
    fmt.eprintf(
        "[flow] %d source funcs, %d stmts, %d decls, %d branches, max depth %d\n",
        stats.functions, stats.statements, stats.decls, stats.branches, stats.max_depth,
    )
    fmt.eprintf("[flow] missing-return flagged: %d %v\n",
        len(stats.missing_return), stats.missing_return)
}
