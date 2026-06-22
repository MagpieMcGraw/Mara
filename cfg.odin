package mara

import "core:fmt"
import "core:os"

// ---------------------------------------------------------------------------
// Control-flow graph — a real one, shared by return-checking and the analyzer.
//
// One statement-level CFG per source function, built post-check from the durable
// body. Nodes are statements (plus a synthetic Entry and Exit); edges are the
// possible transfers of control. `if`/`for`/`match` are branch nodes (multiple
// successors); `return` goes to Exit and stops; `break`/`continue` go to the
// innermost loop's exit / header; a loop's body has a back-edge to its header.
//
// Two consumers replace ad-hoc structural walks with this graph:
//   * missing-return: the function can "fall off the end" iff a fall-through path
//     reaches Exit — `fall_off` is non-empty (handles loops, early returns,
//     break/continue, unreachable tails uniformly — what always_returns couldn't).
//   * control dependence (analyzer): post-dominators over this graph give each
//     statement the branches that guard it, INCLUDING early-return guard clauses
//     the lexical approximation missed.
// ---------------------------------------------------------------------------

CFG_Kind :: enum { Entry, Exit, Simple, Branch, Return, Break, Continue }

CFG_Node :: struct {
    kind:  CFG_Kind,
    span:  Span,
    succ:  [dynamic]int,
    // Branch metadata (kind == .Branch): the controlling predicate(s) and which
    // construct, so control dependence can recover the guard.
    bkind: Guard_Kind,    // If / For / Match
    conds: []Expr,
}

CFG :: struct {
    nodes:     [dynamic]CFG_Node,
    entry:     int,
    exit:      int,
    fall_off:  [dynamic]int,   // fall-through preds at the function end — empty ⟺ every path returns
    span_node: map[Span]int,   // statement span -> node id (maps a def/return back to its CFG node)
}

// --- construction ----------------------------------------------------------

build_cfgs :: proc(checked: ^Checked_Program) {
    // Every source function, templates included — control flow is type-independent,
    // so the missing-return check is uniform (the analyzer only queries concretes).
    // Control dependence (post-dominators) is NOT computed here: it's expensive and
    // only the slice queries need it, so it is built lazily per function
    // (ensure_fn_analysis) to keep the compile path cheap.
    for _, ft in checked.functions {
        if ft == nil { continue }
        if _, src := ft.origin.(Origin_Source); !src { continue }
        cfg := new(CFG)
        cfg_construct(cfg, ft)
        checked.cfgs[ft] = cfg
    }
    cfg_dump(checked)
}

// Can control reach the function's end without a `return`? (A fall-through path
// to Exit.) The missing-return verdict, handling loops / early returns / break /
// continue uniformly — what the structural always_returns could not.
cfg_falls_off :: proc(checked: ^Checked_Program, ft: ^Type_Scope) -> bool {
    cfg, ok := checked.cfgs[ft]
    if !ok || cfg == nil { return false }
    return len(cfg.fall_off) > 0
}

// --- post-dominators -> control dependence ---------------------------------
// A statement Y is control-dependent on a branch X when one of X's outgoing
// paths always reaches Y and another can avoid it — i.e. some successor A of X
// is post-dominated by Y while X itself is not. This captures the guard the
// LEXICAL approximation missed: after `if bad { return }`, the rest is
// control-dependent on `bad` even though it is not lexically inside the `if`.

@(private="file")
cfg_set_eq :: proc(a, b: map[int]bool) -> bool {
    if len(a) != len(b) { return false }
    for k in a { if k not_in b { return false } }
    return true
}

cfg_build_control_deps :: proc(checked: ^Checked_Program, c: ^CFG) {
    n := len(c.nodes)
    if n == 0 { return }

    // Post-dominator sets by iterative dataflow: pd[n] = {n} ∪ ⋂ pd[successors].
    pd := make([]map[int]bool, n)
    defer { for s in pd { delete(s) }; delete(pd) }
    for i in 0 ..< n {
        pd[i] = make(map[int]bool)
        if i == c.exit { pd[i][i] = true } else { for j in 0 ..< n { pd[i][j] = true } }
    }
    changed := true
    for changed {
        changed = false
        for i in 0 ..< n {
            if i == c.exit { continue }
            ns := make(map[int]bool)
            ns[i] = true
            succ := c.nodes[i].succ
            if len(succ) > 0 {
                inter := make(map[int]bool)
                for k in pd[succ[0]] { inter[k] = true }
                for si in 1 ..< len(succ) {
                    for k in inter { if k not_in pd[succ[si]] { delete_key(&inter, k) } }
                }
                for k in inter { ns[k] = true }
                delete(inter)
            }
            if cfg_set_eq(ns, pd[i]) { delete(ns) } else { delete(pd[i]); pd[i] = ns; changed = true }
        }
    }

    // For each branch X and successor A: every Y that post-dominates A but not X
    // is control-dependent on X. Record per node the set of controlling branches.
    cd := make([]map[int]bool, n)
    defer { for s in cd { delete(s) }; delete(cd) }
    for i in 0 ..< n { cd[i] = make(map[int]bool) }
    for x in 0 ..< n {
        if len(c.nodes[x].succ) < 2 { continue }
        for a in c.nodes[x].succ {
            for y in pd[a] { if y not_in pd[x] { cd[y][x] = true } }
        }
    }

    // Project onto statement spans: control_deps[span] = guards for its branches.
    for y in 0 ..< n {
        if len(cd[y]) == 0 { continue }
        sp := c.nodes[y].span
        if sp.file == "" || sp in checked.control_deps { continue }
        guards: [dynamic]Guard
        for x in cd[y] {
            bn := c.nodes[x]
            append(&guards, Guard{ kind = bn.bkind, span = bn.span, conds = bn.conds })
        }
        checked.control_deps[sp] = guards[:]
    }
}

@(private="file")
cfg_construct :: proc(c: ^CFG, ft: ^Type_Scope) {
    c.entry = cfg_new(c, .Entry, Span{})
    c.exit  = cfg_new(c, .Exit,  Span{})
    fall := cfg_seq(c, ft.body[:], {c.entry}, -1, -1)
    for p in fall { cfg_edge(c, p, c.exit) }   // fall-off paths reach Exit (single sink for post-doms)
    c.fall_off = fall
}

@(private="file")
cfg_new :: proc(c: ^CFG, kind: CFG_Kind, span: Span) -> int {
    id := len(c.nodes)
    append(&c.nodes, CFG_Node{ kind = kind, span = span })
    if span.file != "" && span not_in c.span_node { c.span_node[span] = id }
    return id
}

@(private="file") cfg_edge :: proc(c: ^CFG, from, to: int) { append(&c.nodes[from].succ, to) }

@(private="file")
cfg_wire :: proc(c: ^CFG, preds: []int, node: int) { for p in preds { cfg_edge(c, p, node) } }

@(private="file")
cfg_one :: proc(n: int) -> [dynamic]int { r: [dynamic]int; append(&r, n); return r }

// Walk a statement sequence, threading the set of pending predecessors (the
// node-ids whose control falls into the next statement). Returns the pending
// predecessors after the sequence (empty when every path diverged).
@(private="file")
cfg_seq :: proc(c: ^CFG, stmts: []Stmt, preds: []int, brk, cont: int) -> [dynamic]int {
    cur: [dynamic]int
    for p in preds { append(&cur, p) }
    for s in stmts {
        next := cfg_stmt(c, s, cur[:], brk, cont)
        delete(cur)
        cur = next
    }
    return cur
}

@(private="file")
cfg_stmt :: proc(c: ^CFG, s: Stmt, preds: []int, brk, cont: int) -> [dynamic]int {
    #partial switch v in s {
    case ^Stmt_If:
        n := cfg_branch(c, v.span, .If, cfg_conds_if(v))
        cfg_wire(c, preds, n)
        exits := cfg_seq(c, v.body[:], {n}, brk, cont)
        if len(v.else_body) > 0 {
            else_ex := cfg_seq(c, v.else_body[:], {n}, brk, cont)
            for e in else_ex { append(&exits, e) }
            delete(else_ex)
        } else {
            append(&exits, n)   // no else: the condition itself falls through
        }
        return exits

    case ^Stmt_For:
        p: [dynamic]int; for x in preds { append(&p, x) }
        if v.init != nil { q := cfg_stmt(c, v.init, p[:], brk, cont); delete(p); p = q }
        h := cfg_branch(c, v.span, .For, cfg_conds_for(v))
        cfg_wire(c, p[:], h); delete(p)
        done := cfg_new(c, .Simple, Span{})
        infinite := v.condition == nil && !v.is_range && !v.is_collection_for
        if !infinite { cfg_edge(c, h, done) }            // the loop may finish (or run zero times)
        body_ex := cfg_seq(c, v.body[:], {h}, done, h)   // break -> done, continue -> header
        back := body_ex
        if v.post != nil { back = cfg_stmt(c, v.post, body_ex[:], brk, cont); delete(body_ex) }
        for x in back { cfg_edge(c, x, h) }              // back-edge
        delete(back)
        return cfg_one(done)

    case ^Stmt_Match:
        n := cfg_branch(c, v.span, .Match, cfg_conds_one(v.subject))
        cfg_wire(c, preds, n)
        exits: [dynamic]int
        for arm in v.arms {
            ae := cfg_seq(c, arm.body[:], {n}, brk, cont)
            for e in ae { append(&exits, e) }
            delete(ae)
        }
        if v.subject == nil || len(v.arms) == 0 { append(&exits, n) }   // not provably exhaustive
        return exits

    case Stmt_Return:
        n := cfg_new(c, .Return, v.span); cfg_wire(c, preds, n); cfg_edge(c, n, c.exit)
        return nil
    case Stmt_Break:
        n := cfg_new(c, .Break, v.span); cfg_wire(c, preds, n); if brk  >= 0 { cfg_edge(c, n, brk)  }
        return nil
    case Stmt_Continue:
        n := cfg_new(c, .Continue, v.span); cfg_wire(c, preds, n); if cont >= 0 { cfg_edge(c, n, cont) }
        return nil

    case ^Stmt_Defer:
        // The deferred body runs at scope exit, not here; model the registration
        // as a pass-through (its statements are unconditional w.r.t. this flow).
        n := cfg_new(c, .Simple, v.span); cfg_wire(c, preds, n)
        return cfg_one(n)

    // Non-executable definitions pulled to the bottom of a body — no control flow.
    case ^Stmt_Scope, ^Stmt_Define, ^Stmt_Union_Def, ^Stmt_Distinct_Def,
         ^Stmt_Dispatch_Def, Stmt_Overload, Stmt_Module, ^Stmt_Foreign:
        out: [dynamic]int; for p in preds { append(&out, p) }
        return out

    case:   // simple straight-line statement (assign / decl / multi / call)
        n := cfg_new(c, .Simple, cfg_stmt_span(s))
        cfg_register_decl_spans(c, s, n)
        cfg_wire(c, preds, n)
        return cfg_one(n)
    }
}

// A Stmt_Decl desugars into per-name assigns whose spans the def-use pass keys
// each def on. Map those inner spans to this node too, so a declared variable's
// control dependence resolves (the CFG walks the body-level Stmt_Decl; the
// analyzer keys on the inner assign's span).
@(private="file")
cfg_register_decl_spans :: proc(c: ^CFG, s: Stmt, node: int) {
    decl, ok := s.(^Stmt_Decl)
    if !ok { return }
    for inner in decl.checked {
        sp: Span
        #partial switch a in inner {
        case ^Stmt_Assign:              sp = a.span
        case ^Stmt_Multi_Return_Assign: sp = a.span
        }
        if sp.file != "" && sp not_in c.span_node { c.span_node[sp] = node }
    }
}

@(private="file")
cfg_branch :: proc(c: ^CFG, span: Span, bkind: Guard_Kind, conds: []Expr) -> int {
    n := cfg_new(c, .Branch, span)
    c.nodes[n].bkind = bkind
    c.nodes[n].conds = conds
    return n
}

@(private="file") cfg_conds_if  :: proc(v: ^Stmt_If)  -> []Expr { return cfg_conds_one(v.condition) }
@(private="file")
cfg_conds_one :: proc(e: Expr) -> []Expr {
    if e == nil { return nil }
    c := make([]Expr, 1); c[0] = e; return c
}
@(private="file")
cfg_conds_for :: proc(v: ^Stmt_For) -> []Expr {
    c: [dynamic]Expr
    if v.condition      != nil { append(&c, v.condition) }
    if v.range_low      != nil { append(&c, v.range_low) }
    if v.range_high     != nil { append(&c, v.range_high) }
    if v.collection     != nil { append(&c, v.collection) }
    if v.collection_len != nil { append(&c, v.collection_len) }
    return c[:]
}

@(private="file")
cfg_stmt_span :: proc(s: Stmt) -> Span {
    #partial switch v in s {
    case ^Stmt_Assign:               return v.span
    case ^Stmt_Decl:                 return v.span
    case ^Stmt_Multi_Assign:         return v.span
    case ^Stmt_Multi_Return_Assign:  return v.span
    case Stmt_Call:                  return v.span
    case Stmt_Return:                return v.span
    }
    return Span{}
}

// --- diagnostic: MARA_DUMP_CFG=1 -------------------------------------------

@(private="file")
cfg_dump :: proc(checked: ^Checked_Program) {
    buf: [8]u8
    if os.get_env_buf(buf[:], "MARA_DUMP_CFG") == "" { return }
    for ft, cfg in checked.cfgs {
        name := ft.source_name if ft.source_name != "" else ft.name
        fmt.eprintf("--- CFG: %s  (%d nodes, fall_off=%d) ---\n", name, len(cfg.nodes), len(cfg.fall_off))
        for node, i in cfg.nodes {
            loc := span_loc(node.span) if node.span.file != "" else ""
            tag := fmt.tprintf("%v", node.kind)
            if node.kind == .Branch { tag = fmt.tprintf("branch:%v", node.bkind) }
            id := fmt.tprintf("n%d", i)
            fmt.eprintf("  %-4s %-12s %-22s ->", id, tag, loc)
            for sx in node.succ { fmt.eprintf(" n%d", sx) }
            fmt.eprintln()
        }
    }
}
