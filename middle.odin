package mara

// middle.odin — the middle end, a code at a time. Each code is lowered on
// its own (lw_code), then folded and analysed while what it calls is
// analysed already: callees first, a recursive group of funs together (the
// call graph's strongly connected components, bottom-up — it's made from the
// annotations, before any code). Constants and structs' codes are lowered
// first: folding a constant's value runs them. What the analyses find is kept
// and reported once every code is (middle_report), in the order the
// program-wide passes reported it.

Middle :: struct {
    on:    bool,
    flow:  Flow_Pass,
    reach: Reach_Pass,
}

// Every code lowered and analysed, then put in place in written order.
middle_program :: proc(k: ^TC, c: ^Checker, checked: ^Checked_Program, fns: []^Type_Scope) -> Middle {
    mid := Middle{on = true, flow = flow_pass_make(fns)}
    k.lowering = true
    defer k.lowering = false
    saved_salt, saved_pkg, saved_subst := TC_Salt{k.salt, k.salt_lo, k.salt_hi}, k.pkg, k.subst
    defer {
        tc_instance_end(k, saved_salt)
        k.pkg, k.subst = saved_pkg, saved_subst
    }
    codes := lower_begin(k)
    b := k.gb
    pc := &b.pc
    fold := graph_fold_begin(pc, checked)
    escape_begin(c, pc)
    analysed: map[^Program_Graph]bool
    defer delete(analysed)
    // (Once: folded where it uses constants, then its flow and what its calls
    // reach.)
    analyse :: proc(mid: ^Middle, fold: ^Folder, b: ^Graph_Builder, analysed: ^map[^Program_Graph]bool, codes: ^LW_Codes, g: ^Program_Graph) {
        if g == nil || g in analysed^ { return }
        analysed[g] = true
        when ODIN_DEBUG {   // (what it calls is built — else what a call reaches would be guessed at)
            for id := Node_Id(0); id <= g.end; id += 1 {
                if g.kind[id] != .Op || (g.op[id] != .Call && g.op[id] != .Construct) { continue }
                callee := graph_called(g, id)
                if callee == nil || callee in b.pc.funs { continue }
                if i, checked := codes.bodies[callee]; checked && !codes.done[i] {
                    graph_fatal(g.origin[id], "'%s' analysed before '%s', which it calls, is built", graph_name(g, 0), callee.name)
                }
            }
        }
        graph_fold_code(fold, b, g)
        flow_code(&mid.flow, g)
        if g.kind[0] != .Const { reach_code(&mid.reach, &b.pc, g) }
    }

    // Constants, and the structs a constant's value may construct.
    for e, i in k.events {
        #partial switch e.kind {
        case .Const, .Program_Struct: lw_code(k, &codes, i)
        case .Body:                   if e.sc.ts.kind == .Struct { lw_code(k, &codes, i) }
        }
    }
    // Each component's funs, then the component's escape analysis, then each
    // one's own.
    cg := c.cg
    for scc in cg.sccs {
        for n in scc {
            if i, checked := codes.bodies[cg.nodes[n]]; checked { lw_code(k, &codes, i) }
        }
        escape_scc(cg, scc[:])
        for n in scc { analyse(&mid, &fold, b, &analysed, &codes, pc.funs[cg.nodes[n]] or_else nil) }
    }
    // What no call graph node is: the constants, a struct nothing constructs
    // or calls, the program's struct — in the order checked.
    for e, i in k.events {
        if e.kind == .Module_Stmt { continue }
        lw_code(k, &codes, i)
        #partial switch e.kind {
        case .Const:
            if c, built := b.consts[tc_sid_of_const(k, e)]; built { analyse(&mid, &fold, b, &analysed, &codes, c.g) }
        case .Body:
            analyse(&mid, &fold, b, &analysed, &codes, pc.funs[e.sc.ts] or_else nil)
        case .Program_Struct:
            if pt := k.table.funs["Program"] or_else nil; pt != nil { analyse(&mid, &fold, b, &analysed, &codes, pc.funs[pt] or_else nil) }
        }
    }
    lower_place(k, &codes)
    graph_fold_end(&fold)
    return mid
}

// A constant's declaration's id, as its code is kept by (Graph_Builder.consts).
@(private="file")
tc_sid_of_const :: proc(k: ^TC, e: TC_Event) -> Syntax_Id {
    tc_instance_end(k, e.salt)
    return tc_sid(k, e.kc.def)
}

// What the middle end found, reported: flow's, escape's, what calls reach.
middle_report :: proc(c: ^Checker, checked: ^Checked_Program, mid: ^Middle, fns: []^Type_Scope, void_defaults: map[Span]bool) {
    flow_report(c, checked, &mid.flow, fns, void_defaults)
    flow_pass_free(&mid.flow)
    escape_report(c)
    reach_report(c, &mid.reach)
}
