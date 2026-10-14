package mara

import "core:fmt"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Name resolution (design/name_resolution.md): what each name in the tree
// refers to, found from the tree alone — before checking, with a stack of
// the names in sight that is thrown away once it's done.
//
// Mara has one kind of scope: a module (its files' text), a file (what it
// uses), a struct's body, a fun's body, a block. A definition (`name :: …`)
// is seen throughout the scope it's written in and every scope inside it; a
// variable from its declaration to its scope's end, never inside a nested
// fun or struct. What a scope uses is seen in it, behind what it defines.
// What a name means by its type — a member, a variant against the type
// expected, a dispatch's member — is the checker's.
// ---------------------------------------------------------------------------

Resolver :: struct {
    k:       ^TC,             // (the check's tree, its modules, its target: `#if`)
    t:       ^Tree,
    refs:    []Ref,           // by node: what its name refers to (kind None: not found)
    token_refs: map[Token_Id]Ref,   // ... a name written as a token: a dispatch's member, an overload's fun
    names:   [dynamic]Rs_Name,
    slots:   map[string]i32,  // a name → its slot in top (one hash a push and a lookup; none a pop)
    top:     [dynamic]i32,    // by slot: the name's innermost entry in names (-1: none)
    scopes:  [dynamic]Rs_Scope,
    modules: map[string]^Rs_Module,
    named:   map[Token_Id]^Rs_Module,   // a module's name, by the token that declares it (its use's)
    defs:    map[Token_Id]Tree_Id,      // a definition, by the token that declares it: its Define
    owners:  map[Token_Id]Token_Id,     // ... a body's: the fun or struct whose body it's in, by its token
    owner:   Token_Id,                  // the fun or struct whose body is being resolved
    members: map[Token_Id]map[string]Ref,   // ... what a qualified name reaches in it (rs_members)
    dispatches: map[Token_Id]bool,      // the definitions that are dispatches (their member's the checker's)
    type_params: map[Token_Id]bool,     // the declarations that are type params (what they're bound to is the checker's)
    type_params_of: map[Tree_Id][dynamic]Token_Id,   // ... each generic's, by its node (an instance binds them)
    generic:     Tree_Id,               // the definition whose signature is being resolved: its type params'
    module:  ^Rs_Module,                // the module being resolved
}

// A name in sight: what it refers to, the entry of the same name it hides,
// the scope it's in (a variable below the innermost fun or struct is out of
// sight).
@(private="file")
Rs_Name :: struct {
    slot:     i32,
    ref:      Ref,
    hides:    i32,
    scope:    i32,
    variable: bool,
}

@(private="file")
Rs_Scope_Kind :: enum u8 { Module, File, Fun, Struct, Block }

@(private="file")
Rs_Scope :: struct {
    kind: Rs_Scope_Kind,
    mark: i32,                  // len(names) when it was entered
    fence: i32,                 // the innermost fun or struct, it or around it: the variables below it are out of sight
    uses: [dynamic]^Rs_Module,  // what it uses: their definitions in sight, behind its own
    self: Ref,                  // a fun's or a struct's: itself (`Self`)
    signature: bool,            // a fun's or a struct's, its params and results being resolved
}

// A module's definitions: what a use of it brings in.
@(private="file")
Rs_Module :: struct {
    name:     string,
    files:    []Tree_Id,
    defs:     map[string]Ref,
    variants: map[string]Ref,   // its enums' variants: what `m.X` reaches past its definitions
}

// --- the stack ----------------------------------------------------------------------

@(private="file")
rs_enter :: proc(r: ^Resolver, kind: Rs_Scope_Kind) {
    fence := i32(len(r.scopes)) if kind == .Fun || kind == .Struct else r.scopes[len(r.scopes) - 1].fence if len(r.scopes) > 0 else -1
    append(&r.scopes, Rs_Scope{kind = kind, mark = i32(len(r.names)), fence = fence})
}

@(private="file")
rs_leave :: proc(r: ^Resolver) {
    s := pop(&r.scopes)
    for i32(len(r.names)) > s.mark {
        e := pop(&r.names)
        r.top[e.slot] = e.hides
    }
}

@(private="file")
rs_push :: proc(r: ^Resolver, name: string, ref: Ref, variable: bool) {
    if name == "" || name == "_" { return }
    slot, ok := r.slots[name]
    if !ok {
        slot = i32(len(r.top))
        append(&r.top, -1)
        r.slots[name] = slot
    }
    append(&r.names, Rs_Name{slot = slot, ref = ref, hides = r.top[slot], scope = i32(len(r.scopes) - 1), variable = variable})
    r.top[slot] = i32(len(r.names) - 1)
}

// A definition, seen throughout the current scope.
@(private="file")
rs_define :: proc(r: ^Resolver, name: string, ref: Ref) { rs_push(r, name, ref, false) }

// A variable, seen from here on.
@(private="file")
rs_declare :: proc(r: ^Resolver, name: string, ref: Ref) { rs_push(r, name, ref, true) }

// What a name refers to from here: a variable in sight, else a definition,
// else what the nearest scope that uses one brings in (two: ambiguous).
@(private="file")
rs_lookup :: proc(r: ^Resolver, name: string) -> (Ref, bool) {
    fence := r.scopes[len(r.scopes) - 1].fence
    if slot, ok := r.slots[name]; ok {
        for i := r.top[slot]; i >= 0; i = r.names[i].hides {
            e := &r.names[i]
            if e.variable && e.scope < fence { continue }
            return e.ref, true
        }
    }
    for i := len(r.scopes) - 1; i >= 0; i -= 1 {
        found: Ref
        n := 0
        for m in r.scopes[i].uses {
            if ref, ok := m.defs[name]; ok && (n == 0 || ref != found) {
                found = ref
                n += 1
            }
        }
        if n == 1 { return found, true }
        if n > 1 { return {}, false }
    }
    return {}, false
}

// --- definitions ----------------------------------------------------------------------

@(private="file")
rs_text :: proc(tok: Token_Id) -> string { return tc_text(tok) }

@(private="file")
rs_live :: proc(r: ^Resolver, stmts: []Tree_Id) -> []Tree_Id { return tc_live(r.k, stmts) }

// What a definition's value makes its name: a fun, a type, a module (`name
// :: use m`, the file's), a constant.
@(private="file")
rs_def_kind :: proc(t: ^Tree, value: Tree_Id) -> Ref_Kind {
    #partial switch t.tag[value] {
    case .Fun_Def:                     return .Fun
    case .Struct_Def, .Union_Def, .Error_Def, .Distinct_Def, .Alias_Def: return .Type
    case .Import:                      return .Module
    case .Dispatch_Def:                return .Fun
    }
    return .Const
}

// Each definition among statements: into a module's table (`into`), else in
// sight in the current scope — a module's alias (`name :: use m`) only so.
@(private="file")
rs_each_def :: proc(r: ^Resolver, stmts: []Tree_Id, into: ^map[string]Ref = nil) {
    t := r.t
    def :: proc(r: ^Resolver, into: ^map[string]Ref, name: string, ref: Ref) {
        if into != nil { into[name] = ref } else { rs_define(r, name, ref) }
    }
    for s in rs_live(r, stmts) {
        #partial switch t.tag[s] {
        case .Define:
            value := Tree_Id(t.b[s])
            kind := rs_def_kind(t, value)
            if kind == .Module {
                if into == nil { rs_name_module(r, t.main[s], value) }
                continue
            }
            def(r, into, rs_text(t.main[s]), {t.main[s], kind})
            r.defs[t.main[s]] = s
            if into == nil && r.owner != 0 { r.owners[t.main[s]] = r.owner }
            if t.tag[value] == .Dispatch_Def { r.dispatches[t.main[s]] = true }
            // (A union's tag enum — a union with data's: `<Name>_Tag`,
            // declared by its `union`.)
            if t.tag[value] == .Union_Def && rs_union_has_data(t, value) {
                def(r, into, strings.concatenate({rs_text(t.main[s]), "_Tag"}, context.temp_allocator), {t.main[value], .Type})
                r.defs[t.main[value]] = s
            }
        case .Foreign:
            for ff in foreign_view(t, s).funs {
                name := foreign_fun_view(t, ff).name
                def(r, into, rs_text(name), {name, .Fun})
            }
        case .Using:
            // (`using x :: …`: as written without it.)
            inner := Tree_Id(t.a[s])
            if t.tag[inner] == .Define {
                one := [1]Tree_Id{inner}
                rs_each_def(r, one[:], into)
            }
        }
    }
}

// Whether a union's variants hold data (else it is an enum).
@(private="file")
rs_union_has_data :: proc(t: ^Tree, u: Tree_Id) -> bool {
    for vr in tree_list(t, t.b[u]) { if t.b[vr] != 0 { return true } }
    return false
}

// What a qualified name reaches in a definition (`A.B`, `m.f`, `Color.Red`):
// a module's definitions; a struct's own (its body's); a union's or an
// error set's variants.
@(private="file")
rs_members :: proc(r: ^Resolver, ref: Ref) -> (map[string]Ref, bool) {
    if ref.kind == .Module {
        if m := rs_ref_module(r, ref); m != nil { return m.defs, true }
        return nil, false
    }
    if ref.decl == 0 { return nil, false }
    if m, made := r.members[ref.decl]; made { return m, true }
    def, ok := r.defs[ref.decl]
    if !ok { return nil, false }
    t := r.t
    value := Tree_Id(t.b[def])
    m := make(map[string]Ref)
    #partial switch t.tag[value] {
    case .Struct_Def, .Fun_Def:
        // (A struct's own definitions; a fun's, its nested ones: `alpha.bump(7)`.)
        rs_each_def(r, scope_view(t, value).body, &m)
    case .Union_Def:
        for vr in tree_list(t, t.b[value]) { m[rs_text(t.main[vr])] = {t.main[vr], .Variant} }
    case .Error_Def:
        for tok in tree_token_list(t, t.a[value]) { m[rs_text(tok)] = {tok, .Variant} }
    case .Distinct_Def, .Alias_Def:
        // (A distinct type's, an alias's: its base's.)
        base := Tree_Id(t.a[value])
        if t.tag[base] != .Type_Name { return nil, false }
        bref, found := r.refs[base], r.refs[base].kind != .None
        if !found {
            parts := tree_token_list(t, t.a[base])
            if len(parts) != 1 { return nil, false }
            bref, found = rs_lookup(r, rs_text(parts[0]))
        }
        if !found || bref.decl == ref.decl { return nil, false }
        return rs_members(r, bref)
    case:
        return nil, false
    }
    r.members[ref.decl] = m
    return m, true
}

// A module named in sight (`name :: use m`, or a use's last part): its name
// the token's.
@(private="file")
rs_name_module :: proc(r: ^Resolver, tok: Token_Id, imp: Tree_Id) {
    m, _ := rs_import(r, imp)
    if m == nil { return }
    r.named[tok] = m
    rs_define(r, rs_text(tok), {tok, .Module})
}

// A module's definitions, from all its files.
@(private="file")
rs_module :: proc(r: ^Resolver, name: string) -> ^Rs_Module {
    if m, ok := r.modules[name]; ok { return m }
    m := new(Rs_Module)
    m.name = name
    m.files = r.k.modules[name] or_else nil
    r.modules[name] = m
    for f in m.files { rs_each_def(r, tree_list(r.t, r.t.a[f]), &m.defs) }
    t := r.t
    for _, ref in m.defs {
        def, ok := r.defs[ref.decl]
        if !ok || ref.kind != .Type { continue }
        value := Tree_Id(t.b[def])
        #partial switch t.tag[value] {
        case .Union_Def:
            if rs_union_has_data(t, value) { continue }
            for vr in tree_list(t, t.b[value]) { m.variants[rs_text(t.main[vr])] = {t.main[vr], .Variant} }
        case .Error_Def:
            for tok in tree_token_list(t, t.a[value]) { m.variants[rs_text(tok)] = {tok, .Variant} }
        }
    }
    return m
}

// The module a use names, and the token that names it (its alias, else its
// path's last part).
@(private="file")
rs_import :: proc(r: ^Resolver, imp: Tree_Id) -> (^Rs_Module, Token_Id) {
    t := r.t
    sb := strings.builder_make(context.temp_allocator)
    parts := tree_token_list(t, t.a[imp])
    for part, i in parts {
        if i > 0 { strings.write_byte(&sb, '.') }
        strings.write_string(&sb, rs_text(part))
    }
    path := strings.to_string(sb)
    if path not_in r.k.modules { return nil, 0 }
    return rs_module(r, path), parts[len(parts) - 1]
}

// --- the walk -------------------------------------------------------------------------

// Every module's names resolved: its definitions in sight in each of its
// files, each file's uses in sight in it.
rs_program :: proc(r: ^Resolver) {
    t := r.t
    names := make([dynamic]string, context.temp_allocator)
    for name in r.k.modules { append(&names, name) }
    slice.sort(names[:])
    for name in names { rs_module(r, name) }
    for name in names {
        m := r.modules[name]
        rs_enter(r, .Module)
        // (The build's own names, every module's: the program, std, void.)
        for b in ([]string{"this_program", "Program", "std", "void"}) { rs_define(r, b, {kind = .Builtin}) }
        r.module = m
        for name, ref in m.defs { rs_define(r, name, ref) }
        // (`include m`: m's definitions in sight in every file of the module.)
        for f in m.files {
            for s in rs_live(r, tree_list(t, t.a[f])) {
                imp := rs_stmt_import(t, s)
                if imp == 0 || build_tokens[t.main[imp]].kind != .Include || t.b[imp] != 0 { continue }
                if used, _ := rs_import(r, imp); used != nil { append(&r.scopes[len(r.scopes) - 1].uses, used) }
            }
        }
        for f in m.files {
            rs_enter(r, .File)
            stmts := rs_live(r, tree_list(t, t.a[f]))
            for s in stmts {
                imp := rs_stmt_import(t, s)
                if imp == 0 { continue }
                used, tok := rs_import(r, imp)
                if used == nil { continue }
                if t.b[imp] == 0 { append(&r.scopes[len(r.scopes) - 1].uses, used) }   // (sealed: only its name)
                if t.tag[s] == .Define { tok = t.main[s] }
                r.named[tok] = used
                rs_define(r, rs_text(tok), {tok, .Module})
            }
            for s in stmts { rs_stmt(r, s) }
            rs_leave(r)
        }
        rs_leave(r)
    }
}

// A statement's use (`use m`, `name :: use m`), if it is one.
@(private="file")
rs_stmt_import :: proc(t: ^Tree, s: Tree_Id) -> Tree_Id {
    imp: Tree_Id
    #partial switch t.tag[s] {
    case .Expr_Stmt: imp = Tree_Id(t.a[s])
    case .Define:    imp = Tree_Id(t.b[s])
    }
    if imp == 0 || t.tag[imp] != .Import { return 0 }
    return imp
}

// A block: its definitions in sight throughout, then its statements in order.
@(private="file")
rs_block :: proc(r: ^Resolver, stmts: []Tree_Id) {
    rs_enter(r, .Block)
    rs_body(r, stmts)
    rs_leave(r)
}

@(private="file")
rs_body :: proc(r: ^Resolver, stmts: []Tree_Id) {
    live := rs_live(r, stmts)
    rs_each_def(r, live)
    for s in live { rs_stmt(r, s) }
}

// What a declaration declares here: a struct's field in its body's top, a
// module's variable in a file, else a local.
@(private="file")
rs_var_kind :: proc(r: ^Resolver) -> Ref_Kind {
    #partial switch r.scopes[len(r.scopes) - 1].kind {
    case .Struct: return .Field
    case .File:   return .Global
    }
    return .Local
}

@(private="file")
rs_stmt :: proc(r: ^Resolver, s: Tree_Id) {
    t := r.t
    #partial switch t.tag[s] {
    case .Define:
        rs_node(r, Tree_Id(t.a[s]))   // (its type, when written)
        rs_def_value(r, s, Tree_Id(t.b[s]))
    case .Decl:
        v := decl_view(t, s)
        rs_node(r, v.type_)
        for x in v.values { rs_node(r, x) }
        kind := rs_var_kind(r)
        for tg in v.targets {
            if t.tag[tg] != .Ident { rs_node(r, tg); continue }
            ref := Ref{t.main[tg], kind}
            r.refs[tg] = ref
            rs_declare(r, rs_text(t.main[tg]), ref)
        }
    case .Using:
        rs_stmt(r, Tree_Id(t.a[s]))
    case .Expose:
        rs_stmt(r, Tree_Id(t.a[s]))
    case .Defer:
        rs_block(r, tree_list(t, t.a[s]))
    case .If, .Elif:
        v := if_view(t, s)
        rs_node(r, v.cond)
        rs_block(r, v.then)
        rs_block(r, v.else_)
    case .Match:
        rs_node(r, Tree_Id(t.a[s]))
        for arm in tree_list(t, t.b[s]) {
            #partial switch t.tag[arm] {
            case .Arm_Else, .Arm_Dot:
                rs_block(r, tree_list(t, t.a[arm]))
            case .Arm_Variant:
                // (Its binding; with none, a subject that is a name is
                // rebound, the variant's payload — declared by the subject's
                // token.)
                rs_enter(r, .Block)
                subject := Tree_Id(t.a[s])
                if b := Token_Id(t.b[arm]); b != 0 {
                    rs_declare(r, rs_text(b), {b, .Local})
                } else if t.tag[subject] == .Ident {
                    rs_declare(r, rs_text(t.main[subject]), {t.main[subject], .Local})
                }
                rs_body(r, tree_list(t, t.a[arm]))
                rs_leave(r)
            case .Arm_Value:
                rs_node(r, Tree_Id(t.a[arm]))
                rs_block(r, tree_list(t, t.b[arm]))
            }
        }
    case .For_Range, .For_Each, .For_C:
        v := for_view(t, s)
        rs_node(r, v.type_)
        rs_node(r, v.lo)
        rs_node(r, v.hi)
        rs_node(r, v.collection)
        rs_enter(r, .Block)
        if v.var != 0 { rs_declare(r, rs_text(v.var), {v.var, .Local}) }
        if v.elem != 0 { rs_declare(r, rs_text(v.elem), {v.elem, .Local}) }
        if v.index != 0 { rs_declare(r, rs_text(v.index), {v.index, .Local}) }
        if v.init != 0 { rs_stmt(r, v.init) }
        rs_node(r, v.cond)
        if v.post != 0 { rs_stmt(r, v.post) }
        rs_block(r, v.body)
        rs_leave(r)
    case .For_Cond:
        rs_node(r, Tree_Id(t.a[s]))
        rs_block(r, tree_list(t, t.b[s]))
    case .Foreign:
        for ff in foreign_view(t, s).funs {
            fv := foreign_fun_view(t, ff)
            for g in fv.params { rs_node(r, params_view(t, g).type_) }
            for x in fv.returns { rs_node(r, x) }
        }
    case .Expr_Stmt:
        if rs_stmt_import(t, s) == 0 { rs_node(r, Tree_Id(t.a[s])) }
    case .Overload:
        rs_token(r, Token_Id(t.b[s]))   // (the dispatch's or the fun's name)
    case .Assign:
        // (A name written that's in sight nowhere — the checker says so — is,
        // from here on, a variable: its uses aren't reported again.)
        rs_node(r, s)
        for tg in tree_list(t, t.a[s]) {
            if t.tag[tg] == .Ident && r.refs[tg].kind == .None { rs_declare(r, rs_text(t.main[tg]), {t.main[tg], rs_var_kind(r)}) }
        }
    case .Break, .Continue, .Module:
    case:
        rs_node(r, s)
    }
}

// A definition's value: a fun's or a struct's scope, a union's variants, a
// type, a constant's value.
@(private="file")
rs_def_value :: proc(r: ^Resolver, def, value: Tree_Id) {
    t := r.t
    #partial switch t.tag[value] {
    case .Fun_Def, .Struct_Def:
        rs_scope_def(r, def, value)
    case .Union_Def:
        // (Its type params, in sight in its variants.)
        rs_enter(r, .Block)
        outer := r.generic
        r.generic = value
        for o in tree_list(t, t.a[value]) {
            if t.tag[o] == .Generic_Param {
                rs_type_param(r, t.main[o])   // (its kind and default: tokens)
            } else {
                rs_node(r, o)
            }
        }
        r.generic = outer
        for vr in tree_list(t, t.b[value]) {
            rs_node(r, Tree_Id(t.a[vr]))
            if body := Tree_Id(t.b[vr]); body != 0 { rs_scope_def(r, vr, body) }
        }
        rs_leave(r)
    case .Dispatch_Def:
        // (Its members: names, written as tokens.)
        for tok in tree_token_list(t, t.a[value]) { rs_token(r, tok) }
    case .Import, .Error_Def:
    case:
        rs_node(r, value)
    }
}

// A name written as a token: what it refers to, by the token.
@(private="file")
rs_token :: proc(r: ^Resolver, tok: Token_Id) {
    if ref, ok := rs_lookup(r, rs_text(tok)); ok { r.token_refs[tok] = ref }
}

// A fun's or a struct's scope: its type params, then its params' types and
// defaults (then the params, in sight), its results, its body.
@(private="file")
rs_scope_def :: proc(r: ^Resolver, def, node: Tree_Id) {
    t := r.t
    v := scope_view(t, node)
    is_struct := t.tag[node] == .Struct_Def
    rs_enter(r, .Struct if is_struct else .Fun)
    sc := &r.scopes[len(r.scopes) - 1]
    sc.self, sc.signature = {t.main[def], .Variant if t.tag[def] == .Variant else .Type}, true
    outer := r.generic
    r.generic = node
    for g in v.generics { rs_type_param(r, t.main[g]) }   // (their kinds and defaults: tokens)
    // (`$T` written in a param's type, a result's: a type param.)
    for g in v.params { rs_dollars(r, params_view(t, g).type_) }
    for x in v.returns { rs_dollars(r, params_view(t, x).type_ if t.tag[x] == .Param_Group else x) }
    for g in v.params {
        pv := params_view(t, g)
        rs_node(r, pv.type_)
        for x in pv.values { rs_node(r, x) }
    }
    for g in v.params {
        pv := params_view(t, g)
        // (A struct's param of a type `$T` or a shape `~S`: a type its
        // instance is given — a type param, its name in sight in its methods.)
        if is_struct && pv.type_ != 0 && (t.tag[pv.type_] == .Type_Dollar || t.tag[pv.type_] == .Type_Tilde) {
            for name in pv.names { rs_type_param(r, name) }
            continue
        }
        for name in pv.names { rs_declare(r, rs_text(name), {name, .Param}) }
    }
    for x in v.returns {
        if t.tag[x] == .Param_Group {
            pv := params_view(t, x)
            rs_node(r, pv.type_)
            for name in pv.names { rs_declare(r, rs_text(name), {name, .Result}) }
        } else {
            rs_node(r, x)
        }
    }
    r.scopes[len(r.scopes) - 1].signature = false
    r.generic = outer
    outer_owner := r.owner
    r.owner = t.main[def]
    if v.intrinsic == 0 { rs_body(r, v.body) }
    r.owner = outer_owner
    rs_leave(r)
}

// A qualified name's parts (`a.b.c`): the first in sight, each next one a
// member. (The first's ref, by its token, too: what a variable's type has
// is the checker's — `fn v.method`.)
@(private="file")
rs_parts :: proc(r: ^Resolver, parts: []Token_Id) -> (ref: Ref, ok: bool) {
    ref, ok = rs_lookup(r, rs_text(parts[0]))
    if ok { r.token_refs[parts[0]] = ref }
    for part in parts[1:] {
        if !ok { break }
        m, has := rs_members(r, ref)
        if !has { return {}, false }
        ref, ok = m[rs_text(part)]
    }
    return
}

// A type param, in sight in its scope.
@(private="file")
rs_type_param :: proc(r: ^Resolver, tok: Token_Id) {
    r.type_params[tok] = true
    if r.generic != 0 {
        if r.generic not_in r.type_params_of { r.type_params_of[r.generic] = {} }
        append(&r.type_params_of[r.generic], tok)
    }
    rs_define(r, rs_text(tok), {tok, .Type})
}

// The type params a type written declares (`$T`).
@(private="file")
rs_dollars :: proc(r: ^Resolver, n: Tree_Id) {
    if n == 0 { return }
    t := r.t
    #partial switch t.tag[n] {
    case .Type_Dollar:
        tok := Token_Id(t.a[n])
        if _, seen := rs_lookup(r, rs_text(tok)); !seen { rs_type_param(r, tok) }
    case .Type_Pointer, .Type_Paren:
        rs_dollars(r, Tree_Id(t.a[n]))
    case .Type_Slice, .Type_Partial, .Type_Array:
        rs_dollars(r, Tree_Id(t.b[n]))
    case .Type_Generic, .Type_Fun:
        for a in tree_list(t, t.a[n]) { rs_dollars(r, a) }
        if t.tag[n] == .Type_Fun { for a in tree_list(t, t.b[n]) { rs_dollars(r, a) } }
    }
}

// An expression's or a type's names, and its parts'.
@(private="file")
rs_node :: proc(r: ^Resolver, n: Tree_Id) {
    if n == 0 { return }
    t := r.t
    #partial switch t.tag[n] {
    case .Ident:
        if ref, ok := rs_lookup(r, rs_text(t.main[n])); ok { r.refs[n] = ref }
        return
    case .Call:
        // (A builtin's name is the builtin's: print, len, a cast, …)
        name := rs_text(t.main[n])
        if rs_builtin_call(name) {
            r.refs[n] = {kind = .Builtin}
        } else if ref, ok := rs_lookup(r, name); ok {
            r.refs[n] = ref
        }
    case .Method_Call:
        // (Through a module or a type, written: what it has by that name.)
        mv := method_view(t, n)
        rs_node(r, mv.receiver)
        if q := mv.receiver; (t.tag[q] == .Ident || t.tag[q] == .Field) && rs_names_def(r.refs[q]) {
            if m, ok := rs_members(r, r.refs[q]); ok {
                if ref, found := m[rs_text(mv.name)]; found { r.refs[n] = ref }
            }
        }
        // (Else, by a value's type, the checker's: its method, or a fun in
        // sight called on it — `x.f(a)`, `f(x, a)`: the fun's, by the name.)
        if r.refs[n].kind == .None { rs_token(r, mv.name) }
        for a in mv.args { rs_node(r, a) }
        rs_node(r, mv.overrides)
        return
    case .Field:
        q := Tree_Id(t.a[n])
        field := rs_text(Token_Id(t.b[n]))
        // (`pkg.X` inside pkg: its own constant — no other name of pkg's.)
        if t.tag[q] == .Ident && r.module != nil && rs_text(t.main[q]) == r.module.name {
            if ref, found := r.module.defs[field]; found && ref.kind == .Const {
                r.refs[n] = ref
                return
            }
        }
        rs_node(r, q)
        if (t.tag[q] == .Ident || t.tag[q] == .Field) && rs_names_def(r.refs[q]) {
            if m, ok := rs_members(r, r.refs[q]); ok {
                if ref, found := m[field]; found {
                    r.refs[n] = ref
                } else if r.refs[q].kind == .Module {
                    // (A module's enum's variant, by its name alone.)
                    if mod := rs_ref_module(r, r.refs[q]); mod != nil { if v, has := mod.variants[field]; has { r.refs[n] = v } }
                }
            }
        }
        return
    case .Dot_Ident, .Named_Entry:
        if t.tag[n] == .Named_Entry { rs_node(r, Tree_Id(t.a[n])) }
        return
    case .Type_Name:
        parts := tree_token_list(t, t.a[n])
        name := rs_text(parts[0])
        ref: Ref
        ok: bool
        switch {
        case len(parts) == 1 && name == "Self":
            ref, ok = rs_self(r)
        case len(parts) == 1:
            if _, primitive := tc_primitive_named(name); primitive { ref, ok = {kind = .Builtin}, true } else { ref, ok = rs_lookup(r, name) }
        case:
            ref, ok = rs_parts(r, parts)
        }
        if ok { r.refs[n] = ref }
        return
    case .Type_Keyword:
        r.refs[n] = {kind = .Builtin}
        return
    case .Type_Dollar:
        // (`$T` again: the first's — what declared it.)
        if ref, ok := rs_lookup(r, rs_text(Token_Id(t.a[n]))); ok { r.refs[n] = ref }
        return
    case .Type_Generic, .Type_Of:
        if t.tag[n] == .Type_Of {
            parts := tree_token_list(t, t.a[n])
            ref, ok := rs_parts(r, parts)
            if ok { r.refs[n] = ref }
            return
        }
        if ref, ok := rs_lookup(r, rs_text(t.main[n])); ok { r.refs[n] = ref }
    }
    rs_children(r, n)
}

// Whether a ref names a definition a qualified name can reach into: a
// module, a type, a fun (its nested definitions).
@(private="file")
rs_names_def :: proc(ref: Ref) -> bool {
    return ref.kind == .Module || ref.kind == .Type || ref.kind == .Fun
}

// `Self`: the innermost struct or fun — a signature's, the one it's in.
@(private="file")
rs_self :: proc(r: ^Resolver) -> (Ref, bool) {
    for i := len(r.scopes) - 1; i >= 0; i -= 1 {
        s := &r.scopes[i]
        if (s.kind == .Fun || s.kind == .Struct) && !s.signature { return s.self, s.self.decl != 0 }
    }
    return {}, false
}

// The builtins called by name: print, crash, the casts, len, … (the checker's
// tc_builtin's).
@(private="file")
rs_builtin_call :: proc(name: string) -> bool {
    switch name {
    case "print", "crash", "int", "uint", "print_cstr", "print_int", "print_float", "len", "cap", "slice_from_ptr", "cstring",
         "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "f16", "f32", "f64", "utf8", "bool":
        return true
    }
    return false
}

// The module a name refers to.
@(private="file")
rs_ref_module :: proc(r: ^Resolver, ref: Ref) -> ^Rs_Module {
    return r.named[ref.decl] or_else nil
}

// A node's children, by its shape: each name in them resolved.
@(private="file")
rs_children :: proc(r: ^Resolver, n: Tree_Id) {
    t := r.t
    shape := tree_shapes[t.tag[n]]
    field :: proc(r: ^Resolver, f: Tree_Field, at: u32) {
        #partial switch f {
        case .Node: rs_node(r, Tree_Id(at))
        case .List: for x in tree_list(r.t, at) { rs_node(r, x) }
        }
    }
    field(r, shape.a, r.t.a[n])
    if shape.a == .Rec {
        count := 0
        for f in shape.rec { if f == .None { break }; count += 1 }
        rec := tree_rec(t, t.a[n], count)
        for f, i in shape.rec[:count] { field(r, f, rec[i]) }
    }
    field(r, shape.b, r.t.b[n])
    if shape.b == .Rec {
        count := 0
        for f in shape.rec { if f == .None { break }; count += 1 }
        rec := tree_rec(t, t.b[n], count)
        for f, i in shape.rec[:count] { field(r, f, rec[i]) }
    }
}

// The program's names resolved, before it's checked: the resolver, kept for
// the checker to read (its refs; what's in sight is gone).
resolve_program :: proc(k: ^TC) -> ^Resolver {
    r := new(Resolver)
    r.k, r.t = k, k.t
    r.refs = make([]Ref, len(k.t.tag))
    rs_program(r)
    delete(r.names)
    delete(r.slots)
    delete(r.top)
    return r
}

// --- the check (stage 1) -----------------------------------------------------------

// MARA_RESOLVE=check: each name the resolver resolved, against the ref the
// checker recorded for it — in instance 0, and for a generic's body, in each
// of its instances. One line a disagreement (the first few), then counts by
// what each said.
resolve_check :: proc(k: ^TC) {
    if os.get_env("MARA_RESOLVE", context.temp_allocator) != "check" || k.c.errors > 0 { return }
    t := k.t
    r := k.rs
    a := k.annot
    Key :: struct { tag: Tree_Tag, checker, resolver: Ref_Kind }
    Tally :: struct {
        agree, missed, extra, differ: map[Key]int,
        // What the checker records differently by design, counted apart:
        // the member a dispatch's arguments chose, where the resolver has the
        // dispatch; the declaration of what a variable holds (its type's, its
        // fun's), where a variable is named in a type or as a callee — and of
        // the type a type param is bound to.
        dispatch, holds: map[Key]int,
        shown: int,
        show:  string,   // (MARA_RESOLVE_SHOW=<tag>: a few of what only one of them resolved, of that tag)
    }
    y := Tally{show = os.get_env("MARA_RESOLVE_SHOW", context.temp_allocator)}
    compare :: proc(r: ^Resolver, n: Tree_Id, want, got: Ref, y: ^Tally) {
        t := r.t
        key := Key{t.tag[n], want.kind, got.kind}
        line :: proc(t: ^Tree, n: Tree_Id, want, got: Ref) {
            sp := tree_span(t, n)
            fmt.printfln("resolve: %s:%d: %v `%s`: checker %v %s, resolver %v %s", span_file(sp), span_line(sp), t.tag[n],
                tc_text(t.main[n]), want.kind, rs_where(want.decl), got.kind, rs_where(got.decl))
        }
        variable := got.kind == .Local || got.kind == .Param || got.kind == .Result || got.kind == .Field || got.kind == .Global || r.type_params[got.decl]
        switch {
        case want.kind == .None && got.kind == .None:
        case want == got:
            y.agree[key] += 1
        case got.kind == .None:
            y.missed[key] += 1
            if y.show != "" && fmt.tprint(t.tag[n]) == y.show && y.missed[key] <= 8 { line(t, n, want, got) }
        case want.kind == .None:
            y.extra[key] += 1
            if y.show != "" && fmt.tprint(t.tag[n]) == y.show && y.extra[key] <= 8 { line(t, n, want, got) }
        case want.kind == .Fun && got.kind == .Fun && r.dispatches[got.decl]:
            y.dispatch[key] += 1
        case variable && want.kind != got.kind:
            y.holds[key] += 1
        case:
            y.differ[key] += 1
            if y.shown < 40 {
                y.shown += 1
                line(t, n, want, got)
            }
        }
    }
    // (A generic's body: its instances' refs; instance 0 says nothing there.)
    covered := make([]bool, len(t.tag), context.temp_allocator)
    for inst, i in a.instances {
        if i == 0 { continue }
        for n := inst.lo; n <= inst.hi; n += 1 {
            covered[n] = true
            compare(r, n, annot_ref(a, Instance_Id(i), n), r.refs[n], &y)
        }
    }
    for n in 1 ..< len(t.tag) {
        if covered[n] { continue }
        compare(r, Tree_Id(n), annot_ref(a, 0, Tree_Id(n)), r.refs[n], &y)
    }
    total :: proc(m: map[Key]int) -> int { s := 0; for _, c in m { s += c }; return s }
    fmt.printfln("resolve: %d agree, %d differ, %d only the checker's, %d only the resolver's, %d a dispatch's member, %d what a variable holds",
        total(y.agree), total(y.differ), total(y.missed), total(y.extra), total(y.dispatch), total(y.holds))
    report :: proc(what: string, m: map[Key]int) {
        keys := make([dynamic]Key, context.temp_allocator)
        for key in m { append(&keys, key) }
        slice.sort_by(keys[:], proc(a, b: Key) -> bool { return int(a.tag) * 64 + int(a.checker) * 8 + int(a.resolver) < int(b.tag) * 64 + int(b.checker) * 8 + int(b.resolver) })
        for key in keys { fmt.printfln("resolve: %s %v: checker %v, resolver %v: %d", what, key.tag, key.checker, key.resolver, m[key]) }
    }
    if k.lookups.on {
        for line in k.lookups.shown { fmt.println(line) }
        fmt.printfln("resolve: lookups: %d agree, %d differ, %d no ref", k.lookups.agree, k.lookups.differ, k.lookups.absent)
    }
    report("differ", y.differ)
    report("only-checker", y.missed)
    report("only-resolver", y.extra)
    report("dispatch", y.dispatch)
    report("holds", y.holds)
}

@(private="file")
rs_where :: proc(tok: Token_Id) -> string {
    if tok == 0 { return "-" }
    sp := token_span(build_tokens[tok])
    return fmt.tprintf("%s:%d", span_file(sp), span_line(sp))
}
