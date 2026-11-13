package mara

import "core:fmt"
import "core:mem"
import "core:os"
import "core:slice"
import "core:strings"

// ---------------------------------------------------------------------------
// Name resolution (design/name_resolution.md): what each name in the tree
// refers to, found from the tree alone — before checking, with a stack of
// the names in sight that is thrown away once it's done. What stays is each
// scope's record (Scope): what it defines, what it uses, the scope it's in —
// what the checker and the tools ask of a scope afterwards.
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
    slots:   map[string]i32,  // a name → its number (made the first time it's declared): how variables are compared (names.odin)
    // Each `all` declared — a local, a param, a definition (not a field):
    // a keyword (a broadcast, `all v`), said by the checker (TYPE_ALL_KEYWORD).
    all_named: map[Token_Id]bool,
    allocator: mem.Allocator,          // the check's: what is found of a scope on a later ask is kept with it
    scopes:  [dynamic]Rs_Level,        // the scopes entered, the innermost last
    here:    ^Scope,                   // ... the innermost one's that has a record
    modules: map[string]^Scope,
    spaces:  map[Token_Id]^Scope,      // a fun's or a struct's scope, by the token that declares it
    files:   map[u16]^Scope,           // a file's, by its index
    named:   map[Token_Id]^Scope,      // a module's name, by the token that declares it (its use's)
    defs:    map[Token_Id]Tree_Id,      // a definition, by the token that declares it: its Define
    owners:  map[Token_Id]Token_Id,     // ... a body's: the fun or struct whose body it's in, by its token
    owner:   Token_Id,                  // the fun or struct whose body is being resolved
    members: map[Token_Id]map[string]Ref,   // ... what a qualified name reaches in it (rs_members)
    alias_of: map[Token_Id]Token_Id,    // `A :: alias B`: the type it names in the end, by A's token (rs_alias_targets)
    dispatches: map[Token_Id]bool,      // the definitions that are dispatches (their member's the checker's)
    type_params: map[Token_Id]bool,     // the declarations that are type params (what they're bound to is the checker's)
    type_params_of: map[Tree_Id][dynamic]Token_Id,   // ... each generic's, by its node (an instance binds them)
    generic:     Tree_Id,               // the definition whose signature is being resolved: its type params'
    module:  ^Scope,                   // the module being resolved
    misses:  map[Tree_Id]Rs_Miss,       // why a name resolved to nothing, by its node ...
    token_misses: map[Token_Id]Rs_Miss, // ... by its token
    clashes: map[Token_Id]Rs_Clash,     // what a declaration runs into, by the token it declares
    in_sight: [dynamic]Rs_Seen,         // resolve_completing: the names in sight at the placeholder
    captured: bool,
    dispatch_names: map[string]bool,    // every dispatch group's name (a call by another isn't one)
    field_types: map[Tree_Id]Rs_Field_Type,   // a type name `S.T` that's a field reference's type, by its node
    type_names: map[Token_Id]bool,      // the definitions `A :: B` that name a type, by the token that declares them (rs_settle_aliases)
    block_of:   map[Tree_Id]Rs_Def,     // a definition in a block of its scope's body, by its node: which, and where it is in sight
    file_rank:  int,                    // the file being resolved: its place among its module's
    records:    [dynamic]^Scope,        // every scope's record that covers text, by where it starts once sorted (names_record_at)
    records_sorted: bool,
    record_lo:  []Token_Id,             // ... where each starts, side by side (the search reads these)
    record_last: int,                   // ... the last one names_record_at started from (the next ask is usually near)
    open_vars:  [dynamic]Names_Open,    // the variables recorded in the levels entered, for their ends (rs_leave)
    levels_entered: int,                // (each level's id)
    seen_defs, seen_used: [dynamic]Names_Seen,   // names_find's scratch
    sight_memo: map[Names_Key]Names_Memo,         // what a file's scope and its module see of a name (names_memo)
    walking:    bool,                             // the walk is on: a file's or a module's names may still change (no memo)
    slot_count: i32,
}

// A definition as written in a scope: its statement (a Define, a foreign
// block). In a block of the scope's body — an if's, a loop's, a match arm's, a
// defer's — it is the body's definition all the same, in sight in its block
// alone: `block`, which of the body's block definitions it is (1, 2, …; 0:
// none — the body's own), and the block's scope.
Rs_Def :: struct {
    node:   Tree_Id,
    block:  int,
    scope:  ^Scope,
    rank:   int,   // (its file's place among its module's: the order they're listed in)
}

// What a scope defines, as written (Scope.list) — the one list of it: the
// checker registers from it, a tool lists from it (resolve_defs). A module's
// is its files'.
Rs_Defs :: struct {
    list:   [dynamic]Rs_Def,
    blocks: int,    // the block definitions so far
    sorted: bool,
}

// What a scope defines, in the order written: the scope the token `decl`
// declares (a fun, a struct, a variant), or — 0 — the module named.
resolve_defs :: proc(r: ^Resolver, decl: Token_Id, module: string) -> []Rs_Def {
    d: ^Rs_Defs
    sc := resolve_scope(r, decl, module)
    if sc == nil { return nil }
    d = &sc.list
    if !d.sorted {
        // (Met a scope at a time — a body's own, then each block's as its
        // statement is reached: as written is by file, then by place.)
        t := r.t
        context.user_ptr = t
        slice.sort_by(d.list[:], proc(x, y: Rs_Def) -> bool {
            t := (^Tree)(context.user_ptr)
            return x.rank < y.rank || x.rank == y.rank && t.first[x.node] < t.first[y.node]
        })
        d.sorted = true
    }
    return d.list[:]
}

// The scope the token `decl` declares (a fun, a struct, a variant), or — 0 —
// the module named; nil: none.
resolve_scope :: proc(r: ^Resolver, decl: Token_Id, module: string) -> ^Scope {
    if decl != 0 { return r.spaces[decl] or_else nil }
    return r.modules[module] or_else nil
}

// A definition in a block of its scope's body: which, and the block's scope.
resolve_block :: proc(r: ^Resolver, def: Tree_Id) -> (Rs_Def, bool) {
    d, in_block := r.block_of[def]
    return d, in_block
}

// `S.T` as a field reference's type: what S names, what T names, and where in
// the name's parts T starts. (T a primitive: its ref the builtin's.)
Rs_Field_Type :: struct {
    owner, elem: Ref,
    split:       int,
}

Rs_Scope_Kind :: enum u8 { Module, File, Fun, Struct, Block }

// A scope entered: its record (a block that defines, uses and overloads
// nothing has none).
@(private="file")
Rs_Level :: struct {
    kind: Rs_Scope_Kind,
    scope: ^Scope,
    end: Token_Id,              // where its text ends: its variables are out of sight from there
    open: int,                  // its variables, from here in open_vars
    id: int,                    // which it is: what's declared at one level (names.odin's clashes)
}

// A use that names its module (`s :: use mara.string`): its definitions are
// reached through the name, `s.trimmed`, and aren't in sight by themselves.
@(private="file")
Rs_Named_Use :: struct {
    name:   string,
    module: ^Scope,
}

// A scope of the program's text, kept: a module (its files' definitions), a
// file, a fun's or a struct's body, a block that uses or overloads
// something. What it defines, what it uses, and the scope it is written in.
// What is in sight at a point is its scope's and each one's around it
// (rs_sight_at); what a use of a scope brings, and what a name into it
// reaches, are its definitions.
Scope :: struct {
    kind:     Rs_Scope_Kind,
    parent:   ^Scope,     // the scope it is written in (a file's: its module)
    name:     string,     // a module's, a fun's, a struct's
    decl:     Token_Id,   // a fun's or a struct's: what declares it (0: a module, a file, a block)
    lo, hi:   Token_Id,   // its statements' tokens (a module's: none)
    own:      Token_Id,   // a module's: its name's last part, as its first file's `module` line writes it — what names it inside itself (rs_own_module)
    files:    []Tree_Id,  // a module's files ...
    parts:    []^Scope,   // ... and the scope of each
    inner:    [dynamic]^Scope,   // a file's: the scopes in it that use or overload something, an inner one before the one around it (rs_scope_at)
    // What it defines.
    defs:     map[string]Ref,   // by name: a module's; a fun's or a struct's once something names into it (filled)
    filled:   bool,
    variants: map[string]Ref,   // its enums' variants: what `m.X` reaches past its definitions
    dispatches: map[string][dynamic]Token_Id,   // its dispatch groups, by name (one name's join)
    aliases:  bool,             // some definition of it may be another name for a type: `A :: B`, `A :: alias B`
    list:     Rs_Defs,          // its definition statements, as written (resolve_defs)
    // What it uses.
    uses:     [dynamic]^Scope,          // the scopes it uses: their definitions in sight in it, behind its own
    named:    [dynamic]Rs_Named_Use,    // ... under a name: reached through that name alone
    overloads: [dynamic]Rs_Overload,    // its `overload op name`s: the operators' groups in it
    used:     [dynamic]Rs_Use,          // a module's: every use written in it, any scope's
    sight:    ^Rs_Sight,                // what is in sight in it, once asked (rs_sight_at)
    // What a name means at a point (names.odin): the text it covers — a
    // file's, a fun's or a struct's whole definition, a union's, a block's
    // statements; a module's, none — its type params, the names its uses
    // declare, and its variables as the checker binds them (a fun's, a
    // struct's, a file's).
    text_lo, text_hi: Token_Id,
    params:   map[string]Ref,
    declared: map[string]Ref,
    vars:     [dynamic]Name_Var,
    checked:  bool,                     // its body was checked
    dups:     map[string][dynamic]Ref,  // the names it defines more than once: the earlier ones (a module's: its files')
    level:    int,                      // the level it's the record of (Rs_Level.id)
    body_lo:  Token_Id,                 // a fun's or a struct's: where its body starts (`Self` before it is the scope around's)
    variant:  bool,                     // ... a union variant's body
}

@(private="file")
Rs_Overload :: struct {
    op:   Token_Kind,
    name: Token_Id,
}

// mara lsp's completion: the text checked has a placeholder name typed in where
// it's asked (COMPLETE_HERE); the names in sight there are recorded (in_sight).
resolve_completing: bool

Rs_Seen :: struct {
    name: string,
    ref:  Ref,
}

// Why a name resolved to nothing — for the checker to say, once nothing it
// knows by type means it either: whose local it is, past a fun's boundary;
// the modules that each have it, at the nearest scope that uses any.
Rs_Miss :: struct {
    hidden: string,
    owners: []string,
    first:  Ref,   // ... one of the things `owners` each have: what kind of name it is
}

// What a declaration (`x := …`) runs into: a name its scope has already (a
// param's, said apart); an enclosing one it hides (before: what declares
// it; shadows: said so — not in a struct); a constant in sight.
Rs_Clash :: struct {
    taken, param, shadows, constant: bool,
    before: Token_Id,
    hides:  Ref,   // a fun, a type or a module of that name in sight (kind None: none)
}

// What is in sight at a point of the groups calls and operators choose
// among: its module's, then what its scope and each one around it use. A
// call names its fun, so a module used under a name is out of its sight; an
// operator names none, so `all` has those too.
Rs_Sight :: struct {
    module: ^Scope,
    uses:   []^Scope,
    named:  []Rs_Named_Use,
    all:    []^Scope,
    overloads: []Rs_Overload,   // the `overload`s of the scopes around it, the nearest's first
}

// A use as written, `use m` or `name :: use m` (alias: its name's token), in
// any scope of a module: what the module needs checked before it is.
Rs_Use :: struct {
    imp:   Tree_Id,
    alias: Token_Id,
}

// The uses written anywhere in a module, in its files' order.
resolve_module_uses :: proc(r: ^Resolver, module: string) -> []Rs_Use {
    if m, ok := r.modules[module]; ok { return m.used[:] }
    return nil
}

// The scope `at` is in: the innermost there that uses or overloads
// something, else its file's (nil: no file of the program's).
@(private="file")
rs_scope_at :: proc(r: ^Resolver, at: Token_Id) -> ^Scope {
    file := r.files[build_tokens[at].file] or_else nil
    if file == nil { return nil }
    for s in file.inner { if at >= s.lo && at < s.hi { return s } }
    return file
}

// What is in sight of the groups where `at` is: what its scope uses, then
// each scope around it — each once. Found the first time its scope is asked,
// and kept with it.
@(private="file")
rs_sight_at :: proc(r: ^Resolver, at: Token_Id) -> (Rs_Sight, bool) {
    here := rs_scope_at(r, at)
    if here == nil { return {}, false }
    if here.sight != nil { return here.sight^, true }
    context.allocator = r.allocator
    s := new(Rs_Sight)
    uses := make([dynamic]^Scope)
    named := make([dynamic]Rs_Named_Use)
    overloads := make([dynamic]Rs_Overload)
    for sc := here; sc != nil; sc = sc.parent {
        for u in sc.uses { if !slice.contains(uses[:], u) { append(&uses, u) } }
        append(&named, ..sc.named[:])
        append(&overloads, ..sc.overloads[:])
        s.module = sc   // (the outermost: its module)
    }
    all := make([dynamic]^Scope)
    append(&all, ..uses[:])
    for u in named { if !slice.contains(all[:], u.module) { append(&all, u.module) } }
    s.uses, s.named, s.all, s.overloads = uses[:], named[:], all[:], overloads[:]
    here.sight = s
    return s^, true
}

// A scope's `overload`s of an operation, as one that sees it has them: its
// own statements'; a module's, its files'. (`once`: those not listed yet.)
@(private="file")
rs_overloads_of :: proc(sc: ^Scope, op: Token_Kind, out: ^[dynamic]Token_Id, once := false) {
    for o in sc.overloads { if o.op == op && !(once && slice.contains(out[:], o.name)) { append(out, o.name) } }
    for f in sc.parts { rs_overloads_of(f, op, out, once) }
}

// The record of the scope being resolved — a block's, made the first time it
// has something to keep: in the nearest scope around it that has one.
@(private="file")
rs_scope_here :: proc(r: ^Resolver) -> ^Scope {
    lv := &r.scopes[len(r.scopes) - 1]
    if lv.scope == nil {
        lv.scope = new(Scope)
        lv.scope.kind, lv.scope.parent = lv.kind, r.here
        lv.scope.level = lv.id
        r.here = lv.scope
        append(&r.records, lv.scope)
    }
    return lv.scope
}

// --- the levels -----------------------------------------------------------------------

@(private="file")
rs_enter :: proc(r: ^Resolver, kind: Rs_Scope_Kind, scope: ^Scope = nil, end: Token_Id = 0) {
    r.levels_entered += 1
    append(&r.scopes, Rs_Level{kind = kind, scope = scope, end = end, open = len(r.open_vars), id = r.levels_entered})
    if scope != nil { r.here = scope }
}

@(private="file")
rs_leave :: proc(r: ^Resolver) {
    s := pop(&r.scopes)
    if s.scope != nil { r.here = s.scope.parent }
    for o in r.open_vars[s.open:] { o.sc.vars[o.at].to = s.end }
    resize(&r.open_vars, s.open)
}

// A name's slot (made, the first time it is met).
@(private="file")
rs_slot :: proc(r: ^Resolver, name: string) -> i32 {
    slot, ok := r.slots[name]
    if !ok {
        slot = r.slot_count
        r.slot_count += 1
        r.slots[name] = slot
    }
    return slot
}

// A variable, recorded in its body's record (a fun's, a struct's, a file's):
// in sight from `from` to its level's end (names.odin).
@(private="file")
rs_declare :: proc(r: ^Resolver, name: string, ref: Ref, from: Token_Id, clash := false) {
    if name == "" || name == "_" { return }
    if name == "all" && ref.decl != 0 { r.all_named[ref.decl] = true }
    slot := rs_slot(r, name)
    if ref.decl == 0 { return }
    for i := len(r.scopes) - 1; i >= 0; i -= 1 {
        #partial switch r.scopes[i].kind {
        case .Fun, .Struct, .File:
            body := r.scopes[i].scope
            if body == nil { return }
            lv := r.scopes[len(r.scopes) - 1]
            append(&body.vars, Name_Var{name, ref, from, 0, lv.id, lv.kind, clash, slot})
            append(&r.open_vars, Names_Open{body, len(body.vars) - 1})
            return
        }
    }
}

// Where a block's names are in sight from: its first statement (else `none`).
@(private="file")
rs_from_body :: proc(r: ^Resolver, body: []Tree_Id, none: Token_Id) -> Token_Id {
    if len(body) > 0 { return r.t.first[body[0]] }
    return none
}

// What `name` means where the walk is, at `at`: asked of the records as they
// stand (names_find_in).
@(private="file")
rs_find :: proc(r: ^Resolver, name: string, at: Token_Id) -> (Ref, bool, Rs_Miss) {
    return names_find_in(r, r.here, name, at)
}

// Whether two definitions of one name are no conflict: one definition, two
// names for one type, or two dispatch groups (groups of one name join).
rs_shares :: proc(r: ^Resolver, a, b: Ref) -> bool {
    if a.decl == b.decl || rs_same(r, a, b) { return true }
    return a.kind == .Fun && b.kind == .Fun && r.dispatches[a.decl] && r.dispatches[b.decl]
}

// Whether a scope's definitions are in sight where `at` is: in its own text
// (a module's: its files'), or where a scope around `at` uses it.
resolve_sees :: proc(r: ^Resolver, at: Token_Id, sc: ^Scope) -> bool {
    if sc == nil { return false }
    if sc.kind != .Module && at >= sc.lo && at < sc.hi { return true }
    for s := rs_scope_at(r, at); s != nil; s = s.parent {
        if s == sc || slice.contains(s.uses[:], sc) { return true }
    }
    return false
}

// Whether a name refers to a scope names reach into: a module, a struct, a fun.
resolve_names_scope :: proc(r: ^Resolver, ref: Ref) -> bool {
    return rs_space_of(r, ref) != nil
}

// A module's definitions, by name (nil: no such module).
resolve_module_defs :: proc(r: ^Resolver, module: string) -> map[string]Ref {
    if m, ok := r.modules[module]; ok { return m.defs }
    return nil
}

// --- definitions ----------------------------------------------------------------------

rs_text :: proc(tok: Token_Id) -> string { return tc_text(tok) }

@(private="file")
rs_live :: proc(r: ^Resolver, stmts: []Tree_Id) -> []Tree_Id { return tc_live(r.k, stmts) }

// What a definition's value makes its name: a fun, a type, a module (`name
// :: use m`, the file's), a constant.
rs_def_kind :: proc(t: ^Tree, value: Tree_Id) -> Ref_Kind {
    #partial switch t.tag[value] {
    case .Fun_Def:                     return .Fun
    case .Struct_Def, .Union_Def, .Error_Def, .Distinct_Def, .Alias_Def: return .Type
    case .Import:                      return .Module
    case .Dispatch_Def:                return .Fun
    }
    return .Const
}

// Each definition among statements: into a record's table (`into`), else
// noted (what defines it, whose it is). (`name :: use m` is a use: rs_uses.)
@(private="file")
rs_each_def :: proc(r: ^Resolver, stmts: []Tree_Id, into: ^map[string]Ref = nil, dups: ^map[string][dynamic]Ref = nil) {
    t := r.t
    def :: proc(r: ^Resolver, into: ^map[string]Ref, dups: ^map[string][dynamic]Ref, name: string, ref: Ref) {
        if into != nil {
            if old, has := into[name]; has && dups != nil && !rs_shares(r, old, ref) {
                if name not_in dups^ { dups[name] = {} }
                append(&dups[name], old)
            }
            into[name] = ref
        }
        if name == "all" && ref.decl != 0 { r.all_named[ref.decl] = true }
    }
    for s in rs_live(r, stmts) {
        #partial switch t.tag[s] {
        case .Define:
            value := Tree_Id(t.b[s])
            kind := rs_def_kind(t, value)
            if kind == .Module { continue }
            if kind == .Const && r.type_names[t.main[s]] { kind = .Type }   // (`A :: B`, B a type: rs_settle_aliases)
            if t.tag[value] == .Dispatch_Def { r.dispatches[t.main[s]] = true }
            def(r, into, dups, rs_text(t.main[s]), {t.main[s], kind})
            r.defs[t.main[s]] = s
            if into == nil && r.owner != 0 { r.owners[t.main[s]] = r.owner }
            // (A union's tag enum — a union with data's: `<Name>_Tag`,
            // declared by its `union`.)
            if t.tag[value] == .Union_Def && rs_union_has_data(t, value) {
                def(r, into, dups, strings.concatenate({rs_text(t.main[s]), "_Tag"}, context.temp_allocator), {t.main[value], .Type})
                r.defs[t.main[value]] = s
            }
        case .Foreign:
            // (A foreign block's funs are definitions like any other.)
            for ff in foreign_view(t, s).funs {
                name := foreign_fun_view(t, ff).name
                def(r, into, dups, rs_text(name), {name, .Fun})
            }
        case .Using:
            // (`using x :: …`: as written without it.)
            inner := Tree_Id(t.a[s])
            if t.tag[inner] == .Define {
                one := [1]Tree_Id{inner}
                rs_each_def(r, one[:], into, dups)
            }
        }
    }
}

// Which of a scope's definitions are other names for types — a module's
// file's, a body's, a block's: its statements, with its names and uses in
// sight. `A :: B`, `A :: m.B`, a name by itself, names a type when what it
// names is one (else it is a constant: `K :: Shape.Rect`, a variant). `A ::
// alias B`, B a type a scope defines, is one type with it, past any aliases
// between (r.alias_of: two names for it are one — rs_same — and `A.X` reaches
// what `B.X` does), and B's variants are its scope's too (`m.X`, as `m.B.X`).
// Again until nothing changes: `A :: B`, `B :: C`. Kept in the scope's names
// too (`space`; nil: none made). Whether any was found.
@(private="file")
rs_settle_aliases :: proc(r: ^Resolver, live: []Tree_Id, space: ^Scope) -> (any: bool) {
    t := r.t
    for changed := true; changed; {
        changed = false
        for s in live {
            if t.tag[s] != .Define || t.a[s] != 0 { continue }
            value := Tree_Id(t.b[s])
            if value == 0 { continue }
            tok := t.main[s]
            name := rs_text(tok)
            #partial switch t.tag[value] {
            case .Ident, .Field:
                if r.type_names[tok] { continue }
                if own, _, _ := rs_find(r, name, tok); own.decl != tok { continue }
                named: Ref
                if t.tag[value] == .Ident {
                    named, _, _ = rs_find(r, rs_text(t.main[value]), t.main[value])
                } else if base := Tree_Id(t.a[value]); t.tag[base] == .Ident {
                    if bref, ok, _ := rs_find(r, rs_text(t.main[base]), t.main[base]); ok {
                        if m, has := rs_members(r, bref); has { named = m[rs_text(Token_Id(t.b[value]))] or_else Ref{} }
                    }
                }
                if named.kind != .Type || named.decl == tok { continue }
                r.type_names[tok] = true
                if space != nil { space.defs[name] = {tok, .Type} }
                changed = true
            case .Alias_Def:
                if tok in r.alias_of || t.tag[Tree_Id(t.a[value])] != .Type_Name { continue }
                // (No parts: `X :: alias` half-written, the editor's text — the parse error says so.)
                parts := tree_token_list(t, t.a[Tree_Id(t.a[value])])
                ref: Ref
                if len(parts) == 1 { ref, _, _ = rs_find(r, rs_text(parts[0]), parts[0]) } else if len(parts) > 1 { ref, _ = rs_parts(r, parts) }
                def, ok := r.defs[ref.decl]
                if ref.kind != .Type || !ok || ref.decl == tok { continue }
                // (An alias of a type name: its target, once known; of any
                // other type, `[512]utf8`, it is the one named.)
                target := ref.decl
                named_value := Tree_Id(t.b[def])
                if t.tag[named_value] == .Alias_Def && t.tag[Tree_Id(t.a[named_value])] == .Type_Name {
                    target = r.alias_of[ref.decl] or_else 0
                    if target == 0 { continue }
                }
                r.alias_of[tok] = target
                changed = true
                if space == nil { continue }
                e := Tree_Id(t.b[r.defs[target]])
                if t.tag[e] == .Error_Def {
                    for v in tree_token_list(t, t.a[e]) { if rs_text(v) not_in space.variants { space.variants[rs_text(v)] = {v, .Variant} } }
                } else if t.tag[e] == .Union_Def && !rs_union_has_data(t, e) {
                    for vr in tree_list(t, t.b[e]) { if rs_text(t.main[vr]) not_in space.variants { space.variants[rs_text(t.main[vr])] = {t.main[vr], .Variant} } }
                }
            }
        }
        any = any || changed
    }
    return
}

// A loop's name, declared in its block (what it runs into: names_clash).
@(private="file")
rs_declare_loop :: proc(r: ^Resolver, tok: Token_Id, from: Token_Id) {
    rs_declare(r, rs_text(tok), {tok, .Local}, from, clash = true)
}

// Whether a union's variants hold data (else it is an enum).
rs_union_has_data :: proc(t: ^Tree, u: Tree_Id) -> bool {
    for vr in tree_list(t, t.b[u]) { if t.b[vr] != 0 { return true } }
    return false
}

// What a qualified name reaches in a definition (`A.B`, `m.f`, `Color.Red`):
// a module's definitions; a struct's own (its body's); a union's or an
// error set's variants.
@(private="file")
rs_members :: proc(r: ^Resolver, ref: Ref) -> (map[string]Ref, bool) {
    // (A module's definitions; a struct's own; a fun's, its nested ones:
    // `alpha.bump(7)`.)
    if sp := rs_space_of(r, ref); sp != nil { return sp.defs, true }
    if ref.kind == .Module || ref.decl == 0 { return nil, false }
    if m, made := r.members[ref.decl]; made { return m, true }
    def, ok := r.defs[ref.decl]
    if !ok { return nil, false }
    t := r.t
    value := Tree_Id(t.b[r.defs[r.alias_of[ref.decl] or_else ref.decl]])
    m := make(map[string]Ref)
    #partial switch t.tag[value] {
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
            bref, found, _ = rs_find(r, rs_text(parts[0]), parts[0])
        }
        if !found || bref.decl == ref.decl { return nil, false }
        return rs_members(r, bref)
    case:
        return nil, false
    }
    r.members[ref.decl] = m
    return m, true
}

// A module's own name inside itself, where nothing in sight has that name
// and it qualifies another (`pkg.helper()` in pkg): the module. No name in
// sight by itself: a variable may be called what its module is.
@(private="file")
rs_own_module :: proc(r: ^Resolver, name: string) -> (Ref, bool) {
    m := r.module
    if m == nil || m.own == 0 || name != rs_text(m.own) { return {}, false }
    r.named[m.own] = m
    return {m.own, .Module}, true
}

// The token that names a module inside itself (0: none).
resolve_module_own :: proc(r: ^Resolver, module: string) -> Token_Id {
    if m, ok := r.modules[module]; ok && m.own in r.named { return m.own }
    return 0
}

// The names of the scope a name refers to — a module, a struct, a fun: nil
// for anything else. A struct's and a fun's are found once, from its body.
rs_space_of :: proc(r: ^Resolver, ref: Ref) -> ^Scope {
    if ref.kind == .Module { return rs_ref_module(r, ref) }
    if ref.decl == 0 || ref.kind != .Type && ref.kind != .Fun { return nil }
    if sp, made := r.spaces[ref.decl]; made && sp.filled { return sp }
    def, ok := r.defs[r.alias_of[ref.decl] or_else ref.decl]
    if !ok { return nil }
    t := r.t
    value := Tree_Id(t.b[def])
    if t.tag[value] != .Struct_Def && t.tag[value] != .Fun_Def { return nil }
    sp := rs_scope_of(r, t.main[def], value)
    if !sp.filled {
        sp.filled = true
        rs_space_fill(r, sp, scope_view(t, value).body)
        rs_space_variants(r, sp)
    }
    return sp
}

// A fun's or a struct's scope, by the token that declares it: made the first
// time it is met — named into, or resolved.
@(private="file")
rs_scope_of :: proc(r: ^Resolver, decl: Token_Id, node: Tree_Id) -> ^Scope {
    if sc, made := r.spaces[decl]; made { return sc }
    sc := new(Scope)
    sc.kind = .Struct if r.t.tag[node] == .Struct_Def else .Fun
    sc.name, sc.decl = rs_text(decl), decl
    sc.text_lo, sc.text_hi = r.t.first[node], r.t.end[node]
    r.spaces[decl] = sc
    append(&r.records, sc)
    return sc
}

// A module's names, from all its files.
@(private="file")
rs_module :: proc(r: ^Resolver, name: string) -> ^Scope {
    if m, ok := r.modules[name]; ok { return m }
    m := new(Scope)
    m.kind, m.name, m.filled = .Module, name, true
    m.files = r.k.modules[name] or_else nil
    m.parts = make([]^Scope, len(m.files))
    for &f in m.parts {
        f = new(Scope)
        f.kind, f.parent, f.name = .File, m, name
    }
    r.modules[name] = m
    for f in m.files {
        if stmts := tree_list(r.t, r.t.a[f]); m.own == 0 && len(stmts) > 0 && r.t.tag[stmts[0]] == .Module {
            if parts := tree_token_list(r.t, r.t.a[stmts[0]]); len(parts) > 0 { m.own = parts[len(parts) - 1] }
        }
    }
    for f in m.files { rs_space_fill(r, m, tree_list(r.t, r.t.a[f])) }
    // (Each file's own, in its record too: one of them defined in another
    // file as well conflicts there, as it's seen.)
    for f, i in m.files { rs_each_def(r, tree_list(r.t, r.t.a[f]), &m.parts[i].defs, &m.parts[i].dups) }
    rs_space_variants(r, m)
    return m
}

// A scope's statements' names, into its record: its definitions and its
// dispatch groups — what a call in sight of it chooses among.
@(private="file")
rs_space_fill :: proc(r: ^Resolver, m: ^Scope, stmts: []Tree_Id) {
    t := r.t
    rs_each_def(r, stmts, &m.defs, nil if m.kind == .Module else &m.dups)
    for s in rs_live(r, stmts) {
        #partial switch t.tag[s] {
        case .Define:
            if value := Tree_Id(t.b[s]); value != 0 && t.tag[value] == .Dispatch_Def && t.a[s] == 0 {
                name := rs_text(t.main[s])
                if name not_in m.dispatches { m.dispatches[name] = {} }
                append(&m.dispatches[name], t.main[s])
                r.dispatch_names[name] = true
            }
            if value := Tree_Id(t.b[s]); value != 0 && t.a[s] == 0 {
                #partial switch t.tag[value] { case .Ident, .Field, .Alias_Def: m.aliases = true }
            }
        }
    }
}

// A space's enums' and error sets' variants: what `m.X` reaches past its
// definitions.
@(private="file")
rs_space_variants :: proc(r: ^Resolver, m: ^Scope) {
    t := r.t
    for _, ref in m.defs {
        def, ok := r.defs[r.alias_of[ref.decl] or_else ref.decl]
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
}

// The scope a use names — a module, by its path; else a struct or a fun in
// sight, `use Shapes`, `use m.Shapes` — its names, the token that names it
// (its path's last part), and what it refers to (a module: nothing — the use
// declares its name).
@(private="file")
rs_import :: proc(r: ^Resolver, imp: Tree_Id) -> (^Scope, Token_Id, Ref) {
    t := r.t
    sb := strings.builder_make(context.temp_allocator)
    parts := tree_token_list(t, t.a[imp])
    if len(parts) == 0 { return nil, 0, {} }
    for part, i in parts {
        if i > 0 { strings.write_byte(&sb, '.') }
        strings.write_string(&sb, rs_text(part))
    }
    path := strings.to_string(sb)
    if path in r.k.modules { return rs_module(r, path), parts[len(parts) - 1], {} }
    ref, ok := rs_parts(r, parts)
    if !ok || ref.kind == .Module { return nil, 0, {} }
    if sp := rs_space_of(r, ref); sp != nil { return sp, parts[len(parts) - 1], ref }
    return nil, 0, {}
}

// --- the walk -------------------------------------------------------------------------

// Whether two refs are one: the same, or two type names for one type (r.alias_of).
rs_same :: proc(r: ^Resolver, a, b: Ref) -> bool {
    if a == b { return true }
    if a.kind != .Type || b.kind != .Type { return false }
    return (r.alias_of[a.decl] or_else a.decl) == (r.alias_of[b.decl] or_else b.decl)
}

// Every module's names recorded, a module after the modules it uses — what
// it names in them is settled by then. In each: its files' definitions and
// uses, then which of its definitions are other names for types (again until
// nothing changes: one file's `A :: B` may name another's `B :: C`), then
// each file's statements. A file is a scope as a body is; its module's scope,
// around it, has every file's definitions: the files of one module see each
// other's.
rs_program :: proc(r: ^Resolver) {
    t := r.t
    names := make([dynamic]string, context.temp_allocator)
    for name in r.k.modules { append(&names, name) }
    slice.sort(names[:])
    for name in names { rs_module(r, name) }
    order := make([dynamic]string, context.temp_allocator)
    seen := make(map[string]bool, allocator = context.temp_allocator)
    for name in names { rs_module_order(r, name, &order, &seen) }
    for name in order {
        m := r.modules[name]
        rs_enter_module(r, m)
        for f, rank in m.files {
            rs_enter(r, .File, m.parts[rank], t.end[f])
            m.parts[rank].text_lo, m.parts[rank].text_hi = t.first[f], t.end[f]
            append(&r.records, m.parts[rank])
            r.file_rank = rank
            if t.first[f] != 0 { r.files[build_tokens[t.first[f]].file] = m.parts[rank] }
            rs_body_names(r, rs_live(r, tree_list(t, t.a[f])))
            rs_leave(r)
        }
        for changed := m.aliases; changed; {
            changed = false
            for f, rank in m.files {
                rs_enter(r, .File, m.parts[rank], t.end[f])
                if rs_settle_aliases(r, rs_live(r, tree_list(t, t.a[f])), m) { changed = true }
                rs_leave(r)
            }
        }
        for f, rank in m.files {
            rs_enter(r, .File, m.parts[rank], t.end[f])
            m.parts[rank].level = r.scopes[len(r.scopes) - 1].id
            r.file_rank = rank
            rs_body_stmts(r, rs_live(r, tree_list(t, t.a[f])))
            rs_leave(r)
        }
        rs_leave(r)
    }
}

// A module after each module its files use (the lexer's list of them), once.
// (A module that needs itself is the checker's to say: met again here, it's
// left where it is.)
@(private="file")
rs_module_order :: proc(r: ^Resolver, name: string, order: ^[dynamic]string, seen: ^map[string]bool) {
    if name in seen { return }
    seen[name] = true
    for f in r.k.modules[name] {
        if r.t.first[f] == 0 { continue }
        for path in build_files[build_tokens[r.t.first[f]].file].imports {
            if path in r.k.modules { rs_module_order(r, path, order, seen) }
        }
    }
    append(order, name)
}

// A module's scope, entered (the build's own names, `std` and `void`, are in
// sight in it: names_gather).
@(private="file")
rs_enter_module :: proc(r: ^Resolver, m: ^Scope) {
    rs_enter(r, .Module, m)
    r.module = m
}

// The dispatch groups named `name` in sight where `at` is: its module's,
// then each module its file or its module uses' — groups of one name join
// (core's `add` and a program's own). In the order a call tries them. For an
// operator's group, `all`: modules used under a name count too.
resolve_dispatches :: proc(r: ^Resolver, at: Token_Id, name: string, all := false) -> []Token_Id {
    if name not_in r.dispatch_names { return nil }
    sight, ok := rs_sight_at(r, at)
    if !ok { return nil }
    out := make([dynamic]Token_Id, context.temp_allocator)
    if groups, has := sight.module.dispatches[name]; has { append(&out, ..groups[:]) }
    for u in sight.all if all else sight.uses {
        if u == sight.module { continue }
        if groups, has := u.dispatches[name]; has { append(&out, ..groups[:]) }
    }
    return out[:]
}

// The dispatch groups an `overload` names (`group`, its name's token) where
// `at` is: those of that name in sight there, and the one the name means
// where the overload is written — a body's own group.
resolve_overload_groups :: proc(r: ^Resolver, at, group: Token_Id) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    append(&out, ..resolve_dispatches(r, at, rs_text(group), all = true))
    if ref, ok := r.token_refs[group]; ok && r.dispatches[ref.decl] && !slice.contains(out[:], ref.decl) { append(&out, ref.decl) }
    return out[:]
}

// The dispatch groups named `name` in the modules `homes` — the modules a
// call's arguments' types are defined in, whose groups join those in sight
// (map.mara's map_hash(key) finds the one beside the key's type).
resolve_dispatches_in :: proc(r: ^Resolver, homes: []string, name: string) -> []Token_Id {
    if name not_in r.dispatch_names { return nil }
    out := make([dynamic]Token_Id, context.temp_allocator)
    for home in homes {
        m, ok := r.modules[home]
        if !ok { continue }
        if groups, has := m.dispatches[name]; has { append(&out, ..groups[:]) }
    }
    return out[:]
}

// The groups an operation `op` overloads in the modules `homes` (its
// operands' types'), beside those in sight.
resolve_overloads_in :: proc(r: ^Resolver, homes: []string, op: Token_Kind) -> []Token_Id {
    out := make([dynamic]Token_Id, context.temp_allocator)
    for home in homes {
        m, ok := r.modules[home]
        if !ok { continue }
        rs_overloads_of(m, op, &out)
    }
    return out[:]
}

// A module in sight at a point, as what's listed there sees it (can_do_funs):
// its name, what its names are called with (`s.` for `s :: use m`, else ""),
// its definitions and its dispatch groups.
Resolve_Seen_Module :: struct {
    name, prefix: string,
    defs:         map[string]Ref,
    dispatches:   map[string][dynamic]Token_Id,
}

// The modules in sight where `at` is: its file's own first, then its uses,
// then those it names.
resolve_modules_in_sight :: proc(r: ^Resolver, at: Token_Id) -> []Resolve_Seen_Module {
    sight, ok := rs_sight_at(r, at)
    if !ok || sight.module == nil { return nil }
    out := make([dynamic]Resolve_Seen_Module, context.temp_allocator)
    seen :: proc(m: ^Scope, prefix: string) -> Resolve_Seen_Module { return {m.name, prefix, m.defs, m.dispatches} }
    append(&out, seen(sight.module, ""))
    for u in sight.uses { if u != sight.module { append(&out, seen(u, "")) } }
    for n in sight.named { append(&out, seen(n.module, fmt.tprintf("%s.", n.name))) }
    return out[:]
}

// The names of the dispatch groups behind operators (`overload + add`), every
// module's.
resolve_overload_names :: proc(r: ^Resolver) -> map[string]bool {
    out := make(map[string]bool, allocator = context.temp_allocator)
    for _, m in r.modules { for f in m.parts { for o in f.overloads { out[rs_text(o.name)] = true } } }
    return out
}

// The use that keeps `name` behind a name where `at` is (`s :: use mara.string`,
// for `trimmed`): what that name is, and the module's.
resolve_named_use_of :: proc(r: ^Resolver, at: Token_Id, name: string) -> (alias, module: string, ok: bool) {
    for sc := rs_scope_at(r, at); sc != nil; sc = sc.parent {
        for u in sc.named {
            _, is_def := u.module.defs[name]
            _, is_variant := u.module.variants[name]
            if is_def || is_variant { return u.name, u.module.name, true }
        }
    }
    return
}

// The groups an operation `op` overloads, by name, in sight where `at` is:
// the `overload`s of the scopes around it, its module's, then each module its
// scopes use, under a name or not.
resolve_overloads :: proc(r: ^Resolver, at: Token_Id, op: Token_Kind) -> []Token_Id {
    sight, ok := rs_sight_at(r, at)
    if !ok { return nil }
    out := make([dynamic]Token_Id, context.temp_allocator)
    for o in sight.overloads { if o.op == op { append(&out, o.name) } }
    rs_overloads_of(sight.module, op, &out, once = true)
    for u in sight.all {
        if u == sight.module { continue }
        rs_overloads_of(u, op, &out)
    }
    return out[:]
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
    rs_enter(r, .Block, end = r.t.end[stmts[len(stmts) - 1]] if len(stmts) > 0 else 0)
    rs_body(r, stmts)
    rs_leave(r)
}

// (`space`: the scope's names, where it has them — a module's file's, a
// fun's or a struct's body's that something named into.)
@(private="file")
rs_body :: proc(r: ^Resolver, stmts: []Tree_Id, space: ^Scope = nil) {
    live := rs_live(r, stmts)
    // (Its definitions, then its uses — one may name a definition of its own
    // — then which of its definitions are other names for types: what they
    // name may come from a use.)
    rs_body_names(r, live)
    rs_settle_aliases(r, live, space)
    rs_body_stmts(r, live)
}

// A scope's definitions and uses, recorded.
@(private="file")
rs_body_names :: proc(r: ^Resolver, live: []Tree_Id) {
    rs_each_def(r, live)
    rs_note_defs(r, live)
    // (A block's definitions, in its record too: in sight in it alone.)
    if lv := r.scopes[len(r.scopes) - 1]; lv.kind == .Block && lv.scope != nil { rs_each_def(r, live, &lv.scope.defs, &lv.scope.dups) }
    rs_uses(r, live)
}

// A scope's statements, walked; then where it is in the text.
@(private="file")
rs_body_stmts :: proc(r: ^Resolver, live: []Tree_Id) {
    for s in live { rs_stmt(r, s) }
    // (Where it is; found there by what asks what is in sight at a point,
    // when it uses a scope or overloads an operator itself: rs_scope_at.)
    if sc := r.scopes[len(r.scopes) - 1].scope; sc != nil && len(live) > 0 {
        t := r.t
        sc.lo, sc.hi = t.first[live[0]], t.end[live[len(live) - 1]]
        if sc.text_hi == 0 { sc.text_lo, sc.text_hi = sc.lo, sc.hi }
        if sc.kind != .File && len(sc.uses) + len(sc.named) + len(sc.overloads) > 0 {
            for i := len(r.scopes) - 2; i >= 0; i -= 1 {
                if r.scopes[i].kind == .File { append(&r.scopes[i].scope.inner, sc); break }
            }
        }
    }
}

// A scope's definition statements, noted for the scope whose they are: the
// fun or struct whose body this is, or is a block of; a file's, its module's.
@(private="file")
rs_note_defs :: proc(r: ^Resolver, live: []Tree_Id) {
    t := r.t
    d: ^Rs_Defs
    for s in live {
        if t.tag[s] != .Define && t.tag[s] != .Foreign { continue }
        if d == nil {
            // (The fun's or the struct's whose body this is, or is a block
            // of; else its module's.)
            d = &r.module.list
            for i := len(r.scopes) - 1; i >= 0; i -= 1 {
                if k := r.scopes[i].kind; k == .Fun || k == .Struct { d = &r.scopes[i].scope.list; break }
            }
        }
        def := Rs_Def{node = s, rank = r.file_rank}
        if t.tag[s] == .Define && r.scopes[len(r.scopes) - 1].kind == .Block {
            d.blocks += 1
            def.block, def.scope = d.blocks, rs_scope_here(r)
            r.block_of[s] = def
        }
        append(&d.list, def)
    }
}

// A scope's uses (`use m`, `name :: use m`), any scope's: the module's
// definitions in sight throughout it, behind its own — under the name alone,
// when the use gives one — and the module's name, its path's last part or the
// name given. Its own: whoever names into the scope doesn't see them. Each is
// noted for its module (Scope.used; `note` false: it is, already). And its
// `overload`s: the groups its operators call, throughout it.
@(private="file")
rs_uses :: proc(r: ^Resolver, live: []Tree_Id, note := true) {
    t := r.t
    for s in live {
        if t.tag[s] == .Overload { append(&rs_scope_here(r).overloads, Rs_Overload{build_tokens[t.a[s]].kind, Token_Id(t.b[s])}) }
        imp := rs_stmt_import(t, s)
        if imp == 0 { continue }
        alias := t.main[s] if t.tag[s] == .Define else Token_Id(0)
        used, tok, ref := rs_import(r, imp)
        // (A module's — one not found too, for the checker to say: checked
        // before this one is.)
        if note && r.module != nil && (used == nil || used.decl == 0) { append(&r.module.used, Rs_Use{imp, alias}) }
        if used == nil { continue }
        scope := rs_scope_here(r)
        if alias != 0 {
            tok = alias
            append(&scope.named, Rs_Named_Use{rs_text(tok), used})
        } else {
            append(&scope.uses, used)
        }
        // (Its name: a module's, the use declares; a struct's or a fun's is
        // another name for it.)
        if used.decl == 0 {
            r.named[tok] = used
            scope.declared[rs_text(tok)] = {tok, .Module}
        } else {
            scope.declared[rs_text(tok)] = ref
        }
    }
}

// A statement: what it declares, the blocks in it. (What its names mean is
// asked of the records once the walk is done: names_fill.)
@(private="file")
rs_stmt :: proc(r: ^Resolver, s: Tree_Id) {
    t := r.t
    #partial switch t.tag[s] {
    case .Define:
        rs_def_value(r, s, Tree_Id(t.b[s]))
    case .Decl:
        // (A local, whatever scope declares it: a file's is its module's
        // body's; a struct's, its constructor's — its layout once checked,
        // tc_layout.)
        for tg in decl_view(t, s).targets {
            if t.tag[tg] != .Ident { continue }
            ref := Ref{t.main[tg], .Local}
            r.refs[tg] = ref
            rs_declare(r, rs_text(t.main[tg]), ref, t.end[s], clash = true)
        }
    case .Using, .Expose:
        rs_stmt(r, Tree_Id(t.a[s]))
    case .Defer:
        rs_block(r, tree_list(t, t.a[s]))
    case .If, .Elif:
        v := if_view(t, s)
        rs_block(r, v.then)
        rs_block(r, v.else_)
    case .Match:
        for arm in tree_list(t, t.b[s]) {
            #partial switch t.tag[arm] {
            case .Arm_Else, .Arm_Dot:
                rs_block(r, tree_list(t, t.a[arm]))
            case .Arm_Variant:
                // (Its binding; with none, a subject that is a name is
                // rebound, the variant's payload — declared by the subject's
                // token.)
                rs_enter(r, .Block, end = t.end[arm])
                subject := Tree_Id(t.a[s])
                from := rs_from_body(r, tree_list(t, t.a[arm]), t.end[arm])
                if b := Token_Id(t.b[arm]); b != 0 {
                    rs_declare(r, rs_text(b), {b, .Local}, from)
                } else if t.tag[subject] == .Ident {
                    rs_declare(r, rs_text(t.main[subject]), {t.main[subject], .Local}, from)
                }
                rs_body(r, tree_list(t, t.a[arm]))
                rs_leave(r)
            case .Arm_Value:
                rs_block(r, tree_list(t, t.b[arm]))
            }
        }
    case .For_Range, .For_Each, .For_C:
        v := for_view(t, s)
        rs_enter(r, .Block, end = t.end[s])
        from := rs_from_body(r, v.body, t.end[s])
        if v.var != 0 { rs_declare_loop(r, v.var, from) }
        if v.elem != 0 { rs_declare_loop(r, v.elem, from) }
        if v.index != 0 { rs_declare_loop(r, v.index, from) }
        for tok in v.more { rs_declare_loop(r, tok, from) }
        if v.init != 0 { rs_stmt(r, v.init) }
        if v.post != 0 { rs_stmt(r, v.post) }
        rs_block(r, v.body)
        rs_leave(r)
    case .For_Cond:
        rs_block(r, tree_list(t, t.b[s]))
    case .Assign:
        // (A name written that's in sight nowhere — the checker says so — is,
        // from here on, a variable: its uses aren't reported again.)
        for tg in tree_list(t, t.a[s]) {
            if t.tag[tg] != .Ident { continue }
            name := rs_text(t.main[tg])
            if _, found, _ := rs_find(r, name, t.main[tg]); !found { rs_declare(r, name, {t.main[tg], .Local}, t.end[s]) }
        }
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
        rs_enter(r, .Block, end = t.end[value])
        outer := r.generic
        r.generic = value
        for o in tree_list(t, t.a[value]) {
            if t.tag[o] == .Generic_Param { rs_type_param(r, t.main[o]) }   // (its kind and default: tokens)
        }
        r.generic = outer
        for vr in tree_list(t, t.b[value]) {
            if body := Tree_Id(t.b[vr]); body != 0 { rs_scope_def(r, vr, body) }
        }
        if sc := r.scopes[len(r.scopes) - 1].scope; sc != nil && sc.text_hi == 0 { sc.text_lo, sc.text_hi = t.first[value], t.end[value] }
        rs_leave(r)
    }
}

// A fun's or a struct's scope: its type params, then its params' types and
// defaults (then the params, in sight), its results, its body.
@(private="file")
rs_scope_def :: proc(r: ^Resolver, def, node: Tree_Id) {
    t := r.t
    v := scope_view(t, node)
    is_struct := t.tag[node] == .Struct_Def
    scope := rs_scope_of(r, t.main[def], node)
    scope.parent = r.here
    // (Its definitions, in its record: what a name in it means is asked of
    // it — names.odin.)
    if !scope.filled {
        scope.filled = true
        rs_space_fill(r, scope, v.body)
        rs_space_variants(r, scope)
    }
    rs_enter(r, .Struct if is_struct else .Fun, scope, t.end[node])
    scope.level, scope.body_lo, scope.variant = r.scopes[len(r.scopes) - 1].id, rs_from_body(r, v.body, t.end[node]), t.tag[def] == .Variant
    outer := r.generic
    r.generic = node
    for g in v.generics { rs_type_param(r, t.main[g]) }   // (their kinds and defaults: tokens)
    // (`$T` written in a param's type, a result's: a type param.)
    for g in v.params { rs_dollars(r, params_view(t, g).type_) }
    for x in v.returns { rs_dollars(r, params_view(t, x).type_ if t.tag[x] == .Param_Group else x) }
    if is_struct { for s in v.body { if t.tag[s] == .Decl { rs_dollars(r, decl_view(t, s).type_) } } }   // (its fields' `$T`s)
    for g in v.params {
        pv := params_view(t, g)
        // (A struct's param of a type `$T` or a shape `~S`: a type its
        // instance is given — a type param, its name in sight in its methods.)
        if is_struct && pv.type_ != 0 && (t.tag[pv.type_] == .Type_Dollar || t.tag[pv.type_] == .Type_Tilde) {
            for name in pv.names { rs_type_param(r, name) }
            continue
        }
        for name in pv.names {
            rs_declare(r, rs_text(name), {name, .Param}, t.end[v.params[len(v.params) - 1]], clash = true)
        }
    }
    for x in v.returns {
        if t.tag[x] != .Param_Group { continue }
        for name in params_view(t, x).names {
            rs_declare(r, rs_text(name), {name, .Result}, rs_from_body(r, v.body, t.end[node]), clash = true)
        }
    }
    r.generic = outer
    outer_owner := r.owner
    r.owner = t.main[def]
    if v.intrinsic == 0 { rs_body(r, v.body, scope if scope.filled else nil) }
    r.owner = outer_owner
    rs_leave(r)
}

// A qualified name's parts (`a.b.c`): the first in sight, each next one a
// member. (The first's ref, by its token, too: what a variable's type has
// is the checker's — `fn v.method`.)
@(private="file")
rs_parts :: proc(r: ^Resolver, parts: []Token_Id) -> (ref: Ref, ok: bool) {
    if len(parts) == 0 { return }   // (a name half-written: only mara lsp gets past its parse error)
    miss: Rs_Miss
    ref, ok, miss = rs_find(r, rs_text(parts[0]), parts[0])
    if !ok && len(parts) > 1 && len(miss.owners) == 0 { ref, ok = rs_own_module(r, rs_text(parts[0])) }
    if ok { r.token_refs[parts[0]] = ref }
    for part in parts[1:] {
        if !ok { break }
        m, has := rs_members(r, ref)
        if !has { return {}, false }
        ref, ok = m[rs_text(part)]
    }
    return
}

// Whether the current scope declares a name already (a signature's `$T`,
// written again: the first's).
@(private="file")
rs_declared_here :: proc(r: ^Resolver, name: string) -> bool {
    return name in rs_scope_here(r).params
}

// A type param, in sight in its scope.
@(private="file")
rs_type_param :: proc(r: ^Resolver, tok: Token_Id) {
    r.type_params[tok] = true
    if r.generic != 0 {
        if r.generic not_in r.type_params_of { r.type_params_of[r.generic] = {} }
        append(&r.type_params_of[r.generic], tok)
    }
    if rs_text(tok) == "all" { r.all_named[tok] = true }
    rs_scope_here(r).params[rs_text(tok)] = {tok, .Type}
}

// The type params a type written declares (`$T`).
@(private="file")
rs_dollars :: proc(r: ^Resolver, n: Tree_Id) {
    if n == 0 { return }
    t := r.t
    #partial switch t.tag[n] {
    case .Type_Dollar:
        tok := Token_Id(t.a[n])
        if !rs_declared_here(r, rs_text(tok)) { rs_type_param(r, tok) }
    case .Type_Pointer, .Type_Paren:
        rs_dollars(r, Tree_Id(t.a[n]))
    case .Type_Slice:
        rs_dollars(r, Tree_Id(t.b[n]))
    case .Type_Partial:
        rs_dollars(r, Tree_Id(t.a[n]))   // (a size's `$N`)
        rs_dollars(r, Tree_Id(t.b[n]))
    case .Type_Array:
        rs_dollars(r, Tree_Id(tree_rec(t, t.a[n], 2)[0]))
        rs_dollars(r, Tree_Id(t.b[n]))
    case .Type_Generic, .Type_Fun:
        for a in tree_list(t, t.a[n]) { rs_dollars(r, a) }
        if t.tag[n] == .Type_Fun { for a in tree_list(t, t.b[n]) { rs_dollars(r, a) } }
    }
}

// Whether a ref names a definition a qualified name can reach into: a
// module, a type, a fun (its nested definitions).
rs_names_def :: proc(ref: Ref) -> bool {
    return ref.kind == .Module || ref.kind == .Type || ref.kind == .Fun
}

// The builtins called by name: print, crash, the casts, len, … (the checker's
// tc_builtin's).
rs_builtin_call :: proc(name: string) -> bool {
    switch name {
    case "print", "crash", "int", "uint", "print_cstr", "print_int", "print_float", "len", "cap", "slice_from_ptr", "cstring",
         "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize", "f16", "f32", "f64", "utf8", "bool":
        return true
    }
    return false
}

// The module a name refers to.
rs_ref_module :: proc(r: ^Resolver, ref: Ref) -> ^Scope {
    return r.named[ref.decl] or_else nil
}

// The program's names resolved, before it's checked: the resolver, kept for
// the checker to read (its refs, its scopes; the names in sight are gone).
resolve_program :: proc(k: ^TC) -> ^Resolver {
    r := new(Resolver)
    r.k, r.t, r.allocator = k, k.t, context.allocator
    r.refs = make([]Ref, len(k.t.tag))
    r.walking = true
    rs_program(r)
    r.walking = false
    names_fill(r)
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
        variable := got.kind == .Local || got.kind == .Param || got.kind == .Result || got.kind == .Field || r.type_params[got.decl]
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
