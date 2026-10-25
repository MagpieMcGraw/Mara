package mara

import "base:runtime"
import "core:slice"

// The syntax tree, flat (design/flat_tree.md): every file's nodes in one table
// for the build, a node's id its index, each node the same shape — its tag,
// its report point, its extent, two fields — and lists and records of more
// fields in one side array. What a field holds is its tag's shape
// (tree_shapes), so what walks every node walks them all alike.
//
// The tree is the text as written: nothing is lowered, names and literals
// are their tokens (token_text), and a node's subtree is a contiguous range of
// ids (nodes are appended as they are parsed, children before their parent).

// A node's id: its index in the table. 0 is no node's: an absent child.
Tree_Id :: distinct u32

Tree :: struct {
    tag:   [dynamic]Tree_Tag,
    main:  [dynamic]Token_Id,   // the report point: where a diagnostic about it lands
    first: [dynamic]Token_Id,   // the extent: its first token ...
    end:   [dynamic]Token_Id,   // ... and one past its last
    a, b:  [dynamic]u32,
    extra: [dynamic]u32,        // lists (a count, then the items) and records
    files: [dynamic]Tree_Id,    // each file's root
    parent: [dynamic]Tree_Id,   // what each node is a child of (0: a file's root) — tree_parents
}

build_tree: Tree

// Each form as written. (`a` and `b`: what the shape says — a child, a list, a
// token, a token list or a record of those.)
Tree_Tag :: enum u8 {
    None,
    File,           // a: list — its statements

    // --- statements ---
    Module,         // a: tokens — the name's parts (`mara.math`; `1M` is two)
    Expr_Stmt,      // a: the expression
    Define,         // `x :: v`, `x : T : v`: main: the name; a: the type; b: the value
    Decl,           // `x := v`, `x : T = v`, `x : T`, `a, b := f()`: a: list — the
                    // targets (a name is an Ident); b: rec {type, values: list}
    Assign,         // `x = v`, `a.b, c = d, e`: a: list — the targets; b: list — the values
    Compound,       // `x op= v`: a: the target; b: rec {operator token, value}
    Return,         // a: list — the values
    Break,
    Continue,
    Defer,          // `defer`, `defer?`: main: the keyword (tree_defer_on_failure);
                    // a: list — the body
    With,           // `with &a {…}`: a: the arena (a pointer to one); b: list — the
                    // body, run on it
    Allocator,      // `#allocator Arena_Basic(16 * MB)` (a DLL's: `#allocator
                    // Arena_Basic`): main: the `#`; a: the arena
    If,             // `if c {…}`, `if c do s`, `#if`: a: the condition; b: rec {then:
                    // list, else: list, `#` token}; an `elif` chain is an Elif in the else list
    Elif,           // as If
    Match,          // a: the subject; b: list — the arms
    Arm_Else,       // a: list — the body
    Arm_Dot,        // `.V`: main: the variant; a: list — the body
    Arm_Variant,    // `V`, `V binding`: main: the variant; a: list — the body; b: the binding
    Arm_Value,      // a: the value; b: list — the body
    For_Range,      // `for i [: T] in lo..hi`: a: rec {var, type, lo, hi, body: list}; b: its `..` or `..<`
    For_Each,       // `for e[, i, …] [: T] in c`: a: rec {elem, the names after it: tokens, type, collection, body: list}
    For_C,          // `for init; cond; post`: a: rec {init, cond, post, body: list}
    For_Cond,       // `for cond`: a: the condition; b: list — the body
    Overload,       // `overload + name`: a: the operator; b: the dispatch's name
    Foreign,        // `foreign static_lib "l" [prefix p] {…}`: a: rec {static_lib, library,
                    // prefix, prefix's name, funs: list}
    Foreign_Fun,    // main: `fun`; a: rec {name, params: list, returns: list}
    Expose,         // `#expose` before a definition: main: `#`; a: the statement
    Using,          // `using` before a declaration: main: `using`; a: the statement

    // --- definitions: a Define's value ---
    Fun_Def,        // main: `fun`; a: rec {generics: list, params: list, returns: list,
                    // body: list, intrinsic}
    Struct_Def,     // main: `struct`/`class`; a: as Fun_Def's; b: `#packed`'s `#`
    Intrinsic_Body, // `{ @llvm.a.b }`: main: `@`; a: tokens — the name's parts
    Param_Group,    // `a, b: T = x, y`, `a := x`: main: the first name; a: tokens — the
                    // names; b: rec {type (none: `:=`), values: list}
    Generic_Param,  // `$T: type`, `$N: int = 256`: main: the name; a: the kind; b: the default
    Union_Def,      // main: `union`; a: list — the header's options; b: list — the variants
    Union_Tag,      // `tag u32`: main: `tag`; a: the type keyword
    Union_Pad,      // `pad T`: main: `pad`; a: the type
    Union_Size,     // `size N`: main: `size`; a: the number
    Variant,        // main: the name; a: its tag's value; b: its body, a Struct_Def (0: none)
    Error_Def,      // main: `error`; a: tokens — the variants
    Dispatch_Def,   // main: `dispatch`; a: tokens — the functions
    Distinct_Def,   // `T`, `distinct T`: main: the type's first token, or `distinct`; a: the type
    Alias_Def,      // `alias T`: main: `alias`; a: the type

    // --- types ---
    Type_Name,      // `T`, `pkg.T`, `A.B.C`: a: tokens — the parts
    Type_Keyword,   // `i64`, `bool`, …: main: the keyword
    Type_Dollar,    // `$T`: main: `$`; a: the name
    Type_Tilde,     // `~T`: main: `~`; a: the name
    Type_Pointer,   // `^T`: main: `^`; a: the element
    Type_Slice,     // `[]T`, `[:N]T`: main: `[`; a: the capacity; b: the element
    Type_Partial,   // `[N]T`, a list (`[Kind]T`, Kind an enum: an array): main: `[`; a: the size; b: the element
    Type_Array,     // `[N!]T`, `[N I]T`: main: `[`; a: rec {size, index type}; b: the element
    Type_Generic,   // `Name(args)`: main: the name; a: list — the arguments (types or values)
    Type_Fun,       // `fun(T) -> R`, `fn(T -> R)`: a: list — the params; b: list — the returns
    Type_Of,        // `fn name`, `fn pkg.name`: main: `fn`; a: tokens — the name's parts
    Type_Paren,     // `(T)`: a: the type

    // --- expressions ---
    Number,
    String,
    Char,
    True,
    False,
    Ident,
    Dot_Ident,      // `.Variant`: main: `.`; a: the name

    Unary,          // `-x`, `-%x`, `not x`, `~x`, `&x`: main: the operator; a: the operand
    Deref,          // `x^`: main: `^` (an assignment target's: its first token); a: the
                    // operand; b: the `^`
    Try,            // `x?`: main: `?`; a: the operand
    Binary,         // main: the operator; a, b: the operands
    In_Range,       // `x in lo..hi`, `x not in lo..hi`: main: `in` / `not`; a: the value;
                    // b: rec {lo, hi, its `..` or `..<`} — hi none: `x in xs`, among xs's items
    Call,           // `f(args)`, `i32(x)`: main: the callee; a: list — the args;
                    // b: an override literal (`Foo() {x = 1}`)
    Method_Call,    // `x.f(args)`: main: `.`; a: rec {receiver, name, args: list, overrides}
    Field,          // `x.f`: main: `.`; a: the operand; b: the field's name
    Index,          // `x[i]`: main: `[`; a: the operand; b: the index
    Slice,          // `x[lo:hi]`: main: `[`; a: the operand; b: rec {lo, hi}
    Big_Endian,     // `#big_endian x[i]`: main: `#`; a: the read
    Literal,        // `{…}`, `Name{…}`, `[N!]T{…}`: main: `{` (a typed array's: its `[`);
                    // a: its type; b: list — its entries
    Named_Entry,    // `name = v` in a literal: main: the name; a: the value
    Broadcast,      // `all v`: main: `all`; a: the value
    Array,          // `[a, b]`: main: `[`; a: list — the elements
    If_Expr,        // `if c do a else b`: main: `if`; a: the condition; b: rec {then, else}
    Paren,          // `(e)`: main: `(`; a: the expression
    Size_Of,        // main: `size_of`; a: the type
    Assert,         // main: `assert`; a: the condition
    Take,           // `let(T, s)`, `slice([:N]T, s)`, `slice(s)`: main: the keyword;
                    // a: the type; b: the storage
    Self,           // `#self`: main: `#`
    Hash_Name,      // `#caller_name`, `#web`, …: main: `#`; a: the name
    Import,         // `use a.b`, `include a.b`: main: the keyword; a: tokens — the path
}

// What one of a node's fields holds.
Tree_Field :: enum u8 { None, Node, List, Token, Tokens, Rec }

// A tag's shape: what `a` and `b` hold, and — for the one that is a record —
// what each of its fields holds.
Tree_Shape :: struct {
    a, b: Tree_Field,
    rec:  [5]Tree_Field,   // (its fields up to the first .None)
}


tree_shapes := [Tree_Tag]Tree_Shape{
    .None           = {},
    .File           = {a = .List},
    .Module         = {a = .Tokens},
    .Expr_Stmt      = {a = .Node},
    .Define         = {a = .Node, b = .Node},
    .Decl           = {a = .List, b = .Rec, rec = {0 = .Node, 1 = .List}},
    .Assign         = {a = .List, b = .List},
    .Compound       = {a = .Node, b = .Rec, rec = {0 = .Token, 1 = .Node}},
    .Return         = {a = .List},
    .Break          = {},
    .Continue       = {},
    .Defer          = {a = .List},
    .With           = {a = .Node, b = .List},
    .Allocator      = {a = .Node},
    .If             = {a = .Node, b = .Rec, rec = {0 = .List, 1 = .List, 2 = .Token}},
    .Elif           = {a = .Node, b = .Rec, rec = {0 = .List, 1 = .List, 2 = .Token}},
    .Match          = {a = .Node, b = .List},
    .Arm_Else       = {a = .List},
    .Arm_Dot        = {a = .List},
    .Arm_Variant    = {a = .List, b = .Token},
    .Arm_Value      = {a = .Node, b = .List},
    .For_Range      = {a = .Rec, b = .Token, rec = {0 = .Token, 1 = .Node, 2 = .Node, 3 = .Node, 4 = .List}},
    .For_Each       = {a = .Rec, b = .Token, rec = {0 = .Token, 1 = .Tokens, 2 = .Node, 3 = .Node, 4 = .List}},
    .For_C          = {a = .Rec, rec = {0 = .Node, 1 = .Node, 2 = .Node, 3 = .List}},
    .For_Cond       = {a = .Node, b = .List},
    .Overload       = {a = .Token, b = .Token},
    .Foreign        = {a = .Rec, rec = {0 = .Token, 1 = .Token, 2 = .Token, 3 = .Token, 4 = .List}},
    .Foreign_Fun    = {a = .Rec, rec = {0 = .Token, 1 = .List, 2 = .List}},
    .Expose         = {a = .Node},
    .Using          = {a = .Node},
    .Fun_Def        = {a = .Rec, rec = {0 = .List, 1 = .List, 2 = .List, 3 = .List, 4 = .Node}},
    .Struct_Def     = {a = .Rec, b = .Token, rec = {0 = .List, 1 = .List, 2 = .List, 3 = .List, 4 = .Node}},
    .Intrinsic_Body = {a = .Tokens},
    .Param_Group    = {a = .Tokens, b = .Rec, rec = {0 = .Node, 1 = .List}},
    .Generic_Param  = {a = .Token, b = .Token},
    .Union_Def      = {a = .List, b = .List},
    .Union_Tag      = {a = .Token},
    .Union_Pad      = {a = .Node},
    .Union_Size     = {a = .Token},
    .Variant        = {a = .Node, b = .Node},
    .Error_Def      = {a = .Tokens},
    .Dispatch_Def   = {a = .Tokens},
    .Distinct_Def   = {a = .Node},
    .Alias_Def      = {a = .Node},
    .Type_Name      = {a = .Tokens},
    .Type_Keyword   = {},
    .Type_Dollar    = {a = .Token},
    .Type_Tilde     = {a = .Token},
    .Type_Pointer   = {a = .Node},
    .Type_Slice     = {a = .Node, b = .Node},
    .Type_Partial   = {a = .Node, b = .Node},
    .Type_Array     = {a = .Rec, b = .Node, rec = {0 = .Node, 1 = .Node, 2 = .Token}},
    .Type_Generic   = {a = .List},
    .Type_Fun       = {a = .List, b = .List},
    .Type_Of        = {a = .Tokens},
    .Type_Paren     = {a = .Node},
    .Number         = {},
    .String         = {},
    .Char           = {},
    .True           = {},
    .False          = {},
    .Ident          = {},
    .Dot_Ident      = {a = .Token},

    .Unary          = {a = .Node},
    .Deref          = {a = .Node, b = .Token},
    .Try            = {a = .Node},
    .Binary         = {a = .Node, b = .Node},
    .In_Range       = {a = .Node, b = .Rec, rec = {0 = .Node, 1 = .Node, 2 = .Token}},
    .Call           = {a = .List, b = .Node},
    .Method_Call    = {a = .Rec, rec = {0 = .Node, 1 = .Token, 2 = .List, 3 = .Node}},
    .Field          = {a = .Node, b = .Token},
    .Index          = {a = .Node, b = .Node},
    .Slice          = {a = .Node, b = .Rec, rec = {0 = .Node, 1 = .Node}},
    .Big_Endian     = {a = .Node},
    .Literal        = {a = .Node, b = .List},
    .Named_Entry    = {a = .Node},
    .Broadcast      = {a = .Node},
    .Array          = {a = .List},
    .If_Expr        = {a = .Node, b = .Rec, rec = {0 = .Node, 1 = .Node}},
    .Paren          = {a = .Node},
    .Size_Of        = {a = .Node},
    .Assert         = {a = .Node},
    .Take           = {a = .Node, b = .Node},
    .Self           = {},
    .Hash_Name      = {a = .Token},
    .Import         = {a = .Tokens},
}

// --- building -------------------------------------------------------------

// The table's first node and the side array's first word are no node's and
// the empty list's.
tree_init :: proc(t: ^Tree) {
    if len(t.tag) > 0 { return }
    // (Its columns grow on the heap, which gives back what they outgrow — a
    // build's arena keeps every size they pass. tree_free lets them go.)
    h := runtime.heap_allocator()
    t.tag = make([dynamic]Tree_Tag, 0, 1 << 16, h)
    t.main, t.first, t.end = make([dynamic]Token_Id, 0, 1 << 16, h), make([dynamic]Token_Id, 0, 1 << 16, h), make([dynamic]Token_Id, 0, 1 << 16, h)
    t.a, t.b, t.extra = make([dynamic]u32, 0, 1 << 16, h), make([dynamic]u32, 0, 1 << 16, h), make([dynamic]u32, 0, 1 << 16, h)
    append(&t.tag, Tree_Tag.None)
    append(&t.main, 0); append(&t.first, 0); append(&t.end, 0)
    append(&t.a, 0); append(&t.b, 0)
    append(&t.extra, 0)
}

// Room in the columns for what the tokens will make — a node for about
// two in three tokens, a side-array word for about four in five — so they
// aren't copied as they grow (a long build's would be, a few times over).
tree_reserve :: proc(t: ^Tree, tokens: int) {
    tree_init(t)
    nodes, extra := tokens * 3 / 4, tokens * 7 / 8
    reserve(&t.tag, nodes); reserve(&t.main, nodes); reserve(&t.first, nodes)
    reserve(&t.end, nodes); reserve(&t.a, nodes); reserve(&t.b, nodes)
    reserve(&t.extra, extra)
}

// The tree's columns let go of (a check of serve's, before the next).
tree_free :: proc(t: ^Tree) {
    delete(t.tag); delete(t.main); delete(t.first); delete(t.end)
    delete(t.a); delete(t.b); delete(t.extra)
    t^ = {}
}

tree_add :: proc(t: ^Tree, tag: Tree_Tag, main: Token_Id, a: u32 = 0, b: u32 = 0) -> Tree_Id {
    id := Tree_Id(len(t.tag))
    push(&t.tag, tag)
    push(&t.main, main)
    push(&t.first, main)
    push(&t.end, main + 1 if main != 0 else 0)
    push(&t.a, a)
    push(&t.b, b)
    return id
}

// An element added at a column's end, as `append` adds one but inline —
// a column that grows by one a node: the tree's, the tokens. (It doubles,
// as append does.)
push :: #force_inline proc(col: ^[dynamic]$T, v: T) {
    raw := (^runtime.Raw_Dynamic_Array)(col)
    if raw.len == raw.cap { reserve(col, max(64, 2 * raw.cap)) }
    ([^]T)(raw.data)[raw.len] = v
    raw.len += 1
}

// A list in the side array: its count, then its items; 0 for none.
tree_list_add :: proc(t: ^Tree, items: []Tree_Id) -> u32 {
    if len(items) == 0 { return 0 }
    at := u32(len(t.extra))
    push(&t.extra, u32(len(items)))
    append(&t.extra, ..transmute([]u32)items)
    return at
}

tree_tokens_add :: proc(t: ^Tree, items: []Token_Id) -> u32 {
    if len(items) == 0 { return 0 }
    at := u32(len(t.extra))
    push(&t.extra, u32(len(items)))
    append(&t.extra, ..transmute([]u32)items)
    return at
}

// A record in the side array: its fields, in its shape's order.
tree_rec_add :: proc(t: ^Tree, fields: ..u32) -> u32 {
    at := u32(len(t.extra))
    append(&t.extra, ..fields)
    return at
}

// --- reading --------------------------------------------------------------

tree_list :: proc(t: ^Tree, at: u32) -> []Tree_Id {
    if at == 0 { return nil }
    n := t.extra[at]
    return transmute([]Tree_Id)t.extra[at + 1:][:n]
}

tree_token_list :: proc(t: ^Tree, at: u32) -> []Token_Id {
    if at == 0 { return nil }
    n := t.extra[at]
    return transmute([]Token_Id)t.extra[at + 1:][:n]
}

tree_rec :: proc(t: ^Tree, at: u32, n: int) -> []u32 {
    return t.extra[at:][:n]
}

tree_span :: proc(t: ^Tree, n: Tree_Id) -> Span {
    return Span{at = t.main[n], tok = t.first[n], end = t.end[n]}
}

// A node's children, in order: its node fields' and its lists' items.
tree_children :: proc(t: ^Tree, n: Tree_Id, out: ^[dynamic]Tree_Id) {
    each :: proc(t: ^Tree, f: Tree_Field, v: u32, out: ^[dynamic]Tree_Id) {
        #partial switch f {
        case .Node: if v != 0 { append(out, Tree_Id(v)) }
        case .List: for c in tree_list(t, v) { append(out, c) }
        }
    }
    shape := tree_shapes[t.tag[n]]
    for f, k in ([2]Tree_Field{shape.a, shape.b}) {
        v := t.a[n] if k == 0 else t.b[n]
        if f == .Rec {
            for rf, i in shape.rec {
                if rf == .None { break }
                each(t, rf, t.extra[v + u32(i)], out)
            }
        } else {
            each(t, f, v, out)
        }
    }
}

// Whether a defer is a `defer?`: run only when its function returns a
// failure.
tree_defer_on_failure :: proc(t: ^Tree, n: Tree_Id) -> bool {
    return build_tokens[t.main[n]].kind == .Defer_Err
}

// Each node's parent (Tree.parent), once the tree is whole: what climbing
// from a node needs — its statement (tree_stmt).
tree_parents :: proc(t: ^Tree) {
    t.parent = make([dynamic]Tree_Id, len(t.tag))
    parent, extra := t.parent[:], t.extra[:]
    // (Each field's children: written straight in, no list of them made.)
    adopt :: #force_inline proc(parent, extra: []u32, n: u32, f: Tree_Field, v: u32) {
        #partial switch f {
        case .Node: if v != 0 { parent[v] = n }
        case .List: if v != 0 { for c in extra[v + 1:][:extra[v]] { parent[c] = n } }
        }
    }
    for n in 1 ..< u32(len(t.tag)) {
        shape := &tree_shapes[t.tag[n]]
        if shape.a == .None { continue }   // (a leaf: b's none either)
        for f, k in ([2]Tree_Field{shape.a, shape.b}) {
            v := t.a[n] if k == 0 else t.b[n]
            if f != .Rec {
                adopt(transmute([]u32)parent, extra, n, f, v)
                continue
            }
            for rf, i in shape.rec {
                if rf == .None { break }
                adopt(transmute([]u32)parent, extra, n, rf, extra[v + u32(i)])
            }
        }
    }
}

// The statement a node is part of — itself, if it's one: a block's, a
// loop's header's, a definition (0: none).
tree_stmt :: proc(t: ^Tree, n: Tree_Id) -> Tree_Id {
    n := n
    for n != 0 {
        #partial switch t.tag[n] {
        case .Assign, .Compound, .Decl, .Using, .Expr_Stmt, .Return, .Break, .Continue, .Defer,
             .With, .If, .Elif, .Match, .For_Range, .For_Each, .For_C, .For_Cond, .Define, .Variant:
            return n
        }
        n = t.parent[n]
    }
    return 0
}

// What a statement does to the variables it writes.
tree_stmt_kind :: proc(t: ^Tree, s: Tree_Id) -> Stmt_Kind {
    #partial switch t.tag[s] {
    case .Using:    return tree_stmt_kind(t, Tree_Id(t.a[s]))   // (its declaration's)
    case .Expr_Stmt:
        if t.tag[t.a[s]] == .Import { return .Decl }
    case .Decl:
        // (Several names from one value: a destructure — a broadcast's, its
        // copies': tc_broadcast.)
        v := decl_view(t, s)
        if len(v.targets) > 1 && len(v.values) == 1 { return .Destructure }
        return .Decl
    case .Assign:
        targets := tree_list(t, t.a[s])
        if len(targets) > 1 && len(targets) == len(tree_list(t, t.b[s])) { return .Other }   // (its assignments')
        if len(targets) == 1 { return tree_assign_kind(t, targets[0]) }
        return .Destructure
    case .Compound:
        if t.tag[t.a[s]] != .Ident { return .Write }
        return .Assign
    case .For_Range, .For_Each, .For_C, .For_Cond: return .Loop
    case .If:    return .If
    case .Match: return .Match
    }
    return .Other
}

// An assignment's statement kind, by its target: a place's a write; `_`'s
// no assignment.
tree_assign_kind :: proc(t: ^Tree, target: Tree_Id) -> Stmt_Kind {
    if t.tag[target] != .Ident { return .Write }
    if name := token_text(build_tokens[t.main[target]]); name == "_" { return .Other }
    return .Assign
}

// The lowest node of a subtree: its nodes are [it, n] (children are made
// before their parents, each child's subtree a range of its own — the first
// made, the lowest).
tree_lo :: proc(t: ^Tree, n: Tree_Id) -> Tree_Id {
    n := n
    kids := make([dynamic]Tree_Id, context.temp_allocator)
    for {
        clear(&kids)
        tree_children(t, n, &kids)
        if len(kids) == 0 { return n }
        n = slice.min(kids[:])
    }
}

// --- views: a form's fields by name ----------------------------------------

// A fun's or a struct's.
Scope_View :: struct {
    generics, params, returns, body: []Tree_Id,
    intrinsic:                       Tree_Id,
    packed:                          Token_Id,   // a struct's `#packed`
}

scope_view :: proc(t: ^Tree, n: Tree_Id) -> Scope_View {
    r := tree_rec(t, t.a[n], 5)
    v := Scope_View{
        generics  = tree_list(t, r[0]),
        params    = tree_list(t, r[1]),
        returns   = tree_list(t, r[2]),
        body      = tree_list(t, r[3]),
        intrinsic = Tree_Id(r[4]),
    }
    if t.tag[n] == .Struct_Def { v.packed = Token_Id(t.b[n]) }
    return v
}

If_View :: struct {
    cond:       Tree_Id,
    then, else_: []Tree_Id,
    hash:       Token_Id,   // `#if`'s `#`
}

if_view :: proc(t: ^Tree, n: Tree_Id) -> If_View {
    r := tree_rec(t, t.b[n], 3)
    return {cond = Tree_Id(t.a[n]), then = tree_list(t, r[0]), else_ = tree_list(t, r[1]), hash = Token_Id(r[2])}
}

Decl_View :: struct {
    targets, values: []Tree_Id,
    type_:           Tree_Id,
}

decl_view :: proc(t: ^Tree, n: Tree_Id) -> Decl_View {
    r := tree_rec(t, t.b[n], 2)
    return {targets = tree_list(t, t.a[n]), type_ = Tree_Id(r[0]), values = tree_list(t, r[1])}
}

Params_View :: struct {
    names:  []Token_Id,
    type_:  Tree_Id,
    values: []Tree_Id,
}

params_view :: proc(t: ^Tree, n: Tree_Id) -> Params_View {
    r := tree_rec(t, t.b[n], 2)
    return {names = tree_token_list(t, t.a[n]), type_ = Tree_Id(r[0]), values = tree_list(t, r[1])}
}

For_View :: struct {
    var, elem, index:       Token_Id,
    by_ref:                 Token_Id,     // `for &item in xs`: its `&` (b); 0 for a loop over copies
    dots:                   Token_Id,     // a range's `..` (its end included) or `..<` (b)
    more:                   []Token_Id,   // a for-each's names after its index (a loop over a call's values)
    type_:                  Tree_Id,
    lo, hi, collection:     Tree_Id,
    init, cond, post:       Tree_Id,
    body:                   []Tree_Id,
}

for_view :: proc(t: ^Tree, n: Tree_Id) -> For_View {
    #partial switch t.tag[n] {
    case .For_Range:
        r := tree_rec(t, t.a[n], 5)
        return {var = Token_Id(r[0]), type_ = Tree_Id(r[1]), lo = Tree_Id(r[2]), hi = Tree_Id(r[3]), body = tree_list(t, r[4]), dots = Token_Id(t.b[n])}
    case .For_Each:
        r := tree_rec(t, t.a[n], 5)
        names := tree_token_list(t, r[1])
        v := For_View{elem = Token_Id(r[0]), type_ = Tree_Id(r[2]), collection = Tree_Id(r[3]), body = tree_list(t, r[4]), by_ref = Token_Id(t.b[n])}
        if len(names) > 0 { v.index, v.more = names[0], names[1:] }
        return v
    case .For_C:
        r := tree_rec(t, t.a[n], 4)
        return {init = Tree_Id(r[0]), cond = Tree_Id(r[1]), post = Tree_Id(r[2]), body = tree_list(t, r[3])}
    case .For_Cond:
        return {cond = Tree_Id(t.a[n]), body = tree_list(t, t.b[n])}
    }
    return {}
}

Method_View :: struct {
    receiver:  Tree_Id,
    name:      Token_Id,
    args:      []Tree_Id,
    overrides: Tree_Id,
}

method_view :: proc(t: ^Tree, n: Tree_Id) -> Method_View {
    r := tree_rec(t, t.a[n], 4)
    return {receiver = Tree_Id(r[0]), name = Token_Id(r[1]), args = tree_list(t, r[2]), overrides = Tree_Id(r[3])}
}

Foreign_View :: struct {
    library, prefix: Token_Id,   // the library's string, the prefix's name (0: none)
    funs:            []Tree_Id,
}

foreign_view :: proc(t: ^Tree, n: Tree_Id) -> Foreign_View {
    r := tree_rec(t, t.a[n], 5)
    return {library = Token_Id(r[1]), prefix = Token_Id(r[3]), funs = tree_list(t, r[4])}
}

Foreign_Fun_View :: struct {
    name:            Token_Id,
    params, returns: []Tree_Id,
}

foreign_fun_view :: proc(t: ^Tree, n: Tree_Id) -> Foreign_Fun_View {
    r := tree_rec(t, t.a[n], 3)
    return {name = Token_Id(r[0]), params = tree_list(t, r[1]), returns = tree_list(t, r[2])}
}

// A two-field record's (a slice's bounds, an array type's size and index
// type, an if expression's branches, a range's ends).
// Whether an In_Range's or a For_Range's end is in it: written `..`, not
// `..<`.
range_includes_end :: proc(t: ^Tree, n: Tree_Id) -> bool {
    dots := Token_Id(t.b[n]) if t.tag[n] == .For_Range else Token_Id(tree_rec(t, t.b[n], 3)[2])
    return dots != 0 && build_tokens[dots].kind == .Dot_Dot
}

tree_pair :: proc(t: ^Tree, n: Tree_Id) -> (Tree_Id, Tree_Id) {
    r := tree_rec(t, t.b[n], 2)
    return Tree_Id(r[0]), Tree_Id(r[1])
}

