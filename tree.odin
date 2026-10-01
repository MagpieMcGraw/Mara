package mara

import "core:fmt"
import "core:os"
import "core:strings"

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
    Defer,          // a: list — the body
    If,             // `if c {…}`, `if c do s`, `#if`: a: the condition; b: rec {then:
                    // list, else: list, `#` token}; an `elif` chain is an Elif in the else list
    Elif,           // as If
    Match,          // a: the subject; b: list — the arms
    Arm_Else,       // a: list — the body
    Arm_Dot,        // `.V`: main: the variant; a: list — the body
    Arm_Variant,    // `V`, `V binding`: main: the variant; a: list — the body; b: the binding
    Arm_Value,      // a: the value; b: list — the body
    For_Range,      // `for i [: T] in lo..hi`: a: rec {var, type, lo, hi, body: list}
    For_Each,       // `for e[, i] [: T] in c`: a: rec {elem, index, type, collection, body: list}
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
    Variant,        // main: the name; a: its tag's value; b: list — its fields
    Field_Def,      // `name: T = v` in a variant: main: the name; a: the type; b: the default
    Error_Def,      // main: `error`; a: tokens — the variants
    Dispatch_Def,   // main: `dispatch`; a: tokens — the functions
    Distinct_Def,   // main: `distinct`; a: the type
    Alias_Def,      // `type(T)`, `type T`: main: `type`; a: the type

    // --- types ---
    Type_Name,      // `T`, `pkg.T`, `A.B.C`: a: tokens — the parts
    Type_Keyword,   // `i64`, `bool`, …: main: the keyword
    Type_Dollar,    // `$T`: main: `$`; a: the name
    Type_Tilde,     // `~T`: main: `~`; a: the name
    Type_Pointer,   // `^T`: main: `^`; a: the element
    Type_Slice,     // `[]T`, `[:N]T`: main: `[`; a: the capacity; b: the element
    Type_Partial,   // `[..N]T`: main: `[`; a: the size; b: the element
    Type_Array,     // `[N]T`, `[N I]T`: main: `[`; a: rec {size, index type}; b: the element
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
    Type_Value,     // a type keyword as a value (`Array(byte, 64)`): main: the keyword
    Unary,          // `-x`, `-%x`, `not x`, `~x`, `&x`: main: the operator; a: the operand
    Deref,          // `x^`: main: `^` (an assignment target's: its first token); a: the
                    // operand; b: the `^`
    Try,            // `x?`: main: `?`; a: the operand
    Binary,         // main: the operator; a, b: the operands
    In_Range,       // `x in lo..hi`, `x not in lo..hi`: main: `in` / `not`; a: the value;
                    // b: rec {lo, hi}
    Call,           // `f(args)`, `i32(x)`: main: the callee; a: list — the args;
                    // b: an override literal (`Foo() {x = 1}`)
    Method_Call,    // `x.f(args)`: main: `.`; a: rec {receiver, name, args: list, overrides}
    Field,          // `x.f`: main: `.`; a: the operand; b: the field's name
    Index,          // `x[i]`: main: `[`; a: the operand; b: the index
    Slice,          // `x[lo:hi]`: main: `[`; a: the operand; b: rec {lo, hi}
    Big_Endian,     // `#big_endian x[i]`: main: `#`; a: the read
    Literal,        // `{…}`, `Name{…}`, `[N]T{…}`: main: `{` (a typed array's: its `[`);
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
    Import,         // `use a.b`, `include a.b`, `sealed use a.b`: main: the keyword;
                    // a: tokens — the path; b: `sealed`
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
    .If             = {a = .Node, b = .Rec, rec = {0 = .List, 1 = .List, 2 = .Token}},
    .Elif           = {a = .Node, b = .Rec, rec = {0 = .List, 1 = .List, 2 = .Token}},
    .Match          = {a = .Node, b = .List},
    .Arm_Else       = {a = .List},
    .Arm_Dot        = {a = .List},
    .Arm_Variant    = {a = .List, b = .Token},
    .Arm_Value      = {a = .Node, b = .List},
    .For_Range      = {a = .Rec, rec = {0 = .Token, 1 = .Node, 2 = .Node, 3 = .Node, 4 = .List}},
    .For_Each       = {a = .Rec, rec = {0 = .Token, 1 = .Token, 2 = .Node, 3 = .Node, 4 = .List}},
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
    .Variant        = {a = .Node, b = .List},
    .Field_Def      = {a = .Node, b = .Node},
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
    .Type_Array     = {a = .Rec, b = .Node, rec = {0 = .Node, 1 = .Node}},
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
    .Type_Value     = {},
    .Unary          = {a = .Node},
    .Deref          = {a = .Node, b = .Token},
    .Try            = {a = .Node},
    .Binary         = {a = .Node, b = .Node},
    .In_Range       = {a = .Node, b = .Rec, rec = {0 = .Node, 1 = .Node}},
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
    .Import         = {a = .Tokens, b = .Token},
}

// --- building -------------------------------------------------------------

// The table's first node and the side array's first word are no node's and
// the empty list's.
tree_init :: proc(t: ^Tree) {
    if len(t.tag) > 0 { return }
    append(&t.tag, Tree_Tag.None)
    append(&t.main, 0); append(&t.first, 0); append(&t.end, 0)
    append(&t.a, 0); append(&t.b, 0)
    append(&t.extra, 0)
}

tree_add :: proc(t: ^Tree, tag: Tree_Tag, main: Token_Id, a: u32 = 0, b: u32 = 0) -> Tree_Id {
    id := Tree_Id(len(t.tag))
    append(&t.tag, tag)
    append(&t.main, main)
    append(&t.first, main)
    append(&t.end, main + 1 if main != 0 else 0)
    append(&t.a, a)
    append(&t.b, b)
    return id
}

// A list in the side array: its count, then its items; 0 for none.
tree_list_add :: proc(t: ^Tree, items: []Tree_Id) -> u32 {
    if len(items) == 0 { return 0 }
    at := u32(len(t.extra))
    append(&t.extra, u32(len(items)))
    for it in items { append(&t.extra, u32(it)) }
    return at
}

tree_tokens_add :: proc(t: ^Tree, items: []Token_Id) -> u32 {
    if len(items) == 0 { return 0 }
    at := u32(len(t.extra))
    append(&t.extra, u32(len(items)))
    for it in items { append(&t.extra, u32(it)) }
    return at
}

// A record in the side array: its fields, in its shape's order.
tree_rec_add :: proc(t: ^Tree, fields: ..u32) -> u32 {
    at := u32(len(t.extra))
    for f in fields { append(&t.extra, f) }
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

// The tokens a node records: its report point, its token fields, its token
// lists' items.
tree_node_tokens :: proc(t: ^Tree, n: Tree_Id, out: ^[dynamic]Token_Id) {
    each :: proc(t: ^Tree, f: Tree_Field, v: u32, out: ^[dynamic]Token_Id) {
        #partial switch f {
        case .Token:  if v != 0 { append(out, Token_Id(v)) }
        case .Tokens: for c in tree_token_list(t, v) { append(out, c) }
        }
    }
    if t.main[n] != 0 { append(out, t.main[n]) }
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
    type_:                  Tree_Id,
    lo, hi, collection:     Tree_Id,
    init, cond, post:       Tree_Id,
    body:                   []Tree_Id,
}

for_view :: proc(t: ^Tree, n: Tree_Id) -> For_View {
    #partial switch t.tag[n] {
    case .For_Range:
        r := tree_rec(t, t.a[n], 5)
        return {var = Token_Id(r[0]), type_ = Tree_Id(r[1]), lo = Tree_Id(r[2]), hi = Tree_Id(r[3]), body = tree_list(t, r[4])}
    case .For_Each:
        r := tree_rec(t, t.a[n], 5)
        return {elem = Token_Id(r[0]), index = Token_Id(r[1]), type_ = Tree_Id(r[2]), collection = Tree_Id(r[3]), body = tree_list(t, r[4])}
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
tree_pair :: proc(t: ^Tree, n: Tree_Id) -> (Tree_Id, Tree_Id) {
    r := tree_rec(t, t.b[n], 2)
    return Tree_Id(r[0]), Tree_Id(r[1])
}

// --- the dump and the check ----------------------------------------------

// MARA_TREE=dump: each file's tree, one node a line, indented by depth.
// MARA_TREE=check: that the tree loses nothing (tree_check).
tree_mode :: proc() -> string {
    return os.get_env("MARA_TREE", context.temp_allocator)
}

tree_dump :: proc(t: ^Tree) {
    line :: proc(t: ^Tree, sb: ^strings.Builder, n: Tree_Id, depth: int) {
        for _ in 0 ..< depth { strings.write_string(sb, "  ") }
        fmt.sbprintf(sb, "%v", t.tag[n])
        toks: [dynamic]Token_Id
        defer delete(toks)
        tree_node_tokens(t, n, &toks)
        for tk in toks { fmt.sbprintf(sb, " '%s'", token_text(build_tokens[tk])) }
        sp := tree_span(t, n)
        if sp.at != 0 { fmt.sbprintf(sb, "  %d:%d", span_line(sp), span_col(sp)) }
        strings.write_byte(sb, '\n')
        kids: [dynamic]Tree_Id
        defer delete(kids)
        tree_children(t, n, &kids)
        for k in kids { line(t, sb, k, depth + 1) }
    }
    sb := strings.builder_make()
    for f in t.files {
        fmt.sbprintf(&sb, "file %s\n", span_file(Span{at = t.first[f]}))
        line(t, &sb, f, 1)
    }
    fmt.print(strings.to_string(sb))
}

