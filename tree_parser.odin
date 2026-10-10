package mara


// The flat tree's parser (tree.odin): the grammar, recorded as written — no
// lowering, no desugaring, names and literals their tokens.
//
// Nodes are appended children first; a production that backtracks drops what
// it appended (tp_mark / tp_reset).

Tree_Parser :: struct {
    t:             ^Tree,
    tokens:        []Token,   // the build's, to the end of this file (positions are token ids)
    first:         int,       // the file's first token
    pos:           int,
    file:          string,
    errors:        int,
    no_struct_lit: bool,      // a `{` after an expression opens a body (a condition's)
}

// Parse a file into the build's tree: its root, and how many errors.
tree_parse_file :: proc(f: ^Source_File) -> (root: Tree_Id, errors: int) {
    t := &build_tree
    tree_init(t)
    p := Tree_Parser{t = t, tokens = build_tokens[:f.end_token], first = int(f.first_token), pos = int(f.first_token), file = f.path}
    stmts := make([dynamic]Tree_Id, context.temp_allocator)
    tp_skip_newlines(&p)
    for tp_kind(&p) != .EOF {
        errs := p.errors
        append(&stmts, tp_stmt(&p))
        if p.errors > errs { tp_recover(&p) }
        tp_skip_separator(&p)
    }
    root = tree_add(t, .File, 0, tree_list_add(t, stmts[:]))
    t.first[root], t.end[root] = f.first_token, f.end_token
    append(&t.files, root)
    return root, p.errors
}

// --- tokens ---------------------------------------------------------------

tp_kind :: proc(p: ^Tree_Parser) -> Token_Kind {
    return p.tokens[p.pos].kind if p.pos < len(p.tokens) else .EOF
}

tp_peek :: proc(p: ^Tree_Parser, offset := 1) -> Token_Kind {
    i := p.pos + offset
    return p.tokens[i].kind if i < len(p.tokens) else .EOF
}

// The token at an offset (past the end: the file's EOF).
tp_tok :: proc(p: ^Tree_Parser, offset := 0) -> Token {
    i := p.pos + offset
    return p.tokens[i] if i < len(p.tokens) else p.tokens[len(p.tokens) - 1]
}

tp_text :: proc(p: ^Tree_Parser, offset := 0) -> string {
    return token_text(tp_tok(p, offset))
}

tp_here :: proc(p: ^Tree_Parser) -> Token_Id {
    return Token_Id(p.pos) if p.pos < len(p.tokens) else Token_Id(len(p.tokens) - 1)
}

tp_advance :: proc(p: ^Tree_Parser) -> Token_Id {
    id := tp_here(p)
    if p.pos < len(p.tokens) { p.pos += 1 }
    return id
}

tp_expect :: proc(p: ^Tree_Parser, kind: Token_Kind) -> Token_Id {
    tok := tp_tok(p)
    if tok.kind != kind { tp_error(p, tp_here(p), PARSE_EXPECTED_TOKEN, kind, tok.kind, token_text(tok)) }
    return tp_advance(p)
}

// A number that doesn't parse: why — past u64, or not a number.
tp_number :: proc(p: ^Tree_Parser, tok: Token_Id) {
    text := token_text(build_tokens[tok])
    _, _, err := parse_number_text(text)
    switch err {
    case .None:
    case .Invalid:      tp_error(p, tok, PARSE_INVALID_NUMBER, text)
    case .Hex_Overflow: tp_error(p, tok, PARSE_HEX_OVERFLOWS_U64, text)
    case .Dec_Overflow: tp_error(p, tok, PARSE_DECIMAL_OVERFLOWS_U64, text)
    case .Bin_Overflow: tp_error(p, tok, PARSE_BINARY_OVERFLOWS_U64, text)
    }
}

// A parse error, reported.
tp_error :: proc(p: ^Tree_Parser, at: Token_Id, msg: string, args: ..any) {
    p.errors += 1
    tok := build_tokens[at]
    emit_diagnostic(.Parse_Error, format_location(p.file, token_line(tok), token_col(tok)), msg, ..args)
}

tp_skip_newlines :: proc(p: ^Tree_Parser) {
    for tp_kind(p) == .Newline { p.pos += 1 }
}

tp_skip_separator :: proc(p: ^Tree_Parser, commas := false) {
    for tp_kind(p) == .Newline || tp_kind(p) == .Semicolon || commas && tp_kind(p) == .Comma { p.pos += 1 }
}

tp_recover :: proc(p: ^Tree_Parser) {
    for {
        k := tp_kind(p)
        if k == .Newline || k == .Semicolon || k == .Right_Brace || k == .EOF { return }
        p.pos += 1
    }
}

// --- nodes ----------------------------------------------------------------

// A node over the tokens from `first` to here.
tp_node :: proc(p: ^Tree_Parser, tag: Tree_Tag, main: Token_Id, first: int, a: u32 = 0, b: u32 = 0) -> Tree_Id {
    n := tree_add(p.t, tag, main, a, b)
    p.t.first[n] = Token_Id(first)
    p.t.end[n] = Token_Id(p.pos)
    return n
}

// A one-token node: the token just consumed.
tp_leaf :: proc(p: ^Tree_Parser, tag: Tree_Tag, tok: Token_Id) -> Tree_Id {
    return tp_node(p, tag, tok, int(tok))
}

tp_list :: proc(p: ^Tree_Parser, items: [dynamic]Tree_Id) -> u32 {
    return tree_list_add(p.t, items[:])
}

tp_tokens :: proc(p: ^Tree_Parser, items: [dynamic]Token_Id) -> u32 {
    return tree_tokens_add(p.t, items[:])
}

tp_items :: proc() -> [dynamic]Tree_Id {
    return make([dynamic]Tree_Id, context.temp_allocator)
}

tp_token_items :: proc() -> [dynamic]Token_Id {
    return make([dynamic]Token_Id, context.temp_allocator)
}

// Where the tree is, to drop what a production that backtracks appended.
Tp_Mark :: struct {
    pos, nodes, extra: int,
    errors:            int,
}

tp_mark :: proc(p: ^Tree_Parser) -> Tp_Mark {
    return {p.pos, len(p.t.tag), len(p.t.extra), p.errors}
}

tp_reset :: proc(p: ^Tree_Parser, m: Tp_Mark) {
    p.pos = m.pos
    t := p.t
    resize(&t.tag, m.nodes); resize(&t.main, m.nodes); resize(&t.first, m.nodes)
    resize(&t.end, m.nodes); resize(&t.a, m.nodes); resize(&t.b, m.nodes)
    resize(&t.extra, m.extra)
}

// --- statements -------------------------------------------------------------

tp_stmt :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    #partial switch tp_kind(p) {
    case .Module:   return tp_module(p)
    case .Use, .Include:
        e := tp_primary(p)
        return tp_node(p, .Expr_Stmt, Token_Id(start), start, u32(e))
    case .Foreign:  return tp_foreign(p)
    case .Return:   return tp_return(p)
    case .Break:    return tp_leaf(p, .Break, tp_advance(p))
    case .Continue: return tp_leaf(p, .Continue, tp_advance(p))
    case .Defer:    return tp_defer(p)
    case .If:       return tp_if(p, 0)
    case .Hash:
        if tp_peek(p) == .If {
            hash := tp_advance(p)
            return tp_if(p, hash)
        }
        if tp_peek(p) == .Identifier && tp_text(p, 1) == "expose" {
            hash := tp_advance(p)
            tp_advance(p)   // `expose`
            tp_skip_newlines(p)
            inner := tp_stmt(p)
            if !tp_is_fun_define(p, inner) { tp_error(p, hash, PARSE_EXPOSE_NEEDS_FUN_DECL) }
            return tp_node(p, .Expose, hash, start, u32(inner))
        }
        if tp_peek(p) == .Identifier && tp_text(p, 1) == "packed" {
            tp_error(p, tp_here(p), PARSE_PACKED_NEEDS_STRUCT_DECL)
            tp_advance(p); tp_advance(p)
            tp_skip_newlines(p)
            return tp_stmt(p)
        }
    case .Match:    return tp_match(p)
    case .For:      return tp_for(p)
    case .Overload: return tp_overload(p)
    case .Using:
        if tp_peek(p) == .Identifier {
            m := tp_mark(p)
            using_tok := tp_advance(p)
            if inner, ok := tp_try_assign(p); ok {
                if tp_assigns_import(p, inner) { tp_error(p, tp_here(p), PARSE_USING_NOT_ALLOWED_ON_INCLUDE, "...", "...") }
                return tp_node(p, .Using, using_tok, start, u32(inner))
            }
            tp_reset(p, m)
        }
    case .Identifier:
        if s, ok := tp_try_assign(p); ok {
            if p.t.tag[s] == .Decl {
                for v in decl_view(p.t, s).values {
                    if p.t.tag[v] == .Import { tp_error(p, tp_here(p), PARSE_INCLUDE_NEEDS_COLON_COLON); break }
                }
            }
            return s
        }
    }
    if tp_kind(p) == .Identifier || tp_kind(p) == .Ampersand {
        e := tp_expr(p)
        return tp_node(p, .Expr_Stmt, Token_Id(start), start, u32(e))
    }
    tok := tp_tok(p)
    if tok.kind == .Else {
        tp_error(p, tp_here(p), PARSE_STRAY_ELSE)
    } else {
        tp_error(p, tp_here(p), PARSE_UNEXPECTED_TOKEN_STMT, tok.kind, token_text(tok))
    }
    bad := tp_advance(p)
    return tp_node(p, .Expr_Stmt, bad, start)
}

// A Define whose value is a fun.
tp_is_fun_define :: proc(p: ^Tree_Parser, s: Tree_Id) -> bool {
    return p.t.tag[s] == .Define && p.t.b[s] != 0 && p.t.tag[p.t.b[s]] == .Fun_Def
}

// A declaration or a constant whose value is an import (`using x := use a`).
tp_assigns_import :: proc(p: ^Tree_Parser, s: Tree_Id) -> bool {
    t := p.t
    #partial switch t.tag[s] {
    case .Decl:
        for v in decl_view(t, s).values { if t.tag[v] == .Import { return true } }
    case .Define:
        return t.b[s] != 0 && t.tag[t.b[s]] == .Import
    }
    return false
}

tp_module :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    parts := tp_token_items()
    if tp_kind(p) == .Number {
        append(&parts, tp_advance(p))
        if tp_kind(p) == .Identifier { append(&parts, tp_advance(p)) }
    } else {
        append(&parts, tp_expect(p, .Identifier))
    }
    for tp_kind(p) == .Dot {
        tp_advance(p)
        append(&parts, tp_expect(p, .Identifier))
    }
    return tp_node(p, .Module, kw, start, tp_tokens(p, parts))
}

// `{ stmt* }`: the statements' list.
tp_block :: proc(p: ^Tree_Parser, commas := false) -> u32 {
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    stmts := tp_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        errs := p.errors
        append(&stmts, tp_stmt(p))
        if p.errors > errs { tp_recover(p) }
        tp_skip_separator(p, commas)
    }
    tp_expect(p, .Right_Brace)
    return tp_list(p, stmts)
}

tp_is_intrinsic_part :: proc(k: Token_Kind) -> bool {
    #partial switch k {
    case .Identifier, .Int, .F64, .F32, .I8, .I16, .I32, .I64,
         .U8, .U16, .U32, .U64, .Utf8, .Byte, .Bool_Type, .Number:
        return true
    }
    return false
}

// A scope's body: its statements, or — `{ @llvm.<name> }` — an intrinsic's.
tp_scope_body :: proc(p: ^Tree_Parser, commas := false) -> (body: u32, intrinsic: Tree_Id) {
    if tp_kind(p) == .Left_Brace {
        m := tp_mark(p)
        start := p.pos
        tp_advance(p)
        tp_skip_newlines(p)
        if tp_kind(p) == .At {
            at := tp_advance(p)
            parts := tp_token_items()
            if !tp_is_intrinsic_part(tp_kind(p)) {
                tp_error(p, at, PARSE_EXPECTED_INTRINSIC_AFTER_AT, tp_text(p))
            } else {
                append(&parts, tp_advance(p))
                for tp_kind(p) == .Dot {
                    tp_advance(p)
                    if !tp_is_intrinsic_part(tp_kind(p)) {
                        tp_error(p, tp_here(p), PARSE_EXPECTED_INTRINSIC_AFTER_DOT, tp_text(p))
                        break
                    }
                    append(&parts, tp_advance(p))
                }
            }
            tp_skip_newlines(p)
            tp_expect(p, .Right_Brace)
            return 0, tp_node(p, .Intrinsic_Body, at, start, tp_tokens(p, parts))
        }
        if tp_kind(p) == .Intrinsic {
            tp_error(p, tp_here(p), PARSE_BARE_INTRINSIC_REMOVED)
            tp_advance(p)
            tp_skip_newlines(p)
            tp_expect(p, .Right_Brace)
            return 0, 0
        }
        tp_reset(p, m)
    }
    return tp_block(p, commas), 0
}

tp_return :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    values := tp_items()
    k := tp_kind(p)
    if k != .Newline && k != .Right_Brace && k != .Semicolon && k != .EOF {
        append(&values, tp_expr(p))
        for tp_kind(p) == .Comma {
            tp_advance(p)
            append(&values, tp_expr(p))
        }
    }
    return tp_node(p, .Return, kw, start, tp_list(p, values))
}

tp_defer :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    body := tp_items()
    tp_skip_newlines(p)
    if tp_kind(p) == .Left_Brace {
        tp_advance(p)
        tp_skip_newlines(p)
        for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
            append(&body, tp_stmt(p))
            tp_skip_separator(p)
        }
        tp_expect(p, .Right_Brace)
    } else {
        append(&body, tp_stmt(p))
    }
    return tp_node(p, .Defer, kw, start, tp_list(p, body))
}

tp_if_branch_end :: proc(p: ^Tree_Parser) -> bool {
    k := tp_kind(p)
    return k == .Right_Brace || k == .Else || k == .Elif || k == .EOF
}

tp_if_branch :: proc(p: ^Tree_Parser) -> u32 {
    tp_skip_newlines(p)
    body := tp_items()
    for !tp_if_branch_end(p) {
        append(&body, tp_stmt(p))
        tp_skip_separator(p)
    }
    return tp_list(p, body)
}

tp_condition :: proc(p: ^Tree_Parser) -> Tree_Id {
    p.no_struct_lit = true
    c := tp_expr(p)
    p.no_struct_lit = false
    return c
}

// `if c {…}` (its else and elif chain inside the braces), `if c do s`; `#if`
// with its `#`.
tp_if :: proc(p: ^Tree_Parser, hash: Token_Id) -> Tree_Id {
    start := int(hash) if hash != 0 else p.pos
    kw := tp_advance(p)
    cond := tp_condition(p)
    tp_skip_newlines(p)
    if tp_kind(p) == .Do {
        tp_advance(p)
        body := tp_items()
        append(&body, tp_stmt(p))
        return tp_node(p, .If, kw, start, u32(cond), tree_rec_add(p.t, tp_list(p, body), 0, u32(hash)))
    }
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    then := tp_if_branch(p)
    else_: u32
    if tp_kind(p) == .Elif {
        chain := tp_items()
        append(&chain, tp_elif(p))
        else_ = tp_list(p, chain)
    } else if tp_kind(p) == .Else {
        tp_advance(p)
        tp_skip_newlines(p)
        else_ = tp_if_branch(p)
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .If, kw, start, u32(cond), tree_rec_add(p.t, then, else_, u32(hash)))
}

tp_elif :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    cond := tp_condition(p)
    tp_skip_newlines(p)
    then := tp_if_branch(p)
    else_: u32
    if tp_kind(p) == .Elif {
        chain := tp_items()
        append(&chain, tp_elif(p))
        else_ = tp_list(p, chain)
    } else if tp_kind(p) == .Else {
        tp_advance(p)
        tp_skip_newlines(p)
        else_ = tp_if_branch(p)
    }
    return tp_node(p, .Elif, kw, start, u32(cond), tree_rec_add(p.t, then, else_, 0))
}

tp_match_arm_start :: proc(p: ^Tree_Parser) -> bool {
    k := tp_kind(p)
    if k == .Right_Brace || k == .EOF { return true }
    if k == .Dot && tp_peek(p) == .Identifier { return true }
    if k == .Identifier {
        #partial switch tp_peek(p) {
        case .Identifier, .Newline, .Return, .If, .For, .Match, .Break, .Continue, .Left_Brace, .Do:
            return true
        case .Dot, .Left_Bracket:
            return tp_path_arm_ends(p)
        }
    }
    return k == .Number || k == .String || k == .Char || k == .Else
}

// A field path or index after an arm's leading name ends where an arm's
// pattern does (`do`, a line break, a `{`), not where a statement goes on.
tp_path_arm_ends :: proc(p: ^Tree_Parser) -> bool {
    pos := p.pos + 1
    depth := 0
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        if depth > 0 {
            #partial switch k {
            case .Left_Bracket:  depth += 1
            case .Right_Bracket: depth -= 1
            case .EOF:           return false
            }
            pos += 1
            continue
        }
        #partial switch k {
        case .Dot, .Identifier: pos += 1; continue
        case .Left_Bracket:     depth += 1; pos += 1; continue
        case .Do, .Newline, .Left_Brace: return true
        }
        return false
    }
    return false
}

tp_arm_body :: proc(p: ^Tree_Parser) -> u32 {
    if tp_kind(p) == .Do {
        tp_advance(p)
        body := tp_items()
        append(&body, tp_stmt(p))
        tp_skip_newlines(p)
        return tp_list(p, body)
    }
    tp_skip_newlines(p)
    body := tp_items()
    for !tp_match_arm_start(p) {
        append(&body, tp_stmt(p))
        tp_skip_separator(p)
    }
    return tp_list(p, body)
}

tp_match :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    subject: Tree_Id
    tp_skip_newlines(p)
    if tp_kind(p) == .Left_Brace {
        tp_error(p, tp_here(p), PARSE_MATCH_NEEDS_SUBJECT)
    } else {
        subject = tp_condition(p)
        tp_skip_newlines(p)
    }
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    arms := tp_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        tp_skip_newlines(p)
        arm_start := p.pos
        if tp_kind(p) == .Else {
            kw := tp_advance(p)
            append(&arms, tp_node(p, .Arm_Else, kw, arm_start, tp_arm_body(p)))
        } else if tp_kind(p) == .Dot && tp_peek(p) == .Identifier {
            tp_advance(p)
            variant := tp_advance(p)
            body := tp_arm_body_lines(p)
            append(&arms, tp_node(p, .Arm_Dot, variant, arm_start, body))
        } else if tp_kind(p) == .Identifier && tp_peek(p) == .Identifier {
            variant := tp_advance(p)
            binding := tp_advance(p)
            body := tp_arm_body(p)
            append(&arms, tp_node(p, .Arm_Variant, variant, arm_start, body, u32(binding)))
        } else if tp_kind(p) == .Identifier && (tp_peek(p) == .Newline || tp_peek(p) == .Do) {
            variant := tp_advance(p)
            body := tp_arm_body(p)
            append(&arms, tp_node(p, .Arm_Variant, variant, arm_start, body))
        } else {
            value := tp_expr(p)
            body := tp_arm_body(p)
            append(&arms, tp_node(p, .Arm_Value, p.t.main[value], arm_start, u32(value), body))
        }
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Match, kw, start, u32(subject), tp_list(p, arms))
}

// A dot arm's body is always its lines (no `do` form).
tp_arm_body_lines :: proc(p: ^Tree_Parser) -> u32 {
    tp_skip_newlines(p)
    body := tp_items()
    for !tp_match_arm_start(p) {
        append(&body, tp_stmt(p))
        tp_skip_separator(p)
    }
    return tp_list(p, body)
}

tp_loop_body :: proc(p: ^Tree_Parser) -> u32 {
    tp_skip_newlines(p)
    if tp_kind(p) == .Do {
        tp_advance(p)
        body := tp_items()
        append(&body, tp_stmt(p))
        return tp_list(p, body)
    }
    return tp_block(p)
}

tp_for :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    if tp_kind(p) == .Identifier {
        m := tp_mark(p)
        first := tp_advance(p)
        second: Token_Id
        has_second := false
        if tp_kind(p) == .Comma {
            tp_advance(p)
            if tp_kind(p) == .Identifier {
                second = tp_advance(p)
                has_second = true
            }
        }
        iter_type: Tree_Id
        if tp_kind(p) == .Colon && tp_peek(p) != .Equals {
            tp_advance(p)
            iter_type = tp_type(p)
        }
        if tp_kind(p) == .In {
            tp_advance(p)
            after := tp_condition(p)
            if tp_kind(p) == .Dot_Dot {
                if has_second { tp_error(p, tp_here(p), PARSE_RANGE_FOR_ONE_VAR) }
                tp_advance(p)
                high := tp_condition(p)
                body := tp_loop_body(p)
                return tp_node(p, .For_Range, kw, start, tree_rec_add(p.t, u32(first), u32(iter_type), u32(after), u32(high), body))
            }
            body := tp_loop_body(p)
            return tp_node(p, .For_Each, kw, start, tree_rec_add(p.t, u32(first), u32(second), u32(iter_type), u32(after), body))
        }
        tp_reset(p, m)
    }
    m := tp_mark(p)
    if init, ok := tp_try_assign(p); ok && tp_kind(p) == .Semicolon {
        tp_advance(p)
        cond := tp_condition(p)
        tp_expect(p, .Semicolon)
        post, _ := tp_try_assign(p)
        body := tp_loop_body(p)
        return tp_node(p, .For_C, kw, start, tree_rec_add(p.t, u32(init), u32(cond), u32(post), body))
    }
    tp_reset(p, m)
    cond := tp_condition(p)
    body := tp_loop_body(p)
    return tp_node(p, .For_Cond, kw, start, u32(cond), body)
}

tp_overload :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    op := tp_advance(p)
    #partial switch build_tokens[op].kind {
    case .Star, .Plus, .Minus, .Slash, .Modulo, .Equal_Equal, .Not_Equal:
    case:
        tp_error(p, op, PARSE_OVERLOAD_EXPECTED_OP, token_text(build_tokens[op]))
    }
    name := tp_expect(p, .Identifier)
    return tp_node(p, .Overload, kw, start, u32(op), u32(name))
}

tp_foreign :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    static_lib: Token_Id
    if tp_kind(p) == .Identifier && tp_text(p) == "static_lib" {
        static_lib = tp_advance(p)
    } else {
        tp_error(p, tp_here(p), PARSE_FOREIGN_NEEDS_STATIC_LIB, tp_text(p))
    }
    lib := tp_expect(p, .String)
    prefix_kw, prefix: Token_Id
    if tp_kind(p) == .Identifier && tp_text(p) == "prefix" {
        prefix_kw = tp_advance(p)
        prefix = tp_expect(p, .Identifier)
    }
    tp_skip_newlines(p)
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    funs := tp_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        fun_start := p.pos
        fun_kw := tp_expect(p, .Fun)
        name := tp_expect(p, .Identifier)
        tp_expect(p, .Left_Paren)
        params := tp_param_loop(p, false)
        tp_expect(p, .Right_Paren)
        returns := tp_optional_returns(p)
        append(&funs, tp_node(p, .Foreign_Fun, fun_kw, fun_start, tree_rec_add(p.t, u32(name), params, returns)))
        tp_skip_newlines(p)
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Foreign, kw, start, tree_rec_add(p.t, u32(static_lib), u32(lib), u32(prefix_kw), u32(prefix), tp_list(p, funs)))
}

// --- declarations -----------------------------------------------------------

// A statement that starts with a name: a definition, a declaration, an
// assignment. Not one: nothing appended, and false.
tp_try_assign :: proc(p: ^Tree_Parser) -> (Tree_Id, bool) {
    start := p.pos
    m := tp_mark(p)
    name := tp_advance(p)

    if tp_kind(p) == .Comma {
        s, ok, done := tp_try_multi(p, start, name)
        if done && ok { return s, true }
        tp_reset(p, m)
        if done { return 0, false }   // a multi-name statement it isn't: none
        name = tp_advance(p)
    }

    #partial switch tp_kind(p) {
    case .Double_Colon:
        tp_advance(p)
        value: Tree_Id
        #partial switch tp_kind(p) {
        case .Fun:      value = tp_scope_def(p, .Fun_Def, 0)
        case .Struct:   value = tp_scope_def(p, .Struct_Def, 0)
        case .Union:    value = tp_union_def(p)
        case .Error:    value = tp_error_def(p)
        case .Dispatch: value = tp_dispatch_def(p)
        case .Distinct:
            def_start := p.pos
            kw := tp_advance(p)
            value = tp_node(p, .Distinct_Def, kw, def_start, u32(tp_type(p)))
        case .Hash:
            if tp_peek(p) == .Identifier && tp_text(p, 1) == "packed" {
                hash := tp_advance(p)
                tp_advance(p)   // `packed`
                if tp_kind(p) != .Struct { tp_error(p, hash, PARSE_PACKED_NEEDS_STRUCT_DECL) }
                value = tp_scope_def(p, .Struct_Def, hash)
            }
        }
        if value == 0 && tp_kind(p) == .Identifier && tp_text(p) == "type" {
            def_start := p.pos
            kw := tp_advance(p)
            parens := tp_kind(p) == .Left_Paren
            if parens { tp_advance(p) }
            base := tp_type(p)
            if parens { tp_expect(p, .Right_Paren) }
            value = tp_node(p, .Alias_Def, kw, def_start, u32(base))
        }
        if value == 0 { value = tp_expr(p) }
        return tp_node(p, .Define, name, start, 0, u32(value)), true

    case .Colon:
        tp_advance(p)
        target := tp_items()
        if tp_kind(p) == .Equals {
            tp_advance(p)
            values := tp_items()
            append(&values, tp_expr(p))
            append(&target, tp_leaf_at(p, .Ident, name))
            return tp_node(p, .Decl, name, start, tp_list(p, target), tree_rec_add(p.t, 0, tp_list(p, values))), true
        }
        type_ := tp_type(p)
        if tp_kind(p) == .Equals {
            tp_advance(p)
            values := tp_items()
            append(&values, tp_expr(p))
            append(&target, tp_leaf_at(p, .Ident, name))
            return tp_node(p, .Decl, name, start, tp_list(p, target), tree_rec_add(p.t, u32(type_), tp_list(p, values))), true
        }
        if tp_kind(p) == .Colon {
            tp_advance(p)
            value := tp_expr(p)
            return tp_node(p, .Define, name, start, u32(type_), u32(value)), true
        }
        append(&target, tp_leaf_at(p, .Ident, name))
        return tp_node(p, .Decl, name, start, tp_list(p, target), tree_rec_add(p.t, u32(type_), 0)), true

    case .Equals:
        tp_advance(p)
        target := tp_items()
        append(&target, tp_leaf_at(p, .Ident, name))
        values := tp_items()
        append(&values, tp_expr(p))
        return tp_node(p, .Assign, name, start, tp_list(p, target), tp_list(p, values)), true

    case .Plus_Equal, .Minus_Equal, .Mul_Equal, .Div_Equal, .Mod_Equal,
         .And_Equal, .Or_Equal, .Xor_Equal, .Shift_Left_Equal, .Shift_Right_Equal:
        target := tp_leaf_at(p, .Ident, name)
        op := tp_advance(p)
        rhs := tp_expr(p)
        return tp_node(p, .Compound, name, start, u32(target), tree_rec_add(p.t, u32(op), u32(rhs))), true

    case .Left_Bracket, .Dot, .Caret:
        lhs := tp_leaf_at(p, .Ident, name)
        for tp_kind(p) == .Left_Bracket || tp_kind(p) == .Dot || tp_kind(p) == .Caret {
            #partial switch tp_kind(p) {
            case .Left_Bracket:
                tp_advance(p)
                low := tp_expr(p)
                if tp_kind(p) == .Colon {
                    tp_advance(p)
                    high: Tree_Id
                    if tp_kind(p) != .Right_Bracket { high = tp_expr(p) }
                    tp_expect(p, .Right_Bracket)
                    if tp_kind(p) == .Equals {
                        target := tp_node(p, .Slice, name, start, u32(lhs), tree_rec_add(p.t, u32(low), u32(high)))
                        tp_advance(p)
                        targets := tp_items()
                        append(&targets, target)
                        values := tp_items()
                        append(&values, tp_expr(p))
                        return tp_node(p, .Assign, name, start, tp_list(p, targets), tp_list(p, values)), true
                    }
                    tp_reset(p, m)
                    return 0, false
                }
                tp_expect(p, .Right_Bracket)
                // (Reported at the target's start, covering it.)
                lhs = tp_node(p, .Index, name, start, u32(lhs), u32(low))
            case .Dot:
                tp_advance(p)
                field := tp_expect(p, .Identifier)
                lhs = tp_node(p, .Field, name, start, u32(lhs), u32(field))
            case .Caret:
                caret := tp_advance(p)
                lhs = tp_node(p, .Deref, name, start, u32(lhs), u32(caret))
            }
        }
        if tp_kind(p) == .Left_Paren {
            tp_reset(p, m)
            return 0, false
        }
        if tp_kind(p) == .Comma {
            targets := tp_items()
            append(&targets, lhs)
            for tp_kind(p) == .Comma {
                tp_advance(p)
                append(&targets, tp_expr(p))
            }
            declares := false
            if tp_kind(p) == .Colon {
                tp_advance(p)
                if tp_kind(p) != .Equals {
                    tp_reset(p, m)
                    return 0, false
                }
                declares = true
            }
            if tp_kind(p) != .Equals {
                tp_reset(p, m)
                return 0, false
            }
            tp_advance(p)
            values := tp_items()
            append(&values, tp_expr(p))
            for tp_kind(p) == .Comma {
                tp_advance(p)
                append(&values, tp_expr(p))
            }
            if len(values) > 1 {
                if len(values) != len(targets) {
                    tp_reset(p, m)
                    return 0, false
                }
                for tg in targets {
                    if !tp_assignable(p, tg) {
                        tp_reset(p, m)
                        return 0, false
                    }
                }
            }
            if declares {
                return tp_node(p, .Decl, name, start, tp_list(p, targets), tree_rec_add(p.t, 0, tp_list(p, values))), true
            }
            return tp_node(p, .Assign, name, start, tp_list(p, targets), tp_list(p, values)), true
        }
        if tp_kind(p) == .Equals {
            tp_advance(p)
            targets := tp_items()
            append(&targets, lhs)
            values := tp_items()
            append(&values, tp_expr(p))
            return tp_node(p, .Assign, name, start, tp_list(p, targets), tp_list(p, values)), true
        }
        #partial switch tp_kind(p) {
        case .Plus_Equal, .Minus_Equal, .Mul_Equal, .Div_Equal, .Mod_Equal,
             .And_Equal, .Or_Equal, .Xor_Equal, .Shift_Left_Equal, .Shift_Right_Equal:
            op := tp_advance(p)
            rhs := tp_expr(p)
            return tp_node(p, .Compound, name, start, u32(lhs), tree_rec_add(p.t, u32(op), u32(rhs))), true
        }
        tp_reset(p, m)
        return 0, false
    }
    tp_reset(p, m)
    return 0, false
}

// A target an assignment can write: a name, a field, an element, a
// dereference.
tp_assignable :: proc(p: ^Tree_Parser, n: Tree_Id) -> bool {
    #partial switch p.t.tag[n] {
    case .Ident, .Field, .Index, .Deref: return true
    }
    return false
}

// A one-token node over a token consumed earlier.
tp_leaf_at :: proc(p: ^Tree_Parser, tag: Tree_Tag, tok: Token_Id) -> Tree_Id {
    n := tree_add(p.t, tag, tok)
    return n
}

// `a, b := …`, `a, b : T = …`, `a, b = …`, `a, x.f := f()`: after the first
// name, at its comma. `done` false: not one of these (the caller backtracks).
tp_try_multi :: proc(p: ^Tree_Parser, start: int, name: Token_Id) -> (s: Tree_Id, ok: bool, done: bool) {
    targets := tp_items()
    append(&targets, tp_leaf_at(p, .Ident, name))
    has_target := false
    for tp_kind(p) == .Comma {
        tp_advance(p)
        if tp_kind(p) != .Identifier { return 0, false, false }
        item := tp_advance(p)
        if tp_kind(p) == .Dot || tp_kind(p) == .Left_Bracket || tp_kind(p) == .Caret {
            chain, chain_ok := tp_bind_chain(p, item)
            if !chain_ok { return 0, false, false }
            append(&targets, chain)
            has_target = true
        } else {
            append(&targets, tp_leaf_at(p, .Ident, item))
        }
    }
    if has_target {
        if tp_kind(p) == .Colon {
            tp_advance(p)
            if tp_kind(p) == .Equals {
                tp_advance(p)
                values := tp_items()
                append(&values, tp_expr(p))
                return tp_node(p, .Decl, name, start, tp_list(p, targets), tree_rec_add(p.t, 0, tp_list(p, values))), true, true
            }
            return 0, false, true
        }
        if tp_kind(p) == .Equals {
            tp_advance(p)
            values := tp_items()
            append(&values, tp_expr(p))
            for tp_kind(p) == .Comma {
                tp_advance(p)
                append(&values, tp_expr(p))
            }
            return tp_node(p, .Assign, name, start, tp_list(p, targets), tp_list(p, values)), true, true
        }
        return 0, false, true
    }
    if tp_kind(p) == .Colon {
        tp_advance(p)
        type_: Tree_Id
        values: u32
        if tp_kind(p) == .Equals {
            tp_advance(p)
            values = tp_multi_values(p, len(targets), false)
        } else {
            type_ = tp_type(p)
            if tp_kind(p) == .Equals {
                tp_advance(p)
                values = tp_multi_values(p, len(targets), false)
            }
        }
        return tp_node(p, .Decl, name, start, tp_list(p, targets), tree_rec_add(p.t, u32(type_), values)), true, true
    }
    if tp_kind(p) == .Equals {
        tp_advance(p)
        values := tp_items()
        if tp_kind(p) == .Identifier && tp_text(p) == "all" {
            all_start := p.pos
            all_tok := tp_advance(p)
            v := tp_expr(p)
            append(&values, tp_node(p, .Broadcast, all_tok, all_start, u32(v)))
        } else {
            append(&values, tp_expr(p))
            for tp_kind(p) == .Comma {
                tp_advance(p)
                append(&values, tp_expr(p))
            }
        }
        return tp_node(p, .Assign, name, start, tp_list(p, targets), tp_list(p, values)), true, true
    }
    return 0, false, false
}

// A destructure item's lvalue chain, its leading name consumed: each link
// reported at the chain's first token. (A slice is no bind target.)
tp_bind_chain :: proc(p: ^Tree_Parser, first: Token_Id) -> (Tree_Id, bool) {
    start := int(first)
    lhs := tp_leaf_at(p, .Ident, first)
    for {
        #partial switch tp_kind(p) {
        case .Dot:
            tp_advance(p)
            field := tp_expect(p, .Identifier)
            lhs = tp_node(p, .Field, first, start, u32(lhs), u32(field))
        case .Left_Bracket:
            tp_advance(p)
            idx := tp_expr(p)
            if tp_kind(p) != .Right_Bracket { return 0, false }
            tp_advance(p)
            lhs = tp_node(p, .Index, first, start, u32(lhs), u32(idx))
        case .Caret:
            caret := tp_advance(p)
            lhs = tp_node(p, .Deref, first, start, u32(lhs), u32(caret))
        case:
            return lhs, true
        }
    }
}

// The values of a multi-name declaration: `all v`, `a, b, c`, one call. In a
// parameter list (`group_break`), a comma before `name :` or `name ,` ends
// the group instead.
tp_multi_values :: proc(p: ^Tree_Parser, n_names: int, group_break: bool) -> u32 {
    values := tp_items()
    if tp_kind(p) == .Identifier && tp_text(p) == "all" {
        all_start := p.pos
        all_tok := tp_advance(p)
        v := tp_expr(p)
        append(&values, tp_node(p, .Broadcast, all_tok, all_start, u32(v)))
        return tp_list(p, values)
    }
    append(&values, tp_expr(p))
    for tp_kind(p) == .Comma {
        if group_break {
            ofs := 1
            for tp_peek(p, ofs) == .Newline { ofs += 1 }
            if tp_peek(p, ofs) == .Identifier {
                next := ofs + 1
                for tp_peek(p, next) == .Newline { next += 1 }
                if k := tp_peek(p, next); k == .Colon || k == .Comma { break }
            }
        }
        tp_advance(p)
        append(&values, tp_expr(p))
    }
    if n := len(values); n != 0 && n != 1 && n != n_names {
        tp_error(p, tp_here(p), PARSE_DEFAULT_VALUE_COUNT_MISMATCH, n, n_names, n_names)
    }
    return tp_list(p, values)
}

// --- scopes -----------------------------------------------------------------

// A generic param in a header: `$T: type`, `$N: int = 256`.
tp_generic_param :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    tp_advance(p)   // `$`
    name := tp_expect(p, .Identifier)
    tp_expect(p, .Colon)
    kind := tp_expect(p, .Identifier)
    default: Token_Id
    if token_text(build_tokens[kind]) != "type" && tp_kind(p) == .Equals {
        tp_advance(p)
        default = tp_expect(p, .Number)
    }
    return tp_node(p, .Generic_Param, name, start, u32(kind), u32(default))
}

// `fun …` / `struct …`, its keyword next: the header — generic params,
// params, returns — and the body.
tp_scope_def :: proc(p: ^Tree_Parser, tag: Tree_Tag, packed: Token_Id) -> Tree_Id {
    start := int(packed) if packed != 0 else p.pos
    kw := tp_advance(p)
    commas := tag == .Struct_Def
    generics, params, returns: u32
    if tp_kind(p) == .Left_Brace {
        body, intrinsic := tp_scope_body(p, commas)
        return tp_node(p, tag, kw, start, tree_rec_add(p.t, 0, 0, 0, body, u32(intrinsic)), u32(packed))
    }
    tp_expect(p, .Left_Paren)
    tp_skip_newlines(p)
    gs := tp_items()
    for tp_kind(p) == .Dollar {
        append(&gs, tp_generic_param(p))
        if tp_kind(p) == .Comma {
            tp_advance(p)
            tp_skip_newlines(p)
        }
    }
    generics = tp_list(p, gs)
    if tp_kind(p) == .Right_Paren {
        tp_advance(p)
        tp_skip_newlines(p)
        if tp_kind(p) == .Arrow || tp_can_start_type(p) {
            if tp_kind(p) == .Arrow {
                tp_advance(p)
                tp_skip_newlines(p)
            }
            returns = tp_return_clause(p, false)
            tp_skip_newlines(p)
        } else if len(gs) > 0 {
            tp_skip_newlines(p)
        } else {
            returns = tp_optional_returns(p)
            tp_skip_newlines(p)
        }
    } else {
        params = tp_param_loop(p, true)
        tp_expect(p, .Right_Paren)
        returns = tp_optional_returns(p)
        tp_skip_newlines(p)
    }
    body, intrinsic := tp_scope_body(p, commas)
    return tp_node(p, tag, kw, start, tree_rec_add(p.t, generics, params, returns, body, u32(intrinsic)), u32(packed))
}

// A parameter list's groups, between parens the caller consumes.
tp_param_loop :: proc(p: ^Tree_Parser, defaults: bool) -> u32 {
    groups := tp_items()
    tp_skip_newlines(p)
    if tp_kind(p) == .Right_Paren { return 0 }
    append(&groups, tp_param_group(p, defaults))
    for tp_kind(p) == .Comma || tp_kind(p) == .Newline {
        if tp_kind(p) == .Comma { tp_advance(p) }
        tp_skip_newlines(p)
        if tp_kind(p) == .Right_Paren { break }
        append(&groups, tp_param_group(p, defaults))
    }
    tp_skip_newlines(p)
    return tp_list(p, groups)
}

// `a, b: T = x, y`, `a := x`: one group of names.
tp_param_group :: proc(p: ^Tree_Parser, defaults: bool) -> Tree_Id {
    start := p.pos
    names := tp_token_items()
    first := tp_expect(p, .Identifier)
    append(&names, first)
    for tp_kind(p) == .Comma {
        if tp_peek(p, 1) == .Identifier && (tp_peek(p, 2) == .Comma || tp_peek(p, 2) == .Colon) {
            tp_advance(p)
            tp_skip_newlines(p)
            append(&names, tp_expect(p, .Identifier))
        } else {
            break
        }
    }
    tp_expect(p, .Colon)
    type_: Tree_Id
    values: u32
    if defaults && tp_kind(p) == .Equals {
        tp_advance(p)
        values = tp_multi_values(p, len(names), true)
    } else {
        type_ = tp_type(p)
        if defaults && tp_kind(p) == .Equals {
            tp_advance(p)
            values = tp_multi_values(p, len(names), true)
        }
    }
    return tp_node(p, .Param_Group, first, start, tp_tokens(p, names), tree_rec_add(p.t, u32(type_), values))
}

// `-> T`, a bare `T`, or none (newlines before either allowed).
tp_optional_returns :: proc(p: ^Tree_Parser) -> u32 {
    saved := p.pos
    for tp_kind(p) == .Newline { p.pos += 1 }
    if tp_kind(p) == .Arrow {
        tp_advance(p)
        tp_skip_newlines(p)
        return tp_return_clause(p, false)
    }
    if tp_can_start_type(p) {
        types := tp_items()
        append(&types, tp_type(p))
        return tp_list(p, types)
    }
    p.pos = saved
    return 0
}

// Whether the tokens from `offset` on start a named group: `name:` or
// `name, name, … :`.
tp_named_group_at :: proc(p: ^Tree_Parser, offset: int) -> bool {
    i := offset
    for tp_peek(p, i) == .Newline { i += 1 }
    for {
        if tp_peek(p, i) != .Identifier { return false }
        i += 1
        if tp_peek(p, i) == .Colon { return true }
        if tp_peek(p, i) != .Comma { return false }
        i += 1
    }
}

// The returns after `->`: types, or named groups; outer parens cosmetic. (A fn
// type's are always types.)
tp_return_clause :: proc(p: ^Tree_Parser, fn_type: bool) -> u32 {
    wrapped := false
    if tp_kind(p) == .Left_Paren {
        wrapped = true
        tp_advance(p)
        tp_skip_newlines(p)
    }
    out := tp_items()
    if !fn_type && tp_named_group_at(p, 0) {
        append(&out, tp_param_group(p, false))
        for tp_kind(p) == .Comma {
            tp_advance(p)
            tp_skip_newlines(p)
            append(&out, tp_param_group(p, false))
        }
    } else {
        append(&out, tp_type(p))
        for tp_kind(p) == .Comma && (wrapped || !tp_named_group_at(p, 1)) {
            tp_advance(p)
            tp_skip_newlines(p)
            append(&out, tp_type(p))
        }
    }
    if wrapped {
        tp_skip_newlines(p)
        tp_expect(p, .Right_Paren)
    }
    return tp_list(p, out)
}

tp_union_def :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    options := tp_items()
    if tp_kind(p) == .Left_Paren {
        tp_advance(p)
        for tp_kind(p) != .Right_Paren && tp_kind(p) != .EOF {
            opt_start := p.pos
            if tp_kind(p) == .Dollar {
                append(&options, tp_generic_param(p))
            } else if tp_kind(p) == .Identifier && tp_text(p) == "tag" {
                opt := tp_advance(p)
                keyword: Token_Id
                if tp_is_type_keyword(tp_kind(p)) {
                    keyword = tp_advance(p)
                } else {
                    tp_error(p, tp_here(p), PARSE_UNION_TAG_NEEDS_TYPE, tp_text(p))
                }
                append(&options, tp_node(p, .Union_Tag, opt, opt_start, u32(keyword)))
            } else if tp_kind(p) == .Identifier && tp_text(p) == "pad" {
                opt := tp_advance(p)
                append(&options, tp_node(p, .Union_Pad, opt, opt_start, u32(tp_type(p))))
            } else if tp_kind(p) == .Identifier && tp_text(p) == "size" {
                opt := tp_advance(p)
                n: Token_Id
                if tp_kind(p) == .Number {
                    n = tp_advance(p)
                } else {
                    tp_error(p, tp_here(p), PARSE_UNION_SIZE_NEEDS_NUM, tp_text(p))
                }
                append(&options, tp_node(p, .Union_Size, opt, opt_start, u32(n)))
            } else {
                tp_error(p, tp_here(p), PARSE_UNION_HEADER_UNKNOWN, tp_text(p))
                tp_advance(p)
            }
            if tp_kind(p) == .Comma { tp_advance(p) }
            tp_skip_newlines(p)
        }
        tp_expect(p, .Right_Paren)
    }
    tp_skip_newlines(p)
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    variants := tp_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        v_start := p.pos
        name := tp_expect(p, .Identifier)
        tag: Tree_Id
        if tp_kind(p) == .Equals {
            tp_advance(p)
            if tp_kind(p) == .Minus {
                minus_start := p.pos
                minus := tp_advance(p)
                n := tp_leaf(p, .Number, tp_expect(p, .Number))
                tag = tp_node(p, .Unary, minus, minus_start, u32(n))
            } else {
                tag = tp_leaf(p, .Number, tp_expect(p, .Number))
            }
        }
        // (Its body a struct's: its declarations its fields, run when it
        // is built.)
        body: Tree_Id
        if tp_kind(p) == .Left_Brace {
            stmts, intrinsic := tp_scope_body(p, true)
            if intrinsic != 0 { tp_error(p, Token_Id(p.t.main[intrinsic]), PARSE_VARIANT_INTRINSIC_BODY) }
            body = tp_node(p, .Struct_Def, name, v_start, tree_rec_add(p.t, 0, 0, 0, stmts, 0), 0)
        }
        append(&variants, tp_node(p, .Variant, name, v_start, u32(tag), u32(body)))
        if tp_kind(p) == .Comma { tp_advance(p) }
        tp_skip_newlines(p)
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Union_Def, kw, start, tp_list(p, options), tp_list(p, variants))
}

tp_error_def :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    tp_skip_newlines(p)
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    names := tp_token_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        append(&names, tp_expect(p, .Identifier))
        if tp_kind(p) == .Comma { tp_advance(p) }
        tp_skip_newlines(p)
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Error_Def, kw, start, tp_tokens(p, names))
}

tp_dispatch_def :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    kw := tp_advance(p)
    tp_expect(p, .Left_Brace)
    tp_skip_newlines(p)
    names := tp_token_items()
    for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
        append(&names, tp_expect(p, .Identifier))
        tp_skip_separator(p, commas = true)
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Dispatch_Def, kw, start, tp_tokens(p, names))
}

// --- types --------------------------------------------------------------------

tp_is_type_keyword :: proc(k: Token_Kind) -> bool {
    #partial switch k {
    case .Int, .F64, .Bool_Type, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .Utf8, .Byte:
        return true
    }
    return false
}

tp_can_start_type :: proc(p: ^Tree_Parser) -> bool {
    if tp_is_type_keyword(tp_kind(p)) { return true }
    #partial switch tp_kind(p) {
    case .Identifier, .Caret, .Left_Bracket, .Left_Paren, .Dollar: return true
    case .Fun: return tp_peek(p) == .Left_Paren
    }
    return false
}

// A removed sentinel (`[N, 0]T`): its error, and the plain form parsed on.
tp_removed_sentinel :: proc(p: ^Tree_Parser) {
    if tp_kind(p) != .Comma { return }
    tp_error(p, tp_here(p), PARSE_SENTINEL_REMOVED)
    tp_advance(p)
    tp_skip_newlines(p)
    tp_expect(p, .Number)
}

// A generic type argument: a type, or a value (a number, a name, an
// expression).
tp_generic_arg :: proc(p: ^Tree_Parser) -> Tree_Id {
    if tp_kind(p) == .Number {
        if tp_peek(p) == .Right_Paren || tp_peek(p) == .Comma { return tp_leaf(p, .Number, tp_advance(p)) }
        return tp_expr(p, 0)
    }
    k := tp_kind(p)
    if tp_is_type_keyword(k) || k == .Caret || k == .Left_Bracket || k == .Left_Paren || k == .Dollar ||
       k == .Fun && tp_peek(p) == .Left_Paren {
        return tp_type(p)
    }
    if k == .Identifier {
        if tp_peek(p) == .Left_Paren { return tp_expr(p, 0) }
        if tp_peek(p) == .Right_Paren || tp_peek(p) == .Comma {
            start := p.pos
            parts := tp_token_items()
            append(&parts, tp_advance(p))
            return tp_node(p, .Type_Name, Token_Id(start), start, tp_tokens(p, parts))
        }
        return tp_expr(p, 0)
    }
    return tp_type(p)
}

tp_type :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    #partial switch tp_kind(p) {
    case .Dollar:
        d := tp_advance(p)
        name := tp_expect(p, .Identifier)
        return tp_node(p, .Type_Dollar, d, start, u32(name))
    case .Tilde:
        t := tp_advance(p)
        name := tp_expect(p, .Identifier)
        return tp_node(p, .Type_Tilde, t, start, u32(name))
    case .Left_Paren:
        paren := tp_advance(p)
        inner := tp_type(p)
        if tp_kind(p) == .Comma {
            tp_error(p, paren, PARSE_TUPLE_TYPE_NOT_SUPPORTED)
            for tp_kind(p) == .Comma {
                tp_advance(p)
                tp_skip_newlines(p)
                tp_type(p)
            }
        }
        tp_expect(p, .Right_Paren)
        return tp_node(p, .Type_Paren, paren, start, u32(inner))
    case .Caret:
        c := tp_advance(p)
        return tp_node(p, .Type_Pointer, c, start, u32(tp_type(p)))
    case .Fn:
        kw := tp_advance(p)
        if tp_kind(p) == .Left_Paren {
            tp_advance(p)
            params := tp_items()
            returns: u32
            if tp_kind(p) != .Arrow && tp_kind(p) != .Right_Paren {
                append(&params, tp_type(p))
                for tp_kind(p) == .Comma {
                    tp_advance(p)
                    append(&params, tp_type(p))
                }
            }
            if tp_kind(p) == .Arrow {
                tp_advance(p)
                returns = tp_return_clause(p, true)
            }
            tp_expect(p, .Right_Paren)
            return tp_node(p, .Type_Fun, kw, start, tp_list(p, params), returns)
        }
        parts := tp_token_items()
        append(&parts, tp_expect(p, .Identifier))
        if tp_kind(p) == .Dot && tp_peek(p) == .Identifier {
            tp_advance(p)
            append(&parts, tp_advance(p))
        }
        return tp_node(p, .Type_Of, kw, start, tp_tokens(p, parts))
    case .Fun:
        if tp_peek(p) != .Left_Paren { break }
        kw := tp_advance(p)
        tp_advance(p)   // `(`
        params := tp_items()
        if tp_kind(p) != .Right_Paren {
            append(&params, tp_type(p))
            for tp_kind(p) == .Comma {
                tp_advance(p)
                append(&params, tp_type(p))
            }
        }
        tp_expect(p, .Right_Paren)
        returns: u32
        if tp_kind(p) == .Arrow {
            tp_advance(p)
            returns = tp_return_clause(p, true)
        }
        return tp_node(p, .Type_Fun, kw, start, tp_list(p, params), returns)
    case .Left_Bracket:
        return tp_bracket_type(p)
    case .Identifier:
        name := tp_advance(p)
        if tp_kind(p) == .Dot && tp_peek(p) == .Identifier {
            parts := tp_token_items()
            append(&parts, name)
            for tp_kind(p) == .Dot && tp_peek(p) == .Identifier {
                tp_advance(p)
                append(&parts, tp_advance(p))
            }
            return tp_node(p, .Type_Name, name, start, tp_tokens(p, parts))
        }
        if tp_kind(p) == .Left_Paren {
            tp_advance(p)
            args := tp_items()
            if tp_kind(p) != .Right_Paren {
                append(&args, tp_generic_arg(p))
                for tp_kind(p) == .Comma {
                    tp_advance(p)
                    append(&args, tp_generic_arg(p))
                }
            }
            tp_expect(p, .Right_Paren)
            return tp_node(p, .Type_Generic, name, start, tp_list(p, args))
        }
        parts := tp_token_items()
        append(&parts, name)
        return tp_node(p, .Type_Name, name, start, tp_tokens(p, parts))
    }
    if tp_is_type_keyword(tp_kind(p)) { return tp_leaf(p, .Type_Keyword, tp_advance(p)) }
    tok := tp_tok(p)
    tp_error(p, tp_here(p), PARSE_EXPECTED_TYPE, tok.kind, token_text(tok))
    bad := tp_advance(p)
    return tp_node(p, .Type_Name, bad, start)
}

// `[]T`, `[:N]T`, `[..N]T`, `[N]T`, `[N I]T`.
tp_bracket_type :: proc(p: ^Tree_Parser) -> Tree_Id {
    start := p.pos
    br := tp_advance(p)
    if tp_kind(p) == .Right_Bracket || tp_kind(p) == .Comma {
        tp_removed_sentinel(p)
        tp_expect(p, .Right_Bracket)
        return tp_node(p, .Type_Slice, br, start, 0, u32(tp_type(p)))
    }
    if tp_kind(p) == .Colon {
        tp_advance(p)
        cap := tp_expr(p, 0)
        tp_removed_sentinel(p)
        tp_expect(p, .Right_Bracket)
        elem := tp_type(p)
        return tp_node(p, .Type_Slice, br, start, u32(cap), u32(elem))
    }
    if tp_kind(p) == .Dot_Dot {
        tp_advance(p)
        size: Tree_Id
        if tp_kind(p) == .Number && (tp_peek(p) == .Right_Bracket || tp_peek(p) == .Comma) {
            size = tp_leaf(p, .Number, tp_advance(p))
        } else if tp_kind(p) == .Identifier && (tp_peek(p) == .Right_Bracket || tp_peek(p) == .Comma) {
            size = tp_leaf(p, .Ident, tp_advance(p))
        } else {
            size = tp_expr(p, 0)
        }
        tp_removed_sentinel(p)
        tp_expect(p, .Right_Bracket)
        elem := tp_type(p)
        return tp_node(p, .Type_Partial, br, start, u32(size), u32(elem))
    }
    terminates := tp_peek(p) == .Right_Bracket || tp_peek(p) == .Comma || tp_peek(p) == .Identifier
    size: Tree_Id
    if tp_kind(p) == .Number && terminates {
        size = tp_leaf(p, .Number, tp_advance(p))
    } else if tp_kind(p) == .Identifier && terminates {
        size = tp_leaf(p, .Ident, tp_advance(p))
    } else {
        size = tp_expr(p, 0)
    }
    index: Tree_Id
    if tp_kind(p) == .Identifier { index = tp_type(p) }
    tp_removed_sentinel(p)
    tp_expect(p, .Right_Bracket)
    elem := tp_type(p)
    return tp_node(p, .Type_Array, br, start, tree_rec_add(p.t, u32(size), u32(index)), u32(elem))
}

// --- expressions ---------------------------------------------------------------

tp_precedence :: proc(k: Token_Kind) -> int {
    #partial switch k {
    case .Or:  return 1
    case .And: return 2
    case .Equal_Equal, .Not_Equal, .Less, .Less_Equal, .Greater, .Greater_Equal: return 3
    case .Pipe: return 4
    case .Tilde: return 5
    case .Ampersand: return 6
    case .Shift_Left, .Shift_Right: return 7
    case .Plus, .Minus, .Wrap_Plus, .Wrap_Minus: return 8
    case .Star, .Slash, .Modulo, .Wrap_Star: return 9
    }
    return -1
}

tp_expr :: proc(p: ^Tree_Parser, min_prec := 0) -> Tree_Id {
    left := tp_primary(p)
    for {
        is_in := tp_kind(p) == .In
        is_not_in := tp_kind(p) == .Not && tp_peek(p) == .In
        if is_in || is_not_in {
            if 3 < min_prec { break }
            first := int(p.t.first[left])
            kw := tp_advance(p)
            if is_not_in { tp_advance(p) }
            lo := tp_expr(p, 4)
            if tp_kind(p) != .Dot_Dot {
                tp_error(p, tp_here(p), PARSE_RANGE_NEEDS_DOTS, "not " if is_not_in else "")
                left = lo
                continue
            }
            tp_advance(p)
            hi := tp_expr(p, 4)
            left = tp_node(p, .In_Range, kw, first, u32(left), tree_rec_add(p.t, u32(lo), u32(hi)))
            continue
        }
        prec := tp_precedence(tp_kind(p))
        if prec < min_prec { break }
        // `a &b` (spaced before, glued after): a prefix `&`, not an AND.
        if tp_kind(p) == .Ampersand && p.pos > p.first {
            amp, prev, next := tp_tok(p), tp_tok(p, -1), tp_tok(p, 1)
            if token_line(amp) == token_line(prev) && token_line(next) == token_line(amp) {
                spaced_before := token_col(amp) > token_col(prev) + len(token_text(prev))
                glued_after := token_col(next) == token_col(amp) + 1
                if spaced_before && glued_after { tp_error(p, tp_here(p), PARSE_AMBIGUOUS_AMPERSAND) }
            }
        }
        first := int(p.t.first[left])
        op := tp_advance(p)
        right := tp_expr(p, prec + 1)
        left = tp_node(p, .Binary, op, first, u32(left), u32(right))
    }
    return left
}

// Whether a `{` here opens a literal rather than a body.
tp_is_literal :: proc(p: ^Tree_Parser) -> bool {
    if tp_kind(p) != .Left_Brace || p.no_struct_lit { return false }
    ofs := 1
    for tp_peek(p, ofs) == .Newline { ofs += 1 }
    next := tp_peek(p, ofs)
    if next == .Right_Brace { return true }
    if next == .Number && tp_text(p, ofs) == "0" && tp_peek(p, ofs + 1) == .Right_Brace { return true }
    if next == .Identifier {
        n := ofs + 1
        for tp_peek(p, n) == .Newline { n += 1 }
        if tp_peek(p, n) == .Equals { return true }
    }
    #partial switch next {
    case .Number, .String, .Char, .True, .False, .Identifier,
         .Left_Bracket, .Left_Paren, .Left_Brace, .Minus, .Ampersand, .Caret, .Bang, .Tilde,
         .If, .Hash,
         .Int, .F64, .Bool_Type, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .Utf8, .Byte:
        return true
    }
    return false
}

tp_is_broadcast_start :: proc(k: Token_Kind) -> bool {
    #partial switch k {
    case .Identifier, .Number, .String, .Char, .True, .False, .Minus, .Caret, .Ampersand,
         .Left_Bracket, .Left_Brace, .Fun, .Match, .If, .Hash,
         .Bool_Type, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .F64, .Utf8, .Byte:
        return true
    }
    return false
}

// A literal's braces and entries: named (`a = v`), positional, `{0}`,
// `{all v}`. Its type, when it has one, parsed before it; `first`, where the
// literal starts (its name, its type).
tp_literal :: proc(p: ^Tree_Parser, type_: Tree_Id, first: int, main: Token_Id = 0) -> Tree_Id {
    brace := tp_advance(p)
    tp_skip_newlines(p)
    entries := tp_items()
    if tp_kind(p) != .Right_Brace {
        if tp_kind(p) == .Number && tp_text(p) == "0" && tp_peek(p) == .Right_Brace {
            append(&entries, tp_leaf(p, .Number, tp_advance(p)))
        } else if tp_kind(p) == .Identifier && tp_text(p) == "all" && tp_peek(p) != .Equals {
            all_start := p.pos
            all_tok := tp_advance(p)
            v := tp_expr(p)
            append(&entries, tp_node(p, .Broadcast, all_tok, all_start, u32(v)))
            tp_skip_newlines(p)
        } else {
            positional := !(tp_kind(p) == .Identifier && tp_peek(p) == .Equals)
            append(&entries, tp_entry(p, positional))
            for tp_kind(p) != .Right_Brace && tp_kind(p) != .EOF {
                if tp_kind(p) == .Comma { tp_advance(p) }
                tp_skip_newlines(p)
                if tp_kind(p) == .Right_Brace { break }
                named := tp_kind(p) == .Identifier && tp_peek(p) == .Equals
                if named == positional { tp_error(p, tp_here(p), PARSE_STRUCT_LIT_MIXED_FIELDS) }
                append(&entries, tp_entry(p, positional))
            }
        }
    }
    tp_expect(p, .Right_Brace)
    return tp_node(p, .Literal, main if main != 0 else brace, first, u32(type_), tp_list(p, entries))
}

tp_entry :: proc(p: ^Tree_Parser, positional: bool) -> Tree_Id {
    if positional { return tp_expr(p) }
    start := p.pos
    name := tp_expect(p, .Identifier)
    tp_expect(p, .Equals)
    return tp_node(p, .Named_Entry, name, start, u32(tp_expr(p)))
}

// Whether an expression is a pure name path (`A.B.C`): a qualified literal's
// type.
tp_is_name_path :: proc(p: ^Tree_Parser, n: Tree_Id) -> bool {
    #partial switch p.t.tag[n] {
    case .Ident: return true
    case .Field: return tp_is_name_path(p, Tree_Id(p.t.a[n]))
    }
    return false
}

// `[…] T {` ahead: a typed array literal (`[3]f32{…}`), not an array.
tp_is_typed_array_literal :: proc(p: ^Tree_Parser) -> bool {
    if tp_kind(p) != .Left_Bracket { return false }
    depth := 0
    pos := p.pos
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        if k == .Left_Bracket {
            depth += 1
        } else if k == .Right_Bracket {
            depth -= 1
            if depth == 0 { pos += 1; break }
        }
        pos += 1
    }
    if pos >= len(p.tokens) { return false }
    for pos < len(p.tokens) {
        k := p.tokens[pos].kind
        if k == .Caret { pos += 1; continue }
        if k == .Left_Bracket {
            depth = 0
            for pos < len(p.tokens) {
                kk := p.tokens[pos].kind
                if kk == .Left_Bracket {
                    depth += 1
                } else if kk == .Right_Bracket {
                    depth -= 1
                    if depth == 0 { pos += 1; break }
                }
                pos += 1
            }
            continue
        }
        break
    }
    if pos + 1 >= len(p.tokens) { return false }
    #partial switch p.tokens[pos].kind {
    case .Identifier, .Int, .F64, .F32, .Bool_Type, .I8, .I16, .I32, .I64,
         .U8, .U16, .U32, .U64, .Utf8, .Byte:
        return p.tokens[pos + 1].kind == .Left_Brace
    }
    return false
}

// A call's arguments, its `(` consumed; its override literal after.
tp_call_args :: proc(p: ^Tree_Parser) -> u32 {
    tp_skip_newlines(p)
    saved := p.no_struct_lit
    p.no_struct_lit = false
    args := tp_items()
    if tp_kind(p) != .Right_Paren {
        append(&args, tp_expr(p))
        for tp_kind(p) == .Comma || tp_kind(p) == .Newline {
            if tp_kind(p) == .Comma { tp_advance(p) }
            tp_skip_newlines(p)
            if tp_kind(p) == .Right_Paren { break }
            append(&args, tp_expr(p))
        }
    }
    tp_skip_newlines(p)
    p.no_struct_lit = saved
    tp_expect(p, .Right_Paren)
    return tp_list(p, args)
}

tp_primary :: proc(p: ^Tree_Parser, allow_dot := true) -> Tree_Id {
    start := p.pos
    result: Tree_Id
    #partial switch tp_kind(p) {
    case .Number:
        tok := tp_advance(p)
        tp_number(p, tok)
        result = tp_leaf(p, .Number, tok)
    case .Identifier:
        tok := tp_advance(p)
        text := token_text(build_tokens[tok])
        switch {
        case text == "size_of" && tp_kind(p) == .Left_Paren:
            tp_advance(p)
            ty := tp_type(p)
            tp_expect(p, .Right_Paren)
            result = tp_node(p, .Size_Of, tok, start, u32(ty))
        case text == "assert" && tp_kind(p) == .Left_Paren:
            tp_advance(p)
            cond := tp_expr(p)
            tp_expect(p, .Right_Paren)
            result = tp_node(p, .Assert, tok, start, u32(cond))
        case (text == "let" || text == "slice") && tp_kind(p) == .Left_Paren:
            tp_advance(p)
            ty: Tree_Id
            if text == "slice" && tp_kind(p) != .Left_Bracket {
                storage := tp_expr(p)
                tp_expect(p, .Right_Paren)
                result = tp_node(p, .Take, tok, start, 0, u32(storage))
            } else {
                ty = tp_type(p)
                tp_expect(p, .Comma)
                tp_skip_newlines(p)
                storage := tp_expr(p)
                tp_expect(p, .Right_Paren)
                result = tp_node(p, .Take, tok, start, u32(ty), u32(storage))
            }
        case text == "all" && tp_is_broadcast_start(tp_kind(p)):
            v := tp_expr(p)
            result = tp_node(p, .Broadcast, tok, start, u32(v))
        case tp_kind(p) == .Left_Paren:
            tp_advance(p)
            args := tp_call_args(p)
            over: Tree_Id
            if tp_is_literal(p) { over = tp_literal(p, 0, p.pos) }
            result = tp_node(p, .Call, tok, start, args, u32(over))
        case tp_is_literal(p):
            name := tp_leaf(p, .Ident, tok)
            result = tp_literal(p, name, start)
        case:
            result = tp_leaf(p, .Ident, tok)
        }
    case .Dot:
        dot := tp_advance(p)
        if tp_kind(p) != .Identifier {
            tp_error(p, tp_here(p), PARSE_EXPECTED_VARIANT_NAME)
            result = tp_leaf(p, .Dot_Ident, dot)
        } else {
            name := tp_advance(p)
            result = tp_node(p, .Dot_Ident, dot, start, u32(name))
        }
    case .True:   result = tp_leaf(p, .True, tp_advance(p))
    case .False:  result = tp_leaf(p, .False, tp_advance(p))
    case .String: result = tp_leaf(p, .String, tp_advance(p))
    case .Char:   result = tp_leaf(p, .Char, tp_advance(p))
    case .Left_Paren:
        paren := tp_advance(p)
        saved := p.no_struct_lit
        p.no_struct_lit = false
        inner := tp_expr(p)
        p.no_struct_lit = saved
        tp_expect(p, .Right_Paren)
        result = tp_node(p, .Paren, paren, start, u32(inner))
    case .Left_Bracket:
        if tp_is_typed_array_literal(p) {
            ty := tp_type(p)
            result = tp_literal(p, ty, start, Token_Id(start))
        } else {
            br := tp_advance(p)
            tp_skip_newlines(p)
            saved := p.no_struct_lit
            p.no_struct_lit = false
            elems := tp_items()
            if tp_kind(p) != .Right_Bracket {
                append(&elems, tp_expr(p))
                for tp_kind(p) == .Comma || tp_kind(p) == .Newline {
                    if tp_kind(p) == .Comma { tp_advance(p) }
                    tp_skip_newlines(p)
                    if tp_kind(p) == .Right_Bracket { break }
                    append(&elems, tp_expr(p))
                }
            }
            p.no_struct_lit = saved
            tp_expect(p, .Right_Bracket)
            result = tp_node(p, .Array, br, start, tp_list(p, elems))
        }
    case .Left_Brace:
        if tp_is_literal(p) {
            result = tp_literal(p, 0, start)
        } else {
            tp_error(p, tp_here(p), PARSE_UNEXPECTED_LBRACE_IN_EXPR)
            result = tp_leaf(p, .Number, tp_advance(p))
        }
    case .Minus:
        op := tp_advance(p)
        operand: Tree_Id
        if tp_kind(p) == .Number {
            num := tp_advance(p)
            tp_number(p, num)
            operand = tp_leaf(p, .Number, num)
        } else {
            operand = tp_primary(p)
        }
        result = tp_node(p, .Unary, op, start, u32(operand))
    case .Wrap_Minus, .Not, .Tilde:
        op := tp_advance(p)
        result = tp_node(p, .Unary, op, start, u32(tp_primary(p)))
    case .Bang:
        // (C's `!x`: said as Mara says it, parsed on as one.)
        op := tp_advance(p)
        tp_error(p, op, PARSE_BANG_NOT)
        result = tp_node(p, .Unary, op, start, u32(tp_primary(p)))
    case .Ampersand:
        op := tp_advance(p)
        result = tp_node(p, .Unary, op, start, u32(tp_primary(p, allow_dot = true)))
    case .If:
        kw := tp_advance(p)
        cond := tp_condition(p)
        tp_expect(p, .Do)
        then := tp_expr(p)
        if p.t.tag[then] == .If_Expr { tp_error(p, kw, PARSE_NESTED_IF_EXPR) }
        tp_expect(p, .Else)
        else_ := tp_expr(p)
        if p.t.tag[else_] == .If_Expr { tp_error(p, kw, PARSE_NESTED_IF_EXPR) }
        result = tp_node(p, .If_Expr, kw, start, u32(cond), tree_rec_add(p.t, u32(then), u32(else_)))
    case .Int, .F64, .Bool_Type, .I8, .I16, .I32, .I64, .U8, .U16, .U32, .U64, .F32, .Utf8, .Byte:
        kw := tp_advance(p)
        if tp_kind(p) == .Left_Paren {
            tp_advance(p)
            args := tp_call_args(p)
            result = tp_node(p, .Call, kw, start, args)
        } else {
            // (A type is no value: `size_of(u8)` takes one as its own.)
            tp_error(p, kw, PARSE_TYPE_AS_VALUE, token_text(build_tokens[kw]))
            result = tp_leaf(p, .Ident, kw)
        }
    case .Hash:
        hash := tp_advance(p)
        if tp_kind(p) != .Identifier {
            tp_error(p, hash, PARSE_EXPECTED_HASH_NAME)
            result = tp_leaf(p, .Self, hash)
        } else {
            name := tp_advance(p)
            switch token_text(build_tokens[name]) {
            case "skip_constructor":
                tp_error(p, hash, PARSE_SKIP_CONSTRUCTOR_REMOVED)
                result = tp_node(p, .Hash_Name, hash, start, u32(name))
            case "self":
                result = tp_node(p, .Self, hash, start)
            case "big_endian":
                inner := tp_primary(p, allow_dot)
                if tag := p.t.tag[inner]; tag != .Index && tag != .Slice { tp_error(p, hash, PARSE_BIG_ENDIAN_NEEDS_BYTE_READ) }
                result = tp_node(p, .Big_Endian, hash, start, u32(inner))
            case "caller_name", "caller_span", "web", "native", "windows", "linux", "mac":
                result = tp_node(p, .Hash_Name, hash, start, u32(name))
            case:
                tp_error(p, hash, PARSE_UNKNOWN_INTRINSIC, token_text(build_tokens[name]))
                result = tp_node(p, .Hash_Name, hash, start, u32(name))
            }
        }
    case .Use, .Include, .Sealed:
        sealed: Token_Id
        if tp_kind(p) == .Sealed { sealed = tp_advance(p) }
        if tp_kind(p) != .Use && tp_kind(p) != .Include {
            tp_error(p, tp_here(p), PARSE_SEALED_NEEDS_USE_INCLUDE, tp_text(p))
            bad := tp_advance(p)
            return tp_node(p, .Import, bad, start, 0, u32(sealed))
        }
        kw := tp_advance(p)
        parts := tp_token_items()
        append(&parts, tp_expect(p, .Identifier))
        for tp_kind(p) == .Dot {
            tp_advance(p)
            append(&parts, tp_expect(p, .Identifier))
        }
        result = tp_node(p, .Import, kw, start, tp_tokens(p, parts), u32(sealed))
    case:
        tok := tp_tok(p)
        tp_error(p, tp_here(p), PARSE_UNEXPECTED_TOKEN, tok.kind, token_text(tok))
        result = tp_leaf(p, .Number, tp_advance(p))
    }
    return tp_postfix(p, result, allow_dot)
}

// Indexing, slicing, fields, method calls, `^`, `?` after an operand.
tp_postfix :: proc(p: ^Tree_Parser, operand: Tree_Id, allow_dot: bool) -> Tree_Id {
    result := operand
    for {
        k := tp_kind(p)
        if !(k == .Left_Bracket || allow_dot && k == .Dot || k == .Caret || k == .Question) { break }
        first := int(p.t.first[result])
        #partial switch k {
        case .Question:
            q := tp_advance(p)
            result = tp_node(p, .Try, q, first, u32(result))
        case .Caret:
            c := tp_advance(p)
            result = tp_node(p, .Deref, c, first, u32(result), u32(c))
        case .Left_Bracket:
            br := tp_advance(p)
            saved := p.no_struct_lit
            p.no_struct_lit = false
            if tp_kind(p) == .Colon {
                tp_advance(p)
                high: Tree_Id
                if tp_kind(p) != .Right_Bracket { high = tp_expr(p) }
                p.no_struct_lit = saved
                tp_expect(p, .Right_Bracket)
                result = tp_node(p, .Slice, br, first, u32(result), tree_rec_add(p.t, 0, u32(high)))
            } else {
                index := tp_expr(p)
                if tp_kind(p) == .Colon {
                    tp_advance(p)
                    high: Tree_Id
                    if tp_kind(p) != .Right_Bracket { high = tp_expr(p) }
                    p.no_struct_lit = saved
                    tp_expect(p, .Right_Bracket)
                    result = tp_node(p, .Slice, br, first, u32(result), tree_rec_add(p.t, u32(index), u32(high)))
                } else {
                    p.no_struct_lit = saved
                    tp_expect(p, .Right_Bracket)
                    result = tp_node(p, .Index, br, first, u32(result), u32(index))
                }
            }
        case .Dot:
            dot := tp_advance(p)
            name := tp_expect(p, .Identifier)
            if tp_kind(p) == .Left_Paren {
                tp_advance(p)
                args := tp_call_args(p)
                over: Tree_Id
                if tp_is_literal(p) { over = tp_literal(p, 0, p.pos) }
                result = tp_node(p, .Method_Call, dot, first, tree_rec_add(p.t, u32(result), u32(name), args, u32(over)))
            } else {
                result = tp_node(p, .Field, dot, first, u32(result), u32(name))
                if tp_is_literal(p) && tp_is_name_path(p, result) {
                    result = tp_literal(p, result, first)
                }
            }
        }
    }
    return result
}

// --- the build's --------------------------------------------------------------

