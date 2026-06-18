package mara

import "core:strings"

Token_Kind :: enum {
    EOF,
    Invalid,

    // Literals
    Number,
    String,
    Char,
    Identifier,

    True,
    False,
    If,
    Else,
    Elif,
    Fun, // fun / method
    Fn,  // fn — nominal function type from a named function
    Struct, // struct / class
    Union,
    Error,    // error { Not_Found ... } — flat tag set, member of the global open `err` type
    Use,      // use <path> — private import (names visible in this file only)
    Include,  // include <path> — re-export (names visible here AND to consumers)
    Sealed,
    Module,
    Return,
    For,
    In,
    Break,
    Continue,
    And,
    Or,
    Not,
    Match,
    Foreign,
    Defer,
    Using,
    Distinct,
    Dispatch,
    Overload,
    Do,
    Var,
    Intrinsic,

    // Type keywords
    Int,
    F64,
    Bool_Type,
    I8, I16, I32, I64,
    U8, U16, U32, U64,
    F32,
    Utf8,
    Byte,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Modulo,
    Wrap_Plus,    // +%  — wrapping (two's-complement) add, no overflow trap
    Wrap_Minus,   // -%  — wrapping sub / wrapping unary negate
    Wrap_Star,    // *%  — wrapping mul
    Equals,
    Equal_Equal,
    Not_Equal,
    Less,
    Less_Equal,
    Greater,
    Greater_Equal,

    Plus_Equal,
    Minus_Equal,
    Mul_Equal,
    Div_Equal,
    Mod_Equal,
    And_Equal,        // &=
    Or_Equal,         // |=
    Xor_Equal,        // ~=
    Shift_Left_Equal, // <<=
    Shift_Right_Equal,// >>=

    Arrow,        // ->
    Bang,         // !
    Question,     // ?  — postfix err propagation
    Double_Colon, // ::
    Ampersand,    // &
    Pipe,         // |
    Tilde,        // ~
    Caret,        // ^
    Hash,         // #
    Dollar,       // $
    At,           // @
    Dot_Dot,      // .. — exclusive range operator (only form)
    Shift_Left,   // <<
    Shift_Right,  // >>

    // Delimiters
    Left_Paren,
    Right_Paren,
    Left_Brace,
    Right_Brace,
    Left_Bracket,
    Right_Bracket,
    Comma,
    Dot,
    Colon,
    Semicolon,
    Newline,
}

Token :: struct {
    kind: Token_Kind,
    text: string, // slice into the source buffer; only escaped string/char literals own a copy
    line: int,
    col:  int,
}

Lexer :: struct {
    source: string,
    pos:    int,
    line:   int,
    col:    int,
    file:   string,
}

// Keyword lookup — maps identifier text to Token_Kind.
// "array" is NOT a keyword — handled contextually in parser after `::`.
keyword_lookup :: proc(text: string) -> (Token_Kind, bool) {
    switch text {
    case "true":     return .True, true
    case "false":    return .False, true
    case "if":       return .If, true
    case "else":     return .Else, true
    case "elif":     return .Elif, true
    case "fun":      return .Fun, true
    case "method":   return .Fun, true
    case "fn":       return .Fn, true
    case "struct":   return .Struct, true
    case "class":    return .Struct, true
    case "union":    return .Union, true
    case "error":    return .Error, true
    case "use":      return .Use, true
    case "include":  return .Include, true
    case "sealed":   return .Sealed, true
    case "module":   return .Module, true
    case "package":  return .Module, true  // deprecated — accepted for backward compat
    case "return":   return .Return, true
    case "for":      return .For, true
    case "in":       return .In, true
    case "break":    return .Break, true
    case "continue": return .Continue, true
    case "and":      return .And, true
    case "or":       return .Or, true
    case "not":      return .Not, true
    case "match":    return .Match, true
    case "foreign":  return .Foreign, true
    case "defer":    return .Defer, true
    case "using":    return .Using, true
    case "distinct": return .Distinct, true
    case "dispatch": return .Dispatch, true
    case "overload": return .Overload, true
    case "do":       return .Do, true
    case "var":      return .Var, true
    case "intrinsic": return .Intrinsic, true
    case "int":      return .Int, true
    case "f64":      return .F64, true
    case "bool":     return .Bool_Type, true
    // "string" is no longer a keyword — it's a regular identifier
    case "i8":       return .I8, true
    case "i16":      return .I16, true
    case "i32":      return .I32, true
    case "i64":      return .I64, true
    case "u8":       return .U8, true
    case "u16":      return .U16, true
    case "u32":      return .U32, true
    case "u64":      return .U64, true
    case "f32":      return .F32, true
    case "utf8":     return .Utf8, true
    case "byte":     return .Byte, true
    }
    return .EOF, false
}

lexer_init :: proc(source: string, file: string = "") -> Lexer {
    return Lexer{source = source, pos = 0, line = 1, col = 1, file = file}
}

// Advance the lexer position by n characters, tracking line/col
// Strip up to `strip` leading whitespace chars (spaces or tabs) from each
// line of `buf`, and drop a single leading newline if the buffer starts with
// one. Used for multi-line text-block-style string literals.
dedent_multiline_string :: proc(buf: [dynamic]u8, strip: int) -> [dynamic]u8 {
    out: [dynamic]u8
    n := len(buf)
    i := 0
    // Drop a single leading newline so `print("\n    line", ...)` style
    // (which is how multi-line literals are typically written) doesn't add
    // a blank first line to the output.
    if i < n && buf[i] == '\n' { i += 1 }
    for i < n {
        // Strip up to `strip` leading whitespace chars on this line. Lines
        // shorter than `strip` keep whatever content they have; we don't
        // error on under-indent.
        skipped := 0
        for skipped < strip && i < n && (buf[i] == ' ' || buf[i] == '\t') {
            skipped += 1
            i += 1
        }
        // Copy the rest of this line, including the trailing newline.
        for i < n && buf[i] != '\n' {
            append(&out, buf[i])
            i += 1
        }
        if i < n && buf[i] == '\n' {
            append(&out, '\n')
            i += 1
        }
    }
    delete(buf)
    // Mirror of the leading-newline drop above: a newline right before the
    // closing `"` — the quote on its own line, which is the idiomatic way to
    // set the dedent column — is structural, not content, so drop it. For an
    // intentional trailing newline, leave a blank line before the closing quote
    // (one structural newline is dropped, the other survives) or use `\n`.
    if len(out) > 0 && out[len(out) - 1] == '\n' {
        pop(&out)
    }
    return out
}

lexer_advance :: proc(l: ^Lexer, n: int = 1) {
    for i := 0; i < n; i += 1 {
        if l.pos < len(l.source) {
            if l.source[l.pos] == '\n' {
                l.line += 1
                l.col = 1
            } else {
                l.col += 1
            }
            l.pos += 1
        }
    }
}

make_token :: proc(l: ^Lexer, kind: Token_Kind, text: string, tok_line: int, tok_col: int) -> Token {
    return Token{kind = kind, text = text, line = tok_line, col = tok_col}
}

next_token :: proc(l: ^Lexer) -> Token {
    // Skip spaces and tabs (but NOT newlines — they're statement separators)
    for l.pos < len(l.source) && (l.source[l.pos] == ' ' || l.source[l.pos] == '\t') {
        lexer_advance(l)
    }

    // Check for end of input
    if l.pos >= len(l.source) {
        return Token{kind = .EOF, line = l.line, col = l.col}
    }

    ch := l.source[l.pos]

    if ch == '/' && peek(l, 1) == '/' {
        for l.pos < len(l.source) && l.source[l.pos] != '\n' {
            lexer_advance(l)
        }
        return next_token(l)
    }

    // Save position for token
    tok_line := l.line
    tok_col := l.col

    // Newlines
    if ch == '\n' || ch == '\r' {
        start := l.pos
        // Consume \r\n as a single newline
        if ch == '\r' && peek(l, 1) == '\n' {
            lexer_advance(l, 2)
        } else {
            lexer_advance(l)
        }
        return make_token(l, .Newline, l.source[start:l.pos], tok_line, tok_col)
    }

    // Character literals: 'c' with escape sequences
    if ch == '\'' {
        lexer_advance(l) // skip opening quote
        char_val: u8
        if l.pos < len(l.source) && l.source[l.pos] == '\\' {
            lexer_advance(l) // skip backslash
            if l.pos < len(l.source) {
                switch l.source[l.pos] {
                case 'n':  char_val = '\n'
                case 't':  char_val = '\t'
                case 'r':  char_val = '\r'
                case '\\': char_val = '\\'
                case '\'': char_val = '\''
                case '0':  char_val = 0
                case:      char_val = l.source[l.pos]
                }
                lexer_advance(l)
            }
        } else if l.pos < len(l.source) {
            char_val = l.source[l.pos]
            lexer_advance(l)
        }
        if l.pos < len(l.source) && l.source[l.pos] == '\'' {
            lexer_advance(l) // skip closing quote
        }
        buf := [1]u8{char_val}
        text := strings.clone_from_bytes(buf[:])
        return make_token(l, .Char, text, tok_line, tok_col)
    }

    // String literals: "..." with escape sequence processing.
    //
    // Multi-line strings (those containing a literal newline in the source)
    // get text-block dedent: the column of the closing `"` defines the strip
    // amount, that many leading whitespace characters are removed from every
    // content line, and a leading newline immediately after the opening `"`
    // is dropped. This lets the source visually nest with surrounding code
    // while the runtime value starts at column 0:
    //
    //     print("
    //         === heading ===
    //         line two
    //         ", a, b)
    //
    // The closing `"` is 8 columns in, so 8 leading whitespace chars are
    // stripped from each line. Source nests cleanly; output starts at col 0.
    if ch == '"' {
        lexer_advance(l) // skip opening quote
        buf: [dynamic]u8
        saw_newline := false
        for l.pos < len(l.source) && l.source[l.pos] != '"' {
            if l.source[l.pos] == '\\' {
                lexer_advance(l) // skip the backslash
                if l.pos < len(l.source) {
                    esc := l.source[l.pos]
                    switch esc {
                    case 'n':  append(&buf, '\n')
                    case 't':  append(&buf, '\t')
                    case 'r':  append(&buf, '\r')
                    case '\\': append(&buf, '\\')
                    case '"':  append(&buf, '"')
                    case:
                        // Unknown escape — drop the backslash (matches char literal behavior)
                        append(&buf, esc)
                    }
                    lexer_advance(l)
                }
            } else if l.source[l.pos] == '\r' {
                // Normalize a raw source line-ending inside the literal: CRLF
                // and a lone CR both collapse to a single '\n', so a multi-line
                // string written in a CRLF-saved file carries no stray carriage
                // returns. (An explicit `\r` escape is handled above and kept.)
                append(&buf, '\n')
                saw_newline = true
                lexer_advance(l)
                if l.pos < len(l.source) && l.source[l.pos] == '\n' {
                    lexer_advance(l) // swallow the LF of a CRLF pair
                }
            } else {
                if l.source[l.pos] == '\n' { saw_newline = true }
                append(&buf, l.source[l.pos])
                lexer_advance(l)
            }
        }
        // l.col is currently the 1-indexed column of the closing `"`. Capture
        // before advancing past it so the dedent logic has the right value.
        closing_col := l.col
        if l.pos < len(l.source) {
            lexer_advance(l) // skip closing quote
        }

        if saw_newline {
            buf = dedent_multiline_string(buf, closing_col - 1)
        }

        text := strings.clone_from_bytes(buf[:])
        return make_token(l, .String, text, tok_line, tok_col)
    }

    // Numbers: consume all consecutive digits.
    // Hex form `0x...` / `0X...` consumes hex digits plus `_` separators
    // (e.g. `0xFFFF_FFFF`). Hex tokens keep the `0x` prefix in their text so
    // the parser can route to base-16 parsing.
    if is_digit(ch) {
        start := l.pos
        if ch == '0' && (peek(l, 1) == 'x' || peek(l, 1) == 'X') {
            lexer_advance(l) // '0'
            lexer_advance(l) // 'x'
            for l.pos < len(l.source) && (is_hex_digit(l.source[l.pos]) || l.source[l.pos] == '_') {
                lexer_advance(l)
            }
            return make_token(l, .Number, l.source[start:l.pos], tok_line, tok_col)
        }
        // Binary form `0b...` / `0B...` consumes 0/1 digits plus `_` separators
        // (e.g. `0b1010_0000`). Keeps the `0b` prefix so the parser routes to
        // base-2.
        if ch == '0' && (peek(l, 1) == 'b' || peek(l, 1) == 'B') {
            lexer_advance(l) // '0'
            lexer_advance(l) // 'b'
            for l.pos < len(l.source) && (l.source[l.pos] == '0' || l.source[l.pos] == '1' || l.source[l.pos] == '_') {
                lexer_advance(l)
            }
            return make_token(l, .Number, l.source[start:l.pos], tok_line, tok_col)
        }
        for l.pos < len(l.source) && (is_digit(l.source[l.pos]) || l.source[l.pos] == '_') {
            lexer_advance(l)
        }
        // A '.' followed by a digit makes this a float literal. The '.' stays in
        // the token text, which is how the parser distinguishes int from float.
        if peek(l) == '.' && is_digit(peek(l, 1)) {
            lexer_advance(l)
            for l.pos < len(l.source) && (is_digit(l.source[l.pos]) || l.source[l.pos] == '_') {
                lexer_advance(l)
            }
        }
        return make_token(l, .Number, l.source[start:l.pos], tok_line, tok_col)
    }

    // Identifiers: start with a letter or underscore
    if is_alpha(ch) {
        start := l.pos
        for l.pos < len(l.source) && is_alnum(l.source[l.pos]) {
            lexer_advance(l)
        }
        text := l.source[start:l.pos]

        // Check for keywords
        if kind, ok := keyword_lookup(text); ok {
            return make_token(l, kind, text, tok_line, tok_col)
        }

        return make_token(l, .Identifier, text, tok_line, tok_col)
    }

    // Three-character tokens (check before two-character)
    start := l.pos

    if l.pos + 2 < len(l.source) {
        three := l.source[start:start+3]
        switch three {
        case "<<=": lexer_advance(l, 3); return make_token(l, .Shift_Left_Equal,  three, tok_line, tok_col)
        case ">>=": lexer_advance(l, 3); return make_token(l, .Shift_Right_Equal, three, tok_line, tok_col)
        }
    }

    // Two-character tokens (check before single-character)
    if l.pos + 1 < len(l.source) {
        two := l.source[start:start+2]
        switch two {
        case "==": lexer_advance(l, 2); return make_token(l, .Equal_Equal,   two, tok_line, tok_col)
        case "!=": lexer_advance(l, 2); return make_token(l, .Not_Equal,     two, tok_line, tok_col)
        case "<=": lexer_advance(l, 2); return make_token(l, .Less_Equal,    two, tok_line, tok_col)
        case ">=": lexer_advance(l, 2); return make_token(l, .Greater_Equal, two, tok_line, tok_col)
        case "<<": lexer_advance(l, 2); return make_token(l, .Shift_Left,    two, tok_line, tok_col)
        case ">>": lexer_advance(l, 2); return make_token(l, .Shift_Right,   two, tok_line, tok_col)
        case "+=": lexer_advance(l, 2); return make_token(l, .Plus_Equal,    two, tok_line, tok_col)
        case "-=": lexer_advance(l, 2); return make_token(l, .Minus_Equal,   two, tok_line, tok_col)
        case "*=": lexer_advance(l, 2); return make_token(l, .Mul_Equal,     two, tok_line, tok_col)
        case "+%": lexer_advance(l, 2); return make_token(l, .Wrap_Plus,     two, tok_line, tok_col)
        case "-%": lexer_advance(l, 2); return make_token(l, .Wrap_Minus,    two, tok_line, tok_col)
        case "*%": lexer_advance(l, 2); return make_token(l, .Wrap_Star,     two, tok_line, tok_col)
        case "/=": lexer_advance(l, 2); return make_token(l, .Div_Equal,     two, tok_line, tok_col)
        case "%=": lexer_advance(l, 2); return make_token(l, .Mod_Equal,     two, tok_line, tok_col)
        case "&=": lexer_advance(l, 2); return make_token(l, .And_Equal,     two, tok_line, tok_col)
        case "|=": lexer_advance(l, 2); return make_token(l, .Or_Equal,      two, tok_line, tok_col)
        case "~=": lexer_advance(l, 2); return make_token(l, .Xor_Equal,     two, tok_line, tok_col)
        case "->": lexer_advance(l, 2); return make_token(l, .Arrow,         two, tok_line, tok_col)
        case "::": lexer_advance(l, 2); return make_token(l, .Double_Colon,  two, tok_line, tok_col)
        }
    }

    // Single-character tokens
    lexer_advance(l)
    switch ch {
    case '=': return make_token(l, .Equals,        l.source[start:l.pos], tok_line, tok_col)
    case '<': return make_token(l, .Less,           l.source[start:l.pos], tok_line, tok_col)
    case '>': return make_token(l, .Greater,        l.source[start:l.pos], tok_line, tok_col)
    case '+': return make_token(l, .Plus,           l.source[start:l.pos], tok_line, tok_col)
    case '-': return make_token(l, .Minus,          l.source[start:l.pos], tok_line, tok_col)
    case '*': return make_token(l, .Star,           l.source[start:l.pos], tok_line, tok_col)
    case '/': return make_token(l, .Slash,          l.source[start:l.pos], tok_line, tok_col)
    case '%': return make_token(l, .Modulo,         l.source[start:l.pos], tok_line, tok_col)
    case '(': return make_token(l, .Left_Paren,     l.source[start:l.pos], tok_line, tok_col)
    case ')': return make_token(l, .Right_Paren,    l.source[start:l.pos], tok_line, tok_col)
    case '{': return make_token(l, .Left_Brace,     l.source[start:l.pos], tok_line, tok_col)
    case '}': return make_token(l, .Right_Brace,    l.source[start:l.pos], tok_line, tok_col)
    case '[': return make_token(l, .Left_Bracket,   l.source[start:l.pos], tok_line, tok_col)
    case ']': return make_token(l, .Right_Bracket,  l.source[start:l.pos], tok_line, tok_col)
    case ',': return make_token(l, .Comma,          l.source[start:l.pos], tok_line, tok_col)
    case '.':
        // .. is the (exclusive) range operator. The legacy `..<` form was
        // dropped — `..` is the only spelling. Use `n+1` on the upper bound
        // when you want to include the endpoint.
        if l.pos < len(l.source) && l.source[l.pos] == '.' {
            lexer_advance(l) // consume second '.'
            return make_token(l, .Dot_Dot, l.source[start:l.pos], tok_line, tok_col)
        }
        return make_token(l, .Dot, l.source[start:l.pos], tok_line, tok_col)
    case ':': return make_token(l, .Colon,          l.source[start:l.pos], tok_line, tok_col)
    case ';': return make_token(l, .Semicolon,     l.source[start:l.pos], tok_line, tok_col)
    case '!': return make_token(l, .Bang,           l.source[start:l.pos], tok_line, tok_col)
    case '?': return make_token(l, .Question,       l.source[start:l.pos], tok_line, tok_col)
    case '&': return make_token(l, .Ampersand,      l.source[start:l.pos], tok_line, tok_col)
    case '|': return make_token(l, .Pipe,            l.source[start:l.pos], tok_line, tok_col)
    case '~': return make_token(l, .Tilde,           l.source[start:l.pos], tok_line, tok_col)
    case '^': return make_token(l, .Caret,           l.source[start:l.pos], tok_line, tok_col)
    case '#': return make_token(l, .Hash,            l.source[start:l.pos], tok_line, tok_col)
    case '$': return make_token(l, .Dollar,          l.source[start:l.pos], tok_line, tok_col)
    case '@': return make_token(l, .At,              l.source[start:l.pos], tok_line, tok_col)
    }

    return make_token(l, .Invalid, l.source[start:l.pos], tok_line, tok_col)
}

// Tokenize the entire source into a heap-allocated token array. Returns a
// pointer so the array lives in the arena (callable from FFI, no by-value
// dynamic-array return crossing the boundary).
lex_all :: proc(source: string, file: string = "") -> ^[dynamic]Token {
    l := lexer_init(source, file)
    tokens := new([dynamic]Token)
    for {
        tok := next_token(&l)
        append(tokens, tok)
        if tok.kind == .EOF {
            break
        }
    }
    return tokens
}

// Helper: is this an ASCII digit?
is_digit :: proc(ch: u8) -> bool {
    return ch >= '0' && ch <= '9'
}

// Helper: is this a hex digit (0-9, a-f, A-F)?
is_hex_digit :: proc(ch: u8) -> bool {
    return is_digit(ch) || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F')
}

// Helper: is this a letter or underscore?
is_alpha :: proc(ch: u8) -> bool {
    return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch == '_'
}

// Helper: is this a letter, digit, or underscore?
is_alnum :: proc(ch: u8) -> bool {
    return is_alpha(ch) || is_digit(ch)
}

// Look at the character at pos + offset without consuming it
peek :: proc(l: ^Lexer, offset: int = 0) -> u8 {
    pos := l.pos + offset
    if pos < len(l.source) {
        return l.source[pos]
    }
    return 0
}