package mara

import "base:runtime"
import "core:fmt"
import "core:os"
import "core:strconv"
import "core:strings"

Token_Kind :: enum u8 {
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
    Defer_Err,  // defer? — a defer only a failure runs
    Using,
    With,       // with p {…} — a block run on another program
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

// Each kind's text as written — two for a keyword with two spellings — or,
// for a kind written many ways, what it is in angle brackets. EOF and Invalid
// have none. (`mara ask #tokens` lists them.)
TOKEN_TEXTS := [Token_Kind][2]string{
    .EOF = {}, .Invalid = {},
    .Number = {"<number>", ""}, .String = {"<string>", ""}, .Char = {"<char>", ""}, .Identifier = {"<name>", ""},
    .True = {"true", ""}, .False = {"false", ""}, .If = {"if", ""}, .Else = {"else", ""}, .Elif = {"elif", ""},
    .Fun = {"fun", "method"}, .Fn = {"fn", ""}, .Struct = {"struct", "class"}, .Union = {"union", ""},
    .Error = {"error", ""}, .Use = {"use", ""}, .Include = {"include", ""}, .Module = {"module", ""},
    .Return = {"return", ""}, .For = {"for", ""}, .In = {"in", ""}, .Break = {"break", ""},
    .Continue = {"continue", ""}, .And = {"and", ""}, .Or = {"or", ""}, .Not = {"not", ""},
    .Match = {"match", ""}, .Foreign = {"foreign", ""}, .Defer = {"defer", ""}, .Defer_Err = {"defer?", ""},
    .Using = {"using", ""}, .With = {"with", ""}, .Distinct = {"distinct", ""}, .Dispatch = {"dispatch", ""},
    .Overload = {"overload", ""}, .Do = {"do", ""}, .Var = {"var", ""}, .Intrinsic = {"intrinsic", ""},
    .Int = {"int", ""}, .F64 = {"f64", ""}, .Bool_Type = {"bool", ""},
    .I8 = {"i8", ""}, .I16 = {"i16", ""}, .I32 = {"i32", ""}, .I64 = {"i64", ""},
    .U8 = {"u8", ""}, .U16 = {"u16", ""}, .U32 = {"u32", ""}, .U64 = {"u64", ""},
    .F32 = {"f32", ""}, .Utf8 = {"utf8", ""}, .Byte = {"byte", ""},
    .Plus = {"+", ""}, .Minus = {"-", ""}, .Star = {"*", ""}, .Slash = {"/", ""}, .Modulo = {"%", ""},
    .Wrap_Plus = {"+%", ""}, .Wrap_Minus = {"-%", ""}, .Wrap_Star = {"*%", ""},
    .Equals = {"=", ""}, .Equal_Equal = {"==", ""}, .Not_Equal = {"!=", ""},
    .Less = {"<", ""}, .Less_Equal = {"<=", ""}, .Greater = {">", ""}, .Greater_Equal = {">=", ""},
    .Plus_Equal = {"+=", ""}, .Minus_Equal = {"-=", ""}, .Mul_Equal = {"*=", ""}, .Div_Equal = {"/=", ""},
    .Mod_Equal = {"%=", ""}, .And_Equal = {"&=", ""}, .Or_Equal = {"|=", ""}, .Xor_Equal = {"~=", ""},
    .Shift_Left_Equal = {"<<=", ""}, .Shift_Right_Equal = {">>=", ""},
    .Arrow = {"->", ""}, .Bang = {"!", ""}, .Question = {"?", ""}, .Double_Colon = {"::", ""},
    .Ampersand = {"&", ""}, .Pipe = {"|", ""}, .Tilde = {"~", ""}, .Caret = {"^", ""}, .Hash = {"#", ""},
    .Dollar = {"$", ""}, .At = {"@", ""}, .Dot_Dot = {"..", ""}, .Shift_Left = {"<<", ""}, .Shift_Right = {">>", ""},
    .Left_Paren = {"(", ""}, .Right_Paren = {")", ""}, .Left_Brace = {"{", ""}, .Right_Brace = {"}", ""},
    .Left_Bracket = {"[", ""}, .Right_Bracket = {"]", ""}, .Comma = {",", ""}, .Dot = {".", ""},
    .Colon = {":", ""}, .Semicolon = {";", ""}, .Newline = {"<newline>", ""},
}

// A token is where it is: its text is its file's source there (token_text), its
// line and column follow from where it starts (token_line, token_col).
Token :: struct {
    kind:   Token_Kind,
    file:   u16,        // its file's index in build_files
    offset: u32,        // where it starts in its file's source
    len:    u32,        // its length there, in bytes
    id:     Token_Id,   // its index in build_tokens — lets token_span record an
                        // extent (Span.tok) without threading ids through 87 call sites
}

// A token's id: its index in the build's one table of tokens, which every
// file's join in turn, each file a range of it (Source_File.first_token to
// end_token). 0 is no token's.
Token_Id :: distinct u32

build_tokens: [dynamic]Token
build_files:  [dynamic]^Source_File

// A string or char literal's value, decoded by the lexer (escapes, a
// multi-line string's indent): its text as the parser reads it.
build_literals: map[Token_Id]string

// A token's text: a literal's value, else its source.
token_text :: proc(t: Token) -> string {
    if t.kind == .String || t.kind == .Char { return build_literals[t.id] }
    return build_files[t.file].source[t.offset:][:t.len]
}

// Its line: the last line starting at or before it.
token_line :: proc(t: Token) -> int {
    lines := build_files[t.file].lines[:]
    lo, hi := 0, len(lines)   // lines[0] = 0: every token is at or past it
    for hi - lo > 1 {
        mid := (lo + hi) / 2
        if lines[mid] <= t.offset { lo = mid } else { hi = mid }
    }
    return lo + 1
}

// Its column, in bytes from its line's start (as the lexer counts).
token_col :: proc(t: Token) -> int {
    return int(t.offset - build_files[t.file].lines[token_line(t) - 1]) + 1
}

Lexer :: struct {
    source: string,
    pos:    int,
    start:  int,      // where the token being lexed starts
    value:  string,   // a literal's value, decoded
    line:   int,
    col:    int,
    file:   string,
    errors: int,    // lexical errors reported (counted with the file's parse errors)
}

// The byte a backslash escape stands for — one table for char and string
// literals alike. `l.pos` is on the character after the backslash; the escape's
// own position is passed in for the diagnostic. An unknown escape is an error:
// it used to drop the backslash silently, so "\x41" read as "x41".
lex_escape :: proc(l: ^Lexer, esc_line, esc_col: int) -> u8 {
    c := l.source[l.pos]
    switch c {
    case 'n':  return '\n'
    case 't':  return '\t'
    case 'r':  return '\r'
    case '0':  return 0
    case '\\': return '\\'
    case '\'': return '\''
    case '"':  return '"'
    }
    emit_diagnostic(.Parse_Error, format_location(l.file, esc_line, esc_col), LEX_UNKNOWN_ESCAPE, rune(c))
    l.errors += 1
    return c
}

// Keyword lookup — maps identifier text to Token_Kind.
// "array" is NOT a keyword — handled contextually in parser after `::`.
keyword_lookup :: proc(text: string) -> (Token_Kind, bool) {
    // (By the first letter, then the few keywords that start with it: one
    // string compared or two, not each keyword in turn.)
    if len(text) < 2 || len(text) > 9 { return .EOF, false }
    switch text[0] {
    case 'a':
        switch text {
        case "and": return .And, true
        }
    case 'b':
        switch text {
        case "break": return .Break, true
        case "bool": return .Bool_Type, true
        case "byte": return .Byte, true
        }
    case 'c':
        switch text {
        case "class": return .Struct, true
        case "continue": return .Continue, true
        }
    case 'd':
        switch text {
        case "defer": return .Defer, true
        case "distinct": return .Distinct, true
        case "dispatch": return .Dispatch, true
        case "do": return .Do, true
        }
    case 'e':
        switch text {
        case "else": return .Else, true
        case "elif": return .Elif, true
        case "error": return .Error, true
        }
    case 'f':
        switch text {
        case "false": return .False, true
        case "fun": return .Fun, true
        case "fn": return .Fn, true
        case "for": return .For, true
        case "foreign": return .Foreign, true
        case "f64": return .F64, true
        case "f32": return .F32, true
        }
    case 'i':
        switch text {
        case "if": return .If, true
        case "include": return .Include, true
        case "in": return .In, true
        case "intrinsic": return .Intrinsic, true
        case "int": return .Int, true
        case "i8": return .I8, true
        case "i16": return .I16, true
        case "i32": return .I32, true
        case "i64": return .I64, true
        }
    case 'm':
        switch text {
        case "method": return .Fun, true
        case "module": return .Module, true
        case "match": return .Match, true
        }
    case 'n':
        switch text {
        case "not": return .Not, true
        }
    case 'o':
        switch text {
        case "or": return .Or, true
        case "overload": return .Overload, true
        }
    case 'r':
        switch text {
        case "return": return .Return, true
        }
    case 's':
        switch text {
        case "struct": return .Struct, true
        }
    case 't':
        switch text {
        case "true": return .True, true
        }
    case 'u':
        switch text {
        case "union": return .Union, true
        case "use": return .Use, true
        case "using": return .Using, true
        case "u8": return .U8, true
        case "u16": return .U16, true
        case "u32": return .U32, true
        case "u64": return .U64, true
        case "utf8": return .Utf8, true
        }
    case 'v':
        switch text {
        case "var": return .Var, true
        }
    case 'w':
        switch text {
        case "with": return .With, true
        }
    }
    return .EOF, false
}

lexer_init :: proc(source: string, file: string = "") -> Lexer {
    return Lexer{source = source, pos = 0, line = 1, col = 1, file = file}
}

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

// Advance the lexer position by n characters, tracking line/col.
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

// To `pos` past a run of no newline — spaces, a name, digits, a comment's
// text: the column moved on by its length (lexer_advance's, a character at
// a time).
@(private="file")
lex_skip_to :: #force_inline proc(l: ^Lexer, pos: int) {
    l.col += pos - l.pos
    l.pos = pos
}

make_token :: proc(l: ^Lexer, kind: Token_Kind) -> Token {
    return Token{kind = kind, offset = u32(l.start), len = u32(l.pos - l.start)}
}

// Where the block comment starting at src[at] (`/*`) ends: just past its
// `*/`, its nested ones' too; the text's end, and ok false, when it doesn't.
block_comment_end :: proc(src: string, at: int) -> (end: int, ok: bool) {
    depth := 0
    p := at
    for p + 1 < len(src) {
        switch {
        case src[p] == '/' && src[p + 1] == '*':
            depth += 1
            p += 2
        case src[p] == '*' && src[p + 1] == '/':
            depth -= 1
            p += 2
            if depth == 0 { return p, true }
        case:
            p += 1
        }
    }
    return len(src), false
}

next_token :: proc(l: ^Lexer) -> Token {
    // Skip spaces and tabs (but NOT newlines — they're statement separators)
    src := l.source
    p := l.pos
    for p < len(src) && (src[p] == ' ' || src[p] == '\t') { p += 1 }
    lex_skip_to(l, p)

    // Check for end of input
    if l.pos >= len(l.source) {
        return Token{kind = .EOF, offset = u32(l.pos)}
    }

    ch := l.source[l.pos]

    if ch == '/' && peek(l, 1) == '/' {
        for p < len(src) && src[p] != '\n' { p += 1 }
        lex_skip_to(l, p)
        return next_token(l)
    }

    // A block comment, `/* … */` (nesting): skipped — one over a line break
    // a line break itself, as the end of a `//` comment's line is.
    if ch == '/' && peek(l, 1) == '*' {
        l.start = l.pos
        line, col := l.line, l.col
        end, ok := block_comment_end(src, l.pos)
        breaks := strings.index_byte(src[l.pos:end], '\n') >= 0
        lexer_advance(l, end - l.pos)
        if !ok {
            emit_diagnostic(.Parse_Error, format_location(l.file, line, col), LEX_UNTERMINATED_COMMENT)
            l.errors += 1
        }
        if breaks { return make_token(l, .Newline) }
        return next_token(l)
    }

    // Save position for token
    l.start = l.pos

    // Newlines
    if ch == '\n' || ch == '\r' {
        // Consume \r\n as a single newline
        if ch == '\r' && peek(l, 1) == '\n' {
            lexer_advance(l, 2)
        } else {
            lexer_advance(l)
        }
        return make_token(l, .Newline)
    }

    // Character literals: 'c' with escape sequences
    if ch == '\'' {
        lexer_advance(l) // skip opening quote
        char_val: u8
        if l.pos < len(l.source) && l.source[l.pos] == '\\' {
            esc_line, esc_col := l.line, l.col
            lexer_advance(l) // skip backslash
            if l.pos < len(l.source) {
                char_val = lex_escape(l, esc_line, esc_col)
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
        l.value = strings.clone_from_bytes(buf[:])
        return make_token(l, .Char)
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
                esc_line, esc_col := l.line, l.col
                lexer_advance(l) // skip the backslash
                if l.pos < len(l.source) {
                    append(&buf, lex_escape(l, esc_line, esc_col))
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

        l.value = strings.clone_from_bytes(buf[:])
        return make_token(l, .String)
    }

    // Numbers: consume all consecutive digits.
    // Hex form `0x...` / `0X...` consumes hex digits plus `_` separators
    // (e.g. `0xFFFF_FFFF`). Hex tokens keep the `0x` prefix in their text so
    // the parser can route to base-16 parsing.
    if is_digit(ch) {
        if ch == '0' && (peek(l, 1) == 'x' || peek(l, 1) == 'X') {
            lexer_advance(l) // '0'
            lexer_advance(l) // 'x'
            p = l.pos
            for p < len(src) && (is_hex_digit(src[p]) || src[p] == '_') { p += 1 }
            lex_skip_to(l, p)
            return make_token(l, .Number)
        }
        // Binary form `0b...` / `0B...` consumes 0/1 digits plus `_` separators
        // (e.g. `0b1010_0000`). Keeps the `0b` prefix so the parser routes to
        // base-2.
        if ch == '0' && (peek(l, 1) == 'b' || peek(l, 1) == 'B') {
            lexer_advance(l) // '0'
            lexer_advance(l) // 'b'
            p = l.pos
            for p < len(src) && (src[p] == '0' || src[p] == '1' || src[p] == '_') { p += 1 }
            lex_skip_to(l, p)
            return make_token(l, .Number)
        }
        for p < len(src) && (is_digit(src[p]) || src[p] == '_') { p += 1 }
        lex_skip_to(l, p)
        // A '.' followed by a digit makes this a float literal. The '.' stays in
        // the token text, which is how the parser distinguishes int from float.
        if peek(l) == '.' && is_digit(peek(l, 1)) {
            p = l.pos + 1
            for p < len(src) && (is_digit(src[p]) || src[p] == '_') { p += 1 }
            lex_skip_to(l, p)
        }
        return make_token(l, .Number)
    }

    // Identifiers: start with a letter or underscore
    if is_alpha(ch) {
        start := l.pos
        for p < len(src) && is_alnum(src[p]) { p += 1 }
        lex_skip_to(l, p)
        text := l.source[start:l.pos]

        // Check for keywords
        if kind, ok := keyword_lookup(text); ok {
            // (`defer?`: one token, written together — `defer ?` is no
            // statement.)
            if kind == .Defer && p < len(src) && src[p] == '?' {
                lex_skip_to(l, p + 1)
                kind = .Defer_Err
            }
            return make_token(l, kind)
        }

        return make_token(l, .Identifier)
    }

    // Operators: by the first character, then the one or two after it —
    // the longest that's an operator.
    c1, c2 := peek(l, 1), peek(l, 2)
    op :: #force_inline proc(l: ^Lexer, n: int, kind: Token_Kind) -> Token {
        lex_skip_to(l, l.pos + n)   // (no newline in an operator)
        return make_token(l, kind)
    }
    switch ch {
    case '=': return op(l, 2, .Equal_Equal) if c1 == '=' else op(l, 1, .Equals)
    case '!': return op(l, 2, .Not_Equal) if c1 == '=' else op(l, 1, .Bang)
    case '<':
        if c1 == '<' { return op(l, 3, .Shift_Left_Equal) if c2 == '=' else op(l, 2, .Shift_Left) }
        return op(l, 2, .Less_Equal) if c1 == '=' else op(l, 1, .Less)
    case '>':
        if c1 == '>' { return op(l, 3, .Shift_Right_Equal) if c2 == '=' else op(l, 2, .Shift_Right) }
        return op(l, 2, .Greater_Equal) if c1 == '=' else op(l, 1, .Greater)
    case '+':
        switch c1 {
        case '=': return op(l, 2, .Plus_Equal)
        case '%': return op(l, 2, .Wrap_Plus)
        }
        return op(l, 1, .Plus)
    case '-':
        switch c1 {
        case '=': return op(l, 2, .Minus_Equal)
        case '%': return op(l, 2, .Wrap_Minus)
        case '>': return op(l, 2, .Arrow)
        }
        return op(l, 1, .Minus)
    case '*':
        switch c1 {
        case '=': return op(l, 2, .Mul_Equal)
        case '%': return op(l, 2, .Wrap_Star)
        }
        return op(l, 1, .Star)
    case '/': return op(l, 2, .Div_Equal) if c1 == '=' else op(l, 1, .Slash)
    case '%': return op(l, 2, .Mod_Equal) if c1 == '=' else op(l, 1, .Modulo)
    case '&': return op(l, 2, .And_Equal) if c1 == '=' else op(l, 1, .Ampersand)
    case '|': return op(l, 2, .Or_Equal) if c1 == '=' else op(l, 1, .Pipe)
    case '~': return op(l, 2, .Xor_Equal) if c1 == '=' else op(l, 1, .Tilde)
    case ':': return op(l, 2, .Double_Colon) if c1 == ':' else op(l, 1, .Colon)
    // .. is the (exclusive) range operator. The legacy `..<` form was
    // dropped — `..` is the only spelling. Use `n+1` on the upper bound
    // when you want to include the endpoint.
    case '.': return op(l, 2, .Dot_Dot) if c1 == '.' else op(l, 1, .Dot)
    case '(': return op(l, 1, .Left_Paren)
    case ')': return op(l, 1, .Right_Paren)
    case '{': return op(l, 1, .Left_Brace)
    case '}': return op(l, 1, .Right_Brace)
    case '[': return op(l, 1, .Left_Bracket)
    case ']': return op(l, 1, .Right_Bracket)
    case ',': return op(l, 1, .Comma)
    case ';': return op(l, 1, .Semicolon)
    case '?': return op(l, 1, .Question)
    case '^': return op(l, 1, .Caret)
    case '#': return op(l, 1, .Hash)
    case '$': return op(l, 1, .Dollar)
    case '@': return op(l, 1, .At)
    }

    lexer_advance(l)
    return make_token(l, .Invalid)
}

// Tokenize the entire source into a heap-allocated token array. Returns a
// pointer so the array lives in the arena (callable from FFI, no by-value
// dynamic-array return crossing the boundary).
// Lex a file onto the build's tokens: its range is first_token to end_token,
// ending with its EOF.
// Room for n more tokens.
lex_reserve :: proc(n: int) {
    if cap(build_tokens) == 0 { build_tokens = make([dynamic]Token, 0, max(n, 1 << 16), runtime.heap_allocator()) }
    reserve(&build_tokens, len(build_tokens) + n)
}

lex_file :: proc(f: ^Source_File) {
    // (The tokens grow on the heap, which gives back what they outgrow — a
    // build's arena keeps every size they pass.)
    if cap(build_tokens) == 0 { build_tokens = make([dynamic]Token, 0, 1 << 16, runtime.heap_allocator()) }
    if len(build_tokens) == 0 { append(&build_tokens, Token{kind = .EOF}) }   // id 0: no token's
    if len(build_files) > int(max(u16)) { fmt.eprintln("mara: too many source files"); os.exit(1) }
    file := u16(len(build_files))
    append(&build_files, f)
    if len(f.source) > int(max(u32)) { fmt.eprintfln("mara: %s is too big", f.path); os.exit(1) }
    push(&f.lines, 0)
    for c, i in transmute([]u8)f.source { if c == '\n' { push(&f.lines, u32(i + 1)) } }
    l := lexer_init(f.source, f.path)
    f.first_token = Token_Id(len(build_tokens))
    for {
        tok := next_token(&l)
        tok.id = Token_Id(len(build_tokens))   // stamp before append: its id is the current length
        tok.file = file
        if tok.kind == .String || tok.kind == .Char { build_literals[tok.id] = l.value }
        push(&build_tokens, tok)
        if tok.kind == .EOF { break }
    }
    f.end_token = Token_Id(len(build_tokens))
    f.lex_errors = l.errors
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
// ---------------------------------------------------------------------------
// Source locations and token text
// ---------------------------------------------------------------------------

// A source location, as tokens (ids in build_tokens). `at` is the REPORT POINT
// every diagnostic prints (its file, line and column: span_location). `tok` to
// `end` is a half-open range of tokens — the EXTENT, which a start point alone
// cannot express.
//
// The two are independent on purpose. A node's report point is not always its
// first token: a Binary anchors on its operator so an error lands on the
// `==` rather than the left operand. The extent still has to begin at the
// leftmost token, so `m == void` reports at the `==` but covers `m`.
//
// Extents exist for the editor queries: resolving a cursor to a node means
// asking which nodes contain a position. With token ids that is integer
// containment (tok <= i < end) rather than comparing (line, col) pairs, and
// the innermost node is simply the smallest containing range.
//
// A Span{} is no place: no report point (at = 0), and no extent (end <= tok).
// Every node of the tree has a real extent: tree_span.
Span :: struct {
    at:  Token_Id,
    tok: Token_Id,
    end: Token_Id,
}

span_file :: proc(s: Span) -> string {
    return build_files[build_tokens[s.at].file].path if s.at != 0 else ""
}

span_line :: proc(s: Span) -> int {
    return token_line(build_tokens[s.at]) if s.at != 0 else 0
}

// Source order: by file, then line, then column.
span_before :: proc(a, b: Span) -> bool {
    if span_file(a) != span_file(b) { return span_file(a) < span_file(b) }
    if span_line(a) != span_line(b) { return span_line(a) < span_line(b) }
    return span_col(a) < span_col(b)
}

span_col :: proc(s: Span) -> int {
    return token_col(build_tokens[s.at]) if s.at != 0 else 0
}

// A span's location as an error message's prefix: "[file:line:col]".
span_loc :: proc(span: Span) -> string {
    return fmt.tprintf("[%s]", span_location(span))
}

// "file:line:col" of a span's report point.
span_location :: proc(s: Span) -> string {
    return format_location(span_file(s), span_line(s), span_col(s))
}

// Format a source location as "file:line:col" or "line:col".
format_location :: proc(file: string, line: int, col: int) -> string {
    if file != "" {
        return fmt.tprintf("%s:%d:%d", file, line, col)
    }
    return fmt.tprintf("%d:%d", line, col)
}

// A token's span: its extent the token itself.
token_span :: proc(tok: Token) -> Span {
    return Span{at = tok.id, tok = tok.id, end = tok.id + 1}
}

// Map compound assignment tokens to their binary operator
compound_assign_op :: proc(kind: Token_Kind) -> (Token_Kind, bool) {
    #partial switch kind {
    case .Plus_Equal:        return .Plus, true
    case .Minus_Equal:       return .Minus, true
    case .Mul_Equal:         return .Star, true
    case .Div_Equal:         return .Slash, true
    case .Mod_Equal:         return .Modulo, true
    case .And_Equal:         return .Ampersand, true
    case .Or_Equal:          return .Pipe, true
    case .Xor_Equal:         return .Tilde, true
    case .Shift_Left_Equal:  return .Shift_Left, true
    case .Shift_Right_Equal: return .Shift_Right, true
    }
    return .EOF, false
}

// Re-escape processed literal text for display: the lexer stores '\n' as the
// raw byte, but a failure message must show the source spelling, not emit a
// real newline mid-line. Mirrors the lexer's escape set; `quote` is the
// enclosing quote character, escaped when it appears in the content.
assert_escape_literal :: proc(text: string, quote: u8) -> string {
    sb := strings.builder_make()
    for i in 0..<len(text) {
        c := text[i]
        switch {
        case c == '\n':  strings.write_string(&sb, "\\n")
        case c == '\t':  strings.write_string(&sb, "\\t")
        case c == '\r':  strings.write_string(&sb, "\\r")
        case c == '\\':  strings.write_string(&sb, "\\\\")
        case c == 0:     strings.write_string(&sb, "\\0")
        case c == quote: strings.write_byte(&sb, '\\'); strings.write_byte(&sb, quote)
        case:            strings.write_byte(&sb, c)
        }
    }
    return strings.to_string(sb)
}

// Display form of one token: char/string literals get their quotes back and
// their content re-escaped (each lexer escape was 2 source chars and
// re-escapes to 2 chars, so the display width matches the source width —
// which the spacing math below relies on).
assert_token_display :: proc(tok: Token) -> string {
    #partial switch tok.kind {
    case .Char:
        return strings.concatenate({"'", assert_escape_literal(token_text(tok), '\''), "'"})
    case .String:
        return strings.concatenate({"\"", assert_escape_literal(token_text(tok), '"'), "\""})
    }
    return token_text(tok)
}

token_range_text :: proc(lo, hi: int) -> string {
    sb := strings.builder_make()
    for i in lo..<hi {
        if i > lo {
            prev := build_tokens[i - 1]
            cur  := build_tokens[i]
            if token_line(cur) != token_line(prev) || token_col(cur) > token_col(prev) + len(assert_token_display(prev)) {
                strings.write_byte(&sb, ' ')
            }
        }
        strings.write_string(&sb, assert_token_display(build_tokens[i]))
    }
    return strings.clone(strings.to_string(sb))
}

// Outcome of parsing a Number token's text.
Number_Parse_Error :: enum {
    None,
    Invalid,        // malformed text (empty hex digits, garbage)
    Hex_Overflow,   // well-formed hex but > u64 max — beyond the simple wide-literal tier
    Dec_Overflow,   // well-formed decimal integer but > u64 max — same tier as Hex_Overflow
    Bin_Overflow,   // well-formed binary but > u64 max (more than 64 significant bits)
}

// Parse a Number token's text into both an f64 and an i128 form. Hex literals
// (`0x...`) and decimal-without-dot integers fill the i128 form exactly;
// floats fill only the f64 form (i128 is set to the truncating cast for
// fallback but should never be read when is_float is true). Integer values
// up to u64 max (`0xFFFFFFFFFFFFFFFF` / `18446744073709551615`) round-trip
// exactly; anything wider is flagged as Hex_Overflow/Dec_Overflow.
parse_number_text :: proc(text_in: string) -> (f_val: f64, i_val: i128, err: Number_Parse_Error) {
    // Strip digit-group separators (`1_000`, `0xFF_FF`, `0b1010_0000`) once, up
    // front, so every base below parses clean digits.
    text := text_in
    has_sep := false
    for i := 0; i < len(text_in); i += 1 {
        if text_in[i] == '_' { has_sep = true; break }
    }
    if has_sep {
        b: strings.Builder
        for i := 0; i < len(text_in); i += 1 {
            if text_in[i] != '_' { strings.write_byte(&b, text_in[i]) }
        }
        text = strings.to_string(b)
    }
    if len(text) > 2 && text[0] == '0' && (text[1] == 'x' || text[1] == 'X') {
        digits := text[2:]
        // More than 16 significant hex digits doesn't fit in u64. Strip leading
        // zeros first so `0x000…FFFF...F` isn't false-flagged.
        clean := digits
        for len(clean) > 0 && clean[0] == '0' { clean = clean[1:] }
        if len(clean) > 16 {
            return 0, 0, .Hex_Overflow
        }
        n, parse_ok := strconv.parse_u64_of_base(digits, 16)
        if !parse_ok {
            return 0, 0, .Invalid
        }
        return f64(n), i128(n), .None
    }
    if len(text) > 2 && text[0] == '0' && (text[1] == 'b' || text[1] == 'B') {
        digits := text[2:]
        // More than 64 significant binary digits doesn't fit in u64.
        clean := digits
        for len(clean) > 0 && clean[0] == '0' { clean = clean[1:] }
        if len(clean) > 64 {
            return 0, 0, .Bin_Overflow
        }
        n, parse_ok := strconv.parse_u64_of_base(digits, 2)
        if !parse_ok {
            return 0, 0, .Invalid
        }
        return f64(n), i128(n), .None
    }
    // Decimal: all-digits text is an integer literal — accumulate it in i128
    // so values up to u64 max round-trip exactly (strconv.parse_int caps at
    // i64 and silently wraps, which turned 18446744073709551615 into -1).
    // Anything past u64 max is Dec_Overflow, the same precision tier as hex.
    // Non-digit text (has `.`) falls back to parse_f64 — int_value gets a
    // truncating cast that shouldn't be read for is_float = true anyway.
    is_int := len(text) > 0
    for i := 0; i < len(text); i += 1 {
        if !(text[i] >= '0' && text[i] <= '9') {
            is_int = false
            break
        }
    }
    if is_int {
        DEC_U64_MAX :: i128(max(u64))
        n: i128
        for i := 0; i < len(text); i += 1 {
            n = n * 10 + i128(text[i] - '0')
            if n > DEC_U64_MAX {
                return 0, 0, .Dec_Overflow
            }
        }
        return f64(n), n, .None
    }
    f, f_ok := strconv.parse_f64(text)
    if !f_ok {
        return 0, 0, .Invalid
    }
    return f, i128(f), .None
}

