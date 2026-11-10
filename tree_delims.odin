package mara

import "core:fmt"
import "core:strings"

// A file's brackets checked before it is parsed: every `(`, `[` and `{`
// against the closer that ends it. The parser meets a missing one late —
// at the file's end, or wherever the next thing stops making sense — and can
// only say what it expected there. This says which bracket it is.
//
// One finding a file, its first:
//   - an opener never closed: another's closer, or the file's end, comes
//     first. Reported at the opener.
//   - a closer with no opener to close. Reported at the closer.
// A `{` is hard to tell that way: with a `}` missing, each `}` after it
// closes the block before its own, and the one left open at the file's end
// is the outermost. So a `}` that starts its line indented differently from
// the line of the `{` it closes marks that `{` as the likely one.

// What the check found: its message, where it's reported, and the token
// the parser's own errors are a consequence of from then on (delims_quiet).
Delims_Finding :: struct {
    at:      int,      // the token it's reported at; -1: none, the brackets match
    message: string,
}

@(private="file")
Delim_Open :: struct {
    tok:   int,
    close: Token_Kind,
}

// The file's brackets matched: its first finding (at -1: none).
delims_check :: proc(tokens: []Token, first: int) -> Delims_Finding {
    open := make([dynamic]Delim_Open, context.temp_allocator)
    // The first `{` closed by a `}` not lined up with it, and that `}`.
    odd_open, odd_close := -1, -1
    for pos in first ..< len(tokens) {
        kind := tokens[pos].kind
        #partial switch kind {
        case .Left_Paren:   append(&open, Delim_Open{pos, .Right_Paren})
        case .Left_Bracket: append(&open, Delim_Open{pos, .Right_Bracket})
        case .Left_Brace:   append(&open, Delim_Open{pos, .Right_Brace})
        case .Right_Paren, .Right_Bracket, .Right_Brace:
            if len(open) > 0 && open[len(open) - 1].close == kind {
                top := pop(&open)
                if kind == .Right_Brace && odd_open < 0 && !delims_lined_up(tokens[top.tok], tokens[pos]) {
                    odd_open, odd_close = top.tok, pos
                }
                continue
            }
            // Not the innermost's closer. An opener further out that it does
            // close: the innermost is the one never closed. None: it closes
            // nothing.
            closes_outer := false
            for o in open { if o.close == kind { closes_outer = true } }
            closer := token_shown(tokens[pos])
            if closes_outer {
                top := open[len(open) - 1]
                return {top.tok, fmt.aprintf(PARSE_NEVER_CLOSED, token_shown(tokens[top.tok]), kind_shown(top.close), closer, delims_where(tokens[pos]))}
            }
            b := strings.builder_make()
            fmt.sbprintf(&b, PARSE_CLOSES_NOTHING, closer, kind_shown(delims_opener(kind)))
            if odd_open >= 0 && kind == .Right_Brace {
                fmt.sbprintf(&b, PARSE_ODD_CLOSE_BEFORE, delims_where(tokens[odd_close]), delims_where(tokens[odd_open]))
            }
            return {pos, strings.to_string(b)}
        }
    }
    if len(open) == 0 { return {at = -1} }
    top := open[len(open) - 1]
    if top.close == .Right_Brace && odd_open >= 0 {
        return {odd_open, fmt.aprintf(PARSE_BRACE_LIKELY_OPEN, delims_where(tokens[odd_close]), delims_where(tokens[top.tok]))}
    }
    return {top.tok, fmt.aprintf(PARSE_NEVER_CLOSED_AT_END, token_shown(tokens[top.tok]), kind_shown(top.close))}
}

// Whether a `}` is lined up with the `{` it closes: on its line, or not the
// first thing on its own line (nothing to line up), or its line indented as
// the `{`'s line is.
@(private="file")
delims_lined_up :: proc(open, close: Token) -> bool {
    if token_line(open) == token_line(close) { return true }
    close_lead, first := line_lead(close)
    if !first { return true }
    open_lead, _ := line_lead(open)
    return open_lead == close_lead
}

@(private="file")
delims_opener :: proc(close: Token_Kind) -> Token_Kind {
    #partial switch close {
    case .Right_Paren:   return .Left_Paren
    case .Right_Bracket: return .Left_Bracket
    }
    return .Left_Brace
}

// A token's place, as a message says it: `line:column`.
delims_where :: proc(t: Token) -> string {
    return fmt.aprintf("%d:%d", token_line(t), token_col(t))
}

// The opener a closer expected at `pos` would close: the nearest before it
// left open, of its kind; -1 for none.
delims_opener_before :: proc(tokens: []Token, first, pos: int, close: Token_Kind) -> int {
    opener := delims_opener(close)
    depth := 0
    for at := pos - 1; at >= first; at -= 1 {
        if tokens[at].kind == close {
            depth += 1
        } else if tokens[at].kind == opener {
            if depth == 0 { return at }
            depth -= 1
        }
    }
    return -1
}

// A kind of token, as a message names it: its text in backquotes; what it
// is, for one with no text of its own.
kind_shown :: proc(kind: Token_Kind) -> string {
    #partial switch kind {
    case .Identifier: return "a name"
    case .Number:     return "a number"
    case .String:     return "a text"
    case .Char:       return "a character"
    case .Newline:    return "the line's end"
    case .EOF:        return "the file's end"
    }
    return fmt.aprintf("`%s`", TOKEN_TEXTS[kind][0])
}

// A token, as a message shows the one it found: as it's written, in
// backquotes — a text in its quotes, a long one cut short.
token_shown :: proc(t: Token) -> string {
    #partial switch t.kind {
    case .Newline, .EOF: return kind_shown(t.kind)
    case .String:
        text := token_text(t)
        if len(text) > 24 {
            cut := 24
            for cut > 0 && text[cut] & 0xC0 == 0x80 { cut -= 1 }   // (not within a character)
            text = strings.concatenate({text[:cut], "…"})
        }
        return fmt.aprintf("`\"%s\"`", text)
    case .Char: return fmt.aprintf("`'%s'`", token_text(t))
    }
    return fmt.aprintf("`%s`", token_text(t))
}

// Whether a token can begin a value: after one, in a list, a `,` may be
// what's missing.
token_starts_value :: proc(kind: Token_Kind) -> bool {
    #partial switch kind {
    case .Identifier, .Number, .String, .Char, .True, .False, .Minus, .Not, .Ampersand, .Dot: return true
    }
    return false
}
