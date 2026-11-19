package mara

import "core:fmt"
import "core:strings"

// requires.odin — what a tool's check makes of a name nothing defines yet.
//
// A body sees the rest of the program through heads. A call of a fun that
// isn't there has no head to see — but the call says what it needs of one:
// its params, what's passed; its result, what the call's value is used as
// (none, where it's dropped). So a tool's check gives the call a head made
// of that (a required fun) and the body checks as if the fun were there: it
// is lowered and answered from like any other, and what uses it never
// knows. The need is kept (TC.required) and said after an answer — the
// signature to write. Once the fun is written, the call is checked against
// it as any call is: a need it doesn't meet is that call's error then.
//
// A build still stops at the call: there is nothing to run.

// A fun a call needs, that nothing defines.
Required :: struct {
    name: string,
    at:   Span,          // the call
    ft:   ^Type_Scope,   // its head, as the call needs it
    by:   ^Type_Scope,   // the body calling it
}

// The head a call of an undefined fun needs — nil when a build's check is
// asked, or the call's value is used where nothing says what type it is
// (`x := f()`): then the call is the error it was.
tc_required_fun :: proc(k: ^TC, n: Tree_Id, name: string, args: []Tree_Id, span: Span) -> ^Type_Scope {
    if !k.run.partial { return nil }
    result: Type
    if n != k.dropped {
        if k.hint == nil || is_infer(k.hint) || is_any(k.hint) { return nil }
        if _, failed := k.hint.(Type_Error); failed { return nil }
        result = k.hint
    }
    ft := new(Type_Scope)
    ft.kind = .Fun
    ft.name, ft.source_name, ft.home_package = name, name, k.pkg
    ft.origin = Origin_Required{}
    hint := k.hint
    for a, i in args {
        k.hint = nil
        at := solidify_type(tc_check(k, a))
        if _, failed := at.(Type_Error); failed || at == nil { k.hint = hint; return nil }
        append(&ft.params, Struct_Type_Field{name = fmt.aprintf("a%d", i + 1), type_ = at})
    }
    k.hint = hint
    if result != nil { append(&ft.return_types, result) }
    append(&k.required, Required{name, span, ft, k.body})
    check_warning(k.c, span, WARN_NOT_DEFINED_NEEDED, name, required_text(name, ft))
    return ft
}

// A required fun as it would be written: `name :: fun(a1: T, a2: U) -> R`.
required_text :: proc(name: string, ft: ^Type_Scope) -> string {
    b := strings.builder_make(context.temp_allocator)
    fmt.sbprintf(&b, "%s :: fun(", name)
    for p, i in ft.params {
        if i > 0 { strings.write_string(&b, ", ") }
        fmt.sbprintf(&b, "%s: %s", p.name, type_name(p.type_))
    }
    strings.write_byte(&b, ')')
    if len(ft.return_types) > 0 { fmt.sbprintf(&b, " -> %s", type_name(ft.return_types[0])) }
    return strings.to_string(b)
}
