package mara

import "base:runtime"
import "core:mem/virtual"

// ---------------------------------------------------------------------------
// FFI helper: per-compilation context for non-Odin callers.
//
// Foreign callers (Mara front-end, C tool, etc.) can't construct an Odin
// `runtime.Context` themselves — they don't know its layout. This file
// exports one tiny `proc "c"` to make one, and a matching destroy.
//
// Everything else the compiler exposes (lex_all, parser_init, parse_program,
// check_program, generate_program) stays `proc "odin"` with its natural
// signature; foreign callers declare it in their own foreign block with the
// context as the trailing parameter and call it directly. No per-function
// wrappers, no opaque-handle bookkeeping.
//
// Memory model: the context's allocator is a growing arena. Every allocation
// done by later compiler stages lands in that arena. mara_destroy_context
// releases the whole thing in one shot — no per-stage teardown.
// ---------------------------------------------------------------------------

Mara_Compile_Ctx :: struct {
    arena:    virtual.Arena,
    odin_ctx: runtime.Context,
}

@(export, link_name="mara_make_context")
mara_make_context_export :: proc "c" () -> ^Mara_Compile_Ctx {
    context = runtime.default_context()
    cctx := new(Mara_Compile_Ctx)
    if virtual.arena_init_growing(&cctx.arena) != nil {
        free(cctx)
        return nil
    }
    cctx.odin_ctx = context
    cctx.odin_ctx.allocator = virtual.arena_allocator(&cctx.arena)
    return cctx
}

@(export, link_name="mara_destroy_context")
mara_destroy_context_export :: proc "c" (cctx: ^Mara_Compile_Ctx) {
    if cctx == nil { return }
    context = runtime.default_context()
    virtual.arena_destroy(&cctx.arena)
    free(cctx)
}
