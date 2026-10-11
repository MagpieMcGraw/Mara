package mara

import "core:fmt"
import "core:hash"
import "core:os"
import "core:strings"
import "core:time"

// ---------------------------------------------------------------------------
// The window (`mara view`) as `mara ask`'s answerer. A window open on a
// module listens on its pipe name (view_pipe_name, given it by `mara view`);
// each connection sends one line, a query as `mara ask` takes it, and gets
// what the window's `mara serve` answers, its end line too; then the window
// closes the connection.
// ---------------------------------------------------------------------------

// How long `mara ask` waits for a window's next byte before it checks here
// instead. (A re-check of a big program takes seconds.)
VIEW_QUIET :: 30 * time.Second

// How a request to a window went.
View_Exchange :: enum {
    Answered,
    No_Window,   // none listens on the name
    Broken,      // one did, then stopped answering
}

// The pipe name a window on `module`, opened here by this compiler, listens
// on: the module, then a hash of the directory and the compiler's path (on
// Windows case folded: one path however it's spelled) — so windows on two
// checkouts, or opened by two compilers, never meet.
view_pipe_name :: proc(module: string) -> string {
    cwd, _ := os.get_working_directory(context.temp_allocator)
    key := strings.concatenate({cwd, "\x00", get_compiler_exe()}, context.temp_allocator)
    when ODIN_OS == .Windows { key = strings.to_lower(key, context.temp_allocator) }
    return fmt.aprintf("mara-view-%s-%016x", module, hash.fnv64a(transmute([]byte)key))
}

// `mara ask`'s query asked of the window open here on its module, when one
// is: the answer, and whether it failed. ok false when no window answers —
// none open, or one that stopped answering or cut its answer off: the check
// here answers then.
ask_via_view :: proc(args: CLI_Args) -> (answer: string, failed: bool, ok: bool) {
    b := strings.builder_make(context.temp_allocator)
    for w, i in args.ask_words {
        if i > 0 { strings.write_byte(&b, ' ') }
        // (A word with a space in it, quoted: still one word to ask_words.)
        if strings.index_any(w, " \t") >= 0 { fmt.sbprintf(&b, `"%s"`, w) } else { strings.write_string(&b, w) }
    }
    reply, how := view_exchange(view_pipe_name(args.pkg_name), strings.to_string(b))
    if how == .No_Window { return }
    // (Its last line ends it: the answer is before.)
    body := strings.trim_suffix(reply, "\n")
    at := strings.last_index_byte(body, '\n') + 1
    switch body[at:] {
    case ASK_DONE:   return body[:at], false, true
    case ASK_FAILED: return body[:at], true, true
    }
    // (A window that stopped answering, or cut its answer off: said, then
    // the check here answers.)
    fmt.eprintln("mara ask: the window open here didn't answer; checking here instead")
    return "", false, false
}
