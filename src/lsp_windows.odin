package mara

import win32 "core:sys/windows"

// Whether stdin has bytes waiting to be read — a pipe's, as an editor runs
// `mara lsp`; a console's, never said so.
stdin_waiting :: proc() -> bool {
    waiting: win32.DWORD
    if !win32.PeekNamedPipe(win32.GetStdHandle(win32.STD_INPUT_HANDLE), nil, 0, nil, &waiting, nil) { return false }
    return waiting > 0
}
