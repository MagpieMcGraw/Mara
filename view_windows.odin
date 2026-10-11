package mara

import "core:fmt"
import "core:strings"
import win32 "core:sys/windows"

// Starts exe with args on its own, to outlive this process and the
// terminal: with no console (DETACHED_PROCESS), so the terminal closing
// doesn't end it; inheriting none of our handles; and out of any job that
// would end it with us, when the job lets it go. In the current directory.
// False when it couldn't start.
start_detached :: proc(exe: string, args: []string) -> bool {
    b := strings.builder_make(context.temp_allocator)
    fmt.sbprintf(&b, `"%s"`, exe)
    for a in args { fmt.sbprintf(&b, ` "%s"`, a) }
    line := win32.utf8_to_wstring(strings.to_string(b))   // (a copy: CreateProcessW may write to it)
    start := win32.STARTUPINFOW{cb = size_of(win32.STARTUPINFOW)}
    info: win32.PROCESS_INFORMATION
    started := win32.CreateProcessW(nil, line, nil, nil, false, win32.DETACHED_PROCESS | win32.CREATE_BREAKAWAY_FROM_JOB, nil, nil, &start, &info)
    if !started {   // (a job that won't let it go: in the job, then)
        started = win32.CreateProcessW(nil, line, nil, nil, false, win32.DETACHED_PROCESS, nil, nil, &start, &info)
    }
    if !started { return false }
    win32.CloseHandle(info.hProcess)
    win32.CloseHandle(info.hThread)
    return true
}
