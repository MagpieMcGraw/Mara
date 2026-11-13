package mara

import "core:fmt"
import "core:strings"
import "core:time"
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

// A request line sent to the window listening on `name`, and its reply, to
// the end it closes the connection at — or No_Window, or Broken when one
// stops answering (VIEW_QUIET without a byte).
view_exchange :: proc(name, request: string) -> (reply: string, how: View_Exchange) {
    path := win32.utf8_to_wstring(strings.concatenate({`\\.\pipe\`, name}, context.temp_allocator))
    pipe := win32.INVALID_HANDLE_VALUE
    for _ in 0 ..< 5 {
        pipe = win32.CreateFileW(path, win32.GENERIC_READ | win32.GENERIC_WRITE, 0, nil, win32.OPEN_EXISTING, 0, nil)
        if pipe != win32.INVALID_HANDLE_VALUE || win32.GetLastError() != win32.ERROR_PIPE_BUSY { break }
        win32.WaitNamedPipeW(path, 1000)   // (each one taken, between one accept and the next)
    }
    if pipe == win32.INVALID_HANDLE_VALUE { return "", .No_Window }
    defer win32.CloseHandle(pipe)
    line := strings.concatenate({request, "\n"}, context.temp_allocator)
    wrote: win32.DWORD
    if !win32.WriteFile(pipe, raw_data(line), win32.DWORD(len(line)), &wrote, nil) || int(wrote) != len(line) { return "", .Broken }
    b := strings.builder_make()
    buf: [4096]byte
    quiet := time.tick_now()
    for {
        waiting: u32
        if !win32.PeekNamedPipe(pipe, nil, 0, nil, &waiting, nil) {
            if win32.GetLastError() == win32.ERROR_BROKEN_PIPE { return strings.to_string(b), .Answered }   // (closed: the end)
            return "", .Broken
        }
        if waiting == 0 {
            if time.tick_since(quiet) > VIEW_QUIET { return "", .Broken }
            win32.Sleep(2)
            continue
        }
        got: win32.DWORD
        if !win32.ReadFile(pipe, &buf[0], min(waiting, u32(len(buf))), &got, nil) { return "", .Broken }
        strings.write_bytes(&b, buf[:got])
        quiet = time.tick_now()
    }
}
