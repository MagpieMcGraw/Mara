package mara

import "core:c"
import "core:os"
import "core:strings"
import "core:sys/posix"
import "core:time"

// Starts exe with args on its own, to outlive this process and the
// terminal: in a session of its own (setsid), so the terminal closing
// doesn't hang up on it, its input and output /dev/null. In the current
// directory. False when it couldn't start — the exec's failure too, told
// through a pipe that closes when the exec runs.
start_detached :: proc(exe: string, args: []string) -> bool {
    argv := make([]cstring, len(args) + 2, context.temp_allocator)   // (its last nil)
    argv[0] = strings.clone_to_cstring(exe, context.temp_allocator)
    for a, i in args { argv[i + 1] = strings.clone_to_cstring(a, context.temp_allocator) }
    failed: [2]posix.FD
    if posix.pipe(&failed) != .OK { return false }
    for fd in failed { _ = posix.fcntl(fd, .SETFD, c.int(posix.FD_CLOEXEC)) }
    pid := posix.fork()
    if pid == 0 {
        _ = posix.close(failed[0])
        _ = posix.setsid()
        null := posix.open("/dev/null", {.RDWR})
        if null >= 0 {
            _ = posix.dup2(null, 0)
            _ = posix.dup2(null, 1)
            _ = posix.dup2(null, 2)
        }
        _ = posix.execv(argv[0], raw_data(argv))
        one := [1]byte{1}
        _ = posix.write(failed[1], &one[0], 1)   // (the exec failed)
        posix._exit(127)
    }
    _ = posix.close(failed[1])
    if pid < 0 {
        _ = posix.close(failed[0])
        return false
    }
    got: [1]byte
    n := posix.read(failed[0], &got[0], 1)   // (0 bytes: closed by the exec — it runs)
    _ = posix.close(failed[0])
    return n == 0
}

// A request line sent to the window listening on `name` (a Unix socket,
// where os.mara's pipe_listen puts it), and its reply, to the end it closes
// the connection at — or No_Window, or Broken when one stops answering
// (VIEW_QUIET without a byte).
view_exchange :: proc(name, request: string) -> (reply: string, how: View_Exchange) {
    dir := os.get_env("XDG_RUNTIME_DIR", context.temp_allocator)
    if dir == "" { dir = "/tmp" }
    path := strings.concatenate({dir, "/", name, ".sock"}, context.temp_allocator)
    at := posix.sockaddr_un{sun_family = .UNIX}
    if len(path) >= len(at.sun_path) { return "", .No_Window }
    copy(at.sun_path[:], transmute([]u8)path)
    fd := posix.socket(.UNIX, .STREAM)
    if fd < 0 { return "", .No_Window }
    defer posix.close(fd)
    if posix.connect(fd, (^posix.sockaddr)(&at), posix.socklen_t(size_of(at))) != .OK { return "", .No_Window }
    line := strings.concatenate({request, "\n"}, context.temp_allocator)
    // (NOSIGNAL: a window gone is a failed send, not SIGPIPE ending us.)
    if posix.send(fd, raw_data(line), len(line), {.NOSIGNAL}) != len(line) { return "", .Broken }
    b := strings.builder_make()
    buf: [4096]byte
    for {
        ready := posix.pollfd{fd = fd, events = {.IN}}
        if posix.poll(&ready, 1, c.int(VIEW_QUIET / time.Millisecond)) <= 0 { return "", .Broken }
        got := posix.read(fd, &buf[0], len(buf))
        if got < 0 { return "", .Broken }
        if got == 0 { return strings.to_string(b), .Answered }   // (closed: the end)
        strings.write_bytes(&b, buf[:got])
    }
}
