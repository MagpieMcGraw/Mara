package mara

import "core:c"
import "core:strings"
import "core:sys/posix"

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
