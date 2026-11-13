package mara

import "core:sys/posix"

// Whether stdin has bytes waiting to be read: a look that doesn't wait.
stdin_waiting :: proc() -> bool {
    fds := [1]posix.pollfd{{fd = 0, events = {.IN}}}
    return posix.poll(&fds[0], 1, 0) > 0
}
