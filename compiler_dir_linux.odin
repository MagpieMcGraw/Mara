package mara

import "core:os"
import "core:path/filepath"

// Directory containing the compiler executable. /proc/self/exe is a symlink
// to the real path of the running binary on Linux — works regardless of how
// the process was invoked.
get_compiler_dir :: proc() -> string {
    if exe_path, err := os.read_link("/proc/self/exe", context.allocator); err == nil {
        dir := filepath.dir(exe_path)
        if dir != "" { return dir }
    }
    dir := filepath.dir(os.args[0])
    if dir == "" { dir = "." }
    return dir
}
