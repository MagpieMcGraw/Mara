package mara

import "core:os"
import "core:path/filepath"

// The compiler executable's path. /proc/self/exe is a symlink to the real
// path of the running binary on Linux — works regardless of how the process
// was invoked.
get_compiler_exe :: proc() -> string {
    if exe_path, err := os.read_link("/proc/self/exe", context.allocator); err == nil && exe_path != "" {
        return exe_path
    }
    return os.args[0]
}

// Directory containing the compiler executable.
get_compiler_dir :: proc() -> string {
    dir := filepath.dir(get_compiler_exe())
    if dir == "" { dir = "." }
    return dir
}
