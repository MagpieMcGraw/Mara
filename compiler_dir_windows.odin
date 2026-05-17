package mara

import "core:os"
import "core:path/filepath"
import win32 "core:sys/windows"

// Directory containing the compiler executable. GetModuleFileNameW returns the
// real path regardless of how Mara was invoked (PATH lookup, full path, symlink).
get_compiler_dir :: proc() -> string {
    buf: [512]u16
    ret := win32.GetModuleFileNameW(nil, &buf[0], 512)
    if ret > 0 {
        exe_path, _ := win32.utf16_to_utf8(buf[:ret])
        dir := filepath.dir(exe_path)
        if dir != "" { return dir }
    }
    dir := filepath.dir(os.args[0])
    if dir == "" { dir = "." }
    return dir
}
