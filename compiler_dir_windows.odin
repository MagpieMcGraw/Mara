package mara

import "core:os"
import "core:path/filepath"
import win32 "core:sys/windows"

// The compiler executable's path. GetModuleFileNameW returns the real path
// regardless of how Mara was invoked (PATH lookup, full path, symlink).
get_compiler_exe :: proc() -> string {
    buf: [512]u16
    ret := win32.GetModuleFileNameW(nil, &buf[0], 512)
    if ret > 0 {
        exe_path, _ := win32.utf16_to_utf8(buf[:ret], context.allocator)   // (kept: serve frees temp after each answer)
        if exe_path != "" { return exe_path }
    }
    return os.args[0]
}

// When the file at path was last written, in unix nanoseconds; false when
// there's none. (Its attributes only: the file isn't opened — opening an exe
// can wake the antivirus.)
file_written :: proc(path: string) -> (i64, bool) {
    data: win32.WIN32_FILE_ATTRIBUTE_DATA
    if !win32.GetFileAttributesExW(win32.utf8_to_wstring(path, context.temp_allocator), win32.GetFileExInfoStandard, &data) { return 0, false }
    return win32.FILETIME_as_unix_nanoseconds(data.ftLastWriteTime), true
}

// Directory containing the compiler executable.
get_compiler_dir :: proc() -> string {
    dir := filepath.dir(get_compiler_exe())
    if dir == "" { dir = "." }
    return dir
}
