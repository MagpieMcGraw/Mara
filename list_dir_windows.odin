package mara

import "core:strings"
import win32 "core:sys/windows"

// A folder's entries as its listing has them — none of them opened. (Odin's
// os.read_dir opens each entry on Windows, for its file id, and a file opened
// is a file the antivirus scans: test_1M.exe, 64 MB, just linked beside the
// sources, cost each of the next few builds ~1.2 s of "discover".)
list_dir :: proc(dir: string, allocator := context.allocator) -> []Dir_Item {
    pattern := win32.utf8_to_wstring(strings.concatenate({dir, `\*`}, context.temp_allocator), context.temp_allocator)
    found: win32.WIN32_FIND_DATAW
    h := win32.FindFirstFileW(pattern, &found)
    if h == win32.INVALID_HANDLE_VALUE { return nil }
    defer win32.FindClose(h)
    items := make([dynamic]Dir_Item, allocator)
    for {
        name, _ := win32.wstring_to_utf8(cstring16(&found.cFileName[0]), -1, allocator)
        if name != "." && name != ".." {
            append(&items, Dir_Item{
                name    = name,
                dir     = found.dwFileAttributes & win32.FILE_ATTRIBUTE_DIRECTORY != 0,
                size    = i64(found.nFileSizeHigh) << 32 | i64(found.nFileSizeLow),
                written = win32.FILETIME_as_unix_nanoseconds(found.ftLastWriteTime),
            })
        }
        if !win32.FindNextFileW(h, &found) { break }
    }
    return items[:]
}
