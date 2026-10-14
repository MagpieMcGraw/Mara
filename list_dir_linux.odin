package mara

import "core:os"
import "core:time"

// A folder's entries. (Here os.read_dir opens each only as a path, O_PATH:
// nothing is read, nothing scanned — list_dir_windows.odin is why it matters.)
list_dir :: proc(dir: string, allocator := context.allocator) -> []Dir_Item {
    dh, err := os.open(dir)
    if err != nil { return nil }
    defer os.close(dh)
    entries, _ := os.read_dir(dh, -1, allocator)
    items := make([]Dir_Item, len(entries), allocator)
    for e, k in entries {
        items[k] = {name = e.name, dir = e.type == .Directory, size = e.size, written = time.time_to_unix_nano(e.modification_time)}
    }
    return items
}
