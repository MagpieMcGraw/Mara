package mara

import "core:strings"
import "core:sys/linux"

// A folder's entries as its listing has them — none of them opened, each
// looked at (fstatat) for whether it's a folder, its size and when it was
// written. One gone by then is left out. (Odin's os.read_dir opens each,
// and when one has gone since the listing it gives back none at all: a
// build beside this one deleting its own files had `mara build` find an
// empty folder.)
list_dir :: proc(dir: string, allocator := context.allocator) -> []Dir_Item {
    dfd, err := linux.open(strings.clone_to_cstring(dir, context.temp_allocator), {.DIRECTORY, .CLOEXEC})
    if err != .NONE { return nil }
    defer linux.close(dfd)
    items := make([dynamic]Dir_Item, allocator)
    buf: [8192]u8
    for {
        n, e := linux.getdents(dfd, buf[:])
        if e != .NONE || n <= 0 { break }
        offset := 0
        for d in linux.dirent_iterate_buf(buf[:n], &offset) {
            name := linux.dirent_name(d)
            if name == "." || name == ".." { continue }
            st: linux.Stat
            if linux.fstatat(dfd, cstring(raw_data(name)), &st, {}) != .NONE { continue }   // (gone since)
            append(&items, Dir_Item{
                name    = strings.clone(name, allocator),
                dir     = linux.S_ISDIR(st.mode),
                size    = i64(st.size),
                written = i64(st.mtime.time_sec) * 1_000_000_000 + i64(st.mtime.time_nsec),
            })
        }
    }
    return items[:]
}
