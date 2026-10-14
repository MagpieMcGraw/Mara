package mara

import "core:mem"
import "core:mem/virtual"

// Scratch memory for one thread's short-lived lists — a parse's: each
// allocation where the last one ended, the newest grown in place, an older
// one copied anew when it grows; all of it let go of at once (bump_reset).
// No locking, no blocks: address space reserved once, committed as it
// fills. (virtual.Arena locks on every allocation.)
Bump :: struct {
    base:       [^]byte,
    reserved:   uint,
    committed:  uint,
    last, used: uint,   // its newest allocation: [last, used)
}

@(private="file")
BUMP_RESERVE :: uint(4) << 30
@(private="file")
BUMP_COMMIT :: uint(1) << 20

bump_allocator :: proc(b: ^Bump) -> mem.Allocator {
    return {procedure = bump_proc, data = b}
}

// Everything let go of: the next allocation starts at the beginning again.
bump_reset :: proc(b: ^Bump) {
    b.last, b.used = 0, 0
}

bump_destroy :: proc(b: ^Bump) {
    if b.base != nil { virtual.release(b.base, b.reserved) }
    b^ = {}
}

@(private="file")
bump_proc :: proc(data: rawptr, mode: mem.Allocator_Mode, size, alignment: int,
                  old_memory: rawptr, old_size: int, loc := #caller_location) -> (memory: []byte, err: mem.Allocator_Error) {
    b := (^Bump)(data)
    // (The newest allocation to end at `end`, committed — zero past `from`
    // when asked.)
    end_at :: proc(b: ^Bump, end, from: uint, zero: bool) -> mem.Allocator_Error {
        if end > b.reserved { return .Out_Of_Memory }
        if end > b.committed {
            to := min(mem.align_forward_uint(end, BUMP_COMMIT), b.reserved)
            virtual.commit(b.base[b.committed:], to - b.committed) or_return
            b.committed = to
        }
        if zero && end > from { mem.zero(b.base[from:], int(end - from)) }
        b.used = end
        return nil
    }
    switch mode {
    case .Alloc, .Alloc_Non_Zeroed:
        if b.base == nil {
            space := virtual.reserve(BUMP_RESERVE) or_return
            b.base, b.reserved = raw_data(space), uint(len(space))
        }
        start := mem.align_forward_uint(b.used, uint(alignment))
        end_at(b, start + uint(size), start, mode == .Alloc) or_return
        b.last = start
        return b.base[start:][:size], nil
    case .Resize, .Resize_Non_Zeroed:
        if old_memory == nil {
            return bump_proc(data, .Alloc if mode == .Resize else .Alloc_Non_Zeroed, size, alignment, nil, 0, loc)
        }
        start := uint(uintptr(old_memory) - uintptr(b.base))
        if start == b.last && start + uint(old_size) == b.used {   // (the newest: in place)
            end_at(b, start + uint(size), start + uint(old_size), mode == .Resize) or_return
            return b.base[start:][:size], nil
        }
        // (An older one: anew, its bytes copied.)
        fresh := bump_proc(data, .Alloc_Non_Zeroed, size, alignment, nil, 0, loc) or_return
        copy(fresh, ([^]byte)(old_memory)[:min(old_size, size)])
        if mode == .Resize && size > old_size { mem.zero(raw_data(fresh[old_size:]), size - old_size) }
        return fresh, nil
    case .Free:
        // (The newest given back; one before it stays where it is.)
        if old_memory != nil && uint(uintptr(old_memory) - uintptr(b.base)) == b.last { b.used = b.last }
        return nil, nil
    case .Free_All:
        bump_reset(b)
        return nil, nil
    case .Query_Features:
        if set := (^mem.Allocator_Mode_Set)(old_memory); set != nil {
            set^ = {.Alloc, .Alloc_Non_Zeroed, .Resize, .Resize_Non_Zeroed, .Free, .Free_All, .Query_Features}
        }
        return nil, nil
    case .Query_Info:
        return nil, .Mode_Not_Implemented
    }
    return nil, nil
}
