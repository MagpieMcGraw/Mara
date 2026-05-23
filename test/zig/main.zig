const std = @import("std");

const Config = struct {
    name: []const u8,
    next: ?*Config,
};

pub fn main() void {
    var root: Config = undefined;
    root.name = "root";

    var it: ?*Config = &root;
    while (it) |c| {
        std.debug.print("{s}\n", .{c.name});
        it = c.next;
    }
}
