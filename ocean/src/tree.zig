// NONOS Operating System (AGPL-3.0-or-later)
//! The note tree as GoldilocksIncrementalTree keeps it: depth 32, zeros[0] = 0,
//! zeros[l + 1] = compress(zeros[l], zeros[l]), leaves appended left to right.
//! Every level is stored, so a witness for any past leaf costs depth reads.

const std = @import("std");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;
const Allocator = std.mem.Allocator;
const List = std.ArrayListUnmanaged(Digest);

pub const DEPTH = 32;
pub const CAPACITY: usize = 1 << DEPTH;

pub const Error = error{ TreeFull, IndexOutOfRange } || Allocator.Error;

pub const Witness = struct {
    leaf_index: u64,
    siblings: [DEPTH]Digest,
};

pub const Tree = struct {
    alloc: Allocator,
    h: *const Poseidon,
    zeros: [DEPTH + 1]Digest,
    levels: [DEPTH + 1]List,

    pub fn init(alloc: Allocator, h: *const Poseidon) Tree {
        var t: Tree = .{ .alloc = alloc, .h = h, .zeros = undefined, .levels = undefined };
        t.zeros[0] = digest.ZERO;
        for (0..DEPTH) |l| t.zeros[l + 1] = h.compress(&t.zeros[l], &t.zeros[l]);
        for (0..DEPTH + 1) |l| t.levels[l] = .{};
        return t;
    }

    pub fn deinit(self: *Tree) void {
        for (0..DEPTH + 1) |l| self.levels[l].deinit(self.alloc);
    }

    pub fn len(self: *const Tree) usize {
        return self.levels[0].items.len;
    }

    fn node(self: *const Tree, level: usize, idx: usize) Digest {
        const items = self.levels[level].items;
        return if (idx < items.len) items[idx] else self.zeros[level];
    }

    pub fn leaf(self: *const Tree, index: usize) Error!Digest {
        if (index >= self.len()) return error.IndexOutOfRange;
        return self.levels[0].items[index];
    }

    pub fn root(self: *const Tree) Digest {
        return self.node(DEPTH, 0);
    }

    /// Capacity is reserved on every level first, so a failed allocation
    /// leaves the tree exactly as it was.
    pub fn insert(self: *Tree, cm: Digest) Error!usize {
        const index = self.len();
        if (index >= CAPACITY) return error.TreeFull;
        for (0..DEPTH + 1) |l| {
            const need = (index >> @intCast(l)) + 1;
            try self.levels[l].ensureTotalCapacity(self.alloc, need);
        }
        self.levels[0].appendAssumeCapacity(cm);
        var idx = index;
        for (1..DEPTH + 1) |l| {
            idx >>= 1;
            const v = self.h.compress(&self.node(l - 1, 2 * idx), &self.node(l - 1, 2 * idx + 1));
            const items = self.levels[l].items;
            if (idx < items.len) {
                items[idx] = v;
            } else {
                self.levels[l].appendAssumeCapacity(v);
            }
        }
        return index;
    }

    pub fn witness(self: *const Tree, index: usize) Error!Witness {
        if (index >= self.len()) return error.IndexOutOfRange;
        var w: Witness = .{ .leaf_index = index, .siblings = undefined };
        for (0..DEPTH) |l| w.siblings[l] = self.node(l, (index >> @intCast(l)) ^ 1);
        return w;
    }
};

/// Fold a leaf up a witness. Bit l of the index set puts the running node on
/// the right, the direction the circuit's openings carry.
pub fn rootOf(h: *const Poseidon, w: *const Witness, leaf: *const Digest) Digest {
    var cur = leaf.*;
    for (0..DEPTH) |l| {
        const right = ((w.leaf_index >> @intCast(l)) & 1) == 1;
        cur = if (right) h.compress(&w.siblings[l], &cur) else h.compress(&cur, &w.siblings[l]);
    }
    return cur;
}
