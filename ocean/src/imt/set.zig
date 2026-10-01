// NONOS Operating System (AGPL-3.0-or-later)
//! The set as a settler holds it: every leaf, and the tree over their hashes.
//!
//! Callers replay it from the nullifiers a batch publishes, which is why those
//! are calldata rather than storage. A set that cannot be rebuilt from L1
//! makes whoever has been accumulating it a liveness dependency for everyone's
//! funds.

const std = @import("std");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const Leaf = @import("leaf.zig").Leaf;
const order = @import("order.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;
const Allocator = std.mem.Allocator;

/// One depth for both trees, so a reader never has to ask which tree a path
/// belongs to.
pub const DEPTH: usize = 32;

pub const Error = error{
    OutOfOrder,
    AlreadyPresent,
    NoLowLeaf,
    IndexOutOfRange,
    SetFull,
} || Allocator.Error;

pub const Absent = struct {
    index: usize,
    leaf: Leaf,
};

pub const Set = struct {
    alloc: Allocator,
    h: *const Poseidon,
    leaves: std.ArrayListUnmanaged(Leaf),
    zeros: [DEPTH + 1]Digest,
    levels: [DEPTH + 1]std.ArrayListUnmanaged(Digest),

    pub fn init(alloc: Allocator, h: *const Poseidon) Error!Set {
        var s: Set = .{
            .alloc = alloc,
            .h = h,
            .leaves = .{},
            .zeros = undefined,
            .levels = undefined,
        };
        for (0..DEPTH + 1) |l| s.levels[l] = .{};
        s.zeros[0] = Leaf.empty().hash(h);
        for (0..DEPTH) |l| s.zeros[l + 1] = h.compress(&s.zeros[l], &s.zeros[l]);
        errdefer s.deinit();
        _ = try s.append(Leaf.sentinel());
        return s;
    }

    pub fn deinit(self: *Set) void {
        self.leaves.deinit(self.alloc);
        for (0..DEPTH + 1) |l| self.levels[l].deinit(self.alloc);
    }

    pub fn len(self: *const Set) usize {
        return self.leaves.items.len;
    }

    pub fn at(self: *const Set, index: usize) Error!Leaf {
        if (index >= self.len()) return error.IndexOutOfRange;
        return self.leaves.items[index];
    }

    fn node(self: *const Set, level: usize, idx: usize) Digest {
        const items = self.levels[level].items;
        return if (idx < items.len) items[idx] else self.zeros[level];
    }

    pub fn root(self: *const Set) Digest {
        return self.node(DEPTH, 0);
    }

    /// Recompute the path from one leaf upward. Capacity on every level is
    /// reserved first, so a failed allocation leaves the set as it was.
    fn refold(self: *Set, index: usize) Error!void {
        for (0..DEPTH + 1) |l| {
            const need = (index >> @intCast(l)) + 1;
            try self.levels[l].ensureTotalCapacity(self.alloc, need);
        }
        var idx = index;
        const leaf_hash = self.leaves.items[index].hash(self.h);
        if (idx < self.levels[0].items.len) {
            self.levels[0].items[idx] = leaf_hash;
        } else {
            self.levels[0].appendAssumeCapacity(leaf_hash);
        }
        for (1..DEPTH + 1) |l| {
            idx >>= 1;
            const v = self.h.compress(&self.node(l - 1, 2 * idx), &self.node(l - 1, 2 * idx + 1));
            if (idx < self.levels[l].items.len) {
                self.levels[l].items[idx] = v;
            } else {
                self.levels[l].appendAssumeCapacity(v);
            }
        }
    }

    fn append(self: *Set, leaf: Leaf) Error!usize {
        const index = self.leaves.items.len;
        if (index >= @as(usize, 1) << DEPTH) return error.SetFull;
        try self.leaves.append(self.alloc, leaf);
        errdefer _ = self.leaves.pop();
        try self.refold(index);
        return index;
    }

    /// The leaf strictly below `v`, which is the one an insert rewrites.
    pub fn lowLeaf(self: *const Set, v: *const Digest) Error!usize {
        var best: ?usize = null;
        for (self.leaves.items, 0..) |*l, i| {
            if (order.cmp(&l.value, v) != .lt) continue;
            if (best == null or order.cmp(&self.leaves.items[best.?].value, &l.value) == .lt) {
                best = i;
            }
        }
        return best orelse error.NoLowLeaf;
    }

    pub fn contains(self: *const Set, v: *const Digest) bool {
        for (self.leaves.items) |*l| {
            if (order.cmp(&l.value, v) == .eq) return true;
        }
        return false;
    }

    /// Prove `v` absent: the low leaf and its index. The caller checks
    /// `excludes` and folds the leaf to the root it already holds.
    pub fn proveAbsent(self: *const Set, v: *const Digest) Error!Absent {
        if (self.contains(v)) return error.AlreadyPresent;
        const i = try self.lowLeaf(v);
        return .{ .index = i, .leaf = self.leaves.items[i] };
    }

    /// Retire `v`: rewrite the low leaf to point at the new one, and append
    /// the new one pointing where the low leaf did.
    pub fn insert(self: *Set, v: Digest) Error!usize {
        if (self.contains(&v)) return error.AlreadyPresent;
        const li = try self.lowLeaf(&v);
        const low = self.leaves.items[li];
        const index = self.leaves.items.len;
        _ = try self.append(.{
            .value = v,
            .next_index = if (low.is_last) 0 else low.next_index,
            .next_value = if (low.is_last) digest.ZERO else low.next_value,
            .is_last = low.is_last,
        });
        self.leaves.items[li] = .{
            .value = low.value,
            .next_index = index,
            .next_value = v,
            .is_last = false,
        };
        try self.refold(li);
        return index;
    }

    pub fn witness(self: *const Set, index: usize) Error![DEPTH]Digest {
        if (index >= self.len()) return error.IndexOutOfRange;
        var sibs: [DEPTH]Digest = undefined;
        for (0..DEPTH) |l| sibs[l] = self.node(l, (index >> @intCast(l)) ^ 1);
        return sibs;
    }
};

/// Fold a leaf hash up its siblings, the convention the note tree shares.
pub fn rootOf(
    h: *const Poseidon,
    index: u64,
    sibs: *const [DEPTH]Digest,
    leaf: *const Digest,
) Digest {
    var cur = leaf.*;
    for (0..DEPTH) |l| {
        const right = ((index >> @intCast(l)) & 1) == 1;
        cur = if (right) h.compress(&sibs[l], &cur) else h.compress(&cur, &sibs[l]);
    }
    return cur;
}
