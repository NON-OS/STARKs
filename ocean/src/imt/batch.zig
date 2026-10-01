// NONOS Operating System (AGPL-3.0-or-later)
//! A batch of nullifiers as a chain of inserts.

const std = @import("std");
const digest = @import("../digest.zig");
const order = @import("order.zig");
const set = @import("set.zig");
const Digest = digest.Digest;
const Set = set.Set;
const Error = set.Error;
const Allocator = std.mem.Allocator;

/// Where a key enters the chain: under a leaf already in the tree, or under
/// the key the batch inserted just before it.
pub const Low = union(enum) {
    in_tree: usize,
    in_batch: usize,
};

pub const Step = struct {
    key: Digest,
    low: Low,
};

/// A batch, sorted, so sort adjacent keys do not fight over one neighbour.
///
/// An insert rewrites the low leaf's pointer, so two new keys landing beside
/// each other touch one leaf and serialise. Sorting first turns the batch into
/// a chain: each key's low leaf is either an existing leaf or the key before
/// it, and the whole run proves as one subtree.
///
/// Strictly increasing, so a duplicate cannot survive the chain. Uniqueness
/// stops being a rule to enforce and becomes a consequence of the shape.
pub fn chain(alloc: Allocator, s: *const Set, sorted: []const Digest) Error![]Step {
    for (0..sorted.len -| 1) |i| {
        if (order.cmp(&sorted[i], &sorted[i + 1]) != .lt) return error.OutOfOrder;
    }
    const steps = try alloc.alloc(Step, sorted.len);
    errdefer alloc.free(steps);
    for (sorted, 0..) |k, i| {
        const in_tree = try s.lowLeaf(&k);
        const prior = i > 0 and order.cmp(&s.leaves.items[in_tree].value, &sorted[i - 1]) == .lt;
        steps[i] = .{
            .key = k,
            .low = if (prior) .{ .in_batch = i - 1 } else .{ .in_tree = in_tree },
        };
    }
    return steps;
}

/// No two keys update the same leaf.
///
/// This holds today because a same gap key takes the key before it as its low
/// leaf rather than the leaf they both sit under. That is a consequence, not a
/// property: validate every key against the pre-batch tree instead and both
/// same gap keys satisfy the bounds, both write the same pointer, they
/// collide, and the fold loses one without saying so. So it is checked.
pub fn writesAreDistinct(steps: []const Step) bool {
    for (steps, 0..) |s, i| {
        for (steps[0..i]) |o| {
            const clash = switch (s.low) {
                .in_tree => |a| switch (o.low) {
                    .in_tree => |b| a == b,
                    .in_batch => false,
                },
                .in_batch => |a| switch (o.low) {
                    .in_batch => |b| a == b,
                    .in_tree => false,
                },
            };
            if (clash) return false;
        }
    }
    return true;
}
