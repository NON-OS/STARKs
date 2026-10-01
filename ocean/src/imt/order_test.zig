// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const Leaf = @import("leaf.zig").Leaf;
const order = @import("order.zig");
const Digest = digest.Digest;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

fn key(v: u64) Digest {
    return .{ v, 0, 0, 0 };
}

/// A key whose weight is in the high limb, to catch a comparison that reads
/// the limbs in the wrong order.
fn high(v: u64) Digest {
    return .{ 0, 0, 0, v };
}

test "the_order_is_the_four_limbs_as_one_little_endian_integer" {
    try expectEqual(std.math.Order.lt, order.cmp(&key(1), &key(2)));
    try expectEqual(std.math.Order.gt, order.cmp(&key(2), &key(1)));
    try expectEqual(std.math.Order.eq, order.cmp(&key(7), &key(7)));
    try expectEqual(std.math.Order.lt, order.cmp(&key(std.math.maxInt(u64)), &high(1)));
    try expectEqual(std.math.Order.gt, order.cmp(&high(1), &key(std.math.maxInt(u64))));
}

test "both_bounds_are_strict" {
    const low: Leaf = .{
        .value = key(10),
        .next_index = 2,
        .next_value = key(20),
        .is_last = false,
    };
    try expect(order.excludes(&low, &key(15)));
    // The key already in the set is a double spend, refused by the lower bound.
    try expect(!order.excludes(&low, &key(10)));
    // The neighbour's own key is the same, refused by the upper bound.
    try expect(!order.excludes(&low, &key(20)));
    try expect(!order.excludes(&low, &key(5)));
    try expect(!order.excludes(&low, &key(25)));
}

test "the_last_leaf_excludes_everything_above_it" {
    const last: Leaf = .{
        .value = key(10),
        .next_index = 0,
        .next_value = digest.ZERO,
        .is_last = true,
    };
    try expect(order.excludes(&last, &key(11)));
    try expect(order.excludes(&last, &high(1)));
    try expect(!order.excludes(&last, &key(10)));
    try expect(!order.excludes(&last, &key(9)));
}
