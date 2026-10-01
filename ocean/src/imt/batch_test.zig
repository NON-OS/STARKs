// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const batch = @import("batch.zig");
const set = @import("set.zig");
const Poseidon = poseidon.Poseidon;
const Digest = digest.Digest;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

fn key(v: u64) Digest {
    return .{ v, 0, 0, 0 };
}

test "a_batch_chains_and_an_unsorted_one_is_refused" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    _ = try s.insert(key(100));
    const alloc = std.testing.allocator;

    const sorted = [_]Digest{ key(10), key(20), key(30) };
    const steps = try batch.chain(alloc, &s, &sorted);
    defer alloc.free(steps);
    try expectEqual(3, steps.len);
    try expect(batch.writesAreDistinct(steps));
    // The first key sits under a tree leaf, the rest under the key before them.
    try expectEqual(batch.Low.in_tree, std.meta.activeTag(steps[0].low));
    try expectEqual(batch.Low.in_batch, std.meta.activeTag(steps[1].low));
    try expectEqual(batch.Low.in_batch, std.meta.activeTag(steps[2].low));

    const unsorted = [_]Digest{ key(30), key(20) };
    try expectError(error.OutOfOrder, batch.chain(alloc, &s, &unsorted));
    const repeated = [_]Digest{ key(10), key(10) };
    try expectError(error.OutOfOrder, batch.chain(alloc, &s, &repeated));
}

test "keys_in_separate_gaps_write_separate_leaves" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    for ([_]u64{ 100, 200 }) |v| _ = try s.insert(key(v));
    const alloc = std.testing.allocator;
    const sorted = [_]Digest{ key(50), key(150) };
    const steps = try batch.chain(alloc, &s, &sorted);
    defer alloc.free(steps);
    try expect(batch.writesAreDistinct(steps));
    try expectEqual(batch.Low.in_tree, std.meta.activeTag(steps[0].low));
    try expectEqual(batch.Low.in_tree, std.meta.activeTag(steps[1].low));
}

test "two_keys_naming_one_tree_leaf_are_caught" {
    const a: batch.Step = .{ .key = key(1), .low = .{ .in_tree = 3 } };
    const b: batch.Step = .{ .key = key(2), .low = .{ .in_tree = 3 } };
    try expect(!batch.writesAreDistinct(&[_]batch.Step{ a, b }));
    const c: batch.Step = .{ .key = key(2), .low = .{ .in_batch = 3 } };
    // A tree index and a batch index are different leaves even when equal.
    try expect(batch.writesAreDistinct(&[_]batch.Step{ a, c }));
}

test "an_empty_batch_chains_to_nothing" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    const alloc = std.testing.allocator;
    const steps = try batch.chain(alloc, &s, &[_]Digest{});
    defer alloc.free(steps);
    try expectEqual(0, steps.len);
    try expect(batch.writesAreDistinct(steps));
}
