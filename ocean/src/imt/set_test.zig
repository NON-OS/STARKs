// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const Leaf = @import("leaf.zig").Leaf;
const order = @import("order.zig");
const set = @import("set.zig");
const Poseidon = poseidon.Poseidon;
const Digest = digest.Digest;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

fn key(v: u64) Digest {
    return .{ v, 0, 0, 0 };
}

test "an_empty_set_holds_one_sentinel_and_excludes_every_key" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    try expectEqual(1, s.len());
    const sentinel = try s.at(0);
    try expect(sentinel.is_last);
    for ([_]u64{ 1, 2, 1000, std.math.maxInt(u32) }) |v| {
        const k = key(v);
        try expect(order.excludes(&sentinel, &k));
        try expect(!s.contains(&k));
    }
}

test "an_insert_rewrites_the_low_leaf_and_moves_the_root" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    const before = s.root();
    try expectEqual(1, try s.insert(key(50)));
    try expect(!digest.eql(&before, &s.root()));
    try expect(s.contains(&key(50)));
    const low = try s.at(0);
    try expect(!low.is_last);
    try expectEqual(@as(u64, 1), low.next_index);
    try expectEqual(key(50), low.next_value);
    try expect((try s.at(1)).is_last);
}

test "a_key_already_retired_cannot_be_retired_again" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    _ = try s.insert(key(50));
    try expectError(error.AlreadyPresent, s.insert(key(50)));
    try expectError(error.AlreadyPresent, s.proveAbsent(&key(50)));
}

test "insertion_keeps_every_gap_consistent" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    for ([_]u64{ 50, 10, 90, 30, 70 }) |v| _ = try s.insert(key(v));
    try expectEqual(6, s.len());
    for ([_]u64{ 10, 30, 50, 70, 90 }) |v| try expect(s.contains(&key(v)));
    for ([_]u64{ 5, 20, 40, 60, 80, 100 }) |v| {
        const k = key(v);
        const p = try s.proveAbsent(&k);
        try expect(order.excludes(&p.leaf, &k));
    }
}

test "an_absence_proof_folds_to_the_root_the_set_reports" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    for ([_]u64{ 50, 10, 90 }) |v| _ = try s.insert(key(v));
    const k = key(60);
    const p = try s.proveAbsent(&k);
    try expect(order.excludes(&p.leaf, &k));
    const sibs = try s.witness(p.index);
    const leaf_hash = p.leaf.hash(&h);
    try expectEqual(s.root(), set.rootOf(&h, p.index, &sibs, &leaf_hash));
}

test "a_bent_low_leaf_does_not_fold_to_the_root" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    for ([_]u64{ 50, 10 }) |v| _ = try s.insert(key(v));
    const k = key(30);
    const p = try s.proveAbsent(&k);
    var bent = p.leaf;
    bent.next_value = key(31);
    const sibs = try s.witness(p.index);
    const bent_hash = bent.hash(&h);
    try expect(!digest.eql(&s.root(), &set.rootOf(&h, p.index, &sibs, &bent_hash)));
}

test "an_index_past_the_end_is_refused" {
    const h = Poseidon.init();
    var s = try set.Set.init(std.testing.allocator, &h);
    defer s.deinit();
    try expectError(error.IndexOutOfRange, s.at(1));
    try expectError(error.IndexOutOfRange, s.witness(1));
}
