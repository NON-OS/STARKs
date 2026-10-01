// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const leaf = @import("leaf.zig");
const Poseidon = poseidon.Poseidon;
const Digest = digest.Digest;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

fn key(v: u64) Digest {
    return .{ v, 0, 0, 0 };
}

test "the_leaf_hash_binds_every_field" {
    const h = Poseidon.init();
    const base: leaf.Leaf = .{
        .value = key(10),
        .next_index = 2,
        .next_value = key(20),
        .is_last = false,
    };
    const want = base.hash(&h);
    var a = base;
    a.value = key(11);
    var b = base;
    b.next_index = 3;
    var c = base;
    c.next_value = key(21);
    var d = base;
    d.is_last = true;
    for ([_]leaf.Leaf{ a, b, c, d }) |bent| {
        try expect(!digest.eql(&want, &bent.hash(&h)));
    }
}

test "the_tag_sits_past_the_payload_and_the_rest_is_zero" {
    const l: leaf.Leaf = .{
        .value = key(1),
        .next_index = 9,
        .next_value = key(2),
        .is_last = true,
    };
    const limbs = l.limbs();
    try expectEqual(@as(u64, 1), limbs[0]);
    try expectEqual(@as(u64, 2), limbs[4]);
    try expectEqual(@as(u64, 9), limbs[8]);
    try expectEqual(@as(u64, 1), limbs[leaf.LEAF_LIMBS - 1]);
    try expectEqual(leaf.LEAF_DOMAIN, limbs[leaf.LEAF_LIMBS]);
    for (limbs[leaf.LEAF_LIMBS + 1 ..]) |v| try expectEqual(@as(u64, 0), v);
}

test "an_empty_slot_and_the_sentinel_are_different_leaves" {
    const h = Poseidon.init();
    const s = leaf.Leaf.sentinel();
    const e = leaf.Leaf.empty();
    try expect(s.is_last);
    try expect(!e.is_last);
    try expect(!digest.eql(&s.hash(&h), &e.hash(&h)));
}
