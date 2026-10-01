// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const tree = @import("tree.zig");
const Poseidon = poseidon.Poseidon;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

/// Pool 0xa760D749adfe15BafFfeC8E7301CEA89B150c046 on Sepolia: leaves 0, 1, 2
/// as its NoteCommitted logs carry them, and the root it reports after leaf 2.
const LEAF0 = "0f14542ea9ec2683cac6fb8e8167203c8c7eed6759da835fd29c233259e8ba62";
const LEAF1 = "59b6835c74c863e7b9defa6bc7c34e1ad9ee1c8519a6fe0f301a2502cd927fd8";
const LEAF2 = "1edff88b113db999adadd2406035b75c13c3eb69ee244dc4f56ecaf36e544897";
const ROOT = "e083f588523bb322c7d4077ecf9d36f1628a2655c22c86136c73b6b3da159a3f";

test "the_live_pool_root_after_three_leaves_at_depth_32" {
    const h = Poseidon.init();
    var t = tree.Tree.init(std.testing.allocator, &h);
    defer t.deinit();
    for ([_][]const u8{ LEAF0, LEAF1, LEAF2 }, 0..) |hex, i| {
        try expectEqual(i, try t.insert(try digest.fromHex(hex)));
    }
    try expectEqual(3, t.len());
    try expectEqual(try digest.fromHex(ROOT), t.root());
}

test "an_empty_tree_has_the_zeros_chain_root" {
    const h = Poseidon.init();
    var t = tree.Tree.init(std.testing.allocator, &h);
    defer t.deinit();
    var z = digest.ZERO;
    for (0..tree.DEPTH) |_| z = h.compress(&z, &z);
    try expectEqual(z, t.root());
    try expectEqual(0, t.len());
}

test "a_witness_folds_to_the_root_and_a_moved_index_does_not" {
    const h = Poseidon.init();
    var t = tree.Tree.init(std.testing.allocator, &h);
    defer t.deinit();
    for (0..5) |i| _ = try t.insert(digest.tag(i + 1));
    for (0..5) |i| {
        const w = try t.witness(i);
        const leaf = try t.leaf(i);
        try expectEqual(t.root(), tree.rootOf(&h, &w, &leaf));
        var moved = w;
        moved.leaf_index ^= 1;
        try expect(!digest.eql(&t.root(), &tree.rootOf(&h, &moved, &leaf)));
    }
}

test "a_witness_taken_before_a_later_insert_still_folds_to_the_new_root_with_new_siblings" {
    const h = Poseidon.init();
    var t = tree.Tree.init(std.testing.allocator, &h);
    defer t.deinit();
    _ = try t.insert(digest.tag(1));
    const old = try t.witness(0);
    const root0 = t.root();
    _ = try t.insert(digest.tag(2));
    const leaf = try t.leaf(0);
    try expectEqual(root0, tree.rootOf(&h, &old, &leaf));
    try expect(!digest.eql(&root0, &t.root()));
    const fresh = try t.witness(0);
    try expectEqual(t.root(), tree.rootOf(&h, &fresh, &leaf));
    try expectEqual(digest.tag(2), fresh.siblings[0]);
}

test "leaf_and_witness_refuse_an_index_past_the_end" {
    const h = Poseidon.init();
    var t = tree.Tree.init(std.testing.allocator, &h);
    defer t.deinit();
    try expectError(error.IndexOutOfRange, t.leaf(0));
    try expectError(error.IndexOutOfRange, t.witness(0));
    _ = try t.insert(digest.tag(1));
    try expectError(error.IndexOutOfRange, t.witness(1));
}

test "a_failed_allocation_leaves_the_tree_as_it_was" {
    const h = Poseidon.init();
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 3 });
    var t = tree.Tree.init(failing.allocator(), &h);
    defer t.deinit();
    const r = t.insert(digest.tag(1));
    if (r) |_| {
        try expectEqual(1, t.len());
    } else |e| {
        try expectEqual(error.OutOfMemory, e);
        try expectEqual(0, t.len());
    }
}
