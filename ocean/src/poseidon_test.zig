// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const Poseidon = poseidon.Poseidon;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

test "the_mds_is_cauchy_over_nodes_i_and_8_plus_j" {
    const h = Poseidon.init();
    for (0..poseidon.WIDTH) |i| {
        for (0..poseidon.WIDTH) |j| {
            const d = field.sub(@intCast(i), @intCast(poseidon.WIDTH + j));
            try expectEqual(field.ONE, field.mul(h.mds[i][j], d));
        }
    }
}

test "round_constants_are_blake3_of_the_domain_and_the_indices" {
    const h = Poseidon.init();
    var buf: [28 + 16]u8 = undefined;
    @memcpy(buf[0..28], "NONOS-POSEIDON-GOLDILOCKS-RC");
    std.mem.writeInt(u64, buf[28..36], 3, .little);
    std.mem.writeInt(u64, buf[36..44], 5, .little);
    var out: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(&buf, &out, .{});
    const want = field.reduce(std.mem.readInt(u64, out[0..8], .little));
    try expectEqual(want, h.rc[3][5]);
    try expectEqual(want, poseidon.roundConstant(3, 5));
    try expect(h.rc[0][0] != h.rc[0][1]);
    try expect(h.rc[0][0] != h.rc[1][0]);
}

test "compress_orders_its_operands_and_permute_runs_all_32_rounds" {
    const h = Poseidon.init();
    const a = digest.Digest{ 1, 2, 3, 4 };
    const b = digest.Digest{ 5, 6, 7, 8 };
    const ab = h.compress(&a, &b);
    const ba = h.compress(&b, &a);
    try expect(!digest.eql(&ab, &ba));
    var st: poseidon.State = .{ 1, 2, 3, 4, 5, 6, 7, 8 };
    for (0..poseidon.ROUNDS) |r| st = h.round(&st, r);
    try expectEqual(st[0..4].*, ab);
}

// The public quad and the secret quads never share a compression, which is
// what lets a pool compute the commitment from the amount it escrowed and an
// owner digest it cannot open.
test "commit_note_nests_the_owner_under_the_public_quad" {
    const h = Poseidon.init();
    const limbs = [_]u64{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 };
    const public = digest.Digest{ 1, 2, 3, poseidon.NOTE_DOMAIN };
    const owner = h.compress(limbs[3..7], limbs[7..11]);
    try expectEqual(h.commitOwner(limbs[3..7], limbs[7..11]), owner);
    try expectEqual(h.compress(&public, &owner), h.commitNote(&limbs));
}

// Moving value, asset or the owner half moves the commitment.
test "every_half_of_the_nested_commitment_binds" {
    const h = Poseidon.init();
    const limbs = [_]u64{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 };
    const base = h.commitNote(&limbs);
    for ([_]usize{ 0, 1, 2, 3, 6, 7, 10 }) |i| {
        var bent = limbs;
        bent[i] += 1;
        try expect(!digest.eql(&base, &h.commitNote(&bent)));
    }
}
