// NONOS Operating System (AGPL-3.0-or-later)
//! The client against the pinned activity wallet vector
//! (spec/wallet-vectors-activity/claim): the key commitment K and the weekly tag
//! T from the seed's key, each spent note's nullifier at its leaf, the week's
//! leaves folded to Λ_e at depth 16, and the payout address as P, each equal to
//! the words the Rust prover proved.

const std = @import("std");
const digest = @import("digest.zig");
const key = @import("key.zig");
const poseidon = @import("poseidon.zig");
const spend = @import("spend.zig");
const Digest = digest.Digest;

const SK = [4]u64{ 659918, 2827, 12648430, 53261 };
const WEEK: u64 = 2935;
const LEAVES = [_][]const u8{ "0x0000000000000007000000000000000500000000000000030000000000012cc8", "0x0000000000000007000000000000000500000000000000030000000000012cc9", "0x02b1a8f77d095d8873f91f5f03db47895c440a5b4344c8b8c791fabeb05c7b0a", "0x0000000000000007000000000000000500000000000000030000000000012cca", "0x0000000000000007000000000000000500000000000000030000000000012ccb", "0xd16ee62c9463a6c8fbe289617824ad7f4e1012c151db4c685d1c393422a68c3c", "0xb2cba9b2bf5f147745dd6c08e146a0b5d3db1edfacddfc2ef3ada41d34d9f8fb", "0x0000000000000007000000000000000500000000000000030000000000012ccc", "0x0000000000000007000000000000000500000000000000030000000000012ccd", "0x0000000000000007000000000000000500000000000000030000000000012cce", "0x0000000000000007000000000000000500000000000000030000000000012ccf" };
const CMS = [_][]const u8{ "0x000000000000032200000000000002be000000000000025a00000000000001f6", "0x000000000000032000000000000002bc000000000000025800000000000001f4", "0x000000000000032100000000000002bd000000000000025900000000000001f5" };
const NOTE_POSITIONS = [_]u64{ 4022, 4000, 4011 };
const PAYOUT_ADDRESS = "0x0018000000000017000000000016000000000015";
const PUBLICS = [18]u64{ 9438258360667914599, 16125766314127921623, 7458207211238384697, 13969931631697608773, 2935, 3, 13302999927338112619, 8294111438542460391, 16629032222603265372, 15463095390215338946, 21, 22, 23, 24, 9425393185437381193, 16065497387004548799, 13410382485595425668, 14663646003371575446 };
const DEPTH = 16;

fn words(at: usize) Digest {
    return PUBLICS[at..][0..4].*;
}

/// A depth-16 tree over `leaves` the way the pool's is built: zero leaves,
/// zeros[l + 1] = compress(zeros[l], zeros[l]), each node compress(left, right).
fn fold(h: *const poseidon.Poseidon, leaves: []const Digest) Digest {
    var level: [1 << DEPTH]Digest = undefined;
    var zero: Digest = .{ 0, 0, 0, 0 };
    var n: usize = leaves.len;
    for (leaves, 0..) |l, i| level[i] = l;
    var depth: usize = 0;
    while (depth < DEPTH) : (depth += 1) {
        const next = (n + 1) / 2;
        var i: usize = 0;
        while (i < next) : (i += 1) {
            const left = level[2 * i];
            const right = if (2 * i + 1 < n) level[2 * i + 1] else zero;
            level[i] = h.compress(&left, &right);
        }
        zero = h.compress(&zero, &zero);
        n = next;
    }
    return level[0];
}

test "the_client_reproduces_the_pinned_activity_vector" {
    const h = poseidon.Poseidon.init();
    const secret = try key.Secret.fromLimbs(&SK);
    const nk = secret.derive(&h).nk;

    try std.testing.expectEqualSlices(u64, &words(14), &key.keyCommitment(&h, &nk));
    try std.testing.expectEqualSlices(u64, &words(6), &key.activityTag(&h, &nk, WEEK));
    try std.testing.expectEqual(WEEK, PUBLICS[4]);
    try std.testing.expectEqual(@as(u64, CMS.len), PUBLICS[5]);

    var leaves: [LEAVES.len]Digest = undefined;
    for (LEAVES, 0..) |s, i| leaves[i] = try digest.fromHex(s);
    try std.testing.expectEqualSlices(u64, &words(0), &fold(&h, &leaves));

    for (CMS, NOTE_POSITIONS) |s, pos| {
        const cm = try digest.fromHex(s);
        const nf = key.nullifier(&h, &nk, &cm, pos, true);
        var found = false;
        for (leaves) |l| found = found or std.mem.eql(u64, &l, &nf);
        try std.testing.expect(found);
    }

    var addr: [20]u8 = undefined;
    _ = try std.fmt.hexToBytes(&addr, PAYOUT_ADDRESS[2..]);
    try std.testing.expectEqualSlices(u64, &words(10), &spend.addressLimbs(&addr));
}

test "another_week_or_another_key_moves_the_tag_and_only_the_key_moves_k" {
    const h = poseidon.Poseidon.init();
    const nk = (try key.Secret.fromLimbs(&SK)).derive(&h).nk;
    var other = nk;
    other[0] +%= 1;
    const t = key.activityTag(&h, &nk, WEEK);
    try std.testing.expect(!std.mem.eql(u64, &t, &key.activityTag(&h, &nk, WEEK + 1)));
    try std.testing.expect(!std.mem.eql(u64, &t, &key.activityTag(&h, &other, WEEK)));
    try std.testing.expect(!std.mem.eql(u64, &key.keyCommitment(&h, &nk), &key.keyCommitment(&h, &other)));
    try std.testing.expect(!std.mem.eql(u64, &key.keyCommitment(&h, &nk), &t));
}
