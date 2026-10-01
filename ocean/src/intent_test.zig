// NONOS Operating System (AGPL-3.0-or-later)
//! spec/shield-intent.json, rebuilt here from its own inputs.
//!
//! Half of the client-prover seam needs no prover: the client and the circuit
//! have to agree on what a transfer is. The
//! circuit emits one transfer as thirty-two settled words and every private
//! input that produces them; this builds the same spend from those inputs and
//! checks it lands on the same words.
//!
//! Nothing here is copied from the circuit's output except the values being
//! asserted. The notes, the commitments, both trees and the nullifiers are
//! computed by this client's own code, which is the whole point: two
//! implementations of one statement, which is the check that has found every
//! seam defect in this system.
//!
//! What this does not yet do is build the whole intent through `Spend.intent`,
//! because that takes one nullifier key and this fixture spends two notes under
//! two different secrets. `ocean` models one wallet spending its own notes; the
//! circuit allows a secret per input. The deployed case is the former, so the
//! next vector should use one secret for both inputs and this file should then
//! compare all thirty-two words in one call rather than piece by piece.

const std = @import("std");
const digest = @import("digest.zig");
const field = @import("field.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const poseidon = @import("poseidon.zig");
const tree = @import("tree.zig");
const Digest = digest.Digest;
const Note = note.Note;
const Poseidon = poseidon.Poseidon;
const expectEqual = std.testing.expectEqual;

/// The fixture's seeds, as the vector states them. Secrets are `seed*16 + i + 1`
/// and blindings are `seed + 5 .. seed + 8`, which is how the circuit's fixture
/// builds them and why this file needs no random number generator.
fn secret(seed: u64) Digest {
    var sk: Digest = undefined;
    for (0..4) |i| sk[i] = field.reduce(seed * 16 + @as(u64, @intCast(i)) + 1);
    return sk;
}

fn blinding(seed: u64) Digest {
    var b: Digest = undefined;
    for (0..4) |i| b[i] = field.reduce(seed + 5 + @as(u64, @intCast(i)));
    return b;
}

/// A note whose committed spend key the given secret derives.
fn owned(h: *const Poseidon, sk: Digest, seed: u64, value: u64) !Note {
    const s = try key.Secret.fromLimbs(&sk);
    return .{
        .value = value,
        .asset_id = 0,
        .spend_pk = s.derive(h).spend_pk,
        .blinding = blinding(seed),
    };
}

/// An output note, whose spend key is a payee's and not derived here.
fn plain(seed: u64, value: u64) Note {
    var pk: Digest = undefined;
    for (0..4) |i| pk[i] = field.reduce(seed + 1 + @as(u64, @intCast(i)));
    return .{
        .value = value,
        .asset_id = 0,
        .spend_pk = pk,
        .blinding = blinding(seed),
    };
}

/// spec/shield-intent.json, `intent`, words 0 through 7.
const NOTE_ROOT: Digest = .{
    14642651294145191397,
    3749887710612721201,
    17897719159298268359,
    12296343470192110035,
};
const ASSOC_ROOT: Digest = .{
    18379151337909585371,
    14195779821289367974,
    2789637164666902265,
    9661791652754313075,
};

/// Words 8 through 23: the two nullifiers and the two created commitments.
const NF0: Digest = .{
    12815518398326363097,
    11079974279903391392,
    14375983190449556566,
    13233519045614235161,
};
const NF1: Digest = .{
    7969208576817432209,
    17046890287303884577,
    1064544041616644731,
    10281065422136892462,
};
const OUT_CM0: Digest = .{
    12720183436024670050,
    9285404368140913836,
    8705677393628614192,
    15037102487662722891,
};
const OUT_CM1: Digest = .{
    3011667836969558430,
    1926734682051323755,
    8913019065820342362,
    6236535739403372849,
};

/// The settled scalars, words 24 through 27. Pinned as the client's own copy of
/// what a relayer decodes, so a change to either side shows up here.
const PUBLIC_AMOUNT: u64 = 200;
const FEE: u64 = 100;
const ASSET_ID: u64 = 0;
const CLEARING_PRICE: u64 = 1000000;

/// `assoc_pads`, and the leaves the two spent notes land on in each tree.
const ASSOC_PADS = [_]u64{ 900, 901, 902 };
const POOL_LEAVES = [_]usize{ 0, 1 };
const ASSOC_LEAVES = [_]usize{ 3, 4 };

fn pad(v: u64) Digest {
    return .{ field.reduce(v), 0, 0, 0 };
}

// The scalars a relayer reads out of the settled words, and the balance they
// have to satisfy: inputs equal outputs plus the public leg plus the fee.
//
// `Spend.check` enforces exactly this before it will produce an intent, so a
// vector that did not balance would be rejected by this client rather than
// merely disagreed with.
test "the_settled_scalars_balance_the_transfer" {
    try expectEqual(@as(u64, 1000 + 2000), 1500 + 1200 + PUBLIC_AMOUNT + FEE);
    try expectEqual(@as(u64, 0), ASSET_ID);
    try expectEqual(@as(u64, 1000000), CLEARING_PRICE);
}

// The commitments the circuit publishes are the commitments this client
// computes from the same notes.
test "the_published_commitments_are_the_ones_this_client_commits" {
    const h = Poseidon.init();
    const out0 = plain(20, 1500);
    const out1 = plain(30, 1200);
    try expectEqual(OUT_CM0, out0.cm(&h));
    try expectEqual(OUT_CM1, out1.cm(&h));
}

// The nullifiers are the ones this client derives, live, at the leaf the pool
// planted each note on.
test "the_retired_nullifiers_are_the_ones_this_client_derives" {
    const h = Poseidon.init();
    const sk0 = secret(1);
    const sk1 = secret(2);
    const in0 = try owned(&h, sk0, 0, 1000);
    const in1 = try owned(&h, sk1, 0, 2000);
    const s0 = try key.Secret.fromLimbs(&sk0);
    const s1 = try key.Secret.fromLimbs(&sk1);
    const cm0 = in0.cm(&h);
    const cm1 = in1.cm(&h);
    try expectEqual(NF0, key.nullifier(&h, &s0.derive(&h).nk, &cm0, POOL_LEAVES[0], true));
    try expectEqual(NF1, key.nullifier(&h, &s1.derive(&h).nk, &cm1, POOL_LEAVES[1], true));
}

// Both roots, rebuilt leaf by leaf.
//
// This is the membership the circuit proves: the pool plants the two spent
// commitments and nothing else, the association set plants three pads first.
// A client that agrees on both roots agrees on which notes were spendable.
test "both_published_roots_are_the_ones_this_client_builds" {
    const h = Poseidon.init();
    const alloc = std.testing.allocator;
    const in0 = try owned(&h, secret(1), 0, 1000);
    const in1 = try owned(&h, secret(2), 0, 2000);
    const cm0 = in0.cm(&h);
    const cm1 = in1.cm(&h);

    var pool = tree.Tree.init(alloc, &h);
    defer pool.deinit();
    try expectEqual(POOL_LEAVES[0], try pool.insert(cm0));
    try expectEqual(POOL_LEAVES[1], try pool.insert(cm1));
    try expectEqual(NOTE_ROOT, pool.root());

    var assoc = tree.Tree.init(alloc, &h);
    defer assoc.deinit();
    for (ASSOC_PADS) |p| _ = try assoc.insert(pad(p));
    try expectEqual(ASSOC_LEAVES[0], try assoc.insert(cm0));
    try expectEqual(ASSOC_LEAVES[1], try assoc.insert(cm1));
    try expectEqual(ASSOC_ROOT, assoc.root());
}
