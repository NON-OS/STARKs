// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const note = @import("../note.zig");
const key = @import("../key.zig");
const call = @import("call.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

fn aNote(rng: std.Random, h: *const Poseidon, value: u64, asset: u64) !Note {
    const s = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
    return Note.fresh(rng, value, asset, s.derive(h).spend_pk);
}

// The whole point of the nesting: what the pool computes from the amount it
// escrowed is the commitment the wallet holds the opening for.
test "the_pool_computes_the_leaf_the_wallet_owns" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(41);
    const n = try aNote(prng.random(), &h, 1_995_000_000_000_000, 0);
    const d = call.prepare(&h, &n);
    try expectEqual(call.leafOf(&h, &n), d.leaf(&h));
}

test "the_call_carries_no_spend_key_and_no_blinding" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(42);
    const n = try aNote(prng.random(), &h, 1000, 0);
    const d = call.prepare(&h, &n);
    const b = call.encode(&d);
    // The owner digest is a compression of both, so neither appears whole.
    try expect(!std.mem.containsAtLeast(u8, &b, 1, &digest.toBytes(&n.spend_pk)));
    try expect(!std.mem.containsAtLeast(u8, &b, 1, &digest.toBytes(&n.blinding)));
    try expectEqual(@as(usize, 48), b.len);
}

test "a_different_escrowed_amount_is_a_different_leaf" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(43);
    const n = try aNote(prng.random(), &h, 1000, 0);
    var d = call.prepare(&h, &n);
    const honest = d.leaf(&h);
    // A payer who escrows less cannot reach the leaf their note commits to.
    d.amount = 1;
    try expect(!digest.eql(&honest, &d.leaf(&h)));
    d.amount = 1000;
    d.asset_id = 1;
    try expect(!digest.eql(&honest, &d.leaf(&h)));
}

test "the_value_splits_at_thirty_two_bits_and_the_high_half_binds" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(44);
    const n = try aNote(prng.random(), &h, 0, 0);
    var lo = call.prepare(&h, &n);
    lo.amount = 0xFFFF_FFFF;
    var hi = call.prepare(&h, &n);
    hi.amount = @as(u64, 0xFFFF_FFFF) << 32;
    try expect(!digest.eql(&lo.leaf(&h), &hi.leaf(&h)));
}

test "a_deposit_round_trips_through_its_calldata" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(45);
    const n = try aNote(prng.random(), &h, 7, 3);
    const d = call.prepare(&h, &n);
    const back = try call.decode(&call.encode(&d));
    try expectEqual(d.asset_id, back.asset_id);
    try expectEqual(d.amount, back.amount);
    try expectEqual(d.owner, back.owner);
    try expectEqual(d.leaf(&h), back.leaf(&h));
}

test "a_non_canonical_owner_limb_is_refused" {
    var b: [call.CALLDATA]u8 = [_]u8{0} ** call.CALLDATA;
    // Limb zero occupies the last eight bytes; p itself is not a field element.
    std.mem.writeInt(u64, b[40..48], 0xFFFF_FFFF_0000_0001, .big);
    try expectError(error.NonCanonical, call.decode(&b));
}
