// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const memo = @import("memo.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const Sha3 = std.crypto.hash.sha3.Sha3_256;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Party = struct {
    secret: key.Secret,
    view: memo.ViewKey,
    addr: memo.Address,

    fn init(h: *const Poseidon, limbs: [4]u64) !Party {
        const s = try key.Secret.fromLimbs(&limbs);
        const v = try memo.ViewKey.fromSecret(&s);
        return .{ .secret = s, .view = v, .addr = v.address(s.derive(h).spend_pk) };
    }
};

fn sha3Hex(bytes: []const u8) [64]u8 {
    var d: [32]u8 = undefined;
    Sha3.hash(bytes, &d, .{});
    return std.fmt.bytesToHex(d, .lower);
}

test "the_note_seal_vector_is_reproduced" {
    const seed = [_]u8{0x07} ** 32;
    const eseed = [_]u8{0x09} ** 64;
    const leaf = [_]u8{0x5a} ** 32;
    const o = memo.Opening{ .value = 1_000_000_000_000_000_000, .asset_id = 1, .blinding = .{ 11, 22, 33, 44 } };
    const v = try memo.ViewKey.fromSeed(&seed);
    try expectEqual("4c82604001ad0b7a4cbc022c322f5e757f09ba4a5b095c8af545caeeac6836c8".*, sha3Hex(&v.ek));
    const m = try memo.sealWith(&v.ek, &o, &leaf, &eseed);
    try expectEqual(@as(u8, 0xd2), m[1]);
    try expectEqual("78fbb6f16dfdcf4b5cc87ecb0cca92c4aa44b4747f3b2c183a9d3eb9152e1dc9".*, sha3Hex(&m));
    const back = try memo.openOpening(&v, &m, &leaf);
    try expectEqual(o.value, back.value);
    try expectEqual(o.asset_id, back.asset_id);
    try expectEqual(o.blinding, back.blinding);
}

test "the_sizes_are_version_one" {
    try expectEqual(1249, memo.Address.BYTES);
    try expectEqual(1186, memo.LEN);
    try expectEqual(1216, memo.EK_BYTES);
    try expectEqual(1120, memo.CT_BYTES);
}

test "a_sealed_note_opens_only_under_the_payee_key_and_its_leaf" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(21);
    const rng = prng.random();
    const a = try Party.init(&h, .{ 1, 2, 3, 4 });
    const b = try Party.init(&h, .{ 5, 6, 7, 8 });
    const n = Note.fresh(rng, 42, 3, a.addr.spend_pk);
    const cm = n.cm(&h);
    const m = try memo.seal(rng, &a.addr, &n, &cm);

    const got = try memo.open(&a.view, &m, &cm, a.addr.spend_pk);
    try expectEqual(n.value, got.value);
    try expectEqual(n.asset_id, got.asset_id);
    try expectEqual(n.spend_pk, got.spend_pk);
    try expectEqual(n.blinding, got.blinding);

    try expectError(error.NotForUs, memo.open(&b.view, &m, &cm, b.addr.spend_pk));
    const other = digest.tag(1);
    try expectError(error.NotForUs, memo.open(&a.view, &m, &other, a.addr.spend_pk));
}

// ML-KEM decapsulates a bent ciphertext to an implicit secret, so the view tag
// or the AEAD tag rejects it. A byte in each field.
test "a_memo_with_any_byte_bent_does_not_open" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(22);
    const rng = prng.random();
    const a = try Party.init(&h, .{ 1, 2, 3, 4 });
    const n = Note.fresh(rng, 1, 0, a.addr.spend_pk);
    const cm = n.cm(&h);
    const m = try memo.seal(rng, &a.addr, &n, &cm);
    const at = [_]usize{ 0, 1, 2, memo.CT_BYTES / 2, memo.CT_BYTES - 1, memo.CT_BYTES + 1, memo.LEN - 40, memo.LEN - 17, memo.LEN - 1 };
    for (at) |i| {
        var t = m;
        t[i] ^= 1;
        try expectError(error.NotForUs, memo.open(&a.view, &t, &cm, a.addr.spend_pk));
    }
}

test "two_seals_of_one_note_differ" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(23);
    const rng = prng.random();
    const a = try Party.init(&h, .{ 1, 2, 3, 4 });
    const n = Note.fresh(rng, 1, 0, a.addr.spend_pk);
    const cm = n.cm(&h);
    const m1 = try memo.seal(rng, &a.addr, &n, &cm);
    const m2 = try memo.seal(rng, &a.addr, &n, &cm);
    try expect(!std.mem.eql(u8, &m1, &m2));
}

test "the_view_key_is_a_function_of_the_secret" {
    const h = Poseidon.init();
    const a = try Party.init(&h, .{ 1, 2, 3, 4 });
    const a2 = try Party.init(&h, .{ 1, 2, 3, 4 });
    const b = try Party.init(&h, .{ 1, 2, 3, 5 });
    try expectEqual(a.addr.ek, a2.addr.ek);
    try expect(!std.mem.eql(u8, &a.addr.ek, &b.addr.ek));
}

test "an_address_round_trips_and_another_version_is_refused" {
    const h = Poseidon.init();
    const a = try Party.init(&h, .{ 1, 2, 3, 4 });
    var b = a.addr.bytes();
    const back = try memo.Address.fromBytes(&b);
    try expectEqual(a.addr.spend_pk, back.spend_pk);
    try expectEqual(a.addr.ek, back.ek);
    b[0] = 0x02;
    try expectError(error.MalformedAddress, memo.Address.fromBytes(&b));
}

test "a_non_canonical_blinding_is_refused" {
    var b = (memo.Opening{ .value = 1, .asset_id = 0, .blinding = .{ 1, 2, 3, 4 } }).bytes();
    std.mem.writeInt(u64, b[16..24], 0xFFFF_FFFF_0000_0001, .little);
    try expect(std.meta.isError(memo.Opening.fromBytes(&b)));
}

test "a_note_round_trips_through_its_80_bytes" {
    var prng = std.Random.DefaultPrng.init(24);
    const n = Note.fresh(prng.random(), 0xFFFF_FFFF_FFFF_FFFF, 9, .{ 1, 2, 3, 4 });
    const b = n.bytes();
    const back = try Note.fromBytes(&b);
    try expectEqual(n.value, back.value);
    try expectEqual(n.asset_id, back.asset_id);
    try expectEqual(n.spend_pk, back.spend_pk);
    try expectEqual(n.blinding, back.blinding);
}
