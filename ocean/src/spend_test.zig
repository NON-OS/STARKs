// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const tree = @import("tree.zig");
const spend = @import("spend.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Scene = struct {
    keys: key.Keys,
    pool: tree.Tree,
    assoc: tree.Tree,
    notes: [2]Note,

    fn init(alloc: std.mem.Allocator, h: *const Poseidon) !Scene {
        const secret = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
        const keys = secret.derive(h);
        var s: Scene = .{
            .keys = keys,
            .pool = tree.Tree.init(alloc, h),
            .assoc = tree.Tree.init(alloc, h),
            .notes = undefined,
        };
        errdefer s.deinit();
        s.notes[0] = .{ .value = 1000, .asset_id = 0, .spend_pk = keys.spend_pk, .blinding = .{ 6, 7, 8, 9 } };
        s.notes[1] = .{ .value = 5, .asset_id = 0, .spend_pk = keys.spend_pk, .blinding = .{ 7, 8, 9, 10 } };
        for (&s.notes) |*n| {
            const cm = n.cm(h);
            _ = try s.pool.insert(cm);
            _ = try s.assoc.insert(cm);
        }
        return s;
    }

    fn deinit(s: *Scene) void {
        s.pool.deinit();
        s.assoc.deinit();
    }

    fn real(s: *const Scene, i: usize) !spend.Input {
        return .{ .real = .{ .note = s.notes[i], .pool = try s.pool.witness(i), .assoc = try s.assoc.witness(i) } };
    }

    fn transfer(s: *const Scene, rng: std.Random, out0: u64, out1: u64) !spend.Spend {
        return .{
            .note_root = s.pool.root(),
            .assoc_root = s.assoc.root(),
            .inputs = .{ try s.real(0), .{ .dummy = Note.fresh(rng, 0, 0, s.keys.spend_pk) } },
            .outputs = .{ Note.fresh(rng, out0, 0, s.keys.spend_pk), Note.fresh(rng, out1, 0, s.keys.spend_pk) },
            .public_amount = 0,
            .fee = 0,
            .asset_id = 0,
            .clearing_price = 0,
            .recipient = [_]u8{0} ** 20,
        };
    }
};

test "a_balanced_transfer_yields_the_intent_words_in_settle_order" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(11);
    const sp = try s.transfer(prng.random(), 700, 300);
    const secret = try key.Secret.fromLimbs(&.{ 17, 18, 19, 20 });
    const nk = secret.derive(&h).nk;
    const w = try sp.intent(&h, &nk);
    try expectEqual(s.pool.root(), w[spend.NOTE_ROOT..][0..4].*);
    try expectEqual(s.assoc.root(), w[spend.ASSOC_ROOT..][0..4].*);
    const cm0 = s.notes[0].cm(&h);
    try expectEqual(key.nullifier(&h, &nk, &cm0, 0, true), w[spend.NF0..][0..4].*);
    try expectEqual(sp.outputs[0].cm(&h), w[spend.OUT_CM0..][0..4].*);
    try expectEqual(sp.outputs[1].cm(&h), w[spend.OUT_CM1..][0..4].*);
    try expectEqual(0, w[spend.PUBLIC_AMOUNT]);
    try expectEqual(0, w[spend.FEE]);
    try expectEqual(digest.ZERO, w[spend.RECIPIENT..][0..4].*);
}

test "an_unbalanced_transfer_is_refused" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(12);
    const sp = try s.transfer(prng.random(), 700, 301);
    try expectError(error.Unbalanced, sp.check(&h, &s.keys.nk));
}

test "a_dummy_that_carries_value_is_refused_even_when_balanced" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(13);
    const rng = prng.random();
    var sp = try s.transfer(rng, 700, 301);
    sp.inputs[1] = .{ .dummy = Note.fresh(rng, 1, 0, s.keys.spend_pk) };
    try expectError(error.DummyCarriesValue, sp.check(&h, &s.keys.nk));
}

test "the_same_note_twice_is_a_double_spend" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(14);
    var sp = try s.transfer(prng.random(), 2000, 0);
    sp.inputs[1] = try s.real(0);
    try expectError(error.DoubleSpend, sp.check(&h, &s.keys.nk));
}

test "a_note_outside_the_pool_or_the_association_set_is_refused" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(15);
    var sp = try s.transfer(prng.random(), 700, 300);
    sp.note_root = digest.ZERO;
    try expectError(error.NotInPool, sp.check(&h, &s.keys.nk));
    sp.note_root = s.pool.root();
    sp.assoc_root = digest.ZERO;
    try expectError(error.NotInAssoc, sp.check(&h, &s.keys.nk));
}

test "a_transfer_names_no_recipient_and_pays_a_fee_only_to_a_named_submitter" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(16);
    var sp = try s.transfer(prng.random(), 700, 300);
    sp.fee = 1;
    sp.outputs[1].value = 299;
    try expectError(error.NoFeeRecipient, sp.check(&h, &s.keys.nk));
    sp.fee_recipient[19] = 0x5B;
    const w = try sp.intent(&h, &s.keys.nk);
    try expectEqual(1, w[spend.FEE]);
    try expectEqual(digest.Digest{ 0x5B, 0, 0, 0 }, w[spend.FEE_RECIPIENT..][0..4].*);
    try expectEqual(digest.ZERO, w[spend.RECIPIENT..][0..4].*);
    sp.fee = 0;
    sp.outputs[1].value = 300;
    try expectError(error.FeeRecipientWithoutFee, sp.check(&h, &s.keys.nk));
    sp.fee_recipient = [_]u8{0} ** 20;
    sp.recipient[19] = 1;
    try expectError(error.SettleFieldsOnTransfer, sp.check(&h, &s.keys.nk));
}

test "an_unshield_needs_a_recipient_and_carries_it_across_four_48_bit_limbs" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(17);
    var sp = try s.transfer(prng.random(), 0, 0);
    sp.public_amount = 990;
    sp.fee = 10;
    sp.fee_recipient[19] = 0x5B;
    try expectError(error.NoRecipient, sp.check(&h, &s.keys.nk));
    for (0..20) |i| sp.recipient[i] = @intCast(i + 1);
    const w = try sp.intent(&h, &s.keys.nk);
    try expectEqual(990, w[spend.PUBLIC_AMOUNT]);
    try expectEqual(10, w[spend.FEE]);
    try expectEqual(digest.Digest{ 0x0f1011121314, 0x090a0b0c0d0e, 0x030405060708, 0x0102 }, w[spend.RECIPIENT..][0..4].*);
}

test "an_asset_mismatch_is_refused" {
    const h = Poseidon.init();
    var s = try Scene.init(std.testing.allocator, &h);
    defer s.deinit();
    var prng = std.Random.DefaultPrng.init(18);
    var sp = try s.transfer(prng.random(), 700, 300);
    sp.outputs[0].asset_id = 1;
    try expectError(error.AssetMismatch, sp.check(&h, &s.keys.nk));
}
