// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const note = @import("note.zig");
const tree = @import("tree.zig");
const memo = @import("memo.zig");
const wallet = @import("wallet.zig");
const anon = @import("anon/mod.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const Wallet = wallet.Wallet;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const SEED_A = [_]u8{1} ** 32;
const SEED_B = [_]u8{2} ** 32;
/// Every note in these tests lands at block 100 and is spent at block 200.
const LANDED: u64 = 100;
const NOW: u64 = LANDED + wallet.MIN_AGE + 68;

const Pair = struct {
    a: Wallet,
    b: Wallet,
    assoc: tree.Tree,

    fn init(h: *const Poseidon) !Pair {
        const alloc = std.testing.allocator;
        var a = try Wallet.init(alloc, h, &SEED_A);
        errdefer a.deinit();
        var b = try Wallet.init(alloc, h, &SEED_B);
        errdefer b.deinit();
        // These tests drive the protocol itself: amounts, change and
        // settlement. The anonymity defaults are anon_test.zig's.
        a.policy = anon.Policy.unprotected();
        b.policy = anon.Policy.unprotected();
        return .{ .a = a, .b = b, .assoc = tree.Tree.init(alloc, h) };
    }

    fn deinit(p: *Pair) void {
        p.a.deinit();
        p.b.deinit();
        p.assoc.deinit();
    }

    /// One funded note for a, absorbed by both wallets and the registry.
    fn fund(p: *Pair, h: *const Poseidon, rng: std.Random, value: u64, block: u64) !usize {
        const n = Note.fresh(rng, value, 0, p.a.keys.spend_pk);
        const cm = n.cm(h);
        const ia = try p.a.absorb(cm);
        _ = try p.b.absorb(cm);
        _ = try p.assoc.insert(cm);
        const m = try memo.seal(rng, &p.a.address(), &n, &cm);
        try expect(try p.a.receive(&m, ia, block));
        try expect(!(try p.b.receive(&m, ia, block)));
        try p.reattest();
        return ia;
    }

    /// Settlement as both wallets see it: the two outputs land as leaves at
    /// `block`, and the registry lists them.
    fn settle(p: *Pair, h: *const Poseidon, pay: *const wallet.Payment, block: u64) !void {
        const cms = pay.spend.outCm(h);
        for (0..2) |i| {
            const ia = try p.a.absorb(cms[i]);
            const ib = try p.b.absorb(cms[i]);
            _ = try p.assoc.insert(cms[i]);
            _ = try p.a.receive(&pay.memos[i], ia, block);
            _ = try p.b.receive(&pay.memos[i], ib, block);
        }
        try p.reattest();
    }

    /// An association opening is only valid against the root it was taken at,
    /// so every witness is retaken whenever the registry grows. A wallet that
    /// keeps the one it was given is a wallet whose next payment is refused
    /// with NotInAssoc for a note it genuinely owns.
    ///
    /// These tests insert into the pool and the registry in one order, so a
    /// note's leaf index is its registry index too.
    fn reattest(p: *Pair) !void {
        for ([_]*Wallet{ &p.a, &p.b }) |w| {
            for (w.owned.items) |*o| {
                try w.attest(o.leaf_index, try p.assoc.witness(o.leaf_index));
            }
        }
    }
};

test "a_payment_lands_in_the_payee_and_change_returns_to_the_payer" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(31);
    const rng = prng.random();
    _ = try p.fund(&h, rng, 1000, LANDED);
    try expectEqual(1000, p.a.balance(0));
    try expectEqual(0, p.b.balance(0));

    const pay = try p.a.pay(rng, &p.b.address(), 300, 0, p.assoc.root(), NOW);
    try expectEqual(0, pay.intent[24]);
    try expectEqual(0, p.a.balance(0));

    try p.settle(&h, &pay, NOW + 1);
    try expectEqual(300, p.b.balance(0));
    try expectEqual(700, p.a.balance(0));
}

test "a_note_is_not_spent_before_it_is_old_enough" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(32);
    const rng = prng.random();
    _ = try p.fund(&h, rng, 1000, LANDED);
    try expectError(error.Immature, p.a.pay(rng, &p.b.address(), 300, 0, p.assoc.root(), LANDED));
    try expectError(error.Immature, p.a.pay(rng, &p.b.address(), 300, 0, p.assoc.root(), LANDED + wallet.MIN_AGE - 1));
    try expectEqual(0, p.a.spendable(0, LANDED));
    try expectEqual(1000, p.a.spendable(0, LANDED + wallet.MIN_AGE));
    _ = try p.a.pay(rng, &p.b.address(), 300, 0, p.assoc.root(), LANDED + wallet.MIN_AGE);
}

test "a_payment_that_did_not_settle_gives_its_inputs_back" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(33);
    const rng = prng.random();
    _ = try p.fund(&h, rng, 1000, LANDED);
    const pay = try p.a.pay(rng, &p.b.address(), 300, 0, p.assoc.root(), NOW);
    try expectEqual(0, p.a.balance(0));
    p.a.release(&pay);
    try expectEqual(1000, p.a.balance(0));
}

test "an_unattested_note_cannot_be_spent" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(34);
    const rng = prng.random();
    const n = Note.fresh(rng, 50, 0, p.a.keys.spend_pk);
    const cm = n.cm(&h);
    const ia = try p.a.absorb(cm);
    const m = try memo.seal(rng, &p.a.address(), &n, &cm);
    try expect(try p.a.receive(&m, ia, LANDED));
    try expectError(error.NotAttested, p.a.pay(rng, &p.b.address(), 10, 0, p.assoc.root(), NOW));
}

test "two_notes_merge_and_a_payment_above_them_needs_a_chain" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(35);
    const rng = prng.random();
    _ = try p.fund(&h, rng, 600, LANDED);
    _ = try p.fund(&h, rng, 500, LANDED);
    _ = try p.fund(&h, rng, 400, LANDED);
    try expectError(error.Insufficient, p.a.pay(rng, &p.b.address(), 1501, 0, p.assoc.root(), NOW));
    try expectError(error.NeedsChain, p.a.pay(rng, &p.b.address(), 1200, 0, p.assoc.root(), NOW));

    const merged = try p.a.merge(rng, 0, p.assoc.root(), NOW);
    try expectEqual(0, merged.intent[24]);
    try p.settle(&h, &merged, NOW + 1);
    try expectEqual(1500, p.a.balance(0));
    try expectEqual(0, p.b.balance(0));

    const later = NOW + 1 + wallet.MIN_AGE;
    const pay = try p.a.pay(rng, &p.b.address(), 1200, 0, p.assoc.root(), later);
    try p.settle(&h, &pay, later + 1);
    try expectEqual(1200, p.b.balance(0));
    try expectEqual(300, p.a.balance(0));
}

test "a_memo_under_our_view_key_but_a_foreign_spend_key_does_not_commit" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(36);
    const rng = prng.random();
    const n = Note.fresh(rng, 5, 0, p.b.keys.spend_pk);
    const cm = n.cm(&h);
    const ia = try p.a.absorb(cm);
    const to = p.a.view.address(p.b.keys.spend_pk);
    try expect(!digest.eql(&to.spend_pk, &p.a.keys.spend_pk));
    const m = try memo.seal(rng, &to, &n, &cm);
    try expectError(error.MemoLeafMismatch, p.a.receive(&m, ia, LANDED));
}

test "a_memo_whose_note_does_not_commit_to_its_leaf_is_named" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    var prng = std.Random.DefaultPrng.init(37);
    const rng = prng.random();
    const n = Note.fresh(rng, 5, 0, p.a.keys.spend_pk);
    const other = digest.tag(9);
    const ia = try p.a.absorb(other);
    const m = try memo.seal(rng, &p.a.address(), &n, &other);
    try expectError(error.MemoLeafMismatch, p.a.receive(&m, ia, LANDED));
}

test "the_wallet_never_exposes_more_than_its_address" {
    const h = Poseidon.init();
    var p = try Pair.init(&h);
    defer p.deinit();
    const addr = p.a.address();
    try expectEqual(p.a.keys.spend_pk, addr.spend_pk);
    try expectEqual(p.a.view.ek, addr.ek);
    try expect(!digest.eql(&p.a.secret.sk, &addr.spend_pk));
    try expect(!digest.eql(&p.a.keys.nk, &addr.spend_pk));
}
