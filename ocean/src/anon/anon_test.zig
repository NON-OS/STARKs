// NONOS Operating System (AGPL-3.0-or-later)
//! Each anonymity default, and that the wallet applies it without being
//! asked.

const std = @import("std");
const poseidon = @import("../poseidon.zig");
const note = @import("../note.zig");
const tree = @import("../tree.zig");
const memo = @import("../memo.zig");
const spend = @import("../spend.zig");
const field = @import("../field.zig");
const wallet = @import("../wallet.zig");
const anon = @import("mod.zig");
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const Wallet = wallet.Wallet;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const U = anon.policy.UNIT;
const LANDED: u64 = 100;
const NOW: u64 = LANDED + wallet.MIN_AGE + 68;
const SUBMITTER: [20]u8 = [_]u8{0x5B} ** 20;

test "the_default_policy_weakens_nothing_and_the_unprotected_one_says_so" {
    var buf: [5]anon.Policy.Warning = undefined;
    const d: anon.Policy = .{};
    try expectEqual(0, d.warnings(&buf).len);
    const u = anon.Policy.unprotected();
    try expectEqual(5, u.warnings(&buf).len);
}

test "standard_sizes_are_the_one_two_five_series_of_the_unit" {
    for ([_]u64{ 1, 2, 5, 10, 20, 50, 100, 1000, 5000 }) |m| try expect(anon.denom.isStandard(m * U, U));
    for ([_]u64{ 3, 4, 6, 7, 9, 11, 15, 25, 150 }) |m| try expect(!anon.denom.isStandard(m * U, U));
    try expect(!anon.denom.isStandard(0, U));
    try expect(!anon.denom.isStandard(U + 1, U));
    try expectEqual(@as(u64, 5 * U), anon.denom.largestAtMost(9 * U, U));
    try expectEqual(@as(u64, 0), anon.denom.largestAtMost(U - 1, U));
    // The top of the range: no overflow walking the decades.
    try expect(anon.denom.largestAtMost(std.math.maxInt(u64), 1) > 0);
}

test "the_standard_unit_follows_the_asset" {
    try expectEqual(@as(?u64, 1_000_000_000_000_000), anon.denom.unitFor(0));
    try expectEqual(@as(?u64, 1_000_000), anon.denom.unitFor(1));
    try expectEqual(@as(?u64, null), anon.denom.unitFor(9));
    // 0.005 NOX in note units is standard for NOX and not a multiple of the ETH unit.
    try expect(anon.denom.isStandard(5_000_000, anon.denom.unitFor(1).?));
    try expect(!anon.denom.isStandard(5_000_000, anon.denom.unitFor(0).?));
}

test "an_amount_splits_into_the_fewest_standard_pieces" {
    // 1.370 in units of 0.001: 1 + 0.2 + 0.1 + 0.05 + 0.02.
    const p = anon.denom.split(1370 * U + 7, U);
    try expectEqual(@as(u64, 7), p.rest);
    const want = [_]u64{ 1000 * U, 200 * U, 100 * U, 50 * U, 20 * U };
    try std.testing.expectEqualSlices(u64, &want, p.slice());
    var sum: u64 = p.rest;
    for (p.slice()) |x| {
        try expect(anon.denom.isStandard(x, U));
        sum += x;
    }
    try expectEqual(1370 * U + 7, sum);
}

test "a_payment_waits_a_draw_from_the_window_and_never_less_than_the_minimum" {
    var prng = std.Random.DefaultPrng.init(3);
    const p: anon.Policy = .{};
    var saw_spread = false;
    var first: ?u64 = null;
    for (0..200) |_| {
        const w = anon.timing.draw(prng.random(), 1000, &p);
        try expect(w.not_before >= 1000 + p.delay_min and w.not_before <= 1000 + p.delay_max);
        try expect(!w.ready(w.not_before - 1) and w.ready(w.not_before));
        if (first) |f| {
            if (f != w.not_before) saw_spread = true;
        } else first = w.not_before;
    }
    try expect(saw_spread);
    const reversed: anon.Policy = .{ .delay_min = 50, .delay_max = 10 };
    try expectEqual(@as(u64, 1050), anon.timing.draw(prng.random(), 1000, &reversed).not_before);
}

test "a_fresh_address_is_the_ethereum_address_of_its_key" {
    // Private key 1: the generator's address, the published vector.
    var one = [_]u8{0} ** 32;
    one[31] = 1;
    const a = try anon.fresh.addressOf(&one);
    var want: [20]u8 = undefined;
    _ = try std.fmt.hexToBytes(&want, "7e5f4552091a69125d5dfcb7b8c2659029395bdf");
    try expectEqual(want, a);

    const secret = [_]u8{9} ** 32;
    var f0 = try anon.fresh.derive(&secret, 0);
    defer f0.wipe();
    var f0b = try anon.fresh.derive(&secret, 0);
    defer f0b.wipe();
    var f1 = try anon.fresh.derive(&secret, 1);
    defer f1.wipe();
    try expectEqual(f0.address, f0b.address);
    try expect(!std.mem.eql(u8, &f0.address, &f1.address));
    try expectEqual(f0.address, try anon.fresh.addressOf(&f0.sk));
    var other = try anon.fresh.derive(&([_]u8{8} ** 32), 0);
    defer other.wipe();
    try expect(!std.mem.eql(u8, &f0.address, &other.address));
}

test "the_anonymity_set_counts_what_landed_since_and_warns_when_small" {
    const s = anon.set.measure(250, 100, 100);
    try expectEqual(@as(usize, 250), s.total);
    try expectEqual(@as(usize, 149), s.since);
    try expect(!s.small);
    try expect(anon.set.measure(150, 100, 100).small);
    try expectEqual(@as(usize, 0), anon.set.measure(10, 20, 100).since);
}

/// A default-policy wallet holding one attested note of `value`.
const Funded = struct {
    w: Wallet,
    assoc: tree.Tree,

    fn init(h: *const Poseidon, rng: std.Random, value: u64) !Funded {
        const alloc = std.testing.allocator;
        var w = try Wallet.init(alloc, h, &([_]u8{7} ** 32));
        errdefer w.deinit();
        var assoc = tree.Tree.init(alloc, h);
        errdefer assoc.deinit();
        const n = Note.fresh(rng, value, 0, w.keys.spend_pk);
        const cm = n.cm(h);
        const at = try w.absorb(cm);
        _ = try assoc.insert(cm);
        const m = try memo.seal(rng, &w.address(), &n, &cm);
        try expect(try w.receive(&m, at, LANDED));
        try w.attest(at, try assoc.witness(at));
        return .{ .w = w, .assoc = assoc };
    }

    fn deinit(f: *Funded) void {
        f.w.deinit();
        f.assoc.deinit();
    }
};

test "by_default_a_payment_goes_through_a_submitter_or_not_at_all" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(41);
    const rng = prng.random();
    var f = try Funded.init(&h, rng, 10 * U);
    defer f.deinit();
    var payee = try Wallet.init(std.testing.allocator, &h, &([_]u8{6} ** 32));
    defer payee.deinit();

    try expectError(error.NoSubmitter, f.w.pay(rng, &payee.address(), 5 * U, 0, f.assoc.root(), NOW));

    f.w.policy.submitter = SUBMITTER;
    f.w.policy.relay_fee = U;
    const p = try f.w.pay(rng, &payee.address(), 5 * U, 0, f.assoc.root(), NOW);
    try expectEqual(field.reduce(U), p.intent[spend.FEE]);
    try expectEqual(spend.addressLimbs(&SUBMITTER), p.intent[spend.FEE_RECIPIENT..][0..4].*);
    try expect(p.window.not_before >= NOW + anon.policy.DELAY_MIN);
}

test "by_default_a_payee_amount_is_a_standard_size" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(42);
    const rng = prng.random();
    var f = try Funded.init(&h, rng, 10 * U);
    defer f.deinit();
    f.w.policy.submitter = SUBMITTER;
    var payee = try Wallet.init(std.testing.allocator, &h, &([_]u8{6} ** 32));
    defer payee.deinit();
    try expectError(error.NonStandardAmount, f.w.pay(rng, &payee.address(), 3 * U, 0, f.assoc.root(), NOW));
}

test "by_default_a_withdrawal_goes_to_a_fresh_address_used_once" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(43);
    const rng = prng.random();
    var f = try Funded.init(&h, rng, 10 * U);
    defer f.deinit();
    f.w.policy.submitter = SUBMITTER;
    f.w.policy.relay_fee = U;

    const foreign: [20]u8 = [_]u8{0xAA} ** 20;
    try expectError(error.RecipientNotFresh, f.w.unshield(rng, foreign, 5 * U, U, SUBMITTER, 0, 1, f.assoc.root(), NOW));

    var wd = try f.w.withdraw(rng, 5 * U, 0, 1, f.assoc.root(), NOW);
    defer wd.fresh.wipe();
    try expectEqual(spend.addressLimbs(&wd.fresh.address), wd.payment.intent[spend.RECIPIENT..][0..4].*);
    try expectEqual(wd.fresh.address, try anon.fresh.addressOf(&wd.fresh.sk));

    // The address is spent: a second withdrawal to it is refused.
    f.w.release(&wd.payment);
    try expectError(error.RecipientNotFresh, f.w.unshield(rng, wd.fresh.address, 5 * U, U, SUBMITTER, 0, 1, f.assoc.root(), NOW));
}

test "scanning_absorbs_every_leaf_keeps_ours_and_refuses_a_gap" {
    const h = Poseidon.init();
    var prng = std.Random.DefaultPrng.init(44);
    const rng = prng.random();
    var w = try Wallet.init(std.testing.allocator, &h, &([_]u8{7} ** 32));
    defer w.deinit();
    var other = try Wallet.init(std.testing.allocator, &h, &([_]u8{5} ** 32));
    defer other.deinit();

    var events: [4]anon.scan.Event = undefined;
    for (0..4) |i| {
        const mine = i % 2 == 0;
        const who = if (mine) &w else &other;
        const n = Note.fresh(rng, (i + 1) * U, 0, who.keys.spend_pk);
        const cm = n.cm(&h);
        events[i] = .{ .leaf_index = i, .cm = cm, .memo = try memo.seal(rng, &who.address(), &n, &cm), .block = LANDED };
    }
    const r = try anon.scan.scan(&w, &events);
    try expectEqual(@as(usize, 4), r.absorbed);
    try expectEqual(@as(usize, 2), r.ours);
    try expectEqual(@as(u64, 4 * U), w.balance(0));

    var skip = events[0];
    skip.leaf_index = 9;
    try expectError(error.Gap, anon.scan.scan(&w, &[_]anon.scan.Event{skip}));
}
