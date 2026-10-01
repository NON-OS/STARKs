// NONOS Operating System (AGPL-3.0-or-later)
//! Notes are the money. The wallet keeps sk in RAM, mirrors the pool tree
//! from L1 leaves, opens memos by trial, and shapes every payment as two
//! inputs and two outputs with the second output always to itself. A note
//! is spent only once it is old enough that its absorb and its spend do not
//! sit next to each other on chain.
//!
//! Anonymity is the default (`anon.Policy`): every spend goes out through a
//! submitter the relay fee pays, payee notes and public amounts come in
//! standard sizes, a payment carries the earliest block it may be submitted,
//! and withdrawals go to a fresh address derived for that withdrawal alone.
//! Turning any of it off is a named policy field, listed by
//! `Policy.warnings`.

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const tree = @import("tree.zig");
const spend = @import("spend.zig");
const memo = @import("memo.zig");
const anon = @import("anon/mod.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const Allocator = std.mem.Allocator;

/// Blocks a note waits after its leaf lands before the wallet will spend it.
pub const MIN_AGE: u64 = 32;

pub const Error = error{
    MemoLeafMismatch,
    NotAttested,
    Insufficient,
    Immature,
    NeedsChain,
    UnknownNote,
    /// No submitter is configured and self-submission is not opted into.
    NoSubmitter,
    /// A payee amount or a public amount outside the standard sizes.
    NonStandardAmount,
    /// An asset with no standard unit in the table, and none in the policy.
    UnknownAsset,
    /// A withdrawal to an address this wallet did not derive for it, or to
    /// one a withdrawal already used.
    RecipientNotFresh,
} || tree.Error || spend.Error || memo.Error || anon.fresh.Error || Allocator.Error;

pub const Owned = struct {
    note: Note,
    leaf_index: usize,
    /// The block the leaf landed in.
    block: u64,
    /// The registry's opening under the association set; none until attested.
    assoc: ?tree.Witness,
    spent: bool,
};

const Issued = struct {
    address: [20]u8,
    used: bool,
};

pub const Payment = struct {
    spend: spend.Spend,
    intent: [spend.WORDS]field.Fp,
    /// memos[i] opens outputs[i]; one is the payee's, one is the payer's own.
    memos: [2]memo.Memo,
    /// The earliest block the payment may be submitted in.
    window: anon.timing.Window,
};

/// A withdrawal and the fresh address it pays. The address's key is the
/// caller's to keep; `fresh.wipe()` clears this copy.
pub const Withdrawal = struct {
    payment: Payment,
    fresh: anon.fresh.Fresh,
};

const Settle = struct {
    public_amount: u64,
    fee: u64,
    clearing_price: u64,
    recipient: [20]u8,
    fee_recipient: [20]u8 = [_]u8{0} ** 20,
};

const TRANSFER: Settle = .{ .public_amount = 0, .fee = 0, .clearing_price = 0, .recipient = [_]u8{0} ** 20 };

pub const Wallet = struct {
    alloc: Allocator,
    h: *const Poseidon,
    secret: key.Secret,
    keys: key.Keys,
    view: memo.ViewKey,
    tree: tree.Tree,
    owned: std.ArrayListUnmanaged(Owned),
    min_age: u64,
    policy: anon.Policy,
    /// The next fresh withdrawal index, and every address issued so far with
    /// whether a withdrawal used it.
    fresh_next: u64,
    issued: std.ArrayListUnmanaged(Issued),

    pub fn init(alloc: Allocator, h: *const Poseidon, seed: *const [32]u8) memo.Error!Wallet {
        var secret = key.Secret.fromSeed(seed);
        errdefer secret.wipe();
        const view = try memo.ViewKey.fromSecret(&secret);
        return .{
            .alloc = alloc,
            .h = h,
            .secret = secret,
            .keys = secret.derive(h),
            .view = view,
            .tree = tree.Tree.init(alloc, h),
            .owned = .{},
            .min_age = MIN_AGE,
            .policy = .{},
            .fresh_next = 0,
            .issued = .{},
        };
    }

    pub fn deinit(self: *Wallet) void {
        for (self.owned.items) |*o| o.note.wipe();
        self.owned.deinit(self.alloc);
        self.issued.deinit(self.alloc);
        self.tree.deinit();
        self.view.wipe();
        self.secret.wipe();
    }

    pub fn address(self: *const Wallet) memo.Address {
        return self.view.address(self.keys.spend_pk);
    }

    /// Every leaf the pool commits, in order, ours or not.
    pub fn absorb(self: *Wallet, cm: Digest) tree.Error!usize {
        return self.tree.insert(cm);
    }

    /// Ours when the memo opens and its note, under our spend key, commits to
    /// the leaf. The opening carries no key, so a note sealed to our view key
    /// but committed under a foreign spend key fails that check and is named.
    pub fn receive(self: *Wallet, m: *const memo.Memo, leaf_index: usize, block: u64) Error!bool {
        const cm = try self.tree.leaf(leaf_index);
        var n = memo.open(&self.view, m, &cm, self.keys.spend_pk) catch |e| {
            if (e == error.NotForUs) return false;
            return e;
        };
        defer n.wipe();
        if (!digest.eql(&n.cm(self.h), &cm)) return error.MemoLeafMismatch;
        try self.owned.append(self.alloc, .{
            .note = n,
            .leaf_index = leaf_index,
            .block = block,
            .assoc = null,
            .spent = false,
        });
        return true;
    }

    pub fn attest(self: *Wallet, leaf_index: usize, w: tree.Witness) Error!void {
        for (self.owned.items) |*o| {
            if (o.leaf_index == leaf_index) {
                o.assoc = w;
                return;
            }
        }
        return error.UnknownNote;
    }

    /// A payment that did not settle gives its inputs back.
    pub fn release(self: *Wallet, p: *const Payment) void {
        for (&p.spend.inputs) |*in| {
            switch (in.*) {
                .real => |*r| self.mark(r.pool.leaf_index, false),
                .dummy => {},
            }
        }
    }

    fn mark(self: *Wallet, leaf_index: u64, spent: bool) void {
        for (self.owned.items) |*o| {
            if (o.leaf_index == leaf_index) o.spent = spent;
        }
    }

    fn usable(o: *const Owned, asset_id: u64) bool {
        return !o.spent and o.note.asset_id == asset_id;
    }

    fn mature(self: *const Wallet, o: *const Owned, now: u64) bool {
        return now >= o.block and now - o.block >= self.min_age;
    }

    pub fn balance(self: *const Wallet, asset_id: u64) u64 {
        var sum: u64 = 0;
        for (self.owned.items) |*o| {
            if (usable(o, asset_id)) sum +|= o.note.value;
        }
        return sum;
    }

    /// What can be spent at block `now`.
    pub fn spendable(self: *const Wallet, asset_id: u64, now: u64) u64 {
        var sum: u64 = 0;
        for (self.owned.items) |*o| {
            if (usable(o, asset_id) and self.mature(o, now)) sum +|= o.note.value;
        }
        return sum;
    }

    /// A private transfer, sent the way the policy says: through its
    /// submitter for its relay fee, or refused when there is none and
    /// self-submission is not opted into. The amount is a standard size.
    pub fn pay(self: *Wallet, rng: std.Random, to: *const memo.Address, value: u64, asset_id: u64, assoc_root: Digest, now: u64) Error!Payment {
        try self.standard(value, asset_id);
        return self.build(rng, to, value, asset_id, assoc_root, try self.transferSettle(), now);
    }

    /// The settle fields a transfer carries under the policy.
    fn transferSettle(self: *const Wallet) Error!Settle {
        if (self.policy.submitter) |sub| {
            return .{ .public_amount = 0, .fee = self.policy.relay_fee, .clearing_price = 0, .recipient = [_]u8{0} ** 20, .fee_recipient = if (self.policy.relay_fee != 0) sub else [_]u8{0} ** 20 };
        }
        if (!self.policy.self_submit) return error.NoSubmitter;
        return TRANSFER;
    }

    fn standard(self: *const Wallet, value: u64, asset_id: u64) Error!void {
        if (!self.policy.standard_notes) return;
        const unit = self.policy.unit orelse anon.denom.unitFor(asset_id) orelse return error.UnknownAsset;
        if (!anon.denom.isStandard(value, unit)) return error.NonStandardAmount;
    }

    /// How many notes a spend of our note at `leaf_index` hides among.
    pub fn anonymitySet(self: *const Wallet, leaf_index: usize) anon.set.Set {
        return anon.set.measure(self.tree.len(), leaf_index, self.policy.min_set);
    }

    /// The next fresh withdrawal address, recorded as issued.
    pub fn freshAddress(self: *Wallet) Error!anon.fresh.Fresh {
        var sb = self.secret.bytes();
        defer std.crypto.secureZero(u8, &sb);
        const f = try anon.fresh.derive(&sb, self.fresh_next);
        try self.issued.append(self.alloc, .{ .address = f.address, .used = false });
        self.fresh_next += 1;
        return f;
    }

    /// Value out of the pool to a fresh address derived for it alone, through
    /// the policy's submitter; the relay fee pays the gas, so the address
    /// needs no funding. `value` is a standard size.
    pub fn withdraw(self: *Wallet, rng: std.Random, value: u64, asset_id: u64, clearing_price: u64, assoc_root: Digest, now: u64) Error!Withdrawal {
        if (self.policy.submitter == null and !self.policy.self_submit) return error.NoSubmitter;
        try self.standard(value, asset_id);
        var f = try self.freshAddress();
        errdefer f.wipe();
        const sub = self.policy.submitter orelse [_]u8{0} ** 20;
        const fee = if (self.policy.submitter != null) self.policy.relay_fee else 0;
        const p = try self.unshield(rng, f.address, value, fee, if (fee != 0) sub else [_]u8{0} ** 20, asset_id, clearing_price, assoc_root, now);
        return .{ .payment = p, .fresh = f };
    }

    /// A private transfer someone else submits: `fee` pays `submitter`, and
    /// the proof binds both, so the transaction carries nothing of the
    /// sender's and a copier cannot take the fee.
    pub fn payVia(self: *Wallet, rng: std.Random, to: *const memo.Address, value: u64, asset_id: u64, assoc_root: Digest, fee: u64, submitter: [20]u8, now: u64) Error!Payment {
        try self.standard(value, asset_id);
        const st: Settle = .{ .public_amount = 0, .fee = fee, .clearing_price = 0, .recipient = [_]u8{0} ** 20, .fee_recipient = submitter };
        return self.build(rng, to, value, asset_id, assoc_root, st, now);
    }

    /// Value leaves the pool to an L1 address; both note outputs stay ours.
    /// `fee_recipient` is the submitter a nonzero fee pays, zero when fee is.
    /// Under the default policy the recipient must be a fresh address this
    /// wallet issued and no withdrawal used, and `value` a standard size.
    pub fn unshield(self: *Wallet, rng: std.Random, recipient: [20]u8, value: u64, fee: u64, fee_recipient: [20]u8, asset_id: u64, clearing_price: u64, assoc_root: Digest, now: u64) Error!Payment {
        try self.standard(value, asset_id);
        const slot = self.issuedSlot(recipient);
        if (self.policy.fresh_withdrawals) {
            const s = slot orelse return error.RecipientNotFresh;
            if (s.used) return error.RecipientNotFresh;
        }
        const me = self.address();
        const st: Settle = .{ .public_amount = value, .fee = fee, .clearing_price = clearing_price, .recipient = recipient, .fee_recipient = fee_recipient };
        const p = try self.build(rng, &me, 0, asset_id, assoc_root, st, now);
        if (slot) |s| s.used = true;
        return p;
    }

    fn issuedSlot(self: *Wallet, a: [20]u8) ?*Issued {
        for (self.issued.items) |*i| {
            if (std.mem.eql(u8, &i.address, &a)) return i;
        }
        return null;
    }

    /// The two largest mature notes into one note to self: the step a
    /// payment above any two notes runs first. On chain it is a transfer.
    pub fn merge(self: *Wallet, rng: std.Random, asset_id: u64, assoc_root: Digest, now: u64) Error!Payment {
        const two = try self.largestTwo(asset_id, now);
        const s = two[1] orelse return error.NeedsChain;
        const me = self.address();
        const total = @as(u128, two[0].?.note.value) + s.note.value;
        if (total > std.math.maxInt(u64)) return error.ValueOverflow;
        return self.build(rng, &me, @intCast(total), asset_id, assoc_root, try self.transferSettle(), now);
    }

    fn build(self: *Wallet, rng: std.Random, to: *const memo.Address, value: u64, asset_id: u64, assoc_root: Digest, st: Settle, now: u64) Error!Payment {
        const need: u128 = @as(u128, value) + st.public_amount + st.fee;
        const picked = try self.select(asset_id, need, now);
        var inputs: [2]spend.Input = undefined;
        var have: u128 = 0;
        for (0..2) |i| {
            if (picked[i]) |o| {
                inputs[i] = .{ .real = .{
                    .note = o.note,
                    .pool = try self.tree.witness(o.leaf_index),
                    .assoc = o.assoc orelse return error.NotAttested,
                } };
                have += o.note.value;
            } else {
                inputs[i] = .{ .dummy = Note.fresh(rng, 0, asset_id, self.keys.spend_pk) };
            }
        }
        const change: u64 = @intCast(have - need);
        var outputs: [2]Note = .{
            Note.fresh(rng, value, asset_id, to.spend_pk),
            Note.fresh(rng, change, asset_id, self.keys.spend_pk),
        };
        var addrs: [2]memo.Address = .{ to.*, self.address() };
        if (rng.boolean()) {
            std.mem.swap(Note, &outputs[0], &outputs[1]);
            std.mem.swap(memo.Address, &addrs[0], &addrs[1]);
        }
        if (rng.boolean()) std.mem.swap(spend.Input, &inputs[0], &inputs[1]);
        const s: spend.Spend = .{
            .note_root = self.tree.root(),
            .assoc_root = assoc_root,
            .inputs = inputs,
            .outputs = outputs,
            .public_amount = st.public_amount,
            .fee = st.fee,
            .asset_id = asset_id,
            .clearing_price = st.clearing_price,
            .recipient = st.recipient,
            .fee_recipient = st.fee_recipient,
        };
        const intent = try s.intent(self.h, &self.keys.nk);
        var memos: [2]memo.Memo = undefined;
        for (0..2) |i| {
            const cm = outputs[i].cm(self.h);
            memos[i] = try memo.seal(rng, &addrs[i], &outputs[i], &cm);
        }
        for (picked) |p| {
            if (p) |o| o.spent = true;
        }
        return .{ .spend = s, .intent = intent, .memos = memos, .window = anon.timing.draw(rng, now, &self.policy) };
    }

    fn largestTwo(self: *Wallet, asset_id: u64, now: u64) Error![2]?*Owned {
        var best: ?*Owned = null;
        var second: ?*Owned = null;
        for (self.owned.items) |*o| {
            if (!usable(o, asset_id) or !self.mature(o, now)) continue;
            if (best == null or o.note.value > best.?.note.value) {
                second = best;
                best = o;
            } else if (second == null or o.note.value > second.?.note.value) {
                second = o;
            }
        }
        if (best == null) {
            return if (self.balance(asset_id) > 0) error.Immature else error.Insufficient;
        }
        return .{ best, second };
    }

    /// Largest first: one note when it covers the amount, else the two
    /// largest, else `merge` first. Immature when the balance would cover it
    /// but the mature part does not.
    fn select(self: *Wallet, asset_id: u64, need: u128, now: u64) Error![2]?*Owned {
        const two = try self.largestTwo(asset_id, now);
        const b = two[0].?;
        if (b.note.value >= need) return .{ b, null };
        const s = two[1] orelse return self.short(asset_id, need, now);
        if (@as(u128, b.note.value) + s.note.value >= need) return .{ b, s };
        return self.short(asset_id, need, now);
    }

    fn short(self: *Wallet, asset_id: u64, need: u128, now: u64) Error {
        if (self.spendable(asset_id, now) >= need) return error.NeedsChain;
        if (self.balance(asset_id) >= need) return error.Immature;
        return error.Insufficient;
    }
};
