// NONOS Operating System (AGPL-3.0-or-later)
//! One statement shape: two inputs, two outputs. The intent is the 32 words
//! settleBatch decodes, in the order stark_proofs shield::join::publics fixes.

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const key = @import("key.zig");
const note = @import("note.zig");
const tree = @import("tree.zig");
const Fp = field.Fp;
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;
const Note = note.Note;
const Witness = tree.Witness;

pub const WORDS = 36;
pub const NOTE_ROOT = 0;
pub const ASSOC_ROOT = 4;
pub const NF0 = 8;
pub const NF1 = 12;
pub const OUT_CM0 = 16;
pub const OUT_CM1 = 20;
pub const PUBLIC_AMOUNT = 24;
pub const FEE = 25;
pub const ASSET_ID = 26;
pub const CLEARING_PRICE = 27;
pub const RECIPIENT = 28;
pub const FEE_RECIPIENT = 32;
/// Word 36 of the 37-word statement the production pool settles: the earliest
/// time, Unix seconds, the pool may settle the proof. It sits on a grid of
/// `NOT_BEFORE_GRID_S`, so every proof released into one slot carries the same
/// value and the draw that chose it is not a fingerprint.
pub const NOT_BEFORE = 36;
pub const WORDS_NOT_BEFORE = 37;
pub const NOT_BEFORE_GRID_S: u64 = 600;

pub const Error = error{
    Unbalanced,
    ValueOverflow,
    AssetMismatch,
    DummyCarriesValue,
    DoubleSpend,
    NotInPool,
    NotInAssoc,
    SettleFieldsOnTransfer,
    NoRecipient,
    NoFeeRecipient,
    FeeRecipientWithoutFee,
    NotBeforeOffGrid,
};

pub const Real = struct {
    note: Note,
    pool: Witness,
    /// Opening of cm under the association set root.
    assoc: Witness,
};

/// A dummy input carries value 0 and no leaf. Its nullifier still enters the
/// set: cm is fresh per blinding, so the nullifier is fresh and unlinkable.
pub const Input = union(enum) {
    real: Real,
    dummy: Note,

    pub fn noteOf(self: *const Input) *const Note {
        return switch (self.*) {
            .real => |*r| &r.note,
            .dummy => |*n| n,
        };
    }

    pub fn leafIndex(self: *const Input) u64 {
        return switch (self.*) {
            .real => |*r| r.pool.leaf_index,
            .dummy => 0,
        };
    }
};

pub const Spend = struct {
    note_root: Digest,
    assoc_root: Digest,
    inputs: [2]Input,
    outputs: [2]Note,
    public_amount: u64,
    fee: u64,
    asset_id: u64,
    clearing_price: u64,
    /// 20 bytes, all zero on a transfer.
    recipient: [20]u8,
    /// Who the fee pays: the submitter the spender chose, bound by the proof
    /// so a copier cannot redirect it. Named exactly when the fee is nonzero,
    /// on a transfer as on an unshield: that is how a transfer is submitted
    /// by someone other than its sender.
    fee_recipient: [20]u8 = [_]u8{0} ** 20,

    pub fn nullifiers(self: *const Spend, h: *const Poseidon, nk: *const Digest) [2]Digest {
        var nf: [2]Digest = undefined;
        for (0..2) |i| {
            const n = self.inputs[i].noteOf();
            const cm = n.cm(h);
            // Liveness is the value, as the circuit decides it: the gate
            // recomposes the two limbs, so a note worth exactly p is worth zero
            // there and the two sides would disagree about which word to hash.
            nf[i] = key.nullifier(h, nk, &cm, self.inputs[i].leafIndex(), field.reduce(n.value) != 0);
        }
        return nf;
    }

    pub fn outCm(self: *const Spend, h: *const Poseidon) [2]Digest {
        return .{ self.outputs[0].cm(h), self.outputs[1].cm(h) };
    }

    pub fn isTransfer(self: *const Spend) bool {
        return self.public_amount == 0;
    }

    /// Everything the settler or the circuit would refuse, checked before
    /// anything is signed: one asset, balance, dummies at zero, both openings,
    /// distinct nullifiers, no price or recipient on a transfer, and a fee
    /// recipient exactly when there is a fee.
    pub fn check(self: *const Spend, h: *const Poseidon, nk: *const Digest) Error!void {
        var in_sum: u128 = 0;
        var out_sum: u128 = @as(u128, self.public_amount) + self.fee;
        for (&self.inputs) |*in| {
            const n = in.noteOf();
            if (n.asset_id != self.asset_id) return error.AssetMismatch;
            in_sum += n.value;
        }
        for (&self.outputs) |*o| {
            if (o.asset_id != self.asset_id) return error.AssetMismatch;
            out_sum += o.value;
        }
        if (in_sum > std.math.maxInt(u64)) return error.ValueOverflow;
        if (in_sum != out_sum) return error.Unbalanced;
        for (&self.inputs) |*in| {
            switch (in.*) {
                .dummy => |*n| {
                    if (n.value != 0) return error.DummyCarriesValue;
                },
                .real => |*r| {
                    const cm = r.note.cm(h);
                    if (!digest.eql(&tree.rootOf(h, &r.pool, &cm), &self.note_root)) return error.NotInPool;
                    if (!digest.eql(&tree.rootOf(h, &r.assoc, &cm), &self.assoc_root)) return error.NotInAssoc;
                },
            }
        }
        const nf = self.nullifiers(h, nk);
        if (digest.eql(&nf[0], &nf[1])) return error.DoubleSpend;
        const no_recipient = std.mem.allEqual(u8, &self.recipient, 0);
        if (self.isTransfer()) {
            if (self.clearing_price != 0 or !no_recipient) return error.SettleFieldsOnTransfer;
        } else if (no_recipient) {
            return error.NoRecipient;
        }
        // The circuit publishes the fee recipient only when the fee is
        // nonzero. A wallet that set one beside a zero fee would sign an
        // intent that is not the one it meant, so both mismatches are refused.
        const no_fee_recipient = std.mem.allEqual(u8, &self.fee_recipient, 0);
        if (self.fee != 0 and no_fee_recipient) return error.NoFeeRecipient;
        if (self.fee == 0 and !no_fee_recipient) return error.FeeRecipientWithoutFee;
    }

    pub fn intent(self: *const Spend, h: *const Poseidon, nk: *const Digest) Error![WORDS]Fp {
        try self.check(h, nk);
        const nf = self.nullifiers(h, nk);
        const cm = self.outCm(h);
        var w: [WORDS]Fp = undefined;
        w[NOTE_ROOT..][0..4].* = self.note_root;
        w[ASSOC_ROOT..][0..4].* = self.assoc_root;
        w[NF0..][0..4].* = nf[0];
        w[NF1..][0..4].* = nf[1];
        w[OUT_CM0..][0..4].* = cm[0];
        w[OUT_CM1..][0..4].* = cm[1];
        w[PUBLIC_AMOUNT] = field.reduce(self.public_amount);
        w[FEE] = field.reduce(self.fee);
        w[ASSET_ID] = field.reduce(self.asset_id);
        w[CLEARING_PRICE] = field.reduce(self.clearing_price);
        w[RECIPIENT..][0..4].* = addressLimbs(&self.recipient);
        w[FEE_RECIPIENT..][0..4].* = addressLimbs(&self.fee_recipient);
        return w;
    }
};

/// The 37-word intent: the 36 words, then `not_before`, which must be a positive
/// multiple of `NOT_BEFORE_GRID_S`.
pub fn intentNotBefore(sp: *const Spend, h: *const Poseidon, nk: *const Digest, not_before: u64) Error![WORDS_NOT_BEFORE]Fp {
    if (not_before == 0 or not_before % NOT_BEFORE_GRID_S != 0) return error.NotBeforeOffGrid;
    const w36 = try sp.intent(h, nk);
    var w: [WORDS_NOT_BEFORE]Fp = undefined;
    w[0..WORDS].* = w36;
    w[NOT_BEFORE] = field.reduce(not_before);
    return w;
}

/// A 160 bit address as a digest: limb i is bits 48i..48i+48 of the address
/// read big-endian, so three 48 bit limbs and a 16 bit fourth. A 64 bit limb
/// can be p or more and has no canonical encoding; a 48 bit one never does.
/// One word would bind 64 bits of it.
pub fn addressLimbs(a: *const [20]u8) Digest {
    return .{
        std.mem.readInt(u48, a[14..20], .big),
        std.mem.readInt(u48, a[8..14], .big),
        std.mem.readInt(u48, a[2..8], .big),
        std.mem.readInt(u16, a[0..2], .big),
    };
}
