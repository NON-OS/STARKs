// NONOS Operating System (AGPL-3.0-or-later)
//! What a depositor sends and what the pool does with it.
//!
//! `absorb(assetId, amount, ownerCommit)`. The pool holds the amount, builds
//! `[value_lo, value_hi, asset, NOTE_DOMAIN]` from what it escrowed, and
//! compresses that with the digest it was handed. The leaf it inserts commits
//! to the amount it actually holds, by construction rather than by policy.
//!
//! Neither the spend key nor the blinding appears here. The opening reaches
//! the payee as a sealed memo, off chain.

const std = @import("std");
const field = @import("../field.zig");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const note = @import("../note.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;
const Note = note.Note;

/// asset_id 8 | amount 8 | owner 32, big endian.
pub const CALLDATA = 48;

pub const Error = error{ ValueOverflow, LeafMismatch } || field.Error;

/// The three arguments, and nothing else.
pub const Deposit = struct {
    asset_id: u64,
    amount: u64,
    owner: Digest,

    /// The leaf the pool will insert, computed the way the pool computes it:
    /// the public quad from the escrowed amount, then one compression.
    pub fn leaf(self: *const Deposit, h: *const Poseidon) Digest {
        const public: Digest = .{
            self.amount & 0xFFFF_FFFF,
            self.amount >> 32,
            field.reduce(self.asset_id),
            poseidon.NOTE_DOMAIN,
        };
        return h.compress(&public, &self.owner);
    }

    pub fn bytes(self: *const Deposit) [CALLDATA]u8 {
        var out: [CALLDATA]u8 = undefined;
        std.mem.writeInt(u64, out[0..8], self.asset_id, .big);
        std.mem.writeInt(u64, out[8..16], self.amount, .big);
        out[16..48].* = digest.toBytes(&self.owner);
        return out;
    }
};

/// The call a wallet builds for a note it is about to own.
pub fn prepare(h: *const Poseidon, n: *const Note) Deposit {
    return .{ .asset_id = n.asset_id, .amount = n.value, .owner = n.owner(h) };
}

/// The same leaf, from the note rather than from the call. A wallet checks
/// these agree before it signs: a deposit whose leaf is not its note's
/// commitment is value escrowed into a note nobody can spend.
pub fn leafOf(h: *const Poseidon, n: *const Note) Digest {
    return n.cm(h);
}

pub fn encode(d: *const Deposit) [CALLDATA]u8 {
    return d.bytes();
}

pub fn decode(b: *const [CALLDATA]u8) Error!Deposit {
    return .{
        .asset_id = std.mem.readInt(u64, b[0..8], .big),
        .amount = std.mem.readInt(u64, b[8..16], .big),
        .owner = try digest.fromBytes(b[16..48]),
    };
}
