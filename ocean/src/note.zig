// NONOS Operating System (AGPL-3.0-or-later)
//! A note: value, asset, owner key, blinding. cm = commit_note(limbs), the
//! three-compression tree ShieldedPool._computeCommitment runs.

const std = @import("std");
const field = @import("field.zig");
const poseidon = @import("poseidon.zig");
const digest = @import("digest.zig");
const Fp = field.Fp;
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;

/// value 8 | asset_id 8 | spend_pk 32 | blinding 32, big endian.
pub const BYTES = 80;

pub const Note = struct {
    value: u64,
    asset_id: u64,
    spend_pk: Digest,
    blinding: Digest,

    /// Value low 32, value high 32, asset, spend_pk at 3..7, blinding at 7..11.
    /// The split at 32 bits is what the range argument bounds.
    pub fn limbs(self: *const Note) [poseidon.NOTE_LIMBS]Fp {
        var l: [poseidon.NOTE_LIMBS]Fp = undefined;
        l[0] = self.value & 0xFFFF_FFFF;
        l[1] = self.value >> 32;
        l[2] = field.reduce(self.asset_id);
        for (0..4) |i| {
            l[3 + i] = self.spend_pk[i];
            l[7 + i] = self.blinding[i];
        }
        return l;
    }

    pub fn cm(self: *const Note, h: *const Poseidon) Digest {
        const l = self.limbs();
        return h.commitNote(&l);
    }

    /// What a depositor hands the pool: the pool builds the public quad from
    /// the amount it escrowed and never sees an operand of this.
    pub fn owner(self: *const Note, h: *const Poseidon) Digest {
        return h.commitOwner(&self.spend_pk, &self.blinding);
    }

    /// Four uniform field limbs of blinding from the caller's entropy.
    pub fn fresh(rng: std.Random, value: u64, asset_id: u64, spend_pk: Digest) Note {
        var b: Digest = undefined;
        for (0..4) |i| b[i] = field.random(rng);
        return .{ .value = value, .asset_id = asset_id, .spend_pk = spend_pk, .blinding = b };
    }

    pub fn bytes(self: *const Note) [BYTES]u8 {
        var out: [BYTES]u8 = undefined;
        std.mem.writeInt(u64, out[0..8], self.value, .big);
        std.mem.writeInt(u64, out[8..16], self.asset_id, .big);
        out[16..48].* = digest.toBytes(&self.spend_pk);
        out[48..80].* = digest.toBytes(&self.blinding);
        return out;
    }

    pub fn fromBytes(b: *const [BYTES]u8) field.Error!Note {
        return .{
            .value = std.mem.readInt(u64, b[0..8], .big),
            .asset_id = std.mem.readInt(u64, b[8..16], .big),
            .spend_pk = try digest.fromBytes(b[16..48]),
            .blinding = try digest.fromBytes(b[48..80]),
        };
    }

    /// The blinding is what opens cm; the rest is public once spent.
    pub fn wipe(self: *Note) void {
        field.wipe(u64, &self.blinding);
    }
};
