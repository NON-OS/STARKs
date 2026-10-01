// NONOS Operating System (AGPL-3.0-or-later)
//! sk to spend_pk and nk by one compression each under a domain tag; nf from
//! nk, cm and the leaf index. spec/shield-key-hierarchy.json is the vector.

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const poseidon = @import("poseidon.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;

/// ASCII "SPND".
pub const SPEND_DOMAIN: u64 = 0x5350_4E44;
/// ASCII "NULL".
pub const NULL_DOMAIN: u64 = 0x4E55_4C4C;
/// ASCII "DEAD". Lane one of the word a dummy input's nullifier hashes beside
/// its position.
///
/// The pool spends both nullifiers of every intent and cannot do otherwise:
/// liveness is private and no public word carries it, and a word that did would
/// publish how many notes each payment spent. So a dummy's nullifier is burned
/// like a note's and has to live where a note's cannot.
pub const DEAD_DOMAIN: u64 = 0x4445_4144;
const SK_DOMAIN = "NOX-SHIELD-SPEND-KEY";
/// ASCII "NOXACTV1", lane 0 of the weekly activity tag's compression.
pub const ACTIVITY_DOMAIN: u64 = 0x4E4F_5841_4354_5631;
/// ASCII "NOXACTK1", lane 0 of the activity key commitment's compression.
pub const ACTIVITY_KEY_DOMAIN: u64 = 0x4E4F_5841_4354_4B31;

pub const Keys = struct {
    spend_pk: Digest,
    nk: Digest,
};

pub const Secret = struct {
    sk: Digest,

    /// Limb i is the first BLAKE3(SK_DOMAIN || seed || i || ctr), little
    /// endian u64, that falls below p.
    pub fn fromSeed(seed: *const [32]u8) Secret {
        var s: Secret = undefined;
        var buf: [SK_DOMAIN.len + 34]u8 = undefined;
        defer field.wipe(u8, &buf);
        @memcpy(buf[0..SK_DOMAIN.len], SK_DOMAIN);
        buf[SK_DOMAIN.len..][0..32].* = seed.*;
        for (0..4) |i| {
            var ctr: u8 = 0;
            while (true) : (ctr +%= 1) {
                buf[SK_DOMAIN.len + 32] = @intCast(i);
                buf[SK_DOMAIN.len + 33] = ctr;
                var h: [32]u8 = undefined;
                std.crypto.hash.Blake3.hash(&buf, &h, .{});
                const x = std.mem.readInt(u64, h[0..8], .little);
                field.wipe(u8, &h);
                if (x < field.P) {
                    s.sk[i] = x;
                    break;
                }
            }
        }
        return s;
    }

    pub fn fromLimbs(l: *const [4]u64) field.Error!Secret {
        var s: Secret = undefined;
        for (0..4) |i| s.sk[i] = try field.canonical(l[i]);
        return s;
    }

    pub fn derive(self: *const Secret, h: *const Poseidon) Keys {
        return .{
            .spend_pk = h.compress(&self.sk, &digest.tag(SPEND_DOMAIN)),
            .nk = h.compress(&self.sk, &digest.tag(NULL_DOMAIN)),
        };
    }

    pub fn bytes(self: *const Secret) [32]u8 {
        return digest.toBytes(&self.sk);
    }

    pub fn wipe(self: *Secret) void {
        field.wipe(u64, &self.sk);
    }
};

/// The word the fourth compression absorbs: the position the path recovered,
/// and the lane that says whether this input is a note or a dummy.
pub fn positionWord(index: u64, live: bool) Digest {
    var q = digest.tag(index);
    q[1] = if (live) 0 else DEAD_DOMAIN;
    return q;
}

/// nf = compress(compress(nk, cm), positionWord(leaf_index, live)). The index is
/// in the preimage so two equal notes retire under two nullifiers, and the lane
/// beside it keeps a dummy's nullifier out of the space a note's occupies.
pub fn nullifier(
    h: *const Poseidon,
    nk: *const Digest,
    cm: *const Digest,
    leaf_index: u64,
    live: bool,
) Digest {
    const t = h.compress(nk, cm);
    return h.compress(&t, &positionWord(leaf_index, live));
}

/// The weekly activity tag, T = compress([NOXACTV1, nk0, nk1, nk2], [nk3, week, 0, 0]):
/// one per key per week, unlinkable across weeks without nk. Words 6 to 9 of the
/// activity statement.
pub fn activityTag(h: *const Poseidon, nk: *const Digest, week: u64) Digest {
    return h.compress(&.{ ACTIVITY_DOMAIN, nk[0], nk[1], nk[2] }, &.{ nk[3], week, 0, 0 });
}

/// The activity key commitment, K = compress([NOXACTK1, nk0, nk1, nk2], [nk3, 0, 0, 0]):
/// the same every week, what a holder declares once with its lock. Words 14 to 17 of
/// the activity statement.
pub fn keyCommitment(h: *const Poseidon, nk: *const Digest) Digest {
    return h.compress(&.{ ACTIVITY_KEY_DOMAIN, nk[0], nk[1], nk[2] }, &.{ nk[3], 0, 0, 0 });
}
