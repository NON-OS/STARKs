// NONOS Operating System (AGPL-3.0-or-later)
//! Poseidon over Goldilocks as the pool hashes: width 8, rate 4, 32 full
//! rounds of x^7, Cauchy MDS M[i][j] = 1 / (i - (8 + j)), round constants
//! BLAKE3(RC_DOMAIN || r || j) as little endian u64, reduced.

const std = @import("std");
const field = @import("field.zig");
const Fp = field.Fp;

pub const WIDTH = 8;
pub const RATE = 4;
/// 1 << LOG_ROUNDS = FULL_ROUNDS in PoseidonGoldilocks.sol.
pub const LOG_ROUNDS = 5;
pub const ROUNDS = 1 << LOG_ROUNDS;
pub const NOTE_LIMBS = 11;
/// ASCII "NOTE", limb 11 of a note preimage.
pub const NOTE_DOMAIN: u64 = 0x4E4F_5445;
const RC_DOMAIN = "NONOS-POSEIDON-GOLDILOCKS-RC";

pub const Digest = [RATE]Fp;
pub const State = [WIDTH]Fp;

pub const Poseidon = struct {
    mds: [WIDTH][WIDTH]Fp,
    rc: [ROUNDS][WIDTH]Fp,

    pub fn init() Poseidon {
        var p: Poseidon = undefined;
        cauchy(&p.mds);
        constants(&p.rc);
        return p;
    }

    /// S-box on every lane, MDS, then the round constants.
    pub fn round(self: *const Poseidon, s: *const State, r: usize) State {
        var sb: State = undefined;
        for (0..WIDTH) |i| sb[i] = field.sbox7(s[i]);
        var out: State = undefined;
        for (0..WIDTH) |j| {
            var acc = self.rc[r][j];
            for (0..WIDTH) |i| acc = field.add(acc, field.mul(self.mds[j][i], sb[i]));
            out[j] = acc;
        }
        return out;
    }

    pub fn permute(self: *const Poseidon, s: State) State {
        var st = s;
        for (0..ROUNDS) |r| st = self.round(&st, r);
        return st;
    }

    /// Two-to-one: left in the rate lanes, right in the capacity, permute,
    /// read the rate.
    pub fn compress(self: *const Poseidon, l: *const Digest, r: *const Digest) Digest {
        var st: State = undefined;
        @memcpy(st[0..RATE], l);
        @memcpy(st[RATE..WIDTH], r);
        const out = self.permute(st);
        return out[0..RATE].*;
    }

    /// Sixteen limbs as four quads: compress(compress(q0, q1), compress(q2, q3)).
    /// The nullifier set leaf hash; a note commitment is the nested form below.
    pub fn commit16(self: *const Poseidon, p: *const [16]Fp) Digest {
        const d0 = self.compress(p[0..4], p[4..8]);
        const d1 = self.compress(p[8..12], p[12..16]);
        return self.compress(&d0, &d1);
    }

    /// `owner = compress(spend_pk, blinding)`. Hiding under a uniform blinding,
    /// binding under the collision resistance of compress.
    pub fn commitOwner(self: *const Poseidon, spend_pk: *const Digest, blinding: *const Digest) Digest {
        return self.compress(spend_pk, blinding);
    }

    /// `cm = compress([value_lo, value_hi, asset, NOTE_DOMAIN], owner)` over
    /// eleven limbs: value low, value high, asset, spend key, blinding.
    ///
    /// No quad holds a public element and a secret one. A pool builds the
    /// public quad from the amount it escrowed and is handed `owner`, so the
    /// leaf binds the escrowed value without the pool seeing an operand of
    /// `owner`.
    pub fn commitNote(self: *const Poseidon, limbs: *const [NOTE_LIMBS]Fp) Digest {
        const public: Digest = .{ limbs[0], limbs[1], limbs[2], NOTE_DOMAIN };
        const owner = self.commitOwner(limbs[3..7], limbs[7..11]);
        return self.compress(&public, &owner);
    }
};

/// Nodes x_i = i and y_j = 8 + j never meet, so every entry has an inverse.
fn cauchy(m: *[WIDTH][WIDTH]Fp) void {
    for (0..WIDTH) |i| {
        for (0..WIDTH) |j| {
            const d = field.sub(@intCast(i), @intCast(WIDTH + j));
            m[i][j] = field.pow(d, field.P - 2);
        }
    }
}

pub fn roundConstant(r: u64, j: u64) Fp {
    var buf: [RC_DOMAIN.len + 16]u8 = undefined;
    @memcpy(buf[0..RC_DOMAIN.len], RC_DOMAIN);
    std.mem.writeInt(u64, buf[RC_DOMAIN.len..][0..8], r, .little);
    std.mem.writeInt(u64, buf[RC_DOMAIN.len + 8 ..][0..8], j, .little);
    var h: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(&buf, &h, .{});
    return field.reduce(std.mem.readInt(u64, h[0..8], .little));
}

fn constants(rc: *[ROUNDS][WIDTH]Fp) void {
    for (0..ROUNDS) |r| {
        for (0..WIDTH) |j| rc[r][j] = roundConstant(r, j);
    }
}
