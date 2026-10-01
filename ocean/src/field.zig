// NONOS Operating System (AGPL-3.0-or-later)
//! Goldilocks, p = 2^64 - 2^32 + 1. Every Fp this module returns is canonical,
//! in [0, p), so equal values have equal bytes.

const std = @import("std");

pub const Fp = u64;

pub const P: u64 = 0xFFFF_FFFF_0000_0001;
/// 2^64 mod p.
pub const EPSILON: u64 = 0xFFFF_FFFF;
pub const ZERO: Fp = 0;
pub const ONE: Fp = 1;

pub const Error = error{ NonCanonical, ZeroInverse };

/// The circuit's from_u64: one conditional subtraction.
pub fn reduce(x: u64) Fp {
    return if (x >= P) x - P else x;
}

/// Input boundary. A limb read from bytes is refused rather than reduced.
pub fn canonical(x: u64) Error!Fp {
    if (x >= P) return error.NonCanonical;
    return x;
}

pub fn add(a: Fp, b: Fp) Fp {
    const r = @addWithOverflow(a, b);
    return reduce(if (r[1] == 1) r[0] +% EPSILON else r[0]);
}

pub fn sub(a: Fp, b: Fp) Fp {
    const r = @subWithOverflow(a, b);
    return if (r[1] == 1) r[0] -% EPSILON else r[0];
}

pub fn neg(a: Fp) Fp {
    return sub(ZERO, a);
}

pub fn mul(a: Fp, b: Fp) Fp {
    return reduce128(@as(u128, a) * @as(u128, b));
}

/// x = lo + hi 2^64 with hi = hh 2^32 + hl; 2^64 = EPSILON and 2^96 = -1 (mod p).
pub fn reduce128(x: u128) Fp {
    const lo: u64 = @truncate(x);
    const hi: u64 = @truncate(x >> 64);
    const hh = hi >> 32;
    const hl = hi & EPSILON;
    const t = @subWithOverflow(lo, hh);
    const t0 = if (t[1] == 1) t[0] -% EPSILON else t[0];
    const s = @addWithOverflow(t0, hl * EPSILON);
    return reduce(if (s[1] == 1) s[0] +% EPSILON else s[0]);
}

pub fn square(a: Fp) Fp {
    return mul(a, a);
}

pub fn pow(base: Fp, e: u64) Fp {
    var r: Fp = ONE;
    var b = base;
    var k = e;
    while (k != 0) : (k >>= 1) {
        if (k & 1 == 1) r = mul(r, b);
        b = mul(b, b);
    }
    return r;
}

pub fn inv(a: Fp) Error!Fp {
    if (a == ZERO) return error.ZeroInverse;
    return pow(a, P - 2);
}

/// x^7, a permutation of the field: gcd(7, p - 1) = 1.
pub fn sbox7(x: Fp) Fp {
    const x2 = mul(x, x);
    const x4 = mul(x2, x2);
    return mul(mul(x, x2), x4);
}

/// Uniform in [0, p): a u64 is rejected with probability 2^-32.
pub fn random(rng: std.Random) Fp {
    while (true) {
        const x = rng.int(u64);
        if (x < P) return x;
    }
}

/// Volatile stores, so the wipe survives dead store elimination.
pub fn wipe(comptime T: type, s: []T) void {
    const p: [*]volatile T = s.ptr;
    for (0..s.len) |i| p[i] = 0;
}
