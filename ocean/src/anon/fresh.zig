// NONOS Operating System (AGPL-3.0-or-later)
//! Fresh withdrawal addresses.
//!
//! A withdrawal to the address that deposited, or to one address twice,
//! links the two ends through the pool whatever the proof hides. The wallet
//! derives a new Ethereum key for every withdrawal from its own secret, so
//! the addresses are recoverable from the seed and never reused. The relay
//! fee pays for the withdrawal's gas, so a fresh address needs no funding
//! that would link it back.
//!
//! Key i is `reduce48(HMAC(secret, "NOX-WITHDRAW-A" || i) ||
//! HMAC(secret, "NOX-WITHDRAW-B" || i)[0..16])`, a uniform secp256k1 scalar
//! to within 2^-128; the address is the last 20 bytes of Keccak-256 over the
//! uncompressed public key without its prefix, as Ethereum defines it.

const std = @import("std");
const Secp256k1 = std.crypto.ecc.Secp256k1;
const HmacSha256 = std.crypto.auth.hmac.sha2.HmacSha256;
const Keccak256 = std.crypto.hash.sha3.Keccak256;

pub const Error = error{IdentityElement};

pub const Fresh = struct {
    index: u64,
    address: [20]u8,
    /// The address's private key, big endian: what moves the withdrawn funds
    /// on. The caller keeps it and wipes this copy.
    sk: [32]u8,

    pub fn wipe(self: *Fresh) void {
        std.crypto.secureZero(u8, &self.sk);
    }
};

/// The Ethereum address of a private key.
pub fn addressOf(sk: *const [32]u8) Error![20]u8 {
    const pk = Secp256k1.basePoint.mul(sk.*, .big) catch return error.IdentityElement;
    const sec1 = pk.toUncompressedSec1();
    var h: [32]u8 = undefined;
    Keccak256.hash(sec1[1..], &h, .{});
    return h[12..32].*;
}

/// Withdrawal key and address `index` of the wallet whose secret is `secret`.
pub fn derive(secret: *const [32]u8, index: u64) Error!Fresh {
    var wide: [48]u8 = undefined;
    defer std.crypto.secureZero(u8, &wide);
    var msg: [22]u8 = undefined;
    @memcpy(msg[0..14], "NOX-WITHDRAW-A");
    std.mem.writeInt(u64, msg[14..22], index, .little);
    var a: [32]u8 = undefined;
    HmacSha256.create(&a, &msg, secret);
    msg[13] = 'B';
    var b: [32]u8 = undefined;
    HmacSha256.create(&b, &msg, secret);
    @memcpy(wide[0..32], &a);
    @memcpy(wide[32..48], b[0..16]);
    std.crypto.secureZero(u8, &a);
    std.crypto.secureZero(u8, &b);
    var sk = Secp256k1.scalar.reduce48(wide, .big);
    errdefer std.crypto.secureZero(u8, &sk);
    return .{ .index = index, .address = try addressOf(&sk), .sk = sk };
}
