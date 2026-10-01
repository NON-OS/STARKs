// NONOS Operating System (AGPL-3.0-or-later)
//! Four limbs, limb 0 low. bytes32 is the big endian u256 of the limbs, the
//! form every pool event and every hex under spec/ carries: bytes 24..32 are
//! limb 0, bytes 0..8 are limb 3.

const std = @import("std");
const field = @import("field.zig");
const poseidon = @import("poseidon.zig");

pub const Digest = poseidon.Digest;
pub const ZERO: Digest = .{ 0, 0, 0, 0 };

pub fn eql(a: *const Digest, b: *const Digest) bool {
    return std.mem.eql(u64, a, b);
}

/// tag(v) = [v, 0, 0, 0]: the right operand of a domain or index compression.
pub fn tag(v: u64) Digest {
    return .{ field.reduce(v), 0, 0, 0 };
}

pub fn toBytes(d: *const Digest) [32]u8 {
    var out: [32]u8 = undefined;
    for (0..4) |i| {
        const at = 24 - 8 * i;
        std.mem.writeInt(u64, out[at..][0..8], d[i], .big);
    }
    return out;
}

pub fn fromBytes(b: *const [32]u8) field.Error!Digest {
    var d: Digest = undefined;
    for (0..4) |i| {
        const at = 24 - 8 * i;
        d[i] = try field.canonical(std.mem.readInt(u64, b[at..][0..8], .big));
    }
    return d;
}

pub const HexError = field.Error || error{ InvalidLength, InvalidCharacter };

/// 64 hex digits, an optional 0x prefix.
pub fn fromHex(s: []const u8) HexError!Digest {
    const has_prefix = s.len >= 2 and s[0] == '0' and (s[1] == 'x' or s[1] == 'X');
    const t = if (has_prefix) s[2..] else s;
    if (t.len != 64) return error.InvalidLength;
    var b: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&b, t) catch return error.InvalidCharacter;
    return fromBytes(&b);
}

pub fn toHex(d: *const Digest) [64]u8 {
    return std.fmt.bytesToHex(toBytes(d), .lower);
}
