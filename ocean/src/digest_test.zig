// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const field = @import("field.zig");
const digest = @import("digest.zig");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;
const expectEqualSlices = std.testing.expectEqualSlices;

const LIVE_SK = "9c4b73105bd8c464250d949588b61807aee31121ea9d916ff6bf6105dab3ff7e";

test "limb_0_is_the_last_eight_bytes" {
    const d = digest.Digest{ 1, 2, 3, 4 };
    const b = digest.toBytes(&d);
    try expectEqual(4, std.mem.readInt(u64, b[0..8], .big));
    try expectEqual(1, std.mem.readInt(u64, b[24..32], .big));
    try expectEqual(d, try digest.fromBytes(&b));
}

test "hex_round_trips_with_and_without_the_prefix" {
    const d = try digest.fromHex(LIVE_SK);
    try expectEqualSlices(u8, LIVE_SK, &digest.toHex(&d));
    const p = try digest.fromHex("0x" ++ LIVE_SK);
    try expectEqual(d, p);
    try expectEqual(0x9c4b73105bd8c464, d[3]);
    try expectEqual(0xf6bf6105dab3ff7e, d[0]);
}

test "a_non_canonical_limb_is_refused_not_reduced" {
    const hi = "ffffffffffffffff" ++ "0" ** 48;
    try expectError(error.NonCanonical, digest.fromHex(hi));
    const p = "0" ** 48 ++ "ffffffff00000001";
    try expectError(error.NonCanonical, digest.fromHex(p));
    const p1 = "0" ** 48 ++ "ffffffff00000000";
    try expectEqual(field.P - 1, (try digest.fromHex(p1))[0]);
}

test "malformed_hex_is_named" {
    try expectError(error.InvalidLength, digest.fromHex("abcd"));
    try expectError(error.InvalidCharacter, digest.fromHex("zz" ++ "0" ** 62));
}

test "tag_is_the_value_in_limb_zero" {
    try expectEqual(digest.Digest{ 7, 0, 0, 0 }, digest.tag(7));
    try expectEqual(digest.Digest{ 0, 0, 0, 0 }, digest.tag(field.P));
    try expect(digest.eql(&digest.ZERO, &digest.tag(0)));
}
