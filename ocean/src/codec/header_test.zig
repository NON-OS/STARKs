// NONOS Operating System (AGPL-3.0-or-later)

const std = @import("std");
const digest = @import("../digest.zig");
const header = @import("header.zig");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

/// The emitted settlement artifact: 1,296,148 bytes, permRoot leading,
/// regionWidth 510 at offset 32, traceRoot at 36.
const PERM = "67d58da90f59f915588bff4ef9e01e36678217d3f477474feb3c8dd079bcaa8f";
const TRACE = "dde38d537e11880a6eaa117e04914788d53c4d00a2792dc20c4f62d5cdeda54a";
const SPLIT: u32 = 510;
const WIDTH: u32 = 556;

fn sample() ![header.LEN]u8 {
    var b: [header.LEN]u8 = undefined;
    b[0..32].* = digest.toBytes(&(try digest.fromHex(PERM)));
    std.mem.writeInt(u32, b[32..36], SPLIT, .little);
    b[36..68].* = digest.toBytes(&(try digest.fromHex(TRACE)));
    return b;
}

test "the_header_leads_with_the_second_root" {
    const b = try sample();
    const h = try header.read(&b);
    try expectEqual(try digest.fromHex(PERM), h.perm_root);
    try expectEqual(SPLIT, h.region_width);
    try expectEqual(try digest.fromHex(TRACE), h.trace_root);
}

test "the_split_names_the_accumulator_columns" {
    const b = try sample();
    const h = try header.read(&b);
    const s = try header.splitRow(&h, WIDTH, SPLIT);
    try expectEqual(SPLIT, s.region);
    // 556 less 510 is the 46 chained accumulators.
    try expectEqual(@as(u32, 46), s.permutation);
}

test "a_split_the_verifier_did_not_emit_is_refused" {
    const b = try sample();
    const h = try header.read(&b);
    try expectError(error.SplitDisagrees, header.splitRow(&h, WIDTH, SPLIT + 1));
}

test "a_split_outside_the_trace_is_refused" {
    var b = try sample();
    std.mem.writeInt(u32, b[32..36], WIDTH, .little);
    const h = try header.read(&b);
    try expectError(error.SplitOutOfRange, header.splitRow(&h, WIDTH, WIDTH));
    std.mem.writeInt(u32, b[32..36], 0, .little);
    const z = try header.read(&b);
    try expectError(error.SplitOutOfRange, header.splitRow(&z, WIDTH, 0));
}

test "a_file_shorter_than_the_header_is_refused" {
    const b = try sample();
    try expectError(error.TooShort, header.read(b[0 .. header.LEN - 1]));
    try expectError(error.TooShort, header.read(&[_]u8{}));
}

// A v1.0 file starts with the trace root and has no second one, so the two
// thirty two byte fields a reader picks up are the trace root and whatever
// followed it. Equal roots mean the second round committed nothing.
test "two_equal_roots_are_refused" {
    var b = try sample();
    b[36..68].* = b[0..32].*;
    try expectError(error.RootsCollide, header.read(&b));
}

test "a_non_canonical_root_limb_is_refused" {
    var b = try sample();
    // Limb zero of permRoot sits in bytes 24 to 32.
    std.mem.writeInt(u64, b[24..32], 0xFFFF_FFFF_0000_0001, .big);
    try expectError(error.NonCanonical, header.read(&b));
}
