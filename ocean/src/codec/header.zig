// NONOS Operating System (AGPL-3.0-or-later)
//! The v1.1 proof header, and the row split it names.
//!
//! The copy constraint is argued at challenges drawn after the region columns
//! are committed, so a proof carries two roots. The second leads the file
//! because a reader that starts at the trace root is reading v1.0, where the
//! challenges were constants of the layout and the grand product argued
//! nothing.
//!
//! `regionWidth` is read here for checking, never for deciding. A verifier
//! holds it as a constant from the emitted structure: a proof that names its
//! own split checks two roots against halves of its own choosing and shows two
//! valid walks.

const std = @import("std");
const digest = @import("../digest.zig");
const Digest = digest.Digest;

pub const PERM_ROOT: usize = 0;
pub const REGION_WIDTH: usize = 32;
pub const TRACE_ROOT: usize = 36;
/// permRoot 32 | regionWidth 4 | traceRoot 32.
pub const LEN: usize = 68;

pub const Error = error{
    TooShort,
    SplitOutOfRange,
    SplitDisagrees,
    RootsCollide,
} || digest.HexError;

pub const Header = struct {
    perm_root: Digest,
    region_width: u32,
    trace_root: Digest,
};

/// Read the header. Roots are digests, so a non-canonical limb is refused
/// here rather than surfacing later as a walk that cannot close.
pub fn read(bytes: []const u8) Error!Header {
    if (bytes.len < LEN) return error.TooShort;
    const perm = try digest.fromBytes(bytes[PERM_ROOT..][0..32]);
    const trace = try digest.fromBytes(bytes[TRACE_ROOT..][0..32]);
    // Two rounds over one trace cannot commit to the same root unless the
    // second round committed nothing.
    if (digest.eql(&perm, &trace)) return error.RootsCollide;
    return .{
        .perm_root = perm,
        .region_width = std.mem.readInt(u32, bytes[REGION_WIDTH..][0..4], .little),
        .trace_root = trace,
    };
}

/// Where an opened row splits, checked against the width the verifier holds
/// and the split the structure file emitted. Both, because either alone lets
/// one side drift.
pub fn splitRow(h: *const Header, trace_width: u32, emitted_split: u32) Error!struct {
    region: u32,
    permutation: u32,
} {
    if (h.region_width != emitted_split) return error.SplitDisagrees;
    if (h.region_width == 0 or h.region_width >= trace_width) return error.SplitOutOfRange;
    return .{ .region = h.region_width, .permutation = trace_width - h.region_width };
}
