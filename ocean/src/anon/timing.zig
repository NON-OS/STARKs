// NONOS Operating System (AGPL-3.0-or-later)
//! When a built payment may be submitted.
//!
//! A deposit followed by a withdrawal of the same size one block later is
//! one user, whatever the proof hides. Each payment carries the earliest
//! block it may go out, drawn uniformly from the policy's window, and a
//! submitter holds it until then.

const std = @import("std");
const Policy = @import("policy.zig").Policy;

pub const Window = struct {
    /// The block the payment was built at.
    built: u64,
    /// The earliest block it may be submitted in.
    not_before: u64,

    pub fn ready(self: *const Window, now: u64) bool {
        return now >= self.not_before;
    }
};

/// A uniform draw from `[built + delay_min, built + delay_max]`. A window
/// whose ends are reversed is read as its smaller end: a policy error never
/// makes a payment go out sooner than the minimum.
pub fn draw(rng: std.Random, built: u64, p: *const Policy) Window {
    const lo = p.delay_min;
    const hi = @max(p.delay_min, p.delay_max);
    const wait = if (hi == lo) lo else rng.intRangeAtMost(u64, lo, hi);
    return .{ .built = built, .not_before = built +| wait };
}
