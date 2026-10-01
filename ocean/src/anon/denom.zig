// NONOS Operating System (AGPL-3.0-or-later)
//! Standard note sizes.
//!
//! The proof hides the values of notes inside the pool. What it cannot hide
//! is a public amount: a deposit, a withdrawal, and every note a payee later
//! withdraws. An amount like 1.2371 is a name. The standard sizes are the
//! 1-2-5 series of the asset's unit, `unit * {1, 2, 5} * 10^k`, so every
//! amount is a short sum of sizes thousands of other notes share.

const std = @import("std");

/// The launch pool's asset table: the smallest standard note in note units.
/// ETH (asset 0) counts wei, so 0.001 ETH is 10^15; NOX (asset 1) counts
/// 10^9 base units per note unit, so 0.001 NOX is 10^6.
pub fn unitFor(asset_id: u64) ?u64 {
    return switch (asset_id) {
        0 => 1_000_000_000_000_000,
        1 => 1_000_000,
        else => null,
    };
}

/// At most three sizes per decade and twenty decades in a u64.
pub const MAX_PIECES = 64;

/// Whether `v` is one of the standard sizes of `unit`.
pub fn isStandard(v: u64, unit: u64) bool {
    if (unit == 0 or v == 0 or v % unit != 0) return false;
    var m = v / unit;
    while (m % 10 == 0) m /= 10;
    return m == 1 or m == 2 or m == 5;
}

/// The largest standard size at most `v`, or zero when `v < unit`.
pub fn largestAtMost(v: u64, unit: u64) u64 {
    if (unit == 0 or v < unit) return 0;
    var best: u64 = unit;
    var decade: u64 = unit;
    while (true) {
        for ([_]u64{ 1, 2, 5 }) |k| {
            const s = std.math.mul(u64, decade, k) catch return best;
            if (s > v) return best;
            best = s;
        }
        decade = std.math.mul(u64, decade, 10) catch return best;
    }
}

pub const Plan = struct {
    pieces: [MAX_PIECES]u64 = undefined,
    len: usize = 0,
    /// What does not fit in whole units and stays with the sender.
    rest: u64 = 0,

    pub fn slice(self: *const Plan) []const u64 {
        return self.pieces[0..self.len];
    }
};

/// `amount` as standard sizes, largest first, greedily: the fewest pieces
/// the 1-2-5 series allows. What is below one unit is `rest`.
pub fn split(amount: u64, unit: u64) Plan {
    var p: Plan = .{};
    var left = amount;
    while (p.len < MAX_PIECES) {
        const s = largestAtMost(left, unit);
        if (s == 0) break;
        p.pieces[p.len] = s;
        p.len += 1;
        left -= s;
    }
    p.rest = left;
    return p;
}
