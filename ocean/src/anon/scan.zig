// NONOS Operating System (AGPL-3.0-or-later)
//! Scanning that tells the RPC nothing.
//!
//! A wallet that asks a node for "my notes" names them. This one fetches
//! every `OutputNote` event in a block range, the same request any wallet
//! makes, and does the rest locally: every leaf goes into its mirror of the
//! pool tree, and every memo is trial-opened with the view key. Which events
//! were ours never leaves the machine. The RPC is the caller's choice, its
//! own node or one reached over Tor; this module never opens a connection.

const std = @import("std");
const digest = @import("../digest.zig");
const memo = @import("../memo.zig");
const Digest = digest.Digest;

pub const Event = struct {
    leaf_index: usize,
    cm: Digest,
    memo: memo.Memo,
    block: u64,
};

pub const Error = error{
    /// The events skip a leaf or repeat one: the mirror would diverge from
    /// the pool's tree, and every later witness would prove against a root
    /// nobody published.
    Gap,
};

pub const Report = struct {
    absorbed: usize = 0,
    ours: usize = 0,
};

/// Absorb `events`, which must continue the wallet's tree leaf by leaf, and
/// keep the notes that open to us. `w` is a `wallet.Wallet`.
pub fn scan(w: anytype, events: []const Event) !Report {
    var r: Report = .{};
    for (events) |*e| {
        if (e.leaf_index != w.tree.len()) return error.Gap;
        const at = try w.absorb(e.cm);
        r.absorbed += 1;
        if (try w.receive(&e.memo, at, e.block)) r.ours += 1;
    }
    return r;
}
