// NONOS Operating System (AGPL-3.0-or-later)
//! The order the set is kept in, and what absence means under it.

const std = @import("std");
const digest = @import("../digest.zig");
const Leaf = @import("leaf.zig").Leaf;
const Digest = digest.Digest;

/// The four limbs as one 256 bit integer, little endian. Every limb of a
/// nullifier is below p, so the same comparison runs as `uint256 <` on chain
/// and as a limb chain in circuit without either side translating.
pub fn cmp(a: *const Digest, b: *const Digest) std.math.Order {
    var i: usize = 4;
    while (i > 0) {
        i -= 1;
        if (a[i] != b[i]) return if (a[i] < b[i]) .lt else .gt;
    }
    return .eq;
}

/// Non-membership: the low leaf sits strictly below the key and its neighbour
/// strictly above, or it is the last leaf and nothing is above it.
///
/// Both bounds strict. Equal to the low value is the key already in the set,
/// which is a double spend; equal to the neighbour is the next leaf's key,
/// which is the same. They fail through different comparisons, so each carries
/// its own forgery.
pub fn excludes(low: *const Leaf, v: *const Digest) bool {
    if (cmp(&low.value, v) != .lt) return false;
    if (low.is_last) return true;
    return cmp(v, &low.next_value) == .lt;
}
