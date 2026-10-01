// NONOS Operating System (AGPL-3.0-or-later)
//! The nullifier set's leaf: the key, the key it points at, and whether
//! nothing is above it.

const field = @import("../field.zig");
const digest = @import("../digest.zig");
const poseidon = @import("../poseidon.zig");
const Digest = digest.Digest;
const Poseidon = poseidon.Poseidon;

/// ASCII "IMTL", at the first limb past the payload.
pub const LEAF_DOMAIN: u64 = 0x494D_544C;
/// Limbs the payload occupies before the tag.
pub const LEAF_LIMBS: usize = 10;

/// `is_last` is a flag rather than a maximum sentinel. A sentinel would have
/// to be non-canonical to sit above every key, and a non-canonical value does
/// not survive the field reduction, so the leaf would commit to something the
/// comparison never sees.
pub const Leaf = struct {
    value: Digest,
    next_index: u64,
    /// Zero when `is_last`, which the constraint requires rather than assumes.
    next_value: Digest,
    is_last: bool,

    /// The empty set: one leaf below every key, pointing nowhere.
    pub fn sentinel() Leaf {
        return .{
            .value = digest.ZERO,
            .next_index = 0,
            .next_value = digest.ZERO,
            .is_last = true,
        };
    }

    /// An unwritten slot. A real leaf, so the zeros chain is based on a hash
    /// rather than on nothing.
    pub fn empty() Leaf {
        return .{
            .value = digest.ZERO,
            .next_index = 0,
            .next_value = digest.ZERO,
            .is_last = false,
        };
    }

    /// value, next_value, next_index, is_last, then the tag. The two keys
    /// occupy the first two quads so a compression takes each whole.
    pub fn limbs(self: *const Leaf) [16]field.Fp {
        var l: [16]field.Fp = [_]field.Fp{0} ** 16;
        @memcpy(l[0..4], &self.value);
        @memcpy(l[4..8], &self.next_value);
        l[8] = self.next_index;
        l[LEAF_LIMBS - 1] = @intFromBool(self.is_last);
        l[LEAF_LIMBS] = LEAF_DOMAIN;
        return l;
    }

    /// The same three compression tree a note commitment uses, so one hasher
    /// serves both trees.
    pub fn hash(self: *const Leaf, h: *const Poseidon) Digest {
        const l = self.limbs();
        return h.commit16(&l);
    }
};
