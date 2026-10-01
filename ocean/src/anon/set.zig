// NONOS Operating System (AGPL-3.0-or-later)
//! How many notes a spend hides among.
//!
//! A spend proves its note is one of the pool's leaves without saying which.
//! The set it hides among is every leaf in the tree it proves against, but
//! an observer who knows roughly when the note arrived narrows that to the
//! leaves that landed since. Both numbers are shown; the warning reads the
//! smaller one.

pub const Set = struct {
    /// Every leaf the spend could be.
    total: usize,
    /// Leaves that landed after this note: the set left to an observer who
    /// knows when it was deposited.
    since: usize,
    /// `since` is below the policy's minimum.
    small: bool,
};

pub fn measure(tree_len: usize, leaf_index: usize, min_set: usize) Set {
    const since = if (tree_len > leaf_index + 1) tree_len - leaf_index - 1 else 0;
    return .{ .total = tree_len, .since = since, .small = since < min_set };
}
