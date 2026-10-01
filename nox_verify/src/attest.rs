// NONOS Operating System (AGPL-3.0-or-later)
//! The attestation statement's nine words, computed the way a gate computes
//! them: the tree's root, the context digest's four words, the kind.
//!
//! The context digest is `nonos_attest_path::context_digest`: BLAKE3 over a
//! domain tag, the context's length as a little-endian u32, and the context
//! bytes. The context is what the gate is about to run and grant (a capsule's
//! measurement, capability word and policy epoch; a kernel's measurement and
//! boot epoch), so the words come from those bytes and nowhere else.

use crate::crypto::stark::air::{Poseidon, RATE};
use crate::crypto::stark::field::{Fp, P};
use crate::crypto::stark::hash::blake3_hash;
use alloc::vec::Vec;

const DOMAIN: &[u8] = b"NONOS-ATTEST-PATH-LEAF-v3";

/// "NONOSLV3", lane 0 of a leaf's compression.
const LEAF_DOMAIN: u64 = 0x4E4F_4E4F_534C_5633;

/// Poseidon at 32 rounds, the tree's and the circuit's.
fn hasher() -> Poseidon {
    Poseidon::new(5, [Fp::ZERO; RATE])
}

fn fp4(w: &[u64; 4]) -> Option<[Fp; RATE]> {
    if w.iter().any(|&v| v >= P) {
        return None;
    }
    Some(core::array::from_fn(|i| Fp::from_u64(w[i])))
}

fn u4(f: &[Fp; RATE]) -> [u64; 4] {
    core::array::from_fn(|i| f[i].to_u64())
}

pub const KIND_KERNEL: u64 = 0;
pub const KIND_CAPSULE: u64 = 1;
pub const KIND_BOOTLOADER: u64 = 3;

/// The context digest, or `None` for a context longer than a u32 counts.
pub fn context_digest(ctx: &[u8]) -> Option<[u8; 32]> {
    let len = u32::try_from(ctx.len()).ok()?;
    let mut b = Vec::with_capacity(DOMAIN.len() + 4 + ctx.len());
    b.extend_from_slice(DOMAIN);
    b.extend_from_slice(&len.to_le_bytes());
    b.extend_from_slice(ctx);
    Some(blake3_hash(&b))
}

/// A digest's four little-endian words, each reduced below p, as the leaf
/// reads them.
pub fn digest_words(d: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| {
        let mut w = [0u8; 8];
        w.copy_from_slice(&d[8 * i..8 * i + 8]);
        let v = u64::from_le_bytes(w);
        if v >= P {
            v - P
        } else {
            v
        }
    })
}

/// The nine words for a slot of `root` holding `ctx` as `kind`. `None` for a
/// kind that is never proven, a root word not below p, or an oversized
/// context.
pub fn words(root: [u64; 4], ctx: &[u8], kind: u64) -> Option<[u64; 9]> {
    if !matches!(kind, KIND_KERNEL | KIND_CAPSULE | KIND_BOOTLOADER) || root.iter().any(|&w| w >= P)
    {
        return None;
    }
    let d = digest_words(&context_digest(ctx)?);
    Some([
        root[0], root[1], root[2], root[3], d[0], d[1], d[2], d[3], kind,
    ])
}

/// A slot's leaf: `nonos_attest_path::leaf_of`, the compression of
/// `[NONOSLV3, d0, d1, d2]` and `[d3, kind, 0, 0]`. Any kind, padding
/// included, since a page refolding a tree needs every slot's leaf.
pub fn leaf(kind: u64, d: &[u8; 32]) -> [u64; 4] {
    let w = digest_words(d);
    let f = |v: u64| Fp::from_u64(v);
    u4(&hasher().compress(
        &[f(LEAF_DOMAIN), f(w[0]), f(w[1]), f(w[2])],
        &[f(w[3]), f(kind), Fp::ZERO, Fp::ZERO],
    ))
}

/// The root of a complete tree over `leaves`, nodes `compress(left, right)`.
/// `None` unless the count is a power of two from 1 to 2^16 and every word is
/// below p.
pub fn fold_tree(leaves: &[[u64; 4]]) -> Option<[u64; 4]> {
    let n = leaves.len();
    if n == 0 || n > 1 << 16 || !n.is_power_of_two() {
        return None;
    }
    let h = hasher();
    let mut level: Vec<[Fp; RATE]> = leaves.iter().map(fp4).collect::<Option<_>>()?;
    while level.len() > 1 {
        level = level
            .chunks_exact(2)
            .map(|p| h.compress(&p[0], &p[1]))
            .collect();
    }
    level.first().map(u4)
}

/// The root a leaf reaches along a path: `siblings[i]` at level `i`, on the
/// left of the node when `right[i]`. `None` for mismatched lengths, a path
/// longer than 32, or a word not below p.
pub fn fold_path(leaf: [u64; 4], siblings: &[[u64; 4]], right: &[bool]) -> Option<[u64; 4]> {
    if siblings.len() != right.len() || siblings.len() > 32 {
        return None;
    }
    let h = hasher();
    let mut node = fp4(&leaf)?;
    for (sib, &r) in siblings.iter().zip(right) {
        let s = fp4(sib)?;
        node = if r {
            h.compress(&s, &node)
        } else {
            h.compress(&node, &s)
        };
    }
    Some(u4(&node))
}
