// NONOS Operating System (AGPL-3.0-or-later)

//! The bytes of version 0x01: sizes, the domains of the two derivations, the
//! opening and the rules a reader applies to it.

use chacha20poly1305::aead::KeyInit;
use chacha20poly1305::ChaCha20Poly1305;
use sha3::{Digest, Sha3_256};

/// The only version this crate writes or reads.
pub const VERSION: u8 = 0x01;
/// X-Wing ciphertext: 1,088 bytes of ML-KEM-768 and 32 of X25519.
pub const KEM_BYTES: usize = x_wing::CIPHERTEXT_SIZE;
/// The opening: value, asset, blinding.
pub const OPENING_BYTES: usize = 8 + 8 + 32;
/// Poly1305.
pub const TAG_BYTES: usize = 16;
/// A whole blob.
pub const BLOB_BYTES: usize = 2 + KEM_BYTES + OPENING_BYTES + TAG_BYTES;
/// A payee's X-Wing encapsulation key.
pub const ENCAPSULATION_KEY_BYTES: usize = x_wing::ENCAPSULATION_KEY_SIZE;
/// A payee's address: the version, the spend key as four field words, the
/// encapsulation key.
pub const ADDRESS_BYTES: usize = 1 + 32 + ENCAPSULATION_KEY_BYTES;

pub(crate) const TAG_DOMAIN: &[u8] = b"NOX-NOTE-VIEW-TAG-v1";
pub(crate) const KEY_DOMAIN: &[u8] = b"NOX-NOTE-SEAL-KEY-v1";

/// The Goldilocks modulus: every blinding word must be below it.
pub(crate) const P: u64 = 0xFFFF_FFFF_0000_0001;

/// What a payee needs to spend a note besides its own key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Opening {
    pub value: u64,
    pub asset_id: u64,
    pub blinding: [u64; 4],
}

impl Opening {
    pub(crate) fn to_bytes(self) -> [u8; OPENING_BYTES] {
        let mut b = [0u8; OPENING_BYTES];
        b[0..8].copy_from_slice(&self.value.to_le_bytes());
        b[8..16].copy_from_slice(&self.asset_id.to_le_bytes());
        for (k, w) in self.blinding.iter().enumerate() {
            b[16 + 8 * k..24 + 8 * k].copy_from_slice(&w.to_le_bytes());
        }
        b
    }

    /// Refuses a blinding word at or above the modulus: two encodings of one
    /// field element are two blobs for one note.
    pub(crate) fn from_bytes(b: &[u8]) -> Option<Opening> {
        if b.len() != OPENING_BYTES {
            return None;
        }
        let word = |at: usize| u64::from_le_bytes(b[at..at + 8].try_into().unwrap_or([0u8; 8]));
        let blinding = [word(16), word(24), word(32), word(40)];
        if blinding.iter().any(|w| *w >= P) {
            return None;
        }
        Some(Opening {
            value: word(0),
            asset_id: word(8),
            blinding,
        })
    }
}

pub(crate) fn view_tag(ss: &[u8]) -> u8 {
    let mut h = Sha3_256::new();
    h.update(TAG_DOMAIN);
    h.update(ss);
    h.finalize()[0]
}

pub(crate) fn seal_key(ss: &[u8]) -> ChaCha20Poly1305 {
    let mut h = Sha3_256::new();
    h.update(KEY_DOMAIN);
    h.update(ss);
    let k = h.finalize();
    ChaCha20Poly1305::new_from_slice(&k)
        .unwrap_or_else(|_| unreachable!("a SHA3-256 digest is a ChaCha20 key"))
}

pub(crate) fn aad(tag: u8, leaf: &[u8; 32]) -> [u8; 34] {
    let mut a = [0u8; 34];
    a[0] = VERSION;
    a[1] = tag;
    a[2..].copy_from_slice(leaf);
    a
}

pub(crate) const NONCE: [u8; 12] = [0u8; 12];
