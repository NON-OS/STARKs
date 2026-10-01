// NONOS Operating System (AGPL-3.0-or-later)

//! The receiving side: a payee's key, its address, and reading a blob.

use super::format::{aad, seal_key, view_tag, Opening, ADDRESS_BYTES, BLOB_BYTES};
use super::format::{ENCAPSULATION_KEY_BYTES, KEM_BYTES, NONCE, P, VERSION};
use chacha20poly1305::aead::{Aead, Payload};
use x_wing::{Decapsulate, Decapsulator, KeyExport, TryKeyInit};

/// A payee's receiving key: the 32-byte X-Wing seed. The encapsulation key a
/// sender needs is derived from it.
pub struct Payee {
    dk: x_wing::DecapsulationKey,
}

impl Payee {
    pub fn from_seed(seed: [u8; 32]) -> Payee {
        Payee {
            dk: x_wing::DecapsulationKey::from(seed),
        }
    }

    /// The encapsulation key to publish.
    pub fn encapsulation_key(&self) -> [u8; ENCAPSULATION_KEY_BYTES] {
        let mut out = [0u8; ENCAPSULATION_KEY_BYTES];
        out.copy_from_slice(&self.dk.encapsulation_key().to_bytes());
        out
    }

    /// The address a sender pays: version, spend key, encapsulation key.
    pub fn address(&self, spend_pk: [u64; 4]) -> [u8; ADDRESS_BYTES] {
        let mut a = [0u8; ADDRESS_BYTES];
        a[0] = VERSION;
        for (k, w) in spend_pk.iter().enumerate() {
            a[1 + 8 * k..9 + 8 * k].copy_from_slice(&w.to_le_bytes());
        }
        a[33..].copy_from_slice(&self.encapsulation_key());
        a
    }

    /// The opening in `blob` if it is a version 0x01 note for this payee
    /// bound to `leaf`, and nothing otherwise. A blob of another version or
    /// length is skipped, never guessed at.
    pub fn open(&self, blob: &[u8], leaf: &[u8; 32]) -> Option<Opening> {
        if blob.len() != BLOB_BYTES || blob[0] != VERSION {
            return None;
        }
        let ct = x_wing::Ciphertext::try_from(&blob[2..2 + KEM_BYTES]).ok()?;
        let ss = self.dk.decapsulate(&ct);
        let tag = view_tag(&ss);
        if blob[1] != tag {
            return None;
        }
        let pt = seal_key(&ss)
            .decrypt(
                &NONCE.into(),
                Payload {
                    msg: &blob[2 + KEM_BYTES..],
                    aad: &aad(tag, leaf),
                },
            )
            .ok()?;
        Opening::from_bytes(&pt)
    }
}

/// A payee's address, read back: the spend key and the encapsulation key.
pub fn parse_address(a: &[u8]) -> Option<([u64; 4], x_wing::EncapsulationKey)> {
    if a.len() != ADDRESS_BYTES || a[0] != VERSION {
        return None;
    }
    let mut pk = [0u64; 4];
    for (k, w) in pk.iter_mut().enumerate() {
        *w = u64::from_le_bytes(a[1 + 8 * k..9 + 8 * k].try_into().ok()?);
        if *w >= P {
            return None;
        }
    }
    let ek = x_wing::EncapsulationKey::new_from_slice(&a[33..]).ok()?;
    Some((pk, ek))
}
