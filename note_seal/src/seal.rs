// NONOS Operating System (AGPL-3.0-or-later)

//! The sending side: sealing an opening to a payee.

use super::format::{aad, seal_key, view_tag, Opening, BLOB_BYTES, KEM_BYTES, NONCE, VERSION};
use chacha20poly1305::aead::{Aead, Payload};

/// Seal `opening` to `ek` for the output whose leaf commitment is `leaf`, with
/// the 64 bytes of encapsulation randomness given. A wallet draws them fresh
/// from the operating system's generator for every note; `seal` does.
pub fn seal_with(
    ek: &x_wing::EncapsulationKey,
    opening: Opening,
    leaf: &[u8; 32],
    randomness: &[u8; 64],
) -> [u8; BLOB_BYTES] {
    let (ct, ss) = ek.encapsulate_deterministic(&(*randomness).into());
    let tag = view_tag(&ss);
    let sealed = seal_key(&ss)
        .encrypt(
            &NONCE.into(),
            Payload {
                msg: &opening.to_bytes(),
                aad: &aad(tag, leaf),
            },
        )
        .unwrap_or_else(|_| {
            unreachable!("48 bytes and 34 of AAD are within ChaCha20-Poly1305's limits")
        });
    let mut blob = [0u8; BLOB_BYTES];
    blob[0] = VERSION;
    blob[1] = tag;
    blob[2..2 + KEM_BYTES].copy_from_slice(ct.as_ref());
    blob[2 + KEM_BYTES..].copy_from_slice(&sealed);
    blob
}

/// Seal with fresh randomness from the operating system.
pub fn seal(
    ek: &x_wing::EncapsulationKey,
    opening: Opening,
    leaf: &[u8; 32],
) -> Option<[u8; BLOB_BYTES]> {
    let mut r = [0u8; 64];
    getrandom::fill(&mut r).ok()?;
    Some(seal_with(ek, opening, leaf, &r))
}
