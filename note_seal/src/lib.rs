// NONOS Operating System (AGPL-3.0-or-later)

//! The client data a settlement publishes for each output note, version 0x01.
//!
//! The pool counts these bytes and emits them; it never reads one. Everything
//! here is a convention between a sender and a payee, and it is written down
//! to the byte because two wallets implementing a sentence do not interoperate.
//!
//! ```text
//! byte  0            version, 0x01
//! byte  1            view tag: SHA3-256(TAG_DOMAIN || ss)[0]
//! bytes 2..1122      X-Wing ciphertext: ML-KEM-768 then the X25519 ephemeral key
//! bytes 1122..1186   ChaCha20-Poly1305 of the 48-byte opening,
//!                    key   SHA3-256(KEY_DOMAIN || ss)
//!                    nonce twelve zero bytes
//!                    aad   byte 0 || byte 1 || the leaf commitment, 32 bytes
//! ```
//!
//! `ss` is the X-Wing shared secret (draft-connolly-cfrg-xwing-kem-06), which
//! combines X25519 and ML-KEM-768 so the note stays sealed while either holds.
//! The view tag is derived from that combined secret and not from the X25519
//! half: a tag an attacker who breaks X25519 could recompute would let them
//! sort every note by recipient, and that partition is permanent.
//!
//! Each note encapsulates afresh, so each key is used once and the zero nonce
//! is never reused under a key. The leaf commitment in the AAD binds a blob to
//! the note it describes: a blob copied onto another output does not open.
//!
//! Opening a blob is not accepting it. A payee recomputes the commitment from
//! the opening and its own spend key and compares it with the leaf the pool
//! emitted; the pool treats the owner digest as opaque and cannot do it.

mod format;
mod payee;
mod seal;

pub use format::{Opening, ADDRESS_BYTES, BLOB_BYTES, ENCAPSULATION_KEY_BYTES, KEM_BYTES};
pub use format::{OPENING_BYTES, TAG_BYTES, VERSION};
pub use payee::{parse_address, Payee};
pub use seal::{seal, seal_with};

#[cfg(test)]
mod tests;
