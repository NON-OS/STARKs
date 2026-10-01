// NONOS Operating System (AGPL-3.0-or-later)

use super::format::P;
use super::*;
use sha3::{Digest, Sha3_256};

fn payee(b: u8) -> Payee {
    Payee::from_seed([b; 32])
}

fn opening() -> Opening {
    Opening {
        value: 1_000_000_000_000_000_000,
        asset_id: 1,
        blinding: [11, 22, 33, 44],
    }
}

const LEAF: [u8; 32] = [0x5a; 32];

fn sealed_to(p: &Payee, r: u8) -> [u8; BLOB_BYTES] {
    let (_, ek) =
        parse_address(&p.address([1, 2, 3, 4])).expect("an address this crate wrote reads back");
    seal_with(&ek, opening(), &LEAF, &[r; 64])
}

#[test]
fn the_layout_is_the_specified_one() {
    assert_eq!(KEM_BYTES, 1120);
    assert_eq!(BLOB_BYTES, 1186);
    assert_eq!(ADDRESS_BYTES, 1249);
    let blob = sealed_to(&payee(7), 9);
    assert_eq!(blob[0], VERSION);
}

#[test]
fn the_payee_opens_its_note() {
    let p = payee(7);
    assert_eq!(p.open(&sealed_to(&p, 9), &LEAF), Some(opening()));
}

#[test]
fn another_payee_opens_nothing() {
    assert_eq!(payee(8).open(&sealed_to(&payee(7), 9), &LEAF), None);
}

/// A blob copied onto another output does not open: the leaf is in the AAD.
#[test]
fn a_blob_is_bound_to_its_leaf() {
    let p = payee(7);
    let mut other = LEAF;
    other[31] ^= 1;
    assert_eq!(p.open(&sealed_to(&p, 9), &other), None);
}

/// One bit anywhere after the version refuses the blob.
#[test]
fn every_byte_is_authenticated() {
    let p = payee(7);
    let blob = sealed_to(&p, 9);
    for at in [1, 2, 500, 1121, 1122, 1150, 1169, 1170, 1185] {
        let mut b = blob;
        b[at] ^= 1;
        assert_eq!(p.open(&b, &LEAF), None, "byte {at}");
    }
}

#[test]
fn another_version_or_length_is_skipped() {
    let p = payee(7);
    let mut b = sealed_to(&p, 9);
    b[0] = 0x02;
    assert_eq!(p.open(&b, &LEAF), None);
    let short = &sealed_to(&p, 9)[..BLOB_BYTES - 1];
    assert_eq!(p.open(short, &LEAF), None);
}

/// Two notes to one payee carry tags that are not the payee's: over many
/// notes the tag takes many values, so it names no one.
#[test]
fn the_tag_is_per_note() {
    let p = payee(7);
    let mut seen = [false; 256];
    for r in 0..=255u8 {
        seen[sealed_to(&p, r)[1] as usize] = true;
    }
    assert!(
        seen.iter().filter(|s| **s).count() > 100,
        "tags repeat per payee"
    );
}

#[test]
fn a_non_canonical_blinding_is_refused() {
    let mut b = Opening {
        value: 1,
        asset_id: 1,
        blinding: [P, 0, 0, 0],
    }
    .to_bytes();
    assert_eq!(Opening::from_bytes(&b), None);
    b[16..24].copy_from_slice(&(P - 1).to_le_bytes());
    assert!(Opening::from_bytes(&b).is_some());
}

#[test]
fn an_address_with_a_non_canonical_key_is_refused() {
    let mut a = payee(7).address([1, 2, 3, 4]);
    a[1..9].copy_from_slice(&P.to_le_bytes());
    assert!(parse_address(&a).is_none());
}

#[test]
fn fresh_randomness_seals_and_opens() {
    let p = payee(3);
    let (_, ek) = parse_address(&p.address([5, 6, 7, 8])).expect("reads back");
    let a = seal(&ek, opening(), &LEAF).expect("the OS has entropy");
    let b = seal(&ek, opening(), &LEAF).expect("the OS has entropy");
    assert_ne!(a, b, "two seals of one note are two blobs");
    assert_eq!(p.open(&a, &LEAF), Some(opening()));
    assert_eq!(p.open(&b, &LEAF), Some(opening()));
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// The vector a second implementation checks itself against: payee seed
/// 0x07 * 32, encapsulation randomness 0x09 * 64, value 10^18, asset 1,
/// blinding [11, 22, 33, 44], leaf 0x5a * 32. Pinned from this crate's first
/// run, so it guards against drift here and is the target elsewhere; the KEM
/// under it is checked against the X-Wing draft's own vectors by that crate.
#[test]
fn the_vector() {
    let blob = sealed_to(&payee(7), 9);
    assert_eq!(blob[1], 0xd2, "view tag");
    assert_eq!(
        hex(&Sha3_256::digest(blob)),
        "78fbb6f16dfdcf4b5cc87ecb0cca92c4aa44b4747f3b2c183a9d3eb9152e1dc9",
        "blob"
    );
    assert_eq!(
        hex(&Sha3_256::digest(payee(7).encapsulation_key())),
        "4c82604001ad0b7a4cbc022c322f5e757f09ba4a5b095c8af545caeeac6836c8",
        "encapsulation key"
    );
}
