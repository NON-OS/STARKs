// NONOS Operating System (AGPL-3.0-or-later)
//! Open a blob as its payee.
//!
//!     open_note <seed_hex> <leaf_hex> <blob_hex>
//!
//! Prints the opening, or refuses. The caller then recomputes the commitment
//! from it and compares it with the leaf; this does not.

use note_seal::Payee;

fn die(why: &str) -> ! {
    eprintln!("{why}");
    std::process::exit(1)
}

fn unhex(s: &str) -> Vec<u8> {
    let s = s.trim().trim_start_matches("0x");
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap_or_else(|_| die("not hex")))
        .collect()
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() != 3 {
        die("usage: open_note <seed_hex> <leaf_hex> <blob_hex>");
    }
    let seed: [u8; 32] = unhex(&a[0]).try_into().unwrap_or_else(|_| die("a seed is 32 bytes"));
    let leaf: [u8; 32] = unhex(&a[1]).try_into().unwrap_or_else(|_| die("a leaf is 32 bytes"));
    match Payee::from_seed(seed).open(&unhex(&a[2]), &leaf) {
        Some(o) => println!(
            "{{\"value\": {}, \"asset_id\": {}, \"blinding\": [{}, {}, {}, {}]}}",
            o.value, o.asset_id, o.blinding[0], o.blinding[1], o.blinding[2], o.blinding[3]
        ),
        None => die("not a note for this payee at this leaf"),
    }
}
