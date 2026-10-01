// NONOS Operating System (AGPL-3.0-or-later)
//! Seal one output's opening to a fresh payee.
//!
//!     seal_note <leaf_hex> <value> <asset_id> <b0> <b1> <b2> <b3> [seed=<hex>]
//!
//! Seals to the payee `seed` names, a receiver's standing identity, or to a
//! fresh payee drawn from the operating system. Prints the seed, the payee's
//! encapsulation key hash, and the 1,186-byte blob as hex, one per line. The
//! seed is the payee's receiving secret: whoever keeps it opens the note.

use note_seal::{seal, Opening, Payee};

fn die(why: &str) -> ! {
    eprintln!("{why}");
    std::process::exit(1)
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex32(s: &str) -> [u8; 32] {
    let s = s.trim_start_matches("0x");
    if s.len() != 64 {
        die("a leaf is 32 bytes of hex");
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap_or_else(|_| die("not hex"));
    }
    out
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() != 7 && a.len() != 8 {
        die("usage: seal_note <leaf_hex> <value> <asset_id> <b0> <b1> <b2> <b3> [seed=<hex>]");
    }
    let n = |i: usize| a[i].parse::<u64>().unwrap_or_else(|_| die("not a u64"));
    let leaf = unhex32(&a[0]);
    let opening = Opening { value: n(1), asset_id: n(2), blinding: [n(3), n(4), n(5), n(6)] };
    let seed = match a.get(7).and_then(|s| s.strip_prefix("seed=")) {
        Some(hex) => unhex32(hex),
        None => {
            let mut s = [0u8; 32];
            getrandom::fill(&mut s).unwrap_or_else(|_| die("no entropy"));
            s
        }
    };
    let payee = Payee::from_seed(seed);
    let (_, ek) = note_seal::parse_address(&payee.address([0; 4])).unwrap_or_else(|| die("address"));
    let blob = seal(&ek, opening, &leaf).unwrap_or_else(|| die("no entropy"));
    if payee.open(&blob, &leaf) != Some(opening) {
        die("the blob does not open for its own payee; nothing printed");
    }
    println!("{}", hex(&seed));
    println!("{}", hex(&payee.encapsulation_key()));
    println!("{}", hex(&blob));
}
