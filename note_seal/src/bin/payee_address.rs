// NONOS Operating System (AGPL-3.0-or-later)
//! A receiver's address, the thing a sender pays to.
//!
//!     payee_address <seed_hex> <spend_pk_word>
//!
//! `seed_hex` is the receiver's X-Wing seed, 32 bytes, and `spend_pk_word`
//! its spend key as the pool packs a digest (limb 3 first, big endian). Prints
//! the 1,249-byte address as hex: version, spend key, encapsulation key.

use note_seal::Payee;

fn die(why: &str) -> ! {
    eprintln!("{why}");
    std::process::exit(1)
}

fn unhex32(s: &str) -> [u8; 32] {
    let s = s.trim_start_matches("0x");
    if s.len() != 64 {
        die("32 bytes of hex");
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap_or_else(|_| die("not hex"));
    }
    out
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() != 2 {
        die("usage: payee_address <seed_hex> <spend_pk_word>");
    }
    let payee = Payee::from_seed(unhex32(&a[0]));
    let w = unhex32(&a[1]);
    // The pool word is limb 3 first, each limb big endian.
    let spend_pk: [u64; 4] = core::array::from_fn(|k| {
        let at = 24 - 8 * k;
        u64::from_be_bytes(w[at..at + 8].try_into().unwrap_or([0; 8]))
    });
    let addr = payee.address(spend_pk);
    println!("{}", addr.iter().map(|x| format!("{x:02x}")).collect::<String>());
}
