// NONOS Operating System (AGPL-3.0-or-later)
//! Any bytes into the format 7 reader, at the shape A parameter set. The reader
//! must return, never panic, and never read past the input.
#![no_main]

use libfuzzer_sys::fuzz_target;
use stark_proofs::proof_wire::{deserialize_rounds_shared, read_header};

#[path = "pin.rs"]
mod pin;

fuzz_target!(|data: &[u8]| {
    let _ = read_header(data);
    let _ = deserialize_rounds_shared(data, &pin::pin().params);
});
