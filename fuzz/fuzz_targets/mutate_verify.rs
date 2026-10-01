// NONOS Operating System (AGPL-3.0-or-later)
//! The pinned shape A transfer, changed and verified. The fuzzer's bytes choose
//! the change: up to eight byte flips anywhere in the proof, or one public word
//! replaced. Anything that differs from the pinned proof and its words must be
//! refused, by the reader or by the verifier. The only accepted input is the
//! unchanged one.
#![no_main]

use libfuzzer_sys::fuzz_target;
use stark_proofs::crypto::stark::air::stark_verify_ext_rounds_shared_why;
use stark_proofs::crypto::stark::field::{Fp, P};
use stark_proofs::proof_wire::deserialize_rounds_shared;
use stark_proofs::shield::join::join_split_shape;
use stark_proofs::shield::member::TREE_DEPTH;
use stark_proofs::shield_params::direct;

#[path = "pin.rs"]
mod pin;

fuzz_target!(|data: &[u8]| {
    let p = pin::pin();
    let mut proof = p.proof.clone();
    let mut words = p.words.clone();
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };
    if mode & 1 == 0 {
        // Up to eight flips: a u32 position and a nonzero xor byte each.
        for op in rest.chunks_exact(5).take(8) {
            let at = u32::from_le_bytes([op[0], op[1], op[2], op[3]]) as usize % proof.len();
            if op[4] != 0 {
                proof[at] ^= op[4];
            }
        }
    } else if rest.len() >= 9 {
        // One public word replaced by a canonical value.
        let at = rest[0] as usize % words.len();
        let v = u64::from_le_bytes(rest[1..9].try_into().unwrap_or([0; 8])) % P;
        words[at] = Fp::from_u64(v);
    }
    if proof == p.proof && words == p.words {
        return;
    }
    let Some((skeleton, shared)) = deserialize_rounds_shared(&proof, &p.params) else {
        return;
    };
    let air = join_split_shape(TREE_DEPTH, &words);
    let verdict = stark_verify_ext_rounds_shared_why(
        air,
        &skeleton,
        &shared,
        pin::Q,
        pin::GRIND,
        direct::EXTRA_BLOWUP_BITS,
        &p.root,
        &words,
    );
    assert!(
        verdict.is_err(),
        "a changed proof or statement was accepted"
    );
});
