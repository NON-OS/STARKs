// NONOS Operating System (AGPL-3.0-or-later)
//! The pinned shape A transfer, loaded once: its bytes, its public words, its
//! parameter set and its periodic root, each computed from the circuit here
//! and never taken from the file beside it.

use stark_proofs::crypto::stark::air::periodic_root;
use stark_proofs::crypto::stark::field::Fp;
use stark_proofs::proof_wire::ParamSet;
use stark_proofs::shield::join::join_split_shape;
use stark_proofs::shield::member::TREE_DEPTH;
use stark_proofs::shield_params::direct;
use std::sync::OnceLock;

pub const Q: usize = 19;
pub const GRIND: u32 = 28;

pub struct Pin {
    pub proof: Vec<u8>,
    pub words: Vec<Fp>,
    pub root: [u8; 32],
    pub params: ParamSet,
}

static PIN: OnceLock<Pin> = OnceLock::new();

pub fn pin() -> &'static Pin {
    PIN.get_or_init(|| {
        let dir = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../spec/transfer/transfer-eth-shape1"
        );
        let proof = std::fs::read(format!("{dir}/proof.bin")).expect("pinned proof");
        let json = std::fs::read_to_string(format!("{dir}/publics.json")).expect("pinned publics");
        let (a, b) = (json.find('[').expect("["), json.find(']').expect("]"));
        let words: Vec<Fp> = json[a + 1..b]
            .split(',')
            .map(|x| Fp::from_u64(x.trim().parse::<u64>().expect("limb")))
            .collect();
        let air = join_split_shape(TREE_DEPTH, &words);
        let params = ParamSet::of(&air, Q, GRIND, direct::EXTRA_BLOWUP_BITS);
        let root = periodic_root(&air, direct::EXTRA_BLOWUP_BITS);
        Pin {
            proof,
            words,
            root,
            params,
        }
    })
}
