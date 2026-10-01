// NONOS Operating System (AGPL-3.0-or-later)
//! Every pinned proof verifies through the program image, and every change a
//! gate must refuse is refused: a public word moved, a byte flipped, the wrong
//! statement, a drifted shape, a tampered image, a length out of bounds.

use nox_verify::statements::{ACTIVITY, ATTEST, CLAIM, NOT_BEFORE, TRANSFER};
use nox_verify::{verify, Refusal, Statement};

const SPEC: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../spec");
const P: u64 = 0xFFFF_FFFF_0000_0001;

fn publics(path: &str) -> Vec<u64> {
    let s = std::fs::read_to_string(path).expect("pinned publics");
    let (a, b) = (s.find('[').expect("["), s.find(']').expect("]"));
    s[a + 1..b]
        .split(',')
        .map(|w| w.trim().parse().expect("a word"))
        .collect()
}

/// `(directory, proof file)` for every pinned proof of a set.
fn pinned(set: &str, file: &str) -> Vec<(String, Vec<u8>, Vec<u64>)> {
    let mut out = Vec::new();
    let mut dirs: Vec<_> = std::fs::read_dir(format!("{SPEC}/{set}"))
        .expect("pinned set")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.join(file).exists())
        .collect();
    dirs.sort();
    for d in dirs {
        let proof = std::fs::read(d.join(file)).expect("proof");
        let words = publics(d.join("publics.json").to_str().expect("utf-8 path"));
        out.push((d.display().to_string(), proof, words));
    }
    assert!(!out.is_empty(), "no pinned proofs in {set}");
    out
}

fn sets() -> [(&'static Statement, &'static str, &'static str); 7] {
    [
        (&ACTIVITY, "activity", "proof.bin"),
        (&ACTIVITY, "wallet-vectors-activity", "proof.bin"),
        (&ATTEST, "attest", "proof.bin"),
        (&TRANSFER, "transfer", "proof.bin"),
        (&NOT_BEFORE, "not-before", "proof.bin"),
        (&CLAIM, "claim", "proof.bin"),
        (
            &NOT_BEFORE,
            "wallet-vectors-not-before",
            "proof-format7.bin",
        ),
    ]
}

#[test]
fn every_pinned_proof_verifies_through_its_image() {
    for (st, set, file) in sets() {
        for (name, proof, words) in pinned(set, file) {
            assert_eq!(verify(st, &proof, &words), Ok(()), "{name}");
        }
    }
}

#[test]
fn a_moved_public_word_is_refused() {
    for (st, set, file) in sets() {
        for (name, proof, words) in pinned(set, file) {
            let last = words.len() - 1;
            for i in [0, 4, 8, 16, 24, 25, 26, 28, 32, last]
                .into_iter()
                .filter(|&i| i <= last)
            {
                let mut w = words.clone();
                w[i] = (w[i] + 1) % P;
                assert_eq!(
                    verify(st, &proof, &w),
                    Err(Refusal::Proof),
                    "{name} word {i}"
                );
            }
        }
    }
}

#[test]
fn a_flipped_byte_is_refused() {
    for (st, set, file) in sets() {
        for (name, proof, words) in pinned(set, file) {
            for at in [8, 40, 41, 200, 5_000, proof.len() / 2, proof.len() - 5] {
                let mut p = proof.clone();
                p[at] ^= 0x01;
                assert!(verify(st, &p, &words).is_err(), "{name} byte {at}");
            }
        }
    }
}

#[test]
fn a_proof_is_refused_under_another_statement() {
    let (_, tr, w36) = pinned("transfer", "proof.bin").remove(0);
    let (_, nb, w37) = pinned("not-before", "proof.bin").remove(0);
    let (_, cl, w38) = pinned("claim", "proof.bin").remove(0);
    assert_eq!(verify(&NOT_BEFORE, &tr, &w36), Err(Refusal::Header));
    assert_eq!(verify(&TRANSFER, &nb, &w37), Err(Refusal::Header));
    assert_eq!(verify(&NOT_BEFORE, &cl, &w38), Err(Refusal::Header));
    assert_eq!(verify(&CLAIM, &nb, &w37), Err(Refusal::Header));
    let (_, at, w9) = pinned("attest", "proof.bin").remove(0);
    assert_eq!(verify(&TRANSFER, &at, &w9), Err(Refusal::Header));
    assert_eq!(verify(&ATTEST, &nb, &w37), Err(Refusal::Header));
    let (_, ac, w14) = pinned("activity", "proof.bin").remove(0);
    assert_eq!(verify(&CLAIM, &ac, &w14), Err(Refusal::Header));
    assert_eq!(verify(&ATTEST, &ac, &w14), Err(Refusal::Header));
    assert_eq!(verify(&ACTIVITY, &cl, &w38), Err(Refusal::Header));
    assert_eq!(verify(&ACTIVITY, &at, &w9), Err(Refusal::Header));
}

/// A slot's proof under another kind, another context or another root: the
/// three things a gate computes, each moved alone.
#[test]
fn an_attestation_is_refused_for_another_kind_context_or_root() {
    for (name, proof, words) in pinned("attest", "proof.bin") {
        let kind = words[8];
        for other in [0u64, 1, 3].into_iter().filter(|&k| k != kind) {
            let mut w = words.clone();
            w[8] = other;
            assert_eq!(
                verify(&ATTEST, &proof, &w),
                Err(Refusal::Proof),
                "{name} as kind {other}"
            );
        }
        for i in 0..8 {
            let mut w = words.clone();
            w[i] = (w[i] + 1) % P;
            assert_eq!(
                verify(&ATTEST, &proof, &w),
                Err(Refusal::Proof),
                "{name} word {i}"
            );
        }
    }
}

#[test]
fn the_wrong_word_count_or_a_word_above_p_is_refused() {
    let (_, proof, words) = pinned("not-before", "proof.bin").remove(0);
    assert_eq!(
        verify(&NOT_BEFORE, &proof, &words[..36]),
        Err(Refusal::Publics)
    );
    let mut longer = words.clone();
    longer.push(0);
    assert_eq!(verify(&NOT_BEFORE, &proof, &longer), Err(Refusal::Publics));
    let mut high = words.clone();
    high[3] = P;
    assert_eq!(verify(&NOT_BEFORE, &proof, &high), Err(Refusal::Publics));
}

#[test]
fn lengths_out_of_bounds_are_refused() {
    let (_, proof, words) = pinned("not-before", "proof.bin").remove(0);
    assert_eq!(
        verify(&NOT_BEFORE, &proof[..39], &words),
        Err(Refusal::Length)
    );
    assert_eq!(
        verify(&NOT_BEFORE, &proof[..proof.len() - 1], &words),
        Err(Refusal::Encoding)
    );
    let mut long = proof.clone();
    long.resize(NOT_BEFORE.max_proof_bytes + 1, 0);
    assert_eq!(verify(&NOT_BEFORE, &long, &words), Err(Refusal::Length));
    let mut trailing = proof.clone();
    trailing.push(0);
    assert_eq!(
        verify(&NOT_BEFORE, &trailing, &words),
        Err(Refusal::Encoding)
    );
}

/// A statement whose pin, image or numbers drifted verifies nothing.
#[test]
fn a_drifted_statement_is_refused() {
    let (_, proof, words) = pinned("not-before", "proof.bin").remove(0);

    let mut hash = NOT_BEFORE.program_hash;
    hash[0] ^= 1;
    let wrong_pin = Statement {
        program_hash: hash,
        ..copy(&NOT_BEFORE)
    };
    assert_eq!(verify(&wrong_pin, &proof, &words), Err(Refusal::Image));

    /*
     * The region split is not in the parameter id, so it passes the id check
     * and is refused by the engine, which compares it with the split the proof
     * carries. Width and degree are in the id.
     */
    let mut shape = NOT_BEFORE.shape;
    shape.region_width = 33;
    let wrong_split = Statement {
        shape,
        ..copy(&NOT_BEFORE)
    };
    assert_eq!(verify(&wrong_split, &proof, &words), Err(Refusal::Proof));

    let mut shape = NOT_BEFORE.shape;
    shape.trace_width = 45;
    let wrong_width = Statement {
        shape,
        ..copy(&NOT_BEFORE)
    };
    assert_eq!(verify(&wrong_width, &proof, &words), Err(Refusal::Shape));

    let mut shape = NOT_BEFORE.shape;
    shape.constraint_degree = 7;
    let wrong_degree = Statement {
        shape,
        ..copy(&NOT_BEFORE)
    };
    assert_eq!(verify(&wrong_degree, &proof, &words), Err(Refusal::Shape));

    let mut root = NOT_BEFORE.periodic_root;
    root[31] ^= 1;
    let wrong_root = Statement {
        periodic_root: root,
        ..copy(&NOT_BEFORE)
    };
    assert_eq!(verify(&wrong_root, &proof, &words), Err(Refusal::Proof));
}

fn copy(s: &Statement) -> Statement {
    Statement {
        program: s.program,
        program_hash: s.program_hash,
        periodic_root: s.periodic_root,
        shape: s.shape,
        extra_blowup_bits: s.extra_blowup_bits,
        points: s.points,
        words: s.words,
        max_proof_bytes: s.max_proof_bytes,
    }
}

/// The context digest is the kernel's: BLAKE3 over the domain tag, the
/// length and the context. The answer was computed by `b3sum` over those
/// exact bytes, on two machines.
#[test]
fn the_context_digest_is_the_kernels() {
    use nox_verify::attest::{context_digest, digest_words, words, KIND_CAPSULE};
    let d = context_digest(b"nonos capsule context, fixture").expect("a short context");
    let hex: String = d.iter().map(|b| format!("{b:02x}")).collect();
    assert_eq!(
        hex,
        "6fc7bcf4f4b46314afe0d2e71f58776d0dfdcdf9fc4c96dad1a91a8ba23b61c6"
    );

    let w = words(
        [1, 2, 3, 4],
        b"nonos capsule context, fixture",
        KIND_CAPSULE,
    )
    .expect("words");
    assert_eq!(&w[4..8], &digest_words(&d));
    assert_eq!(w[8], KIND_CAPSULE);
    assert!(
        words([1, 2, 3, 4], b"x", 2).is_none(),
        "padding is never proven"
    );
    assert!(
        words([P, 2, 3, 4], b"x", KIND_CAPSULE).is_none(),
        "a root word not below p"
    );
    let high = [0xffu8; 32];
    assert!(digest_words(&high).iter().all(|&v| v < P));
}

/// The pinned slots' digest words are their statements' digests, read the
/// gate's way.
#[test]
fn the_pinned_slots_carry_their_digests_words() {
    use nox_verify::attest::digest_words;
    for (name, _, words) in pinned("attest", "proof.bin") {
        let st = std::fs::read_to_string(format!("{name}/statement.json")).expect("statement");
        let at = st.find("\"digest\": \"").expect("digest") + 11;
        let hex = &st[at..at + 64];
        let d: [u8; 32] =
            core::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("hex"));
        assert_eq!(&words[4..8], &digest_words(&d), "{name}");
    }
}

/// Every quoted decimal in a file, in order.
fn quoted_words(text: &str) -> Vec<u64> {
    text.split('"')
        .skip(1)
        .step_by(2)
        .filter(|t| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit()))
        .map(|t| t.parse().expect("a word"))
        .collect()
}

/// The published leaf set refolds to the root every attestation proof was
/// made under, and each pinned slot's leaf is its kind and digest's.
#[test]
fn the_published_tree_refolds_to_the_proofs_root() {
    use nox_verify::attest::{fold_path, fold_tree, leaf};
    let tree = std::fs::read_to_string(format!("{SPEC}/attest/tree.json")).expect("tree.json");
    let w = quoted_words(&tree);
    assert_eq!(w.len(), 4 + 256 * 4);
    let root = [w[0], w[1], w[2], w[3]];
    let leaves: Vec<[u64; 4]> = w[4..]
        .chunks_exact(4)
        .map(|c| [c[0], c[1], c[2], c[3]])
        .collect();
    assert_eq!(fold_tree(&leaves), Some(root));
    assert_eq!(fold_tree(&leaves[..255]), None, "not a complete tree");

    for (name, _, words) in pinned("attest", "proof.bin") {
        assert_eq!(&words[..4], &root, "{name}");
        let st = std::fs::read_to_string(format!("{name}/statement.json")).expect("statement");
        let field = |k: &str| {
            let at = st.find(&format!("\"{k}\": ")).expect("field") + k.len() + 4;
            st[at..]
                .split(|c: char| c == ',' || c == '\n')
                .next()
                .expect("value")
                .trim()
                .trim_matches('"')
                .to_string()
        };
        let hex = field("digest");
        let d: [u8; 32] =
            core::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("hex"));
        let kind: u64 = field("kind").parse().expect("kind");
        let slot: usize = field("slot").parse().expect("slot");
        let l = leaf(kind, &d);
        assert_eq!(l, leaves[slot], "{name}");

        let (mut sibs, mut right, mut level, mut i) =
            (Vec::new(), Vec::new(), leaves.clone(), slot);
        while level.len() > 1 {
            sibs.push(level[i ^ 1]);
            right.push(i & 1 == 1);
            let up: Vec<[u64; 4]> = level
                .chunks_exact(2)
                .map(|p| fold_tree(p).expect("a pair"))
                .collect();
            level = up;
            i >>= 1;
        }
        assert_eq!(fold_path(l, &sibs, &right), Some(root), "{name}");
    }
}
