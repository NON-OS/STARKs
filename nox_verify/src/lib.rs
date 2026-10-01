// NONOS Operating System (AGPL-3.0-or-later)
//! Verify a format 7 proof against a pinned circuit, with `no_std` and an
//! allocator and nothing else.
//!
//! The circuit is not rebuilt here. It is read from its program image, the
//! constraint tape and boundary list the on-chain evaluator is compiled from,
//! and the engine's verifier runs over that. A gate therefore pins three
//! things and trusts nothing else: the image (by its keccak256), the parameter
//! ids it accepts, and the periodic root. The proof names its parameter id in
//! its header; the public words are the caller's to compute.
//!
//! What this crate does not do is decide what the public words are. A boot or
//! spawn gate computes them from the bytes it is about to run and passes them
//! in; a proof that carries its own claim of them is a proof about something
//! else.
#![no_std]

extern crate alloc;

/// The engine at the path the format 7 reader was written against.
mod crypto {
    pub use nonos_stark as stark;
}

#[allow(dead_code, unused_imports)]
#[path = "../../stark_proofs/src/proof_wire/mod.rs"]
mod proof_wire;

pub mod attest;
mod program;
pub mod statements;

pub use program::{Program, Shape};

use crypto::stark::air::stark_verify_ext_rounds_shared_why;
use crypto::stark::field::{Fp, P};
use program::ProgramAir;
use proof_wire::{deserialize_rounds_shared, read_header, ParamSet, FORMAT_7, HEADER_BYTES};

/// One accepted query shape: a parameter id and the point it names.
#[derive(Clone, Copy)]
pub struct Point {
    pub params: [u8; 32],
    pub queries: usize,
    pub grind_bits: u32,
}

/// Everything a gate pins about one statement.
pub struct Statement {
    /// The program image, checked against `program_hash` before it is parsed.
    pub program: &'static [u8],
    pub program_hash: [u8; 32],
    pub periodic_root: [u8; 32],
    pub shape: Shape,
    pub extra_blowup_bits: u32,
    pub points: &'static [Point],
    /// The statement's public word count.
    pub words: usize,
    /// The longest proof any accepted point produces, refused above before
    /// anything is read.
    pub max_proof_bytes: usize,
}

/// Why a proof was refused. Stable: a gate may log it, and nothing about the
/// proof beyond it is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// The pinned image does not hash to its pin, or does not parse.
    Image,
    /// Longer than the statement allows, or shorter than a header.
    Length,
    /// Not format 7 of this protocol, or a parameter id the statement does not accept.
    Header,
    /// The public words are not the statement's count, or one is not below p.
    Publics,
    /// The statement's numbers and its image disagree with the proof's parameter id.
    Shape,
    /// The bytes after the header do not parse as the point's proof.
    Encoding,
    /// The proof does not verify.
    Proof,
}

impl Refusal {
    /// What the refusal means, for a log.
    pub const fn reason(self) -> &'static str {
        match self {
            Refusal::Image => "the pinned image does not hash to its pin or does not parse",
            Refusal::Length => "the proof's length is out of bounds",
            Refusal::Header => "not a format 7 proof at an accepted parameter id",
            Refusal::Publics => "the public words are not the statement's",
            Refusal::Shape => "the statement's shape does not match the proof's parameter id",
            Refusal::Encoding => "the proof does not parse at its point",
            Refusal::Proof => "the proof does not verify",
        }
    }

    /// A stable number per refusal, for a gate's log.
    pub const fn code(self) -> u32 {
        match self {
            Refusal::Image => 1,
            Refusal::Length => 2,
            Refusal::Header => 3,
            Refusal::Publics => 4,
            Refusal::Shape => 5,
            Refusal::Encoding => 6,
            Refusal::Proof => 7,
        }
    }
}

/// Verify `proof` against `statement` and the caller's public words.
pub fn verify(statement: &Statement, proof: &[u8], publics: &[u64]) -> Result<(), Refusal> {
    verify_why(statement, proof, publics).map_err(|(r, _)| r)
}

/// `verify`, with the check that refused named: the engine's reason for a
/// proof that does not verify, a fixed one for every other refusal. For a log;
/// nothing in it depends on secret data.
pub fn verify_why(
    statement: &Statement,
    proof: &[u8],
    publics: &[u64],
) -> Result<(), (Refusal, &'static str)> {
    check(statement, proof, publics)
}

fn check(
    statement: &Statement,
    proof: &[u8],
    publics: &[u64],
) -> Result<(), (Refusal, &'static str)> {
    let fail = |r: Refusal| move || (r, r.reason());
    if crypto::stark::hash::keccak256(statement.program) != statement.program_hash {
        return Err(fail(Refusal::Image)());
    }
    if proof.len() < HEADER_BYTES || proof.len() > statement.max_proof_bytes {
        return Err(fail(Refusal::Length)());
    }
    let header = read_header(proof).ok_or_else(fail(Refusal::Header))?;
    if header.format != FORMAT_7 || header.protocol != proof_wire::PROTOCOL_VERSION {
        return Err(fail(Refusal::Header)());
    }
    let point = statement
        .points
        .iter()
        .find(|p| p.params == header.params)
        .ok_or_else(fail(Refusal::Header))?;
    if publics.len() != statement.words || publics.iter().any(|&w| w >= P) {
        return Err(fail(Refusal::Publics)());
    }
    let words: alloc::vec::Vec<Fp> = publics.iter().map(|&w| Fp::from_u64(w)).collect();

    let program =
        Program::parse(statement.program, statement.shape.window).ok_or_else(fail(Refusal::Image))?;
    if program.public_words() > statement.words {
        return Err(fail(Refusal::Image)());
    }
    let air = ProgramAir::new(&program, statement.shape, &words).ok_or_else(fail(Refusal::Shape))?;

    /*
     * The id the proof names is recomputed from the image and the pinned
     * numbers. Equal ids mean the reader below sizes every section from the
     * circuit the proof was made for; a statement whose numbers drifted from
     * its image refuses here rather than reading the proof under the wrong
     * layout.
     */
    let params = ParamSet::of(&air, point.queries, point.grind_bits, statement.extra_blowup_bits);
    if params.id() != point.params {
        return Err(fail(Refusal::Shape)());
    }
    let (skeleton, streams) =
        deserialize_rounds_shared(proof, &params).ok_or_else(fail(Refusal::Encoding))?;
    stark_verify_ext_rounds_shared_why(
        air,
        &skeleton,
        &streams,
        point.queries,
        point.grind_bits,
        statement.extra_blowup_bits,
        &statement.periodic_root,
        &words,
    )
    .map_err(|why| (Refusal::Proof, why))
}
