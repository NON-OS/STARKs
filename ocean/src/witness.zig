// NONOS Operating System (AGPL-3.0-or-later)
//! The witness this client hands the prover.
//!
//! The intent vector checks the half of the client-prover seam that needs no
//! prover, which is that the two languages agree on what a transfer is. This is the other half: the private side
//! crossing the boundary, so a proof is made from a witness a wallet produced
//! rather than from a fixture the prover built for itself.
//!
//! The format is `stark_proofs/src/shield/witness_wire.rs` and is flat
//! little-endian `u64` with no tags and no length prefixes. The depth is the
//! second word and every count follows from it, so this writes it with a loop
//! and the reader knows the exact length before it allocates.
//!
//! Nothing derivable is written. No commitments, no nullifiers, nothing the
//! openings already determine: a witness that carried those could disagree with
//! itself. The two roots are the exception, because they are the statement the
//! pool published rather than something this computes.

const std = @import("std");
const digest = @import("digest.zig");
const field = @import("field.zig");
const note = @import("note.zig");
const spend = @import("spend.zig");
const tree = @import("tree.zig");
const Digest = digest.Digest;
const Fp = field.Fp;
const Note = note.Note;

/// ASCII `NOXWIT02`, so a file that is not this is refused before it is read as
/// this. Must equal `witness_wire::MAGIC`. 02 added the fee recipient's limbs;
/// a 01 file is refused by name rather than read short.
pub const MAGIC: u64 = 0x4E4F5857_49543032;

/// Words a note occupies: value, asset, four of key, four of blinding.
const NOTE_WORDS = 10;

/// Magic, depth, two secrets, four notes, four scalars, the recipient's and
/// the fee recipient's limbs.
const HEAD_WORDS = 2 + 2 * 4 + 4 * NOTE_WORDS + 4 + 4 + 4;

pub const Error = error{Overflow};

/// The exact length of a witness at this depth. A caller sizes its buffer from
/// the depth alone, before it writes a word.
pub fn wordsAt(depth: usize) usize {
    return HEAD_WORDS + 4 * (1 + depth * 4) + 2 * 4;
}

fn putDigest(w: []u64, at: *usize, d: *const Digest) void {
    for (d) |v| {
        w[at.*] = v;
        at.* += 1;
    }
}

fn putNote(w: []u64, at: *usize, n: *const Note) void {
    w[at.*] = n.value;
    w[at.* + 1] = n.asset_id;
    at.* += 2;
    putDigest(w, at, &n.spend_pk);
    putDigest(w, at, &n.blinding);
}

fn putOpening(w: []u64, at: *usize, o: *const tree.Witness) void {
    w[at.*] = o.leaf_index;
    at.* += 1;
    for (&o.siblings) |*s| putDigest(w, at, s);
}

/// A dummy's opening: position zero and a path of zeros.
///
/// Not a placeholder the prover has to know about. The circuit multiplies each
/// input's membership by a live bit that is the value's own inverse, so a note
/// worth nothing has its walk multiplied by zero and reaches wherever its
/// siblings take it. A zero path is as good as any other and the format needs no
/// flag: the value already says which input this is.
///
/// This is what lets a wallet holding one note pay, which is the common case for
/// a small wallet and was the case this format refused to write.
fn putDummyOpening(w: []u64, at: *usize) void {
    w[at.*] = 0;
    at.* += 1;
    for (0..tree.DEPTH * 4) |_| {
        w[at.*] = 0;
        at.* += 1;
    }
}

/// Write `sp` and its two secrets into `out`, which must be `wordsAt(DEPTH)`
/// long. Returns the number of words written, which is that length.
///
/// A dummy input is written with a zero opening. The circuit gates each input's
/// membership on a live bit it derives from the value, so a dummy's walk binds
/// nothing and the path it carries is never compared to a root.
pub fn write(out: []u64, sp: *const spend.Spend, secrets: *const [2]Digest) Error!usize {
    const need = wordsAt(tree.DEPTH);
    if (out.len < need) return error.Overflow;

    var at: usize = 0;
    out[at] = MAGIC;
    out[at + 1] = tree.DEPTH;
    at += 2;

    for (secrets) |*sk| putDigest(out, &at, sk);
    for (&sp.inputs) |*in| putNote(out, &at, in.noteOf());
    for (&sp.outputs) |*o| putNote(out, &at, o);

    for (&sp.inputs) |*in| switch (in.*) {
        .real => |*r| putOpening(out, &at, &r.pool),
        .dummy => putDummyOpening(out, &at),
    };
    putDigest(out, &at, &sp.note_root);
    for (&sp.inputs) |*in| switch (in.*) {
        .real => |*r| putOpening(out, &at, &r.assoc),
        .dummy => putDummyOpening(out, &at),
    };
    putDigest(out, &at, &sp.assoc_root);

    out[at] = sp.public_amount;
    out[at + 1] = sp.fee;
    out[at + 2] = sp.asset_id;
    out[at + 3] = sp.clearing_price;
    at += 4;

    const limbs = spend.addressLimbs(&sp.recipient);
    putDigest(out, &at, &limbs);
    const fee_limbs = spend.addressLimbs(&sp.fee_recipient);
    putDigest(out, &at, &fee_limbs);

    std.debug.assert(at == need);
    return at;
}

/// Every field a reader takes, in the order it takes them, so a disagreement
/// about the layout is a disagreement about one of these offsets rather than a
/// proof that will not parse.
pub const Offsets = struct {
    pub const magic = 0;
    /// Where the depth is written, not the depth itself. The two are different
    /// quantities and Zig refuses to let them share a spelling, which is the
    /// right call: every function below takes the value as a parameter.
    pub const depth_word = 1;
    pub const secrets = 2;
    pub const inputs = secrets + 2 * 4;
    pub const outputs = inputs + 2 * NOTE_WORDS;
    pub const pool = outputs + 2 * NOTE_WORDS;

    /// The openings are depth-sized, so everything past them is a function of
    /// the depth and is given as a call rather than a constant.
    pub fn noteRoot(depth: usize) usize {
        return pool + 2 * (1 + depth * 4);
    }

    pub fn assoc(depth: usize) usize {
        return noteRoot(depth) + 4;
    }

    pub fn assocRoot(depth: usize) usize {
        return assoc(depth) + 2 * (1 + depth * 4);
    }

    pub fn scalars(depth: usize) usize {
        return assocRoot(depth) + 4;
    }

    pub fn recipient(depth: usize) usize {
        return scalars(depth) + 4;
    }

    pub fn feeRecipient(depth: usize) usize {
        return recipient(depth) + 4;
    }
};
