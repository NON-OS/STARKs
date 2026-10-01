# 17. The transcript

The order of every absorb, draw and grind in a format 7 proof, and the wire it travels on. A
verifier that follows this page draws what the prover drew. It is the `fri8` build: exact draws,
vector absorbs, a grind and independent coefficients for the DEEP round, a grind before each FRI
fold, the query shape, radix 8, 32-byte digests and the periodic overlay.

## Tags

| tag | operation |
|---|---|
| `0x01` | absorb a digest, 32 bytes |
| `0x02` | absorb a vector of field elements |
| `0x03` | base-field challenge, from an exact stream (docs/15) |
| `0x04` | query index, masked to a power of two |
| `0x05` | proof-of-work nonce |
| `0x06` | F_p² challenge: one exact stream, c0 then c1 |
| `0x08` | the FRI seed |
| `0x09` | the DEEP coefficient stream |
| `0x0A` | the query shape |

A **stream** (docs/15) squeezes `state = keccak256(tag || state)`. It reads four little-endian lanes
in order, accepts a lane below p and refuses one at or above it, and squeezes again when the lanes
run out. Lanes left at the end are dropped. An F_p² challenge is one stream of two accepted lanes,
c0 then c1.

A **vector absorb** is `state = keccak256(0x02 || state || v_0 || v_1 || ...)`, each element as
8 little-endian bytes and an F_p² element as c0 then c1: one Keccak over the whole vector. Every
vector has a length the parameters fix, so nothing about its length needs absorbing.

## Order

1. `NONOS-STARK-EXT` label; absorb the public words (vector).
2. Absorb the region (trace) root.
3. Draw β, γ (F_p², stream `0x06` each); absorb the permutation root.
4. Draw α (F_p², stream `0x06`); the composition coefficients are its powers, an algebraic batch
   (docs/12 Section 2.4). Absorb the composition root.
5. Draw z (F_p², stream `0x06`).
6. Absorb the out-of-domain frame (vector: two window rows of every column).
7. Absorb the periodic claims at z (vector, one per periodic column).
8. **DEEP grind**: 19 bits, one nonce; absorb it (`0x05`).
9. **DEEP coefficients**: stream `0x09`, independent F_p² values, one per DEEP term (the frame, the
   composition, then the periodic claims). Then the **mask pair**: in each window row, column b's
   coefficient is set to X times column a's (X² = 7), and b's drawn value is dropped. The batch
   stays an affine space, because the relation is linear, so its error is one line's (docs/12
   Section 1).
10. The FRI seed: squeeze `0x08`.
11. FRI, on a `NONOS-STARK-FRI-EXT` transcript seeded by it. For each layer (radix 8):
    - absorb the layer root;
    - a 21-bit commit grind, nonce absorbed;
    - draw the fold challenge β_m (F_p², stream `0x06`).
12. Absorb the final layer (vector of F_p² coefficients).
13. **Shape**: absorb the shape id byte under `0x0A` (docs/16).
14. The query grind: 8 chained nonces, each at `g - 3` bits for the shape's grind `g`.
15. The query positions: `0x04`, one per query.

## Wire: format 7

After the 40-byte header (`NOXP`, format `7`, protocol `1`, the parameter identity):
- the roots in transcript order;
- the frame and the periodic claims at z, then **one u64, the DEEP nonce**;
- the FRI layer roots, each with its commit nonce, and the final layer;
- the 8 query nonces;
- the queried rows' openings, each FRI query layer carrying `FOLD = 8` F_p² values;
- one shared set of Merkle paths for every queried position (docs/14), with 32-byte digests.

The shape byte is not on the wire. The parameter identity already names the shape, since it hashes
the query count and grind, and the verifier maps each accepted identity to its shape id.

## Parameter identity

`keccak256` of a preimage under the domain tag `NOX_PARAMS_V1`: the query count, grind bits, extra
blowup bits, fold, the trace and region widths, the window, the degree, the periodic count, the mask
columns, the challenge lanes, the commit grind and the grind chunk count. Then four more fields:
- the transcript version `2`;
- the DEEP grind bits `19`;
- the draw rule `1`, exact;
- the shape id.

Each is a u32, four little-endian bytes. Two different shapes, or the same circuit at two points,
never share an identity, and a verifier that accepts one identity refuses every other before it
reads the proof (`ParamSet::preimage`, `ParamSet::id`).

## Choices this page settles

- **Big-endian limbs: no.** The execution they save does not set the price while verification is
  bound by its calldata floor, and every encoder and Lean transcription would move.
- **Vector absorbs: yes.** One Keccak per vector in place of one per element, with no soundness
  cost in the random-oracle model, since the length is fixed.
