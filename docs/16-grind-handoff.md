# 16. The query grind and its optional helper

The query grind sits between the prover's last commitment and its query openings: the positions
are drawn from its nonces, and only the prover can open its own trees. A helper that grinds for the
prover therefore works in the middle of a proof. This page fixes what crosses between them, so any
relayer or open-market worker can offer it and no prover has to depend on one.

## The shapes

A verifier accepts a fixed set of parameter identities and nothing else. They differ only in
the query count and the query grind; everything before the grind is identical.

| shape | id byte | queries | grind | chunks x bits | query-phase bits | who grinds |
|---|---|---|---|---|---|---|
| A | `0x01` | 19 | 28 | 8 x 25 | 80.8 | the prover |
| A' | `0x02` | 18 | 31 | 8 x 28 | 81.0 | the prover, if its GPU is fast enough |
| B | `0x03` | 17 | 33 | 8 x 30 | 80.2 | a helper, optionally |

Every other round is the same in all three (docs/12 Section 1), so the declared minimum of each
shape is the smaller of its query phase and 80.1.

## Choosing late, and binding the choice

The prover proves once, up to and including the final layer, and chooses the shape only then:
- if a helper answers in time, shape B;
- otherwise shape A or A', ground on the device.

The choice is bound before any grind starts: the prover absorbs one byte, the shape's id, under
tag `0x0A` (`state = keccak256(0x0A || state || id)`), which no other operation uses. The query
grind and the query draw then run on that state.

**Why late choice is sound.**
- A grind attempt is made against a state that already names its shape, so its work counts for
  that shape alone.
- An attacker attempting shape s pays `2^g_s` hashes an attempt and succeeds with probability at
  most `ε_s` for the query round. The best it can do is attempt the weakest shape every time, so
  the query round is worth the minimum over the accepted shapes: 80.2 bits, shape B.
- Without the binding byte, one grind could be read under two shapes. With it, it cannot.

## The hand-off

**Prover to helper: 33 bytes.** The shape id and the 32-byte transcript state, taken after the id
is absorbed. Nothing else: no commitment, no public word, no proof byte.

**Helper to prover: 64 bytes.** Eight nonces, little-endian `u64`, in search order. Each is the
smallest nonce meeting the chunk's bits:

```text
S_0 = the state received
for i in 0..8:
    n_i = the smallest n with leading_zeros(keccak256(0x05 || S_i || n as u64 le)[0..8] as u64 le) >= bits
    S_{i+1} = keccak256(0x05 || S_i || n_i as u64 le)
return n_0 .. n_7
```

**The prover checks before using them.** It recomputes each word, eight Keccaks, and the
smallest-nonce rule is not required of the helper: any nonce meeting the bits verifies. If a
nonce fails, or no answer arrives in time, the prover grinds shape A itself. It has not lost its
proof: it absorbs A's id in place of B's and continues from the same final layer.

## What the helper learns

The helper sees one 32-byte hash of the transcript. It is a function of commitments the final
proof publishes anyway, and it reveals nothing about the witness (docs/12-zero-knowledge.md 4.5).
It cannot link the request to a sender beyond what the network hop already shows. It cannot steer
the proof to a worse zero-knowledge case: a steered draw into the collision class is refused by
the prover's rank check like any other, and the prover proves again.

## Known answers

`grind_kat_test` pins eight 12-bit chunks from `keccak256("nox grind kat")`. A helper
implementation, CUDA, Metal or CPU, must reproduce those nonces
and that final state before it serves a real request.
