# 15. Drawing challenges

How a challenge is drawn from the Keccak transcript, exactly enough that a verifier matches the
prover draw for draw.

## Why not reduce

Reducing a 64-bit word mod p is not uniform: values below `2^64 - p = 2^32 - 1` have two
preimages, so a coordinate lands on one of them with probability up to `2 / 2^64` where a uniform
draw gives `1 / p`. In the worst case over where a round's bad challenges lie, that costs up to 2
bits per F_p² challenge round (`Shield.Sampling`). The rule below removes the bias instead of
paying for it.

## The rule

Every challenge is drawn exactly uniformly. The rule, for a stream of challenges under one tag:

1. **Squeeze.** `state = keccak256(tag || state)`. The 32 bytes give four lanes,
   `lane_j = state[8j .. 8j + 8]` read little-endian, `j = 0, 1, 2, 3`, taken in that order.
2. **Accept or refuse.** A lane `w` is accepted as the field element `w` if `w < p`, where
   `p = 0xFFFFFFFF00000001`. It is refused otherwise, and the next lane is taken.
3. **Refill.** When all four lanes of a squeeze are used, squeeze again under the same tag.
4. **F_p².** A challenge in F_p² is two accepted lanes, `c0` then `c1`.
5. **Discard.** Lanes left over when a stream ends are dropped. The next stream starts with a fresh
   squeeze under its own tag.

Accepted lanes are uniform on F_p and independent: a refusal happens with probability
`(2^32 - 1) / 2^64 < 2^-32` (`Shield.Sampling.refusal_below_2_32`).

**The DEEP coefficients.**
- **The grind.** After the frame and the periodic claims are absorbed, the prover grinds 19 bits
  under the proof-of-work rule of the query grind, and the nonce is absorbed.
- **The stream.** The coefficients are then drawn as one stream under tag `0x09`: one independent
  F_p² value per DEEP term, in coefficient order (window row, then column, then the composition
  term, then the periodic claims).
- **The cost.** Two accepted lanes per term, four lanes per squeeze; a refused lane is rare enough
  that a stream almost never needs an extra squeeze.

**Every other challenge** (the composition's alpha, `z`, the permutation's beta and gamma,
the fold challenges) is a stream of one or two elements under its current tag, by the same rule.

## Why exact, and not wider

A 128-bit word reduced mod p is also close to uniform, within `2^-64`. But it would take two
lanes per element where refusal takes one, and it only nearly removes the bias. Refusal is
exact, costs one comparison, and almost never takes more than one squeeze per four elements.
