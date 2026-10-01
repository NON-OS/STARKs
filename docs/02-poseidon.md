# 02. Poseidon

The circuits commit to notes, keys, trees and the inner proof's transcript with one algebraic
permutation over $`\mathbb{F}_p`$. This document defines the permutation, the three functions
built from it (the single-block hash, the two-to-one compression and the domain tag), the AIR
that proves a preimage, and the security margin of the chosen round count against the bounds
of the Poseidon paper [5]. It is for implementers of a second Poseidon (the Solidity contract
is one) and for reviewers of the hash's parameters.

Code references are to `nonos-stark/src/air/poseidon.rs` unless another path is given.

## 1. Parameters

| symbol | value | code |
|---|---|---|
| state width $t$ | 8 | `WIDTH` (line 29) |
| rate $r$ | 4 | `RATE` (line 31) |
| capacity $c$ | 4 elements, 256 bits | $t - r$ |
| S-box | $x \mapsto x^7$ | `sbox7` |
| rounds $R$ | 32, every round full, no partial rounds | `Poseidon::new(5, _)`, $R = 2^5$ |
| linear layer | Cauchy matrix $M$ | `cauchy_mds` |
| round constants | BLAKE3 of a domain string, round and lane | `round_constants` |

The settlement circuits use $\log R = 5$: `POOL_LOG_ROUNDS = 5`
(`stark_proofs/src/shield/note/limbs.rs:7`) and `LOG_ROUNDS = 5`
(`stark_proofs/src/recursion_assembly/inner/params.rs`). The contract
`PoseidonGoldilocks.sol` fixes `FULL_ROUNDS = 32` and `HASH_ROUNDS = 31` and checks known
answers in its constructor, so a wrong constant or a wrong round function fails deployment.

## 2. The S-box

**Proposition 2.1.** $x \mapsto x^7$ is a permutation of $`\mathbb{F}_p`$, and 7 is the smallest
exponent $\alpha \ge 3$ with this property.

*Proof.* A power map $x \mapsto x^\alpha$ permutes $`\mathbb{F}_p`$ if and only if
$\gcd(\alpha, p - 1) = 1$. By the factorisation of $p - 1$ in
[01-field.md](01-field.md), Proposition 3.1, $\gcd(3, p-1) = 3$, $\gcd(5, p - 1) = 5$,
$\gcd(4, p-1) = \gcd(6, p-1) > 1$ because $p - 1$ is even, and $\gcd(7, p - 1) = 1$ because
$7 \nmid p - 1$. $\square$

The Poseidon paper takes $\alpha$ as the smallest integer $\alpha \ge 3$ with
$\gcd(\alpha, p-1) = 1$ [5, §1], which is 7 here.

## 3. The linear layer

**Definition 3.1.** $`M \in \mathbb{F}_p^{8 \times 8}`$ with

```math
M_{ij} = \frac{1}{x_i - y_j}, \qquad x_i = i,\ \ y_j = 8 + j, \qquad 0 \le i, j < 8
```

(`cauchy_mds`, line 278).

**Proposition 3.2.** $M$ is maximum distance separable: every square submatrix is invertible.

*Proof.* The node sets $`\{0, \dots, 7\}`$ and $`\{8, \dots, 15\}`$ are disjoint, and all sixteen
values are distinct modulo $p$. A square submatrix on rows $I$ and columns $J$ is again a Cauchy
matrix, with determinant

```math
\det M_{I,J} = \frac{\prod_{i < i'} (x_{i'} - x_i) \prod_{j < j'} (y_j - y_{j'})}{\prod_{i, j} (x_i - y_j)}
```

(the Cauchy determinant [18]). Every factor is a difference of distinct field elements, so the
determinant is nonzero. A matrix all of whose square submatrices are invertible has branch
number $t + 1 = 9$ [18]. $\square$

## 4. The round function and the permutation

**Definition 4.1.** For round $`r \in \{0, \dots, R-1\}`$ with constants $`c_r \in \mathbb{F}_p^8`$,

```math
\mathrm{round}_r(x) = M \cdot S(x) + c_r, \qquad S(x)_j = x_j^7
```

(`round`, line 62). The permutation is
$`\pi = \mathrm{round}_{R-1} \circ \dots \circ \mathrm{round}_0`$ (`permute`, line 121).

Each round applies the S-box to all eight lanes, then the matrix, then the constants. The
Poseidon specification adds the constants before the S-box [5, §2.3]. The two orders differ by
the constant layer at each end of the permutation: the first S-box acts on the input directly,
and the last round ends with a constant addition. An affine layer at either end of a permutation
is known to every party and does not change the attacks of Section 7.

**Definition 4.2 (round constants).** For round $r$ and lane $j$,

```math
c_{r,j} = \mathrm{le64}\big(\mathrm{BLAKE3}(\texttt{"NONOS-POSEIDON-GOLDILOCKS-RC"} \,\|\, \mathrm{le64}(r) \,\|\, \mathrm{le64}(j))[0..8]\big) \bmod p
```

(`round_constants`, line 292, with the domain string `RC_DOMAIN` of line 41). The rule has no
free parameter beyond the domain string. The Poseidon paper derives its constants from a Grain
LFSR [5, App. E], and this instance does not.

## 5. Functions built on the permutation

Let $`\mathrm{rate}(x) = (x_0, x_1, x_2, x_3)`$ for a state $`x \in \mathbb{F}_p^8`$.

**Compression.** For $`\ell, r \in \mathbb{F}_p^4`$,

```math
\mathrm{compress}(\ell, r) = \mathrm{rate}\big(\pi(\ell \,\|\, r)\big)
```

(`compress`, line 132). This is the node hash of every Poseidon Merkle tree, the note
commitment's building block and the key derivation. It uses all 32 rounds.

**Single-block hash.** For $`m \in \mathbb{F}_p^4`$,

```math
\mathrm{hash}(m) = \mathrm{rate}\big(\mathrm{round}_{R-2} \circ \dots \circ \mathrm{round}_0\,(m \,\|\, 0^4)\big)
```

(`hash`, line 80). It runs $R - 1 = 31$ rounds so that the preimage AIR of Section 6, a trace
of $2^5 = 32$ rows, holds the input in row 0 and the digest in row 31. The capacity starts at
zero, which is the sponge's domain separation. The contract's `HASH_ROUNDS = 31` is the same
count.

**Domain tag.** For a 64-bit value $v$, $\mathrm{tag}(v) = (v, 0, 0, 0)$
(`stark_proofs/src/shield/key/domain.rs:23`). A tag fills the second operand of a compression,
so outputs of compressions with different tags come from different preimages.

| tag | value | ASCII | use |
|---|---|---|---|
| `SPEND_DOMAIN` | `0x5350_4E44` | SPND | spend key |
| `NULL_DOMAIN` | `0x4E55_4C4C` | NULL | nullifier key |
| `NOTE_DOMAIN` | `0x4E4F_5445` | NOTE | note commitment |
| `DEAD_DOMAIN` | `0x4445_4144` | DEAD | a dummy input's nullifier position |
| `IMT_LEAF_DOMAIN` | `0x494D_544C` | IMTL | indexed-tree leaf |

[03-keys-notes-nullifiers.md](03-keys-notes-nullifiers.md) uses these.

## 6. The preimage AIR

`Poseidon` also implements `Air` (line 230). The trace has $t = 8$ columns and $2^5$ rows, one
state per row, and the round constants ride in eight periodic columns, one per lane
(`periodic_columns`, line 251).

**Transition.** For the window $(x, x')$ of two consecutive rows and the periodic values $c$ of
the first,

```math
C_j(x, x', c) = x'_j - \Big(\sum_{k} M_{jk}\, x_k^7 + c_j\Big), \qquad 0 \le j < 8
```

(`transition_impl`, line 210). The constraint degree is 7 (line 243).

**Boundary.** The capacity lanes $4..7$ of row 0 are zero, and the rate lanes $0..3$ of the last
row equal the public digest (`boundary`, line 260).

**Split form.** `round_split_generic` (line 177) takes the squares $x^2$ and $x^4$ as witness
cells and returns the round with the S-box as $x^4 \cdot x^2 \cdot x$, plus the two constraints
$x^2 - x \cdot x$ and $x^4 - x^2 \cdot x^2$. Every constraint then has degree three. The
transcript regions (`transcript_check.rs`) and the membership regions
(`multi_membership/rules.rs`) of the recursion use this form (see 05-air.md).

All forms share `mds_rc` (line 195), so the native hash, the AIR and the recursion's regions
compute one function.

## 7. Security margin

The permutation targets $M = 128$ bits of security, set by the capacity: a sponge with
capacity $c = 256$ bits is indifferentiable from a random oracle up to $2^{c/2} = 2^{128}$ calls to the permutation, and the paper claims $2^M$ security against collisions and preimages [5, §5, §5.2]. The
attacks below are the ones the Poseidon paper uses to set round numbers. With $t = 8$,
$\alpha = 7$, $`\log_2 p \approx 64`$ and $M = 128$:

**Statistical attacks.** Differential and linear attacks can apply when
$`R_F < 6`$ for $`M \le (\lfloor \log_2 p \rfloor - C)(t + 1)`$, and when $`R_F < 10`$ otherwise,
where $`C = \log_2(\alpha - 1)`$ [5, §5.5.1, eq. (2)]. Here $`C = \log_2 6 \approx 2.58`$ and
$(63 - 2.58) \cdot 9 \approx 544 \ge 128$, so the threshold is 6 full rounds.

**Interpolation.** An $R$-round permutation can be attacked when

```math
R \le \lceil \log_\alpha(2) \cdot \min\{M, \log_2 p\} \rceil + \lceil \log_\alpha t \rceil
```

[5, §5.5.2, eq. (3)]. Here $`\lceil 64 / \log_2 7 \rceil + \lceil \log_7 8 \rceil = 23 + 2 = 25`$.

**Gröbner bases.** An attack faster than $2^M$ exists if any of

```math
R_F + R_P \le \log_\alpha(2)\min\{M, \log_2 p\}, \quad
R_F + R_P \le t - 1 + \log_\alpha(2)\min\Big\{\tfrac{M}{t+1}, \tfrac{\log_2 p}{2}\Big\}, \quad
(t - 1) R_F + R_P \le t - 2 + \frac{M}{2 \log_2 \alpha}
```

holds [5, §5.5.2, eq. (4)]. With $`R_P = 0`$ the three right-hand sides are $22.8$, $12.1$ and,
for the third, $`R_F \le 4.1`$.

| attack | largest round count it reaches | rounds here |
|---|---:|---:|
| statistical | 5 full rounds | 32 |
| interpolation | 25 | 32 |
| Gröbner, first bound | 22 | 32 |

The paper adds two full rounds and 7.5 percent of the partial rounds as a security margin
[5, §5.4]. The largest bound above plus two full rounds is 27, below 32.

**Open item 7.1.** This instance is not one of the published Poseidon instances. It differs in
four ways: all rounds are full, the constants come from BLAKE3 and not the Grain LFSR, the
linear layer is the Cauchy matrix of Section 3, and the constants follow the matrix. The bounds
above are the published round-number bounds evaluated at these parameters. No third-party
cryptanalysis of this instance exists.

## 8. Known answers

`the_permutation_vector` in `poseidon.rs` (line 322) prints $\pi(1, 2, \dots, 8)$, the hash of
$(1, 2, 3, 4)$, $`c_{0,0}`$ and $`M_{00}`$, and pins them in its assertion. The contract checks its
own known answers at construction. A second implementation reproduces these values before it
computes anything else.
