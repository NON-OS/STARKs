# 12. Soundness

What a verifier's acceptance proves, at the parameters the code proves at. Every figure names the
Lean theorem that decides it, and a figure that rests on a preprint or a conjecture says so.
Zero knowledge is its own file, [12-zero-knowledge.md](12-zero-knowledge.md).

## 1. The points

Every statement in this repository is proven on the deployed transcript ([17-transcript.md](17-transcript.md))
at one of these points. The rate is ρ = 2^-(1+e) for extra blowup e = 5, so ρ = 2^-6.

| point | queries q | query grind γ | conjectured | statements |
|---|---:|---:|---:|---|
| A | 19 | 28 | 142 | transfer, transfer with not-before, claim, activity (the wallet's default) |
| A′ | 18 | 31 | 139 | transfer, transfer with not-before, claim |
| B | 17 | 33 | 135 | transfer, transfer with not-before, claim |
| attestation | 26 | 28 | 184 | attestation |

The conjectured column is q · log2(1/ρ) + γ, under the FRI proximity conjecture. The provable
figures are round by round, Section 2.

Each statement's trace is sized so its FRI domain is 2^23 (degree bound 2^17 at the trace's
composition degree, blown up 2^6). The terms below that grow with the domain are computed at 2^23.

## 2. Round by round

A Fiat-Shamir STARK is measured round by round (ethSTARK documentation v1.2, Theorem 5): a
cheating prover can retry any one challenge on its own, so each round's error counts alone, and a
grind raises only the round it precedes. The provable figure is the weakest round.

The Johnson term of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf (2020, "BCIKS20") at rate 2^-6
over 2^23, with proximity parameter m = 3 and challenges in F_p², is

```math
\varepsilon_J = \frac{(m + \tfrac12)^7 \, N^2}{3 \, \rho^{3/2} \, p^2}
```

`Shield.Launch.cNum / cDen`, 61.9 bits on one line with no grind (`Shield.Launch.one_line_bare_61_9`).

| round | batch | grind before it | bits, BCIKS20 | decided by |
|---|---|---|---:|---|
| composition coefficients | an algebraic batch, the powers of α | none | about 120 | Section 3.2 |
| out-of-domain point z | a root of a polynomial below 2^17 | none | above 110 | Section 3.1 |
| DEEP coefficients | independent coefficients: an affine space, one line's error | 19 bits | 80.9 | `Shield.RoundByRound.independent_deep_grind_19` |
| each FRI fold, radix 8 | a curve of degree 7 | 21 bits | 80.1 | `Shield.RoundByRound.radix8_fold_needs_21` |
| query draw, point A | (7/48)^19 | 28 bits | 80.8 | `Shield.Launch` |

So point A is **80.8 bits on the query phase and 80.1 bits provable**, set by the fold rounds.
For A′ and B the published figure is the smaller of the query phase and 80.1 ([16-grind-handoff.md](16-grind-handoff.md)).
For the attestation the query phase is about 100 bits and the fold rounds keep it at 80.

**Under the 2025 proximity gaps.** Ben-Sasson, Carmon, Haböck, Kopparty and Saraf (November 2025,
a preprint) prove a threshold linear in the domain. Under it a single line clears 87 bits and a
radix-8 fold 84 with no grind at all (`Shield.Gaps2025.one_line`, `radix8_fold_no_grind`). The
published figures do not rest on it.

## 3. Where each term comes from

### 3.1 The out-of-domain point

z is drawn in F_p², outside the trace and evaluation domains. A false claim about a committed
polynomial at z passes only if z is a root of a nonzero polynomial of at most that polynomial's
degree, below B = 2^17. So the error is at most 2^17 / p² < 2^-110.

### 3.2 The composition batch

The composition coefficients are α^0, ..., α^(n-1) for one drawn α. A batch that hides a nonzero
constraint quotient is a nonzero polynomial of degree below n in α, so a random α is one of its
roots with probability at most n / p², far below 2^-110 for every circuit here.

### 3.3 The DEEP batch

The DEEP polynomial goes to FRI, which tests it for proximity. If any one quotient is far from low
degree, the combination is far except for coefficients in a small set. With independent
coefficients the set is one line's (BCIKS20 Theorem 1.6), ε_J. The two mask columns are combined
as one F_p² value (column b's coefficient is X times column a's); the relation is linear, so the
batch is still an affine space. A 19-bit grind before the draw lifts the round to 80.9 bits.

### 3.4 FRI

A codeword at relative distance δ from every polynomial of the bound survives one query with
probability at most 1 - δ. Inside the Johnson radius each query gives
-log2(√ρ (1 + 1/(2m))) bits, log2(48/7) = 2.78 at rate 2^-6. Each fold at radix 8 combines eight
values by a curve of degree 7, so its round errs on at most 7 ε_J of the challenges; a 21-bit grind
before each fold challenge lifts it to 80.1.

### 3.5 Grinding, and why it counts

Before the query positions are drawn, the prover finds nonces whose hashes with the transcript
state have the grind's leading zero bits. Every query position is drawn after them, so a prover
that wants different positions redoes the work: each attempt costs 2^γ hashes. γ is paid as 8
chained searches of γ - 3 bits (`fri_ext::GRIND_CHUNKS`), each against the state with the previous
nonce absorbed, so a retry still costs 2^γ, and only the prover's waiting time changes.

There is one set of query positions, drawn after the nonces and shared by FRI and the consistency
check, so the grind applies to all of it.

**Shapes and outsourced work.** A query at rate 2^-6 is worth 2.78 provable bits, so a query can be
traded for about 2.8 bits of grind. A′ and B trade one and two queries for a longer grind, which a
helper may search: the nonce is a function of public transcript state and the verifier checks it
with one hash, so who finds it changes neither soundness nor what the proof reveals
([16-grind-handoff.md](16-grind-handoff.md)). `Shield.Outsourced` decides each shape's query
phase.

### 3.6 The copy constraint

The wiring is a grand product over the wired cells. If two cells a binding says are equal are not,
the two multisets differ, and the product check passes only if (β, γ) is a root of a nonzero
polynomial of total degree at most t·k, for t rows and k wired columns. β and γ are drawn in F_p²
after the region columns are committed, so the error is at most t·k / p², below 2^-100 for every
circuit here.

### 3.7 Hash collisions

Merkle commitments keep all 32 bytes of each Keccak-256 digest. After 2^w hash evaluations a
collision is at most 2^(2w - 257) likely, 2^-97 at w = 80. Poseidon commitments in the circuit
keep four field elements, about 256 bits.

## 4. Values

The balance region is sound over the integers, not only modulo p: every value, limb, room and
carry is range-checked, and the closing constraints then force integer conservation
([03-values.md](03-values.md), and `Shield.LimbBalance` in Lean).

## 5. What is assumed

- Fiat-Shamir in the random-oracle model, with Keccak-256 for the transcript.
- The provable column rests on BCIKS20. The 2025 margins in Section 2 rest on a preprint and are
  not used in any published figure.
- The conjectured column rests on the FRI proximity conjecture.
