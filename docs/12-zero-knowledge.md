# 12. Zero-knowledge

Section 4 of the soundness argument: what a proof reveals, and why it reveals nothing else. The
numbering continues [12-soundness.md](12-soundness.md), which holds Sections 1 to 3 and the open
items.

## 4. Zero-knowledge

**Proposition 4.** For the launch point there is a simulator that, given only the public words,
outputs proofs distributed as the prover's proofs, up to:
- $\varepsilon_{\mathrm{RO}} \le Q \cdot 2^{-64}$ for an observer making $Q$ random-oracle
  queries;
- the pseudorandomness of the blinding derivation (Section 4.6);
- the rank condition (R) of Section 4.4: it fails with probability below $2^{-101.6}$, and the
  wallet's per-proof check makes it hold exactly for every proof sent.

The rest of this section proves it. Sections 4.1 to 4.5 cover every value a proof carries, 4.6
gives the simulator, and 4.7 lists the conditions with the code that meets each.

### 4.1 What a proof reveals

| | values | source |
|---|---|---|
| V1 | every committed column at the opened rows: for each of the $q$ queries, the `radix` points of its FRI leaf and each point's successor | the consistency section |
| V2 | every column at $z$ and $g z$, the out-of-domain frame, with the mask pair as one F_p² value $N = M_a + X M_b$ (Section 4.4) | the frame |
| V3 | the composition polynomial at the V1 points and at $z$ | the consistency section, the replay |
| V4 | the DEEP polynomial at the V1 points: FRI layer zero | FRI |
| V5 | FRI layers 1 to 3 at their opened points, and the final layer's 512 coefficients | FRI |
| V6 | Merkle roots, and the sibling digests on every opened path | all trees |
| V7 | the grind nonces | the nonce region |

The periodic columns and their claims at $z$ are fixed by the circuit and carry no witness.

### 4.2 The trace, product and mask columns (V1, V2)

Each committed column is $C = f + r \cdot Z_H$ with $Z_H(x) = x^t - 1$. On the trace domain
$Z_H = 0$, so the constraints see $f$.

| column | $f$ | $r$ |
|---|---|---|
| region | the witness column | degree $d$ |
| product | built from challenges drawn after the region commitment | degree $d$ |
| mask | uniform values on the trace domain, read by no constraint | degree $B - t - 1$ |

So each mask column is a uniform polynomial of degree below $B$. The counts come from
`recursion_assembly::inner::hide_at` and `air::zk::blinding_degree`.

**Count.** Per column, V1 and V2 fix at most

```math
E = \mathrm{radix} \cdot w \cdot q + 2w = 4 \cdot 2 \cdot 19 + 4 = 156
```

base-field linear functionals. V1 gives one per point. V2 gives two per point, since $z \in
\mathbb{F}_{p^2}$.

**Lemma 4.1.** Let $x_1, \dots, x_E$ be the V1 points, which lie off the trace domain, and let V2
be the evaluations at $z, gz$. If $r$ is uniform of degree $d \ge E - 1$ and the $E$ functionals
are independent on polynomials of degree $\le d$, then the V1 and V2 values of $C$ are uniform
and independent of $f$.

*Proof.* The map $r \mapsto$ (V1, V2 of $r Z_H$) is linear. $Z_H$ is nonzero at each point.
Evaluation at $E$ distinct points is surjective on polynomials of degree $\ge E - 1$, and so is
the frame's pair of extension evaluations with them, except when $z$ is a root of a nonzero
polynomial of degree at most $d + 1$: probability at most $(d + 1)/p^2$. A uniform $r$ gives
uniform values, and adding the fixed contribution of $f$ keeps them uniform. $\square$

At the launch point $d = 164 \ge 155$. A mask column has degree $B - 1 \ge 155$ outright. The
product columns satisfy the lemma conditionally on the challenges they depend on, which are
public.

`Shield.Masking` checks the masking count for every shape, not only this one; it is the count,
not the proof of Lemmas 4.1 and 4.2. The blinding
`blinding_degree` draws exceeds the count the lemma needs by nine coefficients for every query
count, window and radix. It stays under the composition bound for every query count up to 91 at
the launch shape. The mask degree covers every such count. The lemma's interpolation step is the
algebra this section proves; the Lean checks the numbers it rests on.

**Checked:** `zk_check`. It evaluates the committed polynomials exactly as the prover builds them,
at fixed points in $\mathbb{F}_p$ and $\mathbb{F}_{p^2}$, over 1,000 pairs of blinding seeds, for
all 34 region columns and both mask columns. Results:

| | value | bound |
|---|---|---|
| equal values within a pair | 0 | 0 |
| correlation | $-0.00015$ | $0.0076$ |
| uniformity, $\chi^2$ over 64 buckets | 55.9 | 119.1 |
| two different spends, largest per-column KS distance | 0.0188 | 0.0335 |

The unblinded control fails every check it should.

### 4.3 What is computed from V1 and V2 (V3, V4)

The composition $H(x)$ is a fixed function of the columns at $x$ and $g x$, the periodic values at
$x$, the public words and the drawn challenges. So its V1 values and $H(z)$ are functions of V1,
V2 and public data.

The DEEP polynomial at a layer-zero point is
$\sum_{j,k} a_{k,j} (C_j(x) - C_j(z_k))/(x - z_k)$ plus the composition and periodic terms, which
is again a function of V1, V2 and public data. A simulator that has sampled V1 and V2 computes V3
and V4 exactly as the verifier does.

### 4.4 FRI beyond layer zero (V5)

V5 is a list of linear functionals $F$ of the DEEP polynomial $D$. $F$ covers FRI layers 1 to 3
at their opened points and the final layer's 512 coefficients.

**The mask pair is one F_p² polynomial.** The two mask columns $M_a, M_b$ (columns 42 and 43) are
uniform base-field polynomials of degree below $B$. So

```math
N = M_a + X M_b, \qquad X^2 = 7,
```

is a uniform polynomial in $\mathbb{F}_{p^2}[x]$ of degree below $B$: $(M_a, M_b) \mapsto N$ is a
bijection, because $\{1, X\}$ is a basis of $\mathbb{F}_{p^2}$ over $\mathbb{F}_p$.

On the launch transcript the frame opens $N$ and not $M_a, M_b$ apart. In each window row $k$:
- slot $a$ carries $N(z_k)$;
- slot $b$ carries zero, which the verifier requires;
- DEEP gives column $b$ the coefficient $X a_k$, with $a_k = \alpha^{44k + 42}$ column $a$'s.

The code is `replay_pre::mask_pair_frame`, `mask_pair_canonical` and `mask_pair_coeffs`, applied by
the prover, the verifier and every replay. So the mask's part of $D$ is

```math
D_M = \sum_{k \in \{0,1\}} a_k \, \frac{N(x) - N(z_k)}{x - z_k},
```

and $D = D_W + D_M$, with $D_W$ everything else.

**Lemma 4.3 (F_p²-linearity).** Everything the proof reveals about the mask is
$\mathbb{F}_{p^2}$-linear in $N$:
- its values at the 152 opened rows and successors, the pair $(M_a(x), M_b(x))$ being $N(x)$ for
  base-field $x$;
- $N(z_k)$;
- $F(D_M)$.

*Proof.* Evaluation at a point is linear, $Q_{z}(N) = (N - N(z))/(x - z)$ is linear in $N$, and
FRI's folds and openings are $\mathbb{F}_{p^2}$-linear in $D$. $\square$

Let $A$ be the mask's openings: 152 row values and $N(z_0), N(z_1)$, 154 functionals over
$\mathbb{F}_{p^2}$. Let $L_0$ be FRI layer zero.

The simulator samples $D^*$ uniformly among polynomials of degree below $B - 1$ that take the
layer-zero values it has already fixed. Its V5 is then uniform on $F(D^*_0) + F(\ker L_0)$, where
$D^*_0$ is any polynomial with those values.

**Condition (R).** $\dim_{\mathbb{F}_{p^2}} F(\ker A) = \dim_{\mathbb{F}_{p^2}} F(\ker L_0)$,
with $\ker A$ taken over $N$ and $\ker L_0$ over all $D$.

**Lemma 4.2.** Under (R), conditioned on V1 to V4, the real V5 is distributed exactly as the
simulator's.

*Proof.* Given the openings, $N$ is uniform on a coset of $\ker A$, so $F(D_M)$ is uniform on
$F(D_{M,0}) + F(\ker A)$.

For $N \in \ker A$, $N$ vanishes at the V1 points and at $z_k$, so $D_M$ vanishes at every
layer-zero point. Hence $F(\ker A) \subseteq F(\ker L_0)$, and (R) makes the two equal.

The real V5 is $F(D_W + D_M)$, uniform on $F(D_W + D_{M,0}) + F(\ker L_0)$. The real $D$ and
$D^*_0$ agree at layer zero, so this is the simulator's affine space. $\square$

**The bound on (R) failing.** Write the matrix $[A; F]$ in the monomial basis $N = x^i$,
$i < B = 2^{17}$. Its entries are polynomials over $\mathbb{F}_{p^2}$ in the challenges
$z, \alpha, \beta_0, \dots, \beta_3$:

| rows | count | depends on | degree at most |
|---|---|---|---|
| $A$, the opened rows | 152 | nothing: the points are fixed by the positions | 0 |
| $A$, $N(z_k)$ | 2 | $z$ | $B - 1$ |
| $F$, layers 1 to 3 and the final layer | 740, rank 664 | $z$ through $Q_{z_k}(x^i)$; $\alpha$ through $a_k$, exponent at most 86; the betas, 3 per layer | $e = (B - 1) + 86 + 12 = 131{,}169$ |

(R) holds when a square minor of size $154 + 664 = 818$ is nonzero. The determinant has degree at
most

```math
2(B - 1) + 664 \, e = 262{,}142 + 87{,}096{,}216 = 87{,}358{,}358 < 2^{26.38}.
```

It is a nonzero polynomial: `zk_fri_rank` and `zk_h6` find the full rank on real proofs. By
Schwartz-Zippel over $\mathbb{F}_{p^2}$, for challenges drawn uniformly by the random oracle, and
positions that do not collide:

```math
\varepsilon_R \le \frac{87{,}358{,}358}{p^2} < \frac{2^{26.38}}{2^{127.99}} = 2^{-101.6}.
```

That bound is for challenges drawn at random over positions in general position. It is not the
rate at which (R) fails, because one class of positions makes it fail for every challenge.

**The collision class.** Let query $A$ open the layer-zero coset $C_A$, and its successor rows
$g C_A$, which is again a coset of the fourth roots of unity. Its fourth power is one point $s_A$
of the layer-one domain. If $s_A$ lies in another query $B$'s layer-one leaf and is not $B$'s own
point, (R) fails:
- every $N \in \ker A$ vanishes on $g C_A$, because the mask columns are opened at every row and
  its successor, so all four components of $D_M$ vanish at $s_A$ and the folded value there is
  zero for every $\beta_0$;
- the simulator's $D^*$ is fixed only on layer zero, and the leaf value at $s_A$ is one of its free
  values.

For $q$ queries it has probability at most $3 q (q - 1) / 2^{21} = 1{,}026 / 2^{21}$, about one
proof in 2,044. When $s_A$ is $B$'s own point both sides vanish there and (R) is unaffected. The
per-proof check refuses the class and the wallet proves again, so the class costs time, not
privacy. `zk_rank_test` places the queries by hand and shows all three cases.

**Lemma 4.4 (general position).** Outside the collision class, and with distinct leaves at every
layer, the minor is a nonzero polynomial in the challenges.

*Proof.* It is enough to exhibit one assignment where (R) holds. Take $\beta_m = 0$ for every
layer, so each fold keeps one component: writing $D(x) = \sum_{i<4} x^i h_i(x^4)$, layer one is
$h_0$, and every value FRI reveals past layer zero is a functional of $h_0$. The simulator's
space projects onto $\{h_0 : h_0(Y_0) = 0\}$, with $Y_0$ the queries' layer-one points. The
mask's space $\ker A$ projects onto the same set with $h_0(S) = 0$ added, $S$ the points $s_A$,
because the components $h_1, h_2, h_3$ still meet the remaining constraints, one evaluation away
from the domain for the DEEP pole, with room to spare. So (R) needs no revealed functional to
involve $h_0$ at a point of $S$. Layer one reveals $h_0$ only on the queries' leaves, which the
class excludes. Deeper layers and the final polynomial are functions of the layer-two
components of $h_0$. The polynomial $x \, r(x^4)$ with $r$ vanishing on the fourth powers of every
opened leaf has zero layer-two components, vanishes on every opened leaf, and is nonzero at a
point of $S$ outside the leaves. So the evaluations at $S$ are independent of everything revealed,
and dropping them costs no rank. Each degree used stays below $B / 4^4 = 512$, far above the 19
queries. $\square$

**The certificate.** `zk_rank` gives each mask column its own row, 304 in all, over the distinct
rows opened, so the check constrains each column and not only their sum. It refuses the collision
class, holds on every pinned proof, and runs in 16 to 20 s on one server core.

**Checked**, on the route 2 package, each proof with its own challenges and positions:

| proof | simulator rank, $\mathbb{F}_p$ | mask rank, $\mathbb{F}_p$ | H6: rank over $\mathbb{F}_{p^2}$ on $\ker A$ | fast certificate |
|---|---|---|---|---|
| withdraw-a | 1,328 | 1,328 | 664 of 740 | holds |
| withdraw-b | 1,328 | 1,328 | 664 of 740 | holds |
| honest | 1,328 | 1,328 | 664 of 740 | holds |
| spend | 1,328 | 1,328 | 664 of 740 | holds |
| control: masks of degree below $2^{12}$ | 1,328 | 318 | | fails, as it must |

- `zk_fri_rank`: both sides over $\mathbb{F}_p$.
- `zk_h6`: masks $N = W (x - z)(x - gz) R$, exactly $\ker A$.
- `zk_rank`: the certificate a wallet runs.

**Route 1, kept permanently.** The wallet runs `nox_prover::zk_fri_rank_check` on every proof and
re-proves with fresh entropy on a shortfall. A sent proof then satisfies (R) exactly. The
collision class sets how often that happens, about once in 2,044 proofs; Schwartz-Zippel adds
less than $2^{-101.6}$. `Shield.Launch` checks both figures in Lean. `Shield.Masking` extends
the Schwartz-Zippel bound to every query count up to 19: with all $12q + 512$ rows of $F$ the
failure stays below $2^{-100}$, so each point with fewer queries keeps it.

### 4.5 Digests and nonces (V6, V7)

- **Digests.** A Merkle digest is the random oracle on a leaf. Every unopened leaf holds values of
  blinded or masked polynomials at a point outside V1, and each has at least 64 bits of
  min-entropy given the whole view: Lemma 4.1 and Lemma 4.2 leave every such value undetermined.
  An observer who wants to test a guess at a leaf must query the oracle on it, and succeeds with
  probability at most $2^{-64}$ per query. So the digests can be replaced by uniform strings, at
  the cost $\varepsilon_{\mathrm{RO}}$ of the proposition.
- **Nonces.** They are the smallest winners against transcript states the simulator knows, and it
  computes them the same way.

### 4.6 The simulator

Given the public words:

1. Sample V1 and V2 uniformly.
2. Compute V3 and V4 from them (Section 4.3).
3. Sample $D^*$ as in Section 4.4 and compute V5 from it.
4. Commit random strings for every unopened leaf.
5. Program the random oracle so that each challenge, and each query position, is the one the
   simulated values assume.
6. Compute the nonces against the programmed states.

The hybrid argument then takes one step per section:
- 4.2 makes V1 and V2 uniform;
- 4.3 makes V3 and V4 the same functions of them;
- 4.4 makes V5 identical under (R);
- 4.5 replaces the digests at cost $\varepsilon_{\mathrm{RO}}$.

The blinding and mask polynomials are drawn from a pseudorandom function (Poseidon, keyed by a
seed from the operating system's CSPRNG: `air::zk::blinding_poly`, `seed_from_entropy`), not from
true randomness. So the statement is computational: it holds for any observer who cannot
distinguish that function from random.

### 4.7 Conditions and the code that meets each

| | condition | where | launch |
|---|---|---|---|
| Z1 | blinding degree covers what is opened: $d \ge E - 1$ | `air::zk::blinding_degree` | $164 \ge 155$ |
| Z2 | blinding fits under the composition bound: $D d + w - 1 < t$ | `air::zk::blinding_fits` | $1{,}805 < 8{,}192$ |
| Z3 | mask columns uniform of degree below $B$, read by no constraint | `hide_at`, `WiredMultiExt::with_mask`, `MASK_COLUMNS` = 2 | 2 columns |
| Z4 | the rank condition (R), over $\mathbb{F}_{p^2}$ with the mask pair opened as one value | `replay_pre::mask_pair_*`, `zk_rank`, `zk_fri_rank`, `zk_h6` | fails for about one proof in 2,044, which the wallet re-proves; checked on every proof sent |
| Z5 | fresh, secret seeds: 512 bytes from the CSPRNG per proof, never reused | `nox_prover::ENTROPY_BYTES`, `seed_from_entropy` | per proof |

Whether Z1 to Z5 match the conditions of Haböck's note item for item is for the auditor to
confirm against the note itself. They are this construction's own conditions, stated so that
each can be checked.

### 4.8 The relayed path

The settlement outer's witness is the inner proof and the public words, so whatever the outer
reveals is a function of the inner proof. Once the inner is zero-knowledge, the outer leaks
nothing beyond the public words and needs no mask of its own. It is blinded at degree 124
regardless.

### 4.9 A scan for secrets in the clear

The settled proof of transaction 0xbc0c2f0d (root c7701eaa) and the relayer's copy of its inner
proof were scanned for every secret of that spend: 198 words, each value, limb, blinding and key,
at every byte offset in both byte orders. There were no hits, and a control with one planted
secret was found. This rules out secrets in the clear. The sections above are what rule out
linear combinations.
