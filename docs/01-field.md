# 01. The field

Every value the proof system computes with is an element of the Goldilocks field or of its
quadratic extension. This document defines both, proves the identities the arithmetic relies
on, and states the encoding every reader and writer of a proof applies. It is for anyone who
reimplements the arithmetic, audits the reduction, or has to decide whether a byte string is a
valid field element.

Notation follows 00-notation.md. Code references are to
`nonos-stark/src/field/` unless another path is given.

## 1. The base field

**Definition 1.1.** Let

```math
p = 2^{64} - 2^{32} + 1 = 18\,446\,744\,069\,414\,584\,321
```

and let $`\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}`$. Let $\varepsilon = 2^{32} - 1 = 2^{64} - p$.

In code, `P = 0xFFFF_FFFF_0000_0001` and `EPSILON = 0xFFFF_FFFF`
(`element.rs:6`, `element.rs:9`). An element is the type `Fp(u64)` and is held in canonical
form, the unique representative in $[0, p)$ (`element.rs:13`).

The number $p$ is prime. It is the Goldilocks prime used by Plonky2 [12], and any primality
test confirms it.

**Proposition 1.2.** In $`\mathbb{F}_p`$, $2^{64} \equiv \varepsilon$ and $2^{96} \equiv -1$.

*Proof.* $2^{64} = p + (2^{32} - 1) = p + \varepsilon$, so $2^{64} \equiv \varepsilon$. Then
$2^{96} = 2^{32} \cdot 2^{64} \equiv 2^{32}(2^{32} - 1) = 2^{64} - 2^{32} \equiv \varepsilon - 2^{32} = -1$. $\square$

Both identities replace a division in the reduction of a 128-bit product (Section 2).

### 1.1 Reduction of a 64-bit word

`Fp::from_u64(x)` returns $x$ if $x < p$ and $x - p$ otherwise (`element.rs:29`). One
conditional subtraction is enough because $x < 2^{64} = p + \varepsilon < 2p$.

### 1.2 Addition, subtraction, negation

For canonical $a, b$ the sum $a + b$ lies in $0, 2p)$. The code computes the 64-bit wrapping
sum and its carry (`ops.rs:14`):

- if the sum carried past $2^{64}$, the true value is $s + 2^{64} \equiv s + \varepsilon$, and
  $s + \varepsilon$ is already below $p$ because $s = a + b - 2^{64} < 2p - 2^{64} = p - \varepsilon$.
- otherwise one conditional subtraction of $p$ makes the value canonical.

Subtraction (`ops.rs:33`) computes $a - b$ modulo $2^{64}$ with a borrow flag. On a borrow the
wrapped word is $a - b + 2^{64}$, and the field result $a - b + p$ is that word minus
$\varepsilon$. Negation maps $0$ to $0$ and $a \neq 0$ to $p - a$ (`ops.rs:46`).

## 2. Multiplication and the 128-bit reduction

A product of two canonical elements is a 128-bit integer $x < p^2$. The code writes

```math
x = \ell + 2^{64}\,(h_1 \cdot 2^{32} + h_0), \qquad 0 \le \ell < 2^{64},\ 0 \le h_0, h_1 < 2^{32}
```

where `lo` $= \ell$, `hi_hi` $`= h_1`$ and `hi_lo` $`= h_0`$ (`ops.rs:77`).

**Proposition 2.1.** $`x \equiv \ell - h_1 + \varepsilon\, h_0 \pmod p`$.

*Proof.* By Proposition 1.2, $`2^{64} h_0 \equiv \varepsilon h_0`$ and
$`2^{96} h_1 \equiv -h_1`$. $\square$

**Proposition 2.2.** `reduce128` returns the canonical representative of $x$ for every
$x < 2^{128}$.

*Proof.* Follow the code (`ops.rs:83` to `ops.rs:94`).

1. $`t \leftarrow \ell - h_1 \bmod 2^{64}`$. If there is no borrow, $`t = \ell - h_1`$. If there is
   a borrow, the word is $`\ell - h_1 + 2^{64}`$, and the code subtracts $\varepsilon$ to obtain
   $`\ell - h_1 + p`$, congruent to $`\ell - h_1`$. The subtraction does not wrap, because the word is
   at least $`2^{64} - h_1 > 2^{64} - 2^{32} > \varepsilon`$.
2. $`r \leftarrow t + \varepsilon h_0 \bmod 2^{64}`$. The term $`\varepsilon h_0`$ is at most
   $(2^{32} - 1)^2 = 18\,446\,744\,065\,119\,617\,025 < p$. If the sum carries, the true value is
   $r + 2^{64} \equiv r + \varepsilon$, and the code adds $\varepsilon$. That addition cannot carry
   again: after a carry $`r = t + \varepsilon h_0 - 2^{64} < \varepsilon h_0 < 2^{64} - 2^{33} + 2`$,
   so $r + \varepsilon < 2^{64} - 2^{32} + 1 = p$.
3. Without a carry, $r < 2^{64} < 2p$, and one conditional subtraction of $p$ lands in $[0, p)$.
   With a carry, $r + \varepsilon < p$ already.

Every step preserves the residue class by Proposition 2.1, and the result lies in $[0, p)$. $\square$

The proof is held by two tests in `ops.rs`:

| test | what it checks |
|---|---|
| `the_fast_reduction_agrees_with_the_division` | `reduce128` equals `x mod p` on the 144 products of twelve corner words (0, 1, 2, $\varepsilon$, $\varepsilon + 1$, $2^{32}$, $p - 2$, $p - 1$, $p$, $p + 1$, $2^{64} - 1$, $2^{64} - 2$) and on 20,000 pseudorandom products |
| `the_reduction_is_canonical` | the output is below $p$ on 50,000 products near the top of the range |

## 3. The multiplicative group and roots of unity

**Proposition 3.1.** $p - 1 = 2^{32} \cdot 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$.

*Proof.* $p - 1 = 2^{64} - 2^{32} = 2^{32}(2^{32} - 1)$, and
$2^{32} - 1 = (2^{16} - 1)(2^{16} + 1) = 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$. $\square$

The **two-adicity** of $`\mathbb{F}_p`$ is 32: the multiplicative group contains a subgroup of
order $2^k$ for every $k \le 32$ and none of order $2^{33}$.

**Proposition 3.2.** $7$ generates $`\mathbb{F}_p^{\times}`$.

*Checked by computation.* An element $g$ generates a cyclic group of order $p - 1$ if and only
if $g^{(p-1)/q} \neq 1$ for every prime $q \mid p - 1$. For $g = 7$ and
$`q \in \{2, 3, 5, 17, 257, 65537\}`$ none of the six powers is $1$. The check is a six-line
computation (`pow(7, (p-1)//q, p) != 1`). $\square$

**Definition 3.3.** For $k \le 32$ let $`\omega_k = 7^{(p-1)/2^k}`$ (`fri/domain.rs:16`).

**Corollary 3.4.** $`\omega_k`$ has order $2^k$, and $`\omega_k^{2^{k-1}} = -1`$.

*Proof.* $7$ has order $p - 1$, so $7^{(p-1)/2^k}$ has order $2^k$. Its power $2^{k-1}$ is an
element of order two, and the only element of order two in a field is $-1$. $\square$

The FRI fold pairs each point $x$ of a domain with $-x$, which Corollary 3.4 places in the same
domain (see [08-fri.md).

### 3.1 The trace domain and the evaluation coset

Let $t = 2^{\log t}$ be the trace length. The **trace domain** is $H = \langle g \rangle$ with
$`g = \omega_{\log t}`$. The **evaluation domain** of size $N = 2^{\log N}$ is the coset

```math
D = s \cdot \langle \omega \rangle, \qquad \omega = \omega_{\log N},\ s = 7,
```

with `SHIFT = 7` (`air/prove_ext/setup.rs:17`) and its $j$-th point $s\,\omega^j$
(`setup.rs:61`).

**Proposition 3.5.** $D \cap H = \emptyset$.

*Proof.* Every element of $H$ satisfies $x^t = 1$. For $s\,\omega^j \in D$,
$(s\,\omega^j)^t = s^t\,\omega^{jt}$. If this were $1$, then $s^t \in \langle \omega \rangle$, so
$s^{tN} = 1$ and the order of $s = 7$, which is $p - 1$, would divide $tN \le 2^{64}$. It does
not, because $p - 1$ has odd factors. $\square$

Proposition 3.5 is what makes every divisor $x^t - 1$ in the composition invertible on $D$
(06-composition.md).

The size $N$ follows from the AIR (`air/composition.rs:36`):

```math
B = \operatorname{next\_pow2}(d \cdot t), \qquad N = 2B \cdot 2^{e},
```

where $d$ is the constraint degree and $e$ the point's extra blowup. The FRI rate is
$\rho = B/N = 2^{-(1+e)}$.

## 4. Exponentiation and inversion

`Fp::pow` is square and multiply over the bits of the exponent (`exp.rs:14`). Inversion is
Fermat's little theorem, $a^{-1} = a^{p-2}$ for $a \neq 0$ (`exp.rs:29`).

**Convention 4.1.** `inv(0)` returns $0$. Zero has no inverse, and every caller divides only by
values proved or checked nonzero: points of $D$ minus points of $H$ (Proposition 3.5), $z$
minus points of $H$ (the out-of-domain point is redrawn until it avoids $H$ and $D$, see
07-deep.md), and the differences $i - (8 + j)$ in the Poseidon matrix
([02-poseidon.md](02-poseidon.md)).

## 5. The quadratic extension

**Definition 5.1.** $`\mathbb{F}_{p^2} = \mathbb{F}_p[X]/(X^2 - 7)`$. An element is
$`a = a_0 + a_1 X`$ with $`a_0, a_1 \in \mathbb{F}_p`$, held as the pair `Fp2 { c0, c1 }`
(`ext.rs:23`), with `W = 7` (`ext.rs:19`).

**Proposition 5.2.** $7$ is a quadratic non-residue modulo $p$, so $X^2 - 7$ is irreducible and
$`\mathbb{F}_{p^2}`$ is a field of $p^2 \approx 2^{128}$ elements.

*Proof.* By quadratic reciprocity, since $p \equiv 1 \pmod 4$,
$\left(\frac{7}{p}\right) = \left(\frac{p}{7}\right)$. Modulo 7, $2^3 \equiv 1$, so
$2^{64} \equiv 2$ and $2^{32} \equiv 4$, and $p \equiv 2 - 4 + 1 = -1 \equiv 6$. The squares
modulo 7 are $`\{1, 2, 4\}`$, so $\left(\frac{6}{7}\right) = -1$. A polynomial of degree two
without a root is irreducible, and the quotient by an irreducible polynomial is a field. $\square$

Proposition 3.2 gives a second proof: a generator of $`\mathbb{F}_p^{\times}`$ is never a square.

The operations (`ext.rs:96` to `ext.rs:134`):

```math
(a_0 + a_1 X)(b_0 + b_1 X) = (a_0 b_0 + 7\, a_1 b_1) + (a_0 b_1 + a_1 b_0) X
```

```math
N(a) = a_0^2 - 7\,a_1^2 = (a_0 + a_1 X)(a_0 - a_1 X), \qquad a^{-1} = \frac{a_0 - a_1 X}{N(a)}.
```

**Proposition 5.3.** $N(a) = 0$ if and only if $a = 0$.

*Proof.* If $`a_1 \neq 0`$ and $N(a) = 0$, then $`(a_0/a_1)^2 = 7`$, contradicting Proposition 5.2.
If $`a_1 = 0`$, then $`N(a) = a_0^2`$, which is zero only for $`a_0 = 0`$. $\square$

`Fp2::inv` returns $0$ for $0$ under Convention 4.1 (`ext.rs:86`). `mul_base` scales both
coordinates by a base element (`ext.rs:80`), and the base field embeds as $a \mapsto a + 0X$
(`ext.rs:40`).

### 5.1 Why challenges live in the extension

Every random challenge the verifier draws (the composition and DEEP coefficients, the
out-of-domain point $z$, the FRI folding challenges $`\beta_m`$) is an element of
$`\mathbb{F}_{p^2}`$. The copy-constraint challenges $\beta, \gamma$ of
10-copy-constraint.md are base-field elements, and their soundness
term is bounded there. The error terms in the soundness analysis are of the form
$\deg / |\mathbb{F}|$ (Schwartz and Zippel [7], [8]), which is near $2^{-64+\log \deg}$ over
the base field and near $2^{-128+\log \deg}$ over the extension. The terms are collected in
[12-soundness.md](12-soundness.md).

### 5.2 The tower used by the recursion

The recursive verifier evaluates an inner AIR's constraints on inner extension elements that it
holds as pairs of its own cells. `Ext2<F>` in `tower.rs` is the ring $F[X]/(X^2 - 7)$ over any
base $F$ implementing `Felt`, so the inner constraint code runs unchanged over the pairs. With
$`F = \mathbb{F}_p`$ it is $`\mathbb{F}_{p^2}`$ element for element. See
11-recursion.md.

## 6. Encoding

**Rule 6.1.** A base element is written as 8 bytes, little endian, canonical. A reader refuses a
word $v \ge p$. It never reduces it.

| reader | location |
|---|---|
| proof codec, rounds | `stark_proofs/src/proof_wire/read_rounds.rs:48` |
| proof codec, base half | `nonos-stark/src/air/wire/deserialize_ext.rs:41` |
| sealed opening | `note_seal/src/format.rs` (`Opening::from_bytes`) |

An extension element is $`c_0`$ then $`c_1`$, 16 bytes. Refusing a non-canonical word gives every
element one encoding, so two byte strings never decode to one proof or one note.

A digest of four elements is packed differently in two places, and each is stated where it is
used: the note tree and the pool pack the four limbs as one 256-bit little-endian integer
(`stark_proofs/src/shield/imt/hash.rs:54`), and the client prints digests big endian with limb 0
in bytes 24 to 32. 13-codec.md gives the proof's own
layout.
