# 03. Values

Section 4 of [03-keys-notes-nullifiers.md](03-keys-notes-nullifiers.md), in its own file: how a
note's value is represented so that conservation is a statement about integers and not only about
field elements. The numbering continues that document's.

## 4. Values

### 4.1 Why a value is split at 32 bits

A note's value is a 64-bit integer and a field element holds less: $p < 2^{64}$. The circuit
checks balance with field arithmetic, and a field equation holds modulo $p$. A transfer whose
inputs and outputs agree only modulo $p$ creates money.

**Proposition 4.1.** The single congruence
$`v_{in,0} + v_{in,1} \equiv v_{out,0} + v_{out,1} \pmod p`$ over 64-bit amounts does not imply
integer conservation.

*Proof.* Take $K = 10^{18}$, inputs $1$ and $1$, outputs $2 + K$ and $p - K$. Both outputs are
below $2^{64}$, the input sum minus the output sum is $-p$, and the first output alone exceeds
the inputs. $\square$

This is `Shield.LimbBalance.modular_balance_alone_creates_value` in
`lean/Shield/LimbBalance.lean:64`, closed by `decide`. The Rust test
`value_wrap_test.rs` (`a_transfer_that_balances_only_modulo_p_is_refused`) builds a transfer of
this shape and checks that the wired circuit refuses it.

Carrying a value as two limbs of at most 32 bits each, bounding every limb, and balancing the
two limb sums separately turns the congruences into integer equations. The rest of this section
states the constraints and proves that.

### 4.2 The balance region

The balance region has 7 columns and one row per *leg* (`nonos-stark/src/air/value_balance/air.rs`).
A join-split has six legs, in the fixed order

| row | leg | sign $\sigma$ |
|---|---|---|
| 0, 1 | spent note 0, spent note 1 | $+1$ |
| 2, 3 | created note 0, created note 1 | $-1$ |
| 4 | public amount | $-1$ |
| 5 | fee | $-1$ |
| 6, 7 | padding | $0$ |

(`join/terms.rs:15`, `balance_shape`). The sign is a periodic column (`value_balance/leg.rs:21`),
so it is fixed by the statement. A prover chooses the values on the rows and cannot relabel an
output as an input.

Row $r$ holds $`(S^{lo}_r, \ell_r, h_r, v_r, S^{hi}_r, \kappa_r, \rho_r)`$: the running low sum,
the low limb, the high limb, the recomposed value, the running high sum, the carry cell and the
high limb's room. With the limb base $B = 2^{32}$, the bound $H = 2^{32} - 2$
(`HI_MAX`, `air.rs:31`), the carry offset $3$ (`CARRY_OFFSET`, `air.rs:25`), the periodic sign
$`\sigma_r`$ and the periodic closing selector $`\chi_r`$, the transition constraints are

```math
\begin{aligned}
v_r - \ell_r - B\,h_r &= 0 \\
\rho_r + h_r - H &= 0 \\
S^{lo}_{r+1} - S^{lo}_r - \sigma_r \ell_r &= 0 \\
S^{hi}_{r+1} - S^{hi}_r - \sigma_r h_r &= 0 \\
\chi_r \big(S^{lo}_r - (\kappa_r - 3) B\big) &= 0 \\
\chi_r \big(S^{hi}_r + (\kappa_r - 3)\big) &= 0
\end{aligned}
```

(`air.rs:62`, `transition_impl`, term for term in this order). The boundary constraints set
$`S^{lo}_0 = S^{hi}_0 = 0`$ (`value_balance/spec.rs:42`). The closing selector is one on row 6,
the first row after the six legs, and zero elsewhere (`air.rs:74`, `close_row`). There both sums
are complete:

```math
S^{lo}_6 = \sum_{r<6} \sigma_r \ell_r, \qquad S^{hi}_6 = \sum_{r<6} \sigma_r h_r.
```

### 4.3 The range region

A second region proves that 19 cells of the balance region lie in ranges: for each of the six
legs the low limb, the high limb and the room at 32 bits, and the carry cell at 3 bits
(`value_balance/trace.rs:49`, `ranged`). Each range is a segment of $L$ rows over two columns
$(\mathit{acc}, \mathit{bit})$ (`value_balance/range.rs`) with constraints

```math
\mathit{bit}_r (\mathit{bit}_r - 1) = 0, \qquad (1 - e_r)(\mathit{acc}_r - 2\,\mathit{acc}_{r+1} - \mathit{bit}_r) + e_r (\mathit{acc}_r - \mathit{bit}_r) = 0,
```

where the periodic column $e$ is one on the last row of each segment (`range.rs:62`,
`transition_gen`).

**Lemma 4.2.** If a segment of $L \le 32$ rows satisfies the constraints, its first cell is an
integer in $0, 2^L)$.

*Proof.* Every $`\mathit{bit}_r`$ is 0 or 1. Unrolling from the last row,
$`\mathit{acc}_{\text{first}} = \sum_{i<L} 2^i\,\mathit{bit}_i`$ in $`\mathbb{F}_p`$. The sum is an
integer in $[0, 2^L)$, and $2^L \le 2^{32} < p$, so it is its own canonical representative.
$\square$

Each segment's first cell is wired to the balance cell it bounds (`join/bind_range.rs:11`,
`range_classes`). The wiring is a copy constraint, proved by the permutation argument of
[10-copy-constraint.md. The unit tests
`values_that_fit_their_segments_satisfy` and `a_value_one_past_its_segment_is_refused` in
`range.rs` check the boundary on both sides.

### 4.4 Integer conservation

**Theorem 4.3 (limb-wise conservation).** Suppose every leg satisfies
$`0 \le \ell_r < 2^{32}`$ and $`0 \le h_r \le 2^{32} - 2`$, the carry $`c = \kappa_6 - 3`$ satisfies
$0 \le c + 3 < 8$, and the two closing constraints hold in $`\mathbb{F}_p`$. Then, as integers,

```math
v_0 + v_1 = v_2 + v_3 + v_4 + v_5, \qquad v_r = \ell_r + 2^{32} h_r.
```

*Proof.* Write $`L = \ell_0 + \ell_1 - \ell_2 - \ell_3 - \ell_4 - \ell_5`$ and
$`H' = h_0 + h_1 - h_2 - h_3 - h_4 - h_5`$ as integers. The closing constraints say
$L - cB \equiv 0$ and $H' + c \equiv 0 \pmod p$. By the bounds,
$-2^{34} < L < 2^{33}$ and $-3 \le c \le 4$, so $|L - cB| < 2^{34} + 2^{35} < p$, and a
multiple of $p$ that small is zero: $L = cB$. In the same way $|H' + c| < 2^{35} < p$ gives
$H' = -c$. Then $L + B H' = cB - cB = 0$, which is the statement. $\square$

This is `limbwise_conservation` in `lean/Shield/LimbBalance.lean:39`, stated with the two
closing constraints as congruences $(\,\cdot\,) = k p$ and closed by `omega`. The companion
`the_carry_fits_three_bits` (line 52) shows that the honest carry lies in $[-3, 1]$, so an
honest transfer always has a witness: the low sum lies in $(-2^{34}, 2^{33})$ and is a multiple of
$2^{32}$ when the transfer balances. The prover computes it as $\lfloor L / 2^{32} \rfloor + 3$
(`value_balance/trace.rs:38`).

**Corollary 4.4.** Every value in the balance region is at most $p - 2$, and its field value and
integer value agree.

*Proof.* $v = \ell + 2^{32} h \le (2^{32} - 1) + 2^{32}(2^{32} - 2) = 2^{64} - 2^{32} - 1 = p - 2$.
$\square$

This is `a_bounded_value_is_below_p` (line 25). The room column is what bounds the high limb:
$h \le 2^{32} - 2$ holds because $\rho = H - h$ is range-checked to $[0, 2^{32})$, and a high limb
of $2^{32} - 1$ would make $\rho = -1 = p - 1$.

### 4.5 How the values reach the rest of the circuit

The balance region sums numbers, and the wiring says which numbers. For each note leg the low
and high limb cells are wired to lanes 0 and 1 of that note's public quad
(`join/bind_note.rs:19`), so the limbs summed are the limbs committed. The public amount and the
fee are wired to their public words through the recomposed value $`v_r`$ in column 3
(`join/bind_publics.rs:86`). All four notes' asset limbs are one wiring class, and the first
input's is wired to the public asset word (`join/bind_asset.rs:17`,
`join/bind_publics.rs:88`), so a transfer moves one asset. Conservation per asset in a swap
needs a different region, and none exists.

### 4.6 Dummy inputs

A payment with one note spends a dummy beside it. The live gate of each input
(`nonos-stark/src/air/live_gate/air.rs`) holds a bit $\lambda$, the input's two value limbs
$(\ell, h)$ wired to its balance row (`join/bind_publics.rs:42`), and a witnessed inverse
$\iota$, with

```math
\lambda(\lambda - 1) = 0, \qquad \lambda - (\ell + B h)\,\iota = 0, \qquad (1 - \lambda)\,\ell = 0, \qquad (1 - \lambda)\,h = 0,
```

and the membership equalities of the input multiplied by $\lambda$ (`air.rs:71`). A live input
must reach the published roots. A dead one must be worth zero in both limbs.

**Proposition 4.5.** An input worth $p$ as an integer is refused.

*Proof.* Its limbs are $\ell = 1$ and $h = 2^{32} - 1$, since $p = (2^{32} - 1) 2^{32} + 1$.
Its room is $-1$, which fails the range region (Corollary 4.4). Independently, if $\lambda = 0$
the constraint $(1 - \lambda)\ell = 0$ fails, and if $\lambda = 1$ then
$(\ell + Bh)\,\iota = p\,\iota = 0 \ne 1$. $\square$

`a_bounded_value_zero_mod_p_is_zero` (line 31) is the general form: a bounded value that is zero
modulo $p$ is zero. The test `test/one_note.rs` (`a_dummy_worth_p_is_refused`) checks the
instance, and `a_dead_input_cannot_carry_value` checks the dead-bit forgery.
