-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
The masking count of docs/12-zero-knowledge.md, Sections 4.2 and 4.4, at the
launch shape and at every point the `fri8` build proposes, as statements about the formulas
the prover runs. It is the count, not the masking proof: that the count
matches what a proof opens is taken from the formulas, and Lemmas 4.1 and 4.2
themselves are not here yet.

What is proved here is the counting: that the blinding the prover draws
(`air::zk::blinding_degree`) has more random coefficients than a proof
reveals evaluations of a column (Lemma 4.1's hypothesis `d ≥ E - 1`), that
the blinding keeps the composition under its degree bound
(`air::zk::blinding_fits`), and that the rank condition's Schwartz-Zippel
bound stays below 2^-100 at every query count up to the launch's.

What is not proved here is Lemma 4.1's algebra, that evaluation at E points is
onto polynomials of degree at least E - 1. That is interpolation over F_p, and
this development is core Lean with no field library; docs/12 carries the proof
and `zk_check` measures its consequence on the committed polynomials.

The general theorems hold for every query count, window and radix, so a
parameter change cannot leave the counting behind: only the instances move.
-/

namespace Shield.Masking

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

/-! ### The formulas, transcribed -/

/-- `air::zk::ZK_MARGIN` -/
def margin : Nat := 8

/-- `air::zk::blinding_degree(n_queries, window, radix)` -/
def blindingDegree (q w r : Nat) : Nat := r * w * q + 2 * w + margin

/-- Base-field functionals a proof fixes on one column (docs/12 4.2): each
query's FRI leaf has `r` points and each point `w - 1` successors, one
evaluation each; the frame reads `w` points of F_p^2, two each. -/
def revealed (q w r : Nat) : Nat := r * w * q + 2 * w

/-- `air::zk::blinding_fits(deg, D, t, window)` -/
def fits (deg D t w : Nat) : Prop := D * deg + w - 1 < t

instance (deg D t w : Nat) : Decidable (fits deg D t w) := by unfold fits; infer_instance

/-! ### Lemma 4.1's hypothesis, for every shape -/

/-- The blinding has exactly nine coefficients beyond the count Lemma 4.1 needs
(`d ≥ E - 1`), whatever the queries, window and radix. -/
theorem blinding_exceeds_revealed (q w r : Nat) :
    blindingDegree q w r + 1 = revealed q w r + margin + 1 := rfl

theorem lemma_4_1_hypothesis (q w r : Nat) : revealed q w r - 1 ≤ blindingDegree q w r :=
  Nat.le_trans (Nat.sub_le _ 1) (Nat.le_add_right _ margin)

/-- Fewer queries never need more blinding: the count falls with q. -/
theorem fewer_queries_less_to_hide (q q' w r : Nat) (h : q' ≤ q) :
    revealed q' w r ≤ revealed q w r := by
  unfold revealed
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-! ### The launch shape: radix 4, window 2, t = 2^13, constraint degree 11 -/

def radix : Nat := 4
def boundB : Nat := 131072

theorem boundB_is : boundB = 2 ^ 17 := by decide
def window : Nat := 2
def t : Nat := 8192

theorem t_is : t = 2 ^ 13 := by decide
def constraintDegree : Nat := 11

theorem launch_counts : revealed 19 window radix = 156 ∧ blindingDegree 19 window radix = 164 := by
  decide

/-- The launch blinding fits under the composition bound, with room: 1,805 of 8,192. -/
theorem launch_fits : fits (blindingDegree 19 window radix) constraintDegree t window := by decide

/-- It fits at every query count up to 91 at this shape, so no `fri8` point is
limited by the composition bound. -/
theorem fits_up_to_91 (q : Nat) (h : q ≤ 91) :
    fits (blindingDegree q window radix) constraintDegree t window := by
  unfold fits blindingDegree radix window constraintDegree t margin
  omega

theorem fits_stops_at_92 : ¬ fits (blindingDegree 92 window radix) constraintDegree t window := by
  decide

/-- The points once proposed for the `fri8` build at radix 4: 17 and 15 queries at rate 2^-6,
15, 14 and 13 at 2^-7. The blinding does not depend on the rate. The `fri8` build shipped at
radix 8; its shapes are `query_shape_counts` below. -/
theorem radix8_counts :
    blindingDegree 17 window radix = 148 ∧ blindingDegree 15 window radix = 132 ∧
      blindingDegree 14 window radix = 124 ∧ blindingDegree 13 window radix = 116 := by
  decide

/-! ### The `fri8` shapes: radix 8, window 2, t = 2^13, constraint degree 11

The wallet sizes the blinding with `1 << FRI_FOLD_LOG` (`nox_prover::api`),
which is 8 under `fri8`, so a query opens a coset of eight points. -/

def radix8 : Nat := 8

/-- Revealed evaluations and random coefficients per column, for A (19
queries), A' (18) and B (17). -/
theorem query_shape_counts :
    (revealed 19 window radix8 = 308 ∧ blindingDegree 19 window radix8 + 1 = 317) ∧
      (revealed 18 window radix8 = 292 ∧ blindingDegree 18 window radix8 + 1 = 301) ∧
      (revealed 17 window radix8 = 276 ∧ blindingDegree 17 window radix8 + 1 = 285) := by
  decide

/-- At radix 8 the blinding keeps the composition under its bound up to 45
queries, where radix 4 reached 91. -/
theorem radix8_fits_up_to_45 (q : Nat) (h : q ≤ 45) :
    fits (blindingDegree q window radix8) constraintDegree t window := by
  unfold fits blindingDegree radix8 window constraintDegree t margin
  omega

theorem radix8_fits_stops_at_46 : ¬ fits (blindingDegree 46 window radix8) constraintDegree t window := by
  decide

/-- The mask columns are uniform of degree below B = 2^17 (`hide_at`), far above
any count here. -/
theorem mask_degree_covers (q : Nat) (h : q ≤ 91) : revealed q window radix < boundB - 1 := by
  unfold revealed radix window boundB
  omega

/-! ### The rank condition's bound at every query count (docs/12 4.4)

The mask's openings A are `r w q` rows and two frame values; FRI past layer
zero reveals 3 layers of `r` values per query and the final layer's 512
coefficients, and the minor's rank is at most that count. Each F row has degree
at most e = (B - 1) + 86 + 12 in the challenges, the frame rows B - 1. -/

def e : Nat := (boundB - 1) + 86 + 12
def fRows (q : Nat) : Nat := 3 * radix * q + 512
def minorDegree (q : Nat) : Nat := 2 * (boundB - 1) + fRows q * e

theorem launch_f_rows : fRows 19 = 740 := by decide

/-- The launch's measured rank, 664, is under the row count, so the bound with
all 740 rows is the weaker one and still below 2^-100. -/
theorem launch_rank_bound : minorDegree 19 * 2 ^ 100 < Shield.Launch.p ^ 2 := by decide

/-- The degree only falls with fewer queries. -/
theorem minor_degree_monotone (q : Nat) (h : q ≤ 19) : minorDegree q ≤ minorDegree 19 := by
  unfold minorDegree fRows
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by unfold radix; omega)) _

/-- So (R) fails with probability below 2^-100 at every query count up to the
launch's, the `fri8` points included. -/
theorem rank_bound_every_point (q : Nat) (h : q ≤ 19) : minorDegree q * 2 ^ 100 < Shield.Launch.p ^ 2 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (minor_degree_monotone q h)) launch_rank_bound

end Shield.Masking
