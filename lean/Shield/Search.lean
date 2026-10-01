-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout
import Shield.Params

/-!
Which parameter points are admissible: provable soundness at or above the
floor, bytes under the ceiling, a domain the field and the prover can hold,
grinding a prover will do. Mirrors budget/search.rs. The point we ship is
one of eighty; the search says which others are worth the proving time.
-/

namespace Shield.Search

open Shield.Layout

structure Limits where
  minProvable : Nat
  maxBytes : Nat
  maxGrind : Nat
  maxLogDomain : Nat
  deriving DecidableEq

def defaults : Limits :=
  { minProvable := 80, maxBytes := 131072, maxGrind := 32, maxLogDomain := 30 }

/-- the circuit is fixed; a point moves queries, grind, rate, stop and fold -/
structure Point where
  queries : Nat
  grind : Nat
  extraBlowup : Nat
  stopLog : Nat
  foldLog : Nat
  deriving DecidableEq

def circuit : Params := shippedFour

def paramsAt (pt : Point) : Params :=
  { circuit with
    queries := pt.queries, extraBlowup := pt.extraBlowup, stopLog := pt.stopLog,
    foldLog := pt.foldLog }

def soundness (pt : Point) : Params.Point := ⟨pt.queries, pt.grind, pt.extraBlowup⟩

def provable (pt : Point) : Nat := Params.provable (soundness pt)
def conjectured (pt : Point) : Nat := Params.conjectured (soundness pt)
def bytes (pt : Point) : Nat := total (paramsAt pt)
def domain (pt : Point) : Nat := logDomain (paramsAt pt)

/-- the fold radix the prover implements -/
def implementedFold : Nat := 2

def admissible (l : Limits) (pt : Point) : Prop :=
  l.minProvable ≤ provable pt ∧ bytes pt ≤ l.maxBytes ∧ pt.grind ≤ l.maxGrind ∧
    domain pt ≤ l.maxLogDomain ∧ pt.foldLog = implementedFold ∧ 1 ≤ layers (paramsAt pt)

instance (l : Limits) (pt : Point) : Decidable (admissible l pt) := by
  unfold admissible; infer_instance

/-! the points in the table -/

def shippedPoint : Point := ⟨12, 32, 7, 8, 2⟩
def stopSix : Point := ⟨12, 32, 7, 6, 2⟩
def stopFour : Point := ⟨12, 32, 7, 4, 2⟩
def fourteenAtSeven : Point := ⟨14, 32, 6, 6, 2⟩
def fourteenAtSevenStopEight : Point := ⟨14, 32, 6, 8, 2⟩
def sixteenAtSix : Point := ⟨16, 32, 5, 4, 2⟩
def radixEight : Point := ⟨16, 32, 5, 4, 3⟩
def sixQueries : Point := ⟨6, 32, 7, 8, 2⟩
def grindForty : Point := ⟨10, 40, 7, 8, 2⟩

theorem the_shipped_point_is_admissible : admissible defaults shippedPoint := by decide

theorem the_shipped_point_measures :
    provable shippedPoint = 80 ∧ conjectured shippedPoint = 128 ∧
    bytes shippedPoint = 112436 ∧ domain shippedPoint = 29 := by decide

/-- same soundness, same domain, fewer bytes -/
theorem stop_six_dominates_the_shipped_point :
    admissible defaults stopSix ∧ provable stopSix = provable shippedPoint ∧
    domain stopSix = domain shippedPoint ∧ bytes stopSix < bytes shippedPoint := by decide

theorem stop_six_bytes : bytes stopSix = 111452 := by decide

theorem stop_four_is_admissible_and_larger :
    admissible defaults stopFour ∧ bytes stopFour = 114500 := by decide

/-- the candidate that halves the domain -/
theorem fourteen_at_seven :
    admissible defaults fourteenAtSeven ∧ provable fourteenAtSeven = 81 ∧
    domain fourteenAtSeven = 28 ∧ bytes fourteenAtSeven = 125068 := by decide

theorem fourteen_at_seven_stop_eight :
    admissible defaults fourteenAtSevenStopEight ∧ bytes fourteenAtSevenStopEight = 125532 := by
  decide

/-- sixteen queries at rate exponent six clear the floor but not the byte ceiling at radix four -/
theorem sixteen_at_six_does_not_fit :
    provable sixteenAtSix = 80 ∧ domain sixteenAtSix = 27 ∧ 131072 < bytes sixteenAtSix := by
  decide

/-- radix eight fits and proves fastest, and the prover does not implement it -/
theorem radix_eight_is_not_admissible_by_default :
    ¬ admissible defaults radixEight ∧ provable radixEight = 80 ∧ domain radixEight = 27 ∧
    bytes radixEight = 123532 := by decide

theorem radix_eight_fails_on_the_fold_alone :
    80 ≤ provable radixEight ∧ bytes radixEight ≤ 131072 ∧ radixEight.grind ≤ 32 ∧
    domain radixEight ≤ 30 ∧ radixEight.foldLog ≠ implementedFold := by decide

/-- six queries reach eighty only under the conjecture -/
theorem six_queries_are_refused :
    ¬ admissible defaults sixQueries ∧ conjectured sixQueries = 80 ∧ provable sixQueries = 56 := by
  decide

/-- more grind than a prover will do -/
theorem grind_forty_is_refused :
    ¬ admissible defaults grindForty ∧ provable grindForty = 80 := by decide

/-! what admissibility guarantees -/

theorem admissible_clears_the_floor (l : Limits) (pt : Point) (h : admissible l pt) :
    l.minProvable ≤ provable pt := h.1

theorem admissible_fits_the_ceiling (l : Limits) (pt : Point) (h : admissible l pt) :
    bytes pt ≤ l.maxBytes := h.2.1

theorem admissible_folds_at_least_once (l : Limits) (pt : Point) (h : admissible l pt) :
    1 ≤ layers (paramsAt pt) := h.2.2.2.2.2

theorem admissible_is_the_implemented_radix (l : Limits) (pt : Point) (h : admissible l pt) :
    pt.foldLog = 2 := h.2.2.2.2.1

/-- provable soundness never exceeds conjectured -/
theorem provable_le_conjectured (pt : Point) : provable pt ≤ conjectured pt :=
  Params.provable_le_conjectured (soundness pt)

/-- the floor is checked on the provable figure, so a point admitted under defaults is at
eighty provable bits, not merely eighty conjectured -/
theorem admitted_means_eighty_provable (pt : Point) (h : admissible defaults pt) :
    80 ≤ provable pt := h.1

/-- raising the floor only removes points -/
theorem a_higher_floor_admits_fewer (l : Limits) (pt : Point) (m : Nat)
    (h : admissible { l with minProvable := m } pt) (hm : l.minProvable ≤ m) :
    admissible l pt := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.le_trans hm h1, h2, h3, h4, h5, h6⟩

/-- a lower byte ceiling only removes points -/
theorem a_lower_ceiling_admits_fewer (l : Limits) (pt : Point) (b : Nat)
    (h : admissible { l with maxBytes := b } pt) (hb : b ≤ l.maxBytes) :
    admissible l pt := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, Nat.le_trans h2 hb, h3, h4, h5, h6⟩

/-! the sweep at the shippedFour domain -/

def atStop (s : Nat) : Point := ⟨12, 32, 7, s, 2⟩

theorem every_stop_below_ten_is_admissible : ∀ s < 10, admissible defaults (atStop s) := by
  decide

/-- stop ten fails on bytes alone -/
theorem stop_ten_is_refused : ¬ admissible defaults (atStop 10) ∧ bytes (atStop 10) = 131276 := by
  decide

theorem stop_six_is_the_smallest : ∀ s < 12, bytes stopSix ≤ bytes (atStop s) := by decide

theorem stops_pair_up :
    bytes (atStop 6) = bytes (atStop 7) ∧ bytes (atStop 8) = bytes (atStop 9) ∧
    bytes (atStop 4) = bytes (atStop 5) := by decide

/-! the sweep over the rate at twelve queries: only exponent eight clears the floor -/

def atRate (e : Nat) : Point := ⟨12, 32, e, 8, 2⟩

theorem below_eight_twelve_queries_are_short : ∀ e < 7, ¬ admissible defaults (atRate e) := by
  decide

theorem at_nine_the_domain_is_over : domain (atRate 8) = 30 ∧ domain (atRate 9) = 31 := by decide

theorem rate_eight_is_the_only_admissible_rate_at_twelve :
    ∀ e < 12, admissible defaults (atRate e) ↔ e = 7 ∨ e = 8 := by decide

/-! the search's stated ranking key: proving cost first -/

/-- relative proving work, n log n over the shippedFour domain, in parts per thousand -/
def provingPermille (pt : Point) : Nat :=
  (2 ^ domain pt * domain pt * 1000) / (2 ^ 29 * 29)

theorem the_shipped_point_is_the_baseline : provingPermille shippedPoint = 1000 := by decide

theorem fourteen_at_seven_halves_the_work : provingPermille fourteenAtSeven = 482 := by decide

theorem radix_eight_would_quarter_it : provingPermille radixEight = 232 := by decide

end Shield.Search
