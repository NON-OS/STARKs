-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Gas against the number of pieces the one-call verifier is given, measured on
the shipped proof after the six fixes. The first twelve pieces are base
queries, the next twelve are FRI queries. The marginal cost of a piece rises
across the walk, which is the memory term at its remaining amplitude.
-/

namespace Shield.Curve

/-- gas with the first `k` pieces, from the gas test -/
def total : Nat → Nat
  | 0 => 1961704
  | 12 => 4688018
  | 16 => 6260089
  | 20 => 8049382
  | 24 => 10139687
  | _ => 0

def head : Nat := total 0

def work (k : Nat) : Nat := total k - head

theorem head_decode : head = 1961704 := by decide

theorem work_at_the_measured_points :
    work 12 = 2726314 ∧ work 16 = 4298385 ∧ work 20 = 6087678 ∧ work 24 = 8177983 := by decide

/-- gas a piece, between consecutive measured points -/
def marginal (a b : Nat) : Nat := (work b - work a) / (b - a)

theorem the_base_half : marginal 0 12 = 227192 := by decide

theorem the_fri_half :
    marginal 12 16 = 393017 ∧ marginal 16 20 = 447323 ∧ marginal 20 24 = 522576 := by decide

theorem marginals_rise :
    marginal 0 12 < marginal 12 16 ∧ marginal 12 16 < marginal 16 20 ∧
    marginal 16 20 < marginal 20 24 := by decide

/-- the last pieces cost more than twice the first -/
theorem the_last_pieces_cost_over_twice_the_first : 2 * marginal 0 12 < marginal 20 24 := by decide

/-- linear extrapolation from the base half undershoots the whole walk by 2.7M -/
theorem linear_extrapolation_undershoots :
    24 * marginal 0 12 = 5452608 ∧ work 24 - 24 * marginal 0 12 = 2725375 := by decide

/-- the excess is a third of the walk, to within two thousand gas -/
theorem the_walk_is_a_third_superlinear :
    3 * (work 24 - 24 * marginal 0 12) ≤ work 24 ∧
    work 24 < 3 * (work 24 - 24 * marginal 0 12) + 2000 := by decide

/-- the base half costs the same as it did before any fix; the FRI half is where the fixes landed -/
theorem the_base_half_is_flat : work 12 / 12 = 227192 := by decide

theorem base_queries_are_cheaper_than_fri_queries : work 12 < work 24 - work 12 := by decide

/-- a FRI query, at the end of the walk, against a base query at the start -/
theorem a_fri_query_at_the_end : (work 24 - work 20) / 4 = 522576 := by decide

/-! what the curve says a streaming reader would remove -/

/-- if every piece cost what the first twelve do -/
def flatWork (k : Nat) : Nat := k * marginal 0 12

theorem the_superlinear_excess : work 24 - flatWork 24 = 2725375 := by decide

theorem the_excess_is_a_quarter_of_the_verification :
    4 * (work 24 - flatWork 24) < total 24 + 1000000 ∧ 4 * (work 24 - flatWork 24) > total 24 := by
  decide

/-! general: rising marginals put the total above the line through the first point -/

/-- a walk whose per-piece cost never falls: `cost i ≤ cost j` for `i ≤ j` -/
def sumTo (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo cost k + cost k

theorem sumTo_succ (cost : Nat → Nat) (k : Nat) : sumTo cost (k + 1) = sumTo cost k + cost k := rfl

theorem rising_costs_exceed_the_first_line (cost : Nat → Nat) (h : ∀ i, cost 0 ≤ cost i) :
    ∀ k, k * cost 0 ≤ sumTo cost k := by
  intro k
  induction k with
  | zero => simp [sumTo]
  | succ k ih =>
    rw [sumTo_succ, Nat.succ_mul]
    have := h k
    omega

theorem a_flat_walk_is_the_line (c : Nat) : ∀ k, sumTo (fun _ => c) k = k * c := by
  intro k
  induction k with
  | zero => simp only [sumTo, Nat.zero_mul]
  | succ k ih => rw [sumTo_succ, ih, Nat.succ_mul]

/-- the measured walk is not flat: its total is above the line by the excess above -/
theorem the_measured_walk_is_not_flat : flatWork 24 < work 24 := by decide

/-! the old verifier, same experiment, program form at 32 queries -/

def oldTotal : Nat → Nat
  | 0 => 1675086
  | 8 => 3302245
  | 16 => 5176199
  | 24 => 7605848
  | 32 => 11038494
  | 40 => 20451964
  | 48 => 34862856
  | 56 => 55690236
  | 64 => 96377651
  | _ => 0

def oldMarginal (a b : Nat) : Nat := (oldTotal b - oldTotal a) / (b - a)

theorem old_marginals :
    oldMarginal 0 8 = 203394 ∧ oldMarginal 24 32 = 429080 ∧ oldMarginal 56 64 = 5085926 := by
  decide

/-- twenty five fold across identical work -/
theorem the_old_walk_rose_twenty_five_fold : 25 * oldMarginal 0 8 ≤ oldMarginal 56 64 := by decide

/-- the fixes took the whole walk from 96M to 10M at the same query count -/
theorem what_the_fixes_took : oldTotal 64 / total 24 ≥ 9 := by decide

theorem the_old_head_and_the_new : oldTotal 0 = 1675086 ∧ head = 1961704 := by decide

end Shield.Curve
