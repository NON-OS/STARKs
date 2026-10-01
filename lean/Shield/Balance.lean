-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Conservation across a two in two out payment, over `Nat`, so no subtraction
underflows into a value the circuit would have to catch separately.
-/

namespace Shield.Balance

structure Spend where
  inA : Nat
  inB : Nat
  outA : Nat
  outB : Nat
  publicAmount : Nat
  fee : Nat
  deriving DecidableEq

/-- Inputs sum to outputs plus what leaves the pool plus the fee. -/
def balanced (s : Spend) : Prop :=
  s.inA + s.inB = s.outA + s.outB + s.publicAmount + s.fee

theorem no_value_is_created (s : Spend) (h : balanced s) :
    s.outA + s.outB ≤ s.inA + s.inB := by
  simp only [balanced] at h
  omega

theorem nothing_leaves_beyond_the_inputs (s : Spend) (h : balanced s) :
    s.publicAmount + s.fee ≤ s.inA + s.inB := by
  simp only [balanced] at h
  omega

/-- A transfer takes nothing out, so the notes on both sides hold the same
total and the amount is never a public number. -/
theorem a_transfer_conserves (s : Spend) (h : balanced s)
    (hp : s.publicAmount = 0) (hf : s.fee = 0) :
    s.inA + s.inB = s.outA + s.outB := by
  simp only [balanced] at h
  omega

/-- A dummy input carries zero, so the shape costs nothing: two inputs with
one dummy balance exactly as one input would. -/
theorem a_dummy_input_adds_nothing (s : Spend) (h : balanced s) (hd : s.inB = 0) :
    s.inA = s.outA + s.outB + s.publicAmount + s.fee := by
  simp only [balanced] at h
  omega

/-- A dummy output is a real commitment holding nothing, so change is the
whole remainder. -/
theorem change_is_the_remainder (s : Spend) (h : balanced s) (hd : s.outB = 0) :
    s.outA = s.inA + s.inB - (s.publicAmount + s.fee) := by
  simp only [balanced] at h
  omega

end Shield.Balance
