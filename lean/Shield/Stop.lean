-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
FRI stops early: the last `stopLog` halvings are replaced by sending the final
polynomial's coefficients once in the head, and every query evaluates it by
Horner. The layer count and the final size come from the degree bound, not the
rate, so they do not move when the domain does. Mirrors fri/stop.rs.
-/

namespace Shield.Stop

open Shield.Layout

theorem at_least_one_layer (p : Params) : 1 ≤ layers p := by
  unfold layers
  exact Nat.le_max_left _ _

theorem layers_take_their_share (p : Params) (hb : p.foldLog ≤ logBound p) :
    layers p * p.foldLog ≤ logBound p := by
  unfold layers
  have h1 : (logBound p - p.stopLog) / p.foldLog * p.foldLog ≤ logBound p - p.stopLog :=
    Nat.div_mul_le_self _ _
  rcases Nat.le_total 1 ((logBound p - p.stopLog) / p.foldLog) with h | h
  · rw [Nat.max_eq_right h]
    omega
  · rw [Nat.max_eq_left h]
    omega

/-- what the layers do not take is the final polynomial -/
theorem the_final_is_what_is_left (p : Params) (hb : p.foldLog ≤ logBound p) :
    layers p * p.foldLog + finalLog p = logBound p := by
  have := layers_take_their_share p hb
  unfold finalLog
  omega

/-- the layer count does not depend on the rate -/
theorem layers_ignore_the_rate (p : Params) (e : Nat) :
    layers { p with extraBlowup := e } = layers p := rfl

theorem the_final_ignores_the_rate (p : Params) (e : Nat) :
    finalLog { p with extraBlowup := e } = finalLog p := rfl

/-- the tree depths do -/
theorem depths_follow_the_rate (p : Params) (e : Nat) :
    treeDepth { p with extraBlowup := e } = logBound p + 1 + e := rfl

/-! the shippedFour point: stop 8 -/

theorem shipped_shape : layers shippedFour = 6 ∧ finalLog shippedFour = 9 := by decide

/-- the halvings the stop leaves, 21 - 8 = 13, are odd, so radix four overshoots by one and
the final polynomial is 512 rather than 256 coefficients -/
theorem radix_four_overshoots_the_stop :
    logBound shippedFour - shippedFour.stopLog = 13 ∧ 2 ^ finalLog shippedFour = 512 ∧
    2 ^ shippedFour.stopLog = 256 := by decide

theorem at_radix_two_the_stop_is_met : finalLog { shippedFour with foldLog := 1 } = 8 := by decide

/-- Horner steps a verifier pays: coefficients times queries -/
def hornerSteps (p : Params) : Nat := p.queries * 2 ^ finalLog p

theorem shipped_horner_steps : hornerSteps shippedFour = 6144 := by decide

/-! stop 6: one more layer, a quarter of the coefficients -/

def stopSix : Params := { shippedFour with stopLog := 6 }

theorem stop_six_shape : layers stopSix = 7 ∧ finalLog stopSix = 7 := by decide

theorem stop_six_horner_steps : hornerSteps stopSix = 1536 := by decide

theorem stop_six_is_smaller : total stopSix = 111452 ∧ total shippedFour - total stopSix = 984 := by
  decide

theorem stop_six_saves_horner_steps : hornerSteps shippedFour - hornerSteps stopSix = 4608 := by decide

/-- the seventh layer is fifteen deep and costs each query 428 bytes -/
theorem the_seventh_layer :
    friDepth stopSix 6 = 15 ∧ layerBytes stopSix 6 = 428 := by decide

/-- where the 984 comes from: 384 fewer coefficients at 16 bytes, one more root, twelve more layers -/
theorem the_saving_accounted :
    (512 - 128) * 16 = 6144 ∧ 6144 - 24 - 12 * 428 = 984 := by decide

theorem stop_six_keeps_the_soundness_point :
    stopSix.queries = shippedFour.queries ∧ stopSix.extraBlowup = shippedFour.extraBlowup := by decide

theorem stop_six_keeps_the_domain : logDomain stopSix = logDomain shippedFour := by decide

/-! the stop cannot be driven past the bound -/

theorem a_stop_past_the_bound_still_folds_once (p : Params) (h : logBound p ≤ p.stopLog) :
    layers p = 1 := by
  unfold layers
  have : logBound p - p.stopLog = 0 := by omega
  rw [this, Nat.zero_div]
  decide

theorem a_zero_fold_means_no_final (p : Params) (h : p.foldLog = 0) :
    finalLog p = logBound p := by
  unfold finalLog
  rw [h, Nat.mul_zero, Nat.sub_zero]

/-! the sweep the search runs -/

def atStop (s : Nat) : Params := { shippedFour with stopLog := s }

theorem the_sweep_of_layers :
    [layers (atStop 0), layers (atStop 2), layers (atStop 4), layers (atStop 6),
     layers (atStop 8), layers (atStop 10)] = [10, 9, 8, 7, 6, 5] := by decide

theorem the_sweep_of_finals :
    [2 ^ finalLog (atStop 0), 2 ^ finalLog (atStop 2), 2 ^ finalLog (atStop 4),
     2 ^ finalLog (atStop 6), 2 ^ finalLog (atStop 8), 2 ^ finalLog (atStop 10)] =
      [2, 8, 32, 128, 512, 2048] := by decide

/-- stops up to nine keep the proof under the ceiling -/
theorem the_sweep_fits : ∀ s < 10, total (atStop s) ≤ 131072 := by decide

/-- ten and eleven leave 2048 coefficients in the head and put it 204 bytes over -/
theorem stop_ten_does_not_fit :
    total (atStop 10) = 131276 ∧ 131072 < total (atStop 10) ∧ total (atStop 11) = 131276 := by
  decide

/-- stop 6 is the smallest proof in the sweep -/
theorem stop_six_is_the_smallest_in_the_sweep : ∀ s < 12, total stopSix ≤ total (atStop s) := by
  decide

end Shield.Stop
