-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Layout
import Shield.Stop

/-!
FRI at radix two, four and eight over the same bound and stop.

A radix-four layer is two radix-two halvings under one leaf: four values and one path where
radix two sends two values and a path per halving. Fewer paths is the whole saving, and the
final polynomial it pays for is what the odd halving count leaves over. Everything is `Nat`,
core only.
-/

namespace Shield.Radix

open Shield.Layout

/-- The shippedFour point at another fold. -/
def atFold (p : Params) (f : Nat) : Params := { p with foldLog := f }

theorem at_fold_two_is_shipped : atFold shippedFour 2 = shippedFour := by decide

theorem at_fold_keeps_the_bound (p : Params) (f : Nat) : logBound (atFold p f) = logBound p := rfl

theorem at_fold_keeps_the_domain (p : Params) (f : Nat) :
    logDomain (atFold p f) = logDomain p := rfl

theorem at_fold_keeps_the_stop (p : Params) (f : Nat) : (atFold p f).stopLog = p.stopLog := rfl

/-! ## Layers and final at the shippedFour point -/

theorem layers_by_fold :
    layers (atFold shippedFour 1) = 13 ∧ layers (atFold shippedFour 2) = 6 ∧
    layers (atFold shippedFour 3) = 4 := by decide

theorem finals_by_fold :
    finalLog (atFold shippedFour 1) = 8 ∧ finalLog (atFold shippedFour 2) = 9 ∧
    finalLog (atFold shippedFour 3) = 9 := by decide

/-- Halvings taken by the layers: layers times fold. -/
def halvings (p : Params) : Nat := layers p * p.foldLog

theorem halvings_by_fold :
    halvings (atFold shippedFour 1) = 13 ∧ halvings (atFold shippedFour 2) = 12 ∧
    halvings (atFold shippedFour 3) = 12 := by decide

/-- Radix two meets the stop exactly; radix four and eight leave one halving to the final. -/
theorem only_radix_two_meets_the_stop :
    finalLog (atFold shippedFour 1) = shippedFour.stopLog ∧
    finalLog (atFold shippedFour 2) = shippedFour.stopLog + 1 ∧
    finalLog (atFold shippedFour 3) = shippedFour.stopLog + 1 := by decide

theorem finals_in_coefficients :
    2 ^ finalLog (atFold shippedFour 1) = 256 ∧ 2 ^ finalLog (atFold shippedFour 2) = 512 ∧
    2 ^ finalLog (atFold shippedFour 3) = 512 := by decide

/-! ## General facts -/

/-- At radix two the layer count is the halvings the stop leaves. -/
theorem radix_two_layers (p : Params) (h : 1 ≤ logBound p - p.stopLog) :
    layers (atFold p 1) = logBound p - p.stopLog := by
  have e : layers (atFold p 1) = max 1 ((logBound p - p.stopLog) / 1) := rfl
  have h1 : 1 ≤ (logBound p - p.stopLog) / 1 := by omega
  rw [e, Nat.max_eq_right h1]
  omega

/-- Radix four never takes more halvings than radix two. -/
theorem radix_four_takes_no_more_halvings (p : Params) (h : 2 ≤ logBound p - p.stopLog) :
    layers (atFold p 2) * 2 ≤ layers (atFold p 1) * 1 := by
  have e2 : layers (atFold p 2) = max 1 ((logBound p - p.stopLog) / 2) := rfl
  have e1 : layers (atFold p 1) = max 1 ((logBound p - p.stopLog) / 1) := rfl
  have h2 : 1 ≤ (logBound p - p.stopLog) / 2 := by omega
  have h1 : 1 ≤ (logBound p - p.stopLog) / 1 := by omega
  rw [e2, e1, Nat.max_eq_right h2, Nat.max_eq_right h1]
  omega

/-- With one halving left the inequality fails: radix four still folds once, taking two. -/
theorem one_halving_left_breaks_it :
    layers (atFold { shippedFour with stopLog := 20 } 2) * 2 = 2 ∧
    layers (atFold { shippedFour with stopLog := 20 } 1) * 1 = 1 := by decide

/-- Radix four is short by at most one halving. -/
theorem radix_four_is_short_by_at_most_one (p : Params) (h : 2 ≤ logBound p - p.stopLog) :
    layers (atFold p 1) * 1 ≤ layers (atFold p 2) * 2 + 1 := by
  have e2 : layers (atFold p 2) = max 1 ((logBound p - p.stopLog) / 2) := rfl
  have e1 : layers (atFold p 1) = max 1 ((logBound p - p.stopLog) / 1) := rfl
  have h2 : 1 ≤ (logBound p - p.stopLog) / 2 := by omega
  have h1 : 1 ≤ (logBound p - p.stopLog) / 1 := by omega
  rw [e2, e1, Nat.max_eq_right h2, Nat.max_eq_right h1]
  omega

/-- At any fold the layers and the final together take the whole bound. -/
theorem halvings_and_final_are_the_bound (p : Params) (f : Nat) (h : f ≤ logBound p) :
    layers (atFold p f) * f + finalLog (atFold p f) = logBound p :=
  Shield.Stop.the_final_is_what_is_left (atFold p f) h

theorem layers_take_their_share_at_any_fold (p : Params) (f : Nat) (h : f ≤ logBound p) :
    layers (atFold p f) * f ≤ logBound p :=
  Shield.Stop.layers_take_their_share (atFold p f) h

/-- Folding cannot change the layer count's floor of one. -/
theorem at_least_one_layer_at_any_fold (p : Params) (f : Nat) : 1 ≤ layers (atFold p f) :=
  Shield.Stop.at_least_one_layer (atFold p f)

/-! ## Bytes per layer -/

/-- A radix `2^f` layer's values: `2^f` of them at sixteen bytes. -/
theorem layer_values_by_fold :
    16 * 2 ^ (atFold shippedFour 1).foldLog = 32 ∧ 16 * 2 ^ (atFold shippedFour 2).foldLog = 64 ∧
    16 * 2 ^ (atFold shippedFour 3).foldLog = 128 := by decide

theorem radix_two_depths :
    friDepth (atFold shippedFour 1) 0 = 28 ∧ friDepth (atFold shippedFour 1) 12 = 16 := by decide

theorem radix_eight_depths :
    [friDepth (atFold shippedFour 3) 0, friDepth (atFold shippedFour 3) 1,
     friDepth (atFold shippedFour 3) 2, friDepth (atFold shippedFour 3) 3] = [26, 23, 20, 17] := by
  decide

theorem radix_two_layer_bytes :
    layerBytes (atFold shippedFour 1) 0 = 708 ∧ layerBytes (atFold shippedFour 1) 12 = 420 := by decide

/-- Two radix-two layers against the one radix-four layer that replaces them. -/
theorem the_first_pair :
    layerBytes (atFold shippedFour 1) 0 + layerBytes (atFold shippedFour 1) 1 = 1392 ∧
    layerBytes (atFold shippedFour 2) 0 = 716 := by decide

/-- In general a pair of radix-two layers costs one radix-four layer plus one more path. -/
theorem a_pair_is_a_quad_plus_a_path (q : Params) (d : Nat) :
    (16 * 2 + pathBytes q (d + 1)) + (16 * 2 + pathBytes q d) =
      (16 * 4 + pathBytes q d) + pathBytes q (d + 1) := by
  unfold pathBytes
  omega

/-- That path is the deeper of the two, so the saving grows with depth. -/
theorem the_path_saved (q : Params) (d : Nat) : pathBytes q (d + 1) = pathBytes q d + q.digest := by
  unfold pathBytes
  have e : q.digest * (d + 1) = q.digest * d + q.digest := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Three radix-two layers cost one radix-eight layer plus two paths, less the 32 extra value
bytes the radix-eight leaf carries. -/
theorem a_triple_is_an_octet_plus_two_paths (q : Params) (d : Nat) :
    (16 * 2 + pathBytes q (d + 2)) + (16 * 2 + pathBytes q (d + 1)) +
        (16 * 2 + pathBytes q d) + 32 =
      (16 * 8 + pathBytes q d) + pathBytes q (d + 1) + pathBytes q (d + 2) := by
  unfold pathBytes
  omega

theorem the_first_pair_saves : 1392 - 716 = pathBytes shippedFour 28 := by decide

/-! ## Bytes per query -/

theorem radix_two_stride : friStride (atFold shippedFour 1) = 7336 := by decide

theorem radix_four_stride : friStride (atFold shippedFour 2) = 3580 := by decide

theorem radix_eight_stride : friStride (atFold shippedFour 3) = 2596 := by decide

theorem radix_four_is_smaller_per_query :
    friStride (atFold shippedFour 2) < friStride (atFold shippedFour 1) := by decide

theorem radix_eight_is_smaller_again :
    friStride (atFold shippedFour 3) < friStride (atFold shippedFour 2) := by decide

/-- The per-query saving of radix four over radix two. -/
theorem saving_per_query : friStride (atFold shippedFour 1) - friStride (atFold shippedFour 2) = 3756 := by
  decide

theorem saving_over_the_queries :
    shippedFour.queries * (friStride (atFold shippedFour 1) - friStride (atFold shippedFour 2)) = 45072 := by
  decide

/-- Radix four sends under half the FRI bytes per query of radix two. -/
theorem radix_four_under_half :
    2 * friStride (atFold shippedFour 2) < friStride (atFold shippedFour 1) := by
  decide

/-! ## The head pays some of it back -/

theorem heads_by_fold :
    head (atFold shippedFour 1) = 5832 ∧ head (atFold shippedFour 2) = 9760 ∧
    head (atFold shippedFour 3) = 9712 := by decide

/-- Radix four sends 256 more final coefficients and seven fewer roots. -/
theorem the_head_difference :
    head (atFold shippedFour 2) - head (atFold shippedFour 1) = 3928 ∧ 256 * 16 - 7 * 24 = 3928 := by
  decide

theorem totals_by_fold :
    total (atFold shippedFour 1) = 153484 ∧ total (atFold shippedFour 2) = 112436 ∧
    total (atFold shippedFour 3) = 101060 := by decide

/-- The net saving is the query saving less the head difference. -/
theorem the_net_saving :
    total (atFold shippedFour 1) - total (atFold shippedFour 2) = 41048 ∧ 44976 - 3928 = 41048 := by
  decide

/-- Radix two does not fit under the ceiling at this point; radix four does. -/
theorem radix_two_is_over_the_ceiling :
    131072 < total (atFold shippedFour 1) ∧ total (atFold shippedFour 2) ≤ 131072 := by decide

/-- Radix eight fits too, and is smaller still. -/
theorem radix_eight_fits : total (atFold shippedFour 3) < total (atFold shippedFour 2) := by decide

end Shield.Radix
