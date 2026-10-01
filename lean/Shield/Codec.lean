-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
Two real artifacts, one layout. The program-form proof of 21 September was
radix two with 24-byte digests at 32 queries and rate exponent four; the
one-transaction proof of 22 September is radix four at 12 queries and rate
exponent eight. The same equations end on the last byte of both.
-/

namespace Shield.Codec

open Shield.Layout

/-- spec/program-1: 32 queries, extra blowup 3, radix two, stop 8 -/
def programOne : Params :=
  { queries := 32, extraBlowup := 3, foldLog := 1, stopLog := 8, digest := 24,
    width := 41, periodic := 119, logTrace := 18, degreeLog := 3, window := 2, format := 3 }

theorem program_one_shape :
    logDomain programOne = 25 ∧ layers programOne = 13 ∧ 2 ^ finalLog programOne = 256 ∧
    treeDepth programOne = 25 := by decide

theorem program_one_strides :
    friStride programOne = 6088 ∧ consStride programOne = 2176 ∧
    sidecarStride programOne = 1556 ∧ permStride programOne = 604 := by decide

theorem program_one_head : head programOne = 5832 := by decide

/-- the artifact is 341,324 bytes -/
theorem program_one_closes : total programOne = 341324 := by decide

theorem program_one_fri_depths :
    [friDepth programOne 0, friDepth programOne 1, friDepth programOne 12] = [24, 23, 12] := by
  decide

/-- the same circuit at the same point, folded four at a time, would have been 246,564 bytes -/
theorem program_one_at_radix_four :
    total { programOne with foldLog := 2 } = 246564 ∧
    layers { programOne with foldLog := 2 } = 6 := by decide

theorem radix_four_would_have_saved_a_quarter :
    4 * (total programOne - total { programOne with foldLog := 2 }) > total programOne := by
  decide

/-! the two artifacts against each other -/

theorem the_circuit_is_the_same :
    programOne.width = shippedFour.width ∧ programOne.periodic = shippedFour.periodic ∧
    programOne.logTrace = shippedFour.logTrace ∧ programOne.degreeLog = shippedFour.degreeLog ∧
    programOne.window = shippedFour.window ∧ programOne.digest = shippedFour.digest := by decide

theorem the_point_is_not :
    programOne.queries ≠ shippedFour.queries ∧ programOne.extraBlowup ≠ shippedFour.extraBlowup ∧
    programOne.foldLog ≠ shippedFour.foldLog := by decide

theorem the_bound_is_shared : logBound programOne = logBound shippedFour := rfl

/-- four more blowup bits, four more levels in every tree -/
theorem four_more_levels : treeDepth shippedFour = treeDepth programOne + 4 := by decide

/-- a third of the queries, a third of the sections -/
theorem a_third_of_the_queries : 3 * shippedFour.queries - programOne.queries = 4 := by decide

theorem shipped_is_a_third_the_size : 3 * total shippedFour < total programOne := by decide

/-- per query, the one-transaction proof is larger: deeper trees at a higher rate -/
theorem per_query_the_shipped_proof_is_larger :
    consStride programOne < consStride shippedFour ∧ permStride programOne < permStride shippedFour := by
  decide

/-- and its FRI half is smaller: half the layers -/
theorem but_its_fri_half_is_smaller : friStride shippedFour < friStride programOne := by decide

/-! what the codec versions changed -/

/-- v1.1: 32-byte digests, radix two, folded to a constant; v1.2: 24, radix four, early stop -/
def v11 : Params := { programOne with digest := 32, stopLog := 0 }

theorem v11_folds_to_the_end : 2 ^ finalLog v11 = 1 ∧ layers v11 = 21 := by decide

theorem v11_is_the_largest : total programOne < total v11 := by decide

theorem v11_program_one_bytes : total v11 = 500196 := by decide

/-- digests are most of a proof: the 32 to 24 move alone -/
theorem the_digest_move :
    total { programOne with digest := 32 } - total programOne = 92040 := by decide

theorem the_digest_move_is_over_a_quarter :
    4 * (total { programOne with digest := 32 } - total programOne) > total programOne := by
  decide

/-- the early stop: from folding to a constant to 256 coefficients, at radix two -/
theorem the_early_stop_move :
    total { programOne with stopLog := 0 } - total programOne = 51408 := by decide

/-! the three moves together, from the oldest form to the shippedFour one -/

def oldest : Params := { shippedFour with digest := 32, foldLog := 1, stopLog := 0, format := 3 }

theorem oldest_shape : layers oldest = 21 ∧ 2 ^ finalLog oldest = 1 ∧ treeDepth oldest = 29 := by
  decide

theorem the_shipped_point_in_the_oldest_codec : total oldest = 230052 := by decide

theorem the_codec_halved_the_proof : 2 * total shippedFour < total oldest := by decide

theorem the_three_moves_in_order :
    total oldest = 230052 ∧
    total { oldest with digest := 24 } = 179644 ∧
    total { oldest with digest := 24, stopLog := 8 } = 153580 ∧
    total { oldest with digest := 24, stopLog := 8, foldLog := 2 } = 112436 := by decide

/-- the last move is the format: the DEEP value opened in FRI layer zero, at no cost in bytes -/
theorem the_last_move_is_the_shipped_point :
    ({ oldest with digest := 24, stopLog := 8, foldLog := 2, format := 4 } : Params) = shippedFour ∧
    total { oldest with digest := 24, stopLog := 8, foldLog := 2, format := 4 } = 112436 := by decide

/-! every listed artifact has a layout that closes on it -/

def artifacts : List (Params × Nat) := [(programOne, 341324), (shippedFour, 112436)]

theorem every_artifact_closes : ∀ a ∈ artifacts, total a.1 = a.2 := by decide

end Shield.Codec
