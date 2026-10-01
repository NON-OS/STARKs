-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Budget

/-!
What the old reader allocated, in 32-byte words, and what the high-water mark
charged for it. Solidity never frees memory, so every allocation in a loop
raises the mark and the square term prices the late iterations highest.
-/

namespace Shield.Allocation

open Shield.Budget (memory memory_monotone memory_superadditive)

/-! ## Layouts -/

/-- `bytes32[k]`: a length word and the elements -/
def arrayWords (k : Nat) : Nat := 1 + k

/-- an array of two-word structs: length, one pointer each, then each struct -/
def structArrayWords (n : Nat) : Nat := 1 + n + 2 * n

/-- `bytes memory` of `L` bytes: a length word and the bytes rounded up to words -/
def bytesWords (L : Nat) : Nat := 1 + (L + 31) / 32

theorem structArrayWords_eq (n : Nat) : structArrayWords n = 1 + 3 * n := by
  simp only [structArrayWords]
  omega

theorem arrayWords_data (k : Nat) : arrayWords k - 1 = k := by
  simp only [arrayWords]
  omega

theorem structArrayWords_overhead (n : Nat) : structArrayWords n = 2 * n + (n + 1) := by
  simp only [structArrayWords]
  omega

theorem arrayWords_monotone (a b : Nat) (h : a ≤ b) : arrayWords a ≤ arrayWords b := by
  simp only [arrayWords]
  omega

theorem structArrayWords_monotone (a b : Nat) (h : a ≤ b) :
    structArrayWords a ≤ structArrayWords b := by
  simp only [structArrayWords]
  omega

theorem bytesWords_monotone (a b : Nat) (h : a ≤ b) : bytesWords a ≤ bytesWords b := by
  simp only [bytesWords]
  omega

theorem bytesWords_of_words (n : Nat) : bytesWords (32 * n) = 1 + n := by
  simp only [bytesWords]
  omega

theorem bytesWords_le (L : Nat) : bytesWords L ≤ 2 + L / 32 := by
  simp only [bytesWords]
  omega

theorem bytesWords_covers (L : Nat) : L ≤ 32 * (bytesWords L - 1) := by
  simp only [bytesWords]
  omega

theorem bytesWords_small : bytesWords 0 = 1 ∧ bytesWords 32 = 2 ∧ bytesWords 33 = 3 := by
  decide

/-! ## Concrete objects -/

/-- the 119 Fp2 claims: 238 words of data held in 358 -/
theorem claim_set_words : structArrayWords 119 = 358 := by decide

theorem claim_set_data : 2 * 119 = 238 := by decide

theorem claim_set_overhead : structArrayWords 119 - 2 * 119 = 120 := by decide

theorem claim_set_is_one_plus_three_per_claim : structArrayWords 119 = 1 + 3 * 119 := by
  decide

/-- the proof copied into memory -/
theorem proof_copy_words : bytesWords 621568 = 19425 := by decide

theorem proof_copy_is_whole_words : 621568 = 32 * 19424 := by decide

theorem artifact_copy_words : bytesWords 112436 = 3515 := by decide

theorem calldata_copy_words : bytesWords 113828 = 3559 := by decide

theorem ceiling_copy_words : bytesWords 131072 = 4097 := by decide

/-- a 29-deep authentication path -/
theorem path_words : arrayWords 29 = 30 := by decide

/-- the trace row -/
theorem trace_row_words : arrayWords 41 = 42 := by decide

/-- a quad of four Fp2 structs -/
theorem quad_words : structArrayWords 4 = 13 := by decide

/-! ## Per query -/

/-- deep, trace, comp, periodic and perm paths, and the trace row -/
def oldBaseQueryWords : Nat := 5 * arrayWords 29 + arrayWords 41

theorem old_base_query_words : oldBaseQueryWords = 192 := by decide

def friPathWords : Nat :=
  arrayWords 27 + arrayWords 25 + arrayWords 23 + arrayWords 21 + arrayWords 19 + arrayWords 17

/-- six radix-four layers, depths 27 down to 17 -/
theorem fri_path_words : friPathWords = 138 := by decide

theorem fri_path_words_expanded :
    arrayWords 27 + arrayWords 25 + arrayWords 23 + arrayWords 21 + arrayWords 19 +
      arrayWords 17 = 138 := by
  decide

def friQuadWords : Nat := 6 * structArrayWords 4

theorem fri_quad_words : friQuadWords = 78 := by decide

def oldFriQueryWords : Nat := friPathWords + friQuadWords

theorem old_fri_query_words : oldFriQueryWords = 216 := by decide

theorem old_query_words : oldBaseQueryWords + oldFriQueryWords = 408 := by decide

theorem twelve_queries_of_each :
    12 * oldBaseQueryWords = 2304 ∧ 12 * oldFriQueryWords = 2592 := by
  decide

/-! ## The Horner loop -/

def hornerSteps : Nat := 512
def queries : Nat := 12

/-- two 2-word structs a step -/
def hornerWordsPerQuery : Nat := hornerSteps * (2 * 2)

theorem horner_words_per_query : hornerWordsPerQuery = 2048 := by decide

theorem horner_words_per_query_as_steps : 4 * 512 = 2048 := by decide

def hornerWords : Nat := queries * hornerWordsPerQuery

theorem horner_words : hornerWords = 24576 := by decide

theorem horner_words_as_queries : 12 * 2048 = 24576 := by decide

theorem horner_words_agree_with_budget : hornerWords = 512 * 12 * 2 * 2 := by decide

/-! ## What the mark charged -/

def measuredMark : Nat := 18563

def oldMark : Nat := measuredMark + hornerWords

theorem old_mark : oldMark = 43139 := by decide

theorem memory_at_measured_mark : memory measuredMark = 728706 := by decide

theorem memory_at_old_mark : memory oldMark = 3764130 := by decide

/-- the Horner words alone cost over three million gas of memory -/
theorem horner_memory_cost : memory (18563 + 24576) - memory 18563 > 3000000 := by decide

theorem horner_memory_cost_exact : memory (18563 + 24576) - memory 18563 = 3035424 := by
  decide

/-- the arithmetic the loop does, at 40 gas a step -/
def hornerArithmetic : Nat := queries * hornerSteps * 40

theorem horner_arithmetic : hornerArithmetic = 245760 := by decide

theorem horner_arithmetic_literal : 12 * 512 * 40 = 245760 := by decide

/-- dropping the words saves more than twelve times the arithmetic they served -/
theorem saving_exceeds_twelve_times_the_arithmetic :
    (3 * 43139 + 43139 * 43139 / 512) -
        (3 * (43139 - 24576) + (43139 - 24576) * (43139 - 24576) / 512) >
      12 * (12 * 512 * 40) := by
  decide

theorem saving_through_memory :
    memory oldMark - memory (oldMark - hornerWords) > 12 * hornerArithmetic := by
  decide

/-- the same words allocated from an empty frame cost far less -/
theorem horner_words_from_empty : memory hornerWords = 1253376 := by decide

theorem position_matters :
    memory hornerWords < memory (measuredMark + hornerWords) - memory measuredMark := by
  decide

/-- one query's base and FRI objects on top of the measured mark -/
theorem base_query_on_the_mark : memory (18563 + 192) - memory 18563 = 14570 := by decide

theorem fri_query_on_the_mark : memory (18563 + 216) - memory 18563 = 16402 := by decide

/-! ## Allocation in a loop -/

/-- the mark after `q` iterations of `a` words each, from `w0` -/
def markAfter (w0 a q : Nat) : Nat := w0 + a * q

theorem markAfter_zero (w0 a : Nat) : markAfter w0 a 0 = w0 := by
  simp only [markAfter, Nat.mul_zero, Nat.add_zero]

theorem markAfter_succ (w0 a q : Nat) : markAfter w0 a (q + 1) = markAfter w0 a q + a := by
  simp only [markAfter, Nat.mul_add, Nat.mul_one]
  omega

theorem mark_rises (w0 a q : Nat) : markAfter w0 a q ≤ markAfter w0 a (q + 1) := by
  simp only [markAfter]
  have h : a * q ≤ a * (q + 1) := Nat.mul_le_mul (Nat.le_refl a) (Nat.le_succ q)
  omega

/-- every iteration costs something or nothing, never a refund -/
theorem memory_after_monotone (w0 a q : Nat) :
    memory (markAfter w0 a q) ≤ memory (markAfter w0 a (q + 1)) :=
  memory_monotone _ _ (mark_rises w0 a q)

theorem mark_rises_le (w0 a q r : Nat) (h : q ≤ r) : markAfter w0 a q ≤ markAfter w0 a r := by
  simp only [markAfter]
  have h' : a * q ≤ a * r := Nat.mul_le_mul (Nat.le_refl a) h
  omega

theorem memory_after_monotone_le (w0 a q r : Nat) (h : q ≤ r) :
    memory (markAfter w0 a q) ≤ memory (markAfter w0 a r) :=
  memory_monotone _ _ (mark_rises_le w0 a q r h)

/-- a loop in one frame costs at least the start plus the loop alone -/
theorem loop_superadditive (w0 a q : Nat) :
    memory w0 + memory (a * q) ≤ memory (markAfter w0 a q) :=
  memory_superadditive w0 (a * q)

theorem horner_is_a_loop : markAfter measuredMark hornerWordsPerQuery queries = oldMark := by
  decide

/-- the step from nothing to one iteration -/
theorem first_step :
    memory (markAfter 20000 4531 1) - memory (markAfter 20000 4531 0) = 407674 := by
  decide

/-- the step from 31 iterations to 32 -/
theorem last_step :
    memory (markAfter 20000 4531 32) - memory (markAfter 20000 4531 31) = 2893725 := by
  decide

/-- the same allocation costs more late in the loop than early -/
theorem late_steps_cost_more :
    memory (markAfter 20000 4531 1) - memory (markAfter 20000 4531 0) <
      memory (markAfter 20000 4531 32) - memory (markAfter 20000 4531 31) := by
  decide

theorem thirty_two_iterations_reach : markAfter 20000 4531 32 = 164992 := by decide

end Shield.Allocation
