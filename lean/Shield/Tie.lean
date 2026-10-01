-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Merkle
import Shield.Transcript

/-!
Two roots name one codeword only if something says so.

A base query opens the DEEP value under the consistency root; the first FRI
layer opens its value under the FRI root. The consistency check argues about
the codeword behind the first root and FRI argues about the codeword behind
the second. Merkle binding ties each value to its own root and nothing else:
with no equation between the roots there is no theorem that the two values
are the same value, and with the equation there is. This file states both
halves over the abstract compression of `Shield.Hash`, so the argument does
not depend on the digest.
-/

namespace Shield.Tie

open Shield.Hash Shield.Merkle

variable {D : Type}

/-- the base query: the opened value authenticates under the consistency root -/
def consistency (h : Compress D) (root : D) (p : Path D) (v : D) : Prop := fold h p v = root

/-- the first FRI layer: the opened value authenticates under the FRI root -/
def layerZero (h : Compress D) (root : D) (p : Path D) (v : D) : Prop := fold h p v = root

/-- both checks, and the roots equated -/
def tied (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D) : Prop :=
  consistency h r1 p v1 ∧ layerZero h r2 p v2 ∧ r1 = r2

/-- both checks and nothing between the roots -/
def untied (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D) : Prop :=
  consistency h r1 p v1 ∧ layerZero h r2 p v2

/-! ## With the tie -/

/-- one index, one path, two roots equated: the two opened values are one value -/
theorem tied_names_one_value (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (ht : tied h r1 r2 p v1 v2) : v1 = v2 := by
  obtain ⟨h1, h2, h12⟩ := ht
  have e : fold h p v1 = fold h p v2 := by
    rw [h1, h2, h12]
  exact a_root_binds_its_leaf h p v1 v2 e

/-- so a FRI argument about the second value is an argument about the first -/
theorem fri_speaks_for_the_deep_value (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (ht : tied h r1 r2 p v1 v2) (P : D → Prop) (hP : P v2) : P v1 := by
  rw [tied_names_one_value h r1 r2 p v1 v2 ht]
  exact hP

/-- the tie is refused whenever the values differ, whatever the roots -/
theorem different_values_are_not_tied (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (hne : v1 ≠ v2) : ¬ tied h r1 r2 p v1 v2 :=
  fun ht => hne (tied_names_one_value h r1 r2 p v1 v2 ht)

/-! ## Without the tie -/

/-- any two values pass both checks, each under the root it computes -/
theorem untied_admits_any_pair (h : Compress D) (p : Path D) (v1 v2 : D) :
    untied h (fold h p v1) (fold h p v2) p v1 v2 :=
  ⟨rfl, rfl⟩

/-- and when the values differ the two roots differ, so nothing downstream of the roots alone
can tell the pair from an honest one -/
theorem untied_pair_has_two_roots (h : Compress D) (p : Path D) (v1 v2 : D) (hne : v1 ≠ v2) :
    untied h (fold h p v1) (fold h p v2) p v1 v2 ∧ fold h p v1 ≠ fold h p v2 :=
  ⟨untied_admits_any_pair h p v1 v2, a_foreign_leaf_misses_the_root h p v1 v2 hne⟩

/-- the tie adds exactly the root equation: an untied pair with equal roots is tied -/
theorem tie_is_the_root_equation (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (hu : untied h r1 r2 p v1 v2) (hr : r1 = r2) : tied h r1 r2 p v1 v2 :=
  ⟨hu.1, hu.2, hr⟩

theorem tied_is_untied_and_the_equation (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D) :
    tied h r1 r2 p v1 v2 ↔ untied h r1 r2 p v1 v2 ∧ r1 = r2 :=
  ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-! ## Where the tie has to live -/

/-- the FRI transcript never absorbs the consistency root, so the FRI challenges cannot carry
the equation; it is a check the verifier makes, which is what format 4 does -/
theorem the_fri_transcript_does_not_see_the_deep_root :
    Transcript.has .deepRoot Transcript.fri = false :=
  Transcript.the_deep_root_is_not_in_fri

theorem the_main_transcript_does_not_see_the_first_fri_root :
    Transcript.has (.friRoot 0) Transcript.main = false := by decide

/-- three places the equation can be made, and which side sees it -/
inductive Where
  | verifierCheck
  | mainTranscriptAbsorb
  | friTranscriptAbsorb
  deriving DecidableEq

/-- an absorb into the FRI transcript happens after the FRI root is drawn, so it binds the
challenges to the root but does not compare it with anything; the comparison is the check -/
def compares : Where → Bool
  | .verifierCheck => true
  | .mainTranscriptAbsorb => false
  | .friTranscriptAbsorb => false

theorem only_the_check_compares : ∀ w, compares w = true ↔ w = .verifierCheck := by
  intro w
  cases w <;> decide

/-! ## Format 4 -/

/-- what format 4's verifier checks: one root, required equal to FRI's first, and both openings
under it -/
def formatFour (h : Compress D) (deepRoot friRoot0 : D) (p : Path D) (v1 v2 : D) : Prop :=
  deepRoot = friRoot0 ∧ consistency h deepRoot p v1 ∧ layerZero h friRoot0 p v2

theorem format_four_is_tied (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (hf : formatFour h r1 r2 p v1 v2) : tied h r1 r2 p v1 v2 :=
  ⟨hf.2.1, hf.2.2, hf.1⟩

/-- so under format 4 the value a base query checks is the value FRI tested -/
theorem format_four_names_one_value (h : Compress D) (r1 r2 : D) (p : Path D) (v1 v2 : D)
    (hf : formatFour h r1 r2 p v1 v2) : v1 = v2 :=
  tied_names_one_value h r1 r2 p v1 v2 (format_four_is_tied h r1 r2 p v1 v2 hf)

/-! ## Where a position sits in layer zero

A layer-zero leaf holds positions `i`, `i + q`, `i + 2q`, `i + 3q` of a domain of `4q`. A query at
`p` opens leaf `p mod q` and reads slot `p / q`, as `deep_leaf::leaf_of` computes them. -/

theorem the_leaf_and_slot_name_the_position (p q : Nat) : p % q + q * (p / q) = p := by
  rw [Nat.add_comm]
  exact Nat.div_add_mod p q

theorem the_slot_is_one_of_four (p q : Nat) (hp : p < 4 * q) : p / q < 4 := by
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q)]
  exact hp

theorem the_leaf_is_in_the_layer (p q : Nat) (hq : 0 < q) : p % q < q := Nat.mod_lt p hq

/-- two positions with one leaf and one slot are one position -/
theorem leaf_and_slot_are_injective (p p' q : Nat) (h1 : p % q = p' % q) (h2 : p / q = p' / q) :
    p = p' := by
  rw [← the_leaf_and_slot_name_the_position p q, ← the_leaf_and_slot_name_the_position p' q,
    h1, h2]

/-- the shipped domain: `2^29` points, `2^27` leaves -/
theorem shipped_layer_zero : 4 * 2 ^ 27 = 2 ^ 29 ∧ 2 ^ 29 / 4 = 2 ^ 27 := by decide

/-! ## The witness that both halves are about something -/

theorem blob_tied : tied blobCompress (fold blobCompress [] (Blob.lit 3))
    (fold blobCompress [] (Blob.lit 3)) [] (Blob.lit 3) (Blob.lit 3) :=
  ⟨rfl, rfl, rfl⟩

theorem blob_untied_pair :
    untied blobCompress (Blob.lit 3) (Blob.lit 4) [] (Blob.lit 3) (Blob.lit 4) ∧
    Blob.lit 3 ≠ Blob.lit 4 :=
  ⟨⟨rfl, rfl⟩, by decide⟩

end Shield.Tie
