-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Transcript
/-!
Keccak calls and gas of the on-chain transcript in StarkTranscript.sol, per event of
Shield.Transcript at the shipped shape. Every call hashes at most 64 bytes and costs 42 gas,
so 42 times the call count is a floor that no verifier of this transcript goes under.
-/

namespace Shield.Sponge

open Shield.Transcript (Event Kind kind)

/-! keccak gas -/

/-- 30 gas a call and 6 for every 32-byte word started -/
def keccakGas (bytes : Nat) : Nat := 30 + 6 * ((bytes + 31) / 32)

def words (bytes : Nat) : Nat := (bytes + 31) / 32

theorem keccak_gas_counts_words (b : Nat) : keccakGas b = 30 + 6 * words b := rfl

theorem keccak_gas_41 : keccakGas 41 = 42 := by decide
theorem keccak_gas_57 : keccakGas 57 = 42 := by decide
theorem keccak_gas_33 : keccakGas 33 = 42 := by decide
theorem keccak_gas_136 : keccakGas 136 = 60 := by decide
theorem keccak_gas_0 : keccakGas 0 = 30 := by decide
theorem keccak_gas_32 : keccakGas 32 = 36 := by decide

theorem keccak_gas_is_monotone (a b : Nat) (h : a ≤ b) : keccakGas a ≤ keccakGas b := by
  unfold keccakGas
  omega

theorem keccak_gas_is_at_least_30 (b : Nat) : 30 ≤ keccakGas b := by
  unfold keccakGas
  omega

theorem another_word_is_six_gas (b : Nat) : keccakGas (b + 32) = keccakGas b + 6 := by
  unfold keccakGas
  omega

theorem two_words_cost_42 (b : Nat) (h1 : 33 ≤ b) (h2 : b ≤ 64) : keccakGas b = 42 := by
  unfold keccakGas
  omega

theorem one_word_costs_36 (b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ 32) : keccakGas b = 36 := by
  unfold keccakGas
  omega

/-! what one call hashes -/

def tagBytes : Nat := 1
def stateBytes : Nat := 32
def limbBytes : Nat := 8
def digestBytes : Nat := 24

/-- tag 0x02, the state, one little-endian limb -/
def absorbElementBytes : Nat := tagBytes + stateBytes + limbBytes

/-- tag, the state, a 24-byte digest -/
def absorbDigestBytes : Nat := tagBytes + stateBytes + digestBytes

/-- tag and the state -/
def squeezeBytes : Nat := tagBytes + stateBytes

theorem an_element_absorb_hashes_41_bytes : absorbElementBytes = 41 := by decide
theorem a_digest_absorb_hashes_57_bytes : absorbDigestBytes = 57 := by decide
theorem a_squeeze_hashes_33_bytes : squeezeBytes = 33 := by decide

theorem every_call_is_two_words :
    words absorbElementBytes = 2 ∧ words absorbDigestBytes = 2 ∧ words squeezeBytes = 2 := by
  decide

theorem every_call_costs_42 :
    keccakGas absorbElementBytes = 42 ∧ keccakGas absorbDigestBytes = 42 ∧
    keccakGas squeezeBytes = 42 := by decide

/-- the tag byte is what pushes a squeeze into a second word -/
theorem the_tag_costs_a_word : keccakGas squeezeBytes = keccakGas stateBytes + 6 := by decide

theorem a_digest_leaves_seven_bytes_of_the_second_word : 2 * 32 - absorbDigestBytes = 7 := by
  decide

/-! the limb -/

/-- a field element as eight little-endian bytes -/
def le8 (x : Nat) : List Nat :=
  [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256, x / 4294967296 % 256,
   x / 1099511627776 % 256, x / 281474976710656 % 256, x / 72057594037927936 % 256]

def unle : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * unle bs

theorem a_limb_is_eight_bytes (x : Nat) : (le8 x).length = 8 := rfl

theorem the_limb_is_the_limb_width : limbBytes = 8 := rfl

theorem one_is_little_endian : le8 1 = [1, 0, 0, 0, 0, 0, 0, 0] := by decide

theorem the_largest_element_bytes :
    le8 18446744069414584320 = [0, 0, 0, 0, 255, 255, 255, 255] := by decide

theorem the_largest_element_round_trips :
    unle (le8 18446744069414584320) = 18446744069414584320 := by decide

theorem the_largest_u64_round_trips : unle (le8 (2 ^ 64 - 1)) = 2 ^ 64 - 1 := by decide

/-! calls per event -/

/-- keccak calls at the shipped shape -/
def calls : Event → Nat
  | .publics => 32
  | .traceRoot => 1
  | .beta => 1
  | .gamma => 1
  | .permRoot => 1
  | .compCoeffs => 1520
  | .compRoot => 1
  | .z => 2
  | .frame => 164
  | .claims => 238
  | .deepCoeffs => 404
  | .deepRoot => 1
  | .consIndex => 12
  | .friRoot _ => 1
  | .friBeta _ => 2
  | .finalPoly => 1024
  | .nonce => 1
  | .friIndex => 12

/-- 760 extension coefficients, two squeezes each -/
theorem composition_coefficients : calls .compCoeffs = 2 * 760 := by decide

/-- 82 frame elements, two limbs each -/
theorem frame_elements : calls .frame = 2 * 82 := by decide

theorem deep_coefficients : calls .deepCoeffs = 2 * 202 := by decide

theorem final_polynomial : calls .finalPoly = 2 * 512 := by decide

theorem z_is_one_extension_element : calls .z = 2 := by decide

theorem a_fri_layer_costs_three (m : Nat) : calls (.friRoot m) + calls (.friBeta m) = 3 := rfl

theorem every_main_event_hashes : ∀ e ∈ Transcript.main, 0 < calls e := by decide

theorem every_fri_event_hashes : ∀ e ∈ Transcript.fri, 0 < calls e := by decide

/-- the composition coefficients are drawn and never read by a query, and still cost a squeeze
each -/
theorem the_composition_coefficients_are_1520 : calls .compCoeffs = 1520 := rfl

theorem the_composition_coefficients_are_the_largest_item :
    ∀ e ∈ Transcript.main, e ≠ .compCoeffs → calls e < calls .compCoeffs := by decide

theorem the_final_polynomial_is_the_largest_fri_item :
    ∀ e ∈ Transcript.fri, e ≠ .finalPoly → calls e < calls .finalPoly := by decide

/-! totals -/

def total : List Event → Nat
  | [] => 0
  | e :: es => calls e + total es

theorem total_append (a b : List Event) : total (a ++ b) = total a + total b := by
  induction a with
  | nil => simp only [List.nil_append, total, Nat.zero_add]
  | cons x xs ih =>
    show calls x + total (xs ++ b) = calls x + total xs + total b
    rw [ih]
    omega

theorem the_main_transcript : total Transcript.main = 2378 := by decide

theorem the_fri_transcript : total Transcript.fri = 1055 := by decide

theorem both_transcripts : total (Transcript.main ++ Transcript.fri) = 3433 := by
  rw [total_append, the_main_transcript, the_fri_transcript]

theorem the_main_sum_by_hand :
    32 + 1 + 1 + 1 + 1 + 1520 + 1 + 2 + 164 + 238 + 404 + 1 + 12 = 2378 := by decide

theorem the_fri_sum_by_hand : 6 * 1 + 6 * 2 + 1024 + 1 + 12 = 1055 := by decide

theorem the_composition_coefficients_are_most_of_main :
    total Transcript.main < 2 * calls .compCoeffs := by decide

theorem main_without_the_composition_coefficients :
    total Transcript.main - calls .compCoeffs = 858 := by decide

theorem the_final_polynomial_is_most_of_fri : total Transcript.fri - calls .finalPoly = 31 := by
  decide

/-- publics up to z, the part measured as the transcript to z -/
theorem the_prefix_to_z :
    Transcript.main.take 8 =
      [.publics, .traceRoot, .beta, .gamma, .permRoot, .compCoeffs, .compRoot, .z] := by decide

theorem the_prefix_to_z_calls : total (Transcript.main.take 8) = 1559 := by decide

/-- the frame, the claims and the deep coefficients -/
theorem the_deep_draw : (Transcript.main.drop 8).take 3 = [.frame, .claims, .deepCoeffs] := by
  decide

theorem the_deep_draw_calls : total ((Transcript.main.drop 8).take 3) = 806 := by decide

/-! absorbs and squeezes -/

def absorbOne (e : Event) : Nat :=
  match kind e with
  | .absorb => calls e
  | .squeeze => 0

def squeezeOne (e : Event) : Nat :=
  match kind e with
  | .absorb => 0
  | .squeeze => calls e

theorem each_call_is_one_or_the_other (e : Event) : absorbOne e + squeezeOne e = calls e := by
  cases e <;> rfl

def absorbCalls : List Event → Nat
  | [] => 0
  | e :: es => absorbOne e + absorbCalls es

def squeezeCalls : List Event → Nat
  | [] => 0
  | e :: es => squeezeOne e + squeezeCalls es

theorem absorbs_and_squeezes_are_the_total (l : List Event) :
    absorbCalls l + squeezeCalls l = total l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [absorbCalls, squeezeCalls, total]
    have h := each_call_is_one_or_the_other x
    omega

theorem main_split : absorbCalls Transcript.main = 438 ∧ squeezeCalls Transcript.main = 1940 := by
  decide

theorem fri_split : absorbCalls Transcript.fri = 1031 ∧ squeezeCalls Transcript.fri = 24 := by
  decide

/-- the main transcript is mostly squeezes, the FRI one mostly absorbs -/
theorem the_transcripts_lean_opposite_ways :
    absorbCalls Transcript.main < squeezeCalls Transcript.main ∧
    squeezeCalls Transcript.fri < absorbCalls Transcript.fri := by decide

/-! gas floor -/

def callGas : Nat := 42

theorem call_gas_is_every_call : keccakGas absorbElementBytes = callGas := by decide

def floor (l : List Event) : Nat := callGas * total l

theorem floor_append (a b : List Event) : floor (a ++ b) = floor a + floor b := by
  unfold floor
  rw [total_append, Nat.mul_add]

theorem the_main_floor : floor Transcript.main = 99876 := by decide

theorem the_fri_floor : floor Transcript.fri = 44310 := by decide

theorem the_whole_floor : floor (Transcript.main ++ Transcript.fri) = 144186 := by
  rw [floor_append, the_main_floor, the_fri_floor]

/-! against the measured phases -/

def transcriptToZ : Nat := 325190
def deepCoefficients : Nat := 168742
def friChallenges : Nat := 961412
def batchSaving : Nat := 589185

theorem the_prefix_to_z_is_under_its_phase :
    floor (Transcript.main.take 8) = 65478 ∧ 65478 < transcriptToZ := by decide

theorem the_deep_draw_is_under_its_phase :
    floor ((Transcript.main.drop 8).take 3) = 33852 ∧ 33852 < deepCoefficients := by decide

theorem the_main_floor_is_under_both_phases :
    floor Transcript.main < transcriptToZ + deepCoefficients := by decide

/-- the FRI challenge phase ran at more than twenty times its hashing floor, so the phase was
overhead and not keccak -/
theorem the_fri_floor_is_far_under_the_phase : 20 * floor Transcript.fri < friChallenges := by
  decide

theorem the_fri_phase_after_the_batch_absorb : friChallenges - batchSaving = 372227 := by decide

theorem what_remains_is_still_above_the_floor :
    floor Transcript.fri < friChallenges - batchSaving := by decide

theorem what_remains_is_eight_floors : 8 * floor Transcript.fri < friChallenges - batchSaving := by
  decide

/-- the batch absorb saved thirteen times what hashing the final polynomial costs -/
theorem the_batch_saved_more_than_the_hashing :
    13 * (callGas * calls .finalPoly) < batchSaving := by decide

theorem the_final_polynomial_floor : callGas * calls .finalPoly = 43008 := by decide

theorem the_composition_squeezes_floor : callGas * calls .compCoeffs = 63840 := by decide

end Shield.Sponge
