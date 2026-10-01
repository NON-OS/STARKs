-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Field
import Shield.Layout

/-!
The artifact every other check is anchored to: settlement-onetx.proof, proved
2026-09-22, the last of codec v1.2 before the header. Its digest, its size,
the values the prover printed for it, and the emit the contract side reads.
-/

namespace Shield.Fixture

open Shield.Layout

/-- sha256 of the bytes, as bytes -/
def sha256 : List Nat :=
  [0x92, 0x47, 0x9a, 0x55, 0xac, 0x87, 0x40, 0x57, 0x1a, 0xca, 0x88, 0xbb, 0xf8, 0x92, 0xf0, 0x72,
   0x77, 0x12, 0xa7, 0x18, 0xde, 0x9d, 0xf2, 0xaa, 0x2c, 0x89, 0x80, 0xb0, 0x83, 0x93, 0x76, 0x0]

theorem the_digest_is_thirty_two_bytes : sha256.length = 32 := by decide

theorem every_digest_byte_is_a_byte : ∀ b ∈ sha256, b < 256 := by decide

def bytes : Nat := 112436

/-- the fixture is the format 4 artifact of 2026-09-22 -/
theorem the_size_is_the_layout : bytes = total shippedFour := by decide

theorem under_the_ceiling : bytes ≤ 131072 ∧ 131072 - bytes = 18636 := by decide

/-! what the prover printed -/

def provedSeconds : Nat := 5269
def wallSeconds : Nat := 5322
def threads : Nat := 128
def peakGigabytes : Nat := 152
def verifyMilliseconds : Nat := 57

theorem proving_is_eighty_seven_minutes : provedSeconds / 60 = 87 := by decide

theorem proving_is_not_minutes : 10 * 60 < provedSeconds := by decide

theorem assembly_took_under_a_minute : wallSeconds - provedSeconds < 60 := by decide

theorem a_native_verification_is_a_thousandth_of_a_proof :
    1000 * verifyMilliseconds < provedSeconds * 1000 / 90 := by decide

/-- the out-of-domain point and the composition value there -/
def z0 : Nat := 9795573721576993152
def z1 : Nat := 5332705269378914657
def compZ0 : Nat := 10979086823035242724
def compZ1 : Nat := 119666858454548103

theorem the_published_point_is_canonical : z0 < Field.p ∧ z1 < Field.p := by decide

theorem the_composition_value_is_canonical : compZ0 < Field.p ∧ compZ1 < Field.p := by decide

theorem the_point_is_not_in_the_base_field : z1 ≠ 0 := by decide

/-- the periodic root the verifier bakes, keccak truncated to 24 bytes -/
def periodicRoot : List Nat :=
  [0x6a, 0xd8, 0xda, 0x27, 0x18, 0xd9, 0x6e, 0xd3, 0x8f, 0xcc, 0xc2, 0x44, 0x54, 0xec, 0xcb, 0x90,
   0xa8, 0x58, 0xe6, 0x55, 0xb6, 0x71, 0xa7, 0x46]

theorem the_root_is_a_digest : periodicRoot.length = shipped.digest := by decide

/-- padded to a word on chain: the tail is zero -/
def periodicRootWord : List Nat := periodicRoot ++ [0, 0, 0, 0, 0, 0, 0, 0]

theorem the_word_is_thirty_two_bytes : periodicRootWord.length = 32 := by decide

theorem the_padding_is_zero : ∀ b ∈ periodicRootWord.drop 24, b = 0 := by decide

/-! the emit the contract reads -/

def nQueries : Nat := 12
def logDomain : Nat := 29
def logTraceLen : Nat := 18
def traceWidth : Nat := 41
def nCoeffs : Nat := 760
def grindBits : Nat := 32
def cosetShift : Nat := 7
def regionWidth : Nat := 37
def constraintDegree : Nat := 8
def extraBlowupBits : Nat := 7
def nPeriodic : Nat := 119
def digestBytes : Nat := 24
def friRadix : Nat := 4

theorem the_emit_agrees_with_the_layout :
    nQueries = shipped.queries ∧ logDomain = Layout.logDomain shipped ∧
    logTraceLen = shipped.logTrace ∧ traceWidth = shipped.width ∧
    extraBlowupBits = shipped.extraBlowup ∧ nPeriodic = shipped.periodic ∧
    digestBytes = shipped.digest ∧ friRadix = 2 ^ shipped.foldLog := by decide

/-- 37 transitions and 723 boundaries; the count that replays to the published z -/
theorem the_coefficient_count : nCoeffs = 37 + 723 := by decide

/-- the count carried from an older proof, which failed at the first query -/
theorem the_wrong_count_was_722 : 722 ≠ nCoeffs := by decide

theorem the_region_is_inside_the_trace : regionWidth < traceWidth := by decide

theorem the_permutation_columns : traceWidth - regionWidth = 4 := by decide

theorem the_degree_is_a_power_of_two : constraintDegree = 2 ^ 3 := by decide

theorem the_shift_is_the_generator : cosetShift = 7 ∧ cosetShift < Field.p := by decide

/-- the artifact predates the header and stays that way -/
def hasHeader : Bool := false

theorem the_fixture_is_headerless : hasHeader = false := rfl

/-- its first four bytes are the permutation root, not the magic -/
theorem the_first_bytes_are_not_magic : periodicRoot.take 4 ≠ [78, 79, 88, 80] := by decide

/-! the publics -/

def nPublics : Nat := 32

theorem thirty_two_public_words : nPublics = 4 + 4 + 8 + 8 + 1 + 1 + 1 + 1 + 4 := by decide

/-- the publics are absorbed first, before the trace root -/
def absorbedFirst : Bool := true

/-! the transaction that carried it, on a local node -/

def txGas : Nat := 9582160
def txCalldataBytes : Nat := 113828

theorem the_calldata_is_wider_than_the_proof : bytes < txCalldataBytes ∧ txCalldataBytes - bytes = 1392 := by
  decide

theorem the_transaction_fits : txGas < 16777216 := by decide

/-- not Sepolia: chain id 31337 -/
def chainId : Nat := 31337

theorem the_receipt_is_from_a_local_node : chainId ≠ 11155111 ∧ chainId ≠ 1 := by decide

end Shield.Fixture
