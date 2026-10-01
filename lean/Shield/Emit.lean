-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
The contract-side emit: structure.json and layout.json, the fields a verifier
is constructed from. Some are the circuit's and are the same for every proof of
it; some are the point's and move with it. Carrying one of the second kind
across from another proof is how a run fails at its first query.
-/

namespace Shield.Emit

open Shield.Layout

inductive Key
  | outerNQueries
  | logDomain
  | logTraceLen
  | traceWidth
  | nCoeffs
  | grindBits
  | cosetShift
  | regionWidth
  | constraintDegree
  | extraBlowupBits
  | outerNPeriodic
  | nChal
  | digestBytes
  | finalLayerCoefficients
  | friRadix
  | periodicRoot
  deriving DecidableEq

inductive Owner
  | circuit
  | point
  | codec
  deriving DecidableEq

def owner : Key → Owner
  | .outerNQueries | .logDomain | .grindBits | .extraBlowupBits | .periodicRoot => .point
  | .logTraceLen | .traceWidth | .nCoeffs | .cosetShift | .regionWidth | .constraintDegree
  | .outerNPeriodic | .nChal => .circuit
  | .digestBytes | .finalLayerCoefficients | .friRadix => .codec

def keys : List Key :=
  [.outerNQueries, .logDomain, .logTraceLen, .traceWidth, .nCoeffs, .grindBits, .cosetShift,
   .regionWidth, .constraintDegree, .extraBlowupBits, .outerNPeriodic, .nChal, .digestBytes,
   .finalLayerCoefficients, .friRadix, .periodicRoot]

def count (o : Owner) : List Key → Nat
  | [] => 0
  | k :: rest => (if owner k = o then 1 else 0) + count o rest

theorem sixteen_keys : keys.length = 16 := by decide

theorem five_move_with_the_point : count .point keys = 5 := by decide

theorem eight_are_the_circuits : count .circuit keys = 8 := by decide

theorem three_are_the_codecs : count .codec keys = 3 := by decide

theorem every_key_has_one_owner : count .point keys + count .circuit keys + count .codec keys = 16 := by
  decide

/-- the periodic root moves with the point because the tree is built over the domain -/
theorem the_root_is_the_points : owner .periodicRoot = .point := rfl

/-- the coefficient count is the circuit's: transitions plus boundaries, whatever the point -/
theorem the_coefficient_count_is_the_circuits : owner .nCoeffs = .circuit := rfl

/-! the two emits -/

structure Values where
  outerNQueries : Nat
  logDomain : Nat
  logTraceLen : Nat
  traceWidth : Nat
  nCoeffs : Nat
  grindBits : Nat
  cosetShift : Nat
  regionWidth : Nat
  constraintDegree : Nat
  extraBlowupBits : Nat
  outerNPeriodic : Nat
  nChal : Nat
  digestBytes : Nat
  finalLayerCoefficients : Bool
  friRadix : Nat
  deriving DecidableEq

/-- spec/program-1 -/
def programOne : Values :=
  { outerNQueries := 32, logDomain := 25, logTraceLen := 18, traceWidth := 41, nCoeffs := 760,
    grindBits := 16, cosetShift := 7, regionWidth := 37, constraintDegree := 8,
    extraBlowupBits := 3, outerNPeriodic := 119, nChal := 2, digestBytes := 24,
    finalLayerCoefficients := true, friRadix := 2 }

/-- spec/onetx -/
def oneTx : Values :=
  { programOne with
    outerNQueries := 12, logDomain := 29, grindBits := 32, extraBlowupBits := 7, friRadix := 4 }

/-- the circuit's keys agree between the two emits -/
theorem the_circuit_keys_agree :
    programOne.logTraceLen = oneTx.logTraceLen ∧ programOne.traceWidth = oneTx.traceWidth ∧
    programOne.nCoeffs = oneTx.nCoeffs ∧ programOne.cosetShift = oneTx.cosetShift ∧
    programOne.regionWidth = oneTx.regionWidth ∧ programOne.constraintDegree = oneTx.constraintDegree ∧
    programOne.outerNPeriodic = oneTx.outerNPeriodic ∧ programOne.nChal = oneTx.nChal := by decide

/-- the point's keys do not -/
theorem the_point_keys_differ :
    programOne.outerNQueries ≠ oneTx.outerNQueries ∧ programOne.logDomain ≠ oneTx.logDomain ∧
    programOne.grindBits ≠ oneTx.grindBits ∧ programOne.extraBlowupBits ≠ oneTx.extraBlowupBits := by
  decide

/-- program-1's emit carried 722 for a day; the value that replays to z is 760 -/
def carriedAcross : Nat := 722

theorem the_carried_count_was_wrong : carriedAcross ≠ oneTx.nCoeffs ∧ oneTx.nCoeffs = 37 + 723 := by
  decide

/-! consistency with the layout -/

theorem the_emit_agrees_with_the_layout :
    oneTx.outerNQueries = shipped.queries ∧ oneTx.logDomain = logDomain shipped ∧
    oneTx.logTraceLen = shipped.logTrace ∧ oneTx.traceWidth = shipped.width ∧
    oneTx.extraBlowupBits = shipped.extraBlowup ∧ oneTx.outerNPeriodic = shipped.periodic ∧
    oneTx.digestBytes = shipped.digest ∧ oneTx.friRadix = 2 ^ shipped.foldLog := by decide

theorem the_domain_is_derived_not_read :
    oneTx.logDomain = oneTx.logTraceLen + 3 + 1 + oneTx.extraBlowupBits := by decide

theorem the_degree_gives_the_three : oneTx.constraintDegree = 2 ^ 3 := by decide

/-- the two challenge count means the two-round codec: a permutation root before the coefficients -/
theorem two_challenges : oneTx.nChal = 2 := rfl

/-- absent keys default: no fri_radix means two, no digest_bytes means thirty two -/
def friRadixOr (v : Option Nat) : Nat := v.getD 2
def digestBytesOr (v : Option Nat) : Nat := v.getD 32

theorem absent_radix_is_two : friRadixOr none = 2 := rfl
theorem absent_digest_is_thirty_two : digestBytesOr none = 32 := rfl

/-- a radix-four artifact read with the default skips half a quad per layer and walks off the file -/
theorem the_default_radix_misreads_a_quad : 16 * friRadixOr none < 16 * 4 := by decide

end Shield.Emit
