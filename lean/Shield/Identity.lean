-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Header

/-!
Three identities on an artifact, because they answer three questions: how the
bytes decode, what the decoded statement means, and which configuration
produced it. A change to the system moves some of them and not others, and a
reader that conflates them accepts a proof it can decode and must not believe.
-/

namespace Shield.Identity

inductive Which
  | format
  | protocol
  | params
  | layout
  deriving DecidableEq

/-- changes the system has made or considered -/
inductive Change
  | digestWidth
  | foldRadix
  | earlyStop
  | queryCount
  | grindBits
  | rateExponent
  | traceWidth
  | boundaryCount
  | cosetShift
  | relationRewrite
  | transcriptBinding
  | sectionReorder
  | deepInLayerZero
  | oneQuerySet
  deriving DecidableEq

/-- which identities a change moves -/
def moves : Change → List Which
  | .digestWidth => [.format, .params, .layout]
  | .foldRadix => [.format, .params, .layout]
  | .earlyStop => [.format, .params, .layout]
  | .queryCount => [.params, .layout]
  | .grindBits => [.params]
  | .rateExponent => [.params, .layout]
  | .traceWidth => [.params, .layout]
  | .boundaryCount => [.params]
  | .cosetShift => [.params]
  | .relationRewrite => [.protocol]
  | .transcriptBinding => [.protocol]
  | .sectionReorder => [.format, .layout]
  | .deepInLayerZero => [.format]
  | .oneQuerySet => [.format, .layout]

def has (w : Which) : List Which → Bool
  | [] => false
  | x :: xs => if x = w then true else has w xs

/-- every soundness-relevant change moves the parameter identity -/
def soundnessRelevant : List Change :=
  [.digestWidth, .foldRadix, .earlyStop, .queryCount, .grindBits, .rateExponent, .traceWidth,
   .boundaryCount, .cosetShift]

theorem every_soundness_change_moves_params :
    ∀ c ∈ soundnessRelevant, has .params (moves c) = true := by decide

/-- a change to the bytes' meaning moves the protocol, and only such changes do -/
theorem only_relation_changes_move_the_protocol :
    ∀ c, has .protocol (moves c) = true ↔ c = .relationRewrite ∨ c = .transcriptBinding := by
  intro c
  cases c <;> decide

/-- a change that moves the layout without the format is a parameter move at fixed encoding -/
theorem layout_without_format_is_a_parameter_move :
    ∀ c, has .layout (moves c) = true → has .format (moves c) = false →
      has .params (moves c) = true := by
  intro c
  cases c <;> decide

/-- grind bits change no byte of the proof: the nonce is eight bytes at any grind -/
theorem grind_moves_nothing_but_params :
    moves .grindBits = [.params] := rfl

/-- no change moves nothing -/
theorem every_change_moves_something : ∀ c, moves c ≠ [] := by
  intro c
  cases c <;> decide

/-- the format moves alone once: format 4 changed what a consistency opening holds and kept every
section's base and stride, so the layout's words, and its identity, did not move. The header's
format number is the only thing that tells a format 3 reader it is reading the wrong bytes;
a layout word for the DEEP opening's depth would make the layout identity say so too. -/
theorem the_format_moved_alone_once :
    ∀ c, has .format (moves c) = true → has .layout (moves c) = false → c = .deepInLayerZero := by
  intro c
  cases c <;> decide

/-- format 5 runs the consistency check at FRI's positions and reads the DEEP value from FRI's own
layer-zero opening: the DEEP root and every query's DEEP opening leave the wire, so the bases and
strides move and the layout identity with them. The parameters and the relation do not. -/
theorem one_query_set_moves_format_and_layout : moves .oneQuerySet = [.format, .layout] := rfl

/-! the check, in the order the parser runs it -/

inductive Outcome
  | wrongMagic
  | wrongFormat
  | wrongProtocol
  | wrongParams
  | accepted
  deriving DecidableEq

def check (magicOk : Bool) (format protocol : Nat) (params expected : List Nat) : Outcome :=
  if !magicOk then .wrongMagic
  else if format ≠ Header.formatVersion then .wrongFormat
  else if protocol ≠ Header.protocolVersion then .wrongProtocol
  else if params ≠ expected then .wrongParams
  else .accepted

theorem the_magic_is_checked_first (f pr : Nat) (p e : List Nat) :
    check false f pr p e = .wrongMagic := rfl

theorem a_foreign_format_stops_before_the_protocol (pr : Nat) (p e : List Nat) :
    check true 2 pr p e = .wrongFormat := by
  simp [check, Header.formatVersion]

theorem a_foreign_protocol_stops_before_the_params (p e : List Nat) :
    check true 5 2 p e = .wrongProtocol := by
  simp [check, Header.formatVersion, Header.protocolVersion]

theorem only_the_exact_identity_is_accepted (p e : List Nat) (h : p ≠ e) :
    check true 5 1 p e = .wrongParams := by
  simp [check, Header.formatVersion, Header.protocolVersion, h]

theorem accepted_means_every_check_passed (m : Bool) (f pr : Nat) (p e : List Nat)
    (h : check m f pr p e = .accepted) :
    m = true ∧ f = Header.formatVersion ∧ pr = Header.protocolVersion ∧ p = e := by
  unfold check at h
  cases m with
  | false => exact absurd h (by simp [check])
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hf : f = Header.formatVersion
    · rw [if_neg (fun hne => hne hf)] at h
      by_cases hp : pr = Header.protocolVersion
      · rw [if_neg (fun hne => hne hp)] at h
        by_cases hpe : p = e
        · exact ⟨rfl, hf, hp, hpe⟩
        · rw [if_pos hpe] at h; exact absurd h (by decide)
      · rw [if_pos hp] at h; exact absurd h (by decide)
    · rw [if_pos hf] at h; exact absurd h (by decide)

/-- the expensive work is behind every check: an accepted header is the only way in -/
def expensiveWorkRuns (o : Outcome) : Bool := o = .accepted

theorem nothing_expensive_before_acceptance (o : Outcome) (h : o ≠ .accepted) :
    expensiveWorkRuns o = false := by
  simp [expensiveWorkRuns, h]

/-! the two tags -/

/-- NOX_PARAMS_V1 and NOX_LAYOUT_V1 differ, so a parameter preimage is never a layout preimage -/
theorem the_tags_differ : Header.domain ≠ [78, 79, 88, 95, 76, 65, 89, 79, 85, 84, 95, 86, 49] := by
  decide

theorem the_tags_share_a_prefix_and_a_version :
    Header.domain.take 4 = [78, 79, 88, 95] ∧ Header.domain.drop 11 = [86, 49] := by decide

/-! what is bound where -/

inductive Binding
  | parserCheck
  | transcriptAbsorb
  | bakedImmutable
  deriving DecidableEq

/-- how each identity reaches the verifier today -/
def boundBy : Which → Binding
  | .format => .parserCheck
  | .protocol => .parserCheck
  | .params => .parserCheck
  | .layout => .bakedImmutable

/-- the parameter identity is checked, not absorbed; absorbing it is the next transcript change -/
theorem params_are_checked_not_absorbed : boundBy .params = .parserCheck := rfl

theorem the_layout_is_compiled_in : boundBy .layout = .bakedImmutable := rfl

theorem no_identity_is_absorbed_yet : ∀ w, boundBy w ≠ .transcriptAbsorb := by
  intro w
  cases w <;> decide

/-- absorbing the identity is one sponge block: 32 bytes, four field words -/
theorem an_identity_is_one_block : 32 / 8 = 4 := by decide

end Shield.Identity
