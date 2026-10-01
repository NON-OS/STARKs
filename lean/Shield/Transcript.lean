-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The order the prover absorbs and squeezes, read off prove_ext_pre/rounds.rs
and fri_ext/prove.rs. A challenge squeezed before the thing it should depend
on was absorbed is a challenge the prover picked.
-/

namespace Shield.Transcript

inductive Kind
  | absorb
  | squeeze
  deriving DecidableEq

inductive Event
  | publics
  | traceRoot
  | beta
  | gamma
  | permRoot
  | compCoeffs
  | compRoot
  | z
  | frame
  | claims
  | deepCoeffs
  | deepRoot
  | consIndex
  | friRoot (m : Nat)
  | friBeta (m : Nat)
  | finalPoly
  | nonce
  | friIndex
  deriving DecidableEq

def kind : Event → Kind
  | .publics | .traceRoot | .permRoot | .compRoot | .frame | .claims | .deepRoot
  | .friRoot _ | .finalPoly | .nonce => .absorb
  | .beta | .gamma | .compCoeffs | .z | .deepCoeffs | .consIndex | .friBeta _ | .friIndex =>
    .squeeze

/-- the main transcript, tag NONOS-STARK-EXT -/
def main : List Event :=
  [.publics, .traceRoot, .beta, .gamma, .permRoot, .compCoeffs, .compRoot, .z, .frame, .claims,
   .deepCoeffs, .deepRoot, .consIndex]

/-- the FRI transcript, tag NONOS-STARK-FRI-EXT, six layers -/
def fri : List Event :=
  [.friRoot 0, .friBeta 0, .friRoot 1, .friBeta 1, .friRoot 2, .friBeta 2,
   .friRoot 3, .friBeta 3, .friRoot 4, .friBeta 4, .friRoot 5, .friBeta 5,
   .finalPoly, .nonce, .friIndex]

def has (e : Event) : List Event → Bool
  | [] => false
  | x :: xs => if x = e then true else has e xs

/-- `a` occurs, and `b` occurs after it -/
def before (a b : Event) : List Event → Bool
  | [] => false
  | x :: xs => if x = a then has b xs else before a b xs

theorem before_means_both_occur (a b : Event) :
    ∀ l, before a b l = true → has a l = true ∧ has b l = true := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp [before])
  | cons x xs ih =>
    intro h
    simp only [before, has] at h ⊢
    by_cases hx : x = a
    · rw [if_pos hx] at h
      refine ⟨by rw [if_pos hx], ?_⟩
      by_cases hb : x = b
      · rw [if_pos hb]
      · rw [if_neg hb]; exact h
    · rw [if_neg hx] at h
      obtain ⟨ha, hb⟩ := ih h
      refine ⟨by rw [if_neg hx]; exact ha, ?_⟩
      by_cases hxb : x = b
      · rw [if_pos hxb]
      · rw [if_neg hxb]; exact hb

/-! main transcript -/

theorem publics_come_first : main.head? = some .publics := by decide

theorem the_trace_root_precedes_the_copy_challenges :
    before .traceRoot .beta main = true ∧ before .traceRoot .gamma main = true := by decide

theorem the_copy_challenges_precede_the_permutation_root :
    before .beta .permRoot main = true ∧ before .gamma .permRoot main = true := by decide

theorem the_permutation_root_precedes_the_composition :
    before .permRoot .compCoeffs main = true ∧ before .permRoot .compRoot main = true := by decide

theorem both_roots_precede_z :
    before .traceRoot .z main = true ∧ before .compRoot .z main = true := by decide

/-- the claims are absorbed after z and before the deep coefficients; a verifier that skips them
draws different coefficients and misses every query -/
theorem the_claims_sit_between_z_and_the_deep_coefficients :
    before .z .claims main = true ∧ before .claims .deepCoeffs main = true := by decide

theorem the_frame_precedes_the_deep_coefficients : before .frame .deepCoeffs main = true := by
  decide

theorem the_deep_root_precedes_the_indices : before .deepRoot .consIndex main = true := by decide

/-- every absorb in the main transcript comes before the index draw -/
theorem no_index_before_a_commitment :
    ∀ e ∈ main, kind e = .absorb → before e .consIndex main = true := by decide

theorem the_index_is_last : main.getLast? = some .consIndex := by decide

/-! FRI transcript -/

theorem each_beta_follows_its_root :
    ∀ m < 6, before (.friRoot m) (.friBeta m) fri = true := by decide

theorem the_layers_are_in_order :
    ∀ m < 5, before (.friBeta m) (.friRoot (m + 1)) fri = true := by decide

/-- the final polynomial is absorbed before the nonce is checked and before any index is
drawn, so a prover cannot pick the polynomial after seeing where it will be checked -/
theorem the_final_polynomial_precedes_the_nonce : before .finalPoly .nonce fri = true := by decide

theorem the_nonce_precedes_the_indices : before .nonce .friIndex fri = true := by decide

theorem every_root_precedes_the_indices :
    ∀ m < 6, before (.friRoot m) .friIndex fri = true := by decide

theorem no_fri_index_before_a_commitment :
    ∀ e ∈ fri, kind e = .absorb → before e .friIndex fri = true := by decide

/-! the two transcripts are separate -/

/-- domain tags, as bytes -/
def mainTag : List Nat := [78, 79, 78, 79, 83, 45, 83, 84, 65, 82, 75, 45, 69, 88, 84]
def friTag : List Nat := [78, 79, 78, 79, 83, 45, 83, 84, 65, 82, 75, 45, 70, 82, 73, 45, 69, 88, 84]

theorem the_tags_differ : mainTag ≠ friTag := by decide

theorem the_fri_tag_extends_the_main_one :
    friTag.take 12 = mainTag.take 12 ∧ friTag.length = mainTag.length + 4 := by decide

theorem no_event_is_shared : ∀ e ∈ main, has e fri = false := by decide

/-- the FRI transcript never sees the deep root, and the main one never sees a FRI root -/
theorem the_deep_root_is_not_in_fri : has .deepRoot fri = false := by decide
theorem no_fri_root_is_in_main : ∀ m < 6, has (.friRoot m) main = false := by decide

/-! counts -/

def count (k : Kind) : List Event → Nat
  | [] => 0
  | x :: xs => (if kind x = k then 1 else 0) + count k xs

theorem main_counts : count .absorb main = 7 ∧ count .squeeze main = 6 := by decide
theorem fri_counts : count .absorb fri = 8 ∧ count .squeeze fri = 7 := by decide

theorem count_is_the_length (l : List Event) : count .absorb l + count .squeeze l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [count, List.length_cons]
    cases h : kind x <;> simp [h] <;> omega

end Shield.Transcript
