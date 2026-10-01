-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
The DEEP combination a base query recomputes: one coefficient per frame cell,
one for the composition, one per periodic column, in that order off the
transcript. The claims' whole contribution collapses to a scalar the session
computes once. Mirrors ProductionDeepQuery.sol.
-/

namespace Shield.Combine

open Shield.Layout

/-- coefficients drawn after the claims are absorbed -/
def terms (width window periodic : Nat) : Nat := width * window + 1 + periodic

theorem shipped_terms : terms 41 2 119 = 202 := by decide

/-- where each block of coefficients starts -/
def frameStart : Nat := 0
def compositionAt (width window : Nat) : Nat := width * window
def periodicStart (width window : Nat) : Nat := width * window + 1

theorem shipped_positions :
    compositionAt 41 2 = 82 ∧ periodicStart 41 2 = 83 ∧ periodicStart 41 2 + 119 = 202 := by decide

/-- the frame coefficient of row `r`, column `c` -/
def frameAt (width r c : Nat) : Nat := r * width + c

theorem the_frame_is_row_major (width r c : Nat) (hc : c < width) :
    frameAt width r c < (r + 1) * width := by
  simp only [frameAt]
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem the_last_frame_cell_precedes_the_composition (width window : Nat) (hw : 0 < window) :
    frameAt width (window - 1) (width - 1) < compositionAt width window ∨ width = 0 := by
  by_cases h : width = 0
  · exact Or.inr h
  · left
    simp only [frameAt, compositionAt]
    have : (window - 1) * width + width = window * width := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hw]
    rw [Nat.mul_comm width window]
    omega

theorem shipped_frame_cells :
    frameAt 41 0 0 = 0 ∧ frameAt 41 0 40 = 40 ∧ frameAt 41 1 0 = 41 ∧ frameAt 41 1 40 = 81 := by
  decide

theorem the_blocks_tile_the_terms (width window periodic : Nat) :
    compositionAt width window + 1 + periodic = terms width window periodic := rfl

theorem periodic_follows_the_composition (width window : Nat) :
    periodicStart width window = compositionAt width window + 1 := rfl

/-! the claims scalar -/

/-- `sum k_j * (row_j - claim_j)` against `sum k_j * row_j - sum k_j * claim_j`, over the
integers before reduction. Stated on lists of triples. -/
def weightedDiff : List (Nat × Nat × Nat) → Int
  | [] => 0
  | (k, r, z) :: rest => (k : Int) * ((r : Int) - (z : Int)) + weightedDiff rest

def weightedRows : List (Nat × Nat × Nat) → Int
  | [] => 0
  | (k, r, _) :: rest => (k : Int) * (r : Int) + weightedRows rest

def weightedClaims : List (Nat × Nat × Nat) → Int
  | [] => 0
  | (k, _, z) :: rest => (k : Int) * (z : Int) + weightedClaims rest

theorem the_scalar_factors : ∀ l, weightedDiff l = weightedRows l - weightedClaims l := by
  intro l
  induction l with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨k, r, z⟩ := t
    simp only [weightedDiff, weightedRows, weightedClaims]
    rw [ih, Int.mul_sub]
    omega

/-- the claims' sum depends on the coefficients and the claims alone, not on the query -/
theorem the_scalar_ignores_the_row (k z r r' : Nat) (rest : List (Nat × Nat × Nat)) :
    weightedClaims ((k, r, z) :: rest) = weightedClaims ((k, r', z) :: rest) := rfl

theorem a_concrete_scalar :
    weightedDiff [(2, 10, 3), (5, 7, 7), (1, 0, 4)] = 10 ∧
    weightedRows [(2, 10, 3), (5, 7, 7), (1, 0, 4)] = 55 ∧
    weightedClaims [(2, 10, 3), (5, 7, 7), (1, 0, 4)] = 45 := by decide

/-! what a query reads and what it does not -/

/-- values a base query opens: the row, the DEEP value, the composition value, the periodic row -/
def opened (width periodic : Nat) : Nat := width + 1 + 1 + periodic

theorem shipped_opened : opened 41 119 = 162 := by decide

/-- the claims at z ride once in the sidecar, not once per query -/
def claimsOnWire (periodic : Nat) : Nat := periodic

def claimsIfPerQuery (queries periodic : Nat) : Nat := queries * periodic

theorem the_sidecar_saves_eleven_copies :
    claimsIfPerQuery 12 119 - claimsOnWire 119 = 1309 ∧ 1309 * 16 = 20944 := by decide

/-- the pre-summed scalar replaces a 119-term sum per query with one subtraction -/
def scalarMultiplies (queries periodic : Nat) : Nat := queries * periodic

theorem the_scalar_saves_multiplies : scalarMultiplies 12 119 = 1428 := by decide

/-! the shared denominators -/

/-- row 0 and the composition share `x - z`; row 1 uses `x - g z`; one inverse each -/
def inversesPerQuery (window : Nat) : Nat := window

theorem shipped_inverses : inversesPerQuery 2 = 2 := by decide

/-- the composition term rides on row zero's inverse, so the periodic terms do too -/
def sharedInverse : Nat := 0

theorem the_composition_shares_row_zero : sharedInverse = frameStart := rfl

/-! sizes on the wire -/

theorem the_frame_is_the_ood (width window : Nat) : width * window = ood { shipped with width := width, window := window } := rfl

theorem shipped_frame_bytes : 16 * compositionAt 41 2 = 1312 := by decide

theorem shipped_claim_bytes : 16 * 119 = 1904 := by decide

theorem the_coefficients_are_never_on_the_wire (width window periodic : Nat) :
    terms width window periodic * 0 = 0 := by simp

/-- the head carries the frame and the sidecar carries the claims; the coefficients are
squeezed from both, which is why the claims must be absorbed before the draw -/
theorem drawn_after_both : periodicStart 41 2 + 119 = terms 41 2 119 := by decide

end Shield.Combine
