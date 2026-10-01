-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
What the one-call verifier is handed: the head, the claims, and the queries
section re-tiled into pieces in walk order, a base piece per query then a FRI
piece per query. A base piece is three non-adjacent ranges of the file joined
together. Mirrors the test gas test's _parts and the chunk order in _walk.
-/

namespace Shield.Pieces

open Shield.Layout

/-- a base piece: the consistency opening, the sidecar row with its path, the permutation path -/
def basePiece (p : Params) : Nat := consStride p + sidecarStride p + permStride p

/-- a FRI piece: one query's layers -/
def friPiece (p : Params) : Nat := friStride p

def pieces (p : Params) : Nat := 2 * p.queries

def piecesBytes (p : Params) : Nat := p.queries * basePiece p + p.queries * friPiece p

theorem shipped_pieces : pieces shippedFour = 24 := by decide

theorem shipped_base_piece : basePiece shippedFour = 4816 := by decide

theorem shipped_fri_piece : friPiece shippedFour = 3580 := by decide

theorem shipped_pieces_bytes : piecesBytes shippedFour = 100752 := by decide

/-- the pieces are the file less the head, the four counts, the nonce and the claims -/
theorem the_pieces_are_the_rest_of_the_file :
    piecesBytes shippedFour = total shippedFour - head shippedFour - 4 - 8 - 4 - 4 - 16 * shippedFour.periodic := by
  decide

theorem the_pieces_are_the_rest_of_the_file_in_general (p : Params) :
    piecesBytes p + head p + 4 + 8 + 4 + 4 + 16 * p.periodic = total p := by
  simp only [piecesBytes, basePiece, friPiece, total, permBase, sidecarEnd, sidecarBase, consEnd,
    consBase, friEnd, friBase]
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-! the head the gas test sends: the file up to the FRI queries, plus twelve bytes -/

/-- the twelve bytes between the FRI queries and the base queries: nonce and the query count -/
def headTail : Nat := 8 + 4

theorem the_twelve_bytes : headTail = 12 := by decide

def testHead (p : Params) : Nat := friBase p + 4 + headTail

theorem shipped_test_head : testHead shippedFour = 9776 := by decide

/-- the claims section: a count and the periodic claims at z -/
def claims (p : Params) : Nat := 4 + 16 * p.periodic

theorem shipped_claims : claims shippedFour = 1908 := by decide

/-- everything the gas test sends is the file, re-tiled -/
theorem the_test_sends_the_whole_file (p : Params) :
    testHead p + claims p + piecesBytes p = total p := by
  have := the_pieces_are_the_rest_of_the_file_in_general p
  simp only [testHead, claims, headTail, friBase] at *
  omega

theorem shipped_calldata_body : testHead shippedFour + claims shippedFour + piecesBytes shippedFour = 112436 := by
  decide

/-! walk order -/

inductive Kind
  | base
  | fri
  deriving DecidableEq

/-- piece `i` of `2q` -/
def kindOf (q i : Nat) : Kind := if i < q then .base else .fri

theorem the_first_half_is_base (q i : Nat) (h : i < q) : kindOf q i = .base := by
  simp [kindOf, h]

theorem the_second_half_is_fri (q i : Nat) (h : q ≤ i) : kindOf q i = .fri := by
  simp only [kindOf]
  rw [if_neg (Nat.not_lt.mpr h)]

theorem shipped_order :
    kindOf 12 0 = .base ∧ kindOf 12 11 = .base ∧ kindOf 12 12 = .fri ∧ kindOf 12 23 = .fri := by
  decide

/-- the query a piece belongs to -/
def queryOf (q i : Nat) : Nat := if i < q then i else i - q

theorem both_pieces_of_a_query (q i : Nat) (h : i < q) :
    queryOf q i = i ∧ queryOf q (i + q) = i := by
  simp only [queryOf]
  constructor
  · rw [if_pos h]
  · rw [if_neg (by omega)]; omega

/-- the byte offset of piece `i` inside the re-tiled section -/
def offsetOf (p : Params) (i : Nat) : Nat :=
  if i < p.queries then i * basePiece p else p.queries * basePiece p + (i - p.queries) * friPiece p

theorem shipped_offsets :
    offsetOf shippedFour 0 = 0 ∧ offsetOf shippedFour 1 = 4816 ∧ offsetOf shippedFour 12 = 57792 ∧
    offsetOf shippedFour 13 = 61372 ∧ offsetOf shippedFour 24 = 100752 := by decide

theorem the_last_offset_is_the_end (p : Params) : offsetOf p (2 * p.queries) = piecesBytes p := by
  simp only [offsetOf, piecesBytes]
  rw [if_neg (by omega)]
  have : 2 * p.queries - p.queries = p.queries := by omega
  rw [this]

theorem offsets_step_by_the_piece (p : Params) (i : Nat) (h : i + 1 < p.queries) :
    offsetOf p (i + 1) = offsetOf p i + basePiece p := by
  simp only [offsetOf]
  rw [if_pos h, if_pos (by omega), Nat.add_mul, Nat.one_mul]

theorem fri_offsets_step_by_the_piece (p : Params) (i : Nat) (hi : p.queries ≤ i) :
    offsetOf p (i + 1) = offsetOf p i + friPiece p := by
  simp only [offsetOf]
  rw [if_neg (by omega), if_neg (by omega)]
  have : i + 1 - p.queries = (i - p.queries) + 1 := by omega
  rw [this, Nat.add_mul, Nat.one_mul]
  omega

/-! what a piece opens -/

/-- a base piece authenticates five paths; a FRI piece, one per layer -/
def pathsInBase : Nat := 5
def pathsInFri (p : Params) : Nat := layers p

theorem shipped_paths_per_query : pathsInBase + pathsInFri shippedFour = 11 := by decide

theorem shipped_paths_per_proof : 12 * (pathsInBase + pathsInFri shippedFour) = 132 := by decide

/-- from stop 4 up the FRI piece is smaller than the base piece -/
theorem fri_pieces_are_smaller_from_stop_four :
    ∀ s < 12, 4 ≤ s → friPiece { shippedFour with stopLog := s } < basePiece shippedFour := by decide

/-- at stop 0 ten layers make it the larger of the two -/
theorem the_deepest_stop_makes_a_larger_fri_piece :
    friPiece { shippedFour with stopLog := 0 } = 5004 ∧ basePiece shippedFour < 5004 := by decide

end Shield.Pieces
