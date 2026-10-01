-- NONOS Operating System (AGPL-3.0-or-later)
/-!
A structural EVM cost model of one FRI query. Each coefficient is priced from
the opcodes the verifier runs for one unit of that work, and a query is the sum
of six terms over the proof's shape. The model prices shape only, so the
measured totals are compared against it rather than derived from it.
-/

namespace Shield.Cost

/-- gas per unit of each kind of work -/
structure Model where
  node : Nat
  fp2Mul : Nat
  rowValue : Nat
  transitionPerDegree : Nat
  deepTerm : Nat
  fold : Nat
  fixed : Nat

def default : Model :=
  { node := 60, fp2Mul := 40, rowValue := 20, transitionPerDegree := 40, deepTerm := 60,
    fold := 500, fixed := 200000 }

/-- what one query touches -/
structure Shape where
  nodes : Nat
  deepTerms : Nat
  transitions : Nat
  degree : Nat
  width : Nat
  window : Nat
  folds : Nat
  finalCoeffs : Nat

def merkle (m : Model) (s : Shape) : Nat := s.nodes * m.node
def deep (m : Model) (s : Shape) : Nat := s.deepTerms * m.deepTerm
def transitions (m : Model) (s : Shape) : Nat := s.transitions * s.degree * m.transitionPerDegree
def row (m : Model) (s : Shape) : Nat := s.width * s.window * m.rowValue
def folds (m : Model) (s : Shape) : Nat := s.folds * m.fold
def horner (m : Model) (s : Shape) : Nat := s.finalCoeffs * m.fp2Mul

def query (m : Model) (s : Shape) : Nat :=
  merkle m s + deep m s + transitions m s + row m s + folds m s + horner m s

def verify (m : Model) (s : Shape) (q : Nat) : Nat := m.fixed + q * query m s

theorem query_expands (m : Model) (a d t g w v f c : Nat) :
    query m ⟨a, d, t, g, w, v, f, c⟩ =
      a * m.node + d * m.deepTerm + t * g * m.transitionPerDegree + w * v * m.rowValue +
        f * m.fold + c * m.fp2Mul := rfl

theorem the_default_prices :
    default.node = 60 ∧ default.fp2Mul = 40 ∧ default.rowValue = 20 ∧
    default.transitionPerDegree = 40 ∧ default.deepTerm = 60 ∧ default.fold = 500 ∧
    default.fixed = 200000 := by decide

/-! the shipped shape -/

def shipped : Shape :=
  { nodes := 277, deepTerms := 202, transitions := 37, degree := 8, width := 41, window := 2,
    folds := 6, finalCoeffs := 512 }

theorem shipped_merkle : merkle default shipped = 16620 := by decide
theorem shipped_deep : deep default shipped = 12120 := by decide
theorem shipped_transitions : transitions default shipped = 11840 := by decide
theorem shipped_row : row default shipped = 1640 := by decide
theorem shipped_folds : folds default shipped = 3000 := by decide
theorem shipped_horner : horner default shipped = 20480 := by decide

theorem shipped_query : query default shipped = 65700 := by decide

theorem the_terms_add_up :
    16620 + 12120 + 11840 + 1640 + 3000 + 20480 = query default shipped := by decide

theorem shipped_verify_at_twelve : verify default shipped 12 = 988400 := by decide

theorem the_queries_at_twelve : 12 * query default shipped = 788400 := by decide

theorem the_fixed_work_is_over_a_fifth_of_the_model :
    verify default shipped 12 - default.fixed = 788400 ∧
    5 * default.fixed > verify default shipped 12 := by decide

/-- Horner leads, then Merkle, then DEEP, transitions, folds, the row -/
theorem the_terms_in_order :
    horner default shipped > merkle default shipped ∧
    merkle default shipped > deep default shipped ∧
    deep default shipped > transitions default shipped ∧
    transitions default shipped > folds default shipped ∧
    folds default shipped > row default shipped := by decide

theorem horner_is_under_a_third_of_a_query :
    3 * horner default shipped < query default shipped := by decide

theorem horner_and_merkle_are_over_half :
    2 * (horner default shipped + merkle default shipped) > query default shipped := by decide

theorem the_row_is_under_three_percent :
    100 * row default shipped < 3 * query default shipped := by decide

/-! the model against the measurements -/

def measuredLinear : Nat := 46376
def measuredTotal : Nat := 7783856
def measuredOld : Nat := 54562634

/-- the measured linear work per query comes in under the model -/
theorem measured_linear_is_under_the_model : measuredLinear < query default shipped := by decide

theorem the_model_over_measured_linear : query default shipped - measuredLinear = 19324 := by
  decide

/-- the measured total is more than seven models and under eight -/
theorem measured_total_is_over_seven_models :
    7 * verify default shipped 12 < measuredTotal ∧
    measuredTotal < 8 * verify default shipped 12 := by decide

theorem what_the_model_leaves_out : measuredTotal - verify default shipped 12 = 6795456 := by
  decide

theorem thirty_two_queries : 32 * query default shipped = 2102400 := by decide

theorem verify_at_thirty_two : verify default shipped 32 = 2302400 := by decide

/-- the old verifier ran 32 queries at between 25 and 26 times the model -/
theorem the_old_verifier_ratio :
    25 * (32 * query default shipped) < measuredOld ∧
    measuredOld < 26 * (32 * query default shipped) := by decide

theorem the_old_verifier_ratio_floor : measuredOld / (32 * query default shipped) = 25 := by
  decide

/-! stop six: one more fold, 15 more nodes, a quarter of the coefficients -/

def stopSix : Shape := { shipped with nodes := 292, folds := 7, finalCoeffs := 128 }

theorem stop_six_nodes : stopSix.nodes = shipped.nodes + 15 := by decide

theorem stop_six_keeps_the_rest :
    stopSix.deepTerms = shipped.deepTerms ∧ stopSix.transitions = shipped.transitions ∧
    stopSix.degree = shipped.degree ∧ stopSix.width = shipped.width ∧
    stopSix.window = shipped.window := by decide

theorem stop_six_query : query default stopSix = 51740 := by decide

theorem stop_six_accounted :
    query default shipped - 15360 + 500 + 900 = query default stopSix := by decide

theorem stop_six_horner_saving :
    horner default stopSix = 5120 ∧
    horner default shipped - horner default stopSix = 15360 ∧
    (512 - 128) * default.fp2Mul = 15360 := by decide

theorem stop_six_pays_one_fold_and_fifteen_nodes :
    folds default stopSix - folds default shipped = 500 ∧
    merkle default stopSix - merkle default shipped = 900 := by decide

theorem stop_six_saves_per_query : query default shipped - query default stopSix = 13960 := by
  decide

theorem stop_six_verify_at_twelve : verify default stopSix 12 = 820880 := by decide

/-- at stop six Merkle leads and Horner falls behind the transitions -/
theorem stop_six_terms_in_order :
    merkle default stopSix = 17520 ∧
    merkle default stopSix > deep default stopSix ∧
    deep default stopSix > transitions default stopSix ∧
    transitions default stopSix > horner default stopSix ∧
    horner default stopSix > folds default stopSix ∧
    folds default stopSix > row default stopSix := by decide

/-! general -/

theorem query_monotone_in_nodes (m : Model) (a b d t g w v f c : Nat) (h : a ≤ b) :
    query m ⟨a, d, t, g, w, v, f, c⟩ ≤ query m ⟨b, d, t, g, w, v, f, c⟩ := by
  rw [query_expands, query_expands]
  have hm : a * m.node ≤ b * m.node := Nat.mul_le_mul h (Nat.le_refl m.node)
  omega

theorem query_monotone_in_deep_terms (m : Model) (a d e t g w v f c : Nat) (h : d ≤ e) :
    query m ⟨a, d, t, g, w, v, f, c⟩ ≤ query m ⟨a, e, t, g, w, v, f, c⟩ := by
  rw [query_expands, query_expands]
  have hm : d * m.deepTerm ≤ e * m.deepTerm := Nat.mul_le_mul h (Nat.le_refl m.deepTerm)
  omega

theorem query_monotone_in_final_coeffs (m : Model) (a d t g w v f c k : Nat) (h : c ≤ k) :
    query m ⟨a, d, t, g, w, v, f, c⟩ ≤ query m ⟨a, d, t, g, w, v, f, k⟩ := by
  rw [query_expands, query_expands]
  have hm : c * m.fp2Mul ≤ k * m.fp2Mul := Nat.mul_le_mul h (Nat.le_refl m.fp2Mul)
  omega

theorem query_monotone_in_folds (m : Model) (a d t g w v f e c : Nat) (h : f ≤ e) :
    query m ⟨a, d, t, g, w, v, f, c⟩ ≤ query m ⟨a, d, t, g, w, v, e, c⟩ := by
  rw [query_expands, query_expands]
  have hm : f * m.fold ≤ e * m.fold := Nat.mul_le_mul h (Nat.le_refl m.fold)
  omega

theorem query_monotone_in_degree (m : Model) (a d t g k w v f c : Nat) (h : g ≤ k) :
    query m ⟨a, d, t, g, w, v, f, c⟩ ≤ query m ⟨a, d, t, k, w, v, f, c⟩ := by
  rw [query_expands, query_expands]
  have hm : t * g * m.transitionPerDegree ≤ t * k * m.transitionPerDegree :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl t) h) (Nat.le_refl m.transitionPerDegree)
  omega

/-- doubling the nodes adds one more Merkle term, no more -/
theorem doubling_nodes_adds_one_merkle (m : Model) (a d t g w v f c : Nat) :
    query m ⟨2 * a, d, t, g, w, v, f, c⟩ = query m ⟨a, d, t, g, w, v, f, c⟩ + a * m.node := by
  rw [query_expands, query_expands]
  have e : 2 * a * m.node = 2 * (a * m.node) := Nat.mul_assoc 2 a m.node
  omega

theorem more_nodes_cost_linearly (m : Model) (a k d t g w v f c : Nat) :
    query m ⟨a + k, d, t, g, w, v, f, c⟩ = query m ⟨a, d, t, g, w, v, f, c⟩ + k * m.node := by
  rw [query_expands, query_expands, Nat.add_mul]
  omega

theorem shipped_with_doubled_nodes :
    query default { shipped with nodes := 2 * shipped.nodes } = 82320 := by decide

theorem an_empty_shape_is_free (m : Model) : query m ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ = 0 := by
  rw [query_expands]
  omega

theorem verify_at_zero_is_the_fixed_work (m : Model) (s : Shape) : verify m s 0 = m.fixed := by
  show m.fixed + 0 * query m s = m.fixed
  omega

theorem one_more_query (m : Model) (s : Shape) (q : Nat) :
    verify m s (q + 1) = verify m s q + query m s := by
  show m.fixed + (q + 1) * query m s = m.fixed + q * query m s + query m s
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem verify_monotone_in_queries (m : Model) (s : Shape) (q r : Nat) (h : q ≤ r) :
    verify m s q ≤ verify m s r := by
  show m.fixed + q * query m s ≤ m.fixed + r * query m s
  have hm : q * query m s ≤ r * query m s := Nat.mul_le_mul h (Nat.le_refl (query m s))
  omega

theorem the_fixed_work_is_a_floor (m : Model) (s : Shape) (q : Nat) : m.fixed ≤ verify m s q := by
  show m.fixed ≤ m.fixed + q * query m s
  omega

/-- a smaller query shape verifies cheaper at every query count -/
theorem cheaper_queries_verify_cheaper (m : Model) (s u : Shape) (q : Nat)
    (h : query m s ≤ query m u) : verify m s q ≤ verify m u q := by
  show m.fixed + q * query m s ≤ m.fixed + q * query m u
  have hm : q * query m s ≤ q * query m u := Nat.mul_le_mul (Nat.le_refl q) h
  omega

theorem stop_six_verifies_cheaper (q : Nat) : verify default stopSix q ≤ verify default shipped q :=
  cheaper_queries_verify_cheaper default stopSix shipped q (by decide)

end Shield.Cost
