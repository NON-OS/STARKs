-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The rows a recursive verifier spends per query, and how many proofs fit under one cap.

Each query opens Merkle chains over a row. The leaf absorbs the row four values at a time
and the walk compresses once per level, 32 rounds each, so narrowing the trace shrinks the
leaf term and leaves the walk where it was. Everything is `Nat`, core only.
-/

namespace Shield.Recursion

/-! ## One chain -/

/-- A chain over a row of `values` field elements into a tree of `depth` levels. -/
def chainRows (values depth : Nat) : Nat := (values / 4 + depth) * 32

/-- The tree walk alone: one 32-round compression per level. -/
def walkRows (depth : Nat) : Nat := depth * 32

/-- The leaf absorption alone. -/
def leafRows (values : Nat) : Nat := values / 4 * 32

/-- The outer's tree depth. -/
def outerDepth : Nat := 25

theorem chain_is_leaf_plus_walk (v d : Nat) : chainRows v d = v / 4 * 32 + walkRows d := by
  unfold chainRows walkRows
  exact Nat.add_mul _ _ _

theorem chain_splits (v d : Nat) : chainRows v d = leafRows v + walkRows d := by
  unfold leafRows
  exact chain_is_leaf_plus_walk v d

/-- The walk does not depend on the width. -/
theorem the_walk_ignores_the_width (v d : Nat) : chainRows v d - v / 4 * 32 = walkRows d := by
  rw [chain_is_leaf_plus_walk]
  omega

theorem the_walk_is_a_floor (v d : Nat) : walkRows d ≤ chainRows v d := by
  rw [chain_is_leaf_plus_walk]
  omega

theorem walk_adds (a b : Nat) : walkRows (a + b) = walkRows a + walkRows b := by
  unfold walkRows
  exact Nat.add_mul _ _ _

theorem walk_closed (d : Nat) : walkRows d = 32 * d := by
  unfold walkRows
  exact Nat.mul_comm _ _

/-- Values under four absorb in the walk's first compression and cost nothing extra. -/
theorem a_narrow_row_is_free (v d : Nat) (h : v < 4) : chainRows v d = walkRows d := by
  rw [chain_is_leaf_plus_walk]
  omega

/-- Width only enters through `v / 4`, so rows that agree there cost the same. -/
theorem chain_depends_on_quarters (v w d : Nat) (h : v / 4 = w / 4) :
    chainRows v d = chainRows w d := by
  unfold chainRows
  rw [h]

/-! ## The measured point -/

theorem outer_trace_chain : chainRows 41 outerDepth = 1120 := by decide

theorem outer_trace_chain_expanded : (41 / 4 + 25) * 32 = (10 + 25) * 32 := by decide

theorem outer_walk : walkRows outerDepth = 800 := by decide

theorem outer_leaf : leafRows 41 = 320 := by decide

theorem outer_leaf_plus_walk : leafRows 41 + walkRows outerDepth = 1120 := by decide

/-- The walk is most of the chain at 41 columns. -/
theorem the_walk_dominates_at_41 : 2 * leafRows 41 < walkRows outerDepth := by decide

/-! ## Per query and per proof -/

/-- Four chains a query, each at least the walk. -/
def floorPerQuery (d : Nat) : Nat := 4 * walkRows d

def queries : Nat := 16

def floorPerProof (d : Nat) : Nat := queries * floorPerQuery d

/-- The row ceiling the outer circuit is sized to. -/
def rowCap : Nat := 131072

theorem row_cap_is_two_to_the_seventeen : rowCap = 2 ^ 17 := by decide

theorem floor_per_query_closed (d : Nat) : floorPerQuery d = 128 * d := by
  unfold floorPerQuery walkRows
  omega

theorem floor_per_proof_closed (d : Nat) : floorPerProof d = 2048 * d := by
  unfold floorPerProof queries floorPerQuery walkRows
  omega

theorem outer_floor_per_query : floorPerQuery outerDepth = 3200 := by decide

theorem outer_floor_per_proof : floorPerProof outerDepth = 51200 := by decide

theorem outer_floor_fits : floorPerProof outerDepth < rowCap := by decide

theorem outer_floor_headroom : rowCap - floorPerProof outerDepth = 79872 := by decide

/-- The floor alone would reach the cap at depth 64. -/
theorem the_floor_reaches_the_cap : floorPerProof 64 = rowCap := by decide

/-- The full four chains at 41 columns, before any other verifier work. -/
theorem outer_chains_per_proof : queries * (4 * chainRows 41 outerDepth) = 71680 := by decide

/-! ## Fanout -/

/-- How many proofs of `verifyOne` rows fit under `cap` after `fixed` rows of overhead. -/
def fanout (cap fixed verifyOne : Nat) : Nat := (cap - fixed) / verifyOne

theorem two_le_fanout_iff (c f v : Nat) (hv : 0 < v) :
    2 ≤ fanout c f v ↔ 2 * v ≤ c - f := by
  unfold fanout
  exact Nat.le_div_iff_mul_le hv

theorem one_le_fanout_iff (c f v : Nat) (hv : 0 < v) :
    1 ≤ fanout c f v ↔ 1 * v ≤ c - f := by
  unfold fanout
  exact Nat.le_div_iff_mul_le hv

/-- A verifier that costs more than half the cap cannot fan out. -/
theorem over_half_is_not_two (c v : Nat) (h : c / 2 < v) : ¬ 2 ≤ fanout c 0 v := by
  have hv : 0 < v := by omega
  intro h2
  have h3 := (two_le_fanout_iff c 0 v hv).mp h2
  omega

theorem over_half_fans_out_once (c v : Nat) (h : c / 2 < v) : fanout c 0 v ≤ 1 := by
  have := over_half_is_not_two c v h
  omega

/-- Fixed overhead only ever lowers the fanout. -/
theorem fixed_cost_only_lowers_fanout (c f v : Nat) : fanout c f v ≤ fanout c 0 v := by
  unfold fanout
  by_cases hv : v = 0
  · subst hv
    have h1 := Nat.div_zero (c - f)
    have h2 := Nat.div_zero (c - 0)
    omega
  · have hv' : 0 < v := by omega
    have h1 := Nat.div_mul_le_self (c - f) v
    exact (Nat.le_div_iff_mul_le hv').mpr (by omega)

/-- Fanout is at least two exactly when two verifiers fit side by side. -/
theorem two_fit_means_fanout_two (c f v : Nat) (hv : 0 < v) (h : 2 * v ≤ c - f) :
    2 ≤ fanout c f v :=
  (two_le_fanout_iff c f v hv).mpr h

theorem a_seventy_thousand_row_verifier_fans_out_once : fanout rowCap 0 70000 = 1 := by decide

theorem a_sixty_thousand_row_verifier_fans_out_twice : fanout rowCap 0 60000 = 2 := by decide

theorem seventy_thousand_is_over_half : rowCap / 2 < 70000 := by decide

theorem sixty_thousand_is_under_half : 2 * 60000 ≤ rowCap - 0 := by decide

/-- The largest verifier that still fans out two. -/
theorem the_half_cap_is_the_line : fanout rowCap 0 65536 = 2 ∧ fanout rowCap 0 65537 = 1 := by
  decide

/-- The floor alone at the outer's depth leaves room for two. -/
theorem the_floor_fans_out_twice : fanout rowCap 0 (floorPerProof outerDepth) = 2 := by decide

/-- The four chains alone at 41 columns already fan out once. -/
theorem the_chains_fan_out_once :
    fanout rowCap 0 (queries * (4 * chainRows 41 outerDepth)) = 1 := by decide

/-! ## The width collapse -/

/-- The trace chain at 662 columns, before the collapse. -/
theorem wide_trace_chain : chainRows 662 outerDepth = 6080 := by decide

theorem wide_trace_chain_expanded : (662 / 4 + 25) * 32 = 6080 := by decide

theorem the_width_factor_is_over_sixteen : 16 * 41 < 662 := by decide

/-- The chain shrinks by a factor under six. -/
theorem the_chain_factor_is_under_six :
    6080 < 6 * 1120 ∧ 5 * 1120 < 6080 := by decide

theorem the_chain_falls_by_less_than_the_width :
    chainRows 662 outerDepth < 16 * chainRows 41 outerDepth ∧
    chainRows 662 outerDepth < 6 * chainRows 41 outerDepth ∧
    5 * chainRows 41 outerDepth < chainRows 662 outerDepth := by decide

/-- The walk is the part the collapse cannot touch. -/
theorem the_collapse_keeps_the_walk :
    chainRows 662 outerDepth - leafRows 662 = chainRows 41 outerDepth - leafRows 41 := by decide

theorem the_collapse_saving : chainRows 662 outerDepth - chainRows 41 outerDepth = 4960 := by
  decide

theorem the_saving_is_all_leaf : leafRows 662 - leafRows 41 = 4960 := by decide

/-! ## Composition -/

/-- Floor of the base-two log, with a step budget so it reduces structurally. -/
def lg : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n < 2 then 0 else 1 + lg f (n / 2)

/-- The security bound of a single proof, in bits. -/
def bits : Nat := 80

theorem lg_of_1024 : lg 64 1024 = 10 := by decide

theorem lg_of_16 : lg 64 16 = 4 := by decide

theorem lg_small : lg 64 0 = 0 ∧ lg 64 1 = 0 ∧ lg 64 2 = 1 ∧ lg 64 3 = 1 := by decide

theorem lg_rounds_down : lg 64 1023 = 9 ∧ lg 64 1025 = 10 := by decide

theorem lg_of_powers : ∀ k < 20, lg 64 (2 ^ k) = k := by decide

/-- With `M` leaves composed, the bound drops by `lg M`. -/
def composedBits (leaves : Nat) : Nat := bits - lg 64 leaves

theorem a_thousand_and_twenty_four_leaves_cost_ten_bits : 80 - lg 64 1024 = 70 := by decide

theorem composed_1024 : composedBits 1024 = 70 := by decide

theorem composed_16 : composedBits 16 = 76 := by decide

theorem one_leaf_costs_nothing : composedBits 1 = bits := by decide

theorem composition_never_raises_the_bound (m : Nat) : composedBits m ≤ bits := by
  unfold composedBits
  exact Nat.sub_le _ _

end Shield.Recursion
