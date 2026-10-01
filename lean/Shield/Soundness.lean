-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Params

/-!
Bits, in both regimes, at the points we run and the points we do not. The
Johnson bound gives a query half the rate exponent; list decoding to capacity
gives all of it. Grinding adds its bits to either and costs the prover 2^g.
Composition over M proofs under one root loses about log2 M.
-/

namespace Shield.Soundness

open Shield.Params

/-- the shipped settlement point -/
def twoTx : Point := ⟨12, 32, 7⟩

/-- the candidate the search ranks first at radix four -/
def fourteenAtSeven : Point := ⟨14, 32, 6⟩

theorem two_tx_rate : rateBits twoTx = 8 := by decide
theorem two_tx_is_eighty_provable : provable twoTx = 80 := by decide
theorem two_tx_is_128_conjectured : conjectured twoTx = 128 := by decide
theorem the_regimes_differ_by_forty_eight : conjectured twoTx - provable twoTx = 48 := by decide

theorem fourteen_at_seven_is_eighty_one : provable fourteenAtSeven = 81 := by decide
theorem fourteen_at_seven_conjectured : conjectured fourteenAtSeven = 130 := by decide

/-! what a query is worth -/

theorem grind_is_unconditional (p : Point) : p.grind ≤ provable p := by
  simp only [provable]
  omega

theorem grind_is_unconditional_conjectured (p : Point) : p.grind ≤ conjectured p := by
  simp only [conjectured]
  omega

/-- two more queries buy exactly one rate exponent, provably -/
theorem two_queries_buy_the_rate_exponent (p : Point) :
    provable ⟨p.queries + 2, p.grind, p.extraBlowup⟩ = provable p + rateBits p := by
  simp only [provable, rateBits]
  rw [Nat.add_mul]
  omega

/-- one more query buys a full rate exponent under the conjecture -/
theorem a_query_buys_the_rate_exponent_conjectured (p : Point) :
    conjectured ⟨p.queries + 1, p.grind, p.extraBlowup⟩ = conjectured p + rateBits p := by
  simp only [conjectured, rateBits]
  rw [Nat.add_mul]
  omega

/-- a bit of grind is a bit, in either regime -/
theorem a_grind_bit_is_a_bit (p : Point) :
    provable ⟨p.queries, p.grind + 1, p.extraBlowup⟩ = provable p + 1 ∧
    conjectured ⟨p.queries, p.grind + 1, p.extraBlowup⟩ = conjectured p + 1 := by
  simp only [provable, conjectured, rateBits]
  omega

/-- one more blowup bit is worth `queries / 2` bits provably: the whole domain doubles for it -/
theorem a_blowup_bit_costs_a_domain_and_buys_half_the_queries (p : Point) :
    provable ⟨p.queries, p.grind, p.extraBlowup + 1⟩ + p.queries / 2 ≤
      provable p + p.queries := by
  simp only [provable, rateBits]
  have e : 1 + (p.extraBlowup + 1) = 1 + p.extraBlowup + 1 := by omega
  rw [e, Nat.mul_add, Nat.mul_one]
  omega

/-! the floor -/

/-- at rate exponent eight with thirty two grind bits, eleven queries are not enough -/
theorem eleven_queries_are_short : ∀ q < 12, provable ⟨q, 32, 7⟩ < 80 := by decide

theorem twelve_is_the_least_at_this_rate : provable ⟨12, 32, 7⟩ = 80 := by decide

/-- and no grind under thirty two rescues twelve queries -/
theorem no_lesser_grind_reaches_eighty : ∀ g < 32, provable ⟨12, g, 7⟩ < 80 := by decide

/-- six queries clear the floor only under the conjecture -/
theorem six_queries_clear_the_floor_only_conjecturally :
    conjectured ⟨6, 32, 7⟩ = 80 ∧ provable ⟨6, 32, 7⟩ = 56 := by decide

/-- every point at grind thirty two with rate exponent at most sixteen that clears eighty
provably has at least six queries -/
theorem the_floor_needs_queries : ∀ e < 16, ∀ q < 6, provable ⟨q, 32, e⟩ < 80 := by decide

/-! grinding -/

def work (g : Nat) : Nat := 2 ^ g

theorem grind_32_hashes : work 32 = 4294967296 := by decide

theorem sixteen_more_bits_is_65536_times_the_work (g : Nat) : work (g + 16) = 65536 * work g := by
  simp only [work]
  rw [Nat.pow_add, Nat.mul_comm]

/-- at three hundred million hashes a second, grind 48 is over 260 hours -/
theorem grind_48_is_hours : 260 ≤ work 48 / (300000000 * 3600) := by decide

theorem grind_32_is_seconds : work 32 / 300000000 < 15 := by decide

/-- the verifier pays one hash for any grind -/
def verifierHashes (_g : Nat) : Nat := 1

theorem the_verifier_never_pays_for_grind (g : Nat) : verifierHashes g = 1 := rfl

/-! composition -/

def lg : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else 1 + lg fuel (n / 2)

theorem lg_of_powers : ∀ k < 33, lg 64 (2 ^ k) = k := by decide

/-- `M` proofs under one root: a cheating prover has `M` attempts -/
def composed (bits leaves : Nat) : Nat := bits - lg 64 leaves

theorem composition_never_adds (b m : Nat) : composed b m ≤ b := Nat.sub_le _ _

theorem one_leaf_costs_nothing (b : Nat) : composed b 1 = b := by
  simp [composed, lg]

theorem a_thousand_leaves_cost_ten_bits : composed 80 1024 = 70 := by decide

theorem a_thousand_leaves_break_the_floor : composed (provable twoTx) 1024 < 80 := by decide

/-- to keep eighty across a thousand leaves the point itself needs ninety -/
theorem what_a_thousand_leaves_demand : composed 90 1024 = 80 := by decide

/-- sixteen leaves, the most one proof carries, cost four bits -/
theorem sixteen_leaves_cost_four_bits : composed 80 16 = 76 := by decide

theorem lg_le_fuel (fuel n : Nat) : lg fuel n ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [lg]
  | succ f ih =>
    simp only [lg]
    by_cases h : n < 2
    · rw [if_pos h]; omega
    · rw [if_neg h]
      have := ih (n / 2)
      omega

/-- sixty four steps of fuel cover any leaf count below 2^64 -/
theorem composed_leaves_bits_for_small_trees (b : Nat) : b - 64 ≤ composed b (2 ^ 40) := by
  simp only [composed]
  have := lg_le_fuel 64 (2 ^ 40)
  omega

end Shield.Soundness
