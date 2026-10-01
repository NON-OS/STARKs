-- NONOS Operating System (AGPL-3.0-or-later)
/-!
EIP-7825 caps a transaction at 2^24 gas. EIP-7623 prices calldata in tokens
and charges the larger of two branches. Memory is priced on the high-water
mark with a square term. This file holds those rules, the shipped proof's
numbers, and the receipt's.
-/

namespace Shield.Budget

def cap : Nat := 16777216
def base : Nat := 21000

/-- a zero byte is one token, anything else four -/
def tokens (z nz : Nat) : Nat := z + 4 * nz

def standard (t exec : Nat) : Nat := 4 * t + exec
def floor (t : Nat) : Nat := 10 * t

def charged (z nz exec : Nat) : Nat :=
  base + max (standard (tokens z nz) exec) (floor (tokens z nz))

/-- execution left under the cap after base and calldata -/
def budget (t : Nat) : Nat := cap - base - 4 * t

def fits (z nz exec : Nat) : Prop := charged z nz exec ≤ cap

instance (z n e : Nat) : Decidable (fits z n e) := by
  unfold fits; infer_instance

theorem cap_is_two_to_the_twenty_four : cap = 2 ^ 24 := by decide

/-! settlement-onetx.proof, bytes counted -/

def artifactZero : Nat := 2503
def artifactNonZero : Nat := 109933

theorem artifact_bytes : artifactZero + artifactNonZero = 112436 := by decide
theorem artifact_tokens : tokens artifactZero artifactNonZero = 442235 := by decide
theorem artifact_calldata_gas : 4 * tokens artifactZero artifactNonZero = 1768940 := by decide
theorem artifact_budget : budget (tokens artifactZero artifactNonZero) = 14987276 := by decide

theorem the_budget_partitions_the_cap :
    base + 4 * tokens artifactZero artifactNonZero +
      budget (tokens artifactZero artifactNonZero) = cap := by
  decide

/-! the calldata actually sent: ABI offsets, lengths and the 32 public words on top of the proof -/

def calldataZero : Nat := 3662
def calldataNonZero : Nat := 110166

theorem calldata_bytes : calldataZero + calldataNonZero = 113828 := by decide
theorem calldata_tokens : tokens calldataZero calldataNonZero = 444326 := by decide
theorem intrinsic : base + 4 * tokens calldataZero calldataNonZero = 1798304 := by decide

def receiptExecution : Nat := 7783856
def receiptTotal : Nat := 9582160

theorem the_receipt_adds_up :
    base + 4 * tokens calldataZero calldataNonZero + receiptExecution = receiptTotal := by decide

theorem the_floor_did_not_bind :
    floor (tokens calldataZero calldataNonZero) <
      standard (tokens calldataZero calldataNonZero) receiptExecution := by decide

theorem the_transaction_fits : fits calldataZero calldataNonZero receiptExecution := by decide

theorem charged_is_the_receipt :
    charged calldataZero calldataNonZero receiptExecution = receiptTotal := by decide

theorem under_three_fifths_of_the_cap : 10 * receiptTotal < 6 * cap := by decide

theorem headroom : cap - receiptTotal = 7195056 := by decide

theorem execution_within_its_budget :
    receiptExecution ≤ budget (tokens calldataZero calldataNonZero) ∧
    budget (tokens calldataZero calldataNonZero) - receiptExecution = 7195056 := by decide

/-! general -/

theorem floor_binds_iff (t exec : Nat) : standard t exec ≤ floor t ↔ exec ≤ 6 * t := by
  simp only [standard, floor]
  omega

theorem heavy_execution_pays_standard (t exec : Nat) (h : 6 * t ≤ exec) :
    max (standard t exec) (floor t) = standard t exec := by
  simp only [standard, floor]
  omega

theorem a_nonzero_byte_is_sixteen_gas (z n : Nat) :
    4 * tokens z (n + 1) = 4 * tokens z n + 16 := by
  simp only [tokens]
  omega

theorem headroom_falls_sixteen_per_byte (t : Nat) (h : base + 4 * (t + 4) ≤ cap) :
    budget (t + 4) + 16 = budget t := by
  simp only [budget, base, cap] at *
  omega

theorem budget_antitone (s t : Nat) (h : s ≤ t) : budget t ≤ budget s := by
  simp only [budget]
  omega

theorem calldata_alone_caps_out (t : Nat) (h : cap < base + 4 * t) : budget t = 0 := by
  simp only [budget, base, cap] at *
  omega

/-- a proof at the size ceiling, all bytes nonzero, still leaves most of the cap -/
theorem the_size_ceiling_leaves_a_budget : 8000000 < budget (tokens 0 131072) := by decide

/-! memory: 3w + w²/512 on the high-water mark, never lowered -/

def memory (w : Nat) : Nat := 3 * w + w * w / 512

theorem memory_zero : memory 0 = 0 := by decide

theorem memory_at_the_measured_mark : memory 165000 = 53668828 := by decide

theorem memory_of_a_few_hundred_words : memory 300 = 1075 := by decide

/-- the old Horner loop: 512 coefficients, two 2-word structs a step, 12 queries -/
theorem the_old_horner_loop_in_words : 512 * 12 * 2 * 2 = 24576 := by decide

/-- those words on top of the measured 18,563 cost more than the streaming verifier does -/
theorem the_old_horner_loop_cost_more_than_a_verifier :
    memory (18563 + 24576) - memory 18563 > 3000000 := by decide

private theorem div512_add (x y : Nat) : x / 512 + y / 512 ≤ (x + y) / 512 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 512)]
  have hx := Nat.div_add_mod x 512
  have hy := Nat.div_add_mod y 512
  omega

private theorem div_le_div_right {a b c : Nat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [Nat.le_div_iff_mul_le hc]
  exact Nat.le_trans (Nat.div_mul_le_self a c) h

private theorem sq_expand (a b : Nat) : (a + b) * (a + b) = a * a + a * b + b * a + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega

theorem memory_monotone (a b : Nat) (h : a ≤ b) : memory a ≤ memory b := by
  simp only [memory]
  have hsq : a * a ≤ b * b := Nat.mul_le_mul h h
  have hdiv : a * a / 512 ≤ b * b / 512 := div_le_div_right (by decide) hsq
  omega

/-- two allocations in one frame cost at least what they cost in two frames -/
theorem memory_superadditive (a b : Nat) : memory a + memory b ≤ memory (a + b) := by
  simp only [memory]
  rw [sq_expand]
  have h1 := div512_add (a * a) (b * b)
  have h2 : (a * a + b * b) / 512 ≤ (a * a + a * b + b * a + b * b) / 512 :=
    div_le_div_right (by decide) (by omega)
  omega

theorem doubling_more_than_doubles (w : Nat) (h : 512 ≤ w) : 2 * memory w < memory (2 * w) := by
  simp only [memory]
  have e : 2 * w * (2 * w) = 4 * (w * w) := by
    rw [Nat.mul_assoc, Nat.mul_comm w (2 * w), Nat.mul_assoc]
    omega
  rw [e]
  have h4 : 4 * (w * w) / 512 = w * w / 128 := by
    rw [show (512 : Nat) = 4 * 128 from rfl, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (by decide)]
  rw [h4]
  have hw : 512 * 512 ≤ w * w := Nat.mul_le_mul h h
  have h128 : w * w / 512 * 4 ≤ w * w / 128 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 128)]
    have := Nat.div_mul_le_self (w * w) 512
    omega
  have hpos : 2 ≤ w * w / 512 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 512)]
    omega
  omega

theorem one_frame_costs_at_least_two (a : Nat) : 2 * memory a ≤ memory (2 * a) := by
  have := memory_superadditive a a
  rw [show a + a = 2 * a by omega] at this
  omega

end Shield.Budget
