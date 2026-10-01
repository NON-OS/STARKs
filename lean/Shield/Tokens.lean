-- NONOS Operating System (AGPL-3.0-or-later)
/-!
EIP-7623 tokens estimated from a length alone, as the budget tool does. The
nonzero ratio is calibrated on the shipped artifact, 109933 nonzero bytes of
112436. The estimate is exact at the calibration point and bounded between one
and four tokens a byte everywhere.
-/

namespace Shield.Tokens

def shippedNonZero : Nat := 109933
def shippedTotal : Nat := 112436

def cap : Nat := 16777216
def base : Nat := 21000

/-- a zero byte is one token, anything else four -/
def tokens (z nz : Nat) : Nat := z + 4 * nz

/-- nonzero bytes a proof of this length is assumed to carry -/
def nonZeroOf (len : Nat) : Nat := len * shippedNonZero / shippedTotal

def zeroOf (len : Nat) : Nat := len - nonZeroOf len

def tokensOf (len : Nat) : Nat := (len - nonZeroOf len) + 4 * nonZeroOf len

/-- execution left under the cap after base and calldata -/
def budget (t : Nat) : Nat := cap - base - 4 * t

def budgetOf (len : Nat) : Nat := budget (tokensOf len)

/-! ## The calibration point -/

theorem shipped_zero : shippedTotal - shippedNonZero = 2503 := by decide

theorem nonZero_at_calibration : nonZeroOf 112436 = 109933 := by decide

theorem zero_at_calibration : zeroOf 112436 = 2503 := by decide

theorem tokens_at_calibration : tokensOf 112436 = 442235 := by decide

theorem estimate_matches_the_count : tokensOf 112436 = tokens 2503 109933 := by decide

theorem calldata_gas_at_calibration : 4 * tokensOf 112436 = 1768940 := by decide

theorem shipped_budget : budgetOf 112436 = 14987276 := by decide

theorem shipped_budget_partitions_the_cap :
    base + 4 * tokensOf 112436 + budgetOf 112436 = cap := by
  decide

/-! ## The calldata actually sent -/

def calldataLen : Nat := 113828
def measuredZero : Nat := 3662
def measuredNonZero : Nat := 110166

theorem measured_bytes : measuredZero + measuredNonZero = calldataLen := by decide

theorem measured_tokens : tokens measuredZero measuredNonZero = 444326 := by decide

theorem estimated_nonZero : nonZeroOf calldataLen = 111294 := by decide

theorem estimated_zero : zeroOf calldataLen = 2534 := by decide

theorem estimated_tokens : tokensOf calldataLen = 447710 := by decide

/-- the ABI words carry more zeros than the proof, so the estimate runs high -/
theorem estimate_over_measured :
    tokensOf calldataLen = 447710 ∧ tokens measuredZero measuredNonZero = 444326 ∧
      tokensOf calldataLen - tokens measuredZero measuredNonZero = 3384 := by
  decide

theorem nonZero_overcount : nonZeroOf calldataLen - measuredNonZero = 1128 := by decide

theorem zero_undercount : measuredZero - zeroOf calldataLen = 1128 := by decide

theorem estimated_budget : budgetOf calldataLen = 14965376 := by decide

theorem measured_budget : budget (tokens measuredZero measuredNonZero) = 14978912 := by decide

/-- the estimate is conservative: it never promises more execution than was there -/
theorem estimate_is_conservative :
    budgetOf calldataLen ≤ budget (tokens measuredZero measuredNonZero) := by decide

theorem conservative_by :
    budget (tokens measuredZero measuredNonZero) - budgetOf calldataLen = 13536 := by
  decide

/-! ## Small and large lengths -/

theorem empty : tokensOf 0 = 0 := by decide

theorem one_byte : nonZeroOf 1 = 0 ∧ tokensOf 1 = 1 := by decide

theorem a_thousand_bytes : nonZeroOf 1000 = 977 ∧ tokensOf 1000 = 3931 := by decide

theorem wrap_sized : tokensOf 24224 = 95276 := by decide

theorem size_ceiling : tokensOf 131072 = 515534 := by decide

/-- a proof at the size ceiling still leaves over 14.2M of execution -/
theorem size_ceiling_budget : budgetOf 131072 = 14694080 ∧ 14200000 < budgetOf 131072 := by
  decide

/-- even with every byte nonzero the ceiling leaves over 14.6M -/
theorem size_ceiling_dense_budget : budget (tokens 0 131072) = 14659064 := by decide

/-! ## General bounds -/

theorem nonZeroOf_lt_succ (len : Nat) : nonZeroOf len < len + 1 := by
  simp only [nonZeroOf, shippedNonZero, shippedTotal]
  omega

theorem nonZeroOf_le (len : Nat) : nonZeroOf len ≤ len := by
  have := nonZeroOf_lt_succ len
  omega

private theorem div_le_div_right {a b c : Nat} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [Nat.le_div_iff_mul_le hc]
  exact Nat.le_trans (Nat.div_mul_le_self a c) h

theorem nonZeroOf_monotone (len : Nat) : nonZeroOf len ≤ nonZeroOf (len + 1) := by
  simp only [nonZeroOf, shippedNonZero, shippedTotal]
  have h : len * 109933 ≤ (len + 1) * 109933 := Nat.mul_le_mul (Nat.le_succ len) (Nat.le_refl _)
  exact div_le_div_right (by decide) h

theorem nonZeroOf_step (len : Nat) : nonZeroOf (len + 1) ≤ nonZeroOf len + 1 := by
  simp only [nonZeroOf, shippedNonZero, shippedTotal]
  omega

theorem tokensOf_eq (len : Nat) : tokensOf len = len + 3 * nonZeroOf len := by
  have := nonZeroOf_le len
  simp only [tokensOf]
  omega

theorem tokensOf_is_tokens (len : Nat) : tokensOf len = tokens (zeroOf len) (nonZeroOf len) :=
  rfl

theorem zero_plus_nonZero (len : Nat) : zeroOf len + nonZeroOf len = len := by
  have := nonZeroOf_le len
  simp only [zeroOf]
  omega

/-- tokens never fall as the proof grows -/
theorem tokensOf_monotone (len : Nat) : tokensOf len ≤ tokensOf (len + 1) := by
  have h1 := nonZeroOf_le len
  have h2 := nonZeroOf_le (len + 1)
  have h3 := nonZeroOf_monotone len
  simp only [tokensOf]
  omega

/-- one more byte adds at most four tokens -/
theorem tokensOf_step (len : Nat) : tokensOf (len + 1) ≤ tokensOf len + 4 := by
  have h1 := nonZeroOf_le len
  have h2 := nonZeroOf_le (len + 1)
  have h3 := nonZeroOf_step len
  have h4 := nonZeroOf_monotone len
  simp only [tokensOf]
  omega

theorem tokensOf_le_of_le (a b : Nat) (h : a ≤ b) : tokensOf a ≤ tokensOf b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ k ih =>
    by_cases hk : a ≤ k
    · exact Nat.le_trans (ih hk) (tokensOf_monotone k)
    · have : a = k + 1 := by omega
      subst this
      exact Nat.le_refl _

/-- a byte is at most four tokens -/
theorem tokensOf_le_four (len : Nat) : tokensOf len ≤ 4 * len := by
  have := nonZeroOf_le len
  simp only [tokensOf]
  omega

/-- and at least one -/
theorem le_tokensOf (len : Nat) : len ≤ tokensOf len := by
  have := nonZeroOf_le len
  simp only [tokensOf]
  omega

theorem tokens_le_four (z n : Nat) : tokens z n ≤ 4 * (z + n) := by
  simp only [tokens]
  omega

theorem le_tokens (z n : Nat) : z + n ≤ tokens z n := by
  simp only [tokens]
  omega

/-! ## Budget -/

theorem budget_antitone (s t : Nat) (h : s ≤ t) : budget t ≤ budget s := by
  simp only [budget]
  omega

theorem budgetOf_antitone (a b : Nat) (h : a ≤ b) : budgetOf b ≤ budgetOf a :=
  budget_antitone _ _ (tokensOf_le_of_le a b h)

/-- a dense count is the worst case for the budget -/
theorem dense_is_the_floor_of_the_budget (len : Nat) : budget (4 * len) ≤ budgetOf len :=
  budget_antitone _ _ (tokensOf_le_four len)

theorem budget_partitions (t : Nat) (h : base + 4 * t ≤ cap) : base + 4 * t + budget t = cap := by
  simp only [budget]
  omega

/-! ## The floor never binds for a verifier -/

def standard (t exec : Nat) : Nat := 4 * t + exec
def floor (t : Nat) : Nat := 10 * t

theorem floor_below_standard (t exec : Nat) (h : 6 * t < exec) : floor t < standard t exec := by
  simp only [floor, standard]
  omega

theorem floor_binds_iff (t exec : Nat) : standard t exec ≤ floor t ↔ exec ≤ 6 * t := by
  simp only [standard, floor]
  constructor
  · intro h
    omega
  · intro h
    omega

def receiptExecution : Nat := 7783856

theorem shipped_floor_threshold : 6 * tokensOf 112436 = 2653410 := by decide

theorem shipped_floor_clear : 6 * tokensOf 112436 < receiptExecution := by decide

theorem estimated_floor_clear : 6 * tokensOf calldataLen = 2686260 ∧
    6 * tokensOf calldataLen < receiptExecution := by
  decide

theorem measured_floor_clear : floor (tokens measuredZero measuredNonZero) <
    standard (tokens measuredZero measuredNonZero) receiptExecution := by
  decide

theorem shipped_floor_does_not_bind :
    floor (tokensOf 112436) < standard (tokensOf 112436) receiptExecution :=
  floor_below_standard _ _ shipped_floor_clear

/-- the verifier's execution sits well inside the estimated budget -/
theorem receipt_within_estimated_budget : receiptExecution ≤ budgetOf calldataLen ∧
    budgetOf calldataLen - receiptExecution = 7181520 := by
  decide

end Shield.Tokens
