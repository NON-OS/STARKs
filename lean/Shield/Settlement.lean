-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The settlement that is on Sepolia and the one that is not yet. Fourteen
transactions carried the first, one carries the second. What a payment costs
under each, from the receipts.
-/

namespace Shield.Settlement

/-- accepted on Sepolia on 22 September: fourteen transactions -/
def sepoliaGas : Nat := 96077500
def sepoliaTransactions : Nat := 14

/-- accepted on a local node the same evening: one transaction -/
def oneTxGas : Nat := 9582160

theorem a_sepolia_transaction_on_average : sepoliaGas / sepoliaTransactions = 6862678 := by decide

theorem the_chunks_were_each_under_the_cap : sepoliaGas / sepoliaTransactions < 16777216 := by decide

/-- the whole chunked settlement was five and a half caps -/
theorem the_chunked_settlement_spanned_caps :
    5 * 16777216 < sepoliaGas ∧ sepoliaGas < 6 * 16777216 := by decide

theorem one_transaction_is_a_tenth : 10 * oneTxGas < sepoliaGas ∧ sepoliaGas < 11 * oneTxGas := by
  decide

theorem the_saving : sepoliaGas - oneTxGas = 86495340 := by decide

/-! what a payment costs: the shipped proof settles one join-split -/

def spendsPerProof : Nat := 1

theorem a_payment_today : oneTxGas / spendsPerProof = 9582160 := by decide

/-- at 20 gwei and 3,000 dollars an ether, in cents -/
def gwei : Nat := 20
def dollarsPerEther : Nat := 3000

def centsFor (gas : Nat) : Nat := gas * gwei * dollarsPerEther * 100 / 1000000000

theorem one_transaction_in_cents : centsFor oneTxGas = 57492 := by decide

theorem the_chunked_settlement_in_cents : centsFor sepoliaGas = 576465 := by decide

theorem centsFor_scales (g : Nat) : centsFor (2 * g) = centsFor g * 2 ∨ centsFor (2 * g) = centsFor g * 2 + 1 := by
  simp only [centsFor]
  have e : 2 * g * gwei * dollarsPerEther * 100 = 2 * (g * gwei * dollarsPerEther * 100) := by
    simp only [gwei, dollarsPerEther]; omega
  rw [e]
  omega

/-! batching, as arithmetic rather than a claim: the proof stays one transaction and the
spends it carries divide the cost -/

def perSpend (spends : Nat) : Nat := oneTxGas / spends

theorem per_spend_at_sixteen : perSpend 16 = 598885 := by decide

theorem per_spend_at_four : perSpend 4 = 2395540 := by decide

theorem sixteen_spends_are_under_a_million_each : perSpend 16 < 1000000 := by decide

theorem per_spend_halves_as_spends_double (s : Nat) : perSpend (2 * s) ≤ perSpend s / 2 + 1 := by
  simp only [perSpend]
  rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
  omega

/-- what the proof's trace can hold is the field's business: the two-adicity caps the domain -/
def domainCap : Nat := 32

theorem the_domain_has_three_levels_spare : domainCap - 29 = 3 := by decide

/-- eight times the rows at the same rate would need a domain of 2^32 -/
theorem eight_times_the_rows_hits_the_cap : 29 + 3 = domainCap := by decide

theorem sixteen_times_does_not_fit : domainCap < 29 + 4 := by decide

/-! the chain's own limits -/

def blockGasLimit : Nat := 36000000

theorem one_transaction_is_under_a_third_of_a_block : 3 * oneTxGas < blockGasLimit := by decide

theorem three_settlements_fit_a_block : 3 * oneTxGas ≤ blockGasLimit := by decide

theorem four_do_not : blockGasLimit < 4 * oneTxGas := by decide

/-- twelve-second blocks: settlements an hour if the chain did nothing else -/
theorem settlements_per_hour_if_alone : 3 * (3600 / 12) = 900 := by decide

/-! the proof size against the transaction -/

def proofBytes : Nat := 112436
def calldataBytes : Nat := 113828

theorem the_envelope : calldataBytes - proofBytes = 1392 := by decide

/-- 32 public words at 32 bytes, plus ABI offsets and lengths -/
theorem the_envelope_accounted : 32 * 32 + 368 = 1392 := by decide

theorem calldata_is_under_the_size_ceiling : calldataBytes ≤ 131072 := by decide

end Shield.Settlement
