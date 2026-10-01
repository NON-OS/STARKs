-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The calldata floor, and what it rules out.

Under EIP-7623 a transaction costs
`21000 + max(4 * tokens + execution, 10 * tokens)`, where a token is one zero
byte or four non zero ones. The floor binds whenever execution is below
`6 * tokens`, which for anything proof shaped means calldata sets the budget
before a single opcode runs.

Proof bytes are field elements, so a byte is zero about one time in 256 and
the dense count is the right model. A five percent zero fraction is optimistic
by an order of magnitude.
-/

namespace Shield.Gas

def tokens (zeroBytes nonZeroBytes : Nat) : Nat := zeroBytes + 4 * nonZeroBytes

/-- What a transaction costs, floor included. -/
def total (zeroBytes nonZeroBytes execution : Nat) : Nat :=
  21000 + max (4 * tokens zeroBytes nonZeroBytes + execution)
              (10 * tokens zeroBytes nonZeroBytes)

/-- Dense bytes, the model proof data actually meets. -/
def dense (bytes execution : Nat) : Nat := total 0 bytes execution

def oneMillion : Nat := 1000000

/-- Below this much execution the floor binds and the verifier is free. -/
def executionUntilTheFloorLifts (bytes : Nat) : Nat := 6 * tokens 0 bytes

theorem the_floor_binds_for_proof_shaped_work :
    dense 24224 285000 = 21000 + 10 * tokens 0 24224 := by decide

/-- The settlement proof today, and after each phase of the size table. -/
def v11 : Nat := 122784
def afterFoldEight : Nat := 115616
def afterRetune : Nat := 89184

/-- None of them fits. Over three million on bytes alone after every phase of
the size table, so no amount of verifier work saves the settlement proof. -/
theorem the_settlement_proof_never_fits :
    3000000 < dense v11 0
    ∧ 3000000 < dense afterFoldEight 0
    ∧ 3000000 < dense afterRetune 0 := by decide

/-- The two larger ones miss even at the cheapest calldata can be, every byte
a zero. The retuned one clears that bound at 912,840, which says something
about the bound rather than about the proof: proof bytes are not zeros. -/
theorem the_larger_two_miss_even_at_the_zero_byte_bound :
    oneMillion < total v11 0 0
    ∧ oneMillion < total afterFoldEight 0 0
    ∧ total afterRetune 0 0 < oneMillion := by decide

/-- The wrap, at the size the envelope allows. -/
def wrapBytes : Nat := 24224

/-- It fits, densely, with the verifier's work absorbed under the floor. -/
theorem the_wrap_fits : dense wrapBytes 285000 < oneMillion := by decide

/-- The margin is thin. Ten thousand gas is about two hundred and fifty extra
bytes, so a codec change that grows the proof by one percent spends it. -/
theorem the_margin_is_thin : oneMillion - dense wrapBytes 285000 < 11000 := by decide

/-- The verifier has room to be five hundred thousand gas before the floor
lifts and execution starts adding to the bill. -/
theorem the_verifier_has_room :
    500000 < executionUntilTheFloorLifts wrapBytes := by decide

theorem more_verifier_work_is_free_under_the_floor :
    dense wrapBytes 285000 = dense wrapBytes 500000 := by decide

/-- Two output commitments per payment, published so wallets can build the
tree. Nullifiers ride calldata too and are not stored, which is what turns
forty thousand gas of cold storage into five thousand of bytes. -/
def perIntentBytes : Nat := 64

/-- The wrap amortised over a batch, plus each payment's own bytes. -/
def perPayment (wrapGas n : Nat) : Nat := wrapGas / n + 10 * tokens 0 perIntentBytes

def wrapGas : Nat := dense wrapBytes 285000

/-- One payment under one proof is already inside the budget. -/
theorem one_payment_fits : perPayment wrapGas 1 < oneMillion := by decide

/-- Twenty payments under one proof cost less each than a token transfer. -/
theorem twenty_payments_beat_a_token_transfer : perPayment wrapGas 20 < 65000 := by
  decide

/-- Ten do not. The crossover sits between them, and the difference is one
doubling of the batch. -/
theorem ten_payments_do_not : 65000 < perPayment wrapGas 10 := by decide

/-- A hundred payments, which is also the anonymity set. -/
theorem a_hundred_payments_are_cheap : perPayment wrapGas 100 < 13000 := by decide

/-- Amortisation falls as the batch grows, and the per payment bytes are the
floor it falls to. -/
theorem amortisation_falls :
    perPayment wrapGas 100 < perPayment wrapGas 20
    ∧ perPayment wrapGas 20 < perPayment wrapGas 10
    ∧ perPayment wrapGas 10 < perPayment wrapGas 1 := by decide

theorem the_per_payment_floor_is_its_own_bytes :
    10 * tokens 0 perIntentBytes ≤ perPayment wrapGas 1000000 := by decide

end Shield.Gas
