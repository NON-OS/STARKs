-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Conservation in the balance region, from the constraints it enforces modulo p to the integer
statement `Shield.Balance.balanced` assumes. The circuit checks two congruences, one per limb
column, and range-checks every limb, every high limb's room and the carry. These are enough
for the integer sum to balance. Without the bounds a congruence modulo p admits a transfer that
creates value, and `modular_balance_alone_creates_value` exhibits one.

Core only. Everything is `Int`, and `omega` closes each bound.
-/

namespace Shield.LimbBalance

/-- The Goldilocks prime. -/
def p : Int := 18446744069414584321

/-- The limb base, `2^32`. -/
def B : Int := 4294967296

/-- A value's limbs as the range region bounds them: the low limb below `2^32`, the high limb
at most `2^32 - 2`, so its room `2^32 - 2 - hi` is in range too. -/
def Limbs (lo hi : Int) : Prop := 0 ≤ lo ∧ lo < 4294967296 ∧ 0 ≤ hi ∧ hi ≤ 4294967294

/-- A bounded value is below `p - 1`, so its field value and its integer value agree. -/
theorem a_bounded_value_is_below_p (lo hi : Int) (h : Limbs lo hi) :
    0 ≤ lo + B * hi ∧ lo + B * hi < p - 1 := by
  simp only [Limbs, B, p] at *
  omega

/-- A bounded value that is zero modulo p is zero, so a dummy input carries nothing. -/
theorem a_bounded_value_zero_mod_p_is_zero (lo hi k : Int) (h : Limbs lo hi)
    (hz : lo + B * hi = k * p) : lo + B * hi = 0 := by
  simp only [Limbs, B, p] at *
  omega

/-- The limb-wise closing constraints give integer conservation. Legs 0 and 1 are the inputs,
2 and 3 the outputs, 4 the public amount and 5 the fee. The carry cell holds `c + 3` in
`[0, 8)`. The two hypotheses `hlo` and `hhi` are the closing constraints as congruences. -/
theorem limbwise_conservation
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 c k1 k2 : Int)
    (h0 : Limbs a0 b0) (h1 : Limbs a1 b1) (h2 : Limbs a2 b2)
    (h3 : Limbs a3 b3) (h4 : Limbs a4 b4) (h5 : Limbs a5 b5)
    (hc : 0 ≤ c + 3 ∧ c + 3 < 8)
    (hlo : (a0 + a1 - a2 - a3 - a4 - a5) - c * B = k1 * p)
    (hhi : (b0 + b1 - b2 - b3 - b4 - b5) + c = k2 * p) :
    (a0 + B * b0) + (a1 + B * b1)
      = (a2 + B * b2) + (a3 + B * b3) + (a4 + B * b4) + (a5 + B * b5) := by
  simp only [Limbs, B, p] at *
  omega

/-- The carry the honest prover writes lies in `[-3, 1]`, inside the checked range. -/
theorem the_carry_fits_three_bits
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 c : Int)
    (h0 : Limbs a0 b0) (h1 : Limbs a1 b1) (h2 : Limbs a2 b2)
    (h3 : Limbs a3 b3) (h4 : Limbs a4 b4) (h5 : Limbs a5 b5)
    (hlo : a0 + a1 - a2 - a3 - a4 - a5 = c * B) :
    0 ≤ c + 3 ∧ c + 3 < 8 := by
  simp only [Limbs, B] at *
  omega

/-- Without the bounds, one congruence modulo p is satisfied by a transfer that creates
`10^18`: inputs worth 1 and 1, outputs worth `2 + 10^18` and `p - 10^18`. Both outputs are
honest 64-bit amounts. -/
theorem modular_balance_alone_creates_value :
    let K : Int := 1000000000000000000
    let inA : Int := 1
    let inB : Int := 1
    let outA : Int := 2 + K
    let outB : Int := p - K
    (inA + inB - outA - outB = (-1) * p) ∧ outA > inA + inB ∧ outB < 18446744073709551616 := by
  simp only [p]
  decide

end Shield.LimbBalance
