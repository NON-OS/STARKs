-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Field

/-!
Roots of unity for the number-theoretic transform over Goldilocks.

Each root is stated as a `powMod` fact decided by the kernel and then lifted to
`b ^ e % p` through `powMod_eq`. The order of a root is pinned by a power that is
one and a half power that is `p - 1`.
-/

namespace Shield.Roots

open Shield.Field (p powMod powMod_eq)

/-- The multiplicative generator the roots are drawn from. -/
def generator : Nat := 7

/-- A root of order `2^32`, `7 ^ ((p - 1) / 2^32)`. -/
def omega32 : Nat := 1753635133440165772

/-- The shipped domain's root, of order `2^29`. -/
def omega29 : Nat := 16116352524544190054

/-- The fold's inverse of two. -/
def inv2 : Nat := 9223372034707292161

/-- The fold's inverse of seven. -/
def inv7 : Nat := 2635249152773512046

/-! ## Sizes -/

theorem two_to_the_twenty_nine : 2 ^ 29 = 536870912 := by decide

theorem two_to_the_thirty_two : 2 ^ 32 = 4294967296 := by decide

theorem two_to_the_thirty_one : 2 ^ 31 = 2147483648 := by decide

theorem two_to_the_twenty_eight : 2 ^ 28 = 268435456 := by decide

theorem roots_are_field_elements : omega32 < p ∧ omega29 < p ∧ inv2 < p ∧ inv7 < p := by
  decide

theorem exponents_fit_the_fuel :
    2 ^ 32 < 2 ^ 64 ∧ 2 ^ 31 < 2 ^ 64 ∧ 2 ^ 29 < 2 ^ 64 ∧ 2 ^ 28 < 2 ^ 64 ∧
      p - 1 < 2 ^ 64 ∧ p - 2 < 2 ^ 64 := by
  decide

/-! ## The generator -/

set_option maxRecDepth 100000 in
theorem fermat_powMod : powMod 64 generator (p - 1) p = 1 := by decide

theorem fermat : generator ^ (p - 1) % p = 1 :=
  (powMod_eq 64 generator (p - 1) p (by decide)).symm.trans fermat_powMod

set_option maxRecDepth 100000 in
theorem omega32_from_generator_powMod : powMod 64 generator ((p - 1) / 2 ^ 32) p = omega32 := by
  decide

/-- `omega32` is the generator raised to the odd part of `p - 1`. -/
theorem omega32_from_generator : generator ^ ((p - 1) / 2 ^ 32) % p = omega32 :=
  (powMod_eq 64 generator ((p - 1) / 2 ^ 32) p (by decide)).symm.trans
    omega32_from_generator_powMod

set_option maxRecDepth 100000 in
theorem omega29_from_generator_powMod : powMod 64 generator ((p - 1) / 2 ^ 29) p = omega29 := by
  decide

theorem omega29_from_generator : generator ^ ((p - 1) / 2 ^ 29) % p = omega29 :=
  (powMod_eq 64 generator ((p - 1) / 2 ^ 29) p (by decide)).symm.trans
    omega29_from_generator_powMod

/-! ## The root of order 2^32 -/

set_option maxRecDepth 100000 in
theorem omega32_full_powMod : powMod 64 omega32 (2 ^ 32) p = 1 := by decide

theorem omega32_full : omega32 ^ (2 ^ 32) % p = 1 :=
  (powMod_eq 64 omega32 (2 ^ 32) p (by decide)).symm.trans omega32_full_powMod

set_option maxRecDepth 100000 in
theorem omega32_half_powMod : powMod 64 omega32 (2 ^ 31) p = p - 1 := by decide

theorem omega32_half : omega32 ^ (2 ^ 31) % p = p - 1 :=
  (powMod_eq 64 omega32 (2 ^ 31) p (by decide)).symm.trans omega32_half_powMod

set_option maxRecDepth 100000 in
/-- A quarter of the way round is `2^48`, the square root of `-1` the radix-four butterfly uses. -/
theorem omega32_quarter_powMod : powMod 64 omega32 (2 ^ 30) p = 2 ^ 48 := by decide

theorem omega32_quarter : omega32 ^ (2 ^ 30) % p = 2 ^ 48 :=
  (powMod_eq 64 omega32 (2 ^ 30) p (by decide)).symm.trans omega32_quarter_powMod

theorem two_to_the_forty_eight_squared : 2 ^ 48 * 2 ^ 48 % p = p - 1 := by decide

/-! ## The shipped domain's root -/

set_option maxRecDepth 100000 in
theorem omega32_to_the_eighth_powMod : powMod 64 omega32 8 p = omega29 := by decide

/-- `omega29` is `omega32 ^ 8`, so both domains share one generator. -/
theorem omega32_to_the_eighth : omega32 ^ 8 % p = omega29 :=
  (powMod_eq 64 omega32 8 p (by decide)).symm.trans omega32_to_the_eighth_powMod

set_option maxRecDepth 100000 in
theorem omega29_full_powMod : powMod 64 omega29 (2 ^ 29) p = 1 := by decide

theorem omega29_full : omega29 ^ (2 ^ 29) % p = 1 :=
  (powMod_eq 64 omega29 (2 ^ 29) p (by decide)).symm.trans omega29_full_powMod

set_option maxRecDepth 100000 in
theorem omega29_half_powMod : powMod 64 omega29 (2 ^ 28) p = p - 1 := by decide

theorem omega29_half : omega29 ^ (2 ^ 28) % p = p - 1 :=
  (powMod_eq 64 omega29 (2 ^ 28) p (by decide)).symm.trans omega29_half_powMod

set_option maxRecDepth 100000 in
theorem omega29_quarter_powMod : powMod 64 omega29 (2 ^ 27) p = 2 ^ 48 := by decide

theorem omega29_quarter : omega29 ^ (2 ^ 27) % p = 2 ^ 48 :=
  (powMod_eq 64 omega29 (2 ^ 27) p (by decide)).symm.trans omega29_quarter_powMod

/-! ## The fold's inverses -/

theorem inv2_times_two : 2 * inv2 % p = 1 := by decide

theorem inv7_times_seven : 7 * inv7 % p = 1 := by decide

theorem inv2_is_the_field_constant : inv2 = Shield.Field.inv2 := rfl

set_option maxRecDepth 100000 in
theorem inv2_by_fermat_powMod : powMod 64 2 (p - 2) p = inv2 := by decide

theorem inv2_by_fermat : 2 ^ (p - 2) % p = inv2 :=
  (powMod_eq 64 2 (p - 2) p (by decide)).symm.trans inv2_by_fermat_powMod

set_option maxRecDepth 100000 in
theorem inv7_by_fermat_powMod : powMod 64 7 (p - 2) p = inv7 := by decide

theorem inv7_by_fermat : 7 ^ (p - 2) % p = inv7 :=
  (powMod_eq 64 7 (p - 2) p (by decide)).symm.trans inv7_by_fermat_powMod

/-! ## The order argument -/

theorem p_minus_one_ne_one : p - 1 ≠ 1 := by decide

theorem p_minus_one_squared : (p - 1) * (p - 1) % p = 1 := by decide

theorem p_minus_one_to_the_two : (p - 1) ^ 2 % p = 1 := by decide

/-- a value equal to `p - 1` is not one -/
theorem ne_one_of_eq_p_minus_one (v : Nat) (h : v = p - 1) : v ≠ 1 := by
  rw [h]
  exact p_minus_one_ne_one

/-- a power that is one whose half is `p - 1` has a half that is not one -/
theorem half_power_is_not_one (x k : Nat) (h1 : x ^ (2 * k) % p = 1)
    (h2 : x ^ k % p = p - 1) : x ^ k % p ≠ 1 ∧ x ^ (2 * k) % p = 1 :=
  ⟨ne_one_of_eq_p_minus_one _ h2, h1⟩

/-- reducing the base first does not change a power's residue -/
theorem pow_mod_base (a n m : Nat) : (a % m) ^ n % m = a ^ n % m := by
  induction n with
  | zero => simp only [Nat.pow_zero]
  | succ k ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]

theorem pow_square_pow (x k : Nat) : (x ^ 2) ^ (2 ^ k) = x ^ (2 ^ (k + 1)) := by
  rw [← Nat.pow_mul x 2 (2 ^ k), show 2 ^ (k + 1) = 2 * 2 ^ k by
    rw [Nat.pow_succ, Nat.mul_comm]]

/-- squaring a root halves the power that brings it to one -/
theorem squared_root (x k : Nat) : (x ^ 2 % p) ^ (2 ^ k) % p = x ^ (2 ^ (k + 1)) % p := by
  rw [pow_mod_base, pow_square_pow]

/-- a root whose `2^k` power is `p - 1` has `2^(k+1)` power one -/
theorem minus_one_then_one (x k : Nat) (h : x ^ (2 ^ k) % p = p - 1) :
    x ^ (2 ^ (k + 1)) % p = 1 := by
  rw [Nat.pow_succ, Nat.pow_mul x (2 ^ k) 2,
    ← pow_mod_base (x ^ 2 ^ k) 2 p, h]
  exact p_minus_one_to_the_two

/-- a root whose `2^k` power is `p - 1` does not have `2^k` power one -/
theorem minus_one_is_not_yet_one (x k : Nat) (h : x ^ (2 ^ k) % p = p - 1) :
    x ^ (2 ^ k) % p ≠ 1 :=
  ne_one_of_eq_p_minus_one _ h

theorem omega32_full_from_half : omega32 ^ (2 ^ (31 + 1)) % p = 1 :=
  minus_one_then_one omega32 31 omega32_half

theorem omega29_full_from_half : omega29 ^ (2 ^ (28 + 1)) % p = 1 :=
  minus_one_then_one omega29 28 omega29_half

theorem omega32_half_is_not_one : omega32 ^ (2 ^ 31) % p ≠ 1 :=
  minus_one_is_not_yet_one omega32 31 omega32_half

theorem omega29_half_is_not_one : omega29 ^ (2 ^ 28) % p ≠ 1 :=
  minus_one_is_not_yet_one omega29 28 omega29_half

/-- the order of `omega32` divides `2^32` and not `2^31`, so it is `2^32` -/
theorem omega32_has_order_two_to_the_thirty_two :
    omega32 ^ (2 ^ 32) % p = 1 ∧ omega32 ^ (2 ^ 31) % p ≠ 1 :=
  ⟨omega32_full, omega32_half_is_not_one⟩

/-- the order of `omega29` divides `2^29` and not `2^28`, so it is `2^29` -/
theorem omega29_has_order_two_to_the_twenty_nine :
    omega29 ^ (2 ^ 29) % p = 1 ∧ omega29 ^ (2 ^ 28) % p ≠ 1 :=
  ⟨omega29_full, omega29_half_is_not_one⟩

/-! ## Two-adicity -/

theorem odd_part : (p - 1) / 2 ^ 32 = 4294967295 := by decide

theorem odd_part_is_odd : (p - 1) / 2 ^ 32 % 2 = 1 := by decide

theorem two_to_the_thirty_two_divides : (p - 1) % 2 ^ 32 = 0 := by decide

/-- no subgroup of order `2^33`, so no root of that order -/
theorem two_to_the_thirty_three_does_not_divide : (p - 1) % 2 ^ 33 ≠ 0 := by decide

theorem p_minus_one_splits : p - 1 = 2 ^ 32 * 4294967295 := by decide

/-! ## Domains the prover may ask for -/

def twoAdicity : Nat := 32

def shippedLogDomain : Nat := 29

def shippedLogTrace : Nat := 21

/-- log size of the evaluation domain: trace, the extension step, and the blowup -/
def logDomain (logTrace ext logBlowup : Nat) : Nat := logTrace + ext + logBlowup

def supported (logTrace ext logBlowup : Nat) : Prop :=
  logDomain logTrace ext logBlowup ≤ twoAdicity

theorem shipped_domain_is_supported : shippedLogDomain ≤ twoAdicity := by decide

theorem shipped_domain_size : 2 ^ shippedLogDomain = 536870912 := by decide

theorem largest_blowup_at_this_trace : logDomain shippedLogTrace 1 10 = 32 := by decide

theorem one_more_is_too_many : logDomain shippedLogTrace 1 11 = 33 ∧ twoAdicity < 33 := by
  decide

theorem ten_is_supported : supported shippedLogTrace 1 10 := by
  unfold supported
  decide

theorem eleven_is_not_supported : ¬ supported shippedLogTrace 1 11 := by
  unfold supported
  decide

theorem supported_iff (t e b : Nat) (h : t + e ≤ twoAdicity) :
    supported t e b ↔ b ≤ twoAdicity - t - e := by
  simp only [supported, logDomain]
  constructor
  · intro h'
    omega
  · intro h'
    omega

theorem smaller_blowup_stays_supported (t e b c : Nat) (hc : c ≤ b)
    (h : supported t e b) : supported t e c := by
  simp only [supported, logDomain] at *
  omega

theorem a_larger_trace_leaves_less_blowup (t e b : Nat) (h : supported (t + 1) e b) :
    supported t e (b + 1) := by
  simp only [supported, logDomain] at *
  omega

end Shield.Roots
