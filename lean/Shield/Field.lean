-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The Goldilocks field, and the arithmetic facts the verifier's constants rest on.

The on-chain verifier hard-codes the modulus, one half, the reduction
identity and the extension `X^2 - 7`. Each is stated here and checked by the
kernel, so a transcription error in any of them fails the build.

Exponentiation to a 63-bit power cannot be evaluated directly, so `powMod`
squares and multiplies with a step budget, and `powMod_eq` proves it equals
`b ^ e % m` whenever the budget covers the exponent's bits. The large facts are
then decided through it, never assumed.

Everything is `Nat`, core only.
-/

namespace Shield.Field

/-- The Goldilocks prime. -/
def p : Nat := 2 ^ 64 - 2 ^ 32 + 1

theorem p_value : p = 18446744069414584321 := by decide

/-- `p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`: a multiplicative subgroup of order `2^32`,
which is what makes the number-theoretic transform exist at every power of two to that size. -/
theorem p_minus_one : p - 1 = 2 ^ 32 * (3 * 5 * 17 * 257 * 65537) := by decide

/-- The two-adicity is exactly 32: the odd part is odd. -/
theorem two_adicity : (p - 1) % 2 ^ 32 = 0 ∧ (p - 1) / 2 ^ 32 % 2 = 1 := by decide

/-- The reduction identity the verifier's arithmetic leans on: `2^64 ≡ 2^32 - 1 (mod p)`. -/
theorem reduction : 2 ^ 64 % p = 2 ^ 32 - 1 := by decide

/-- The constant the fold hard-codes as one half. -/
def inv2 : Nat := 9223372034707292161

theorem inv2_is_one_half : 2 * inv2 % p = 1 := by decide

/-! ## Exponentiation, with a proof that it is exponentiation -/

/-- Square and multiply, with `fuel` steps. Structural in `fuel`, so the kernel evaluates it. -/
def powMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let r := powMod fuel (b * b % m) (e / 2) m
      if e % 2 = 0 then r else b % m * r % m

private theorem sq_pow (b k : Nat) : (b * b) ^ k = b ^ (2 * k) := by
  rw [Nat.pow_mul, Nat.pow_two]

/-- Reducing the base first does not change a power's residue. -/
private theorem pow_mod_base (a n m : Nat) : (a % m) ^ n % m = a ^ n % m := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]

/-- `powMod` is `b ^ e % m` whenever the step budget covers the exponent. -/
theorem powMod_eq : ∀ (fuel b e m : Nat), e < 2 ^ fuel → powMod fuel b e m = b ^ e % m
  | 0, b, e, m, h => by
    have : e = 0 := by simp at h; omega
    subst this; simp [powMod]
  | fuel + 1, b, e, m, h => by
    simp only [powMod]
    by_cases he : e = 0
    · subst he; simp
    · rw [if_neg he]
      have hlt : e / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at h; omega
      rw [powMod_eq fuel (b * b % m) (e / 2) m hlt, pow_mod_base, sq_pow]
      by_cases hpar : e % 2 = 0
      · rw [if_pos hpar, show 2 * (e / 2) = e by omega]
      · rw [if_neg hpar, ← Nat.mul_mod, ← Nat.pow_succ', show Nat.succ (2 * (e / 2)) = e by omega]

/-! ## The extension -/

set_option maxRecDepth 100000 in
/-- `7^((p-1)/2) ≡ -1 (mod p)`. By Euler's criterion, if `p` is prime this says 7 is not a
square mod `p`, so `X^2 - 7` has no root and `F_p[X]/(X^2 - 7)` is a field. The primality of
`p` is not proved in this file; the congruence is. -/
theorem seven_to_half_is_minus_one : 7 ^ ((p - 1) / 2) % p = p - 1 := by
  rw [← powMod_eq 64 7 ((p - 1) / 2) p (by decide)]
  decide

set_option maxRecDepth 100000 in
/-- The fold's per-layer inverse of two agrees with the exponentiation route to it. -/
theorem inv2_by_fermat_form : powMod 64 2 (p - 2) p = inv2 := by decide

end Shield.Field
