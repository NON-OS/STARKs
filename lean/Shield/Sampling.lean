-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
How a challenge is drawn from a squeezed 64-bit word, and what it costs.

Reducing a word w < 2^64 to w mod p (`Fp::from_u64`: w - p when w ≥ p) is
not uniform. Values below 2^64 - p = 2^32 - 1 then have two preimages,
so each coordinate of a challenge lands on a given value with probability at
most 2 / 2^64, where a uniform draw gives 1 / p. A round's error counts its
bad challenges; if a prover could place them all on doubled values in both
coordinates of an F_p^2 challenge, each would be hit 4 / 2^128 of the time,
not 1 / p^2: up to 2 bits off that round, in the worst case.

The `fri8` build draws exactly: each 64-bit lane is accepted only when below p, and the next
lane is taken otherwise. An accepted lane is uniform on F_p. A lane is refused
with probability (2^32 - 1) / 2^64, under 2^-32.
-/

namespace Shield.Sampling

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

def p : Nat := Shield.Launch.p

theorem doubled_values : 2 ^ 64 - p = 2 ^ 32 - 1 := by decide

/-- Every 64-bit word below 2 p, so a reduced value has at most two preimages:
the value itself and the value plus p. -/
theorem words_below_two_p : 2 ^ 64 < 2 * p := by decide

theorem at_most_two_preimages (w x : Nat) (hw : w < 2 ^ 64) (h : w % p = x) :
    w = x ∨ w = x + p := by
  have h2 : w < 2 * p := Nat.lt_trans hw words_below_two_p
  by_cases hlt : w < p
  · left
    rw [Nat.mod_eq_of_lt hlt] at h
    exact h
  · right
    have hge : p ≤ w := Nat.le_of_not_lt hlt
    have hm : w % p = w - p := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The worst case for one F_p^2 challenge: a point hit with probability
(2 / 2^64)^2 against 1 / p^2 is at most four times as likely. -/
theorem worst_case_factor_is_four : 4 * p ^ 2 < 4 * 2 ^ 128 ∧ 2 ^ 128 < 2 * p ^ 2 := by decide

/-- The `fri8` rejection draw refuses a lane with probability below 2^-32. -/
theorem refusal_below_2_32 : (2 ^ 64 - p) * 2 ^ 32 < 2 ^ 64 := by decide


end Shield.Sampling
