-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The base-field lane of one FRI fold, as the verifier computes it:
`(a + b) / 2 + beta * ((a - b) / 2) / x` modulo the Goldilocks prime.
Subtraction is written so it never underflows and every product is reduced
before the next one, which is how the contract spells it.
-/

namespace Shield.Fold

def p : Nat := 18446744069414584321

/-- One half in the field. -/
def inv2 : Nat := 9223372034707292161

/-- Subtraction modulo `p` that never goes below zero. -/
def sub (a b : Nat) : Nat := (a + (p - b % p)) % p

/-- The even part: the mean of the pair. -/
def even (a b : Nat) : Nat := (a + b) * inv2 % p

/-- The odd part: half the difference, divided by the coset point. -/
def odd (a b invx : Nat) : Nat := sub a b * inv2 % p * invx % p

def fold (a b beta invx : Nat) : Nat := (even a b + beta * odd a b invx) % p

/-! the constants -/

theorem p_pos : 0 < p := by decide

theorem inv2_halves : 2 * inv2 % p = 1 := by decide

/-- One half is the element just above the middle of the field. -/
theorem inv2_twice_is_one_past_p : inv2 + inv2 = p + 1 := by decide

theorem inv2_below_p : inv2 < p := by decide

/-! subtraction -/

theorem sub_plain : sub 6 4 = 2 := by decide

/-- Below zero it wraps to the top of the field instead of truncating. -/
theorem sub_wraps : sub 4 6 = p - 2 := by decide

theorem sub_zero_zero : sub 0 0 = 0 := by decide

theorem sub_top : sub (p - 1) 1 = p - 2 := by decide

theorem sub_lt (a b : Nat) : sub a b < p := by
  unfold sub
  exact Nat.mod_lt _ p_pos

/-- A reduced value minus itself is zero. -/
theorem sub_self (a : Nat) (h : a < p) : sub a a = 0 := by
  unfold sub
  rw [Nat.mod_eq_of_lt h]
  have e : a + (p - a) = p := by omega
  rw [e, Nat.mod_self]

/-! the two parts -/

theorem even_six_four : even 6 4 = 5 := by decide

theorem odd_six_four : odd 6 4 1 = 1 := by decide

/-- Reversed, the odd part is the negation of one. -/
theorem odd_four_six : odd 4 6 1 = p - 1 := by decide

theorem even_lt (a b : Nat) : even a b < p := by
  unfold even
  exact Nat.mod_lt _ p_pos

theorem odd_lt (a b invx : Nat) : odd a b invx < p := by
  unfold odd
  exact Nat.mod_lt _ p_pos

/-- The even part does not see the order of the pair. -/
theorem even_comm (a b : Nat) : even a b = even b a := by
  unfold even
  rw [Nat.add_comm a b]

/-- Equal values have no odd part. -/
theorem odd_of_equal (a invx : Nat) (h : a < p) : odd a a invx = 0 := by
  unfold odd
  rw [sub_self a h, Nat.zero_mul, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]

/-- A zero inverse would drop the odd part, so the verifier must never be handed one. -/
theorem odd_of_zero_inverse (a b : Nat) : odd a b 0 = 0 := by
  unfold odd
  rw [Nat.mul_zero, Nat.zero_mod]

/-- The mean of a reduced value with itself is the value. -/
theorem mean_of_equal (v : Nat) (h : v < p) : (v + v) * inv2 % p = v := by
  have h2 : inv2 + inv2 = p + 1 := inv2_twice_is_one_past_p
  have e : (v + v) * inv2 = v * p + v := by
    rw [Nat.add_mul, ← Nat.mul_add, h2, Nat.mul_add, Nat.mul_one]
  rw [e, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt h]

theorem mean_of_six : (6 + 6) * inv2 % p = 6 := by decide

/-! the fold on concrete pairs -/

/-- A zero challenge keeps the mean. -/
theorem fold_six_four_at_zero : fold 6 4 0 1 = 5 := by decide

theorem fold_six_four_at_one : fold 6 4 1 1 = 6 := by decide

/-- The order of the pair reaches the result through the odd part. -/
theorem fold_four_six_at_one : fold 4 6 1 1 = 4 := by decide

theorem the_order_matters : fold 6 4 1 1 ≠ fold 4 6 1 1 := by decide

/-- At a zero challenge the order no longer matters. -/
theorem the_order_is_lost_at_zero : fold 6 4 0 1 = fold 4 6 0 1 := by decide

/-- Equal values fold to themselves whatever the challenge and the point. -/
theorem fold_six_six : fold 6 6 12345 999 = 6 := by decide

theorem fold_zero_zero : fold 0 0 5 7 = 0 := by decide

/-- The pair `p - 1, 1` sums to `p`, so its mean is zero. -/
theorem fold_wraps_to_zero : fold (p - 1) 1 0 1 = 0 := by decide

/-- The same pair at challenge one: the odd part is `p - 1`. -/
theorem fold_wraps_at_one : fold (p - 1) 1 1 1 = p - 1 := by decide

theorem odd_of_the_wrapping_pair : odd (p - 1) 1 1 = p - 1 := by decide

/-- The pair `1, 2` has a mean that is not a small number. -/
theorem fold_one_two_at_zero : fold 1 2 0 1 = 9223372034707292162 := by decide

theorem fold_one_two_is_three_halves : fold 1 2 0 1 = 3 * inv2 % p := by decide

theorem fold_ten_two : fold 10 2 3 1 = 18 ∧ fold 10 2 2 1 = 14 := by decide

/-! the fold in general -/

theorem fold_lt (a b beta invx : Nat) : fold a b beta invx < p := by
  unfold fold
  exact Nat.mod_lt _ p_pos

/-- A zero challenge leaves only the even part. -/
theorem fold_at_zero (a b invx : Nat) : fold a b 0 invx = even a b := by
  unfold fold
  rw [Nat.zero_mul, Nat.add_zero]
  unfold even
  rw [Nat.mod_mod]

/-- So does a zero inverse. -/
theorem fold_at_zero_inverse (a b beta : Nat) : fold a b beta 0 = even a b := by
  unfold fold
  rw [odd_of_zero_inverse a b, Nat.mul_zero, Nat.add_zero]
  unfold even
  rw [Nat.mod_mod]

/-- Equal values fold to their mean, for every challenge and point. -/
theorem fold_of_equal (a beta invx : Nat) (h : a < p) :
    fold a a beta invx = (a + a) * inv2 % p := by
  unfold fold
  rw [odd_of_equal a invx h, Nat.mul_zero, Nat.add_zero]
  unfold even
  rw [Nat.mod_mod]

/-- And that mean is the value itself. -/
theorem fold_self (a beta invx : Nat) (h : a < p) : fold a a beta invx = a := by
  rw [fold_of_equal a beta invx h]
  exact mean_of_equal a h

/-- The challenge is only ever read reduced. -/
theorem fold_reads_beta_reduced (a b beta invx : Nat) :
    fold a b (beta % p) invx = fold a b beta invx := by
  unfold fold
  rw [Nat.add_mod (even a b) (beta % p * odd a b invx) p,
    Nat.mul_mod (beta % p) (odd a b invx) p, Nat.mod_mod,
    ← Nat.mul_mod beta (odd a b invx) p, ← Nat.add_mod (even a b) (beta * odd a b invx) p]

theorem beta_reduced_concrete : fold 6 4 (p + 1) 1 = fold 6 4 1 1 := by decide

/-! radix four as two levels of radix two -/

/-- The first level pairs `v0` with `v2` and `v1` with `v3`, the second level folds the two
results at the squared challenge and the squared point. -/
def quad (v0 v1 v2 v3 beta invx invx1 : Nat) : Nat :=
  fold (fold v0 v2 beta invx) (fold v1 v3 beta invx1) (beta * beta % p) (invx * invx % p)

theorem quad_pairs (v0 v1 v2 v3 b x y : Nat) :
    quad v0 v1 v2 v3 b x y = fold (fold v0 v2 b x) (fold v1 v3 b y) (b * b % p) (x * x % p) :=
  rfl

theorem quad_lt (v0 v1 v2 v3 b x y : Nat) : quad v0 v1 v2 v3 b x y < p := by
  unfold quad
  exact fold_lt _ _ _ _

theorem quad_six : quad 6 6 6 6 3 5 7 = 6 := by decide

/-- At a zero challenge radix four is the mean of the two means. -/
theorem quad_at_zero : quad 1 2 3 4 0 1 1 = 5 * inv2 % p := by decide

theorem quad_at_zero_value : quad 1 2 3 4 0 1 1 = 9223372034707292163 := by decide

theorem quad_at_zero_is_even_of_evens :
    quad 1 2 3 4 0 1 1 = even (even 1 3) (even 2 4) := by decide

theorem quad_one : quad 1 2 3 4 1 1 1 = 1 := by decide

theorem quad_zero : quad 0 0 0 0 9 9 9 = 0 := by decide

/-- Swapping the pairing changes the result: `v1` with `v2` is not the same fold. -/
theorem quad_pairing_matters : quad 1 2 3 4 2 1 1 ≠ quad 1 3 2 4 2 1 1 := by decide

/-- A constant leaf folds to its value for every challenge and every pair of points. -/
theorem quad_of_constant (v b x y : Nat) (h : v < p) : quad v v v v b x y = v := by
  unfold quad
  rw [fold_self v b x h, fold_self v b y h]
  exact fold_self v _ _ h

/-- At a zero challenge the first level is two means. -/
theorem quad_first_level_at_zero (v0 v1 v2 v3 x y : Nat) :
    quad v0 v1 v2 v3 0 x y = fold (even v0 v2) (even v1 v3) 0 (x * x % p) := by
  unfold quad
  rw [fold_at_zero v0 v2 x, fold_at_zero v1 v3 y, Nat.zero_mul, Nat.zero_mod]

/-- And the second level is the mean of those. -/
theorem quad_at_zero_general (v0 v1 v2 v3 x y : Nat) :
    quad v0 v1 v2 v3 0 x y = even (even v0 v2) (even v1 v3) := by
  rw [quad_first_level_at_zero]
  exact fold_at_zero _ _ _

end Shield.Fold
