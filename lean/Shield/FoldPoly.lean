-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Horner
import Shield.Fold

/-!
The FRI fold as an operation on polynomials, and why the verifier's two-point
formula computes it.

A polynomial splits by parity of exponent: `f(x) = E(x^2) + x O(x^2)`. The
fold at challenge `beta` is `E + beta O`, a polynomial in `x^2` of half the
degree. The verifier never sees `E` or `O`; it sees `f` at `x` and at `-x`,
where `f(-x) = E(x^2) - x O(x^2)`, and recovers `E` as half the sum and `O`
as half the difference over `x`. Everything is over `Nat`, so the value at
`-x` is carried as the `b` with `b + x O = E`, and the halving is stated
modulo the field with the inverse of two the verifier hard-codes.
-/

namespace Shield.FoldPoly

open Shield.Horner (hornerN reducing_the_right_factor_first_is_free)

/-- the even-index coefficients -/
def evens : List Nat → List Nat
  | [] => []
  | [c] => [c]
  | c :: _ :: rest => c :: evens rest

/-- the odd-index coefficients -/
def odds : List Nat → List Nat
  | [] => []
  | [_] => []
  | _ :: d :: rest => d :: odds rest

theorem evens_of_four : evens [1, 2, 3, 4] = [1, 3] := rfl
theorem odds_of_four : odds [1, 2, 3, 4] = [2, 4] := rfl
theorem evens_of_five : evens [1, 2, 3, 4, 5] = [1, 3, 5] := rfl
theorem odds_of_five : odds [1, 2, 3, 4, 5] = [2, 4] := rfl

/-- `f(x) = E(x^2) + x O(x^2)` -/
theorem split (x : Nat) : ∀ f : List Nat,
    hornerN x f = hornerN (x * x) (evens f) + x * hornerN (x * x) (odds f)
  | [] => by simp only [hornerN, evens, odds, Nat.mul_zero, Nat.add_zero]
  | [c] => by simp only [hornerN, evens, odds, Nat.mul_zero, Nat.add_zero]
  | c :: d :: rest => by
    have ih := split x rest
    show c + x * (d + x * hornerN x rest) =
      (c + x * x * hornerN (x * x) (evens rest)) + x * (d + x * x * hornerN (x * x) (odds rest))
    rw [ih]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

/-! ## The folded polynomial -/

def add : List Nat → List Nat → List Nat
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: add as bs

def scale (k : Nat) : List Nat → List Nat := List.map (k * ·)

/-- `E + beta O`, the polynomial the next FRI layer commits to -/
def foldPoly (beta : Nat) (f : List Nat) : List Nat := add (evens f) (scale beta (odds f))

theorem horner_add (y : Nat) : ∀ as bs : List Nat,
    hornerN y (add as bs) = hornerN y as + hornerN y bs
  | [], bs => by simp only [add, hornerN, Nat.zero_add]
  | a :: as, [] => by simp only [add, hornerN, Nat.add_zero]
  | a :: as, b :: bs => by
    have ih := horner_add y as bs
    show (a + b) + y * hornerN y (add as bs) = (a + y * hornerN y as) + (b + y * hornerN y bs)
    rw [ih, Nat.mul_add]
    omega

theorem horner_scale (y k : Nat) : ∀ cs : List Nat, hornerN y (scale k cs) = k * hornerN y cs
  | [] => by simp only [scale, List.map, hornerN, Nat.mul_zero]
  | c :: cs => by
    have ih := horner_scale y k cs
    show k * c + y * hornerN y (scale k cs) = k * (c + y * hornerN y cs)
    rw [ih, Nat.mul_add, Nat.mul_left_comm y k]

/-- the folded polynomial at `y` is `E(y) + beta O(y)` -/
theorem fold_eval (beta y : Nat) (f : List Nat) :
    hornerN y (foldPoly beta f) = hornerN y (evens f) + beta * hornerN y (odds f) := by
  unfold foldPoly
  rw [horner_add, horner_scale]

/-- folding halves the length, rounding up -/
theorem evens_length : ∀ f : List Nat, (evens f).length = (f.length + 1) / 2
  | [] => rfl
  | [_] => by simp [evens]
  | _ :: _ :: rest => by
    show (evens rest).length + 1 = (rest.length + 2 + 1) / 2
    rw [evens_length rest]
    omega

theorem odds_length : ∀ f : List Nat, (odds f).length = f.length / 2
  | [] => rfl
  | [_] => by simp [odds]
  | _ :: _ :: rest => by
    show (odds rest).length + 1 = (rest.length + 2) / 2
    rw [odds_length rest]
    omega

theorem add_length : ∀ as bs : List Nat, (add as bs).length = max as.length bs.length
  | [], bs => by simp only [add, List.length_nil, Nat.zero_max]
  | a :: as, [] => by simp only [add, List.length_nil, Nat.max_zero]
  | a :: as, b :: bs => by
    show (add as bs).length + 1 = max (as.length + 1) (bs.length + 1)
    rw [add_length as bs, Nat.succ_max_succ]

theorem scale_length (k : Nat) (cs : List Nat) : (scale k cs).length = cs.length :=
  List.length_map cs _

theorem fold_length (beta : Nat) (f : List Nat) : (foldPoly beta f).length = (f.length + 1) / 2 := by
  unfold foldPoly
  rw [add_length, scale_length, evens_length, odds_length]
  omega

/-- six folds of radix two take 2^21 coefficients to 2^15; the shipped radix-four layers take
two of these each -/
theorem six_folds : (2 ^ 21 + 1) / 2 = 2 ^ 20 ∧ (2 ^ 16 + 1) / 2 = 2 ^ 15 := by decide

/-! ## What the verifier holds: the values at `x` and `-x` -/

/-- with `a = f(x)` and `b = f(-x)`, `a + b = 2 E` and `a = b + 2 x O`. Over `Nat` the value at
`-x` is the `b` with `b + x O = E`. -/
theorem verifier_pair (x b : Nat) (f : List Nat)
    (hb : b + x * hornerN (x * x) (odds f) = hornerN (x * x) (evens f)) :
    hornerN x f + b = 2 * hornerN (x * x) (evens f) ∧
    hornerN x f = b + 2 * (x * hornerN (x * x) (odds f)) := by
  rw [split x f]
  omega

/-- halving with the field's inverse of two: `2 E * inv2 ≡ E` -/
theorem half_of_double (E i m : Nat) (h2 : 2 * i % m = 1) : (2 * E * i) % m = E % m := by
  rw [Nat.mul_right_comm 2 E i, Nat.mul_comm (2 * i) E,
    ← reducing_the_right_factor_first_is_free E (2 * i) m, h2, Nat.mul_one]

/-- the even lane of `Shield.Fold`: `(a + b) * inv2` is `E` modulo the prime -/
theorem the_even_lane (x b : Nat) (f : List Nat)
    (hb : b + x * hornerN (x * x) (odds f) = hornerN (x * x) (evens f)) :
    ((hornerN x f + b) * Shield.Fold.inv2) % Shield.Fold.p =
      hornerN (x * x) (evens f) % Shield.Fold.p := by
  rw [(verifier_pair x b f hb).1]
  exact half_of_double _ _ _ Shield.Fold.inv2_halves

/-- the odd lane before the division by `x`: `(a - b) * inv2` is `x O`, carried as `a = b + 2 x O` -/
theorem the_odd_lane (x b : Nat) (f : List Nat)
    (hb : b + x * hornerN (x * x) (odds f) = hornerN (x * x) (evens f)) :
    ((hornerN x f - b) * Shield.Fold.inv2) % Shield.Fold.p =
      (x * hornerN (x * x) (odds f)) % Shield.Fold.p := by
  have h := (verifier_pair x b f hb).2
  have e : hornerN x f - b = 2 * (x * hornerN (x * x) (odds f)) := by omega
  rw [e]
  exact half_of_double _ _ _ Shield.Fold.inv2_halves

/-! ## A case in the field of seven -/

/-- `f = 1 + 2x + 3x^2 + 4x^3` at `x = 2` and `x = -2 = 5`: `E(4) - 2 O(4) = 13 - 36`, which is
five modulo seven -/
theorem seven_values : hornerN 2 [1, 2, 3, 4] % 7 = 0 ∧ hornerN 5 [1, 2, 3, 4] % 7 = 5 := by
  decide

/-- `E = 1 + 3y`, `O = 2 + 4y` at `y = 4`: `E = 13`, `O = 18`; `f(2) = 13 + 2 * 18 = 49` -/
theorem seven_split : hornerN 2 [1, 2, 3, 4] = 49 ∧ hornerN 4 (evens [1, 2, 3, 4]) = 13 ∧
    hornerN 4 (odds [1, 2, 3, 4]) = 18 := by decide

/-- the fold at `beta = 3`: `E + 3 O = (1 + 6) + (3 + 12) y` -/
theorem seven_fold : foldPoly 3 [1, 2, 3, 4] = [7, 15] ∧ hornerN 4 (foldPoly 3 [1, 2, 3, 4]) = 67 ∧
    67 = 13 + 3 * 18 := by decide

end Shield.FoldPoly
