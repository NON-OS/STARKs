-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Horner

/-!
The DEEP quotient as an object rather than a formula.

For a coefficient list `f` and a point `z`, `quot z f` is the list `q` with
`f(x) - f(z) = (x - z) q(x)`, built by synthetic division from the constant
term up. Everything is stated over `Nat` with no subtraction: the identity is
carried as `f(x) + z q(x) = x q(x) + f(z)`, which is the same equation with
its two negative terms moved across. Reduced modulo the field it gives the
value a verifier computes for the quotient at a query point,
`(f(x) - f(z)) / (x - z)`, as the evaluation of `q` there. That is the
`deep_value_is_the_quotient` theorem, and it is what lets FRI be run on `q`
in place of `f`: a degree bound on `q` is a bound one lower on `f`.
-/

namespace Shield.Poly

open Shield.Horner (hornerN eval reducing_once_at_the_end_agrees
  reducing_the_left_summand_first_is_free reducing_the_right_summand_first_is_free
  reducing_the_left_factor_first_is_free
  reducing_the_right_factor_first_is_free)

/-- synthetic division of `f` by `x - z`, lowest coefficient first; the top entry is always
zero, which keeps the list as long as `f` -/
def quot (z : Nat) : List Nat → List Nat
  | [] => []
  | _ :: cs => hornerN z cs :: quot z cs

theorem quot_nil (z : Nat) : quot z [] = [] := rfl

theorem quot_cons (z c : Nat) (cs : List Nat) :
    quot z (c :: cs) = hornerN z cs :: quot z cs := rfl

theorem quot_length (z : Nat) : ∀ f : List Nat, (quot z f).length = f.length
  | [] => rfl
  | _ :: cs => by
    show (quot z cs).length + 1 = cs.length + 1
    rw [quot_length z cs]

/-- the top coefficient of a list -/
def top : List Nat → Nat
  | [] => 0
  | [c] => c
  | _ :: c :: cs => top (c :: cs)

theorem top_of_quot (z : Nat) : ∀ f : List Nat, top (quot z f) = 0
  | [] => rfl
  | [_] => rfl
  | _ :: d :: cs => by
    show top (quot z (d :: cs)) = 0
    exact top_of_quot z (d :: cs)

/-! ## The division identity -/

/-- `f(x) + z q(x) = x q(x) + f(z)`, over `Nat`, for every `x` and `z` -/
theorem division (x z : Nat) : ∀ f : List Nat,
    hornerN x f + z * hornerN x (quot z f) = x * hornerN x (quot z f) + hornerN z f
  | [] => by simp only [hornerN, quot, Nat.mul_zero, Nat.add_zero]
  | c :: cs => by
    have ih := division x z cs
    show c + x * hornerN x cs + z * (hornerN z cs + x * hornerN x (quot z cs)) =
      x * (hornerN z cs + x * hornerN x (quot z cs)) + (c + z * hornerN z cs)
    have h2 : x * (hornerN x cs + z * hornerN x (quot z cs)) =
        x * (x * hornerN x (quot z cs) + hornerN z cs) := by
      rw [ih]
    rw [Nat.mul_add, Nat.mul_add] at h2
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm z x]
    omega

/-- the same identity on residues, which is all a verifier ever holds -/
theorem division_mod (m x z : Nat) (f : List Nat) :
    (eval m x f + z * hornerN x (quot z f)) % m =
      (x * hornerN x (quot z f) + eval m z f) % m := by
  rw [reducing_once_at_the_end_agrees m x f, reducing_once_at_the_end_agrees m z f,
    reducing_the_left_summand_first_is_free, reducing_the_right_summand_first_is_free, division]

/-- a root of `f` makes `f(x)` a multiple of `x - z`: `f(x) + z q(x) ≡ x q(x)` -/
theorem root_factor (m x z : Nat) (f : List Nat) (hz : eval m z f = 0) :
    (eval m x f + z * hornerN x (quot z f)) % m = (x * hornerN x (quot z f)) % m := by
  have h := division_mod m x z f
  rw [hz, Nat.add_zero] at h
  exact h

/-! ## Cancelling a common summand modulo `m` -/

private theorem mod_of_lt_two (u m : Nat) (hu : u < 2 * m) :
    u % m = u ∨ u % m + m = u := by
  by_cases h : u < m
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    have hle : m ≤ u := Nat.le_of_not_lt h
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
    omega

theorem mod_add_right_cancel (a b c m : Nat) (hm : 0 < m) (h : (a + c) % m = (b + c) % m) :
    a % m = b % m := by
  rw [Nat.add_mod, Nat.add_mod b] at h
  have ha := Nat.mod_lt a hm
  have hb := Nat.mod_lt b hm
  have hc := Nat.mod_lt c hm
  rcases mod_of_lt_two (a % m + c % m) m (by omega) with h1 | h1 <;>
  rcases mod_of_lt_two (b % m + c % m) m (by omega) with h2 | h2 <;> omega

/-! ## The verifier's quotient value -/

/-- what a base query computes at its point: the opened value less the claim at `z`, times the
inverse of `x - z`. `w` is that inverse. -/
def deepValue (m v claim w : Nat) : Nat := ((v + (m - claim % m)) * w) % m

private theorem residue_of_division (m H F Q x z w : Nat) (hm : 0 < m) (hz : z ≤ m)
    (hdiv : H + z * Q = x * Q + F) (hw : ((x + (m - z)) * w) % m = 1) :
    ((H % m + (m - F % m)) * w) % m = Q % m := by
  have hFlt := Nat.mod_lt F hm
  have hF := Nat.div_add_mod F m
  have hHF : (H % m + (m - F % m) + F) % m = H % m := by
    have e : H % m + (m - F % m) + F = H % m + m * (F / m + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_mod]
  have e1 : m * Q = z * Q + (m - z) * Q := by
    rw [← Nat.add_mul, show z + (m - z) = m by omega]
  have e2 : (x + (m - z)) * Q = x * Q + (m - z) * Q := Nat.add_mul x (m - z) Q
  have hMQ : H + m * Q = (x + (m - z)) * Q + F := by omega
  have hmul : (H + m * Q) * w = ((x + (m - z)) * Q + F) * w := by rw [hMQ]
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc m Q w] at hmul
  have step : ((x + (m - z)) * w * Q + F * w) % m = (Q + F * w) % m := by
    rw [← reducing_the_left_summand_first_is_free ((x + (m - z)) * w * Q),
      ← reducing_the_left_factor_first_is_free ((x + (m - z)) * w) Q m, hw, Nat.one_mul,
      reducing_the_left_summand_first_is_free]
  have hHw : (H * w) % m = (Q + F * w) % m := by
    rw [← Nat.add_mul_mod_self_left (H * w) m (Q * w), hmul,
      Nat.mul_right_comm (x + (m - z)) Q w]
    exact step
  have hD : ((H % m + (m - F % m)) * w + F * w) % m = (Q + F * w) % m := by
    rw [← Nat.add_mul, ← reducing_the_left_factor_first_is_free (H % m + (m - F % m) + F) w m,
      hHF, reducing_the_left_factor_first_is_free]
    exact hHw
  exact mod_add_right_cancel _ _ _ m hm hD

/-- the value the verifier computes is the quotient polynomial at the query point, whenever `w`
inverts `x - z`. This is the step that lets FRI test `q` and conclude about `f`. -/
theorem deep_value_is_the_quotient (m x z w : Nat) (f : List Nat) (hm : 0 < m) (hz : z ≤ m)
    (hw : ((x + (m - z)) * w) % m = 1) :
    deepValue m (eval m x f) (eval m z f) w = eval m x (quot z f) := by
  unfold deepValue
  rw [reducing_once_at_the_end_agrees m x f, reducing_once_at_the_end_agrees m z f,
    reducing_once_at_the_end_agrees m x (quot z f), Nat.mod_mod]
  exact residue_of_division m _ _ _ x z w hm hz (division x z f) hw

/-- with no inverse at all the verifier computes nothing: `w = 0` gives zero -/
theorem no_inverse_no_value (m v claim : Nat) : deepValue m v claim 0 = 0 % m := by
  simp only [deepValue, Nat.mul_zero]

/-! ## Worked instances -/

/-- `x^3 + 1` at `z = 2`: `x^3 - 8 = (x - 2)(x^2 + 2x + 4)` -/
theorem cube_plus_one_at_two : quot 2 [1, 0, 0, 1] = [4, 2, 1, 0] := by decide

theorem cube_plus_one_top_is_zero : top (quot 2 [1, 0, 0, 1]) = 0 := by decide

/-- over the field of seven elements: `x = 5`, `z = 2`, `x - z = 3`, and `5` inverts `3` -/
theorem seven_inverts : (5 + (7 - 2)) * 5 % 7 = 1 := by decide

theorem seven_example :
    deepValue 7 (eval 7 5 [1, 0, 0, 1]) (eval 7 2 [1, 0, 0, 1]) 5 = eval 7 5 (quot 2 [1, 0, 0, 1]) ∧
    eval 7 5 (quot 2 [1, 0, 0, 1]) = 4 := by decide

/-- a constant has a zero quotient everywhere -/
theorem a_constant_has_no_quotient (z c : Nat) : quot z [c] = [0] := rfl

/-- a linear polynomial `a + b x` divided at `z` leaves its slope -/
theorem a_line_leaves_its_slope (z a b : Nat) : quot z [a, b] = [b, 0] := by
  simp only [quot, hornerN, Nat.mul_zero, Nat.add_zero]

/-- the division identity checked at the Goldilocks prime on a small case -/
theorem division_at_goldilocks :
    (eval Shield.Horner.p 9 [3, 1, 4, 1, 5] + 7 * hornerN 9 (quot 7 [3, 1, 4, 1, 5])) %
        Shield.Horner.p =
      (9 * hornerN 9 (quot 7 [3, 1, 4, 1, 5]) + eval Shield.Horner.p 7 [3, 1, 4, 1, 5]) %
        Shield.Horner.p := by
  decide

end Shield.Poly
