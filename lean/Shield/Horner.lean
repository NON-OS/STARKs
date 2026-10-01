-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Horner evaluation of the final FRI polynomial, as the verifier runs it.

The final layer arrives as a coefficient list, lowest first, and the verifier
evaluates it once per query at that query's final point, reducing after every
multiply-add. Reducing once at the end gives the same value, and so does padding
the list with zero coefficients. The cost is one multiply-add per coefficient
per query, which is what moving the stop from 8 to 6 buys back.

Everything is `Nat`, core only.
-/

namespace Shield.Horner

/-- Horner's rule mod `m`, coefficients lowest first. -/
def eval (m x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => (c + x * eval m x cs) % m

/-- The same rule with no reduction at all. -/
def hornerN (x : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + x * hornerN x cs

/-- The textbook form: coefficient `i` times `x ^ i`, summed, starting at power `i`. -/
def powerSum (x : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | i, c :: cs => c * x ^ i + powerSum x (i + 1) cs

def sum : List Nat → Nat
  | [] => 0
  | c :: cs => c + sum cs

/-- Multiply-adds the verifier pays for one evaluation. -/
def steps (cs : List Nat) : Nat := cs.length

/-- A list of `k` coefficients claims a degree below `k`. -/
def degreeBound (cs : List Nat) : Nat := cs.length

/-- The list with `k` zero coefficients appended on top. -/
def pad (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k + 1 => pad cs k ++ [0]

/-- The Goldilocks prime the verifier works in. -/
def p : Nat := 18446744069414584321

theorem p_is_goldilocks : p = 2 ^ 64 - 2 ^ 32 + 1 := by decide

/-! ## Reduction lemmas, from `Nat.add_mod` and `Nat.mul_mod` -/

theorem reducing_the_right_summand_first_is_free (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_mod a (b % m) m, Nat.mod_mod, ← Nat.add_mod]

theorem reducing_the_left_summand_first_is_free (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  rw [Nat.add_mod (a % m) b m, Nat.mod_mod, ← Nat.add_mod]

theorem reducing_the_left_factor_first_is_free (a b m : Nat) :
    (a % m * b) % m = (a * b) % m := by
  rw [Nat.mul_mod (a % m) b m, Nat.mod_mod, ← Nat.mul_mod]

theorem reducing_the_right_factor_first_is_free (a b m : Nat) :
    (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_mod a (b % m) m, Nat.mod_mod, ← Nat.mul_mod]

/-! ## Small lists -/

theorem no_coefficients_is_zero (m x : Nat) : eval m x [] = 0 := rfl

theorem one_coefficient_is_itself_reduced (m x c : Nat) : eval m x [c] = c % m := by
  simp only [eval, Nat.mul_zero, Nat.add_zero]

theorem at_zero_only_the_constant_is_left (m c : Nat) (cs : List Nat) :
    eval m 0 (c :: cs) = c % m := by
  simp only [eval, Nat.zero_mul, Nat.add_zero]

/-- A claim of degree below one does not see the point. -/
theorem a_constant_ignores_the_point (m x y c : Nat) : eval m x [c] = eval m y [c] := by
  simp only [one_coefficient_is_itself_reduced]

theorem the_empty_claim_ignores_the_point (m x y : Nat) : eval m x [] = eval m y [] := rfl

theorem a_claim_below_one_ignores_the_point (m x y : Nat) (cs : List Nat)
    (h : degreeBound cs ≤ 1) : eval m x cs = eval m y cs := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    cases cs with
    | nil => exact a_constant_ignores_the_point m x y c
    | cons d ds =>
      have h' : ds.length + 1 + 1 ≤ 1 := h
      omega

/-! ## The result is a residue -/

theorem the_value_is_below_the_modulus (m x : Nat) (cs : List Nat) (h : 0 < m) :
    eval m x cs < m := by
  cases cs with
  | nil =>
    simp only [eval]
    exact h
  | cons c cs =>
    simp only [eval]
    exact Nat.mod_lt _ h

theorem the_value_is_already_reduced (m x : Nat) (cs : List Nat) :
    eval m x cs % m = eval m x cs := by
  cases cs with
  | nil => simp only [eval, Nat.zero_mod]
  | cons c cs => simp only [eval, Nat.mod_mod]

theorem modulus_one_sends_everything_to_zero (x : Nat) (cs : List Nat) :
    eval 1 x cs = 0 := by
  have h := the_value_is_below_the_modulus 1 x cs (by decide)
  omega

/-! ## Zero coefficients on top -/

theorem a_trailing_zero_is_free (m x : Nat) (cs : List Nat) :
    eval m x (cs ++ [0]) = eval m x cs := by
  induction cs with
  | nil => simp only [List.nil_append, eval, Nat.mul_zero, Nat.add_zero, Nat.zero_mod]
  | cons c cs ih =>
    show (c + x * eval m x (cs ++ [0])) % m = (c + x * eval m x cs) % m
    rw [ih]

theorem padding_keeps_the_value (m x : Nat) (cs : List Nat) (k : Nat) :
    eval m x (pad cs k) = eval m x cs := by
  induction k with
  | zero => simp only [pad]
  | succ k ih => simp only [pad, a_trailing_zero_is_free, ih]

theorem the_zero_polynomial_is_zero (m x k : Nat) : eval m x (pad [] k) = 0 := by
  simp only [padding_keeps_the_value, eval]

theorem a_zero_coefficient_raises_the_bound (cs : List Nat) :
    degreeBound (cs ++ [0]) = degreeBound cs + 1 := by
  simp only [degreeBound, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]

theorem padding_adds_to_the_bound (cs : List Nat) (k : Nat) :
    degreeBound (pad cs k) = degreeBound cs + k := by
  induction k with
  | zero => simp only [pad, Nat.add_zero]
  | succ k ih =>
    simp only [pad]
    rw [a_zero_coefficient_raises_the_bound, ih, Nat.add_assoc]

/-- Padding raises the claimed bound and the price, never the value. -/
theorem padding_costs_a_step_per_zero (cs : List Nat) (k : Nat) :
    steps (pad cs k) = steps cs + k := padding_adds_to_the_bound cs k

theorem steps_are_the_degree_bound (cs : List Nat) : steps cs = degreeBound cs := rfl

/-! ## Where the reductions go -/

/-- Reducing after every step agrees with reducing once at the end. -/
theorem reducing_once_at_the_end_agrees (m x : Nat) (cs : List Nat) :
    eval m x cs = hornerN x cs % m := by
  induction cs with
  | nil => simp only [eval, hornerN, Nat.zero_mod]
  | cons c cs ih =>
    simp only [eval, hornerN]
    rw [ih, ← reducing_the_right_summand_first_is_free c (x * (hornerN x cs % m)) m,
      reducing_the_right_factor_first_is_free, reducing_the_right_summand_first_is_free]

theorem power_sum_is_horner (x : Nat) (cs : List Nat) :
    ∀ i, powerSum x i cs = x ^ i * hornerN x cs := by
  induction cs with
  | nil =>
    intro i
    simp only [powerSum, hornerN, Nat.mul_zero]
  | cons c cs ih =>
    intro i
    simp only [powerSum, hornerN]
    rw [ih (i + 1), Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm c]

/-- The verifier's loop computes the polynomial the prover committed to. -/
theorem horner_is_the_power_sum (m x : Nat) (cs : List Nat) :
    eval m x cs = powerSum x 0 cs % m := by
  rw [reducing_once_at_the_end_agrees, power_sum_is_horner, Nat.pow_zero, Nat.one_mul]

/-- The point may be reduced before the loop starts. -/
theorem the_point_can_be_reduced_first (m x : Nat) (cs : List Nat) :
    eval m (x % m) cs = eval m x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [eval]
    rw [ih, ← reducing_the_right_summand_first_is_free c (x % m * eval m x cs) m,
      reducing_the_left_factor_first_is_free, reducing_the_right_summand_first_is_free]

/-- So may the constant coefficient. -/
theorem the_constant_can_be_reduced_first (m x c : Nat) (cs : List Nat) :
    eval m x ((c % m) :: cs) = eval m x (c :: cs) := by
  simp only [eval]
  exact reducing_the_left_summand_first_is_free c (x * eval m x cs) m

/-- Adding to the constant term adds to the value. -/
theorem the_constant_term_is_linear (m x a b : Nat) (cs : List Nat) :
    (eval m x (a :: cs) + b) % m = eval m x ((a + b) :: cs) := by
  simp only [eval]
  rw [reducing_the_left_summand_first_is_free]
  have e : a + x * eval m x cs + b = a + b + x * eval m x cs := by omega
  rw [e]

/-- At the point one the polynomial is the sum of its coefficients. -/
theorem at_one_it_is_the_sum (m : Nat) (cs : List Nat) : eval m 1 cs = sum cs % m := by
  induction cs with
  | nil => simp only [eval, sum, Nat.zero_mod]
  | cons c cs ih =>
    simp only [eval, sum, Nat.one_mul]
    rw [ih, reducing_the_right_summand_first_is_free]

/-! ## Concrete evaluations mod p -/

theorem eval_two_at_one_one_one : eval p 2 [1, 1, 1] = 7 := by decide

theorem eval_three_at_x_squared : eval p 3 [0, 0, 1] = 9 := by decide

/-- `1 + (p - 1)` is `p`, which is zero. -/
theorem eval_minus_one_at_one_one : eval p (p - 1) [1, 1] = 0 := by decide

theorem eval_seven_at_five_plus_x_cubed : eval p 7 [5, 0, 0, 1] = 348 := by decide

theorem eval_ten_reads_the_digits : eval p 10 [1, 2, 3] = 321 := by decide

theorem eval_three_at_two_seven_one_eight : eval p 3 [2, 7, 1, 8] = 248 := by decide

/-- `(p - 1) ^ 2` is one mod p. -/
theorem minus_one_squared_is_one : eval p (p - 1) [0, 0, 1] = 1 := by decide

theorem minus_one_is_minus_one : eval p (p - 1) [0, 1] = p - 1 := by decide

/-- A coefficient equal to p is a zero coefficient. -/
theorem a_coefficient_of_p_is_zero : eval p 5 [p, 1] = 5 := by decide

theorem the_sum_wraps : eval p 2 [p - 1, 1] = 1 := by decide

theorem padded_twice_is_unchanged : eval p 2 (pad [1, 1, 1] 2) = 7 := by decide

theorem the_power_sum_agrees_at_seven : powerSum 7 0 [5, 0, 0, 1] % p = 348 := by decide

theorem the_power_sum_agrees_at_three : powerSum 3 0 [2, 7, 1, 8] % p = 248 := by decide

theorem the_power_sum_agrees_at_minus_one : powerSum (p - 1) 0 [0, 0, 1] % p = 1 := by decide

theorem unreduced_horner_at_seven : hornerN 7 [5, 0, 0, 1] = 348 := by decide

theorem the_sum_at_one : eval p 1 [3, 4, 5] = 12 := by decide

/-! ## What the verifier pays -/

/-- FRI layers at a bound, a stop and a fold, at least one. -/
def layers (bound stop fold : Nat) : Nat := max 1 ((bound - stop) / fold)

/-- Coefficients of the final polynomial the layers leave. -/
def finalCoeffs (bound stop fold : Nat) : Nat := 2 ^ (bound - layers bound stop fold * fold)

/-- One evaluation per query at `coeffs` multiply-adds each. -/
def queryCost (coeffs queries : Nat) : Nat := coeffs * queries

def gas (perStep n : Nat) : Nat := perStep * n

/-- Memory words the loop allocates: `perStep` per multiply-add. -/
def wordsAllocated (perStep steps : Nat) : Nat := perStep * steps

/-- The shipped point: bound `2^21`, stop 8, fold 2, six layers, 512 coefficients. -/
theorem shipped_layers : layers 21 8 2 = 6 := by decide
theorem shipped_final_coeffs : finalCoeffs 21 8 2 = 512 := by decide

/-- A stop of 6 takes one more layer and leaves 128. -/
theorem stop_six_layers : layers 21 6 2 = 7 := by decide
theorem stop_six_final_coeffs : finalCoeffs 21 6 2 = 128 := by decide

theorem shipped_steps : queryCost (finalCoeffs 21 8 2) 12 = 6144 := by decide
theorem stop_six_steps : queryCost (finalCoeffs 21 6 2) 12 = 1536 := by decide
theorem the_stop_saves_steps : 6144 - 1536 = 4608 := by decide

theorem shipped_gas : gas 40 6144 = 245760 := by decide
theorem stop_six_gas : gas 40 1536 = 61440 := by decide
theorem the_stop_saves_gas : gas 40 6144 - gas 40 1536 = 184320 := by decide

theorem a_full_final_costs_its_length (cs : List Nat) (h : cs.length = 512) :
    queryCost (steps cs) 12 = 6144 := by
  simp only [queryCost, steps]
  omega

theorem gas_splits_over_steps (g a b : Nat) : gas g (a + b) = gas g a + gas g b := by
  simp only [gas, Nat.mul_add]

theorem padding_is_paid_per_query (cs : List Nat) (k q : Nat) :
    queryCost (steps (pad cs k)) q = queryCost (steps cs) q + k * q := by
  simp only [queryCost, padding_costs_a_step_per_zero, Nat.add_mul]

/-! ## The two on-chain loops

The allocating loop builds two two-word structs per multiply-add. The assembly
loop keeps both in registers and allocates nothing. -/

theorem the_allocating_loop_allocates : wordsAllocated 4 6144 = 24576 := by decide

theorem the_allocating_loop_in_bytes : wordsAllocated 4 6144 * 32 = 786432 := by decide

theorem the_allocating_loop_at_stop_six : wordsAllocated 4 1536 = 6144 := by decide

theorem the_assembly_loop_allocates_nothing : wordsAllocated 0 6144 = 0 := by decide

theorem nothing_per_step_is_nothing (n : Nat) : wordsAllocated 0 n = 0 := by
  simp only [wordsAllocated, Nat.zero_mul]

end Shield.Horner
