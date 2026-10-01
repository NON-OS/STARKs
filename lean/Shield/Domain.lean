-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Layout
import Shield.Field

/-!
The evaluation domain is `2^logDomain` points, and it has to be a subgroup of the field.

Goldilocks has two-adicity 32, so `logDomain ≤ 32` is a hard limit on every parameter set
and not a tuning choice. The rate, the FRI blowup and the trace length all trade against it.
Everything is `Nat`, core only.
-/

namespace Shield.Domain

open Shield.Layout

/-! ## The field's limit -/

/-- The largest power of two dividing `p - 1`. -/
def twoAdicity : Nat := 32

theorem the_field_has_the_subgroup :
    Shield.Field.p - 1 = 2 ^ 32 * (3 * 5 * 17 * 257 * 65537) := Shield.Field.p_minus_one

theorem the_subgroup_is_two_to_the_adicity : (Shield.Field.p - 1) % 2 ^ twoAdicity = 0 :=
  Shield.Field.two_adicity.1

theorem the_adicity_is_exact : (Shield.Field.p - 1) / 2 ^ twoAdicity % 2 = 1 :=
  Shield.Field.two_adicity.2

/-- No subgroup of order `2^33` exists. -/
theorem no_domain_of_thirty_three : (Shield.Field.p - 1) % 2 ^ 33 ≠ 0 := by decide

/-- A parameter set whose domain the field can hold. -/
def fits (p : Params) : Prop := logDomain p ≤ twoAdicity

instance (p : Params) : Decidable (fits p) :=
  inferInstanceAs (Decidable (logDomain p ≤ 32))

/-- Every domain the field can hold is a subgroup: its order divides `p - 1`. -/
theorem every_fitting_domain_divides (q : Params) (h : fits q) :
    (Shield.Field.p - 1) % 2 ^ logDomain q = 0 := by
  have hl : logDomain q ≤ 32 := h
  have e : 2 ^ 32 = 2 ^ logDomain q * 2 ^ (32 - logDomain q) := by
    rw [← Nat.pow_add 2 (logDomain q) (32 - logDomain q)]
    have s : logDomain q + (32 - logDomain q) = 32 := by omega
    rw [s]
  rw [Shield.Field.p_minus_one, e,
    Nat.mul_assoc (2 ^ logDomain q) (2 ^ (32 - logDomain q)) (3 * 5 * 17 * 257 * 65537)]
  exact Nat.mul_mod_right _ _

/-- The domain order grows with its log, so a smaller log is always a smaller domain. -/
theorem a_smaller_log_is_a_smaller_domain (a b : Nat) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-! ## The shipped domain -/

theorem shipped_domain : logDomain shipped = 29 := by decide

theorem shipped_fits : fits shipped := by decide

theorem shipped_domain_divides : (Shield.Field.p - 1) % 2 ^ logDomain shipped = 0 := by decide

theorem shipped_headroom : twoAdicity - logDomain shipped = 3 := by decide

/-! ## Rate -/

/-- The rate is `2^-(1 + extraBlowup)`: the doubling in `logDomain` and the extra blowup. -/
def rateExponent (p : Params) : Nat := 1 + p.extraBlowup

theorem shipped_rate : rateExponent shipped = 8 := by decide

theorem domain_is_bound_plus_rate (p : Params) : logDomain p = logBound p + rateExponent p := by
  unfold logDomain rateExponent
  omega

/-- The blowup FRI sees, as a log. -/
def friLogBlowup (p : Params) : Nat := logDomain p - logBound p

theorem fri_blowup_is_the_rate (p : Params) : friLogBlowup p = rateExponent p := by
  unfold friLogBlowup logDomain rateExponent
  omega

/-- What FRI has left to halve after the blowup is the bound itself. -/
theorem fri_halves_the_bound (p : Params) : logDomain p - friLogBlowup p = logBound p := by
  unfold friLogBlowup logDomain
  omega

theorem shipped_fri_blowup : friLogBlowup shipped = 8 := by decide

theorem the_bound_fits_under_the_domain (p : Params) : logBound p ≤ logDomain p := by
  unfold logDomain
  omega

theorem the_rate_is_at_least_one (p : Params) : 1 ≤ rateExponent p := by
  unfold rateExponent
  omega

/-! ## How far the rate can move -/

def atBlowup (e : Nat) : Params := { shipped with extraBlowup := e }

theorem every_blowup_to_ten_fits :
    ∀ e < 11, logDomain { shipped with extraBlowup := e } ≤ 32 := by
  decide

theorem blowup_eleven_is_thirty_three : logDomain { shipped with extraBlowup := 11 } = 33 := by
  decide

theorem blowup_eleven_does_not_fit : ¬ fits (atBlowup 11) := by decide

theorem blowup_ten_is_the_edge : logDomain (atBlowup 10) = 32 := by decide

theorem the_largest_extra_blowup : twoAdicity - logBound shipped - 1 = 10 := by decide

theorem blowup_moves_the_domain_one_for_one (e : Nat) : logDomain (atBlowup e) = 22 + e := by
  show logBound shipped + 1 + e = 22 + e
  have : logBound shipped = 21 := by decide
  omega

/-- Any extra blowup that keeps bound, doubling and blowup under 32 fits, at any point. -/
theorem any_rate_that_sums_under_the_limit_fits (p : Params) (e : Nat)
    (h : logBound p + 1 + e ≤ 32) : logDomain { p with extraBlowup := e } ≤ 32 := h

theorem fits_iff (p : Params) :
    fits p ↔ p.logTrace + p.degreeLog + 1 + p.extraBlowup ≤ 32 := Iff.rfl

/-- The blowup does not move the bound, only the domain above it. -/
theorem blowup_keeps_the_bound (p : Params) (e : Nat) :
    logBound { p with extraBlowup := e } = logBound p := rfl

/-- The blowup does not move the FRI layer count; that is fixed by the bound. -/
theorem blowup_keeps_the_layers (e : Nat) : layers (atBlowup e) = layers shipped := rfl

theorem blowup_keeps_the_final (e : Nat) : finalLog (atBlowup e) = finalLog shipped := rfl

/-- It does move every tree one level per unit. -/
theorem blowup_deepens_the_trees (e : Nat) : treeDepth (atBlowup e) = 22 + e :=
  blowup_moves_the_domain_one_for_one e

/-! ## How far the trace can grow -/

def atTrace (t : Nat) : Params := { shipped with logTrace := t }

/-- At degree 8 and rate exponent 8 the trace can reach `2^21` and no further. -/
theorem trace_twenty_one_is_the_edge : logDomain (atTrace 21) = 32 := by decide

theorem trace_twenty_two_is_over : logDomain (atTrace 22) = 33 := by decide

theorem every_trace_to_twenty_one_fits : ∀ t < 22, fits (atTrace t) := by decide

theorem the_trace_has_three_levels_to_spare : 21 - shipped.logTrace = 3 := by decide

theorem shipped_degree_and_rate : shipped.degreeLog = 3 ∧ rateExponent shipped = 8 := by decide

/-- Trace length, degree and rate share one budget of 32. -/
theorem the_budget_is_shared (p : Params) (h : fits p) :
    p.logTrace + p.degreeLog + rateExponent p ≤ 32 := by
  have := (fits_iff p).mp h
  unfold rateExponent
  omega

/-- A degree-four circuit would buy one more trace level at the same rate. -/
theorem degree_four_buys_a_level :
    logDomain { atTrace 22 with degreeLog := 2 } = 32 := by decide

/-! ## Sizes -/

theorem shipped_domain_points : 2 ^ logDomain shipped = 536870912 := by decide

theorem shipped_domain_is_two_to_the_29 : 2 ^ logDomain shipped = 2 ^ 29 := by decide

/-- One base-field column over the domain, eight bytes a point, is four gibibytes. -/
theorem one_column_bytes : 8 * 2 ^ 29 = 4294967296 := by decide

theorem one_column_is_four_gibibytes : 8 * 2 ^ 29 = 4 * 1024 * 1024 * 1024 := by decide

theorem one_column_is_over_four_gigabytes : 4000000000 < 8 * 2 ^ 29 := by decide

/-- An extension-field column is twice that. -/
theorem one_extension_column_bytes : 16 * 2 ^ 29 = 8589934592 := by decide

/-- The measured 152 GiB peak, per domain point, is between 280 and 305 bytes. -/
theorem peak_per_point_lower : 280 * 2 ^ 29 ≤ 152 * 1024 * 1024 * 1024 := by decide

theorem peak_per_point_upper : 152 * 1024 * 1024 * 1024 < 305 * 2 ^ 29 := by decide

/-- Read as binary gigabytes the peak is exactly 304 bytes a point. -/
theorem peak_per_point_binary : 152 * 1024 * 1024 * 1024 = 304 * 2 ^ 29 := by decide

/-- Read as decimal gigabytes it is 283 bytes a point, rounded down. -/
theorem peak_per_point_decimal :
    283 * 2 ^ 29 ≤ 152000000000 ∧ 152000000000 < 284 * 2 ^ 29 := by decide

/-- 304 bytes is 38 base-field columns held over the whole domain at once. -/
theorem peak_in_columns : 304 = 38 * 8 := by decide

/-- At the edge of the field the same per-point cost is eight times larger. -/
theorem peak_at_the_edge : 304 * 2 ^ 32 = 8 * (304 * 2 ^ 29) := by decide

/-- Each extra level of blowup doubles the domain and so the peak. -/
theorem one_more_blowup_doubles_the_domain :
    2 ^ logDomain (atBlowup 8) = 2 * 2 ^ logDomain shipped := by decide

end Shield.Domain
