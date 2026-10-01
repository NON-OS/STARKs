-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
Round-by-round soundness under the proximity gaps of Ben-Sasson, Carmon,
Haböck, Kopparty and Saraf, *On Proximity Gaps for Reed-Solomon Codes*
(November 2025, preprint; "BCHKS25").

`Shield.RoundByRound` states the rounds under BCIKS20, whose Johnson-regime
threshold grows with n^2. BCHKS25 proves a threshold linear in n (their
Theorem 1.5 for lines, Theorem 4.2 for curves of degree M): if more than
M * a challenges z make `u_0 + z u_1 + ... + z^M u_M` γ-close to the code, the
u_i agree with codewords on a common set of density 1 - γ, where

    a = 2 D_X D_Y^2 D_Z + (γ n + 1) D_Y          (their (13), with Lemma 3.1)
    D_X = (m + 1/2) √(n k),  D_Y = (m + 1/2) / √ρ,  D_Z = (m + 1/2)^2 / (3 ρ)

so a = 2 (m + 1/2)^5 n / (3 ρ^(3/2)) + (γ n + 1)(m + 1/2) / √ρ, with ρ = k / n,
γ = 1 - √ρ (1 + 1/(2m)) and m = 3, the proximity parameter the query phase
already uses. A round that batches M + 1 functions by powers of one challenge
then fails with probability at most M a / |K|.

At rate 2^-6 over 2^23 the FRI code has k = 2^17 - 1 over n = 2^23, so
ρ = 2^-6 (1 - 2^-17). The bound below is looser on purpose, so it holds
exactly: √ρ ≥ (1/8)(1 - 2^-16), hence ρ^(-3/2) ≤ 512 / (1 - 2^-16)^3 and
1/√ρ ≤ 8 / (1 - 2^-16), and γ ≤ 1. Each only raises a. With E = 2^16:

    a ≤ (537824 n E^3 + 84 (n + 1) E (E - 1)^2) / (3 (E - 1)^3)

(537824 = 2 * (7/2)^5 * 512, and 84 = 3 * 28 = 3 * (7/2) * 8.)

The result: under BCHKS25 a single line clears 87 bits and a radix-8 fold 84
with no grind at all, a margin on top of the BCIKS20 figures of
`Shield.RoundByRound`. It rests on a preprint, and says so.
-/

namespace Shield.Gaps2025

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

def p : Nat := Shield.Launch.p
def n : Nat := 2 ^ 23
def E : Nat := 2 ^ 16

/-- the threshold a over |K| = p^2, as an upper bound's numerator and denominator -/
def aNum : Nat := 537824 * n * E ^ 3 + 84 * (n + 1) * E * (E - 1) ^ 2
def aDen : Nat := 3 * (E - 1) ^ 3

theorem constants : 2 * 16807 * 512 = 537824 * 32 ∧ 3 * 28 = 84 := by decide

/-- A round batching by a curve of degree M clears b bits: M a / p^2 < 2^-b. -/
def clears (M b : Nat) : Prop := M * aNum * 2 ^ b < aDen * p ^ 2

instance (M b : Nat) : Decidable (clears M b) := by unfold clears; infer_instance

/-- One line clears 87. -/
theorem one_line : clears 1 87 := by decide


/-! ### `fri8` at rate 2^-6 -/

/-- Radix 8 folds are degree-7 curves: 84 bits with no commit grind at all. -/
theorem radix8_fold_no_grind : clears 7 84 := by decide


end Shield.Gaps2025
