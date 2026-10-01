-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
Soundness round by round, which is how a Fiat-Shamir STARK is measured
(ethSTARK documentation v1.2, Theorem 5; the error terms from Ben-Sasson,
Carmon, Ishai, Kopparty and Saraf 2020). An attacker can retry any one
challenge on its own, so each round's error counts alone, and a grind raises
only the round it sits in. The provable figure is the weakest round.

The Johnson term at rate 2^-6 over a 2^23 domain is
ε_J = (m + 1/2)^7 N^2 / (3 ρ^(3/2) |K|), from `Shield.Launch`. Two rounds carry
it, and each has its own grind on the deployed transcript:

- the DEEP batching challenge draws independent coefficients, so the batch is an
  affine space whose error is one line's (BCIKS20 Theorem 1.6); a 19-bit grind
  precedes the draw;
- each FRI fold at radix 8 is a curve of degree 7; a 21-bit grind precedes each
  fold challenge.

The query phase is `Shield.Launch` and `Shield.Outsourced`. The composition
challenge (an algebraic batch over p^2) and the out-of-domain point are far
above the floor.
-/

namespace Shield.RoundByRound

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

def p : Nat := Shield.Launch.p

/-- ε_J at rate 2^-6 over 2^23, from `Shield.Launch`: 7^7 * 2^48 / (3 p^2). -/
def jNum : Nat := Shield.Launch.cNum
def jDen : Nat := Shield.Launch.cDen

/-- Independent DEEP coefficients: one line's error, so 19 bits before the draw
clear 80 and 18 do not. -/
theorem independent_deep_grind_19 :
    jNum * 2 ^ 80 < jDen * 2 ^ 19 ∧ jDen * 2 ^ 18 ≤ jNum * 2 ^ 80 := by
  decide

/-- Radix 8 folds are degree-7 curves: 21 bits before each fold challenge clear
80, and 20 do not. -/
theorem radix8_fold_needs_21 :
    jDen * 2 ^ 20 ≤ (7 * jNum) * 2 ^ 80 ∧ (7 * jNum) * 2 ^ 80 < jDen * 2 ^ 21 := by
  decide

end Shield.RoundByRound
