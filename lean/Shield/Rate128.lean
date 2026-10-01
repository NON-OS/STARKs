-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
The launch circuit at rate 2^-7 in place of 2^-6: the same degree bound
B = 2^17, so the domain doubles to 2^24, radix 4, F_p^2 challenges, m = 3.

At this rate one query survives with probability at most 2^-3.5 * 7/6, which
carries a √2, so every query bound is stated on ε²: ε ≤ 2^-(k/10) is
(ε²)^5 * 2^k ≤ 1. The query grind is outsourced (docs/12 Section 2.2); the
three grinds are the ones the contracts asked about.

The commit phase is the one that moves against the rate: a doubled domain
costs it two bits and the rate one and a half, so the launch's 20-bit commit
grind no longer clears 80 here.
-/

namespace Shield.Rate128

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

def p : Nat := Shield.Launch.p

/-- ε_Q² = (49/4608)^q * 2^-(2g) -/
def sqNum (q : Nat) : Nat := 49 ^ q
def sqDen (q g : Nat) : Nat := 4608 ^ q * 2 ^ (2 * g)

theorem factor : (2 * 3 + 1) ^ 2 = 49 ∧ 2 ^ 7 * (2 * 3) ^ 2 = 4608 := by decide

/-! ### The query phase at 2^33, 2^36 and 2^39 of grinding -/

/-- 15 queries at 33 bits: more than 82.1, at most 82.2 -/
theorem q15_g33 : sqNum 15 ^ 5 * 2 ^ 821 < sqDen 15 33 ^ 5 ∧ sqDen 15 33 ^ 5 ≤ sqNum 15 ^ 5 * 2 ^ 822 := by
  decide

/-- 14 queries at 36 bits: more than 81.8, at most 81.9 -/
theorem q14_g36 : sqNum 14 ^ 5 * 2 ^ 818 < sqDen 14 36 ^ 5 ∧ sqDen 14 36 ^ 5 ≤ sqNum 14 ^ 5 * 2 ^ 819 := by
  decide

/-- 13 queries at 39 bits: more than 81.6, at most 81.7 -/
theorem q13_g39 : sqNum 13 ^ 5 * 2 ^ 816 < sqDen 13 39 ^ 5 ∧ sqDen 13 39 ^ 5 ≤ sqNum 13 ^ 5 * 2 ^ 817 := by
  decide

/-- and each is the fewest queries that clear 80 at its grind -/
theorem fewest :
    sqDen 14 33 ≤ sqNum 14 * 2 ^ 160 ∧ sqDen 13 36 ≤ sqNum 13 * 2 ^ 160 ∧
      sqDen 12 39 ≤ sqNum 12 * 2 ^ 160 := by
  decide

/-! ### The commit phase

ε_C = (m + 1/2)^7 N^2 / (3 ρ^(3/2) |K|), N = 2^24, ρ = 2^-7, |K| = p^2.
Squared and cleared: 7^14 * 2^(2 (48 - 7) + 21) / (9 p^4). -/

def commitSqNum : Nat := 7 ^ 14 * 2 ^ 103
def commitSqDen : Nat := 9 * p ^ 4

/-- with no commit grind it is between 58.4 and 58.5 bits -/
theorem commit_bare :
    commitSqNum ^ 5 * 2 ^ 584 < commitSqDen ^ 5 ∧ commitSqDen ^ 5 ≤ commitSqNum ^ 5 * 2 ^ 585 := by
  decide

/-- the launch's 20 bits fall short of 80 here; 22 is the least that clears it
for a line. A radix-4 fold is a degree-3 curve and needs 24, and the DEEP round
at this rate needs 30 (`Shield.RoundByRound`). -/
theorem commit_needs_22 :
    commitSqDen * 2 ^ (2 * 20) ≤ commitSqNum * 2 ^ 160 ∧
      commitSqDen * 2 ^ (2 * 21) ≤ commitSqNum * 2 ^ 160 ∧
      commitSqNum * 2 ^ 160 < commitSqDen * 2 ^ (2 * 22) := by
  decide

/-! ### The collision class

The layer-one domain is 2^22, so the re-prove rate is 3 q (q - 1) / 2^22. -/

def collisionNum (q : Nat) : Nat := 3 * q * (q - 1)

/-- one proof in about 6,658 at 15 queries, 7,682 at 14, 8,962 at 13 -/
theorem collision_rates :
    collisionNum 15 * 6657 ≤ 2 ^ 22 ∧ 2 ^ 22 < collisionNum 15 * 6658 ∧
      collisionNum 14 * 7681 ≤ 2 ^ 22 ∧ 2 ^ 22 < collisionNum 14 * 7682 ∧
      collisionNum 13 * 8962 ≤ 2 ^ 22 ∧ 2 ^ 22 < collisionNum 13 * 8963 := by
  decide

end Shield.Rate128
