-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Launch

/-!
The `fri8` points that buy queries with outsourced grinding, checked the way
`Shield.Launch` checks the launch point: every figure a rational compared as
integers, so the decimals docs/12 Section 2.2 quotes are decided, not rounded.

Rate 2^-6, radix 4 over 2^23, commit grind 20, m = 3 and B = 2^17 are the
launch point's and are not restated here. Only the query count and the query
grind move:

- 17 queries at a 33 bit grind, the `fri8` default;
- 15 queries at a 39 bit grind, the accelerator option.

The query phase is what these points change. The weakest round at each is the
DEEP batching challenge, which `Shield.RoundByRound` states and which the `fri8` build closes
with a grind of at least 26 bits before it.
-/

namespace Shield.Outsourced

set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

/-- one query survives with probability at most 7/48 at rate 2^-6, m = 3 -/
def qNum : Nat := 7
def qDen : Nat := 48

/-- ε_Q = (7/48)^q * 2^-g, as a numerator and a denominator -/
def epsNum (q : Nat) : Nat := qNum ^ q
def epsDen (q g : Nat) : Nat := qDen ^ q * 2 ^ g

/-- `bitsAbove q g k`: the query phase is worth more than k/10 bits -/
def bitsAbove (q g k : Nat) : Prop := epsNum q ^ 10 * 2 ^ k < epsDen q g ^ 10

/-- `bitsAtMost q g k`: and no more than k/10 bits -/
def bitsAtMost (q g k : Nat) : Prop := epsDen q g ^ 10 ≤ epsNum q ^ 10 * 2 ^ k

/-- the factor is the launch point's -/
theorem factor_is_the_launch_factor :
    qNum = Shield.Launch.qNum ∧ qDen = Shield.Launch.qDen := by decide

/-! ### 17 queries, 33 bit grind -/

theorem q17_above_80_2 : bitsAbove 17 33 802 := by
  unfold bitsAbove; decide
theorem q17_at_most_80_3 : bitsAtMost 17 33 803 := by
  unfold bitsAtMost; decide

/-- 33 is the least grind that clears 80 bits at 17 queries -/
theorem q17_needs_33 : epsNum 17 * 2 ^ 80 < epsDen 17 33 ∧ epsDen 17 32 ≤ epsNum 17 * 2 ^ 80 := by
  decide

/-! ### 15 queries, 39 bit grind -/

theorem q15_above_80_6 : bitsAbove 15 39 806 := by
  unfold bitsAbove; decide
theorem q15_at_most_80_7 : bitsAtMost 15 39 807 := by
  unfold bitsAtMost; decide

/-- 39 is the least grind that clears 80 bits at 15 queries -/
theorem q15_needs_39 : epsNum 15 * 2 ^ 80 < epsDen 15 39 ∧ epsDen 15 38 ≤ epsNum 15 * 2 ^ 80 := by
  decide

/-- Shape A' (docs/16): 18 queries at 31 bits, more than 80.9, and 31 is the
least grind that clears 80 at 18 queries: 30 falls just short, at 79.996. -/
theorem q18_above_80_9 : bitsAbove 18 31 809 := by unfold bitsAbove; decide

theorem q18_needs_31 : epsNum 18 * 2 ^ 80 < epsDen 18 31 ∧ epsDen 18 30 ≤ epsNum 18 * 2 ^ 80 := by
  decide

/-- 16 queries needs 36, three bits more than 17 for one query less -/
theorem q16_needs_36 : epsNum 16 * 2 ^ 80 < epsDen 16 36 ∧ epsDen 16 35 ≤ epsNum 16 * 2 ^ 80 := by
  decide

/-! ### Both points clear the floor with the commit phase

The provable figure is the smaller of the query and commit terms. -/

theorem provable_clears_eighty :
    epsNum 17 * 2 ^ 80 < epsDen 17 33 ∧ epsNum 15 * 2 ^ 80 < epsDen 15 39 ∧
      Shield.Launch.cNum * 2 ^ 80 < Shield.Launch.cDen * 2 ^ Shield.Launch.commitGrind := by
  decide

/-! ### The chunked grind

The query grind is searched in 8 chained pieces (`GRIND_CHUNKS`), each of
g - 3 bits, so a retry of the query draw still costs 2^g hashes on average. -/

def chunks : Nat := 8

theorem chunked_work : chunks * 2 ^ 30 = 2 ^ 33 ∧ chunks * 2 ^ 36 = 2 ^ 39 := by decide

/-! ### The collision class at fewer queries

3 q (q - 1) / 2^21 falls with q, so the re-prove rate improves. -/

def collisionNum (q : Nat) : Nat := 3 * q * (q - 1)

theorem collisions : collisionNum 17 = 816 ∧ collisionNum 15 = 630 := by decide

/-- about one proof in 2,570 at 17 queries, one in 3,329 at 15 -/
theorem collision_rates :
    2 ^ 21 < collisionNum 17 * 2571 ∧ collisionNum 17 * 2570 ≤ 2 ^ 21 ∧
      2 ^ 21 < collisionNum 15 * 3329 ∧ collisionNum 15 * 3328 ≤ 2 ^ 21 := by
  decide

theorem fewer_queries_fewer_collisions :
    collisionNum 15 < collisionNum 17 ∧ collisionNum 17 < Shield.Launch.collisionNum := by decide

end Shield.Outsourced
