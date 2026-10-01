-- NONOS Operating System (AGPL-3.0-or-later)

/-!
Point A's error terms, exactly. `Params` counts whole bits; here
every bound in docs/12 Sections 2.1 and 4.4 is a rational compared as
integers, so the decimals the documents quote are checked, not rounded.

The point: 19 queries at rate 2^-6 over a domain of 2^23, a 28 bit query
grind, challenges in F_p^2, proximity parameter m = 3, FRI bound B = 2^17. The
Johnson term `cNum / cDen` below is what `Shield.RoundByRound` charges to the
DEEP and fold rounds, each under its own grind.

A bound of the form ε ≤ 2^-(k/10) is stated as ε^10 * 2^k ≤ 1 with ε's
numerator and denominator cleared, so the kernel decides it on naturals.
-/

namespace Shield.Launch

/- The bounds compare numbers of a few thousand bits; the kernel decides them
   with GMP, the elaborator needs leave to expand the powers. -/
set_option exponentiation.threshold 2048
set_option maxRecDepth 20000

/-- the Goldilocks prime -/
def p : Nat := 2 ^ 64 - 2 ^ 32 + 1

def queries : Nat := 19
def rhoBits : Nat := 6
def domainBits : Nat := 23
def m : Nat := 3
def queryGrind : Nat := 28
def commitGrind : Nat := 20
def boundB : Nat := 2 ^ 17

/-! ### Query phase

One query survives with probability at most √ρ (1 + 1/(2m)). With ρ = 2^-6
and m = 3 that is (2m + 1) / (2^3 * 2m) = 7/48.
-/

def qNum : Nat := 2 * m + 1
def qDen : Nat := 2 ^ (rhoBits / 2) * (2 * m)

theorem query_factor : qNum = 7 ∧ qDen = 48 := by decide

/-- 19 queries and the grind: ε_Q = (7/48)^19 * 2^-28 -/
def epsQNum : Nat := qNum ^ queries
def epsQDen : Nat := qDen ^ queries * 2 ^ queryGrind

/-- the query phase is worth more than 80.7 bits -/
theorem query_phase_above_80_7 : epsQNum ^ 10 * 2 ^ 807 < epsQDen ^ 10 := by decide

/-- and not 80.8: the document rounds 80.77 to 80.8, and no further -/
theorem query_phase_below_80_8 : epsQDen ^ 10 ≤ epsQNum ^ 10 * 2 ^ 808 := by decide

/-! ### Commit phase

ε_C = (m + 1/2)^7 N^2 / (3 ρ^(3/2) |K|), with N = 2^23, ρ^(3/2) = 2^-9 and
|K| = p^2. Clearing the halves: (2m + 1)^7 * 2^(2*23 + 9 - 7) / (3 p^2).
-/

def cNum : Nat := (2 * m + 1) ^ 7 * 2 ^ (2 * domainBits + 3 * rhoBits / 2 - 7)
def cDen : Nat := 3 * p ^ 2

theorem commit_numerator : cNum = 7 ^ 7 * 2 ^ 48 := by decide

/-- the Johnson term on one line, with no grind: 61.9 bits -/
theorem one_line_bare_61_9 : cNum ^ 10 * 2 ^ 619 < cDen ^ 10 := by decide

/-- the provable figure is the smaller term, and it clears the 80 bit floor -/
theorem provable_clears_eighty :
    epsQNum * 2 ^ 80 < epsQDen ∧ cNum * 2 ^ 80 < cDen * 2 ^ commitGrind := by decide

/-! ### Zero knowledge: the rank condition (R), docs/12-zero-knowledge.md 4.4

The minor that decides (R) has degree at most 2(B - 1) + 664 e in the
challenges, e = (B - 1) + 86 + 12. Over F_p^2, Schwartz-Zippel bounds its
chance of vanishing by that degree over p^2.
-/

def e : Nat := (boundB - 1) + 86 + 12
def minorDegree : Nat := 2 * (boundB - 1) + 664 * e

theorem minor_degree_is : e = 131169 ∧ minorDegree = 87358358 := by decide

/-- (R) fails, for challenges drawn at random, below 2^-101.6 -/
theorem rank_failure_below_101_6 : minorDegree ^ 10 * 2 ^ 1016 < (p ^ 2) ^ 10 := by decide

/-! ### The collision class

A successor row's fourth power can land inside another query's layer-one
coset. The masks vanish on every opened row and its successor, so they vanish
on that point's whole coset and cannot move the layer-one value there; the
simulator's polynomial can. (R) then fails for every challenge, and the
per-proof check refuses the proof and the wallet proves again.

For each ordered pair of distinct queries the point lands in the other's
coset with probability 4 / 2^21 over the layer-one domain, and one of the four
landings is the other query's own point, where both sides already agree. So
the class has probability at most 3 q (q - 1) / 2^21.
-/

def layerOneBits : Nat := domainBits - 2
def collisionNum : Nat := 3 * queries * (queries - 1)

theorem collision_count : collisionNum = 1026 ∧ layerOneBits = 21 := by decide

/-- about one proof in 2,044 is proved twice: above 2^-11, below 2^-10.9 -/
theorem collision_rate :
    2 ^ layerOneBits < collisionNum * 2 ^ 11 ∧ collisionNum ^ 10 * 2 ^ 109 < 2 ^ (10 * layerOneBits) := by
  decide

/-- the collision class, not Schwartz-Zippel, sets the re-prove rate -/
theorem collisions_dominate : minorDegree * 2 ^ layerOneBits < collisionNum * p ^ 2 := by decide

end Shield.Launch
