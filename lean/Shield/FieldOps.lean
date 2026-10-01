-- NONOS Operating System (AGPL-3.0-or-later)

import Std.Tactic.BVDecide

/-!
The Goldilocks ring operations of `nonos-stark/src/field/ops.rs`, transcribed
operation for operation on 64 bit words, and proved for every input.

Each function below is the Rust body with its wrapping arithmetic and its
carry and borrow flags written out: `overflowing_add` carries exactly when the
wrapped sum is below an addend, `overflowing_sub` borrows exactly when the
subtrahend is larger. A change to `ops.rs` that is not made here too leaves
these proofs about code that no longer runs; the two are reviewed together.

Two kinds of statement:
- *range*, by `bv_decide`: the result is canonical, below P, and differs from
  the exact integer value by a whole number of P, one of a few named ones. It
  covers all 2^64 or 2^128 inputs, not a sample. The SAT solver's LRAT
  certificate is checked by Lean's own checker run as compiled code, so these
  theorems trust `Lean.ofReduceBool` besides the usual axioms; `#print axioms`
  shows it. The multiply-as-shift lemma and the congruence do not.
- *congruence*, by `omega` over the integers: the exact value the word
  arithmetic tracks is the field value, from `2^64 = 2^32 - 1` and
  `2^96 = -1` modulo P.
-/

namespace Shield.FieldOps

def P : BitVec 64 := 0xFFFFFFFF00000001
def EPS : BitVec 64 := 0xFFFFFFFF

/-- `impl Add for Fp` -/
def add (a b : BitVec 64) : BitVec 64 :=
  let sum := a + b
  bif BitVec.ult sum a then sum + EPS
  else bif BitVec.ule P sum then sum - P else sum

/-- `impl Sub for Fp` -/
def sub (a b : BitVec 64) : BitVec 64 :=
  let diff := a - b
  bif BitVec.ult a b then diff - EPS else diff

/-- `impl Neg for Fp` -/
def neg (a : BitVec 64) : BitVec 64 :=
  bif a == 0 then 0 else P - a

/-- `reduce_parts`: fold `lo + 2^64 hi` into the field -/
def reduce (lo hi : BitVec 64) : BitVec 64 :=
  let hiHi := hi >>> 32
  let hiLo := hi &&& EPS
  let t0 := lo - hiHi
  let t := bif BitVec.ult lo hiHi then t0 - EPS else t0
  let r0 := t + hiLo * EPS
  let r1 := bif BitVec.ult r0 t then r0 + EPS else r0
  bif BitVec.ule P r1 then r1 - P else r1

/-! ### Range, for every input -/

/-- widen a word for exact sums -/
abbrev W (x : BitVec 64) : BitVec 70 := x.zeroExtend 70
abbrev PW : BitVec 70 := W P

theorem add_exact (a b : BitVec 64) (ha : BitVec.ult a P) (hb : BitVec.ult b P) :
    BitVec.ult (add a b) P ∧ (W a + W b = W (add a b) ∨ W a + W b = W (add a b) + PW) := by
  simp only [add, P, EPS, W, PW] at *
  bv_decide

theorem sub_exact (a b : BitVec 64) (ha : BitVec.ult a P) (hb : BitVec.ult b P) :
    BitVec.ult (sub a b) P ∧ (W a + PW = W (sub a b) + W b ∨ W a = W (sub a b) + W b) := by
  simp only [sub, P, EPS, W, PW] at *
  bv_decide

theorem neg_exact (a : BitVec 64) (ha : BitVec.ult a P) :
    BitVec.ult (neg a) P ∧ (W a + W (neg a) = 0 ∨ W a + W (neg a) = PW) := by
  simp only [neg, P, W, PW] at *
  bv_decide

/-- `reduce` with its one multiply written as a shift: a 32 bit word times
`2^32 - 1` is the word shifted up 32 bits, less itself. Solvers fold adders
well and multipliers badly; this is the form the range proof is solved in. -/
def reduceShift (lo hi : BitVec 64) : BitVec 64 :=
  let hiHi := hi >>> 32
  let hiLo := hi &&& EPS
  let t0 := lo - hiHi
  let t := bif BitVec.ult lo hiHi then t0 - EPS else t0
  let r0 := t + ((hiLo <<< 32) - hiLo)
  let r1 := bif BitVec.ult r0 t then r0 + EPS else r0
  bif BitVec.ule P r1 then r1 - P else r1

theorem mul_eps_is_a_shift (x : BitVec 64) :
    (x &&& EPS) * EPS = ((x &&& EPS) <<< 32) - (x &&& EPS) := by
  generalize hy : x &&& EPS = y
  have h : y.toNat < 2 ^ 32 := by
    subst hy
    rw [BitVec.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have heps : EPS.toNat = 4294967295 := by decide
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, heps]
  simp only [Nat.reducePow, Nat.reduceMod] at h ⊢
  omega

theorem reduce_is_reduce_shift (lo hi : BitVec 64) : reduce lo hi = reduceShift lo hi := by
  simp only [reduce, reduceShift, mul_eps_is_a_shift]

/-- the folded value `lo + P - hi_hi + hi_lo * (2^32 - 1)`, exactly, in 70
bits, the product written as a shift as in `reduceShift` -/
abbrev folded (lo hi : BitVec 64) : BitVec 70 :=
  W lo + PW - W (hi >>> 32) + (W (hi &&& EPS) <<< 32) - W (hi &&& EPS)

/-- `reduce` lands below P, a whole number of P under the folded value -/
theorem reduce_exact (lo hi : BitVec 64) :
    BitVec.ult (reduce lo hi) P ∧
      (folded lo hi = W (reduce lo hi) ∨ folded lo hi = W (reduce lo hi) + PW ∨
        folded lo hi = W (reduce lo hi) + 2 * PW ∨ folded lo hi = W (reduce lo hi) + 3 * PW) := by
  rw [reduce_is_reduce_shift]
  simp only [reduceShift, folded, W, PW, P, EPS]
  bv_decide

/-! ### Congruence, over the integers -/

def p : Nat := 2 ^ 64 - 2 ^ 32 + 1

/-- the folded value is the product modulo P: `2^64 = EPS`, `2^96 = -1` -/
theorem folded_is_the_product (lo hiLo hiHi : Nat) (h1 : hiHi < 2 ^ 32) :
    (lo + p - hiHi + hiLo * (2 ^ 32 - 1)) % p = (lo + 2 ^ 64 * (hiLo + 2 ^ 32 * hiHi)) % p := by
  simp only [p] at *
  omega

end Shield.FieldOps
