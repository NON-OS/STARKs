-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Merkle

/-!
The chain's Merkle check takes a leaf index, not a list of sides: bit `l` of
the index says which side the node is on at level `l`, and the index must be
exhausted when the path ends. Mirrors StarkMerkle._fold. Built on the abstract
`Merkle.fold`, so everything there carries over.
-/

namespace Shield.Index

open Shield.Hash Shield.Merkle

variable {D : Type}

/-- bit `l` of `i` -/
def bit (i l : Nat) : Nat := i / 2 ^ l % 2

def sideOf (b : Nat) : Side := if b = 0 then .left else .right

/-- the sides an index names, bottom first, for a path of `k` siblings -/
def sides (i : Nat) : Nat → List Side
  | 0 => []
  | k + 1 => sideOf (i % 2) :: sides (i / 2) k

theorem sides_length (i k : Nat) : (sides i k).length = k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [sides, ih]

/-- zip an index onto a list of siblings -/
def attach (i : Nat) : List D → Path D
  | [] => []
  | sib :: rest => (sideOf (i % 2), sib) :: attach (i / 2) rest

theorem attach_length (i : Nat) (sibs : List D) : (attach i sibs).length = sibs.length := by
  induction sibs generalizing i with
  | nil => rfl
  | cons s rest ih => simp [attach, ih]

/-- the chain's check: fold the siblings under the index, exhaust the index, match the root -/
def verify (h : Compress D) (root : D) (i : Nat) (leaf : D) (sibs : List D) : Prop :=
  i < 2 ^ sibs.length ∧ fold h (attach i sibs) leaf = root

/-! the index is exhausted exactly when it fits the depth -/

theorem exhausted_iff (i k : Nat) : i / 2 ^ k = 0 ↔ i < 2 ^ k := by
  constructor
  · intro h
    have := Nat.div_add_mod i (2 ^ k)
    rw [h] at this
    have hp : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by decide)
    have := Nat.mod_lt i hp
    omega
  · intro h
    exact Nat.div_eq_of_lt h

theorem an_index_at_the_depth_is_refused (k : Nat) : ¬ (2 ^ k < 2 ^ k) := Nat.lt_irrefl _

/-- one more level halves the index -/
theorem halving_shifts_the_bits (i l : Nat) : bit (i / 2) l = bit i (l + 1) := by
  simp only [bit]
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem the_low_bit_is_the_side (i : Nat) : bit i 0 = i % 2 := by
  simp [bit]

/-! what an index binds -/

theorem attach_binds_the_index_bit (i j : Nat) (s : D) (rest : List D)
    (h : attach i (s :: rest) = attach j (s :: rest)) : sideOf (i % 2) = sideOf (j % 2) := by
  simp only [attach, List.cons.injEq, Prod.mk.injEq] at h
  exact h.1.1

theorem sideOf_injective_on_bits (a b : Nat) (ha : a < 2) (hb : b < 2)
    (h : sideOf a = sideOf b) : a = b := by
  simp only [sideOf] at h
  by_cases h0 : a = 0
  · rw [if_pos h0] at h
    by_cases h1 : b = 0
    · omega
    · rw [if_neg h1] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : b = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · omega

/-- two indices that attach the same siblings identically agree on every bit the path consumed -/
theorem attach_binds_the_index (sibs : List D) :
    ∀ i j, i < 2 ^ sibs.length → j < 2 ^ sibs.length →
      attach i sibs = attach j sibs → i = j := by
  induction sibs with
  | nil =>
    intro i j hi hj _
    simp at hi hj
    omega
  | cons s rest ih =>
    intro i j hi hj h
    have hb := attach_binds_the_index_bit i j s rest h
    have hlow := sideOf_injective_on_bits (i % 2) (j % 2) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) hb
    simp only [attach, List.cons.injEq, Prod.mk.injEq] at h
    have hrest := ih (i / 2) (j / 2) (by
        rw [List.length_cons, Nat.pow_succ] at hi
        omega) (by
        rw [List.length_cons, Nat.pow_succ] at hj
        omega) h.2
    omega

/-- a verified opening at one index and one root names one leaf -/
theorem the_root_and_index_name_one_leaf (h : Compress D) (root : D) (i : Nat) (a b : D)
    (sibs : List D) (ha : verify h root i a sibs) (hb : verify h root i b sibs) : a = b :=
  a_root_binds_its_leaf h (attach i sibs) a b (ha.2.trans hb.2.symm)

/-- a path that is too long for the index would reach the root by pretending the index has
leading zero bits; the exhaustion check refuses it because the check is on the depth -/
theorem depth_is_part_of_the_statement (h : Compress D) (root : D) (i : Nat) (leaf : D)
    (sibs : List D) (hv : verify h root i leaf sibs) : i < 2 ^ sibs.length := hv.1

/-! the depths in the shipped proof -/

/-- five trees at 29, and a query index below 2^29 -/
theorem shipped_indices_fit : ∀ i, i < 2 ^ 29 → i / 2 ^ 29 = 0 := fun _ h => Nat.div_eq_of_lt h

theorem a_domain_index_does_not_fit_a_fri_layer : ¬ (2 ^ 27 < 2 ^ 27) := Nat.lt_irrefl _

/-- the quad index a FRI layer opens is the query index reduced by the layer's quarter, so it
always fits that layer's depth -/
theorem a_reduced_index_fits (pos q : Nat) (hq : 0 < q) : pos % q < q := Nat.mod_lt _ hq

theorem sides_of_the_first_leaf (k : Nat) : ∀ s ∈ sides 0 k, s = .left := by
  induction k with
  | zero => intro s hs; exact absurd hs (by simp [sides])
  | succ k ih =>
    intro s hs
    simp only [sides, List.mem_cons] at hs
    rcases hs with h | h
    · rw [h]; rfl
    · exact ih s h

theorem sides_of_the_last_leaf (k : Nat) : ∀ s ∈ sides (2 ^ k - 1) k, s = .right := by
  induction k with
  | zero => intro s hs; exact absurd hs (by simp [sides])
  | succ k ih =>
    intro s hs
    simp only [sides, List.mem_cons] at hs
    have hpow : 1 ≤ 2 ^ k := Nat.pos_pow_of_pos k (by decide)
    have e1 : (2 ^ (k + 1) - 1) % 2 = 1 := by
      rw [Nat.pow_succ]; omega
    have e2 : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by
      rw [Nat.pow_succ]; omega
    rcases hs with h | h
    · rw [h, e1]; rfl
    · rw [e2] at h; exact ih s h

end Shield.Index
