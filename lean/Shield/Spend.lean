-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Balance
import Shield.Hash
import Shield.Key
import Shield.Merkle
import Shield.Note

/-!
The statement a payment proves, composed from the parts.

Two inputs, two outputs. Each input opens to the published note root, retires
under a nullifier derived from its own commitment and its own position, and
the values conserve. The theorems here are the compositions: what an observer
learns from the published tuple, and what an attacker cannot do with it.
-/

namespace Shield.Spend

open Shield.Hash Shield.Merkle

variable {D : Type}

/-- One spent note: the commitment the pool holds, the position it holds it
at, and the path that proves so. -/
structure Input (D : Type) where
  cm : D
  indexTag : D
  path : Path D

/-- The root an input walks to. Membership is this equalling the published
root; the circuit does not check the path, it checks where the path lands. -/
def walked (h : Compress D) (i : Input D) : D := fold h i.path i.cm

def nullifierOf (h : Compress D) (nk : D) (i : Input D) : D :=
  Key.nullifier h nk i.cm i.indexTag

/-- Two inputs at one position with one commitment retire identically, which
is what makes a repeat a collision in the set rather than a second spend. -/
theorem the_nullifier_is_determined (h : Compress D) (nk : D) {a b : Input D}
    (hc : a.cm = b.cm) (hi : a.indexTag = b.indexTag) :
    nullifierOf h nk a = nullifierOf h nk b := by
  simp only [nullifierOf, hc, hi]

/-- There is no third way to move a nullifier. A prover that produces a second
one for a note it already spent moved the commitment or moved the position,
and the membership binding refuses both. -/
theorem a_moved_nullifier_moved_something (h : Compress D) (nk : D) {a b : Input D}
    (hne : nullifierOf h nk a ≠ nullifierOf h nk b) :
    a.cm ≠ b.cm ∨ a.indexTag ≠ b.indexTag := by
  by_cases hc : a.cm = b.cm
  · by_cases hi : a.indexTag = b.indexTag
    · exact absurd (the_nullifier_is_determined h nk hc hi) hne
    · exact Or.inr hi
  · exact Or.inl hc

/-- An input that walks to the published root is the note the pool holds at
that leaf. Two commitments cannot share one opening. -/
theorem an_opening_names_one_note (h : Compress D) {p : Path D} {a b : D}
    (heq : fold h p a = fold h p b) : a = b :=
  a_root_binds_its_leaf h p a b heq

/-- Spending a note the pool does not hold means walking to a root it never
published. -/
theorem a_foreign_note_misses_the_root (h : Compress D) (p : Path D) {a b : D}
    (hne : a ≠ b) : fold h p a ≠ fold h p b :=
  a_foreign_leaf_misses_the_root h p a b hne

/-- The published tuple. Roots, nullifiers, output commitments, and the
settlement fields, which a transfer carries as zeros. -/
structure Publics (D : Type) where
  noteRoot : D
  assocRoot : D
  nf : D × D
  outCm : D × D
  amount : Nat
  fee : Nat

/-- A payment is two in two out whatever it is doing, so the tuple has the
same shape for a one note payment and a two note one. Nothing published counts
how many inputs were real. -/
def publish (h : Compress D) (nk : D) (root assoc : D) (a b : Input D)
    (cm0 cm1 : D) (amount fee : Nat) : Publics D :=
  { noteRoot := root
    assocRoot := assoc
    nf := (nullifierOf h nk a, nullifierOf h nk b)
    outCm := (cm0, cm1)
    amount := amount
    fee := fee }

/-- A transfer publishes the anchors, the nullifiers and the commitments, and
zeros where a settlement would put an amount and a fee. The settle fields
carry no information because they are constants. -/
theorem a_transfer_publishes_zeros (h : Compress D) (nk root assoc : D)
    (a b : Input D) (cm0 cm1 : D) :
    (publish h nk root assoc a b cm0 cm1 0 0).amount = 0
    ∧ (publish h nk root assoc a b cm0 cm1 0 0).fee = 0 := ⟨rfl, rfl⟩

/-- The two nullifiers a payment publishes differ exactly when it is not
spending one note twice, which is the check the set performs and the circuit
does not have to. -/
theorem the_pair_differs_iff_the_inputs_do (h : Compress D) (nk : D) {a b : Input D}
    (hne : nullifierOf h nk a ≠ nullifierOf h nk b) :
    a.cm ≠ b.cm ∨ a.indexTag ≠ b.indexTag :=
  a_moved_nullifier_moved_something h nk hne

/-- Conservation carries through to the published amount: what leaves the pool
is bounded by what the spent notes held. -/
theorem what_leaves_is_bounded (s : Balance.Spend) (h : Balance.balanced s) :
    s.publicAmount + s.fee ≤ s.inA + s.inB :=
  Balance.nothing_leaves_beyond_the_inputs s h

/-- A note the escrow bound cannot be spent for more than it holds: the leaf
names the value, and the balance names the leaf. -/
theorem the_escrow_reaches_the_balance (hc : Compress D) (q : Quad D)
    {vl vh a d vl' vh' a' d' : Nat} {o o' : D}
    (heq : Note.commit hc q vl vh a d o = Note.commit hc q vl' vh' a' d' o') :
    vl = vl' ∧ vh = vh' :=
  let e := Note.the_leaf_binds_the_escrowed_value hc q heq
  ⟨e.1, e.2.1⟩

end Shield.Spend
