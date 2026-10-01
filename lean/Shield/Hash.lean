-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The two assumptions everything below rests on, and a witness that they can
both be met at once.

`Compress` and `Quad` are stated over an abstract digest type. Nothing here
assumes Poseidon, the field, or a round count: replace the permutation and the
theorems stand, break its collision resistance and they all fall together.

A development conditional on an assumption proves nothing if the assumption is
unsatisfiable, since everything follows from a hypothesis no structure meets.
`Blob` is a structure meeting both, so the theorems are not vacuous.
-/

namespace Shield.Hash

/-- Two to one compression with collision freedom. The field is a
cryptographic assumption, not a theorem of arithmetic, which is why it is a
hypothesis carried in the structure rather than proved. -/
structure Compress (D : Type) where
  f : D → D → D
  inj : ∀ a b c d, f a b = f c d → a = c ∧ b = d

/-- A fixed arity packing of four field elements into a digest. The note
commitment's public half is one of these. -/
structure Quad (D : Type) where
  pack : Nat → Nat → Nat → Nat → D
  inj : ∀ a b c d a' b' c' d',
    pack a b c d = pack a' b' c' d' → a = a' ∧ b = b' ∧ c = c' ∧ d = d'

namespace Compress

variable {D : Type} (h : Compress D)

theorem left_binds {a b c : D} (hne : a ≠ c) : h.f a b ≠ h.f c b :=
  fun heq => hne (h.inj _ _ _ _ heq).1

theorem right_binds {a b d : D} (hne : b ≠ d) : h.f a b ≠ h.f a d :=
  fun heq => hne (h.inj _ _ _ _ heq).2

theorem left_of_eq {a b c d : D} (heq : h.f a b = h.f c d) : a = c :=
  (h.inj _ _ _ _ heq).1

theorem right_of_eq {a b c d : D} (heq : h.f a b = h.f c d) : b = d :=
  (h.inj _ _ _ _ heq).2

end Compress

/-- A digest that records how it was built. Constructor injectivity gives
collision freedom for free, which is exactly the property a real permutation
is assumed to approximate. -/
inductive Blob where
  | lit : Nat → Blob
  | pair : Blob → Blob → Blob
  deriving DecidableEq

def blobCompress : Compress Blob where
  f := Blob.pair
  inj := by
    intro a b c d hab
    injection hab with h1 h2
    exact ⟨h1, h2⟩

def blobQuad : Quad Blob where
  pack a b c d := .pair (.pair (.lit a) (.lit b)) (.pair (.lit c) (.lit d))
  inj := by
    intro a b c d a' b' c' d' hp
    injection hp with hl hr
    injection hl with p1 p2
    injection hr with p3 p4
    injection p1 with e1
    injection p2 with e2
    injection p3 with e3
    injection p4 with e4
    exact ⟨e1, e2, e3, e4⟩

/-- Both assumptions are met by one structure, so no theorem below is vacuous. -/
theorem the_assumptions_are_satisfiable :
    Nonempty (Compress Blob) ∧ Nonempty (Quad Blob) :=
  ⟨⟨blobCompress⟩, ⟨blobQuad⟩⟩

/-- Collision freedom is not trivially true: the witness separates digests
that differ. A structure where every digest were equal would satisfy nothing. -/
theorem the_witness_separates : blobCompress.f (.lit 0) (.lit 0) ≠ .lit 0 := by
  intro h
  exact Blob.noConfusion h

end Shield.Hash
