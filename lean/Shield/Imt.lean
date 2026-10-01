-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Non-membership in the nullifier set, and why both bounds are strict.

A key is the integer its four limbs denote, which is the order the contract
compares in and the order the circuit walks, so neither side translates.
-/

namespace Shield.Imt

/-- A nullifier as one integer. -/
abbrev Key := Nat

/-- The leaf below a key: its own value, the value it points at, and whether
nothing is above it. `isLast` is a flag rather than a maximum sentinel: a
sentinel would have to be non-canonical to sit above every key, and a
non-canonical value does not survive the field reduction, so the leaf would
commit to something the comparison never sees. -/
structure Leaf where
  value : Key
  next : Key
  isLast : Bool
  deriving DecidableEq

/-- `v` is absent: the low leaf is strictly below it and its neighbour
strictly above, or the low leaf is the last. -/
abbrev excludes (l : Leaf) (v : Key) : Prop :=
  l.value < v ∧ (l.isLast = true ∨ v < l.next)

/-- A key already in the set cannot be shown absent. This is the double spend
the lower bound stops, and it is why that bound is strict. -/
theorem excludes_refuses_the_low_leaf {l : Leaf} {v : Key} (h : excludes l v) :
    v ≠ l.value := by
  intro hv
  subst hv
  exact absurd h.1 (Nat.lt_irrefl _)

/-- The neighbour's own key cannot be shown absent either. It fails through
the upper comparison rather than the lower, so it carries its own forgery. -/
theorem excludes_refuses_the_neighbour {l : Leaf} {v : Key}
    (h : excludes l v) (hlast : l.isLast = false) : v ≠ l.next := by
  intro hv
  rcases h.2 with hl | hr
  · simp [hlast] at hl
  · subst hv
    exact absurd hr (Nat.lt_irrefl _)

/-- Absence is exclusive: no key is both absent under a leaf and equal to
either end of the gap that leaf names. -/
theorem excludes_is_exclusive {l : Leaf} {v : Key}
    (h : excludes l v) (hlast : l.isLast = false) :
    v ≠ l.value ∧ v ≠ l.next :=
  ⟨excludes_refuses_the_low_leaf h, excludes_refuses_the_neighbour h hlast⟩

/-- A batch is sorted strictly, which is what makes a duplicate impossible:
uniqueness becomes a property of the shape rather than a rule to enforce. -/
theorem a_strict_order_excludes_duplicates {a b : Key} (h : a < b) : a ≠ b := by
  intro hab
  subst hab
  exact absurd h (Nat.lt_irrefl _)

/-- The low leaf of a key is strictly below it, so a key is never its own low
leaf and the chain a batch walks cannot revisit a leaf. -/
theorem no_key_is_its_own_low_leaf {l : Leaf} {v : Key} (h : excludes l v) :
    l.value ≠ v := fun hv => absurd (hv ▸ h.1) (Nat.lt_irrefl _)

end Shield.Imt
