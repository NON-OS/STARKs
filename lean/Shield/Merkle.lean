-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Hash

/-!
A membership path and the property membership rests on.

The circuit does not enforce membership by checking a path. A tampered path is
honest arithmetic that walks somewhere else, so membership is the walked root
equalling the published one. What makes that mean anything is that no second
leaf walks the same path to the same root.
-/

namespace Shield.Merkle

open Shield.Hash

variable {D : Type}

/-- Which side the running node takes. Bit `l` of the position set puts it on
the right, the convention the tree, the witness and the index binding share. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

def step (h : Compress D) (s : Side) (sib node : D) : D :=
  match s with
  | .left => h.f node sib
  | .right => h.f sib node

/-- A sibling and a side per level, bottom first. -/
abbrev Path (D : Type) := List (Side × D)

def fold (h : Compress D) : Path D → D → D
  | [], leaf => leaf
  | (s, sib) :: rest, leaf => fold h rest (step h s sib leaf)

theorem step_binds_the_node (h : Compress D) (s : Side) (sib a b : D)
    (hab : step h s sib a = step h s sib b) : a = b := by
  cases s with
  | left =>
    simp only [step] at hab
    exact (h.inj _ _ _ _ hab).1
  | right =>
    simp only [step] at hab
    exact (h.inj _ _ _ _ hab).2

theorem step_binds_the_sibling (h : Compress D) (s : Side) (sib sib' node : D)
    (hab : step h s sib node = step h s sib' node) : sib = sib' := by
  cases s with
  | left =>
    simp only [step] at hab
    exact (h.inj _ _ _ _ hab).2
  | right =>
    simp only [step] at hab
    exact (h.inj _ _ _ _ hab).1

/-- Two leaves that walk one path to one root are one leaf, so an opening
cannot be reused for a note the pool never held. -/
theorem a_root_binds_its_leaf (h : Compress D) :
    ∀ (p : Path D) (a b : D), fold h p a = fold h p b → a = b := by
  intro p
  induction p with
  | nil =>
    intro a b hab
    simp only [fold] at hab
    exact hab
  | cons x rest ih =>
    intro a b hab
    obtain ⟨s, sib⟩ := x
    simp only [fold] at hab
    exact step_binds_the_node h s sib a b (ih _ _ hab)

/-- A leaf the tree does not hold does not reach its root. This is what
`NotInPool` refuses. -/
theorem a_foreign_leaf_misses_the_root (h : Compress D) (p : Path D) (a b : D)
    (hne : a ≠ b) : fold h p a ≠ fold h p b :=
  fun heq => hne (a_root_binds_its_leaf h p a b heq)

/-- A depth zero opening names the leaf and proves nothing else. -/
theorem the_empty_path_is_the_leaf (h : Compress D) (a : D) : fold h [] a = a := rfl

/-- One more level binds the level below it, so depth composes. -/
theorem one_more_level (h : Compress D) (s : Side) (sib : D) (p : Path D) (a : D) :
    fold h ((s, sib) :: p) a = fold h p (step h s sib a) := rfl

end Shield.Merkle
