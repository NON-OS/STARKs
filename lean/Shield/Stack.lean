-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Params

/-!
The recursive stack, and the floor it clears.

Three layers, three rates, three query counts. A stack is no stronger than its
weakest layer, so the floor is a minimum rather than a sum, and the figure
that has to clear it is the one that does not rest on the conjecture.
-/

namespace Shield.Stack

open Shield.Params

/-- The layers, bottom first: what a sender proves, what a settler folds it
into, and what the chain reads. -/
def layers : List Point := [transfer, settlement, wrap]

/-- A stack is no stronger than its weakest layer. -/
def weakestProvable : List Point → Nat
  | [] => 0
  | [p] => provable p
  | p :: rest => Nat.min (provable p) (weakestProvable rest)

def weakestConjectured : List Point → Nat
  | [] => 0
  | [p] => conjectured p
  | p :: rest => Nat.min (conjectured p) (weakestConjectured rest)

/-- **The stack clears the floor without the conjecture.** -/
theorem the_stack_clears_eighty : 80 ≤ weakestProvable layers := by decide

/-- And it is exactly eighty, at every layer, which is not a coincidence: it
is what holding the provable floor while moving the rate looks like. -/
theorem every_layer_sits_at_eighty :
    provable transfer = 80 ∧ provable settlement = 80 ∧ provable wrap = 80 := by
  decide

/-- The conjectured figure is not uniform, and the layer that steps down is
the one on chain, where the step buys the proof size. -/
theorem the_wrap_is_the_layer_that_steps_down :
    conjectured wrap < conjectured settlement
    ∧ conjectured wrap < conjectured transfer := by decide

/-- The weakest layer by the conjectured figure is the wrap, so a document
that quotes one number for the stack is quoting 128, not 144. -/
theorem the_stack_conjectured_is_the_wrap :
    weakestConjectured layers = conjectured wrap := by decide

/-- Adding a layer never strengthens a stack. -/
theorem a_layer_never_strengthens (p : Point) (rest : List Point) (hne : rest ≠ []) :
    weakestProvable (p :: rest) ≤ weakestProvable rest := by
  cases rest with
  | nil => exact absurd rfl hne
  | cons q qs =>
    simp only [weakestProvable]
    exact Nat.min_le_right _ _

end Shield.Stack
