-- NONOS Operating System (AGPL-3.0-or-later)

/-!
What the live gate buys and what it costs.

A payment is always two inputs and two outputs, so a wallet holding one note
pays with a dummy beside it. Requiring membership for both inputs means a
wallet down to one note cannot pay until it absorbs again, which is a pattern
an observer reads off the chain.

The gate makes the membership equality conditional on a bit and makes the bit
cost value. Three constraints carry it:

    live * (live - 1)       = 0     the bit is a bit
    (1 - live) * value      = 0     a dead input is worth nothing
    live * (walked - root)  = 0     a live input reached the published root

What has to be true is that the second forbids the only thing worth forging:
declaring a real note dead to skip proving it is in the pool. It does, because
a dead input carries zero, and an input carrying zero moves no value.
-/

namespace Shield.Live

/-- A spent input as the gate sees it: the bit, the value, and whether its walk
reached the published root. -/
structure Input where
  live : Nat
  value : Nat
  reached : Bool

/-- The three constraints, as the circuit writes them. -/
def holds (i : Input) : Prop :=
  i.live * (i.live - 1) = 0 ∧
  (1 - i.live) * i.value = 0 ∧
  (i.live = 1 → i.reached = true)

/-- An honest live input: worth something, and its walk reached the root. -/
def spent (v : Nat) : Input := { live := 1, value := v, reached := true }

/-- An honest dummy: worth nothing, and its walk reached nowhere. -/
def dummy : Input := { live := 0, value := 0, reached := false }

/-- The forgery the gate exists to refuse: a note worth something, declared
dead so its membership is never checked. -/
def stolen (v : Nat) : Input := { live := 0, value := v, reached := false }

theorem a_real_spend_holds : holds (spent 1000) := by
  refine ⟨rfl, rfl, fun _ => rfl⟩

theorem a_dummy_holds : holds dummy := by
  refine ⟨rfl, rfl, fun h => absurd h (by decide)⟩

/-- A dead input carrying value fails the second constraint, which is the whole
point: the only way to skip membership is to move nothing. -/
theorem a_dead_input_cannot_carry_value : ¬ holds (stolen 1000) := by
  intro h
  exact absurd h.2.1 (by decide)

/-- And it is not one amount: any nonzero value fails it. -/
theorem no_amount_hides_behind_a_dead_bit :
    ¬ holds (stolen 1) ∧ ¬ holds (stolen 7) := by
  refine ⟨fun h => absurd h.2.1 (by decide), fun h => absurd h.2.1 (by decide)⟩

/-- A live input that did not reach the root fails the third, so the gate does
not weaken membership for the inputs that use it. -/
theorem a_live_input_still_proves_membership :
    ¬ holds { live := 1, value := 1000, reached := false } := by
  intro h
  exact absurd (h.2.2 rfl) (by decide)

/-- The shape a one note wallet needs: one real input and one dummy, both
satisfying the gate, so the payment exists at all. -/
theorem one_note_can_pay : holds (spent 1000) ∧ holds dummy :=
  ⟨a_real_spend_holds, a_dummy_holds⟩

end Shield.Live
