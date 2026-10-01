-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Field

/-!
The checkpoint rule of the membership and chain regions (`multi_membership/rules.rs`).

A region walks a Poseidon state through `depth` compressions of `l` rounds per
opening. The last round of every compression but the last injects a witnessed
sibling by a direction bit. The last round of the last compression is the
checkpoint: its successor row carries the digest the walk reached, and the root
or output pin reads it there.

The checkpoint row has its own selector: the successor holds the round output in
lanes 0 to 3 and zero in lanes 4 to 7. There is no level above the last
compression, so nothing is injected there. On every row that injects nothing,
the direction and sibling are held at zero.

What is proved:
- The schedule, exactly as `periodic_columns` builds it, for every `l ≥ 1` and
  `depth ≥ 1`, with `span = (depth + 1) * l`:
  - `checkpoint_iff`: the checkpoint selector is on at exactly one row of an
    opening, `within = depth * l - 1`;
  - `checkpoint_not_opening_boundary`: the opening boundary never masks it;
  - `fixed_slot_not_checkpoint`: the schedule never injects there.
- The row rule, over the integers modulo `p`, for any row where the selectors
  hold the values the schedule gives them:
  - `checkpoint_carries_the_walked_digest`: on a checkpoint row, lanes 0 to 3 of
    the successor are the round output, lanes 4 to 7 are zero, and the
    direction and sibling are zero;
  - `held_off_injection`: on every row that injects nothing, the direction and
    sibling are zero;
  - `round_row_is_the_round`: on a plain round row the successor is the round.

The round output itself is Poseidon's (`Shield.Poseidon`); here it is an
arbitrary vector, so the statements hold whatever it is.
-/

namespace Shield.Checkpoint

/-! ## The schedule -/

/-- The last round of a compression. -/
def atRowBoundary (l within : Nat) : Bool := within % l == l - 1

/-- The opening boundary: the last row of an opening that has a successor. -/
def opSel (span count opening within : Nat) : Bool :=
  within == span - 1 && opening + 1 < count

/-- The slot injection: every compression's last round but the last one's. -/
def slotFixed (l depth within : Nat) : Bool :=
  atRowBoundary l within && decide (within + l < depth * l)

/-- The checkpoint: the last round of the last compression. -/
def cpSel (l depth within : Nat) : Bool :=
  atRowBoundary l within && within + 1 == depth * l

/-- What the periodic columns hold: each selector is off on an opening boundary. -/
def slotCol (l depth span count opening within : Nat) : Bool :=
  slotFixed l depth within && !opSel span count opening within

def cpCol (l depth span count opening within : Nat) : Bool :=
  cpSel l depth within && !opSel span count opening within

private theorem last_mod (l d : Nat) (hl : 1 ≤ l) : ((d + 1) * l - 1) % l = l - 1 := by
  have h : (d + 1) * l - 1 = (l - 1) + l * d := by
    rw [Nat.succ_mul, Nat.mul_comm l d]; omega
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem checkpoint_iff (l depth within : Nat) (hl : 1 ≤ l) (hd : 1 ≤ depth) :
    cpSel l depth within = true ↔ within = depth * l - 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, depth = d + 1 := ⟨depth - 1, by omega⟩
  have hpos : 1 ≤ (d + 1) * l := Nat.mul_le_mul hd hl
  unfold cpSel atRowBoundary
  constructor
  · intro h
    simp at h
    omega
  · intro h
    subst h
    simp [last_mod l d hl]
    omega

theorem checkpoint_not_opening_boundary (l depth span count opening within : Nat)
    (hl : 1 ≤ l) (hspan : span = (depth + 1) * l) (h : cpSel l depth within = true) :
    opSel span count opening within = false := by
  unfold cpSel at h
  simp at h
  unfold opSel
  have : span = depth * l + l := by rw [hspan, Nat.succ_mul]
  simp
  intro h2
  omega

/-- So the checkpoint column holds exactly the checkpoint selector. -/
theorem cpCol_eq (l depth span count opening within : Nat)
    (hl : 1 ≤ l) (hspan : span = (depth + 1) * l) :
    cpCol l depth span count opening within = cpSel l depth within := by
  unfold cpCol
  cases hc : cpSel l depth within
  · simp
  · simp [checkpoint_not_opening_boundary l depth span count opening within hl hspan hc]

theorem fixed_slot_not_checkpoint (l depth within : Nat) (hl : 1 ≤ l)
    (h : cpSel l depth within = true) : slotFixed l depth within = false := by
  unfold cpSel at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hno : decide (within + l < depth * l) = false := decide_eq_false (by omega)
  unfold slotFixed
  rw [hno, Bool.and_false]

/-- The slot and checkpoint columns are never both on, and neither is on with the
opening boundary, so at most one of the three selectors is one on any row. -/
theorem selectors_exclusive (l depth span count opening within : Nat)
    (hl : 1 ≤ l) (hspan : span = (depth + 1) * l) :
    !(slotCol l depth span count opening within && cpCol l depth span count opening within) ∧
    !(slotCol l depth span count opening within && opSel span count opening within) ∧
    !(cpCol l depth span count opening within && opSel span count opening within) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold slotCol
    cases hc : cpSel l depth within
    · simp [cpCol, hc]
    · simp [fixed_slot_not_checkpoint l depth within hl hc]
  · unfold slotCol; cases opSel span count opening within <;> simp
  · rw [cpCol_eq l depth span count opening within hl hspan]
    cases hc : cpSel l depth within
    · simp
    · simp [checkpoint_not_opening_boundary l depth span count opening within hl hspan hc]

/-! ## The row rule, modulo p -/

/-- `a` and `b` are equal in the field. -/
def Eqv (a b : Int) : Prop := (Shield.Field.p : Int) ∣ a - b

def WIDTH : Nat := 8
def RATE : Nat := 4

/-- One row of the production form: the round output `pr`, the successor state
`nxt`, the witnessed direction and sibling, and the three selectors. -/
structure Row where
  pr : Nat → Int
  nxt : Nat → Int
  dir : Int
  sib : Nat → Int
  slot : Int
  op : Int
  cp : Int

/-- What the injection writes to lane `j`. -/
def inject (r : Row) (j : Nat) : Int :=
  if j < RATE then (1 - r.dir) * r.pr j + r.dir * r.sib j
  else (1 - r.dir) * r.sib (j - RATE) + r.dir * r.pr (j - RATE)

/-- What the checkpoint writes to lane `j`: the digest low, zero high. -/
def checkpoint (r : Row) (j : Nat) : Int := if j < RATE then r.pr j else 0

/-- The constraints `rules.rs` emits for the row, as written there. -/
structure Holds (r : Row) : Prop where
  lane : ∀ j, j < WIDTH →
    Eqv (r.nxt j) (r.op * r.nxt j + r.slot * inject r j + r.cp * checkpoint r j
      + (1 - r.op - r.slot - r.cp) * r.pr j)
  dirBit : Eqv (r.dir * (1 - r.dir)) 0
  dirHeld : Eqv ((1 - r.slot) * r.dir) 0
  sibHeld : ∀ c, c < RATE → Eqv ((1 - r.slot) * r.sib c) 0

theorem held_off_injection (r : Row) (h : Holds r) (hs : r.slot = 0) :
    Eqv r.dir 0 ∧ ∀ c, c < RATE → Eqv (r.sib c) 0 := by
  refine ⟨?_, fun c hc => ?_⟩
  · have := h.dirHeld; simp [hs] at this; exact this
  · have := h.sibHeld c hc; simp [hs] at this; exact this

theorem checkpoint_carries_the_walked_digest (r : Row) (h : Holds r)
    (hs : r.slot = 0) (ho : r.op = 0) (hc : r.cp = 1) :
    (∀ j, j < RATE → Eqv (r.nxt j) (r.pr j)) ∧
    (∀ j, RATE ≤ j → j < WIDTH → Eqv (r.nxt j) 0) ∧
    Eqv r.dir 0 ∧ ∀ c, c < RATE → Eqv (r.sib c) 0 := by
  refine ⟨fun j hj => ?_, fun j hj hw => ?_, held_off_injection r h hs⟩
  · have := h.lane j (by unfold RATE at hj; unfold WIDTH; omega)
    simp [hs, ho, hc, checkpoint, hj] at this
    exact this
  · have := h.lane j hw
    have hn : ¬ j < RATE := by omega
    simp [hs, ho, hc, checkpoint, hn] at this
    exact this

theorem round_row_is_the_round (r : Row) (h : Holds r)
    (hs : r.slot = 0) (ho : r.op = 0) (hc : r.cp = 0) :
    ∀ j, j < WIDTH → Eqv (r.nxt j) (r.pr j) := by
  intro j hj
  have := h.lane j hj
  simp [hs, ho, hc] at this
  exact this

/-! ## The pinned program

The join-split runs `l = 32` rounds per compression, with depth-32 paths
(kinds 2 and 5) and single-compression openings (kinds 1 and 4). -/

theorem pinned_checkpoints :
    (cpSel 32 32 1023 = true ∧ slotFixed 32 32 1023 = false) ∧
    (cpSel 32 1 31 = true ∧ slotFixed 32 1 31 = false) := by
  decide

/-- A membership instance of the join-split: its first row, depth and openings. -/
structure Member where
  off : Nat
  depth : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- The instances, in row order. `checkpoint_lean_test` holds the circuit to this list. -/
def joinSplitMembers : List Member :=
  [⟨8, 1, 2⟩, ⟨136, 1, 2⟩, ⟨264, 1, 2⟩, ⟨392, 1, 2⟩, ⟨520, 32, 1⟩, ⟨1576, 32, 1⟩,
   ⟨2760, 1, 4⟩, ⟨3016, 1, 4⟩, ⟨3272, 32, 1⟩, ⟨4328, 32, 1⟩]

/-- An instance's checkpoint rows: by `checkpoint_iff`, one per opening, at
`within = depth * l - 1` of that opening's span. -/
def checkpointRows (l : Nat) (m : Member) : List Nat :=
  (List.range m.count).map (fun o => m.off + o * ((m.depth + 1) * l) + m.depth * l - 1)

/-- The join-split's 20 checkpoint rows, as `checkpoint_lean_test` reads them
off the assembled circuit's selector columns. -/
theorem join_split_checkpoint_rows :
    joinSplitMembers.foldr (fun m acc => checkpointRows 32 m ++ acc) [] =
      [39, 103, 167, 231, 295, 359, 423, 487, 1543, 2599,
       2791, 2855, 2919, 2983, 3047, 3111, 3175, 3239, 4295, 5351] := by
  decide

end Shield.Checkpoint
