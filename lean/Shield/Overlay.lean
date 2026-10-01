-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The periodic overlay (`Stack::overlay`): every kind's
periodic slots on one set of columns, where each kind had its own.

The model. Regions are row intervals `[off, off + len)` with a kind. A row's owner is
the region containing it. The stacked layout gives kind `k` its own column for slot
`j`, holding `k`'s schedule on rows `k` owns and zero elsewhere. The overlay gives
slot `j` one column, holding the owner's schedule on every owned row. Kind `k` is
active at row `r` when `k` owns `r` and `r + 1` too: its selector is on for every
row of a region but its last, since a transition reads the row and the next.

What is proved:
- `overlay_agrees`: at every row where kind `k` is active, the overlaid column holds
  exactly what `k`'s own stacked column holds. So no constraint of `k` that reads
  its slots at its own row can tell the layouts apart.
- `window_stays_home`: where `k` is active, the next row has the same owner, so a
  transition's window never reaches a row whose schedule belongs to another kind.
- `owner_of_member`: with the regions pairwise disjoint, the owner of a row is the one
  region that contains it, whatever the order.

Constraints read periodic values at their own row only: the AIR interface passes a
single row of them (`transition(window, periodic)`), and no region reads another
row's. `launch_regions_disjoint` decides disjointness for the launch circuit's 17
region instances; `overlay_test` checks the Rust against this on every row of a
random trace.
-/

namespace Shield.Overlay

structure Region where
  off : Nat
  len : Nat
  kind : Nat
  deriving DecidableEq, Repr

def contains (g : Region) (r : Nat) : Bool := decide (g.off ≤ r ∧ r < g.off + g.len)

def owner : List Region → Nat → Option Region
  | [], _ => none
  | g :: gs, r => if contains g r then some g else owner gs r

/-- Two regions share no row. -/
def disjoint (a b : Region) : Prop := a.off + a.len ≤ b.off ∨ b.off + b.len ≤ a.off

instance (a b : Region) : Decidable (disjoint a b) := by unfold disjoint; infer_instance

def pairwiseDisjoint : List Region → Prop
  | [] => True
  | g :: gs => (∀ h ∈ gs, disjoint g h) ∧ pairwiseDisjoint gs

def decPairwiseDisjoint : (rs : List Region) → Decidable (pairwiseDisjoint rs)
  | [] => isTrue trivial
  | g :: gs =>
    match List.decidableBAll (fun h => disjoint g h) gs, decPairwiseDisjoint gs with
    | isTrue h1, isTrue h2 => isTrue ⟨h1, h2⟩
    | isFalse h1, _ => isFalse (fun h => h1 h.1)
    | _, isFalse h2 => isFalse (fun h => h2 h.2)

instance (rs : List Region) : Decidable (pairwiseDisjoint rs) := decPairwiseDisjoint rs

theorem owner_of_member (rs : List Region) (g : Region) (r : Nat)
    (hd : pairwiseDisjoint rs) (hg : g ∈ rs) (hc : contains g r = true) : owner rs r = some g := by
  induction rs with
  | nil => simp at hg
  | cons a as ih =>
    simp only [owner]
    rcases List.mem_cons.mp hg with h | h
    · subst h; simp [hc]
    · have hda := hd.1 g h
      have hnot : contains a r = false := by
        unfold contains at hc ⊢
        unfold disjoint at hda
        simp at hc ⊢
        omega
      simp [hnot]
      exact ih hd.2 h

/-- Kind `k`'s own stacked column for slot `j`. -/
def stacked (rs : List Region) (sched : Nat → Nat → Nat → Nat) (k j r : Nat) : Nat :=
  match owner rs r with
  | some g => if g.kind = k then sched k j (r - g.off) else 0
  | none => 0

/-- The overlaid column for slot `j`. -/
def overlaid (rs : List Region) (sched : Nat → Nat → Nat → Nat) (j r : Nat) : Nat :=
  match owner rs r with
  | some g => sched g.kind j (r - g.off)
  | none => 0

/-- Kind `k` is live at row `r`: it owns `r`, and `r` is not its region's last row. -/
def active (rs : List Region) (k r : Nat) : Bool :=
  match owner rs r with
  | some g => decide (g.kind = k ∧ r + 1 < g.off + g.len)
  | none => false

theorem overlay_agrees (rs : List Region) (sched : Nat → Nat → Nat → Nat) (k j r : Nat)
    (h : active rs k r = true) : overlaid rs sched j r = stacked rs sched k j r := by
  unfold active at h
  unfold overlaid stacked
  cases ho : owner rs r with
  | none => simp [ho] at h
  | some g =>
    simp [ho] at h
    simp [h.1]

theorem owner_contains (rs : List Region) (g : Region) (r : Nat) (h : owner rs r = some g) :
    g ∈ rs ∧ contains g r = true := by
  induction rs with
  | nil => simp [owner] at h
  | cons a as ih =>
    simp only [owner] at h
    by_cases ha : contains a r = true
    · simp [ha] at h; subst h; exact ⟨List.mem_cons_self _ _, ha⟩
    · simp [ha] at h
      obtain ⟨hm, hc⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hc⟩

theorem window_stays_home (rs : List Region) (k r : Nat) (hd : pairwiseDisjoint rs)
    (h : active rs k r = true) : owner rs (r + 1) = owner rs r := by
  unfold active at h
  cases ho : owner rs r with
  | none => simp [ho] at h
  | some g =>
    simp [ho] at h
    obtain ⟨hm, hc⟩ := owner_contains rs g r ho
    have hc' : contains g (r + 1) = true := by
      unfold contains at hc ⊢
      simp at hc ⊢
      omega
    exact owner_of_member rs g (r + 1) hd hm hc'

/-! ### The launch circuit's regions

From the per-kind placement report (`print_the_kinds_in_region_periods`): each
instance's first row and height, by kind. -/

def launchRegions : List Region :=
  [⟨0, 8, 0⟩, ⟨8, 128, 1⟩, ⟨136, 128, 1⟩, ⟨264, 128, 1⟩, ⟨392, 128, 1⟩,
   ⟨520, 1056, 2⟩, ⟨1576, 1056, 2⟩, ⟨2632, 64, 3⟩, ⟨2696, 64, 3⟩,
   ⟨2760, 256, 4⟩, ⟨3016, 256, 4⟩, ⟨3272, 1056, 5⟩, ⟨4328, 1056, 5⟩,
   ⟨5384, 2, 7⟩, ⟨5386, 2, 7⟩, ⟨5388, 64, 6⟩, ⟨5452, 580, 8⟩]

theorem launch_regions_disjoint : pairwiseDisjoint launchRegions := by decide

/-- So for the launch circuit, at every row where a kind is live, the overlay
reads that kind's own schedule, and its window stays in its own region. -/
theorem launch_overlay_is_faithful (sched : Nat → Nat → Nat → Nat) (k j r : Nat)
    (h : active launchRegions k r = true) :
    overlaid launchRegions sched j r = stacked launchRegions sched k j r ∧
      owner launchRegions (r + 1) = owner launchRegions r :=
  ⟨overlay_agrees _ _ _ _ _ h, window_stays_home _ _ _ launch_regions_disjoint h⟩

end Shield.Overlay
