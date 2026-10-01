-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The shared-path walk of docs/14-shared-paths.md, on index sets.

A tree of depth d opened at a set K of leaves. At each level the walk knows
the nodes above the opened leaves; for each known node whose sibling is not
known it reads the sibling from the stream, then it moves to the parents.
The Rust is `merkle::multi`; the chain's walk follows the same order.

Three facts carry the format:
- `carried_is_unknown`: a sibling is read only when the walk could not have
  computed it, so the stream holds nothing redundant;
- `children_available`: every parent's two children are known or carried
  when the walk reaches it, so the walk never stalls and computes every node
  the per-leaf paths would;
- `stream_never_longer`: the stream is at most d digests per opened leaf, the
  cost of separate paths, whatever the set.

`launch_streams` then decides the measured stream lengths of the pinned
transfer from its 19 positions, so this model and the Rust agree on a real
proof and not only on a description.

The sibling is written with arithmetic, `i + 1` or `i - 1` by parity, which is
`i ^ 1` on the naturals; the Rust uses the XOR.
-/

namespace Shield.Multiproof

/-! ### Siblings and parents -/

def sib (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i - 1

theorem sib_ne (i : Nat) : sib i ≠ i := by
  unfold sib; split <;> omega

theorem sib_sib (i : Nat) : sib (sib i) = i := by
  unfold sib; split <;> split <;> omega

theorem sib_parent (i : Nat) : sib i / 2 = i / 2 := by
  unfold sib; split <;> omega

/-- The two nodes under parent `j` are `i` and its sibling, for either child `i`. -/
theorem child_cases (i j : Nat) (h : i / 2 = j) : (i = 2 * j ∧ sib i = 2 * j + 1) ∨ (i = 2 * j + 1 ∧ sib i = 2 * j) := by
  unfold sib; split <;> omega

/-! ### The known set, kept sorted and without repeats -/

def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: ins x ys

def norm : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (norm xs)

theorem mem_ins (a x : Nat) (l : List Nat) : a ∈ ins x l ↔ a = x ∨ a ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    unfold ins
    split
    · simp
    · split
      · rename_i h; subst h; simp
      · simp [ih, or_left_comm]

theorem mem_norm (a : Nat) (l : List Nat) : a ∈ norm l ↔ a ∈ l := by
  induction l with
  | nil => simp [norm]
  | cons x xs ih => simp [norm, mem_ins, ih]

theorem length_ins (x : Nat) (l : List Nat) : (ins x l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    unfold ins
    split
    · simp
    · split
      · simp
      · simp; omega

theorem length_norm (l : List Nat) : (norm l).length ≤ l.length := by
  induction l with
  | nil => simp [norm]
  | cons x xs ih =>
    simp only [norm, List.length_cons]
    exact Nat.le_trans (length_ins x (norm xs)) (Nat.add_le_add_right ih 1)

/-! ### One level of the walk -/

/-- The known nodes whose sibling the stream carries, in the known set's order. -/
def carried (K : List Nat) : List Nat := K.filter (fun i => !(K.contains (sib i)))

/-- The known set one level up. -/
def parents (K : List Nat) : List Nat := norm (K.map (· / 2))

/-- Digests the stream holds for a tree of depth `d` opened at `K`. -/
def streamLen : Nat → List Nat → Nat
  | 0, _ => 0
  | d + 1, K => (carried K).length + streamLen d (parents K)

theorem carried_is_unknown (K : List Nat) (i : Nat) (h : i ∈ carried K) : sib i ∉ K := by
  unfold carried at h
  simp [List.mem_filter] at h
  exact h.2

theorem carried_is_known (K : List Nat) (i : Nat) (h : i ∈ carried K) : i ∈ K := by
  unfold carried at h
  exact (List.mem_filter.mp h).1

/-- Either a node is known or, being the sibling of a known node the stream
carries for, it is read. -/
def available (K : List Nat) (n : Nat) : Prop := n ∈ K ∨ ∃ i, i ∈ carried K ∧ sib i = n

theorem sibling_available (K : List Nat) (i : Nat) (h : i ∈ K) : available K (sib i) := by
  by_cases hs : sib i ∈ K
  · exact Or.inl hs
  · refine Or.inr ⟨i, ?_, rfl⟩
    unfold carried
    simp [List.mem_filter, h, hs]

/-- Every parent the walk moves to has both children in hand. -/
theorem children_available (K : List Nat) (j : Nat) (hj : j ∈ parents K) :
    available K (2 * j) ∧ available K (2 * j + 1) := by
  unfold parents at hj
  rw [mem_norm] at hj
  obtain ⟨i, hi, hij⟩ := List.mem_map.mp hj
  have hs := sibling_available K i hi
  rcases child_cases i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl (h1 ▸ hi), h2 ▸ hs⟩
  · exact ⟨h2 ▸ hs, Or.inl (h1 ▸ hi)⟩

theorem carried_length (K : List Nat) : (carried K).length ≤ K.length := by
  unfold carried
  exact List.length_filter_le _ _

theorem parents_length (K : List Nat) : (parents K).length ≤ K.length := by
  unfold parents
  exact Nat.le_trans (length_norm _) (by simp)

/-- The stream is never longer than a separate path per opened leaf. -/
theorem stream_never_longer (d : Nat) (K : List Nat) : streamLen d K ≤ d * K.length := by
  induction d generalizing K with
  | zero => simp [streamLen]
  | succ d ih =>
    simp only [streamLen]
    have h1 := carried_length K
    have h2 := Nat.le_trans (ih (parents K)) (Nat.mul_le_mul_left d (parents_length K))
    rw [Nat.succ_mul]
    omega

/-- One opened leaf pays exactly its path. -/
theorem one_leaf (d i : Nat) : streamLen d [i] = d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    have hc : carried [i] = [i] := by
      unfold carried
      simp [sib_ne]
    simp [streamLen, hc, parents, norm, ins, ih]
    omega

/-! ### The pinned transfer

The 19 positions the launch verifier draws for `spec/wallet-vectors/transfer-eth`,
printed by `shared_paths_test`. The four base trees have depth 23 and open at
the positions; FRI layer m has depth 21 - 2m and opens at the position modulo
its leaf count. The Rust carried 341, 306, 269, 222 and 187 digests. -/

def positions : List Nat :=
  [4540182, 1495665, 382077, 5200523, 7437701, 303283, 6864698, 3176679, 1408667, 6457868, 7673439, 3831579, 6586047, 2557720, 6819381, 3986117, 858978, 6998869, 2375396]

def fri (m : Nat) : List Nat := positions.map (· % 2 ^ (21 - 2 * m))

theorem launch_streams :
    streamLen 23 (norm positions) = 341 ∧ streamLen 21 (norm (fri 0)) = 306 ∧
      streamLen 19 (norm (fri 1)) = 269 ∧ streamLen 17 (norm (fri 2)) = 222 ∧
      streamLen 15 (norm (fri 3)) = 187 := by
  decide

end Shield.Multiproof
