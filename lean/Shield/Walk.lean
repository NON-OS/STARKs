-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The walk the one-call verifier takes over a proof of `2n` pieces, read off
RealSplitVerifier._walk. Base queries go first while `nb < n`, then FRI
queries while `nf < n`. The chunked path runs the same step and persists
`(nb, nf)` between calls, so it has to land where one call would.
-/

namespace Shield.Walk

structure State where
  nb : Nat
  nf : Nat
  deriving DecidableEq

/-- One piece: a base query if any are left, else a FRI query, else nothing. -/
def step (n : Nat) (s : State) : State :=
  if s.nb < n then ⟨s.nb + 1, s.nf⟩ else if s.nf < n then ⟨s.nb, s.nf + 1⟩ else s

/-- `k` pieces. -/
def run (n : Nat) : Nat → State → State
  | 0, s => s
  | k + 1, s => step n (run n k s)

def accepted (n : Nat) (s : State) : Prop := s.nb = n ∧ s.nf = n

instance (n : Nat) (s : State) : Decidable (accepted n s) :=
  inferInstanceAs (Decidable (s.nb = n ∧ s.nf = n))

theorem run_zero (n : Nat) (s : State) : run n 0 s = s := rfl

theorem run_succ (n k : Nat) (s : State) : run n (k + 1) s = step n (run n k s) := rfl

/-! the three branches of a step -/

theorem step_base (n : Nat) (s : State) (h : s.nb < n) : step n s = ⟨s.nb + 1, s.nf⟩ := by
  unfold step
  rw [if_pos h]

theorem step_fri (n : Nat) (s : State) (h1 : ¬ s.nb < n) (h2 : s.nf < n) :
    step n s = ⟨s.nb, s.nf + 1⟩ := by
  unfold step
  rw [if_neg h1, if_pos h2]

theorem step_done (n : Nat) (s : State) (h1 : ¬ s.nb < n) (h2 : ¬ s.nf < n) : step n s = s := by
  unfold step
  rw [if_neg h1, if_neg h2]

/-! the walks the shipped parameters take -/

theorem walk_of_twelve : accepted 12 (run 12 24 ⟨0, 0⟩) := by decide

set_option maxRecDepth 100000 in
theorem walk_of_thirty_two : accepted 32 (run 32 64 ⟨0, 0⟩) := by decide

theorem walk_of_one : accepted 1 (run 1 2 ⟨0, 0⟩) := by decide

/-- An empty proof is accepted after no pieces at all. -/
theorem walk_of_zero : accepted 0 (run 0 0 ⟨0, 0⟩) := by decide

theorem walk_of_twelve_ends_at : run 12 24 ⟨0, 0⟩ = ⟨12, 12⟩ := by decide

/-- Halfway through, every base query is in and no FRI query has started. -/
theorem walk_of_twelve_halfway : run 12 12 ⟨0, 0⟩ = ⟨12, 0⟩ := by decide

theorem walk_of_twelve_first_fri : run 12 13 ⟨0, 0⟩ = ⟨12, 1⟩ := by decide

theorem walk_of_twelve_short : ∀ k < 24, ¬ accepted 12 (run 12 k ⟨0, 0⟩) := by decide

/-! a step stays inside the bounds -/

theorem step_nb_le (n : Nat) (s : State) (hb : s.nb ≤ n) : (step n s).nb ≤ n := by
  by_cases h1 : s.nb < n
  · have e : (step n s).nb = s.nb + 1 := by simp only [step_base n s h1]
    omega
  · by_cases h2 : s.nf < n
    · have e : (step n s).nb = s.nb := by simp only [step_fri n s h1 h2]
      omega
    · have e : (step n s).nb = s.nb := by simp only [step_done n s h1 h2]
      omega

theorem step_nf_le (n : Nat) (s : State) (hf : s.nf ≤ n) : (step n s).nf ≤ n := by
  by_cases h1 : s.nb < n
  · have e : (step n s).nf = s.nf := by simp only [step_base n s h1]
    omega
  · by_cases h2 : s.nf < n
    · have e : (step n s).nf = s.nf + 1 := by simp only [step_fri n s h1 h2]
      omega
    · have e : (step n s).nf = s.nf := by simp only [step_done n s h1 h2]
      omega

theorem run_le (n : Nat) (s : State) (hb : s.nb ≤ n) (hf : s.nf ≤ n) :
    ∀ k, (run n k s).nb ≤ n ∧ (run n k s).nf ≤ n := by
  intro k
  induction k with
  | zero => exact ⟨hb, hf⟩
  | succ k ih =>
    rw [run_succ]
    exact ⟨step_nb_le n _ ih.1, step_nf_le n _ ih.2⟩

/-- While base queries remain, a step leaves the FRI count alone. -/
theorem base_before_fri (n : Nat) (s : State) (h : s.nb < n) : (step n s).nf = s.nf := by
  simp only [step_base n s h]

/-- A FRI step does not touch the base count. -/
theorem fri_keeps_base (n : Nat) (s : State) (h1 : ¬ s.nb < n) (h2 : s.nf < n) :
    (step n s).nb = s.nb := by
  simp only [step_fri n s h1 h2]

/-- Once accepted, a further piece changes nothing. -/
theorem accepted_is_fixed (n : Nat) (s : State) (h : accepted n s) : step n s = s := by
  obtain ⟨h1, h2⟩ := h
  exact step_done n s (by omega) (by omega)

/-- A step that is not at the end moves exactly one piece forward. -/
theorem step_moves_one (n : Nat) (s : State) (hb : s.nb ≤ n) (hf : s.nf ≤ n)
    (hna : ¬ accepted n s) : (step n s).nb + (step n s).nf = s.nb + s.nf + 1 := by
  by_cases h1 : s.nb < n
  · have e1 : (step n s).nb = s.nb + 1 := by simp only [step_base n s h1]
    have e2 : (step n s).nf = s.nf := by simp only [step_base n s h1]
    omega
  · by_cases h2 : s.nf < n
    · have e1 : (step n s).nb = s.nb := by simp only [step_fri n s h1 h2]
      have e2 : (step n s).nf = s.nf + 1 := by simp only [step_fri n s h1 h2]
      omega
    · exact (hna ⟨by omega, by omega⟩).elim

/-! the walk from the start, for every n -/

/-- The first `n` pieces are all base queries. -/
theorem walk_base (n : Nat) : ∀ k, k ≤ n → run n k ⟨0, 0⟩ = ⟨k, 0⟩ := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have hk : k < n := by omega
    rw [run_succ, ih (by omega)]
    exact step_base n ⟨k, 0⟩ hk

/-- The next `n` are all FRI queries. -/
theorem walk_fri (n : Nat) : ∀ j, j ≤ n → run n (n + j) ⟨0, 0⟩ = ⟨n, j⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    show run n n ⟨0, 0⟩ = ⟨n, 0⟩
    exact walk_base n n (Nat.le_refl n)
  | succ j ih =>
    intro h
    have hj : j < n := by omega
    rw [← Nat.add_assoc n j 1, run_succ, ih (by omega)]
    exact step_fri n ⟨n, j⟩ (Nat.lt_irrefl n) hj

/-- Every walk of `2n` pieces from the start is accepted. -/
theorem walk_accepts (n : Nat) : accepted n (run n (2 * n) ⟨0, 0⟩) := by
  have e : 2 * n = n + n := by omega
  rw [e, walk_fri n n (Nat.le_refl n)]
  exact ⟨rfl, rfl⟩

/-- No walk of fewer than `2n` pieces is. -/
theorem walk_short_refused (n k : Nat) (hk : k < 2 * n) : ¬ accepted n (run n k ⟨0, 0⟩) := by
  by_cases hkn : k ≤ n
  · rw [walk_base n k hkn]
    intro h
    obtain ⟨_, h2⟩ := h
    have h3 : (0 : Nat) = n := h2
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    rw [walk_fri n j (by omega)]
    intro h
    obtain ⟨_, h2⟩ := h
    have h3 : j = n := h2
    omega

/-- A FRI query is only ever seen after the last base query. -/
theorem fri_only_after_base (n k : Nat) (hk : k ≤ 2 * n) (hf : 0 < (run n k ⟨0, 0⟩).nf) :
    (run n k ⟨0, 0⟩).nb = n := by
  by_cases hkn : k ≤ n
  · rw [walk_base n k hkn] at hf
    have h0 : (0 : Nat) < 0 := hf
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    exact congrArg State.nb (walk_fri n j (by omega))

/-- Extra pieces past the end are absorbed. -/
theorem walk_past_the_end (n : Nat) :
    ∀ j, run n j (run n (2 * n) ⟨0, 0⟩) = run n (2 * n) ⟨0, 0⟩ := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [run_succ n j, ih]
    exact accepted_is_fixed n _ (walk_accepts n)

/-! chunks -/

/-- Running `b` pieces then `a` pieces is running `a + b`. -/
theorem run_add (n : Nat) (b : Nat) (s : State) :
    ∀ a, run n (a + b) s = run n a (run n b s) := by
  intro a
  induction a with
  | zero =>
    show run n (0 + b) s = run n b s
    rw [Nat.zero_add]
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e, run_succ n (a + b) s, run_succ n a (run n b s), ih]

/-- So two calls of any sizes that add up to `2n` accept. -/
theorem chunks_agree (n a b : Nat) (h : a + b = 2 * n) :
    accepted n (run n a (run n b ⟨0, 0⟩)) := by
  rw [← run_add n b ⟨0, 0⟩ a, h]
  exact walk_accepts n

theorem last_chunk_of_one : run 12 24 ⟨0, 0⟩ = run 12 1 (run 12 23 ⟨0, 0⟩) := by decide

theorem chunks_of_eight :
    run 12 8 (run 12 8 (run 12 8 ⟨0, 0⟩)) = ⟨12, 12⟩ := by decide

theorem chunks_uneven :
    run 12 12 (run 12 7 (run 12 5 ⟨0, 0⟩)) = run 12 24 ⟨0, 0⟩ := by decide

/-- A chunk boundary inside the base queries leaves the FRI count at zero. -/
theorem chunk_inside_base : run 12 5 ⟨0, 0⟩ = ⟨5, 0⟩ := by decide

/-- A chunk that straddles the boundary carries on into the FRI queries. -/
theorem chunk_straddles : run 12 10 (run 12 5 ⟨0, 0⟩) = ⟨12, 3⟩ := by decide

/-! the kinds of piece, in order -/

/-- `true` for a base query, `false` for a FRI query, in the order the walk takes them. -/
def pieces (n : Nat) : Nat → State → List Bool
  | 0, _ => []
  | k + 1, s => decide (s.nb < n) :: pieces n k (step n s)

theorem pieces_length (n : Nat) : ∀ k s, (pieces n k s).length = k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro s
    show (pieces n k (step n s)).length + 1 = k + 1
    rw [ih]

/-- Queries of each kind in the shipped proof. -/
def shipped : Nat := 12

theorem shipped_pieces : 2 * shipped = 24 := by decide

theorem shipped_order :
    pieces shipped 24 ⟨0, 0⟩ = List.replicate 12 true ++ List.replicate 12 false := by decide

theorem shipped_base_count : (pieces shipped 24 ⟨0, 0⟩).take 12 = List.replicate 12 true := by
  decide

theorem shipped_fri_count : (pieces shipped 24 ⟨0, 0⟩).drop 12 = List.replicate 12 false := by
  decide

theorem shipped_walk : run shipped (2 * shipped) ⟨0, 0⟩ = ⟨12, 12⟩ := by decide

end Shield.Walk
