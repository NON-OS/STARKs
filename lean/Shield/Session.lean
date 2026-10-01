-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The chunked session RealSplitVerifier keeps on chain. `begin` opens it under
the head's digest, `computeScalar` runs once before any chunk, and each chunk
advances `(nb, nf)` base first and FRI after. A transition that reverts is
`none` here.
-/

namespace Shield.Session

inductive Phase
  | absent
  | opened
  | ready
  | accepted
  deriving DecidableEq

structure Session where
  phase : Phase
  nb : Nat
  nf : Nat
  deriving DecidableEq

def empty : Session := ⟨Phase.absent, 0, 0⟩

/-- `begin`: only a session that does not exist yet can be opened. -/
def open_ (s : Session) : Option Session :=
  if s.phase = Phase.absent then some ⟨Phase.opened, 0, 0⟩ else none

/-- `computeScalar`: only from an opened session, and only once. -/
def scalar (s : Session) : Option Session :=
  if s.phase = Phase.opened then some ⟨Phase.ready, s.nb, s.nf⟩ else none

/-- One piece, base queries first. -/
def bump (n : Nat) (s : Session) : Session :=
  if s.nb < n then ⟨s.phase, s.nb + 1, s.nf⟩ else ⟨s.phase, s.nb, s.nf + 1⟩

def advance (n : Nat) : Nat → Session → Session
  | 0, s => s
  | c + 1, s => bump n (advance n c s)

/-- The session is accepted once both counts reach `n`. -/
def finish (n : Nat) (t : Session) : Session :=
  if t.nb = n ∧ t.nf = n then ⟨Phase.accepted, t.nb, t.nf⟩ else t

/-- A chunk of `count` pieces: only when ready, and never past the last piece. -/
def chunk (n count : Nat) (s : Session) : Option Session :=
  if s.phase = Phase.ready then
    if s.nb + s.nf + count ≤ 2 * n then some (finish n (advance n count s)) else none
  else none

def isAccepted (s : Session) : Bool := decide (s.phase = Phase.accepted)

/-- `k` chunks of `c` pieces each. -/
def chunks (n c : Nat) : Nat → Option Session → Option Session
  | 0, o => o
  | k + 1, o => (chunks n c k o).bind (chunk n c)

/-- A session opened and given its scalar. -/
def started : Option Session := (open_ empty).bind scalar

/-! the shipped walk, twelve queries of each kind -/

theorem started_is_ready : started = some ⟨Phase.ready, 0, 0⟩ := by decide

theorem one_piece_at_a_time : chunks 12 1 24 started = some ⟨Phase.accepted, 12, 12⟩ := by
  decide

theorem one_piece_short : chunks 12 1 23 started = some ⟨Phase.ready, 12, 11⟩ := by decide

theorem one_piece_short_not_accepted : (chunks 12 1 23 started).map isAccepted = some false := by
  decide

theorem accepted_after_all : (chunks 12 1 24 started).map isAccepted = some true := by decide

/-- ScalarNotReady: a chunk straight after `begin` reverts. -/
theorem chunk_before_scalar : (open_ empty).bind (chunk 12 1) = none := by decide

/-- ScalarAlreadyComputed. -/
theorem scalar_twice : started.bind scalar = none := by decide

/-- AlreadyAccepted. -/
theorem chunk_after_accepted : (chunks 12 1 24 started).bind (chunk 12 1) = none := by decide

theorem open_twice : (open_ empty).bind open_ = none := by decide

theorem open_after_scalar : started.bind open_ = none := by decide

theorem scalar_without_open : scalar empty = none := by decide

theorem chunk_without_open : chunk 12 1 empty = none := by decide

/-- One chunk of every piece accepts in one call. -/
theorem all_at_once : started.bind (chunk 12 24) = some ⟨Phase.accepted, 12, 12⟩ := by decide

/-- One piece too many is refused, not clamped. -/
theorem one_too_many : started.bind (chunk 12 25) = none := by decide

theorem two_halves :
    started.bind (chunk 12 12) = some ⟨Phase.ready, 12, 0⟩ ∧
    (started.bind (chunk 12 12)).bind (chunk 12 12) = some ⟨Phase.accepted, 12, 12⟩ := by
  decide

theorem a_chunk_straddles : started.bind (chunk 12 15) = some ⟨Phase.ready, 12, 3⟩ := by decide

theorem chunks_of_five :
    chunks 12 5 4 started = some ⟨Phase.ready, 12, 8⟩ ∧
    (chunks 12 5 4 started).bind (chunk 12 4) = some ⟨Phase.accepted, 12, 12⟩ := by
  decide

/-- The fifth chunk of five would pass the end, so it reverts. -/
theorem fifth_chunk_of_five : chunks 12 5 5 started = none := by decide

/-! the transitions in general -/

theorem open_only_from_absent (s : Session) (h : s.phase ≠ Phase.absent) : open_ s = none := by
  unfold open_
  rw [if_neg h]

theorem scalar_only_from_opened (s : Session) (h : s.phase ≠ Phase.opened) : scalar s = none := by
  unfold scalar
  rw [if_neg h]

theorem scalar_readies (s t : Session) (h : scalar s = some t) :
    t.phase = Phase.ready ∧ t.nb = s.nb ∧ t.nf = s.nf := by
  unfold scalar at h
  by_cases hp : s.phase = Phase.opened
  · rw [if_pos hp] at h
    have e := Option.some.inj h
    subst e
    exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hp] at h
    cases h

/-- The scalar runs at most once. -/
theorem scalar_once (s t : Session) (h : scalar s = some t) : scalar t = none := by
  obtain ⟨hp, _, _⟩ := scalar_readies s t h
  exact scalar_only_from_opened t (by rw [hp]; decide)

theorem chunk_only_when_ready (n c : Nat) (s : Session) (h : s.phase ≠ Phase.ready) :
    chunk n c s = none := by
  unfold chunk
  rw [if_neg h]

theorem accepted_refuses (n c : Nat) (s : Session) (h : s.phase = Phase.accepted) :
    chunk n c s = none :=
  chunk_only_when_ready n c s (by rw [h]; decide)

theorem too_many_refused (n c : Nat) (s : Session) (h : s.nb + s.nf + c > 2 * n) :
    chunk n c s = none := by
  unfold chunk
  have hc : ¬ (s.nb + s.nf + c ≤ 2 * n) := by omega
  rw [if_neg hc]
  by_cases hp : s.phase = Phase.ready
  · rw [if_pos hp]
  · rw [if_neg hp]

/-- A count of one more than the pieces left always reverts. -/
theorem one_past_the_end (n : Nat) (s : Session) :
    chunk n (2 * n - (s.nb + s.nf) + 1) s = none :=
  too_many_refused n (2 * n - (s.nb + s.nf) + 1) s (by omega)

theorem chunk_ready (n c : Nat) (s : Session) (hp : s.phase = Phase.ready)
    (hc : s.nb + s.nf + c ≤ 2 * n) : chunk n c s = some (finish n (advance n c s)) := by
  unfold chunk
  rw [if_pos hp, if_pos hc]

/-- What a chunk that went through tells us. -/
theorem chunk_some (n c : Nat) (s t : Session) (h : chunk n c s = some t) :
    s.phase = Phase.ready ∧ s.nb + s.nf + c ≤ 2 * n ∧ t = finish n (advance n c s) := by
  unfold chunk at h
  by_cases hp : s.phase = Phase.ready
  · rw [if_pos hp] at h
    by_cases hc : s.nb + s.nf + c ≤ 2 * n
    · rw [if_pos hc] at h
      exact ⟨hp, hc, (Option.some.inj h).symm⟩
    · rw [if_neg hc] at h
      cases h
  · rw [if_neg hp] at h
    cases h

/-! pieces -/

theorem advance_succ (n c : Nat) (s : Session) : advance n (c + 1) s = bump n (advance n c s) :=
  rfl

theorem bump_base (n : Nat) (s : Session) (h : s.nb < n) :
    bump n s = ⟨s.phase, s.nb + 1, s.nf⟩ := by
  unfold bump
  rw [if_pos h]

theorem bump_fri (n : Nat) (s : Session) (h : ¬ s.nb < n) :
    bump n s = ⟨s.phase, s.nb, s.nf + 1⟩ := by
  unfold bump
  rw [if_neg h]

theorem bump_phase (n : Nat) (s : Session) : (bump n s).phase = s.phase := by
  by_cases h : s.nb < n
  · simp only [bump_base n s h]
  · simp only [bump_fri n s h]

theorem bump_sum (n : Nat) (s : Session) : (bump n s).nb + (bump n s).nf = s.nb + s.nf + 1 := by
  by_cases h : s.nb < n
  · have e1 : (bump n s).nb = s.nb + 1 := by simp only [bump_base n s h]
    have e2 : (bump n s).nf = s.nf := by simp only [bump_base n s h]
    omega
  · have e1 : (bump n s).nb = s.nb := by simp only [bump_fri n s h]
    have e2 : (bump n s).nf = s.nf + 1 := by simp only [bump_fri n s h]
    omega

theorem advance_phase (n : Nat) (s : Session) : ∀ c, (advance n c s).phase = s.phase := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [advance_succ, bump_phase]
    exact ih

theorem advance_sum (n : Nat) (s : Session) :
    ∀ c, (advance n c s).nb + (advance n c s).nf = s.nb + s.nf + c := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [advance_succ]
    have := bump_sum n (advance n c s)
    omega

/-- The first `n` pieces of a fresh session are base queries. -/
theorem advance_base (n : Nat) (ph : Phase) :
    ∀ c, c ≤ n → advance n c ⟨ph, 0, 0⟩ = ⟨ph, c, 0⟩ := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro h
    have hc : c < n := by omega
    rw [advance_succ, ih (by omega)]
    exact bump_base n ⟨ph, c, 0⟩ hc

/-- The rest are FRI queries. -/
theorem advance_fri (n : Nat) (ph : Phase) :
    ∀ j, advance n (n + j) ⟨ph, 0, 0⟩ = ⟨ph, n, j⟩ := by
  intro j
  induction j with
  | zero =>
    show advance n n ⟨ph, 0, 0⟩ = ⟨ph, n, 0⟩
    exact advance_base n ph n (Nat.le_refl n)
  | succ j ih =>
    rw [← Nat.add_assoc n j 1, advance_succ, ih]
    exact bump_fri n ⟨ph, n, j⟩ (Nat.lt_irrefl n)

/-! acceptance -/

theorem finish_done (n : Nat) (t : Session) (h : t.nb = n ∧ t.nf = n) :
    finish n t = ⟨Phase.accepted, t.nb, t.nf⟩ := by
  unfold finish
  rw [if_pos h]

theorem finish_open (n : Nat) (t : Session) (h : ¬ (t.nb = n ∧ t.nf = n)) : finish n t = t := by
  unfold finish
  rw [if_neg h]

theorem finish_nb (n : Nat) (t : Session) : (finish n t).nb = t.nb := by
  by_cases h : t.nb = n ∧ t.nf = n
  · simp only [finish_done n t h]
  · simp only [finish_open n t h]

theorem finish_nf (n : Nat) (t : Session) : (finish n t).nf = t.nf := by
  by_cases h : t.nb = n ∧ t.nf = n
  · simp only [finish_done n t h]
  · simp only [finish_open n t h]

/-- A chunk advances the session by exactly its count. -/
theorem chunk_advances_by_count (n c : Nat) (s t : Session) (h : chunk n c s = some t) :
    t.nb + t.nf = s.nb + s.nf + c := by
  obtain ⟨_, _, rfl⟩ := chunk_some n c s t h
  rw [finish_nb, finish_nf]
  exact advance_sum n s c

/-- And never past the last piece. -/
theorem chunk_within (n c : Nat) (s t : Session) (h : chunk n c s = some t) :
    t.nb + t.nf ≤ 2 * n := by
  have e := chunk_advances_by_count n c s t h
  obtain ⟨_, hc, _⟩ := chunk_some n c s t h
  omega

/-- A chunk leaves the session ready or accepted, nothing else. -/
theorem chunk_phase (n c : Nat) (s t : Session) (h : chunk n c s = some t) :
    t.phase = Phase.ready ∨ t.phase = Phase.accepted := by
  obtain ⟨hp, _, rfl⟩ := chunk_some n c s t h
  have hr : (advance n c s).phase = Phase.ready := (advance_phase n s c).trans hp
  by_cases hf : (advance n c s).nb = n ∧ (advance n c s).nf = n
  · exact Or.inr (congrArg Session.phase (finish_done n _ hf))
  · refine Or.inl ?_
    rw [finish_open n _ hf]
    exact hr

/-- Accepted means both counts reached `n`. -/
theorem accepted_at_the_end (n c : Nat) (s t : Session) (h : chunk n c s = some t)
    (ha : t.phase = Phase.accepted) : t.nb = n ∧ t.nf = n := by
  obtain ⟨hp, _, rfl⟩ := chunk_some n c s t h
  have hr : (advance n c s).phase = Phase.ready := (advance_phase n s c).trans hp
  by_cases hf : (advance n c s).nb = n ∧ (advance n c s).nf = n
  · rw [finish_nb, finish_nf]
    exact hf
  · rw [finish_open n _ hf, hr] at ha
    cases ha

/-- For every `n`, one chunk of all `2n` pieces accepts a ready session. -/
theorem one_call_accepts (n : Nat) :
    chunk n (2 * n) ⟨Phase.ready, 0, 0⟩ = some ⟨Phase.accepted, n, n⟩ := by
  rw [chunk_ready n (2 * n) ⟨Phase.ready, 0, 0⟩ rfl (by show 0 + 0 + 2 * n ≤ 2 * n; omega)]
  have e : 2 * n = n + n := by omega
  rw [e, advance_fri n Phase.ready n]
  exact congrArg some (finish_done n ⟨Phase.ready, n, n⟩ ⟨rfl, rfl⟩)

/-- And the session it leaves takes no further chunk. -/
theorem nothing_after_one_call (n c : Nat) : chunk n c ⟨Phase.accepted, n, n⟩ = none :=
  accepted_refuses n c ⟨Phase.accepted, n, n⟩ rfl

/-! the key and the restore -/

/-- The session key stands in for the digest of the head. -/
def digest (head : List Nat) : List Nat := head

theorem different_heads_different_sessions (a b : List Nat) (h : a ≠ b) : digest a ≠ digest b :=
  fun e => h e

/-- `restore` on a session already restored reverts. -/
def restore (restored : Bool) : Option Bool := if restored then none else some true

theorem restore_once : restore false = some true := by decide

theorem restore_twice : (restore false).bind restore = none := by decide

end Shield.Session
