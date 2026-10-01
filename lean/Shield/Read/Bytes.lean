-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The byte primitives of the proof reader, as the Rust `Reader` in
proof_wire/read_rounds.rs and air/wire/deserialize_ext.rs runs them, and
executable over the real artifact.

A read is a function of an offset that returns the value and the offset after
it, or nothing. Every read goes through `take`, which checks its bound before
it slices, so no read can reach past the buffer; that is `take_bound`, and it
is the only place the bound is checked. Every primitive has a fixed width, and
a counted list of fixed-width items is exactly the count times the width.

A count prefix is capped by the bytes left, as the Rust reader caps it. The cap
is a resource guard and nothing else: `capped_eq` proves that a capped read
and an uncapped one agree on every input, so the cap refuses no proof the
reader would otherwise have accepted.
-/

namespace Shield.Read

/-- the Goldilocks modulus; a field word at or above it is refused -/
def p : Nat := 18446744069414584321

/-- the kept bytes of a digest -/
def digestBytes : Nat := 24

theorem p_is_goldilocks : p = 2 ^ 64 - 2 ^ 32 + 1 := by decide

/-- a value and the offset after it, or nothing -/
abbrev Step (α : Type) := Option (α × Nat)

/-- run a read, then the rest from where it ended -/
def andThen {α β : Type} (x : Step α) (k : α → Nat → Step β) : Step β :=
  match x with
  | none => none
  | some (a, j) => k a j

theorem andThen_some {α β : Type} {x : Step α} {k : α → Nat → Step β} {r : β × Nat} :
    andThen x k = some r ↔ ∃ a j, x = some (a, j) ∧ k a j = some r := by
  cases x with
  | none =>
    constructor
    · intro h; cases h
    · intro ⟨_, _, h, _⟩; cases h
  | some v =>
    obtain ⟨a, j⟩ := v
    constructor
    · intro h; exact ⟨a, j, rfl, h⟩
    · intro ⟨a', j', h1, h2⟩
      cases h1
      exact h2

theorem andThen_none {α β : Type} (k : α → Nat → Step β) : andThen none k = none := rfl

/-! ## The one bounds check -/

/-- `n` bytes at `i`, refused when they would run past the end -/
def take (b : ByteArray) (n i : Nat) : Step ByteArray :=
  if i + n ≤ b.size then some (b.extract i (i + n), i + n) else none

theorem take_some {b : ByteArray} {n i j : Nat} {v : ByteArray} (h : take b n i = some (v, j)) :
    j = i + n ∧ j ≤ b.size := by
  unfold take at h
  by_cases hle : i + n ≤ b.size
  · rw [if_pos hle] at h
    cases h
    exact ⟨rfl, hle⟩
  · rw [if_neg hle] at h
    cases h

theorem take_bound (b : ByteArray) (n i : Nat) (h : b.size < i + n) : take b n i = none := by
  unfold take
  rw [if_neg (by omega)]

/-! ## Widths -/

/-- a read that always advances by `w` of what it read, and never past the end -/
def Exact {α : Type} (b : ByteArray) (s : Nat → Step α) (w : α → Nat) : Prop :=
  ∀ i a j, s i = some (a, j) → j = i + w a ∧ j ≤ b.size

theorem take_exact (b : ByteArray) (n : Nat) : Exact b (take b n) (fun _ => n) :=
  fun _ _ _ h => take_some h

/-- little-endian, `n` bytes from `i` -/
@[irreducible] def le (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (b.get! i).toNat + 256 * le b (i + 1) n

def u32 (b : ByteArray) (i : Nat) : Step Nat :=
  andThen (take b 4 i) fun _ j => some (le b i 4, j)

def u64 (b : ByteArray) (i : Nat) : Step Nat :=
  andThen (take b 8 i) fun _ j => some (le b i 8, j)

/-- a field word, refused at or above the modulus: two encodings of one value hash apart -/
def fp (b : ByteArray) (i : Nat) : Step Nat :=
  andThen (u64 b i) fun v j => if v < p then some (v, j) else none

def fp2 (b : ByteArray) (i : Nat) : Step (Nat × Nat) :=
  andThen (fp b i) fun a j => andThen (fp b j) fun c k => some ((a, c), k)

def digest (b : ByteArray) (i : Nat) : Step ByteArray := take b digestBytes i

theorem u32_exact (b : ByteArray) : Exact b (u32 b) (fun _ => 4) := by
  intro i a j h
  try dsimp only
  unfold u32 at h
  rw [andThen_some] at h
  obtain ⟨_, j1, h1, h2⟩ := h
  have e := (Prod.mk.inj (Option.some.inj h2)).2
  subst e
  exact take_some h1

theorem u64_exact (b : ByteArray) : Exact b (u64 b) (fun _ => 8) := by
  intro i a j h
  try dsimp only
  unfold u64 at h
  rw [andThen_some] at h
  obtain ⟨_, j1, h1, h2⟩ := h
  have e := (Prod.mk.inj (Option.some.inj h2)).2
  subst e
  exact take_some h1

theorem fp_exact (b : ByteArray) : Exact b (fp b) (fun _ => 8) := by
  intro i a j h
  try dsimp only
  unfold fp at h
  rw [andThen_some] at h
  obtain ⟨v, j1, h1, h2⟩ := h
  by_cases hv : v < p
  · rw [if_pos hv] at h2
    cases h2
    exact u64_exact b i _ _ h1
  · rw [if_neg hv] at h2
    cases h2

/-- every field word the reader returns is canonical -/
theorem fp_canonical {b : ByteArray} {i j v : Nat} (h : fp b i = some (v, j)) : v < p := by
  unfold fp at h
  rw [andThen_some] at h
  obtain ⟨v', _, _, h2⟩ := h
  by_cases hv : v' < p
  · rw [if_pos hv] at h2
    cases h2
    exact hv
  · rw [if_neg hv] at h2
    cases h2

theorem fp2_exact (b : ByteArray) : Exact b (fp2 b) (fun _ => 16) := by
  intro i a j h
  try dsimp only
  unfold fp2 at h
  rw [andThen_some] at h
  obtain ⟨x, j1, h1, h2⟩ := h
  rw [andThen_some] at h2
  obtain ⟨y, j2, h3, h4⟩ := h2
  cases h4
  have e1 := fp_exact b i x j1 h1
  have e2 := fp_exact b j1 y j h3
  try dsimp only at e1 e2
  exact ⟨by omega, e2.2⟩

theorem fp2_canonical {b : ByteArray} {i j x y : Nat} (h : fp2 b i = some ((x, y), j)) :
    x < p ∧ y < p := by
  unfold fp2 at h
  rw [andThen_some] at h
  obtain ⟨x', j1, h1, h2⟩ := h
  rw [andThen_some] at h2
  obtain ⟨y', _, h3, h4⟩ := h2
  cases h4
  exact ⟨fp_canonical h1, fp_canonical h3⟩

theorem digest_exact (b : ByteArray) : Exact b (digest b) (fun _ => digestBytes) :=
  take_exact b digestBytes

/-! ## Counted lists -/

/-- `n` reads in a row -/
def many {α : Type} (s : Nat → Step α) : Nat → Nat → Step (List α)
  | 0, i => some ([], i)
  | n + 1, i => andThen (s i) fun a j => andThen (many s n j) fun l k => some (a :: l, k)

def sumW {α : Type} (w : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => w a + sumW w l

theorem sumW_const {α : Type} (c : Nat) : ∀ l : List α, sumW (fun _ => c) l = c * l.length
  | [] => rfl
  | _ :: l => by
    show c + sumW (fun _ => c) l = c * (l.length + 1)
    rw [sumW_const c l, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- a list whose every item weighs `c` weighs `c` a item -/
theorem sumW_uniform {α : Type} (w : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ x ∈ l, w x = c) → sumW w l = c * l.length
  | [], _ => rfl
  | a :: l, h => by
    show w a + sumW w l = c * (l.length + 1)
    rw [h a (List.mem_cons_self a l), sumW_uniform w c l (fun x hx => h x (List.mem_cons_of_mem a hx)),
      Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem many_exact {α : Type} {b : ByteArray} {s : Nat → Step α} {w : α → Nat}
    (hs : Exact b s w) : ∀ n i l j, many s n i = some (l, j) → l.length = n ∧ j = i + sumW w l := by
  intro n
  induction n with
  | zero =>
    intro i l j h
    try dsimp only
    cases h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro i l j h
    try dsimp only
    unfold many at h
    rw [andThen_some] at h
    obtain ⟨a, j1, h1, h2⟩ := h
    rw [andThen_some] at h2
    obtain ⟨l', k, h3, h4⟩ := h2
    cases h4
    have e1 := hs i a j1 h1
    have e2 := ih j1 l' j h3
    refine ⟨by rw [List.length_cons, e2.1], ?_⟩
    show j = i + (w a + sumW w l')
    omega

/-- a non-empty run of reads that stay inside the buffer ends inside the buffer -/
theorem many_bound {α : Type} {b : ByteArray} {s : Nat → Step α} {w : α → Nat}
    (hs : Exact b s w) : ∀ n i l j, many s (n + 1) i = some (l, j) → j ≤ b.size := by
  intro n
  induction n with
  | zero =>
    intro i l j h
    try dsimp only
    unfold many at h
    rw [andThen_some] at h
    obtain ⟨a, j1, h1, h2⟩ := h
    rw [andThen_some] at h2
    obtain ⟨l', k, h3, h4⟩ := h2
    cases h4
    cases h3
    exact (hs i a j h1).2
  | succ n ih =>
    intro i l j h
    try dsimp only
    unfold many at h
    rw [andThen_some] at h
    obtain ⟨a, j1, _, h2⟩ := h
    rw [andThen_some] at h2
    obtain ⟨l', k, h3, h4⟩ := h2
    cases h4
    exact ih j1 l' j h3

/-- a count of fixed-width items is the count times the width -/
theorem many_fixed {α : Type} {b : ByteArray} {s : Nat → Step α} {c : Nat}
    (hs : Exact b s (fun _ => c)) (n i : Nat) {l : List α} {j : Nat}
    (h : many s n i = some (l, j)) : l.length = n ∧ j = i + c * n := by
  have e := many_exact hs n i l j h
  refine ⟨e.1, ?_⟩
  rw [e.2, sumW_const, e.1]

/-- a fixed-width run that succeeds fits in what was left -/
theorem many_fits {α : Type} {b : ByteArray} {s : Nat → Step α} {c : Nat}
    (hs : Exact b s (fun _ => c)) (n i : Nat) {l : List α} {j : Nat}
    (h : many s n i = some (l, j)) : c * n ≤ b.size - i := by
  have e := many_fixed hs n i h
  cases n with
  | zero => simp only [Nat.mul_zero, Nat.zero_le]
  | succ n =>
    have hb := many_bound hs n i l j h
    omega

/-! ## The count prefix and its cap -/

/-- a four-byte count, then that many items -/
def counted {α : Type} (b : ByteArray) (s : Nat → Step α) (i : Nat) : Step (List α) :=
  andThen (u32 b i) fun n j => many s n j

/-- the same, with the count refused when the bytes left cannot hold it -/
def capped {α : Type} (b : ByteArray) (s : Nat → Step α) (c : Nat) (i : Nat) : Step (List α) :=
  andThen (u32 b i) fun n j => if c * n ≤ b.size - j then many s n j else none

/-- the cap is a resource guard only: it changes no answer -/
theorem capped_eq {α : Type} {b : ByteArray} {s : Nat → Step α} {c : Nat}
    (hs : Exact b s (fun _ => c)) (i : Nat) : capped b s c i = counted b s i := by
  unfold capped counted
  cases hu : u32 b i with
  | none => rfl
  | some v =>
    obtain ⟨n, j⟩ := v
    show (if c * n ≤ b.size - j then many s n j else none) = many s n j
    by_cases hc : c * n ≤ b.size - j
    · rw [if_pos hc]
    · rw [if_neg hc]
      cases hm : many s n j with
      | none => rfl
      | some r =>
        obtain ⟨l, k⟩ := r
        exact absurd (many_fits hs n j hm) hc

theorem counted_exact {α : Type} {b : ByteArray} {s : Nat → Step α} {w : α → Nat}
    (hs : Exact b s w) : Exact b (counted b s) (fun l => 4 + sumW w l) := by
  intro i l j h
  try dsimp only
  unfold counted at h
  rw [andThen_some] at h
  obtain ⟨n, j1, h1, h2⟩ := h
  have e1 := u32_exact b i n j1 h1
  have e2 := many_exact hs n j1 l j h2
  try dsimp only at e1
  refine ⟨by omega, ?_⟩
  cases n with
  | zero =>
    cases h2
    exact e1.2
  | succ n => exact many_bound hs n j1 l j h2

/-- a Merkle path: a count and that many digests -/
def path (b : ByteArray) (i : Nat) : Step (List ByteArray) := capped b (digest b) digestBytes i

def pathW (l : List ByteArray) : Nat := 4 + digestBytes * l.length

theorem path_is_counted (b : ByteArray) (i : Nat) : path b i = counted b (digest b) i :=
  capped_eq (digest_exact b) i

theorem path_exact (b : ByteArray) : Exact b (path b) pathW := by
  intro i l j h
  try dsimp only
  rw [path_is_counted] at h
  have e := counted_exact (digest_exact b) i l j h
  try dsimp only at e
  rw [sumW_const] at e
  exact e

end Shield.Read
