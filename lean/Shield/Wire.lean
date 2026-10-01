-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Layout

/-!
The strict proof reader in proof_wire/read_rounds.rs and StarkProofReader.sol, at the byte
level. A proof is a list of bytes, every read is a bounded slice, and the reader accepts
exactly the length the layout derives. Field words are refused unless canonical.
-/

namespace Shield.Wire

/-! ## Slices -/

/-- Where the reader is. -/
structure Reader where
  off : Nat
  deriving DecidableEq

def Reader.advance (c : Reader) (n : Nat) : Reader := ⟨c.off + n⟩

/-- `n` bytes at `off`, or nothing when they run past the end. -/
def slice (b : List Nat) (off n : Nat) : Option (List Nat) :=
  if off + n ≤ b.length then some ((b.drop off).take n) else none

/-- A read returns the bytes and the cursor after them. -/
def read (b : List Nat) (c : Reader) (n : Nat) : Option (List Nat × Reader) :=
  (slice b c.off n).map (fun s => (s, c.advance n))

theorem slice_refuses_past_the_end (b : List Nat) (off n : Nat) (h : b.length < off + n) :
    slice b off n = none := by
  unfold slice
  rw [if_neg (show ¬ (off + n ≤ b.length) by omega)]

theorem slice_accepts (b : List Nat) (off n : Nat) (h : off + n ≤ b.length) :
    slice b off n = some ((b.drop off).take n) := by
  unfold slice
  rw [if_pos h]

theorem an_accepted_slice_has_the_asked_length (b s : List Nat) (off n : Nat)
    (h : off + n ≤ b.length) (hs : slice b off n = some s) : s.length = n := by
  rw [slice_accepts b off n h] at hs
  have e := Option.some.inj hs
  rw [← e, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem take_all (b : List Nat) : b.take b.length = b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    show x :: xs.take xs.length = x :: xs
    rw [ih]

theorem slicing_everything_from_zero_is_the_list (b : List Nat) :
    slice b 0 b.length = some b := by
  rw [slice_accepts b 0 b.length (by omega)]
  show some (b.take b.length) = some b
  rw [take_all]

theorem an_empty_slice_inside_the_list_is_empty (b : List Nat) (off : Nat)
    (h : off ≤ b.length) : slice b off 0 = some [] := by
  have e := slice_accepts b off 0 (by omega)
  exact e

theorem advance_adds (c : Reader) (m n : Nat) :
    (c.advance m).advance n = c.advance (m + n) :=
  congrArg Reader.mk (by omega : c.off + m + n = c.off + (m + n))

theorem read_refuses_past_the_end (b : List Nat) (c : Reader) (n : Nat)
    (h : b.length < c.off + n) : read b c n = none := by
  simp only [read, slice_refuses_past_the_end b c.off n h, Option.map]

theorem read_accepts (b : List Nat) (c : Reader) (n : Nat) (h : c.off + n ≤ b.length) :
    read b c n = some ((b.drop c.off).take n, c.advance n) := by
  simp only [read, slice_accepts b c.off n h, Option.map]

theorem slice_examples :
    slice [1, 2, 3, 4] 1 2 = some [2, 3] ∧
    slice [1, 2, 3, 4] 3 2 = none ∧
    slice [1, 2, 3, 4] 0 4 = some [1, 2, 3, 4] ∧
    slice [1, 2, 3, 4] 4 0 = some [] ∧
    slice [] 0 1 = none := by decide

theorem read_examples :
    read [1, 2, 3, 4, 5] ⟨1⟩ 3 = some ([2, 3, 4], ⟨4⟩) ∧
    read [1, 2, 3] ⟨2⟩ 2 = none ∧
    read [7] ⟨0⟩ 1 = some ([7], ⟨1⟩) := by decide

/-! ## Little endian words -/

def u32 (b0 b1 b2 b3 : Nat) : Nat := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3

theorem u32_is_a_word (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256)
    (h3 : b3 < 256) : u32 b0 b1 b2 b3 < 2 ^ 32 := by
  have e : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [e]
  unfold u32
  omega

theorem u32_low_byte (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) : u32 b0 b1 b2 b3 % 256 = b0 := by
  unfold u32
  omega

/-- The query count as it sits on the wire. -/
theorem u32_query_count : u32 12 0 0 0 = 12 := by decide

/-- The region width the chain reads at offset 64. -/
theorem u32_region_width : u32 37 0 0 0 = 37 := by decide

theorem u32_artifact_length : u32 52 183 1 0 = 112436 := by decide

theorem u32_largest : u32 255 255 255 255 = 4294967295 := by decide

/-- A count read from four bytes at `off`, or nothing. -/
def readU32 (bs : List Nat) (off : Nat) : Option Nat :=
  match slice bs off 4 with
  | some [b0, b1, b2, b3] => some (u32 b0 b1 b2 b3)
  | _ => none

theorem read_u32_examples :
    readU32 [12, 0, 0, 0] 0 = some 12 ∧
    readU32 [0, 37, 0, 0, 0] 1 = some 37 ∧
    readU32 [12, 0, 0] 0 = none ∧
    readU32 [12, 0, 0, 0] 1 = none := by decide

/-- Two words make a field word, low word first. -/
def u64 (lo hi : Nat) : Nat := lo + 4294967296 * hi

theorem u64_is_a_word (lo hi : Nat) (hl : lo < 4294967296) (hh : hi < 4294967296) :
    u64 lo hi < 18446744073709551616 := by
  unfold u64
  omega

/-! ## Canonical field words -/

def p : Nat := 18446744069414584321

theorem p_is_goldilocks : p = 2 ^ 64 - 2 ^ 32 + 1 := by decide

/-- The reader refuses a word at or above the modulus. -/
def canonical (x : Nat) : Prop := x < p

instance (x : Nat) : Decidable (canonical x) := Nat.decLt x p

theorem p_minus_one_is_canonical : canonical (p - 1) := by decide

theorem p_is_not_canonical : ¬ canonical p := by decide

theorem the_largest_word_is_not_canonical : ¬ canonical (2 ^ 64 - 1) := by decide

theorem zero_is_canonical : canonical 0 := by decide

/-- The bytes of `p` on the wire: 01 00 00 00 ff ff ff ff. -/
theorem the_bytes_of_p : u64 (u32 1 0 0 0) (u32 255 255 255 255) = p := by decide

theorem the_bytes_of_p_are_refused : ¬ canonical (u64 (u32 1 0 0 0) (u32 255 255 255 255)) := by
  decide

theorem the_bytes_below_p_are_accepted : canonical (u64 (u32 0 0 0 0) (u32 255 255 255 255)) := by
  decide

/-- One residue, two words: `1` and `1 + p` both fit in 64 bits. Only the first is canonical. -/
theorem a_non_canonical_word_aliases_a_canonical_one :
    (1 + p) % p = 1 % p ∧ 1 + p < 2 ^ 64 ∧ canonical 1 ∧ ¬ canonical (1 + p) := by decide

theorem canonical_is_below_the_word_size (x : Nat) (h : canonical x) : x < 2 ^ 64 := by
  have e : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hp : p = 18446744069414584321 := rfl
  rw [e]
  unfold canonical at h
  rw [hp] at h
  omega

/-! ## Strictness -/

/-- The reader accepts exactly the derived length. -/
def strict (expected : Nat) (b : List Nat) : Prop := b.length = expected

instance (e : Nat) (b : List Nat) : Decidable (strict e b) := Nat.decEq b.length e

theorem one_more_byte_is_not_strict (e x : Nat) (b : List Nat) (h : strict e b) :
    ¬ strict e (b ++ [x]) := by
  intro h'
  unfold strict at h h'
  rw [List.length_append, List.length_cons, List.length_nil] at h'
  omega

theorem any_suffix_is_not_strict (e : Nat) (b t : List Nat) (h : strict e b) (ht : t ≠ []) :
    ¬ strict e (b ++ t) := by
  intro h'
  unfold strict at h h'
  rw [List.length_append] at h'
  cases t with
  | nil => exact ht rfl
  | cons y ys =>
    rw [List.length_cons] at h'
    omega

theorem a_prefix_has_its_length (e k : Nat) (b : List Nat) (h : strict e b) (hk : k ≤ e) :
    (b.take k).length = k := by
  unfold strict at h
  rw [List.length_take, h]
  exact Nat.min_eq_left hk

theorem a_proper_prefix_is_not_strict (e k : Nat) (b : List Nat) (h : strict e b) (hk : k < e) :
    ¬ strict e (b.take k) := by
  intro h'
  unfold strict at h'
  rw [a_prefix_has_its_length e k b h (by omega)] at h'
  omega

theorem strict_is_one_length (e : Nat) (a b : List Nat) (ha : strict e a) (hb : strict e b) :
    a.length = b.length := by
  unfold strict at ha hb
  omega

theorem strict_at_the_shipped_total (b : List Nat) :
    strict (Shield.Layout.total Shield.Layout.shippedFour) b ↔ b.length = 112436 := by
  unfold strict
  rw [Shield.Layout.shipped_four_closes]

/-- The artifact with one trailing byte. -/
theorem a_trailing_byte_is_refused (b : List Nat) (h : b.length = 112437) :
    ¬ strict (Shield.Layout.total Shield.Layout.shippedFour) b := by
  intro h'
  unfold strict at h'
  rw [Shield.Layout.shipped_four_closes] at h'
  omega

/-- The artifact with its last byte cut. -/
theorem a_truncated_artifact_is_refused (b : List Nat) (h : b.length = 112435) :
    ¬ strict (Shield.Layout.total Shield.Layout.shippedFour) b := by
  intro h'
  unfold strict at h'
  rw [Shield.Layout.shipped_four_closes] at h'
  omega

theorem strict_examples :
    strict 3 [1, 2, 3] ∧ ¬ strict 3 [1, 2] ∧ ¬ strict 3 [1, 2, 3, 0] := by decide

/-! ## Length prefixes -/

/-- A count of `w`-byte items is read only when the bytes are there. -/
def pathFits (remaining count w : Nat) : Prop := count * w ≤ remaining

instance (r c w : Nat) : Decidable (pathFits r c w) := Nat.decLe (c * w) r

theorem an_oversized_count_is_refused : ¬ pathFits 100 5 24 := by decide

theorem a_shipped_path_fits : pathFits 720 29 24 := by decide

theorem a_shipped_path_is_696_bytes : 29 * 24 = 696 := by decide

theorem the_largest_count_never_fits_the_artifact : ¬ pathFits 112436 4294967295 24 := by
  decide

theorem one_digest_past_the_end_is_refused : ¬ pathFits 695 29 24 := by decide

theorem fits_is_monotone (r r' c w : Nat) (h : pathFits r c w) (hr : r ≤ r') :
    pathFits r' c w := by
  unfold pathFits at *
  omega

theorem a_smaller_count_still_fits (r c c' w : Nat) (h : pathFits r c w) (hc : c' ≤ c) :
    pathFits r c' w := by
  obtain ⟨d, rfl⟩ : ∃ d, c = c' + d := ⟨c - c', by omega⟩
  unfold pathFits at *
  rw [Nat.add_mul] at h
  omega

theorem an_oversized_count_is_refused_in_general (r c w : Nat) (h : r < c * w) :
    ¬ pathFits r c w := by
  unfold pathFits
  omega

/-- The path under every non-FRI tree: a count and 29 digests. -/
theorem the_shipped_path_is_the_perm_stride :
    Shield.Layout.pathBytes Shield.Layout.shippedFour 29 = 700 ∧
    Shield.Layout.permStride Shield.Layout.shippedFour = 700 := by decide

/-! ## Section reads at the shippedFour bases -/

/-- FRI: the count, twelve queries, the grind nonce. -/
theorem fri_section_lands_on_cons : 9760 + 4 + 12 * 3580 + 8 = 52732 := by decide

/-- Consistency: the count and twelve openings. -/
theorem cons_section_lands_on_sidecar : 52732 + 4 + 12 * 2464 = 82304 := by decide

/-- Sidecar: the count, 119 periodic values, twelve openings. -/
theorem sidecar_section_lands_on_perm : 82304 + 4 + 16 * 119 + 12 * 1652 = 104036 := by decide

/-- Permutation: twelve paths, and nothing after them. -/
theorem perm_section_lands_on_the_end : 104036 + 12 * 700 = 112436 := by decide

theorem the_literals_are_the_layout :
    Shield.Layout.friBase Shield.Layout.shippedFour = 9760 ∧
    Shield.Layout.consBase Shield.Layout.shippedFour = 52732 ∧
    Shield.Layout.sidecarBase Shield.Layout.shippedFour = 82304 ∧
    Shield.Layout.permBase Shield.Layout.shippedFour = 104036 ∧
    Shield.Layout.total Shield.Layout.shippedFour = 112436 :=
  ⟨Shield.Layout.shipped_four_strides.2.1, Shield.Layout.shipped_four_strides.2.2.1,
    Shield.Layout.shipped_four_strides.2.2.2.1, Shield.Layout.shipped_four_strides.2.2.2.2,
    Shield.Layout.shipped_four_closes⟩

/-- The head and the four sections, read in order, cover the artifact once. -/
theorem the_sections_cover_the_artifact :
    ([9760, 4 + 12 * 3580 + 8, 4 + 12 * 2464, 4 + 16 * 119 + 12 * 1652, 12 * 700] : List Nat).foldl
      (· + ·) 0 = 112436 := by decide

/-- The count that opens each section is the query count, read as a word. -/
theorem the_section_count_is_the_query_count :
    readU32 [12, 0, 0, 0] 0 = some Shield.Layout.shippedFour.queries := by decide

/-! ## Encodings and digests -/

/-- Two byte strings hash apart unless they are one string. -/
def digestsDiffer (a b : List Nat) : Prop := a ≠ b

theorem padding_is_a_second_encoding (b : List Nat) : digestsDiffer b (b ++ [0]) := by
  unfold digestsDiffer
  intro h
  have := congrArg List.length h
  rw [List.length_append, List.length_cons, List.length_nil] at this
  omega

theorem any_suffix_is_a_second_encoding (b t : List Nat) (ht : t ≠ []) :
    digestsDiffer b (b ++ t) := by
  unfold digestsDiffer
  intro h
  have := congrArg List.length h
  rw [List.length_append] at this
  cases t with
  | nil => exact ht rfl
  | cons y ys =>
    rw [List.length_cons] at this
    omega

/-- Of a proof and its padded twin, the strict reader accepts at most one. -/
theorem strictness_leaves_one_encoding (e : Nat) (b : List Nat) (h : strict e b) :
    digestsDiffer b (b ++ [0]) ∧ ¬ strict e (b ++ [0]) :=
  ⟨padding_is_a_second_encoding b, one_more_byte_is_not_strict e 0 b h⟩

end Shield.Wire
