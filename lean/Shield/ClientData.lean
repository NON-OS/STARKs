-- NONOS Operating System (AGPL-3.0-or-later)

/-!
The client data a settlement publishes for each output, version 0x01, as
note_seal writes it: the version, the view tag, the X-Wing ciphertext, and
the sealed opening. The pool counts these blobs and never reads one, so the
only guarantees are the ones a reader checks; this file states them.

Two facts carry the privacy argument. A blob is read version first and a
reader that meets another version or length reads nothing, so a format change
is detected rather than guessed at. And the view tag is a function of the
per-note secret, never of the payee alone: a tag that depends only on the
payee puts every note to that payee in one bucket, which sorts the whole pool
by recipient, permanently.
-/

namespace Shield.ClientData

def version : Nat := 1
def kemBytes : Nat := 1088 + 32
def openingBytes : Nat := 8 + 8 + 32
def macBytes : Nat := 16
def blobBytes : Nat := 2 + kemBytes + openingBytes + macBytes
def addressBytes : Nat := 1 + 32 + (1184 + 32)
def aadBytes : Nat := 1 + 1 + 32

theorem the_sizes : kemBytes = 1120 ∧ blobBytes = 1186 ∧ addressBytes = 1249 ∧ aadBytes = 34 := by
  decide

/-! ## Regions -/

structure Region where
  base : Nat
  len : Nat
  deriving DecidableEq

def versionAt : Region := ⟨0, 1⟩
def tagAt : Region := ⟨1, 1⟩
def kemAt : Region := ⟨2, kemBytes⟩
def sealedAt : Region := ⟨2 + kemBytes, openingBytes + macBytes⟩

def regions : List Region := [versionAt, tagAt, kemAt, sealedAt]

/-- each region starts where the one before it ends, and the last ends the blob -/
def tiles : Nat → List Region → Bool
  | at_, [] => at_ == blobBytes
  | at_, r :: rs => r.base == at_ && tiles (at_ + r.len) rs

/-- the four regions cover the blob exactly, no gap and no overlap -/
theorem the_regions_tile_the_blob : tiles 0 regions = true := by decide

theorem the_sealed_part_ends_the_blob : sealedAt.base + sealedAt.len = blobBytes := by decide

/-! ## Reading, version first -/

inductive Read
  | skipped
  | refused
  | opened
  deriving DecidableEq

/-- The reader's decisions in order: length, version, tag, then the AEAD. The
tag and AEAD outcomes are the payee's; everything before them is a byte count
and one byte. -/
def read (len v : Nat) (tagMatches aeadOpens : Bool) : Read :=
  if len ≠ blobBytes then .skipped
  else if v ≠ version then .skipped
  else if !tagMatches then .skipped
  else if !aeadOpens then .refused
  else .opened

/-- another version is skipped whatever else it holds: nothing is guessed -/
theorem another_version_is_skipped (v : Nat) (h : v ≠ version) (t a : Bool) :
    read blobBytes v t a = .skipped := by
  simp [read, h]

theorem another_length_is_skipped (n v : Nat) (h : n ≠ blobBytes) (t a : Bool) :
    read n v t a = .skipped := by
  simp [read, h]

/-- a note is opened only when every check passed -/
theorem opened_means_every_check (n v : Nat) (t a : Bool) (h : read n v t a = .opened) :
    n = blobBytes ∧ v = version ∧ t = true ∧ a = true := by
  unfold read at h
  by_cases h1 : n = blobBytes
  · by_cases h2 : v = version
    · cases t <;> cases a <;> simp_all
    · simp [h1, h2] at h
  · simp [h1] at h

/-- a matching tag with a failing seal is refused, not skipped: a tag collision is
one in 256 and must not be read as a note -/
theorem a_tag_collision_is_refused : read blobBytes version true false = .refused := by decide

/-! ## The view tag -/

/-- A tag scheme: from the payee and the note's own secret to a byte. -/
abbrev TagScheme := Nat → Nat → Nat

/-- The unsafe scheme: the payee alone. -/
def byPayee : TagScheme := fun payee _ => payee % 256

/-- The specified scheme: the per-note secret alone, which the sender draws
fresh for every note and which already depends on the payee's key. -/
def byNote : TagScheme := fun _ secret => secret % 256

/-- under the unsafe scheme every note to one payee carries one tag, so an
observer can put them all in one bucket -/
theorem by_payee_links_every_note (payee s1 s2 : Nat) : byPayee payee s1 = byPayee payee s2 := rfl

/-- under the specified scheme two notes to one payee with different secrets
modulo 256 carry different tags, so the tag names the note and not the payee -/
theorem by_note_separates_notes (payee s1 s2 : Nat) (h : s1 % 256 ≠ s2 % 256) :
    byNote payee s1 ≠ byNote payee s2 := h

/-- and two payees can share a tag: the tag cannot be read as a recipient -/
theorem by_note_can_collide_across_payees : byNote 1 7 = byNote 2 263 := by decide

/-! ## The opening -/

def p : Nat := 18446744069414584321

/-- every blinding word is a canonical field element; two encodings of one
note would be two different blobs for one leaf -/
def canonical (words : List Nat) : Bool := words.all (· < p)

theorem a_word_equal_to_p_is_refused : canonical [p, 0, 0, 0] = false := by decide

theorem the_largest_word_is_accepted : canonical [p - 1, 0, 0, 0] = true := by decide

theorem the_opening_is_value_asset_blinding : openingBytes = 8 + 8 + 4 * 8 := by decide

/-! ## Cost on chain -/

/-- calldata for the two blobs of a two-output settlement. A nonzero byte is four
EIP-7623 tokens at four gas each, sixteen gas, and a ciphertext is nonzero bytes
almost throughout: about 38 thousand gas, not the 9,408 a four-gas-a-byte count gives. -/
theorem two_blobs_cost : 2 * blobBytes = 2372 ∧ 16 * (2 * blobBytes) = 37952 := by decide

end Shield.ClientData
