-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The public words of a settlement: 32 field words laid out as a region of 2^5 rows
(`Publics { log_t: 5, words }` in shield/join/intent.rs) and absorbed before the trace root.
A transfer publishes no price and no recipient.
-/

namespace Shield.Publics

/-! the region -/

def logT : Nat := 5
def rows : Nat := 2 ^ logT
def count : Nat := 32

theorem the_region_holds_every_word : rows = count := by decide

theorem the_region_is_32_rows : rows = 32 := by decide

/-! the layout -/

inductive Field
  | noteRoot
  | assocRoot
  | nullifier0
  | nullifier1
  | outCm0
  | outCm1
  | publicAmount
  | fee
  | assetId
  | clearingPrice
  | recipient
  deriving DecidableEq

def width : Field → Nat
  | .noteRoot | .assocRoot | .nullifier0 | .nullifier1 | .outCm0 | .outCm1 => 4
  | .publicAmount | .fee | .assetId | .clearingPrice => 1
  | .recipient => 4

def layout : List Field :=
  [.noteRoot, .assocRoot, .nullifier0, .nullifier1, .outCm0, .outCm1, .publicAmount, .fee,
   .assetId, .clearingPrice, .recipient]

def widths : List Nat := [4, 4, 4, 4, 4, 4, 1, 1, 1, 1, 4]

def sum : List Nat → Nat
  | [] => 0
  | w :: ws => w + sum ws

theorem the_widths_are_the_layout : layout.map width = widths := by decide

theorem the_widths_sum_to_the_count : sum widths = 32 := by decide

theorem the_widths_fill_the_region : sum widths = rows := by decide

theorem eleven_fields : widths.length = 11 := by decide

theorem seven_digests_and_four_scalars :
    (widths.filter (· == 4)).length = 7 ∧ (widths.filter (· == 1)).length = 4 := by decide

theorem sum_append (a b : List Nat) : sum (a ++ b) = sum a + sum b := by
  induction a with
  | nil => simp only [List.nil_append, sum, Nat.zero_add]
  | cons x xs ih =>
    show x + sum (xs ++ b) = x + sum xs + sum b
    rw [ih]
    omega

/-! offsets -/

/-- the starting word of each field, counted from `acc` -/
def offsetsFrom (acc : Nat) : List Nat → List Nat
  | [] => []
  | w :: ws => acc :: offsetsFrom (acc + w) ws

def offsets (l : List Nat) : List Nat := offsetsFrom 0 l

theorem the_offsets : offsets widths = [0, 4, 8, 12, 16, 20, 24, 25, 26, 27, 28] := by decide

theorem offsets_from_length (l : List Nat) : ∀ acc, (offsetsFrom acc l).length = l.length := by
  induction l with
  | nil => intro acc; rfl
  | cons w ws ih => intro acc; simp only [offsetsFrom, List.length_cons, ih]

theorem offsets_length (l : List Nat) : (offsets l).length = l.length := offsets_from_length l 0

theorem offsets_start_at_zero (w : Nat) (l : List Nat) : (offsets (w :: l)).head? = some 0 := rfl

/-- starting later shifts every offset -/
theorem offsets_shift (b : Nat) (l : List Nat) :
    ∀ a, offsetsFrom (a + b) l = (offsetsFrom a l).map (· + b) := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    show (a + b) :: offsetsFrom (a + b + x) xs = (a + b) :: (offsetsFrom (a + x) xs).map (· + b)
    rw [Nat.add_right_comm, ih (a + x)]

/-- a field appended at the end starts where the sum of the others ends -/
theorem offsets_snoc (w : Nat) (l : List Nat) :
    ∀ a, offsetsFrom a (l ++ [w]) = offsetsFrom a l ++ [a + sum l] := by
  induction l with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    show a :: offsetsFrom (a + x) (xs ++ [w]) =
      a :: (offsetsFrom (a + x) xs ++ [a + (x + sum xs)])
    rw [ih (a + x), Nat.add_assoc]

theorem the_last_field_ends_at_the_sum :
    (offsets widths).getLast? = some 28 ∧ widths.getLast? = some 4 ∧ 28 + 4 = sum widths := by
  decide

theorem every_offset_is_inside_the_region : ∀ o ∈ offsets widths, o < count := by decide

/-! offsets by name -/

def offset : Field → Nat
  | .noteRoot => 0
  | .assocRoot => 4
  | .nullifier0 => 8
  | .nullifier1 => 12
  | .outCm0 => 16
  | .outCm1 => 20
  | .publicAmount => 24
  | .fee => 25
  | .assetId => 26
  | .clearingPrice => 27
  | .recipient => 28

theorem the_named_offsets_are_the_offsets : layout.map offset = offsets widths := by decide

theorem every_field_fits : ∀ f ∈ layout, offset f + width f ≤ count := by decide

theorem no_two_fields_overlap :
    ∀ f ∈ layout, ∀ g ∈ layout, f ≠ g →
      offset f + width f ≤ offset g ∨ offset g + width g ≤ offset f := by decide

/-- the field a word belongs to -/
def locate (i : Nat) : Option Field :=
  layout.find? (fun f => decide (offset f ≤ i) && decide (i < offset f + width f))

theorem every_word_has_a_field : ∀ i < 32, (locate i).isSome = true := by decide

theorem no_word_past_the_region : locate 32 = none := by decide

theorem the_scalars :
    locate 24 = some .publicAmount ∧ locate 25 = some .fee ∧ locate 26 = some .assetId ∧
    locate 27 = some .clearingPrice := by decide

theorem the_recipient_is_the_last_four_words :
    locate 28 = some .recipient ∧ locate 31 = some .recipient := by decide

/-! a word is a field element -/

def p : Nat := 18446744069414584321

theorem p_is_goldilocks : p = 2 ^ 64 - 2 ^ 32 + 1 := by decide

def canonical (x : Nat) : Prop := x < p

instance (x : Nat) : Decidable (canonical x) := by unfold canonical; infer_instance

/-- a raw u64 can reach past p -/
theorem a_u64_can_exceed_the_field : 2 ^ 64 - 1 ≥ p := by decide

theorem the_largest_u64_is_not_canonical : ¬ canonical (2 ^ 64 - 1) := by decide

theorem non_canonical_u64s : 2 ^ 64 - p = 4294967295 := by decide

def reduce (x : Nat) : Nat := x % p

theorem reduce_is_canonical (x : Nat) : canonical (reduce x) := by
  unfold canonical reduce
  exact Nat.mod_lt _ (by decide)

/-- two different u64 amounts publish the same word -/
theorem a_non_canonical_amount_aliases :
    (2 ^ 64 - 1 : Nat) ≠ 4294967294 ∧ reduce (2 ^ 64 - 1) = reduce 4294967294 := by decide

/-- the balance rule bounds amounts by 2^63 -/
theorem the_amount_bound_is_under_p : 2 ^ 63 < p := by decide

theorem the_amount_bound : (2 ^ 63 : Nat) = 9223372036854775808 := by decide

theorem a_bounded_amount_is_canonical (a : Nat) (h : a < 9223372036854775808) : canonical a := by
  unfold canonical p
  omega

theorem a_bounded_amount_is_its_own_word (a : Nat) (h : a < 9223372036854775808) :
    reduce a = a := by
  unfold reduce
  exact Nat.mod_eq_of_lt (a_bounded_amount_is_canonical a h)

/-! the privacy rule -/

/-- the eleven fields; a digest stands for its four words -/
structure Words where
  noteRoot : Nat
  assocRoot : Nat
  nullifier0 : Nat
  nullifier1 : Nat
  outCm0 : Nat
  outCm1 : Nat
  publicAmount : Nat
  fee : Nat
  assetId : Nat
  clearingPrice : Nat
  recipient : Nat
  deriving DecidableEq

/-- a transfer (public_amount = 0) publishes no price and no recipient -/
def sanitize (w : Words) : Words :=
  if w.publicAmount = 0 then { w with clearingPrice := 0, recipient := 0 } else w

theorem sanitize_transfer (w : Words) (h : w.publicAmount = 0) :
    sanitize w = { w with clearingPrice := 0, recipient := 0 } := by
  unfold sanitize
  rw [if_pos h]

theorem sanitize_settlement (w : Words) (h : w.publicAmount ≠ 0) : sanitize w = w := by
  unfold sanitize
  rw [if_neg h]

theorem sanitize_is_idempotent (w : Words) : sanitize (sanitize w) = sanitize w := by
  by_cases h : w.publicAmount = 0
  · have h2 : sanitize { w with clearingPrice := 0, recipient := 0 } =
        { w with clearingPrice := 0, recipient := 0 } :=
      sanitize_transfer { w with clearingPrice := 0, recipient := 0 } h
    rw [sanitize_transfer w h]
    exact h2
  · rw [sanitize_settlement w h, sanitize_settlement w h]

theorem a_transfer_publishes_no_price_or_recipient (w : Words) (h : w.publicAmount = 0) :
    (sanitize w).clearingPrice = 0 ∧ (sanitize w).recipient = 0 := by
  rw [sanitize_transfer w h]
  exact ⟨rfl, rfl⟩

theorem a_settlement_is_untouched (w : Words) (h : w.publicAmount ≠ 0) :
    (sanitize w).clearingPrice = w.clearingPrice ∧ (sanitize w).recipient = w.recipient := by
  rw [sanitize_settlement w h]
  exact ⟨rfl, rfl⟩

theorem sanitize_keeps_the_amount (w : Words) : (sanitize w).publicAmount = w.publicAmount := by
  by_cases h : w.publicAmount = 0
  · exact (congrArg Words.publicAmount (sanitize_transfer w h)).trans rfl
  · exact congrArg Words.publicAmount (sanitize_settlement w h)

theorem sanitize_keeps_the_nullifiers (w : Words) :
    (sanitize w).nullifier0 = w.nullifier0 ∧ (sanitize w).nullifier1 = w.nullifier1 := by
  by_cases h : w.publicAmount = 0
  · exact ⟨(congrArg Words.nullifier0 (sanitize_transfer w h)).trans rfl,
      (congrArg Words.nullifier1 (sanitize_transfer w h)).trans rfl⟩
  · exact ⟨congrArg Words.nullifier0 (sanitize_settlement w h),
      congrArg Words.nullifier1 (sanitize_settlement w h)⟩

theorem sanitize_keeps_the_fee (w : Words) : (sanitize w).fee = w.fee := by
  by_cases h : w.publicAmount = 0
  · exact (congrArg Words.fee (sanitize_transfer w h)).trans rfl
  · exact congrArg Words.fee (sanitize_settlement w h)

def exampleTransfer : Words :=
  { noteRoot := 11, assocRoot := 12, nullifier0 := 13, nullifier1 := 14, outCm0 := 15,
    outCm1 := 16, publicAmount := 0, fee := 3, assetId := 1, clearingPrice := 7, recipient := 99 }

def exampleSettlement : Words := { exampleTransfer with publicAmount := 500 }

theorem the_example_transfer_is_cleared :
    sanitize exampleTransfer = { exampleTransfer with clearingPrice := 0, recipient := 0 } := by
  decide

theorem the_example_settlement_is_kept : sanitize exampleSettlement = exampleSettlement := by
  decide

/-! absorb order -/

def absorbPosition (i : Nat) : Nat := i
def traceRootPosition : Nat := 32
def betaPosition : Nat := 33
def gammaPosition : Nat := 34
def permRootPosition : Nat := 35

theorem every_public_precedes_the_trace_root :
    ∀ i < 32, absorbPosition i < traceRootPosition := by decide

theorem a_public_precedes_the_trace_root (i : Nat) (h : i < count) :
    absorbPosition i < traceRootPosition := by
  simp only [absorbPosition, traceRootPosition, count] at h ⊢
  omega

theorem the_trace_root_follows_the_last_public :
    traceRootPosition = absorbPosition (count - 1) + 1 := by decide

theorem the_copy_challenges_follow_the_trace_root :
    traceRootPosition < betaPosition ∧ betaPosition < gammaPosition ∧
    gammaPosition < permRootPosition := by decide

/-! the z replay -/

def coefficientCount : Nat := 37 + 723

theorem the_coefficient_count : coefficientCount = 760 := by decide

theorem two_squeezes_each : 2 * coefficientCount = 1520 := by decide

def coefficientPosition (j : Nat) : Nat := permRootPosition + 1 + j

theorem every_coefficient_follows_the_permutation_root (j : Nat) :
    permRootPosition < coefficientPosition j := by
  unfold coefficientPosition
  omega

theorem every_coefficient_follows_every_public (i j : Nat) (h : i < count) :
    absorbPosition i < coefficientPosition j := by
  simp only [absorbPosition, coefficientPosition, permRootPosition, count] at h ⊢
  omega

theorem the_first_coefficient : coefficientPosition 0 = 36 := by decide

theorem the_last_coefficient : coefficientPosition (coefficientCount - 1) = 795 := by decide

end Shield.Publics
