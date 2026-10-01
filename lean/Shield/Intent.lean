-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The public intent of a join-split, read off shield/join/intent.rs. Thirty-two
field words: two roots, two nullifiers, two output commitments, four scalars
and the recipient. A transfer publishes no clearing price and no recipient,
and the word count does not say which kind of payment it was.
-/

namespace Shield.Intent

/-- four field words -/
structure Digest where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq

def Digest.words (x : Digest) : List Nat := [x.a, x.b, x.c, x.d]

def Digest.zero : Digest := ⟨0, 0, 0, 0⟩

structure Intent where
  noteRoot : Digest
  assocRoot : Digest
  nullifier0 : Digest
  nullifier1 : Digest
  outCm0 : Digest
  outCm1 : Digest
  publicAmount : Nat
  fee : Nat
  assetId : Nat
  clearingPrice : Nat
  recipient : Digest

/-- the order `Intent::words` emits -/
def words (i : Intent) : List Nat :=
  i.noteRoot.words ++ i.assocRoot.words ++ i.nullifier0.words ++ i.nullifier1.words ++
    i.outCm0.words ++ i.outCm1.words ++ [i.publicAmount, i.fee, i.assetId, i.clearingPrice] ++
    i.recipient.words

theorem the_intent_is_thirty_two_words (i : Intent) : (words i).length = 32 := rfl

/-! positions -/

def nth : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

/-- the four words starting at `k` -/
def digestAt (l : List Nat) (k : Nat) : List Nat := (l.drop k).take 4

def positionOfNoteRoot : Nat := 0
def positionOfAssocRoot : Nat := 4
def positionOfNullifier0 : Nat := 8
def positionOfNullifier1 : Nat := 12
def positionOfOutCm0 : Nat := 16
def positionOfOutCm1 : Nat := 20
def positionOfPublicAmount : Nat := 24
def positionOfFee : Nat := 25
def positionOfAssetId : Nat := 26
def positionOfClearingPrice : Nat := 27
def positionOfRecipient : Nat := 28

theorem the_digests_sit_at_their_positions (i : Intent) :
    digestAt (words i) positionOfNoteRoot = i.noteRoot.words ∧
    digestAt (words i) positionOfAssocRoot = i.assocRoot.words ∧
    digestAt (words i) positionOfNullifier0 = i.nullifier0.words ∧
    digestAt (words i) positionOfNullifier1 = i.nullifier1.words ∧
    digestAt (words i) positionOfOutCm0 = i.outCm0.words ∧
    digestAt (words i) positionOfOutCm1 = i.outCm1.words ∧
    digestAt (words i) positionOfRecipient = i.recipient.words :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem the_scalars_sit_at_their_positions (i : Intent) :
    nth (words i) positionOfPublicAmount = some i.publicAmount ∧
    nth (words i) positionOfFee = some i.fee ∧
    nth (words i) positionOfAssetId = some i.assetId ∧
    nth (words i) positionOfClearingPrice = some i.clearingPrice :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- the recipient closes the tuple -/
theorem the_recipient_ends_the_words (i : Intent) :
    positionOfRecipient + 4 = (words i).length := rfl

theorem nothing_sits_past_the_end (i : Intent) : nth (words i) 32 = none := rfl

theorem the_positions_do_not_overlap :
    positionOfNoteRoot + 4 = positionOfAssocRoot ∧
    positionOfAssocRoot + 4 = positionOfNullifier0 ∧
    positionOfNullifier0 + 4 = positionOfNullifier1 ∧
    positionOfNullifier1 + 4 = positionOfOutCm0 ∧
    positionOfOutCm0 + 4 = positionOfOutCm1 ∧
    positionOfOutCm1 + 4 = positionOfPublicAmount ∧
    positionOfPublicAmount + 1 = positionOfFee ∧
    positionOfFee + 1 = positionOfAssetId ∧
    positionOfAssetId + 1 = positionOfClearingPrice ∧
    positionOfClearingPrice + 1 = positionOfRecipient := by decide

/-! the privacy rule -/

def settles (i : Intent) : Prop := i.publicAmount ≠ 0

/-- `publics_region`: settlement fields ride the intent only when value leaves the pool -/
def sanitized (i : Intent) : Intent :=
  { i with
    clearingPrice := if i.publicAmount = 0 then 0 else i.clearingPrice,
    recipient := if i.publicAmount = 0 then Digest.zero else i.recipient }

theorem sanitized_of_transfer (i : Intent) (h : i.publicAmount = 0) :
    sanitized i = { i with clearingPrice := 0, recipient := Digest.zero } := by
  show ({ i with
    clearingPrice := if i.publicAmount = 0 then 0 else i.clearingPrice,
    recipient := if i.publicAmount = 0 then Digest.zero else i.recipient } : Intent) =
    { i with clearingPrice := 0, recipient := Digest.zero }
  rw [if_pos h, if_pos h]

theorem a_transfer_publishes_no_price (i : Intent) (h : i.publicAmount = 0) :
    (sanitized i).clearingPrice = 0 := by
  show (if i.publicAmount = 0 then 0 else i.clearingPrice) = 0
  exact if_pos h

theorem a_transfer_publishes_no_recipient (i : Intent) (h : i.publicAmount = 0) :
    (sanitized i).recipient = Digest.zero := by
  show (if i.publicAmount = 0 then Digest.zero else i.recipient) = Digest.zero
  exact if_pos h

/-- the five settlement words of a transfer are zeros -/
theorem a_transfer_publishes_zero_words (i : Intent) (h : i.publicAmount = 0) :
    (words (sanitized i)).drop positionOfClearingPrice = [0, 0, 0, 0, 0] :=
  (congrArg (fun j => (words j).drop positionOfClearingPrice) (sanitized_of_transfer i h)).trans
    rfl

theorem a_transfer_price_word_is_zero (i : Intent) (h : i.publicAmount = 0) :
    nth (words (sanitized i)) positionOfClearingPrice = some 0 :=
  (congrArg (fun j => nth (words j) positionOfClearingPrice) (sanitized_of_transfer i h)).trans
    rfl

theorem a_settlement_is_untouched (i : Intent) (h : settles i) : sanitized i = i := by
  cases i with
  | mk r0 r1 n0 n1 o0 o1 pa fe ai cp rc =>
    have h' : pa ≠ 0 := h
    show Intent.mk r0 r1 n0 n1 o0 o1 pa fe ai (if pa = 0 then 0 else cp)
      (if pa = 0 then Digest.zero else rc) = Intent.mk r0 r1 n0 n1 o0 o1 pa fe ai cp rc
    rw [if_neg h', if_neg h']

theorem a_settlement_keeps_its_price_and_recipient (i : Intent) (h : settles i) :
    (sanitized i).clearingPrice = i.clearingPrice ∧ (sanitized i).recipient = i.recipient :=
  ⟨congrArg Intent.clearingPrice (a_settlement_is_untouched i h),
   congrArg Intent.recipient (a_settlement_is_untouched i h)⟩

theorem a_settlement_publishes_its_words (i : Intent) (h : settles i) :
    words (sanitized i) = words i :=
  congrArg words (a_settlement_is_untouched i h)

theorem sanitizing_is_idempotent (i : Intent) : sanitized (sanitized i) = sanitized i := by
  by_cases h : i.publicAmount = 0
  · have e := sanitized_of_transfer i h
    rw [e]
    exact sanitized_of_transfer { i with clearingPrice := 0, recipient := Digest.zero } h
  · have h' : settles (sanitized i) := h
    exact a_settlement_is_untouched (sanitized i) h'

theorem sanitizing_keeps_settles (i : Intent) : settles (sanitized i) ↔ settles i := Iff.rfl

/-- the spend half is never rewritten -/
theorem sanitizing_keeps_the_spend (i : Intent) :
    (sanitized i).noteRoot = i.noteRoot ∧ (sanitized i).assocRoot = i.assocRoot ∧
    (sanitized i).nullifier0 = i.nullifier0 ∧ (sanitized i).nullifier1 = i.nullifier1 ∧
    (sanitized i).outCm0 = i.outCm0 ∧ (sanitized i).outCm1 = i.outCm1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sanitizing_keeps_the_amounts (i : Intent) :
    (sanitized i).publicAmount = i.publicAmount ∧ (sanitized i).fee = i.fee ∧
    (sanitized i).assetId = i.assetId :=
  ⟨rfl, rfl, rfl⟩

/-- the first twenty-seven words are the same before and after -/
theorem sanitizing_keeps_the_leading_words (i : Intent) :
    (words (sanitized i)).take positionOfClearingPrice =
      (words i).take positionOfClearingPrice := rfl

theorem sanitizing_keeps_the_word_count (i : Intent) :
    (words (sanitized i)).length = (words i).length :=
  (the_intent_is_thirty_two_words (sanitized i)).trans (the_intent_is_thirty_two_words i).symm

/-! the words bind the intent -/

theorem a_digest_is_its_words (x y : Digest) (hw : x.words = y.words) : x = y := by
  cases x with
  | mk a b c d =>
    cases y with
    | mk a' b' c' d' =>
      have s0 : some a = some a' := congrArg (fun l => nth l 0) hw
      have s1 : some b = some b' := congrArg (fun l => nth l 1) hw
      have s2 : some c = some c' := congrArg (fun l => nth l 2) hw
      have s3 : some d = some d' := congrArg (fun l => nth l 3) hw
      have e0 : a = a' := Option.some.inj s0
      have e1 : b = b' := Option.some.inj s1
      have e2 : c = c' := Option.some.inj s2
      have e3 : d = d' := Option.some.inj s3
      subst e0
      subst e1
      subst e2
      subst e3
      rfl

/-- no two intents publish the same words -/
theorem the_words_determine_the_intent (a b : Intent) (hw : words a = words b) : a = b := by
  cases a with
  | mk r0 r1 n0 n1 o0 o1 pa fe ai cp rc =>
    cases b with
    | mk r0' r1' n0' n1' o0' o1' pa' fe' ai' cp' rc' =>
      have e0 : r0 = r0' := a_digest_is_its_words r0 r0' (congrArg (fun l => digestAt l 0) hw)
      have e1 : r1 = r1' := a_digest_is_its_words r1 r1' (congrArg (fun l => digestAt l 4) hw)
      have e2 : n0 = n0' := a_digest_is_its_words n0 n0' (congrArg (fun l => digestAt l 8) hw)
      have e3 : n1 = n1' := a_digest_is_its_words n1 n1' (congrArg (fun l => digestAt l 12) hw)
      have e4 : o0 = o0' := a_digest_is_its_words o0 o0' (congrArg (fun l => digestAt l 16) hw)
      have e5 : o1 = o1' := a_digest_is_its_words o1 o1' (congrArg (fun l => digestAt l 20) hw)
      have e10 : rc = rc' := a_digest_is_its_words rc rc' (congrArg (fun l => digestAt l 28) hw)
      have s6 : some pa = some pa' := congrArg (fun l => nth l 24) hw
      have s7 : some fe = some fe' := congrArg (fun l => nth l 25) hw
      have s8 : some ai = some ai' := congrArg (fun l => nth l 26) hw
      have s9 : some cp = some cp' := congrArg (fun l => nth l 27) hw
      have e6 : pa = pa' := Option.some.inj s6
      have e7 : fe = fe' := Option.some.inj s7
      have e8 : ai = ai' := Option.some.inj s8
      have e9 : cp = cp' := Option.some.inj s9
      subst e0
      subst e1
      subst e2
      subst e3
      subst e4
      subst e5
      subst e6
      subst e7
      subst e8
      subst e9
      subst e10
      rfl

theorem the_words_bind_the_first_nullifier (a b : Intent) (hw : words a = words b) :
    a.nullifier0 = b.nullifier0 :=
  congrArg Intent.nullifier0 (the_words_determine_the_intent a b hw)

theorem the_words_bind_the_note_root (a b : Intent) (hw : words a = words b) :
    a.noteRoot = b.noteRoot :=
  congrArg Intent.noteRoot (the_words_determine_the_intent a b hw)

theorem distinct_nullifiers_publish_distinct_words (a b : Intent)
    (hne : a.nullifier0 ≠ b.nullifier0) : words a ≠ words b :=
  fun hw => hne (the_words_bind_the_first_nullifier a b hw)

theorem distinct_recipients_publish_distinct_words (a b : Intent)
    (hne : a.recipient ≠ b.recipient) : words a ≠ words b :=
  fun hw => hne (congrArg Intent.recipient (the_words_determine_the_intent a b hw))

/-! a concrete intent, each word naming its own position -/

def demo : Intent :=
  { noteRoot := ⟨1, 2, 3, 4⟩
    assocRoot := ⟨5, 6, 7, 8⟩
    nullifier0 := ⟨9, 10, 11, 12⟩
    nullifier1 := ⟨13, 14, 15, 16⟩
    outCm0 := ⟨17, 18, 19, 20⟩
    outCm1 := ⟨21, 22, 23, 24⟩
    publicAmount := 25
    fee := 26
    assetId := 27
    clearingPrice := 28
    recipient := ⟨29, 30, 31, 32⟩ }

def demoTransfer : Intent := { demo with publicAmount := 0 }

theorem the_demo_words :
    words demo = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
      23, 24, 25, 26, 27, 28, 29, 30, 31, 32] := by decide

theorem the_demo_words_count_up : ∀ k < 32, nth (words demo) k = some (k + 1) := by decide

theorem the_demo_scalars :
    nth (words demo) positionOfPublicAmount = some 25 ∧ nth (words demo) positionOfFee = some 26 ∧
    nth (words demo) positionOfAssetId = some 27 ∧
    nth (words demo) positionOfClearingPrice = some 28 := by decide

theorem the_demo_nullifiers :
    digestAt (words demo) positionOfNullifier0 = [9, 10, 11, 12] ∧
    digestAt (words demo) positionOfNullifier1 = [13, 14, 15, 16] := by decide

theorem the_demo_settlement_is_published_whole : words (sanitized demo) = words demo := by
  decide

theorem the_demo_transfer_is_zeroed :
    words (sanitized demoTransfer) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
      18, 19, 20, 21, 22, 23, 24, 0, 26, 27, 0, 0, 0, 0, 0] := by decide

/-- an unsanitized transfer would publish the price and the address -/
theorem the_raw_transfer_leaks : nth (words demoTransfer) positionOfClearingPrice = some 28 ∧
    digestAt (words demoTransfer) positionOfRecipient = [29, 30, 31, 32] := by decide

theorem one_nullifier_word_changes_the_words :
    words demo ≠ words { demo with nullifier0 := ⟨9, 10, 11, 99⟩ } := by decide

theorem the_transfer_and_the_settlement_differ :
    words (sanitized demo) ≠ words (sanitized demoTransfer) := by decide

end Shield.Intent
