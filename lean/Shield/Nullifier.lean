-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Hash
import Shield.Key

/-!
The chain's nullifier set. Every accepted spend publishes its nullifiers, the
contract inserts them, and a value already present is refused. With the
nullifier derivation from `Shield.Key`, a second spend of one note collides in
the set, and two distinct notes never do.
-/

namespace Shield.Nullifier

open Shield.Hash

variable {D : Type} [DecidableEq D]

def has (x : D) : List D → Bool
  | [] => false
  | y :: ys => if y = x then true else has x ys

/-- the contract's insert: a repeat is refused, a fresh value is prepended -/
protected def insert (nf : D) (s : List D) : Option (List D) :=
  if has nf s then none else some (nf :: s)

/-- a batch of inserts, refused as a whole if any one is -/
def insertAll : List D → List D → Option (List D)
  | [], s => some s
  | nf :: rest, s => Option.bind (Nullifier.insert nf s) (fun s' => insertAll rest s')

/-! membership -/

theorem has_nil (x : D) : has x [] = false := rfl

theorem has_cons_self {x : D} {s : List D} : has x (x :: s) = true := by
  show (if x = x then true else has x s) = true
  exact if_pos (Eq.refl x)

theorem has_cons_of_ne {x y : D} {s : List D} (hne : y ≠ x) : has x (y :: s) = has x s := by
  show (if y = x then true else has x s) = has x s
  exact if_neg hne

/-- insertion never removes anything -/
theorem a_present_value_stays_present {x nf : D} {s : List D} (hx : has x s = true) :
    has x (nf :: s) = true := by
  by_cases e : nf = x
  · show (if nf = x then true else has x s) = true
    exact if_pos e
  · exact (has_cons_of_ne e).trans hx

theorem a_present_value_survives_any_prefix {x : D} {s : List D} (hx : has x s = true) :
    ∀ t : List D, has x (t ++ s) = true := by
  intro t
  induction t with
  | nil => exact hx
  | cons y ys ih =>
    show has x (y :: (ys ++ s)) = true
    exact a_present_value_stays_present ih

theorem a_value_in_the_prefix_is_present {x : D} (s : List D) :
    ∀ t : List D, has x t = true → has x (t ++ s) = true := by
  intro t
  induction t with
  | nil =>
    intro hx
    exact absurd ((has_nil x).symm.trans hx) (by decide)
  | cons y ys ih =>
    intro hx
    by_cases e : y = x
    · show (if y = x then true else has x (ys ++ s)) = true
      exact if_pos e
    · have hys : has x ys = true := (has_cons_of_ne e).symm.trans hx
      exact (has_cons_of_ne e).trans (ih hys)

/-! a single insert -/

theorem an_absent_value_is_accepted {nf : D} {s : List D} (hh : ¬has nf s = true) :
    Nullifier.insert nf s = some (nf :: s) := by
  show (if has nf s = true then none else some (nf :: s)) = some (nf :: s)
  exact if_neg hh

theorem a_fresh_nullifier_is_accepted {nf : D} {s : List D} (h : has nf s = false) :
    Nullifier.insert nf s = some (nf :: s) :=
  an_absent_value_is_accepted (fun e => absurd (h.symm.trans e) (by decide))

theorem a_present_nullifier_is_refused {nf : D} {s : List D} (hh : has nf s = true) :
    Nullifier.insert nf s = none := by
  show (if has nf s = true then none else some (nf :: s)) = none
  exact if_pos hh

theorem an_accepted_insert_prepends {nf : D} {s s' : List D}
    (hi : Nullifier.insert nf s = some s') : s' = nf :: s := by
  by_cases hh : has nf s = true
  · exact Option.noConfusion ((a_present_nullifier_is_refused hh).symm.trans hi)
  · exact (Option.some.inj ((an_absent_value_is_accepted hh).symm.trans hi)).symm

theorem an_accepted_nullifier_is_present {nf : D} {s s' : List D}
    (hi : Nullifier.insert nf s = some s') : has nf s' = true := by
  have e := an_accepted_insert_prepends hi
  subst e
  exact has_cons_self

/-- a second insertion of one value after a successful first is refused -/
theorem a_second_insert_is_refused {nf : D} {s s' : List D}
    (hi : Nullifier.insert nf s = some s') : Nullifier.insert nf s' = none :=
  a_present_nullifier_is_refused (an_accepted_nullifier_is_present hi)

theorem an_accepted_insert_keeps_the_set {x nf : D} {s s' : List D}
    (hi : Nullifier.insert nf s = some s') (hx : has x s = true) : has x s' = true := by
  have e := an_accepted_insert_prepends hi
  subst e
  exact a_present_value_stays_present hx

/-- the set only grows, by one on success -/
theorem an_accepted_insert_grows_by_one {nf : D} {s s' : List D}
    (hi : Nullifier.insert nf s = some s') : s'.length = s.length + 1 := by
  have e := an_accepted_insert_prepends hi
  subst e
  rfl

theorem a_refusal_means_present {nf : D} {s : List D} (hn : Nullifier.insert nf s = none) :
    has nf s = true := by
  by_cases hh : has nf s = true
  · exact hh
  · exact Option.noConfusion ((an_absent_value_is_accepted hh).symm.trans hn)

/-! batches -/

theorem a_batch_step {nf : D} {rest s s' : List D} (hs : insertAll (nf :: rest) s = some s') :
    has nf s = false ∧ insertAll rest (nf :: s) = some s' := by
  by_cases hh : has nf s = true
  · have hn : insertAll (nf :: rest) s = none :=
      (congrArg (fun o => Option.bind o (fun s' => insertAll rest s'))
        (a_present_nullifier_is_refused hh)).trans rfl
    exact Option.noConfusion (hn.symm.trans hs)
  · refine ⟨?_, ?_⟩
    · cases hb : has nf s
      · rfl
      · exact absurd hb hh
    · exact (congrArg (fun o => Option.bind o (fun s' => insertAll rest s'))
        (an_absent_value_is_accepted hh)).symm.trans hs

theorem a_batch_grows_by_its_length :
    ∀ (ns s s' : List D), insertAll ns s = some s' → s'.length = s.length + ns.length
  | [], s, s', hs => by
    have e : s = s' := Option.some.inj hs
    subst e
    rfl
  | nf :: rest, s, s', hs => by
    have ih := a_batch_grows_by_its_length rest (nf :: s) s' (a_batch_step hs).2
    have e1 : (nf :: s).length = s.length + 1 := rfl
    have e2 : (nf :: rest).length = rest.length + 1 := rfl
    omega

theorem a_batch_keeps_the_set (x : D) :
    ∀ (ns s s' : List D), has x s = true → insertAll ns s = some s' → has x s' = true
  | [], s, s', hx, hs => by
    have e : s = s' := Option.some.inj hs
    subst e
    exact hx
  | nf :: rest, s, s', hx, hs =>
    a_batch_keeps_the_set x rest (nf :: s) s' (a_present_value_stays_present hx)
      (a_batch_step hs).2

/-- a nullifier spent before a batch stays spent after it -/
theorem a_batch_cannot_replay_an_old_spend {nf : D} {ns s s' : List D} (hx : has nf s = true)
    (hs : insertAll ns s = some s') : Nullifier.insert nf s' = none :=
  a_present_nullifier_is_refused (a_batch_keeps_the_set nf ns s s' hx hs)

/-! the set under the key hierarchy -/

omit [DecidableEq D] in
/-- equal nullifiers under one key came from one note at one position -/
theorem equal_nullifiers_share_note_and_position (h : Compress D) {nk cm cm' t t' : D}
    (e : Key.nullifier h nk cm t = Key.nullifier h nk cm' t') : cm = cm' ∧ t = t' :=
  ⟨(h.inj _ _ _ _ (h.inj _ _ _ _ e).1).2, (h.inj _ _ _ _ e).2⟩

omit [DecidableEq D] in
theorem one_note_retires_under_one_nullifier (h : Compress D) {nk cm cm' t t' : D}
    (hc : cm = cm') (ht : t = t') : Key.nullifier h nk cm t = Key.nullifier h nk cm' t' := by
  subst hc
  subst ht
  rfl

omit [DecidableEq D] in
/-- two notes under one key never collide, whatever their positions -/
theorem distinct_notes_never_collide (h : Compress D) {nk cm cm' t t' : D} (hne : cm ≠ cm') :
    Key.nullifier h nk cm t ≠ Key.nullifier h nk cm' t' :=
  fun e => hne (equal_nullifiers_share_note_and_position h e).1

omit [DecidableEq D] in
theorem distinct_notes_at_one_position (h : Compress D) {nk cm cm' t : D} (hne : cm ≠ cm') :
    Key.nullifier h nk cm t ≠ Key.nullifier h nk cm' t :=
  Key.distinct_notes_retire_apart h hne

/-- a second spend of one note is refused once the first is in the set -/
theorem a_respend_is_refused (h : Compress D) {nk cm t : D} {s s' : List D}
    (hi : Nullifier.insert (Key.nullifier h nk cm t) s = some s') :
    Nullifier.insert (Key.nullifier h nk cm t) s' = none :=
  a_second_insert_is_refused hi

/-- the respend is refused even with other spends accepted in between -/
theorem a_respend_after_a_batch_is_refused (h : Compress D) {nk cm t : D} {s s' s'' ns : List D}
    (hi : Nullifier.insert (Key.nullifier h nk cm t) s = some s')
    (hb : insertAll ns s' = some s'') :
    Nullifier.insert (Key.nullifier h nk cm t) s'' = none :=
  a_batch_cannot_replay_an_old_spend (an_accepted_nullifier_is_present hi) hb

/-- an honest spender of two distinct notes is never refused by their own earlier spend -/
theorem an_honest_second_spend_is_accepted (h : Compress D) {nk cm cm' t t' : D}
    {s s' : List D} (hne : cm ≠ cm')
    (h1 : Nullifier.insert (Key.nullifier h nk cm t) s = some s')
    (hf : has (Key.nullifier h nk cm' t') s = false) :
    Nullifier.insert (Key.nullifier h nk cm' t') s' = some (Key.nullifier h nk cm' t' :: s') := by
  have e := an_accepted_insert_prepends h1
  subst e
  have hd : Key.nullifier h nk cm t ≠ Key.nullifier h nk cm' t' :=
    distinct_notes_never_collide h hne
  have hf' : has (Key.nullifier h nk cm' t') (Key.nullifier h nk cm t :: s) = false :=
    (has_cons_of_ne hd).trans hf
  exact a_fresh_nullifier_is_accepted hf'

theorem both_honest_spends_land (h : Compress D) {nk cm cm' t t' : D} {s : List D}
    (hne : cm ≠ cm') (hf0 : has (Key.nullifier h nk cm t) s = false)
    (hf1 : has (Key.nullifier h nk cm' t') s = false) :
    insertAll [Key.nullifier h nk cm t, Key.nullifier h nk cm' t'] s =
      some (Key.nullifier h nk cm' t' :: Key.nullifier h nk cm t :: s) := by
  have e0 := a_fresh_nullifier_is_accepted hf0
  have e1 := an_honest_second_spend_is_accepted h hne e0 hf1
  have step0 : insertAll [Key.nullifier h nk cm t, Key.nullifier h nk cm' t'] s =
      insertAll [Key.nullifier h nk cm' t'] (Key.nullifier h nk cm t :: s) :=
    (congrArg (fun o => Option.bind o (fun s' => insertAll [Key.nullifier h nk cm' t'] s'))
      e0).trans rfl
  have step1 : insertAll [Key.nullifier h nk cm' t'] (Key.nullifier h nk cm t :: s) =
      some (Key.nullifier h nk cm' t' :: Key.nullifier h nk cm t :: s) :=
    (congrArg (fun o => Option.bind o (fun s' => insertAll [] s')) e1).trans rfl
  exact step0.trans step1

/-- a nullifier under another key never blocks the owner's -/
theorem a_foreign_key_does_not_block (h : Compress D) {nk nk' cm t : D} (hne : nk ≠ nk') :
    has (Key.nullifier h nk cm t) [Key.nullifier h nk' cm t] = false := by
  have hd : Key.nullifier h nk' cm t ≠ Key.nullifier h nk cm t :=
    Key.the_nullifier_needs_the_key h (Ne.symm hne)
  exact (has_cons_of_ne hd).trans rfl

/-! a concrete set over Nat -/

theorem five_joins_the_set : Nullifier.insert (5 : Nat) [1, 2, 3] = some [5, 1, 2, 3] := by
  decide

theorem two_is_refused : Nullifier.insert (2 : Nat) [1, 2, 3] = none := by decide

theorem the_set_refuses_exactly_its_members :
    ∀ n < 8, (Nullifier.insert n [1, 2, 3]).isNone = has n [1, 2, 3] := by decide

theorem a_sequence_of_fresh_inserts :
    insertAll ([4, 5, 6] : List Nat) [1, 2, 3] = some [6, 5, 4, 1, 2, 3] := by decide

theorem a_repeat_inside_a_batch_is_refused :
    insertAll ([4, 5, 4] : List Nat) [1, 2, 3] = none := by decide

theorem an_old_value_inside_a_batch_is_refused :
    insertAll ([4, 2] : List Nat) [1, 2, 3] = none := by decide

theorem the_empty_batch_changes_nothing :
    insertAll ([] : List Nat) [1, 2, 3] = some [1, 2, 3] := by decide

theorem after_the_batch_every_value_is_refused :
    ∀ n ∈ ([6, 5, 4, 1, 2, 3] : List Nat), Nullifier.insert n [6, 5, 4, 1, 2, 3] = none := by
  decide

end Shield.Nullifier
