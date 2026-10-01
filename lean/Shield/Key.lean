-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Hash

/-!
The key hierarchy and the nullifier.

    spend_pk = compress(sk, SPND)
    nk       = compress(sk, NULL)
    nf       = compress(compress(nk, cm), index)

Two facts carry the double spend argument. A note retires under one nullifier
per position, and moving the position moves the nullifier. The circuit binds
the position to the membership it proved, so the second fact is what turns a
foreign index into a rejection instead of a second spend.
-/

namespace Shield.Key

open Shield.Hash

variable {D : Type}

def spendPk (h : Compress D) (sk spendTag : D) : D := h.f sk spendTag

def nullifierKey (h : Compress D) (sk nullTag : D) : D := h.f sk nullTag

/-- The leaf position sits in the preimage. -/
def nullifier (h : Compress D) (nk cm indexTag : D) : D := h.f (h.f nk cm) indexTag

/-- Distinct tags give distinct keys. A free nullifier key would let anyone
holding a commitment retire a note they do not own. -/
theorem the_two_keys_differ (h : Compress D) {sk spendTag nullTag : D}
    (hne : spendTag ≠ nullTag) :
    spendPk h sk spendTag ≠ nullifierKey h sk nullTag :=
  fun heq => hne (h.inj _ _ _ _ heq).2

/-- A note names one secret. -/
theorem the_key_names_one_secret (h : Compress D) {sk sk' tag : D} (hne : sk ≠ sk') :
    spendPk h sk tag ≠ spendPk h sk' tag :=
  fun heq => hne (h.inj _ _ _ _ heq).1

/-- Equal nullifiers at one position came from one key and one commitment. -/
theorem a_nullifier_names_its_note (h : Compress D) {nk cm nk' cm' t : D}
    (heq : nullifier h nk cm t = nullifier h nk' cm' t) : nk = nk' ∧ cm = cm' :=
  h.inj _ _ _ _ (h.inj _ _ _ _ heq).1

/-- Retiring a note under a position the pool did not authenticate yields a
different nullifier. Without the position in the preimage, two deposits of one
note share a nullifier and spending one locks the other. -/
theorem the_position_moves_the_nullifier (h : Compress D) {nk cm t t' : D}
    (hne : t ≠ t') : nullifier h nk cm t ≠ nullifier h nk cm t' :=
  fun heq => hne (h.inj _ _ _ _ heq).2

/-- Two notes at one position retire apart. -/
theorem distinct_notes_retire_apart (h : Compress D) {nk cm cm' t : D}
    (hne : cm ≠ cm') : nullifier h nk cm t ≠ nullifier h nk cm' t :=
  fun heq => hne (a_nullifier_names_its_note h heq).2

/-- A nullifier is a function of the nullifier key, so a holder of the
commitment alone cannot compute it. -/
theorem the_nullifier_needs_the_key (h : Compress D) {nk nk' cm t : D}
    (hne : nk ≠ nk') : nullifier h nk cm t ≠ nullifier h nk' cm t :=
  fun heq => hne (a_nullifier_names_its_note h heq).1

end Shield.Key
