-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Hash

/-!
The nested note commitment and the solvency property it exists for.

`cm = compress(public, compress(spend_pk, blinding))` with
`public = [value_lo, value_hi, asset, NOTE_DOMAIN]`. No quad holds a public
element and a secret one, so a pool builds the public half from the amount it
escrowed and takes the owner half as a digest it cannot open.

`the_leaf_binds_the_escrowed_value` is the reason the layout is cut this way.
Without it a payer escrows one wei, supplies a commitment to any amount, and
spends it under a proof every constraint accepts.
-/

namespace Shield.Note

open Shield.Hash

variable {D : Type}

/-- The half only the depositor can build. -/
def owner (h : Compress D) (spendPk blinding : D) : D := h.f spendPk blinding

/-- The commitment as a pool computes it: the public quad it built from the
amount in front of it, and the one digest it was handed. -/
def commit (h : Compress D) (q : Quad D) (valueLo valueHi asset noteDomain : Nat)
    (o : D) : D :=
  h.f (q.pack valueLo valueHi asset noteDomain) o

/-- The factorisation, by definition: the pool needs the amount, the asset and
one digest. Not the spend key, not the blinding. -/
theorem the_pool_needs_only_the_owner_digest (h : Compress D) (q : Quad D)
    (vl vh a d : Nat) (spendPk blinding : D) :
    commit h q vl vh a d (owner h spendPk blinding)
      = h.f (q.pack vl vh a d) (h.f spendPk blinding) := rfl

/-- Solvency. A leaf commits to one value, one asset, one domain tag and one
owner half, so two deposits landing on one leaf escrowed one amount. -/
theorem the_leaf_binds_the_escrowed_value (h : Compress D) (q : Quad D)
    {vl vh a d vl' vh' a' d' : Nat} {o o' : D}
    (heq : commit h q vl vh a d o = commit h q vl' vh' a' d' o') :
    vl = vl' ∧ vh = vh' ∧ a = a' ∧ d = d' ∧ o = o' := by
  obtain ⟨hp, ho⟩ := h.inj _ _ _ _ heq
  obtain ⟨e1, e2, e3, e4⟩ := q.inj _ _ _ _ _ _ _ _ hp
  exact ⟨e1, e2, e3, e4, ho⟩

/-- A payer supplying only the owner half cannot move the value, because the
pool put the value in the other operand. -/
theorem a_payer_cannot_move_the_value (h : Compress D) (q : Quad D)
    (vl vh a d : Nat) {o o' : D} (hne : o ≠ o') :
    commit h q vl vh a d o ≠ commit h q vl vh a d o' :=
  fun heq => hne (h.inj _ _ _ _ heq).2

/-- A different escrowed amount is a different leaf, so the tree cannot hold
one commitment under two values. -/
theorem a_different_amount_is_a_different_leaf (h : Compress D) (q : Quad D)
    {vl vl' vh a d : Nat} (o : D) (hne : vl ≠ vl') :
    commit h q vl vh a d o ≠ commit h q vl' vh a d o :=
  fun heq => hne (the_leaf_binds_the_escrowed_value h q heq).1

/-- The high half of the value is bound as well, so the split at thirty two
bits cannot be used to carry a second amount. -/
theorem the_high_half_is_bound (h : Compress D) (q : Quad D)
    {vl vh vh' a d : Nat} (o : D) (hne : vh ≠ vh') :
    commit h q vl vh a d o ≠ commit h q vl vh' a d o :=
  fun heq => hne (the_leaf_binds_the_escrowed_value h q heq).2.1

/-- The asset is bound, so value cannot cross between assets by relabelling. -/
theorem the_asset_is_bound (h : Compress D) (q : Quad D)
    {vl vh a a' d : Nat} (o : D) (hne : a ≠ a') :
    commit h q vl vh a d o ≠ commit h q vl vh a' d o :=
  fun heq => hne (the_leaf_binds_the_escrowed_value h q heq).2.2.1

/-- The domain tag is in the preimage, so a note commitment never equals a
bare internal node built from the same compression. -/
theorem the_domain_tag_is_bound (h : Compress D) (q : Quad D)
    {vl vh a d d' : Nat} (o : D) (hne : d ≠ d') :
    commit h q vl vh a d o ≠ commit h q vl vh a d' o :=
  fun heq => hne (the_leaf_binds_the_escrowed_value h q heq).2.2.2.1

/-- The owner half binds both operands, so a note cannot be re-owned by
keeping its blinding nor re-blinded by keeping its key. -/
theorem the_owner_binds_key_and_blinding (h : Compress D)
    {spendPk blinding spendPk' blinding' : D}
    (heq : owner h spendPk blinding = owner h spendPk' blinding') :
    spendPk = spendPk' ∧ blinding = blinding' :=
  h.inj _ _ _ _ heq

end Shield.Note
