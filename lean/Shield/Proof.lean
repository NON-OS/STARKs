-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Gas

/-!
What a proof weighs, by category, and which category decides.

Three things ride a proof: the FRI layer openings, the trace and auxiliary row
openings, and the out of domain frame. A size table that counts the second
without the first is counting the smaller half, and the arithmetic below is
here so that cannot happen again silently.

The model is calibrated against the emitted settlement artifact: 32 queries,
fold two, domain 2^26, 726,660 bytes of FRI openings measured. It charges one
path per layer where the deployed prover charges one per opening, so every
figure it produces is optimistic by about a factor of two.
-/

namespace Shield.Proof

/-- An extension element. -/
def elemBytes : Nat := 16

/-- A keccak digest on a path, as codec v1.1 carried it. Codec v1.2 keeps
24 bytes of each digest (`merkle::DIGEST_BYTES`); the bounds below are stated
at 32 and only tighten at 24. -/
def nodeBytes : Nat := 32

/-- Layers a fold of `2 ^ foldBits` takes from `logD` down to `finalLog`. -/
def layers (logD foldBits finalLog : Nat) : Nat := (logD - finalLog) / foldBits

/-- Sum of tree depths across the layers, which is where the bytes are.
Depth at layer `i` is `logD - i * foldBits - foldBits`. -/
def pathLevels (logD foldBits finalLog : Nat) : Nat :=
  let n := layers logD foldBits finalLog
  n * (logD - foldBits) - foldBits * (n * (n - 1) / 2)

/-- FRI openings for one query. -/
def friPerQuery (logD foldBits finalLog : Nat) : Nat :=
  layers logD foldBits finalLog * (2 ^ foldBits * elemBytes)
    + pathLevels logD foldBits finalLog * nodeBytes

/-- One FRI layer, charged either way: with the coset in one leaf a query pays
one path, with a path per opening it pays `2 ^ foldBits`. -/
def layerCost (foldBits depth pathsPerLayer : Nat) : Nat :=
  2 ^ foldBits * elemBytes + pathsPerLayer * depth * nodeBytes

/-- At fold two the two layouts differ by about a factor of two, which is the
gap between this model and the emitted artifact. -/
theorem the_gap_at_fold_two :
    layerCost 1 25 2 < 2 * layerCost 1 25 1 := by decide

/-- At fold eight it is a factor of seven, because the paths skipped are the
fold factor. -/
theorem the_gap_grows_with_the_fold :
    6 * layerCost 3 24 1 < layerCost 3 24 8 := by decide

/-- So without the coset in one leaf, raising the fold factor makes the proof
larger: one fold eight layer costs more than the three fold two layers it
replaces. Coset per leaf is not one of the size levers, it is the precondition
that makes the others point the right way. -/
theorem a_bigger_fold_inverts_without_it :
    3 * layerCost 1 25 2 < layerCost 3 24 8 := by decide

/-- Two path sets: the region trace and the auxiliary tree that carries the
permutation columns and the composition together. -/
def rowsPerQuery (width logD : Nat) : Nat := 2 * (width * 8 + logD * nodeBytes)

def proofBytes (logD foldBits finalLog queries width : Nat) : Nat :=
  queries * (friPerQuery logD foldBits finalLog + rowsPerQuery width logD)
    + 2 ^ finalLog * elemBytes

/-- The wrap at the parameters the one transaction spec names. -/
def specLogD : Nat := 27
def specQueries : Nat := 8
def specWidth : Nat := 50

/-- The row openings alone are about what the spec budgeted for the whole
proof, which is the sign that the FRI term was not counted. -/
theorem the_row_openings_are_the_budget :
    20000 < specQueries * rowsPerQuery specWidth specLogD
    ∧ specQueries * rowsPerQuery specWidth specLogD < 21000 := by decide

/-- The FRI openings are larger than the row openings. -/
theorem fri_is_the_larger_term :
    specQueries * rowsPerQuery specWidth specLogD
      < specQueries * friPerQuery specLogD 3 3 := by decide

/-- And the whole proof is over fifty thousand bytes, which is over two
million gas of calldata, against a budget of one. -/
theorem the_spec_does_not_fit :
    Gas.oneMillion < Gas.dense (proofBytes specLogD 3 3 specQueries specWidth) 0 := by
  decide

/-- Raising the fold factor does not rescue it: the coset values grow as fast
as the paths shrink. -/
theorem a_bigger_fold_does_not_rescue_it :
    Gas.oneMillion < Gas.dense (proofBytes specLogD 4 3 specQueries specWidth) 0 := by
  decide

/-- Nor does halving the queries, which would also spend the provable floor. -/
theorem fewer_queries_do_not_rescue_it :
    Gas.oneMillion < Gas.dense (proofBytes specLogD 3 3 4 specWidth) 0 := by decide

/-- A batch shares the proof, so the per payment cost falls even though the
proof does not. At the spec's own parameters two payments do not fit and
three do, which is a different sentence from the one the spec makes. -/
def perPaymentAt (bytes n : Nat) : Nat :=
  Gas.dense bytes 0 / n + 10 * Gas.tokens 0 Gas.perIntentBytes

theorem three_payments_fit_at_the_spec :
    Gas.oneMillion < perPaymentAt (proofBytes specLogD 3 3 specQueries specWidth) 2
    ∧ perPaymentAt (proofBytes specLogD 3 3 specQueries specWidth) 3 < Gas.oneMillion := by
  decide

/-- The smallest proof the parameter space allows, searched rather than
assumed: rate 1/65536, six queries, grind 32, fold 16, with the top Merkle
levels shared across queries. -/
def floorBytes : Nat := 39776

/-- There, two payments fit. The difference between two and three is the
whole distance between the spec's parameters and the reachable ones. -/
theorem two_payments_fit_at_the_floor :
    perPaymentAt floorBytes 2 < Gas.oneMillion := by decide

/-- And one never does, at either. -/
theorem one_payment_never_fits :
    Gas.oneMillion < perPaymentAt floorBytes 1
    ∧ Gas.oneMillion < perPaymentAt (proofBytes specLogD 3 3 specQueries specWidth) 1 := by
  decide

end Shield.Proof
