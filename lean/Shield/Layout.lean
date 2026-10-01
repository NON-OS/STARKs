-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Where every byte of a settlement proof is, as arithmetic over its parameters.

The Rust module `proof_wire::layout` derives every base, stride and depth from
the parameter set, and the Solidity verifier reads the proof at those offsets.
This is the same derivation, stated once more in a language that checks it.
Two offset errors reached a hand-written table on 2026-09-22, and both were
coherent with every formula downstream of them; each is restated here as a
theorem that it does not close.

Everything is `Nat`, core only.
-/

namespace Shield.Layout

/-- The parameters the layout depends on. -/
structure Params where
  queries : Nat
  extraBlowup : Nat
  foldLog : Nat
  stopLog : Nat
  digest : Nat
  width : Nat
  periodic : Nat
  logTrace : Nat
  degreeLog : Nat
  window : Nat
  /-- The wire format. 5 reads the DEEP value from FRI's own layer-zero opening at FRI's
  positions and carries no DEEP root; 4 opened it in FRI layer zero at positions of its own;
  3 had a tree of its own. -/
  format : Nat := 5
  deriving DecidableEq

/-- The shipped settlement point. The constraint degree is 8, so `degreeLog` is 3. -/
def shipped : Params :=
  { queries := 12, extraBlowup := 7, foldLog := 2, stopLog := 8, digest := 24,
    width := 41, periodic := 119, logTrace := 18, degreeLog := 3, window := 2 }

/-- The composition's degree bound, as a log: the trace length times the degree. -/
def logBound (p : Params) : Nat := p.logTrace + p.degreeLog

/-- The evaluation domain: the bound, doubled, then blown up. -/
def logDomain (p : Params) : Nat := logBound p + 1 + p.extraBlowup

/-- FRI layers: the halvings the stop leaves, taken `foldLog` at a time, at least one. -/
def layers (p : Params) : Nat := max 1 ((logBound p - p.stopLog) / p.foldLog)

/-- What the layers leave for the final polynomial, as a log of its coefficient count. -/
def finalLog (p : Params) : Nat := logBound p - layers p * p.foldLog

/-- Every tree that is not a FRI layer commits one leaf per point: depth `LN`. -/
def treeDepth (p : Params) : Nat := logDomain p

/-- A radix `2^f` layer puts `2^f` values under a leaf, so layer `m` is `LN - f(m+1)` deep. -/
def friDepth (p : Params) (m : Nat) : Nat := logDomain p - p.foldLog * (m + 1)

/-- A path is a four-byte count and `depth` digests. -/
def pathBytes (p : Params) (depth : Nat) : Nat := 4 + p.digest * depth

/-- One FRI layer inside a query: the `2^f` values at sixteen bytes each, and its path. -/
def layerBytes (p : Params) (m : Nat) : Nat := 16 * 2 ^ p.foldLog + pathBytes p (friDepth p m)

/-- The layers of one query, summed. -/
def layersBytes (p : Params) : Nat → Nat
  | 0 => 0
  | n + 1 => layersBytes p n + layerBytes p n

def ood (p : Params) : Nat := p.width * p.window

/-- The roots the head carries after the region width: trace, composition, and before format 5
the DEEP root, which is FRI's first and is not repeated at 5. -/
def headRoots (p : Params) : Nat := if p.format ≤ 4 then 3 else 2

/-- The head: permutation root, region width, the roots, the frame, the FRI roots and the
final polynomial, each list behind a four-byte count. -/
def head (p : Params) : Nat :=
  p.digest + 4 + headRoots p * p.digest + 4 + 16 * ood p + 4 + p.digest * layers p + 4 +
    16 * 2 ^ finalLog p

def friStride (p : Params) : Nat := 4 + layersBytes p (layers p)

/-- The DEEP opening inside a consistency query. Format 5 carries none: the check runs at FRI's
positions and reads FRI's own layer-zero opening. Format 4 opened it in FRI layer zero, where a
leaf holds `2^f` values and the tree is `f` levels shallower than the domain; format 3 opened
one value under a tree of its own, which FRI never tested. -/
def deepOpening (p : Params) : Nat :=
  if p.format ≤ 3 then 16 + pathBytes p (treeDepth p)
  else if p.format ≤ 4 then 16 * 2 ^ p.foldLog + pathBytes p (logDomain p - p.foldLog)
  else 0

/-- A consistency opening: the DEEP opening, the trace row behind its count, the trace path,
the composition value and path. -/
def consStride (p : Params) : Nat :=
  deepOpening p + 4 + 8 * p.width + pathBytes p (treeDepth p) + 16 + pathBytes p (treeDepth p)

def sidecarStride (p : Params) : Nat := 8 * p.periodic + pathBytes p (treeDepth p)

def permStride (p : Params) : Nat := pathBytes p (treeDepth p)

/-! Section bases, each defined as the end of the one before. -/

def friBase (p : Params) : Nat := head p
def friEnd (p : Params) : Nat := friBase p + 4 + p.queries * friStride p
/-- The eight-byte grind nonce sits between the FRI queries and the consistency section. -/
def consBase (p : Params) : Nat := friEnd p + 8
def consEnd (p : Params) : Nat := consBase p + 4 + p.queries * consStride p
def sidecarBase (p : Params) : Nat := consEnd p
def sidecarEnd (p : Params) : Nat := sidecarBase p + 4 + 16 * p.periodic + p.queries * sidecarStride p
def permBase (p : Params) : Nat := sidecarEnd p
def total (p : Params) : Nat := permBase p + p.queries * permStride p

/-! ## The shipped proof -/

theorem shipped_domain : logDomain shipped = 29 := by decide
theorem shipped_layers : layers shipped = 6 := by decide
theorem shipped_final : 2 ^ finalLog shipped = 512 := by decide
theorem shipped_tree_depth : treeDepth shipped = 29 := by decide

theorem shipped_fri_depths :
    [friDepth shipped 0, friDepth shipped 1, friDepth shipped 2,
     friDepth shipped 3, friDepth shipped 4, friDepth shipped 5] = [27, 25, 23, 21, 19, 17] := by
  decide

theorem shipped_strides :
    friStride shipped = 3580 ∧ consStride shipped = 1748 ∧
    sidecarStride shipped = 1652 ∧ permStride shipped = 700 := by decide

theorem shipped_bases :
    friBase shipped = 9736 ∧ consBase shipped = 52708 ∧
    sidecarBase shipped = 73688 ∧ permBase shipped = 95420 := by decide

/-- The shipped point at format 5 ends at byte 103,820. -/
theorem shipped_closes : total shipped = 103820 := by decide

/-- The format 4 artifact of 2026-09-22, the one the layout was first held to byte for byte. -/
def shippedFour : Params := { shipped with format := 4 }

theorem shipped_four_strides :
    consStride shippedFour = 2464 ∧ friBase shippedFour = 9760 ∧ consBase shippedFour = 52732 ∧
    sidecarBase shippedFour = 82304 ∧ permBase shippedFour = 104036 := by decide

/-- The layout ended on that artifact's last byte: 112,436. -/
theorem shipped_four_closes : total shippedFour = 112436 := by decide

/-- What format 5 takes off the wire at the shipped point: the DEEP root, and one layer-zero
opening a query (four values, a count, a path of 27 digests). -/
theorem format_five_saves :
    total shippedFour = total shipped + 12 * (16 * 4 + 4 + 24 * 27) + 24 := by decide

/-! ## The two errors, and the one that caused them -/

/-- The FRI depth issued as a correction on the day, `LN - 3 - 2m`. It does not close. -/
def wrongFriStride (p : Params) : Nat :=
  4 + (List.range (layers p)).foldl
    (fun acc m => acc + 16 * 2 ^ p.foldLog + 4 + p.digest * (logDomain p - 3 - 2 * m)) 0

theorem wrong_fri_depth_does_not_close :
    wrongFriStride shipped ≠ friStride shipped := by decide

/-- The consistency stride with a phantom length prefix: 56 where it is 48. -/
theorem wrong_cons_stride_does_not_close :
    56 + 8 * shipped.width + 72 * treeDepth shipped ≠ consStride shipped := by decide

/-- The domain printed one too large by a tool that derived it as depth plus one. The layout
derives it, so that value is not reachable from the parameters. -/
theorem the_domain_is_not_thirty : logDomain shipped ≠ 30 := by decide

/-! ## Facts that hold for every parameter set -/

/-- Every non-FRI tree is exactly as deep as the domain. Not `LN - 1`. -/
theorem tree_depth_is_the_domain (p : Params) : treeDepth p = logDomain p := rfl

/-- Adjacent sections abut by construction: no parameter set can leave a gap or an overlap. -/
theorem chain_closes (p : Params) :
    consBase p = friEnd p + 8 ∧ sidecarBase p = consEnd p ∧ permBase p = sidecarEnd p :=
  ⟨rfl, rfl, rfl⟩

/-- The consistency stride of format 3, in closed form. -/
theorem cons_stride_closed (p : Params) (h : p.format ≤ 3) :
    consStride p = 48 + 8 * p.width + 3 * (p.digest * treeDepth p) := by
  simp only [consStride, deepOpening, if_pos h, pathBytes]
  omega

/-- The consistency stride of format 4, in closed form. -/
theorem cons_stride_closed_four (p : Params) (h3 : ¬ p.format ≤ 3) (h4 : p.format ≤ 4) :
    consStride p = 16 * 2 ^ p.foldLog + 32 + 8 * p.width +
      p.digest * (logDomain p - p.foldLog) + 2 * (p.digest * treeDepth p) := by
  simp only [consStride, deepOpening, if_neg h3, if_pos h4, pathBytes]
  omega

/-- The consistency stride of format 5, in closed form: the trace row and path, the
composition value and path, nothing of the DEEP codeword. -/
theorem cons_stride_closed_five (p : Params) (h : ¬ p.format ≤ 4) :
    consStride p = 28 + 8 * p.width + 2 * (p.digest * treeDepth p) := by
  have h3 : ¬ p.format ≤ 3 := fun h' => h (Nat.le_succ_of_le h')
  simp only [consStride, deepOpening, if_neg h3, if_neg h, pathBytes]
  omega

/-- The two formats give one stride exactly when the extra values of a leaf cost what the
missing levels saved: `16 (2^f - 1) = d f`. At 24-byte digests and radix four both sides are
48, so format 4 moved no offset of the shipped proof. -/
theorem format_four_moves_no_shipped_offset :
    consStride shippedFour = consStride { shipped with format := 3 } ∧
    total shippedFour = total { shipped with format := 3 } ∧
    16 * (2 ^ shipped.foldLog - 1) = shipped.digest * shipped.foldLog := by decide

theorem shipped_is_format_five : shipped.format = 5 := rfl

theorem shipped_four_is_format_four : shippedFour.format = 4 := rfl

/-- Each FRI layer is `foldLog` levels shallower than the one before it. -/
theorem fri_depth_step (p : Params) (m : Nat) (h : p.foldLog * (m + 2) ≤ logDomain p) :
    friDepth p m = friDepth p (m + 1) + p.foldLog := by
  unfold friDepth
  have e : p.foldLog * (m + 1 + 1) = p.foldLog * (m + 1) + p.foldLog := by
    rw [Nat.mul_add, Nat.mul_one]
  have h' : p.foldLog * (m + 1 + 1) ≤ logDomain p := h
  rw [e] at h' ⊢
  omega

end Shield.Layout
