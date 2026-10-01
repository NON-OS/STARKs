-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Read.Exact
import Shield.Layout
import Shield.Manifest

/-!
The reader and the layout agree, for every parameter set.

`Shield.Layout` derives where every section of a proof starts from the
parameters alone; `Shield.Read` reads a proof and knows its size only from
the counts it found. `Fits p r` says the counts are the ones `p` asks for: so
many queries, a path of the domain's depth under every non-FRI tree, a layer
of `friDepth p m` at FRI position `m`. Under it the two sizes are one number,
so a proof the reader accepts at a parameter set is exactly `total p` bytes,
and the Solidity verifier's offsets, which are generated from the layout,
land on the fields this reader reads.

The reader reads four values a FRI layer and a 24-byte digest, so the
agreement is stated for parameter sets with `2 ^ foldLog = 4` and
`digest = 24`, which is every set the codec serves.
-/

namespace Shield.Read

open Shield.Layout

/-- a query's FRI layers, from position `m` -/
def LayersFit (p : Params) : Nat → List Layer → Prop
  | _, [] => True
  | m, l :: ls => l.v.length = 2 ^ p.foldLog ∧ l.path.length = friDepth p m ∧ LayersFit p (m + 1) ls

/-- how many other values of its leaf a DEEP opening carries, and how deep its path is -/
def deepOthersAt (p : Params) : Nat := if p.format ≤ 3 then 0 else 2 ^ p.foldLog - 1
def deepDepthAt (p : Params) : Nat := if p.format ≤ 3 then treeDepth p else logDomain p - p.foldLog

def QueryFits (p : Params) (q : Query) : Prop :=
  q.deepOthers.length = deepOthersAt p ∧ q.deepPath.length = deepDepthAt p ∧
    q.trace.length = p.width ∧ q.tracePath.length = treeDepth p ∧ q.compPath.length = treeDepth p

/-- the counts `p` asks for -/
structure Fits (p : Params) (r : Rounds) : Prop where
  digest : p.digest = digestBytes
  ood : r.ext.ood.length = ood p
  roots : r.ext.fri.roots.length = layers p
  final : r.ext.fri.final.length = 2 ^ finalLog p
  friQueries : r.ext.fri.queries.length = p.queries
  friLayers : ∀ ls ∈ r.ext.fri.queries, ls.length = layers p ∧ LayersFit p 0 ls
  queries : r.ext.queries.length = p.queries
  queryShape : ∀ q ∈ r.ext.queries, QueryFits p q
  periodic : r.periodicZ.length = p.periodic
  openings : r.openings.length = p.queries
  openingShape : ∀ o ∈ r.openings, o.row.length = p.periodic ∧ o.path.length = treeDepth p
  permPaths : r.permPaths.length = p.queries
  permShape : ∀ pp ∈ r.permPaths, pp.length = treeDepth p

/-! ## Section by section -/

theorem pathW_at (p : Params) (hd : p.digest = digestBytes) (l : List ByteArray) (d : Nat)
    (h : l.length = d) : pathW l = pathBytes p d := by
  simp only [pathW, pathBytes, hd, h]

theorem layers_sum (p : Params) (hd : p.digest = digestBytes) :
    ∀ (ls : List Layer) (m : Nat), LayersFit p m ls →
      sumW layerW ls = Manifest.sumFrom p m ls.length
  | [], _, _ => rfl
  | l :: ls, m, ⟨hv, hp, hr⟩ => by
    show layerW l + sumW layerW ls = layerBytes p m + Manifest.sumFrom p (m + 1) ls.length
    rw [layers_sum p hd ls (m + 1) hr]
    simp only [layerW, layerBytes, hv, pathW_at p hd l.path (friDepth p m) hp]

theorem friQuery_is_the_stride (p : Params) (hd : p.digest = digestBytes) (ls : List Layer)
    (hl : ls.length = layers p ∧ LayersFit p 0 ls) : friQueryW ls = friStride p := by
  unfold friQueryW friStride
  rw [layers_sum p hd ls 0 hl.2, hl.1, Manifest.layersBytes_is_sumFrom]

theorem query_is_the_stride (p : Params) (hd : p.digest = digestBytes) (hfmt : p.format ≤ 4)
    (q : Query) (h : QueryFits p q) : queryW q = consStride p := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hp : 0 < 2 ^ p.foldLog := Nat.pos_pow_of_pos _ (by decide)
  unfold queryW consStride deepOpening
  unfold deepOthersAt at h0
  unfold deepDepthAt at h1
  rw [pathW_at p hd _ _ h3, pathW_at p hd _ _ h4, h2]
  by_cases hf : p.format ≤ 3
  · rw [if_pos hf] at h0 h1
    rw [if_pos hf, h0, pathW_at p hd _ _ h1]
    omega
  · rw [if_neg hf] at h0 h1
    rw [if_neg hf, if_pos hfmt, h0, pathW_at p hd _ _ h1]
    omega

theorem opening_is_the_stride (p : Params) (hd : p.digest = digestBytes) (o : Opening)
    (h : o.row.length = p.periodic ∧ o.path.length = treeDepth p) :
    openingW o = sidecarStride p := by
  unfold openingW sidecarStride
  rw [h.1, pathW_at p hd _ _ h.2]

/-! ## The whole file -/

/-- a proof with the counts `p` asks for is exactly as long as the layout says. This reader
reads formats 3 and 4, whose queries carry a DEEP opening and whose head carries a DEEP root;
format 5 carries neither and is read by the Rust codec. -/
theorem size_is_the_layout (p : Params) (h4 : p.format ≤ 4) (r : Rounds) (f : Fits p r) :
    roundsW r = total p := by
  have hd := f.digest
  have hF : sumW friQueryW r.ext.fri.queries = friStride p * p.queries := by
    rw [sumW_uniform friQueryW (friStride p) _
      (fun ls hls => friQuery_is_the_stride p hd ls (f.friLayers ls hls)), f.friQueries]
  have hQ : sumW queryW r.ext.queries = consStride p * p.queries := by
    rw [sumW_uniform queryW (consStride p) _
      (fun q hq => query_is_the_stride p hd h4 q (f.queryShape q hq)), f.queries]
  have hO : sumW openingW r.openings = sidecarStride p * p.queries := by
    rw [sumW_uniform openingW (sidecarStride p) _
      (fun o ho => opening_is_the_stride p hd o (f.openingShape o ho)), f.openings]
  have hP : sumW pathW r.permPaths = permStride p * p.queries := by
    rw [sumW_uniform pathW (permStride p) _
      (fun pp hpp => pathW_at p hd pp (treeDepth p) (f.permShape pp hpp)), f.permPaths]
  unfold roundsW extW friW
  rw [hF, hQ, hO, hP, f.ood, f.roots, f.final, f.periodic]
  simp only [total, permBase, sidecarEnd, sidecarBase, consEnd, consBase, friEnd, friBase, head,
    headRoots, if_pos h4, hd]
  rw [Nat.mul_comm (friStride p), Nat.mul_comm (consStride p), Nat.mul_comm (sidecarStride p),
    Nat.mul_comm (permStride p)]
  omega

/-- the shipped point's format 4 artifact: any one the reader accepts with its counts is 112,436
bytes -/
theorem shipped_size (r : Rounds) (f : Fits shippedFour r) : roundsW r = 112436 :=
  (size_is_the_layout shippedFour (by decide) r f).trans shipped_four_closes

/-- the shipped point as format 3 wrote it, before the DEEP value moved into layer zero -/
def shippedThree : Params := { shipped with format := 3 }

/-- so a legacy file that reads with the format 3 counts is 112,436 bytes long -/
theorem an_accepted_shipped_file_is_112436_bytes (b : ByteArray) (r : Rounds)
    (h : readLegacy b = some r) (f : Fits shippedThree r) : b.size = 112436 := by
  rw [← readLegacy_size b r h, size_is_the_layout shippedThree (by decide) r f]
  decide

/-- and a format 4 file that reads with the shipped counts is its header and 112,436 bytes -/
theorem an_accepted_format_four_file_is_112476_bytes (b : ByteArray) (e : List UInt8) (r : Rounds)
    (h : readFour b e = some r) (f : Fits shippedFour r) : b.size = 112476 := by
  rw [← readFour_size b e r h, shipped_size r f]
  decide

/-! ## The check, as the executable runs it -/

def layersFitB (p : Params) : Nat → List Layer → Bool
  | _, [] => true
  | m, l :: ls =>
    l.v.length == 2 ^ p.foldLog && l.path.length == friDepth p m && layersFitB p (m + 1) ls

def queryFitsB (p : Params) (q : Query) : Bool :=
  q.deepOthers.length == deepOthersAt p && q.deepPath.length == deepDepthAt p &&
    q.trace.length == p.width && q.tracePath.length == treeDepth p &&
    q.compPath.length == treeDepth p

def fitsB (p : Params) (r : Rounds) : Bool :=
  p.digest == digestBytes && r.ext.ood.length == ood p &&
    r.ext.fri.roots.length == layers p && r.ext.fri.final.length == 2 ^ finalLog p &&
    r.ext.fri.queries.length == p.queries &&
    r.ext.fri.queries.all (fun ls => ls.length == layers p && layersFitB p 0 ls) &&
    r.ext.queries.length == p.queries && r.ext.queries.all (queryFitsB p) &&
    r.periodicZ.length == p.periodic && r.openings.length == p.queries &&
    r.openings.all (fun o => o.row.length == p.periodic && o.path.length == treeDepth p) &&
    r.permPaths.length == p.queries && r.permPaths.all (fun pp => pp.length == treeDepth p)

theorem layersFitB_sound (p : Params) : ∀ (m : Nat) (ls : List Layer),
    layersFitB p m ls = true → LayersFit p m ls
  | _, [], _ => trivial
  | m, l :: ls, h => by
    simp only [layersFitB, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, layersFitB_sound p (m + 1) ls h.2⟩

/-- the executable's check implies the theorem's hypothesis -/
theorem fitsB_sound (p : Params) (r : Rounds) (h : fitsB p r = true) : Fits p r := by
  simp only [fitsB, queryFitsB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, ho⟩, hr⟩, hf⟩, hfq⟩, hfl⟩, hq⟩, hqs⟩, hpz⟩, hop⟩, hos⟩, hpp⟩, hps⟩ := h
  exact
    { digest := hd, ood := ho, roots := hr, final := hf, friQueries := hfq
      friLayers := fun ls hls => ⟨(hfl ls hls).1, layersFitB_sound p 0 ls (hfl ls hls).2⟩
      queries := hq
      queryShape := fun q hq' => by
        have := hqs q hq'
        exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
      periodic := hpz, openings := hop, openingShape := hos, permPaths := hpp
      permShape := hps }

end Shield.Read
