-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Read.Proof

/-!
What the reader accepts has exactly the size its contents say.

Each section reader advances by the wire size of what it read, never past the
buffer, and the body is refused unless it ends on the last byte. So an accepted
file is the encoding of what was read and nothing more: two files that parse
to one proof have one length, and no byte can be appended to an accepted file
and still be accepted. Every field word in it is canonical by `fp_canonical`.
-/

namespace Shield.Read

theorem readLayer_exact (b : ByteArray) : Exact b (readLayer b) layerW := by
  intro i a j h
  try dsimp only
  unfold readLayer at h
  rw [andThen_some] at h
  obtain ⟨v, j1, h1, h2⟩ := h
  rw [andThen_some] at h2
  obtain ⟨pa, j2, h3, h4⟩ := h2
  cases h4
  have e1 := many_fixed (fp2_exact b) 4 i h1
  have e2 := counted_exact (digest_exact b) j1 pa j h3
  try dsimp only at e1 e2
  rw [sumW_const] at e2
  refine ⟨?_, e2.2⟩
  show j = i + (16 * v.length + (4 + digestBytes * pa.length))
  rw [e1.1]
  omega

theorem readFriQuery_exact (b : ByteArray) : Exact b (readFriQuery b) friQueryW :=
  counted_exact (readLayer_exact b)

theorem readQuery_exact (b : ByteArray) (k : Nat) : Exact b (readQuery b k) queryW := by
  intro i a j h
  try dsimp only
  unfold readQuery at h
  rw [andThen_some] at h
  obtain ⟨deep, j1, h1, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨ot, j0, h0, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨dp, j2, h2, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨tr, j3, h3, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨tp, j4, h4, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨comp, j5, h5, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨cp, j6, h6, h⟩ := h
  cases h
  have e1 := fp2_exact b i deep j1 h1
  have e0 := many_fixed (fp2_exact b) k j1 h0
  have e2 := counted_exact (digest_exact b) j0 dp j2 h2
  have e3 := counted_exact (fp_exact b) j2 tr j3 h3
  have e4 := counted_exact (digest_exact b) j3 tp j4 h4
  have e5 := fp2_exact b j4 comp j5 h5
  have e6 := counted_exact (digest_exact b) j5 cp j h6
  try dsimp only at e1 e0 e2 e3 e4 e5 e6
  simp only [sumW_const] at e2 e3 e4 e6
  refine ⟨?_, e6.2⟩
  show j = i + (16 + 16 * ot.length + (4 + digestBytes * dp.length) + (4 + 8 * tr.length) +
    (4 + digestBytes * tp.length) + 16 + (4 + digestBytes * cp.length))
  omega

theorem readFri_exact (b : ByteArray) : Exact b (readFri b) friW := by
  intro i a j h
  try dsimp only
  unfold readFri at h
  rw [andThen_some] at h
  obtain ⟨roots, j1, h1, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨final, j2, h2, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨qs, j3, h3, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨nonce, j4, h4, h⟩ := h
  cases h
  have e1 := counted_exact (digest_exact b) i roots j1 h1
  have e2 := counted_exact (fp2_exact b) j1 final j2 h2
  have e3 := counted_exact (readFriQuery_exact b) j2 qs j3 h3
  have e4 := u64_exact b j3 nonce j h4
  try dsimp only at e1 e2 e3 e4
  simp only [sumW_const] at e1 e2
  refine ⟨?_, e4.2⟩
  show j = i + ((4 + digestBytes * roots.length) + (4 + 16 * final.length) +
    (4 + sumW friQueryW qs) + 8)
  omega

theorem readExt_exact (b : ByteArray) (k : Nat) : Exact b (readExt b k) extW := by
  intro i a j h
  try dsimp only
  unfold readExt at h
  rw [andThen_some] at h
  obtain ⟨r1, j1, h1, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨r2, j2, h2, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨r3, j3, h3, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨ood, j4, h4, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨fri, j5, h5, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨qs, j6, h6, h⟩ := h
  cases h
  have e1 := digest_exact b i r1 j1 h1
  have e2 := digest_exact b j1 r2 j2 h2
  have e3 := digest_exact b j2 r3 j3 h3
  have e4 := counted_exact (fp2_exact b) j3 ood j4 h4
  have e5 := readFri_exact b j4 fri j5 h5
  have e6 := counted_exact (readQuery_exact b k) j5 qs j h6
  try dsimp only at e1 e2 e3 e4 e5 e6
  simp only [sumW_const] at e4
  refine ⟨?_, e6.2⟩
  show j = i + (3 * digestBytes + (4 + 16 * ood.length) + friW fri + (4 + sumW queryW qs))
  omega

theorem readOpening_exact (b : ByteArray) (n : Nat) : Exact b (readOpening b n) openingW := by
  intro i a j h
  try dsimp only
  unfold readOpening at h
  rw [andThen_some] at h
  obtain ⟨row, j1, h1, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨pa, j2, h2, h⟩ := h
  cases h
  have e1 := many_fixed (fp_exact b) n i h1
  have e2 := path_exact b j1 pa j h2
  try dsimp only at e1 e2
  refine ⟨?_, e2.2⟩
  show j = i + (8 * row.length + pathW pa)
  rw [e1.1]
  omega

/-- every opening row is as wide as the periodic claims -/
theorem rows_of_many (b : ByteArray) (n : Nat) : ∀ (k i : Nat) {l : List Opening} {j : Nat},
    many (readOpening b n) k i = some (l, j) → ∀ o ∈ l, o.row.length = n := by
  intro k
  induction k with
  | zero =>
    intro i l j h o ho
    cases h
    cases ho
  | succ k ih =>
    intro i l j h o ho
    unfold many at h
    rw [andThen_some] at h
    obtain ⟨a, j1, h1, h⟩ := h
    rw [andThen_some] at h
    obtain ⟨l', k', h2, h3⟩ := h
    cases h3
    cases ho with
    | head =>
      unfold readOpening at h1
      rw [andThen_some] at h1
      obtain ⟨row, j2, hr, h1⟩ := h1
      rw [andThen_some] at h1
      obtain ⟨pa, j3, _, h1⟩ := h1
      cases h1
      exact (many_fixed (fp_exact b) n i hr).1
    | tail _ hm => exact ih j1 h2 o hm

/-- an accepted body is the encoding of what was read, ending on the last byte -/
theorem readBody_exact (b : ByteArray) (k i : Nat) {r : Rounds} {j : Nat}
    (h : readBody b k i = some (r, j)) :
    j = b.size ∧ b.size = i + roundsW r ∧ r.openings.length = r.ext.queries.length ∧
      r.permPaths.length = r.ext.queries.length ∧
      ∀ o ∈ r.openings, o.row.length = r.periodicZ.length := by
  unfold readBody at h
  rw [andThen_some] at h
  obtain ⟨pr, j1, h1, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨rw', j2, h2, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨ext, j3, h3, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨pz, j4, h4, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨ops, j5, h5, h⟩ := h
  rw [andThen_some] at h
  obtain ⟨pps, j6, h6, h⟩ := h
  by_cases hend : j6 = b.size
  · rw [if_pos hend] at h
    cases h
    have e1 := digest_exact b i pr j1 h1
    have e2 := u32_exact b j1 rw' j2 h2
    have e3 := readExt_exact b k j2 ext j3 h3
    try dsimp only at e1 e2 e3
    rw [capped_eq (fp2_exact b)] at h4
    have e4 := counted_exact (fp2_exact b) j3 pz j4 h4
    have e5 := many_exact (readOpening_exact b pz.length) _ j4 ops j5 h5
    have e6 := many_exact (path_exact b) _ j5 pps _ h6
    try dsimp only at e4 e5 e6
    simp only [sumW_const] at e4
    refine ⟨hend, ?_, e5.1, e6.1, ?_⟩
    · show b.size = i + (digestBytes + 4 + extW ext + (4 + 16 * pz.length) +
        sumW openingW ops + sumW pathW pps)
      omega
    · exact rows_of_many b pz.length _ j4 h5
  · rw [if_neg hend] at h
    cases h

/-- an accepted legacy artifact is exactly as long as its contents -/
theorem readLegacy_size (b : ByteArray) (r : Rounds) (h : readLegacy b = some r) :
    roundsW r = b.size := by
  unfold readLegacy at h
  cases hb : readBody b 0 0 with
  | none => rw [hb] at h; cases h
  | some v =>
    obtain ⟨r', j⟩ := v
    rw [hb] at h
    cases h
    have e := readBody_exact b 0 0 hb
    show roundsW r' = b.size
    omega

/-- an accepted format 4 artifact is its forty-byte header and exactly its contents -/
theorem readFour_size (b : ByteArray) (e : List UInt8) (r : Rounds) (h : readFour b e = some r) :
    headerBytes + roundsW r = b.size := by
  unfold readFour at h
  by_cases hh : headerOk b e = true
  · rw [if_pos hh] at h
    cases hb : readBody b 3 headerBytes with
    | none => rw [hb] at h; cases h
    | some v =>
      obtain ⟨r', j⟩ := v
      rw [hb] at h
      cases h
      have e := readBody_exact b 3 headerBytes hb
      show headerBytes + roundsW r' = b.size
      omega
  · rw [if_neg hh] at h
    cases h

/-- nothing is read from a file whose header is not the one this build serves -/
theorem a_foreign_header_reads_nothing (b : ByteArray) (e : List UInt8)
    (h : headerOk b e = false) : readFour b e = none := by
  unfold readFour
  rw [if_neg (by rw [h]; decide)]

/-- so one proof has one encoding length: two accepted files that read to the same contents
are the same size -/
theorem one_proof_one_length (b c : ByteArray) (r : Rounds) (hb : readLegacy b = some r)
    (hc : readLegacy c = some r) : b.size = c.size := by
  rw [← readLegacy_size b r hb, ← readLegacy_size c r hc]

end Shield.Read
