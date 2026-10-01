-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The index arithmetic of a radix-four FRI layer, for every layer size.

A layer of `4q` values is committed four to a leaf: the leaf at index
`i < q` holds the values at `i`, `i + q`, `i + 2q`, `i + 3q`. A query drawn at
position `pos` opens leaf `pos % q`, folds the four values into one, and that
one must equal a value the next layer opens. The on-chain verifier picks which
with `v[(i / q') % 4]`, where `q' = q / 4` is the next layer's quarter.

That selector is the one line of the radix-four path that is index arithmetic
rather than field arithmetic, and a verifier that gets it wrong refuses every
honest proof or checks the wrong value. These theorems say it is right for
every size, not only the size of the proof we shipped.

Everything is `Nat`, core only.
-/

namespace Shield.Quad

/-- The four positions one leaf holds, for leaf `i` of a layer with quarter `q`. -/
def positions (q i : Nat) : List Nat := [i, i + q, i + 2 * q, i + 3 * q]

/-- All four positions lie inside the layer. -/
theorem positions_in_layer (q i : Nat) (h : i < q) : ∀ x ∈ positions q i, x < 4 * q := by
  intro x hx
  simp only [positions, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  omega

/-- The four positions are distinct, pairwise, whenever the leaf index is inside the quarter. -/
theorem positions_distinct (q i : Nat) (h : i < q) :
    i ≠ i + q ∧ i ≠ i + 2 * q ∧ i ≠ i + 3 * q ∧
    i + q ≠ i + 2 * q ∧ i + q ≠ i + 3 * q ∧ i + 2 * q ≠ i + 3 * q := by
  omega

/-- The fold pairs each value with the one half a layer away, which is its negation on the
coset. `v0` with `v2`, `v1` with `v3`: both pairs are `2q` apart in a layer of `4q`. -/
theorem pairs_are_half_a_layer_apart (q i : Nat) :
    (i + 2 * q) - i = (4 * q) / 2 ∧ (i + 3 * q) - (i + q) = (4 * q) / 2 := by
  omega

/-- Every position in a layer belongs to exactly one leaf: the leaf `x % q`, as the
`x / q`-th of its four values. -/
theorem every_position_has_one_leaf (q x : Nat) (hq : 0 < q) (hx : x < 4 * q) :
    x = x % q + (x / q) * q ∧ x / q < 4 := by
  refine ⟨?_, ?_⟩
  · have := Nat.mod_add_div x q
    rw [Nat.mul_comm] at this
    omega
  · exact (Nat.div_lt_iff_lt_mul hq).mpr hx

/-- The next-layer selector is sound.

A query at `pos` opens leaf `i = pos % (4q')` on the current layer, whose output lands at
position `i` of the next layer. The next layer's quarter is `q'`, so it opens leaf
`pos % q'`, and position `i` is its `(i / q')`-th value. The selector the verifier uses,
`(i / q') % 4`, therefore names exactly the value the fold has to match. -/
theorem next_layer_selector (pos q' : Nat) (hq : 0 < q') :
    let i := pos % (4 * q')
    i = pos % q' + ((i / q') % 4) * q' := by
  intro i
  have hi : i < 4 * q' := Nat.mod_lt _ (by omega)
  have hd : q' ∣ 4 * q' := ⟨4, by rw [Nat.mul_comm]⟩
  -- the leaf the next layer opens is the current position reduced by its quarter
  have hleaf : i % q' = pos % q' := Nat.mod_mod_of_dvd pos hd
  obtain ⟨hsplit, hlt⟩ := every_position_has_one_leaf q' i hq hi
  rw [Nat.mod_eq_of_lt hlt, ← hleaf]
  exact hsplit

/-- The selector never leaves the leaf: it indexes one of the four values opened. -/
theorem selector_in_range (pos q' : Nat) :
    (pos % (4 * q') / q') % 4 < 4 := Nat.mod_lt _ (by decide)

/-! The shipped proof's first layers, as a check the general statements are the ones used. -/

/-- At the shipped domain of `2^29`, the first layer's quarter is `2^27`. -/
theorem shipped_first_quarter : 2 ^ 29 / 4 = 2 ^ 27 := by decide

/-- Layer quarters shrink by four each layer: `2^27, 2^25, ..., 2^17` over six layers. -/
def quarter (logDomain m : Nat) : Nat := 2 ^ (logDomain - 2 * (m + 1))

theorem shipped_quarters :
    [quarter 29 0, quarter 29 1, quarter 29 2, quarter 29 3, quarter 29 4, quarter 29 5] =
      [2 ^ 27, 2 ^ 25, 2 ^ 23, 2 ^ 21, 2 ^ 19, 2 ^ 17] := by
  decide

end Shield.Quad
