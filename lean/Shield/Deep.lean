-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The DEEP region's row count, which is a step rather than a slope.

`DeepCheckExt::new` sizes the region as `next_power_of_two (terms + 1)`, so a
term count is only expensive when it crosses a boundary and free everywhere
else. Five exchanges of gas tables were written against a linear model of
this, and every one of them was wrong about which lever mattered.
-/

namespace Shield.Deep

/-- Double `acc` until it reaches `n`. The fuel bounds the doubling and is not
a modelling choice: twelve steps carry a term count past any trace this system
can build, and structural recursion on it needs no termination argument. -/
private def upTo (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | f + 1, acc => if n ≤ acc then acc else upTo n f (acc * 2)

/-- Rows of a DEEP region over `terms` terms. -/
def rows (terms : Nat) : Nat := upTo (terms + 1) 64 1

/-- Terms of a wrap over a layer `width` columns wide with `periodic`
preprocessed columns: the opened frame is two rows of the trace, every
periodic column is claimed at `z`, and the composition value is one more. -/
def terms (width periodic : Nat) : Nat := 2 * width + periodic + 1

/-- The measured artifact. `settle-v1.1-layout.json` reports `width_inner 20`,
`n_pz 70`, `n_terms 111`, and its region offsets put the DEEP region at 128
rows. -/
theorem the_emitted_layout_agrees : terms 20 70 = 111 ∧ rows 111 = 128 := by decide

/-- The settlement layer sits just over a boundary. -/
theorem settlement_is_over_the_boundary : rows (terms 556 1005) = 4096 := by decide

/-- Shedding seventy one periodic columns halves the dominant term. At twenty
queries that is 40,960 rows, which is more than the whole authentication term
and more than grind and degree buy together. -/
theorem shedding_seventy_one_halves_it :
    rows (terms 556 1005) = 2 * rows (terms 556 934) := by decide

/-- Degree four widens the trace by 138 columns and costs nothing in DEEP,
because 2118 and 2394 land in the same bucket. -/
theorem degree_four_is_free_here : rows (terms 694 1005) = rows (terms 556 1005) := by
  decide

/-- What degree four actually costs is the reachability of that boundary: the
same seventy one columns no longer cross it, and the cut needed becomes 35
percent instead of 7. -/
theorem degree_four_closes_the_boundary : rows (terms 694 934) ≠ 2048 := by decide

/-- Rows never shrink as terms grow, so a boundary once crossed stays crossed. -/
theorem rows_is_monotone_on_the_measured_range :
    rows (terms 556 934) ≤ rows (terms 556 1005)
    ∧ rows (terms 556 1005) ≤ rows (terms 694 1005) := by decide

end Shield.Deep
