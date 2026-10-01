-- NONOS Operating System (AGPL-3.0-or-later)
import Shield.Deep

/-!
What a wrap costs, with both terms counted.

A wrap verifies the layer below it. Its rows are the authentication it walks
plus the DEEP quotient it recomputes, and for five exchanges every table
counted only the first. The second is larger.

Authentication is `chains * queries * depth * rounds`, linear in all four.
DEEP is `queries * next_power_of_two(terms + 1)`, a step. The lever that moves
a step is which side of a boundary the term count sits on, and that is a
different lever from the ones that move a product.
-/

namespace Shield.Wrap

open Shield.Deep

/-- Poseidon rounds per compression. -/
def rounds : Nat := 32

/-- Merkle chains the wrap walks per query. Three with the periodic chain,
two once its root is baked into the verifier. -/
def chains : Nat := 2

def authRows (queries depth : Nat) : Nat := chains * queries * depth * rounds

def deepRows (queries width periodic : Nat) : Nat := queries * rows (terms width periodic)

def wrapRows (queries depth width periodic : Nat) : Nat :=
  authRows queries depth + deepRows queries width periodic

/-- At the settlement layer's own parameters, DEEP is the larger term. Every
figure written before this one was measuring the smaller half. -/
theorem deep_is_the_larger_term :
    authRows 32 26 < deepRows 32 556 1005 := by decide

/-- The wrap at settlement's current shape, with both terms. -/
theorem the_wrap_is_over_two_to_the_seventeen :
    131072 < wrapRows 32 26 556 1005 := by decide

/-- Grind buys queries, which is linear in both terms. -/
theorem grinding_to_twenty_queries_helps :
    wrapRows 20 26 556 1005 < wrapRows 32 26 556 1005 := by decide

/-- Degree four shortens the layer below, so the authentication term falls. -/
theorem degree_four_shortens_the_walk :
    authRows 20 24 < authRows 20 26 := by decide

/-- And it widens the trace, which costs nothing in DEEP because 2118 and 2394
land in one bucket. -/
theorem degree_four_is_free_in_deep :
    deepRows 20 694 1005 = deepRows 20 556 1005 := by decide

/-- So degree four is a net win at this point, by the authentication term
alone. -/
theorem degree_four_is_a_net_win :
    wrapRows 20 24 694 1005 < wrapRows 20 26 556 1005 := by decide

/-- The boundary is worth more than either. Shedding seventy one periodic
columns at degree ten halves the dominant term, which is a larger saving than
grind and degree together. -/
theorem the_boundary_beats_both :
    wrapRows 20 26 556 934 < wrapRows 20 24 694 1005 := by decide

/-- And degree four closes it: at width 694 the same cut no longer crosses. -/
theorem degree_four_closes_the_boundary :
    deepRows 20 694 934 = deepRows 20 694 1005 := by decide

/-- The two levers are therefore not additive, and the order matters. Take the
boundary first, and degree four only if the boundary proves unreachable. -/
theorem the_levers_conflict :
    wrapRows 20 26 556 934 < wrapRows 20 24 694 934 := by decide

/-- Baking the periodic root drops a chain, which is a third of the
authentication term and is available at every layer. -/
theorem baking_the_periodic_root_drops_a_chain :
    chains * 20 * 26 * rounds < 3 * 20 * 26 * rounds := by decide

end Shield.Wrap
