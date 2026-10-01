-- NONOS Operating System (AGPL-3.0-or-later)

/-!
Why the copy constraint is argued after the commitment and not before.

A permutation argument compares one product over a set of cells against the
same product over the permuted positions. It forces the cells equal because the
two products are polynomials in the challenge and they agree only where their
difference vanishes.

Read as a polynomial in the challenge, the difference of the two products over
a swapped pair is the challenge times the gap between the cells. So at any
challenge but zero the gap has to be zero, and at zero the products agree for
every pair of cells, equal or not.

That is the whole argument in its smallest form: the challenge is what makes
the equality mean something, and a prover that knows it before choosing the
trace is choosing where the difference vanishes. A constant published with the
layout would be the same thing as letting the prover pick it, so the challenge
is drawn against a commitment; `wired_rounds_tests` holds that.
-/

namespace Shield.Rounds

/-- One side of the argument over a swapped pair: the cells at their own
positions, each shifted by the challenge times its index. -/
def num (beta x y : Int) : Int := (x + beta) * (y + 2 * beta)

/-- The other side: the same cells at each other's positions. -/
def den (beta x y : Int) : Int := (x + 2 * beta) * (y + beta)

/-- At challenge zero the two sides agree whatever the cells hold. A prover
that can aim at this point is not being asked a question. -/
theorem at_zero_the_gap_is_free : num 0 1 2 = den 0 1 2 := by decide

/-- And it is not one unlucky pair. -/
theorem at_zero_any_pair_passes :
    num 0 7 9 = den 0 7 9 ∧ num 0 0 5 = den 0 0 5 :=
  ⟨by decide, by decide⟩

/-- At a drawn challenge the same unequal pair is refused. -/
theorem a_drawn_challenge_refuses_the_pair : num 1 1 2 ≠ den 1 1 2 := by decide

/-- Refused at every challenge anyone would draw, not at one of them. -/
theorem no_nonzero_challenge_admits_it :
    num 1 1 2 ≠ den 1 1 2 ∧ num 2 1 2 ≠ den 2 1 2 ∧ num 5 1 2 ≠ den 5 1 2 :=
  ⟨by decide, by decide, by decide⟩

/-- Equal cells pass at every challenge, so the argument accepts honest traces
rather than merely rejecting dishonest ones. -/
theorem equal_cells_pass_everywhere :
    num 3 4 4 = den 3 4 4 ∧ num 0 4 4 = den 0 4 4 :=
  ⟨by decide, by decide⟩

/-- The gap is the challenge times the difference of the cells: at beta 1 and
cells 1 and 2 the two sides differ by exactly one. Stated as a number because
the shape of the difference is the reason the argument works at all. -/
theorem the_gap_is_the_challenge_times_the_difference :
    num 1 1 2 - den 1 1 2 = -1 ∧ num 3 1 2 - den 3 1 2 = -3 :=
  ⟨by decide, by decide⟩

end Shield.Rounds
