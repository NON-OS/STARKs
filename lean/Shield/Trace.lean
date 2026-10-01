-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
The outer trace as the prover laid it out: 2^18 rows, 41 columns, of which 37
are the regions' own witness and 4 the permutation argument's, and a compose
region of 10,914 program steps in 16,384 rows. From the run log.
-/

namespace Shield.Trace

open Shield.Layout

def logRows : Nat := 18
def rows : Nat := 2 ^ logRows
def width : Nat := 41
def regionWidth : Nat := 37
def permutationColumns : Nat := width - regionWidth

theorem rows_is_the_layout : logRows = shipped.logTrace ∧ width = shipped.width := by decide

theorem four_permutation_columns : permutationColumns = 4 := by decide

theorem the_regions_come_first : regionWidth < width := by decide

/-- two columns a challenge: beta and gamma each get an accumulator pair -/
theorem two_columns_a_challenge : permutationColumns = 2 * 2 := by decide

def cells : Nat := rows * width

theorem cells_count : cells = 10747904 := by decide

/-- eight bytes a cell before blowup -/
theorem the_trace_in_bytes : 8 * cells = 85983232 := by decide

/-- and over the evaluation domain, 2^11 times more -/
theorem the_blown_trace_in_bytes : 8 * 2 ^ 29 * width = 176093659136 := by decide

theorem blowup_factor : 2 ^ 29 / rows = 2048 := by decide

/-! the compose region -/

def composeSteps : Nat := 10914
def composeRows : Nat := 16384

theorem compose_rows_are_a_power_of_two : composeRows = 2 ^ 14 := by decide

theorem compose_fits : composeSteps ≤ composeRows := by decide

theorem compose_would_not_fit_one_size_down : 2 ^ 13 < composeSteps := by decide

/-- just under two thirds full: three times the steps fall 26 short of twice the rows -/
theorem compose_is_just_under_two_thirds :
    3 * composeSteps < 2 * composeRows ∧ 2 * composeRows - 3 * composeSteps = 26 := by decide

theorem compose_headroom : composeRows - composeSteps = 5470 := by decide

/-- the compose region is one sixteenth of the trace -/
theorem compose_is_a_sixteenth : 16 * composeRows = rows := by decide

/-! degree and the domain -/

def constraintDegree : Nat := 8

theorem degree_log : constraintDegree = 2 ^ shipped.degreeLog := by decide

/-- the composition's degree bound is the trace times the degree -/
theorem the_bound : rows * constraintDegree = 2 ^ logBound shipped := by decide

theorem the_bound_log : logBound shipped = 21 := by decide

/-- an inner S-box of degree 7 witnessed at degree 3 keeps every constraint under 8 -/
def sboxWitnessed : Nat := 3
theorem the_sbox_fits_the_degree : sboxWitnessed ≤ constraintDegree := by decide

/-! blinding -/

/-- one blinding polynomial a column, so every column is hidden off the trace domain -/
def blindingPolynomials : Nat := width

theorem one_blind_a_column : blindingPolynomials = 41 := by decide

/-! rows a region kind costs, from the assembly log -/

def regionRows (values depth : Nat) : Nat := (values / 4 + depth) * 32

theorem trace_auth_in_program_form : regionRows 41 25 = 1120 := by decide

theorem the_walk_alone : regionRows 0 25 = 800 := by decide

/-- the region count of the outer, as assembled: 37 transitions bind it -/
def transitions : Nat := 37
def boundaries : Nat := 723

theorem transitions_and_boundaries : transitions + boundaries = 760 := by decide

/-- boundaries outnumber transitions twenty to one: the wiring is mostly pins -/
theorem boundaries_dominate : 19 * transitions < boundaries := by decide

/-! utilisation -/

def used (steps rowsOf : Nat) : Nat := steps * 1000 / rowsOf

theorem compose_utilisation_permille : used composeSteps composeRows = 666 := by decide

theorem a_full_region : used composeRows composeRows = 1000 := by decide

theorem used_le_thousand (s r : Nat) (h : s ≤ r) : used s r ≤ 1000 := by
  simp only [used]
  exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right 1000 h)

end Shield.Trace
