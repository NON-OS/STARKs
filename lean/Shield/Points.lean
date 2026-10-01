-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout
import Shield.Params

/-!
The named soundness points in shield_params, side by side: what each proves,
what each costs in domain, and what the settlement circuit weighs at each.
The circuit is fixed; only queries, grind and blowup move.
-/

namespace Shield.Points

open Shield.Layout

/-- the circuit at a soundness point -/
def at_ (pt : Params.Point) : Params :=
  { shippedFour with queries := pt.queries, extraBlowup := pt.extraBlowup }

def dev : Params.Point := Params.dev
def transfer : Params.Point := Params.transfer
def settlement : Params.Point := Params.settlement
def wrap : Params.Point := Params.wrap
def twoTx : Params.Point := ⟨12, 32, 7⟩

def named : List (String × Params.Point) :=
  [("dev", dev), ("transfer", transfer), ("settlement", settlement), ("wrap", wrap), ("two_tx", twoTx)]

/-! soundness -/

theorem provable_bits :
    Params.provable dev = 24 ∧ Params.provable transfer = 80 ∧ Params.provable settlement = 80 ∧
    Params.provable wrap = 80 ∧ Params.provable twoTx = 80 := by decide

theorem conjectured_bits :
    Params.conjectured dev = 40 ∧ Params.conjectured transfer = 144 ∧
    Params.conjectured settlement = 144 ∧ Params.conjectured wrap = 128 ∧
    Params.conjectured twoTx = 128 := by decide

/-- dev is the only named point under the floor -/
theorem only_dev_is_under_the_floor :
    ∀ e ∈ named, Params.provable e.2 < 80 ↔ e.1 = "dev" := by decide

/-- every production point sits exactly on the floor -/
theorem the_production_points_sit_on_the_floor :
    ∀ e ∈ named, e.1 ≠ "dev" → Params.provable e.2 = 80 := by decide

/-! domains -/

theorem domains :
    logDomain (at_ dev) = 22 ∧ logDomain (at_ transfer) = 23 ∧
    logDomain (at_ settlement) = 25 ∧ logDomain (at_ wrap) = 33 ∧ logDomain (at_ twoTx) = 29 := by
  decide

/-- the wrap point does not fit this circuit: its domain passes the two-adicity -/
theorem the_wrap_point_does_not_fit_this_circuit : 32 < logDomain (at_ wrap) := by decide

theorem every_other_point_fits : ∀ e ∈ named, e.1 ≠ "wrap" → logDomain (at_ e.2) ≤ 32 := by decide

/-! bytes -/

theorem bytes_at_each :
    total (at_ dev) = 221220 ∧ total (at_ transfer) = 447652 ∧
    total (at_ settlement) = 246564 ∧ total (at_ twoTx) = 112436 := by decide

/-- at the same eighty bits, the one-transaction point is the smallest of the three that fit -/
theorem two_tx_is_the_smallest_eighty :
    total (at_ twoTx) < total (at_ settlement) ∧ total (at_ settlement) < total (at_ transfer) := by
  decide

/-- and the only one under the ceiling -/
theorem only_two_tx_is_under_the_ceiling :
    ∀ e ∈ named, e.1 ≠ "wrap" → (total (at_ e.2) ≤ 131072 ↔ e.1 = "two_tx") := by decide

/-! the trade the points make -/

/-- from settlement to two_tx: four more blowup bits, twenty fewer queries, sixteen more grind -/
theorem settlement_to_two_tx :
    twoTx.extraBlowup - settlement.extraBlowup = 4 ∧
    settlement.queries - twoTx.queries = 20 ∧
    twoTx.grind - settlement.grind = 16 := by decide

/-- the domain grows sixteen fold for it -/
theorem sixteen_times_the_domain :
    2 ^ logDomain (at_ twoTx) = 16 * 2 ^ logDomain (at_ settlement) := by decide

/-- the proof shrinks to under half -/
theorem under_half_the_bytes : 2 * total (at_ twoTx) < total (at_ settlement) := by decide

/-- paths per proof: settlement opens 32 queries of 11 paths, two_tx 12 of 11 -/
def pathsPerQuery (p : Params) : Nat := 5 + layers p

theorem paths_per_proof :
    settlement.queries * pathsPerQuery (at_ settlement) = 352 ∧
    twoTx.queries * pathsPerQuery (at_ twoTx) = 132 := by decide

/-! grind against queries -/

/-- the queries alone: settlement proves sixty four bits, two_tx forty eight; the sixteen
missing bits are exactly the sixteen extra grind bits -/
theorem the_grind_covers_the_queries :
    settlement.queries * Params.rateBits settlement / 2 = 64 ∧
    twoTx.queries * Params.rateBits twoTx / 2 = 48 ∧
    twoTx.grind - settlement.grind = 16 := by decide

/-- under the conjecture the trade is not even: two_tx gives up sixteen bits -/
theorem the_conjectured_figure_falls :
    Params.conjectured settlement - Params.conjectured twoTx = 16 := by decide

end Shield.Points
