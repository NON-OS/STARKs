-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The soundness arithmetic of a point, and the two facts a parameter change has
to respect. Everything here is `Nat`, core only, decided rather than argued.
-/

namespace Shield.Params

/-- A soundness point: how many FRI queries are drawn, how many bits of
proof of work sit on the transcript, and how far the domain is blown past the
minimal rate one half. -/
structure Point where
  queries : Nat
  grind : Nat
  extraBlowup : Nat
  deriving DecidableEq

/-- `log2 (1 / rate)`. The rate is `1 / 2 ^ (1 + extraBlowup)`. -/
def rateBits (p : Point) : Nat := 1 + p.extraBlowup

/-- Under the FRI conjecture a query yields `rateBits` bits. -/
def conjectured (p : Point) : Nat := p.queries * rateBits p + p.grind

/-- Inside the proven list decoding radius a query yields half of that. The
grind is unconditional either way. -/
def provable (p : Point) : Nat := p.queries * rateBits p / 2 + p.grind

theorem provable_le_conjectured (p : Point) : provable p ≤ conjectured p := by
  simp only [provable, conjectured]
  omega

def dev : Point := ⟨32, 8, 0⟩
def transfer : Point := ⟨64, 16, 1⟩
def settlement : Point := ⟨32, 16, 3⟩
def wrap : Point := ⟨8, 32, 11⟩

/-- Every production point clears the floor an audit is entitled to. -/
theorem transfer_clears_the_floor : 80 ≤ provable transfer := by decide

theorem settlement_clears_the_floor : 80 ≤ provable settlement := by decide

theorem wrap_clears_the_floor : 80 ≤ provable wrap := by decide

/-- The development point is weaker and is labelled so. If it ever reaches
deployment strength the distinction has collapsed. -/
theorem dev_is_weaker : conjectured dev < conjectured settlement := by decide

/-- The published pair, so a document that states one figure states a number
this file can be checked against. -/
theorem settlement_figures : conjectured settlement = 144 ∧ provable settlement = 80 := by
  decide

theorem wrap_figures : conjectured wrap = 128 ∧ provable wrap = 80 := by decide

/-- Cutting queries at a fixed rate spends the provable floor. -/
theorem cutting_queries_spends_the_floor :
    provable { settlement with queries := 20 } < provable settlement := by decide

/-- Raising the rate to compensate does not. This is the whole argument for
the wrap's parameters, and it is the one the conjectured column cannot see:
both points read 144 and 128 there, which look like a loss. -/
theorem raising_the_rate_holds_the_floor : provable wrap = provable settlement := by
  decide

/-- Fewer queries never buys provable bits back at the same rate and grind. -/
theorem fewer_queries_never_helps (p : Point) (q : Nat) (h : q ≤ p.queries) :
    provable { p with queries := q } ≤ provable p := by
  simp only [provable, rateBits]
  have hm : q * (1 + p.extraBlowup) ≤ p.queries * (1 + p.extraBlowup) :=
    Nat.mul_le_mul_right _ h
  omega

end Shield.Params
