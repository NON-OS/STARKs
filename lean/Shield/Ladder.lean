-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Accepted verifications of the shipped 112436-byte proof, each on the same
verifier after one more fix, measured in the gas test. The receipt of the
real transaction closes the file. Every figure is gas.
-/

namespace Shield.Ladder

/-! the gas test figures, one per fix -/

def radixFourWired : Nat := 23182679
def hornerNoAlloc : Nat := 12069603
def foldOnStack : Nat := 11245248
def hornerYul : Nat := 9752952
def finalAbsorbBatch : Nat := 9163767
def friPathsInPlace : Nat := 8876381

def ladder : List Nat := [23182679, 12069603, 11245248, 9752952, 9163767, 8876381]

theorem ladder_is_the_named_steps :
    ladder = [radixFourWired, hornerNoAlloc, foldOnStack, hornerYul, finalAbsorbBatch,
      friPathsInPlace] := rfl

theorem ladder_length : ladder.length = 6 := by decide

theorem ladder_head : ladder.head? = some radixFourWired := rfl

/-- execution left under the cap after base and calldata, from Budget -/
def executionBudget : Nat := 14987276
def cap : Nat := 16777216

theorem the_budget_is_under_the_cap : cap - executionBudget = 1789940 := by decide

theorem base_and_calldata_are_the_difference : 21000 + 1768940 = cap - executionBudget := by
  decide

/-! strictly falling -/

/-- the head of the list, if any, is below `a` -/
def headBelow (a : Nat) : List Nat → Prop
  | [] => True
  | b :: _ => b < a

/-- each element strictly greater than the next -/
def descending : List Nat → Prop
  | [] => True
  | a :: l => headBelow a l ∧ descending l

def decHeadBelow (a : Nat) : (l : List Nat) → Decidable (headBelow a l)
  | [] => isTrue trivial
  | b :: _ => Nat.decLt b a

instance (a : Nat) (l : List Nat) : Decidable (headBelow a l) := decHeadBelow a l

def decDescending : (l : List Nat) → Decidable (descending l)
  | [] => isTrue trivial
  | a :: l =>
    match decHeadBelow a l, decDescending l with
    | isTrue h₁, isTrue h₂ => isTrue (And.intro h₁ h₂)
    | isFalse h₁, _ => isFalse (fun h => h₁ (And.left h))
    | _, isFalse h₂ => isFalse (fun h => h₂ (And.right h))

instance (l : List Nat) : Decidable (descending l) := decDescending l

theorem descending_ladder : descending ladder := by decide

theorem the_named_steps_descend :
    radixFourWired > hornerNoAlloc ∧ hornerNoAlloc > foldOnStack ∧ foldOnStack > hornerYul ∧
    hornerYul > finalAbsorbBatch ∧ finalAbsorbBatch > friPathsInPlace := by decide

theorem descending_head (a b : Nat) (l : List Nat) (h : descending (a :: b :: l)) : a > b :=
  And.left h

theorem descending_tail (a : Nat) (l : List Nat) (h : descending (a :: l)) : descending l :=
  And.right h

theorem descending_drop_one (l : List Nat) (h : descending l) : descending (l.drop 1) := by
  cases l with
  | nil => exact trivial
  | cons a t => exact And.right h

/-- every later element of a descending list is below its head -/
theorem descending_bounds (a : Nat) (l : List Nat) : descending (a :: l) → ∀ x ∈ l, x < a := by
  induction l generalizing a with
  | nil =>
    intro _ x hx
    cases hx
  | cons b t ih =>
    intro h x hx
    have hab : b < a := And.left h
    have ht : descending (b :: t) := And.right h
    cases List.mem_cons.mp hx with
    | inl e => omega
    | inr hm =>
      have hxb := ih b ht x hm
      omega

theorem the_first_step_is_the_highest : ∀ x ∈ ladder.drop 1, x < radixFourWired :=
  descending_bounds radixFourWired (ladder.drop 1) descending_ladder

theorem the_last_step_is_the_lowest : ∀ x ∈ ladder, friPathsInPlace ≤ x := by decide

/-! against the budget -/

def underBudget (g : Nat) : Prop := g ≤ executionBudget

instance (g : Nat) : Decidable (underBudget g) := Nat.decLe g executionBudget

theorem only_the_first_step_is_over_budget :
    executionBudget < radixFourWired ∧ hornerNoAlloc ≤ executionBudget ∧
    foldOnStack ≤ executionBudget ∧ hornerYul ≤ executionBudget ∧
    finalAbsorbBatch ≤ executionBudget ∧ friPathsInPlace ≤ executionBudget := by decide

theorem every_later_step_is_under_budget : ∀ x ∈ ladder.drop 1, x ≤ executionBudget := by
  decide

theorem every_step_is_the_first_or_under_budget :
    ∀ x ∈ ladder, x = radixFourWired ∨ underBudget x := by decide

theorem the_first_step_is_over_the_cap : cap < radixFourWired := by decide

theorem the_first_step_overshoots_the_budget : radixFourWired - executionBudget = 8195403 := by
  decide

theorem the_second_step_clears_the_budget : executionBudget - hornerNoAlloc = 2917673 := by
  decide

theorem the_last_step_margin : executionBudget - friPathsInPlace = 6110895 := by decide

theorem under_budget_is_downward_closed (g k : Nat) (hg : g ≤ k) (hu : underBudget k) :
    underBudget g :=
  Nat.le_trans hg hu

/-- below the second step, every figure is under budget -/
theorem below_the_second_step_is_under_budget (g : Nat) (h : g ≤ hornerNoAlloc) :
    underBudget g :=
  under_budget_is_downward_closed g hornerNoAlloc h (by decide)

/-! what each fix saved -/

/-- Horner stopped allocating a struct per step -/
theorem horner_allocation_saving : radixFourWired - hornerNoAlloc = 11113076 := by decide

/-- the fold kept its values on the stack -/
theorem fold_saving : hornerNoAlloc - foldOnStack = 824355 := by decide

/-- Horner written in assembly -/
theorem horner_assembly_saving : foldOnStack - hornerYul = 1492296 := by decide

/-- the final absorb hashed in one batch -/
theorem batch_absorb_saving : hornerYul - finalAbsorbBatch = 589185 := by decide

/-- the FRI paths read in place -/
theorem paths_in_place_saving : finalAbsorbBatch - friPathsInPlace = 287386 := by decide

theorem total_drop : radixFourWired - friPathsInPlace = 14306298 := by decide

theorem the_savings_add_up :
    11113076 + 824355 + 1492296 + 589185 + 287386 = radixFourWired - friPathsInPlace := by
  decide

theorem the_horner_step_is_over_half_the_drop : 2 * 11113076 > 14306298 := by decide

theorem the_horner_step_is_over_three_quarters : 4 * 11113076 > 3 * 14306298 := by decide

/-- the two Horner fixes together, allocation and assembly -/
theorem the_horner_fixes_together : 11113076 + 1492296 = 12605372 := by decide

theorem the_smallest_saving_is_the_last :
    287386 < 589185 ∧ 589185 < 824355 ∧ 824355 < 1492296 ∧ 1492296 < 11113076 := by decide

/-- the last gas test figure is under two thirds of the budget -/
theorem the_last_step_under_two_thirds : 3 * friPathsInPlace < 2 * executionBudget := by decide

/-! the receipt -/

def receiptExecution : Nat := 7783856
def receiptIntrinsic : Nat := 1798304
def receiptTotal : Nat := 9582160

theorem the_receipt_adds_up : receiptIntrinsic + receiptExecution = receiptTotal := by decide

theorem the_receipt_is_under_the_cap : receiptTotal < cap := by decide

theorem under_three_fifths_of_the_cap : 10 * receiptTotal < 6 * cap := by decide

theorem headroom : cap - receiptTotal = 7195056 := by decide

/-- the gas test charged for its own argument encoding, the chain did not -/
theorem the_receipt_is_under_the_last_step : receiptExecution < friPathsInPlace := by decide

theorem the_gas_test_overhead : friPathsInPlace - receiptExecution = 1092525 := by decide

theorem the_receipt_is_under_budget : underBudget receiptExecution := by decide

theorem the_receipt_budget_margin : executionBudget - receiptExecution = 7203420 := by decide

/-- the ABI words around the proof raise intrinsic gas by 8364 over the bare proof -/
theorem the_abi_wrapping :
    receiptIntrinsic - (cap - executionBudget) = 8364 ∧
    executionBudget - receiptExecution - 8364 = cap - receiptTotal := by decide

theorem the_receipt_is_under_every_step : ∀ x ∈ ladder, receiptExecution < x := by decide

/-! tampered proofs, as refused -/

inductive Tamper
  | friValue
  | friPath
  | lastLayer
  | nonce
  deriving DecidableEq

def refusal : Tamper → String
  | .friValue => "LayerAuthFailed"
  | .friPath => "LayerAuthFailed"
  | .lastLayer => "LayerAuthFailed"
  | .nonce => "GrindRejected"

def Tamper.all : List Tamper := [.friValue, .friPath, .lastLayer, .nonce]

theorem every_tamper_is_listed : ∀ t : Tamper, t ∈ Tamper.all := by
  intro t
  cases t <;> decide

theorem the_layer_tampers_fail_authentication :
    refusal .friValue = "LayerAuthFailed" ∧ refusal .friPath = "LayerAuthFailed" ∧
    refusal .lastLayer = "LayerAuthFailed" := ⟨rfl, rfl, rfl⟩

theorem the_nonce_tamper_fails_the_grind : refusal .nonce = "GrindRejected" := rfl

theorem no_tamper_is_accepted : ∀ t : Tamper, refusal t ≠ "accepted" := by
  intro t
  cases t <;> decide

theorem every_listed_tamper_is_refused : ∀ t ∈ Tamper.all, refusal t ≠ "accepted" := by decide

/-- only the nonce reaches the grind check -/
theorem only_the_nonce_is_a_grind_refusal :
    ∀ t : Tamper, refusal t = "GrindRejected" → t = .nonce := by
  intro t
  cases t <;> decide

end Shield.Ladder
