-- NONOS Operating System (AGPL-3.0-or-later)
/-!
Gas by phase of one verification of the shipped proof, measured with
checkpoints inside verifyWhole after the radix-four and Horner fixes and before
the last three. The walk is three quarters of the call; everything before it
is a quarter.
-/

namespace Shield.Phase

inductive Step
  | decodeHead
  | decodeClaims
  | transcriptToZ
  | deepCoefficients
  | friChallenges
  | claimScalar
  | walk
  deriving DecidableEq

def gas : Step → Nat
  | .decodeHead => 894170
  | .decodeClaims => 82796
  | .transcriptToZ => 325190
  | .deepCoefficients => 168742
  | .friChallenges => 961412
  | .claimScalar => 58464
  | .walk => 7661125

def order : List Step :=
  [.decodeHead, .decodeClaims, .transcriptToZ, .deepCoefficients, .friChallenges, .claimScalar,
   .walk]

def sum : List Step → Nat
  | [] => 0
  | s :: rest => gas s + sum rest

theorem the_phases_add_up : sum order = 10151899 := by decide

def beforeTheWalk : List Step := order.take 6

theorem the_head_of_the_call : sum beforeTheWalk = 2490774 := by decide

theorem the_walk_is_three_quarters : 3 * sum order < 4 * gas .walk := by decide

theorem the_walk_is_under_four_fifths : 4 * gas .walk < 4 * sum order := by decide

/-- the FRI challenge derivation absorbed 512 final coefficients one at a time; the batch
absorb that replaced it is worth most of the 961k -/
theorem fri_challenges_were_the_largest_fixed_phase :
    gas .decodeHead < gas .friChallenges ∧ gas .transcriptToZ < gas .friChallenges ∧
    gas .deepCoefficients < gas .friChallenges := by decide

theorem the_claim_scalar_is_cheap : 16 * gas .claimScalar < gas .friChallenges := by decide

theorem decoding_the_head_is_under_a_tenth : 10 * gas .decodeHead < sum order := by decide

/-! the walk, per piece -/

def pieces : Nat := 24

theorem a_piece_on_average : gas .walk / pieces = 319213 := by decide

/-- against the structural model's 65,700 a query, which is 32,850 a piece -/
theorem the_walk_is_ten_times_the_model : 9 * 32850 * pieces < gas .walk := by decide

/-! phases and what they read -/

inductive Reads
  | head
  | claims
  | publics
  | queries
  | nothing
  deriving DecidableEq

def reads : Step → Reads
  | .decodeHead => .head
  | .decodeClaims => .claims
  | .transcriptToZ => .publics
  | .deepCoefficients => .nothing
  | .friChallenges => .head
  | .claimScalar => .nothing
  | .walk => .queries

/-- the queries section is read by the walk alone -/
theorem only_the_walk_reads_the_queries : ∀ s ∈ order, reads s = .queries → s = .walk := by decide

/-- the head is read twice: once to decode it, once to replay its FRI roots -/
def count (r : Reads) : List Step → Nat
  | [] => 0
  | s :: rest => (if reads s = r then 1 else 0) + count r rest

theorem the_head_is_read_twice : count .head order = 2 := by decide

theorem the_claims_are_read_once : count .claims order = 1 := by decide

/-- two phases read nothing from the proof: they derive from the transcript state -/
theorem two_phases_read_nothing : count .nothing order = 2 := by decide

/-! order -/

def before (a b : Step) : List Step → Bool
  | [] => false
  | x :: xs => if x = a then xs.contains b else before a b xs

theorem the_claims_are_decoded_before_z : before .decodeClaims .transcriptToZ order = true := by
  decide

theorem z_precedes_the_deep_coefficients : before .transcriptToZ .deepCoefficients order = true := by
  decide

theorem the_scalar_precedes_the_walk : before .claimScalar .walk order = true := by decide

theorem the_walk_is_last : order.getLast? = some .walk := by decide

/-! what the batch absorb took off the FRI challenge phase -/

theorem the_fri_challenge_phase_after_the_batch_absorb : 961412 - 589185 = 372227 := by decide

/-! shares, in tenths of a percent -/

def permille (s : Step) : Nat := gas s * 1000 / sum order

theorem shares :
    permille .walk = 754 ∧ permille .friChallenges = 94 ∧ permille .decodeHead = 88 ∧
    permille .transcriptToZ = 32 ∧ permille .deepCoefficients = 16 ∧
    permille .decodeClaims = 8 ∧ permille .claimScalar = 5 := by decide

theorem the_shares_lose_rounding : 754 + 94 + 88 + 32 + 16 + 8 + 5 = 997 := by decide

theorem permille_sums_to_at_most_a_thousand (l : List Step) :
    ∀ s ∈ l, permille s ≤ 1000 := by
  intro s _
  simp only [permille]
  cases s <;> decide

end Shield.Phase
