-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The sponge the recursion runs in-circuit: width 8, rate 4, capacity 4, full
rounds only, a block of four field elements. The block counts for the publics,
the frame and the claims are checked here, with the trace rows each one costs.
-/

namespace Shield.Poseidon

def width : Nat := 8
def rate : Nat := 4
def capacity : Nat := 4

theorem rate_plus_capacity_is_width : rate + capacity = width := by decide

theorem rate_is_half_the_width : 2 * rate = width := by decide

/-- the capacity in bits, four 64-bit lanes -/
theorem capacity_bits : capacity * 64 = 256 := by decide

theorem capacity_collision_bits : capacity * 64 / 2 = 128 := by decide

/-! ## Blocks -/

/-- permutations to absorb `n` elements -/
def blocks (n : Nat) : Nat := (n + rate - 1) / rate

theorem blocks_of_the_publics : blocks 32 = 8 := by decide

/-- a 32-byte identity is four 8-byte words, one block -/
theorem blocks_of_an_identity : blocks 4 = 1 := by decide

theorem blocks_of_the_frame : blocks 82 = 21 := by decide

theorem blocks_of_the_claims : blocks 119 = 30 := by decide

theorem blocks_of_nothing : blocks 0 = 0 := by decide

theorem blocks_of_one : blocks 1 = 1 := by decide

theorem an_identity_is_four_words : 32 / 8 = 4 := by decide

theorem blocks_of_whole_blocks (k : Nat) : blocks (4 * k) = k := by
  unfold blocks rate
  omega

theorem blocks_cover_the_input (n : Nat) : n ≤ blocks n * rate := by
  unfold blocks rate
  omega

theorem blocks_are_tight (n : Nat) : blocks n * rate < n + rate := by
  unfold blocks rate
  omega

theorem padding_is_under_one_block (n : Nat) : blocks n * rate - n < rate := by
  unfold blocks rate
  omega

theorem one_more_block (n : Nat) : blocks (n + 4) = blocks n + 1 := by
  unfold blocks rate
  omega

theorem blocks_are_monotone (a b : Nat) (h : a ≤ b) : blocks a ≤ blocks b := by
  unfold blocks rate
  omega

theorem blocks_are_zero_only_for_nothing (n : Nat) : blocks n = 0 ↔ n = 0 := by
  unfold blocks rate
  constructor
  · intro a
    omega
  · intro a
    omega

theorem blocks_split_at_whole_blocks (a k : Nat) : blocks (a + 4 * k) = blocks a + k := by
  unfold blocks rate
  omega

/-- absorbing two inputs separately never costs less than absorbing them together -/
theorem separate_absorbs_cost_at_least_joint (a b : Nat) :
    blocks (a + b) ≤ blocks a + blocks b := by
  unfold blocks rate
  omega

theorem separate_absorbs_cost_at_most_one_more (a b : Nat) :
    blocks a + blocks b ≤ blocks (a + b) + 1 := by
  unfold blocks rate
  omega

/-! ## Lanes consumed -/

/-- lanes a message occupies, padding included -/
def lanes (n : Nat) : Nat := blocks n * rate

theorem lanes_of_the_publics : lanes 32 = 32 := by decide

theorem lanes_of_the_frame : lanes 82 = 84 := by decide

theorem lanes_of_the_claims : lanes 119 = 120 := by decide

theorem the_publics_need_no_padding : lanes 32 - 32 = 0 := by decide

theorem the_frame_pads_two_lanes : lanes 82 - 82 = 2 := by decide

theorem the_claims_pad_one_lane : lanes 119 - 119 = 1 := by decide

/-! ## Chunking -/

/-- a message cut into rate-sized blocks, the last one short -/
def chunks : List Nat → List (List Nat)
  | [] => []
  | a :: b :: c :: d :: rest => [a, b, c, d] :: chunks rest
  | l => [l]

theorem chunks_of_a_short_message : chunks [1, 2, 3] = [[1, 2, 3]] := by decide

theorem chunks_of_one_block : chunks [1, 2, 3, 4] = [[1, 2, 3, 4]] := by decide

theorem chunks_of_nothing : chunks [] = [] := rfl

theorem chunks_of_the_publics : (chunks (List.range 32)).length = blocks 32 := by decide

theorem chunks_of_the_frame : (chunks (List.range 82)).length = blocks 82 := by decide

theorem chunks_of_the_claims : (chunks (List.range 119)).length = blocks 119 := by decide

theorem the_frame_ends_short : (chunks (List.range 82)).getLast? = some [80, 81] := by decide

theorem chunking_keeps_every_element :
    (chunks (List.range 82)).foldr (fun c acc => c ++ acc) [] = List.range 82 := by
  decide

/-! ## Rounds -/

def rounds (logRounds : Nat) : Nat := 2 ^ logRounds

/-- the pool's log round count -/
def poolLogRounds : Nat := 5

theorem pool_rounds : rounds poolLogRounds = 32 := by decide

theorem rounds_at_five : rounds 5 = 32 := by decide

theorem rounds_at_two : rounds 2 = 4 := by decide

/-- a four-round instance is eight times fewer rounds than the pool's -/
theorem four_rounds_is_an_eighth : 8 * rounds 2 = rounds 5 := by decide

theorem rounds_add (a b : Nat) : rounds (a + b) = rounds a * rounds b := Nat.pow_add 2 a b

theorem rounds_split_as_three_and_two : rounds 5 = rounds 3 * rounds 2 := rounds_add 3 2

theorem rounds_are_monotone (a b : Nat) (h : a ≤ b) : rounds a ≤ rounds b :=
  Nat.pow_le_pow_right (by decide) h

theorem rounds_never_vanish : ∀ k < 11, 0 < rounds k := by decide

/-! ## Trace rows -/

/-- one absorb block, one row per round -/
def rowsPerBlock : Nat := 32

theorem a_row_per_round : rowsPerBlock = rounds poolLogRounds := by decide

def rows (n : Nat) : Nat := rowsPerBlock * blocks n

theorem the_identity_binding_is_one_block : rowsPerBlock * blocks 4 = 32 := by decide

theorem rows_of_the_publics : rows 32 = 256 := by decide

theorem rows_of_the_frame : rows 82 = 672 := by decide

theorem rows_of_the_claims : rows 119 = 960 := by decide

theorem rows_of_the_transcript_inputs : rows 32 + rows 4 + rows 82 + rows 119 = 1920 := by
  decide

theorem rows_of_whole_blocks (k : Nat) : rows (4 * k) = 32 * k := by
  unfold rows rowsPerBlock
  rw [blocks_of_whole_blocks]

theorem the_identity_adds_one_block (n : Nat) : rows (n + 4) = rows n + rowsPerBlock := by
  unfold rows
  rw [one_more_block, Nat.mul_add, Nat.mul_one]

/-! ## S-box -/

def sboxDegree : Nat := 7

def witnessedDegree : Nat := 3

theorem witnessing_lowers_the_degree : witnessedDegree < sboxDegree := by decide

theorem two_witnessed_rows_cover_the_seventh : 3 * 3 = 9 ∧ 7 ≤ 9 := by decide

theorem the_seventh_splits : 4 + 2 + 1 = sboxDegree := by decide

theorem the_cube_splits : 2 + 1 = witnessedDegree := by decide

theorem seventh_power_is_fourth_square_first (x : Nat) : x ^ 7 = x ^ 4 * x ^ 2 * x := by
  have a : x ^ 7 = x ^ 6 * x := rfl
  have b : x ^ 6 = x ^ 4 * x ^ 2 := Nat.pow_add x 4 2
  rw [a, b]

theorem cube_is_square_times_first (x : Nat) : x ^ 3 = x ^ 2 * x := rfl

/-- `x^7` permutes the field since 7 does not divide `p - 1` -/
theorem seven_does_not_divide_the_group_order : 18446744069414584320 % 7 = 5 := by decide

/-- `x^3` does not, since 3 divides `p - 1` -/
theorem three_divides_the_group_order : 18446744069414584320 % 3 = 0 := by decide

theorem seventh_power_of_two : 2 ^ sboxDegree = 128 := by decide

/-! ## Digest lanes -/

/-- a 24-byte keccak digest is three 8-byte words -/
theorem a_keccak_digest_is_three_words : 24 / 8 = 3 := by decide

theorem a_digest_fits_one_block : 3 < rate := by decide

theorem one_lane_spare : rate - 3 = 1 := by decide

theorem a_digest_is_one_absorb : blocks 3 = 1 := by decide

theorem a_sponge_digest_is_one_rate : rate * 8 = 32 := by decide

theorem a_sponge_digest_is_a_word : rate * 64 = 256 := by decide

end Shield.Poseidon
