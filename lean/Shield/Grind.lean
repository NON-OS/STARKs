-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The proof of work before the FRI queries. The prover searches for a 64-bit
nonce whose squeezed transcript word has `g` leading zero bits; the verifier
checks one comparison. Stated over `Nat` with the word as a value below `2^64`.
-/

namespace Shield.Grind

theorem two_to_64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

/-- `g` leading zero bits in a 64-bit word is the word being below `2^(64 - g)` -/
def passes (h g : Nat) : Prop := h < 2 ^ (64 - g)

instance (h g : Nat) : Decidable (passes h g) := by
  unfold passes; infer_instance

/-! ## The check -/

theorem every_word_passes_zero_bits (h : Nat) (hh : h < 18446744073709551616) :
    passes h 0 := by
  unfold passes
  show h < 2 ^ 64
  rw [two_to_64]
  exact hh

theorem zero_passes_every_grind : ∀ g < 65, passes 0 g := by decide

theorem a_passing_word_is_a_word (h g : Nat) (hp : passes h g) : h < 2 ^ 64 := by
  unfold passes at hp
  have e : 2 ^ (64 - g) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.sub_le 64 g)
  exact Nat.lt_of_lt_of_le hp e

theorem one_more_bit_is_harder (h g : Nat) (hp : passes h (g + 1)) : passes h g := by
  unfold passes at hp ⊢
  have e : 2 ^ (64 - (g + 1)) ≤ 2 ^ (64 - g) := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le hp e

theorem more_bits_is_harder (h a b : Nat) (hab : a ≤ b) (hp : passes h b) : passes h a := by
  unfold passes at hp ⊢
  have e : 2 ^ (64 - b) ≤ 2 ^ (64 - a) := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le hp e

theorem a_smaller_word_passes_too (h k g : Nat) (hk : k ≤ h) (hp : passes h g) :
    passes k g := by
  unfold passes at hp ⊢
  exact Nat.lt_of_le_of_lt hk hp

/-- a passing word has nothing above its low `64 - g` bits -/
theorem a_passing_word_has_no_high_bits (h g : Nat) (hp : passes h g) : h / 2 ^ (64 - g) = 0 :=
  Nat.div_eq_of_lt hp

theorem thirty_two_bits_concrete : passes 4294967295 32 := by decide

theorem thirty_two_bits_refuses_the_next : ¬ passes 4294967296 32 := by decide

theorem sixty_four_bits_is_zero_only : passes 0 64 ∧ ¬ passes 1 64 := by decide

theorem the_top_word_fails_one_bit : ¬ passes 9223372036854775808 1 := by decide

theorem just_below_the_top_bit_passes_one_bit : passes 9223372036854775807 1 := by decide

/-! ## Counting -/

/-- the passing words at `g` bits -/
def passingWords (g : Nat) : Nat := 2 ^ (64 - g)

theorem passes_iff_below_the_count (h g : Nat) : passes h g ↔ h < passingWords g := Iff.rfl

theorem passing_words_at_32 : passingWords 32 = 4294967296 := by decide

theorem passing_words_at_0 : passingWords 0 = 2 ^ 64 := by decide

theorem passing_words_at_64 : passingWords 64 = 1 := by decide

theorem passing_words_never_vanish : ∀ g < 65, 0 < passingWords g := by decide

theorem passing_words_at_16 : passingWords 16 = 281474976710656 := by decide

theorem every_bit_halves_the_passing_words (g : Nat) (hg : g < 64) :
    passingWords g = 2 * passingWords (g + 1) := by
  unfold passingWords
  have s : 64 - g = 64 - (g + 1) + 1 := by omega
  have e : 2 ^ (64 - (g + 1) + 1) = 2 ^ (64 - (g + 1)) * 2 := rfl
  rw [s, e, Nat.mul_comm]

theorem every_bit_halves_concrete : ∀ g < 64, passingWords g = 2 * passingWords (g + 1) := by
  decide

theorem zero_bits_is_any_word (h : Nat) : passes h 0 ↔ h < 2 ^ 64 := Iff.rfl

theorem sixty_four_bits_is_the_zero_word (h : Nat) : passes h 64 ↔ h = 0 := by
  unfold passes
  show h < 1 ↔ h = 0
  constructor
  · intro a
    omega
  · intro a
    omega

/-- expected hashes before a pass -/
def trials (g : Nat) : Nat := 2 ^ g

theorem trials_times_passing_is_every_word :
    ∀ g < 65, trials g * passingWords g = 18446744073709551616 := by decide

theorem trials_times_passing_is_two_to_64 (g : Nat) (hg : g ≤ 64) :
    trials g * passingWords g = 2 ^ 64 := by
  unfold trials passingWords
  have s : g + (64 - g) = 64 := by omega
  rw [← Nat.pow_add, s]

theorem one_more_bit_doubles_the_work (g : Nat) : trials (g + 1) = 2 * trials g := by
  have e : trials (g + 1) = trials g * 2 := rfl
  rw [e, Nat.mul_comm]

theorem trials_are_monotone (a b : Nat) (h : a ≤ b) : trials a ≤ trials b :=
  Nat.pow_le_pow_right (by decide) h

theorem trials_at_32 : trials 32 = 4294967296 := by decide

theorem trials_at_0 : trials 0 = 1 := by decide

/-- at the shipped 32 bits the search space and the passing set are the same size -/
theorem thirty_two_bits_splits_the_word_evenly : trials 32 = passingWords 32 := by decide

/-! ## The prover's search -/

/-- try nonces from `n` upward, at most `fuel` of them -/
def search (f : Nat → Nat) (g : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n => if passes (f n) g then some n else search f g fuel (n + 1)

theorem a_found_nonce_passes (f : Nat → Nat) (g : Nat) :
    ∀ fuel n m, search f g fuel n = some m → passes (f m) g := by
  intro fuel
  induction fuel with
  | zero =>
    intro n m h
    change none = some m at h
    cases h
  | succ k ih =>
    intro n m h
    change (if passes (f n) g then some n else search f g k (n + 1)) = some m at h
    by_cases hp : passes (f n) g
    · rw [if_pos hp] at h
      cases h
      exact hp
    · rw [if_neg hp] at h
      exact ih (n + 1) m h

theorem a_found_nonce_is_in_range (f : Nat → Nat) (g : Nat) :
    ∀ fuel n m, search f g fuel n = some m → n ≤ m ∧ m < n + fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro n m h
    change none = some m at h
    cases h
  | succ k ih =>
    intro n m h
    change (if passes (f n) g then some n else search f g k (n + 1)) = some m at h
    by_cases hp : passes (f n) g
    · rw [if_pos hp] at h
      cases h
      exact ⟨Nat.le_refl _, by omega⟩
    · rw [if_neg hp] at h
      obtain ⟨a, b⟩ := ih (n + 1) m h
      exact ⟨by omega, by omega⟩

theorem no_fuel_finds_nothing (f : Nat → Nat) (g n : Nat) : search f g 0 n = none := rfl

theorem the_search_finds_the_first_pass : search (fun n => 100 - n) 58 50 0 = some 37 := by
  decide

theorem a_short_search_can_miss : search (fun n => 100 - n) 58 30 0 = none := by decide

theorem a_word_too_large_never_passes : search (fun _ => 2 ^ 63) 32 10 0 = none := by decide

theorem zero_bits_take_the_first_nonce : search (fun n => n) 0 5 3 = some 3 := by decide

/-! ## The verifier -/

/-- one comparison of the squeezed word against `2^(64 - g)` -/
def verifierChecks : Nat := 1

theorem the_verifier_checks_once : verifierChecks = 1 := rfl

/-- the prover pays `trials g` hashes, the verifier one comparison -/
theorem the_asymmetry_at_32 : trials 32 = 4294967296 * verifierChecks := by decide

/-- the bits the grind adds to the soundness budget -/
def bits (g : Nat) : Nat := g

theorem the_bits_are_the_zero_count (g : Nat) : bits g = g := rfl

theorem shipped_grind_bits : bits 32 = 32 := rfl

/-! ## Wall clock at 300M hashes a second -/

def hashRate : Nat := 300000000

/-- whole seconds of grinding at `g` bits -/
def seconds (g : Nat) : Nat := trials g / hashRate

theorem thirty_two_bits_is_under_fifteen_seconds : 2 ^ 32 / 300000000 < 15 := by decide

theorem forty_eight_bits_is_over_260_hours : 260 * 3600 * 300000000 ≤ 2 ^ 48 := by decide

theorem seconds_at_32 : seconds 32 = 14 := by decide

theorem seconds_at_36 : seconds 36 = 229 := by decide

theorem seconds_at_40 : seconds 40 = 3665 := by decide

theorem seconds_at_44 : seconds 44 = 58640 := by decide

theorem seconds_at_48 : seconds 48 = 938249 := by decide

theorem hours_at_48 : seconds 48 / 3600 = 260 := by decide

theorem below_29_bits_is_under_a_second : ∀ g < 29, seconds g = 0 := by decide

end Shield.Grind
