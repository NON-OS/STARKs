-- NONOS Operating System (AGPL-3.0-or-later)
/-!
How the on-chain reader takes field elements and digests out of 32-byte words,
following StarkProofReader.sol and StarkMerkle.trunc. A word is a `Nat` below
`2^256`, an element is eight little-endian bytes read from the top of a word,
and a digest is the top 24 bytes with the low eight zeroed.
-/

namespace Shield.Canon

/-! ## Words -/

def word : Nat := 2 ^ 256

def mask64 : Nat := 2 ^ 64 - 1

/-- the `shr(192, w)` read -/
def top64 (w : Nat) : Nat := w / 2 ^ 192

/-- the `and(w, mask64)` read -/
def low64 (w : Nat) : Nat := w % 2 ^ 64

theorem two_to_64_value : (2 : Nat) ^ 64 = 18446744073709551616 := by decide

theorem mask64_value : mask64 = 18446744073709551615 := by decide

theorem a_word_splits_at_192 : (2 : Nat) ^ 64 * 2 ^ 192 = word := by decide

theorem a_word_is_four_lanes : (2 : Nat) ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 = word := by decide

theorem top64_of_a_word_is_below_two_to_64 (w : Nat) (h : w < word) : top64 w < 2 ^ 64 := by
  unfold top64
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 192), a_word_splits_at_192]
  exact h

theorem low64_is_below_two_to_64 (w : Nat) : low64 w < 2 ^ 64 :=
  Nat.mod_lt w (by decide : 2 ^ 64 > 0)

theorem low64_fits_the_mask (w : Nat) : low64 w ≤ mask64 := by
  have h := low64_is_below_two_to_64 w
  unfold mask64
  omega

theorem top64_reads_back_a_shifted_value (x : Nat) : top64 (x * 2 ^ 192) = x := by
  unfold top64
  exact Nat.mul_div_cancel x (by decide : 0 < 2 ^ 192)

theorem a_shifted_element_is_a_word (x : Nat) (h : x < 2 ^ 64) : x * 2 ^ 192 < word := by
  have hd : x * 2 ^ 192 / 2 ^ 192 < 2 ^ 64 := by
    rw [Nat.mul_div_cancel x (by decide : 0 < 2 ^ 192)]
    exact h
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 192)] at hd
  rw [← a_word_splits_at_192]
  exact hd

/-- the top read and the remainder below it rebuild the word -/
theorem top64_and_the_rest_rebuild_the_word (w : Nat) :
    top64 w * 2 ^ 192 + w % 2 ^ 192 = w := by
  unfold top64
  rw [Nat.mul_comm]
  exact Nat.div_add_mod w (2 ^ 192)

theorem low64_of_a_small_value (x : Nat) (h : x < 2 ^ 64) : low64 x = x := by
  unfold low64
  exact Nat.mod_eq_of_lt h

theorem low64_is_idempotent (w : Nat) : low64 (low64 w) = low64 w := by
  unfold low64
  exact Nat.mod_mod w (2 ^ 64)

theorem top64_of_the_full_word : top64 (2 ^ 256 - 1) = mask64 := by decide

theorem low64_of_the_full_word : low64 (2 ^ 256 - 1) = mask64 := by decide

theorem top64_of_zero : top64 0 = 0 := by decide

/-! ## Bytes -/

/-- eight little-endian bytes, as Header.le64 -/
def bytesLE (x : Nat) : List Nat :=
  [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256,
   x / 4294967296 % 256, x / 1099511627776 % 256, x / 281474976710656 % 256,
   x / 72057594037927936 % 256]

def readLE : List Nat → Nat
  | [a, b, c, d, e, f, g, h] =>
    a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * e + 1099511627776 * f +
      281474976710656 * g + 72057594037927936 * h
  | _ => 0

def bytesBE (x : Nat) : List Nat := (bytesLE x).reverse

theorem bytesLE_length (x : Nat) : (bytesLE x).length = 8 := rfl

theorem bytesBE_length (x : Nat) : (bytesBE x).length = 8 := by
  unfold bytesBE
  rw [List.length_reverse, bytesLE_length]

theorem bytesBE_reversed_is_bytesLE (x : Nat) : (bytesBE x).reverse = bytesLE x := by
  unfold bytesBE
  exact List.reverse_reverse (bytesLE x)

theorem readLE_bytesLE (x : Nat) (h : x < 18446744073709551616) : readLE (bytesLE x) = x := by
  simp only [bytesLE, readLE]
  have h0 := Nat.div_add_mod x 256
  have h1 := Nat.div_add_mod (x / 256) 256
  have h2 := Nat.div_add_mod (x / 65536) 256
  have h3 := Nat.div_add_mod (x / 16777216) 256
  have h4 := Nat.div_add_mod (x / 4294967296) 256
  have h5 := Nat.div_add_mod (x / 1099511627776) 256
  have h6 := Nat.div_add_mod (x / 281474976710656) 256
  have e1 : x / 256 / 256 = x / 65536 := Nat.div_div_eq_div_mul x 256 256
  have e2 : x / 65536 / 256 = x / 16777216 := Nat.div_div_eq_div_mul x 65536 256
  have e3 : x / 16777216 / 256 = x / 4294967296 := Nat.div_div_eq_div_mul x 16777216 256
  have e4 : x / 4294967296 / 256 = x / 1099511627776 := Nat.div_div_eq_div_mul x 4294967296 256
  have e5 : x / 1099511627776 / 256 = x / 281474976710656 :=
    Nat.div_div_eq_div_mul x 1099511627776 256
  have e6 : x / 281474976710656 / 256 = x / 72057594037927936 :=
    Nat.div_div_eq_div_mul x 281474976710656 256
  have h7 : x / 72057594037927936 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  rw [e6] at h6
  rw [Nat.mod_eq_of_lt h7]
  omega

theorem bytesLE_injective (x y : Nat) (hx : x < 18446744073709551616)
    (hy : y < 18446744073709551616) (h : bytesLE x = bytesLE y) : x = y := by
  have := congrArg readLE h
  rw [readLE_bytesLE x hx, readLE_bytesLE y hy] at this
  exact this

theorem bytesBE_injective (x y : Nat) (hx : x < 18446744073709551616)
    (hy : y < 18446744073709551616) (h : bytesBE x = bytesBE y) : x = y := by
  have e := congrArg List.reverse h
  rw [bytesBE_reversed_is_bytesLE, bytesBE_reversed_is_bytesLE] at e
  exact bytesLE_injective x y hx hy e

theorem bytesLE_of_a_sample : bytesLE 112436 = [52, 183, 1, 0, 0, 0, 0, 0] := by decide

theorem bytesBE_of_a_sample : bytesBE 112436 = [0, 0, 0, 0, 0, 1, 183, 52] := by decide

theorem bytesBE_of_one : bytesBE 1 = [0, 0, 0, 0, 0, 0, 0, 1] := by decide

/-! ## Byte swap -/

/-- the value whose little-endian bytes are the big-endian bytes of `x` -/
def swap64 (x : Nat) : Nat := readLE (bytesBE x)

theorem swap64_reads_the_reversed_bytes (x : Nat) : swap64 x = readLE (bytesLE x).reverse := rfl

theorem swap64_of_one : swap64 1 = 72057594037927936 := by decide

theorem swap64_of_the_top_byte : swap64 72057594037927936 = 1 := by decide

theorem swap64_of_a_sample : swap64 112436 = 3798505910221930496 := by decide

theorem swap64_twice_on_a_sample : swap64 (swap64 112436) = 112436 := by decide

theorem swap64_of_zero : swap64 0 = 0 := by decide

theorem swap64_of_all_ones : swap64 18446744073709551615 = 18446744073709551615 := by decide

theorem swap64_twice_on_the_prime :
    swap64 (swap64 18446744069414584321) = 18446744069414584321 := by
  decide

/-- an element as the reader takes it: the top eight bytes, little endian -/
def element (w : Nat) : Nat := swap64 (top64 w)

theorem element_of_seven_in_the_first_byte : element (7 * 2 ^ 248) = 7 := by decide

theorem element_of_a_placed_sample : element (swap64 112436 * 2 ^ 192) = 112436 := by decide

theorem element_ignores_the_low_bytes : element (7 * 2 ^ 248 + 2 ^ 192 - 1) = 7 := by decide

theorem element_reads_the_shifted_swap (x : Nat) : element (x * 2 ^ 192) = swap64 x := by
  unfold element
  rw [top64_reads_back_a_shifted_value]

/-! ## Digest truncation -/

/-- keep the top 24 bytes of a 32-byte word and zero the low eight -/
def trunc (h : Nat) : Nat := h / 2 ^ 64 * 2 ^ 64

theorem trunc_clears_the_low_bytes (h : Nat) : trunc h % 2 ^ 64 = 0 := by
  unfold trunc
  exact Nat.mul_mod_left (h / 2 ^ 64) (2 ^ 64)

theorem trunc_low64_is_zero (h : Nat) : low64 (trunc h) = 0 := trunc_clears_the_low_bytes h

theorem trunc_is_idempotent (h : Nat) : trunc (trunc h) = trunc h := by
  unfold trunc
  rw [Nat.mul_div_cancel (h / 2 ^ 64) (by decide : 0 < 2 ^ 64)]

theorem trunc_is_below (h : Nat) : trunc h ≤ h := Nat.div_mul_le_self h (2 ^ 64)

theorem trunc_and_low64_rebuild_the_word (h : Nat) : trunc h + low64 h = h := by
  unfold trunc low64
  rw [Nat.mul_comm]
  exact Nat.div_add_mod h (2 ^ 64)

theorem agreeing_top_bytes_truncate_equally (h g : Nat) (e : h / 2 ^ 64 = g / 2 ^ 64) :
    trunc h = trunc g := by
  unfold trunc
  rw [e]

theorem equal_truncations_agree_on_the_top_bytes (h g : Nat) (e : trunc h = trunc g) :
    h / 2 ^ 64 = g / 2 ^ 64 :=
  calc h / 2 ^ 64 = trunc h / 2 ^ 64 := (Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 64)).symm
    _ = trunc g / 2 ^ 64 := by rw [e]
    _ = g / 2 ^ 64 := Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 64)

theorem trunc_of_the_full_word : trunc (2 ^ 256 - 1) = 2 ^ 256 - 2 ^ 64 := by decide

theorem trunc_of_a_low_value : trunc (2 ^ 64 - 1) = 0 := by decide

/-- two words differing only in the low eight bytes are the same digest -/
theorem the_low_bytes_are_invisible : trunc (2 ^ 200 + 5) = trunc (2 ^ 200 + 2 ^ 63) := by decide

/-! ## Canonical elements -/

def p : Nat := 18446744069414584321

theorem p_is_goldilocks : p = 2 ^ 64 - 2 ^ 32 + 1 := by decide

def canonical (x : Nat) : Prop := x < p

instance (x : Nat) : Decidable (canonical x) := by
  unfold canonical; infer_instance

theorem the_largest_element_is_canonical : canonical (p - 1) := by decide

theorem the_modulus_is_not_canonical : ¬ canonical p := by decide

theorem all_ones_is_not_canonical : ¬ canonical (2 ^ 64 - 1) := by decide

theorem zero_is_canonical : canonical 0 := by decide

theorem a_canonical_element_fits_eight_bytes (x : Nat) (h : canonical x) : x < 2 ^ 64 :=
  Nat.lt_trans h (by decide)

theorem a_canonical_element_survives_the_mask (x : Nat) (h : canonical x) : low64 x = x :=
  low64_of_a_small_value x (a_canonical_element_fits_eight_bytes x h)

theorem a_canonical_element_round_trips_its_bytes (x : Nat) (h : canonical x) :
    readLE (bytesLE x) = x := by
  have hx := a_canonical_element_fits_eight_bytes x h
  rw [two_to_64_value] at hx
  exact readLE_bytesLE x hx

theorem non_canonical_count : 2 ^ 64 - p = 4294967295 := by decide

theorem non_canonical_is_rare : 4294967295 * 2 ^ 32 < 2 ^ 64 := by decide

/-- one subtraction of `p` brings any non-canonical 64-bit value into range -/
theorem one_subtraction_canonicalizes (x : Nat) (hx : x < 18446744073709551616)
    (hn : ¬ canonical x) : canonical (x - p) := by
  have hp : p = 18446744069414584321 := rfl
  unfold canonical at hn ⊢
  rw [hp] at hn ⊢
  omega

theorem the_non_canonical_band :
    ∀ x, x < 18446744073709551616 → ¬ canonical x → x - p < 4294967295 := by
  intro x hx hn
  have hp : p = 18446744069414584321 := rfl
  unfold canonical at hn
  rw [hp] at hn ⊢
  omega

theorem a_canonical_reader_refuses_all_ones : decide (canonical (2 ^ 64 - 1)) = false := by
  decide

/-! ## Digest sizes -/

theorem digest_bytes_are_three_elements : 24 = 3 * 8 := by decide

theorem a_digest_has_2_192_values : (2 : Nat) ^ (8 * 24) = 2 ^ 192 := by decide

theorem collision_resistance_is_half : (2 : Nat) ^ 96 * 2 ^ 96 = 2 ^ 192 := by decide

theorem a_full_word_is_eight_more_bytes : (2 : Nat) ^ (8 * 32) = word := by decide

theorem truncation_drops_64_bits : (2 : Nat) ^ 192 * 2 ^ 64 = word := by decide

end Shield.Canon
