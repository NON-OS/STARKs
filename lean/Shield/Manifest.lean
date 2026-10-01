-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Layout

/-!
The layout as a flat list of words, in the order the identity hashes them and
the generated Solidity holds them. Nineteen fixed words, then four a FRI layer.
Mirrors proof_wire/layout/identity.rs.
-/

namespace Shield.Manifest

open Shield.Layout

structure Layer where
  base : Nat
  stride : Nat
  depth : Nat
  count : Nat
  deriving DecidableEq

/-- layers from index `m` at byte `base` inside a query, `k` of them -/
def layersFrom (p : Params) (m base : Nat) : Nat → List Layer
  | 0 => []
  | k + 1 =>
    ⟨base, layerBytes p m, friDepth p m, 2 ^ p.foldLog⟩ ::
      layersFrom p (m + 1) (base + layerBytes p m) k

/-- the layer count sits at byte zero of a query, so the first layer starts at four -/
def friLayers (p : Params) : List Layer := layersFrom p 0 4 (layers p)

def flat : List Layer → List Nat
  | [] => []
  | l :: rest => l.base :: l.stride :: l.depth :: l.count :: flat rest

def fixedWords (p : Params) : List Nat :=
  [total p, logDomain p, p.foldLog, p.digest, p.queries, p.width, p.periodic, ood p,
   2 ^ finalLog p, treeDepth p, friBase p, friStride p, consBase p, consStride p,
   sidecarBase p, sidecarStride p, permBase p, permStride p, layers p]

def words (p : Params) : List Nat := fixedWords p ++ flat (friLayers p)

/-! lengths -/

theorem layersFrom_length (p : Params) : ∀ k m b, (layersFrom p m b k).length = k := by
  intro k
  induction k with
  | zero => intro m b; rfl
  | succ k ih => intro m b; simp only [layersFrom, List.length_cons, ih]

theorem friLayers_length (p : Params) : (friLayers p).length = layers p :=
  layersFrom_length p _ _ _

theorem flat_length : ∀ l : List Layer, (flat l).length = 4 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih => simp only [flat, List.length_cons, ih]; omega

theorem fixed_is_nineteen (p : Params) : (fixedWords p).length = 19 := rfl

theorem words_length (p : Params) : (words p).length = 19 + 4 * layers p := by
  simp only [words, List.length_append, fixed_is_nineteen, flat_length, friLayers_length]

theorem shipped_words_length : (words shipped).length = 43 := by decide

/-! the layers fill the query -/

/-- bytes of layers `m` to `m + k - 1` -/
def sumFrom (p : Params) (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => layerBytes p m + sumFrom p (m + 1) k

theorem sumFrom_succ (p : Params) : ∀ k m, sumFrom p m (k + 1) = sumFrom p m k + layerBytes p (m + k) := by
  intro k
  induction k with
  | zero => intro m; simp [sumFrom]
  | succ k ih =>
    intro m
    have e : m + 1 + k = m + (k + 1) := by omega
    calc sumFrom p m (k + 1 + 1)
        = layerBytes p m + sumFrom p (m + 1) (k + 1) := rfl
      _ = layerBytes p m + (sumFrom p (m + 1) k + layerBytes p (m + 1 + k)) := by rw [ih]
      _ = sumFrom p m (k + 1) + layerBytes p (m + (k + 1)) := by
          simp only [sumFrom]; rw [e]; omega

theorem layersBytes_is_sumFrom (p : Params) : ∀ n, layersBytes p n = sumFrom p 0 n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [layersBytes]
    rw [ih, sumFrom_succ, Nat.zero_add]

def endOf (b : Nat) : List Layer → Nat
  | [] => b
  | l :: rest => endOf (l.base + l.stride) rest

theorem endOf_layersFrom (p : Params) : ∀ k m b, endOf b (layersFrom p m b k) = b + sumFrom p m k := by
  intro k
  induction k with
  | zero => intro m b; simp [layersFrom, endOf, sumFrom]
  | succ k ih =>
    intro m b
    simp only [layersFrom, endOf, sumFrom]
    rw [ih]
    omega

/-- the last layer ends exactly where the query's stride says -/
theorem the_layers_fill_the_query (p : Params) : endOf 4 (friLayers p) = friStride p := by
  unfold friLayers friStride
  rw [endOf_layersFrom, layersBytes_is_sumFrom]

/-! the shipped manifest -/

theorem shipped_layers :
    friLayers shipped =
      [⟨4, 716, 27, 4⟩, ⟨720, 668, 25, 4⟩, ⟨1388, 620, 23, 4⟩, ⟨2008, 572, 21, 4⟩,
       ⟨2580, 524, 19, 4⟩, ⟨3104, 476, 17, 4⟩] := by decide

theorem shipped_fixed_words :
    fixedWords shipped =
      [103820, 29, 2, 24, 12, 41, 119, 82, 512, 29, 9736, 3580, 52708, 1748, 73688, 1652,
       95420, 700, 6] := by decide

theorem shipped_last_layer_ends_the_query : 3104 + 476 = friStride shipped := by decide

theorem shipped_layer_count_word : (words shipped).getLast? = some 4 := by decide

/-! the identity preimage: tag, the 32-byte parameter identity, then each word big endian -/

def be64 (x : Nat) : List Nat :=
  [x / 72057594037927936 % 256, x / 281474976710656 % 256, x / 1099511627776 % 256,
   x / 4294967296 % 256, x / 16777216 % 256, x / 65536 % 256, x / 256 % 256, x % 256]

theorem be64_length (x : Nat) : (be64 x).length = 8 := rfl

/-- NOX_LAYOUT_V1 -/
def domain : List Nat := [78, 79, 88, 95, 76, 65, 89, 79, 85, 84, 95, 86, 49]

def encode : List Nat → List Nat
  | [] => []
  | w :: rest => be64 w ++ encode rest

theorem encode_length : ∀ l : List Nat, (encode l).length = 8 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons w rest ih => simp only [encode, List.length_append, be64_length, List.length_cons, ih]; omega

def preimage (paramsId : List Nat) (p : Params) : List Nat :=
  domain ++ paramsId ++ encode (words p)

theorem preimage_length (paramsId : List Nat) (h : paramsId.length = 32) (p : Params) :
    (preimage paramsId p).length = 45 + 8 * (19 + 4 * layers p) := by
  simp only [preimage, List.length_append, encode_length, words_length, h]
  rfl

theorem shipped_preimage_is_389_bytes (paramsId : List Nat) (h : paramsId.length = 32) :
    (preimage paramsId shipped).length = 389 := by
  rw [preimage_length paramsId h]
  decide

/-- big endian: the most significant byte first, so a word below 2^56 has a leading zero -/
theorem be64_of_small (x : Nat) (h : x < 72057594037927936) : (be64 x).head? = some 0 := by
  simp only [be64, List.head?]
  rw [Nat.div_eq_of_lt h]

theorem be64_of_total : be64 112436 = [0, 0, 0, 0, 0, 1, 183, 52] := by decide

theorem be64_and_le64_are_reverses : (be64 112436).reverse = [52, 183, 1, 0, 0, 0, 0, 0] := by
  decide

/-- a different query count, width or fold is a different word list -/
theorem the_geometry_moves_the_words :
    words { shipped with queries := 13 } ≠ words shipped ∧
    words { shipped with width := 42 } ≠ words shipped ∧
    words { shipped with foldLog := 1 } ≠ words shipped := by decide

theorem encode_injective_on_length : ∀ a b : List Nat, encode a = encode b → a.length = b.length := by
  intro a b h
  have := congrArg List.length h
  rw [encode_length, encode_length] at this
  omega

/-- two parameter sets with a different layer count have preimages of different lengths -/
theorem a_different_layer_count_is_a_different_preimage (paramsId : List Nat)
    (h : paramsId.length = 32) (p q : Params) (hl : layers p ≠ layers q) :
    preimage paramsId p ≠ preimage paramsId q := by
  intro heq
  have := congrArg List.length heq
  rw [preimage_length paramsId h, preimage_length paramsId h] at this
  omega

end Shield.Manifest
