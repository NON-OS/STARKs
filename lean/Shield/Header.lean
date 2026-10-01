-- NONOS Operating System (AGPL-3.0-or-later)
/-!
The forty byte header an artifact carries: magic, format, protocol, and a
hash of the parameter set. The parameter set has fourteen fields and its
preimage starts with a domain tag. Mirrors proof_wire/header.rs.
-/

namespace Shield.Header

def magic : List Nat := [78, 79, 88, 80]
/-- 4: the DEEP value opens in FRI layer zero.
5: the consistency check runs at FRI's positions and reads FRI's layer-zero opening; the DEEP
root and the per-query DEEP opening leave the wire. -/
def formatVersion : Nat := 5
def protocolVersion : Nat := 1

/-- 4 + 2 + 2 + 32 -/
def headerBytes : Nat := 40

theorem magic_reads_NOXP : magic = [0x4E, 0x4F, 0x58, 0x50] := by decide

theorem header_is_forty_bytes : magic.length + 2 + 2 + 32 = headerBytes := by decide

/-- where the chain reads: permRoot at 40, regionWidth at 64 with 24-byte digests -/
theorem the_offsets_the_chain_reads : headerBytes = 40 ∧ headerBytes + 24 = 64 := by decide

structure Header where
  format : Nat
  protocol : Nat
  params : List Nat
  deriving DecidableEq

/-- fail closed: the format, the protocol, and the exact parameter identity -/
def accepts (expected : List Nat) (h : Header) : Prop :=
  h.format = formatVersion ∧ h.protocol = protocolVersion ∧ h.params = expected

instance (e : List Nat) (h : Header) : Decidable (accepts e h) := by
  unfold accepts; infer_instance

theorem a_foreign_format_is_refused (e p : List Nat) (f : Nat) (hf : f ≠ formatVersion) :
    ¬ accepts e ⟨f, protocolVersion, p⟩ := fun h => hf h.1

theorem a_foreign_protocol_is_refused (e p : List Nat) (v : Nat) (hv : v ≠ protocolVersion) :
    ¬ accepts e ⟨formatVersion, v, p⟩ := fun h => hv h.2.1

theorem a_wrong_parameter_set_is_refused (e p : List Nat) (hp : p ≠ e) :
    ¬ accepts e ⟨formatVersion, protocolVersion, p⟩ := fun h => hp h.2.2

theorem accepted_means_every_identity_matched (e : List Nat) (h : Header) (ha : accepts e h) :
    h = ⟨formatVersion, protocolVersion, e⟩ := by
  obtain ⟨h1, h2, h3⟩ := ha
  cases h
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-! little endian words -/

def le32 (x : Nat) : List Nat :=
  [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256]

def de32 : List Nat → Nat
  | [a, b, c, d] => a + 256 * b + 65536 * c + 16777216 * d
  | _ => 0

theorem le32_length (x : Nat) : (le32 x).length = 4 := rfl

theorem de32_le32 (x : Nat) (h : x < 4294967296) : de32 (le32 x) = x := by
  simp only [le32, de32]
  have h0 := Nat.div_add_mod x 256
  have h1 := Nat.div_add_mod (x / 256) 256
  have h2 := Nat.div_add_mod (x / 65536) 256
  have e1 : x / 256 / 256 = x / 65536 := Nat.div_div_eq_div_mul x 256 256
  have e2 : x / 65536 / 256 = x / 16777216 := Nat.div_div_eq_div_mul x 65536 256
  have h3 : x / 16777216 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega
  rw [e1] at h1
  rw [e2] at h2
  rw [Nat.mod_eq_of_lt h3]
  omega

theorem le32_injective (x y : Nat) (hx : x < 4294967296) (hy : y < 4294967296)
    (h : le32 x = le32 y) : x = y := by
  have := congrArg de32 h
  rw [de32_le32 x hx, de32_le32 y hy] at this
  exact this

def le64 (x : Nat) : List Nat :=
  [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256,
   x / 4294967296 % 256, x / 1099511627776 % 256, x / 281474976710656 % 256,
   x / 72057594037927936 % 256]

def de64 : List Nat → Nat
  | [a, b, c, d, e, f, g, h] =>
    a + 256 * b + 65536 * c + 16777216 * d + 4294967296 * e + 1099511627776 * f +
      281474976710656 * g + 72057594037927936 * h
  | _ => 0

theorem le64_length (x : Nat) : (le64 x).length = 8 := rfl

theorem de64_le64 (x : Nat) (h : x < 18446744073709551616) : de64 (le64 x) = x := by
  simp only [le64, de64]
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

theorem le64_injective (x y : Nat) (hx : x < 18446744073709551616)
    (hy : y < 18446744073709551616) (h : le64 x = le64 y) : x = y := by
  have := congrArg de64 h
  rw [de64_le64 x hx, de64_le64 y hy] at this
  exact this

/-! the parameter set -/

structure ParamSet where
  nQueries : Nat
  grindBits : Nat
  extraBlowupBits : Nat
  friFoldLog : Nat
  friStopLog : Nat
  digestBytes : Nat
  traceWidth : Nat
  nPeriodic : Nat
  logTraceLen : Nat
  constraintDegree : Nat
  windowSize : Nat
  numTransition : Nat
  nBoundary : Nat
  cosetShift : Nat
  deriving DecidableEq

/-- NOX_PARAMS_V1 -/
def domain : List Nat := [78, 79, 88, 95, 80, 65, 82, 65, 77, 83, 95, 86, 49]

theorem domain_is_thirteen_bytes : domain.length = 13 := by decide

/-- the tag, thirteen u32 little endian, the shift as a u64 -/
def preimage (p : ParamSet) : List Nat :=
  domain ++ le32 p.nQueries ++ le32 p.grindBits ++ le32 p.extraBlowupBits ++
    le32 p.friFoldLog ++ le32 p.friStopLog ++ le32 p.digestBytes ++ le32 p.traceWidth ++
    le32 p.nPeriodic ++ le32 p.logTraceLen ++ le32 p.constraintDegree ++ le32 p.windowSize ++
    le32 p.numTransition ++ le32 p.nBoundary ++ le64 p.cosetShift

theorem preimage_length (p : ParamSet) : (preimage p).length = 73 := by
  simp [preimage, domain, le32, le64]

theorem the_tag_leads (p : ParamSet) : (preimage p).take 13 = domain := by
  simp [preimage, domain]

/-- the shipped settlement point, boundaries recovered from the prover's z -/
def shipped : ParamSet :=
  { nQueries := 12, grindBits := 32, extraBlowupBits := 7, friFoldLog := 2, friStopLog := 8,
    digestBytes := 24, traceWidth := 41, nPeriodic := 119, logTraceLen := 18,
    constraintDegree := 8, windowSize := 2, numTransition := 37, nBoundary := 723,
    cosetShift := 7 }

theorem shipped_coefficients : shipped.numTransition + shipped.nBoundary = 760 := by decide

/-- every field moves the preimage: the smallest change each admits -/
theorem every_field_moves_the_preimage :
    preimage { shipped with nQueries := 13 } ≠ preimage shipped ∧
    preimage { shipped with grindBits := 33 } ≠ preimage shipped ∧
    preimage { shipped with extraBlowupBits := 8 } ≠ preimage shipped ∧
    preimage { shipped with friFoldLog := 3 } ≠ preimage shipped ∧
    preimage { shipped with friStopLog := 9 } ≠ preimage shipped ∧
    preimage { shipped with digestBytes := 25 } ≠ preimage shipped ∧
    preimage { shipped with traceWidth := 42 } ≠ preimage shipped := by decide

theorem every_field_moves_the_preimage_continued :
    preimage { shipped with nPeriodic := 120 } ≠ preimage shipped ∧
    preimage { shipped with logTraceLen := 19 } ≠ preimage shipped ∧
    preimage { shipped with constraintDegree := 9 } ≠ preimage shipped ∧
    preimage { shipped with windowSize := 3 } ≠ preimage shipped ∧
    preimage { shipped with numTransition := 38 } ≠ preimage shipped ∧
    preimage { shipped with nBoundary := 724 } ≠ preimage shipped ∧
    preimage { shipped with cosetShift := 8 } ≠ preimage shipped := by decide

/-- the wrong boundary count that sat in the fixture for a day -/
theorem a_guessed_boundary_count_is_a_different_identity :
    preimage { shipped with nBoundary := 3 } ≠ preimage shipped := by decide

/-- the untagged encoding is not a suffix-free identity: it is the preimage with the tag gone -/
theorem the_tag_is_what_separates_the_encoding (p : ParamSet) :
    (preimage p).drop 13 ≠ preimage p := by
  intro h
  have := congrArg List.length h
  rw [List.length_drop, preimage_length] at this
  omega

end Shield.Header
