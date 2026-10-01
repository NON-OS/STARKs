-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Read.Bytes

/-!
The settlement artifact, read section by section in the order
`read_body` and `read_proof` read it, and the size each section has on the
wire as a function of what was read.

The base half is `deserialize_proof_ext_at`: three roots, the out-of-domain
frame, the FRI roots and final polynomial, the FRI queries, the grind nonce,
and the base queries. The sidecar follows: the permutation root and the region
width come first in the file, the periodic claims and one opening per base
query after the base half, then one permutation path per base query. The query
count is the base half's own and is not repeated on the wire. Nothing may
follow the last path.
-/

namespace Shield.Read

/-- a quadratic extension element: two canonical base words -/
abbrev Fp2 := Nat × Nat

/-- one FRI layer inside a query: four values under one leaf, and the leaf's path -/
structure Layer where
  v : List Fp2
  path : List ByteArray

/-- one base query -/
structure Query where
  deep : Fp2
  /-- format 4: the other values of the DEEP value's layer-zero leaf; format 3: none -/
  deepOthers : List Fp2
  deepPath : List ByteArray
  trace : List Nat
  tracePath : List ByteArray
  comp : Fp2
  compPath : List ByteArray

structure Fri where
  roots : List ByteArray
  final : List Fp2
  queries : List (List Layer)
  nonce : Nat

/-- the base half -/
structure Ext where
  traceRoot : ByteArray
  compRoot : ByteArray
  deepRoot : ByteArray
  ood : List Fp2
  fri : Fri
  queries : List Query

/-- a periodic row and its path -/
structure Opening where
  row : List Nat
  path : List ByteArray

/-- the whole artifact -/
structure Rounds where
  permRoot : ByteArray
  regionWidth : Nat
  ext : Ext
  periodicZ : List Fp2
  openings : List Opening
  permPaths : List (List ByteArray)

/-! ## Readers -/

def readLayer (b : ByteArray) (i : Nat) : Step Layer :=
  andThen (many (fp2 b) 4 i) fun v i =>
  andThen (counted b (digest b) i) fun path i =>
  some (⟨v, path⟩, i)

def readFriQuery (b : ByteArray) (i : Nat) : Step (List Layer) := counted b (readLayer b) i

/-- a base query; `k` is how many other values of the DEEP leaf follow the DEEP value -/
def readQuery (b : ByteArray) (k : Nat) (i : Nat) : Step Query :=
  andThen (fp2 b i) fun deep i =>
  andThen (many (fp2 b) k i) fun deepOthers i =>
  andThen (counted b (digest b) i) fun deepPath i =>
  andThen (counted b (fp b) i) fun trace i =>
  andThen (counted b (digest b) i) fun tracePath i =>
  andThen (fp2 b i) fun comp i =>
  andThen (counted b (digest b) i) fun compPath i =>
  some (⟨deep, deepOthers, deepPath, trace, tracePath, comp, compPath⟩, i)

def readFri (b : ByteArray) (i : Nat) : Step Fri :=
  andThen (counted b (digest b) i) fun roots i =>
  andThen (counted b (fp2 b) i) fun final i =>
  andThen (counted b (readFriQuery b) i) fun queries i =>
  andThen (u64 b i) fun nonce i =>
  some (⟨roots, final, queries, nonce⟩, i)

def readExt (b : ByteArray) (k : Nat) (i : Nat) : Step Ext :=
  andThen (digest b i) fun traceRoot i =>
  andThen (digest b i) fun compRoot i =>
  andThen (digest b i) fun deepRoot i =>
  andThen (counted b (fp2 b) i) fun ood i =>
  andThen (readFri b i) fun fri i =>
  andThen (counted b (readQuery b k) i) fun queries i =>
  some (⟨traceRoot, compRoot, deepRoot, ood, fri, queries⟩, i)

def readOpening (b : ByteArray) (n : Nat) (i : Nat) : Step Opening :=
  andThen (many (fp b) n i) fun row i =>
  andThen (path b i) fun path i =>
  some (⟨row, path⟩, i)

/-- the body after the header, from `i`; refused unless it ends on the last byte -/
def readBody (b : ByteArray) (k : Nat) (i : Nat) : Step Rounds :=
  andThen (digest b i) fun permRoot i =>
  andThen (u32 b i) fun regionWidth i =>
  andThen (readExt b k i) fun ext i =>
  andThen (capped b (fp2 b) 16 i) fun periodicZ i =>
  andThen (many (readOpening b periodicZ.length) ext.queries.length i) fun openings i =>
  andThen (many (path b) ext.queries.length i) fun permPaths i =>
  if i = b.size then some (⟨permRoot, regionWidth, ext, periodicZ, openings, permPaths⟩, i)
  else none

/-- an artifact written before the header, format 3: the body from byte zero -/
def readLegacy (b : ByteArray) : Option Rounds := (readBody b 0 0).map Prod.fst

/-! ## The header -/

def headerBytes : Nat := 40

/-- `NOXP` as a little-endian word -/
def magicWord : Nat := 0x50584F4E

def magicOf (b : ByteArray) : Nat := le b 0 4
def formatOf (b : ByteArray) : Nat := le b 4 2
def protocolOf (b : ByteArray) : Nat := le b 6 2
def paramsOf (b : ByteArray) : List UInt8 := (b.extract 8 headerBytes).toList

/-- the header this build serves: format 4, protocol 1, and the parameter identity the caller
was deployed with. Checked before a byte of the body is read. -/
def headerOk (b : ByteArray) (expect : List UInt8) : Bool :=
  decide (headerBytes ≤ b.size) && magicOf b == magicWord && formatOf b == 4 &&
    protocolOf b == 1 && paramsOf b == expect

/-- a format 4 artifact: the header, then the body with three other values a DEEP leaf -/
def readFour (b : ByteArray) (expect : List UInt8) : Option Rounds :=
  if headerOk b expect then (readBody b 3 headerBytes).map Prod.fst else none

/-! ## Sizes -/

def layerW (l : Layer) : Nat := 16 * l.v.length + pathW l.path

def friQueryW (ls : List Layer) : Nat := 4 + sumW layerW ls

def queryW (q : Query) : Nat :=
  16 + 16 * q.deepOthers.length + pathW q.deepPath + (4 + 8 * q.trace.length) +
    pathW q.tracePath + 16 + pathW q.compPath

def friW (f : Fri) : Nat :=
  (4 + digestBytes * f.roots.length) + (4 + 16 * f.final.length) +
    (4 + sumW friQueryW f.queries) + 8

def extW (e : Ext) : Nat :=
  3 * digestBytes + (4 + 16 * e.ood.length) + friW e.fri + (4 + sumW queryW e.queries)

def openingW (o : Opening) : Nat := 8 * o.row.length + pathW o.path

def roundsW (r : Rounds) : Nat :=
  digestBytes + 4 + extW r.ext + (4 + 16 * r.periodicZ.length) + sumW openingW r.openings +
    sumW pathW r.permPaths

end Shield.Read
