-- NONOS Operating System (AGPL-3.0-or-later)

import Shield.Read.Shape

/-!
`shieldread FILE [PARAMS]`: read a settlement artifact with the Lean reader,
report its sections, check it against the shipped layout, and run the reader
over corruptions of it that must each be refused. A file that starts with the
header is read as format 4 against the parameter identity `PARAMS` (hex); one
that does not is read as a format 3 legacy file.
-/

open Shield.Read Shield.Layout

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x.toNat < 16 then "0" else "") ++ (Nat.toDigits 16 x.toNat).asString) ""

/-- overwrite `v` little-endian at `i`, `n` bytes -/
def poke (b : ByteArray) (i n v : Nat) : ByteArray := Id.run do
  let mut c := b
  let mut x := v
  for k in [0:n] do
    c := c.set! (i + k) (UInt8.ofNat (x % 256))
    x := x / 256
  return c

def unhex (s : String) : List UInt8 :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => UInt8.ofNat (16 * d (cs.getD (2 * i) '0') + d (cs.getD (2 * i + 1) '0'))

def verdict (read : ByteArray → Option Rounds) (name : String) (b : ByteArray) : IO Bool := do
  let refused := (read b).isNone
  IO.println s!"  {name}: {if refused then "refused" else "ACCEPTED"}"
  return refused

def main (args : List String) : IO UInt32 := do
  let some file := args.head? | IO.eprintln "usage: shieldread FILE"; return 2
  let b ← IO.FS.readBinFile file
  IO.println s!"bytes {b.size}"
  let four := b.size ≥ headerBytes && magicOf b == magicWord
  let expect := match args.tail.head? with
    | some h => unhex h
    | none => paramsOf b
  if four then
    IO.println s!"header: format {formatOf b}, protocol {protocolOf b}, params {hex (b.extract 8 40)}"
    if args.tail.isEmpty then IO.println "  params not pinned on the command line; read against the file's own"
  let read : ByteArray → Option Rounds := if four then (readFour · expect) else readLegacy
  let at0 := if four then headerBytes else 0
  let layout := if four then shippedFour else shippedThree
  let some r := read b | IO.println "refused"; return 1
  let e := r.ext
  IO.println s!"perm root  {hex r.permRoot}"
  IO.println s!"trace root {hex e.traceRoot}"
  IO.println s!"comp root  {hex e.compRoot}"
  IO.println s!"deep root  {hex e.deepRoot}"
  IO.println s!"fri root 0 {(e.fri.roots.head?.map hex).getD "-"}"
  IO.println s!"region width {r.regionWidth}, ood {e.ood.length}, fri roots {e.fri.roots.length}, final {e.fri.final.length}"
  IO.println s!"fri queries {e.fri.queries.length}, base queries {e.queries.length}, periodic {r.periodicZ.length}"
  IO.println s!"nonce {e.fri.nonce}"
  IO.println s!"size by contents {at0 + roundsW r}, by layout {at0 + total layout}"
  let fits := fitsB layout r
  IO.println s!"fits the shipped layout, format {layout.format}: {fits}"
  if four then
    let tied := match e.fri.roots.head? with
      | some r0 => r0.toList == e.deepRoot.toList
      | none => false
    IO.println s!"deep root is FRI's first root: {tied}"
  IO.println "corruptions:"
  let head := at0 + 24 + 4 + 3 * 24
  let oodAt := head + 4
  let v := verdict read
  let a ← v "one byte appended" (b.push 0)
  let c ← v "last byte cut" (b.extract 0 (b.size - 1))
  let d ← v "first frame word set to p" (poke b oodAt 8 p)
  let f ← v "frame count one higher" (poke b head 4 (e.ood.length + 1))
  let g ← v "fri query count one lower" (poke b (at0 + friBase layout) 4 (e.fri.queries.length - 1))
  let hs ← if four then do
      let x ← v "format set to 3" (poke b 4 2 3)
      let y ← v "protocol set to 2" (poke b 6 2 2)
      let z ← v "one params byte flipped" (poke b 8 1 ((b.get! 8).toNat ^^^ 1))
      pure (x && y && z)
    else pure true
  let ok := fits && at0 + roundsW r == b.size && a && c && d && f && g && hs
  IO.println (if ok then "OK" else "FAIL")
  return (if ok then 0 else 1)
