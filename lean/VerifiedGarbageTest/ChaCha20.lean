import Lean.Elab.Command
import VerifiedGarbage.Spec.ChaCha20

/-!
# Known-answer tests for the ChaCha20 specification

The test vectors of RFC 8439, Appendix A.1 (the block function) and A.2
(encryption), read from the vendored RFC `vectors/rfc8439/rfc8439.txt` (see
`vectors/sources.toml`) when this file is built and checked against
`VG.Spec.ChaCha20.chacha20Block`, `VG.Spec.ChaCha20.encrypt` and
`VG.Spec.ChaCha20.keystream`, so that a transcription error in the spec fails
the build.
-/

namespace VG.Test.ChaCha20

open Lean Elab Command Spec.ChaCha20

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes of the hex pairs at the start of `cs`, separated by single
spaces and ending at two spaces or the end of the line. -/
def hexBytes : List Char → Option (List Byte)
  | h :: l :: ' ' :: ' ' :: _ | [h, l] => do
    return [BitVec.ofNat 8 (16 * (← hexDigit h) + (← hexDigit l))]
  | h :: l :: ' ' :: more => do
    return BitVec.ofNat 8 (16 * (← hexDigit h) + (← hexDigit l)) :: (← hexBytes more)
  | _ => none

/-- The bytes of a line of an RFC hex dump, `  016  bd d2 19 …  ASCII`: an
offset of three decimal digits, two spaces, then up to 16 bytes in hex
separated by single spaces, then two spaces and the ASCII rendering (which is
ignored). `none` if the line is not a hex-dump line. -/
def dumpLine (l : String) : Option (List Byte) :=
  match l.toList.dropWhile (· == ' ') with
  | d₁ :: d₂ :: d₃ :: ' ' :: ' ' :: rest =>
    if d₁.isDigit && d₂.isDigit && d₃.isDigit then hexBytes rest else none
  | _ => none

/-- One test vector of Appendix A.1 or A.2: the hex dumps under each label,
and the block counter. -/
structure Vector where
  fields : List (String × List Byte) := []
  counter : Option Nat := none

def Vector.get (v : Vector) (label : String) : Except String (List Byte) :=
  match v.fields.find? (·.1 == label) with
  | some (_, bs) => pure bs
  | none => throw s!"no `{label}`"

/-- The labels of the hex dumps in Appendix A.1 and A.2. -/
def labels : List String := ["Key:", "Nonce:", "Keystream:", "Plaintext:", "Ciphertext:"]

/-- The test vectors of the section of the RFC starting at the line that
begins with `heading` and ending before the one that begins with `next`
(section headings are not indented, which tells them apart from the table of
contents). Page footers and headers between the lines of a hex dump are
skipped. `labels` are the labels of the hex dumps. -/
def vectorsIn (text heading next : String) (labels : List String := labels) :
    Except String (List Vector) := do
  let lines := text.splitOn "\n"
  let lines := (lines.dropWhile (!·.startsWith heading)).drop 1
  let lines := lines.takeWhile (!·.startsWith next)
  let mut vs : Array Vector := #[]
  let mut cur : Option Vector := none
  let mut label : Option String := none
  for l in lines do
    let t := String.ofList (l.toList.dropWhile (· == ' '))
    if t.startsWith "Test Vector #" then
      if let some v := cur then vs := vs.push v
      cur := some {}
      label := none
    else if labels.contains t then
      let some v := cur | throw s!"`{t}` outside a test vector"
      cur := some { v with fields := v.fields ++ [(t, [])] }
      label := some t
    else if t.startsWith "Block Counter = " || t.startsWith "Initial Block Counter = " then
      let some v := cur | throw s!"`{t}` outside a test vector"
      let some n := ((t.splitOn " = ").getD 1 "").toNat? | throw s!"bad counter: {t}"
      cur := some { v with counter := some n }
      label := none
    else if let some bs := dumpLine l then
      let (some v, some lab) := (cur, label) | throw s!"hex dump outside a field: {l}"
      cur := some { v with
        fields := v.fields.map fun (k, b) => if k == lab then (k, b ++ bs) else (k, b) }
  if let some v := cur then vs := vs.push v
  return vs.toList

/-- Appendix A.1: the keystream block for each key, counter and nonce;
Appendix A.2: the ciphertext of each plaintext. -/
def check (text : String) : Except String Unit := do
  let blocks ← vectorsIn text "A.1.  " "A.2.  "
  unless blocks.length == 5 do throw s!"A.1: expected 5 vectors, got {blocks.length}"
  for v in blocks do
    let some c := v.counter | throw "A.1: no block counter"
    unless chacha20Block (← v.get "Key:") (BitVec.ofNat 32 c) (← v.get "Nonce:") ==
        (← v.get "Keystream:") do
      throw s!"A.1: the block with counter {c} is wrong"
  let encs ← vectorsIn text "A.2.  " "A.3.  "
  unless encs.length == 3 do throw s!"A.2: expected 3 vectors, got {encs.length}"
  for v in encs do
    let some c := v.counter | throw "A.2: no initial block counter"
    let pt ← v.get "Plaintext:"
    let ct ← v.get "Ciphertext:"
    unless pt.length == ct.length do throw "A.2: plaintext and ciphertext lengths differ"
    unless encrypt (← v.get "Key:") (BitVec.ofNat 32 c) (← v.get "Nonce:") pt == ct do
      throw s!"A.2: the encryption of the {pt.length}-byte plaintext is wrong"
    let ks := keystream (initState (← v.get "Key:") (BitVec.ofNat 32 c) (← v.get "Nonce:")) pt.length
    unless List.zipWith (· ^^^ ·) pt ks == ct do
      throw s!"A.2: the keystream for the {pt.length}-byte plaintext is wrong"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/ChaCha20.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8439" / "rfc8439.txt")
  match check text with
  | .ok () => pure ()
  | .error e => throwError "rfc8439.txt: {e}"

end VG.Test.ChaCha20
