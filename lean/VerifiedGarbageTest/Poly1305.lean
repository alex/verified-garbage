import VerifiedGarbageTest.ChaCha20
import VerifiedGarbage.Spec.Poly1305

/-!
# Known-answer tests for the Poly1305 specification

The test vectors of RFC 8439, Appendix A.3, read from the vendored RFC
`vectors/rfc8439/rfc8439.txt` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.Poly1305.mac`, so that a transcription
error in the spec fails the build. Test vectors #1–#4 are hex dumps (as in
Appendices A.1 and A.2); #5–#11, which exercise the edge cases of the
modular reduction, give `R` and `S` (the two halves of the key), the data
and the tag as rows of hex bytes.
-/

namespace VG.Test.Poly1305

open Lean Elab Command Spec.Poly1305
open Test.ChaCha20 (vectorsIn)

/-- A hex digit, in either case. -/
def hexDigit (c : Char) : Option Nat :=
  Test.ChaCha20.hexDigit c.toLower

/-- The bytes of a line of hex bytes separated by single spaces
(`FF FF 01 …`), or `none` if it is not one. -/
def hexRow (l : String) : Option (List Byte) := do
  let ws := (l.splitOn " ").filter (· ≠ "")
  if ws.isEmpty then none
  ws.mapM fun w => match w.toList with
    | [h, lo] => return BitVec.ofNat 8 (16 * (← hexDigit h) + (← hexDigit lo))
    | _ => none

/-- Test vectors #5–#11 of Appendix A.3: each `Test Vector #n:` is followed by
the labels `R:`, `S:`, `data:` and `tag:`, each followed by rows of hex
bytes. Returns, for each vector, the fields in order. -/
def rowVectors (text : String) : Except String (List (List (String × List Byte))) := do
  let lines := text.splitOn "\n"
  let lines := (lines.dropWhile (!·.startsWith "A.3.  ")).drop 1
  let lines := lines.takeWhile (!·.startsWith "A.4.  ")
  let mut vs : Array (List (String × List Byte)) := #[]
  let mut cur : Option (List (String × List Byte)) := none
  let mut label : Option String := none
  for l in lines do
    let t := String.ofList (l.toList.dropWhile (· == ' '))
    if l.startsWith "   Test Vector #" then
      if let some v := cur then vs := vs.push v
      cur := some []
      label := none
    else if l.startsWith "  Test Vector #" then
      -- #1–#4, the hex dumps, are not rows.
      if let some v := cur then vs := vs.push v
      cur := none
      label := none
    else if ["R:", "S:", "data:", "tag:"].contains t then
      if let some v := cur then
        cur := some (v ++ [(t, [])])
        label := some t
    else if let (some v, some lab, some bs) := (cur, label, hexRow t) then
      cur := some (v.map fun (k, b) => if k == lab then (k, b ++ bs) else (k, b))
  if let some v := cur then vs := vs.push v
  return vs.toList

def field (v : List (String × List Byte)) (label : String) : Except String (List Byte) :=
  match v.find? (·.1 == label) with
  | some (_, bs) => pure bs
  | none => throw s!"no `{label}`"

/-- Appendix A.3: the tag of each text under each key. -/
def check (text : String) : Except String Unit := do
  let dumps ← vectorsIn text "A.3.  " "A.4.  "
    (labels := ["One-time Poly1305 Key:", "Text to MAC:", "Tag:"])
  -- `vectorsIn` also starts a (field-less) vector at each of #5–#11.
  let dumps := dumps.filter (!·.fields.isEmpty)
  unless dumps.length == 4 do throw s!"A.3: expected 4 hex-dump vectors, got {dumps.length}"
  for v in dumps do
    let key ← v.get "One-time Poly1305 Key:"
    let msg ← v.get "Text to MAC:"
    unless key.length == 32 do throw "A.3: a key is not 32 bytes"
    unless mac key msg == (← v.get "Tag:") do
      throw s!"A.3: the tag of the {msg.length}-byte text is wrong"
  let rows ← rowVectors text
  unless rows.length == 7 do throw s!"A.3: expected 7 vectors of rows, got {rows.length}"
  for v in rows do
    let key := (← field v "R:") ++ (← field v "S:")
    let msg ← field v "data:"
    unless key.length == 32 do throw "A.3: a key is not 32 bytes"
    unless mac key msg == (← field v "tag:") do
      throw s!"A.3: the tag of the {msg.length}-byte data is wrong"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Poly1305.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8439" / "rfc8439.txt")
  match check text with
  | .ok () => pure ()
  | .error e => throwError "rfc8439.txt: {e}"

end VG.Test.Poly1305
