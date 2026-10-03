import VerifiedGarbageTest.Aes
import VerifiedGarbage.Spec.GcmSiv

/-!
# Known-answer tests for the AES-GCM-SIV specification

Read from RFC 8452, vendored unmodified under `vectors/rfc8452/` (see
`vectors/sources/`), when this file is built and checked against
`VG.Spec.GcmSiv`, so that a transcription error in the spec fails the build:

* Appendix A: `mulX_POLYVAL` of its first example (the field's bit order)
  and its worked example of POLYVAL. Its second example of `mulX_POLYVAL`
  is not checked: the last byte of its result has a typo (f2 for 72,
  verified erratum 5854).
* Appendix C: every vector, for both key sizes (C.1, C.2) and the counter
  wrap tests (C.3). Each checks the derived keys (`deriveKeys`), POLYVAL's
  result, the tag and the result of `encrypt`; then that `decrypt` of the
  result is the plaintext, and that it fails with the last byte of the tag
  changed.
-/

namespace VG.Test.GcmSiv

open Lean Elab Command

/-- The contents of `vectors/<path>`. -/
def readFile (path : System.FilePath) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/<File>.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / path)

/-- The lines of the RFC's text without its page breaks (each a footer line,
a form feed and a header line). -/
def body (text : String) : List String :=
  (text.splitOn "\n").filter fun l =>
    !(l.startsWith "Gueron, et al.") && !(l.startsWith "RFC 8452 ") && !(l.startsWith "\x0c")

/-- Whether `w` is a nonempty string of hex digits. -/
def isHex (w : String) : Bool := !w.isEmpty && w.all Char.isHexDigit

/-- The vectors of Appendix C: for each, its fields `label = hex` in order,
the hex continuing on the lines below that hold nothing else. A label
`Plaintext (8 bytes)` is `Plaintext`. A vector starts at `Plaintext`. -/
def vectors (text : String) : List (List (String × List Byte)) := Id.run do
  let lines := ((body text).dropWhile (· != "Appendix C.  Test Vectors"))
  let mut out : Array (List (String × String)) := #[]
  let mut cur : Array (String × String) := #[]
  for l in lines do
    let t := l.trimAscii.toString
    match t.splitOn " = " with
    | [label, v] =>
      let label := (label.splitOn " (").headD label |>.trimAscii.toString
      if label == "Plaintext" && !cur.isEmpty then
        out := out.push cur.toList
        cur := #[]
      cur := cur.push (label, v.trimAscii.toString)
    | _ =>
      match t.splitOn " =" with
      | [label, ""] =>
        let label := (label.splitOn " (").headD label |>.trimAscii.toString
        if label == "Plaintext" && !cur.isEmpty then
          out := out.push cur.toList
          cur := #[]
        cur := cur.push (label, "")
      | _ =>
        if isHex t && !cur.isEmpty && l.startsWith "                " then
          cur := cur.modify (cur.size - 1) fun (k, v) => (k, v ++ t)
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList.map fun fs => fs.filterMap fun (k, v) => (Test.Sha256.unhex v).map (k, ·)

/-- The hex after `label` in `text`, up to the next character that is not a
hex digit. -/
def after (text label : String) : Option (List Byte) :=
  match text.splitOn label with
  | _ :: rest :: _ => Test.Sha256.unhex (rest.takeWhile Char.isHexDigit).toString
  | _ => none

-- Appendix A.
run_cmd do
  let text := String.intercalate "\n" (body (← readFile ("rfc8452" / "rfc8452.txt")))
  let get (label : String) : CommandElabM (List Byte) := match after text label with
    | some v => pure v
    | none => throwError "RFC 8452: no `{label}`"
  let mulX (bs : List Byte) := Spec.GcmSiv.toBytes (Spec.GcmSiv.mulX (Spec.GcmSiv.ofBytes bs))
  let example1 ← get "and mulX_POLYVAL\n   of that string is "
  unless mulX (← get "Given the 16-byte string ") == example1 do
    throwError "RFC 8452 Appendix A: mulX_POLYVAL of 01000000000000000000000000000000 is wrong"
  let h ← get "let H = "
  let x1 ← get "X_1 = "
  let x2 ← get "X_2 = "
  unless Spec.GcmSiv.toBytes (Spec.GcmSiv.polyval (Spec.GcmSiv.ofBytes h)
      [Spec.GcmSiv.ofBytes x1, Spec.GcmSiv.ofBytes x2]) == (← get "POLYVAL(H, X_1, X_2) = ") do
    throwError "RFC 8452 Appendix A: the worked example of POLYVAL is wrong"

-- Appendix C.
run_cmd do
  let vs := vectors (← readFile ("rfc8452" / "rfc8452.txt"))
  let mut n : Nat := 0
  let mut keyLens : List Nat := []
  for fs in vs do
    let get (label : String) : CommandElabM (List Byte) := match fs.lookup label with
      | some v => pure v
      | none => throwError "RFC 8452, vector {n}: no `{label}`"
    let pt ← get "Plaintext"
    let aad ← get "AAD"
    let key ← get "Key"
    let nonce ← get "Nonce"
    let result ← get "Result"
    let ciph := Spec.GcmSiv.aes key
    let (authKey, encKey) := Spec.GcmSiv.deriveKeys ciph key.length nonce
    let keys := (← get "Record authentication key", ← get "Record encryption key")
    unless (authKey, encKey) == keys do
      throwError "RFC 8452, vector {n}: the derived keys are wrong"
    let lengthBlock := Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length)
    let s := Spec.GcmSiv.polyval (Spec.GcmSiv.ofBytes authKey)
      (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad ++ Spec.GcmSiv.pad16 pt ++ lengthBlock))
    unless Spec.GcmSiv.toBytes s == (← get "POLYVAL result") do
      throwError "RFC 8452, vector {n}: POLYVAL is wrong"
    unless (Spec.GcmSiv.encryptWith ciph key.length nonce pt aad).2 == (← get "Tag") do
      throwError "RFC 8452, vector {n}: the tag is wrong"
    unless Spec.GcmSiv.encrypt key nonce pt aad == some result do
      throwError "RFC 8452, vector {n}: encryption is wrong"
    unless Spec.GcmSiv.decrypt key nonce result aad == some pt do
      throwError "RFC 8452, vector {n}: decryption is wrong"
    let forged := result.set (result.length - 1) (result.getLast! ^^^ 1)
    unless Spec.GcmSiv.decrypt key nonce forged aad == none do
      throwError "RFC 8452, vector {n}: decryption accepts a wrong tag"
    n := n + 1
    keyLens := key.length :: keyLens
  -- C.1 and C.2 have 24 vectors each (C.1 for 16-byte keys, C.2 for 32-byte keys), and C.3 two.
  unless n == 50 && keyLens.count 16 == 24 do
    throwError "expected 50 vectors, 24 of them with 16-byte keys, checked {n}: {keyLens.count 16}"

end VG.Test.GcmSiv
