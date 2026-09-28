import VerifiedGarbageTest.Poly1305
import VerifiedGarbage.Spec.ChaCha20Poly1305

/-!
# Known-answer tests for the ChaCha20-Poly1305 specification

The test vectors of RFC 8439 for the AEAD, read from the vendored RFC
`vectors/rfc8439/rfc8439.txt` (see `vectors/sources.toml`) when this file is
built, so that a transcription error in the spec fails the build:

* Appendix A.4, the one-time key (`VG.Spec.ChaCha20Poly1305.polyKeyGen`);
* §2.8.2, an encryption (`VG.Spec.ChaCha20Poly1305.encrypt`), with its
  Poly1305 input (`macData`) and one-time key;
* Appendix A.5, a decryption (`VG.Spec.ChaCha20Poly1305.decrypt`), with its
  Poly1305 input; and the same message with a changed tag, which must not
  decrypt.
-/

namespace VG.Test.ChaCha20Poly1305

open Lean Elab Command Spec.ChaCha20Poly1305
open Test.ChaCha20 (vectorsIn dumpLine)

/-- The lines of the section of the RFC starting at the line that begins with
`heading` and ending before the one that begins with `next`. -/
def section_ (text heading next : String) : List String :=
  let lines := text.splitOn "\n"
  ((lines.dropWhile (!·.startsWith heading)).drop 1).takeWhile (!·.startsWith next)

/-- Whether a line is blank or part of a page break (footer and header). -/
def pageLine (l : String) : Bool :=
  l.trimAscii.isEmpty || l.startsWith "Nir & Langley" || l.startsWith "RFC 8439" || l == "\x0c"

/-- The hex dump following the first line of `lines` whose text is `label`:
its consecutive dump lines, across page breaks. -/
def dumpAfter (lines : List String) (label : String) : Except String (List Byte) := do
  let rest := (lines.dropWhile (fun l => (String.ofList (l.toList.dropWhile (· == ' '))) != label)).drop 1
  if rest.isEmpty then throw s!"no `{label}`"
  let mut out : List Byte := []
  for l in rest do
    if let some bs := dumpLine l then
      out := out ++ bs
    else if !pageLine l then
      break
  if out.isEmpty then throw s!"no hex dump after `{label}`"
  return out

/-- The bytes of a line of hex pairs separated by colons (`1a:e1:…`). -/
def colonHex (l : String) : Option (List Byte) :=
  ((l.trimAscii.toString.splitOn ":").filter (· ≠ "")).mapM fun w => match w.toList with
    | [h, lo] => do return BitVec.ofNat 8 (16 * (← Test.Poly1305.hexDigit h) + (← Test.Poly1305.hexDigit lo))
    | _ => none

/-- The colon-separated hex on the line after the one whose text is `label`. -/
def colonAfter (lines : List String) (label : String) : Except String (List Byte) := do
  let rest := (lines.dropWhile (fun l => (String.ofList (l.toList.dropWhile (· == ' '))) != label)).drop 1
  match rest.head? >>= colonHex with
  | some bs => pure bs
  | none => throw s!"no colon-separated hex after `{label}`"

def check (text : String) : Except String Unit := do
  -- A.4: the one-time key.
  let keys ← vectorsIn text "A.4.  " "A.5.  "
    (labels := ["The ChaCha20 Key:", "The ChaCha20 Key", "The nonce:", "Poly1305 one-time key:"])
  unless keys.length == 3 do throw s!"A.4: expected 3 vectors, got {keys.length}"
  for v in keys do
    let key ← (v.get "The ChaCha20 Key:" <|> v.get "The ChaCha20 Key")
    unless polyKeyGen key (← v.get "The nonce:") == (← v.get "Poly1305 one-time key:") do
      throw "A.4: a one-time key is wrong"
  -- §2.8.2: an encryption.
  let enc := section_ text "2.8.2.  " "3.  "
  let pt ← dumpAfter enc "Plaintext:"
  let aad ← dumpAfter enc "AAD:"
  let key ← dumpAfter enc "Key:"
  let nonce := (← dumpAfter enc "32-bit fixed-common part:") ++ (← dumpAfter enc "IV:")
  unless polyKeyGen key nonce == (← dumpAfter enc "Poly1305 Key:") do
    throw "2.8.2: the one-time key is wrong"
  let ct ← dumpAfter enc "Ciphertext:"
  unless macData aad ct == (← dumpAfter enc "AEAD Construction for Poly1305:") do
    throw "2.8.2: the Poly1305 input is wrong"
  unless encrypt key nonce aad pt == (ct, ← colonAfter enc "Tag:") do
    throw "2.8.2: the encryption is wrong"
  -- A.5: a decryption.
  let dec := section_ text "A.5.  " "Appendix B.  "
  let key ← dumpAfter dec "The ChaCha20 Key"
  let ct ← dumpAfter dec "Ciphertext:"
  let nonce ← dumpAfter dec "The nonce:"
  let aad ← dumpAfter dec "The AAD:"
  let tag ← dumpAfter dec "Received Tag:"
  unless polyKeyGen key nonce == (← dumpAfter dec "Poly1305 one-time key:") do
    throw "A.5: the one-time key is wrong"
  unless macData aad ct == (← dumpAfter dec "Poly1305 Input:") do
    throw "A.5: the Poly1305 input is wrong"
  unless decrypt key nonce aad ct tag == some (← dumpAfter dec "Plaintext::") do
    throw "A.5: the decryption is wrong"
  let badTag := tag.set 0 (tag.getD 0 0 ^^^ 1)
  unless decrypt key nonce aad ct badTag == none do
    throw "A.5: a message with a wrong tag decrypts"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/ChaCha20Poly1305.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8439" / "rfc8439.txt")
  match check text with
  | .ok () => pure ()
  | .error e => throwError "rfc8439.txt: {e}"

end VG.Test.ChaCha20Poly1305
