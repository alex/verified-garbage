import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Md5

/-!
# Known-answer tests for the MD5 specification

The seven vectors of the MD5 test suite in Appendix A.5 of RFC 1321, read from
the vendored `vectors/rfc1321/rfc1321.txt` (see `vectors/sources.toml`) when
this file is built and checked against `VG.Spec.Md5.hash`, so that a
transcription error in the spec fails the build. They include the empty
message, messages whose padding takes one block, and 62- and 80-byte ones
whose padding takes a second block.
-/

namespace VG.Test.Md5

open Lean Elab Command

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The `(message, digest)` of each `MD5 ("message") = digest` line of the
test suite. The RFC wraps two of them onto a second line, so the suite's
lines are joined without separators before they are split into vectors. -/
def vectors (text : String) : Except String (List (List Byte × List Byte)) := do
  let lines := text.splitOn "\n"
  let some start := lines.findIdx? (· == "MD5 test suite:")
    | throw "no `MD5 test suite:` line"
  let suite := String.join ((lines.drop (start + 1)).takeWhile (!·.isEmpty))
  let rec go : List String → Except String (List (List Byte × List Byte))
    | [] => pure []
    | v :: rest => do
      let [msg, md] := v.splitOn "\") ="
        | throw s!"expected `MD5 (\"...\") = ...`, got {v}"
      let some md := Sha256.unhex md.trimAscii.toString
        | throw s!"expected a hex digest, got {md}"
      return (ascii msg, md) :: (← go rest)
  match suite.splitOn "MD5 (\"" with
  | "" :: vs => go vs
  | _ => throw s!"expected the suite to start with `MD5 (\"`, got {suite}"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Md5.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc1321" / "rfc1321.txt")
  let vs ← match vectors text with
    | .ok vs => pure vs
    | .error e => throwError "rfc1321.txt: {e}"
  unless vs.length == 7 do throwError "expected 7 vectors, got {vs.length}"
  for (msg, md) in vs do
    unless Spec.Md5.hash msg == md do
      throwError "MD5 of the {msg.length}-byte RFC 1321 vector is wrong"

end VG.Test.Md5
