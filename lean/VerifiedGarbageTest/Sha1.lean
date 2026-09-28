import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Sha1

/-!
# Known-answer tests for the SHA-1 specification

Three of the NIST CAVP SHA-1 vectors, read from the vendored response file
`vectors/nist-cavp/sha1/SHA1ShortMsg.rsp` (see `vectors/sources/`) when
this file is built and checked against `VG.Spec.Sha1.hash`, so that a
transcription error in the spec fails the build. The vectors checked are the
empty message, and 55 and 56 bytes: the longest message whose padding fits in
one block, and the shortest that needs a second. (Evaluating the spec is
slow, so only these are checked here; the Rust tests run every CAVP vector
against the implementation.)
-/

namespace VG.Test.Sha1

open Lean Elab Command

/-- The vectors checked here, by message length in bytes. -/
def lengths : List Nat := [0, 55, 56]

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Sha1.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "sha1" / "SHA1ShortMsg.rsp")
  let vs ← match Sha256.vectors text with
    | .ok vs => pure vs
    | .error e => throwError "SHA1ShortMsg.rsp: {e}"
  unless vs.length == 65 do throwError "expected 65 vectors, got {vs.length}"
  for n in lengths do
    let some (msg, md) := vs.find? (·.1.length == n)
      | throwError "no {n}-byte vector"
    unless Spec.Sha1.hash msg == md do throwError "SHA-1 of the {n}-byte CAVP vector is wrong"

end VG.Test.Sha1
