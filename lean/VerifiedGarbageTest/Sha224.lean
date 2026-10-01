import VerifiedGarbageTest.Sha256

/-!
# Known-answer tests for the SHA-224 specification

Two of the NIST CAVP SHA-224 vectors, read from the vendored response file
`vectors/nist-cavp/sha224/SHA224ShortMsg.rsp` (see `vectors/sources/`)
when this file is built and checked against `VG.Spec.Sha256.sha224`, so that
a transcription error in its initial hash value fails the build. (As for
SHA-256, the Rust tests run every CAVP vector against the implementation.)
-/

namespace VG.Test.Sha224

open Lean Elab Command
open VG.Test.Sha256 (vectors lengths)

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Sha224.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "sha224" / "SHA224ShortMsg.rsp")
  let vs ← match vectors text with
    | .ok vs => pure vs
    | .error e => throwError "SHA224ShortMsg.rsp: {e}"
  unless vs.length == 65 do throwError "expected 65 vectors, got {vs.length}"
  for n in lengths do
    let some (msg, md) := vs.find? (·.1.length == n)
      | throwError "no {n}-byte vector"
    unless Spec.Sha256.sha224 msg == md do throwError "SHA-224 of the {n}-byte CAVP vector is wrong"

end VG.Test.Sha224
