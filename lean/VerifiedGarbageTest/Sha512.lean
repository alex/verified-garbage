import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# Known-answer tests for the SHA-512 family specification

Three of the NIST CAVP vectors for each of SHA-384, SHA-512, SHA-512/224 and
SHA-512/256, read from the vendored response files under
`vectors/nist-cavp/sha512/` (see `vectors/sources.toml`) when this file is
built and checked against `VG.Spec.Sha512`, so that a transcription error in
the spec fails the build. The vectors checked are the empty message, and 111
and 112 bytes: the longest message whose padding fits in one block, and the
shortest that needs a second. (Evaluating the spec is slow, so only these are
checked here; the Rust tests run every CAVP vector against the
implementation.)

The initial hash values of SHA-512/224 and SHA-512/256 are also checked
against the generation function of §5.3.6.
-/

namespace VG.Test.Sha512

open Lean Elab Command Spec.Sha512

/-- The vectors checked here, by message length in bytes. -/
def lengths : List Nat := [0, 111, 112]

/-- Each function, the response file of its short messages, and its number
of vectors (every length from 0 to 128 bytes). -/
def files : List (String × (List Byte → List Byte)) :=
  [("SHA384ShortMsg.rsp", sha384), ("SHA512ShortMsg.rsp", sha512),
   ("SHA512_224ShortMsg.rsp", sha512_224), ("SHA512_256ShortMsg.rsp", sha512_256)]

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Sha512.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  for (name, f) in files do
    let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "sha512" / name)
    let vs ← match Sha256.vectors text with
      | .ok vs => pure vs
      | .error e => throwError "{name}: {e}"
    unless vs.length == 129 do throwError "{name}: expected 129 vectors, got {vs.length}"
    for n in lengths do
      let some (msg, md) := vs.find? (·.1.length == n)
        | throwError "{name}: no {n}-byte vector"
      unless f msg == md do throwError "{name}: the {n}-byte vector is wrong"

def ascii (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- §5.3.6: the initial hash value of SHA-512/t is the SHA-512 hash, starting
from `H0_512` with each word XORed with `a5a5a5a5a5a5a5a5`, of the ASCII
string "SHA-512/t". -/
def ivGen (t : String) : List Byte :=
  finalHash (H0_512.map (· ^^^ 0xa5a5a5a5a5a5a5a5)) (ascii s!"SHA-512/{t}")

#guard ivGen "224" == H0_512_224.toList.flatMap wordBytes
#guard ivGen "256" == H0_512_256.toList.flatMap wordBytes

end VG.Test.Sha512
