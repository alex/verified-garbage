import Lean.Elab.Command
import VerifiedGarbage.Spec.Sha256

/-!
# Known-answer tests for the SHA-256 specification

Two of the NIST CAVP SHA-256 vectors, read from the vendored response file
`vectors/nist-cavp/sha256/SHA256ShortMsg.rsp` (see `vectors/sources/`)
when this file is built and checked against `VG.Spec.Sha256.hash`, so that a
transcription error in the spec fails the build. (Evaluating the spec is slow,
so only two are checked here; the Rust tests run every CAVP vector against
the implementation, whose compression function is proven equal to the spec's.)
-/

namespace VG.Test.Sha256

open Lean Elab Command Spec.Sha256

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes written in hex by `s`. -/
def unhex (s : String) : Option (List Byte) :=
  let rec go : List Char → Option (List Byte)
    | [] => some []
    | hi :: lo :: rest => do
      let b := 16 * (← hexDigit hi) + (← hexDigit lo)
      return BitVec.ofNat 8 b :: (← go rest)
    | [_] => none
  go s.toList

/-- The `(message, digest)` of each `Len`/`Msg`/`MD` triple of a CAVP
response file. -/
def vectors (text : String) : Except String (List (List Byte × List Byte)) := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString) |>.filter fun l =>
    !l.isEmpty && !l.startsWith "#" && !l.startsWith "["
  let rec go : List String → Except String (List (List Byte × List Byte))
    | [] => pure []
    | len :: msg :: md :: rest => do
      let some len := (len.dropPrefix? "Len = ").bind (·.toString.toNat?)
        | throw s!"expected `Len = ...`, got {len}"
      let some msg := (msg.dropPrefix? "Msg = ").bind (unhex ·.toString)
        | throw s!"expected `Msg = ...`, got {msg}"
      let some md := (md.dropPrefix? "MD = ").bind (unhex ·.toString)
        | throw s!"expected `MD = ...`, got {md}"
      -- `Len` is in bits; the zero-length message is written as `Msg = 00`.
      return (msg.take (len / 8), md) :: (← go rest)
    | rest => throw s!"trailing lines: {rest}"
  go lines

/-- The vectors checked here: a one-byte message, and a 64-byte one (whose
padding takes a second block). -/
def lengths : List Nat := [1, 64]

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/Sha256.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "sha256" / "SHA256ShortMsg.rsp")
  let vs ← match vectors text with
    | .ok vs => pure vs
    | .error e => throwError "SHA256ShortMsg.rsp: {e}"
  unless vs.length == 65 do throwError "expected 65 vectors, got {vs.length}"
  for n in lengths do
    let some (msg, md) := vs.find? (·.1.length == n)
      | throwError "no {n}-byte vector"
    unless Spec.Sha256.hash msg == md do throwError "SHA-256 of the {n}-byte CAVP vector is wrong"

end VG.Test.Sha256
