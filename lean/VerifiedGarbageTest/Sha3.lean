import VerifiedGarbageTest.Sha256
import VerifiedGarbage.Spec.Sha3

/-!
# Known-answer tests for the SHA-3 and SHAKE specification

NIST CAVP vectors, read from the vendored response files under
`vectors/nist-cavp/sha3/` and `vectors/nist-cavp/shake/` (see
`vectors/sources.toml`) when this file is built and checked against
`VG.Spec.Sha3`, so that a transcription error in the spec fails the build.

For each of SHA3-224/256/384/512 and SHAKE128/256 (with the fixed output
length of its `ShortMsg` file), the vectors checked are the empty message,
and messages of `r - 1` and `r` bytes for the rate `r`: the longest message
whose padding is the single byte `suffix ⊕ 0x80`, and the shortest whose
padding takes a block of its own. From SHAKE256's `VariableOut` file, the
2-byte and 250-byte outputs: the shortest, and the longest, which is
squeezed from two blocks. (Evaluating the spec is slow, so only these are
checked here; the Rust tests run every CAVP vector against the
implementation.)
-/

namespace VG.Test.Sha3

open Lean Elab Command Spec.Sha3

/-- The `key = value` lines of a CAVP response file, without comments and
`[...]` headers. -/
def fields (text : String) : List (String × String) :=
  (text.splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" || l.startsWith "[" then none
    else match l.splitOn " = " with
      | [k, v] => some (k, v)
      | _ => none

/-- The `(message, output length in bytes, output)` of each record of a
CAVP response file, whose output is under the key `out` (`MD` or `Output`).
The message length is `Len` in bits when given (the zero-length message is
written as `Msg = 00`); the output length `Outputlen` in bits when given,
and the length of the output otherwise. -/
def records (out : String) (text : String) :
    Except String (List (List Byte × Nat × List Byte)) := do
  let rec go (len : Option Nat) (outLen : Option Nat) (msg : Option (List Byte)) :
      List (String × String) → Except String (List (List Byte × Nat × List Byte))
    | [] => pure []
    | (k, v) :: rest =>
      if k == "Len" then do
        let some n := v.toNat? | throw s!"bad Len {v}"
        go (some n) outLen msg rest
      else if k == "Outputlen" then do
        let some n := v.toNat? | throw s!"bad Outputlen {v}"
        go len (some n) msg rest
      else if k == "Msg" then do
        let some m := Test.Sha256.unhex v | throw s!"bad Msg {v}"
        go len outLen (some m) rest
      else if k == out then do
        let some md := Test.Sha256.unhex v | throw s!"bad {out} {v}"
        let some m := msg | throw s!"{out} without Msg"
        let m := match len with | some n => m.take (n / 8) | none => m
        let d := match outLen with | some n => n / 8 | none => md.length
        return (m, d, md) :: (← go none none none rest)
      else go len outLen msg rest
  go none none none (fields text)

/-- The response file `dir/name` under `vectors/nist-cavp/`. -/
def readVectors (dir name : String) : CommandElabM String := do
  -- This file is `lean/VerifiedGarbageTest/Sha3.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  IO.FS.readFile (root / "vectors" / "nist-cavp" / dir / name)

/-- Checks `f` on the vectors of `dir/name` whose message lengths are
`lengths`. -/
def check (dir name out : String) (lengths : List Nat)
    (f : List Byte → Nat → List Byte) : CommandElabM Unit := do
  let vs ← match records out (← readVectors dir name) with
    | .ok vs => pure vs
    | .error e => throwError "{name}: {e}"
  for n in lengths do
    let some (msg, d, md) := vs.find? (·.1.length == n)
      | throwError "{name}: no {n}-byte vector"
    unless f msg d == md do throwError "{name}: the {n}-byte vector is wrong"

run_cmd check "sha3" "SHA3_224ShortMsg.rsp" "MD" [0, 143, 144] fun m _ => sha3_224 m
run_cmd check "sha3" "SHA3_256ShortMsg.rsp" "MD" [0, 135, 136] fun m _ => sha3_256 m
run_cmd check "sha3" "SHA3_384ShortMsg.rsp" "MD" [0, 103, 104] fun m _ => sha3_384 m
run_cmd check "sha3" "SHA3_512ShortMsg.rsp" "MD" [0, 71, 72] fun m _ => sha3_512 m
run_cmd check "shake" "SHAKE128ShortMsg.rsp" "Output" [0, 167, 168] shake128
run_cmd check "shake" "SHAKE256ShortMsg.rsp" "Output" [0, 135, 136] shake256

run_cmd do
  let vs ← match records "Output" (← readVectors "shake" "SHAKE256VariableOut.rsp") with
    | .ok vs => pure vs
    | .error e => throwError "SHAKE256VariableOut.rsp: {e}"
  for d in [2, 250] do
    let some (msg, _, out) := vs.find? (·.2.1 == d)
      | throwError "SHAKE256VariableOut.rsp: no {d}-byte output"
    unless out.length == d && shake256 msg d == out do
      throwError "SHAKE256VariableOut.rsp: the {d}-byte output is wrong"

end VG.Test.Sha3
