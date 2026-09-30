import VerifiedGarbageTest.ChaCha20
import VerifiedGarbage.Spec.X25519

/-!
# Known-answer tests for the X25519 specification

The test vectors of RFC 7748, read from the vendored RFC
`vectors/rfc7748/rfc7748.txt` (see `vectors/sources/`) when this file is
built and checked against `VG.Spec.X25519`, so that a transcription error in
the spec fails the build:

* §5.2, the two X25519 vectors: the scalar and u-coordinate decoded
  (`decodeScalar25519`, `decodeUCoordinate`, against their values in base
  10) and the output u-coordinate;
* §5.2, the iterated X25519 vectors after one and 1,000 iterations (the
  one after 1,000,000 iterations would take the build minutes);
* §6.1, the Diffie-Hellman vector: both public keys, from the base point,
  and the shared secret, computed by both parties.

Each value is on the lines after its label (a line ending with `:`): 64 hex
digits, or a number in base 10 split over lines.
-/

namespace VG.Test.X25519

open Lean Elab Command Spec.X25519

/-- The labelled values of the section of the RFC from the line starting
with `heading` to the next one starting with `next`: each label (a line
ending with `:`, without leading spaces) and the lines after it, without
leading spaces, up to the next label. Only indented lines count: the page
footers and headers (`Langley, et al. …`, `RFC 7748 …`) are not. -/
def values (text heading next : String) : List (String × List String) := Id.run do
  let lines := text.splitOn "\n"
  let lines := (lines.dropWhile (!·.startsWith heading)).drop 1
  let lines := lines.takeWhile (!·.startsWith next)
  let mut vs : Array (String × List String) := #[]
  for l in lines.filter (·.startsWith " ") do
    let t := String.ofList ((l.toList.dropWhile (· == ' ')).reverse.dropWhile
      (fun c => c == ' ' || c == '\r')).reverse
    if t.endsWith ":" then vs := vs.push (t, [])
    else if !t.isEmpty then
      if let some (lab, ls) := vs.back? then vs := vs.pop.push (lab, ls ++ [t])
  return vs.toList

/-- The 32 bytes of a line of 64 hex digits. -/
def hex32 (l : String) : Except String (List Byte) := do
  let cs := l.toList
  unless cs.length == 64 do throw s!"not 64 hex digits: {l}"
  (List.range 32).mapM fun i => do
    let some h := Test.ChaCha20.hexDigit cs[2 * i]! | throw s!"not hex: {l}"
    let some lo := Test.ChaCha20.hexDigit cs[2 * i + 1]! | throw s!"not hex: {l}"
    return BitVec.ofNat 8 (16 * h + lo)

/-- A number in base 10 split over lines. -/
def decimal (ls : List String) : Except String Nat :=
  match (String.join ls).toNat? with
  | some n => pure n
  | none => throw s!"not a number: {ls}"

/-- The single line of the value labelled `label` at position `i` among the
values `vs` (a label may occur more than once). -/
def lineAt (vs : List (String × List String)) (label : String) (i : Nat) :
    Except String String :=
  match (vs.filter (·.1 == label))[i]? with
  | some (_, [l]) => pure l
  | some (_, ls) => throw s!"`{label}` #{i}: {ls.length} lines"
  | none => throw s!"no `{label}` #{i}"

/-- The value labelled `label` at position `i`, in base 10. -/
def decimalAt (vs : List (String × List String)) (label : String) (i : Nat) :
    Except String Nat :=
  match (vs.filter (·.1 == label))[i]? with
  | some (_, ls) => decimal ls
  | none => throw s!"no `{label}` #{i}"

/-- `X25519` applied `n` times as in §5.2: `k` becomes the result and `u`
the old `k`. -/
def iterate : Nat → List Byte → List Byte → List Byte
  | 0, k, _ => k
  | n + 1, k, u => iterate n (x25519 k u) k

def check (text : String) : Except String Unit := do
  -- §5.2: the X25519 vectors come before the X448 ones.
  let vs := values text "5.2.  Test Vectors" "   X448:"
  for i in [0, 1] do
    let k ← hex32 (← lineAt vs "Input scalar:" i)
    let u ← hex32 (← lineAt vs "Input u-coordinate:" i)
    unless decodeScalar25519 k == (← decimalAt vs "Input scalar as a number (base 10):" i) do
      throw s!"5.2: vector {i + 1}: the decoded scalar is wrong"
    unless decodeUCoordinate u == (← decimalAt vs "Input u-coordinate as a number (base 10):" i) do
      throw s!"5.2: vector {i + 1}: the decoded u-coordinate is wrong"
    unless x25519 k u == (← hex32 (← lineAt vs "Output u-coordinate:" i)) do
      throw s!"5.2: vector {i + 1}: the output is wrong"
  -- §5.2, the iterated vectors: again the X25519 ones before the X448 ones.
  let vs := values text "   The second type of test vector" "   X448:"
  let nine ← hex32 (← lineAt vs "For X25519:" 0)
  unless nine == basePoint do throw "5.2: the initial k and u are not 9"
  unless iterate 1 nine nine == (← hex32 (← lineAt vs "After one iteration:" 0)) do
    throw "5.2: the result after one iteration is wrong"
  unless iterate 1000 nine nine == (← hex32 (← lineAt vs "After 1,000 iterations:" 0)) do
    throw "5.2: the result after 1,000 iterations is wrong"
  -- §6.1.
  let vs := values text "6.1.  Curve25519" "6.2.  Curve448"
  let a ← hex32 (← lineAt vs "Alice's private key, a:" 0)
  let b ← hex32 (← lineAt vs "Bob's private key, b:" 0)
  let ka ← hex32 (← lineAt vs "Alice's public key, X25519(a, 9):" 0)
  let kb ← hex32 (← lineAt vs "Bob's public key, X25519(b, 9):" 0)
  let k ← hex32 (← lineAt vs "Their shared secret, K:" 0)
  unless x25519 a basePoint == ka do throw "6.1: Alice's public key is wrong"
  unless x25519 b basePoint == kb do throw "6.1: Bob's public key is wrong"
  unless x25519 a kb == k do throw "6.1: Alice's shared secret is wrong"
  unless x25519 b ka == k do throw "6.1: Bob's shared secret is wrong"

run_cmd do
  -- This file is `lean/VerifiedGarbageTest/X25519.lean`.
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7748" / "rfc7748.txt")
  match check text with
  | .ok () => pure ()
  | .error e => throwError "rfc7748.txt: {e}"

end VG.Test.X25519
