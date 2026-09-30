import Lean.Elab.Command
import VerifiedGarbage.Spec.X448

/-!
# Known-answer tests for the X448 specification

RFC 7748 §5.2 and §6.2, read directly from the byte-for-byte vendored RFC
in `vectors/rfc7748/rfc7748.txt`. Check both scalar-multiplication vectors
and their decimal decodings, one and 1,000 iterations, both public keys,
and both parties' shared secrets. The million-iteration test is omitted
from the build, as it is for X25519.

Boundary tests derive inputs from the field parameters and the published
scalars. In particular, X448 must preserve bit 447 of the u-coordinate
and accept noncanonical coordinates. No known-answer bytes are embedded.
-/

namespace VG.Test.X448

open Lean Elab Command Spec.X448

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- A section starts at an exact heading, excluding its table-of-contents
entry, and ends before the next heading. -/
def sectionText (text heading next : String) : String :=
  let lines := ((text.splitOn "\n").dropWhile (· != heading)).drop 1
  String.intercalate "\n" (lines.takeWhile (· != next))

/-- Collect labelled decimal/hexadecimal lines, skipping page headers,
footers and explanatory prose between vectors. -/
def values (text : String) : List (String × String) := Id.run do
  let mut vs : Array (String × String) := #[]
  for line in text.splitOn "\n" do
    if !line.startsWith " " then continue
    let t := String.ofList (line.toList.dropWhile (· == ' '))
    if t.endsWith ":" then vs := vs.push (t, "")
    else if !t.isEmpty && t.toList.all (fun c => (hexDigit c).isSome) then
      if let some (label, s) := vs.back? then vs := vs.pop.push (label, s ++ t)
  return vs.toList

def valueAt (vs : List (String × String)) (label : String) (i : Nat := 0) :
    Except String String :=
  match (vs.filter (·.1 == label))[i]? with
  | some (_, s) => pure s
  | none => throw s!"no `{label}` #{i}"

/-- Exactly 56 bytes, split over two lines in the RFC. -/
def hex56 (s : String) : Except String (List Byte) := do
  let cs := s.toList
  unless cs.length == 112 do throw s!"not 112 hex digits: {s}"
  (List.range 56).mapM fun i => do
    let some hi := hexDigit cs[2 * i]! | throw s!"not hex: {s}"
    let some lo := hexDigit cs[2 * i + 1]! | throw s!"not hex: {s}"
    return BitVec.ofNat 8 (16 * hi + lo)

def hexAt (vs : List (String × String)) (label : String) (i : Nat := 0) :
    Except String (List Byte) := do
  hex56 (← valueAt vs label i)

def decimalAt (vs : List (String × String)) (label : String) (i : Nat) :
    Except String Nat := do
  let s ← valueAt vs label i
  let some n := s.toNat? | throw s!"not decimal: {s}"
  return n

/-- Apply X448 repeatedly, assigning the old scalar to the next point (§5.2). -/
def iterate : Nat → List Byte → List Byte → List Byte
  | 0, k, _ => k
  | n + 1, k, u => iterate n (x448 k u) k

/-- A raw 448-bit encoding, without reduction modulo the field prime. -/
def encodeRaw (n : Nat) : List Byte :=
  (List.range 56).map fun i => BitVec.ofNat 8 (n >>> (8 * i))

def checkBoundaries (k : List Byte) : Except String Unit := do
  let scalar := decodeScalar448 k
  unless scalar % 4 == 0 && 2 ^ 447 ≤ scalar && scalar < 2 ^ 448 do
    throw "scalar clamping bounds are wrong"
  for low in List.range 4 do
    let changed := k.set 0 (k.getD 0 0 ^^^ BitVec.ofNat 8 low)
    unless decodeScalar448 changed == scalar do throw "low scalar bits were not cleared"
  unless decodeScalar448 (k.set 55 (k.getD 55 0 ^^^ 128)) == scalar do
    throw "scalar bit 447 was not set"
  unless decodeScalar448 (k.set 0 (k.getD 0 0 ^^^ 4)) != scalar do
    throw "scalar bit 2 was incorrectly cleared"
  unless decodeScalar448 (k.set 55 (k.getD 55 0 ^^^ 64)) != scalar do
    throw "scalar bit 446 was incorrectly overwritten"
  let high := basePoint.set 55 128
  unless decodeUCoordinate high == 2 ^ 447 + 5 do
    throw "u-coordinate bit 447 was masked"
  unless x448 k high != x448 k basePoint do
    throw "u-coordinate bit 447 did not affect the ladder"
  -- Noncanonical inputs, including both ends of the permitted range.
  for u in [P, P + 1, P + 5, 2 ^ 448 - 1] do
    unless decodeUCoordinate (encodeRaw u) == u do throw "raw u decoding is wrong"
    unless x448 k (encodeRaw u) == x448 k (encodeRaw (u % P)) do
      throw "noncanonical u-coordinate was not reduced"
  for u in [0, 1, P - 1] do
    unless x448 k (encodeRaw u) == List.replicate 56 0 do
      throw "small-order point did not produce zero"
  for u in [0, 1, 5, P - 1] do
    unless encodeUCoordinate (Fin.ofNat P u) == encodeRaw u do
      throw "canonical field encoding is wrong"
  let out := x448 k basePoint
  unless out.length == 56 && decodeUCoordinate out < P do
    throw "output is not a canonical 56-byte coordinate"

def check (text : String) : Except String Unit := do
  let tests := sectionText text "5.2.  Test Vectors" "6.  Diffie-Hellman"
  let vs := values (sectionText tests "   X448:"
    "   The second type of test vector consists of the result of calling the")
  unless (vs.filter (·.1 == "Input scalar:")).length == 2 do
    throw "expected two X448 scalar-multiplication vectors"
  for i in [0, 1] do
    let k ← hexAt vs "Input scalar:" i
    let u ← hexAt vs "Input u-coordinate:" i
    unless decodeScalar448 k == (← decimalAt vs "Input scalar as a number (base 10):" i) do
      throw s!"5.2: vector {i + 1}: decoded scalar is wrong"
    unless decodeUCoordinate u == (← decimalAt vs "Input u-coordinate as a number (base 10):" i) do
      throw s!"5.2: vector {i + 1}: decoded u-coordinate is wrong"
    unless x448 k u == (← hexAt vs "Output u-coordinate:" i) do
      throw s!"5.2: vector {i + 1}: output is wrong"
    checkBoundaries k
  let repeated := sectionText tests
    "   The second type of test vector consists of the result of calling the" "6.  Diffie-Hellman"
  let initial ← hexAt (values repeated) "For X448:"
  unless initial == basePoint do throw "5.2: initial k and u are not the base point"
  let vs := values (sectionText repeated "   X448:" "6.  Diffie-Hellman")
  unless iterate 1 initial initial == (← hexAt vs "After one iteration:") do
    throw "5.2: result after one iteration is wrong"
  unless iterate 1000 initial initial == (← hexAt vs "After 1,000 iterations:") do
    throw "5.2: result after 1,000 iterations is wrong"
  let vs := values (sectionText text "6.2.  Curve448" "7.  Security Considerations")
  let a ← hexAt vs "Alice's private key, a:"
  let b ← hexAt vs "Bob's private key, b:"
  let ka ← hexAt vs "Alice's public key, X448(a, 5):"
  let kb ← hexAt vs "Bob's public key, X448(b, 5):"
  let shared ← hexAt vs "Their shared secret, K:"
  unless x448 a basePoint == ka do throw "6.2: Alice's public key is wrong"
  unless x448 b basePoint == kb do throw "6.2: Bob's public key is wrong"
  unless x448 a kb == shared do throw "6.2: Alice's shared secret is wrong"
  unless x448 b ka == shared do throw "6.2: Bob's shared secret is wrong"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc7748" / "rfc7748.txt")
  match check text with
  | .ok () => pure ()
  | .error e => throwError "rfc7748.txt: {e}"

end VG.Test.X448
