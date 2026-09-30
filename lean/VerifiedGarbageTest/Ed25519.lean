import Lean.Elab.Command
import VerifiedGarbage.Spec.Ed25519

/-!
# RFC 8032 Ed25519 specification tests

All five known-answer vectors are parsed directly from §7.1 of the
byte-for-byte vendored RFC, including its 1023-byte message and the
SHA-512(abc) message (which is still signed using pure Ed25519).
Boundary and mutation tests below derive inputs from those vectors or
from the mathematical parameters; no known-answer byte strings are embedded.
-/

namespace VG.Test.Ed25519

open Lean Elab Command Spec.Ed25519

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Except String (List Byte)
  | [] => pure []
  | h :: l :: rest => do
    let some hi := hexDigit h | throw "invalid hexadecimal digit"
    let some lo := hexDigit l | throw "invalid hexadecimal digit"
    return BitVec.ofNat 8 (16 * hi + lo) :: (← hexBytes rest)
  | _ => throw "odd number of hexadecimal digits"

structure Vector where
  seed : List Byte := []
  pk : List Byte := []
  message : List Byte := []
  signature : List Byte := []

/-- Collect only indented hex lines under each recognized field, skipping
page headers and footers. Stop before the Ed25519ctx vectors. -/
def parseVectors (text : String) : Except String (List Vector) := do
  let lines := ((text.splitOn "\n").dropWhile
    (!·.startsWith "7.1.  Test Vectors for Ed25519")).drop 1
  let lines := lines.takeWhile (!·.startsWith "7.2.  Test Vectors for Ed25519ctx")
  let mut vs : Array Vector := #[]
  let mut field := ""
  for line in lines do
    if !line.startsWith "   " then continue
    let t := String.ofList (line.toList.dropWhile (· == ' '))
    if t.startsWith "-----TEST" then
      vs := vs.push {}
      field := ""
    else if t == "SECRET KEY:" then field := "seed"
    else if t == "PUBLIC KEY:" then field := "pk"
    else if t.startsWith "MESSAGE (length " then field := "message"
    else if t == "SIGNATURE:" then field := "signature"
    else if !t.isEmpty && t.toList.all (fun c => (hexDigit c).isSome) then
      let bs ← hexBytes t.toList
      let some v := vs.back? | throw "hex data before the first test"
      let v ← match field with
        | "seed" => pure { v with seed := v.seed ++ bs }
        | "pk" => pure { v with pk := v.pk ++ bs }
        | "message" => pure { v with message := v.message ++ bs }
        | "signature" => pure { v with signature := v.signature ++ bs }
        | _ => throw "hex data outside a recognized field"
      vs := vs.pop.push v
  unless vs.size == 5 do throw s!"expected 5 vectors, got {vs.size}"
  unless (vs.toList.map (·.message.length)) == [0, 1, 2, 1023, 64] do
    throw "incorrect message lengths"
  return vs.toList

def checkVector (i : Nat) (v : Vector) : Except String Unit := do
  unless v.seed.length == 32 && v.pk.length == 32 && v.signature.length == 64 do
    throw s!"vector {i}: incorrect key/signature lengths"
  unless publicKey v.seed == v.pk do throw s!"vector {i}: public key mismatch"
  unless sign v.seed v.message == v.signature do throw s!"vector {i}: signature mismatch"
  unless verify v.pk v.message v.signature do throw s!"vector {i}: verification failed"
  for bs in [v.pk, v.signature.take 32] do
    let some p := decodePoint bs | throw s!"vector {i}: point did not decode"
    unless encodePoint p == bs do throw s!"vector {i}: point round trip failed"
  let (s, noncePrefix) := expandSecret v.seed
  unless s % 8 == 0 && 2 ^ 254 ≤ s && s < 2 ^ 255 do
    throw s!"vector {i}: pruning failed"
  unless scalarBase (encodeLE 32 s) == v.pk do throw s!"vector {i}: scalarBase failed"
  let r := scalarReduce (Spec.Sha512.sha512 (noncePrefix ++ v.message))
  let k := scalarReduce (Spec.Sha512.sha512 (v.signature.take 32 ++ v.pk ++ v.message))
  unless scalarBase r == v.signature.take 32 do throw s!"vector {i}: nonce point failed"
  unless scalarMulAdd r k (encodeLE 32 s) == v.signature.drop 32 do
    throw s!"vector {i}: scalarMulAdd failed"
  if verify v.pk (v.message ++ [0]) v.signature then
    throw s!"vector {i}: accepted changed message"
  if verify v.pk v.message (v.signature.set 0 (v.signature.getD 0 0 ^^^ 1)) then
    throw s!"vector {i}: accepted changed signature"
  let noncanonical := v.signature.take 32 ++ encodeLE 32 (decodeLE (v.signature.drop 32) + L)
  if verify v.pk v.message noncanonical then throw s!"vector {i}: accepted S + L"
  if verify (v.pk.drop 1) v.message v.signature ||
      verify (v.pk ++ [0]) v.message v.signature ||
      verify v.pk v.message (v.signature.drop 1) ||
      verify v.pk v.message (v.signature ++ [0]) then
    throw s!"vector {i}: accepted incorrect length"

def checkBoundaries : Except String Unit := do
  -- No reduction of a noncanonical y, for either sign.
  for y in List.range 19 do
    for signBit in [0, 1] do
      if (decodePoint (encodeLE 32 (Spec.X25519.P + y + signBit * 2 ^ 255))).isSome then
        throw "accepted noncanonical y"
  -- Both points with x = 0 must reject a set sign bit.
  for y in [1, Spec.X25519.P - 1] do
    if (decodePoint (encodeLE 32 (y + 2 ^ 255))).isSome then throw "accepted negative zero"
    unless (decodePoint (encodeLE 32 y)).isSome do throw "rejected positive zero"
  unless pointEqual (pointMul L basePoint) identity do throw "base point has wrong order"
  unless pointEqual (pointAdd basePoint identity) basePoint do throw "identity addition failed"
  -- Pin the documented policy: there is no separate small-order rejection.
  let id := encodePoint identity
  let sig := id ++ encodeLE 32 0
  unless verify id [] sig do throw "identity-key policy changed"
  for s in [L, L + 1, 2 ^ 256 - 1] do
    if verify id [] (id ++ encodeLE 32 s) then throw "accepted S >= L"
  -- A full 512-bit challenge matters for non-prime-order public keys.
  let some orderTwo := decodePoint (encodeLE 32 (Spec.X25519.P - 1))
    | throw "order-two point did not decode"
  if verifyEquation (encodePoint orderTwo) sig (encodeLE 64 L) then
    throw "challenge was incorrectly reduced modulo L"
  unless verifyEquation (encodePoint orderTwo) sig (encodeLE 64 (2 * L)) do
    throw "order-two equation failed for an even challenge"
  if verifyEquation id sig (encodeLE 63 0) then throw "accepted short challenge"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8032" / "rfc8032.txt")
  let result := do
    let vs ← parseVectors text
    for (v, i) in vs.zipIdx do checkVector i v
    checkBoundaries
  match result with
  | .ok () => pure ()
  | .error e => throwError "rfc8032.txt: {e}"

end VG.Test.Ed25519
