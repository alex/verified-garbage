import Lean.Elab.Command
import VerifiedGarbage.Spec.Ed448

/-!
# RFC 8032 Ed448 specification tests

All nine known-answer vectors are parsed directly from §7.4 of the
byte-for-byte vendored RFC, including the one with a context and the
1023-byte message. Boundary and mutation tests below derive inputs from
those vectors or from the mathematical parameters; no known-answer byte
strings are embedded.
-/

namespace VG.Test.Ed448

open Lean Elab Command Spec.Ed448

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
  context : List Byte := []
  signature : List Byte := []

/-- Collect only indented hex lines under each recognized field, skipping
page headers and footers. Stop before the Ed448ph vectors. -/
def parseVectors (text : String) : Except String (List Vector) := do
  let lines := ((text.splitOn "\n").dropWhile
    (!·.startsWith "7.4.  Test Vectors for Ed448")).drop 1
  let lines := lines.takeWhile (!·.startsWith "7.5.  Test Vectors for Ed448ph")
  let mut vs : Array Vector := #[]
  let mut field := ""
  for line in lines do
    if !line.startsWith "   " then continue
    let t := String.ofList (line.toList.dropWhile (· == ' '))
    if t.startsWith "-----" && t != "-----" then
      vs := vs.push {}
      field := ""
    else if t == "ALGORITHM:" then field := ""
    else if t == "SECRET KEY:" then field := "seed"
    else if t == "PUBLIC KEY:" then field := "pk"
    else if t.startsWith "MESSAGE (length " then field := "message"
    else if t == "CONTEXT:" then field := "context"
    else if t == "SIGNATURE:" then field := "signature"
    else if !t.isEmpty && t.toList.all (fun c => (hexDigit c).isSome) then
      let bs ← hexBytes t.toList
      let some v := vs.back? | throw "hex data before the first test"
      let v ← match field with
        | "seed" => pure { v with seed := v.seed ++ bs }
        | "pk" => pure { v with pk := v.pk ++ bs }
        | "message" => pure { v with message := v.message ++ bs }
        | "context" => pure { v with context := v.context ++ bs }
        | "signature" => pure { v with signature := v.signature ++ bs }
        | _ => throw "hex data outside a recognized field"
      vs := vs.pop.push v
  unless vs.size == 9 do throw s!"expected 9 vectors, got {vs.size}"
  unless (vs.toList.map (·.message.length)) == [0, 1, 1, 11, 12, 13, 64, 256, 1023] do
    throw "incorrect message lengths"
  unless (vs.toList.map (·.context.length)) == [0, 0, 3, 0, 0, 0, 0, 0, 0] do
    throw "incorrect context lengths"
  return vs.toList

def checkVector (i : Nat) (v : Vector) : Except String Unit := do
  unless v.seed.length == 57 && v.pk.length == 57 && v.signature.length == 114 do
    throw s!"vector {i}: incorrect key/signature lengths"
  unless publicKey v.seed == v.pk do throw s!"vector {i}: public key mismatch"
  unless sign v.seed v.context v.message == v.signature do
    throw s!"vector {i}: signature mismatch"
  unless verify v.pk v.context v.message v.signature do
    throw s!"vector {i}: verification failed"
  for bs in [v.pk, v.signature.take 57] do
    let some p := decodePoint bs | throw s!"vector {i}: point did not decode"
    unless encodePoint p == bs do throw s!"vector {i}: point round trip failed"
  let (s, noncePrefix) := expandSecret v.seed
  unless s % 4 == 0 && 2 ^ 447 ≤ s && s < 2 ^ 448 do
    throw s!"vector {i}: pruning failed"
  unless scalarBase (encodeLE 57 s) == v.pk do throw s!"vector {i}: scalarBase failed"
  let r := scalarReduce (hash v.context (noncePrefix ++ v.message))
  let k := scalarReduce (hash v.context (v.signature.take 57 ++ v.pk ++ v.message))
  unless scalarBase r == v.signature.take 57 do throw s!"vector {i}: nonce point failed"
  unless scalarMulAdd r k (encodeLE 57 s) == v.signature.drop 57 do
    throw s!"vector {i}: scalarMulAdd failed"
  unless verifyEquation v.pk v.signature k do throw s!"vector {i}: verifyEquation failed"
  if verify v.pk v.context (v.message ++ [0]) v.signature then
    throw s!"vector {i}: accepted changed message"
  if verify v.pk (v.context ++ [0]) v.message v.signature then
    throw s!"vector {i}: accepted changed context"
  if verify v.pk v.context v.message (v.signature.set 0 (v.signature.getD 0 0 ^^^ 1)) then
    throw s!"vector {i}: accepted changed signature"
  let noncanonical := v.signature.take 57 ++ encodeLE 57 (decodeLE (v.signature.drop 57) + L)
  if verify v.pk v.context v.message noncanonical then throw s!"vector {i}: accepted S + L"
  if verify (v.pk.drop 1) v.context v.message v.signature ||
      verify (v.pk ++ [0]) v.context v.message v.signature ||
      verify v.pk v.context v.message (v.signature.drop 1) ||
      verify v.pk v.context v.message (v.signature ++ [0]) then
    throw s!"vector {i}: accepted incorrect length"

def checkBoundaries : Except String Unit := do
  let P := Spec.X448.P
  -- No reduction of a noncanonical y, for either sign, including y with
  -- bits 448–454 set.
  for y in (List.range 8).map (P + ·) ++ (List.range 7).map (fun i => 2 ^ (448 + i) + 1) do
    for signBit in [0, 1] do
      if (decodePoint (encodeLE 57 (y + signBit * 2 ^ 455))).isSome then
        throw "accepted noncanonical y"
  -- Both points with x = 0 must reject a set sign bit.
  for y in [1, P - 1] do
    if (decodePoint (encodeLE 57 (y + 2 ^ 455))).isSome then throw "accepted negative zero"
    unless (decodePoint (encodeLE 57 y)).isSome do throw "rejected positive zero"
  unless pointEqual (pointMul L basePoint) identity do throw "base point has wrong order"
  if pointEqual basePoint identity then throw "base point is the identity"
  unless pointEqual (pointAdd basePoint identity) basePoint do throw "identity addition failed"
  -- Pin the documented policy: there is no separate small-order rejection.
  let id := encodePoint identity
  let sig := id ++ encodeLE 57 0
  unless verify id [] [] sig do throw "identity-key policy changed"
  for s in [L, L + 1, 2 ^ 456 - 1] do
    if verify id [] [] (id ++ encodeLE 57 s) then throw "accepted S >= L"
  if verifyEquation id sig (encodeLE 56 0) then throw "accepted short challenge"
  -- No context longer than 255 bytes.
  if verify id (List.replicate 256 0) [] sig then throw "accepted a 256-byte context"
  unless verify id (List.replicate 255 0) [] sig do throw "rejected a 255-byte context"

/-- `verifyEquation` checks the cofactored equation: multiplying both sides
by 4 removes the torsion components of A and R. With the point `T = (1, 0)`
of order 4 as A or R and `S = 0`, the uncofactored equation `O = R + [k]A`
fails unless `R + [k]A = O`, but the cofactored one holds for every `R` and
`k`. The points are derived here, not embedded. -/
def checkCofactored : Except String Unit := do
  let some t := decodePoint (encodeLE 57 (2 ^ 455)) | throw "(1, 0) did not decode"
  unless pointEqual (pointMul 4 t) identity && !pointEqual (pointMul 2 t) identity do
    throw "(1, 0) does not have order 4"
  let pk := encodePoint t
  let message : List Byte := [0]
  for j in List.range 4 do
    let rr := encodePoint (pointMul j t)
    let sig := rr ++ encodeLE 57 0
    unless verify pk [] message sig do throw s!"R = [{j}]T: rejected a torsion signature"
    for k in List.range 4 do
      unless verifyEquation pk sig (encodeLE 57 k) do
        throw s!"R = [{j}]T, k = {k}: the equation is not cofactored"
  -- A torsion component of R does not change the result for a real key.
  let a := scalarBase (encodeLE 57 1)
  let some ap := decodePoint a | throw "B did not decode"
  let rr := encodePoint (pointAdd (pointMul 2 basePoint) t)
  let k := 3
  -- [4][S]B = [4]R + [4][k]B for S = 2 + k.
  unless verifyEquation (encodePoint ap) (rr ++ encodeLE 57 (2 + k)) (encodeLE 57 k) do
    throw "rejected R with a torsion component"
  if verifyEquation (encodePoint ap) (rr ++ encodeLE 57 (3 + k)) (encodeLE 57 k) then
    throw "accepted the wrong S"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "rfc8032" / "rfc8032.txt")
  let result := do
    let vs ← parseVectors text
    for (v, i) in vs.zipIdx do checkVector i v
    checkBoundaries
    checkCofactored
  match result with
  | .ok () => pure ()
  | .error e => throwError "rfc8032.txt: {e}"

end VG.Test.Ed448
