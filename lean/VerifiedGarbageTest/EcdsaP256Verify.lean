import Lean.Elab.Command
import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Spec.Sha512

/-!
# ECDSA P-256 signature verification specification tests

The 75 P-256 vectors of NIST CAVP's ECDSA signature verification test
(`SigVer.rsp`, vendored byte for byte), 15 with each of SHA-1, SHA-224,
SHA-256, SHA-384 and SHA-512: each gives a message, a public key `Q`, a
signature `(R, S)` and whether it is valid (`P`) or not (`F`, with the
changed field), so they test `verify` on keys, hashes shorter and longer than
`n` and signatures that are valid and not. The signatures whose fields are
out of range, and the keys that are not valid, are derived from the vectors
and from the curve's parameters.
-/

namespace VG.Test.EcdsaP256Verify

open Lean Elab Command Spec.Weierstrass Spec.Ecdsa

def C : Curve := Spec.P256.curve

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (fun acc c => match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"invalid hexadecimal digit {c}") 0

def hexBytes (s : String) : Except String (List Byte) := do
  let cs := s.toList
  unless cs.length % 2 == 0 do throw s!"odd hexadecimal string {s}"
  (List.range (cs.length / 2)).mapM fun i => do
    let some hi := hexDigit cs[2 * i]! | throw s!"invalid hexadecimal digit in {s}"
    let some lo := hexDigit cs[2 * i + 1]! | throw s!"invalid hexadecimal digit in {s}"
    pure (BitVec.ofNat 8 (16 * hi + lo))

structure Case where
  hash : String
  msg : List Byte
  qx : Nat
  qy : Nat
  r : Nat
  s : Nat
  valid : Bool

def hashes : List (String × (List Byte → List Byte)) :=
  [("SHA-1", Spec.Sha1.hash), ("SHA-224", Spec.Sha256.sha224), ("SHA-256", Spec.Sha256.hash),
    ("SHA-384", Spec.Sha512.sha384), ("SHA-512", Spec.Sha512.sha512)]

/-- The vectors of the `[P-256,SHA-*]` sections. -/
def parse (text : String) : Except String (List Case) := do
  let lines := (text.splitOn "\n").map fun l => String.ofList (l.toList.filter (· != '\r'))
  let mut vs : Array Case := #[]
  let mut sect : Option String := none
  let mut cur : List (String × String) := []
  for line in lines do
    if line.startsWith "[" then
      sect := if line.startsWith "[P-256," then some (String.ofList ((line.toList.drop 7).dropLast))
        else none
      cur := []
    else if let some h := sect then
      match line.splitOn " = " with
      | [k, v] =>
        if k == "Result" then
          let get (k : String) : Except String String := match cur.lookup k with
            | some v => pure v
            | none => throw s!"missing {k}"
          let msg ← hexBytes (← get "Msg")
          let qx ← hexNat (← get "Qx")
          let qy ← hexNat (← get "Qy")
          let r ← hexNat (← get "R")
          let sv ← hexNat (← get "S")
          vs := vs.push { hash := h, msg, qx, qy, r, s := sv, valid := v.startsWith "P" }
          cur := []
        else cur := cur ++ [(k, v)]
      | _ => pure ()
  unless vs.size == 75 do throw s!"expected 75 vectors, got {vs.size}"
  return vs.toList

def point (x y : Nat) : List Byte := 4 :: (toBytes 32 x ++ toBytes 32 y)

def checkVector (v : Case) : Except String Unit := do
  let some (_, H) := hashes.find? (·.1 == v.hash) | throw s!"unknown hash {v.hash}"
  let digest := H v.msg
  let e := hashToInt C digest
  let sig := toBytes 32 v.r ++ toBytes 32 v.s
  unless verify C (point v.qx v.qy) e sig == v.valid do
    throw s!"{v.hash}, R = {v.r}: expected {v.valid}"
  -- The contract's hash argument: the leftmost 32 octets, or the hash
  -- padded on the left with zeros, which `hashToInt` reads as `e`.
  let arg := if digest.length ≥ 32 then digest.take 32
    else List.replicate (32 - digest.length) 0 ++ digest
  unless hashToInt C arg == e do throw s!"{v.hash}: truncated hash disagrees"
  if v.valid then
    -- Another hash, or a signature with `r` and `s` exchanged or out of
    -- range, is not valid.
    if verify C (point v.qx v.qy) (e + 1) sig then throw "accepted another hash"
    if verify C (point v.qx v.qy) e (toBytes 32 v.s ++ toBytes 32 v.r) then
      throw "accepted r and s exchanged"
    for (r, s) in [(0, v.s), (v.r, 0), (v.r + C.n, v.s), (v.r, v.s + C.n)] do
      if r < 2 ^ 256 ∧ s < 2 ^ 256 then
        if verify C (point v.qx v.qy) e (toBytes 32 r ++ toBytes 32 s) then
          throw s!"accepted r = {r}, s = {s}"
    -- The key must be uncompressed, below `p` and on the curve.
    for pub in [0x02 :: (point v.qx v.qy).tail, 0x00 :: (point v.qx v.qy).tail,
        point v.qx (v.qy + 1), point (v.qx + C.p) v.qy, point v.qx (C.p - v.qy)] do
      if verify C pub e sig then throw s!"accepted the key {pub}"
    -- `(x, p - y)` is `-Q`: on the curve, so only the signature fails.
    unless (Spec.EcKey.decodePublicKey C (point v.qx (C.p - v.qy))).isSome do throw "-Q rejected"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp-ecdsa" / "SigVer.rsp")
  let result := do
    let vs : List Case ← parse text
    unless vs.any (·.valid) && vs.any (!·.valid) do
      throw "expected valid and invalid vectors"
    for v in vs do checkVector v
  match result with
  | .ok () => pure ()
  | .error e => throwError "SigVer.rsp: {e}"

end VG.Test.EcdsaP256Verify
