import Lean.Elab.Command
import VerifiedGarbage.Spec.Ecdh.P256

/-!
# P-256 public key and ECDH specification tests

The 25 P-256 vectors of NIST CAVP's SP 800-56A ECC CDH primitive test
(`KAS_ECC_CDH_PrimitiveTest.txt`, vendored byte for byte): each gives the
peer's public key `QCAVS`, the private key `dIUT`, its public key `QIUT` and
the shared secret `ZIUT`, so they test `publicKey`, `encodePoint`,
`decodePublicKey` and `exchange`. The invalid public keys are derived from
them and from the curve's parameters.
-/

namespace VG.Test.EcdhP256

open Lean Elab Command Spec.Weierstrass Spec.EcKey Spec.Ecdh

def C : Curve := Spec.P256.curve

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String Nat :=
  s.toList.foldlM (fun acc c => match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"invalid hexadecimal digit {c}") 0

structure Vector where
  qx : Nat
  qy : Nat
  d : Nat
  ux : Nat
  uy : Nat
  z : Nat

/-- The `[P-256]` section's vectors. -/
def parse (text : String) : Except String (List Vector) := do
  let lines := (text.splitOn "\n").map fun l => String.ofList (l.toList.filter (· != '\r'))
  let lines := (lines.dropWhile (· != "[P-256]")).drop 1
  let lines := lines.takeWhile (!·.startsWith "[")
  let mut vs : Array Vector := #[]
  let mut cur : List (String × Nat) := []
  for line in lines do
    match line.splitOn " = " with
    | [k, v] =>
      if k == "COUNT" then cur := []
      else
        cur := cur ++ [(k, ← hexNat v)]
        if k == "ZIUT" then
          let get (k : String) : Except String Nat := match cur.lookup k with
            | some v => pure v
            | none => throw s!"missing {k}"
          let qx ← get "QCAVSx"
          let qy ← get "QCAVSy"
          let d ← get "dIUT"
          let ux ← get "QIUTx"
          let uy ← get "QIUTy"
          let z ← get "ZIUT"
          vs := vs.push { qx, qy, d, ux, uy, z }
    | _ => pure ()
  unless vs.size == 25 do throw s!"expected 25 vectors, got {vs.size}"
  return vs.toList

/-- `04 ‖ x ‖ y`, from the integers. -/
def point (x y : Nat) : List Byte := 4 :: (toBytes 32 x ++ toBytes 32 y)

def checkVector (i : Nat) (v : Vector) : Except String Unit := do
  let U : Point C := .affine (Fin.ofNat C.p v.ux) (Fin.ofNat C.p v.uy)
  unless publicKey C v.d == some U do throw s!"vector {i}: public key mismatch"
  unless encodePoint U == point v.ux v.uy do throw s!"vector {i}: encoding mismatch"
  unless decodePublicKey C (point v.ux v.uy) == some U do throw s!"vector {i}: decoding failed"
  unless exchange C v.d (point v.qx v.qy) == some (toBytes 32 v.z) do
    throw s!"vector {i}: shared secret mismatch"
  -- Both sides agree, when the peer's key is the other key pair's.
  let Q : Point C := .affine (Fin.ofNat C.p v.qx) (Fin.ofNat C.p v.qy)
  unless mul v.d Q == .affine (Fin.ofNat C.p v.z) (match mul v.d Q with
      | .affine _ y => y | .infinity => 0) do
    throw s!"vector {i}: dQ"
  -- Invalid public keys: off the curve, a coordinate not below p, the
  -- wrong prefix or length, and compressed.
  let bad := [point v.qx (v.qy + 1), (0 : Byte) :: (point v.qx v.qy).drop 1,
    (point v.qx v.qy).take 64, point v.qx v.qy ++ [0],
    (if v.qy % 2 = 0 then 2 else 3) :: toBytes 32 v.qx]
  for (b, j) in bad.zipIdx do
    if (exchange C v.d b).isSome || (decodePublicKey C b).isSome then
      throw s!"vector {i}: accepted invalid public key {j}"
  for d in [0, C.n, C.n + v.d] do
    if (exchange C d (point v.qx v.qy)).isSome || (publicKey C d).isSome then
      throw s!"vector {i}: accepted private key {d}"

def checkCurve : Except String Unit := do
  -- A coordinate not below `p` that is congruent to a valid one.
  let gx := C.gx
  let gy := C.gy
  unless decodePublicKey C (point gx gy) == some (G C) do throw "G did not decode"
  if 2 ^ 256 > gx + C.p then
    if (decodePublicKey C (point (gx + C.p) gy)).isSome then throw "accepted x ≥ p"
  if 2 ^ 256 > gy + C.p then
    if (decodePublicKey C (point gx (gy + C.p))).isSome then throw "accepted y ≥ p"
  if (decodePublicKey C [0]).isSome then throw "accepted O"
  unless encodePoint (.infinity : Point C) == [0] do throw "O encoding"
  unless publicKey C 1 == some (G C) do throw "1G ≠ G"
  unless publicKey C (C.n - 1) == some (.affine (Fin.ofNat C.p gx) (-(Fin.ofNat C.p gy))) do
    throw "(n-1)G ≠ -G"

run_cmd do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent >>= (·.parent) >>= (·.parent)
    | throwError "no repository root above {file}"
  let text ← IO.FS.readFile (root / "vectors" / "nist-cavp" / "ecc-cdh" /
    "KAS_ECC_CDH_PrimitiveTest.txt")
  let result := do
    let vs ← parse text
    for (v, i) in vs.zipIdx do checkVector i v
    checkCurve
  match result with
  | .ok () => pure ()
  | .error e => throwError "KAS_ECC_CDH_PrimitiveTest.txt: {e}"

end VG.Test.EcdhP256
