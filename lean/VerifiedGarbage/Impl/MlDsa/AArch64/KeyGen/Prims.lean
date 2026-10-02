import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Hint

/-!
# ML-DSA on AArch64: key generation and verification with this library's primitives

`vg_mldsa{44,65,87}_keygen` and `vg_mldsa{44,65,87}_verify`, calling the
AArch64 implementations of the primitives (`prims`).
-/

namespace VG.Impl.MlDsa.AArch64.KeyGen

open VG.AArch64 VG.Impl.MlDsa.AArch64.Call

/-- The AArch64 primitives. -/
def primsWith (c : Impl.Sha3.AArch64.Callee) : Prims where
  suffix := c.suffix
  ntt := Arith.Neon.ntt
  invNtt := Arith.Neon.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  sub := Arith.sub
  rejNtt := Sample.rejNTTWith c
  rej4 := Sample.Rej4.rejNTT4With c.pairedSha3
  rejBounded := Sample.rejBoundedWith c
  ball := Sample.sampleInBallWith c
  power2Round := Round.power2Round
  useHint := Round.useHint
  normLt := Round.normLt
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack

def keyGen44With (c : Impl.Sha3.AArch64.Callee) : Prog isa := keyGenWith c (primsWith c) Spec.MlDsa.mlDsa44
def keyGen65With (c : Impl.Sha3.AArch64.Callee) : Prog isa := keyGenWith c (primsWith c) Spec.MlDsa.mlDsa65
def keyGen87With (c : Impl.Sha3.AArch64.Callee) : Prog isa := keyGenWith c (primsWith c) Spec.MlDsa.mlDsa87

def verify44With (c : Impl.Sha3.AArch64.Callee) : Prog isa := Verify.verifyWith c (primsWith c) Spec.MlDsa.mlDsa44
def verify65With (c : Impl.Sha3.AArch64.Callee) : Prog isa := Verify.verifyWith c (primsWith c) Spec.MlDsa.mlDsa65
def verify87With (c : Impl.Sha3.AArch64.Callee) : Prog isa := Verify.verifyWith c (primsWith c) Spec.MlDsa.mlDsa87

def prims := primsWith .scalar
def keyGen44 := keyGen44With .scalar
def keyGen65 := keyGen65With .scalar
def keyGen87 := keyGen87With .scalar
def verify44 := verify44With .scalar
def verify65 := verify65With .scalar
def verify87 := verify87With .scalar

end VG.Impl.MlDsa.AArch64.KeyGen
