import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Impl.MlDsa.AArch64.Round.Round
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

open VG.AArch64

/-- The AArch64 primitives. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  rejBounded := Sample.rejBounded
  ball := Sample.sampleInBall
  power2Round := Round.power2Round
  useHint := Round.useHint
  normLt := Round.normLt
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack

def keyGen44 : Prog isa := keyGen prims Spec.MlDsa.mlDsa44
def keyGen65 : Prog isa := keyGen prims Spec.MlDsa.mlDsa65
def keyGen87 : Prog isa := keyGen prims Spec.MlDsa.mlDsa87

def verify44 : Prog isa := Verify.verify prims Spec.MlDsa.mlDsa44
def verify65 : Prog isa := Verify.verify prims Spec.MlDsa.mlDsa65
def verify87 : Prog isa := Verify.verify prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.AArch64.KeyGen
