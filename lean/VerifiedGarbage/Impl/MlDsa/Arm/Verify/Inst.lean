import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Verify
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint

/-!
# ML-DSA verification on 32-bit ARM, with this library's primitives

`verify` (`Verify.lean`) called with the ARM implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

namespace VG.Impl.MlDsa.Arm.Verify

open VG.Arm

/-- The ARM implementations of the primitives verification calls. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  ball := Sample.sampleInBall
  useHint := Round.useHint
  simpleBitPack := Pack.simpleBitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack
  normLt := Round.normLt

/-- `vg_mldsa44_verify` -/
def verify44 : Prog isa := verify prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_verify` -/
def verify65 : Prog isa := verify prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_verify` -/
def verify87 : Prog isa := verify prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.Arm.Verify
