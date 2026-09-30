import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.X86.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-!
# ML-DSA verification on x86 (32-bit), with this library's primitives

`verify` (`Verify.lean`) called with the x86 implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

namespace VG.Impl.MlDsa.X86.Verify

open VG.X86

/-- The x86 implementations of the primitives verification calls. -/
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

end VG.Impl.MlDsa.X86.Verify
