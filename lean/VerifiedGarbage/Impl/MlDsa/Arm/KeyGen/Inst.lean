import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode

/-!
# ML-DSA key generation on 32-bit ARM, with this library's primitives

`keyGen` (`KeyGen.lean`) called with the ARM implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

namespace VG.Impl.MlDsa.Arm.KeyGen

open VG.Arm

/-- The ARM implementations of the primitives key generation calls. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  add := Arith.add
  rejNtt := Sample.rejNTT
  rejBounded := Sample.rejBounded
  power2Round := Round.power2Round
  simpleBitPack := Pack.simpleBitPack
  bitPack := Pack.bitPack

/-- `vg_mldsa44_keygen` -/
def keyGen44 : Prog isa := keyGen prims Spec.MlDsa.mlDsa44
/-- `vg_mldsa65_keygen` -/
def keyGen65 : Prog isa := keyGen prims Spec.MlDsa.mlDsa65
/-- `vg_mldsa87_keygen` -/
def keyGen87 : Prog isa := keyGen prims Spec.MlDsa.mlDsa87

end VG.Impl.MlDsa.Arm.KeyGen
