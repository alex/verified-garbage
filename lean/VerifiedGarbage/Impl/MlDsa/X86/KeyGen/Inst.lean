import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.X86.Round.Round
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode

/-!
# ML-DSA key generation on x86 (32-bit), with this library's primitives

`keyGen` (`KeyGen.lean`) called with the x86 implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`).
-/

namespace VG.Impl.MlDsa.X86.KeyGen

open VG.X86

/-- The x86 implementations of the primitives key generation calls. -/
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

end VG.Impl.MlDsa.X86.KeyGen
