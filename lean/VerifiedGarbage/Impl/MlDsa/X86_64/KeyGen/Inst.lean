import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.X86_64.Round.Round
import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode

/-!
# ML-DSA key generation on x86-64, with this library's primitives

`keyGen` (`KeyGen.lean`) called with the x86-64 implementations of the
primitives it calls (`Arith/`, `Sample/`, `Round/`, `Pack/`), with the
polynomial arithmetic of a `Backend` (`primsWith`).
-/

namespace VG.Impl.MlDsa.X86_64.KeyGen

open VG.X86_64

/-- The x86-64 implementations of the primitives key generation calls. -/
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

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Arith.Backend) : Prims :=
  { prims with
    ntt := B.ntt
    invNtt := B.invNtt
    mul := B.mul
    mulAdd := B.mulAdd
    add := B.add
    sfx := B.sfx }

end VG.Impl.MlDsa.X86_64.KeyGen
