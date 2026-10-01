import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Fixed-base multiplication with the precomputed, cached powers of the base point. -/
namespace VG.Impl.Ed25519.X86_64
open VG.X86_64

def scalarBasePrecomputedEngine : Prog isa :=
  .seq scalarBasePrepare (.seq baseMultiply pointEncode)

def scalarBase_precomputed : Prog isa :=
  scalarBaseWith scalarBasePrecomputedEngine

end VG.Impl.Ed25519.X86_64
