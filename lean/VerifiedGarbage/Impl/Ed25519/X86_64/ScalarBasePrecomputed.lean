import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Fixed-base multiplication with the precomputed, cached powers of the base point. -/
namespace VG.Impl.Ed25519.X86_64
open VG.X86_64

def scalarBasePrecomputedEngine (fld : Arith) : Prog isa :=
  .seq (scalarBasePrepare fld) (.seq (baseMultiply fld) (pointEncode fld))

def scalarBase_precomputed (fld : Arith) : Prog isa :=
  scalarBaseWith (scalarBasePrecomputedEngine fld)

end VG.Impl.Ed25519.X86_64
