import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! Fixed-base multiplication with a comb of precomputed, cached multiples of the base point. -/
namespace VG.Impl.Ed25519.X86_64
open VG.X86_64

def scalarBasePrecomputedEngine (fld : Arith) : Prog isa :=
  .seq (scalarBasePrepare fld) (.seq (combMultiply fld) (pointEncode fld))

def scalarBase_precomputed (fld : Arith) : Prog isa :=
  scalarBaseWith (scalarBasePrecomputedEngine fld)

end VG.Impl.Ed25519.X86_64
