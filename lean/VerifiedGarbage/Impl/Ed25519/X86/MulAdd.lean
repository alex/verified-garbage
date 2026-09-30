import VerifiedGarbage.Impl.Ed25519.X86.Scalar

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

/-- The addend contributes only to the low eight columns. -/
def scalarMulTerms (k : Nat) : List Term :=
  prodTerms 256 288 k ++ if k < 8 then [.addM (320 + 4 * k)] else []

def scalarWideMul : List Instr := zeroAcc ++ cols 128 16 scalarMulTerms
end VG.Impl.Ed25519.X86
