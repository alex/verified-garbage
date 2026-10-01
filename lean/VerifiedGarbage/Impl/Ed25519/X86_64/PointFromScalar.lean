import VerifiedGarbage.Impl.Ed25519.X86_64.Bits
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul

/-! Expand an unsigned scalar supplied in memory into bits, for a multiplication. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- Expand the scalar bits and initialize the curve constant. -/
def pointFromScalarPrepare (count : Nat) : Prog isa :=
  .seq (scalarBits (2 * count)) (.block (constField 16 Spec.Ed25519.d))

end VG.Impl.Ed25519.X86_64
