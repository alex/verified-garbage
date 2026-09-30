import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
import VerifiedGarbage.Impl.Ed25519.AArch64.PointMul

/-! Multiply the point in scratch by an unsigned scalar supplied in memory. -/

namespace VG.Impl.Ed25519.AArch64

open VG.AArch64

/-- Expand the scalar bits and initialize the curve constant. -/
def pointFromScalarPrepare (count : Nat) : Prog isa :=
  .seq (scalarBits (2 * count)) (.block (constField 16 Spec.Ed25519.d))

/-- Read 2*count bytes through x1, with 16 bits per checkpoint batch. -/
def pointFromScalar (count : Nat) : Prog isa :=
  .seq (pointFromScalarPrepare count) (pointMultiply count)

end VG.Impl.Ed25519.AArch64
