import VerifiedGarbage.Impl.Ed25519.X86_64.Bits
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul

/-! Multiply the point in scratch by an unsigned scalar supplied in memory. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- Expand the scalar bits and initialize the curve constant. -/
def pointFromScalarPrepare (count : Nat) : Prog isa :=
  .seq (scalarBits (2 * count)) (.block (constField 16 Spec.Ed25519.d))

/-- Read 2*count bytes through rsi, with 16 bits per checkpoint batch. -/
def pointFromScalar (count : Nat) : Prog isa :=
  .seq (pointFromScalarPrepare count) (pointMultiply count)

end VG.Impl.Ed25519.X86_64
