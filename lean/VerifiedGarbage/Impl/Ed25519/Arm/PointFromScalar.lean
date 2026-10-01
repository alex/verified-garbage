import VerifiedGarbage.Impl.Ed25519.Arm.PointMul

/-! Multiply the working point by the scalar at r12, with a public byte count. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def pointFromScalar (count : Nat) : Prog isa :=
  .seq (.block [.str .r12 .r0 52]) (.seq (fieldCode [.const 16 Spec.Ed25519.d]) (pointMultiply count))

end VG.Impl.Ed25519.Arm
