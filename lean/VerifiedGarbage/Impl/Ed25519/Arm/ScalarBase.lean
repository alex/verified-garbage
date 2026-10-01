import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI

/-! Ed25519 base-point multiplication with the reviewed zero-stack ARM ABI. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def scalarBaseEngine : Prog isa :=
  .seq (.block initFields) (.seq (constPoint Spec.Ed25519.basePoint)
    (.seq (pointFromScalar 16) pointEncode))

def scalarBaseSetup : List Instr :=
  scalarSave .r2 ++ [.str .r0 .r2 48, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1)]

def scalarBaseFinish : List Instr := [.ldr .r12 .r0 48] ++ packField FR 0 ++ scalarRestore

def scalarBase : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq scalarBaseEngine (.block scalarBaseFinish))

end VG.Impl.Ed25519.Arm
