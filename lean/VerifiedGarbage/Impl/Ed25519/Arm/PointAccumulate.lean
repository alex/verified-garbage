import VerifiedGarbage.Impl.Ed25519.Arm.PointPowers
import VerifiedGarbage.Impl.Ed25519.Arm.PointSelect

/-! Descending scalar bits. Sixteen bits at workspace bytes 32–47 are
expanded from two scalar bytes for each checkpoint batch. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def scalarBitMask : List Instr :=
  [.dp .add .r2 .r0 (.reg .r11), .ldrb .r9 .r2 32, .dp .sub .r9 .r9 (.imm 1)]

def prepareAdd : Prog isa :=
  .seq savePoint (.seq (.block (tableAddr 5696 ++ pointFromTable))
    (.seq copyPointToQ restorePoint))

def pointAccumulate : Prog isa :=
  .seq prepareAdd (.seq pointAdd (.block (scalarBitMask ++ pointSelect)))

def accumulateBody : Prog isa :=
  .seq (.block [.dp .sub .r11 .r11 (.imm 1)])
    (.seq pointAccumulate (.block [.cmp .r11 (.imm 0)]))

def accumulate16 : Prog isa :=
  .seq (.block [.movw .r11 16]) (.loop accumulateBody .ne)

end VG.Impl.Ed25519.Arm
