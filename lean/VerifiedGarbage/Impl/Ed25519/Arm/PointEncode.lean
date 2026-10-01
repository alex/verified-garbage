import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Impl.Ed25519.Arm.Freeze

/-! Normalize extended coordinates, then form the compressed point in FR. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def affineOps : List FieldOp := [.mul 0 0 15, .mul 1 1 15]
def pointAffine : Prog isa := .seq invert (fieldCode affineOps)

def pointSign : List Instr :=
  [.ldr .r3 .r0 FR, .dp .and .r10 .r3 (.imm 1), .mov .r10 (.shifted .r10 .lsl 15)]

def encodeSign : List Instr :=
  [.ldr .r3 .r0 (FR + 60), .dp .add .r3 .r3 (.reg .r10), .str .r3 .r0 (FR + 60)]

def pointEncode : Prog isa :=
  .seq pointAffine (.block (freeze 0 ++ pointSign ++ freeze 1 ++ encodeSign))

end VG.Impl.Ed25519.Arm
