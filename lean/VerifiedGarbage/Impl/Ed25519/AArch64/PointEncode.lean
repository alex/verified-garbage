import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory
import VerifiedGarbage.Impl.Ed25519.AArch64.Power

/-! Affine conversion and canonical point encoding into x4–x7. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def affineOps : List FieldOp := [.mul 0 0 15, .mul 1 1 15]
def pointAffine : Prog isa := .seq invert (.block (fieldCode affineOps))

def pointSign : List Instr :=
  [.movz .w .x9 1 0, .logic .and .x .x19 .x4 .x9, .lsl .x .x19 .x19 63]

def pointEncode : Prog isa :=
  .seq pointAffine (.block (freeze 64 ++ pointSign ++ freeze 96 ++ [.add .x .x7 .x7 .x19]))

end VG.Impl.Ed25519.AArch64
