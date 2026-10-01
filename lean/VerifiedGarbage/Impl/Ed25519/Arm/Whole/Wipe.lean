import VerifiedGarbage.TCB.Arm.Isa

namespace VG.Impl.Ed25519.Arm.Whole
open VG.Arm

/-- Clear a frame word using only caller-saved registers. -/
def zeroWord (k : Nat) : List Instr :=
  [.addSp .r12 0, .movw .r0 0, .str .r0 .r12 (4 * k)]

/-- Word indices, each four bytes. -/
def zeroWords (start count : Nat) : List Instr :=
  (List.range count).flatMap fun j => zeroWord (start + j)

end VG.Impl.Ed25519.Arm.Whole
