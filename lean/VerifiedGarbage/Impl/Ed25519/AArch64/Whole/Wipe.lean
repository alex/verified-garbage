import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.Ed25519.AArch64.Whole
open VG.AArch64

/-- Clear one frame word without using callee-saved registers. -/
def zeroWord (k : Nat) : List Instr :=
  [.addSp .x15 0, .movz .x .x14 0 0, .str .x .x14 .x15 (8 * k)]

/-- Word indices, each eight bytes. -/
def zeroWords (start count : Nat) : List Instr :=
  (List.range count).flatMap fun j => zeroWord (start + j)

end VG.Impl.Ed25519.AArch64.Whole
