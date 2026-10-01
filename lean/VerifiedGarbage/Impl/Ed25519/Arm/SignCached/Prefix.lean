import VerifiedGarbage.TCB.Arm.Isa

namespace VG.Impl.Ed25519.Arm.SignCached
open VG.Arm

def copyWord (k : Nat) : List Instr :=
  [.ldrSp .r0 (216 + 4 * k), .addSp .r12 0, .str .r0 .r12 (56 + 4 * k)]

def copyPrefix : List Instr := (List.range 8).flatMap copyWord

end VG.Impl.Ed25519.Arm.SignCached
