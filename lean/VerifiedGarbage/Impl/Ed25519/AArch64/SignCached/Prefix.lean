import VerifiedGarbage.TCB.AArch64.Isa

namespace VG.Impl.Ed25519.AArch64.SignCached
open VG.AArch64

/-- Copy the upper half of the expanded seed before the digest is reused. -/
def copyWord (k : Nat) : List Instr :=
  [.ldrSp .x0 (224 + 8 * k), .addSp .x15 64, .str .x .x0 .x15 (8 * k)]

def copyPrefix : List Instr := (List.range 4).flatMap copyWord

end VG.Impl.Ed25519.AArch64.SignCached
