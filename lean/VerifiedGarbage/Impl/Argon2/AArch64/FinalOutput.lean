import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.HPrime
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Final H′: matrix block zero is the input, using the derivation's hash backend. -/

namespace VG.Impl.Argon2.AArch64.FinalOutput

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def args : List Instr :=
  [load .x0 .x19 232, imm .x1 1024, load .x2 .x19 256, load .x3 .x19 264, load .x4 .x19 248].flatten

def code (name : String) (h : HPrime.Hash) : Prog isa :=
  .seq (.block args) (.call name (HPrime.code h))

end VG.Impl.Argon2.AArch64.FinalOutput
