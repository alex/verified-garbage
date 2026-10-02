import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! Lane-major matrix addressing. The matrix base is in `x4`, the lane
in `x8`, the column in `x3`, and the lane length in `x20`. The resulting
block pointer is returned in `x8`. Scalar multiplication and ten doublings
work on the baseline ISA, including when the reference coordinates are secret.
-/

namespace VG.Impl.Argon2.AArch64.BlockAddress

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def flatten : List Instr := [mul .x20, add .x8 .x3].flatten

def scale : List Instr := (List.replicate 10 (add .x8 .x8)).flatten

def code : Prog isa :=
  .seq (.block flatten) (.seq (.block scale) (.block [add .x8 .x4].flatten))

end VG.Impl.Argon2.AArch64.BlockAddress
