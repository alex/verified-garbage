import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! # The two eligible reference windows

`x5` is the pass, `x20` the lane length, `x21` the segment length, `x22`
the slice and `x23` the index within the segment. `x2` receives the count
for the current lane; `x3` receives the count for another lane. Only the
public pass controls a branch. The zero-index adjustment uses a borrow mask.
-/

namespace VG.Impl.Argon2.AArch64.CountCandidates

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def first : List Instr := [mov .x8 .x21, mul .x22, mov .x3 .x8, mov .x2 .x8, add .x2 .x23, subi .x2 1].flatten

def later : List Instr := [mov .x8 .x20, sub .x8 .x21, mov .x3 .x8, mov .x2 .x8, add .x2 .x23, subi .x2 1].flatten

def adjust : List Instr := [mov .x4 .x23, subi .x4 1, sbb .x5, add .x3 .x5].flatten

def code : Prog isa :=
  .seq (.block [comparei .x5 0].flatten)
    (.seq (.ite (.zero .x .x15) (.block first) (.block later)) (.block adjust))

end VG.Impl.Argon2.AArch64.CountCandidates
