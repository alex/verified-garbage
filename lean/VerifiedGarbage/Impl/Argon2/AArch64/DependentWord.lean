import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillKernel

/-! Read the previous cell's first word for data-dependent addressing. Only the
public loop position and matrix base determine the read address.
-/

namespace VG.Impl.Argon2.AArch64.DependentWord

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def args : List Instr := [mov .x3 .x0, mov .x8 .x24].flatten

def pointer : Prog isa := .seq (.block FillKernel.matrix)
  (.seq FillColumn.code (.seq (.block args) BlockAddress.code))

def read : List Instr := [load .x0 .x8 0].flatten

def code : Prog isa := .seq pointer (.block read)

end VG.Impl.Argon2.AArch64.DependentWord
