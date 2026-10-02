import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillIteration

/-! Advance the public pass counter stored in the mutable header. -/

namespace VG.Impl.Argon2.AArch64.FillIterations

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def increment : List Instr := [load .x8 .x19 0, addi .x8 1].flatten

def saveCheck : List Instr := [store .x19 0 .x8, comparem .x8 .x19 72].flatten

def advance : Prog isa := .seq (.block increment) (.block saveCheck)

def body : Prog isa := .seq FillIteration.code advance

def loop : Prog isa := .loop body (.nonzero .x .x14)

end VG.Impl.Argon2.AArch64.FillIterations
