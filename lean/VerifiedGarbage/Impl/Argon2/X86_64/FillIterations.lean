import VerifiedGarbage.Impl.Argon2.X86_64.FillIteration

/-! Advance the public pass counter stored in the mutable header. -/

namespace VG.Impl.Argon2.X86_64.FillIterations

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def increment : List Instr := [.mov .rax (.mem (at_ .rbp 0)), .alu .add .rax (.imm 1)]

def saveCheck : List Instr := [.store (at_ .rbp 0) .rax, .alu .cmp .rax (.mem (at_ .rbp 72))]

def advance : Prog isa := .seq (.block increment) (.block saveCheck)

def body : Prog isa := .seq FillIteration.code advance

def loop : Prog isa := .loop body .b

end VG.Impl.Argon2.X86_64.FillIterations
