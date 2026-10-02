import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Determine the segment's address mode from public variant, pass and slice.
The mask in `x6` is one for independent addressing and zero otherwise.
-/

namespace VG.Impl.Argon2.AArch64.AddressMode

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def kind : List Instr := [load .x8 .x19 112, mov .x6 .x8, logici .eor .x6 1, comparei .x6 1, sbb .x6, mov .x4 .x8, logici .eor .x4 2, comparei .x4 1, sbb .x4].flatten

def pass : List Instr := [load .x5 .x19 0, comparei .x5 1, sbb .x5].flatten

def slice : List Instr := [comparei .x22 2, sbb .x7, logic .and .x4 .x5, logic .and .x4 .x7, logic .orr .x6 .x4, logici .and .x6 1].flatten

def code : Prog isa := .seq (.block kind) (.seq (.block pass) (.block slice))

end VG.Impl.Argon2.AArch64.AddressMode
