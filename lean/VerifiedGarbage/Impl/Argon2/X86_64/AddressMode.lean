import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Determine the segment's address mode from public variant, pass and slice.
The mask in `r10` is one for independent addressing and zero otherwise.
-/

namespace VG.Impl.Argon2.X86_64.AddressMode

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def kind : List Instr := [
  .mov .rax (.mem (at_ .rbp 112)),
  .mov .r10 (.reg .rax), .alu .xor .r10 (.imm 1), .alu .cmp .r10 (.imm 1), .alu .sbb .r10 (.reg .r10),
  .mov .r8 (.reg .rax), .alu .xor .r8 (.imm 2), .alu .cmp .r8 (.imm 1), .alu .sbb .r8 (.reg .r8)]

def pass : List Instr := [
  .mov .r9 (.mem (at_ .rbp 0)), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9)]

def slice : List Instr := [
  .alu .cmp .r14 (.imm 2), .alu .sbb .r11 (.reg .r11),
  .alu .and .r8 (.reg .r9), .alu .and .r8 (.reg .r11), .alu .or .r10 (.reg .r8), .alu .and .r10 (.imm 1)]

def code : Prog isa := .seq (.block kind) (.seq (.block pass) (.block slice))

end VG.Impl.Argon2.X86_64.AddressMode
