import VerifiedGarbage.Impl.Argon2.X86_64.SegmentSetup

/-! Fill one slice's lanes serially, advancing only the public lane coordinate. -/

namespace VG.Impl.Argon2.X86_64.FillLanes

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def advance : List Instr := [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.mem (at_ .rbp 184))]

def body : Prog isa := .seq SegmentSetup.code (.block advance)

def loop : Prog isa := .loop body .b

end VG.Impl.Argon2.X86_64.FillLanes
