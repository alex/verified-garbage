import VerifiedGarbage.Impl.Argon2.X86_64.FillSegment
import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache

/-! Reset the address cache per segment and skip the two initialized cells. -/

namespace VG.Impl.Argon2.X86_64.SegmentSetup

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def reset : Prog isa := .seq (.block [.mov .rax (.imm 0)]) (.block AddressCache.save)

def first : List Instr := [
  .mov .rcx (.mem (at_ .rbp 0)), .alu .or .rcx (.reg .r14), .alu .cmp .rcx (.imm 0)]

def index : Prog isa := .seq (.block first)
  (.ite .e (.block [.mov .r15 (.imm 2)]) (.block [.mov .r15 (.imm 0)]))

def check : List Instr := [.alu .cmp .r15 (.reg .r13)]

def prepare : Prog isa := .seq reset index

def code : Prog isa := .seq prepare (.seq (.block check) (.ite .b FillSegment.loop (.block [])))

end VG.Impl.Argon2.X86_64.SegmentSetup
