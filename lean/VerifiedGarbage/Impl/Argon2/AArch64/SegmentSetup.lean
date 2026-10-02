import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.FillSegment
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCache

/-! Reset the address cache per segment and skip the two initialized cells. -/

namespace VG.Impl.Argon2.AArch64.SegmentSetup

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def reset : Prog isa := .seq (.block [imm .x8 0].flatten) (.block AddressCache.save)

def first : List Instr := [load .x3 .x19 0, logic .orr .x3 .x22, comparei .x3 0].flatten

def index : Prog isa := .seq (.block first)
  (.ite (.zero .x .x15) (.block [imm .x23 2].flatten) (.block [imm .x23 0].flatten))

def check : List Instr := [Instructions.compare .x23 .x21].flatten

def prepare : Prog isa := .seq reset index

def code : Prog isa := .seq prepare (.seq (.block check) (.ite (.nonzero .x .x14) FillSegment.loop (.block [])))

end VG.Impl.Argon2.AArch64.SegmentSetup
