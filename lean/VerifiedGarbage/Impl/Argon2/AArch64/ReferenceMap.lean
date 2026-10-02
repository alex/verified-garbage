import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceLane
import VerifiedGarbage.Impl.Argon2.AArch64.FirstLane
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceCount
import VerifiedGarbage.Impl.Argon2.AArch64.Relative
import VerifiedGarbage.Impl.Argon2.AArch64.Wrap

/-! Complete mapping of J₁ and J₂ to a reference lane and column.

`x0` contains the random word and `x1` the lane count. The current
lane is in `x24`, lane and segment lengths in `x20` and `x21`, slice and
index in `x22` and `x23`. The pass counter is at the frame base `x19`:
H₀'s first word is reused after memory initialization. `x5` and `x0`
receive the reference lane and column. The input word is retained in `x7`.
-/

namespace VG.Impl.Argon2.AArch64.ReferenceMap

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def loadPass : List Instr := [load .x5 .x19 0].flatten

def laneArgs : List Instr := [mov .x0 .x4, mov .x1 .x24].flatten

def relativeArgs : List Instr := [mov .x5 .x0, mov .x0 .x7, mov .x1 .x4].flatten

def wrapArgs : List Instr := [mov .x0 .x8, add .x0 .x6, mov .x1 .x20].flatten

def chooseLane : Prog isa :=
  .seq ReferenceLane.code (.seq (.block loadPass) FirstLane.code)

def prepareLanes : Prog isa := .seq chooseLane (.block laneArgs)

def window : Prog isa := .seq ReferenceStart.code ReferenceCount.code

def relative : Prog isa := .seq (.block relativeArgs) Relative.code

def finish : Prog isa := .seq (.block wrapArgs) Wrap.code

def code : Prog isa := .seq prepareLanes (.seq window (.seq relative finish))

end VG.Impl.Argon2.AArch64.ReferenceMap
