import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceLane
import VerifiedGarbage.Impl.Argon2.X86_64.FirstLane
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Impl.Argon2.X86_64.Relative
import VerifiedGarbage.Impl.Argon2.X86_64.Wrap

/-! Complete mapping of J₁ and J₂ to a reference lane and column.

`rdi` contains the random word and `rsi` the lane count. The current
lane is in `rbx`, lane and segment lengths in `r12` and `r13`, slice and
index in `r14` and `r15`. The pass counter is at the frame base `rbp`:
H₀'s first word is reused after memory initialization. `r9` and `rdi`
receive the reference lane and column. The input word is retained in `r11`.
-/

namespace VG.Impl.Argon2.X86_64.ReferenceMap

open VG.X86_64

def loadPass : List Instr := [.mov .r9 (.mem { base := .rbp })]

def laneArgs : List Instr := [.mov .rdi (.reg .r8), .mov .rsi (.reg .rbx)]

def relativeArgs : List Instr := [
  .mov .r9 (.reg .rdi), .mov .rdi (.reg .r11), .mov .rsi (.reg .r8)]

def wrapArgs : List Instr := [
  .mov .rdi (.reg .rax), .alu .add .rdi (.reg .r10), .mov .rsi (.reg .r12)]

def chooseLane : Prog isa :=
  .seq ReferenceLane.code (.seq (.block loadPass) FirstLane.code)

def prepareLanes : Prog isa := .seq chooseLane (.block laneArgs)

def window : Prog isa := .seq ReferenceStart.code ReferenceCount.code

def relative : Prog isa := .seq (.block relativeArgs) Relative.code

def finish : Prog isa := .seq (.block wrapArgs) Wrap.code

def code : Prog isa := .seq prepareLanes (.seq window (.seq relative finish))

end VG.Impl.Argon2.X86_64.ReferenceMap
