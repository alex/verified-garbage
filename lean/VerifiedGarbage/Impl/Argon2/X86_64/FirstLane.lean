import VerifiedGarbage.TCB.X86_64.Isa

/-! Force the current lane on the first slice of the first pass.

The pass and slice are public in `r9` and `r14`. The current lane is in
`rbx`; `r8` initially contains J₂ modulo the lane count. Only the public
position controls a branch.
-/

namespace VG.Impl.Argon2.X86_64.FirstLane

open VG.X86_64

def test : List Instr := [.mov .rax (.reg .r9), .alu .or .rax (.reg .r14)]

def current : List Instr := [.mov .r8 (.reg .rbx)]

def code : Prog isa := .seq (.block test) (.ite .e (.block current) (.block []))

end VG.Impl.Argon2.X86_64.FirstLane
