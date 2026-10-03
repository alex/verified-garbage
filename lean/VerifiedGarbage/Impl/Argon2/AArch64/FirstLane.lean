import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! Force the current lane on the first slice of the first pass.

The pass and slice are public in `x5` and `x22`. The current lane is in
`x24`; `x4` initially contains J₂ modulo the lane count. Only the public
position controls a branch.
-/

namespace VG.Impl.Argon2.AArch64.FirstLane

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def test : List Instr := [mov .x8 .x5, logic .orr .x8 .x22].flatten

def current : List Instr := [mov .x4 .x24].flatten

def code : Prog isa := .seq (.block test) (.ite (.zero .x .x15) (.block current) (.block []))

end VG.Impl.Argon2.AArch64.FirstLane
