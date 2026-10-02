import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Divide

/-! # Selecting a lane from J₂ with fixed-time division

`x0` contains the full address word and `x1` the positive lane count.
`x4` receives J₂ modulo the lane count; `x7` retains the address word
for the subsequent J₁ mapping. The first slice of pass zero instead uses
the current lane; the enclosing public loop selects that case separately.
-/

namespace VG.Impl.Argon2.AArch64.ReferenceLane

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def highArgs : List Instr := [mov .x7 .x0, shr .x0 32].flatten

def code : Prog isa := .seq (.block highArgs) Divide.code

end VG.Impl.Argon2.AArch64.ReferenceLane
