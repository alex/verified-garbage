import VerifiedGarbage.Impl.Argon2.X86_64.Divide

/-! # Selecting a lane from J₂ with fixed-time division

`rdi` contains the full address word and `rsi` the positive lane count.
`r8` receives J₂ modulo the lane count; `r11` retains the address word
for the subsequent J₁ mapping. The first slice of pass zero instead uses
the current lane; the enclosing public loop selects that case separately.
-/

namespace VG.Impl.Argon2.X86_64.ReferenceLane

open VG.X86_64

def highArgs : List Instr := [.mov .r11 (.reg .rdi), .shift .shr .rdi 32]

def code : Prog isa := .seq (.block highArgs) Divide.code

end VG.Impl.Argon2.X86_64.ReferenceLane
