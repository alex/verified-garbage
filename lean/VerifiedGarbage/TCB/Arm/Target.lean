import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The 32-bit ARM target (AAPCS)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for `target_arch = "arm"`. The model is of ARMv7-A: on an older
architecture version the assembler rejects instructions such as `movw`.

AAPCS (Arm's "Procedure Call Standard for the Arm Architecture"): integer and
pointer arguments arrive in `r0`–`r3`; `r4`–`r11` and `sp` are callee-saved.
The printer ends every function with `bx lr`, which returns to the address
in the link register `lr`, so `lr` must be unchanged on exit.

Not modelled: the floating-point and SIMD registers (never modified; `d8`–
`d15` are callee-saved), the flags other than N, Z, C, V (never modified), and
memory below `sp` (never granted to a function).
-/

namespace VG.Arm

def preserved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

abbrev target : Target where
  name := "arm"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"arm\""
  rustAbi := "C"

/-- AAPCS argument registers, in order. -/
def argRegs : List Reg := [.r0, .r1, .r2, .r3]

end VG.Arm
