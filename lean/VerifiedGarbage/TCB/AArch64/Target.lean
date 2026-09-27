import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The AArch64 target (AAPCS64)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions.

AAPCS64 (Arm's "Procedure Call Standard for the Arm 64-bit Architecture"):
integer/pointer arguments arrive in `x0`–`x7`; `x19`–`x28` and the frame
pointer `x29` are callee-saved, as is `sp`. The printer ends every function
with `ret`, which returns to the address in the link register `x30`, so `x30`
must be unchanged on exit. `x18` is the platform register (reserved on Apple
platforms and Windows), so it must not be modified either.

Not modelled: the SIMD and floating-point registers (never modified; the
low 64 bits of `v8`–`v15` are callee-saved), the condition flags (never
modified) and memory below `sp` (never granted to a function).
-/

namespace VG.AArch64

def preserved : List Reg := [.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28,
  .x29, .x30]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

abbrev target : Target where
  name := "aarch64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"aarch64\""
  rustAbi := "C"

/-- AAPCS64 argument registers, in order. -/
def argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

end VG.AArch64
