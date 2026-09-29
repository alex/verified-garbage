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
platforms and Windows), which the model does not have (see `TCB/AArch64/Isa.lean`),
so no code can modify it.

The SIMD and floating-point registers `v0`–`v7` and `v16`–`v31` are
caller-saved (AAPCS64 §6.1.2), so `abiPreserved` says nothing about them.
The low 64 bits of `v8`–`v15` are callee-saved, and the model does not have
those registers (see `TCB/AArch64/Isa.lean`), so no code can modify them.

Not modelled: the condition flags (never modified), FPCR and FPSR (no
modelled instruction reads or writes them) and memory below `sp` (never
granted to a function).
-/

namespace VG.AArch64

def preserved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28,
  .x29, .x30]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

/-- AAPCS64 argument registers, in order. -/
def argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `x0`–`x7`
(a 32-bit argument in the low half; the upper half is unspecified).
Arguments on the stack (more than eight) are not modelled. The return
address is in `x30`, not in memory; the integer result is in `x0`.
-/

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr else none
  argArea _ _ := []
  reserved n s := stackBelow s.sp n
  -- The stack the function's calls and frames use does not wrap around.
  wf _ n s := match n with
    | 0 => True
    | n => n ≤ s.sp.toNat
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .x0
  argAreaDoc _ := none
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"

abbrev target : Target where
  name := "aarch64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"aarch64\""
  rustAbi := "C"
  abi := abi

end VG.AArch64
