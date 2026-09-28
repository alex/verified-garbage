import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Sig

/-!
# The AAPCS64 calling convention, for `Sig`

**Trusted.** Each integer or pointer argument takes the next of `x0`–`x7`
(a 32-bit argument in the low half; the upper half is unspecified).
Arguments on the stack (more than eight) are not modelled. The return
address is in `x30`, not in memory; the integer result is in `x0`.
-/

namespace VG.AArch64

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr else none
  argArea _ _ := []
  reserved _ := []
  wf _ _ := True
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret _ s := s.gpr .x0

end VG.AArch64
