import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.TCB.Sig

/-!
# The System V AMD64 calling convention, for `Sig`

**Trusted.** Each integer or pointer argument takes the next of `rdi, rsi,
rdx, rcx, r8, r9` (a 32-bit argument in the low half; the upper half is
unspecified). Arguments on the stack (more than six) are not modelled. The
return address is at `[rsp]`; the integer result is in `rax`.
-/

namespace VG.X86_64

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr else none
  argArea _ _ := []
  reserved s := [⟨s.gpr .rsp, 8⟩]
  wf _ _ := True
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret _ s := s.gpr .rax

end VG.X86_64
