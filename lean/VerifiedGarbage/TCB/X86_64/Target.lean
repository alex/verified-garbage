import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The x86-64 System V target

**Trusted.** Functions are emitted as Rust `extern "sysv64"` naked functions.

System V AMD64 ABI: integer/pointer arguments arrive in `rdi, rsi, rdx, rcx,
r8, r9`; the integer result is returned in `rax`; `rbx, rbp, rsp, r12–r15` are
callee-saved. The return address is at `[rsp]` on entry; the printer ends
every function with `ret`, so `abiPreserved` demands that `rsp` and the
return-address slot are unchanged on exit.

Not modelled: the direction flag (no modelled instruction changes it; it is
clear on entry and exit), x87/MXCSR control words (never modified), and the
red zone: a contract that grants write access below `rsp` must keep it within
the 128-byte red zone.
-/

namespace VG.X86_64

def calleeSaved : List Reg := [.rbx, .rbp, .rsp, .r12, .r13, .r14, .r15]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
  s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64

abbrev target : Target where
  name := "x86_64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"x86_64\""
  rustAbi := "sysv64"

/-- System V argument registers, in order. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

end VG.X86_64
