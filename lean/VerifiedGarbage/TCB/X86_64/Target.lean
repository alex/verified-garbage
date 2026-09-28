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

The SSE registers `xmm0`–`xmm15` are all caller-saved (System V AMD64
psABI §3.2.1, Figure 3.4: "No" under "callee-saved"; also on Windows, whose
own convention the functions do not use), and so are the upper halves of
the `ymm` registers that contain them (the psABI makes no vector register
callee-saved), so `abiPreserved` says nothing about them.

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

/-- System V argument registers, in order. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `rdi, rsi,
rdx, rcx, r8, r9` (a 32-bit argument in the low half; the upper half is
unspecified). Arguments on the stack (more than six) are not modelled. The
return address is at `[rsp]`; the integer result is in `rax`.
-/

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr else none
  argArea _ _ := []
  reserved n s := ⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) n
  wf _ _ _ := True
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .rax

abbrev target : Target where
  name := "x86_64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"x86_64\""
  rustAbi := "sysv64"
  abi := abi

end VG.X86_64
