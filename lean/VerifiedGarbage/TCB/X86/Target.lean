import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The x86 (32-bit) cdecl target

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for `target_arch = "x86"`, where `extern "C"` is cdecl.

cdecl: the arguments are on the stack, the first at `[esp + 4]` on entry (the
return address is at `[esp]`), each 4 bytes; `ebx`, `esi`, `edi`, `ebp` and
`esp` are callee-saved. The printer ends every function with `ret`, so
`abiPreserved` demands that `esp` and the return-address slot are unchanged
on exit. The caller removes the arguments.

Not modelled: the direction flag (no modelled instruction changes it; it is
clear on entry and exit), x87/SSE state (never modified), and memory below
`esp` (never granted to a function).
-/

namespace VG.X86

def calleeSaved : List Reg := [.ebx, .esi, .edi, .ebp, .esp]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
  s'.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32

abbrev target : Target where
  name := "x86"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "target_arch = \"x86\""
  rustAbi := "C"

/-- The address of the `i`-th (from 0) 4-byte argument on entry. -/
def argAddr (s : State) (i : Nat) : Addr := (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64

/-- The value of the `i`-th (from 0) 4-byte argument on entry. -/
def arg (s : State) (i : Nat) : BitVec 32 := s.mem.readW (argAddr s i) 32

end VG.X86
