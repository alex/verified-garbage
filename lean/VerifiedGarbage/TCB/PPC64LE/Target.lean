import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The 64-bit little-endian PowerPC target (ELFv2)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions,
compiled for little-endian `powerpc64`, whose C calling convention is the
64-bit ELF V2 ABI (OpenPOWER, Revision 1.5).

ELFv2 (§2.2.2.1, "Register Roles"): integer and pointer arguments arrive in
`r3`–`r10`; `r14`–`r31` are nonvolatile, as is `r1`, the stack pointer, and
`r2`, the TOC pointer, must hold the same value on return (for a function
whose symbol's `st_other` entry-point bits are 0, as for a naked function,
which has a single entry point: §3.4.1, "Symbol Values"). `r13`, the thread
pointer, is reserved; the model never changes it. The printer ends every
function with `blr`, which returns to the address in the link register, so
`LR` must be unchanged on exit.

Not modelled: the floating-point and vector registers (never modified;
`f14`–`f31` and `v20`–`v31` are nonvolatile), the condition register (only
field 0, which is volatile, is ever modified: the nonvolatile fields
`CR2`–`CR4` are not), `XER` and `CTR` (never modified by the modelled
instructions; both volatile), and memory below `r1` (never granted to a
function; the frames' pushes write there, see `push`).
-/

namespace VG.PPC64LE

def preserved : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
  .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.lr = s.lr

/-- ELFv2 argument registers, in order. -/
def argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `r3`–`r10` (§2.2.4, "Up
to eight arguments can be passed in general-purpose registers r3–r10"; a
32-bit argument in the low half, whose upper half the model does not rely
on). Arguments in memory (more than eight) are not modelled. The return
address is in `LR`, not in memory; the integer result is in `r3` (§2.2.6).
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
  ret s := s.gpr .r3
  -- Every modelled argument is in a register.
  argAreaDoc _ := none
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"

abbrev target : Target where
  name := "powerpc64le"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  rustCfg := "all(target_arch = \"powerpc64\", target_endian = \"little\")"
  rustAbi := "C"
  abi := abi

end VG.PPC64LE
