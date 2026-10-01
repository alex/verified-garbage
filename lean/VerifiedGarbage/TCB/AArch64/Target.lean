import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.Artifact

/-!
# The AArch64 target (AAPCS64)

**Trusted.** Functions are emitted as Rust `extern "C"` naked functions.

AAPCS64 (Arm's "Procedure Call Standard for the Arm 64-bit Architecture"):
integer/pointer arguments arrive in `x0`–`x7`; `x19`–`x28` and the frame
pointer `x29` are callee-saved, as is `sp`. The model excludes `x29`,
so every instruction preserves the inherited frame pointer, including during
execution (Apple's ABI requires a valid frame pointer at all times).
The printer ends every function with `ret`, which returns to the address
in the link register `x30`, so `x30`
must be unchanged on exit. `x18` is the platform register (reserved on Apple
platforms and Windows), which the model does not have (see `TCB/AArch64/Isa.lean`),
so no code can modify it.

The SIMD and floating-point registers `v0`–`v7` and `v16`–`v31` are
caller-saved (AAPCS64 §6.1.2), so `abiPreserved` says nothing about them.
The low 64 bits of `v8`–`v15` are callee-saved, and the model does not have
those registers (see `TCB/AArch64/Isa.lean`), so no code can modify them.

PSTATE.C is modelled but is not callee-saved: NZCV is undefined on entry
to and return from a public interface (AAPCS64 §6.1.1). N, Z and V are not
observable by modelled instructions. FPCR and FPSR are not modelled (no
modelled instruction reads or writes them), nor is memory below `sp`
(never granted to a function).
-/

namespace VG.AArch64

def preserved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28,
  .x30]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp

/-- AAPCS64 argument registers, in order. -/
def argRegs : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]

/-! ## The calling convention, for `Sig`

Each integer or pointer argument takes the next of `x0`–`x7`
(a 32-bit argument in the low half; the upper half is unspecified). Once
they are used up, each further argument takes the next 8 bytes of stack, in
order, the first at `sp` on entry. AAPCS64, "Parameter passing rules":
stage A sets the next stacked argument address (NSAA) to `sp`; in stage C,
an integral or pointer argument of at most 8 bytes goes in `x[NGRN]` while
the next general-purpose register number NGRN is less than 8; otherwise
NGRN is set to 8, the NSAA is rounded up to the larger of 8 and the
argument's natural alignment, an argument of less than 8 bytes is given a
size of 8 bytes, and the argument is copied to memory at the NSAA, which is
then incremented by its size. Only 64-bit arguments (pointers, `usize`,
`u64`) are modelled on the stack: Apple's arm64 ABI ("Writing ARM64 code for
Apple platforms") passes narrower stack arguments in slots of their natural
size instead, and for 8-byte arguments the two conventions agree. `abi` only
grants reading the stack arguments, and assumes they do not wrap around the
end of the address space. The return address is in `x30`, not in memory;
the integer result is in `x0`.
-/

/-- The address of the `i`-th (from 0) stack argument, on entry. -/
def stackArgAddr (s : State) (i : Nat) : Addr := s.sp + BitVec.ofNat 64 (8 * i)

/-- The `i`-th (from 0) stack argument, on entry. -/
def stackArg (s : State) (i : Nat) : BitVec 64 := s.mem.readW (stackArgAddr s i) 64

def abi : Abi isa where
  ptrBits := 64
  args ws := if ws.length ≤ argRegs.length then
    some fun s => (argRegs.take ws.length).map s.gpr
  else if (ws.drop argRegs.length).all (· = 64) then
    some fun s => argRegs.map s.gpr ++ (List.range (ws.length - argRegs.length)).map (stackArg s)
  else none
  argArea ws s := let n := ws.length - argRegs.length
    if n = 0 then [] else [(⟨stackArgAddr s 0, 8 * n⟩, false)]
  reserved n s := stackBelow s.sp n
  -- The stack the function's calls and frames use, and its stack arguments,
  -- do not wrap around.
  wf ws n s := if ws.length ≤ argRegs.length then
      match n with
      | 0 => True
      | n => n ≤ s.sp.toNat
    else
      (match n with
      | 0 => True
      | n => n ≤ s.sp.toNat) ∧ s.sp.toNat + 8 * (ws.length - argRegs.length) ≤ 2 ^ 64
  pub s₁ s₂ := s₁.sp = s₂.sp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .x0
  argAreaDoc ws := if ws.length - argRegs.length = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"

abbrev target : Target where
  name := "aarch64"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  -- `aarch64_be` targets are big-endian, and ILP32 ones (`aarch64-unknown-linux-gnu_ilp32`)
  -- have 32-bit pointers. The model's baseline includes AdvSIMD (NEON: see
  -- `Instr.requires`), which `aarch64-unknown-none-softfloat` turns off.
  rustCfg := "all(target_arch = \"aarch64\", target_endian = \"little\", \
    target_pointer_width = \"64\", target_feature = \"neon\")"
  rustAbi := "C"
  abi := abi

end VG.AArch64
