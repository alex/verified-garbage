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

The nightly-only `-Zregparm=N` flag changes this: it passes the first `N`
integer arguments of `extern "C"` (and `cdecl`) functions in `eax`, `edx` and
`ecx` instead of on the stack, so the functions read other values than the
arguments. There is no `cfg` for it, so the crate cannot refuse to build with
it: it must not be built with `-Zregparm` (nor Clang's `-mregparm` for code
calling it through the C ABI).

Not modelled: the direction flag (no modelled instruction changes it; it is
clear on entry and exit), x87 state and MXCSR (never modified), and memory
below `esp` (never granted to a function).
-/

namespace VG.X86

def calleeSaved : List Reg := [.ebx, .esi, .edi, .ebp, .esp]

/-- Calling-convention obligations on return. -/
def abiPreserved (s s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
  s'.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32

/-- The address of the `i`-th (from 0) 4-byte argument on entry. -/
def argAddr (s : State) (i : Nat) : Addr := (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64

/-- The value of the `i`-th (from 0) 4-byte argument on entry. -/
def arg (s : State) (i : Nat) : BitVec 32 := s.mem.readW (argAddr s i) 32

/-! ## The calling convention, for `Sig`

Every argument is on the stack, from `[esp + 4]` on entry upwards: a 32-bit
one in a 4-byte slot, a 64-bit one in two (low word first), with no further
alignment. The callee owns the argument area: GCC and LLVM both overwrite
incoming argument slots (e.g. for sibling calls), and callers never read them
back. So a function may overwrite it if its contract asks for it
(`writeArgs`). The return address at `[esp]` may not be touched. The
caller's frame (at and above `esp`) does not wrap around the end of the
address space. The result is in `eax` (low word) and `edx`.
-/

/-- The offsets from `esp + 4` (in 4-byte slots) of arguments of widths `ws`
(32 or 64 bits). -/
def argSlots : List Nat → Nat → List Nat
  | [], _ => []
  | w :: ws, i => i :: argSlots ws (i + w / 32)

def argVal (s : State) (w i : Nat) : BitVec 64 :=
  if w = 64 then arg s (i + 1) ++ arg s i else (arg s i).setWidth 64

/-- The size in bytes of the arguments. -/
def argBytes (ws : List Nat) : Nat := 4 * (ws.map (· / 32)).sum

def abi : Abi isa where
  ptrBits := 32
  args ws := if ws.all (fun w => w = 32 ∨ w = 64) then
    some fun s => (ws.zip (argSlots ws 0)).map fun (w, i) => argVal s w i else none
  argArea ws s := if argBytes ws = 0 then [] else [(⟨argAddr s 0, argBytes ws⟩, true)]
  reserved n s := ⟨(s.gpr .esp).setWidth 64, 4⟩ :: stackBelow ((s.gpr .esp).setWidth 64) n
  wf ws n s := match n with
    | 0 => (s.gpr .esp).toNat + 4 + argBytes ws ≤ 2 ^ 32
    | n => n ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + argBytes ws ≤ 2 ^ 32
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp
  mem s := s.mem
  rd s := s.rd
  wr s := s.wr
  ret s := s.gpr .edx ++ s.gpr .eax
  argAreaDoc ws := if argBytes ws = 0 then none else some ("the arguments on the stack", true)
  reservedDoc n := some (if n = 0 then "the return address on the stack" else
    s!"the return address on the stack or the {n} bytes of stack below it")

abbrev target : Target where
  name := "x86"
  isa := isa
  printer := printer
  abiPreserved := abiPreserved
  -- The model's baseline is i686 with SSE2 (`TCB/X86/Isa.lean`), which the
  -- `i586-*` targets and `i686-unknown-uefi` lack.
  rustCfg := "all(target_arch = \"x86\", target_feature = \"sse2\")"
  rustAbi := "C"
  abi := abi

end VG.X86
