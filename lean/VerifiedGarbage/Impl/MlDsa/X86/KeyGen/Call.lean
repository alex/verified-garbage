import VerifiedGarbage.Impl.MlKem.X86.Top

/-!
# ML-DSA on x86 (32-bit): calls of the primitives from the top-level functions

`vg_mldsa*_keygen` and `vg_mldsa*_verify` are, like ML-KEM's top-level
functions (`Impl/MlKem/X86/Top.lean`, whose buffers `Buf`, `ptrTo`, hashes,
byte stores, copies and masks they use), leaves that keep `scratch` in `esi`
and call the primitives and the Keccak functions with their arguments pushed
in a frame of their own.

A call of a primitive (`callP`) is written for any code `c` of it: its
arguments (`Arg`: a buffer's address, or an immediate) are set in `eax`,
`ecx`, `edx`, `ebx`, `edi` and `ebp`, in order (`setArgs`), then pushed,
last first, so that the callee finds argument `i` at `[esp + 4 + 4i]`.
`callPR` keeps the value the callee returns in `eax` (`callRet`).
-/

namespace VG.Impl.MlDsa.X86.KeyGen

open VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo callWith callRet)

/-- An argument of a call: the address of a buffer, or a 32-bit immediate. -/
inductive Arg
  | buf (b : Buf)
  | imm (v : Nat)

/-- The registers the arguments are set in, in order. -/
def argRegs : List Reg := [.eax, .ecx, .edx, .ebx, .edi, .ebp]

/-- `r ← a`. -/
def Arg.set (sc : Nat) (r : Reg) : Arg → List Instr
  | .buf b => ptrTo sc r b
  | .imm v => [.mov r (.imm (BitVec.ofNat 32 v))]

/-- Each argument into its register. -/
def setArgs (sc : Nat) : List Reg → List Arg → List Instr
  | r :: rs, a :: as => a.set sc r ++ setArgs sc rs as
  | _, _ => []

/-- The registers of `n` arguments, in the order they are pushed. -/
def argRs (n : Nat) : List Reg := (argRegs.take n).reverse

/-- A call of `c` (named `nm`) with the arguments `as`. -/
def callP (sc : Nat) (nm : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (setArgs sc argRegs as)) (callWith (argRs as.length) nm c)

/-- `callP`, keeping the value `c` returns in `eax`. -/
def callPR (sc : Nat) (nm : String) (c : Prog isa) (as : List Arg) : Prog isa :=
  .seq (.block (setArgs sc argRegs as)) (callRet (argRs as.length) nm c)

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

end VG.Impl.MlDsa.X86.KeyGen
