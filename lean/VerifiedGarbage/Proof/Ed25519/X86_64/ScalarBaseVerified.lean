import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT
import VerifiedGarbage.Proof.Framework.Contract

/-! A state satisfying the precondition of `vg_ed25519_scalar_base`'s contract,
the witness that it is satisfiable (`ScalarBasePrecomputedVerified.lean`). -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

def baseSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

end VG.Proof.Ed25519.X86_64
