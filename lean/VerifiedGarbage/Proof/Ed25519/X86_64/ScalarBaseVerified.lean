import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseLit
import VerifiedGarbage.Proof.Framework.Contract

/-! Untrusted: base-point multiplication satisfies the merged specification. -/

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

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBase fld) s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct (fld := fld) hs
  exact ⟨t, s', he, abiPreserved_of_exec (by fld_lit_decide) he h.1, h.2⟩

theorem scalarBase_verified : Verified X86_64.target (scalarBase fld) (Spec.Ed25519.scalarBaseContract X86_64.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, scalarBaseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.Ed25519.X86_64
