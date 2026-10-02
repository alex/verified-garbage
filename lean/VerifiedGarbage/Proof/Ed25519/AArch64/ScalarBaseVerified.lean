import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseCT
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseLit
import VerifiedGarbage.Proof.Framework.Contract

/-! Base-point multiplication satisfies the merged specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def baseSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' := scalarBase_correct hs

theorem scalarBase_verified : Verified AArch64.target scalarBase (Spec.Ed25519.scalarBaseContract AArch64.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, scalarBaseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.Ed25519.AArch64
