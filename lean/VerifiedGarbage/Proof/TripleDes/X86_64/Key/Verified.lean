import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩, ⟨0x3000, 512⟩]

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Key.expandKey s t s' ∧ abiPreserved s s' ∧ contract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := expand_correct s hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.X86_64.Key.expandKey
    (Spec.TripleDes.expandKeyContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig, abi, argRegs,
    contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.X86_64.Key
