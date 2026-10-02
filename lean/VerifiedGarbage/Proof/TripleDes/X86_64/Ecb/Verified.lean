import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Correct

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .encrypt s hs
  change Exec isa Impl.TripleDes.X86_64.Ecb.encrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .decrypt s hs
  change Exec isa Impl.TripleDes.X86_64.Ecb.decrypt s t s' at he
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.X86_64.Ecb.encrypt
    (Spec.TripleDes.ecbEncryptContract abi 8) := by
  refine Verified.of_correct encrypt_correct
    (ecbEncrypt_constantTime _ _ (ecbTaint_agree .encrypt)) ?_
  sig_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_five] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.X86_64.Ecb.decrypt
    (Spec.TripleDes.ecbDecryptContract abi 8) := by
  refine Verified.of_correct decrypt_correct
    (ecbDecrypt_constantTime _ _ (ecbTaint_agree .decrypt)) ?_
  sig_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_five] [satState] using satState

end VG.Proof.TripleDes.X86_64.Ecb
