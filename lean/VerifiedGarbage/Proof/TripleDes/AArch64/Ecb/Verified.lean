import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Correct

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.AArch64.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .encrypt s hs
  change Exec isa Impl.TripleDes.AArch64.Ecb.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.AArch64.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .decrypt s hs
  change Exec isa Impl.TripleDes.AArch64.Ecb.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.AArch64.Exec.sp he, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
      s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.AArch64.Ecb.encrypt
    (Spec.TripleDes.ecbEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct
    (ecbEncrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.AArch64.Ecb.decrypt
    (Spec.TripleDes.ecbDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct
    (ecbDecrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.AArch64.Ecb
