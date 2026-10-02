import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Correct

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .encrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .decrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
      s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.encrypt
    (Spec.TripleDes.ecbEncryptContract abi 0) := by
  refine Verified.of_correct encrypt_correct
    (ecbEncrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.decrypt
    (Spec.TripleDes.ecbDecryptContract abi 0) := by
  refine Verified.of_correct decrypt_correct
    (ecbDecrypt_constantTime _) ?_
  sig_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.Arm.Ecb
