import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Ecb
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.ConstantTime
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Verified

/-! # The AVX2 bitsliced ECB functions meet their contracts -/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx2

open VG VG.X86_64
open VG.Proof.TripleDes.X86_64.Bitsliced (contract ecbTaint_agree satState publicRegs_five)

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx2.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .encrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.X86_64.BitsliceAvx2.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  obtain ⟨t, s', he, ha, hp⟩ := ecb_ok .decrypt rd wr kd kb db rdt rb fit
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

theorem encrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceAvx2.encrypt
    (Spec.TripleDes.ecbEncryptContract abi) := by
  refine Verified.of_correct encrypt_correct
    (encrypt_constantTime _ _ (ecbTaint_agree .encrypt)) ?_
  sig_implies [Spec.TripleDes.ecbEncryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_five] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.X86_64.BitsliceAvx2.decrypt
    (Spec.TripleDes.ecbDecryptContract abi) := by
  refine Verified.of_correct decrypt_correct
    (decrypt_constantTime _ _ (ecbTaint_agree .decrypt)) ?_
  sig_implies [Spec.TripleDes.ecbDecryptContract, Spec.TripleDes.ecbContract,
    Spec.TripleDes.ecbSig, abi, argRegs, contract, publicRegs_five] [satState] using satState

end VG.Proof.TripleDes.X86_64.BitslicedAvx2
