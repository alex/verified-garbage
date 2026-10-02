import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Hash
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified

/-! # H′: supplying a verified BLAKE2b streaming backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

/-- A backend supplies code together with its streaming correctness and
constant-time certificates. H′ is generic over every such backend. -/
structure Backend where
  suffix : String
  features : List String
  hash : Impl.Argon2.AArch64.HPrime.Hash
  ok : HashOk hash
  initCT : ConstantTime isa (Proof.Blake2.initAArch64 Spec.Blake2.b).pre
    (Proof.Blake2.initAArch64 Spec.Blake2.b).pub hash.init
  updateCT : ConstantTime isa (Proof.Blake2.updateAArch64 Spec.Blake2.b).pre
    (Proof.Blake2.updateAArch64 Spec.Blake2.b).pub hash.update
  finalizeCT : ConstantTime isa (Proof.Blake2.finalizeAArch64 Spec.Blake2.b).pre
    (Proof.Blake2.finalizeAArch64 Spec.Blake2.b).pub hash.finalize
  initV : hash.init.allInstrs keepsV = true
  updateV : hash.update.allInstrs keepsV = true
  finalizeV : hash.finalize.allInstrs keepsV = true
  initCorrect : ∀ s, (Proof.Blake2.initAArch64 Spec.Blake2.b).pre s →
    ∃ tr t, Exec isa hash.init s tr t ∧ abiPreserved s t ∧
      (Proof.Blake2.initAArch64 Spec.Blake2.b).post s t
  updateCorrect : ∀ s, (Proof.Blake2.updateAArch64 Spec.Blake2.b).pre s →
    ∃ tr t, Exec isa hash.update s tr t ∧ abiPreserved s t ∧
      (Proof.Blake2.updateAArch64 Spec.Blake2.b).post s t
  finalizeCorrect : ∀ s, (Proof.Blake2.finalizeAArch64 Spec.Blake2.b).pre s →
    ∃ tr t, Exec isa hash.finalize s tr t ∧ abiPreserved s t ∧
      (Proof.Blake2.finalizeAArch64 Spec.Blake2.b).post s t

def scalar : Backend where
  suffix := ""
  features := []
  hash := {
    initName := Spec.Blake2.initBApi.name
    init := Impl.Blake2.AArch64.Stream.init Spec.Blake2.b
    updateName := Spec.Blake2.updateBApi.name
    update := Impl.Blake2.AArch64.Stream.update Spec.Blake2.b
    finalizeName := Spec.Blake2.finalizeBApi.name
    finalize := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b }
  ok := ⟨Proof.Blake2.AArch64.Stream.initB_verified,
    Proof.Blake2.AArch64.Stream.updateB_verified, Proof.Blake2.AArch64.Stream.finalizeB_verified,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  initCT := Proof.Blake2.AArch64.Stream.initB_ct
  updateCT := Proof.Blake2.AArch64.Stream.updateB_ct
  finalizeCT := Proof.Blake2.AArch64.Stream.finalizeB_ct
  initV := by decide +kernel
  updateV := by decide +kernel
  finalizeV := by decide +kernel
  initCorrect := Proof.Blake2.AArch64.Stream.initB_correct
  updateCorrect := Proof.Blake2.AArch64.Stream.updateB_correct
  finalizeCorrect := Proof.Blake2.AArch64.Stream.finalizeB_correct

end VG.Proof.Argon2.AArch64.HPrime
