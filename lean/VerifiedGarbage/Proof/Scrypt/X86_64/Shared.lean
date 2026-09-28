import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Scrypt/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Scrypt/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Scrypt.X86_64.Shared

theorem salsa :
    Verified X86_64.target Impl.Scrypt.X86_64.salsa (Spec.Scrypt.salsaContract X86_64.abi) :=
  Proof.Scrypt.X86_64.salsa_verified.of_implies (by
    contract_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig,
      Proof.Scrypt.salsaX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Scrypt.X86_64.satState] using Proof.Scrypt.X86_64.satState)

theorem blockMix :
    Verified X86_64.target Impl.Scrypt.X86_64.blockMix (Spec.Scrypt.blockMixContract X86_64.abi 8) :=
  Proof.Scrypt.X86_64.BlockMix.blockMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs] at h
        obtain ⟨-, -, -, -, -, hrc, -⟩ := id h
        rw [hrc] at h
        simp only [Proof.Scrypt.blockMixX86_64]
        rw [hrc]
        and_intros
        all_goals simp_all [Region.disjoint_comm, Nat.mul_comm]
      post := by
        implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.BlockMix.satState] using Proof.Scrypt.X86_64.BlockMix.satState }

theorem roMix :
    Verified X86_64.target Impl.Scrypt.X86_64.roMix (Spec.Scrypt.roMixContract X86_64.abi 16) :=
  Proof.Scrypt.X86_64.RoMix.roMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs] at h
        have hr9 := h.2.2.2.2.2.2.2.2
        simp only [Proof.Scrypt.roMixX86_64]
        rw [hr9] at h ⊢
        and_intros
        all_goals simp_all [Region.disjoint_comm, Nat.mul_comm]
      post := by
        implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.RoMix.satState] using Proof.Scrypt.X86_64.RoMix.satState }

end VG.Proof.Scrypt.X86_64.Shared
