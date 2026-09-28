import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.AArch64.RoMixCT
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scrypt on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Scrypt/AArch64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Scrypt/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Scrypt.AArch64.Shared

theorem salsa :
    Verified AArch64.target Impl.Scrypt.AArch64.salsa (Spec.Scrypt.salsaContract AArch64.abi) :=
  Proof.Scrypt.AArch64.salsa_verified.of_implies (by
    contract_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig,
      Proof.Scrypt.salsaAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Scrypt.AArch64.satState] using Proof.Scrypt.AArch64.satState)

theorem blockMix :
    Verified AArch64.target Impl.Scrypt.AArch64.blockMix
      (Spec.Scrypt.blockMixContract AArch64.abi 16) :=
  Proof.Scrypt.AArch64.BlockMix.blockMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs] at h
        obtain ⟨-, -, -, -, -, -, hrc, -⟩ := id h
        rw [hrc] at h
        simp only [Proof.Scrypt.blockMixAArch64]
        rw [hrc]
        and_intros
        all_goals simp_all [Nat.mul_comm]
      post := by
        implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.BlockMix.bmSat] using Proof.Scrypt.AArch64.BlockMix.bmSat }

theorem roMix :
    Verified AArch64.target Impl.Scrypt.AArch64.roMix (Spec.Scrypt.roMixContract AArch64.abi 16) :=
  Proof.Scrypt.AArch64.RoMix.roMix_verified.of_implies
    { pre := by
        intro s h
        sig_unfold [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs] at h
        obtain ⟨hsp, hrd, hwr, ⟨⟨a, b⟩, c⟩, ⟨d, e, f⟩, ⟨g, i, j⟩, k, l, m, n⟩ := h
        exact ⟨hrd, hwr, a, b, c, hsp, d, e, f, g, i, j, k, l, m, n⟩
      post := by
        implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.RoMix.satState] using Proof.Scrypt.AArch64.RoMix.satState }

end VG.Proof.Scrypt.AArch64.Shared
