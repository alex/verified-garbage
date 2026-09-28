import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Aes/AArch64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Aes/Contract.lean` and
`Spec/Gcm/Contract.lean`, which the artifacts are emitted with.
-/

namespace VG.Proof.Aes.AArch64.Shared

theorem ctr32 :
    Verified AArch64.target Impl.Aes.AArch64.ctr32 (Spec.Gcm.ctr32Contract AArch64.abi) :=
  Proof.Aes.AArch64.ctr32_verified.of_implies (by
    contract_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32AArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Aes.AArch64.satState] using Proof.Aes.AArch64.satState)

theorem expandKey :
    Verified AArch64.target Impl.Aes.AArch64.expandKey (Spec.Aes.expandKeyContract AArch64.abi) :=
  Proof.Aes.AArch64.expandKey_verified.of_implies (by
    contract_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Aes.AArch64.ekSatState] using Proof.Aes.AArch64.ekSatState)

end VG.Proof.Aes.AArch64.Shared
