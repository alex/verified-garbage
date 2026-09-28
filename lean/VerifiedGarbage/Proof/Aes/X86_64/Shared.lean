import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Aes/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Aes/Contract.lean` and
`Spec/Gcm/Contract.lean`, which the artifacts are emitted with.
-/

namespace VG.Proof.Aes.X86_64.Shared

theorem ctr32 :
    Verified X86_64.target Impl.Aes.X86_64.ctr32 (Spec.Gcm.ctr32Contract X86_64.abi) :=
  Proof.Aes.X86_64.ctr32_verified.of_implies (by
    contract_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32X86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.satState] using Proof.Aes.X86_64.satState)

theorem expandKey :
    Verified X86_64.target Impl.Aes.X86_64.expandKey (Spec.Aes.expandKeyContract X86_64.abi) :=
  Proof.Aes.X86_64.expandKey_verified.of_implies (by
    contract_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Proof.Aes.expandKeyX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.ekSatState] using Proof.Aes.X86_64.ekSatState)

end VG.Proof.Aes.X86_64.Shared
