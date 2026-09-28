import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-NI: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Aes/X86_64/AesNi/Contract.lean`);
these theorems move them to the shared contracts of `Spec/`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Aes.X86_64.AesNi.Shared

theorem ctr32 :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.ctr32 (Spec.Gcm.ctr32Contract X86_64.abi) :=
  Proof.Aes.X86_64.AesNi.ctr32_verified.of_implies (by
    contract_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig,
      Proof.Aes.X86_64.AesNi.ctr32X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.AesNi.satState] using Proof.Aes.X86_64.AesNi.satState)

theorem expandKey :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.expandKey (Spec.Aes.expandKeyContract X86_64.abi) :=
  Proof.Aes.X86_64.AesNi.Key.expandKey_verified.of_implies (by
    contract_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig,
      Proof.Aes.X86_64.AesNi.expandKeyX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Aes.X86_64.AesNi.Key.satState] using Proof.Aes.X86_64.AesNi.Key.satState)

end VG.Proof.Aes.X86_64.AesNi.Shared
