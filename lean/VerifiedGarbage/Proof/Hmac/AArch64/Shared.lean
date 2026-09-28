import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.AArch64.Finalize
import VerifiedGarbage.Proof.Hmac.AArch64.Init
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# Hmac on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/AArch64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Hmac/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Hmac.AArch64.Shared

theorem init :
    Verified AArch64.target Impl.Hmac.AArch64.init (Spec.Hmac.initSha256Contract AArch64.abi 16) :=
  Proof.Hmac.AArch64.Init.init_verified.of_implies (by
    contract_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig,
      Proof.Hmac.initSha256AArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Hmac.AArch64.Init.sat] using Proof.Hmac.AArch64.Init.sat)

theorem finalize :
    Verified AArch64.target Impl.Hmac.AArch64.finalize
      (Spec.Hmac.finalizeSha256Contract AArch64.abi 32) :=
  Proof.Hmac.AArch64.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Hmac.finalizeSha256Contract, Spec.Hmac.finalizeSha256Sig,
      Proof.Hmac.finalizeSha256AArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Hmac.AArch64.Finalize.sat] using Proof.Hmac.AArch64.Finalize.sat)

end VG.Proof.Hmac.AArch64.Shared
