import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.X86_64.Finalize
import VerifiedGarbage.Proof.Hmac.X86_64.Init
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# Hmac on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Hmac/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Hmac.X86_64.Shared

theorem init :
    Verified X86_64.target Impl.Hmac.X86_64.init (Spec.Hmac.initSha256Contract X86_64.abi 8) :=
  Proof.Hmac.X86_64.Init.init_verified.of_implies (by
    contract_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig,
      Proof.Hmac.initSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Hmac.X86_64.Init.sat] using Proof.Hmac.X86_64.Init.sat)

theorem finalize :
    Verified X86_64.target Impl.Hmac.X86_64.finalize (Spec.Hmac.finalizeSha256Contract X86_64.abi 16) :=
  Proof.Hmac.X86_64.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Hmac.finalizeSha256Contract, Spec.Hmac.finalizeSha256Sig,
      Proof.Hmac.finalizeSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Hmac.X86_64.Finalize.sat] using Proof.Hmac.X86_64.Finalize.sat)

end VG.Proof.Hmac.X86_64.Shared
