import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.X86.Finalize
import VerifiedGarbage.Proof.Hmac.X86.Init
import VerifiedGarbage.Spec.Hmac.Contract

/-!
# Hmac on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Hmac/X86/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Hmac/Contract.lean`, which the
artifacts are emitted with.
-/

namespace VG.Proof.Hmac.X86.Shared

theorem init :
    Verified X86.target Impl.Hmac.X86.init (Spec.Hmac.initSha256Contract X86.abi) :=
  Proof.Hmac.X86.Init.init_verified.of_implies (by
    contract_implies [Spec.Hmac.initSha256Contract, Spec.Hmac.initSha256Sig,
      Proof.Hmac.initSha256X86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Hmac.X86.Init.sat, Proof.Hmac.X86.Init.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Hmac.X86.Init.sat)

theorem finalize :
    Verified X86.target Impl.Hmac.X86.finalize (Spec.Hmac.finalizeSha256OutContract X86.abi) :=
  Proof.Hmac.X86.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Hmac.finalizeSha256OutContract, Spec.Hmac.finalizeSha256OutSig,
      Proof.Hmac.finalizeSha256X86, Proof.Hmac.countFinalizeX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Hmac.X86.Finalize.sat, Proof.Hmac.X86.Finalize.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Hmac.X86.Finalize.sat)

end VG.Proof.Hmac.X86.Shared
