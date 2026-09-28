import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# GCM on AArch64: the shared contracts

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Gcm/AArch64/Contract.lean`); this theorem moves
it to the shared contract of `Spec/Gcm/Contract.lean`, which the artifact is
emitted with.
-/

namespace VG.Proof.Gcm.AArch64.Shared

theorem ghash :
    Verified AArch64.target Impl.Gcm.AArch64.ghash (Spec.Gcm.ghashContract AArch64.abi) :=
  Proof.Gcm.AArch64.ghash_verified.of_implies (by
    contract_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig,
      Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

end VG.Proof.Gcm.AArch64.Shared
