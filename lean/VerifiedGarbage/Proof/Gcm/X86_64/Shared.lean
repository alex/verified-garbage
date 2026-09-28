import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.X86_64.Ghash
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# GCM on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Gcm/X86_64/Contract.lean`); this theorem moves
it to the shared contract of `Spec/Gcm/Contract.lean`, which the artifact is
emitted with.
-/

namespace VG.Proof.Gcm.X86_64.Shared

theorem ghash :
    Verified X86_64.target Impl.Gcm.X86_64.ghash (Spec.Gcm.ghashContract X86_64.abi) :=
  Proof.Gcm.X86_64.ghash_verified.of_implies (by
    contract_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig,
      Proof.Gcm.ghashX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Gcm.X86_64.satState] using Proof.Gcm.X86_64.satState)

end VG.Proof.Gcm.X86_64.Shared
